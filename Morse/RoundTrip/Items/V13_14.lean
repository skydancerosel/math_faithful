import Morse
import RoundTrip.Check
import RoundTrip.Blind.V13_14
import RoundTrip.Bridge

open Set Filter Topology Function Module
open scoped ContDiff Manifold unitInterval

namespace RoundTrip.V13_14

/-- The project's statement (universes instantiated at `0`): for a slice submanifold `N ⊆ V` (any
model `Z`) and `f = F|N` with `F : V → ℝ` smooth on `V`, minimum value `d` (not assumed attained),
compact sublevel sets, every critical point outside `M⁰ = f⁻¹(d)` of index `≥ λ₀`, and `M⁰` with an
open neighbourhood `U` from which it pushes maps (in place of Milnor's "`M⁰` is a manifold" + Hanner):
every map from a compact `P` embedded in a real vector space of dimension `< λ₀` into `N` (resp. into
`N^b`, `b < a₀`, in the sublevel version) is homotopic rel the preimage of `M⁰` to a map into `M⁰`
(`lemma_22_5`, `lemma_22_5_sublevel`); a neighbourhood deforming into `M⁰` fixing `M⁰` pushes maps
(`pushesInto_of_deformation`); critical points and Hessians of `F|N` depend only on the germ of `F`
(`criticalPoint_hessianM_congr`). -/
def A : Prop :=
  type_of% @Morse.pushesInto_of_deformation.{0,0} ∧
  type_of% @Morse.criticalPoint_hessianM_congr.{0,0,0} ∧
  type_of% @Morse.lemma_22_5_sublevel.{0,0,0,0,0} ∧
  type_of% @Morse.lemma_22_5.{0,0,0,0,0}

theorem A_holds : A :=
  ⟨@Morse.pushesInto_of_deformation, @Morse.criticalPoint_hessianM_congr,
    @Morse.lemma_22_5_sublevel, @Morse.lemma_22_5⟩

/-! Neither `A → B` nor `B → A` is proved; see `V13_14.json`.

* `A ⇒ B` fails: `B` is for abstract manifolds and smooth `f : M → ℝ`; `A` only for `f = F|N`
  with `F` smooth on the ambient `V` (not every smooth function on a non-closed slice submanifold
  extends), and `A` assumes the neighbourhood `U` pushing maps into `M⁰`, which `B`'s hypothesis
  "`M⁰` is a topological manifold" yields only through Hanner's theorem (a manifold is a
  neighbourhood retract) and a deformation of the neighbourhood (Milnor's short geodesics,
  item V13_15) — neither formalized.
* `B ⇒ A` fails: `A`'s hypothesis (a pushing neighbourhood) does not make `M⁰` a manifold, so `B`
  cannot be applied under `A`'s hypotheses; `A`'s conclusion covers every compact `P` embedded in
  `ℝ^{<λ₀}` rel the (arbitrary closed) preimage of `M⁰`, not only cubes rel `∂Iʳ`; `A` has a
  sublevel version and two general lemmas.

## The embedded special case (smooth, not Riemannian)

What is glue is the passage between the conclusions: `B_emb'` is `B` on `M = ↥N` (the Bridge's
smooth manifold, model `ℝⁿ`) for `f = F|N`, with "`M⁰` is a topological manifold" replaced by the
conclusion of Milnor's Hanner step (item V13_15): "`M⁰` has an open neighbourhood `U` which deforms
into `M⁰` within `M`, fixing `M⁰`". `A ⇒ B_emb'` is proved below; the blind critical points and
index are the project's (`IsCritM` = `IsCriticalPointM` by definition, `idxM = indexM` through
`bIndex_univ_eq_index`). -/

/-- The blind index of a continuous bilinear form on the whole space is the project's `index`. -/
theorem bIndex_univ_eq_index {m : ℕ} (H : Rn m →L[ℝ] Rn m →L[ℝ] ℝ) :
    bIndex (Set.univ : Set (Rn m)) (fun v w => H v w) = (Morse.index H : ℕ∞) := by
  refine le_antisymm (iSup₂_le fun S hS => ?_) ?_
  · exact_mod_cast Morse.finrank_le_index_of_negDef H hS.2.2
  · obtain ⟨W, hW, hneg⟩ := Morse.exists_negDef_finrank_eq_index H
    rw [← hW]
    exact le_iSup₂_of_le (f := fun (S : Submodule ℝ (Rn m))
      (_ : (S : Set (Rn m)) ⊆ Set.univ ∧ FiniteDimensional ℝ S ∧ IsNegDefSub (fun v w => H v w) S) =>
      (Module.finrank ℝ S : ℕ∞)) W ⟨subset_univ _, inferInstance, hneg⟩ le_rfl

/-- The blind index on a manifold is the project's `indexM` (the blind `hessM` is `hessianM`). -/
theorem idxM_eq_indexM {m : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (Rn m) M]
    (f : M → ℝ) (x : M) : idxM (m := m) f x = (Morse.indexM (Rn m) f x : ℕ∞) :=
  bIndex_univ_eq_index _

/-- `B` on the Bridge's embedded manifolds `M = ↥N` (model `ℝⁿ`). -/
def B_emb : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (W : Type) [NormedAddCommGroup W] [NormedSpace ℝ W] (n : ℕ) (N : Set V)
    (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N) (f : Bridge.Sub hN → ℝ) (l0 : ℕ),
    ContMDiff 𝓘(ℝ, Rn n) 𝓘(ℝ, ℝ) ∞ f →
    (∀ x, 0 ≤ f x) → (∃ x, f x = 0) → (∀ c : ℝ, IsCompact {x | f x ≤ c}) →
    IsTopMfd ↥{x : Bridge.Sub hN | f x = 0} →
    (∀ x, f x ≠ 0 → IsCritM (m := n) f x → (l0 : ℕ∞) ≤ idxM (m := n) f x) →
    ∀ r : ℕ, r < l0 → RelPiTrivial (Bridge.Sub hN) {x | f x = 0} r

theorem B_to_B_emb : B → B_emb := fun hB _ _ _ _ _ _ _ n _ hN =>
  hB n (Bridge.Sub hN)

/-- `B_emb` for `f = F|N` (`F` smooth on `V`), with "`M⁰` is a topological manifold" replaced by the
conclusion of Milnor's Hanner step: an open `U ⊇ M⁰` deforming into `M⁰` within `M`, fixing `M⁰`. -/
def B_emb' : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (W : Type) [NormedAddCommGroup W] [NormedSpace ℝ W] (n : ℕ) (N : Set V)
    (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N) (F : V → ℝ) (l0 : ℕ),
    ContDiff ℝ ∞ F →
    (∀ x : Bridge.Sub hN, 0 ≤ F (Bridge.incl hN x)) →
    (∃ x : Bridge.Sub hN, F (Bridge.incl hN x) = 0) →
    (∀ c : ℝ, IsCompact {x : Bridge.Sub hN | F (Bridge.incl hN x) ≤ c}) →
    (∃ U : Set (Bridge.Sub hN), IsOpen U ∧ {x | F (Bridge.incl hN x) = 0} ⊆ U ∧
      ∃ D : C(I × U, Bridge.Sub hN), (∀ x, D (0, x) = x) ∧
        (∀ x, F (Bridge.incl hN (D (1, x))) = 0) ∧
        ∀ t (x : U), F (Bridge.incl hN x) = 0 → D (t, x) = x) →
    (∀ x : Bridge.Sub hN, F (Bridge.incl hN x) ≠ 0 → IsCritM (m := n) (F ∘ Bridge.incl hN) x →
      (l0 : ℕ∞) ≤ idxM (m := n) (F ∘ Bridge.incl hN) x) →
    ∀ r : ℕ, r < l0 → RelPiTrivial (Bridge.Sub hN) {x | F (Bridge.incl hN x) = 0} r

/-- **A gives B's conclusion on `↥N` for `f = F|N`, under the deformation hypothesis**: A's
`pushesInto_of_deformation` turns the deformation into A's pushing neighbourhood, and A's
`lemma_22_5` with `d = 0`, `P = Iʳ ⊆ ℝʳ` gives the compression (rel `h⁻¹(M⁰) ⊇ ∂Iʳ`). -/
theorem A_to_B_emb' : A → B_emb' := by
  rintro ⟨hdef, -, -, h225⟩ V _ _ _ W _ _ n N hN F l0 hF hmin - hK ⟨U, hUo, hMU, D, hD0, hD1, hDfix⟩
    hidx r hr
  let _ := hN.chartedSpace
  have hzero : ∀ x : Bridge.Sub hN, F (Bridge.incl hN x) ≤ 0 → F (Bridge.incl hN x) = 0 :=
    fun x hx => le_antisymm hx (hmin x)
  have hpush : Morse.PushesInto (Fin r → I) (Morse.sublevel (F ∘ Subtype.val : N → ℝ) 0) univ := by
    refine h225 hN hF (d := 0) hmin hK (l₀ := l0) (fun q hq hpos => ?_) (P := Fin r → I)
      (E := Fin r → ℝ) (by rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]; exact hr)
      (ι := fun y j => (y j : ℝ)) (by fun_prop)
      (fun a b hab => funext fun j => Subtype.ext (congrFun hab j))
      ⟨U, hUo, fun x hx => hMU (hzero x hx),
        hdef D hD0 (fun x => le_of_eq (hD1 x)) fun t x hx => hDfix t x (hzero x.1 hx)⟩
    have h1 := hidx q (ne_of_gt hpos) hq
    have h2 : (l0 : ℕ∞) ≤ (Morse.indexM (Rn n) (F ∘ Subtype.val) q : ℕ∞) :=
      h1.trans_eq (idxM_eq_indexM (m := n) (M := Bridge.Sub hN) _ _)
    exact_mod_cast h2
  intro f hf
  obtain ⟨g, hg, ⟨H⟩⟩ := hpush f fun _ => trivial
  exact ⟨g, fun y => hzero _ (hg y),
    ⟨Morse.Homotopy.homotopyRelMono H fun y hy => le_of_eq (hf y hy)⟩⟩

#rt_check RoundTrip.V13_14.A_to_B_emb' [Morse.pushesInto_of_deformation,
  Morse.criticalPoint_hessianM_congr, Morse.lemma_22_5_sublevel, Morse.lemma_22_5]
#rt_overlap RoundTrip.V13_14.A_to_B_emb' [Morse.pushesInto_of_deformation,
  Morse.criticalPoint_hessianM_congr, Morse.lemma_22_5_sublevel, Morse.lemma_22_5]

end RoundTrip.V13_14
