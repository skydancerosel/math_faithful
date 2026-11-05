import Morse
import RoundTrip.Check
import RoundTrip.Blind.V9_19
import RoundTrip.Bridge

open Set Filter Topology Function Module
open scoped ContDiff Manifold

namespace RoundTrip.V9_19

/-- The project's statement (universes instantiated at `0`), for a slice submanifold `N ⊆ V` with
the induced metric, ANY smooth curve `γ` in `N` on `[0, 1]` (no geodesic hypothesis), `0 < τ ≤ 1`
and division points `B` with `Morse.IsFine hN γ hc B τ` (pieces of length `≤ h₀`); `E_**` is the
formula-defined bilinear form `Morse.energyHessian`:
* `lemma_15_4`: `formIndex (E_** on fieldsUpTo τ) = formIndex (E_** on brokenSpace B τ)`;
* `lemma_15_4_ker`: the null space of `E_**` on `fieldsUpTo τ` is (the image of) its null space on
  the broken Jacobi fields;
* `eq_jacobi_of_jumps_zero`: a broken Jacobi field with `P Δ_b X' = 0` at every division point
  agrees on `[0, τ]` with a Jacobi field (any `B ⊆ (0, τ)`, no fineness needed);
* `finrank_ker_broken`: the nullity on the broken Jacobi fields is `conjMultiplicity 0 τ`;
* `indexUpTo_lt_top`: `λ(τ) = Morse.indexUpTo hN γ hc τ < ⊤`. -/
def A : Prop :=
  type_of% @Morse.lemma_15_4.{0, 0, 0} ∧ type_of% @Morse.lemma_15_4_ker.{0, 0, 0} ∧
    type_of% @Morse.eq_jacobi_of_jumps_zero.{0, 0, 0} ∧
    type_of% @Morse.finrank_ker_broken.{0, 0, 0} ∧ type_of% @Morse.indexUpTo_lt_top.{0, 0, 0}

theorem A_holds : A :=
  ⟨@Morse.lemma_15_4, @Morse.lemma_15_4_ker, @Morse.eq_jacobi_of_jumps_zero,
    @Morse.finrank_ker_broken, @Morse.indexUpTo_lt_top⟩

/-! Neither `A → B` nor `B → A` is proved; see `V9_19.json`. The obstacles are those of V9_18:
B's `E_**` is the choice function `HessT 1 γ` of the variational relation `IsHessT` (Fréchet mixed
partial of `E ∘ α` for some 2-parameter variation, junk `0` when no variation realizes the pair),
A's is the formula-defined `energyHessian`; identifying them needs the missing joint `C²`
regularity of `u ↦ E(α(u))` (and Lemma 11.A, Theorem 13.1, a `TΩ` dictionary). B's subdivision is
Milnor's `FineSub`, A's is `IsFine` (pieces `≤ h₀`), and neither implies the other.

What does match is the linear algebra: below, for a bilinear form `H` and a subspace `T`, B's
`bIndex T H` is `Morse.formIndex (H.restrict T)` (`bIndex_eq_formIndex_restrict`) and B's nullity
`setDim (bNullSet T H)` is the rank of `ker (H.restrict T)` (`setDim_bNullSet_eq`); so B's two
equalities have the shape of A's `lemma_15_4` / `lemma_15_4_ker` once `HessT` is known to be a
bilinear form on `TΩ_γ` matching `energyHessian`.

## Linear algebra: the blind index and nullity on a subspace -/

section LinAlg

variable {E : Type} [AddCommGroup E] [Module ℝ E]

/-- B's index of a bilinear form on (the carrier of) a subspace `T` is the project's index of the
restricted form. -/
theorem bIndex_eq_formIndex_restrict (H : LinearMap.BilinForm ℝ E) (T : Submodule ℝ E) :
    bIndex (T : Set E) (fun x y => H x y) = Morse.formIndex (H.restrict T) := by
  refine le_antisymm (iSup₂_le fun S hS => ?_) (iSup₂_le fun S' hS' => iSup_le fun hneg => ?_)
  · -- `S ⊆ T`: pull back to a subspace of `T`
    obtain ⟨hST, hfin, hneg⟩ := hS
    have hle : S ≤ T := hST
    set S' : Submodule ℝ T := S.comap T.subtype
    have e : S' ≃ₗ[ℝ] S := Submodule.comapSubtypeEquivOfLe hle
    have : FiniteDimensional ℝ S' := LinearEquiv.finiteDimensional e.symm
    have hneg' : Morse.IsNegDefOn (H.restrict T) S' := by
      intro v hv hv0
      exact hneg (v : E) hv fun h => hv0 (Subtype.ext h)
    calc (finrank ℝ S : ℕ∞) = (finrank ℝ S' : ℕ∞) := by rw [e.finrank_eq]
      _ ≤ Morse.formIndex (H.restrict T) := Morse.le_formIndex hneg'
  · -- `S' ≤ T`: push forward
    set S : Submodule ℝ E := S'.map T.subtype
    have e : S' ≃ₗ[ℝ] S := Submodule.equivMapOfInjective _ T.injective_subtype S'
    have : FiniteDimensional ℝ S := LinearEquiv.finiteDimensional e
    have hST : (S : Set E) ⊆ T := by
      rintro _ ⟨v, -, rfl⟩
      exact v.2
    have hneg' : IsNegDefSub (fun x y => H x y) S := by
      rintro _ ⟨v, hv, rfl⟩ hv0
      exact hneg v hv fun h => hv0 (by rw [h]; rfl)
    calc (finrank ℝ S' : ℕ∞) = (finrank ℝ S : ℕ∞) := by rw [e.finrank_eq]
      _ ≤ bIndex (T : Set E) (fun x y => H x y) :=
        le_iSup₂_of_le (f := fun (S : Submodule ℝ E)
          (_ : (S : Set E) ⊆ T ∧ FiniteDimensional ℝ S ∧ IsNegDefSub (fun x y => H x y) S) =>
          (finrank ℝ S : ℕ∞)) S ⟨hST, inferInstance, hneg'⟩ le_rfl

/-- B's null set of `H` on a subspace `T` is the image of the kernel of the restricted form. -/
theorem bNullSet_eq_image_ker (H : LinearMap.BilinForm ℝ E) (T : Submodule ℝ E) :
    bNullSet (T : Set E) (fun x y => H x y) =
      ((LinearMap.ker (H.restrict T)).map T.subtype : Set E) := by
  ext v
  constructor
  · rintro ⟨hv, hnull⟩
    refine ⟨⟨v, hv⟩, ?_, rfl⟩
    show _ ∈ LinearMap.ker (H.restrict T)
    rw [LinearMap.mem_ker]
    ext w
    exact hnull w w.2
  · rintro ⟨v, hv, rfl⟩
    refine ⟨v.2, fun w hw => ?_⟩
    have hv' : H.restrict T v = 0 := LinearMap.mem_ker.1 hv
    exact LinearMap.congr_fun hv' ⟨w, hw⟩

/-- B's nullity of `H` on a subspace `T` is the rank of the kernel of the restricted form. -/
theorem setDim_bNullSet_eq (H : LinearMap.BilinForm ℝ E) (T : Submodule ℝ E) :
    setDim (bNullSet (T : Set E) (fun x y => H x y)) =
      (Module.rank ℝ (LinearMap.ker (H.restrict T))).toENat := by
  rw [setDim, bNullSet_eq_image_ker, Submodule.span_eq,
    (Submodule.equivMapOfInjective _ T.injective_subtype _).rank_eq.symm]

end LinAlg

#rt_check RoundTrip.V9_19.bIndex_eq_formIndex_restrict [Morse.lemma_15_4, Morse.lemma_15_4_ker,
  Morse.eq_jacobi_of_jumps_zero, Morse.finrank_ker_broken, Morse.indexUpTo_lt_top]
#rt_check RoundTrip.V9_19.setDim_bNullSet_eq [Morse.lemma_15_4, Morse.lemma_15_4_ker,
  Morse.eq_jacobi_of_jumps_zero, Morse.finrank_ker_broken, Morse.indexUpTo_lt_top]

/-! ## The embedded special case (stated, not proved) -/

/-- B on embedded manifolds: `M = ↥N` (model `ℝⁿ`, induced metric), induced connection. -/
def B_emb : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (W : Type) [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] (n : ℕ)
    (N : Set V) (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N)
    [ConnectedSpace (Bridge.Sub hN)] (γ : ℝ → Bridge.Sub hN),
    IsGeodesic (Bridge.conn (hN := hN)) γ (Set.Icc 0 1) →
  ∀ (k : ℕ) (t : ℕ → ℝ), FineSub (Bridge.conn (hN := hN)) γ 1 k t →
    bIndex (TOm (n := n) 1 γ) (HessT (n := n) 1 γ) =
        bIndex (BrokenSet (Bridge.conn (hN := hN)) γ 1 k t) (HessT (n := n) 1 γ) ∧
    setDim (bNullSet (TOm (n := n) 1 γ) (HessT (n := n) 1 γ)) =
        setDim (bNullSet (BrokenSet (Bridge.conn (hN := hN)) γ 1 k t) (HessT (n := n) 1 γ)) ∧
    bIndex (TOm (n := n) 1 γ) (HessT (n := n) 1 γ) ≠ ⊤

theorem B_to_B_emb : B → B_emb := fun hB _ _ _ _ _ _ _ _ n _ hN _ =>
  hB n (Bridge.Sub hN) (Bridge.conn (hN := hN)) Bridge.conn_isLC

end RoundTrip.V9_19
