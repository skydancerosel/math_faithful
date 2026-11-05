import Morse
import RoundTrip.Check
import RoundTrip.Blind.V9_23
import RoundTrip.Bridge
import RoundTrip.EnergyC2

namespace RoundTrip.V9_23

/-- The project's statement (universes instantiated at `0`; `exists_dual` has universes
`u_1 u_2 u_3` as well), for a slice submanifold `N ⊆ V` with the induced metric and ANY smooth
curve `γ` in `N` on `[0, 1]` (`Morse.IsSmoothCurveIn`, no geodesic hypothesis), with
`λ(τ) = Morse.indexUpTo hN γ hc τ` the index of `energyHessian` (the bilinear form DEFINED by the
second variation formula on `TΩ_γ`, for the whole of `[0, 1]`) restricted to the fields vanishing
outside `[0, τ]`, and `ν(τ) = conjMultiplicity hN γ hc 0 τ` (dimension of the Jacobi fields
vanishing at `0` and `τ`):
* `assertion_4_le`: eventually for `τ' → τ⁺`, `λ(τ') ≤ λ(τ) + ν(τ)`;
* `energyHessian_cut`: `E_**(J·1_{[0,τ]}, Y) = 2⟨Y(τ), DJ/dt(τ)⟩` for `J` Jacobi vanishing at `0, τ`;
* `exists_dual`: linearly independent tangent vectors at a point of `N` have a dual family;
* `assertion_4_ge`: `λ(τ) + ν(τ) ≤ λ(τ')` for EVERY `τ' ∈ (τ, 1]`;
* `assertion_4`: eventually for `τ' → τ⁺`, `λ(τ') = λ(τ) + ν(τ)`. -/
def A : Prop :=
  type_of% @Morse.assertion_4_le.{0, 0, 0} ∧
    type_of% @Morse.energyHessian_cut.{0, 0, 0} ∧
    type_of% @Morse.exists_dual.{0, 0, 0} ∧
    type_of% @Morse.assertion_4_ge.{0, 0, 0} ∧
    type_of% @Morse.assertion_4.{0, 0, 0}

theorem A_holds : A :=
  ⟨@Morse.assertion_4_le, @Morse.energyHessian_cut, @Morse.exists_dual, @Morse.assertion_4_ge,
    @Morse.assertion_4⟩

/-! Neither `A → B` nor `B → A` is proved, and the embedded special case is not closed either;
see `V9_23.json`. Besides the setting (abstract Riemannian manifolds with any Levi-Civita
connection vs slice submanifolds with the induced metric), the two sides use different `E_**`,
`λ` and `ν`:
* B's `E_**` is Milnor's variational one, `HessT τ γ W₁ W₂ = ∂²E_0^τ(α(u))/∂u₁∂u₂(0)` for a
  2-parameter variation `α` (Fréchet `mixedD`, joint differentiability required, junk `0` when no
  variation realizes the pair); A's `energyHessian` is the bilinear form defined by the second
  variation formula. Identifying them on `↥N` needs the Fréchet-`C²` regularity of
  `u ↦ E(α(u))` for variations smooth on strips, which the project does not have (as in `V8_13`,
  `V8_14`, `V9_5`), plus a variation dictionary.
* B's `λ(τ)` is the index of `(E_0^τ)_**` on `TΩ(γ|[0,τ])`; A's is the index of `(E_0^1)_**`
  restricted to the fields vanishing outside `[0, τ]` (the same by locality of the second
  variation formula, but only once the Hessians are identified).
* B's `ν` is the nullity of `(E_0^τ)_**` (dimension of the span of its null vectors in `TΩ`); A's
  is the conjugate multiplicity. They agree by Theorem 14.1, which itself needs the Hessian
  identification on `↥N` (cf. `V9_5`).
A also has content B lacks: `assertion_4_ge` for every `τ' > τ` (not only small `ε`), the cut-off
formula `energyHessian_cut`, `exists_dual`, and all of it for an arbitrary smooth curve. -/


/-! ## Second attempt (with `RoundTrip.EnergyC2`): the embedded special case

The shared §§13–15 Hessian dictionary of `Items/V8_13.lean` (copied in namespace `Emb`: blind
2-parameter variations ⇔ `Morse.IsVariation`, `D_varField`, `hess_data` from `EnergyC2`,
`hess_eq`, `exists_isHess`), the Jacobi-field dictionary and `toFA` of `Items/V9_4.lean`, and new
glue: `IsHessT 1 = IsHess`, `TΩ` project ⇒ blind (`inTOmegaT_toFA`), and `HessT 1 γ = 2
secondVariation` on `TΩ_γ` (`hessT_eq`, with Theorem 13.1 = `Morse.second_variation`, which is
not a theorem of this item). -/

open Set Filter Topology Function
open scoped ContDiff Manifold
open Bundle

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Emb

set_option linter.unusedSectionVars false

/-- `e₀, e₁ ∈ ℝ²`. -/
noncomputable abbrev e0 : Rn 2 := EuclideanSpace.single 0 (1 : ℝ)
noncomputable abbrev e1 : Rn 2 := EuclideanSpace.single 1 (1 : ℝ)

/-! ### Subdivisions (copied from `Items/V8_9.lean`, `Items/V8_10.lean`) -/

theorem exists_piece_of_mem {k : ℕ} {t : ℕ → ℝ} (h0 : t 0 = 0) (hk : t k = 1)
    (hlt : ∀ i < k, t i < t (i + 1)) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    ∃ i < k, s ∈ Icc (t i) (t (i + 1)) := by
  classical
  have hk0 : k ≠ 0 := by rintro rfl; rw [h0] at hk; exact zero_ne_one hk
  have hP : ∃ j, s ≤ t j ∧ j ≤ k := ⟨k, hk ▸ hs.2, le_rfl⟩
  have hm := Nat.find_spec hP
  by_cases hm0 : Nat.find hP = 0
  · refine ⟨0, Nat.pos_of_ne_zero hk0, ?_, ?_⟩
    · rw [h0]; exact hs.1
    · have : s ≤ t 0 := by rw [← hm0]; exact hm.1
      exact this.trans (hlt 0 (Nat.pos_of_ne_zero hk0)).le
  · refine ⟨Nat.find hP - 1, by omega, ?_, ?_⟩
    · by_contra hcon
      exact Nat.find_min hP (Nat.sub_lt (Nat.pos_of_ne_zero hm0) one_pos)
        ⟨(lt_of_not_ge hcon).le, by omega⟩
    · rw [Nat.sub_add_cancel (Nat.pos_of_ne_zero hm0)]; exact hm.1

theorem exists_piece_of_subdiv {t : ℕ → ℝ} {k : ℕ} (h0 : t 0 = 0) (hk : t k = 1)
    (hlt : ∀ i < k, t i < t (i + 1)) {s u : ℝ} (hs : 0 ≤ s) (hsu : s < u) (hub : u ≤ 1)
    (hB : ∀ x ∈ (Finset.range (k + 1)).image t, x ∉ Ioo s u) :
    ∃ i < k, t i ≤ s ∧ u ≤ t (i + 1) := by
  have hP : ∃ j, s < t j ∧ j ≤ k := ⟨k, by rw [hk]; linarith, le_rfl⟩
  classical
  set m := Nat.find hP
  have hm : s < t m ∧ m ≤ k := Nat.find_spec hP
  have hm0 : m ≠ 0 := by
    intro h; have := hm.1; rw [h, h0] at this; linarith
  have hi : t (m - 1) ≤ s := by
    by_contra hcon
    exact Nat.find_min hP (Nat.sub_lt (Nat.pos_of_ne_zero hm0) one_pos)
      ⟨lt_of_not_ge hcon, by omega⟩
  have hu : u ≤ t m := by
    by_contra hcon
    exact hB (t m) (Finset.mem_image.2 ⟨m, Finset.mem_range.2 (by omega), rfl⟩)
      ⟨hm.1, lt_of_not_ge hcon⟩
  have hm1 : m - 1 + 1 = m := Nat.sub_add_cancel (Nat.pos_of_ne_zero hm0)
  exact ⟨m - 1, by omega, hi, hm1.symm ▸ hu⟩

/-- A subdivision `0 = t₀ < ⋯ < t_k = 1` whose open pieces avoid a finite set `B`. -/
theorem exists_subdiv (B : Finset ℝ) : ∃ (k : ℕ) (t : ℕ → ℝ), t 0 = 0 ∧ t k = 1 ∧
    (∀ i < k, t i < t (i + 1)) ∧
    ∀ i < k, 0 ≤ t i ∧ t (i + 1) ≤ 1 ∧ ∀ x ∈ B, x ∉ Ioo (t i) (t (i + 1)) := by
  classical
  have hlt : (0 : ℝ) < 1 := zero_lt_one
  set a : ℝ := 0
  set b : ℝ := 1
  set S : Finset ℝ := insert a (insert b (B.filter (· ∈ Ioo a b)))
  have hS : ∀ x ∈ S, a ≤ x ∧ x ≤ b := by
    intro x hx
    simp only [S, Finset.mem_insert, Finset.mem_filter] at hx
    rcases hx with rfl | rfl | ⟨-, hx⟩
    · exact ⟨le_rfl, hlt.le⟩
    · exact ⟨hlt.le, le_rfl⟩
    · exact ⟨hx.1.le, hx.2.le⟩
  have haS : a ∈ S := Finset.mem_insert_self _ _
  have hbS : b ∈ S := Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  set m := S.card
  have hm : 1 < m := Finset.one_lt_card.2 ⟨a, haS, b, hbS, hlt.ne⟩
  set e := S.orderEmbOfFin rfl
  set t : ℕ → ℝ := fun j => if h : j < m then e ⟨j, h⟩ else b
  have ht : ∀ j (h : j < m), t j = e ⟨j, h⟩ := fun j h => dif_pos h
  refine ⟨m - 1, t, ?_, ?_, ?_, ?_⟩
  · rw [ht 0 (by omega), Finset.orderEmbOfFin_zero rfl (by omega)]
    exact le_antisymm (Finset.min'_le _ _ haS) ((hS _ (Finset.min'_mem _ _)).1)
  · rw [ht (m - 1) (by omega), Finset.orderEmbOfFin_last rfl (by omega)]
    exact le_antisymm ((hS _ (Finset.max'_mem _ _)).2) (Finset.le_max' _ _ hbS)
  · intro i hi
    rw [ht i (by omega), ht (i + 1) (by omega)]
    exact e.strictMono (Fin.mk_lt_mk.2 (Nat.lt_succ_self i))
  · intro i hi
    rw [ht i (by omega), ht (i + 1) (by omega)]
    refine ⟨(hS _ (Finset.orderEmbOfFin_mem _ _ _)).1, (hS _ (Finset.orderEmbOfFin_mem _ _ _)).2,
      fun x hx hxi => ?_⟩
    have hxS : x ∈ S := Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
      (Finset.mem_filter.2 ⟨hx, (hS _ (Finset.orderEmbOfFin_mem _ _ _)).1.trans_lt hxi.1,
        hxi.2.trans_le (hS _ (Finset.orderEmbOfFin_mem _ _ _)).2⟩))
    obtain ⟨j, rfl⟩ : x ∈ Set.range e := by
      rw [Finset.range_orderEmbOfFin]; exact hxS
    have h1 := e.lt_iff_lt.1 hxi.1
    have h2 := e.lt_iff_lt.1 hxi.2
    rw [Fin.lt_def] at h1 h2
    simp only at h1 h2
    omega

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] {n : ℕ} {N : Set V}
  {hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N}

/-! ### Maps into `↥N` (copied from `Items/V8_10.lean`, `Items/V8_12.lean`) -/

theorem contMDiffWithinAt_map_iff {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → Bridge.Sub hN} {s : Set E} {x : E} :
    ContMDiffWithinAt 𝓘(ℝ, E) 𝓘(ℝ, Rn n) ∞ f s x ↔
      ContDiffWithinAt ℝ ∞ (Bridge.incl hN ∘ f) s x := by
  constructor
  · intro h
    exact contMDiffWithinAt_iff_contDiffWithinAt.1
      ((Bridge.contMDiff_incl (f x)).comp_contMDiffWithinAt x h)
  · intro h
    have hcont : ContinuousWithinAt f s x :=
      (Topology.IsInducing.subtypeVal.continuousWithinAt_iff (f := f)).2 h.continuousWithinAt
    rw [contMDiffWithinAt_iff_target]
    refine ⟨hcont, ?_⟩
    set σ := Morse.sliceAt hN (f x)
    have hφ : ContDiffAt ℝ ∞ (fun y => (σ.φ y).1) (Bridge.incl hN (f x)) :=
      contDiff_fst.contDiffAt.comp _ ((Milnor.Problems.sliceChart_contDiffOn σ).contDiffAt
        (σ.φ.open_source.mem_nhds (Morse.mem_sliceAt_source hN (f x))))
    have e : (extChartAt 𝓘(ℝ, Rn n) (f x) ∘ f) =
        (fun y => (σ.φ y).1) ∘ (Bridge.incl hN ∘ f) := rfl
    rw [e]
    exact contMDiffWithinAt_iff_contDiffWithinAt.2 (hφ.comp_contDiffWithinAt x h)

theorem contMDiffOn_map_iff {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → Bridge.Sub hN} {s : Set E} :
    ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, Rn n) ∞ f s ↔ ContDiffOn ℝ ∞ (Bridge.incl hN ∘ f) s :=
  forall₂_congr fun _ _ => contMDiffWithinAt_map_iff

/-- The derivative of a map from a normed space into `N`, read in `V`. -/
theorem D_mfderiv_map {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → Bridge.Sub hN}
    {x : E} (hf : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, Rn n) f x) (v : E) :
    Bridge.D hN (f x) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, Rn n) f x v) = fderiv ℝ (Bridge.incl hN ∘ f) x v := by
  have h := HasMFDerivAt.comp x
    ((Bridge.contMDiff_incl (f x)).mdifferentiableAt (by simp)).hasMFDerivAt hf.hasMFDerivAt
  have h' : HasFDerivAt (Bridge.incl hN ∘ f)
      ((Bridge.D hN (f x)).comp (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, Rn n) f x : E →L[ℝ] Rn n)) x :=
    hasMFDerivAt_iff_hasFDerivAt.1 h
  have h'' : fderiv ℝ (Bridge.incl hN ∘ f) x =
      (Bridge.D hN (f x)).comp (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, Rn n) f x : E →L[ℝ] Rn n) :=
    HasFDerivAt.fderiv h'
  exact (DFunLike.congr_fun h'' v).symm

/-- A map into `N` that is `C^∞` at `x` when read in `V` has its derivative read in `V`. -/
theorem D_mfderiv_of_contDiffAt {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → Bridge.Sub hN} {x : E} (hf : ContDiffAt ℝ ∞ (Bridge.incl hN ∘ f) x) (v : E) :
    Bridge.D hN (f x) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, Rn n) f x v) = fderiv ℝ (Bridge.incl hN ∘ f) x v := by
  have : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, Rn n) ∞ f x := by
    rw [← contMDiffWithinAt_univ]
    exact contMDiffWithinAt_map_iff.2 (contDiffWithinAt_univ.2 hf)
  exact D_mfderiv_map (this.mdifferentiableAt (by simp)) v

/-! ### Paths, geodesics and `TΩ` -/

/-- A blind geodesic on `[0, 1]` (induced connection) is a project unbroken geodesic. -/
theorem isUnbrokenGeodesic_of_isGeodesic {pw : ℝ → Bridge.Sub hN}
    (h : IsGeodesic (Bridge.conn (hN := hN)) pw (Icc 0 1)) :
    Morse.IsUnbrokenGeodesic hN (Bridge.incl hN ∘ pw) := by
  have h' : RoundTrip.BridgePrelude.IsGeodesic (Bridge.conn (hN := hN)) pw (Icc 0 1) := h
  exact ⟨(Bridge.isGeodesic_iff.1 h').2.1, Bridge.isGeodesicOn_Ioo h'⟩

theorem mem_pathSpace_of_isGeodesic {pw : ℝ → Bridge.Sub hN}
    (h : IsGeodesic (Bridge.conn (hN := hN)) pw (Icc 0 1)) :
    Bridge.incl hN ∘ pw ∈ Morse.pathSpace N (Bridge.incl hN (pw 0)) (Bridge.incl hN (pw 1)) := by
  have hcd := (isUnbrokenGeodesic_of_isGeodesic h).1
  exact ⟨⟨zero_le_one, hcd.continuousOn, ∅, fun s u hs _ hu _ => hcd.mono (Icc_subset_Icc hs hu)⟩,
    fun t _ => (pw t).2, rfl, rfl⟩

/-- **Dictionary: `TΩ_γ`, blind ⇒ project.** The ambient field of a blind `W ∈ TΩ_γ` lies in
`Morse.pathTangent`. -/
theorem mem_pathTangent_of_inTOmega {γ : ℝ → Bridge.Sub hN} {X : FA n γ}
    (h : InTOmega (n := n) γ X) :
    Bridge.ambA γ X ∈ Morse.pathTangent hN (Bridge.incl hN ∘ γ) := by
  obtain ⟨⟨k, t, ht0, htk, hlt, -, hsm⟩, hX0, hX1⟩ := h
  have hsm' : ∀ i < k, ContDiffOn ℝ ∞ (Bridge.ambA γ X) (Icc (t i) (t (i + 1))) := fun i hi => by
    have h' : RoundTrip.BridgePrelude.IsSmoothAlong γ (Icc (t i) (t (i + 1))) X := hsm i hi
    exact (Bridge.isSmoothAlong_iff.1 h').2
  have hpiece : ∀ s u, 0 ≤ s → s < u → u ≤ 1 →
      (∀ x ∈ (Finset.range (k + 1)).image t, x ∉ Ioo s u) →
      ContDiffOn ℝ ∞ (Bridge.ambA γ X) (Icc s u) := by
    intro s u hs hsu hu hB
    obtain ⟨i, hi, hti, hui⟩ := exists_piece_of_subdiv ht0 htk hlt hs hsu hu hB
    exact (hsm' i hi).mono (Icc_subset_Icc hti hui)
  refine (Morse.mem_pathTangent hN).2 ⟨⟨zero_le_one, Morse.continuousOn_of_piecewise
    fun s u hs hsu hu hB => (hpiece s u hs hsu hu hB).continuousOn, _, hpiece⟩,
    fun τ _ => (Morse.prj_eq_self_iff hN (γ τ).2).2 (Bridge.D_mem (γ τ) (X τ)), ?_, ?_⟩
  · show Bridge.D hN (γ 0) (X 0) = 0
    rw [hX0]; exact map_zero _
  · show Bridge.D hN (γ 1) (X 1) = 0
    rw [hX1]; exact map_zero _

/-! ### 2-parameter variations -/

/-- The ambient family `(u, s) ↦ α(u, s) ∈ N ⊆ V`. -/
def amb {m : ℕ} (α : Rn m → ℝ → Bridge.Sub hN) : Rn m → ℝ → V := fun u s => Bridge.incl hN (α u s)

/-- **Dictionary: variations.** A blind `m`-parameter variation is a project `IsVariation`
(parameters in `U ⊆ ℝᵐ`, break points the subdivision points). -/
theorem isVariation_of_isVarSub {m : ℕ} {U : Set (Rn m)} {α : Rn m → ℝ → Bridge.Sub hN} {k : ℕ}
    {t : ℕ → ℝ} (h : IsVarSub (n := n) U α k t) :
    Morse.IsVariation N U (amb α) ((Finset.range (k + 1)).image t) := by
  obtain ⟨hU, h0U, ht0, htk, hlt, hend, hsm⟩ := h
  refine ⟨hU, h0U, fun _ _ _ _ => (α _ _).2, fun x hx => ?_, fun x hx => ?_,
    fun s u hs hsu hu hB => ?_⟩
  · show Bridge.incl hN (α x 0) = Bridge.incl hN (α 0 0)
    rw [(hend _ hx).2.1]
  · show Bridge.incl hN (α x 1) = Bridge.incl hN (α 0 1)
    rw [(hend _ hx).2.2]
  · obtain ⟨i, hi, hti, hui⟩ := exists_piece_of_subdiv ht0 htk hlt hs hsu hu hB
    exact (contMDiffOn_map_iff.1 (hsm i hi)).mono
      fun p hp => ⟨hp.1, hti.trans hp.2.1, hp.2.2.trans hui⟩

/-- **Dictionary: variation fields.** `Wᵢ = ∂α/∂uᵢ (0, τ)`, read in `V`, is the derivative along
the line `r ↦ r eᵢ`, for `τ ∈ [0, 1]`. -/
theorem D_varField {m : ℕ} {U : Set (Rn m)} {α : Rn m → ℝ → Bridge.Sub hN} {k : ℕ}
    {t : ℕ → ℝ} (hα : IsVarSub (n := n) U α k t) (i : Fin m) {τ : ℝ} (hτ : τ ∈ Icc (0 : ℝ) 1) :
    Bridge.D hN (α 0 τ) (varField (n := n) α i τ) =
      deriv (fun r : ℝ => amb α (r • EuclideanSpace.single i (1 : ℝ)) τ) 0 := by
  obtain ⟨hU, h0U, ht0, htk, hlt, -, hsm⟩ := hα
  obtain ⟨j, hj, hτj⟩ := exists_piece_of_mem ht0 htk hlt hτ
  have hG : ContDiffOn ℝ ∞ (Bridge.incl hN ∘ fun x : Rn m × ℝ => α x.1 x.2)
      (U ×ˢ Icc (t j) (t (j + 1))) := contMDiffOn_map_iff.1 (hsm j hj)
  have hcd : ContDiffAt ℝ ∞ (Bridge.incl hN ∘ fun u => α u τ) 0 :=
    (hG.comp (contDiff_id.prodMk contDiff_const).contDiffOn fun u hu => ⟨hu, hτj⟩).contDiffAt
      (hU.mem_nhds h0U)
  have h1 := D_mfderiv_of_contDiffAt hcd (EuclideanSpace.single i (1 : ℝ))
  have h2 := RoundTrip.EnergyC2.hasDerivAt_line (hcd.differentiableAt (by simp))
    (EuclideanSpace.single i (1 : ℝ))
  simp only [zero_add] at h2
  exact h1.trans h2.deriv.symm

/-- The blind energy of `α u` is the project energy of the ambient path. -/
theorem efun_eq {m : ℕ} (α : Rn m → ℝ → Bridge.Sub hN) :
    (fun v : Rn m => Efun (n := n) (α v)) = fun v => Morse.energy (amb α v) 0 1 :=
  funext fun v => Bridge.energy_eq (α v) 0 1

/-- **`E ∘ α` is `C²` (EnergyC2)**: the blind `DifferentiableAt` clause of `IsHess` holds for every
blind 2-parameter variation, and the blind `mixedD` is the project's iterated derivative
`∂/∂u₁ ∂/∂u₂ E(α(u₁ e₀ + u₂ e₁))` at `0`. -/
theorem hess_data {U : Set (Rn 2)} {α : Rn 2 → ℝ → Bridge.Sub hN} {k : ℕ} {t : ℕ → ℝ}
    (hα : IsVarSub (n := n) U α k t) :
    DifferentiableAt ℝ (fun u : Rn 2 => fderiv ℝ (fun v : Rn 2 => Efun (n := n) (α v)) u e0) 0 ∧
    mixedD (fun v : Rn 2 => Efun (n := n) (α v)) =
      deriv (fun s : ℝ => deriv (fun r : ℝ => Morse.energy (amb α (s • e0 + r • e1)) 0 1) 0) 0 := by
  have hvar := isVariation_of_isVarSub hα
  have hF : ContDiffOn ℝ 2 (fun v => Morse.energy (amb α v) 0 1) U :=
    hvar.contDiffOn_energy.of_le ENat.LEInfty.out
  rw [efun_eq]
  refine ⟨RoundTrip.EnergyC2.differentiableAt_fderiv_apply hvar.isOpen hF hvar.zero_mem e0, ?_⟩
  have h := RoundTrip.EnergyC2.fderiv_fderiv_apply_eq_deriv_deriv hvar.isOpen hF hvar.zero_mem
    e0 e1
  simp only [zero_add] at h
  exact h

/-- Theorem 13.1 for `N` (the statement of `Morse.second_variation`, or of
`Morse.hasDerivAt_energyHessian` unfolded), taken as a hypothesis. -/
def SV (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N) : Prop :=
  ∀ {γ : ℝ → V} {p q : V}, γ ∈ Morse.pathSpace N p q → Morse.IsUnbrokenGeodesic hN γ →
    ∀ {U : Set (ℝ × ℝ)} {α : ℝ × ℝ → ℝ → V} {B : Finset ℝ}, Morse.IsVariation N U α B →
    (∀ t ∈ Icc (0 : ℝ) 1, α 0 t = γ t) →
    HasDerivAt (fun u₁ => deriv (fun u₂ => Morse.energy (α (u₁, u₂)) 0 1) 0)
      (2 * Morse.secondVariation hN γ (fun t => deriv (fun u₁ => α (u₁, 0) t) 0)
        (fun t => deriv (fun u₂ => α (0, u₂) t) 0)) 0

/-- **Every blind `IsHess` value is `E_**` of the ambient fields** (Theorem 13.1 in Fréchet form
on `↥N`): `r = 2 secondVariation γ W₁ W₂`. -/
theorem hess_eq (hsv : SV hN) {γ : ℝ → Bridge.Sub hN}
    (hgeo : IsGeodesic (Bridge.conn (hN := hN)) γ (Icc 0 1)) {W₁ W₂ : FA n γ} {r : ℝ}
    (h : IsHess (n := n) γ W₁ W₂ r) :
    r = 2 * Morse.secondVariation hN (Bridge.incl hN ∘ γ) (Bridge.ambA γ W₁)
      (Bridge.ambA γ W₂) := by
  obtain ⟨U, α, ⟨k, t, hα⟩, rfl, hW₁, hW₂, -, hr⟩ := h
  have hvar := isVariation_of_isVarSub hα
  have hφ : ContDiff ℝ ∞ (fun p : ℝ × ℝ => p.1 • e0 + p.2 • e1) :=
    (contDiff_fst.smul contDiff_const).add (contDiff_snd.smul contDiff_const)
  have hφ0 : (fun p : ℝ × ℝ => p.1 • e0 + p.2 • e1) 0 ∈ U := by
    simpa using hvar.zero_mem
  have hvar2 := hvar.comp hφ hφ0
  have hαγ : ∀ τ ∈ Icc (0 : ℝ) 1,
      (fun p : ℝ × ℝ => amb α (p.1 • e0 + p.2 • e1)) 0 τ = (Bridge.incl hN ∘ α 0) τ := by
    intro τ _
    simp [amb]
  have hd := hsv (mem_pathSpace_of_isGeodesic hgeo) (isUnbrokenGeodesic_of_isGeodesic hgeo)
    hvar2 hαγ
  simp only [zero_smul, add_zero, zero_add] at hd
  rw [← hr, (hess_data hα).2, hd.deriv]
  congr 1
  refine Morse.secondVariation_congr hN (fun τ hτ => ?_) (fun τ hτ => ?_)
  · rw [Bridge.ambA, eq_of_heq (hW₁ τ), D_varField hα 0 hτ]
  · rw [Bridge.ambA, eq_of_heq (hW₂ τ), D_varField hα 1 hτ]

/-! ### Existence of `IsHess` values (Lemma 11.A on `↥N`, fields matched on all of `ℝ`) -/

/-- Near the zero section `exp` is smooth with `d(exp_q)₀ = id` (from `Morse.exists_isOpen_exp`
and `Morse.hasFDerivAt_exp_zero`), along any linear map into `T_qN`. -/
theorem exp_local {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] {q : V} (hq : q ∈ N)
    (Λ : P →L[ℝ] V) (hΛ : ∀ u, Morse.prj hN q (Λ u) = Λ u) :
    (∀ᶠ u in 𝓝 (0 : P), Morse.exp hN q (Λ u) ∈ N) ∧
    ContDiffAt ℝ ∞ (fun u => Morse.exp hN q (Λ u)) 0 ∧
    HasFDerivAt (fun u => Morse.exp hN q (Λ u)) Λ 0 := by
  obtain ⟨O, hO, hO0, hexp⟩ := Morse.exists_isOpen_exp (hN := hN)
  have hTN : ∀ u, (q, Λ u) ∈ Milnor.Problems.tangentBundleSet hN :=
    fun u => ⟨hq, (Morse.prj_eq_self_iff hN hq).1 (hΛ u)⟩
  have hc : Continuous (fun u : P => (q, Λ u)) := continuous_const.prodMk Λ.continuous
  have hq0 : (q, Λ 0) ∈ O := by rw [map_zero]; exact hO0 q hq
  have hev : ∀ᶠ u in 𝓝 (0 : P), (q, Λ u) ∈ O :=
    hc.continuousAt.preimage_mem_nhds (hO.mem_nhds hq0)
  refine ⟨?_, ?_, ?_⟩
  · filter_upwards [hev] with u hu
    exact Morse.exp_mem_of_mem_expDom (hexp _ hu (hTN u)).1
  · obtain ⟨-, F, O', hO', hzO', hF, hFeq⟩ := hexp _ hq0 (hTN 0)
    have h1 : ContDiffAt ℝ ∞ (fun u => F (q, Λ u)) 0 :=
      (hF.contDiffAt (hO'.mem_nhds hzO')).comp (0 : P)
        (contDiff_const.prodMk Λ.contDiff).contDiffAt
    refine h1.congr_of_eventuallyEq ?_
    filter_upwards [hc.continuousAt.preimage_mem_nhds (hO'.mem_nhds hzO')] with u hu
    exact hFeq _ hu (hTN u)
  · set qt : N := ⟨q, hq⟩
    let L : P →L[ℝ] Morse.tangentSubspace hN qt :=
      Λ.codRestrict (Morse.tangentSubspace hN qt) fun u =>
        (Morse.prj_eq_self_iff hN hq).1 (hΛ u)
    have h1 := Morse.hasFDerivAt_exp_zero (hN := hN) qt
    rw [← map_zero L] at h1
    have h2 := h1.comp (0 : P) L.hasFDerivAt
    have hL : ((Morse.tangentSubspace hN qt).subtypeL.comp L) = Λ :=
      ContinuousLinearMap.ext fun u => rfl
    rw [hL] at h2
    exact h2

open Classical in
/-- Milnor's `α(u, t) = exp_{γ(t)}(Λ(t) u)`, as a map into `↥N` (junk `γ t` where `exp` leaves
`N`, which does not happen near `u = 0`). -/
noncomputable def liftE (γ : ℝ → Bridge.Sub hN) (Λ : ℝ → Rn 2 →L[ℝ] V) (u : Rn 2) (t : ℝ) :
    Bridge.Sub hN :=
  if h : Morse.exp hN (Bridge.incl hN (γ t)) (Λ t u) ∈ N then (⟨_, h⟩ : N) else γ t

theorem liftE_of_mem {γ : ℝ → Bridge.Sub hN} {Λ : ℝ → Rn 2 →L[ℝ] V} {u : Rn 2} {t : ℝ}
    (h : Morse.exp hN (Bridge.incl hN (γ t)) (Λ t u) ∈ N) :
    liftE γ Λ u t = (⟨_, h⟩ : N) := by
  unfold liftE; exact dif_pos h

theorem incl_liftE {γ : ℝ → Bridge.Sub hN} {Λ : ℝ → Rn 2 →L[ℝ] V} {u : Rn 2} {t : ℝ}
    (h : Morse.exp hN (Bridge.incl hN (γ t)) (Λ t u) ∈ N) :
    Bridge.incl hN (liftE γ Λ u t) = Morse.exp hN (Bridge.incl hN (γ t)) (Λ t u) := by
  rw [liftE_of_mem h]; rfl

/-- **Existence of `E_**(W₁, W₂)` on `↥N`**: for a geodesic `γ` and blind `W₁, W₂ ∈ TΩ_γ` there is
a blind 2-parameter variation with fields `W₁, W₂` (at every `t ∈ ℝ`), hence an `IsHess` value. -/
theorem exists_isHess {γ : ℝ → Bridge.Sub hN}
    (hgeo : IsGeodesic (Bridge.conn (hN := hN)) γ (Icc 0 1)) {W₁ W₂ : FA n γ}
    (h₁ : InTOmega (n := n) γ W₁) (h₂ : InTOmega (n := n) γ W₂) :
    ∃ r, IsHess (n := n) γ W₁ W₂ r := by
  have hc := mem_pathSpace_of_isGeodesic hgeo
  obtain ⟨hXs₁, -, hX0₁, hX1₁⟩ := (Morse.mem_pathTangent hN).1 (mem_pathTangent_of_inTOmega h₁)
  obtain ⟨hXs₂, -, hX0₂, hX1₂⟩ := (Morse.mem_pathTangent hN).1 (mem_pathTangent_of_inTOmega h₂)
  set X₁ := Bridge.ambA γ W₁
  set X₂ := Bridge.ambA γ W₂
  set Λ : ℝ → Rn 2 →L[ℝ] V := fun t =>
    (EuclideanSpace.proj (0 : Fin 2) : Rn 2 →L[ℝ] ℝ).smulRight (X₁ t) +
      (EuclideanSpace.proj (1 : Fin 2) : Rn 2 →L[ℝ] ℝ).smulRight (X₂ t) with hΛdef
  have hΛapp : ∀ t u, Λ t u = u 0 • X₁ t + u 1 • X₂ t := fun t u => by
    simp [hΛdef]
  have hΛT : ∀ t u, Morse.prj hN (Bridge.incl hN (γ t)) (Λ t u) = Λ t u := fun t u =>
    (Morse.prj_eq_self_iff hN (γ t).2).2 (by
      rw [hΛapp]
      exact add_mem (Submodule.smul_mem _ _ (Bridge.D_mem (γ t) (W₁ t)))
        (Submodule.smul_mem _ _ (Bridge.D_mem (γ t) (W₂ t))))
  have hΛs : Morse.IsPiecewiseSmooth Λ 0 1 :=
    (hXs₁.smulRight (EuclideanSpace.proj (0 : Fin 2) : Rn 2 →L[ℝ] ℝ)).add
      (hXs₂.smulRight (EuclideanSpace.proj (1 : Fin 2) : Rn 2 →L[ℝ] ℝ))
  have hΛ0 : Λ 0 = 0 := ContinuousLinearMap.ext fun u => by
    rw [hΛapp]; simp [hX0₁, hX0₂]
  have hΛ1 : Λ 1 = 0 := ContinuousLinearMap.ext fun u => by
    rw [hΛapp]; simp [hX1₁, hX1₂]
  obtain ⟨ε, hε, B, hα, -, -⟩ := Morse.exists_variation hN hc (P := Rn 2) hΛs
    (fun t _ u => hΛT t u) hΛ0 hΛ1
  set α := liftE γ Λ
  have hinc : ∀ u ∈ Metric.ball (0 : Rn 2) ε, ∀ t ∈ Icc (0 : ℝ) 1,
      Bridge.incl hN (α u t) = Morse.exp hN (Bridge.incl hN (γ t)) (Λ t u) :=
    fun u hu t ht => incl_liftE (hα.mem u hu t ht)
  have hinj : Function.Injective (Bridge.incl hN) := Subtype.val_injective
  have hα0 : α 0 = γ := funext fun t => by
    have e : Morse.exp hN (Bridge.incl hN (γ t)) (Λ t 0) = Bridge.incl hN (γ t) := by
      rw [map_zero]; exact Morse.exp_zero (γ t).2
    exact hinj ((incl_liftE (γ := γ) (Λ := Λ) (u := 0) (t := t) (by rw [e]; exact (γ t).2)).trans e)
  -- the subdivision
  obtain ⟨k, tt, ht0, htk, hlt, hgood⟩ := exists_subdiv B
  have hstrip : ∀ i < k, ContMDiffOn 𝓘(ℝ, Rn 2 × ℝ) 𝓘(ℝ, Rn n) ∞
      (fun x : Rn 2 × ℝ => α x.1 x.2) (Metric.ball (0 : Rn 2) ε ×ˢ Icc (tt i) (tt (i + 1))) := by
    intro i hi
    obtain ⟨hi0, hi1, hiB⟩ := hgood i hi
    refine contMDiffOn_map_iff.2 ((hα.smooth _ _ hi0 (hlt i hi) hi1 hiB).congr fun p hp => ?_)
    exact hinc p.1 hp.1 p.2 ⟨hi0.trans hp.2.1, hp.2.2.trans hi1⟩
  have hvs : IsVarSub (n := n) (Metric.ball (0 : Rn 2) ε) α k tt := by
    refine ⟨Metric.isOpen_ball, Metric.mem_ball_self hε, ht0, htk, hlt, fun u hu => ⟨?_, ?_, ?_⟩,
      hstrip⟩
    · refine ⟨k, tt, ht0, htk, hlt, fun i hi => ?_⟩
      have hι : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, Rn 2 × ℝ) ∞ (fun s : ℝ => (u, s)) :=
        contMDiff_iff_contDiff.2 (contDiff_const.prodMk contDiff_id)
      exact (hstrip i hi).comp hι.contMDiffOn fun s hs => ⟨hu, hs⟩
    · refine hinj ?_
      rw [hinc u hu 0 ⟨le_rfl, zero_le_one⟩, hinc 0 (Metric.mem_ball_self hε) 0 ⟨le_rfl, zero_le_one⟩,
        hΛ0]
      rfl
    · refine hinj ?_
      rw [hinc u hu 1 ⟨zero_le_one, le_rfl⟩, hinc 0 (Metric.mem_ball_self hε) 1 ⟨zero_le_one, le_rfl⟩,
        hΛ1]
      rfl
  -- the variation fields, at every `t ∈ ℝ`
  have hfield : ∀ (i : Fin 2) (t : ℝ),
      Bridge.D hN (γ t) (varField (n := n) α i t) = Λ t (EuclideanSpace.single i (1 : ℝ)) := by
    intro i t
    obtain ⟨hmem, hcd, hfd⟩ := exp_local (hN := hN) (γ t).2 (Λ t) (hΛT t)
    have hev : (Bridge.incl hN ∘ fun u => α u t) =ᶠ[𝓝 0]
        fun u => Morse.exp hN (Bridge.incl hN (γ t)) (Λ t u) := by
      filter_upwards [hmem] with u hu
      exact incl_liftE hu
    have h1 := D_mfderiv_of_contDiffAt (hcd.congr_of_eventuallyEq hev)
      (EuclideanSpace.single i (1 : ℝ))
    have h2 := (hfd.congr_of_eventuallyEq hev).fderiv
    rw [h2] at h1
    calc Bridge.D hN (γ t) (varField (n := n) α i t)
        = Bridge.D hN (α 0 t) (varField (n := n) α i t) := by rw [congrFun hα0 t]
      _ = _ := h1
  have hW : ∀ (i : Fin 2) (Wi : FA n γ), (∀ t, Λ t (EuclideanSpace.single i (1 : ℝ)) =
      Bridge.D hN (γ t) (Wi t)) → ∀ t, HEq (Wi t) (varField (n := n) α i t) := by
    intro i Wi hWi t
    have := Bridge.D_injective (γ t) ((hfield i t).trans (hWi t))
    exact heq_of_eq this.symm
  refine ⟨_, Metric.ball (0 : Rn 2) ε, α, ⟨k, tt, hvs⟩, hα0,
    hW 0 W₁ fun t => by rw [hΛapp]; simp [X₁, Bridge.ambA],
    hW 1 W₂ fun t => by rw [hΛapp]; simp [X₂, Bridge.ambA], (hess_data hvs).1, rfl⟩

end Emb

namespace Emb

set_option linter.unusedSectionVars false

open RoundTrip.Bridge

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] {n : ℕ} {N : Set V}
  {hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Bridge.Rn n) W N}

theorem isIntv_Icc : RoundTrip.BridgePrelude.IsIntv (Icc (0 : ℝ) 1) :=
  ⟨ordConnected_Icc, uniqueDiffOn_Icc zero_lt_one⟩

theorem isSmoothCurveIn {γ : ℝ → Bridge.Sub hN} (hγ : IsSmoothCurve (n := n) γ (Icc 0 1)) :
    Morse.IsSmoothCurveIn hN (incl hN ∘ γ) :=
  ⟨isSmoothCurve_iff.1 hγ, fun t _ => (γ t).2⟩

theorem prj_incl (x : Bridge.Sub hN) : Morse.prj hN (incl hN x) = P hN x :=
  Morse.prj_of_mem hN x.2

theorem tangent_ambA {γ : ℝ → Bridge.Sub hN} (J : FA n γ) (t : ℝ) :
    Morse.prj hN ((incl hN ∘ γ) t) (ambA γ J t) = ambA γ J t := by
  show Morse.prj hN (incl hN (γ t)) (D hN (γ t) (J t)) = D hN (γ t) (J t)
  rw [prj_incl]
  exact P_D _ _

theorem contDiffOn_P {γ : ℝ → Bridge.Sub hN} (hγ : IsSmoothCurve (n := n) γ (Icc 0 1)) :
    ContDiffOn ℝ ∞ (fun t => P hN (γ t)) (Icc 0 1) := by
  have := (isSmoothCurveIn hγ).contDiffOn_prj
  refine this.congr fun t _ => ?_
  exact (prj_incl (γ t)).symm

/-- For a field `X` smooth on `[0,1]`, `covD` (two-sided derivative) agrees near interior points
with `P (derivWithin X [0,1])`. -/
theorem covD_eventuallyEq {γ : ℝ → Bridge.Sub hN} {X : ℝ → V} {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    Morse.covD hN (incl hN ∘ γ) X =ᶠ[𝓝 t]
      fun τ => P hN (γ τ) (derivWithin X (Icc 0 1) τ) := by
  filter_upwards [isOpen_Ioo.mem_nhds ht] with τ hτ
  show Morse.prj hN (incl hN (γ τ)) (deriv X τ) = _
  rw [prj_incl, derivWithin_of_mem_nhds (Icc_mem_nhds hτ.1 hτ.2)]

/-- **Dictionary: Jacobi fields.** For a smooth curve `γ` in `N` on `[0, 1]`, a blind Jacobi field
of the induced connection (`IsJacobi`, Milnor's equation with curvature `IsCurvVal`, on the closed
interval with derivatives within `[0,1]`) is exactly a project Jacobi field (`Morse.IsJacobiField`)
read in `V`. -/
theorem isJacobi_iff {γ : ℝ → Bridge.Sub hN} (hγ : IsSmoothCurve (n := n) γ (Icc 0 1))
    (J : FA n γ) :
    IsJacobi (conn (hN := hN)) γ (Icc 0 1) J ↔ Morse.IsJacobiField hN (incl hN ∘ γ) (ambA γ J) := by
  have hc := isSmoothCurveIn hγ
  have hγ' : RoundTrip.BridgePrelude.IsSmoothCurve (n := n) γ (Icc 0 1) := hγ
  have u : UniqueDiffOn ℝ (Icc (0 : ℝ) 1) := uniqueDiffOn_Icc zero_lt_one
  have hvel : ∀ t ∈ Icc (0 : ℝ) 1, D hN (γ t) (vel (n := n) γ (Icc 0 1) t) =
      Morse.velAlong (incl hN ∘ γ) t := fun t ht => D_vel hγ' u ht
  constructor
  · rintro ⟨J', J'', h1, h2, h3⟩
    have h1' := (hasCovDeriv_iff' isIntv_Icc hγ').1 h1
    have h2' := (hasCovDeriv_iff' isIntv_Icc hγ').1 h2
    refine ⟨(isSmoothAlong_iff.1 h1'.1).2, fun t _ => tangent_ambA J t, fun t ht => ?_⟩
    have ht' := Ioo_subset_Icc_self ht
    have e1 : Morse.covD hN (incl hN ∘ γ) (ambA γ J) =ᶠ[𝓝 t] ambA γ J' := by
      filter_upwards [covD_eventuallyEq (γ := γ) (X := ambA γ J) ht,
        isOpen_Ioo.mem_nhds ht] with τ hτ hτ'
      rw [hτ, h1'.2 τ (Ioo_subset_Icc_self hτ')]
    have e2 : Morse.covD hN (incl hN ∘ γ) (Morse.covD hN (incl hN ∘ γ) (ambA γ J)) t =
        ambA γ J'' t := by
      show Morse.prj hN (incl hN (γ t)) (deriv _ t) = _
      rw [prj_incl, e1.deriv_eq, ← derivWithin_of_mem_nhds (Icc_mem_nhds ht.1 ht.2),
        h2'.2 t ht']
    obtain ⟨r, hr, hr0⟩ := h3 t ht'
    have hr' := (isCurvVal_iff (γ t) _ _ _ r).1 hr
    have hd : deriv (incl hN ∘ γ) t = D hN (γ t) (vel (n := n) γ (Icc 0 1) t) := by
      rw [hvel t ht', hc.velAlong_eq ht]
    rw [Morse.jacobiExpr, e2, hd]
    show D hN (γ t) (J'' t) + Morse.curvR hN (incl hN (γ t)) _ (D hN (γ t) (J t)) _ = 0
    rw [← hr', ← D_tadd, hr0, D_tzero]
  · intro hX
    have hXs : IsSmoothAlong γ (Icc 0 1) J := isSmoothAlong_iff.2 ⟨hγ', hX.contDiffOn⟩
    have hdX : ContDiffOn ℝ ∞ (derivWithin (ambA γ J) (Icc 0 1)) (Icc 0 1) :=
      hX.contDiffOn.derivWithin u (by simp)
    have hamb1 : ambA γ (covA γ (Icc 0 1) J) =
        fun t => P hN (γ t) (derivWithin (ambA γ J) (Icc 0 1) t) := funext fun t => D_covA _ _ _ _
    have hJ's : IsSmoothAlong γ (Icc 0 1) (covA γ (Icc 0 1) J) := by
      refine isSmoothAlong_iff.2 ⟨hγ', ?_⟩
      rw [hamb1]
      exact (contDiffOn_P hγ).clm_apply hdX
    set J' := covA γ (Icc 0 1) J
    set J'' := covA γ (Icc 0 1) J'
    have hamb2 : ambA γ J'' = fun t => P hN (γ t) (derivWithin (ambA γ J') (Icc 0 1) t) :=
      funext fun t => D_covA _ _ _ _
    refine ⟨J', J'', (hasCovDeriv_iff isIntv_Icc hγ').2 ⟨hXs, fun _ _ => rfl⟩,
      (hasCovDeriv_iff isIntv_Icc hγ').2 ⟨hJ's, fun _ _ => rfl⟩, fun t ht => ?_⟩
    -- the curvature term
    set F : ℝ → V := fun τ => Morse.curvR hN (incl hN (γ τ)) (Morse.velAlong (incl hN ∘ γ) τ)
      (ambA γ J τ) (Morse.velAlong (incl hN ∘ γ) τ)
    have hFmem : F t ∈ Morse.tangentSubspace hN (γ t) := by
      show Morse.curvR hN (γ t).1 _ _ _ ∈ _
      rw [Morse.curvR_of_mem hN (γ t).2]
      rw [← hvel t ht]
      exact Morse.curvOp_mem hN (D_mem _ _) (D_mem _ _) (D_mem _ _)
    refine ⟨L hN (γ t) (F t), (isCurvVal_iff (γ t) _ _ _ _).2 ?_, ?_⟩
    · rw [D_L hFmem, hvel t ht]
      rfl
    · apply D_injective (γ t)
      refine (D_tadd (γ t) (J'' t) (L hN (γ t) (F t))).trans ?_
      rw [D_L hFmem, D_tzero]
      -- `G = D/dt(DJ/dt) + R(V, J)V` read in `V` is continuous on `[0,1]` and zero on `(0,1)`
      set G : ℝ → V := fun τ => ambA γ J'' τ + F τ
      have hGc : ContinuousOn G (Icc 0 1) := by
        have hJ'c : ContDiffOn ℝ ∞ (ambA γ J') (Icc 0 1) := (isSmoothAlong_iff.1 hJ's).2
        have h1 : ContinuousOn (ambA γ J'') (Icc 0 1) := by
          rw [hamb2]
          exact ((contDiffOn_P hγ).clm_apply (hJ'c.derivWithin u (m := ∞) (by simp))).continuousOn
        have h2 : ContinuousOn F (Icc 0 1) := by
          have := (hc.contDiffOn_curvAlong.clm_apply hX.contDiffOn).continuousOn
          refine this.congr fun τ hτ => ?_
          show F τ = Morse.curvAlong hN (incl hN ∘ γ) τ (ambA γ J τ)
          rw [Morse.curvAlong_apply (γ τ).2, tangent_ambA]
          rfl
        exact h1.add h2
      have hG0 : EqOn G 0 (Ioo 0 1) := by
        intro τ hτ
        have hτ' := Ioo_subset_Icc_self hτ
        have e1 : Morse.covD hN (incl hN ∘ γ) (ambA γ J) =ᶠ[𝓝 τ] ambA γ J' := by
          filter_upwards [covD_eventuallyEq (γ := γ) (X := ambA γ J) hτ,
            isOpen_Ioo.mem_nhds hτ] with x hx hx'
          rw [hx, hamb1]
        have e2 : Morse.covD hN (incl hN ∘ γ) (Morse.covD hN (incl hN ∘ γ) (ambA γ J)) τ =
            ambA γ J'' τ := by
          show Morse.prj hN (incl hN (γ τ)) (deriv _ τ) = _
          rw [prj_incl, e1.deriv_eq, ← derivWithin_of_mem_nhds (Icc_mem_nhds hτ.1 hτ.2), hamb2]
        have := hX.eq τ hτ
        rw [Morse.jacobiExpr, e2, ← hc.velAlong_eq hτ] at this
        exact this
      have := hG0.of_subset_closure hGc continuousOn_const Ioo_subset_Icc_self
        (by rw [closure_Ioo zero_ne_one]) ht
      exact this

open Classical in
/-- A blind field along `γ` from an ambient field `X`: `t ↦ L_{γ t}(X t)` on `[0,1]`, `0` outside. -/
noncomputable def toFA (γ : ℝ → Bridge.Sub hN) (X : ℝ → V) : FA n γ :=
  fun t => if t ∈ Icc (0 : ℝ) 1 then L hN (γ t) (X t) else 0

theorem toFA_of_mem {γ : ℝ → Bridge.Sub hN} (X : ℝ → V) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    toFA γ X t = L hN (γ t) (X t) := by
  unfold toFA
  exact if_pos ht

theorem toFA_of_not_mem {γ : ℝ → Bridge.Sub hN} (X : ℝ → V) {t : ℝ} (ht : t ∉ Icc (0 : ℝ) 1) :
    toFA γ X t = 0 := by
  unfold toFA
  exact if_neg ht

theorem ambA_toFA {γ : ℝ → Bridge.Sub hN} {X : ℝ → V}
    (hX : ∀ t ∈ Icc (0 : ℝ) 1, Morse.prj hN ((incl hN ∘ γ) t) (X t) = X t) :
    EqOn (ambA γ (toFA γ X)) X (Icc 0 1) := fun t ht => by
  show D hN (γ t) (toFA γ X t) = X t
  rw [toFA_of_mem X ht]
  exact D_L ((Morse.prj_eq_self_iff hN (γ t).2).1 (hX t ht))

/-- `toFA` as a linear map. -/
noncomputable def toFAₗ (γ : ℝ → Bridge.Sub hN) : (ℝ → V) →ₗ[ℝ] FA n γ where
  toFun := toFA γ
  map_add' X Y := by
    funext t
    by_cases ht : t ∈ Icc (0 : ℝ) 1
    · show toFA γ (X + Y) t = toFA γ X t + toFA γ Y t
      rw [toFA_of_mem _ ht, toFA_of_mem _ ht, toFA_of_mem _ ht]
      exact map_add (L hN (γ t)) (X t) (Y t)
    · show toFA γ (X + Y) t = toFA γ X t + toFA γ Y t
      rw [toFA_of_not_mem _ ht, toFA_of_not_mem _ ht, toFA_of_not_mem _ ht, add_zero]
  map_smul' c X := by
    funext t
    by_cases ht : t ∈ Icc (0 : ℝ) 1
    · show toFA γ (c • X) t = c • toFA γ X t
      rw [toFA_of_mem _ ht, toFA_of_mem _ ht]
      exact map_smul (L hN (γ t)) c (X t)
    · show toFA γ (c • X) t = c • toFA γ X t
      rw [toFA_of_not_mem _ ht, toFA_of_not_mem _ ht, smul_zero]

theorem toFA_mem_JacOn {γ : ℝ → Bridge.Sub hN} (hγ : IsSmoothCurve (n := n) γ (Icc 0 1)) {X : ℝ → V}
    (hX : Morse.IsJacobiField hN (incl hN ∘ γ) X) :
    toFA γ X ∈ JacOn (conn (hN := hN)) γ (Icc 0 1) :=
  ⟨(isJacobi_iff hγ _).2 (hX.congr fun t ht => (ambA_toFA hX.tangent ht).symm),
    fun t ht => toFA_of_not_mem X ht⟩

/-- On fields tangent along `γ` on `[0,1]` and constant off `[0,1]`, `toFA` is injective. -/
theorem toFA_injOn {γ : ℝ → Bridge.Sub hN} {X Y : ℝ → V}
    (hX : ∀ t ∈ Icc (0 : ℝ) 1, Morse.prj hN ((incl hN ∘ γ) t) (X t) = X t)
    (hY : ∀ t ∈ Icc (0 : ℝ) 1, Morse.prj hN ((incl hN ∘ γ) t) (Y t) = Y t)
    (h : toFA γ X = toFA γ Y) : EqOn X Y (Icc 0 1) := fun t ht => by
  rw [← ambA_toFA hX ht, ← ambA_toFA hY ht, h]

theorem eq_of_eqOn_jacobiSpace {c : ℝ → V} {hc : Morse.IsSmoothCurveIn hN c} {X Y : ℝ → V}
    (hX : X ∈ Morse.jacobiSpace hN c hc) (hY : Y ∈ Morse.jacobiSpace hN c hc)
    (h : EqOn X Y (Icc 0 1)) : X = Y := by
  funext t
  rw [hX.2 t, hY.2 t]
  exact h (projIcc (0 : ℝ) 1 zero_le_one t).2

end Emb

/-! ### Batch-5 additions: `IsHessT 1` is `IsHess`, `TΩ` project ⇒ blind, and
`HessT 1 γ = 2 secondVariation` on `TΩ_γ` -/

namespace Emb

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] {n : ℕ} {N : Set V}
  {hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N}

/-- Theorem 13.1 (`Morse.second_variation`, not a theorem of this item) in the form `SV`. -/
theorem sv_holds : SV hN := by
  intro _ _ _ _ hub _ _ _ hβ hβγ
  exact Morse.second_variation hN hub hβ hβγ

/-- For `τ = 1`, the batch-5 relation `IsHessT 1` is the batch-4 `IsHess`. -/
theorem isHessT_one_iff {γ : ℝ → Bridge.Sub hN} {W₁ W₂ : FA n γ} {r : ℝ} :
    IsHessT (n := n) 1 γ W₁ W₂ r ↔ IsHess (n := n) γ W₁ W₂ r := by
  constructor
  · rintro ⟨U, α, k, t, hα, h0, h1, h2, h3, h4⟩
    exact ⟨U, α, ⟨k, t, hα⟩, h0, h1, h2, h3, h4⟩
  · rintro ⟨U, α, ⟨k, t, hα⟩, h0, h1, h2, h3, h4⟩
    exact ⟨U, α, k, t, hα, h0, h1, h2, h3, h4⟩

theorem inTOmega_of_T {γ : ℝ → Bridge.Sub hN} {X : FA n γ} (h : InTOmegaT (n := n) 1 γ X) :
    InTOmega (n := n) γ X :=
  ⟨h.1, h.2.1, h.2.2.1⟩

/-- Continuity on `[0, t_k]` from continuity on the closed pieces of a subdivision. -/
theorem continuousOn_of_pieces {β : Type*} [TopologicalSpace β] {f : ℝ → β} {t : ℕ → ℝ}
    (ht0 : t 0 = 0) : ∀ {k : ℕ}, (∀ i < k, t i < t (i + 1)) →
    (∀ i < k, ContinuousOn f (Icc (t i) (t (i + 1)))) → ContinuousOn f (Icc 0 (t k))
  | 0, _, _ => by rw [ht0, Icc_self]; exact continuousOn_singleton f 0
  | k + 1, hlt, h => by
    have hlt' : ∀ i < k, t i < t (i + 1) := fun i hi => hlt i (by omega)
    have h0k : 0 ≤ t k := ht0 ▸ Bridge.le_of_strictSeq hlt' (Nat.zero_le k) le_rfl
    rw [← Icc_union_Icc_eq_Icc h0k (hlt k (by omega)).le]
    exact (continuousOn_of_pieces ht0 hlt' fun i hi => h i (by omega)).union_of_isClosed
      (h k (by omega)) isClosed_Icc isClosed_Icc

/-- **Dictionary: `TΩ_γ`, project ⇒ blind.** For a field `X ∈ TΩ` of the project along
`incl ∘ γ`, the blind field `toFA γ X` (`L X` on `[0,1]`, `0` outside) lies in the blind `TΩ_γ`. -/
theorem inTOmegaT_toFA {γ : ℝ → Bridge.Sub hN} (hγ : IsSmoothCurve (n := n) γ (Icc 0 1))
    {X : ℝ → V} (hX : X ∈ Morse.pathTangent hN (Bridge.incl hN ∘ γ)) :
    InTOmegaT (n := n) 1 γ (toFA γ X) := by
  obtain ⟨⟨-, -, B, hB⟩, hT, hX0, hX1⟩ := (Morse.mem_pathTangent hN).1 hX
  obtain ⟨k, t, ht0, htk, hlt, hgood⟩ := exists_subdiv B
  have hsm : ∀ i < k, IsSmoothAlong γ (Icc (t i) (t (i + 1))) (toFA γ X) := by
    intro i hi
    obtain ⟨h0i, hi1, hBi⟩ := hgood i hi
    have hsub : Icc (t i) (t (i + 1)) ⊆ Icc 0 1 := Icc_subset_Icc h0i hi1
    exact Bridge.isSmoothAlong_iff.2 ⟨ContMDiffOn.mono hγ hsub,
      (hB _ _ h0i (hlt i hi) hi1 hBi).congr fun s hs => ambA_toFA hT (hsub hs)⟩
  refine ⟨⟨k, t, ht0, htk, hlt, ?_, hsm⟩, ?_, ?_, fun s hs => toFA_of_not_mem X hs⟩
  · rw [← htk]
    exact continuousOn_of_pieces ht0 hlt fun i hi => ContMDiffOn.continuousOn (hsm i hi)
  · rw [toFA_of_mem X ⟨le_rfl, zero_le_one⟩, hX0, map_zero]; rfl
  · rw [toFA_of_mem X ⟨zero_le_one, le_rfl⟩, hX1, map_zero]; rfl

/-- **`E_**` on `TΩ_γ`, blind ⇒ project, with existence**: for a geodesic `γ` of `↥N` and blind
`W₁, W₂ ∈ TΩ_γ`, the variational `E_**` (`IsHessT 1`) has the value `2 secondVariation` of the
ambient fields (Lemma 11.A, `EnergyC2`, Theorem 13.1). -/
theorem isHessT_two_sv {γ : ℝ → Bridge.Sub hN}
    (hgeo : IsGeodesic (Bridge.conn (hN := hN)) γ (Icc 0 1)) {W₁ W₂ : FA n γ}
    (h₁ : InTOmegaT (n := n) 1 γ W₁) (h₂ : InTOmegaT (n := n) 1 γ W₂) :
    IsHessT (n := n) 1 γ W₁ W₂
      (2 * Morse.secondVariation hN (Bridge.incl hN ∘ γ) (Bridge.ambA γ W₁) (Bridge.ambA γ W₂)) := by
  obtain ⟨r, hr⟩ := exists_isHess hgeo (inTOmega_of_T h₁) (inTOmega_of_T h₂)
  rw [← hess_eq sv_holds hgeo hr]
  exact isHessT_one_iff.2 hr

/-- **Uniqueness**: every `IsHessT 1` value is `2 secondVariation` of the ambient fields. -/
theorem isHessT_iff {γ : ℝ → Bridge.Sub hN}
    (hgeo : IsGeodesic (Bridge.conn (hN := hN)) γ (Icc 0 1)) {W₁ W₂ : FA n γ}
    (h₁ : InTOmegaT (n := n) 1 γ W₁) (h₂ : InTOmegaT (n := n) 1 γ W₂) {r : ℝ} :
    IsHessT (n := n) 1 γ W₁ W₂ r ↔
      r = 2 * Morse.secondVariation hN (Bridge.incl hN ∘ γ) (Bridge.ambA γ W₁) (Bridge.ambA γ W₂) :=
  ⟨fun h => hess_eq sv_holds hgeo (isHessT_one_iff.1 h), fun h => h ▸ isHessT_two_sv hgeo h₁ h₂⟩

/-- **The choice function `HessT 1 γ` is `2 secondVariation`** on `TΩ_γ`. -/
theorem hessT_eq {γ : ℝ → Bridge.Sub hN}
    (hgeo : IsGeodesic (Bridge.conn (hN := hN)) γ (Icc 0 1)) {W₁ W₂ : FA n γ}
    (h₁ : InTOmegaT (n := n) 1 γ W₁) (h₂ : InTOmegaT (n := n) 1 γ W₂) :
    HessT (n := n) 1 γ W₁ W₂ =
      2 * Morse.secondVariation hN (Bridge.incl hN ∘ γ) (Bridge.ambA γ W₁) (Bridge.ambA γ W₂) := by
  have hex : ∃ r, IsHessT (n := n) 1 γ W₁ W₂ r := ⟨_, isHessT_two_sv hgeo h₁ h₂⟩
  unfold HessT
  rw [dif_pos hex]
  exact (isHessT_iff hgeo h₁ h₂).1 hex.choose_spec

end Emb

/-! ### `E_0^τ` on `↥N`: the batch-5 `IsHessT τ` for `0 < τ ≤ 1`

A blind variation of `γ|[0, τ]` (`IsVarSubT τ`) is extended by `γ = α 0` on `[τ, 1]` to a project
variation `extA τ α` of `γ` on `[0, 1]` (break points: the subdivision and `τ`); its energy `E_0^1`
differs from the blind `E_0^τ` by the constant `E_τ^1(γ)` (`energy_extA`), so `EnergyC2` and
Theorem 13.1 apply (`hessT_data`). With the `TΩ(γ|[0,τ])` dictionary (blind `TOm τ` = the
project's `fieldsUpTo τ`) every `IsHessT τ` value is `2 secondVariation` of the ambient fields
(`hessT_eqT`) and one exists (`exists_isHessT`). -/

namespace Emb

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] {n : ℕ} {N : Set V}
  {hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N}

/-! #### Subdivisions of `[0, τ]` -/

theorem exists_piece_of_memT {τ : ℝ} (hτ : 0 < τ) {k : ℕ} {t : ℕ → ℝ} (h0 : t 0 = 0)
    (hk : t k = τ) (hlt : ∀ i < k, t i < t (i + 1)) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) τ) :
    ∃ i < k, s ∈ Icc (t i) (t (i + 1)) := by
  classical
  have hk0 : k ≠ 0 := by rintro rfl; rw [h0] at hk; exact hτ.ne hk
  have hP : ∃ j, s ≤ t j ∧ j ≤ k := ⟨k, hk ▸ hs.2, le_rfl⟩
  have hm := Nat.find_spec hP
  by_cases hm0 : Nat.find hP = 0
  · refine ⟨0, Nat.pos_of_ne_zero hk0, ?_, ?_⟩
    · rw [h0]; exact hs.1
    · have : s ≤ t 0 := by rw [← hm0]; exact hm.1
      exact this.trans (hlt 0 (Nat.pos_of_ne_zero hk0)).le
  · refine ⟨Nat.find hP - 1, by omega, ?_, ?_⟩
    · by_contra hcon
      exact Nat.find_min hP (Nat.sub_lt (Nat.pos_of_ne_zero hm0) one_pos)
        ⟨(lt_of_not_ge hcon).le, by omega⟩
    · rw [Nat.sub_add_cancel (Nat.pos_of_ne_zero hm0)]; exact hm.1

theorem exists_piece_of_subdivT {τ : ℝ} {t : ℕ → ℝ} {k : ℕ} (h0 : t 0 = 0) (hk : t k = τ)
    (hlt : ∀ i < k, t i < t (i + 1)) {s u : ℝ} (hs : 0 ≤ s) (hsu : s < u) (hub : u ≤ τ)
    (hB : ∀ x ∈ (Finset.range (k + 1)).image t, x ∉ Ioo s u) :
    ∃ i < k, t i ≤ s ∧ u ≤ t (i + 1) := by
  have hP : ∃ j, s < t j ∧ j ≤ k := ⟨k, by rw [hk]; linarith, le_rfl⟩
  classical
  set m := Nat.find hP
  have hm : s < t m ∧ m ≤ k := Nat.find_spec hP
  have hm0 : m ≠ 0 := by
    intro h; have := hm.1; rw [h, h0] at this; linarith
  have hi : t (m - 1) ≤ s := by
    by_contra hcon
    exact Nat.find_min hP (Nat.sub_lt (Nat.pos_of_ne_zero hm0) one_pos)
      ⟨lt_of_not_ge hcon, by omega⟩
  have hu : u ≤ t m := by
    by_contra hcon
    exact hB (t m) (Finset.mem_image.2 ⟨m, Finset.mem_range.2 (by omega), rfl⟩)
      ⟨hm.1, lt_of_not_ge hcon⟩
  have hm1 : m - 1 + 1 = m := Nat.sub_add_cancel (Nat.pos_of_ne_zero hm0)
  exact ⟨m - 1, by omega, hi, hm1.symm ▸ hu⟩

/-- A subdivision `0 = t₀ < ⋯ < t_k = τ` whose open pieces avoid a finite set `B`. -/
theorem exists_subdivT {τ : ℝ} (hτ : 0 < τ) (B : Finset ℝ) : ∃ (k : ℕ) (t : ℕ → ℝ), t 0 = 0 ∧
    t k = τ ∧ (∀ i < k, t i < t (i + 1)) ∧
    ∀ i < k, 0 ≤ t i ∧ t (i + 1) ≤ τ ∧ ∀ x ∈ B, x ∉ Ioo (t i) (t (i + 1)) := by
  classical
  have hlt : (0 : ℝ) < τ := hτ
  set a : ℝ := 0
  set b : ℝ := τ
  set S : Finset ℝ := insert a (insert b (B.filter (· ∈ Ioo a b)))
  have hS : ∀ x ∈ S, a ≤ x ∧ x ≤ b := by
    intro x hx
    simp only [S, Finset.mem_insert, Finset.mem_filter] at hx
    rcases hx with rfl | rfl | ⟨-, hx⟩
    · exact ⟨le_rfl, hlt.le⟩
    · exact ⟨hlt.le, le_rfl⟩
    · exact ⟨hx.1.le, hx.2.le⟩
  have haS : a ∈ S := Finset.mem_insert_self _ _
  have hbS : b ∈ S := Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  set m := S.card
  have hm : 1 < m := Finset.one_lt_card.2 ⟨a, haS, b, hbS, hlt.ne⟩
  set e := S.orderEmbOfFin rfl
  set t : ℕ → ℝ := fun j => if h : j < m then e ⟨j, h⟩ else b
  have ht : ∀ j (h : j < m), t j = e ⟨j, h⟩ := fun j h => dif_pos h
  refine ⟨m - 1, t, ?_, ?_, ?_, ?_⟩
  · rw [ht 0 (by omega), Finset.orderEmbOfFin_zero rfl (by omega)]
    exact le_antisymm (Finset.min'_le _ _ haS) ((hS _ (Finset.min'_mem _ _)).1)
  · rw [ht (m - 1) (by omega), Finset.orderEmbOfFin_last rfl (by omega)]
    exact le_antisymm ((hS _ (Finset.max'_mem _ _)).2) (Finset.le_max' _ _ hbS)
  · intro i hi
    rw [ht i (by omega), ht (i + 1) (by omega)]
    exact e.strictMono (Fin.mk_lt_mk.2 (Nat.lt_succ_self i))
  · intro i hi
    rw [ht i (by omega), ht (i + 1) (by omega)]
    refine ⟨(hS _ (Finset.orderEmbOfFin_mem _ _ _)).1, (hS _ (Finset.orderEmbOfFin_mem _ _ _)).2,
      fun x hx hxi => ?_⟩
    have hxS : x ∈ S := Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
      (Finset.mem_filter.2 ⟨hx, (hS _ (Finset.orderEmbOfFin_mem _ _ _)).1.trans_lt hxi.1,
        hxi.2.trans_le (hS _ (Finset.orderEmbOfFin_mem _ _ _)).2⟩))
    obtain ⟨j, rfl⟩ : x ∈ Set.range e := by
      rw [Finset.range_orderEmbOfFin]; exact hxS
    have h1 := e.lt_iff_lt.1 hxi.1
    have h2 := e.lt_iff_lt.1 hxi.2
    rw [Fin.lt_def] at h1 h2
    simp only at h1 h2
    omega

/-! #### `TΩ(γ|[0, τ])`: blind `TOm τ` vs the project's `fieldsUpTo τ` -/

/-- **Blind ⇒ project**: the ambient field of a blind `W ∈ TΩ(γ|[0,τ])` lies in the project's
`TΩ_γ` and vanishes outside `[0, τ]`. -/
theorem mem_pathTangent_of_inTOmegaT {τ : ℝ} (hτ1 : τ ≤ 1) {γ : ℝ → Bridge.Sub hN}
    {X : FA n γ} (h : InTOmegaT (n := n) τ γ X) :
    Bridge.ambA γ X ∈ Morse.pathTangent hN (Bridge.incl hN ∘ γ) ∧
      ∀ t, t ∉ Icc (0 : ℝ) τ → Bridge.ambA γ X t = 0 := by
  obtain ⟨⟨k, t, ht0, htk, hlt, -, hsm⟩, hX0, hXτ, hout⟩ := h
  have hzero : ∀ s, τ ≤ s → Bridge.ambA γ X s = 0 := by
    intro s hs
    rcases eq_or_lt_of_le hs with rfl | hs'
    · show Bridge.D hN (γ τ) (X τ) = 0
      rw [hXτ]; exact map_zero _
    · show Bridge.D hN (γ s) (X s) = 0
      rw [hout s fun h => absurd h.2 (not_le.2 hs')]; exact map_zero _
  have hsm' : ∀ i < k, ContDiffOn ℝ ∞ (Bridge.ambA γ X) (Icc (t i) (t (i + 1))) := fun i hi => by
    have h' : RoundTrip.BridgePrelude.IsSmoothAlong γ (Icc (t i) (t (i + 1))) X := hsm i hi
    exact (Bridge.isSmoothAlong_iff.1 h').2
  have hpiece : ∀ s u, 0 ≤ s → s < u → u ≤ 1 →
      (∀ x ∈ insert τ ((Finset.range (k + 1)).image t), x ∉ Ioo s u) →
      ContDiffOn ℝ ∞ (Bridge.ambA γ X) (Icc s u) := by
    intro s u hs hsu hu hB
    by_cases huτ : u ≤ τ
    · obtain ⟨i, hi, hti, hui⟩ := exists_piece_of_subdivT ht0 htk hlt hs hsu huτ
        fun x hx => hB x (Finset.mem_insert_of_mem hx)
      exact (hsm' i hi).mono (Icc_subset_Icc hti hui)
    · have hτs : τ ≤ s := by
        by_contra h
        exact hB τ (Finset.mem_insert_self _ _) ⟨lt_of_not_ge h, lt_of_not_ge huτ⟩
      exact contDiffOn_const.congr fun x hx => hzero x (hτs.trans hx.1)
  refine ⟨(Morse.mem_pathTangent hN).2 ⟨⟨zero_le_one, Morse.continuousOn_of_piecewise
    fun s u hs hsu hu hB => (hpiece s u hs hsu hu hB).continuousOn, _, hpiece⟩,
    fun τ' _ => (Morse.prj_eq_self_iff hN (γ τ').2).2 (Bridge.D_mem (γ τ') (X τ')), ?_, ?_⟩, ?_⟩
  · show Bridge.D hN (γ 0) (X 0) = 0
    rw [hX0]; exact map_zero _
  · exact hzero 1 hτ1
  · intro s hs
    show Bridge.D hN (γ s) (X s) = 0
    rw [hout s hs]; exact map_zero _

/-- **Project ⇒ blind**: a project field in `TΩ_γ` vanishing outside `[0, τ]` gives a blind field
`toFA γ X ∈ TΩ(γ|[0,τ])`. -/
theorem inTOmegaT_toFA_T {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1) {γ : ℝ → Bridge.Sub hN}
    (hγ : IsSmoothCurve (n := n) γ (Icc 0 1)) {X : ℝ → V}
    (hX : X ∈ Morse.pathTangent hN (Bridge.incl hN ∘ γ))
    (hXτ : ∀ t, t ∉ Icc (0 : ℝ) τ → X t = 0) :
    InTOmegaT (n := n) τ γ (toFA γ X) := by
  obtain ⟨⟨-, -, B, hB⟩, hT, hX0, -⟩ := (Morse.mem_pathTangent hN).1 hX
  have hmem : (⟨X, hX⟩ : Morse.pathTangent hN (Bridge.incl hN ∘ γ)) ∈
      Morse.fieldsUpTo hN (Bridge.incl hN ∘ γ) τ := hXτ
  have hXτ0 : X τ = 0 := Morse.fieldsUpTo_apply_self hτ.le hτ1 hmem
  obtain ⟨k, t, ht0, htk, hlt, hgood⟩ := exists_subdivT hτ B
  have hsm : ∀ i < k, IsSmoothAlong γ (Icc (t i) (t (i + 1))) (toFA γ X) := by
    intro i hi
    obtain ⟨h0i, hi1, hBi⟩ := hgood i hi
    have hsub : Icc (t i) (t (i + 1)) ⊆ Icc 0 1 := Icc_subset_Icc h0i (hi1.trans hτ1)
    exact Bridge.isSmoothAlong_iff.2 ⟨ContMDiffOn.mono hγ hsub,
      (hB _ _ h0i (hlt i hi) (hi1.trans hτ1) hBi).congr fun s hs => ambA_toFA hT (hsub hs)⟩
  refine ⟨⟨k, t, ht0, htk, hlt, ?_, hsm⟩, ?_, ?_, fun s hs => ?_⟩
  · rw [← htk]
    exact continuousOn_of_pieces ht0 hlt fun i hi => ContMDiffOn.continuousOn (hsm i hi)
  · rw [toFA_of_mem X ⟨le_rfl, zero_le_one⟩, hX0, map_zero]; rfl
  · rw [toFA_of_mem X ⟨hτ.le, hτ1⟩, hXτ0, map_zero]; rfl
  · by_cases hs1 : s ∈ Icc (0 : ℝ) 1
    · rw [toFA_of_mem X hs1, hXτ s hs, map_zero]; rfl
    · exact toFA_of_not_mem X hs1

/-! #### Variations of `γ|[0, τ]` -/

/-- The extension of a blind variation of `γ|[0, τ]` by `α 0` on `(τ, 1]`, read in `V`. -/
noncomputable def extA {m : ℕ} (τ : ℝ) (α : Rn m → ℝ → Bridge.Sub hN) : Rn m → ℝ → V :=
  fun u s => if s ≤ τ then Bridge.incl hN (α u s) else Bridge.incl hN (α 0 s)

theorem extA_zero {m : ℕ} (τ : ℝ) (α : Rn m → ℝ → Bridge.Sub hN) (s : ℝ) :
    extA τ α 0 s = Bridge.incl hN (α 0 s) := by
  unfold extA; split_ifs <;> rfl

/-- **The extension is a project variation** of `incl ∘ α 0` on `[0, 1]`. -/
theorem isVariation_extA {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1) {m : ℕ} {U : Set (Rn m)}
    {α : Rn m → ℝ → Bridge.Sub hN} {k : ℕ} {t : ℕ → ℝ} (hα : IsVarSubT (n := n) τ U α k t)
    (hγ : ContDiffOn ℝ ∞ (Bridge.incl hN ∘ α 0) (Icc 0 1)) :
    Morse.IsVariation N U (extA τ α) (insert τ ((Finset.range (k + 1)).image t)) := by
  obtain ⟨hU, h0U, ht0, htk, hlt, hend, hsm⟩ := hα
  refine ⟨hU, h0U, fun u _ s _ => ?_, fun u hu => ?_, fun u hu => ?_,
    fun s u hs hsu hu hB => ?_⟩
  · unfold extA
    split_ifs
    · exact (α u s).2
    · exact (α 0 s).2
  · rw [extA_zero]
    unfold extA
    rw [if_pos hτ.le, (hend u hu).2.1]
  · rw [extA_zero]
    unfold extA
    split_ifs with h1
    · have : τ = 1 := le_antisymm hτ1 h1
      subst this
      rw [(hend u hu).2.2]
    · rfl
  · by_cases huτ : u ≤ τ
    · obtain ⟨i, hi, hti, hui⟩ := exists_piece_of_subdivT ht0 htk hlt hs hsu huτ
        fun x hx => hB x (Finset.mem_insert_of_mem hx)
      refine ((contMDiffOn_map_iff.1 (hsm i hi)).mono
        (prod_mono subset_rfl (Icc_subset_Icc hti hui))).congr fun p hp => ?_
      show extA τ α p.1 p.2 = Bridge.incl hN (α p.1 p.2)
      unfold extA
      rw [if_pos (hp.2.2.trans huτ)]
    · have hτs : τ ≤ s := by
        by_contra h
        exact hB τ (Finset.mem_insert_self _ _) ⟨lt_of_not_ge h, lt_of_not_ge huτ⟩
      have hg : ContDiffOn ℝ ∞ ((Bridge.incl hN ∘ α 0) ∘ Prod.snd) (U ×ˢ Icc s u) :=
        hγ.comp contDiff_snd.contDiffOn fun p hp => ⟨hs.trans hp.2.1, hp.2.2.trans hu⟩
      refine hg.congr fun p hp => ?_
      show extA τ α p.1 p.2 = Bridge.incl hN (α 0 p.2)
      unfold extA
      split_ifs with h
      · have hpτ : p.2 = τ := le_antisymm h (hτs.trans hp.2.1)
        rw [hpτ, (hend p.1 hp.1).2.2]
      · rfl

/-- `E_0^1` of the extension is `E_0^τ` of the blind path plus the constant `E_τ^1(γ)`. -/
theorem energy_extA {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1) {m : ℕ} {U : Set (Rn m)}
    {α : Rn m → ℝ → Bridge.Sub hN} {B : Finset ℝ}
    (hvar : Morse.IsVariation N U (extA τ α) B) {v : Rn m} (hv : v ∈ U) :
    Morse.energy (extA τ α v) 0 1 =
      Morse.energy (Bridge.incl hN ∘ α v) 0 τ + Morse.energy (Bridge.incl hN ∘ α 0) τ 1 := by
  have hint := (hvar.isPiecewiseSmooth hv).intervalIntegrable_norm_deriv_sq
  have h1 : IntervalIntegrable (fun s => ‖deriv (extA τ α v) s‖ ^ 2) MeasureTheory.volume 0 τ :=
    hint.mono_set (by
      rw [uIcc_of_le hτ.le, uIcc_of_le zero_le_one]; exact Icc_subset_Icc le_rfl hτ1)
  have h2 : IntervalIntegrable (fun s => ‖deriv (extA τ α v) s‖ ^ 2) MeasureTheory.volume τ 1 :=
    hint.mono_set (by
      rw [uIcc_of_le hτ1, uIcc_of_le zero_le_one]; exact Icc_subset_Icc hτ.le le_rfl)
  unfold Morse.energy
  rw [← intervalIntegral.integral_add_adjacent_intervals h1 h2]
  congr 1
  · refine intervalIntegral.integral_congr_Ioo_of_le hτ.le fun s hs => ?_
    have : extA τ α v =ᶠ[𝓝 s] Bridge.incl hN ∘ α v := by
      filter_upwards [Iio_mem_nhds hs.2] with x hx
      unfold extA
      rw [if_pos (le_of_lt hx)]
      rfl
    simp only [this.deriv_eq]
  · refine intervalIntegral.integral_congr_Ioo_of_le hτ1 fun s hs => ?_
    have : extA τ α v =ᶠ[𝓝 s] Bridge.incl hN ∘ α 0 := by
      filter_upwards [Ioi_mem_nhds hs.1] with x hx
      unfold extA
      rw [if_neg (not_le.2 hx)]
      rfl
    simp only [this.deriv_eq]

/-- Variation fields of a blind variation of `γ|[0, τ]`, read in `V`, on `[0, τ]`. -/
theorem D_varFieldT {τ : ℝ} (hτ : 0 < τ) {m : ℕ} {U : Set (Rn m)}
    {α : Rn m → ℝ → Bridge.Sub hN} {k : ℕ} {t : ℕ → ℝ} (hα : IsVarSubT (n := n) τ U α k t)
    (i : Fin m) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) τ) :
    Bridge.D hN (α 0 s) (varField (n := n) α i s) =
      deriv (fun r : ℝ => amb α (r • EuclideanSpace.single i (1 : ℝ)) s) 0 := by
  obtain ⟨hU, h0U, ht0, htk, hlt, -, hsm⟩ := hα
  obtain ⟨j, hj, hsj⟩ := exists_piece_of_memT hτ ht0 htk hlt hs
  have hG : ContDiffOn ℝ ∞ (Bridge.incl hN ∘ fun x : Rn m × ℝ => α x.1 x.2)
      (U ×ˢ Icc (t j) (t (j + 1))) := contMDiffOn_map_iff.1 (hsm j hj)
  have hcd : ContDiffAt ℝ ∞ (Bridge.incl hN ∘ fun u => α u s) 0 :=
    (hG.comp (contDiff_id.prodMk contDiff_const).contDiffOn fun u hu => ⟨hu, hsj⟩).contDiffAt
      (hU.mem_nhds h0U)
  have h1 := D_mfderiv_of_contDiffAt hcd (EuclideanSpace.single i (1 : ℝ))
  have h2 := RoundTrip.EnergyC2.hasDerivAt_line (hcd.differentiableAt (by simp))
    (EuclideanSpace.single i (1 : ℝ))
  simp only [zero_add] at h2
  exact h1.trans h2.deriv.symm

/-- The variation fields of the extension: the blind ones on `[0, τ]`, `0` beyond. -/
theorem deriv_extA {τ : ℝ} (hτ : 0 < τ) {m : ℕ} {U : Set (Rn m)}
    {α : Rn m → ℝ → Bridge.Sub hN} {k : ℕ} {t : ℕ → ℝ} (hα : IsVarSubT (n := n) τ U α k t)
    (i : Fin m) {s : ℝ} (hs : 0 ≤ s) :
    deriv (fun r : ℝ => extA τ α (r • EuclideanSpace.single i (1 : ℝ)) s) 0 =
      if s ≤ τ then Bridge.ambA (α 0) (varField (n := n) α i) s else 0 := by
  split_ifs with h
  · have e : (fun r : ℝ => extA τ α (r • EuclideanSpace.single i (1 : ℝ)) s) =
        fun r : ℝ => amb α (r • EuclideanSpace.single i (1 : ℝ)) s := funext fun r => by
      unfold extA
      rw [if_pos h]
      rfl
    rw [e, ← D_varFieldT hτ hα i ⟨hs, h⟩]
    rfl
  · have e : (fun r : ℝ => extA τ α (r • EuclideanSpace.single i (1 : ℝ)) s) =
        fun _ : ℝ => Bridge.incl hN (α 0 s) := funext fun r => by
      unfold extA
      rw [if_neg h]
    rw [e, deriv_const]

/-- **`E_0^τ ∘ α` is `C²` and its blind `mixedD` is `2 secondVariation`** of the fields
(extended by `0` beyond `τ`), for every blind variation of `γ|[0, τ]`, `γ` a geodesic of `↥N`. -/
theorem hessT_data {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1) {U : Set (Rn 2)}
    {α : Rn 2 → ℝ → Bridge.Sub hN} {k : ℕ} {t : ℕ → ℝ} (hα : IsVarSubT (n := n) τ U α k t)
    (hgeo : IsGeodesic (Bridge.conn (hN := hN)) (α 0) (Icc 0 1)) :
    DifferentiableAt ℝ
        (fun u : Rn 2 => fderiv ℝ (fun v : Rn 2 => energy (n := n) (α v) 0 τ) u e0) 0 ∧
      mixedD (fun v : Rn 2 => energy (n := n) (α v) 0 τ) =
        2 * Morse.secondVariation hN (Bridge.incl hN ∘ α 0)
          (fun s => if s ≤ τ then Bridge.ambA (α 0) (varField (n := n) α 0) s else 0)
          (fun s => if s ≤ τ then Bridge.ambA (α 0) (varField (n := n) α 1) s else 0) := by
  have hub := isUnbrokenGeodesic_of_isGeodesic hgeo
  have hvar := isVariation_extA hτ hτ1 hα hub.1
  have hU := hvar.isOpen
  have h0U := hvar.zero_mem
  have hFG : ∀ v ∈ U, energy (n := n) (α v) 0 τ =
      Morse.energy (extA τ α v) 0 1 - Morse.energy (Bridge.incl hN ∘ α 0) τ 1 := by
    intro v hv
    have h1 : energy (n := n) (α v) 0 τ = Morse.energy (Bridge.incl hN ∘ α v) 0 τ :=
      Bridge.energy_eq (α v) 0 τ
    rw [h1, energy_extA hτ hτ1 hvar hv]
    ring
  have hG : ContDiffOn ℝ 2 (fun v => Morse.energy (extA τ α v) 0 1) U :=
    hvar.contDiffOn_energy.of_le ENat.LEInfty.out
  have hF : ContDiffOn ℝ 2 (fun v : Rn 2 => energy (n := n) (α v) 0 τ) U :=
    (hG.sub contDiffOn_const).congr hFG
  have hev : (fun v : Rn 2 => energy (n := n) (α v) 0 τ) =ᶠ[𝓝 0]
      fun v => Morse.energy (extA τ α v) 0 1 - Morse.energy (Bridge.incl hN ∘ α 0) τ 1 :=
    Filter.eventuallyEq_of_mem (hU.mem_nhds h0U) hFG
  have hD : (fun u => fderiv ℝ (fun v : Rn 2 => energy (n := n) (α v) 0 τ) u e0) =ᶠ[𝓝 0]
      fun u => fderiv ℝ (fun v => Morse.energy (extA τ α v) 0 1) u e0 := by
    filter_upwards [hev.fderiv (𝕜 := ℝ)] with u hu
    rw [hu, fderiv_sub_const]
  refine ⟨RoundTrip.EnergyC2.differentiableAt_fderiv_apply hU hF h0U e0, ?_⟩
  have hmix : mixedD (fun v : Rn 2 => energy (n := n) (α v) 0 τ) =
      fderiv ℝ (fun u => fderiv ℝ (fun v => Morse.energy (extA τ α v) 0 1) u e0) 0 e1 := by
    unfold mixedD
    rw [hD.fderiv_eq]
  have h := RoundTrip.EnergyC2.fderiv_fderiv_apply_eq_deriv_deriv hU hG h0U e0 e1
  simp only [zero_add] at h
  rw [hmix, h]
  have hφ : ContDiff ℝ ∞ (fun p : ℝ × ℝ => p.1 • e0 + p.2 • e1) :=
    (contDiff_fst.smul contDiff_const).add (contDiff_snd.smul contDiff_const)
  have hφ0 : (fun p : ℝ × ℝ => p.1 • e0 + p.2 • e1) 0 ∈ U := by
    simpa using h0U
  have hvar2 := hvar.comp hφ hφ0
  have hαγ : ∀ s ∈ Icc (0 : ℝ) 1,
      (fun p : ℝ × ℝ => extA τ α (p.1 • e0 + p.2 • e1)) 0 s = (Bridge.incl hN ∘ α 0) s := by
    intro s _
    simp only [Prod.fst_zero, Prod.snd_zero, zero_smul, add_zero]
    exact extA_zero τ α s
  have hd := sv_holds (mem_pathSpace_of_isGeodesic hgeo) hub hvar2 hαγ
  simp only [zero_smul, add_zero, zero_add] at hd
  rw [hd.deriv]
  congr 1
  refine Morse.secondVariation_congr hN (fun s hs => ?_) (fun s hs => ?_)
  · exact deriv_extA hτ hα 0 hs.1
  · exact deriv_extA hτ hα 1 hs.1

/-- **Every `IsHessT τ` value is `2 secondVariation`** of the ambient fields, for blind fields in
`TΩ(γ|[0,τ])` (`0` beyond `τ`). -/
theorem hessT_eqT {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1) {γ : ℝ → Bridge.Sub hN}
    (hgeo : IsGeodesic (Bridge.conn (hN := hN)) γ (Icc 0 1)) {W₁ W₂ : FA n γ}
    (h₁ : InTOmegaT (n := n) τ γ W₁) (h₂ : InTOmegaT (n := n) τ γ W₂) {r : ℝ}
    (h : IsHessT (n := n) τ γ W₁ W₂ r) :
    r = 2 * Morse.secondVariation hN (Bridge.incl hN ∘ γ) (Bridge.ambA γ W₁) (Bridge.ambA γ W₂) := by
  obtain ⟨U, α, k, t, hα, rfl, hW₁, hW₂, -, hr⟩ := h
  rw [← hr, (hessT_data hτ hτ1 hα hgeo).2]
  congr 1
  refine Morse.secondVariation_congr hN (fun s _ => ?_) (fun s _ => ?_)
  · split_ifs with hs
    · show Bridge.D hN (α 0 s) (varField (n := n) α 0 s) = Bridge.D hN (α 0 s) (W₁ s)
      rw [eq_of_heq (hW₁ s)]
    · show (0 : V) = Bridge.D hN (α 0 s) (W₁ s)
      rw [h₁.2.2.2 s fun h' => hs h'.2]
      exact (map_zero _).symm
  · split_ifs with hs
    · show Bridge.D hN (α 0 s) (varField (n := n) α 1 s) = Bridge.D hN (α 0 s) (W₂ s)
      rw [eq_of_heq (hW₂ s)]
    · show (0 : V) = Bridge.D hN (α 0 s) (W₂ s)
      rw [h₂.2.2.2 s fun h' => hs h'.2]
      exact (map_zero _).symm

/-- **Existence of `E_**(W₁, W₂)` for `E_0^τ` on `↥N`** (Lemma 11.A on `[0, 1]`, restricted to a
subdivision of `[0, τ]`; fields matched on all of `ℝ`). -/
theorem exists_isHessT {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1) {γ : ℝ → Bridge.Sub hN}
    (hgeo : IsGeodesic (Bridge.conn (hN := hN)) γ (Icc 0 1)) {W₁ W₂ : FA n γ}
    (h₁ : InTOmegaT (n := n) τ γ W₁) (h₂ : InTOmegaT (n := n) τ γ W₂) :
    ∃ r, IsHessT (n := n) τ γ W₁ W₂ r := by
  have hc := mem_pathSpace_of_isGeodesic hgeo
  obtain ⟨hXs₁, -, hX0₁, hX1₁⟩ := (Morse.mem_pathTangent hN).1 (mem_pathTangent_of_inTOmegaT hτ1 h₁).1
  obtain ⟨hXs₂, -, hX0₂, hX1₂⟩ := (Morse.mem_pathTangent hN).1 (mem_pathTangent_of_inTOmegaT hτ1 h₂).1
  set X₁ := Bridge.ambA γ W₁
  set X₂ := Bridge.ambA γ W₂
  have hXτ₁ : X₁ τ = 0 := by
    show Bridge.D hN (γ τ) (W₁ τ) = 0
    rw [h₁.2.2.1]; exact map_zero _
  have hXτ₂ : X₂ τ = 0 := by
    show Bridge.D hN (γ τ) (W₂ τ) = 0
    rw [h₂.2.2.1]; exact map_zero _
  set Λ : ℝ → Rn 2 →L[ℝ] V := fun t =>
    (EuclideanSpace.proj (0 : Fin 2) : Rn 2 →L[ℝ] ℝ).smulRight (X₁ t) +
      (EuclideanSpace.proj (1 : Fin 2) : Rn 2 →L[ℝ] ℝ).smulRight (X₂ t) with hΛdef
  have hΛapp : ∀ t u, Λ t u = u 0 • X₁ t + u 1 • X₂ t := fun t u => by
    simp [hΛdef]
  have hΛT : ∀ t u, Morse.prj hN (Bridge.incl hN (γ t)) (Λ t u) = Λ t u := fun t u =>
    (Morse.prj_eq_self_iff hN (γ t).2).2 (by
      rw [hΛapp]
      exact add_mem (Submodule.smul_mem _ _ (Bridge.D_mem (γ t) (W₁ t)))
        (Submodule.smul_mem _ _ (Bridge.D_mem (γ t) (W₂ t))))
  have hΛs : Morse.IsPiecewiseSmooth Λ 0 1 :=
    (hXs₁.smulRight (EuclideanSpace.proj (0 : Fin 2) : Rn 2 →L[ℝ] ℝ)).add
      (hXs₂.smulRight (EuclideanSpace.proj (1 : Fin 2) : Rn 2 →L[ℝ] ℝ))
  have hΛ0 : Λ 0 = 0 := ContinuousLinearMap.ext fun u => by
    rw [hΛapp]; simp [hX0₁, hX0₂]
  have hΛ1 : Λ 1 = 0 := ContinuousLinearMap.ext fun u => by
    rw [hΛapp]; simp [hX1₁, hX1₂]
  have hΛτ : Λ τ = 0 := ContinuousLinearMap.ext fun u => by
    rw [hΛapp]; simp [hXτ₁, hXτ₂]
  obtain ⟨ε, hε, B, hα, -, -⟩ := Morse.exists_variation hN hc (P := Rn 2) hΛs
    (fun t _ u => hΛT t u) hΛ0 hΛ1
  set α := liftE γ Λ
  have hinc : ∀ u ∈ Metric.ball (0 : Rn 2) ε, ∀ t ∈ Icc (0 : ℝ) 1,
      Bridge.incl hN (α u t) = Morse.exp hN (Bridge.incl hN (γ t)) (Λ t u) :=
    fun u hu t ht => incl_liftE (hα.mem u hu t ht)
  have hinj : Function.Injective (Bridge.incl hN) := Subtype.val_injective
  have hα0 : α 0 = γ := funext fun t => by
    have e : Morse.exp hN (Bridge.incl hN (γ t)) (Λ t 0) = Bridge.incl hN (γ t) := by
      rw [map_zero]; exact Morse.exp_zero (γ t).2
    exact hinj ((incl_liftE (γ := γ) (Λ := Λ) (u := 0) (t := t) (by rw [e]; exact (γ t).2)).trans e)
  obtain ⟨k, tt, ht0, htk, hlt, hgood⟩ := exists_subdivT hτ B
  have hstrip : ∀ i < k, ContMDiffOn 𝓘(ℝ, Rn 2 × ℝ) 𝓘(ℝ, Rn n) ∞
      (fun x : Rn 2 × ℝ => α x.1 x.2) (Metric.ball (0 : Rn 2) ε ×ˢ Icc (tt i) (tt (i + 1))) := by
    intro i hi
    obtain ⟨hi0, hi1, hiB⟩ := hgood i hi
    refine contMDiffOn_map_iff.2
      ((hα.smooth _ _ hi0 (hlt i hi) (hi1.trans hτ1) hiB).congr fun p hp => ?_)
    exact hinc p.1 hp.1 p.2 ⟨hi0.trans hp.2.1, hp.2.2.trans (hi1.trans hτ1)⟩
  have hvs : IsVarSubT (n := n) τ (Metric.ball (0 : Rn 2) ε) α k tt := by
    refine ⟨Metric.isOpen_ball, Metric.mem_ball_self hε, ht0, htk, hlt, fun u hu => ⟨?_, ?_, ?_⟩,
      hstrip⟩
    · refine ⟨k, tt, ht0, htk, hlt, fun i hi => ?_⟩
      have hι : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, Rn 2 × ℝ) ∞ (fun s : ℝ => (u, s)) :=
        contMDiff_iff_contDiff.2 (contDiff_const.prodMk contDiff_id)
      exact (hstrip i hi).comp hι.contMDiffOn fun s hs => ⟨hu, hs⟩
    · refine hinj ?_
      rw [hinc u hu 0 ⟨le_rfl, zero_le_one⟩, hinc 0 (Metric.mem_ball_self hε) 0 ⟨le_rfl, zero_le_one⟩,
        hΛ0]
      rfl
    · refine hinj ?_
      rw [hinc u hu τ ⟨hτ.le, hτ1⟩, hinc 0 (Metric.mem_ball_self hε) τ ⟨hτ.le, hτ1⟩, hΛτ]
      rfl
  have hfield : ∀ (i : Fin 2) (t : ℝ),
      Bridge.D hN (γ t) (varField (n := n) α i t) = Λ t (EuclideanSpace.single i (1 : ℝ)) := by
    intro i t
    obtain ⟨hmem, hcd, hfd⟩ := exp_local (hN := hN) (γ t).2 (Λ t) (hΛT t)
    have hev : (Bridge.incl hN ∘ fun u => α u t) =ᶠ[𝓝 0]
        fun u => Morse.exp hN (Bridge.incl hN (γ t)) (Λ t u) := by
      filter_upwards [hmem] with u hu
      exact incl_liftE hu
    have h1 := D_mfderiv_of_contDiffAt (hcd.congr_of_eventuallyEq hev)
      (EuclideanSpace.single i (1 : ℝ))
    have h2 := (hfd.congr_of_eventuallyEq hev).fderiv
    rw [h2] at h1
    calc Bridge.D hN (γ t) (varField (n := n) α i t)
        = Bridge.D hN (α 0 t) (varField (n := n) α i t) := by rw [congrFun hα0 t]
      _ = _ := h1
  have hW : ∀ (i : Fin 2) (Wi : FA n γ), (∀ t, Λ t (EuclideanSpace.single i (1 : ℝ)) =
      Bridge.D hN (γ t) (Wi t)) → ∀ t, HEq (Wi t) (varField (n := n) α i t) := by
    intro i Wi hWi t
    have := Bridge.D_injective (γ t) ((hfield i t).trans (hWi t))
    exact heq_of_eq this.symm
  have hgeo' : IsGeodesic (Bridge.conn (hN := hN)) (α 0) (Icc 0 1) := by rw [hα0]; exact hgeo
  refine ⟨_, Metric.ball (0 : Rn 2) ε, α, k, tt, hvs, hα0,
    hW 0 W₁ fun t => by rw [hΛapp]; simp [X₁, Bridge.ambA],
    hW 1 W₂ fun t => by rw [hΛapp]; simp [X₂, Bridge.ambA], (hessT_data hτ hτ1 hvs hgeo').1, rfl⟩

theorem isHessT_iffT {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1) {γ : ℝ → Bridge.Sub hN}
    (hgeo : IsGeodesic (Bridge.conn (hN := hN)) γ (Icc 0 1)) {W₁ W₂ : FA n γ}
    (h₁ : InTOmegaT (n := n) τ γ W₁) (h₂ : InTOmegaT (n := n) τ γ W₂) {r : ℝ} :
    IsHessT (n := n) τ γ W₁ W₂ r ↔
      r = 2 * Morse.secondVariation hN (Bridge.incl hN ∘ γ) (Bridge.ambA γ W₁) (Bridge.ambA γ W₂) := by
  refine ⟨hessT_eqT hτ hτ1 hgeo h₁ h₂, fun h => ?_⟩
  obtain ⟨r', hr'⟩ := exists_isHessT hτ hτ1 hgeo h₁ h₂
  rw [h, ← hessT_eqT hτ hτ1 hgeo h₁ h₂ hr']
  exact hr'

/-- **The choice function `HessT τ γ` is `2 secondVariation`** on `TΩ(γ|[0,τ])`. -/
theorem hessT_eq_T {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1) {γ : ℝ → Bridge.Sub hN}
    (hgeo : IsGeodesic (Bridge.conn (hN := hN)) γ (Icc 0 1)) {W₁ W₂ : FA n γ}
    (h₁ : InTOmegaT (n := n) τ γ W₁) (h₂ : InTOmegaT (n := n) τ γ W₂) :
    HessT (n := n) τ γ W₁ W₂ =
      2 * Morse.secondVariation hN (Bridge.incl hN ∘ γ) (Bridge.ambA γ W₁) (Bridge.ambA γ W₂) := by
  have hex := exists_isHessT hτ hτ1 hgeo h₁ h₂
  unfold HessT
  rw [dif_pos hex]
  exact hessT_eqT hτ hτ1 hgeo h₁ h₂ hex.choose_spec

end Emb

/-! ### Index and nullity: B's `λ(τ)` and `ν(τ)` on `↥N` are the project's

Generic linear algebra (`bIndex_eq_formIndex_of`, `setDim_bNullSet_eq_rank`): if an injective
linear map `φ : M → E` maps `M` onto the set `T` and pulls `H` back to the bilinear form `B`, then
B's index and nullity of `H` on `T` are `Morse.formIndex B` and the rank of `ker B`. On `↥N`,
`φ = toFA` maps the project's `fieldsUpTo τ` onto the blind `TOm τ`, pulling `HessT τ` back to
`energyHessian` restricted to `fieldsUpTo τ` (`hessT_φT`). Hence **`lam τ γ = indexUpTo τ`**
(`Emb.lamEq`, the hypothesis `LamEq` of `Items/V9_20.lean`; `Emb.lamEqOne` is the hypothesis
`LamEq` of `Items/V13_3.lean`) and B's nullity of `(E_0^τ)_**` is `conjMultiplicity 0 τ`
(`setDim_bNullSet_T`, `rank_ker_fieldsUpTo`). -/

section LinAlgT

variable {E M : Type} [AddCommGroup E] [Module ℝ E] [AddCommGroup M] [Module ℝ M]

theorem bIndex_eq_formIndex_of {T : Set E} {H : E → E → ℝ} (B : LinearMap.BilinForm ℝ M)
    (φ : M →ₗ[ℝ] E) (hφ : Injective φ) (hT : Set.range φ = T)
    (hH : ∀ x y, H (φ x) (φ y) = B x y) : bIndex T H = Morse.formIndex B := by
  apply le_antisymm
  · unfold bIndex
    refine iSup₂_le fun S ⟨hST, hfd, hneg⟩ => ?_
    have hSR : S ≤ LinearMap.range φ := fun v hv => by
      have := hST hv
      rw [← hT] at this
      exact this
    have hmap : (S.comap φ).map φ = S := Submodule.map_comap_eq_of_le hSR
    let e : S.comap φ ≃ₗ[ℝ] S :=
      (Submodule.equivMapOfInjective φ hφ (S.comap φ)).trans (LinearEquiv.ofEq _ _ hmap)
    haveI : FiniteDimensional ℝ (S.comap φ) := LinearEquiv.finiteDimensional e.symm
    have hneg' : Morse.IsNegDefOn B (S.comap φ) := fun x hx hx0 => by
      rw [← hH]
      exact hneg (φ x) hx fun h => hx0 (hφ (h.trans (map_zero φ).symm))
    calc (Module.finrank ℝ S : ℕ∞) = Module.finrank ℝ (S.comap φ) := by rw [e.finrank_eq]
      _ ≤ Morse.formIndex B := Morse.le_formIndex hneg'
  · refine Morse.formIndex_le fun S' hfd hneg => ?_
    let e : S' ≃ₗ[ℝ] S'.map φ := Submodule.equivMapOfInjective φ hφ S'
    haveI : FiniteDimensional ℝ (S'.map φ) := LinearEquiv.finiteDimensional e
    have hST : ((S'.map φ : Submodule ℝ E) : Set E) ⊆ T := by
      rintro _ ⟨x, -, rfl⟩
      rw [← hT]
      exact ⟨x, rfl⟩
    have hneg' : IsNegDefSub H (S'.map φ) := by
      rintro _ ⟨x, hx, rfl⟩ hx0
      rw [hH]
      exact hneg x hx fun h => hx0 (by rw [h, map_zero])
    calc (Module.finrank ℝ S' : ℕ∞) = Module.finrank ℝ (S'.map φ) := by rw [e.finrank_eq]
      _ ≤ bIndex T H := by
        unfold bIndex
        exact le_iSup₂_of_le (f := fun (S : Submodule ℝ E)
          (_ : (S : Set E) ⊆ T ∧ FiniteDimensional ℝ S ∧ IsNegDefSub H S) =>
            (Module.finrank ℝ S : ℕ∞)) (S'.map φ) ⟨hST, inferInstance, hneg'⟩ le_rfl

end LinAlgT

section LinAlgN

variable {E M : Type} [AddCommGroup E] [Module ℝ E] [AddCommMonoid M] [Module ℝ M]

theorem bNullSet_eq_image_ker {T : Set E} {H : E → E → ℝ} (B : LinearMap.BilinForm ℝ M)
    (φ : M →ₗ[ℝ] E) (hT : Set.range φ = T) (hH : ∀ x y, H (φ x) (φ y) = B x y) :
    bNullSet T H = φ '' (LinearMap.ker B : Set M) := by
  ext v
  constructor
  · rintro ⟨hv, hnull⟩
    rw [← hT] at hv
    obtain ⟨x, rfl⟩ := hv
    refine ⟨x, ?_, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker]
    refine LinearMap.ext fun y => ?_
    rw [← hH, LinearMap.zero_apply]
    exact hnull (φ y) (by rw [← hT]; exact ⟨y, rfl⟩)
  · rintro ⟨x, hx, rfl⟩
    refine ⟨by rw [← hT]; exact ⟨x, rfl⟩, fun w hw => ?_⟩
    rw [← hT] at hw
    obtain ⟨y, rfl⟩ := hw
    rw [hH]
    rw [SetLike.mem_coe, LinearMap.mem_ker] at hx
    rw [hx, LinearMap.zero_apply]

theorem setDim_bNullSet_eq_rank {T : Set E} {H : E → E → ℝ} (B : LinearMap.BilinForm ℝ M)
    (φ : M →ₗ[ℝ] E) (hφ : Injective φ) (hT : Set.range φ = T)
    (hH : ∀ x y, H (φ x) (φ y) = B x y) :
    setDim (bNullSet T H) = (Module.rank ℝ (LinearMap.ker B)).toENat := by
  unfold setDim
  rw [bNullSet_eq_image_ker B φ hT hH, ← Submodule.map_coe, Submodule.span_eq,
    ← (Submodule.equivMapOfInjective φ hφ (LinearMap.ker B)).rank_eq]

end LinAlgN

namespace Emb

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] {n : ℕ} {N : Set V}
  {hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N}

/-- The dictionary map `fieldsUpTo τ → FA n γ`, `X ↦ toFA γ X`. -/
noncomputable def φT (γ : ℝ → Bridge.Sub hN) (τ : ℝ) :
    Morse.fieldsUpTo hN (Bridge.incl hN ∘ γ) τ →ₗ[ℝ] FA n γ :=
  (toFAₗ γ).comp ((Morse.pathTangent hN (Bridge.incl hN ∘ γ)).subtype.comp
    (Morse.fieldsUpTo hN (Bridge.incl hN ∘ γ) τ).subtype)

theorem φT_apply (γ : ℝ → Bridge.Sub hN) (τ : ℝ) (x : Morse.fieldsUpTo hN (Bridge.incl hN ∘ γ) τ) :
    φT (n := n) γ τ x = toFA γ ((x : Morse.pathTangent hN (Bridge.incl hN ∘ γ)) : ℝ → V) := rfl

theorem φT_injective {τ : ℝ} (hτ1 : τ ≤ 1) (γ : ℝ → Bridge.Sub hN) :
    Injective (φT (n := n) γ τ) := by
  intro x y h
  have hx := ((Morse.mem_pathTangent hN).1 (x : Morse.pathTangent hN (Bridge.incl hN ∘ γ)).2).2.1
  have hy := ((Morse.mem_pathTangent hN).1 (y : Morse.pathTangent hN (Bridge.incl hN ∘ γ)).2).2.1
  have h' := toFA_injOn hx hy h
  have hx0 : ∀ t, t ∉ Icc (0 : ℝ) τ →
      ((x : Morse.pathTangent hN (Bridge.incl hN ∘ γ)) : ℝ → V) t = 0 := x.2
  have hy0 : ∀ t, t ∉ Icc (0 : ℝ) τ →
      ((y : Morse.pathTangent hN (Bridge.incl hN ∘ γ)) : ℝ → V) t = 0 := y.2
  refine Subtype.ext (Subtype.ext (funext fun t => ?_))
  by_cases ht : t ∈ Icc (0 : ℝ) τ
  · exact h' ⟨ht.1, ht.2.trans hτ1⟩
  · rw [hx0 t ht, hy0 t ht]

theorem range_φT {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1) {γ : ℝ → Bridge.Sub hN}
    (hγ : IsSmoothCurve (n := n) γ (Icc 0 1)) :
    Set.range (φT (n := n) γ τ) = TOm (n := n) τ γ := by
  ext Wf
  constructor
  · rintro ⟨x, rfl⟩
    exact inTOmegaT_toFA_T hτ hτ1 hγ (x : Morse.pathTangent hN (Bridge.incl hN ∘ γ)).2 x.2
  · intro hW
    have hW' : InTOmegaT (n := n) τ γ Wf := hW
    obtain ⟨hm, hout⟩ := mem_pathTangent_of_inTOmegaT hτ1 hW'
    refine ⟨⟨⟨_, hm⟩, hout⟩, funext fun t => ?_⟩
    rw [φT_apply]
    by_cases ht : t ∈ Icc (0 : ℝ) 1
    · rw [toFA_of_mem _ ht]
      exact Bridge.L_D (γ t) (Wf t)
    · rw [toFA_of_not_mem _ ht, hW'.2.2.2 t fun h => ht ⟨h.1, h.2.trans hτ1⟩]

/-- **`HessT τ` pulled back by `toFA` is `energyHessian` on `fieldsUpTo τ`.** -/
theorem hessT_φT {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1) {γ : ℝ → Bridge.Sub hN}
    (hgeo : IsGeodesic (Bridge.conn (hN := hN)) γ (Icc 0 1))
    (hc : Morse.IsSmoothCurveIn hN (Bridge.incl hN ∘ γ))
    (x y : Morse.fieldsUpTo hN (Bridge.incl hN ∘ γ) τ) :
    HessT (n := n) τ γ (φT γ τ x) (φT γ τ y) =
      ((Morse.energyHessian hN hc.mem_pathSpace).restrict
        (Morse.fieldsUpTo hN (Bridge.incl hN ∘ γ) τ)) x y := by
  have hγs : IsSmoothCurve (n := n) γ (Icc 0 1) := hgeo.2.1
  have hx := inTOmegaT_toFA_T hτ hτ1 hγs (x : Morse.pathTangent hN (Bridge.incl hN ∘ γ)).2 x.2
  have hy := inTOmegaT_toFA_T hτ hτ1 hγs (y : Morse.pathTangent hN (Bridge.incl hN ∘ γ)).2 y.2
  have hxT := ((Morse.mem_pathTangent hN).1 (x : Morse.pathTangent hN (Bridge.incl hN ∘ γ)).2).2.1
  have hyT := ((Morse.mem_pathTangent hN).1 (y : Morse.pathTangent hN (Bridge.incl hN ∘ γ)).2).2.1
  rw [φT_apply, φT_apply, hessT_eq_T hτ hτ1 hgeo hx hy]
  show _ = Morse.energyHessian hN hc.mem_pathSpace (x : Morse.pathTangent hN (Bridge.incl hN ∘ γ))
    (y : Morse.pathTangent hN (Bridge.incl hN ∘ γ))
  rw [Morse.energyHessian_apply]
  congr 1
  exact Morse.secondVariation_congr hN (fun t ht => ambA_toFA hxT ht) (fun t ht => ambA_toFA hyT ht)

/-- **`λ(τ)` of B is the project's `indexUpTo τ`** on `↥N` (for a geodesic, `0 < τ ≤ 1`). -/
theorem lam_eq_indexUpTo {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1) {γ : ℝ → Bridge.Sub hN}
    (hgeo : IsGeodesic (Bridge.conn (hN := hN)) γ (Icc 0 1))
    (hc : Morse.IsSmoothCurveIn hN (Bridge.incl hN ∘ γ)) :
    lam (n := n) τ γ = Morse.indexUpTo hN (Bridge.incl hN ∘ γ) hc τ := by
  unfold lam Morse.indexUpTo
  exact bIndex_eq_formIndex_of _ (φT γ τ) (φT_injective hτ1 γ) (range_φT hτ hτ1 hgeo.2.1)
    (hessT_φT hτ hτ1 hgeo hc)

/-- **B's nullity of `(E_0^τ)_**` is the rank of the kernel of `energyHessian` on
`fieldsUpTo τ`.** -/
theorem setDim_bNullSet_T {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1) {γ : ℝ → Bridge.Sub hN}
    (hgeo : IsGeodesic (Bridge.conn (hN := hN)) γ (Icc 0 1))
    (hc : Morse.IsSmoothCurveIn hN (Bridge.incl hN ∘ γ)) :
    setDim (bNullSet (TOm (n := n) τ γ) (HessT (n := n) τ γ)) =
      (Module.rank ℝ (LinearMap.ker ((Morse.energyHessian hN hc.mem_pathSpace).restrict
        (Morse.fieldsUpTo hN (Bridge.incl hN ∘ γ) τ)))).toENat := by
  exact setDim_bNullSet_eq_rank (T := TOm (n := n) τ γ) (H := HessT (n := n) τ γ)
    ((Morse.energyHessian hN hc.mem_pathSpace).restrict
      (Morse.fieldsUpTo hN (Bridge.incl hN ∘ γ) τ)) (φT γ τ) (φT_injective hτ1 γ)
    (range_φT hτ hτ1 hgeo.2.1) (hessT_φT hτ hτ1 hgeo hc)

/-- The nullity of `energyHessian` on `fieldsUpTo τ` is `conjMultiplicity 0 τ` (Lemma 15.4 for
the null space and the nullity on broken Jacobi fields: `Morse.lemma_15_4_ker`,
`Morse.finrank_ker_broken`, item V9_19). -/
theorem rank_ker_fieldsUpTo {c : ℝ → V} (hc : Morse.IsSmoothCurveIn hN c) {τ : ℝ} (hτ : 0 < τ)
    (hτ1 : τ ≤ 1) :
    Module.rank ℝ (LinearMap.ker ((Morse.energyHessian hN hc.mem_pathSpace).restrict
      (Morse.fieldsUpTo hN c τ))) = Morse.conjMultiplicity hN c hc 0 τ := by
  obtain ⟨B, hB, -⟩ := Morse.exists_isFine hc hτ
  haveI := Morse.finiteDimensional_brokenSpace hc hτ hτ1 hB
  have hle := Morse.brokenSpace_le_fieldsUpTo hc B τ
  let e := Submodule.comapSubtypeEquivOfLe hle
  have hmap : (LinearMap.ker (((Morse.energyHessian hN hc.mem_pathSpace).restrict
      (Morse.fieldsUpTo hN c τ)).restrict ((Morse.brokenSpace hc B τ).comap
        (Morse.fieldsUpTo hN c τ).subtype))).map (e : _ →ₗ[ℝ] _) =
      LinearMap.ker ((Morse.energyHessian hN hc.mem_pathSpace).restrict
        (Morse.brokenSpace hc B τ)) := by
    ext z
    rw [Submodule.mem_map_equiv, LinearMap.mem_ker, LinearMap.mem_ker, LinearMap.ext_iff,
      LinearMap.ext_iff]
    exact ⟨fun h w => h (e.symm w), fun h y => h (e y)⟩
  have hι : Injective ((Morse.pathTangent hN c).subtype.comp (Morse.brokenSpace hc B τ).subtype) :=
    (Submodule.injective_subtype _).comp (Submodule.injective_subtype _)
  haveI : FiniteDimensional ℝ ((LinearMap.ker ((Morse.energyHessian hN hc.mem_pathSpace).restrict
      (Morse.brokenSpace hc B τ))).map
        ((Morse.pathTangent hN c).subtype.comp (Morse.brokenSpace hc B τ).subtype)) :=
    Submodule.finiteDimensional_of_le LinearMap.map_le_range
  have hK : Module.rank ℝ (LinearMap.ker ((Morse.energyHessian hN hc.mem_pathSpace).restrict
      (Morse.brokenSpace hc B τ))) = Morse.conjMultiplicity hN c hc 0 τ := by
    rw [(Submodule.equivMapOfInjective _ hι _).rank_eq, ← Module.finrank_eq_rank,
      ← (Submodule.equivMapOfInjective _ hι _).finrank_eq, Morse.finrank_ker_broken hc hτ hτ1 hB]
  rw [Morse.lemma_15_4_ker hc hτ hτ1 hB,
    ← (Submodule.equivMapOfInjective _ (Submodule.injective_subtype _) _).rank_eq,
    (LinearEquiv.ofSubmodules e _ _ hmap).rank_eq, hK]

/-- `Items/V9_20.lean`'s hypothesis `LamEq`: B's `λ(τ)` is A's `indexUpTo τ`, `0 < τ ≤ 1`. -/
def LamEq {γ : ℝ → Bridge.Sub hN} (hc : Morse.IsSmoothCurveIn hN (Bridge.incl hN ∘ γ)) : Prop :=
  ∀ τ : ℝ, 0 < τ → τ ≤ 1 → lam (n := n) τ γ = Morse.indexUpTo hN (Bridge.incl hN ∘ γ) hc τ

/-- **`LamEq` holds for every geodesic of `↥N`** (EnergyC2 + the Hessian dictionary). -/
theorem lamEq {γ : ℝ → Bridge.Sub hN} (hgeo : IsGeodesic (Bridge.conn (hN := hN)) γ (Icc 0 1))
    (hc : Morse.IsSmoothCurveIn hN (Bridge.incl hN ∘ γ)) : LamEq (n := n) hc :=
  fun _ hτ hτ1 => lam_eq_indexUpTo hτ hτ1 hgeo hc

end Emb

/-- `Items/V13_3.lean`'s hypothesis `LamEq` (there `Emb`-free): B's `λ(1)` of a blind geodesic of
`↥N` is `Morse.formIndex` of `energyHessian` of `incl ∘ γ`. -/
def Emb.LamEqOne : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (W : Type) [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] (n : ℕ)
    (N : Set V) (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N)
    (p q : Bridge.Sub hN) (γ : ℝ → Bridge.Sub hN)
    (hc : Bridge.incl hN ∘ γ ∈ Morse.pathSpace N (Bridge.incl hN p) (Bridge.incl hN q)),
    IsGeodesic (Bridge.conn (hN := hN)) γ (Icc 0 1) →
    lam (n := n) 1 γ = Morse.formIndex (Morse.energyHessian hN hc)

/-- **`LamEqOne` holds** (`lam_eq_indexUpTo` at `τ = 1` and `Morse.indexUpTo_one`). -/
theorem Emb.lamEqOne : Emb.LamEqOne := by
  intro V _ _ _ W _ _ _ n N hN p q γ hc hgeo
  have hcs := Emb.isSmoothCurveIn (hgeo.2.1 : IsSmoothCurve (n := n) γ (Icc 0 1))
  rw [Emb.lam_eq_indexUpTo one_pos le_rfl hgeo hcs, Morse.indexUpTo_one]
  congr 1


/-! ### The embedded special case (second attempt) -/

/-- B on embedded manifolds: `M = ↥N` (model `ℝⁿ`, induced metric), induced connection
(`B_to_B_emb`). -/
def B_emb : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (W : Type) [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] (n : ℕ)
    (N : Set V) (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N)
    [ConnectedSpace (Bridge.Sub hN)] (γ : ℝ → Bridge.Sub hN),
    IsGeodesic (Bridge.conn (hN := hN)) γ (Set.Icc 0 1) →
  ∀ τ : ℝ, 0 < τ → τ < 1 → ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 < ε → ε < δ → τ + ε ≤ 1 →
    lam (n := n) (τ + ε) γ = lam (n := n) τ γ +
      setDim (bNullSet (TOm (n := n) τ γ) (HessT (n := n) τ γ))

theorem B_to_B_emb : B → B_emb := fun hB _ _ _ _ _ _ _ _ n _ hN _ =>
  hB n (Bridge.Sub hN) (Bridge.conn (hN := hN)) Bridge.conn_isLC

/-- **`A ⇒ B_emb`**: on `↥N`, B's `λ(σ)` is A's `indexUpTo σ` (`Emb.lam_eq_indexUpTo`: Lemma 11.A
and Theorem 13.1 for `E_0^σ`, `EnergyC2`, `TΩ` dictionary, index transport) and B's nullity `ν` of
`(E_0^τ)_**` is `conjMultiplicity 0 τ` (`Emb.setDim_bNullSet_T`, `Emb.rank_ker_fieldsUpTo`: Lemma
15.4 for the null space, item V9_19); then A's `assertion_4` gives B's `δ`. -/
theorem A_to_B_emb : A → B_emb := by
  intro hA V _ _ _ W _ _ _ n N hN _ γ hgeo τ hτ hτ1
  have hcs := Emb.isSmoothCurveIn (hgeo.2.1 : IsSmoothCurve (n := n) γ (Icc 0 1))
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 (hA.2.2.2.2 hcs hτ hτ1)
  refine ⟨u - τ, sub_pos.2 hu, fun ε hε hεδ hε1 => ?_⟩
  have h : τ + ε ∈ Ioo τ u := ⟨by linarith, by linarith⟩
  have h' := hsub h
  rw [Emb.lam_eq_indexUpTo (by linarith) hε1 hgeo hcs, Emb.lam_eq_indexUpTo hτ hτ1.le hgeo hcs,
    Emb.setDim_bNullSet_T hτ hτ1.le hgeo hcs, Emb.rank_ker_fieldsUpTo hcs hτ hτ1.le,
    Cardinal.toENat_nat]
  exact h'

#rt_check RoundTrip.V9_23.A_to_B_emb [Morse.assertion_4_le, Morse.energyHessian_cut,
  Morse.exists_dual, Morse.assertion_4_ge, Morse.assertion_4]
#rt_overlap RoundTrip.V9_23.A_to_B_emb [Morse.assertion_4_le, Morse.energyHessian_cut,
  Morse.exists_dual, Morse.assertion_4_ge, Morse.assertion_4]

/-- A's main conjunct `assertion_4` for the geodesics of connected slice submanifolds modelled on
`ℝⁿ`, written as `incl ∘ γ` with `γ` a blind geodesic of `↥N` (every unbroken geodesic of `N` is
one on `[0, 1]`, which is all that `indexUpTo`/`conjMultiplicity` see). -/
def A_geo : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (W : Type) [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] (n : ℕ)
    (N : Set V) (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N)
    [ConnectedSpace (Bridge.Sub hN)] (γ : ℝ → Bridge.Sub hN),
    IsGeodesic (Bridge.conn (hN := hN)) γ (Set.Icc 0 1) →
    ∀ (hc : Morse.IsSmoothCurveIn hN (Bridge.incl hN ∘ γ)) {τ : ℝ}, 0 < τ → τ < 1 →
      ∀ᶠ τ' in 𝓝[>] τ, Morse.indexUpTo hN (Bridge.incl hN ∘ γ) hc τ' =
        Morse.indexUpTo hN (Bridge.incl hN ∘ γ) hc τ +
          Morse.conjMultiplicity hN (Bridge.incl hN ∘ γ) hc 0 τ

theorem A_to_A_geo : A → A_geo := by
  intro hA V _ _ _ W _ _ _ n N hN _ γ _ hc τ hτ hτ1
  exact hA.2.2.2.2 hc hτ hτ1

/-- **`B_emb ⇒ A_geo`**: the same dictionary turns B's `λ(τ+ε) = λ(τ) + ν` into A's
`indexUpTo (τ+ε) = indexUpTo τ + conjMultiplicity 0 τ`. -/
theorem B_emb_to_A_geo : B_emb → A_geo := by
  intro hB V _ _ _ W _ _ _ n N hN _ γ hgeo hc τ hτ hτ1
  obtain ⟨δ, hδ, h⟩ := hB V W n N hN γ hgeo τ hτ hτ1
  refine mem_nhdsGT_iff_exists_Ioo_subset.2 ⟨τ + min δ (1 - τ), ?_, fun τ' hτ' => ?_⟩
  · show τ < τ + min δ (1 - τ)
    have : 0 < min δ (1 - τ) := lt_min hδ (by linarith)
    linarith
  · have hm1 := min_le_left δ (1 - τ)
    have hm2 := min_le_right δ (1 - τ)
    have h' := h (τ' - τ) (by linarith [hτ'.1]) (by linarith [hτ'.2]) (by linarith [hτ'.2])
    have e : τ + (τ' - τ) = τ' := by ring
    rw [e, Emb.lam_eq_indexUpTo (hτ.trans hτ'.1) (by linarith [hτ'.2]) hgeo hc,
      Emb.lam_eq_indexUpTo hτ hτ1.le hgeo hc, Emb.setDim_bNullSet_T hτ hτ1.le hgeo hc,
      Emb.rank_ker_fieldsUpTo hc hτ hτ1.le, Cardinal.toENat_nat] at h'
    exact h'

theorem B_to_A_geo : B → A_geo := fun hB => B_emb_to_A_geo (B_to_B_emb hB)

#rt_check RoundTrip.V9_23.B_to_A_geo [Morse.assertion_4_le, Morse.energyHessian_cut,
  Morse.exists_dual, Morse.assertion_4_ge, Morse.assertion_4]
#rt_overlap RoundTrip.V9_23.B_to_A_geo [Morse.assertion_4_le, Morse.energyHessian_cut,
  Morse.exists_dual, Morse.assertion_4_ge, Morse.assertion_4]

/-! ### For the coordinator: `LamEq` is now a theorem

`Emb.lamEq` (statement of `LamEq` in `Items/V9_20.lean`, `V9_22.lean`: `lam τ γ = indexUpTo τ`,
`0 < τ ≤ 1`) and `Emb.lamEqOne` (statement of `LamEq` in `Items/V13_3.lean`, and, specialized to the
sphere, `V10_23`, `V13_4`, `V13_5`, `V13_7`: `lam 1 γ = formIndex (energyHessian hc)`). The checks
below confirm that neither uses a theorem of those items. -/

#rt_check RoundTrip.V9_23.Emb.lamEq [Morse.indexUpTo_one, Morse.indexUpTo_mono,
  Morse.indexUpTo_eq_zero, Morse.assertion_3, Morse.eq_finsum_of_jumps, Morse.indexUpTo_one_eq,
  Morse.theorem_15_1]
#rt_check RoundTrip.V9_23.Emb.lamEqOne [Morse.theorem_22_1_bijective,
  Morse.theorem_22_1_surjective, Morse.corollary_22_2, Morse.corollary_22_2_surjective,
  Morse.corollary_22_2_mulEquiv, Morse.corollary_22_2_surjective_hom,
  Morse.formIndex_greatCircle_antipode, Morse.le_formIndex_of_not_minimal_sph,
  Morse.mul_pi_lt_sphLen, Morse.energy_sphGeod, Morse.exists_eqOn_sphGeod,
  Morse.notMem_conjLocus_sph, Morse.formIndex_sphGeod, Morse.formIndex_eq_of_eqOn_sphGeod,
  Morse.assertion_3, Morse.eq_finsum_of_jumps, Morse.indexUpTo_one_eq, Morse.theorem_15_1]

end RoundTrip.V9_23

