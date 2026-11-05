import Morse
import RoundTrip.Check
import RoundTrip.Blind.V9_6
import RoundTrip.Bridge
import RoundTrip.EnergyC2

open scoped Manifold ContDiff

namespace RoundTrip.V9_6

/-- The project's statement (universes instantiated at 0), for a slice submanifold `N ⊆ V`, a path
`γ ∈ Ω(N; p, q)` which is an unbroken geodesic: the null space of `E_**` (the image under
`X ↦ X ∘ projIcc` of the kernel of the bilinear form `energyHessian` on `TΩ_γ`, `energyHessian`
defined by the second variation formula) equals the space `conjSpace … 0 1` of Jacobi fields
(normalized constant off `[0,1]`) vanishing at `0` and `1`; the nullity (`finrank`, ℕ-valued) is the
multiplicity `conjMultiplicity … 0 1`; and `0 < nullity ↔ IsConjugate hN γ 0 1`. -/
def A : Prop :=
  type_of% @Morse.hessNullSpace_eq.{0,0,0} ∧
    type_of% @Morse.theorem_14_1_nullity.{0,0,0} ∧
    type_of% @Morse.hessNullity_pos_iff.{0,0,0}

theorem A_holds : A :=
  ⟨@Morse.hessNullSpace_eq, @Morse.theorem_14_1_nullity, @Morse.hessNullity_pos_iff⟩

/-- B ⇒ A, vacuously: A is re-proved outright from Theorem 14.1 (`Morse.theorem_14_1`, item V9_5),
`Morse.isConjugate_iff` (item V9_4) and the definitions (the project's own short proofs); B, about
abstract manifolds and the variational `E_**`, is not used. -/
theorem B_to_A : B → A := by
  intro _
  have hnull : ∀ {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
      {Z : Type} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
      {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
      {N : Set V} {hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N} {γ : ℝ → V} {p q : V}
      (hγ : γ ∈ Morse.pathSpace N p q) (hgeo : Morse.IsUnbrokenGeodesic hN γ),
      Morse.hessNullSpace hN hγ = Morse.conjSpace hN γ (hgeo.isSmoothCurveIn hN hγ) 0 1 := by
    intro V _ _ _ Z _ _ _ W _ _ _ N hN γ p q hγ hgeo
    set hc := hgeo.isSmoothCurveIn hN hγ
    ext J
    rw [Morse.mem_conjSpace hc]
    constructor
    · rintro ⟨X, hX, rfl⟩
      rw [SetLike.mem_coe, LinearMap.mem_ker] at hX
      have hJ : Morse.IsJacobiField hN γ X := (Morse.theorem_14_1 hγ hgeo X).1 fun Y => by
        simpa using congrArg (fun f => f Y) hX
      refine ⟨hJ.comp_projIcc_mem hc, ?_, ?_⟩
      · simp [Morse.restrictIcc, X.2.2.2.1]
      · simp [Morse.restrictIcc, X.2.2.2.2]
    · rintro ⟨hJ, h0, h1⟩
      refine ⟨⟨J, hJ.1.mem_pathTangent h0 h1⟩, ?_, ?_⟩
      · rw [SetLike.mem_coe, LinearMap.mem_ker]
        ext Y
        exact (Morse.theorem_14_1 hγ hgeo ⟨J, hJ.1.mem_pathTangent h0 h1⟩).2 hJ.1 Y
      · funext t
        exact (hJ.2 t).symm
  have hnul : ∀ {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
      {Z : Type} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
      {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
      {N : Set V} {hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N} {γ : ℝ → V} {p q : V}
      (hγ : γ ∈ Morse.pathSpace N p q) (hgeo : Morse.IsUnbrokenGeodesic hN γ),
      Morse.hessNullity hN hγ = Morse.conjMultiplicity hN γ (hgeo.isSmoothCurveIn hN hγ) 0 1 := by
    intro V _ _ _ Z _ _ _ W _ _ _ N hN γ p q hγ hgeo
    rw [Morse.hessNullity, hnull hγ hgeo, Morse.conjMultiplicity]
  refine ⟨@hnull, @hnul, ?_⟩
  intro V _ _ _ Z _ _ _ W _ _ _ N hN γ p q hγ hgeo
  rw [hnul hγ hgeo, Morse.isConjugate_iff (hgeo.isSmoothCurveIn hN hγ)]
  simp [zero_ne_one]

#rt_check RoundTrip.V9_6.B_to_A [Morse.hessNullSpace_eq, Morse.theorem_14_1_nullity,
  Morse.hessNullity_pos_iff]
#rt_overlap RoundTrip.V9_6.B_to_A [Morse.hessNullSpace_eq, Morse.theorem_14_1_nullity,
  Morse.hessNullity_pos_iff]


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

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] {n : ℕ} {N : Set V}
  {hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N}

/-- A project unbroken geodesic is a blind geodesic on `[0, 1]` (copied from `Items/V8_10.lean`). -/
theorem isGeodesic_of_isUnbrokenGeodesic {pw : ℝ → Bridge.Sub hN}
    (h : Morse.IsUnbrokenGeodesic hN (Bridge.incl hN ∘ pw)) :
    IsGeodesic (Bridge.conn (hN := hN)) pw (Icc 0 1) := by
  show RoundTrip.BridgePrelude.IsGeodesic _ _ _
  refine Bridge.isGeodesic_iff.2 ⟨⟨ordConnected_Icc, uniqueDiffOn_Icc zero_lt_one⟩, h.1, ?_⟩
  set f := Bridge.incl hN ∘ pw
  set I := Icc (0 : ℝ) 1
  have uI : UniqueDiffOn ℝ I := uniqueDiffOn_Icc zero_lt_one
  have hg : ContinuousOn (derivWithin (derivWithin f I) I) I :=
    ((h.1.derivWithin uI (m := ∞) (by simp)).derivWithin uI (m := 0) (by simp)).continuousOn
  have hpw : ContinuousOn pw I := fun t ht =>
    (Topology.IsInducing.subtypeVal.continuousWithinAt_iff (f := pw)).2 (h.1.continuousOn t ht)
  have hP : ContinuousOn (fun t => Bridge.P hN (pw t)) I :=
    Bridge.contMDiff_P.continuous.comp_continuousOn hpw
  have hcont : ContinuousOn
      (fun t => Bridge.P hN (pw t) (derivWithin (derivWithin f I) I t)) I := hP.clm_apply hg
  have hzero : EqOn (fun t => Bridge.P hN (pw t) (derivWithin (derivWithin f I) I t)) 0
      (Ioo 0 1) := by
    intro t ht
    have h1 : deriv f =ᶠ[𝓝 t] derivWithin f I := by
      filter_upwards [isOpen_Ioo.mem_nhds ht] with τ hτ
      exact (derivWithin_of_mem_nhds (Icc_mem_nhds hτ.1 hτ.2)).symm
    have e : derivWithin (derivWithin f I) I t = deriv (deriv f) t := by
      rw [h1.deriv_eq, derivWithin_of_mem_nhds (Icc_mem_nhds ht.1 ht.2)]
    show Bridge.P hN (pw t) _ = 0
    rw [e]
    exact (Morse.tanProj_eq_zero_iff hN).2 (h.2.normal t ht)
  intro t ht
  exact hzero.of_subset_closure hcont continuousOn_const Ioo_subset_Icc_self
    (by rw [closure_Ioo zero_ne_one]) ht

theorem isUnbrokenGeodesic_congr {c c' : ℝ → V} (h : EqOn c c' (Icc 0 1))
    (hc : Morse.IsUnbrokenGeodesic hN c) : Morse.IsUnbrokenGeodesic hN c' :=
  ⟨hc.1.congr fun t ht => (h ht).symm, hc.2.congr fun t ht => h (Ioo_subset_Icc_self ht)⟩

/-- `secondVariation` only depends on the path on `[0, 1]`. -/
theorem sv_congr_path {c c' X₁ X₂ : ℝ → V} (h : ∀ t ∈ Icc (0 : ℝ) 1, c t = c' t) :
    Morse.secondVariation hN c X₁ X₂ = Morse.secondVariation hN c' X₁ X₂ := by
  have hev : ∀ t ∈ Ioo (0 : ℝ) 1, c =ᶠ[𝓝 t] c' := fun t ht => by
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with x hx
    exact h x (Ioo_subset_Icc_self hx)
  have hcov : ∀ t ∈ Ioo (0 : ℝ) 1, Morse.covD hN c X₁ =ᶠ[𝓝 t] Morse.covD hN c' X₁ :=
    fun t ht => by
      filter_upwards [Ioo_mem_nhds ht.1 ht.2] with x hx
      simp only [Morse.covD, h x (Ioo_subset_Icc_self hx)]
  rw [Morse.secondVariation, Morse.secondVariation]
  congr 1
  · congr 1
    exact finsum_mem_congr rfl fun t ht => by rw [h t (Ioo_subset_Icc_self ht)]
  · refine intervalIntegral.integral_congr_Ioo_of_le zero_le_one fun t ht => ?_
    simp only [Morse.covD, (hcov t ht).deriv_eq, h t (Ioo_subset_Icc_self ht), (hev t ht).deriv_eq]

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

namespace Emb

open RoundTrip.Bridge

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] {n : ℕ} {N : Set V}
  {hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Bridge.Rn n) W N}

/-- **Dictionary: conjugate points.** For a smooth curve `γ` in `N` on `[0,1]` and `a, b ∈ [0,1]`,
B's `IsConj` (for the induced connection) is the project's `IsConjugate`. -/
theorem isConj_iff {γ : ℝ → Bridge.Sub hN} (hγ : IsSmoothCurve (n := n) γ (Icc 0 1)) {a b : ℝ}
    (ha : a ∈ Icc (0 : ℝ) 1) (hb : b ∈ Icc (0 : ℝ) 1) :
    IsConj (conn (hN := hN)) γ a b ↔ Morse.IsConjugate hN (incl hN ∘ γ) a b := by
  constructor
  · rintro ⟨hab, J, ⟨hJ, hJo⟩, hJ0, hJa, hJb⟩
    obtain ⟨t, ht⟩ : ∃ t, J t ≠ 0 := by
      by_contra h
      push Not at h
      exact hJ0 (funext h)
    have htI : t ∈ Icc (0 : ℝ) 1 := by
      by_contra h
      exact ht (hJo t h)
    refine ⟨ha, hb, hab, ambA γ J, (isJacobi_iff hγ J).1 hJ, ?_, ?_, t, htI, ?_⟩
    · show D hN (γ a) (J a) = 0
      rw [hJa, D_tzero]
    · show D hN (γ b) (J b) = 0
      rw [hJb, D_tzero]
    · intro h
      exact ht (D_injective (γ t) (h.trans (D_tzero (γ t)).symm))
  · rintro ⟨-, -, hab, X, hX, hXa, hXb, t, ht, hXt⟩
    refine ⟨hab, toFA γ X, toFA_mem_JacOn hγ hX, ?_, ?_, ?_⟩
    · intro h
      apply hXt
      rw [← ambA_toFA hX.tangent ht]
      show D hN (γ t) (toFA γ X t) = 0
      rw [h]
      exact D_tzero (γ t)
    · rw [toFA_of_mem X ha, hXa, map_zero] <;> rfl
    · rw [toFA_of_mem X hb, hXb, map_zero] <;> rfl

/-- **Dictionary: multiplicity.** For a smooth curve `γ` in `N` on `[0,1]` and `a, b ∈ [0,1]`,
B's `conjMult` (an `ℕ∞`-valued dimension of a span) is the project's `conjMultiplicity`. -/
theorem conjMult_eq {γ : ℝ → Bridge.Sub hN} (hγ : IsSmoothCurve (n := n) γ (Icc 0 1)) {a b : ℝ}
    (ha : a ∈ Icc (0 : ℝ) 1) (hb : b ∈ Icc (0 : ℝ) 1) :
    conjMult (conn (hN := hN)) γ a b =
      (Morse.conjMultiplicity hN (incl hN ∘ γ) (isSmoothCurveIn hγ) a b : ℕ∞) := by
  have hc := isSmoothCurveIn hγ
  set C := Morse.conjSpace hN (incl hN ∘ γ) hc a b
  set S := {J : FA n γ | J ∈ JacOn (conn (hN := hN)) γ (Icc 0 1) ∧ J a = 0 ∧ J b = 0}
  set Φ : C →ₗ[ℝ] FA n γ := (toFAₗ γ).comp C.subtype
  have hmem : ∀ X : C, Φ X ∈ S := fun X => by
    obtain ⟨hXs, hXa, hXb⟩ := (Morse.mem_conjSpace hc).1 X.2
    refine ⟨toFA_mem_JacOn hγ hXs.1, ?_, ?_⟩
    · show toFA γ (X : ℝ → V) a = 0
      rw [toFA_of_mem _ ha, hXa, map_zero] <;> rfl
    · show toFA γ (X : ℝ → V) b = 0
      rw [toFA_of_mem _ hb, hXb, map_zero] <;> rfl
  have hinj : Injective Φ := fun X Y h => by
    have hX := ((Morse.mem_conjSpace hc).1 X.2).1
    have hY := ((Morse.mem_conjSpace hc).1 Y.2).1
    exact Subtype.ext (eq_of_eqOn_jacobiSpace hX hY (toFA_injOn hX.1.tangent hY.1.tangent h))
  have hspan : Submodule.span ℝ S = LinearMap.range Φ := by
    refine le_antisymm (Submodule.span_le.2 ?_) ?_
    · rintro J ⟨⟨hJ, hJo⟩, hJa, hJb⟩
      have hX := ((isJacobi_iff hγ J).1 hJ).comp_projIcc_mem hc
      have hXC : (fun t => ambA γ J (projIcc (0 : ℝ) 1 zero_le_one t)) ∈ C := by
        refine (Morse.mem_conjSpace hc).2 ⟨hX, ?_, ?_⟩
        · show ambA γ J (projIcc (0 : ℝ) 1 zero_le_one a) = 0
          rw [projIcc_of_mem _ ha]
          show D hN (γ a) (J a) = 0
          rw [hJa, D_tzero]
        · show ambA γ J (projIcc (0 : ℝ) 1 zero_le_one b) = 0
          rw [projIcc_of_mem _ hb]
          show D hN (γ b) (J b) = 0
          rw [hJb, D_tzero]
      refine ⟨⟨_, hXC⟩, funext fun t => ?_⟩
      by_cases ht : t ∈ Icc (0 : ℝ) 1
      · show toFA γ (fun t => ambA γ J (projIcc (0 : ℝ) 1 zero_le_one t)) t = J t
        rw [toFA_of_mem _ ht]
        simp only [projIcc_of_mem _ ht]
        exact L_D (γ t) (J t)
      · show toFA γ (fun t => ambA γ J (projIcc (0 : ℝ) 1 zero_le_one t)) t = J t
        rw [toFA_of_not_mem _ ht, hJo t ht]
    · rintro _ ⟨X, rfl⟩
      exact Submodule.subset_span (hmem X)
  unfold conjMult setDim
  rw [hspan, rank_range_of_injective Φ hinj, ← Module.finrank_eq_rank, Cardinal.toENat_nat]
  rfl

/-- Hence, on embedded manifolds, B's claim is literally A's (for geodesics, model `ℝⁿ`). -/
theorem isConj_iff_pos {γ : ℝ → Bridge.Sub hN} (hγ : IsSmoothCurve (n := n) γ (Icc 0 1)) {a b : ℝ}
    (ha : a ∈ Icc (0 : ℝ) 1) (hb : b ∈ Icc (0 : ℝ) 1) (hab : a ≠ b) :
    (IsConj (conn (hN := hN)) γ a b ↔ 0 < conjMult (conn (hN := hN)) γ a b) ↔
      (Morse.IsConjugate hN (incl hN ∘ γ) a b ↔
        a ∈ Icc (0 : ℝ) 1 ∧ b ∈ Icc (0 : ℝ) 1 ∧ a ≠ b ∧
          0 < Morse.conjMultiplicity hN (incl hN ∘ γ) (isSmoothCurveIn hγ) a b) := by
  rw [isConj_iff hγ ha hb, conjMult_eq hγ ha hb, Nat.cast_pos]
  simp only [ha, hb, hab, true_and, ne_eq, not_false_eq_true]

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

/-! ### The null space of the variational `E_**` on `↥N` -/

namespace Emb

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] {n : ℕ} {N : Set V}
  {hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N}

/-- `TΩ` membership only depends on the field on `[0, 1]`. -/
theorem mem_pathTangent_of_eqOn {c X Y : ℝ → V} (hX : X ∈ Morse.pathTangent hN c)
    (h : EqOn X Y (Icc 0 1)) : Y ∈ Morse.pathTangent hN c := by
  obtain ⟨⟨h01, hc, B, hB⟩, hT, h0, h1⟩ := (Morse.mem_pathTangent hN).1 hX
  refine (Morse.mem_pathTangent hN).2 ⟨⟨h01, hc.congr fun t ht => (h ht).symm, B,
    fun s u hs hsu hu hB' => (hB s u hs hsu hu hB').congr fun x hx =>
      (h ⟨hs.trans hx.1, hx.2.trans hu⟩).symm⟩, fun t ht => ?_, ?_, ?_⟩
  · rw [← h ht]; exact hT t ht
  · rw [← h ⟨le_rfl, zero_le_one⟩]; exact h0
  · rw [← h ⟨zero_le_one, le_rfl⟩]; exact h1

/-- **The blind null space is the project's** (transported by `toFA`): for a geodesic `γ'` of
`↥N` and a project path `γ` agreeing with `incl ∘ γ'` on `[0, 1]`, the null set of B's `HessT 1`
on the blind `TΩ_{γ'}` is the image under `toFA` of `Morse.hessNullSpace` (the restriction to
`[0, 1]` of the kernel of `energyHessian`). -/
theorem bNullSet_eq_image {γ' : ℝ → Bridge.Sub hN}
    (hgeo : IsGeodesic (Bridge.conn (hN := hN)) γ' (Icc 0 1)) {γ : ℝ → V} {p q : V}
    (hγ : γ ∈ Morse.pathSpace N p q) (heq : EqOn (Bridge.incl hN ∘ γ') γ (Icc 0 1)) :
    bNullSet (TOm (n := n) 1 γ') (HessT (n := n) 1 γ') =
      toFA γ' '' (Morse.hessNullSpace hN hγ : Set (ℝ → V)) := by
  have hγs : IsSmoothCurve (n := n) γ' (Icc 0 1) := hgeo.2.1
  have heq' : ∀ t ∈ Icc (0 : ℝ) 1, γ t = (Bridge.incl hN ∘ γ') t := fun t ht => (heq ht).symm
  have hsv : ∀ Y₁ Y₂ : ℝ → V, Morse.secondVariation hN γ Y₁ Y₂ =
      Morse.secondVariation hN (Bridge.incl hN ∘ γ') Y₁ Y₂ := fun _ _ => sv_congr_path heq'
  ext Wf
  constructor
  · rintro ⟨hW, hnull⟩
    have hW' : InTOmegaT (n := n) 1 γ' Wf := hW
    have hX' := mem_pathTangent_of_inTOmega (inTOmega_of_T hW')
    have hX : Bridge.ambA γ' Wf ∈ Morse.pathTangent hN γ := Morse.mem_pathTangent_congr hN heq hX'
    have hker : (⟨_, hX⟩ : Morse.pathTangent hN γ) ∈ LinearMap.ker (Morse.energyHessian hN hγ) := by
      rw [LinearMap.mem_ker]
      refine LinearMap.ext fun Y => ?_
      have hY' : (Y : ℝ → V) ∈ Morse.pathTangent hN (Bridge.incl hN ∘ γ') :=
        Morse.mem_pathTangent_congr hN heq' Y.2
      have hW₂ := inTOmegaT_toFA hγs hY'
      have h0 := hnull _ hW₂
      rw [hessT_eq hgeo hW' hW₂, Morse.secondVariation_congr hN (fun _ _ => rfl)
        (fun t ht => ambA_toFA ((Morse.mem_pathTangent hN).1 hY').2.1 ht)] at h0
      rw [Morse.energyHessian_apply, hsv, LinearMap.zero_apply]
      exact h0
    refine ⟨Morse.restrictIcc V (Bridge.ambA γ' Wf), Submodule.mem_map.2 ⟨_, hker, rfl⟩, ?_⟩
    funext t
    by_cases ht : t ∈ Icc (0 : ℝ) 1
    · rw [toFA_of_mem _ ht]
      show Bridge.L hN (γ' t) (Bridge.ambA γ' Wf (projIcc (0 : ℝ) 1 zero_le_one t)) = Wf t
      rw [projIcc_of_mem _ ht]
      exact Bridge.L_D (γ' t) (Wf t)
    · rw [toFA_of_not_mem _ ht, hW'.2.2.2 t ht]
  · rintro ⟨Z, hZ, rfl⟩
    obtain ⟨X, hXker, rfl⟩ := Submodule.mem_map.1 hZ
    have hXZ : EqOn (X : ℝ → V) (Morse.restrictIcc V (X : ℝ → V)) (Icc 0 1) := fun t ht => by
      show (X : ℝ → V) t = (X : ℝ → V) (projIcc (0 : ℝ) 1 zero_le_one t)
      rw [projIcc_of_mem _ ht]
    have hZ' : Morse.restrictIcc V (X : ℝ → V) ∈ Morse.pathTangent hN (Bridge.incl hN ∘ γ') :=
      mem_pathTangent_of_eqOn (Morse.mem_pathTangent_congr hN heq' X.2) hXZ
    have hW := inTOmegaT_toFA hγs hZ'
    refine ⟨hW, fun W₂ hW₂ => ?_⟩
    have hW₂' : InTOmegaT (n := n) 1 γ' W₂ := hW₂
    have hY := Morse.mem_pathTangent_congr hN heq (mem_pathTangent_of_inTOmega (inTOmega_of_T hW₂'))
    have h0 : Morse.energyHessian hN hγ X ⟨_, hY⟩ = 0 := by
      rw [LinearMap.mem_ker] at hXker
      rw [hXker, LinearMap.zero_apply]
    rw [Morse.energyHessian_apply, hsv] at h0
    show HessT (n := n) 1 γ' (toFA γ' (Morse.restrictIcc V (X : ℝ → V))) W₂ = 0
    rw [hessT_eq hgeo hW hW₂', Morse.secondVariation_congr hN
      (fun t ht => (ambA_toFA ((Morse.mem_pathTangent hN).1 hZ').2.1 ht).trans (hXZ ht).symm)
      (fun _ _ => rfl), h0]

/-- **B's nullity on `↥N` is the rank of the project's null space** `Morse.hessNullSpace`. -/
theorem setDim_bNullSet {γ' : ℝ → Bridge.Sub hN}
    (hgeo : IsGeodesic (Bridge.conn (hN := hN)) γ' (Icc 0 1)) {γ : ℝ → V} {p q : V}
    (hγ : γ ∈ Morse.pathSpace N p q) (heq : EqOn (Bridge.incl hN ∘ γ') γ (Icc 0 1)) :
    setDim (bNullSet (TOm (n := n) 1 γ') (HessT (n := n) 1 γ')) =
      (Module.rank ℝ (Morse.hessNullSpace hN hγ)).toENat := by
  set S := Morse.hessNullSpace hN hγ
  set Φ : S →ₗ[ℝ] FA n γ' := (toFAₗ γ').comp S.subtype
  -- elements of `S` are tangent on `[0, 1]` and constant off `[0, 1]`
  have hS : ∀ Z ∈ S, (∀ t ∈ Icc (0 : ℝ) 1,
      Morse.prj hN ((Bridge.incl hN ∘ γ') t) (Z t) = Z t) ∧
      ∀ t, Z t = Z (projIcc (0 : ℝ) 1 zero_le_one t) := by
    intro Z hZ
    obtain ⟨X, -, rfl⟩ := Submodule.mem_map.1 hZ
    refine ⟨fun t ht => ?_, fun t => ?_⟩
    · show Morse.prj hN _ ((X : ℝ → V) (projIcc (0 : ℝ) 1 zero_le_one t)) =
        (X : ℝ → V) (projIcc (0 : ℝ) 1 zero_le_one t)
      rw [projIcc_of_mem _ ht, heq ht]
      exact ((Morse.mem_pathTangent hN).1 X.2).2.1 t ht
    · show (X : ℝ → V) (projIcc (0 : ℝ) 1 zero_le_one t) =
        (X : ℝ → V) (projIcc (0 : ℝ) 1 zero_le_one (projIcc (0 : ℝ) 1 zero_le_one t))
      rw [projIcc_of_mem _ (projIcc (0 : ℝ) 1 zero_le_one t).2]
  have hinj : Injective Φ := fun Z Z' h => by
    have hZ := hS Z Z.2
    have hZ' := hS Z' Z'.2
    have h' := toFA_injOn hZ.1 hZ'.1 h
    refine Subtype.ext (funext fun t => ?_)
    rw [hZ.2 t, hZ'.2 t]
    exact h' (projIcc (0 : ℝ) 1 zero_le_one t).2
  have himg : toFA γ' '' (S : Set (ℝ → V)) = (LinearMap.range Φ : Set (FA n γ')) := by
    rw [LinearMap.range_comp, Submodule.range_subtype, Submodule.map_coe]
    rfl
  unfold setDim
  rw [bNullSet_eq_image hgeo hγ heq, himg, Submodule.span_eq, rank_range_of_injective Φ hinj]

/-- The space of Jacobi fields vanishing at `a, b` only depends on the curve on `[0, 1]`. -/
theorem conjSpace_congr {c c' : ℝ → V} (h : EqOn c c' (Icc 0 1)) (hc : Morse.IsSmoothCurveIn hN c)
    (hc' : Morse.IsSmoothCurveIn hN c') (a b : ℝ) :
    Morse.conjSpace hN c hc a b = Morse.conjSpace hN c' hc' a b := by
  ext J
  rw [Morse.mem_conjSpace hc, Morse.mem_conjSpace hc']
  exact ⟨fun ⟨⟨hJ, hn⟩, ha, hb⟩ => ⟨⟨hJ.congr_curve h, hn⟩, ha, hb⟩,
    fun ⟨⟨hJ, hn⟩, ha, hb⟩ => ⟨⟨hJ.congr_curve fun t ht => (h ht).symm, hn⟩, ha, hb⟩⟩

end Emb


/-! ### The embedded special case (second attempt) -/

/-- B on embedded manifolds: `M = ↥N` (model `ℝⁿ`, induced metric), induced connection
(`B_to_B_emb`). -/
def B_emb : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (W : Type) [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] (n : ℕ)
    (N : Set V) (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N)
    [ConnectedSpace (Bridge.Sub hN)] (γ : ℝ → Bridge.Sub hN),
    IsGeodesic (Bridge.conn (hN := hN)) γ (Set.Icc 0 1) →
  (0 < setDim (bNullSet (TOm (n := n) 1 γ) (HessT (n := n) 1 γ)) ↔
      IsConj (Bridge.conn (hN := hN)) γ 0 1) ∧
  setDim (bNullSet (TOm (n := n) 1 γ) (HessT (n := n) 1 γ)) =
      conjMult (Bridge.conn (hN := hN)) γ 0 1 ∧
  setDim (bNullSet (TOm (n := n) 1 γ) (HessT (n := n) 1 γ)) ≠ ⊤

theorem B_to_B_emb : B → B_emb := fun hB _ _ _ _ _ _ _ _ n _ hN _ =>
  hB n (Bridge.Sub hN) (Bridge.conn (hN := hN)) Bridge.conn_isLC

/-- **`A ⇒ B_emb`**: B's nullity (`setDim` of the null set of the variational `HessT 1`) is the
rank of the project's `hessNullSpace` (`Emb.setDim_bNullSet`: Hessian dictionary, Lemma 11.A,
`EnergyC2`, Theorem 13.1), which is finite and equal to `conjMultiplicity` by A
(`hessNullSpace_eq`, `theorem_14_1_nullity`); positivity is A's `hessNullity_pos_iff`; blind
`IsConj` / `conjMult` are the project's (`Items/V9_4.lean` dictionary). -/
theorem A_to_B_emb : A → B_emb := by
  intro hA V _ _ _ W _ _ _ n N hN _ γ hgeo
  have hγs : IsSmoothCurve (n := n) γ (Icc 0 1) := hgeo.2.1
  have hpath := Emb.mem_pathSpace_of_isGeodesic hgeo
  have hub := Emb.isUnbrokenGeodesic_of_isGeodesic hgeo
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have h1 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  have hfin : FiniteDimensional ℝ (Morse.hessNullSpace hN hpath) := by
    rw [hA.1 hpath hub]; infer_instance
  have hsd : setDim (bNullSet (TOm (n := n) 1 γ) (HessT (n := n) 1 γ)) =
      (Morse.hessNullity hN hpath : ℕ∞) := by
    rw [Emb.setDim_bNullSet hgeo hpath (fun _ _ => rfl), ← Module.finrank_eq_rank,
      Cardinal.toENat_nat]
    rfl
  rw [hsd, Emb.conjMult_eq hγs h0 h1, Nat.cast_pos, hA.2.2 hpath hub, Emb.isConj_iff hγs h0 h1]
  exact ⟨Iff.rfl, congrArg Nat.cast (hA.2.1 hpath hub), ENat.coe_ne_top _⟩

#rt_check RoundTrip.V9_6.A_to_B_emb [Morse.hessNullSpace_eq, Morse.theorem_14_1_nullity,
  Morse.hessNullity_pos_iff]
#rt_overlap RoundTrip.V9_6.A_to_B_emb [Morse.hessNullSpace_eq, Morse.theorem_14_1_nullity,
  Morse.hessNullity_pos_iff]

/-- A for connected slice submanifolds modelled on `ℝⁿ` (the setting of `B_emb`). -/
def A_emb : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (W : Type) [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] (n : ℕ)
    (N : Set V) (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N)
    [ConnectedSpace (Bridge.Sub hN)] {γ : ℝ → V} {p q : V} (hγ : γ ∈ Morse.pathSpace N p q)
    (hgeo : Morse.IsUnbrokenGeodesic hN γ),
    Morse.hessNullSpace hN hγ = Morse.conjSpace hN γ (hgeo.isSmoothCurveIn hN hγ) 0 1 ∧
    Morse.hessNullity hN hγ = Morse.conjMultiplicity hN γ (hgeo.isSmoothCurveIn hN hγ) 0 1 ∧
    (0 < Morse.hessNullity hN hγ ↔ Morse.IsConjugate hN γ 0 1)

theorem A_to_A_emb : A → A_emb := by
  intro hA V _ _ _ W _ _ _ n N hN _ γ p q hγ hgeo
  exact ⟨hA.1 hγ hgeo, hA.2.1 hγ hgeo, hA.2.2 hγ hgeo⟩

/-- **`B_emb ⇒ A_emb`**: B_emb gives `rank hessNullSpace = conjMultiplicity` (finite) through
`Emb.setDim_bNullSet`; the easy half of Theorem 14.1 (Jacobi fields are null:
`IsJacobiField.secondVariation_eq_zero`, not a theorem of this item) gives
`conjSpace ≤ hessNullSpace`; equal finite dimensions give `hessNullSpace = conjSpace`, and the
rest is `Morse.isConjugate_iff` (item V9_4). -/
theorem B_emb_to_A_emb : B_emb → A_emb := by
  intro hB V _ _ _ W _ _ _ n N hN _ γ p q hγ hgeo
  set hc := hgeo.isSmoothCurveIn hN hγ
  let q₀ : Bridge.Sub hN := (⟨γ 0, hγ.2.1 0 ⟨le_rfl, zero_le_one⟩⟩ : N)
  set γ' := Bridge.lift γ q₀
  have heq : EqOn (Bridge.incl hN ∘ γ') γ (Icc 0 1) := fun t ht =>
    Bridge.incl_lift q₀ (hγ.2.1 t ht)
  have hgeo' : IsGeodesic (Bridge.conn (hN := hN)) γ' (Icc 0 1) :=
    Emb.isGeodesic_of_isUnbrokenGeodesic
      (Emb.isUnbrokenGeodesic_congr (fun t ht => (heq ht).symm) hgeo)
  have hγs : IsSmoothCurve (n := n) γ' (Icc 0 1) := hgeo'.2.1
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have h1 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  obtain ⟨-, hmult, -⟩ := hB V W n N hN γ' hgeo'
  rw [Emb.setDim_bNullSet hgeo' hγ heq, Emb.conjMult_eq hγs h0 h1] at hmult
  have hcm : Morse.conjMultiplicity hN (Bridge.incl hN ∘ γ') (Emb.isSmoothCurveIn hγs) 0 1 =
      Morse.conjMultiplicity hN γ hc 0 1 := by
    unfold Morse.conjMultiplicity
    rw [Emb.conjSpace_congr heq (Emb.isSmoothCurveIn hγs) hc]
  rw [hcm] at hmult
  have hr : Module.rank ℝ (Morse.hessNullSpace hN hγ) = (Morse.conjMultiplicity hN γ hc 0 1 : Cardinal) :=
    Cardinal.toENat_eq_natCast.1 hmult
  haveI : FiniteDimensional ℝ (Morse.hessNullSpace hN hγ) := Module.finite_of_rank_eq_nat hr
  have hfr : Module.finrank ℝ (Morse.hessNullSpace hN hγ) = Morse.conjMultiplicity hN γ hc 0 1 :=
    Module.finrank_eq_of_rank_eq hr
  -- the easy half of Theorem 14.1
  have hle : Morse.conjSpace hN γ hc 0 1 ≤ Morse.hessNullSpace hN hγ := by
    intro J hJ
    obtain ⟨hJs, hJ0, hJ1⟩ := (Morse.mem_conjSpace hc).1 hJ
    have hJT : J ∈ Morse.pathTangent hN γ := hJs.1.mem_pathTangent hJ0 hJ1
    refine Submodule.mem_map.2 ⟨⟨J, hJT⟩, ?_, ?_⟩
    · rw [LinearMap.mem_ker]
      refine LinearMap.ext fun Y => ?_
      rw [Morse.energyHessian_apply, LinearMap.zero_apply, hJs.1.secondVariation_eq_zero, mul_zero]
    · funext t
      exact (hJs.2 t).symm
  have hEq : Morse.hessNullSpace hN hγ = Morse.conjSpace hN γ hc 0 1 :=
    (Submodule.eq_of_le_of_finrank_eq hle (by rw [hfr]; rfl)).symm
  refine ⟨hEq, hfr, ?_⟩
  rw [Morse.hessNullity, hfr, Morse.isConjugate_iff hc]
  simp [zero_ne_one]

theorem B_to_A_emb : B → A_emb := fun hB => B_emb_to_A_emb (B_to_B_emb hB)

#rt_check RoundTrip.V9_6.B_to_A_emb [Morse.hessNullSpace_eq, Morse.theorem_14_1_nullity,
  Morse.hessNullity_pos_iff]
#rt_overlap RoundTrip.V9_6.B_to_A_emb [Morse.hessNullSpace_eq, Morse.theorem_14_1_nullity,
  Morse.hessNullity_pos_iff]

end RoundTrip.V9_6

