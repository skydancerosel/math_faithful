import Morse
import RoundTrip.Check
import RoundTrip.Blind.V8_18
import RoundTrip.Bridge
import RoundTrip.EnergyC2

open Set Filter Topology
open scoped ContDiff Manifold

namespace RoundTrip.V8_18

/-- The project's statement (universes instantiated at 0), for a slice submanifold `N ⊆ V` with the
induced metric: if `γ` is a minimal path of `Ω(N; p, q)` (`IsMinimalPath`: `γ ∈ Ω(N; p, q)` and
its length on `[0,1]` is `≤` that of every path of `Ω(N; p, q)`) and an unbroken geodesic, then
`0 ≤ E_**(X, X)` for every `X ∈ TΩ_γ`, `E_** = energyHessian hN hmin.1` the bilinear form defined
by Milnor's formula 13.1 (positive semi-definiteness only; "index 0" is not stated separately). -/
def A : Prop := type_of% @Morse.lemma_13_6.{0,0,0}

theorem A_holds : A := @Morse.lemma_13_6

/-! ### B ⇒ A: only vacuously

A is proved outright by re-running the project's proof (Lemma 11.A gives a variation with field
`X`; `u ↦ E(ᾱ(u))` has a local minimum at `0` (minimality, `E = L²` for a geodesic); its second
derivative at `0` is `E_**(X, X)` by Remark 13.5 (`Morse.hasDerivAt_deriv_energy`, a project
theorem outside this item); a negative second derivative would make `0` a local maximum too).
B (about abstract manifolds) is not used and could not be. -/

namespace Aux

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {Z : Type} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
  {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {N : Set V} (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N)

theorem lemma_13_6' {γ : ℝ → V} {p q : V} (hmin : Morse.IsMinimalPath N γ p q)
    (hgeo : Morse.IsUnbrokenGeodesic hN γ)
    (X : Morse.pathTangent hN γ) : 0 ≤ Morse.energyHessian hN hmin.1 X X := by
  by_contra hneg
  push Not at hneg
  obtain ⟨ε, hε, B, hα, h0, hd⟩ := Morse.exists_variation_one hN hmin.1 X.2
  set α : ℝ → ℝ → V := fun u t => Morse.exp hN (γ t) (u • (X : ℝ → V) t)
  have hαγ : ∀ t ∈ Icc (0 : ℝ) 1, α 0 t = γ t := h0
  set f : ℝ → ℝ := fun u => Morse.energy (α u) 0 1
  have hmin' : IsLocalMin f 0 := by
    filter_upwards [isOpen_Ioo.mem_nhds (show (0 : ℝ) ∈ Ioo (-ε) ε from ⟨by linarith, hε⟩)]
      with u hu
    have hpath := hα.mem_pathSpace hu
    rw [show α 0 0 = p from (hαγ 0 ⟨le_rfl, zero_le_one⟩).trans hmin.1.2.2.1,
      show α 0 1 = q from (hαγ 1 ⟨zero_le_one, le_rfl⟩).trans hmin.1.2.2.2] at hpath
    calc f 0 = Morse.energy γ 0 1 := Morse.energy_congr hαγ
      _ ≤ f u := Morse.energy_le_of_isMinimalPath hN hmin hgeo hpath
  have hdd := Morse.hasDerivAt_deriv_energy hN hmin.1 hgeo hα hαγ
  have hW : Morse.energyHessian hN hmin.1
      ⟨_, Morse.mem_pathTangent_congr hN hαγ (hα.varField_mem hN)⟩
      ⟨_, Morse.mem_pathTangent_congr hN hαγ (hα.varField_mem hN)⟩ =
        Morse.energyHessian hN hmin.1 X X := by
    rw [Morse.energyHessian_apply, Morse.energyHessian_apply]
    exact congrArg _ (Morse.secondVariation_congr hN hd hd)
  rw [hW] at hdd
  have hf : HasDerivAt f _ 0 := hα.hasDerivAt_energy hN hα.zero_mem
  have hmax : IsLocalMax f 0 :=
    isLocalMax_of_deriv_deriv_neg (by rw [hdd.deriv]; exact hneg)
      hmin'.deriv_eq_zero hf.continuousAt
  have hconst : f =ᶠ[𝓝 0] fun _ => f 0 := by
    filter_upwards [hmin', hmax] with u h1 h2
    exact le_antisymm h2 h1
  have h0' : deriv (deriv f) 0 = 0 := by
    rw [hconst.deriv.deriv_eq]
    simp
  rw [hdd.deriv] at h0'
  exact hneg.ne h0'

end Aux

/-- Vacuous: A is proved outright; B is not used. -/
theorem B_to_A : B → A := fun _ => @Aux.lemma_13_6'

#rt_check RoundTrip.V8_18.B_to_A [Morse.lemma_13_6]
#rt_overlap RoundTrip.V8_18.B_to_A [Morse.lemma_13_6]

/-! A ⇒ B is not proved; see `V8_18.json`. -/

/-! ## Second attempt (with `RoundTrip.EnergyC2`): the variational `E_**` on embedded manifolds

Dictionary for 2-parameter variations on `↥N` (namespace `Emb`): a blind `IsVarSub U α k t`
(`U ⊆ ℝ²`) is a project `IsVariation` of the ambient family `amb α`; its fields are the line
derivatives along `r ↦ r eᵢ` (`D_varField`); by `EnergyC2`, `u ↦ E(α u)` is `C^∞`, so the
blind `DifferentiableAt` clause holds and `mixedD` is the project's iterated derivative
(`hess_data`); hence every blind `IsHess` value is `2 secondVariation` of the ambient fields
(`hess_eq`, from Theorem 13.1 taken as the hypothesis `SV hN`). Conversely every pair of blind
fields `W₁, W₂ ∈ TΩ_γ` has an `IsHess` value (`exists_isHess`): Lemma 11.A
(`Morse.exists_variation` with `P = ℝ²`) gives `α(u, t) = exp_{γ(t)}(u₀ W₁(t) + u₁ W₂(t))`, and
the same formula has the prescribed `∂α/∂uᵢ (0, t)` at every `t ∈ ℝ` (blind `IsHess` matches the
fields on all of `ℝ`), since `exp` is smooth near the zero section with `d(exp_q)₀ = id`. -/

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

/-- B on embedded manifolds: `M = ↥N` with the induced metric and the induced Levi-Civita
connection (a special case of B, see `B_to_B_emb`). -/
def B_emb : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (W : Type) [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] (n : ℕ)
    (N : Set V) (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N)
    [ConnectedSpace (Bridge.Sub hN)],
    ∀ γ : ℝ → Bridge.Sub hN, IsMinimal (Bridge.conn (hN := hN)) γ 0 1 →
    (∀ W : FA n γ, InTOmega (n := n) γ W → ∀ r : ℝ, IsHess (n := n) γ W W r → 0 ≤ r) ∧
    ∀ S : Submodule ℝ (FA n γ), (∀ W ∈ S, InTOmega (n := n) γ W) →
      (∀ W ∈ S, W ≠ 0 → ∀ r : ℝ, IsHess (n := n) γ W W r → r < 0) → S = ⊥

/-- `B_emb` is a special case of B (the induced connection is Levi-Civita, `Bridge.conn_isLC`). -/
theorem B_to_B_emb : B → B_emb := fun hB _ _ _ _ _ _ _ _ n _ hN _ =>
  hB n (Bridge.Sub hN) (Bridge.conn (hN := hN)) Bridge.conn_isLC

namespace Emb

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] {n : ℕ} {N : Set V}
  {hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N}

/-- **Dictionary: minimal geodesics.** A blind minimal geodesic on `[0, 1]` (length `≤` that of
every blind piecewise smooth path, on any parameter interval, with the same end points) is a
project minimal path (`Morse.IsMinimalPath`): lift the competitors with `Bridge.lift`
(`Bridge.isPW_lift`) and compare lengths with `Bridge.arcLen_eq`. -/
theorem isMinimalPath_of_isMinimal {γ : ℝ → Bridge.Sub hN}
    (h : IsMinimal (Bridge.conn (hN := hN)) γ 0 1) :
    Morse.IsMinimalPath N (Bridge.incl hN ∘ γ) (Bridge.incl hN (γ 0)) (Bridge.incl hN (γ 1)) := by
  refine ⟨mem_pathSpace_of_isGeodesic h.1, fun c hc => ?_⟩
  obtain ⟨hcs, hcN, hc0, hc1⟩ := hc
  have hpw : IsPW (n := n) (Bridge.lift c (γ 0)) 0 1 := Bridge.isPW_lift hcs hcN (γ 0)
  have hinj : Function.Injective (Bridge.incl hN) := Subtype.val_injective
  have h0 : Bridge.lift c (γ 0) 0 = γ 0 :=
    hinj ((Bridge.incl_lift (γ 0) (hcN 0 ⟨le_rfl, zero_le_one⟩)).trans hc0)
  have h1 : Bridge.lift c (γ 0) 1 = γ 1 :=
    hinj ((Bridge.incl_lift (γ 0) (hcN 1 ⟨zero_le_one, le_rfl⟩)).trans hc1)
  have hle := h.2 _ 0 1 zero_le_one hpw h0 h1
  have e1 : arcLen (n := n) γ 0 1 = Morse.pathLength (Bridge.incl hN ∘ γ) 0 1 :=
    Bridge.arcLen_eq γ 0 1
  have e2 : arcLen (n := n) (Bridge.lift c (γ 0)) 0 1 = Morse.pathLength c 0 1 :=
    (Bridge.arcLen_eq _ 0 1).trans (Bridge.pathLength_congr zero_le_one fun t ht =>
      Bridge.incl_lift (γ 0) (hcN t ht))
  rw [← e1, ← e2]
  exact hle

end Emb

/-- **`A ⇒ B_emb`**: every blind `IsHess γ W W r` is `E_**(W, W)` of the ambient field
(`Emb.hess_eq`: `EnergyC2` and Theorem 13.1, the project's `Morse.second_variation`, not part of
A), which is `≥ 0` by A at the project minimal path `γ` (`Emb.isMinimalPath_of_isMinimal`); and
every `W ∈ TΩ_γ` has an `IsHess` value (`Emb.exists_isHess`, Lemma 11.A on `↥N`), so a subspace
on which all `IsHess` values are negative is `0`. -/
theorem A_to_B_emb : A → B_emb := by
  intro hA V _ _ _ W _ _ _ n N hN _ γ hmin
  have hgeo := hmin.1
  have hsv : Emb.SV hN := by
    intro _ _ _ _ hub _ _ _ hα hαγ
    exact Morse.second_variation hN hub hα hαγ
  have hmp := Emb.isMinimalPath_of_isMinimal hmin
  have hub := Emb.isUnbrokenGeodesic_of_isGeodesic hgeo
  have hpsd : ∀ X : FA n γ, InTOmega (n := n) γ X → ∀ r, IsHess (n := n) γ X X r → 0 ≤ r := by
    intro X hX r hr
    rw [Emb.hess_eq hsv hgeo hr]
    exact hA hN hmp hub ⟨_, Emb.mem_pathTangent_of_inTOmega hX⟩
  refine ⟨hpsd, fun S hS hneg => (Submodule.eq_bot_iff S).2 fun X hX => ?_⟩
  by_contra hX0
  obtain ⟨r, hr⟩ := Emb.exists_isHess hgeo (hS X hX) (hS X hX)
  exact absurd (hpsd X (hS X hX) r hr) (not_le.2 (hneg X hX hX0 r hr))

#rt_check RoundTrip.V8_18.A_to_B_emb [Morse.lemma_13_6]
#rt_overlap RoundTrip.V8_18.A_to_B_emb [Morse.lemma_13_6]

end RoundTrip.V8_18
