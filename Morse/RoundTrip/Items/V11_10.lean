import Morse
import RoundTrip.Check
import RoundTrip.Blind.V11_10
import RoundTrip.Bridge

open Set Filter Topology Function Module MeasureTheory
open scoped ContDiff Manifold ENNReal unitInterval RealInnerProductSpace

namespace RoundTrip.V11_10

/-- The project's statement (universes instantiated at `0`): a smooth clamp `ℝ → [−a, 1 + a]`
equal to the identity on `[0, 1]` (`exists_smooth_clamp`); a geodesic `γ ∈ Ω(N; p, q)` agrees on
`[0, 1]` with a smooth curve `c : ℝ → N`, `γ' = Vf` on `(0, 1)` with `Vf` smooth, tangent, of
constant norm `L = L(γ)`, and `L⁻¹ Vf` parallel along `c` (`exists_smooth_extension`); and for
`L > 0` there are parallel unit fields `P_i`, `i ∈ u`, along `c` and `s ⊆ u` with `|s| + 1 = n`
and `Σ_{i ∈ s} ⟨R(Vf, P_i)Vf, P_i⟩ ≥ L²|s|/r²` whenever `K ≥ (n − 1)/r²`
(`exists_parallel_frame`; orthonormality of the frame and `P_n = Vf/L` are NOT in the statement). -/
def A : Prop :=
  type_of% @Morse.exists_smooth_clamp ∧ type_of% @Morse.exists_smooth_extension.{0,0,0} ∧
    type_of% @Morse.exists_parallel_frame.{0,0,0}

theorem A_holds : A :=
  ⟨@Morse.exists_smooth_clamp, @Morse.exists_smooth_extension, @Morse.exists_parallel_frame⟩

/-! ## Clause (a) of B holds outright (any Levi-Civita connection, Milnor's compatibility) -/

open Bundle in
/-- B's first clause: parallel fields orthonormal at one point of `[0, 1]` are orthonormal at every
point — immediate from the compatibility axiom `IsCompat` contained in `IsLC`. -/
theorem B_clause_a : ∀ (n : ℕ) (M : Type) [TopologicalSpace M] [T2Space M] [ChartedSpace (Rn n) M]
    [IsManifold 𝓘(ℝ, Rn n) ∞ M] [Bundle.RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, Rn n) x)]
    (cov : Conn n M), IsLC cov → ∀ (γ : ℝ → M), IsGeodesic cov γ (Set.Icc 0 1) →
    ∀ P : Fin n → FA n γ, (∀ i, IsParallel cov γ (Set.Icc 0 1) (P i)) →
      (∃ t₀ ∈ Set.Icc (0 : ℝ) 1, Orthonormal ℝ (fun i => P i t₀)) →
      ∀ t ∈ Set.Icc (0 : ℝ) 1, Orthonormal ℝ (fun i => P i t) := by
  intro n M _ _ _ _ _ cov hcov γ hγ P hP ⟨t₀, ht₀, hon⟩ t ht
  rw [orthonormal_iff_ite] at hon ⊢
  intro i j
  rw [← hon i j]
  exact hcov.2.2 _ hγ.1 γ hγ.2.1 _ _ (hP i) (hP j) t ht t₀ ht₀

/-! ## The embedded special case -/

namespace Emb

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

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

/-- A blind geodesic on `[0, 1]` of `↥N` from `p` to `q` is, in `V`, a project geodesic of
`Ω(N; p, q)` (from `Items/V10_23.lean`). -/
theorem mem_pathSpace_of_isGeodesic {γ : ℝ → Bridge.Sub hN} {p q : Bridge.Sub hN}
    (h : IsGeodesic (conn (hN := hN)) γ (Icc 0 1)) (h0 : γ 0 = p) (h1 : γ 1 = q) :
    incl hN ∘ γ ∈ Morse.pathSpace N (incl hN p) (incl hN q) ∧
      Morse.IsUnbrokenGeodesic hN (incl hN ∘ γ) := by
  have h' : RoundTrip.BridgePrelude.IsGeodesic (conn (hN := hN)) γ (Icc 0 1) := h
  obtain ⟨-, hc, -⟩ := isGeodesic_iff.1 h'
  exact ⟨⟨Morse.IsPiecewiseSmooth.of_contDiffOn hc zero_le_one subset_rfl, fun t _ => (γ t).2,
    congrArg (incl hN) h0, congrArg (incl hN) h1⟩, hc, isGeodesicOn_Ioo h'⟩


/-- **Dictionary: parallel fields.** A project parallel field `X` along a smooth curve `c : ℝ → N`
which agrees with the blind curve `γ` on `[0, 1]` gives a blind parallel field `toFA γ X` of the
induced connection on `[0, 1]`. -/
theorem isParallel_toFA {γ : ℝ → Bridge.Sub hN} (hsm : IsSmoothCurve (n := n) γ (Icc 0 1))
    {c : ℝ → N} (hγc : ∀ t ∈ Icc (0 : ℝ) 1, incl hN (γ t) = (c t : V)) {X : ℝ → V}
    (hX : Morse.IsParallel hN c X) (hXs : ContDiff ℝ ∞ X) :
    IsParallel (conn (hN := hN)) γ (Icc 0 1) (toFA γ X) := by
  have hsm' : RoundTrip.BridgePrelude.IsSmoothCurve (n := n) γ (Icc 0 1) := hsm
  have hpt : ∀ t ∈ Icc (0 : ℝ) 1, (γ t : N) = c t := fun t ht => Subtype.ext (hγc t ht)
  have htan : ∀ t ∈ Icc (0 : ℝ) 1, Morse.prj hN ((incl hN ∘ γ) t) (X t) = X t := fun t ht => by
    show Morse.prj hN (incl hN (γ t)) (X t) = X t
    rw [prj_incl]
    show Morse.tanProj hN (γ t) (X t) = X t
    rw [hpt t ht]
    exact Morse.tanProj_eq_self hN (hX.mem t)
  have heq := ambA_toFA (γ := γ) htan
  have h : RoundTrip.BridgePrelude.HasCovDeriv (conn (hN := hN)) γ (Icc 0 1) (toFA γ X)
      (fun _ => 0) := by
    refine (hasCovDeriv_iff' isIntv_Icc hsm').2 ⟨isSmoothAlong_iff.2 ⟨hsm', hXs.contDiffOn.congr heq⟩,
      fun t ht => ?_⟩
    rw [derivWithin_congr heq (heq ht),
      (hX.differentiable t).hasDerivAt.hasDerivWithinAt.derivWithin
        (uniqueDiffOn_Icc zero_lt_one t ht)]
    show D hN (γ t) 0 = Morse.tanProj hN (γ t) (deriv X t)
    have h1 : Morse.tanProj hN (c t) (deriv X t) = 0 := hX.covDeriv_eq_zero t
    exact (D_tzero (γ t)).trans (h1.symm.trans
      (congrArg (fun x : N => Morse.tanProj hN x (deriv X t)) (hpt t ht).symm))
  exact h

/-- The ambient velocity of a blind geodesic is `Vf` on the closed interval, if it is on the
open one. -/
theorem derivWithin_eq_of_Ioo {g Vf : ℝ → V} (hg : ContDiffOn ℝ ∞ g (Icc 0 1))
    (hVf : Continuous Vf) (h : ∀ t ∈ Ioo (0 : ℝ) 1, deriv g t = Vf t) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) : derivWithin g (Icc 0 1) t = Vf t := by
  have hu := uniqueDiffOn_Icc (zero_lt_one' ℝ)
  have hf : ContinuousOn (derivWithin g (Icc 0 1)) (Icc 0 1) :=
    hg.continuousOn_derivWithin hu (by simp)
  refine EqOn.of_subset_closure (fun s hs => ?_) hf hVf.continuousOn Ioo_subset_Icc_self
    (by rw [closure_Ioo zero_ne_one]) ht
  rw [derivWithin_of_mem_nhds (Icc_mem_nhds hs.1 hs.2)]
  exact h s hs

theorem finrank_tangent (x : N) : finrank ℝ (Morse.tangentSubspace hN x) = n := by
  have := Morse.finrank_tanAt hN x.2
  rwa [Morse.tanAt_of_mem hN x.2, finrank_euclideanSpace_fin] at this

end Emb

open Bundle in
/-- B on embedded manifolds: `M = ↥N` (model `ℝⁿ`, induced metric, connected), `cov = Bridge.conn`. -/
def B_emb : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (W : Type) [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] (n : ℕ)
    (N : Set V) (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N)
    [ConnectedSpace (Bridge.Sub hN)], ∀ (hn : 0 < n) (γ : ℝ → Bridge.Sub hN),
    IsGeodesic (Bridge.conn (hN := hN)) γ (Set.Icc 0 1) →
    (∀ P : Fin n → FA n γ, (∀ i, IsParallel (Bridge.conn (hN := hN)) γ (Set.Icc 0 1) (P i)) →
      (∃ t₀ ∈ Set.Icc (0 : ℝ) 1, Orthonormal ℝ (fun i => P i t₀)) →
      ∀ t ∈ Set.Icc (0 : ℝ) 1, Orthonormal ℝ (fun i => P i t)) ∧
    ∃ P : Fin n → FA n γ, (∀ i, IsParallel (Bridge.conn (hN := hN)) γ (Set.Icc 0 1) (P i)) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 1, Orthonormal ℝ (fun i => P i t)) ∧
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        vel (n := n) γ (Set.Icc 0 1) t = (arcLen (n := n) γ 0 1) • P (lastIdx n hn) t

/-- `B_emb` is a special case of B (the induced connection is Levi-Civita, `Bridge.conn_isLC`). -/
theorem B_to_B_emb : B → B_emb := fun hB _ _ _ _ _ _ _ _ n _ hN _ hn γ hγ =>
  hB n (Bridge.Sub hN) (Bridge.conn (hN := hN)) Bridge.conn_isLC hn γ hγ

open Emb Bridge Bundle in
/-- **A implies B on embedded manifolds.** A's `exists_smooth_extension` extends the geodesic to a
smooth curve `c : ℝ → N` with `L⁻¹γ'` parallel; the orthonormal frame with last vector `γ'/L` is
then built from the project's parallel transport along `c` (`Morse.parallelField`,
`Morse.parallelTransport`, an isometry) — A's own `exists_parallel_frame` cannot be used for this,
since its statement records neither the orthogonality of the frame nor `P_n = γ'/L`. -/
theorem A_to_B_emb : A → B_emb := by
  intro hA V _ _ _ W _ _ _ n N hN _ hn γ hγ
  refine ⟨B_clause_a n (Bridge.Sub hN) (Bridge.conn (hN := hN)) Bridge.conn_isLC γ hγ, ?_⟩
  have hsm : IsSmoothCurve (n := n) γ (Icc 0 1) := hγ.2.1
  have hsm' : RoundTrip.BridgePrelude.IsSmoothCurve (n := n) γ (Icc 0 1) := hsm
  obtain ⟨hmem, hunb⟩ := mem_pathSpace_of_isGeodesic hγ rfl rfl
  obtain ⟨c, hcs, hγc, Vf, hVfs, hVγ, hVn, hVfT, hTpar⟩ := hA.2.1 hmem hunb
  set Lγ := Morse.pathLength (incl hN ∘ γ) 0 1 with hLγ
  have hLγ0 : 0 ≤ Lγ := by rw [← hVn 0]; exact norm_nonneg _
  -- an orthonormal basis of `T_{c(0)}N` whose last vector is `γ'(0)/L` (if `L > 0`)
  set T₀ := Morse.tangentSubspace hN (c 0)
  have hcard : finrank ℝ T₀ = Fintype.card (Fin n) := by rw [finrank_tangent, Fintype.card_fin]
  obtain ⟨b, hb⟩ : ∃ b : OrthonormalBasis (Fin n) ℝ T₀,
      0 < Lγ → (b (lastIdx n hn) : V) = Lγ⁻¹ • Vf 0 := by
    by_cases hL : 0 < Lγ
    · set e₀ : T₀ := ⟨Lγ⁻¹ • Vf 0, hTpar.mem 0⟩
      have he₀ : ‖e₀‖ = 1 := by
        show ‖Lγ⁻¹ • Vf 0‖ = 1
        rw [norm_smul, hVn, Real.norm_eq_abs, abs_inv, abs_of_pos hL, inv_mul_cancel₀ hL.ne']
      have hon : Orthonormal ℝ (({lastIdx n hn} : Set (Fin n)).domRestrict (fun _ => e₀)) := by
        rw [orthonormal_iff_ite]
        rintro ⟨i, hi⟩ ⟨j, hj⟩
        rw [Set.mem_singleton_iff] at hi hj
        subst hi hj
        rw [if_pos rfl]
        show ⟪e₀, e₀⟫ = 1
        rw [real_inner_self_eq_norm_sq, he₀, one_pow]
      obtain ⟨b, hb⟩ := hon.exists_orthonormalBasis_extension_of_card_eq hcard
      exact ⟨b, fun _ => congrArg Subtype.val (hb _ (Set.mem_singleton _))⟩
    · have hon : Orthonormal ℝ ((∅ : Set (Fin n)).domRestrict (fun _ => (0 : T₀))) := by
        rw [orthonormal_iff_ite]
        rintro ⟨i, hi⟩
        exact absurd hi (Set.notMem_empty i)
      obtain ⟨b, -⟩ := hon.exists_orthonormalBasis_extension_of_card_eq hcard
      exact ⟨b, fun h => absurd h hL⟩
  -- the parallel frame along `c`
  set X : Fin n → ℝ → V := fun i => Morse.parallelField hN c 0 (b i : V) with hXdef
  have hX : ∀ i, Morse.IsParallel hN c (X i) ∧ X i 0 = b i := fun i =>
    Morse.parallelField_spec hN hcs (b i).2
  have hXs : ∀ i, ContDiff ℝ ∞ (X i) := fun i => (hX i).1.contDiff hN hcs
  have hbt : ∀ t i, ((b.map (Morse.parallelTransport hN hcs 0 t)) i : V) = X i t := fun t i => by
    rw [OrthonormalBasis.map_apply, Morse.parallelTransport_apply]
  -- `γ' = L · X_n` along `c`
  have hVX : ∀ t, Vf t = Lγ • X (lastIdx n hn) t := by
    by_cases hL : 0 < Lγ
    · have hP₀ : (fun t => Lγ⁻¹ • Vf t) = X (lastIdx n hn) := by
        refine hTpar.eq hN hcs (hX _).1 (t₀ := 0) ?_
        rw [(hX _).2, hb hL]
      intro t
      rw [← congrFun hP₀ t, smul_smul, mul_inv_cancel₀ hL.ne', one_smul]
    · have hL0 : Lγ = 0 := le_antisymm (not_lt.1 hL) hLγ0
      intro t
      rw [hL0, zero_smul, ← norm_eq_zero, hVn, hL0]
  have hγc' : ∀ t ∈ Icc (0 : ℝ) 1, incl hN (γ t) = (c t : V) := fun t ht => hγc t ht
  refine ⟨fun i => toFA γ (X i), fun i => isParallel_toFA hsm hγc' (hX i).1 (hXs i),
    fun t ht => ?_, fun t ht => ?_⟩
  · -- orthonormal at every `t ∈ [0, 1]`: parallel transport is an isometry
    have htan : ∀ i, ∀ s ∈ Icc (0 : ℝ) 1, Morse.prj hN ((incl hN ∘ γ) s) (X i s) = X i s :=
      fun i s hs => by
        show Morse.prj hN (incl hN (γ s)) (X i s) = X i s
        rw [prj_incl]
        show Morse.tanProj hN (γ s) (X i s) = X i s
        rw [show (γ s : N) = c s from Subtype.ext (hγc' s hs)]
        exact Morse.tanProj_eq_self hN ((hX i).1.mem s)
    have hon := (b.map (Morse.parallelTransport hN hcs 0 t)).orthonormal
    rw [orthonormal_iff_ite] at hon ⊢
    intro i j
    rw [← hon i j, Submodule.coe_inner, hbt, hbt]
    show ⟪D hN (γ t) (toFA γ (X i) t), D hN (γ t) (toFA γ (X j) t)⟫ = _
    rw [show D hN (γ t) (toFA γ (X i) t) = X i t from ambA_toFA (htan i) ht,
      show D hN (γ t) (toFA γ (X j) t) = X j t from ambA_toFA (htan j) ht]
  · -- `dγ/dt = L · P_n`
    have htan : ∀ s ∈ Icc (0 : ℝ) 1,
        Morse.prj hN ((incl hN ∘ γ) s) (X (lastIdx n hn) s) = X (lastIdx n hn) s :=
      fun s hs => by
        show Morse.prj hN (incl hN (γ s)) (X _ s) = X _ s
        rw [prj_incl]
        show Morse.tanProj hN (γ s) (X _ s) = X _ s
        rw [show (γ s : N) = c s from Subtype.ext (hγc' s hs)]
        exact Morse.tanProj_eq_self hN ((hX _).1.mem s)
    have hlen : arcLen (n := n) γ 0 1 = Lγ := arcLen_eq γ 0 1
    rw [hlen]
    apply D_injective (γ t)
    have e1 : D hN (γ t) (vel (n := n) γ (Icc 0 1) t) = derivWithin (incl hN ∘ γ) (Icc 0 1) t :=
      D_vel hsm' (uniqueDiffOn_Icc zero_lt_one) ht
    rw [e1, derivWithin_eq_of_Ioo hunb.1 hVfs.continuous hVγ ht, hVX t]
    show _ = D hN (γ t) (Lγ • toFA γ (X (lastIdx n hn)) t)
    rw [D_tsmul]
    rw [show D hN (γ t) (toFA γ (X (lastIdx n hn)) t) = X (lastIdx n hn) t from
      ambA_toFA htan ht]

#rt_check RoundTrip.V11_10.A_to_B_emb [Morse.exists_smooth_clamp, Morse.exists_smooth_extension, Morse.exists_parallel_frame]
#rt_overlap RoundTrip.V11_10.A_to_B_emb [Morse.exists_smooth_clamp, Morse.exists_smooth_extension, Morse.exists_parallel_frame]

end RoundTrip.V11_10
