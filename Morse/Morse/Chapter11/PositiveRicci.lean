import Morse.Chapter11.LongGeodesics
import Morse.Chapter10.FundamentalTheorem

/-!
Milnor, *Morse Theory*, §19, p. 106: **Theorem 19.6** (the path space of a compact manifold with
positive definite Ricci tensor), for a compact submanifold `N ⊆ ℝᴷ` with the induced metric and
end points not conjugate along any geodesic.

# Positive Ricci curvature and the path space

## Milnor's text, paraphrased

**Theorem 19.6** (p. 106): if `M` is compact and its Ricci tensor is everywhere positive definite,
then `Ω(M; p, q)` has the homotopy type of a CW-complex with only finitely many cells in each
dimension.  Proof: the continuous function `K(U, U)` on the compact space of unit vectors takes a
minimum `(n − 1)/r² > 0`; a geodesic of length `> kπr` has index `≥ k`; if `p` and `q` are not
conjugate along any geodesic, there are by 16.3 only finitely many geodesics of length `≤ kπr`,
hence only finitely many of index `< k`; together with 17.3 this completes the proof.

## In the embedded setting

* `Morse.ricciMap`, `Morse.ricci_eq_trace_ricciMap`: `K(U, U)` is the trace on `V` of
  `W ↦ R(U, P_q W)U`; `Morse.continuous_trace_ricciMap`: this trace is continuous on `N × V`.
* `Morse.exists_ricciLowerBound`: **the minimum `(n − 1)/r²`**: on a compact `N` of dimension
  `n ≥ 2` with positive definite Ricci tensor, `K(U, U) ≥ (n − 1)/r²` for some `r > 0` and all
  unit vectors `U` (`Morse.RicciLowerBound`).
* `Morse.energy_le_of_geodesicIndex_le`: with this bound, a geodesic of index `≤ d` has energy
  `≤ ((d + 1)πr)²` (the index estimate of `Morse/Chapter11/LongGeodesics.lean`).
* `Morse.theorem_19_6_of_ricciLowerBound`, `Morse.theorem_19_6`: **Theorem 19.6**, for `p`, `q`
  not conjugate along any geodesic: `Ω(N; p, q)` has the homotopy type of a countable cell complex
  (`Morse.IsCountableCellComplexType`, Theorem 17.3) in which each dimension `d` occurs at only
  finitely many of the stages; each stage attaches finitely many cells, so there are only
  finitely many cells of each dimension.
* The homological consequence, `H_i(Ω(N; p, q); 𝕜)` finite-dimensional for every `i`, is in
  `Morse/Chapter11/RicciHomology.lean`.

## What Milnor leaves implicit

* **The continuity of `K(U, U)` on the unit tangent bundle.**  The Ricci tensor is a trace over
  the moving subspace `T_qN`; it equals the trace over the fixed space `V` of `W ↦ R(U, P_q W)U`
  (`tr_{T_qN} A = tr_V (A ∘ P_q)`), and near each point `P_q` and its derivative along `N` are
  restrictions of smooth maps on `V` (`Morse.projRep`), so this trace is continuous in `(q, U)`.
  The unit tangent vectors form a closed subset of `N × S`, `S` the unit sphere of `V`, hence a
  compact set (Milnor's "the space consisting of all unit vectors on `M` is compact").
* **`n ≥ 2`**, needed for `(n − 1)/r² > 0` and for the index estimate, as in Theorem 19.4.
* **Counting the cells.**  Theorem 16.3 gives finitely many energy values of geodesics below each
  level (`Morse.finite_geodesicEnergies`); the stages of the complex of 17.3 are ordered by
  energy, so only finitely many of them contain a geodesic of index `≤ d`, which has length
  `≤ (d + 1)πr` and energy `≤ ((d + 1)πr)²` (energy is length squared at constant speed).
* **Arbitrary end points.**  Milnor's proof covers only `p`, `q` not conjugate along any
  geodesic, while the theorem is stated for all `p, q`.  The general case needs a `q'`
  non-conjugate to `p` (Corollary 18.2) and the change of end point `Ω(M; p, q) ≃ Ω(M; p, q')`
  (Lemma 17.D of the exposition, through Theorem 17.1); the general case is
  `Morse.theorem_19_6_all` in `Morse/Chapter11/PositiveRicciAll.lean`.
-/

open Set Filter Topology Function Module Metric Real
open scoped ContDiff Manifold RealInnerProductSpace

noncomputable section

namespace Morse

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {N : Set V} {hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N}

/-! ### The Ricci curvature on the unit tangent bundle -/

variable (hN) in
/-- The linear map `W ↦ R(Pu, PW)Pu` of `V` (`P = P_q` the tangent projection), whose trace is
the Ricci curvature `K(u, u)` for `u ∈ T_qN`. -/
def ricciMap (q : N) (u : V) : V →L[ℝ] V :=
  ((dN hN (tanProj hN) q).flip (dN hN (tanProj hN) q (tanProj hN q u) (tanProj hN q u)) -
    (dN hN (tanProj hN) q (tanProj hN q u)).comp
      ((dN hN (tanProj hN) q).flip (tanProj hN q u))).comp (tanProj hN q)

omit [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
theorem ricciMap_apply (q : N) (u w : V) :
    ricciMap hN q u w = curvOp hN q (tanProj hN q u) (tanProj hN q w) (tanProj hN q u) := by
  simp [ricciMap, curvOp]

omit [FiniteDimensional ℝ W] in
/-- **The Ricci curvature as a trace on `V`**: `K(U, U) = tr_V (W ↦ R(U, P_q W)U)`. -/
theorem ricci_eq_trace_ricciMap (q : N) (U : tangentSubspace hN q) :
    ricci hN q U U = LinearMap.trace ℝ V (ricciMap hN q U : V →ₗ[ℝ] V) := by
  have e : (ricciMap hN q U : V →ₗ[ℝ] V) =
      ((tangentSubspace hN q).subtype ∘ₗ (curvTensor hN q U).flip U) ∘ₗ
        ((tangentSubspace hN q).orthogonalProjectionOnto : V →ₗ[ℝ] tangentSubspace hN q) := by
    ext w
    simp only [LinearMap.coe_comp, comp_apply, ContinuousLinearMap.coe_coe, Submodule.coe_subtype,
      LinearMap.flip_apply, coe_curvTensor_apply, ricciMap_apply]
    rw [tanProj_eq_self hN U.2, Submodule.coe_orthogonalProjectionOnto_apply]
    rfl
  rw [e, LinearMap.trace_comp_comm', ← LinearMap.comp_assoc]
  have h2 : ((tangentSubspace hN q).orthogonalProjectionOnto : V →ₗ[ℝ] tangentSubspace hN q) ∘ₗ
      (tangentSubspace hN q).subtype = LinearMap.id := by
    ext x
    simp
  rw [h2, LinearMap.id_comp]
  rfl

omit [FiniteDimensional ℝ W] in
/-- **The Ricci integrand is continuous**: `(q, u) ↦ tr (W ↦ R(Pu, PW)Pu)` is continuous on
`N × V`.  Near `q₀`, with `Q = projRep σ` the smooth ambient extension of `q ↦ P_q` given by a
slice chart, `R(a, b)c = dQ(b)(dQ(a)c) − dQ(a)(dQ(b)c)` for tangent `a, b`, and the trace is
`Σᵢ ⟨eᵢ, ·(eᵢ)⟩` in a fixed orthonormal basis of `V`. -/
theorem continuous_trace_ricciMap :
    Continuous fun z : N × V => LinearMap.trace ℝ V (ricciMap hN z.1 z.2 : V →ₗ[ℝ] V) := by
  set e := stdOrthonormalBasis ℝ V
  rw [continuous_iff_continuousAt]
  rintro ⟨q₀, u₀⟩
  set σ := sliceAt hN q₀
  have hq₀ : (q₀ : V) ∈ σ.φ.source := mem_sliceAt_source hN q₀
  set Pr := projRep σ with hPr_def
  set Qd := fderiv ℝ (projRep σ) with hQd_def
  have hPr : ContinuousAt Pr q₀ := (contDiffAt_projRep σ hq₀).continuousAt
  have hQd : ContinuousAt Qd q₀ :=
    ((contDiffAt_projRep σ hq₀).fderiv_right (m := ∞) (by simp)).continuousAt
  set G : V × V → ℝ := fun z => ∑ i, ⟪e i,
    Qd z.1 (Pr z.1 (e i)) (Qd z.1 (Pr z.1 z.2) (Pr z.1 z.2)) -
      Qd z.1 (Pr z.1 z.2) (Qd z.1 (Pr z.1 (e i)) (Pr z.1 z.2))⟫ with hG_def
  have hG : ContinuousAt G ((q₀ : V), u₀) := by
    have hPr' : ContinuousAt (fun z : V × V => Pr z.1) ((q₀ : V), u₀) :=
      hPr.comp_of_eq continuousAt_fst rfl
    have hQd' : ContinuousAt (fun z : V × V => Qd z.1) ((q₀ : V), u₀) :=
      hQd.comp_of_eq continuousAt_fst rfl
    have ha : ContinuousAt (fun z : V × V => Pr z.1 z.2) ((q₀ : V), u₀) :=
      hPr'.clm_apply continuousAt_snd
    have hb : ContinuousAt (fun z : V × V => Qd z.1 (Pr z.1 z.2) (Pr z.1 z.2)) ((q₀ : V), u₀) :=
      (hQd'.clm_apply ha).clm_apply ha
    refine tendsto_finsetSum _ fun i _ => continuousAt_const.inner ?_
    have hw : ContinuousAt (fun z : V × V => Pr z.1 (e i)) ((q₀ : V), u₀) :=
      hPr'.clm_apply continuousAt_const
    exact ((hQd'.clm_apply hw).clm_apply hb).sub ((hQd'.clm_apply ha).clm_apply
      ((hQd'.clm_apply hw).clm_apply ha))
  have hO : IsOpen {z : N × V | (z.1 : V) ∈ σ.φ.source} :=
    σ.φ.open_source.preimage (continuous_subtype_val.comp continuous_fst)
  have hev : (fun z : N × V => LinearMap.trace ℝ V (ricciMap hN z.1 z.2 : V →ₗ[ℝ] V)) =ᶠ[𝓝 (q₀, u₀)]
      fun z => G ((z.1 : V), z.2) := by
    filter_upwards [hO.mem_nhds hq₀] with z hz
    rw [LinearMap.trace_eq_sum_inner _ e]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    change ricciMap hN z.1 z.2 (e i) = _
    rw [ricciMap_apply, curvOp_apply, secondFundForm, secondFundForm, secondFundForm,
      secondFundForm, dN_tanProj_eq_fderiv hN σ hz (tanProj_apply_mem hN _ _),
      dN_tanProj_eq_fderiv hN σ hz (tanProj_apply_mem hN _ _), ← projRep_eq hN σ hz]
  refine ContinuousAt.congr ?_ hev.symm
  exact ContinuousAt.comp_of_eq (g := G) (f := fun z : N × V => ((z.1 : V), z.2)) hG
    (by fun_prop) rfl

omit [FiniteDimensional ℝ W] in
/-- **The minimum of the Ricci curvature** (Milnor p. 106, the first step of the proof of 19.6):
if `N` is compact, `dim N ≥ 2`, and the Ricci tensor is positive definite, there is `r > 0` with
`K(U, U) ≥ (n − 1)/r²` for every unit vector `U`: the continuous function `K(U, U)` attains a
positive minimum on the compact set of unit tangent vectors. -/
theorem exists_ricciLowerBound (hNc : IsCompact N) (hn : 2 ≤ finrank ℝ Z)
    (hpos : ∀ q : N, ∀ U : tangentSubspace hN q, U ≠ 0 → 0 < ricci hN q U U) :
    ∃ r > 0, RicciLowerBound hN r := by
  let _ := hN.chartedSpace
  have : CompactSpace N := isCompact_iff_compactSpace.1 hNc
  -- the unit tangent bundle, a compact subset of `N × V`
  set K : Set (N × V) := {z | tanProj hN z.1 z.2 = z.2 ∧ ‖z.2‖ = 1} with hK_def
  have hPc : Continuous (tanProj hN) := (contMDiff_tanProj hN).continuous
  have hKc : IsCompact K := by
    have hcl : IsClosed K :=
      (isClosed_eq ((hPc.comp continuous_fst).clm_apply continuous_snd) continuous_snd).inter
        (isClosed_eq (continuous_norm.comp continuous_snd) continuous_const)
    exact (isCompact_univ.prod (isCompact_sphere (0 : V) 1)).of_isClosed_subset hcl
      fun z hz => ⟨trivial, by simpa using hz.2⟩
  have hmemK : ∀ q : N, ∀ U : tangentSubspace hN q, ‖U‖ = 1 → ((q, (U : V)) : N × V) ∈ K :=
    fun q U hU => ⟨tanProj_eq_self hN U.2, by simpa using hU⟩
  have hn' : (0 : ℝ) < (finrank ℝ Z : ℝ) - 1 := by
    have : (2 : ℝ) ≤ finrank ℝ Z := by exact_mod_cast hn
    linarith
  rcases K.eq_empty_or_nonempty with hK0 | hKne
  · refine ⟨1, one_pos, fun q U hU => ?_⟩
    have := hmemK q U hU
    rw [hK0] at this
    exact absurd this (notMem_empty _)
  obtain ⟨z₀, hz₀K, hmin⟩ :=
    hKc.exists_isMinOn hKne (continuous_trace_ricciMap (hN := hN)).continuousOn
  set m := LinearMap.trace ℝ V (ricciMap hN z₀.1 z₀.2 : V →ₗ[ℝ] V) with hm_def
  have hT : z₀.2 ∈ tangentSubspace hN z₀.1 := (tanProj_eq_self_iff hN).1 hz₀K.1
  have hm : 0 < m := by
    have h := hpos z₀.1 ⟨z₀.2, hT⟩ (fun h0 => by
      have := hz₀K.2
      rw [show z₀.2 = 0 from congrArg Subtype.val h0, norm_zero] at this
      exact zero_ne_one this)
    rwa [ricci_eq_trace_ricciMap] at h
  refine ⟨√(((finrank ℝ Z : ℝ) - 1) / m), Real.sqrt_pos.2 (div_pos hn' hm), fun q U hU => ?_⟩
  rw [Real.sq_sqrt (div_pos hn' hm).le, div_div_cancel₀ hn'.ne', ricci_eq_trace_ricciMap]
  exact isMinOn_iff.1 hmin (q, (U : V)) (hmemK q U hU)

/-! ### Theorem 19.6 -/

/-- The energy of a geodesic is the square of its length (constant speed). -/
theorem energy_eq_pathLength_sq_of_geodesic {p q : V} {γ : ℝ → V} (hγ : γ ∈ pathSpace N p q)
    (hgeo : IsUnbrokenGeodesic hN γ) : energy γ 0 1 = pathLength γ 0 1 ^ 2 := by
  have hk : ∃ k, ∀ t ∈ Ioo (0 : ℝ) 1, DifferentiableAt ℝ γ t → ‖deriv γ t‖ = k :=
    ⟨‖deriv γ (1 / 2)‖, fun t ht _ => hgeo.2.norm_deriv_eq isPreconnected_Ioo ht
      ⟨by norm_num, by norm_num⟩⟩
  have h1 := (pathLength_sq_eq_energy_iff hγ.1).2 hk
  simp only [sub_zero, one_mul] at h1
  exact h1.symm

/-- **A geodesic of index `≤ d` has energy `≤ ((d + 1)πr)²`** (Theorem 19.6, from the index
estimate). -/
theorem energy_le_of_geodesicIndex_le {r : ℝ} (hr : 0 < r) (hn : 2 ≤ finrank ℝ Z)
    (hRic : RicciLowerBound hN r) {p q : V} {γ : ℝ → V} (hγ : γ ∈ pathSpace N p q)
    (hgeo : IsUnbrokenGeodesic hN γ) {d : ℕ} (hd : geodesicIndex hN p q γ ≤ d) :
    energy γ 0 1 ≤ (((d + 1 : ℕ) : ℝ) * π * r) ^ 2 := by
  have h1 := geodesicIndex_eq hγ hgeo
  have h2 : formIndex (energyHessian hN hγ) < ((d + 1 : ℕ) : ℕ∞) := by
    rw [← h1]
    exact_mod_cast Nat.lt_succ_of_le hd
  have hL := pathLength_le_of_formIndex_lt hr hn hRic hγ hgeo h2
  rw [energy_eq_pathLength_sq_of_geodesic hγ hgeo]
  exact pow_le_pow_left₀ hγ.1.isAdmissible.pathLength_nonneg hL 2

/-- **Theorem 19.6** (Milnor p. 106), for end points not conjugate along any geodesic, with the
Ricci curvature bounded below by `(n − 1)/r² > 0`: `Ω(N; p, q)` has the homotopy type of a
countable cell complex with only finitely many cells in each dimension. -/
theorem theorem_19_6_of_ricciLowerBound (hcl : IsClosed N) {r : ℝ} (hr : 0 < r)
    (hn : 2 ≤ finrank ℝ Z) (hRic : RicciLowerBound hN r) {p q : V} (hp : p ∈ N) (hq : q ∈ N)
    (hnc : q ∉ conjLocus hN p) :
    ∃ cells : ℕ → List ℕ, IsCountableCellComplexType (PathSp N p q) cells ∧
      ∀ d : ℕ, {n | d ∈ cells n}.Finite := by
  have hnd : ∀ γ (hγ : γ ∈ pathSpace N p q), IsUnbrokenGeodesic hN γ → hessNullity hN hγ = 0 :=
    fun _ hγ hgeo => hessNullity_eq_zero_of_notMem_conjLocus hnc hγ hgeo
  obtain ⟨geo, hgeo, -, -, -, hlt, -, hcell⟩ := theorem_17_3 hcl hp hq hnd
  refine ⟨_, hcell, fun d => ?_⟩
  set E : ℝ := (((d + 1 : ℕ) : ℝ) * π * r) ^ 2 with hE_def
  -- each stage with a cell of dimension `d` contains a geodesic of energy `≤ E`
  have hstage : ∀ n, d ∈ (geo n).map (geodesicIndex hN p q) → ∃ γ ∈ geo n, energy γ 0 1 ≤ E := by
    intro n hn'
    obtain ⟨γ, hγ, hidx⟩ := List.mem_map.1 hn'
    exact ⟨γ, hγ, energy_le_of_geodesicIndex_le hr hn hRic (hgeo n γ hγ).1 (hgeo n γ hγ).2
      hidx.le⟩
  choose! g hg hgE using hstage
  -- the stages are ordered by energy, so the energies of the chosen geodesics are distinct
  have hfin := finite_geodesicEnergies hcl hp hq hnd E
  refine Set.Finite.of_finite_image (f := fun n => energy (g n) 0 1) (hfin.subset ?_) ?_
  · rintro _ ⟨n, hn', rfl⟩
    exact ⟨g n, (hgeo n _ (hg n hn')).1, (hgeo n _ (hg n hn')).2, rfl, hgE n hn'⟩
  · intro n hn' m hm' he
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact (hlt n m h _ (hg n hn') _ (hg m hm')).ne he
    · exact (hlt m n h _ (hg m hm') _ (hg n hn')).ne he.symm

/-- **Theorem 19.6** (Milnor p. 106), for end points not conjugate along any geodesic: if `N` is
compact (so complete), of dimension `≥ 2`, with positive definite Ricci tensor, then
`Ω(N; p, q)` has the homotopy type of a countable cell complex with only finitely many cells in
each dimension. -/
theorem theorem_19_6 (hNc : IsCompact N) (hn : 2 ≤ finrank ℝ Z)
    (hpos : ∀ q : N, ∀ U : tangentSubspace hN q, U ≠ 0 → 0 < ricci hN q U U) {p q : V}
    (hp : p ∈ N) (hq : q ∈ N) (hnc : q ∉ conjLocus hN p) :
    ∃ cells : ℕ → List ℕ, IsCountableCellComplexType (PathSp N p q) cells ∧
      ∀ d : ℕ, {n | d ∈ cells n}.Finite := by
  obtain ⟨r, hr, hRic⟩ := exists_ricciLowerBound hNc hn hpos
  exact theorem_19_6_of_ricciLowerBound hNc.isClosed hr hn hRic hp hq hnc

end Morse
