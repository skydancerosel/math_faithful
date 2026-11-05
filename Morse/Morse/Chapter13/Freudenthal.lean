import Morse.Chapter13.SphereMinimal

/-!
Milnor, *Morse Theory*, §22, Corollary 22.3 (p. 119), with the proof of Exposition/Chapter13.md,
§1.

# The Freudenthal suspension theorem

## Milnor's text, paraphrased

(p. 119) **Corollary 22.3 (Freudenthal)**: `π_i(Sⁿ) ≅ π_{i+1}(Sⁿ⁺¹)` for `i ≤ 2n − 2`.  *Proof*:
for antipodal `p`, `q` on `Sⁿ⁺¹` the space `Ω^{π²}` of minimal geodesics is the equator `Sⁿ`,
every non-minimal geodesic has index `≥ 2n`, and Corollary 22.2 applies with `λ₀ = 2n`.

## What is formalized

* `Morse.corollary_22_2_surjective` (any `N`): the surjectivity half of Corollary 22.2, a
  surjection `π_i(Ω^d, γ) → π_{i+1}(N, p)` for `i + 1 ≤ λ₀` (from `Morse.theorem_22_1_surjective`).
* `Morse.sphNbhd p`, `Morse.sphRetrPath`, `Morse.exists_retraction_minPaths_sph`: **the
  neighbourhood-retract hypothesis of Theorem 22.1 for `Sⁿ⁺¹`**: on the open set of paths `ω`
  with `ω(1/2) ≠ ±p`, `ω ↦` the great semicircle through the normalized equatorial component
  of `ω(1/2)`.
* `Morse.equatorHomeomorph`: the equator `{u ∈ Sⁿ⁺¹ : u ⊥ p}` is homeomorphic to `Sⁿ` (an
  isometry `pᗮ ≅ ℝⁿ⁺¹`).
* `Morse.corollary_22_3`: **Corollary 22.3**, `π_i(Sⁿ, x) ≃ π_{i+1}(Sⁿ⁺¹, y)` for `i + 2 ≤ 2n`
  and all base points `x`, `y`; `Morse.corollary_22_3_surjective`: **a surjection
  `π_i(Sⁿ, x) → π_{i+1}(Sⁿ⁺¹, y)` for `i + 1 ≤ 2n`**, in particular for `i = 2n − 1` (the second
  half of Freudenthal's theorem, Exposition/Chapter13.md).  The group versions are in
  `Morse/Chapter13/CorollaryGroups.lean`.

## What Milnor leaves implicit

* **Hypotheses of Theorem 22.1.** "`Ω^d` is a manifold" enters the project's Theorem 22.1 as the
  existence of a neighbourhood retraction; for the sphere it is written down explicitly (no
  Hanner theorem).  The base point `y` of `Sⁿ⁺¹` is the pole `p`; no change of base point is
  needed, since `p` is arbitrary.
* **Base points in `Sⁿ`.** Corollary 22.2 is available at every minimal geodesic `γ`, and the
  semicircles through the points of the equator are all of them, so every base point of `Sⁿ` is
  reached.
* **The surjective half** (`i = 2n − 1`) is not stated by Milnor in Corollary 22.3; it follows in
  the same way from the surjectivity in Theorem 22.1 (Milnor's remark on p. 118 on `π_{λ₀−1}`).
-/

open Set Filter Topology Function Module
open scoped ContDiff Manifold RealInnerProductSpace ENNReal Topology.Homotopy

noncomputable section

namespace Morse

/-! ### Surjectivity in Corollary 22.2 -/

section General

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {N : Set V}

/-- **Corollary 22.2, surjectivity in the top degree**: under the hypotheses of Theorem 22.1, for
`i + 1 ≤ λ₀` there is a surjection `π_i(Ω^d, γ) → π_{i+1}(N, p)` (the composite of the inclusion
`Ω^d → Ω`, onto by `Morse.theorem_22_1_surjective`, with the bijections of
`Morse.corollary_22_2`). -/
theorem corollary_22_2_surjective (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N) {p q : V}
    (hp : p ∈ N) (hq : q ∈ N) (hball : ∀ r : ℝ, IsCompact (closedRiemBall N p r)) {l₀ : ℕ}
    (hidx : ∀ γ (hγ : γ ∈ pathSpace N p q), IsUnbrokenGeodesic hN γ →
      (∃ γ' ∈ pathSpace N p q, energy γ' 0 1 < energy γ 0 1) →
      (l₀ : ℕ∞) ≤ formIndex (energyHessian hN hγ))
    (hretr : ∃ O : Set (PathSp N p q), IsOpen O ∧ minPaths N p q ⊆ O ∧
      ∃ ρ : PathSp N p q → PathSp N p q, ContinuousOn ρ O ∧ (∀ γ ∈ O, ρ γ ∈ minPaths N p q) ∧
        ∀ γ ∈ minPaths N p q, ρ γ = γ)
    {i : ℕ} (hi : i + 1 ≤ l₀) (γ : minPaths N p q) :
    ∃ f : HomotopyGroup.Pi i (minPaths N p q) γ → HomotopyGroup.Pi (i + 1) N ⟨p, hp⟩,
      Surjective f := by
  have h1 := theorem_22_1_surjective hN hp hq hball hidx hretr (K := Fin i)
    (by simpa using hi) γ
  have h2 := Morse.Homotopy.bijective_homotopyGroupMap_of_isHomotopyEquiv (N := Fin i)
    (theorem_17_1 hN p q) (γ : PathSp N p q)
  set e := pathCHomeomorph (N := N) hp hq
  have h3 := Morse.Homotopy.bijective_homotopyGroupMap_homeomorph (N := Fin i) e
    (pathIncl (N := N) p q γ)
  set x := e (pathIncl (N := N) p q γ)
  have h4 := Morse.Homotopy.bijective_homotopyGroupMap_of_homotopyEquiv (N := Fin i)
    (Morse.Homotopy.pathTransHomotopyEquiv x.symm) x
  let E := (Equiv.ofBijective _ h2).trans
    ((Equiv.ofBijective _ h3).trans ((Equiv.ofBijective _ h4).trans
      ((Morse.Homotopy.changeBaseEquiv (contractPath x)).trans
        (Morse.Homotopy.homotopyGroupPiLoopEquiv i))))
  exact ⟨E ∘ _, E.surjective.comp h1⟩

end General

open Milnor.Sphere Real

variable {n : ℕ} {p : EuclideanSpace ℝ (Fin (n + 1 + 1))}

/-! ### The neighbourhood retraction -/

/-- The equatorial component `x − ⟪p, x⟫ p`. -/
def eqComp (p x : EuclideanSpace ℝ (Fin (n + 1 + 1))) : EuclideanSpace ℝ (Fin (n + 1 + 1)) :=
  x - ⟪p, x⟫ • p

theorem continuous_eqComp (p : EuclideanSpace ℝ (Fin (n + 1 + 1))) : Continuous (eqComp p) := by
  unfold eqComp; fun_prop

theorem eqComp_mem_equator (hp : p ∈ Sph (n + 1)) {x : EuclideanSpace ℝ (Fin (n + 1 + 1))}
    (hx : eqComp p x ≠ 0) : ‖eqComp p x‖⁻¹ • eqComp p x ∈ equator p := by
  refine ⟨?_, ?_⟩
  · rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.2 hx)]
  · rw [real_inner_smul_right, eqComp, inner_sub_right, real_inner_smul_right,
      real_inner_self_eq_norm_sq, norm_of_mem_sph hp]
    ring

theorem eqComp_of_mem_equator {u : EuclideanSpace ℝ (Fin (n + 1 + 1))} (hu : u ∈ equator p) :
    eqComp p u = u := by
  rw [eqComp, hu.2, zero_smul, sub_zero]

variable (p) in
/-- **The neighbourhood `O` of `Ω^d`**: the paths whose midpoint is not `±p`. -/
def sphNbhd : Set (PathSp (Sph (n + 1)) p (-p)) :=
  {γ | eqComp p ((γ : ℝ → EuclideanSpace ℝ (Fin (n + 1 + 1))) (1 / 2)) ≠ 0}

theorem isOpen_sphNbhd : IsOpen (sphNbhd p) :=
  isOpen_ne_fun ((continuous_eqComp p).comp continuous_apply_half_sph) continuous_const

open Classical in
/-- **The retraction onto the minimal geodesics**: `ω ↦` the great semicircle through the
normalized equatorial component of `ω(1/2)`. -/
def sphRetrPath (hp : p ∈ Sph (n + 1)) (γ : PathSp (Sph (n + 1)) p (-p)) :
    PathSp (Sph (n + 1)) p (-p) :=
  if h : γ ∈ sphNbhd p then semicircle hp ⟨_, eqComp_mem_equator hp h⟩ else γ

theorem continuousOn_sphRetrPath (hp : p ∈ Sph (n + 1)) :
    ContinuousOn (sphRetrPath hp) (sphNbhd p) := by
  rw [continuousOn_iff_continuous_domRestrict]
  have e : (sphNbhd p).domRestrict (sphRetrPath hp) = fun γ : sphNbhd p =>
      semicircle hp ⟨_, eqComp_mem_equator hp γ.2⟩ :=
    funext fun γ => by simp only [Set.domRestrict_apply, sphRetrPath, dif_pos γ.2]
  rw [e]
  have hc : Continuous fun γ : sphNbhd p =>
      eqComp p ((γ.1 : ℝ → EuclideanSpace ℝ (Fin (n + 1 + 1))) (1 / 2)) :=
    ((continuous_eqComp p).comp continuous_apply_half_sph).comp continuous_subtype_val
  exact (continuous_semicircle hp).comp
    (((hc.norm.inv₀ fun γ => norm_ne_zero_iff.2 γ.2).smul hc).subtype_mk _)

/-- On `Ω^d`: `ω ∈ O`, and the retraction agrees with `ω` on `[0, 1]`. -/
theorem mem_sphNbhd_and_eqOn (hp : p ∈ Sph (n + 1)) {γ : PathSp (Sph (n + 1)) p (-p)}
    (hγ : γ ∈ minPaths (Sph (n + 1)) p (-p)) :
    γ ∈ sphNbhd p ∧ EqOn (sphRetrPath hp γ) γ (Icc 0 1) := by
  obtain ⟨u, heq⟩ := exists_eqOn_semicircle hp hγ
  have hhalf : (γ : ℝ → EuclideanSpace ℝ (Fin (n + 1 + 1))) (1 / 2) = u := by
    rw [heq ⟨by norm_num, by norm_num⟩, greatCircle_pi_half]
  have hu0 : (u : EuclideanSpace ℝ (Fin (n + 1 + 1))) ≠ 0 := fun h => by
    have := u.2.1
    rw [h, norm_zero] at this
    exact zero_ne_one this
  have hmem : γ ∈ sphNbhd p := by
    change eqComp p _ ≠ 0
    rw [hhalf, eqComp_of_mem_equator u.2]
    exact hu0
  refine ⟨hmem, fun t ht => ?_⟩
  rw [sphRetrPath, dif_pos hmem]
  have : (⟨_, eqComp_mem_equator hp hmem⟩ : equator p) = u := by
    apply Subtype.ext
    change ‖eqComp p _‖⁻¹ • eqComp p _ = _
    rw [hhalf, eqComp_of_mem_equator u.2, u.2.1, inv_one, one_smul]
  rw [this]
  exact (heq ht).symm

/-- **The neighbourhood retract of Theorem 22.1 for `Sⁿ⁺¹`**: `Ω^d(Sⁿ⁺¹; p, −p)` is a retract of
the open neighbourhood `O = Morse.sphNbhd p`. -/
theorem exists_retraction_minPaths_sph (hp : p ∈ Sph (n + 1)) :
    ∃ O : Set (PathSp (Sph (n + 1)) p (-p)), IsOpen O ∧ minPaths _ p (-p) ⊆ O ∧
      ∃ ρ : PathSp (Sph (n + 1)) p (-p) → PathSp (Sph (n + 1)) p (-p),
        ContinuousOn ρ O ∧ (∀ γ ∈ O, ρ γ ∈ minPaths _ p (-p)) ∧
        ∀ γ ∈ minPaths _ p (-p), ρ γ = γ := by
  classical
  set S := minPaths (Sph (n + 1)) p (-p)
  refine ⟨sphNbhd p, isOpen_sphNbhd, fun γ hγ => (mem_sphNbhd_and_eqOn hp hγ).1,
    fun γ => if γ ∈ S then γ else sphRetrPath hp γ, ?_, fun γ hγ => ?_, fun γ hγ => if_pos hγ⟩
  · rw [continuousOn_iff_continuous_domRestrict]
    refine PathSp.continuous_of_edist_eq_zero
      (continuousOn_iff_continuous_domRestrict.1 (continuousOn_sphRetrPath hp)) fun γ => ?_
    simp only [domRestrict_apply]
    split_ifs with h
    · rw [edist_comm]
      exact PathSp.edist_eq_zero_of_eqOn (mem_sphNbhd_and_eqOn hp h).2
    · exact edist_self _
  · simp only
    split_ifs with h
    · exact h
    · rw [sphRetrPath, dif_pos hγ]
      exact semicircle_mem_minPaths hp _

/-! ### The equator is `Sⁿ` -/

/-- **The equator of `Sⁿ⁺¹` is `Sⁿ`**: an isometry of `pᗮ` with `ℝⁿ⁺¹`. -/
def equatorHomeomorph (hp : p ∈ Sph (n + 1)) : equator p ≃ₜ Sph n := by
  have hp0 : p ≠ 0 := fun h => by
    have := norm_of_mem_sph hp
    rw [h, norm_zero] at this
    exact zero_ne_one this
  haveI : Fact (finrank ℝ (EuclideanSpace ℝ (Fin (n + 1 + 1))) = n + 1 + 1) :=
    ⟨finrank_euclideanSpace_fin⟩
  have hfin : finrank ℝ (ℝ ∙ p)ᗮ = n + 1 := Submodule.finrank_orthogonal_span_singleton hp0
  let e : (ℝ ∙ p)ᗮ ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n + 1)) :=
    ((stdOrthonormalBasis ℝ (ℝ ∙ p)ᗮ).reindex (finCongr hfin)).repr
  have hmem : ∀ u : equator p, (u : EuclideanSpace ℝ (Fin (n + 1 + 1))) ∈ (ℝ ∙ p)ᗮ := fun u =>
    Submodule.mem_orthogonal_singleton_iff_inner_right.2 u.2.2
  exact {
    toFun := fun u => ⟨e ⟨u, hmem u⟩, mem_iff_norm.2 (by rw [LinearIsometryEquiv.norm_map]; exact u.2.1)⟩
    invFun := fun v => ⟨(e.symm v.1 : EuclideanSpace ℝ (Fin (n + 1 + 1))),
      ⟨(e.symm.norm_map v.1).trans (mem_iff_norm.1 v.2),
       Submodule.mem_orthogonal_singleton_iff_inner_right.1 (e.symm v.1).2⟩⟩
    left_inv := fun u => Subtype.ext (by simp)
    right_inv := fun v => Subtype.ext (by simp)
    continuous_toFun := by fun_prop
    continuous_invFun := by fun_prop }

/-! ### Corollary 22.3 -/

theorem hidx_sph (hp : p ∈ Sph (n + 1)) :
    ∀ γ (hγ : γ ∈ pathSpace (Sph (n + 1)) p (-p)), IsUnbrokenGeodesic (sphSub (n + 1)) γ →
      (∃ γ' ∈ pathSpace (Sph (n + 1)) p (-p), energy γ' 0 1 < energy γ 0 1) →
      ((2 * n : ℕ) : ℕ∞) ≤ formIndex (energyHessian (sphSub (n + 1)) hγ) :=
  fun _ hγ hgeo hnm => le_formIndex_of_not_minimal_sph hp hγ hgeo hnm

theorem hball_sph (p : EuclideanSpace ℝ (Fin (n + 1 + 1))) (r : ℝ) :
    IsCompact (closedRiemBall (Sph (n + 1)) p r) :=
  isCompact_closedRiemBall_of_isClosed (sphSub (n + 1)) isClosed_sph p r

/-- **Corollary 22.3 (Freudenthal)** (Milnor p. 119): `π_i(Sⁿ) ≅ π_{i+1}(Sⁿ⁺¹)` for
`i ≤ 2n − 2`, at any base points. -/
theorem corollary_22_3 {n i : ℕ} (hi : i + 2 ≤ 2 * n) (x : Sph n) (y : Sph (n + 1)) :
    Nonempty (π_ i (Sph n) x ≃ π_ (i + 1) (Sph (n + 1)) y) := by
  obtain ⟨p, hp⟩ := y
  let h := equatorHomeomorph hp
  let H := sphMinPathsHomotopyEquiv hp
  obtain ⟨e₃⟩ := corollary_22_2 (sphSub (n + 1)) hp (neg_mem_sph hp) (hball_sph p) (hidx_sph hp)
    (exists_retraction_minPaths_sph hp) hi (H.toFun (h.symm x))
  exact ⟨(Homotopy.homotopyGroupEquivOfHomotopyEquiv h.symm.toHomotopyEquiv x).trans
    ((Homotopy.homotopyGroupEquivOfHomotopyEquiv H (h.symm x)).trans e₃)⟩

/-- **Corollary 22.3, the second half of Freudenthal's theorem**: for `i = 2n − 1` (and below)
there is a surjection `π_i(Sⁿ) → π_{i+1}(Sⁿ⁺¹)`. -/
theorem corollary_22_3_surjective {n i : ℕ} (hi : i + 1 ≤ 2 * n) (x : Sph n) (y : Sph (n + 1)) :
    ∃ f : π_ i (Sph n) x → π_ (i + 1) (Sph (n + 1)) y, Surjective f := by
  obtain ⟨p, hp⟩ := y
  let h := equatorHomeomorph hp
  let H := sphMinPathsHomotopyEquiv hp
  obtain ⟨f, hf⟩ := corollary_22_2_surjective (sphSub (n + 1)) hp (neg_mem_sph hp) (hball_sph p)
    (hidx_sph hp) (exists_retraction_minPaths_sph hp) hi (H.toFun (h.symm x))
  let E := (Homotopy.homotopyGroupEquivOfHomotopyEquiv (N := Fin i) h.symm.toHomotopyEquiv x).trans
    (Homotopy.homotopyGroupEquivOfHomotopyEquiv (N := Fin i) H (h.symm x))
  exact ⟨f ∘ E, hf.comp E.surjective⟩

end Morse
