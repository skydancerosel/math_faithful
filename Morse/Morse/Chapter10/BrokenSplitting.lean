import Morse.Chapter10.BrokenVariation
import Morse.Chapter9.IndexReduction

/-!
Milnor, *Morse Theory*, §16, pp. 91–92: the identification of `TB_γ` with the broken Jacobi
fields, and Lemma 15.4 for Milnor's subdivision of §16, for a submanifold `N ⊆ ℝᴷ` with the
induced metric.

# Broken Jacobi fields for the subdivision of §16

## Milnor's text, paraphrased

(pp. 91–92) The tangent space `TB_γ` at a geodesic `γ` is identified with the space
`TΩ_γ(t₀, …, t_k)` of broken Jacobi fields along `γ` (§15): a variation of `γ` through broken
geodesics has a broken Jacobi field as variation field (Lemma 14.3).  "Now the statement that the
index (or the nullity) of `E_**` at `γ` is equal to the index (or nullity) of `E'_**` at `γ` is an
immediate consequence of Lemma 15.4."

## In the embedded setting

Let `γ = B.path y` be an unbroken geodesic (a critical point of `E'`).

* `Morse.IsJacobiField.comp_affine`: Jacobi fields along `γ` restrict to Jacobi fields along an
  affinely reparametrized segment `s ↦ γ(h s + a)` (both terms of the Jacobi equation scale by
  `h²`).
* `Morse.BrokenSetup.not_isConjugate_seg`: **no segment `[tᵢ, t_{i+1}]` contains a pair of
  conjugate points at its ends**: the segment is the radial geodesic `s ↦ exp_{xᵢ}(s vᵢ)` with
  `‖vᵢ‖ < δ ≤` a normal radius at `xᵢ` (`Morse.remark_14_5_of_isNormalRadius`).
* `Morse.BrokenSetup.exists_brokenSpace_node`, `Morse.BrokenSetup.brokenSpace_eq_zero`: broken
  Jacobi fields for the break points `t₁, …, t_m` (`Morse.brokenSpace`, Chapter 9) with arbitrary
  tangent values at the break points exist and are unique; `Morse.BrokenSetup.brokenEquiv`:
  `TΩ_γ(t₀, …, t_k) ≅ ∏_j T_{y_j}N`.
* `Morse.BrokenSetup.energyHessian_nodeZero_nonneg`: on the fields vanishing at the break points,
  `E_** ≥ 0`, because the broken geodesic minimizes the energy among paths through its break
  points (`Morse.BrokenSetup.energy'_nodeVal_le`, formula (∗) and Schwarz's inequality);
  `Morse.BrokenSetup.energyHessian_nodeZero_pos`: `E_**` is even positive definite there (a null
  vector would be a Jacobi field vanishing at `t₀` and `t₁`, hence zero).
* **Lemma 15.4 for the subdivision of §16**: `Morse.BrokenSetup.formIndex_brokenSpace` (the index
  of `E_**` equals its index on `TΩ_γ(t₀, …, t_k)`) and
  `Morse.BrokenSetup.finrank_ker_brokenSpace` (the nullity on `TΩ_γ(t₀, …, t_k)` is the multiplicity
  of `γ(1)` as a conjugate point of `γ(0)`, which is the nullity of `E_**` by Theorem 14.1).

## What Milnor leaves implicit

* **A hidden hypothesis** (exposition, Chapter 10 §3): Lemma 15.4 is proved in §15 for a
  subdivision so fine that the index form is positive definite on fields vanishing at the
  division points (`Morse.IsFine`); the subdivision of §16 need not be that fine.  What the proof
  uses is (1) uniqueness and existence of broken Jacobi fields with given values at the break
  points, i.e. the ends of each segment are not conjugate, and (2) positivity of `E_**` on the
  fields vanishing at the break points.  For §16, (1) holds because each segment lies within a
  normal radius, and (2) because the broken geodesic minimizes the energy among paths through
  the same break points, with (1) excluding null vectors.
-/

open Set Filter Topology Function Module Metric MeasureTheory
open scoped ContDiff Manifold RealInnerProductSpace ENNReal Interval

noncomputable section

namespace Morse

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {N : Set V} {hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N}

/-! ### Jacobi fields under an affine change of parameter -/

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] in
/-- The derivative under an affine change of the parameter. -/
theorem deriv_comp_affine {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : ℝ → E)
    (h a s : ℝ) : deriv (fun s => f (h * s + a)) s = h • deriv f (h * s + a) := by
  have := deriv_comp_mul_left h (fun y => f (y + a)) s
  simp only [deriv_comp_add_const] at this
  exact this

omit [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
theorem curvR_smul_smul (x a b c : V) (h : ℝ) :
    curvR hN x (h • a) b (h • c) = (h * h) • curvR hN x a b c := by
  by_cases hx : x ∈ N
  · simp only [curvR_of_mem hN hx, curvOp, map_smul, sub_apply,
      ContinuousLinearMap.comp_apply, smul_apply, smul_sub, smul_smul]
  · simp [curvR, hx]

omit [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
/-- **Jacobi fields under an affine change of parameter**: if `J` is a Jacobi field along `γ`,
then `s ↦ J(h s + a)` is a Jacobi field along `s ↦ γ(h s + a)` (`0 ≤ a`, `0 < h`, `a + h ≤ 1`):
`D²/ds²` and `R(γ̃', ·)γ̃'` both scale by `h²`. -/
theorem IsJacobiField.comp_affine {γ J : ℝ → V} (hJ : IsJacobiField hN γ J) {a h : ℝ}
    (ha : 0 ≤ a) (hh : 0 < h) (hah : a + h ≤ 1) :
    IsJacobiField hN (fun s => γ (h * s + a)) (fun s => J (h * s + a)) := by
  have hmaps : ∀ s ∈ Icc (0 : ℝ) 1, h * s + a ∈ Icc (0 : ℝ) 1 := fun s hs =>
    ⟨by nlinarith [hs.1], by nlinarith [hs.2]⟩
  have hmapsI : ∀ s ∈ Ioo (0 : ℝ) 1, h * s + a ∈ Ioo (0 : ℝ) 1 := fun s hs =>
    ⟨by nlinarith [hs.1], by nlinarith [hs.2]⟩
  have haff : ContDiff ℝ ∞ (fun s : ℝ => h * s + a) :=
    (contDiff_const.mul contDiff_id).add contDiff_const
  refine ⟨hJ.contDiffOn.comp haff.contDiffOn hmaps, fun s hs => hJ.tangent _ (hmaps s hs),
    fun s hs => ?_⟩
  set τ := h * s + a
  have hτ : τ ∈ Ioo (0 : ℝ) 1 := hmapsI s hs
  have hcovfun : covD hN (fun s => γ (h * s + a)) (fun s => J (h * s + a)) =
      fun s' => h • covD hN γ J (h * s' + a) := funext fun s' => by
    simp only [covD, deriv_comp_affine, map_smul]
  have hcov2 : covD hN (fun s => γ (h * s + a))
      (covD hN (fun s => γ (h * s + a)) (fun s => J (h * s + a))) s =
      (h * h) • covD hN γ (covD hN γ J) τ := by
    rw [hcovfun, covD, deriv_fun_const_smul_field h (fun s' => covD hN γ J (h * s' + a)),
      deriv_comp_affine (covD hN γ J) h a s, covD, map_smul, map_smul, smul_smul]
  have hγd : deriv (fun s => γ (h * s + a)) s = h • deriv γ τ := deriv_comp_affine γ h a s
  rw [jacobiExpr, hcov2, hγd, curvR_smul_smul]
  have := hJ.eq τ hτ
  rw [jacobiExpr] at this
  rw [← smul_add, this, smul_zero]

/-! ### Second derivatives at a minimum -/

/-- **A minimum has a nonnegative second derivative** (the step of Lemma 13.6, Milnor p. 76): if
`0` is a local minimum of `f`, `f` is differentiable near `0` and `f'` has derivative `L` at `0`,
then `L ≥ 0`. -/
theorem nonneg_of_isLocalMin_of_hasDerivAt {f : ℝ → ℝ} {L : ℝ} (hmin : IsLocalMin f 0)
    (hf : DifferentiableAt ℝ f 0) (hL : HasDerivAt (deriv f) L 0) : 0 ≤ L := by
  by_contra hneg
  push Not at hneg
  have hmax : IsLocalMax f 0 := isLocalMax_of_deriv_deriv_neg (by rw [hL.deriv]; exact hneg)
    hmin.deriv_eq_zero hf.continuousAt
  have hconst : f =ᶠ[𝓝 0] fun _ => f 0 := by
    filter_upwards [hmin, hmax] with u h1 h2
    exact le_antisymm h2 h1
  have h0 : deriv (deriv f) 0 = 0 := by
    rw [hconst.deriv.deriv_eq]
    simp
  rw [hL.deriv] at h0
  exact hneg.ne h0

namespace BrokenSetup

variable {p q : V} {c : ℝ} {m : ℕ} (B : BrokenSetup hN p q c m)

/-! ### Minimality of broken geodesics among paths through the same break points -/

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
/-- **The broken geodesic minimizes the energy among paths through its break points**: for every
`γ ∈ Ω(N; p, q)`, `Σᵢ ρ(γ(tᵢ), γ(tᵢ₊₁))²/(t_{i+1} − tᵢ) ≤ E(γ)` (Schwarz's inequality on each
segment; formula (∗)). -/
theorem energy'_nodeVal_le {γ : ℝ → V} (hγ : γ ∈ pathSpace N p q) :
    B.energy' (B.nodeVal γ) ≤ energy γ 0 1 := by
  have hint : ∀ i j, IntervalIntegrable (fun τ => ‖deriv γ τ‖ ^ 2) volume (B.t i) (B.t j) := by
    have hmem : ∀ i, B.t i ∈ uIcc (0 : ℝ) 1 := fun i => by
      rw [uIcc_of_le zero_le_one]; exact ⟨B.t_nonneg i, B.t_le_one i⟩
    exact fun i j => hγ.1.intervalIntegrable_norm_deriv_sq.mono_set
      (uIcc_subset_uIcc (hmem i) (hmem j))
  have hsum := sum_integral_fin B.t hint
  rw [B.t_zero, B.t_last] at hsum
  rw [energy, ← hsum, energy']
  refine Finset.sum_le_sum fun i _ => ?_
  rw [B.vert_nodeVal hγ, B.vert_nodeVal hγ]
  have hl := B.len_pos i
  have h0 := B.t_nonneg i.castSucc
  have hle := B.t_le_iff.2 (Fin.castSucc_lt_succ (i := i)).le
  have h1 := B.t_le_one i.succ
  have hps : IsPiecewiseSmooth γ (B.t i.castSucc) (B.t i.succ) := hγ.1.mono h0 hle h1
  have hρ := riemDist_le_pathLength (N := N) hps fun τ hτ => hγ.2.1 τ ⟨h0.trans hτ.1, hτ.2.trans h1⟩
  have hL := pathLength_sq_le_energy hps
  have hL0 := hps.isAdmissible.pathLength_nonneg
  have hρL := ENNReal.toReal_le_of_le_ofReal hL0 hρ
  rw [div_le_iff₀ hl]
  calc (riemDist (N := N) (γ (B.t i.castSucc)) (γ (B.t i.succ))).toReal ^ 2
      ≤ pathLength γ (B.t i.castSucc) (B.t i.succ) ^ 2 := by gcongr
    _ ≤ (B.t i.succ - B.t i.castSucc) * energy γ (B.t i.castSucc) (B.t i.succ) := hL
    _ = _ := by rw [energy, mul_comm]; rfl

/-! ### No conjugate points on the segments -/

/-- On `[0, 1]`, the reparametrized `i`-th segment of a broken geodesic is the radial geodesic
`s ↦ exp_{xᵢ}(s vᵢ)`. -/
theorem path_affine_eq {y : Fin m → V} (hy : y ∈ B.nodes) (i : Fin (m + 1)) :
    EqOn (fun s => B.path y (B.len i * s + B.t i.castSucc))
      (fun s => exp hN (vert p q y i.castSucc)
        (s • B.joinVec (vert p q y i.castSucc) (vert p q y i.succ))) (Icc 0 1) := by
  intro s hs
  have hl := B.len_pos i
  have hmem : B.len i * s + B.t i.castSucc ∈ Icc (B.t i.castSucc) (B.t i.succ) :=
    ⟨by nlinarith [hs.1], by
      have : B.t i.succ = B.t i.castSucc + B.len i := by simp [Subdivision.len]
      nlinarith [hs.2]⟩
  simp only
  rw [B.path_eq_segPath hy i hmem, segPath]
  congr 2
  field_simp
  ring

section Unbroken

variable {y : Fin m → V} (hy : y ∈ B.nodes) (hgeo : IsUnbrokenGeodesic hN (B.path y))
include hy hgeo

/-- The broken geodesic, when unbroken, is a smooth curve. -/
theorem isSmoothCurveIn_path : IsSmoothCurveIn hN (B.path y) :=
  hgeo.isSmoothCurveIn hN (B.path_mem_pathSpace hy)

/-- **No conjugate points at the ends of a segment** (exposition, Chapter 10 §3 (e)): if
`γ = B.path y` is an unbroken geodesic, `tᵢ` and `t_{i+1}` are not conjugate along `γ`.  The
segment is the radial geodesic `s ↦ exp_{xᵢ}(s vᵢ)` with `‖vᵢ‖ < δ`, below a normal radius at
`xᵢ`, along which a Jacobi field vanishing at both ends vanishes (Remark 14.5). -/
theorem not_isConjugate_seg (i : Fin (m + 1)) :
    ¬IsConjugate hN (B.path y) (B.t i.castSucc) (B.t i.succ) := by
  rintro ⟨-, -, -, J, hJ, hJa, hJb, t, ht, hJt⟩
  have hc := B.isSmoothCurveIn_path hy hgeo
  set a := B.t i.castSucc
  set h := B.len i
  have hl : 0 < h := B.len_pos i
  have hb : a + h = B.t i.succ := by simp [a, h, Subdivision.len]
  have hJ' := hJ.comp_affine (a := a) (h := h) (B.t_nonneg _) hl (by rw [hb]; exact B.t_le_one _)
  have hJ'' := hJ'.congr_curve (B.path_affine_eq hy i)
  set x := vert p q y i.castSucc
  have hxN : x ∈ N := B.vert_mem hy.1 _
  obtain ⟨ε, hδε, hnr⟩ := B.normal ⟨x, hxN⟩ (B.vert_mem_ball hy i.castSucc)
  have hv := B.joinVec_vert hy i
  have hvT := (prj_eq_self_iff hN hxN).1 hv.1
  have hz := remark_14_5_of_isNormalRadius (q := ⟨x, hxN⟩) hnr hvT (hv.2.1.trans_le hδε) hJ''
    (by simp only [mul_zero, zero_add]; exact hJa)
    (by simp only [mul_one]; rw [add_comm, hb]; exact hJb)
  -- `J` vanishes on `[tᵢ, t_{i+1}]`, hence everywhere
  have hJ0 : EqOn (fun t => J (projIcc (0 : ℝ) 1 zero_le_one t)) 0 (Icc a (B.t i.succ)) := by
    intro τ hτ
    have hτ01 : τ ∈ Icc (0 : ℝ) 1 := ⟨(B.t_nonneg _).trans hτ.1, hτ.2.trans (B.t_le_one _)⟩
    have hs : (τ - a) / h ∈ Icc (0 : ℝ) 1 := ⟨div_nonneg (by linarith [hτ.1]) hl.le, by
      rw [div_le_one hl]; linarith [hτ.2]⟩
    have := hz hs
    simp only [Pi.zero_apply] at this ⊢
    rw [projIcc_of_mem _ hτ01]
    rwa [show h * ((τ - a) / h) + a = τ by field_simp; ring] at this
  have hlt : a < B.t i.succ := by linarith
  have := jacobiSpace_eq_zero_of_eqOn hc (hJ.comp_projIcc_mem hc) (B.t_nonneg _) hlt
    (B.t_le_one _) hJ0
  apply hJt
  have h1 := congrFun this t
  simpa [projIcc_of_mem _ ht] using h1

/-! ### Broken Jacobi fields with given values at the break points -/

/-- **Uniqueness of broken Jacobi fields**: a broken Jacobi field for the break points
`t₁, …, t_m` vanishing at them vanishes. -/
theorem brokenSpace_eq_zero {X : pathTangent hN (B.path y)}
    (hX : X ∈ brokenSpace (B.isSmoothCurveIn_path hy hgeo) B.breaks 1)
    (hnodes : ∀ j : Fin m, (X : ℝ → V) (B.t j.castSucc.succ) = 0) : X = 0 := by
  have hc := B.isSmoothCurveIn_path hy hgeo
  refine Subtype.ext (funext fun t => ?_)
  by_cases ht : t ∈ Icc (0 : ℝ) 1
  · have hti := B.mem_Icc_segOf ht
    generalize B.segOf t = i at hti
    have hpiece : ∀ b ∈ B.breaks, b ∉ Ioo (B.t i.castSucc) (B.t i.succ) := by
      intro b hb hbI
      obtain ⟨j, rfl⟩ := B.mem_breaks.1 hb
      have h1 := B.t_lt_iff.1 hbI.1
      have h2 := B.t_lt_iff.1 hbI.2
      rw [Fin.lt_def] at h1 h2
      simp only [Fin.val_succ, Fin.val_castSucc] at h1 h2
      omega
    obtain ⟨J, hJ, hXJ⟩ := hX.2 _ _ (B.t_nonneg _) (B.t_lt_iff.2 Fin.castSucc_lt_succ)
      (B.t_le_one _) hpiece
    have hend : ∀ k : Fin (m + 2), (X : ℝ → V) (B.t k) = 0 := by
      intro k
      induction k using Fin.cases with
      | zero => rw [B.t_zero]; exact X.2.2.2.1
      | succ k =>
        induction k using Fin.lastCases with
        | last => rw [Fin.succ_last, B.t_last]; exact X.2.2.2.2
        | cast j => exact hnodes j
    have hJa : J (B.t i.castSucc) = 0 := by
      rw [← hXJ ⟨le_rfl, (B.t_lt_iff.2 Fin.castSucc_lt_succ).le⟩]; exact hend _
    have hJb : J (B.t i.succ) = 0 := by
      rw [← hXJ ⟨(B.t_lt_iff.2 Fin.castSucc_lt_succ).le, le_rfl⟩]; exact hend _
    have hJ0 : ∀ τ ∈ Icc (0 : ℝ) 1, J τ = 0 := by
      by_contra hne
      push Not at hne
      obtain ⟨τ, hτ, hJτ⟩ := hne
      exact B.not_isConjugate_seg hy hgeo i ⟨⟨B.t_nonneg _, B.t_le_one _⟩,
        ⟨B.t_nonneg _, B.t_le_one _⟩, (B.t_lt_iff.2 Fin.castSucc_lt_succ).ne, J, hJ.1, hJa, hJb,
        τ, hτ, hJτ⟩
    rw [hXJ hti, hJ0 t ht]
    rfl
  · exact hX.1 t ht

/-- **Existence of broken Jacobi fields with given tangent values at the break points.** -/
theorem exists_brokenSpace_node (x : Fin m → V) (hx : ∀ j, prj hN (y j) (x j) = x j) :
    ∃ X ∈ brokenSpace (B.isSmoothCurveIn_path hy hgeo) B.breaks 1,
      ∀ j : Fin m, (X : ℝ → V) (B.t j.castSucc.succ) = x j := by
  classical
  have hc := B.isSmoothCurveIn_path hy hgeo
  set γ := B.path y
  -- the prescribed values at all the division points
  set ξ : Fin (m + 2) → V := vert 0 0 x
  have hγt : ∀ k : Fin (m + 2), γ (B.t k) = vert p q y k := fun k => by
    have := B.vert_nodeVal (B.path_mem_pathSpace hy) k
    rw [B.nodeVal_path hy] at this
    exact this.symm
  have hξ : ∀ k, ξ k ∈ tanAt hN (γ (B.t k)) := by
    intro k
    rw [mem_tanAt hN (hc.mem _ ⟨B.t_nonneg k, B.t_le_one k⟩)]
    induction k using Fin.cases with
    | zero => simp [ξ]
    | succ k =>
      induction k using Fin.lastCases with
      | last => simp only [ξ, Fin.succ_last, vert_last, map_zero]
      | cast j =>
        simp only [ξ, vert_inner]
        rw [hγt, vert_inner]
        exact hx j
  have hseg : ∀ i : Fin (m + 1), ∃ J ∈ jacobiSpace hN γ hc,
      J (B.t i.castSucc) = ξ i.castSucc ∧ J (B.t i.succ) = ξ i.succ := by
    intro i
    have hbij := jacEvalEnds_bijective_of_not_isConjugate hc ⟨B.t_nonneg i.castSucc,
      B.t_le_one _⟩ ⟨B.t_nonneg i.succ, B.t_le_one _⟩ (B.t_lt_iff.2 Fin.castSucc_lt_succ).ne
      (B.not_isConjugate_seg hy hgeo i)
    obtain ⟨J, hJ⟩ := hbij.2 (⟨ξ i.castSucc, hξ _⟩, ⟨ξ i.succ, hξ _⟩)
    exact ⟨J, J.2, congrArg (fun z => (z.1 : V)) hJ, congrArg (fun z => (z.2 : V)) hJ⟩
  choose J hJ hJa hJb using hseg
  set X : ℝ → V := fun t => if t ∈ Icc (0 : ℝ) 1 then J (B.segOf t) t else 0
  -- on each segment, `X` is the Jacobi field of the segment
  have hXseg : ∀ i : Fin (m + 1), EqOn X (J i) (Icc (B.t i.castSucc) (B.t i.succ)) := by
    intro i t ht
    have ht01 : t ∈ Icc (0 : ℝ) 1 := ⟨(B.t_nonneg _).trans ht.1, ht.2.trans (B.t_le_one _)⟩
    simp only [X, if_pos ht01]
    rcases eq_or_lt_of_le ht.2 with h | h
    · subst h
      by_cases hi : i = Fin.last m
      · subst hi
        rw [B.segOf_of_one_le (by rw [Fin.succ_last, B.t_last])]
      · obtain ⟨k, rfl⟩ := Fin.exists_castSucc_eq.2 hi
        have hs : B.segOf (B.t k.castSucc.succ) = k.succ :=
          B.segOf_eq le_rfl (by rw [B.t_lt_iff]; exact Fin.castSucc_lt_succ (i := k.succ))
        rw [hs]
        exact (hJa k.succ).trans (hJb k.castSucc).symm
    · rw [B.segOf_eq ht.1 h]
  have hbroken : IsBrokenJacobi hN γ hc B.breaks 1 X := by
    intro s s' hs hss' hs' hpiece
    obtain ⟨i, hsi, hs'i⟩ := B.exists_seg_of_piece hs hss' hs' hpiece
    exact ⟨J i, hJ i, fun t ht => hXseg i ⟨hsi.trans ht.1, ht.2.trans hs'i⟩⟩
  have hvalue : ∀ k : Fin (m + 2), X (B.t k) = ξ k := by
    intro k
    rcases Fin.eq_castSucc_or_eq_last k with ⟨i, rfl⟩ | rfl
    · rw [hXseg i ⟨le_rfl, (B.t_lt_iff.2 Fin.castSucc_lt_succ).le⟩, hJa]
    · rw [← Fin.succ_last, hXseg (Fin.last m) ⟨(B.t_lt_iff.2 Fin.castSucc_lt_succ).le, le_rfl⟩,
        hJb]
  have hX0 : X 0 = 0 := by
    have := hvalue 0
    rwa [B.t_zero] at this
  have hX1 : X 1 = 0 := by
    have := hvalue (Fin.last (m + 1))
    rw [B.t_last] at this
    rw [this]
    simp [ξ]
  have hout : ∀ t ∉ Icc (0 : ℝ) 1, X t = 0 := fun t ht => by simp only [X, if_neg ht]
  -- `X ∈ TΩ_γ`
  have hpiece : ∀ s t, 0 ≤ s → s < t → t ≤ 1 → (∀ b ∈ B.breaks, b ∉ Ioo s t) →
      ContDiffOn ℝ ∞ X (Icc s t) := by
    intro s t hs hst ht hB
    obtain ⟨i, hsi, hti⟩ := B.exists_seg_of_piece hs hst ht hB
    exact ((hJ i).1.contDiffOn.mono (Icc_subset_Icc hs ht)).congr fun τ hτ =>
      hXseg i ⟨hsi.trans hτ.1, hτ.2.trans hti⟩
  have hmem : X ∈ pathTangent hN γ := by
    refine ⟨⟨zero_le_one, continuousOn_of_piecewise (B := B.breaks) fun s t hs hst ht hB =>
      (hpiece s t hs hst ht hB).continuousOn, B.breaks, hpiece⟩, fun t ht => ?_, hX0, hX1⟩
    have hti := B.mem_Icc_segOf ht
    rw [hXseg _ hti]
    exact (hJ _).1.tangent t ht
  refine ⟨⟨X, hmem⟩, ⟨hout, hbroken⟩, fun j => ?_⟩
  change X (B.t j.castSucc.succ) = x j
  rw [hvalue]
  simp [ξ]

omit hgeo in
/-- The values of a broken Jacobi field at the break points are tangent. -/
theorem brokenSpace_node_mem {X : pathTangent hN (B.path y)} (j : Fin m) :
    (X : ℝ → V) (B.t j.castSucc.succ) ∈ tangentSubspace hN ⟨y j, hy.1 j⟩ := by
  have h := X.2.2.1 (B.t j.castSucc.succ) ⟨B.t_nonneg _, B.t_le_one _⟩
  rw [show B.path y (B.t j.castSucc.succ) = y j from congrFun (B.nodeVal_path hy) j] at h
  exact (prj_eq_self_iff hN (hy.1 j)).1 h

/-- `X ↦ (X(t_j))_j`, from the broken Jacobi fields to `∏_j T_{y_j}N`. -/
def brokenNodeMap :
    brokenSpace (B.isSmoothCurveIn_path hy hgeo) B.breaks 1 →ₗ[ℝ]
      Submodule.pi univ fun j => tangentSubspace hN ⟨y j, hy.1 j⟩ where
  toFun X := ⟨fun j => ((X : pathTangent hN (B.path y)) : ℝ → V) (B.t j.castSucc.succ),
    fun j _ => B.brokenSpace_node_mem hy j⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem brokenNodeMap_bijective : Bijective (B.brokenNodeMap hy hgeo) := by
  constructor
  · rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro X hX
    rw [LinearMap.mem_ker] at hX
    have hnodes : ∀ j : Fin m,
        ((X : pathTangent hN (B.path y)) : ℝ → V) (B.t j.castSucc.succ) = 0 := fun j =>
      congrFun (congrArg Subtype.val hX) j
    exact (Submodule.mem_bot ℝ).2 (Subtype.ext (B.brokenSpace_eq_zero hy hgeo X.2 hnodes))
  · rintro ⟨x, hx⟩
    obtain ⟨X, hX, hXx⟩ := B.exists_brokenSpace_node hy hgeo x fun j =>
      (prj_eq_self_iff hN (hy.1 j)).2 (hx j trivial)
    exact ⟨⟨X, hX⟩, Subtype.ext (funext hXx)⟩

/-- **`TΩ_γ(t₀, …, t_k) ≅ ∏_j T_{y_j}N`** (Milnor p. 92: `TB_γ` is identified with the broken
Jacobi fields). -/
def brokenEquiv : brokenSpace (B.isSmoothCurveIn_path hy hgeo) B.breaks 1 ≃ₗ[ℝ]
    Submodule.pi univ fun j => tangentSubspace hN ⟨y j, hy.1 j⟩ :=
  LinearEquiv.ofBijective _ (B.brokenNodeMap_bijective hy hgeo)

@[simp] theorem brokenEquiv_apply (X : brokenSpace (B.isSmoothCurveIn_path hy hgeo) B.breaks 1)
    (j : Fin m) : ((B.brokenEquiv hy hgeo X : Fin m → V) j) =
      ((X : pathTangent hN (B.path y)) : ℝ → V) (B.t j.castSucc.succ) := rfl

/-! ### The Hessian on broken Jacobi fields; positivity on the fields vanishing at the break
points -/

/-- **`E_**` on broken Jacobi fields** (Milnor p. 84, for the break points of §16):
`E_**(X, Y) = −2 Σ_j ⟨Y(t_j), Δ_{t_j} DX/dt⟩`. -/
theorem energyHessian_brokenSpace_eq {X Y : pathTangent hN (B.path y)}
    (hX : X ∈ brokenSpace (B.isSmoothCurveIn_path hy hgeo) B.breaks 1) :
    energyHessian hN (B.path_mem_pathSpace hy) X Y = -2 * ∑ j : Fin m,
      ⟪(Y : ℝ → V) (B.t j.castSucc.succ),
        prj hN (B.path y (B.t j.castSucc.succ)) (jump X (B.t j.castSucc.succ))⟫ := by
  have hc := B.isSmoothCurveIn_path hy hgeo
  rw [energyHessian_eq_jumps (B.path_mem_pathSpace hy) X Y (B := B.breaks) fun t ht htB =>
    hX.2.eventuallyEq hc one_pos (fun b hb => B.breaks_subset hb) hX.1 t ht (by
      rw [Finset.mem_insert, not_or]; exact ⟨ht.2.ne, htB⟩)]
  have hfilter : B.breaks.filter (· ∈ Ioo (0 : ℝ) 1) = B.breaks :=
    Finset.filter_true_of_mem fun x hx => B.breaks_subset hx
  rw [hfilter, Subdivision.breaks, Finset.sum_image]
  intro j _ k _ hjk
  exact Fin.castSucc_injective _ (Fin.succ_injective _ (B.strictMono.injective hjk))

/-- **Broken Jacobi fields are perpendicular to the fields vanishing at the break points**
(Lemma 15.3 for §16). -/
theorem energyHessian_brokenSpace_nodeZero {X Y : pathTangent hN (B.path y)}
    (hX : X ∈ brokenSpace (B.isSmoothCurveIn_path hy hgeo) B.breaks 1)
    (hY : ∀ j : Fin m, (Y : ℝ → V) (B.t j.castSucc.succ) = 0) :
    energyHessian hN (B.path_mem_pathSpace hy) X Y = 0 := by
  rw [B.energyHessian_brokenSpace_eq hy hgeo hX]
  simp [hY]

/-- **`E_** ≥ 0` on the fields vanishing at the break points**: the variation
`exp_{γ(t)}(u Y(t))` keeps the break points fixed, so its energy is at least that of the broken
geodesic (`Morse.BrokenSetup.energy'_nodeVal_le`); a minimum has a nonnegative second
derivative, which is `E_**(Y, Y)` (Remark 13.5). -/
theorem energyHessian_nodeZero_nonneg {Y : pathTangent hN (B.path y)}
    (hY : ∀ j : Fin m, (Y : ℝ → V) (B.t j.castSucc.succ) = 0) :
    0 ≤ energyHessian hN (B.path_mem_pathSpace hy) Y Y := by
  have hγ := B.path_mem_pathSpace hy
  obtain ⟨ε, hε, Bv, hα, h0, hd⟩ := exists_variation_one hN hγ Y.2
  set α : ℝ → ℝ → V := fun u t => exp hN (B.path y t) (u • (Y : ℝ → V) t)
  have hαγ : ∀ t ∈ Icc (0 : ℝ) 1, α 0 t = B.path y t := h0
  set f : ℝ → ℝ := fun u => energy (α u) 0 1
  have hmin : IsLocalMin f 0 := by
    filter_upwards [isOpen_Ioo.mem_nhds (show (0 : ℝ) ∈ Ioo (-ε) ε from ⟨by linarith, hε⟩)]
      with u hu
    have hpath := hα.mem_pathSpace hu
    rw [show α 0 0 = p from (hαγ 0 ⟨le_rfl, zero_le_one⟩).trans hγ.2.2.1,
      show α 0 1 = q from (hαγ 1 ⟨zero_le_one, le_rfl⟩).trans hγ.2.2.2] at hpath
    have hnode : B.nodeVal (α u) = y := funext fun j => by
      have hj : B.path y (B.t j.castSucc.succ) = y j := congrFun (B.nodeVal_path hy) j
      simp only [nodeVal, α, hY j, smul_zero, hj, exp_zero (hy.1 j)]
    calc f 0 = energy (B.path y) 0 1 := energy_congr hαγ
      _ = B.energy' y := B.energy_path hy
      _ = B.energy' (B.nodeVal (α u)) := by rw [hnode]
      _ ≤ f u := B.energy'_nodeVal_le hpath
  have hdd := hasDerivAt_deriv_energy hN hγ hgeo hα hαγ
  have hW : energyHessian hN hγ ⟨_, mem_pathTangent_congr hN hαγ (hα.varField_mem hN)⟩
      ⟨_, mem_pathTangent_congr hN hαγ (hα.varField_mem hN)⟩ = energyHessian hN hγ Y Y := by
    rw [energyHessian_apply, energyHessian_apply]
    exact congrArg _ (secondVariation_congr hN hd hd)
  rw [hW] at hdd
  exact nonneg_of_isLocalMin_of_hasDerivAt hmin
    (hα.hasDerivAt_energy hN hα.zero_mem).differentiableAt hdd

/-- **`E_**` is positive definite on the fields vanishing at the break points** (and outside
`[0, 1]`): by Cauchy–Schwarz for the semi-definite form and the perpendicularity of broken Jacobi
fields, a null vector `Y` of `E_**` there is in the null space of `E_**`, hence a Jacobi field
(Theorem 14.1) vanishing at `t₀ = 0` and `t₁`, hence zero
(`Morse.BrokenSetup.not_isConjugate_seg`). -/
theorem energyHessian_nodeZero_pos {Y : pathTangent hN (B.path y)}
    (hY : ∀ j : Fin m, (Y : ℝ → V) (B.t j.castSucc.succ) = 0)
    (hout : ∀ t ∉ Icc (0 : ℝ) 1, (Y : ℝ → V) t = 0) (hY0 : Y ≠ 0) :
    0 < energyHessian hN (B.path_mem_pathSpace hy) Y Y := by
  have hγ := B.path_mem_pathSpace hy
  set E := energyHessian hN hγ
  have hsymm := energyHessian_isSymm hN hγ
  refine lt_of_le_of_ne (B.energyHessian_nodeZero_nonneg hy hgeo hY) fun h0 => hY0 ?_
  -- `Y` is a null vector of `E_**`
  have hnull : ∀ X : pathTangent hN (B.path y), E Y X = 0 := by
    intro X
    obtain ⟨Xb, hXb, hXbx⟩ := B.exists_brokenSpace_node hy hgeo
      (fun j => (X : ℝ → V) (B.t j.castSucc.succ)) fun j => by
        have h := X.2.2.1 (B.t j.castSucc.succ) ⟨B.t_nonneg _, B.t_le_one _⟩
        rwa [show B.path y (B.t j.castSucc.succ) = y j from congrFun (B.nodeVal_path hy) j] at h
    have hZ : ∀ j : Fin m, ((X - Xb : pathTangent hN (B.path y)) : ℝ → V)
        (B.t j.castSucc.succ) = 0 := fun j => by simp [hXbx j]
    have h1 : E Y Xb = 0 := by
      rw [LinearMap.BilinForm.isSymm_def.1 hsymm]
      exact B.energyHessian_brokenSpace_nodeZero hy hgeo hXb hY
    -- Cauchy–Schwarz for the semi-definite form on the fields vanishing at the break points
    have h2 : E Y (X - Xb) = 0 := by
      set Z := X - Xb
      have hq : ∀ r : ℝ, 0 ≤ E (Y + r • Z) (Y + r • Z) := fun r =>
        B.energyHessian_nodeZero_nonneg hy hgeo fun j => by simp [hY j, hZ j]
      have hEZY : E Z Y = E Y Z := LinearMap.BilinForm.isSymm_def.1 hsymm Y Z ▸ rfl
      have hexp : ∀ r : ℝ, E (Y + r • Z) (Y + r • Z) =
          E Y Y + 2 * r * E Y Z + r ^ 2 * E Z Z := fun r => by
        simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
        rw [hEZY]; ring
      rw [← h0] at hexp
      by_contra hne
      have hZZ : 0 ≤ E Z Z := B.energyHessian_nodeZero_nonneg hy hgeo hZ
      -- choose `r` of the sign opposite to `E(Y, Z)` and small
      set b := E Y Z
      set a := E Z Z
      have := hq (-b / (a + 1))
      rw [hexp] at this
      have ha1 : 0 < a + 1 := by linarith
      have hb2 : 0 < b ^ 2 := by positivity
      have : 2 * (-b / (a + 1)) * b + (-b / (a + 1)) ^ 2 * a < 0 := by
        rw [div_pow, neg_sq]
        field_simp
        nlinarith
      linarith
    have hsplit : X = Xb + (X - Xb) := by abel
    rw [hsplit, map_add, h1, h2, add_zero]
  -- hence a Jacobi field vanishing at `t₀` and `t₁`
  have hJ := (theorem_14_1 hγ hgeo Y).1 hnull
  have hJ0 : (Y : ℝ → V) (B.t (0 : Fin (m + 1)).castSucc) = 0 := by
    rw [Fin.castSucc_zero, B.t_zero]; exact Y.2.2.2.1
  have hJ1 : (Y : ℝ → V) (B.t (0 : Fin (m + 1)).succ) = 0 := by
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm
      have : (0 : Fin 1).succ = Fin.last 1 := rfl
      rw [this, B.t_last]; exact Y.2.2.2.2
    · have := hY ⟨0, hm⟩
      exact this
  refine Subtype.ext (funext fun t => ?_)
  by_cases ht : t ∈ Icc (0 : ℝ) 1
  · by_contra hYt
    exact B.not_isConjugate_seg hy hgeo 0 ⟨⟨B.t_nonneg _, B.t_le_one _⟩,
      ⟨B.t_nonneg _, B.t_le_one _⟩, (B.t_lt_iff.2 Fin.castSucc_lt_succ).ne, _, hJ, hJ0, hJ1, t, ht,
      hYt⟩
  · exact hout t ht

/-! ### Lemma 15.4 for the subdivision of §16 -/

/-- **The splitting** `TΩ_γ = TΩ_γ(t₀, …, t_k) ⊕ T'` (Lemma 15.3 for §16), inside the fields
vanishing outside `[0, 1]`. -/
theorem isCompl_brokenSpace_nodeZero :
    IsCompl ((brokenSpace (B.isSmoothCurveIn_path hy hgeo) B.breaks 1).comap
      (fieldsUpTo hN (B.path y) 1).subtype)
      ((nodeZero B.breaks 1).comap (fieldsUpTo hN (B.path y) 1).subtype) := by
  have hc := B.isSmoothCurveIn_path hy hgeo
  constructor
  · rw [Submodule.disjoint_def]
    intro X hXA hXC
    have h := B.brokenSpace_eq_zero hy hgeo hXA fun j => hXC.2 _ (B.mem_breaks.2 ⟨j, rfl⟩)
    exact Subtype.ext h
  · rw [codisjoint_iff, eq_top_iff]
    intro X _
    obtain ⟨Y, hY, hYX⟩ := B.exists_brokenSpace_node hy hgeo
      (fun j => ((X : pathTangent hN (B.path y)) : ℝ → V) (B.t j.castSucc.succ)) fun j => by
        have h := (X : pathTangent hN (B.path y)).2.2.1 (B.t j.castSucc.succ)
          ⟨B.t_nonneg _, B.t_le_one _⟩
        rwa [show B.path y (B.t j.castSucc.succ) = y j from congrFun (B.nodeVal_path hy) j] at h
    refine Submodule.mem_sup.2 ⟨⟨Y, brokenSpace_le_fieldsUpTo hc B.breaks 1 hY⟩, hY,
      X - ⟨Y, brokenSpace_le_fieldsUpTo hc B.breaks 1 hY⟩, ⟨fun t ht => ?_, fun b hb => ?_⟩,
      by abel⟩
    · simp [X.2 t ht, hY.1 t ht]
    · obtain ⟨j, rfl⟩ := B.mem_breaks.1 hb
      simp [hYX j]

/-- **Lemma 15.4 for the subdivision of §16, the index** (Milnor p. 92): the index of `E_**` at
the geodesic `γ = B.path y` equals its index on the broken Jacobi fields
`TΩ_γ(t₀, …, t_k)`. -/
theorem formIndex_brokenSpace :
    formIndex (energyHessian hN (B.path_mem_pathSpace hy)) =
      formIndex ((energyHessian hN (B.path_mem_pathSpace hy)).restrict
        (brokenSpace (B.isSmoothCurveIn_path hy hgeo) B.breaks 1)) := by
  have hc := B.isSmoothCurveIn_path hy hgeo
  set E := energyHessian hN (B.path_mem_pathSpace hy)
  have hEq : E = energyHessian hN hc.mem_pathSpace := rfl
  have h1 : indexUpTo hN (B.path y) hc 1 = formIndex E := by rw [hEq]; exact indexUpTo_one hc
  rw [← h1, indexUpTo, ← hEq]
  rw [formIndex_eq_restrict_of_isCompl (B.isCompl_brokenSpace_nodeZero hy hgeo)
    (fun a ha c hc' => B.energyHessian_brokenSpace_nodeZero hy hgeo ha fun j =>
      hc'.2 _ (B.mem_breaks.2 ⟨j, rfl⟩))
    (fun a ha c hc' => by
      change E c a = 0
      rw [LinearMap.BilinForm.isSymm_def.1 (energyHessian_isSymm hN _)]
      exact B.energyHessian_brokenSpace_nodeZero hy hgeo ha fun j =>
        hc'.2 _ (B.mem_breaks.2 ⟨j, rfl⟩))
    (fun c hc' hc0 => B.energyHessian_nodeZero_pos hy hgeo (fun j =>
      hc'.2 _ (B.mem_breaks.2 ⟨j, rfl⟩)) hc'.1 fun h => hc0 (Subtype.ext h))]
  exact formIndex_eq_of_equiv (Submodule.comapSubtypeEquivOfLe
    (brokenSpace_le_fieldsUpTo hc B.breaks 1)) fun _ _ => rfl

/-- **Lemma 15.4 for the subdivision of §16, the nullity** (Milnor p. 92): the nullity of `E_**`
on the broken Jacobi fields `TΩ_γ(t₀, …, t_k)` is the nullity of `E_**` (Theorem 14.1: the
multiplicity of `γ(1)` as a conjugate point of `γ(0)`).  A null broken Jacobi field has no
jumps (test it against the broken Jacobi field with values `P Δ_{t_j}` at the break points), so
it is a Jacobi field vanishing at `0` and `1`; conversely such a Jacobi field is a broken Jacobi
field in the null space. -/
theorem finrank_ker_brokenSpace :
    finrank ℝ (LinearMap.ker ((energyHessian hN (B.path_mem_pathSpace hy)).restrict
      (brokenSpace (B.isSmoothCurveIn_path hy hgeo) B.breaks 1))) =
      hessNullity hN (B.path_mem_pathSpace hy) := by
  classical
  have hc := B.isSmoothCurveIn_path hy hgeo
  have hγ := B.path_mem_pathSpace hy
  set γ := B.path y
  set E := energyHessian hN hγ
  set BS := brokenSpace hc B.breaks 1
  set K := LinearMap.ker (E.restrict BS)
  rw [theorem_14_1_nullity hγ hgeo]
  have hBS : ∀ b ∈ B.breaks, b ∈ Ioo (0 : ℝ) 1 := fun b hb => B.breaks_subset hb
  -- the cut-off of a Jacobi field vanishing at `0` and `1`
  have hmemT : ∀ J ∈ conjSpace hN γ hc 0 1, (Icc 0 1).indicator J ∈ pathTangent hN γ :=
    fun J hJ => indicator_mem_pathTangent ((mem_conjSpace hc).1 hJ).1.1 le_rfl zero_le_one
      le_rfl ((mem_conjSpace hc).1 hJ).2.1 ((mem_conjSpace hc).1 hJ).2.2
  set φ : conjSpace hN γ hc 0 1 →ₗ[ℝ] pathTangent hN γ :=
    { toFun := fun J => ⟨(Icc 0 1).indicator J, hmemT J J.2⟩
      map_add' := fun J J' => Subtype.ext (funext fun t => by
        by_cases h : t ∈ Icc (0 : ℝ) 1 <;> simp [h])
      map_smul' := fun c J => Subtype.ext (funext fun t => by
        by_cases h : t ∈ Icc (0 : ℝ) 1 <;> simp [h]) }
  have hφinj : Injective φ := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro J hJ
    rw [LinearMap.mem_ker] at hJ
    have hJ0 : EqOn (J : ℝ → V) 0 (Icc 0 1) := fun t ht => by
      have := congrFun (congrArg Subtype.val hJ) t
      simpa [φ, indicator_of_mem ht] using this
    exact (Submodule.mem_bot ℝ).2 (Subtype.ext (jacobiSpace_eq_zero_of_eqOn hc
      ((mem_conjSpace hc).1 J.2).1 le_rfl zero_lt_one le_rfl hJ0))
  have hrange : LinearMap.range φ = K.map BS.subtype := by
    ext X
    constructor
    · rintro ⟨J, rfl⟩
      obtain ⟨hJs, hJ0, hJ1⟩ := (mem_conjSpace hc).1 J.2
      have hbroken : φ J ∈ BS := ⟨fun t ht => indicator_of_notMem ht _,
        fun s s' hs hss' hs' _ => ⟨(J : ℝ → V), hJs, fun t ht => by
          change (Icc 0 1).indicator (J : ℝ → V) t = (J : ℝ → V) t
          rw [indicator_of_mem (show t ∈ Icc (0 : ℝ) 1 from ⟨hs.trans ht.1, ht.2.trans hs'⟩)]⟩⟩
      refine ⟨⟨φ J, hbroken⟩, ?_, rfl⟩
      rw [SetLike.mem_coe, LinearMap.mem_ker]
      ext Y
      change E (φ J) (Y : pathTangent hN γ) = 0
      rw [B.energyHessian_brokenSpace_eq hy hgeo hbroken]
      rw [Finset.sum_eq_zero fun j _ => ?_, mul_zero]
      have hb := hBS _ (B.mem_breaks.2 ⟨j, rfl⟩)
      have hev : ((φ J : pathTangent hN γ) : ℝ → V) =ᶠ[𝓝 (B.t j.castSucc.succ)] J := by
        filter_upwards [Ioo_mem_nhds hb.1 hb.2] with t ht
        exact indicator_of_mem (Ioo_subset_Icc_self ht) _
      have hd : DifferentiableAt ℝ (J : ℝ → V) (B.t j.castSucc.succ) :=
        (hJs.1.contDiffOn.contDiffAt (Icc_mem_nhds hb.1 hb.2)).differentiableAt (by simp)
      rw [jump_congr hev, jump_eq_zero hd, map_zero, inner_zero_right]
    · rintro ⟨X, hX, rfl⟩
      rw [SetLike.mem_coe, LinearMap.mem_ker] at hX
      -- all jumps vanish: test against the broken Jacobi field with values `P Δ_{t_j} X'`
      have hjump : ∀ j : Fin m, prj hN (γ (B.t j.castSucc.succ))
          (jump ((X : pathTangent hN γ) : ℝ → V) (B.t j.castSucc.succ)) = 0 := by
        obtain ⟨Y, hY, hYv⟩ := B.exists_brokenSpace_node hy hgeo
          (fun j => prj hN (γ (B.t j.castSucc.succ))
            (jump ((X : pathTangent hN γ) : ℝ → V) (B.t j.castSucc.succ))) fun j => by
            rw [show γ (B.t j.castSucc.succ) = y j from congrFun (B.nodeVal_path hy) j]
            exact prj_prj hN _ _
        have h1 : (E.restrict BS) X ⟨Y, hY⟩ = 0 := by rw [hX]; rfl
        change E (X : pathTangent hN γ) Y = 0 at h1
        rw [B.energyHessian_brokenSpace_eq hy hgeo X.2] at h1
        have h2 : ∑ j : Fin m, ‖prj hN (γ (B.t j.castSucc.succ))
            (jump ((X : pathTangent hN γ) : ℝ → V) (B.t j.castSucc.succ))‖ ^ 2 = 0 := by
          have : ∑ j : Fin m, ⟪(Y : ℝ → V) (B.t j.castSucc.succ), prj hN (γ (B.t j.castSucc.succ))
              (jump ((X : pathTangent hN γ) : ℝ → V) (B.t j.castSucc.succ))⟫ = 0 := by linarith
          rw [← this]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [hYv j, real_inner_self_eq_norm_sq]
        intro j
        have := (Finset.sum_eq_zero_iff_of_nonneg fun j _ => by positivity).1 h2 j
          (Finset.mem_univ j)
        rwa [pow_eq_zero_iff two_ne_zero, norm_eq_zero] at this
      obtain ⟨J, hJ, hXJ⟩ := eq_jacobi_of_jumps_zero hc B.breaks 1 le_rfl hBS _ X.2.2
        (fun b hb => by obtain ⟨j, rfl⟩ := B.mem_breaks.1 hb; exact hjump j) one_pos
      have hJ0 : J 0 = 0 := by
        rw [← hXJ ⟨le_rfl, zero_le_one⟩]; exact (X : pathTangent hN γ).2.2.2.1
      have hJ1 : J 1 = 0 := by
        rw [← hXJ ⟨zero_le_one, le_rfl⟩]; exact (X : pathTangent hN γ).2.2.2.2
      refine ⟨⟨J, (mem_conjSpace hc).2 ⟨hJ, hJ0, hJ1⟩⟩, Subtype.ext (funext fun t => ?_)⟩
      change (Icc 0 1).indicator J t = ((X : pathTangent hN γ) : ℝ → V) t
      by_cases ht : t ∈ Icc (0 : ℝ) 1
      · rw [indicator_of_mem ht, hXJ ht]
      · rw [indicator_of_notMem ht, X.2.1 t ht]
  have h1 := LinearMap.finrank_range_of_inj hφinj
  rw [hrange, ← (Submodule.equivMapOfInjective _ (Submodule.injective_subtype _) K).finrank_eq]
    at h1
  rw [h1]
  rfl

end Unbroken

end BrokenSetup

end Morse
