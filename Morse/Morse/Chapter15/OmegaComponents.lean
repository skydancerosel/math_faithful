import Morse.Chapter15.FiniteStageTwo
import Morse.Chapter15.CliffordModules

/-!
Milnor, *Morse Theory*, §24, p. 147 (case `k ≡ 2 (mod 4)`: "the paths from `J` to `−J` fall into
the components `Ω^{(c)}`"); Exposition/Chapter15.md, §6, "The components".

# Every path from `J_k` to `−J_k` lies in exactly one `Ω^{(c)}` (`k = 2, 6`)

## Milnor's text, paraphrased

(p. 147) For `k ≡ 2 (mod 4)` and `f(J') = det_ℂ(J⁻¹J')`, a path `ω` from `J` to `−J` gives the
loop `f ∘ ω` in `S¹`; its normalized degree `c` is constant on path components, and `Ω^{(c)}` is
the union of the components of degree `c`.

## What is formalized

* `Morse.exists_isAngleLift`: every loop `t ↦ F(ω t)` in the unit circle with `F(ω 0) = 1` has a
  continuous angle (path lifting for the covering `exp : ℝ → S¹`, Mathlib's
  `Circle.isCoveringMap_exp`); `Morse.IsAngleLift.pow`: `n·θ` is the angle of `Fⁿ`;
  `Morse.disjoint_windSet`: the angle at the end is unique.
* `Morse.pdet Q A = det(AQ + 1 − Q)` (the determinant of `A` on the range of the projection `Q`)
  and **`Morse.pdet_split`**: if a complex structure `σ` commutes with `Q` and `A`, and a complex
  structure `s` commuting with `Q` and `A` anticommutes with `σ`, then
  `pdet Q A = pdet (Q P_σ) A ²` (`s` exchanges the `±√−1`-eigenspaces of `σ`).
* **`Morse.omegaF_eq_pow_four`** (`k = 6`): on `Ω_6(n)`,
  `f = det_ℂ(J_6ᵀX) = pdet(P_i P_{J₁J₂} P_{J₃J₄}, J_6ᵀX)⁴` (two splittings, by `J₁J₂` exchanged by
  `J₁`, and by `J₃J₄` exchanged by `J₃`; `J_6ᵀX` commutes with `J₁, …, J₅`).
* **`Morse.exists_mem_omegaComp_two`, `Morse.exists_mem_omegaComp_six`**: every path from `J_k`
  to `−J_k` in (the stratum of) `Ω_k(n)` lies in `Ω^{(c)}` (angle `π m_{k+1} c/2`) for some
  `c ∈ ℤ`, `k = 2, 6`; with `Morse.disjoint_omegaComp`, for exactly one `c`.
  For `k = 2`: `f(−J_2) = det_ℂ(−1) = e^{π√−1 n/2} = 1` as `4 ∣ n`.  For `k = 6`: the angle of
  `f` is `4φ`, `φ` the angle of the fourth root, and `e^{√−1 φ(1)} = pdet(Q, −1) = ±1`.
* **`Morse.theorem_24_5_pi0_two_six`**: the `π₀` part of Theorem 24.5 at the finite stage,
  `k = 2, 6`: for `(n/m_{k+1} − |c|)/4 ≥ 2`, every path in `Ω^{(c)}` is joined to `φ_r(J')` for
  some `J' ∈ Ω_{k+1}(n)`, and `J', J'' ∈ Ω_{k+1}(n)` with `φ_r(J') ∈ Ω^{(c)}` are joined in
  `Ω_{k+1}(n)` iff `φ_r(J')` and `φ_r(J'')` are joined in `Ω(Ω_k(n); J_k, −J_k)`.

## What Milnor leaves implicit

* That `c` is an integer: the degree of `f ∘ ω` is a priori only in `ℤ` after dividing by
  `2π`; that it is a multiple of `m_{k+1}/4` (`= 1` for `k = 2`, `= 2` for `k = 6`) uses, for
  `k = 6`, that `det_ℂ` on the commutant of `J₁, …, J₅` is a fourth power (the commutant is
  `M_{n/8}(ℂ)` acting on `ℂ⁴ ⊗ ℂ^{n/8}`), and for `k = 2` that `4 ∣ n`.
* At a finite stage, the components `Ω^{(c)}` with `|c| > ν − 8` are not controlled (Milnor's
  isomorphism is for the limit `n → ∞`, where every `c` is eventually in range).
-/

open Matrix Set Function Topology
open scoped unitInterval Morse.MatrixInner

noncomputable section

namespace Morse

/-! ### Angles of loops -/

section Angle

variable {V : Type*}

/-- **Every loop in the circle starting at `1` has a continuous angle** (path lifting for
`exp : ℝ → S¹`). -/
theorem exists_isAngleLift {F : V → ℂ} {ω : ℝ → V} (hF : Continuous fun t : I => F (ω t))
    (h1 : ∀ t : I, ‖F (ω t)‖ = 1) (h0 : F (ω ((0 : I) : ℝ)) = 1) :
    ∃ θ : C(I, ℝ), IsAngleLift F ω θ := by
  let γ : C(I, Circle) := ⟨fun t => ⟨F (ω t), mem_sphere_zero_iff_norm.2 (h1 t)⟩,
    hF.subtype_mk _⟩
  have hγ0 : γ 0 = Circle.exp 0 := by
    rw [Circle.exp_zero]
    exact Subtype.ext h0
  obtain ⟨Γ, hΓ, hΓ0⟩ := Circle.isCoveringMap_exp.exists_path_lifts γ 0 hγ0
  refine ⟨Γ, hΓ0, fun t => ?_⟩
  have := congrArg (fun z : Circle => (z : ℂ)) (congrFun hΓ t)
  simp only [Function.comp_apply, Circle.coe_exp] at this
  exact this.symm

/-- **The angle of `Fⁿ`** is `n` times the angle of `F`. -/
theorem IsAngleLift.pow {F G : V → ℂ} {ω : ℝ → V} {θ : C(I, ℝ)} (hθ : IsAngleLift G ω θ)
    (n : ℕ) (hF : ∀ t : I, F (ω t) = G (ω t) ^ n) :
    IsAngleLift F ω ⟨fun t => n * θ t, by fun_prop⟩ := by
  refine ⟨by simp [hθ.1], fun t => ?_⟩
  change F (ω t) = Complex.exp (((n * θ t : ℝ) : ℂ) * Complex.I)
  rw [hF, hθ.2 t, ← Complex.exp_nat_mul]
  push_cast
  ring_nf

variable [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  {N : Set V} {p q : V}

/-- **The sets `Ω^{(c)}` are disjoint**: the angle at the end is unique. -/
theorem disjoint_windSet {F : V → ℂ} {w w' : ℝ} (h : w ≠ w') :
    Disjoint (windSet N p q F w) (windSet N p q F w') := by
  rw [Set.disjoint_left]
  rintro ω ⟨θ, hθ, rfl⟩ ⟨θ', hθ', hw⟩
  exact h ((congrArg (fun θ : C(I, ℝ) => θ 1) (hθ.unique hθ')).trans hw)

end Angle

/-! ### Determinants on the range of a projection -/

section PDet

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `det(AQ + 1 − Q)`: for a projection `Q` commuting with `A`, the determinant of `A` on the
range of `Q`. -/
def pdet (Q A : Matrix ι ι ℂ) : ℂ := (A * Q + (1 - Q)).det

theorem continuous_pdet (Q : Matrix ι ι ℂ) : Continuous (pdet Q) :=
  ((continuous_id.matrix_mul continuous_const).add continuous_const).matrix_det

theorem pdet_one (Q : Matrix ι ι ℂ) : pdet Q 1 = 1 := by
  simp [pdet]

theorem pdet_neg_one_sq {Q : Matrix ι ι ℂ} (hQ : Q * Q = Q) : pdet Q (-1) ^ 2 = 1 := by
  rw [pdet, sq, ← det_mul]
  have : (-1 * Q + (1 - Q)) * (-1 * Q + (1 - Q)) = 1 := by
    have e : (-1 * Q + (1 - Q)) * (-1 * Q + (1 - Q)) = 1 - 4 • Q + 4 • (Q * Q) := by noncomm_ring
    rw [e, hQ]
    abel
  rw [this, det_one]

theorem cdet_eq_pdet (ii M : Matrix ι ι ℝ) : cdet ii M = pdet (projP ii) (cplx M) := by
  rw [cdet, pdet, ← projP_add_projM (ii := ii), add_sub_cancel_left]

theorem commute_projP {a b : Matrix ι ι ℝ} (h : Commute a b) : Commute (projP a) (cplx b) :=
  (cplx_comm_projP (ii := a) h.symm.eq).symm

theorem commute_projP_projP {a b : Matrix ι ι ℝ} (h : Commute a b) :
    Commute (projP a) (projP b) := by
  have h' := commute_projP h
  unfold projP
  exact ((Commute.one_right _).sub_right (h'.smul_right _)).smul_right _

/-- **Splitting off a swapped eigenspace**: if the complex structure `g` commutes with `Q` and
`A`, and the complex structure `s` commutes with `Q` and `A` and anticommutes with `g`, then
`det(A on range Q) = det(A on range Q P_g)²`. -/
theorem pdet_split {Q A : Matrix ι ι ℂ} {g s : Matrix ι ι ℝ} (hg : g * g = -1) (hs : s * s = -1)
    (hsg : s * g = -(g * s)) (hQg : Commute Q (cplx g)) (hQs : Commute Q (cplx s))
    (hAQ : Commute A Q) (hAg : Commute A (cplx g)) (hAs : Commute A (cplx s)) :
    pdet Q A = pdet (Q * projP g) A ^ 2 := by
  set B := A - 1 with hB
  set Q₁ := Q * projP g with hQ₁
  set Q₂ := Q * projM g with hQ₂
  have e : ∀ R : Matrix ι ι ℂ, A * R + (1 - R) = 1 + B * R := fun R => by rw [hB]; noncomm_ring
  have hQP : Commute Q (projP g) := by
    unfold projP; exact ((Commute.one_right _).sub_right (hQg.smul_right _)).smul_right _
  have hQM : Commute Q (projM g) := by
    unfold projM; exact ((Commute.one_right _).add_right (hQg.smul_right _)).smul_right _
  have hBP : Commute B (projP g) := by
    unfold projP
    exact (((Commute.one_right _).sub_right (hAg.smul_right _)).smul_right _).sub_left
      ((Commute.one_left _).sub_right ((Commute.one_left _).smul_right _) |>.smul_right _)
  have hBM : Commute B (projM g) := by
    unfold projM
    exact (((Commute.one_right _).add_right (hAg.smul_right _)).smul_right _).sub_left
      ((Commute.one_left _).add_right ((Commute.one_left _).smul_right _) |>.smul_right _)
  have hBQ : Commute B Q := hAQ.sub_left (Commute.one_left _)
  have h12 : Q₁ * Q₂ = 0 := by
    rw [hQ₁, hQ₂, Matrix.mul_assoc, ← Matrix.mul_assoc (projP g), ← hQP.eq, Matrix.mul_assoc Q,
      projP_mul_projM hg, Matrix.mul_zero, Matrix.mul_zero]
  have hsum : Q₁ + Q₂ = Q := by rw [hQ₁, hQ₂, ← Matrix.mul_add, projP_add_projM, Matrix.mul_one]
  have hB1 : Commute B Q₁ := hBQ.mul_right hBP
  -- the product
  have hprod : (1 + B * Q₁) * (1 + B * Q₂) = 1 + B * Q := by
    have : (1 + B * Q₁) * (1 + B * Q₂) = 1 + B * (Q₁ + Q₂) + B * (Q₁ * B) * Q₂ := by
      noncomm_ring
    have h3 : B * (Q₁ * B) * Q₂ = 0 := by
      rw [← hB1.eq, ← Matrix.mul_assoc B B Q₁, Matrix.mul_assoc (B * B) Q₁ Q₂, h12,
        Matrix.mul_zero]
    rw [this, h3, add_zero, hsum]
  -- the swap
  set S := cplx s with hS
  have hSS : S * S = -1 := by rw [hS, ← map_mul, hs, map_neg, map_one]
  have hSg : S * cplx g = -(cplx g * S) := by rw [hS, ← map_mul, hsg, map_neg, map_mul]
  have hSP : S * projP g = projM g * S := by
    unfold projP projM
    rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sub, Matrix.add_mul, Matrix.mul_one,
      Matrix.one_mul, Matrix.mul_smul, Matrix.smul_mul, hSg, smul_neg, sub_neg_eq_add]
  have hSconj : S * (1 + B * Q₁) = (1 + B * Q₂) * S := by
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul, hQ₁, hQ₂,
      ← Matrix.mul_assoc, ← (hAs.sub_left (Commute.one_left _)).eq, Matrix.mul_assoc,
      ← Matrix.mul_assoc S, ← hQs.eq, Matrix.mul_assoc Q, hSP]
    simp only [Matrix.mul_assoc]
    rfl
  have hdetS : S.det ≠ 0 := by
    intro h0
    have := congrArg det hSS
    rw [det_mul, h0, zero_mul, det_neg, det_one, mul_one] at this
    exact (pow_ne_zero _ (by norm_num : (-1 : ℂ) ≠ 0)) this.symm
  have hdet : (1 + B * Q₁).det = (1 + B * Q₂).det := by
    have := congrArg det hSconj
    rw [det_mul, det_mul, mul_comm (det (1 + B * Q₂))] at this
    exact mul_left_cancel₀ hdetS this
  rw [pdet, pdet, e, e, ← hprod, det_mul, ← hdet, sq]

end PDet

/-! ### Every path lies in some `Ω^{(c)}` -/

section Omega

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {J : ℕ → Matrix ι ι ℝ}

/-- `pᵀX` commutes with `J_1, …, J_{k−1}` for `p, X ∈ Ω_k(n)`. -/
theorem commute_transpose_mul_of_mem_omega {k : ℕ} (hk : k ≠ 0) (hJ : IsAnticommFamily J k)
    {p X : Matrix ι ι ℝ} (hp : p ∈ Omega J k) (hX : X ∈ Omega J k) {α : ℕ} (h1 : 1 ≤ α)
    (h2 : α < k) : Commute (pᵀ * X) (J α) := by
  have hpα := anti_of_mem_omega hk hp α h1 h2
  have hXα := anti_of_mem_omega hk hX α h1 h2
  have ht : (J α)ᵀ = -J α := (hJ.cs α h1 h2.le).transpose
  have hpt : pᵀ * J α = -(J α * pᵀ) := by
    have := congrArg transpose hpα
    rw [transpose_mul, transpose_neg, transpose_mul, ht, Matrix.mul_neg, Matrix.neg_mul,
      neg_neg] at this
    rw [← this, neg_neg]
  change pᵀ * X * J α = J α * (pᵀ * X)
  rw [Matrix.mul_assoc, show X * J α = -(J α * X) by rw [hXα, neg_neg], Matrix.mul_neg,
    ← Matrix.mul_assoc, hpt, Matrix.neg_mul, neg_neg, Matrix.mul_assoc]

variable (J) in
/-- The projection `P_i P_{J₁J₂} P_{J₃J₄}` (`i = J₁⋯J₅`). -/
def q6 : Matrix ι ι ℂ := projP (iWordM J 6) * projP (J 1 * J 2) * projP (J 3 * J 4)

section Six

variable (hJ : IsAnticommFamily J 6)
include hJ

theorem isCentralI_six' : IsCentralI J 6 (iWordM J 6) := by
  rw [iWordM_six]; exact isCentralI_six (hJ.mono (by norm_num))

/-- The commutation relations among `i = J₁⋯J₅`, `J₁J₂`, `J₃J₄`, `J₁`, `J₃`. -/
theorem six_relations :
    J 1 * J 2 * (J 1 * J 2) = -1 ∧ J 3 * J 4 * (J 3 * J 4) = -1 ∧ J 1 * J 1 = -1 ∧
      J 3 * J 3 = -1 ∧ J 1 * (J 1 * J 2) = -(J 1 * J 2 * J 1) ∧
      J 3 * (J 3 * J 4) = -(J 3 * J 4 * J 3) ∧ Commute (iWordM J 6) (J 1 * J 2) ∧
      Commute (iWordM J 6) (J 3 * J 4) ∧ Commute (iWordM J 6) (J 1) ∧
      Commute (iWordM J 6) (J 3) ∧ Commute (J 1 * J 2) (J 3 * J 4) ∧
      Commute (J 1 * J 2) (J 3) := by
  have h := hJ.isClifford
  rw [iWordM_six]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals try change _ * _ = _ * _
  all_goals clifford_simp h

theorem isIdempotentElem_q6 : IsIdempotentElem (q6 J) := by
  obtain ⟨-, -, -, -, -, -, c1, c2, -, -, c3, -⟩ := six_relations hJ
  have hii := isCentralI_six' hJ
  obtain ⟨g1, g2, -⟩ := six_relations hJ
  have i1 : IsIdempotentElem (projP (iWordM J 6)) := projP_mul_projP hii.sq
  have i2 : IsIdempotentElem (projP (J 1 * J 2)) := projP_mul_projP g1
  have i3 : IsIdempotentElem (projP (J 3 * J 4)) := projP_mul_projP g2
  exact (i1.mul_of_commute (commute_projP_projP c1) i2).mul_of_commute
    ((commute_projP_projP c2).mul_left (commute_projP_projP c3)) i3

/-- **On `Ω_6(n)`, `f = det_ℂ(J_6ᵀX)` is a fourth power**: `f(X) = pdet(Q, J_6ᵀX)⁴`,
`Q = P_i P_{J₁J₂} P_{J₃J₄}`. -/
theorem omegaF_eq_pow_four {X : Matrix ι ι ℝ} (hX : X ∈ Omega J 6) :
    omegaF (iWordM J 6) (basePt J 6) X = pdet (q6 J) (cplx ((basePt J 6)ᵀ * X)) ^ 4 := by
  obtain ⟨g1, g2, s1, s3, a1, a2, c1, c2, c4, c5, c3, c6⟩ := six_relations hJ
  have hp := basePt_mem_omega hJ
  have hii := isCentralI_six' hJ
  set Y := (basePt J 6)ᵀ * X with hYdef
  have hY : ∀ α, 1 ≤ α → α < 6 → Commute Y (J α) := fun α h1 h2 =>
    commute_transpose_mul_of_mem_omega (by norm_num) hJ hp hX h1 h2
  have hYi : Commute Y (iWordM J 6) := hii.comm_transpose_mul (by norm_num) hp hX
  have hY12 : Commute Y (J 1 * J 2) :=
    (hY 1 le_rfl (by norm_num)).mul_right (hY 2 (by norm_num) (by norm_num))
  have hY34 : Commute Y (J 3 * J 4) :=
    (hY 3 (by norm_num) (by norm_num)).mul_right (hY 4 (by norm_num) (by norm_num))
  have hA : ∀ {b : Matrix ι ι ℝ}, Commute Y b → Commute (cplx Y) (cplx b) := fun h => h.map cplx
  have hAP : ∀ {b : Matrix ι ι ℝ}, Commute Y b → Commute (cplx Y) (projP b) := fun h =>
    (commute_projP h.symm).symm
  have e1 := pdet_split (Q := projP (iWordM J 6)) (A := cplx Y) g1 s1 a1 (commute_projP c1)
    (commute_projP c4) (hAP hYi) (hA hY12) (hA (hY 1 le_rfl (by norm_num)))
  have e2 := pdet_split (Q := projP (iWordM J 6) * projP (J 1 * J 2)) (A := cplx Y) g2 s3 a2
    ((commute_projP c2).mul_left (commute_projP c3))
    ((commute_projP c5).mul_left (commute_projP c6)) ((hAP hYi).mul_right (hAP hY12))
    (hA hY34) (hA (hY 3 (by norm_num) (by norm_num)))
  rw [omegaF, cdet_eq_pdet, e1, e2, q6, ← pow_mul]

/-- **Every path from `J_6` to `−J_6` lies in some `Ω^{(c)}`**, `c ∈ ℤ` (angle `4πc`). -/
theorem exists_mem_omegaComp_six
    (ω : PathSp (omegaStratum J 6 (basePt J 6)) (basePt J 6) (-basePt J 6)) :
    ∃ c : ℤ, ω ∈ omegaComp J 6 (iWordM J 6) (Real.pi * milnorM (6 + 1) * c / 2) := by
  have hp := basePt_mem_omega hJ
  have hii := isCentralI_six' hJ
  have hpo : (basePt J 6)ᵀ * (basePt J 6) = 1 := by
    have := omega_orth hp; rwa [conjTranspose_real] at this
  let G : Matrix ι ι ℝ → ℂ := fun X => pdet (q6 J) (cplx ((basePt J 6)ᵀ * X))
  have hGc : Continuous G :=
    (continuous_pdet _).comp (continuous_cplx.comp (continuous_const.mul continuous_id))
  have hmem : ∀ t : I, ω t ∈ Omega J 6 := fun t => omegaStratum_subset _ (ω.mem.2.1 t t.2)
  have hF4 : ∀ t : I, omegaF (iWordM J 6) (basePt J 6) (ω t) = G (ω t) ^ 4 := fun t =>
    omegaF_eq_pow_four hJ (hmem t)
  have hG1 : ∀ t : I, ‖G (ω t)‖ = 1 := fun t => by
    have h1 := norm_omegaF hii (by norm_num) hp (hmem t)
    rw [hF4, norm_pow] at h1
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by norm_num)).1 h1
  have hG0 : G (ω ((0 : I) : ℝ)) = 1 := by
    change pdet (q6 J) (cplx ((basePt J 6)ᵀ * ω ((0 : I) : ℝ))) = 1
    rw [show ω ((0 : I) : ℝ) = (basePt J 6) from ω.mem.2.2.1, hpo, map_one, pdet_one]
  obtain ⟨φ, hφ⟩ := exists_isAngleLift (continuous_comp_path hGc ω) hG1 hG0
  have hθ := hφ.pow 4 hF4
  have hend : Complex.exp (φ 1 * Complex.I) = pdet (q6 J) (-1) := by
    rw [← hφ.2 1]
    change pdet (q6 J) (cplx ((basePt J 6)ᵀ * ω ((1 : I) : ℝ))) = _
    rw [show ω ((1 : I) : ℝ) = -(basePt J 6) from ω.mem.2.2.2, Matrix.mul_neg, hpo, map_neg,
      map_one]
  have hsq : Complex.exp (φ 1 * Complex.I) ^ 2 = 1 := by
    rw [hend]; exact pdet_neg_one_sq (isIdempotentElem_q6 hJ)
  rw [← Complex.exp_nat_mul] at hsq
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.1 hsq
  have hφ1 : φ 1 = n * Real.pi := by
    have h2 : ((2 * φ 1 : ℝ) : ℂ) * Complex.I = ((n * (2 * Real.pi) : ℝ) : ℂ) * Complex.I := by
      push_cast; linear_combination hn
    have := Complex.ofReal_injective (mul_right_cancel₀ Complex.I_ne_zero h2)
    linarith
  refine ⟨n, _, hθ, ?_⟩
  change (4 : ℕ) * φ 1 = Real.pi * milnorM (6 + 1) * n / 2
  rw [hφ1, show milnorM (6 + 1) = 8 from rfl]
  push_cast
  ring

end Six

/-- **Every path from `J_2` to `−J_2` lies in some `Ω^{(c)}`**, `c ∈ ℤ` (angle `2πc`):
`f(−J_2) = det_ℂ(−1) = e^{π√−1 n/2} = 1` since `4 ∣ n`. -/
theorem exists_mem_omegaComp_two (hJ : IsAnticommFamily J 2)
    (ω : PathSp (omegaStratum J 2 (basePt J 2)) (basePt J 2) (-basePt J 2)) :
    ∃ c : ℤ, ω ∈ omegaComp J 2 (iWordM J 2) (Real.pi * milnorM (2 + 1) * c / 2) := by
  have hp := basePt_mem_omega hJ
  have hii : IsCentralI J 2 (iWordM J 2) := by
    rw [iWordM_two]; exact isCentralI_two (hJ.mono (by norm_num))
  have hpo : (basePt J 2)ᵀ * (basePt J 2) = 1 := by
    have := omega_orth hp; rwa [conjTranspose_real] at this
  have hmem : ∀ t : I, ω t ∈ Omega J 2 := fun t => omegaStratum_subset _ (ω.mem.2.1 t t.2)
  have h0 : omegaF (iWordM J 2) (basePt J 2) (ω ((0 : I) : ℝ)) = 1 := by
    rw [show ω ((0 : I) : ℝ) = (basePt J 2) from ω.mem.2.2.1]; exact omegaF_self hp
  obtain ⟨θ, hθ⟩ := exists_isAngleLift
    (continuous_comp_path (continuous_omegaF (iWordM J 2) (basePt J 2)) ω)
    (fun t => norm_omegaF hii (by norm_num) hp (hmem t)) h0
  -- `f(−J_2) = 1`
  have hneg : cdet (iWordM J 2) (-1) = 1 := by
    obtain ⟨q, hq⟩ := milnorM_dvd_card (k := 2) (by norm_num) hJ
    have htr : trace (iWordM J 2) = 0 :=
      trace_eq_zero_of_skew_real (by rw [conjTranspose_real]; exact hii.skew)
    rw [← exp_pi_smul hii.sq, cdet_exp hii.sq rfl htr, hii.sq, trace_neg, trace_one, hq,
      show milnorM 2 = 4 from rfl]
    refine Complex.exp_eq_one_iff.2 ⟨q, ?_⟩
    push_cast
    ring
  have hend : Complex.exp (θ 1 * Complex.I) = 1 := by
    rw [← hθ.2 1, show ω ((1 : I) : ℝ) = -(basePt J 2) from ω.mem.2.2.2, omegaF, Matrix.mul_neg,
      hpo, hneg]
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.1 hend
  have hθ1 : θ 1 = n * (2 * Real.pi) := by
    have h2 : ((θ 1 : ℝ) : ℂ) * Complex.I = ((n * (2 * Real.pi) : ℝ) : ℂ) * Complex.I := by
      push_cast; linear_combination hn
    exact Complex.ofReal_injective (mul_right_cancel₀ Complex.I_ne_zero h2)
  refine ⟨n, θ, hθ, ?_⟩
  rw [hθ1, show milnorM (2 + 1) = 4 from rfl]
  push_cast
  ring

/-- **The `Ω^{(c)}` are disjoint.** -/
theorem disjoint_omegaComp {k : ℕ} {ii : Matrix ι ι ℝ} {w w' : ℝ} (h : w ≠ w') :
    Disjoint (omegaComp J k ii w) (omegaComp J k ii w') :=
  disjoint_windSet h

/-- **Every path from `J_k` to `−J_k` lies in exactly one `Ω^{(c)}`**, `k = 2, 6`. -/
theorem existsUnique_mem_omegaComp {k : ℕ} (hk : k = 2 ∨ k = 6) (hJ : IsAnticommFamily J k)
    (ω : PathSp (omegaStratum J k (basePt J k)) (basePt J k) (-basePt J k)) :
    ∃! c : ℤ, ω ∈ omegaComp J k (iWordM J k) (Real.pi * milnorM (k + 1) * c / 2) := by
  have hex : ∃ c : ℤ, ω ∈ omegaComp J k (iWordM J k) (Real.pi * milnorM (k + 1) * c / 2) := by
    rcases hk with rfl | rfl
    · exact exists_mem_omegaComp_two hJ ω
    · exact exists_mem_omegaComp_six hJ ω
  obtain ⟨c, hc⟩ := hex
  refine ⟨c, hc, fun c' hc' => ?_⟩
  by_contra hne
  have hw : Real.pi * milnorM (k + 1) * (c' : ℝ) / 2 ≠ Real.pi * milnorM (k + 1) * c / 2 := by
    intro h
    have hm : (0 : ℝ) < milnorM (k + 1) := by exact_mod_cast milnorM_pos (k + 1)
    have hpos : 0 < Real.pi * milnorM (k + 1) / 2 := by positivity
    have : (c' : ℝ) = c := mul_left_cancel₀ hpos.ne'
      (by linear_combination h : Real.pi * milnorM (k + 1) / 2 * (c' : ℝ) =
        Real.pi * milnorM (k + 1) / 2 * c)
    exact hne (by exact_mod_cast this)
  exact Set.disjoint_left.1 (disjoint_omegaComp hw) hc' hc

end Omega

/-- A homotopy equivalence `e : X → Y` joins `e(e⁻¹ y)` to `y` and `e⁻¹(e x)` to `x`. -/
theorem joined_homotopyEquiv {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : ContinuousMap.HomotopyEquiv X Y) (x : X) (y : Y) :
    Joined (e.toFun (e.invFun y)) y ∧ Joined (e.invFun (e.toFun x)) x := by
  obtain ⟨F⟩ := e.right_inv
  obtain ⟨G⟩ := e.left_inv
  exact ⟨⟨F.evalAt y⟩, ⟨G.evalAt x⟩⟩

/-! ### `π₀` of Theorem 24.5, `k = 2, 6`, at a finite stage -/

section Pi0

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {J : ℕ → Matrix ι ι ℝ} {k : ℕ}
  (hJ : IsAnticommFamily J (k + 1))
include hJ

/-- **The `π₀` part of Theorem 24.5 at the finite stage, `k = 2, 6`** (Milnor pp. 147–148):
for `(n/m_{k+1} − |c|)/4 ≥ 2`, (i) every path in `Ω^{(c)}` is joined, in
`Ω(Ω_k(n); J_k, −J_k)`, to `φ_r(J')` for some `J' ∈ Ω_{k+1}(n)`; (ii) for `φ_r(J') ∈ Ω^{(c)}`,
`J'` and `J''` are joined in `Ω_{k+1}(n)` iff `φ_r(J')` and `φ_r(J'')` are joined.  With
`Morse.exists_mem_omegaComp_two`, `Morse.exists_mem_omegaComp_six` and
`Morse.disjoint_omegaComp` (every path lies in exactly one `Ω^{(c)}`), `φ_r` thus identifies
`π₀Ω_{k+1}(n)^{(c)}` with `π₀Ω^{(c)}` for every `c` in this range. -/
theorem theorem_24_5_pi0_two_six (hk : k = 2 ∨ k = 6) (c : ℤ)
    (hc : 2 ≤ (Fintype.card ι / milnorM (k + 1) - c.natAbs) / 4) :
    (∀ ω ∈ omegaComp J k (iWordM J k) (Real.pi * milnorM (k + 1) * c / 2),
      ∃ J' : Omega J (k + 1), Joined (omegaPhi hJ J' : PathSp _ _ _) ω) ∧
    ∀ J' J'' : Omega J (k + 1), (omegaPhi hJ J' : PathSp _ _ _) ∈
      omegaComp J k (iWordM J k) (Real.pi * milnorM (k + 1) * c / 2) →
      (Joined J' J'' ↔ Joined (omegaPhi hJ J' : PathSp _ _ _) (omegaPhi hJ J'')) := by
  have hk0 : k ≠ 0 := by omega
  have hii := isCentralI_iWordM hJ hk
  set Ω' := omegaComp J k (iWordM J k) (Real.pi * milnorM (k + 1) * c / 2) with hΩ'_def
  have hΩ' : IsClopen Ω' := isClopen_omegaComp (hJ.mono k.le_succ) hk0 hii _
  have hpush0 := pushesInto_cube_clopen
    (isSliceSubmanifold_omegaStratum (hJ.mono k.le_succ) (basePt J k))
    (self_mem_omegaStratum (basePt_mem hJ)) (neg_basePt_mem hJ)
    (fun r => isCompact_closedRiemBall_of_isClosed
      (isSliceSubmanifold_omegaStratum (hJ.mono k.le_succ) (basePt J k))
      (isClosed_omegaStratum (hJ.mono k.le_succ) _) _ r)
    hΩ' (omega_hidx_two hJ hk0 (by omega) (by omega) hii c)
    (exists_retraction_minPaths_omega (hJ.mono k.le_succ) (basePt_mem hJ) (minVel_base hJ))
    (K := Fin 0) (by simpa using hc)
  have hpush1 := pushesInto_cyl_clopen
    (isSliceSubmanifold_omegaStratum (hJ.mono k.le_succ) (basePt J k))
    (self_mem_omegaStratum (basePt_mem hJ)) (neg_basePt_mem hJ)
    (fun r => isCompact_closedRiemBall_of_isClosed
      (isSliceSubmanifold_omegaStratum (hJ.mono k.le_succ) (basePt J k))
      (isClosed_omegaStratum (hJ.mono k.le_succ) _) _ r)
    hΩ' (omega_hidx_two hJ hk0 (by omega) (by omega) hii c)
    (exists_retraction_minPaths_omega (hJ.mono k.le_succ) (basePt_mem hJ) (minVel_base hJ))
    (K := Fin 0) (by simpa using hc)
  obtain ⟨e, he⟩ := isHomotopyEquiv_omegaPhi_minPaths hJ
  have hφ : ∀ x, (omegaPhi hJ x : PathSp _ _ _) = ((e.toFun x : minPaths _ _ _) : PathSp _ _ _) :=
    fun x => (congrFun (congrArg DFunLike.coe he) x).symm
  let z : I^(Fin 0) := fun i => i.elim0
  refine ⟨fun ω hω => ?_, fun J' J'' hJ' => ⟨fun h => h.map (omegaPhi hJ).continuous, ?_⟩⟩
  · -- (i) push `ω` into the minimal geodesics
    obtain ⟨h', hh', ⟨H⟩⟩ := hpush0 (ContinuousMap.const _ ω) fun _ => hω
    let γ : minPaths _ _ _ := ⟨h' z, (hh' z).1⟩
    refine ⟨e.invFun γ, ?_⟩
    rw [hφ]
    exact ((joined_homotopyEquiv e (e.invFun γ) γ).1.map continuous_subtype_val).trans
      ⟨(H.evalAt z).symm⟩
  · -- (ii) push a path between `φ J'` and `φ J''` into the minimal geodesics
    rintro ⟨P⟩
    have hPΩ : ∀ t, P t ∈ Ω' := fun t =>
      (isConnected_range P.continuous).isPreconnected.subset_isClopen hΩ'
        ⟨_, ⟨0, rfl⟩, by rw [P.source]; exact hJ'⟩ ⟨t, rfl⟩
    let h : C(I × I^(Fin 0), PathSp _ _ _) := ⟨fun q => P q.1, by fun_prop⟩
    obtain ⟨h', hh', ⟨H⟩⟩ := hpush1 h fun q => hPΩ q.1
    have hmin : ∀ x : Omega J (k + 1), (omegaPhi hJ x : PathSp _ _ _) ∈ minPaths _ _ _ :=
      fun x => by rw [hφ]; exact (e.toFun x).2
    have h0 : h' (0, z) = omegaPhi hJ J' := by
      rw [← H.fst_eq_snd (show (0, z) ∈ h ⁻¹' (minPaths _ _ _ ∩ Ω') from
        ⟨by simp [h, hmin], by simp [h, hJ']⟩)]
      simp [h]
    have h1 : h' (1, z) = omegaPhi hJ J'' := by
      rw [← H.fst_eq_snd (show (1, z) ∈ h ⁻¹' (minPaths _ _ _ ∩ Ω') from
        ⟨by simp [h, hmin], by simpa [h] using hPΩ 1⟩)]
      simp [h]
    let Q : Path (e.toFun J') (e.toFun J'') :=
      { toFun := fun t => ⟨h' (t, z), (hh' (t, z)).1⟩
        continuous_toFun := by fun_prop
        source' := Subtype.ext (by change h' (0, z) = _; rw [h0, hφ])
        target' := Subtype.ext (by change h' (1, z) = _; rw [h1, hφ]) }
    exact ((joined_homotopyEquiv e J' (e.toFun J')).2.symm.trans
      (Joined.map (⟨Q⟩ : Joined (e.toFun J') (e.toFun J'')) e.invFun.continuous)).trans
      (joined_homotopyEquiv e J'' (e.toFun J'')).2

end Pi0

end Morse
