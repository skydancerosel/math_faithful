import Morse.Chapter15.FiniteStage
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
Milnor, *Morse Theory*, §24, p. 147 (case `k ≡ 2 (mod 4)`); Exposition/Chapter15.md, §6,
"The components".

# The winding number of `det_ℂ` along a path, and the components `Ω^{(c)}`

## Milnor's text, paraphrased

(p. 147) Make `ℝⁿ` complex by `i = J_1⋯J_{k−1}`; for `J' ∈ Ω_k(n)`, `J⁻¹J'` is unitary, and
`f(J') = det_ℂ(J⁻¹J') ∈ S¹`.  A path `ω` from `J` to `−J` gives a closed loop `f ∘ ω` in `S¹`;
its degree `c` (suitably normalized) is constant on path components, so `Ω^{(c)}`, the paths of
degree `c`, is a union of components.  Along the geodesic `t ↦ J exp(πtA)`,
`f = e^{πt tr_ℂ A}`.

## What is formalized

* `Morse.IsAngleLift F ω θ`: `θ : C(I, ℝ)` is the continuous angle of `t ↦ F(ω t)`, `θ 0 = 0`;
  `Morse.IsAngleLift.unique` (`exp : ℝ → S¹` is a covering), `Morse.IsAngleLift.perturb` (a
  uniformly close loop has the lift `θ + arg(F ∘ ω' / F ∘ ω)`, with the same endpoint).
* `Morse.windSet N p q F w`: the paths whose angle ends at `w`; **`Morse.isClopen_windSet`**:
  open and closed in `Ω(N; p, q)` whenever `F` is continuous with `|F| = 1` on a compact set
  containing `N` (Milnor's `|f ∘ ω − f ∘ ω'| < 2` argument, with uniform continuity of `F`).
* `Morse.cdet ii M = det(M_ℂ P₊ + P₋)`, `P_± = (1 ∓ √−1 · ii)/2`: **`det_ℂ` of a real matrix
  commuting with the complex structure `ii`**, as a polynomial in the entries
  (`Morse.cdet_mul`, `Morse.cdet_one`, `Morse.norm_cdet` (`|det_ℂ| = 1` on orthogonal `M`),
  `Morse.cdet_exp` (**`det_ℂ exp(tV) = e^{−√−1 t tr(V·ii)/2}`** for skew `V`)).

## What Milnor leaves implicit

* `det_ℂ` needs a complex basis; here `P₊` projects onto the `+√−1`-eigenspace of `ii` in `ℂⁿ`,
  which is the complex vector space `(ℝⁿ, ii)`, and `M_ℂP₊ + P₋` acts as `M` there and as `1` on
  the other eigenspace.
* The components are only needed to be open and closed; neither the closedness of the loop
  `f ∘ ω` (`f(−J) = 1`) nor the existence of the angle is used for that.
-/

open Set Filter Topology Function Matrix
open scoped unitInterval ENNReal Morse.MatrixInner

noncomputable section

namespace Morse

/-! ### Angles of loops in the circle -/

section Lift

variable {V : Type*}

/-- `θ` is the continuous angle of `t ↦ F(ω t)` on `[0, 1]`, starting at `0`. -/
def IsAngleLift (F : V → ℂ) (ω : ℝ → V) (θ : C(I, ℝ)) : Prop :=
  θ 0 = 0 ∧ ∀ t : I, F (ω t) = Complex.exp (θ t * Complex.I)

/-- **The angle is unique** (`exp : ℝ → S¹` is a covering map). -/
theorem IsAngleLift.unique {F : V → ℂ} {ω : ℝ → V} {θ₁ θ₂ : C(I, ℝ)}
    (h₁ : IsAngleLift F ω θ₁) (h₂ : IsAngleLift F ω θ₂) : θ₁ = θ₂ := by
  have he : Circle.exp ∘ θ₁ = Circle.exp ∘ θ₂ := funext fun t => by
    apply Circle.ext
    rw [Function.comp_apply, Function.comp_apply, Circle.coe_exp, Circle.coe_exp, ← h₁.2 t,
      h₂.2 t]
  exact ContinuousMap.ext (congrFun (Circle.isCoveringMap_exp.eq_of_comp_eq θ₁.continuous
    θ₂.continuous he 0 (h₁.1.trans h₂.1.symm)))

theorem re_pos_of_norm_sub_one_lt {z : ℂ} (hz : ‖z - 1‖ < 1) : 0 < z.re := by
  have h := (Complex.abs_re_le_norm (z - 1)).trans_lt hz
  rw [Complex.sub_re, Complex.one_re] at h
  linarith [abs_lt.1 h]

/-- **A uniformly close loop has an angle**: `θ + arg(F(ω' t)/F(ω t))`, with the same
endpoint when the loops agree there (Milnor's `|ϑ_ω − ϑ_{ω'}| < π`). -/
theorem IsAngleLift.perturb {F : V → ℂ} {ω ω' : ℝ → V} {θ : C(I, ℝ)}
    (hθ : IsAngleLift F ω θ) (hcω : Continuous fun t : I => F (ω t))
    (hcω' : Continuous fun t : I => F (ω' t)) (h1 : ∀ t : I, ‖F (ω t)‖ = 1)
    (h1' : ∀ t : I, ‖F (ω' t)‖ = 1) (hclose : ∀ t : I, ‖F (ω' t) - F (ω t)‖ < 1)
    (h0 : F (ω' (0 : I)) = F (ω (0 : I))) :
    ∃ θ' : C(I, ℝ), IsAngleLift F ω' θ' ∧ (F (ω' (1 : I)) = F (ω (1 : I)) → θ' 1 = θ 1) := by
  set z : I → ℂ := fun t => F (ω' t) / F (ω t) with hzdef
  have hne : ∀ t : I, F (ω t) ≠ 0 := fun t h => by simpa [h] using h1 t
  have hz1 : ∀ t : I, ‖z t - 1‖ < 1 := fun t => by
    have : z t - 1 = (F (ω' t) - F (ω t)) / F (ω t) := by
      rw [hzdef]; field_simp [hne t]
    rw [this, norm_div, h1 t, div_one]
    exact hclose t
  have hzn : ∀ t : I, ‖z t‖ = 1 := fun t => by rw [hzdef, norm_div, h1 t, h1' t, div_one]
  have hslit : ∀ t : I, z t ∈ Complex.slitPlane := fun t =>
    Complex.mem_slitPlane_iff.2 (Or.inl (re_pos_of_norm_sub_one_lt (hz1 t)))
  have hzc : Continuous z := hcω'.div hcω hne
  have harg : Continuous fun t => Complex.arg (z t) :=
    continuous_iff_continuousAt.2 fun t =>
      (Complex.continuousAt_arg (hslit t)).comp hzc.continuousAt
  have hz_eq : ∀ t : I, F (ω' t) = F (ω t) * z t := fun t => by
    rw [hzdef]; field_simp [hne t]
  have hexp : ∀ t : I, Complex.exp (Complex.arg (z t) * Complex.I) = z t := fun t => by
    have := Complex.norm_mul_exp_arg_mul_I (z t)
    rwa [hzn t, Complex.ofReal_one, one_mul] at this
  have harg_one : ∀ t : I, F (ω' t) = F (ω t) → Complex.arg (z t) = 0 := fun t h => by
    change Complex.arg (F (ω' t) / F (ω t)) = 0
    rw [h, div_self (hne t), Complex.arg_one]
  refine ⟨⟨fun t => θ t + Complex.arg (z t), θ.continuous.add harg⟩, ⟨?_, fun t => ?_⟩,
    fun h => ?_⟩
  · change θ 0 + Complex.arg (z 0) = 0
    rw [hθ.1, harg_one 0 h0, add_zero]
  · change F (ω' t) = Complex.exp (((θ t + Complex.arg (z t) : ℝ) : ℂ) * Complex.I)
    rw [Complex.ofReal_add, add_mul, Complex.exp_add, ← hθ.2 t, hexp, hz_eq]
  · change θ 1 + Complex.arg (z 1) = θ 1
    rw [harg_one 1 h, add_zero]

variable [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {N : Set V} {p q : V}

variable (N p q) in
/-- **Milnor's `Ω^{(c)}`**: the paths `ω` whose angle of `t ↦ F(ω t)` ends at `w`. -/
def windSet (F : V → ℂ) (w : ℝ) : Set (PathSp N p q) :=
  {ω | ∃ θ : C(I, ℝ), IsAngleLift F ω θ ∧ θ 1 = w}

omit [FiniteDimensional ℝ V] in
theorem continuous_comp_path {F : V → ℂ} (hF : Continuous F) (ω : PathSp N p q) :
    Continuous fun t : I => F (ω t) :=
  hF.comp (ω.mem.1.2.1.comp_continuous continuous_subtype_val fun t => t.2)

/-- Paths close for Milnor's metric are uniformly close on `[0, 1]`. -/
theorem norm_sub_lt_of_edist_lt {ω ω' : PathSp N p q} {δ : ℝ} (h : edist ω ω' < ENNReal.ofReal δ)
    (t : I) : ‖ω t - ω' t‖ < δ := by
  have h1 := (ofReal_norm_sub_le_riemDist (N := N) (ω' t) (ω t)).trans
    ((PathSp.riemDist_le_supDist (N := N) (γ := ω') (γ' := ω) t.2).trans
      ((PathSp.supDist_le_edist ω' ω)))
  rw [edist_comm] at h1
  exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (norm_nonneg _)).1 (h1.trans_lt h)

/-- The key step: nearby paths have the same angle at the end. -/
theorem exists_mem_windSet_of_close {F : V → ℂ} (hF : Continuous F) {K : Set V} (hK : IsCompact K)
    (hNK : N ⊆ K) (hF1 : ∀ x ∈ K, ‖F x‖ = 1) :
    ∃ δ > 0, ∀ ω ω' : PathSp N p q, edist ω ω' < ENNReal.ofReal δ → ∀ w : ℝ,
      ω ∈ windSet N p q F w → ω' ∈ windSet N p q F w := by
  obtain ⟨δ, hδ, hδF⟩ := Metric.uniformContinuousOn_iff.1
    (hK.uniformContinuousOn_of_continuous hF.continuousOn) 1 one_pos
  refine ⟨δ, hδ, fun ω ω' hωω' w ⟨θ, hθ, hθw⟩ => ?_⟩
  have hmem : ∀ (γ : PathSp N p q) (t : I), γ t ∈ K := fun γ t => hNK (γ.mem.2.1 t t.2)
  have h0 : ∀ γ : PathSp N p q, γ ((0 : I) : ℝ) = p := fun γ => γ.mem.2.2.1
  have h1 : ∀ γ : PathSp N p q, γ ((1 : I) : ℝ) = q := fun γ => γ.mem.2.2.2
  obtain ⟨θ', hθ', hend⟩ := hθ.perturb (continuous_comp_path hF ω)
    (continuous_comp_path hF ω') (fun t => hF1 _ (hmem ω t)) (fun t => hF1 _ (hmem ω' t))
    (fun t => by
      rw [← dist_eq_norm]
      exact hδF _ (hmem ω' t) _ (hmem ω t) (by
        rw [dist_eq_norm, ← norm_neg, neg_sub]
        exact norm_sub_lt_of_edist_lt hωω' t))
    (by rw [h0, h0])
  exact ⟨θ', hθ', (hend (by rw [h1, h1])).trans hθw⟩

/-- **The sets `Ω^{(c)}` are open and closed** (Milnor p. 147). -/
theorem isClopen_windSet {F : V → ℂ} (hF : Continuous F) {K : Set V} (hK : IsCompact K)
    (hNK : N ⊆ K) (hF1 : ∀ x ∈ K, ‖F x‖ = 1) (w : ℝ) :
    IsClopen (windSet N p q F w) := by
  obtain ⟨δ, hδ, hδw⟩ := exists_mem_windSet_of_close (p := p) (q := q) hF hK hNK hF1
  have hball : ∀ ω : PathSp N p q, Metric.eball ω (ENNReal.ofReal δ) ∈ 𝓝 ω := fun ω =>
    Metric.eball_mem_nhds ω (ENNReal.ofReal_pos.2 hδ)
  refine ⟨isOpen_compl_iff.1 (isOpen_iff_mem_nhds.2 fun ω hω => ?_),
    isOpen_iff_mem_nhds.2 fun ω hω => ?_⟩
  · filter_upwards [hball ω] with ω' hω' hω'w
    exact hω (hδw ω' ω hω' w hω'w)
  · filter_upwards [hball ω] with ω' hω'
    exact hδw ω ω' (by rw [edist_comm]; exact hω') w hω

end Lift

/-! ### `det_ℂ` of a real matrix commuting with a complex structure -/

section CDet

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The complexification `M ↦ M_ℂ`. -/
def cplx : Matrix ι ι ℝ →+* Matrix ι ι ℂ := Complex.ofRealHom.mapMatrix

theorem cplx_apply (M : Matrix ι ι ℝ) (i j : ι) : cplx M i j = (M i j : ℂ) := rfl

theorem continuous_cplx : Continuous (cplx : Matrix ι ι ℝ → Matrix ι ι ℂ) :=
  continuous_id.matrix_map Complex.continuous_ofReal

theorem cplx_transpose (M : Matrix ι ι ℝ) : cplx Mᵀ = (cplx M)ᵀ := rfl

theorem cplx_smul (t : ℝ) (M : Matrix ι ι ℝ) : cplx (t • M) = t • cplx M := by
  ext i j; simp [cplx_apply, Complex.real_smul]

theorem trace_cplx (M : Matrix ι ι ℝ) : trace (cplx M) = ((Matrix.trace M : ℝ) : ℂ) := by
  simp [trace, cplx_apply]

/-- `P₊ = (1 − √−1 · ii)/2`, the projection onto the `+√−1`-eigenspace of `ii`. -/
def projP (ii : Matrix ι ι ℝ) : Matrix ι ι ℂ := (1 / 2 : ℂ) • (1 - Complex.I • cplx ii)

/-- `P₋ = (1 + √−1 · ii)/2`. -/
def projM (ii : Matrix ι ι ℝ) : Matrix ι ι ℂ := (1 / 2 : ℂ) • (1 + Complex.I • cplx ii)

/-- **`det_ℂ M`** for `M` commuting with the complex structure `ii`: `det(M_ℂ P₊ + P₋)`. -/
def cdet (ii M : Matrix ι ι ℝ) : ℂ := (cplx M * projP ii + projM ii).det

theorem continuous_cdet (ii : Matrix ι ι ℝ) : Continuous (cdet ii) :=
  (continuous_id.matrix_det).comp ((continuous_cplx.mul continuous_const).add continuous_const)

variable {ii : Matrix ι ι ℝ}

theorem cplx_sq (hii : ii * ii = -1) : cplx ii * cplx ii = -1 := by
  rw [← map_mul, hii, map_neg, map_one]

theorem projP_add_projM : projP ii + projM ii = 1 := by
  rw [projP, projM, ← smul_add, sub_add_add_cancel, ← two_smul ℂ (1 : Matrix ι ι ℂ), smul_smul]
  norm_num

theorem projP_mul_projM (hii : ii * ii = -1) : projP ii * projM ii = 0 := by
  rw [projP, projM, Matrix.smul_mul, Matrix.mul_smul, Matrix.sub_mul, Matrix.mul_add,
    Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.mul_smul, smul_smul, cplx_sq hii, Matrix.one_mul, smul_smul, Complex.I_mul_I]
  module

theorem projM_mul_projP (hii : ii * ii = -1) : projM ii * projP ii = 0 := by
  rw [projP, projM, Matrix.smul_mul, Matrix.mul_smul, Matrix.add_mul, Matrix.mul_sub,
    Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.mul_smul, smul_smul, cplx_sq hii, Matrix.one_mul, smul_smul, Complex.I_mul_I]
  module

theorem projP_mul_projP (hii : ii * ii = -1) : projP ii * projP ii = projP ii := by
  have h := congrArg (projP ii * ·) (projP_add_projM (ii := ii))
  simp only [Matrix.mul_add, projP_mul_projM hii, add_zero, Matrix.mul_one] at h
  exact h

theorem projM_mul_projM (hii : ii * ii = -1) : projM ii * projM ii = projM ii := by
  have h := congrArg (projM ii * ·) (projP_add_projM (ii := ii))
  simp only [Matrix.mul_add, projM_mul_projP hii, zero_add, Matrix.mul_one] at h
  exact h

theorem cplx_comm_projP {M : Matrix ι ι ℝ} (hM : M * ii = ii * M) :
    cplx M * projP ii = projP ii * cplx M := by
  rw [projP, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one,
    Matrix.one_mul, Matrix.mul_smul, Matrix.smul_mul, ← map_mul, ← map_mul, hM]

theorem cplx_comm_projM {M : Matrix ι ι ℝ} (hM : M * ii = ii * M) :
    cplx M * projM ii = projM ii * cplx M := by
  rw [projM, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one,
    Matrix.one_mul, Matrix.mul_smul, Matrix.smul_mul, ← map_mul, ← map_mul, hM]

/-- **`det_ℂ` is multiplicative** on the matrices commuting with `ii`. -/
theorem cdet_mul (hii : ii * ii = -1) (M : Matrix ι ι ℝ) {N : Matrix ι ι ℝ}
    (hN : N * ii = ii * N) : cdet ii (M * N) = cdet ii M * cdet ii N := by
  rw [cdet, cdet, cdet, ← det_mul]
  congr 1
  have hPN := cplx_comm_projP hN
  have hQN := cplx_comm_projM hN
  have e1 : cplx M * projP ii * (cplx N * projP ii) = cplx M * cplx N * projP ii :=
    calc cplx M * projP ii * (cplx N * projP ii) = cplx M * (projP ii * cplx N) * projP ii := by
          simp only [Matrix.mul_assoc]
      _ = cplx M * (cplx N * projP ii) * projP ii := by rw [← hPN]
      _ = cplx M * cplx N * (projP ii * projP ii) := by simp only [Matrix.mul_assoc]
      _ = cplx M * cplx N * projP ii := by rw [projP_mul_projP hii]
  have e2 : cplx M * projP ii * projM ii = 0 := by
    rw [Matrix.mul_assoc, projP_mul_projM hii, Matrix.mul_zero]
  have e3 : projM ii * (cplx N * projP ii) = 0 := by
    rw [← Matrix.mul_assoc, ← hQN, Matrix.mul_assoc, projM_mul_projP hii, Matrix.mul_zero]
  rw [map_mul, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, e1, e2, e3,
    projM_mul_projM hii, add_zero, zero_add]

theorem cdet_one : cdet ii 1 = 1 := by
  rw [cdet, map_one, Matrix.one_mul, projP_add_projM, det_one]

/-- **`conj det_ℂ M = det_ℂ Mᵀ`**. -/
theorem conj_cdet (hskew : iiᵀ = -ii) {M : Matrix ι ι ℝ}
    (hM : M * ii = ii * M) : starRingEnd ℂ (cdet ii M) = cdet ii Mᵀ := by
  have hconjP : (starRingEnd ℂ).mapMatrix (projP ii) = projM ii := by
    ext i j
    rw [RingHom.mapMatrix_apply, Matrix.map_apply]
    simp only [projP, projM, Matrix.smul_apply, Matrix.sub_apply, Matrix.add_apply, cplx_apply,
      smul_eq_mul, Matrix.one_apply]
    split_ifs <;> simp [map_ofNat]
  have hconjM : (starRingEnd ℂ).mapMatrix (projM ii) = projP ii := by
    ext i j
    rw [RingHom.mapMatrix_apply, Matrix.map_apply]
    simp only [projP, projM, Matrix.smul_apply, Matrix.sub_apply, Matrix.add_apply, cplx_apply,
      smul_eq_mul, Matrix.one_apply]
    split_ifs <;> simp [map_ofNat, sub_eq_add_neg]
  have hconjC : (starRingEnd ℂ).mapMatrix (cplx M) = cplx M := by
    ext i j
    rw [RingHom.mapMatrix_apply, Matrix.map_apply, cplx_apply, Complex.conj_ofReal]
  have htP : (projP ii)ᵀ = projM ii := by
    rw [projP, projM, transpose_smul, transpose_sub, transpose_one, transpose_smul,
      ← cplx_transpose, hskew, map_neg, smul_neg, sub_neg_eq_add]
  have htM : (projM ii)ᵀ = projP ii := by
    rw [projP, projM, transpose_smul, transpose_add, transpose_one, transpose_smul,
      ← cplx_transpose, hskew, map_neg, smul_neg, ← sub_eq_add_neg]
  rw [cdet, RingHom.map_det, map_add, map_mul, hconjP, hconjM, hconjC, cdet,
    ← det_transpose (cplx Mᵀ * projP ii + projM ii), transpose_add, transpose_mul, htP, htM,
    cplx_transpose, transpose_transpose, cplx_comm_projM hM]

/-- **`|det_ℂ M| = 1`** for `M` orthogonal and commuting with `ii`. -/
theorem norm_cdet (hii : ii * ii = -1) (hskew : iiᵀ = -ii) {M : Matrix ι ι ℝ}
    (hM : M * ii = ii * M) (horth : M * Mᵀ = 1) : ‖cdet ii M‖ = 1 := by
  have hMt : Mᵀ * ii = ii * Mᵀ := by
    have := congrArg transpose hM
    rw [transpose_mul, transpose_mul, hskew, Matrix.mul_neg, Matrix.neg_mul, neg_inj] at this
    exact this.symm
  have h := Complex.mul_conj (cdet ii M)
  rw [conj_cdet hskew hM, ← cdet_mul hii M hMt, horth, cdet_one] at h
  have h2 : Complex.normSq (cdet ii M) = 1 := by exact_mod_cast h.symm
  rw [Complex.normSq_eq_norm_sq] at h2
  have := norm_nonneg (cdet ii M)
  nlinarith

/-! ### `det_ℂ` along a one-parameter group -/

/-- A solution of `c' = cX` is `c(t) = c(0) exp(tX)` (complex matrices). -/
theorem eq_mul_exp_smul_of_hasDerivAt_cplx {X : Matrix ι ι ℂ} {c : ℝ → Matrix ι ι ℂ}
    (hc : ∀ t, HasDerivAt c (c t * X) t) (t : ℝ) : c t = c 0 * NormedSpace.exp (t • X) := by
  set g : ℝ → Matrix ι ι ℂ := fun s => c s * NormedSpace.exp (s • -X) with hgdef
  have hg : ∀ s, HasDerivAt g 0 s := fun s => by
    have h1 := (hc s).mul (hasDerivAt_exp_smul_const (-X) s)
    refine h1.congr_deriv ?_
    have hcomm : NormedSpace.exp (s • -X) * -X = -X * NormedSpace.exp (s • -X) := exp_smul_mul_self (-X) s
    have hcomm' : X * NormedSpace.exp (s • -X) = NormedSpace.exp (s • -X) * X := by
      have := congrArg Neg.neg hcomm
      simpa only [Matrix.mul_neg, Matrix.neg_mul, neg_neg] using this.symm
    rw [Matrix.mul_assoc, hcomm', Matrix.mul_neg, Matrix.mul_neg, add_neg_cancel]
  have hgc : ∀ s, g s = g 0 := fun s =>
    is_const_of_deriv_eq_zero (fun u => (hg u).differentiableAt) (fun u => (hg u).deriv) s 0
  have h0 : g 0 = c 0 := by simp [hgdef]
  have ht := hgc t
  rw [h0] at ht
  have hinv : NormedSpace.exp (t • -X) * NormedSpace.exp (t • X) = 1 := by
    have := exp_mul_exp_neg (-(t • X))
    rwa [neg_neg, ← smul_neg] at this
  calc c t = c t * NormedSpace.exp (t • -X) * NormedSpace.exp (t • X) := by rw [Matrix.mul_assoc, hinv, Matrix.mul_one]
    _ = c 0 * NormedSpace.exp (t • X) := by rw [← ht]

/-- **`det exp(tX) = e^{t tr X}`** (complex matrices; Jacobi's formula). -/
theorem det_exp_smul_cplx (X : Matrix ι ι ℂ) (t : ℝ) :
    det (NormedSpace.exp (t • X)) = Complex.exp (t * trace X) := by
  set g : ℝ → ℂ := fun s => det (NormedSpace.exp (s • X)) * Complex.exp (-((s : ℂ) * trace X)) with hgdef
  have hg : ∀ s, HasDerivAt g 0 s := fun s => by
    have h1 := hasDerivAt_det_exp_smul X s
    have h2 : HasDerivAt (fun s : ℝ => Complex.exp (-((s : ℂ) * trace X)))
        (Complex.exp (-((s : ℂ) * trace X)) * -((1 : ℝ) * trace X)) s :=
      (((hasDerivAt_id s).ofReal_comp).mul_const (trace X)).neg.cexp
    refine (h1.mul h2).congr_deriv ?_
    simp only [Complex.ofReal_one, one_mul]
    ring
  have hgc := is_const_of_deriv_eq_zero (fun u => (hg u).differentiableAt)
    (fun u => (hg u).deriv) t 0
  simp only [hgdef, Complex.ofReal_zero, zero_mul, neg_zero, Complex.exp_zero, mul_one,
    zero_smul, NormedSpace.exp_zero, det_one] at hgc
  calc det (NormedSpace.exp (t • X)) = det (NormedSpace.exp (t • X)) * Complex.exp (-((t : ℂ) * trace X)) *
        Complex.exp (t * trace X) := by
          rw [mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, mul_one]
    _ = Complex.exp (t * trace X) := by rw [hgc, one_mul]

/-- **`det_ℂ exp(tV) = e^{−√−1 t tr(V·ii)/2}`** for `V` commuting with `ii` and of trace `0`
(Milnor: `f(J exp(πtA)) = e^{πt tr_ℂ A}`). -/
theorem cdet_exp (hii : ii * ii = -1) {V : Matrix ι ι ℝ} (hV : V * ii = ii * V)
    (htr : trace V = 0) (t : ℝ) :
    cdet ii (NormedSpace.exp (t • V)) = Complex.exp (((-(t * trace (V * ii)) / 2 : ℝ) : ℂ) * Complex.I) := by
  set W := cplx V with hW
  have hWP : W * projP ii = projP ii * W := cplx_comm_projP hV
  have hWM : W * projM ii = projM ii * W := cplx_comm_projM hV
  have hmap : ∀ s : ℝ, cplx (NormedSpace.exp (s • V)) = NormedSpace.exp (s • W) := fun s => by
    rw [NormedSpace.map_exp_of_mem_ball (𝕂 := ℝ) (cplx (ι := ι)) continuous_cplx _
      (by rw [NormedSpace.expSeries_radius_eq_top]; exact edist_lt_top _ _), cplx_smul]
  set c : ℝ → Matrix ι ι ℂ := fun s => NormedSpace.exp (s • W) * projP ii + projM ii with hcdef
  have hc : ∀ s, HasDerivAt c (c s * (W * projP ii)) s := fun s => by
    refine ((hasDerivAt_exp_smul_const W s).mul_const (projP ii)).add_const (projM ii)
      |>.congr_deriv ?_
    have e1 : projM ii * (W * projP ii) = 0 := by
      rw [← Matrix.mul_assoc, ← hWM, Matrix.mul_assoc, projM_mul_projP hii, Matrix.mul_zero]
    have e2 : NormedSpace.exp (s • W) * projP ii * (W * projP ii) =
        NormedSpace.exp (s • W) * W * projP ii :=
      calc NormedSpace.exp (s • W) * projP ii * (W * projP ii)
          = NormedSpace.exp (s • W) * (projP ii * W) * projP ii := by simp only [Matrix.mul_assoc]
        _ = NormedSpace.exp (s • W) * (W * projP ii) * projP ii := by rw [← hWP]
        _ = NormedSpace.exp (s • W) * W * (projP ii * projP ii) := by simp only [Matrix.mul_assoc]
        _ = NormedSpace.exp (s • W) * W * projP ii := by rw [projP_mul_projP hii]
    simp only [hcdef]
    rw [Matrix.add_mul, e1, e2, add_zero]
  have hc0 : c 0 = 1 := by simp [hcdef, projP_add_projM]
  have hct := eq_mul_exp_smul_of_hasDerivAt_cplx hc t
  rw [hc0, Matrix.one_mul] at hct
  rw [cdet, hmap, show NormedSpace.exp (t • W) * projP ii + projM ii = c t from rfl, hct,
    det_exp_smul_cplx]
  congr 1
  rw [projP, Matrix.mul_smul, Matrix.mul_sub, Matrix.mul_one, Matrix.mul_smul, trace_smul,
    trace_sub, trace_smul, hW, ← map_mul, trace_cplx, trace_cplx, htr]
  push_cast
  simp only [smul_eq_mul]
  ring

end CDet

end Morse
