import Morse.Chapter15.Winding

/-!
Milnor, *Morse Theory*, §24, p. 147 (case `k ≡ 2 (mod 4)`); Exposition/Chapter15.md, §6,
"The components" and "The geodesics".

# The components `Ω^{(c)}` of the path space of `Ω_k(n)`, `k = 2, 6`

## Milnor's text, paraphrased

(p. 147) For `k ≡ 2 (mod 4)` let `i = J_1⋯J_{k−1}`: a complex structure commuting with
`J_1, …, J_{k−1}` and anticommuting with every `J' ∈ Ω_k(n)`.  With `f(J') = det_ℂ(J⁻¹J')`, the
paths from `J` to `−J` fall into the open and closed sets `Ω^{(c)}`; the geodesic
`t ↦ J exp(πtA)` lies in the one with `f`-angle `π tr_ℂ A / i`.

## What is formalized

* `Morse.IsCentralI J k ii`: `ii` is a complex structure which commutes with every matrix
  commuting with `J_1, …, J_{k−1}` and anticommutes with every matrix anticommuting with them;
  `Morse.isCentralI_two` (`ii = J_1`, `k = 2`), `Morse.isCentralI_six` (`ii = J_1J_2J_3J_4J_5`,
  `k = 6`) (Milnor's `i`; Lemma 2.1 of the exposition).
* `Morse.omegaF ii p X = det_ℂ(pᵀX)` (Milnor's `f`, `p = J_k`), `Morse.norm_omegaF`
  (`|f| = 1` on `Ω_k(n)`), `Morse.omegaF_self` (`f(J) = 1`), `Morse.omegaF_geo`
  (`f(p exp(tV)) = e^{−√−1 t tr(V·ii)/2}`).
* `Morse.omegaComp J k ii w`: the paths in the stratum of `J_k` whose `f`-angle ends at `w`;
  **`Morse.isClopen_omegaComp`**; **`Morse.mem_omegaComp_geo_iff`**: a path equal on `[0, 1]` to
  `t ↦ p exp(tV)`, `V ∈ 𝒯_p`, lies in `omegaComp w` iff `w = −tr(V·ii)/2`.

## What Milnor leaves implicit

* That `J⁻¹J'` commutes with `i` (so that `det_ℂ` makes sense) uses only that `J`, `J'` both
  anticommute with `i`; that `|f| = 1` uses that `J⁻¹J'` is orthogonal.
-/

open Set Filter Topology Function Matrix
open scoped unitInterval ENNReal Morse.MatrixInner

noncomputable section

namespace Morse

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {J : ℕ → Matrix ι ι ℝ} {k : ℕ}

/-- **Milnor's `i = J_1⋯J_{k−1}`** (`k ≡ 2 (mod 4)`), axiomatized by what is used. -/
structure IsCentralI (J : ℕ → Matrix ι ι ℝ) (k : ℕ) (ii : Matrix ι ι ℝ) : Prop where
  sq : ii * ii = -1
  skew : iiᵀ = -ii
  comm : ∀ A : Matrix ι ι ℝ, (∀ α, 1 ≤ α → α < k → A * J α = J α * A) → A * ii = ii * A
  anti : ∀ X : Matrix ι ι ℝ, (∀ α, 1 ≤ α → α < k → J α * X = -(X * J α)) →
    X * ii = -(ii * X)
  jcomm : ∀ α, 1 ≤ α → α < k → J α * ii = ii * J α

variable (J k) in
/-- The word `J_1⋯J_{k−1}`. -/
def iWordM : Matrix ι ι ℝ := ((List.range (k - 1)).map fun i => J (i + 1)).prod

theorem iWordM_two : iWordM J 2 = J 1 := by simp [iWordM]

theorem iWordM_six : iWordM J 6 = J 1 * J 2 * J 3 * J 4 * J 5 := by
  simp [iWordM, List.range_succ, Matrix.mul_assoc]

/-- `k = 2`: `i = J_1`. -/
theorem isCentralI_two (hJ : IsAnticommFamily J 1) : IsCentralI J 2 (J 1) where
  sq := (hJ.cs 1 le_rfl le_rfl).2
  skew := (hJ.cs 1 le_rfl le_rfl).transpose
  comm A hA := hA 1 le_rfl (by norm_num)
  anti X hX := by rw [hX 1 le_rfl (by norm_num), neg_neg]
  jcomm α h1 h2 := by
    obtain rfl : α = 1 := by omega
    rfl

/-- `k = 6`: `i = J_1J_2J_3J_4J_5` (Lemma 2.1: five factors give a complex structure). -/
theorem isCentralI_six (hJ : IsAnticommFamily J 5) :
    IsCentralI J 6 (J 1 * J 2 * J 3 * J 4 * J 5) where
  sq := by
    have h := hJ.isClifford
    clifford_simp h
  skew := by
    have h := hJ.isClifford
    have ht : ∀ α, 1 ≤ α → α ≤ 5 → (J α)ᵀ = -J α := fun α h1 h2 => (hJ.cs α h1 h2).transpose
    simp only [transpose_mul, ht 1 le_rfl (by norm_num), ht 2 (by norm_num) (by norm_num),
      ht 3 (by norm_num) (by norm_num), ht 4 (by norm_num) (by norm_num),
      ht 5 (by norm_num) le_rfl]
    clifford_simp h
  comm A hA := by
    have hc : ∀ α, 1 ≤ α → α ≤ 5 → Commute A (J α) := fun α h1 h2 => hA α h1 (by omega)
    exact ((((hc 1 le_rfl (by norm_num)).mul_right (hc 2 (by norm_num) (by norm_num))).mul_right
      (hc 3 (by norm_num) (by norm_num))).mul_right (hc 4 (by norm_num) (by norm_num))).mul_right
      (hc 5 (by norm_num) le_rfl) |>.eq
  anti X hX := by
    have h1 : ∀ α, 1 ≤ α → α ≤ 5 → ∀ Y, X * (J α * Y) = -(J α * (X * Y)) := fun α h1 h2 Y => by
      rw [← Matrix.mul_assoc, show X * J α = -(J α * X) by rw [hX α h1 (by omega), neg_neg],
        Matrix.neg_mul, Matrix.mul_assoc]
    have h0 : X * J 5 = -(J 5 * X) := by rw [hX 5 (by norm_num) (by norm_num), neg_neg]
    simp only [Matrix.mul_assoc, h1 1 le_rfl (by norm_num), h1 2 (by norm_num) (by norm_num),
      h1 3 (by norm_num) (by norm_num), h1 4 (by norm_num) (by norm_num), h0, Matrix.mul_neg,
      neg_neg]
  jcomm α h1 h2 := by
    have h := hJ.isClifford
    interval_cases α <;> clifford_simp h

/-- **Milnor's `f(X) = det_ℂ(J⁻¹X)`** (`p = J`). -/
def omegaF (ii p X : Matrix ι ι ℝ) : ℂ := cdet ii (pᵀ * X)

theorem continuous_omegaF (ii p : Matrix ι ι ℝ) : Continuous (omegaF ii p) :=
  (continuous_cdet ii).comp (continuous_const.mul continuous_id)

variable {ii p : Matrix ι ι ℝ}

theorem anti_of_mem_omega (hk : k ≠ 0) {X : Matrix ι ι ℝ} (hX : X ∈ Omega J k) :
    ∀ α, 1 ≤ α → α < k → J α * X = -(X * J α) := by
  obtain ⟨k, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  exact fun α h1 h2 => hX.2 α h1 (by omega)

theorem IsCentralI.comm_transpose_mul (hii : IsCentralI J k ii) (hk : k ≠ 0)
    (hp : p ∈ Omega J k) {X : Matrix ι ι ℝ} (hX : X ∈ Omega J k) :
    pᵀ * X * ii = ii * (pᵀ * X) := by
  have hpi := hii.anti p (anti_of_mem_omega hk hp)
  have hXi := hii.anti X (anti_of_mem_omega hk hX)
  have hpt : pᵀ * ii = -(ii * pᵀ) := by
    have := congrArg transpose hpi
    rw [transpose_mul, transpose_neg, transpose_mul, hii.skew, Matrix.mul_neg, Matrix.neg_mul,
      neg_inj] at this
    rw [this, neg_neg]
  rw [Matrix.mul_assoc, hXi, Matrix.mul_neg, ← Matrix.mul_assoc, hpt, Matrix.neg_mul, neg_neg,
    Matrix.mul_assoc]

/-- **`|f| = 1` on `Ω_k(n)`**. -/
theorem norm_omegaF (hii : IsCentralI J k ii) (hk : k ≠ 0) (hp : p ∈ Omega J k)
    {X : Matrix ι ι ℝ} (hX : X ∈ Omega J k) : ‖omegaF ii p X‖ = 1 := by
  refine norm_cdet hii.sq hii.skew (hii.comm_transpose_mul hk hp hX) ?_
  have hpo := omega_orth hp
  have hXo : X * Xᴴ = 1 := mul_eq_one_comm.1 (omega_orth hX)
  rw [conjTranspose_real] at hpo hXo
  rw [transpose_mul, transpose_transpose]
  calc pᵀ * X * (Xᵀ * p) = pᵀ * (X * Xᵀ) * p := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hXo, Matrix.mul_one, hpo]

theorem omegaF_self (hp : p ∈ Omega J k) : omegaF ii p p = 1 := by
  have hpo := omega_orth hp
  rw [conjTranspose_real] at hpo
  rw [omegaF, hpo, cdet_one]

/-- **`f` along a geodesic** `t ↦ p exp(tV)`, `V ∈ 𝒯_p`: `e^{−√−1 t tr(V·ii)/2}`. -/
theorem omegaF_geo (hii : IsCentralI J k ii) (hp : p ∈ Omega J k) {V : Matrix ι ι ℝ}
    (hV : V ∈ tanAlg J k p) (t : ℝ) :
    omegaF ii p (p * NormedSpace.exp (t • V)) =
      Complex.exp (((-(t * trace (V * ii)) / 2 : ℝ) : ℂ) * Complex.I) := by
  have hpo := omega_orth hp
  rw [conjTranspose_real] at hpo
  rw [omegaF, ← Matrix.mul_assoc, hpo, Matrix.one_mul]
  exact cdet_exp hii.sq (hii.comm V hV.2.2) (trace_eq_zero_of_skew_real hV.1) t

variable (J k ii) in
/-- **Milnor's `Ω^{(c)}`** in the path space of (the stratum of `J_k` in) `Ω_k(n)`: the paths
whose `f`-angle ends at `w`. -/
def omegaComp (w : ℝ) :
    Set (PathSp (omegaStratum J k (basePt J k)) (basePt J k) (-basePt J k)) :=
  windSet _ _ _ (omegaF ii (basePt J k)) w

/-- **The sets `Ω^{(c)}` are open and closed** (Milnor p. 147). -/
theorem isClopen_omegaComp (hJ : IsAnticommFamily J k) (hk : k ≠ 0) (hii : IsCentralI J k ii)
    (w : ℝ) : IsClopen (omegaComp J k ii w) :=
  isClopen_windSet (continuous_omegaF ii _) (isCompact_omega J k) (omegaStratum_subset _)
    (fun _ hX => norm_omegaF hii hk (basePt_mem_omega hJ) hX) w

/-- **The component of a geodesic** (Milnor p. 147): a path equal on `[0, 1]` to
`t ↦ J_k exp(tV)`, `V ∈ 𝒯`, lies in `Ω^{(w)}` iff `w = −tr(V·ii)/2`. -/
theorem mem_omegaComp_geo_iff (hJ : IsAnticommFamily J k) (hii : IsCentralI J k ii)
    {γ : ℝ → Matrix ι ι ℝ}
    (hγ : γ ∈ pathSpace (omegaStratum J k (basePt J k)) (basePt J k) (-basePt J k))
    {V : Matrix ι ι ℝ} (hV : V ∈ tanAlg J k (basePt J k))
    (heq : EqOn γ (fun t => basePt J k * NormedSpace.exp (t • V)) (Icc 0 1)) (w : ℝ) :
    (⟨γ, hγ⟩ : PathSp _ _ _) ∈ omegaComp J k ii w ↔ w = -trace (V * ii) / 2 := by
  have hp := basePt_mem_omega hJ
  let θ : C(I, ℝ) := ⟨fun t => -((t : ℝ) * trace (V * ii)) / 2, by fun_prop⟩
  have hθ : IsAngleLift (omegaF ii (basePt J k)) γ θ :=
    ⟨by simp [θ], fun t => by
      rw [heq t.2, omegaF_geo hii hp hV]
      rfl⟩
  constructor
  · rintro ⟨θ', hθ', hθ'w⟩
    rw [← hθ'w, hθ'.unique hθ]
    simp [θ]
  · intro hw
    exact ⟨θ, hθ, by simp [θ, hw]⟩

end Morse
