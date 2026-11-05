import Morse
import RoundTrip.Check
import RoundTrip.Blind.V15_39

namespace RoundTrip.V15_39

/-- The project's statement (universes instantiated at `0`), for `IsAnticommFamily J (k + 1)`
(`J_1, …, J_{k+1}`): `IsCentralI J k (J_1⋯J_{k−1})` for `k = 2, 6`; `φ(J') ∈ Ω^{(w)}` with
`w = −π tr(J_kᵀJ'·i)/2`; and, for `k ≠ 0`, `k + 1 ≤ 8`, `k ≢ 3 (mod 4)` with `IsCentralI`
(resp. `k = 2, 6`): the minimal geodesics in `Ω^{(c)}` include into `Ω^{(c)}` bijectively on `π_j`
for `j + 2 ≤ (n/m_{k+1} − |c|)/4`; `φ : Ω_{k+1}(n) → Ω(stratum of J_k; J_k, −J_k)` is bijective on
`π_{j+1}` at every `J'` with `φ(J') ∈ Ω^{(c)}` for `j + 3 ≤ (n/m_{k+1} − |c|)/4` (two forms), and
then `π_{j+1}(Ω_{k+1}(n), J') ≃ π_{j+2}(Ω_k(n), J_k)`. -/
def A : Prop :=
  type_of% @Morse.isCentralI_iWordM.{0} ∧ type_of% @Morse.omegaPhi_mem_omegaComp.{0} ∧
    type_of% @Morse.omega_minPaths_bijective_two.{0} ∧ type_of% @Morse.omegaPhi_bijective_two.{0} ∧
    type_of% @Morse.theorem_24_5_two_six.{0} ∧ type_of% @Morse.omega_pi_equiv_two.{0}

theorem A_holds : A :=
  ⟨@Morse.isCentralI_iWordM.{0}, @Morse.omegaPhi_mem_omegaComp.{0},
    @Morse.omega_minPaths_bijective_two.{0}, @Morse.omegaPhi_bijective_two.{0},
    @Morse.theorem_24_5_two_six.{0}, @Morse.omega_pi_equiv_two.{0}⟩

/-! ### A's extra hypothesis is satisfiable

A assumes `J_1, …, J_{k+1}` (`IsAnticommFamily J (k + 1)`), B only `J_1, …, J_k`. For
`k ≡ 2 (mod 4)` the product `J_{k+1} := J_1⋯J_k` always completes the family (proved here), so
A's extra hypothesis costs nothing; the failure of A ⇒ B is the transport glue (see the json). -/

section Extend
variable {ι : Type} [Fintype ι] [DecidableEq ι]
set_option linter.unusedSectionVars false
open Matrix

theorem iProd_succ (Js : ℕ → Mat ι) (m : ℕ) : iProd Js (m + 1) = iProd Js m * Js (m + 1) := rfl

theorem iProd_mem_orth (Js : ℕ → Mat ι) :
    ∀ m, (∀ α, 1 ≤ α → α ≤ m → Js α ∈ orthogonalGroup ι ℝ) → iProd Js m ∈ orthogonalGroup ι ℝ
  | 0, _ => (orthogonalGroup ι ℝ).one_mem
  | m + 1, h => by
    rw [iProd_succ]
    exact (orthogonalGroup ι ℝ).mul_mem (iProd_mem_orth Js m fun α h1 h2 => h α h1 (by omega))
      (h (m + 1) (by omega) le_rfl)

theorem comm_iProd (Js : ℕ → Mat ι) (X : Mat ι) :
    ∀ m, (∀ α, 1 ≤ α → α ≤ m → Commute X (Js α)) → Commute X (iProd Js m)
  | 0, _ => Commute.one_right X
  | m + 1, h => by
    rw [iProd_succ]
    exact (comm_iProd Js X m fun α h1 h2 => h α h1 (by omega)).mul_right
      (h (m + 1) (by omega) le_rfl)

/-- `Y (J_1 ⋯ J_m) = (−1)^m (J_1 ⋯ J_m) Y` when `Y` anticommutes with `J_1, …, J_m`. -/
theorem anti_iProd (Js : ℕ → Mat ι) (Y : Mat ι) :
    ∀ m, (∀ α, 1 ≤ α → α ≤ m → Y * Js α = -(Js α * Y)) →
      Y * iProd Js m = ((-1 : ℝ) ^ m) • (iProd Js m * Y)
  | 0, _ => by simp [iProd]
  | m + 1, h => by
    have ih := anti_iProd Js Y m fun α h1 h2 => h α h1 (by omega)
    rw [iProd_succ, ← Matrix.mul_assoc, ih, Matrix.smul_mul, Matrix.mul_assoc,
      h (m + 1) (by omega) le_rfl, Matrix.mul_neg, pow_succ, mul_neg_one, neg_smul, smul_neg,
      ← Matrix.mul_assoc]

theorem isACFam_mono {Js : ℕ → Mat ι} {m : ℕ} (h : IsACFam Js (m + 1)) : IsACFam Js m :=
  ⟨fun α h1 h2 => h.1 α h1 (by omega), fun α β h1 h2 h3 h4 hne => h.2 α β h1 (by omega) h3
    (by omega) hne⟩

/-- `(J_1 ⋯ J_m)² = (−1)^{m(m+1)/2}`. -/
theorem sq_iProd (Js : ℕ → Mat ι) :
    ∀ m, IsACFam Js m → iProd Js m * iProd Js m = ((-1 : ℝ) ^ (m * (m + 1) / 2)) • 1
  | 0, _ => by simp [iProd]
  | m + 1, h => by
    have ih := sq_iProd Js m (isACFam_mono h)
    have hanti := anti_iProd Js (Js (m + 1)) m fun α h1 h2 =>
      h.2 (m + 1) α (by omega) le_rfl h1 (by omega) (by omega)
    have hJJ : Js (m + 1) * Js (m + 1) = -1 := (h.1 (m + 1) (by omega) le_rfl).2
    have hdiv : (m + 1) * (m + 1 + 1) / 2 = m * (m + 1) / 2 + (m + 1) := by
      rw [show (m + 1) * (m + 1 + 1) = m * (m + 1) + 2 * (m + 1) by ring,
        Nat.add_mul_div_left _ _ two_pos]
    rw [iProd_succ]
    calc iProd Js m * Js (m + 1) * (iProd Js m * Js (m + 1))
        = iProd Js m * (Js (m + 1) * iProd Js m) * Js (m + 1) := by simp only [Matrix.mul_assoc]
      _ = ((-1 : ℝ) ^ m) • ((iProd Js m * iProd Js m) * (Js (m + 1) * Js (m + 1))) := by
          rw [hanti, Matrix.mul_smul, Matrix.smul_mul]; simp only [Matrix.mul_assoc]
      _ = _ := by
          rw [ih, hJJ, hdiv, Matrix.smul_mul, Matrix.one_mul, smul_smul, smul_neg, ← neg_smul]
          congr 1
          ring

/-- `J_α (J_1 ⋯ J_m) = (−1)^{m+1} (J_1 ⋯ J_m) J_α` for `1 ≤ α ≤ m`. -/
theorem jcomm_iProd (Js : ℕ → Mat ι) :
    ∀ m, IsACFam Js m → ∀ α, 1 ≤ α → α ≤ m →
      Js α * iProd Js m = ((-1 : ℝ) ^ (m + 1)) • (iProd Js m * Js α)
  | 0, _, α, h1, h2 => absurd h2 (by omega)
  | m + 1, h, α, h1, h2 => by
    rw [iProd_succ]
    rcases (show α ≤ m ∨ α = m + 1 by omega) with hα | rfl
    · have ih := jcomm_iProd Js m (isACFam_mono h) α h1 hα
      have hanti : Js α * Js (m + 1) = -(Js (m + 1) * Js α) :=
        h.2 α (m + 1) h1 (by omega) (by omega) le_rfl (by omega)
      rw [← Matrix.mul_assoc, ih, Matrix.smul_mul, Matrix.mul_assoc, hanti, Matrix.mul_neg,
        ← Matrix.mul_assoc, smul_neg, ← neg_smul, pow_succ (-1 : ℝ) (m + 1), mul_neg_one]
    · have hanti := anti_iProd Js (Js (m + 1)) m fun β h1 h2 =>
        h.2 (m + 1) β (by omega) le_rfl h1 (by omega) (by omega)
      rw [← Matrix.mul_assoc, hanti, Matrix.smul_mul, Matrix.mul_assoc, pow_succ, pow_succ,
        mul_neg_one, mul_neg_one, neg_neg]

theorem transpose_eq_neg {J : Mat ι} (hJ : IsCplxStr J) : Jᵀ = -J := by
  have h1 : Jᵀ * J = 1 := by
    have := hJ.1
    rw [Matrix.mem_orthogonalGroup_iff'] at this
    simpa [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] using this
  calc Jᵀ = Jᵀ * (J * -J) := by rw [Matrix.mul_neg, hJ.2, neg_neg, Matrix.mul_one]
    _ = -J := by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]


/-- **`J_{k+1} := J_1⋯J_k` extends an anticommuting family of length `k ≡ 2 (mod 4)`.** -/
theorem isAnticommFamily_extend {Js : ℕ → Mat ι} {k : ℕ} (hk : k % 4 = 2) (hJ : IsACFam Js k) :
    Morse.IsAnticommFamily (Function.update Js (k + 1) (iProd Js k)) (k + 1) := by
  obtain ⟨q, hq⟩ : ∃ q, k = 4 * q + 2 := ⟨k / 4, by omega⟩
  have hsq : iProd Js k * iProd Js k = -1 := by
    rw [sq_iProd Js k hJ, hq]
    have : (4 * q + 2) * (4 * q + 2 + 1) / 2 = 2 * (4 * q * q + 5 * q + 1) + 1 := by
      rw [show (4 * q + 2) * (4 * q + 2 + 1) = 2 * (2 * (4 * q * q + 5 * q + 1) + 1) by ring]
      exact Nat.mul_div_cancel_left _ two_pos
    rw [this, pow_succ, pow_mul]
    simp
  have hcs : IsCplxStr (iProd Js k) :=
    ⟨iProd_mem_orth Js _ fun α h1 h2 => (hJ.1 α h1 h2).1, hsq⟩
  have hanti : ∀ α, 1 ≤ α → α ≤ k → Js α * iProd Js k = -(iProd Js k * Js α) := fun α h1 h2 => by
    rw [jcomm_iProd Js k hJ α h1 h2, hq, show 4 * q + 2 + 1 = 2 * (2 * q + 1) + 1 by ring,
      pow_succ, pow_mul]
    simp
  have hupd : ∀ α, α ≤ k → Function.update Js (k + 1) (iProd Js k) α = Js α := fun α h =>
    Function.update_of_ne (by omega) _ _
  refine ⟨fun α h1 h2 => ?_, fun α β h1 h2 h3 h4 hne => ?_⟩
  · rcases (show α ≤ k ∨ α = k + 1 by omega) with h | rfl
    · rw [hupd α h]; exact hJ.1 α h1 h
    · rw [Function.update_self]; exact hcs
  · rcases (show α ≤ k ∨ α = k + 1 by omega) with ha | rfl <;>
      rcases (show β ≤ k ∨ β = k + 1 by omega) with hb | rfl
    · rw [hupd α ha, hupd β hb]; exact hJ.2 α β h1 ha h3 hb hne
    · rw [hupd α ha, Function.update_self]; exact hanti α h1 ha
    · rw [hupd β hb, Function.update_self, hanti β h3 hb, neg_neg]
    · exact absurd rfl hne

end Extend

/-! ### B ⇒ A, only vacuously

A is quantitative at every stage (`j + 3 ≤ (n/m_{k+1} − |c|)/4`), on the project's path space;
B only asserts that SOME threshold `N(c, d)` exists, on its own path space. A is re-proved
outright: the project's proofs are copied verbatim (they use only non-item lemmas:
`isCentralI_two/six`, `mem_omegaComp_geo_iff`, `isClopen_omegaComp`, `omega_hidx_two`, the
clopen version of Theorem 22.1, `isHomotopyEquiv_omegaPhi_minPaths`, `nonempty_mulEquiv_pathSp`,
`nonempty_pi_stratum_equiv`). -/

section Outright
open Morse
open Matrix Set Filter Topology Module Function
open scoped Morse.MatrixInner RealInnerProductSpace Manifold ContDiff

variable {ι : Type} [Fintype ι] [DecidableEq ι] {J : ℕ → Matrix ι ι ℝ} {k : ℕ}

/-- **Milnor's `i = J_1⋯J_{k−1}` for `k = 2, 6`.** -/
theorem isCentralI_iWordM' (hJ : IsAnticommFamily J (k + 1)) (hk : k = 2 ∨ k = 6) :
    IsCentralI J k (iWordM J k) := by
  rcases hk with rfl | rfl
  · rw [iWordM_two]; exact isCentralI_two (hJ.mono (by norm_num))
  · rw [iWordM_six]; exact isCentralI_six (hJ.mono (by norm_num))

section Stage

variable (hJ : IsAnticommFamily J (k + 1))
include hJ

/-- **The component of `φ_r(J')`**: the angle of `f` along the semicircle through `J'` is
`−π tr(J_kᵀJ'·i)/2`. -/
theorem omegaPhi_mem_omegaComp' (hii : IsCentralI J k (iWordM J k)) (J' : Omega J (k + 1)) :
    (omegaPhi hJ J' : PathSp _ _ _) ∈ omegaComp J k (iWordM J k)
      (-(Real.pi * trace ((basePt J k)ᴴ * (J' : Matrix ι ι ℝ) * iWordM J k)) / 2) := by
  have hJk := hJ.mono k.le_succ
  have hA : (basePt J k)ᴴ * (J' : Matrix ι ι ℝ) ∈ minVelO J k (basePt J k) :=
    (minVelOHomeomorph hJk).symm J' |>.2
  have hV : Real.pi • ((basePt J k)ᴴ * (J' : Matrix ι ι ℝ)) ∈ tanAlg J k (basePt J k) :=
    (tanAlg J k _).smul_mem _ hA.1
  have heq : EqOn (omegaPhi hJ J' : ℝ → Matrix ι ι ℝ)
      (fun t => basePt J k * NormedSpace.exp (t • (Real.pi • ((basePt J k)ᴴ * J'))))
      (Icc 0 1) := fun t _ => by
    rw [omegaPhi_apply, ← omegaGeo_eq_semicircle hJk J'.2 t]
    rfl
  refine (mem_omegaComp_geo_iff hJk hii (omegaPhi hJ J').2 hV heq _).2 ?_
  rw [Matrix.smul_mul, trace_smul, smul_eq_mul]

/-- **Lemma 6.2 on `Ω^{(c)}`, with `π_0`** (Milnor p. 148): the minimal geodesics in `Ω^{(c)}`
include into `Ω^{(c)}` bijectively on `π_j` for `j + 2 ≤ (ν − |c|)/4`. -/
theorem omega_minPaths_bijective_two' (hk : k ≠ 0) (hk8 : k + 1 ≤ 8) (hk3 : k % 4 ≠ 3)
    (hii : IsCentralI J k (iWordM J k)) (c : ℤ) {j : ℕ}
    (hj : j + 2 ≤ (Fintype.card ι / milnorM (k + 1) - c.natAbs) / 4)
    (γ : {γ : minPaths (omegaStratum J k (basePt J k)) (basePt J k) (-basePt J k) |
      (γ : PathSp _ _ _) ∈ omegaComp J k (iWordM J k) (Real.pi * milnorM (k + 1) * c / 2)}) :
    Bijective (Morse.Homotopy.homotopyGroupMap (N := Fin j)
      (clopenIncl (minPaths _ _ _)
        (omegaComp J k (iWordM J k) (Real.pi * milnorM (k + 1) * c / 2))) γ) :=
  theorem_22_1_clopen_bijective
    (isSliceSubmanifold_omegaStratum (hJ.mono k.le_succ) (basePt J k))
    (self_mem_omegaStratum (basePt_mem hJ)) (neg_basePt_mem hJ)
    (fun r => isCompact_closedRiemBall_of_isClosed
      (isSliceSubmanifold_omegaStratum (hJ.mono k.le_succ) (basePt J k))
      (isClosed_omegaStratum (hJ.mono k.le_succ) _) _ r)
    (isClopen_omegaComp (hJ.mono k.le_succ) hk hii _) (omega_hidx_two hJ hk hk8 hk3 hii c)
    (exists_retraction_minPaths_omega (hJ.mono k.le_succ) (basePt_mem hJ) (minVel_base hJ))
    (by simpa using hj) γ

/-- **Theorem 24.5, finite stage, `k ≡ 2 (mod 4)`** (Milnor pp. 147–148): `φ_r` induces
bijections `π_{j+1}(Ω_{k+1}(n), J') → π_{j+1}(Ω(Ω_k(n); J_k, −J_k), φ_r(J'))` whenever
`φ_r(J') ∈ Ω^{(c)}` and `j + 3 ≤ (ν − |c|)/4`, `ν = n/m_{k+1}`. -/
theorem omegaPhi_bijective_two' (hk : k ≠ 0) (hk8 : k + 1 ≤ 8) (hk3 : k % 4 ≠ 3)
    (hii : IsCentralI J k (iWordM J k)) (c : ℤ) {j : ℕ}
    (hj : j + 3 ≤ (Fintype.card ι / milnorM (k + 1) - c.natAbs) / 4) (J' : Omega J (k + 1))
    (hJ' : (omegaPhi hJ J' : PathSp _ _ _) ∈
      omegaComp J k (iWordM J k) (Real.pi * milnorM (k + 1) * c / 2)) :
    Bijective (Morse.Homotopy.homotopyGroupMap (N := Fin (j + 1)) (omegaPhi hJ) J') := by
  obtain ⟨e, he⟩ := isHomotopyEquiv_omegaPhi_minPaths hJ
  have hmem : ((e.toFun J' : minPaths _ _ _) : PathSp _ _ _) ∈
      omegaComp J k (iWordM J k) (Real.pi * milnorM (k + 1) * c / 2) := by
    have := congrFun (congrArg DFunLike.coe he) J'
    simp only [ContinuousMap.comp_apply] at this
    change minPathsIncl _ _ _ (e.toFun J') ∈ _
    rw [this]
    exact hJ'
  rw [← he, Morse.Homotopy.homotopyGroupMap_comp]
  exact (theorem_22_1_clopen_bijective_minPathsIncl
    (isSliceSubmanifold_omegaStratum (hJ.mono k.le_succ) (basePt J k))
    (self_mem_omegaStratum (basePt_mem hJ)) (neg_basePt_mem hJ)
    (fun r => isCompact_closedRiemBall_of_isClosed
      (isSliceSubmanifold_omegaStratum (hJ.mono k.le_succ) (basePt J k))
      (isClosed_omegaStratum (hJ.mono k.le_succ) _) _ r)
    (isClopen_omegaComp (hJ.mono k.le_succ) hk hii _) (omega_hidx_two hJ hk hk8 hk3 hii c)
    (exists_retraction_minPaths_omega (hJ.mono k.le_succ) (basePt_mem hJ) (minVel_base hJ))
    (K := Fin (j + 1)) (by simpa using hj) _ hmem).comp
    (Morse.Homotopy.bijective_homotopyGroupMap_of_homotopyEquiv e J')

/-- **Theorem 24.5, finite stage, for `k = 2, 6`** (Milnor pp. 147–148): `φ_r` is bijective on
`π_{j+1}` at every `J' ∈ Ω_{k+1}(n)^{(c)}` for `j + 3 ≤ (n/m_k − |c|)/4`. -/
theorem theorem_24_5_two_six' (hk : k = 2 ∨ k = 6) (c : ℤ) {j : ℕ}
    (hj : j + 3 ≤ (Fintype.card ι / milnorM (k + 1) - c.natAbs) / 4) (J' : Omega J (k + 1))
    (hJ' : (omegaPhi hJ J' : PathSp _ _ _) ∈
      omegaComp J k (iWordM J k) (Real.pi * milnorM (k + 1) * c / 2)) :
    Bijective (Morse.Homotopy.homotopyGroupMap (N := Fin (j + 1)) (omegaPhi hJ) J') :=
  omegaPhi_bijective_two' hJ (by omega) (by omega) (by omega) (isCentralI_iWordM' hJ hk) c hj J' hJ'

/-- **Theorem 24.5, finite stage, `k ≡ 2 (mod 4)`, as Milnor's isomorphism** (pp. 147–148 with
Corollary 22.2): `π_{j+1}(Ω_{k+1}(n), J') ≅ π_{j+2}(Ω_k(n), J_k)` (as sets) for
`φ_r(J') ∈ Ω^{(c)}` and `j + 3 ≤ (n/m_{k+1} − |c|)/4`. -/
theorem omega_pi_equiv_two' (hk : k ≠ 0) (hk8 : k + 1 ≤ 8) (hk3 : k % 4 ≠ 3)
    (hii : IsCentralI J k (iWordM J k)) (c : ℤ) {j : ℕ}
    (hj : j + 3 ≤ (Fintype.card ι / milnorM (k + 1) - c.natAbs) / 4) (J' : Omega J (k + 1))
    (hJ' : (omegaPhi hJ J' : PathSp _ _ _) ∈
      omegaComp J k (iWordM J k) (Real.pi * milnorM (k + 1) * c / 2)) :
    Nonempty (π_ (j + 1) (Omega J (k + 1)) J' ≃
      π_ (j + 2) (Omega J k) ⟨basePt J k, basePt_mem hJ⟩) := by
  have e₁ := Equiv.ofBijective _ (omegaPhi_bijective_two' hJ hk hk8 hk3 hii c hj J' hJ')
  obtain ⟨e₂⟩ := nonempty_mulEquiv_pathSp
    (isSliceSubmanifold_omegaStratum (hJ.mono k.le_succ) (basePt J k))
    (self_mem_omegaStratum (basePt_mem hJ)) (neg_basePt_mem hJ) j (omegaPhi hJ J')
  obtain ⟨e₃⟩ := nonempty_pi_stratum_equiv (hJ.mono k.le_succ)
    (self_mem_omegaStratum (basePt_mem hJ)) (j + 1)
  exact ⟨e₁.trans (e₂.toEquiv.trans e₃)⟩

end Stage

end Outright

theorem B_to_A : B → A := fun _ =>
  ⟨@isCentralI_iWordM', @omegaPhi_mem_omegaComp', @omega_minPaths_bijective_two',
    @omegaPhi_bijective_two', @theorem_24_5_two_six', @omega_pi_equiv_two'⟩

#rt_check RoundTrip.V15_39.B_to_A [Morse.isCentralI_iWordM, Morse.omegaPhi_mem_omegaComp,
  Morse.omega_minPaths_bijective_two, Morse.omegaPhi_bijective_two, Morse.theorem_24_5_two_six,
  Morse.omega_pi_equiv_two]
#rt_overlap RoundTrip.V15_39.B_to_A [Morse.isCentralI_iWordM, Morse.omegaPhi_mem_omegaComp,
  Morse.omega_minPaths_bijective_two, Morse.omegaPhi_bijective_two, Morse.theorem_24_5_two_six,
  Morse.omega_pi_equiv_two]

end RoundTrip.V15_39
