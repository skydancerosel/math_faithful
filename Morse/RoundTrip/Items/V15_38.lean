import Morse
import RoundTrip.Check
import RoundTrip.Blind.V15_38

namespace RoundTrip.V15_38

/-- The project's statement (universes instantiated at `0`): the algebra of the intertwiners
(`IsInterRelI.commute_exp`: `D·ii` commutes with `exp(sA)` when `a s ≡ b s (mod 2π)`;
`exists_killing_spaces_two`: from intertwiners `D_i` between a piece with `a₀` and pieces with
`b_i < a₀`, Killing fields in `isoAlg` with conjugate parameters `τ ∈ (0, 1)` of total multiplicity
`Σ_i ((a₀ − b_i)/2 − 1)`), and the index bound for `k ≡ 2 (mod 4)` (`k ≠ 0`, `k + 1 ≤ 8`,
`k ≢ 3 (mod 4)`, `IsCentralI J k (J_1⋯J_{k−1})`): an unbroken geodesic `γ` from `J_k` to `−J_k`
in the stratum of `J_k`, NOT of least energy, lying in `omegaComp` with angle `π m_{k+1} c/2`,
has `⌊(ν − |c|)/4⌋ ≤ formIndex (energyHessian γ)` where `ν m_{k+1} = n` (two forms). -/
def A : Prop :=
  type_of% @Morse.IsInterRelI.commute_exp.{0} ∧ type_of% @Morse.exists_killing_spaces_two.{0, 0} ∧
    type_of% @Morse.le_formIndex_of_not_minimal_omega_two.{0} ∧ type_of% @Morse.omega_hidx_two.{0}

theorem A_holds : A :=
  ⟨@Morse.IsInterRelI.commute_exp.{0}, @Morse.exists_killing_spaces_two.{0, 0},
    @Morse.le_formIndex_of_not_minimal_omega_two.{0}, @Morse.omega_hidx_two.{0}⟩

/-! A ⇒ B is not proved (see `V15_38.json`): A's index is the project's
`formIndex (energyHessian _ hγ)` on the stratum (slice-submanifold calculus), B's is the blind
`idxIn (Ω_k(n)) γ` (second derivatives of energies of hand-built variations); no dictionary
between them exists. A's bound is `⌊(ν − |c|)/4⌋ ≤ λ` for non-minimal geodesics only; B's is
Milnor's `2λ ≥ Σ_{a_h > a_j} (a_h − a_j − 2)` for every geodesic `J exp(πtA)` of a given splitting
(and `4λ ≥ r + c` when some `a_h = −3`, and `n = r m_k`). -/

/-! ### B ⇒ A, only vacuously

A's index is `formIndex (energyHessian _)` of the project's path space; B's is the blind `idxIn`;
B has no Killing fields and says nothing about the project's index, so nothing of A follows
from B. A is re-proved outright: the project's proofs are copied verbatim (the chain
`commute_exp → exists_killing_spaces_two → killing_of_twoPieceData → le_formIndex… →
omega_hidx_two`, renamed; otherwise only non-item lemmas: `IsInterRelI.mul_exp/exp_mul`,
`exists_killing_spaces_gen`, `exists_decomp_two`, `exists_twoPieceData_of_decomp`, the index
theorem for `formIndex`, …). -/

section Outright
open Morse
open Matrix Set Filter Topology Module Function
open scoped Morse.MatrixInner RealInnerProductSpace Manifold ContDiff

variable {ι : Type} [Fintype ι] [DecidableEq ι] {J : ℕ → Matrix ι ι ℝ} {k : ℕ}

/-- **`Di` commutes with `exp(sA)` when `s(a − b) ∈ 2πℤ`** (the conjugate points
`t = 2m/(a − b)` of Milnor p. 148). -/
theorem commute_exp' {A ii D : Matrix ι ι ℝ} {a b : ℝ} (h : IsInterRelI A ii D a b) (hii : ii * ii = -1)
    (hAi : A * ii = ii * A) {s : ℝ} {m : ℤ} (hs : a * s = b * s + m * (2 * Real.pi)) :
    D * ii * NormedSpace.exp (s • A) = NormedSpace.exp (s • A) * (D * ii) := by
  have hc : Commute ii (s • A) := (show Commute ii A from hAi.symm).smul_right s
  have hcomm : ii * NormedSpace.exp (s • A) = NormedSpace.exp (s • A) * ii := hc.exp_right.eq
  rw [Matrix.mul_assoc, hcomm, ← Matrix.mul_assoc, h.mul_exp hii hAi, ← Matrix.mul_assoc,
    h.exp_mul hii hAi, hs, Real.cos_add_int_mul_two_pi, Real.sin_add_int_mul_two_pi, h.di]

/-- **The Killing fields of the pairs `(h₀, j)`** (Milnor p. 148): `X_j = D_ji − (D_ji)ᵀ`, with
the parameters `τ_{j,s} = 2(s + 1)/(a₀ − b_j)`, `s < (a₀ − b_j)/2 − 1`, give spaces `𝒳_τ` of
total dimension `Σ_j ((a₀ − b_j)/2 − 1)` for `V = πA`. -/
theorem exists_killing_spaces_two' {A ii : Matrix ι ι ℝ} (hA : Aᴴ = -A) (hii : ii * ii = -1)
    (hiiH : iiᴴ = -ii) (hAi : A * ii = ii * A) {κ : Type*} [Fintype κ] [DecidableEq κ]
    (D : κ → Matrix ι ι ℝ) (a₀ : ℤ) (b : κ → ℤ) (hb : ∀ i, b i < a₀)
    (heven : ∀ i, Even (a₀ - b i)) (hrel : ∀ i, IsInterRelI A ii (D i) a₀ (b i))
    (R : Matrix ι ι ℝ) (hR : ∀ i, D i * R = D i) (hR' : ∀ i, (D i)ᴴ * R = 0)
    (hRA : R * A = A * R) (hRi : R * ii = ii * R) (Q : κ → Matrix ι ι ℝ)
    (hQ : ∀ j' i, Q j' * D i = if i = j' then D i else 0) (hD0 : ∀ i, D i ≠ 0)
    (hiso : ∀ i, D i * ii - (D i * ii)ᴴ ∈ isoAlg J k p) :
    ∃ (T : Finset ℝ) (𝒳 : ℝ → Submodule ℝ (Matrix ι ι ℝ)), (∀ τ ∈ T, τ ∈ Ioo (0 : ℝ) 1) ∧
      (∀ τ ∈ T, 𝒳 τ ≤ isoAlg J k p) ∧
      (∀ τ ∈ T, ∀ Y ∈ 𝒳 τ, Y * NormedSpace.exp (τ • (Real.pi • A)) =
        NormedSpace.exp (τ • (Real.pi • A)) * Y) ∧
      (∀ τ ∈ T, ∀ Y ∈ 𝒳 τ, Y * (Real.pi • A) = (Real.pi • A) * Y → Y = 0) ∧
      ∑ τ ∈ T, finrank ℝ (𝒳 τ) = ∑ i, ((a₀ - b i) / 2 - 1).toNat := by
  classical
  set X : κ → Matrix ι ι ℝ := fun i => D i * ii - (D i * ii)ᴴ with hXdef
  have hrelH : ∀ i, IsInterRelI A ii (D i)ᴴ (b i) a₀ := fun i => (hrel i).conjTranspose hA hiiH
  have hX : ∀ i, X i = D i * ii + (D i)ᴴ * ii := fun i => by
    change D i * ii - (D i * ii)ᴴ = _
    rw [conjTranspose_mul, hiiH, Matrix.neg_mul, (hrelH i).di, sub_neg_eq_add]
  -- `[X_i, A] R = (b_i − a₀) D_i`
  have hXR : ∀ i, (X i * A - A * X i) * R = ((b i : ℝ) - a₀) • D i := fun i => by
    have e1 : X i * R = D i * ii := by
      rw [hX, Matrix.add_mul, Matrix.mul_assoc, ← hRi, ← Matrix.mul_assoc, hR,
        Matrix.mul_assoc (D i)ᴴ, ← hRi, ← Matrix.mul_assoc, hR', Matrix.zero_mul, add_zero]
    have e2 : X i * A * R = -((a₀ : ℝ) • D i) := by
      rw [Matrix.mul_assoc, ← hRA, ← Matrix.mul_assoc, e1, Matrix.mul_assoc, ← hAi,
        ← Matrix.mul_assoc, (hrel i).da, Matrix.smul_mul, Matrix.mul_assoc, hii, Matrix.mul_neg,
        Matrix.mul_one, smul_neg]
    have e3 : A * X i * R = -((b i : ℝ) • D i) := by
      rw [Matrix.mul_assoc, e1, ← Matrix.mul_assoc, (hrel i).ad, Matrix.smul_mul,
        Matrix.mul_assoc, (hrel i).di, ← Matrix.mul_assoc, hii, Matrix.neg_mul, Matrix.one_mul,
        smul_neg]
    rw [Matrix.sub_mul, e2, e3, sub_smul]
    abel
  have hind : LinearIndependent ℝ fun i => adR (Real.pi • A) (X i) := by
    rw [Fintype.linearIndependent_iff]
    intro c hc j'
    have h1 := congrArg (fun M => Q j' * (M * R)) hc
    simp only [Matrix.zero_mul, Matrix.mul_zero, Finset.sum_mul, Matrix.mul_sum,
      Matrix.smul_mul, Matrix.mul_smul] at h1
    have h2 : ∀ i, adR (Real.pi • A) (X i) * R = (Real.pi * ((b i : ℝ) - a₀)) • D i := fun i => by
      simp only [adR, LinearMap.coe_mk, AddHom.coe_mk, Matrix.mul_smul, Matrix.smul_mul,
        ← smul_sub]
      rw [hXR i, smul_smul]
    simp only [h2, Matrix.mul_smul, hQ, smul_ite, smul_zero] at h1
    rw [Finset.sum_eq_single j' (fun i _ hi => if_neg hi) (fun h => absurd (Finset.mem_univ _) h),
      if_pos rfl, smul_smul] at h1
    have hne : c j' * (Real.pi * ((b j' : ℝ) - a₀)) ≠ 0 → False := fun h0 =>
      hD0 j' ((smul_eq_zero.1 h1).resolve_left h0)
    by_contra hcj
    apply hne
    have hb' : ((b j' : ℝ) - a₀) ≠ 0 := by
      have : (b j' : ℝ) < a₀ := by exact_mod_cast hb j'
      linarith
    exact mul_ne_zero hcj (mul_ne_zero Real.pi_ne_zero hb')
  set n : κ → ℕ := fun i => ((a₀ - b i) / 2 - 1).toNat with hndef
  set τf : (Σ i, Fin (n i)) → ℝ := fun x => 2 * ((x.2 : ℝ) + 1) / ((a₀ : ℝ) - b x.1) with hτdef
  have hpos : ∀ i, (0 : ℝ) < (a₀ : ℝ) - b i := fun i => by
    have : (b i : ℝ) < a₀ := by exact_mod_cast hb i
    linarith
  have hlt : ∀ x : (Σ i, Fin (n i)), 2 * ((x.2 : ℝ) + 1) < (a₀ : ℝ) - b x.1 := fun x => by
    obtain ⟨m, hm⟩ := heven x.1
    have h2 := x.2.2
    simp only [hndef] at h2
    rw [hm, show (m + m) / 2 = m by omega] at h2
    have h3 : 2 * ((x.2 : ℕ) : ℤ) + 2 < m + m := by omega
    have h4 : (a₀ : ℝ) - b x.1 = ((m + m : ℤ) : ℝ) := by rw [← hm]; push_cast; ring
    rw [h4]
    have h5 : 2 * (((x.2 : ℕ) : ℤ) : ℝ) + 2 < ((m + m : ℤ) : ℝ) := by exact_mod_cast h3
    push_cast at h5 ⊢
    linarith
  obtain ⟨T, 𝒳, h1, h2, h3, h4, h5⟩ := exists_killing_spaces_gen (V := Real.pi • A) X hiso hind
    n τf (fun x => ⟨div_pos (by positivity) (hpos x.1),
      (div_lt_one (hpos x.1)).2 (hlt x)⟩)
    (fun i s s' hss' => by
      simp only [hτdef] at hss'
      rw [div_left_inj' (hpos i).ne'] at hss'
      exact Fin.ext (by exact_mod_cast (show (s : ℝ) = s' by linarith)))
    (fun x => by
      have hs : (a₀ : ℝ) * (τf x * Real.pi) =
          (b x.1 : ℝ) * (τf x * Real.pi) + ((x.2 : ℕ) + 1 : ℤ) * (2 * Real.pi) := by
        simp only [hτdef]; push_cast; field_simp [(hpos x.1).ne']; ring
      have hs' : (b x.1 : ℝ) * (τf x * Real.pi) =
          (a₀ : ℝ) * (τf x * Real.pi) + ((-(((x.2 : ℕ) : ℤ) + 1) : ℤ) : ℝ) * (2 * Real.pi) := by
        rw [hs]; push_cast; ring
      have c1 := commute_exp' (hrel x.1) hii hAi hs
      have c2 := commute_exp' (hrelH x.1) hii hAi hs'
      rw [smul_smul, hX, Matrix.add_mul, Matrix.mul_add, c1, c2])
  exact ⟨T, 𝒳, h1, h2, h3, h4, h5⟩


/-- **The Killing fields from the data** (`Morse.TwoPieceData`, transported to matrices). -/
theorem killing_of_twoPieceData' (hJ : IsAnticommFamily J k) (hk : k ≠ 0)
    (hii : IsCentralI J k (iWordM J k)) {A' : Matrix ι ι ℝ}
    (hA' : A' ∈ tanAlg J k (basePt J k)) {a : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι}
    (ha : a = matE ι A') {κ : Type} [Fintype κ] [DecidableEq κ]
    (pd : TwoPieceData k a (matE ι (basePt J k)) (fun α => matE ι (J α)) κ) :
    ∃ (T : Finset ℝ) (𝒳 : ℝ → Submodule ℝ (Matrix ι ι ℝ)), (∀ τ ∈ T, τ ∈ Ioo (0 : ℝ) 1) ∧
      (∀ τ ∈ T, 𝒳 τ ≤ isoAlg J k (basePt J k)) ∧
      (∀ τ ∈ T, ∀ Y ∈ 𝒳 τ, Y * NormedSpace.exp (τ • (Real.pi • A')) =
        NormedSpace.exp (τ • (Real.pi • A')) * Y) ∧
      (∀ τ ∈ T, ∀ Y ∈ 𝒳 τ, Y * (Real.pi • A') = (Real.pi • A') * Y → Y = 0) ∧
      ∑ τ ∈ T, finrank ℝ (𝒳 τ) = ∑ i, ((pd.a₀ - pd.b i) / 2 - 1).toNat := by
  subst ha
  set ii := iWordM J k
  set D : κ → Matrix ι ι ℝ := fun i => (matE ι).symm (pd.d i) with hD
  have hDe : ∀ i, matE ι (D i) = pd.d i := fun i => by simp [hD]
  have hDH : ∀ i, matE ι (D i)ᴴ = ContinuousLinearMap.adjoint (pd.d i) := fun i => by
    rw [matE_conjTranspose, hDe]
  set R : Matrix ι ι ℝ := (matE ι).symm pd.R with hRdef
  have hRe : matE ι R = pd.R := by simp [hRdef]
  set Q : κ → Matrix ι ι ℝ := fun j' => (matE ι).symm (pd.Q j') with hQdef
  have hQe : ∀ j', matE ι (Q j') = pd.Q j' := fun j' => by simp [hQdef]
  have hie : iWord k (fun α => matE ι (J α)) = matE ι ii := iWord_matE
  have hiiH : iiᴴ = -ii := by rw [conjTranspose_real]; exact hii.skew
  have hAi : A' * ii = ii * A' := hii.comm A' hA'.2.2
  have hDJ : ∀ i α, 1 ≤ α → α < k → D i * J α = J α * D i := fun i α h1 h2 => matE_inj (by
    rw [matE_mul, matE_mul, hDe]; exact pd.hj i α h1 h2)
  have hDi : ∀ i, D i * ii = ii * D i := fun i => matE_inj (by
    rw [matE_mul, matE_mul, hDe, ← hie]; exact commute_iWord (pd.hj i))
  have hrel : ∀ i, IsInterRelI A' ii (D i) pd.a₀ (pd.b i) := fun i =>
    { da := matE_inj (by rw [matE_mul, matE_smul, matE_mul, hDe, ← hie]; exact pd.da i)
      ad := matE_inj (by rw [matE_mul, matE_smul, matE_mul, hDe, ← hie]; exact pd.ad i)
      di := hDi i }
  have hiso : ∀ i, D i * ii - (D i * ii)ᴴ ∈ isoAlg J k (basePt J k) := fun i =>
    sub_conjTranspose_mem_isoAlg hJ hk hii (matE_inj (by
      rw [matE_mul, matE_neg, matE_mul, hDe]; exact pd.hq i)) (hDJ i)
  exact exists_killing_spaces_two' hA'.1 hii.sq hiiH hAi D pd.a₀ pd.b
    (fun i => by linarith [pd.ha₀, pd.hb i]) pd.heven hrel R
    (fun i => matE_inj (by rw [matE_mul, hDe, hRe]; exact pd.hR i))
    (fun i => matE_inj (by rw [matE_mul, hDH, hRe, matE_zero]; exact pd.hR' i))
    (matE_inj (by rw [matE_mul, matE_mul, hRe]; exact pd.Ra))
    (matE_inj (by rw [matE_mul, matE_mul, hRe, ← hie]; exact pd.Re)) Q
    (fun j' i => matE_inj (by
      rw [matE_mul, hQe, hDe, pd.hQ j' i]
      split_ifs
      · rw [hDe]
      · rw [matE_zero]))
    (fun i h0 => pd.hne i (by rw [← hDe, h0, matE_zero])) hiso

/-- **The index bound for `k ≡ 2 (mod 4)`** (Milnor p. 148): a geodesic from `J_k` to `−J_k` in
`Ω^{(c)}` which is not of least energy has index `≥ (ν − |c|)/4`, where `n = ν · m_{k+1}`. -/
theorem le_formIndex_of_not_minimal_omega_two' (hJ : IsAnticommFamily J k) (hk : k ≠ 0)
    (hk8 : k + 1 ≤ 8) (hk3 : k % 4 ≠ 3) (hii : IsCentralI J k (iWordM J k)) {A₀ : Matrix ι ι ℝ}
    (hA₀ : A₀ ∈ minVelO J k (basePt J k)) {γ : ℝ → Matrix ι ι ℝ}
    (hγ : γ ∈ pathSpace (omegaStratum J k (basePt J k)) (basePt J k) (-basePt J k))
    (hgeo : IsUnbrokenGeodesic (isSliceSubmanifold_omegaStratum hJ (basePt J k)) γ)
    (hnm : ∃ γ' ∈ pathSpace (omegaStratum J k (basePt J k)) (basePt J k) (-basePt J k),
      energy γ' 0 1 < energy γ 0 1) {c : ℤ}
    (hc : (⟨γ, hγ⟩ : PathSp _ _ _) ∈
      omegaComp J k (iWordM J k) (Real.pi * milnorM (k + 1) * c / 2)) :
    ∃ ν : ℕ, ν * milnorM (k + 1) = Fintype.card ι ∧
      (((ν - c.natAbs) / 4 : ℕ) : ℕ∞) ≤
        formIndex (energyHessian (isSliceSubmanifold_omegaStratum hJ (basePt J k)) hγ) := by
  classical
  set p := basePt J k with hpdef
  set ii := iWordM J k
  have hp : p ∈ Omega J k := basePt_mem_omega hJ
  have hpo := omega_orth hp
  have hT := isTotGeo_omegaStratum hJ p
  obtain ⟨V, hV, heq⟩ := hT.eqOn_of_isUnbrokenGeodesic hγ hgeo
  have hexpV : NormedSpace.exp V = -1 := by
    have h1 := heq ⟨zero_le_one, le_rfl⟩
    rw [hγ.2.2.2] at h1
    simp only [one_smul] at h1
    have := congrArg (pᴴ * ·) h1
    simpa only [← Matrix.mul_assoc, hpo, Matrix.one_mul, Matrix.mul_neg] using this.symm
  set A := Real.pi⁻¹ • V with hAdef
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  have hVA : Real.pi • A = V := by rw [hAdef, smul_smul, mul_inv_cancel₀ hπ, one_smul]
  have hA : A ∈ tanAlg J k p := (tanAlg J k p).smul_mem _ hV
  have hexpA : NormedSpace.exp (Real.pi • A) = -1 := by rw [hVA, hexpV]
  have hnmA : A * A ≠ -1 := by
    intro hsq
    obtain ⟨γ', hγ', hlt⟩ := hnm
    have hVV : V * V = -(Real.pi ^ 2) • (1 : Matrix ι ι ℝ) := by
      rw [← hVA, Matrix.smul_mul, Matrix.mul_smul, hsq, smul_smul, smul_neg, ← neg_smul, sq]
    have hE : energy γ 0 1 = Real.pi ^ 2 * Fintype.card ι := by
      rw [energy_congr heq, IsTotGeo.energy_mul_exp_smul hpo hV.1, norm_sq_of_sq_eq hV.1 hVV]
    have := pi_sq_card_le_energy hJ hp hA₀ hγ'
    linarith
  -- the component: `tr(A·i) = −m c`
  set m := milnorM (k + 1)
  have htr : trace (A * ii) = -((m : ℝ) * c) := by
    have h1 := (mem_omegaComp_geo_iff hJ hii hγ hV heq _).1 hc
    rw [← hVA, Matrix.smul_mul, trace_smul, smul_eq_mul] at h1
    have h2 : Real.pi * (trace (A * ii) + m * c) = 0 := by linarith
    have h3 := (mul_eq_zero.1 h2).resolve_left hπ
    linarith
  -- the operators
  have hops := isOmegaOps_matE hJ hA
  have hI := isIOps_matE hJ hk hii hA
  have hie : iWord k (fun α => matE ι (J α)) = matE ι ii := iWord_matE
  have hiiH : iiᴴ = -ii := by rw [conjTranspose_real]; exact hii.skew
  have hodd : ∀ M : Submodule ℝ (EuclideanSpace ℝ ι),
      IsMinInvar (omegaGens k (matE ι A) (matE ι p) (fun α => matE ι (J α))) M → ∀ c' : ℝ,
      (∀ v ∈ M, matE ι A v = c' • iWord k (fun α => matE ι (J α)) v) →
      ∃ n : ℤ, c' = 2 * n + 1 := by
    intro M hM c' hc'
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hM.1
    refine exists_odd_of_mulVec hiiH hii.sq (hii.comm A hA.2.2) hexpA (w := WithLp.ofLp v) ?_ ?_
    · intro h0; exact hv0 (by simpa using congrArg (WithLp.toLp 2) h0)
    · have := congrArg WithLp.ofLp (hc' v hv)
      rw [hie] at this
      simpa using this
  obtain ⟨L, cs, hmin, horth, hcs, hoddcs, hdim, htrace, hall⟩ :=
    exists_decomp_two hops hI hk hk8 hodd
  rw [finrank_euclideanSpace] at hdim
  have hsum : ∑ i, cs i = c := by
    rw [hie, ← map_mul, trace_matE, htr] at htrace
    have hm : (m : ℝ) ≠ 0 := by have := milnorM_pos (k + 1); positivity
    have h1 : ((∑ i, cs i : ℤ) : ℝ) = c := by
      push_cast
      have := mul_left_cancel₀ hm (neg_inj.1 htrace)
      linarith
    exact_mod_cast h1
  -- some `|a_h| ≥ 3`
  have hnm' : matE ι A * matE ι A ≠ -1 := fun h0 => hnmA (matE_inj (by
    rw [matE_mul, h0, matE_neg, map_one]))
  obtain ⟨i₀, hi₀⟩ : ∃ i₀, cs i₀ ^ 2 ≠ 1 := by
    by_contra hcon
    push Not at hcon
    exact hnm' (hall hcon)
  have h3 : 3 ≤ cs i₀ ∨ cs i₀ ≤ -3 := by
    obtain ⟨n, hn⟩ := hoddcs i₀
    rw [hn] at hi₀ ⊢
    have h0 : n ≠ 0 := by rintro rfl; simp at hi₀
    have h1 : n ≠ -1 := by rintro rfl; simp at hi₀
    omega
  -- the Killing fields, for `A` or for `−A`
  obtain ⟨T, 𝒳, s, h1, h2, h3', h4, h5, hcount⟩ : ∃ (T : Finset ℝ)
      (𝒳 : ℝ → Submodule ℝ (Matrix ι ι ℝ)) (s : ℕ), (∀ τ ∈ T, τ ∈ Ioo (0 : ℝ) 1) ∧
      (∀ τ ∈ T, 𝒳 τ ≤ isoAlg J k p) ∧
      (∀ τ ∈ T, ∀ Y ∈ 𝒳 τ, Y * NormedSpace.exp (τ • V) = NormedSpace.exp (τ • V) * Y) ∧
      (∀ τ ∈ T, ∀ Y ∈ 𝒳 τ, Y * V = V * Y → Y = 0) ∧
      ∑ τ ∈ T, finrank ℝ (𝒳 τ) = s ∧ (L.length : ℤ) - |c| ≤ 4 * s := by
    rcases h3 with h3 | h3
    · obtain ⟨κ, _, _, pd, hle⟩ :=
        exists_twoPieceData_of_decomp hops hI hk (by omega) hk3 hmin horth hcs hoddcs h3
      obtain ⟨T, 𝒳, h1, h2, h3, h4, h5⟩ := killing_of_twoPieceData' hJ hk hii hA rfl pd
      refine ⟨T, 𝒳, _, h1, h2, fun τ hτ Y hY => ?_, fun τ hτ Y hY hc => ?_, h5, ?_⟩
      · rw [← hVA]; exact h3 τ hτ Y hY
      · rw [← hVA] at hc; exact h4 τ hτ Y hY hc
      · have hpos : ∀ i, 0 ≤ (pd.a₀ - pd.b i) / 2 - 1 := fun i => by
          obtain ⟨m', hm'⟩ := pd.heven i
          rw [hm', show (m' + m') / 2 = m' by omega]
          have := pd.ha₀; have := pd.hb i; omega
        push_cast
        rw [Finset.sum_congr rfl fun i _ => Int.toNat_of_nonneg (hpos i), ← hsum]
        have : -|∑ i, cs i| ≤ -∑ i, cs i := neg_le_neg (le_abs_self _)
        linarith
    · have hmin' := fun i => isMinInvar_omegaGens_neg_a (hmin i)
      have hcs' : ∀ i, ∀ v ∈ L.get i, (-matE ι A) v = ((-cs i : ℤ) : ℝ) • iWord k
          (fun α => matE ι (J α)) v := fun i v hv => by
        change -(matE ι A v) = _
        rw [hcs i v hv]; push_cast; rw [neg_smul]
      obtain ⟨κ, _, _, pd, hle⟩ := exists_twoPieceData_of_decomp hops.neg_a hI.neg_a hk
        (by omega) hk3 hmin' (fun i i' h => horth i i' h) hcs' (fun i => (hoddcs i).neg)
        (i₀ := i₀) (by omega)
      have hA' : -A ∈ tanAlg J k p := (tanAlg J k p).neg_mem hA
      obtain ⟨T, 𝒳, h1, h2, h3, h4, h5⟩ :=
        killing_of_twoPieceData' hJ hk hii hA' (map_neg _ _).symm pd
      have hV' : Real.pi • -A = -V := by rw [smul_neg, hVA]
      refine ⟨T, 𝒳, _, h1, h2, fun τ hτ Y hY => ?_, fun τ hτ Y hY hc => ?_, h5, ?_⟩
      · have e := h3 τ hτ Y hY
        rw [hV', smul_neg] at e
        have hinv : NormedSpace.exp (τ • V) * NormedSpace.exp (-(τ • V)) = 1 :=
          exp_mul_exp_neg _
        have hinv' : NormedSpace.exp (-(τ • V)) * NormedSpace.exp (τ • V) = 1 := by
          have := exp_mul_exp_neg (-(τ • V)); rwa [neg_neg] at this
        calc Y * NormedSpace.exp (τ • V)
            = NormedSpace.exp (τ • V) * (NormedSpace.exp (-(τ • V)) * Y) *
              NormedSpace.exp (τ • V) := by
                rw [← Matrix.mul_assoc, hinv, Matrix.one_mul]
          _ = NormedSpace.exp (τ • V) * (Y * NormedSpace.exp (-(τ • V))) *
              NormedSpace.exp (τ • V) := by rw [e]
          _ = NormedSpace.exp (τ • V) * Y := by
                rw [Matrix.mul_assoc, Matrix.mul_assoc, hinv', Matrix.mul_one]
      · refine h4 τ hτ Y hY ?_
        rw [hV', Matrix.mul_neg, Matrix.neg_mul, hc]
      · have hpos : ∀ i, 0 ≤ (pd.a₀ - pd.b i) / 2 - 1 := fun i => by
          obtain ⟨m', hm'⟩ := pd.heven i
          rw [hm', show (m' + m') / 2 = m' by omega]
          have := pd.ha₀; have := pd.hb i; omega
        push_cast
        rw [Finset.sum_congr rfl fun i _ => Int.toNat_of_nonneg (hpos i)]
        have e : ∑ i, -cs i = -c := by rw [Finset.sum_neg_distrib, hsum]
        rw [e] at hle
        have : -|c| ≤ c := neg_abs_le c
        linarith
  refine ⟨L.length, hdim, ?_⟩
  have hidx := sum_finrank_le_formIndex hJ hp hγ hgeo hV heq T h1 𝒳 h2 h3' h4
  rw [h5] at hidx
  refine le_trans ?_ hidx
  have : (L.length - c.natAbs) / 4 ≤ s := by
    have hc' : (|c| : ℤ) = (c.natAbs : ℤ) := Int.abs_eq_natAbs c
    omega
  exact_mod_cast this


section Stage
variable (hJ : IsAnticommFamily J (k + 1))
include hJ

/-- **The index hypothesis of Lemma 6.2 on `Ω^{(c)}`**, `λ₀ = (n/m_{k+1} − |c|)/4`. -/
theorem omega_hidx_two' (hk : k ≠ 0) (hk8 : k + 1 ≤ 8) (hk3 : k % 4 ≠ 3)
    (hii : IsCentralI J k (iWordM J k)) (c : ℤ) :
    ∀ γ (hγ : γ ∈ pathSpace (omegaStratum J k (basePt J k)) (basePt J k) (-basePt J k)),
      (⟨γ, hγ⟩ : PathSp _ _ _) ∈
        omegaComp J k (iWordM J k) (Real.pi * milnorM (k + 1) * c / 2) →
      IsUnbrokenGeodesic (isSliceSubmanifold_omegaStratum (hJ.mono k.le_succ) (basePt J k)) γ →
      (∃ γ' ∈ pathSpace (omegaStratum J k (basePt J k)) (basePt J k) (-basePt J k),
        energy γ' 0 1 < energy γ 0 1) →
      (((Fintype.card ι / milnorM (k + 1) - c.natAbs) / 4 : ℕ) : ℕ∞) ≤
        formIndex (energyHessian
          (isSliceSubmanifold_omegaStratum (hJ.mono k.le_succ) (basePt J k)) hγ) := by
  intro γ hγ hc hgeo hnm
  obtain ⟨ν, hν, hle⟩ := le_formIndex_of_not_minimal_omega_two' (hJ.mono k.le_succ) hk hk8 hk3
    hii (minVel_base hJ) hγ hgeo hnm hc
  have hdiv : Fintype.card ι / milnorM (k + 1) = ν := by
    rw [← hν, Nat.mul_div_cancel _ (milnorM_pos _)]
  rw [hdiv]
  exact hle


end Stage

end Outright

theorem B_to_A : B → A := fun _ =>
  ⟨@commute_exp', @exists_killing_spaces_two', @le_formIndex_of_not_minimal_omega_two',
    @omega_hidx_two'⟩

#rt_check RoundTrip.V15_38.B_to_A [Morse.IsInterRelI.commute_exp, Morse.exists_killing_spaces_two,
  Morse.le_formIndex_of_not_minimal_omega_two, Morse.omega_hidx_two]
#rt_overlap RoundTrip.V15_38.B_to_A [Morse.IsInterRelI.commute_exp, Morse.exists_killing_spaces_two,
  Morse.le_formIndex_of_not_minimal_omega_two, Morse.omega_hidx_two]

end RoundTrip.V15_38
