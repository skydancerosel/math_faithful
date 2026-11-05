import Morse.Chapter15.KillingTwo
import Morse.Chapter15.OmegaWinding

/-!
Milnor, *Morse Theory*, §24, pp. 147–148; Exposition/Chapter15.md, §6, case `k ≡ 2 (mod 4)`.

# The index of non-minimal geodesics in `Ω^{(c)}`, `k ≡ 2 (mod 4)`

## Milnor's text, paraphrased

(p. 148) "A non-minimal geodesic in `Ω^{(c)}` has index `λ ≥ (ν − |c|)/4`", where `ν = n/m_k`
is the number of minimal pieces.

## What is formalized

For `k ≠ 0`, `k + 1 ≤ 8`, `k ≢ 3 (mod 4)` and `IsCentralI J k (J_1⋯J_{k−1})` (true for `k = 2`,
`6`: `Morse.isCentralI_two`, `Morse.isCentralI_six`):

* `Morse.exists_odd_of_mulVec`: `Av = c·iv`, `v ≠ 0`, `exp(πA) = −I` force `c` to be an odd
  integer (`exp(tA)v = cos(ct)v + sin(ct)iv`).
* `Morse.iWord_matE`, `Morse.isIOps_matE`: Milnor's `i` as an operator.
* **`Morse.le_formIndex_of_not_minimal_omega_two`**: a geodesic from `J_k` to `−J_k` in
  `Ω^{(c)}` (`Morse.omegaComp` with angle `π m_{k+1} c / 2`) which is not of least energy has
  index `≥ (ν − |c|)/4` (natural division), where `ν · m_{k+1} = n`.

## What Milnor leaves implicit

* The trace identity `c = Σ a_h` (`tr(A·i) = −m_k Σ a_h`, the angle of `f` being
  `−π tr(A·i)/2`) is what ties the component to the splitting of the geodesic.
* "Suppose for example that some `a_h` is equal to `−3`": the other case follows by `A ↦ −A`,
  which reverses the geodesic's parameter direction in `exp(tπA)` but not its conjugate points.
-/

open Matrix Set Filter Topology Module
open scoped Morse.MatrixInner RealInnerProductSpace Manifold ContDiff

noncomputable section

namespace Morse

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {J : ℕ → Matrix ι ι ℝ} {k : ℕ}

omit [Fintype ι] [DecidableEq ι] in
theorem colRep_smul (c : ℝ) (w : ι → ℝ) : colRep (c • w) = c • colRep w := by
  ext i l; simp [colRep]

/-- **`A = c·i` on a vector forces `c` odd** when `exp(πA) = −I`. -/
theorem exists_odd_of_mulVec {A ii : Matrix ι ι ℝ} (hiiH : iiᴴ = -ii) (hii : ii * ii = -1)
    (hAi : A * ii = ii * A) (hexp : NormedSpace.exp (Real.pi • A) = -1) {w : ι → ℝ}
    (hw : w ≠ 0) {c : ℝ} (hc : A *ᵥ w = c • (ii *ᵥ w)) : ∃ n : ℤ, c = 2 * n + 1 := by
  set E0 := colRep w with hE0def
  set E1 := ii * E0 with hE1def
  have hE0 : E0 ≠ 0 := by
    intro h0
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hw
    have := congrFun (congrFun h0 i) i
    exact hi (by simpa [hE0def, colRep] using this)
  have hAE0 : A * E0 = c • E1 := by
    rw [hE0def, mul_colRep, hc, colRep_smul, hE1def, mul_colRep]
  have hAE1 : A * E1 = -c • E0 := by
    rw [hE1def, ← Matrix.mul_assoc, hAi, Matrix.mul_assoc, hAE0, Matrix.mul_smul, hE1def,
      ← Matrix.mul_assoc, hii, Matrix.neg_mul, Matrix.one_mul, smul_neg, neg_smul]
  set cf : ℝ → Matrix ι ι ℝ := fun t => Real.cos (c * t) • E0 + Real.sin (c * t) • E1
    with hcfdef
  have hcf : ∀ t, HasDerivAt cf (A * cf t) t := fun t => by
    have h1 : HasDerivAt (fun t => Real.cos (c * t)) (-Real.sin (c * t) * c) t := by
      simpa using ((hasDerivAt_id t).const_mul c).cos
    have h2 : HasDerivAt (fun t => Real.sin (c * t)) (Real.cos (c * t) * c) t := by
      simpa using ((hasDerivAt_id t).const_mul c).sin
    refine ((h1.smul_const E0).add (h2.smul_const E1)).congr_deriv ?_
    simp only [hcfdef, Matrix.mul_add, Matrix.mul_smul, hAE0, hAE1, smul_smul]
    module
  have hπ := eq_exp_smul_mul_of_hasDerivAt hcf Real.pi
  simp only [hcfdef, mul_zero, Real.cos_zero, Real.sin_zero, one_smul, zero_smul, add_zero,
    hexp, Matrix.neg_mul, Matrix.one_mul] at hπ
  have hin := congrArg (fun M => ⟪E0, M⟫) hπ
  simp only [inner_add_right, real_inner_smul_right, inner_neg_right, hE1def,
    inner_self_mul_skew hiiH, mul_zero, add_zero, real_inner_self_eq_norm_sq] at hin
  have hpos : 0 < ‖E0‖ ^ 2 := by positivity
  have hcos : Real.cos (c * Real.pi) = -1 := by
    have : (Real.cos (c * Real.pi) + 1) * ‖E0‖ ^ 2 = 0 := by linarith
    have := (mul_eq_zero.1 this).resolve_right hpos.ne'
    linarith
  obtain ⟨n, hn⟩ := Real.cos_eq_neg_one_iff.1 hcos
  refine ⟨n, ?_⟩
  have := Real.pi_pos
  have h2 : (2 * n + 1) * Real.pi = c * Real.pi := by rw [← hn]; ring
  exact (mul_right_cancel₀ Real.pi_ne_zero h2).symm

theorem iWord_matE : iWord k (fun α => matE ι (J α)) = matE ι (iWordM J k) := by
  rw [iWordM, map_list_prod, List.map_map]
  rfl

/-- Milnor's `i` as an operator satisfies `Morse.IsIOps`. -/
theorem isIOps_matE (hJ : IsAnticommFamily J k) (hk : k ≠ 0) (hii : IsCentralI J k (iWordM J k))
    {A : Matrix ι ι ℝ} (hA : A ∈ tanAlg J k (basePt J k)) :
    IsIOps k (matE ι A) (matE ι (basePt J k)) (fun α => matE ι (J α)) where
  sq := by rw [iWord_matE, ← map_mul, hii.sq, map_neg, map_one]
  skew := by rw [iWord_matE, ← matE_conjTranspose, conjTranspose_real, hii.skew, map_neg]
  ia := by rw [iWord_matE, ← map_mul, ← map_mul, hii.comm A hA.2.2]
  iq := by
    have hp : basePt J k ∈ Omega J k := basePt_mem_omega hJ
    have h := hii.anti _ (anti_of_mem_omega hk hp)
    rw [iWord_matE, ← map_mul, ← map_mul, ← map_neg, h, neg_neg]
  ij α h1 h2 := by rw [iWord_matE, ← map_mul, ← map_mul, hii.jcomm α h1 h2]

/-- A product `Di` with `D` anticommuting with `p` and commuting with the `J_α` gives the
Killing field `Di − (Di)ᵀ`. -/
theorem sub_conjTranspose_mem_isoAlg (hJ : IsAnticommFamily J k) (hk : k ≠ 0)
    (hii : IsCentralI J k (iWordM J k)) {D : Matrix ι ι ℝ}
    (hDp : D * basePt J k = -(basePt J k * D))
    (hDJ : ∀ α, 1 ≤ α → α < k → D * J α = J α * D) :
    D * iWordM J k - (D * iWordM J k)ᴴ ∈ isoAlg J k (basePt J k) := by
  set ii := iWordM J k
  set p := basePt J k
  have hp : p ∈ Omega J k := basePt_mem_omega hJ
  have hip : p * ii = -(ii * p) := hii.anti p (anti_of_mem_omega hk hp)
  have hpH : pᴴ = -p := by
    simp only [p, basePt, if_neg hk]
    rw [conjTranspose_real]; exact (hJ.cs k (Nat.one_le_iff_ne_zero.2 hk) le_rfl).transpose
  have hcommH : ∀ (Y S : Matrix ι ι ℝ), Sᴴ = -S → Y * S = S * Y → Yᴴ * S = S * Yᴴ := by
    intro Y S hS hYS
    have := congrArg Matrix.conjTranspose hYS
    rw [conjTranspose_mul, conjTranspose_mul, hS, Matrix.mul_neg, Matrix.neg_mul,
      neg_inj] at this
    exact this.symm
  set Y := D * ii
  have hip' : ii * p = -(p * ii) := by rw [hip, neg_neg]
  have hYp : Y * p = p * Y :=
    calc Y * p = D * (ii * p) := Matrix.mul_assoc _ _ _
      _ = -(D * p * ii) := by rw [hip', Matrix.mul_neg, Matrix.mul_assoc]
      _ = p * Y := by rw [hDp, Matrix.neg_mul, neg_neg, Matrix.mul_assoc]
  have hYJ : ∀ α, 1 ≤ α → α < k → Y * J α = J α * Y := fun α h1 h2 =>
    calc Y * J α = D * (J α * ii) := by rw [Matrix.mul_assoc, hii.jcomm α h1 h2]
      _ = J α * Y := by rw [← Matrix.mul_assoc, hDJ α h1 h2, Matrix.mul_assoc]
  have hJH : ∀ α, 1 ≤ α → α < k → (J α)ᴴ = -J α := fun α h1 h2 => by
    rw [conjTranspose_real]; exact (hJ.cs α h1 (by omega)).transpose
  refine ⟨by rw [conjTranspose_sub, conjTranspose_conjTranspose, neg_sub], ?_,
    fun α h1 h2 => ?_⟩
  · rw [Matrix.sub_mul, Matrix.mul_sub, hYp, hcommH Y p hpH hYp]
  · rw [Matrix.sub_mul, Matrix.mul_sub, hYJ α h1 h2, hcommH Y _ (hJH α h1 h2) (hYJ α h1 h2)]

theorem trace_matE (M : Matrix ι ι ℝ) :
    LinearMap.trace ℝ _ ((matE ι M : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι) :
      EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ ι) = M.trace := by
  have : ((matE ι M : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι) :
      EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ ι) =
        Matrix.toLin (PiLp.basisFun 2 ℝ ι) (PiLp.basisFun 2 ℝ ι) M :=
    LinearMap.ext fun _ => rfl
  rw [this, Matrix.trace_toLin_eq]

/-- **The Killing fields from the data** (`Morse.TwoPieceData`, transported to matrices). -/
theorem killing_of_twoPieceData (hJ : IsAnticommFamily J k) (hk : k ≠ 0)
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
  exact exists_killing_spaces_two hA'.1 hii.sq hiiH hAi D pd.a₀ pd.b
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
theorem le_formIndex_of_not_minimal_omega_two (hJ : IsAnticommFamily J k) (hk : k ≠ 0)
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
      obtain ⟨T, 𝒳, h1, h2, h3, h4, h5⟩ := killing_of_twoPieceData hJ hk hii hA rfl pd
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
        killing_of_twoPieceData hJ hk hii hA' (map_neg _ _).symm pd
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

end Morse
