import Morse
import RoundTrip.Check
import RoundTrip.Blind.V15_37

open Set Module
open scoped Matrix

namespace RoundTrip.V15_37

/-- The project's statement (universes instantiated at `0`; an abstract finite-dimensional real
inner product space `E` with operators `a = A`, `q = J`, `j α = J_α` satisfying Milnor's relations
`IsOmegaOps k a q j`, `k ≠ 0`, and the relations `IsIOps` of `i = iWord k j = J_1⋯J_{k−1}`):
`A = c·i` on every minimal `(A, J, J_α)`-invariant subspace; for matrices, `Av = c·iv`,
`v ≠ 0`, `exp(πA) = −I` force `c` odd (any `ii` with `iiᴴ = −ii`, `ii² = −1`, `Aii = iiA`); the
splitting (`k + 1 ≤ 8`, granted that the scalars are odd): SOME orthogonal list of minimal
pieces with odd `a_h`, `ν·m_{k+1} = dim E`, `tr(A·i) = −m_{k+1} Σ a_h`, and `A² = −1` if all
`a_h² = 1`; Lemma 24.8 between two pieces (`k ≤ 8`, `k ≢ 3 mod 4`, nonzero scalars): a LINEAR
isomorphism `M₀ ≅ M₁` commuting with the `J_α` and anticommuting with `J`. -/
def A : Prop :=
  type_of% @Morse.IsOmegaOps.exists_eq_smul_iWord.{0} ∧ type_of% @Morse.exists_odd_of_mulVec.{0} ∧
    type_of% @Morse.exists_decomp_two.{0} ∧ type_of% @Morse.exists_inter_two.{0}

theorem A_holds : A :=
  ⟨@Morse.IsOmegaOps.exists_eq_smul_iWord.{0}, @Morse.exists_odd_of_mulVec.{0},
    @Morse.exists_decomp_two.{0}, @Morse.exists_inter_two.{0}⟩

section Vocab
variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- B's `tr_ℂ A = tr(A_ℂ Q)` is `−√−1·tr(A·i)/2` for `tr A = 0`. -/
theorem ctr_eq' (i A : Mat ι) (htr : Matrix.trace A = 0) :
    ctr i A = (((-(Matrix.trace (A * i)) / 2 : ℝ)) : ℂ) * Complex.I := by
  rw [ctr, show projQ i = Morse.projP i from rfl, show cplx A = Morse.cplx A from rfl,
    Morse.projP, Matrix.mul_smul, Matrix.mul_sub, Matrix.mul_one,
    Matrix.mul_smul, Matrix.trace_smul, Matrix.trace_sub, Matrix.trace_smul, ← map_mul,
    Morse.trace_cplx, Morse.trace_cplx, htr]
  push_cast
  simp only [smul_eq_mul]
  ring

end Vocab

/-! ### A ⇒ B

B fixes an arbitrary orthogonal splitting `ℝⁿ = M_1 ⊕ ⋯ ⊕ M_r` into minimal
`(J_1, …, J_{k−1}, J, A)`-spaces. Transport to the project's operator setting
(`E = EuclideanSpace ℝ (Fin n)`, `matE`); then A's `exists_eq_smul_iWord` gives the `a_h`, A's
`exists_odd_of_mulVec` gives `a_h ≠ 0`, and A's `exists_inter_two` gives a linear intertwiner
`M_h ≅ M_j`. Not in A, and proved here: the trace formula for B's splitting (the project's
direct-sum argument, re-run for this splitting), `dim M_h = m_k` (non-item project lemma
`finrank_eq_milnorM_of_isMinimal`), minimality under `J_1, …, J_{k−1}, J` alone, and that the
intertwiner can be taken ISOMETRIC (Schur: `TᵀT` commutes with the generators, hence is a
positive scalar on the minimal piece, via the non-item `IsMinInvar.exists_scalar`). -/

section Iso
open Morse
open scoped RealInnerProductSpace
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {k : ℕ} {a q : E →L[ℝ] E} {j : ℕ → E →L[ℝ] E}

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {k : ℕ} {a q : E →L[ℝ] E} {j : ℕ → E →L[ℝ] E}

/-- An operator vanishing on `M` and on `Mᗮ` is zero. -/
theorem eq_of_eq_on_and_orth {M : Submodule ℝ E} {F G : E →L[ℝ] E}
    (h1 : ∀ v ∈ M, F v = G v) (h2 : ∀ v ∈ Mᗮ, F v = G v) : F = G := by
  ext v
  obtain ⟨y, hy, z, hz, rfl⟩ := M.exists_add_mem_mem_orthogonal v
  rw [map_add, map_add, h1 y hy, h2 z hz]

/-- **Lemma 24.8 between two pieces, isometric**: the linear intertwiner of
`exists_inter_two` (supplied as `hT`) is a multiple of an isometry (Schur: `TᵀT` commutes with the
generators, hence is a scalar on the minimal piece `M₀`). -/
theorem exists_isometry_inter (h : IsOmegaOps k a q j) (hk : k ≠ 0) {M₀ M₁ : Submodule ℝ E}
    (hM₀ : IsMinInvar (omegaGens k a q j) M₀)
    {c₀ : ℝ} (hc₀ : ∀ v ∈ M₀, a v = c₀ • iWord k j v)
    (T : M₀ ≃ₗ[ℝ] M₁) (hTj : ∀ α, 1 ≤ α → α < k → ∀ (x : M₀) (hx : j α x ∈ M₀),
      (T ⟨j α x, hx⟩ : E) = j α (T x))
    (hTq : ∀ (x : M₀) (hx : q x ∈ M₀), (T ⟨q x, hx⟩ : E) = -q (T x)) :
    ∃ U : E →L[ℝ] E, (∀ v ∈ M₀, U v ∈ M₁) ∧ (∀ w ∈ M₁, ∃ v ∈ M₀, U v = w) ∧
      (∀ v ∈ M₀, ∀ w ∈ M₀, ⟪U v, U w⟫ = ⟪v, w⟫) ∧
      (∀ α, 1 ≤ α → α < k → ∀ v ∈ M₀, U (j α v) = j α (U v)) ∧
      ∀ v ∈ M₀, U (q v) = -q (U v) := by
  set Tc : M₀ →L[ℝ] M₁ := LinearMap.toContinuousLinearMap (T : M₀ →ₗ[ℝ] M₁) with hTc
  set t : E →L[ℝ] E := M₁.subtypeL ∘L Tc ∘L M₀.orthogonalProjectionOnto with htdef
  have ht0 : ∀ v (hv : v ∈ M₀), t v = T ⟨v, hv⟩ := fun v hv => by
    have hp : M₀.orthogonalProjectionOnto v = ⟨v, hv⟩ :=
      Submodule.orthogonalProjectionOnto_mem_subspace_eq_self ⟨v, hv⟩
    simp only [htdef, ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply, hp]
    rfl
  have ht1 : ∀ v ∈ M₀ᗮ, t v = 0 := fun v hv => by
    simp only [htdef, ContinuousLinearMap.comp_apply,
      Submodule.orthogonalProjectionOnto_apply_of_mem_orthogonal hv, map_zero]
  have hinv₀ := hM₀.2.1
  have hinv₀' := IsInvar.orthogonal h.isStarSigned hinv₀
  -- intertwining on all of `E`
  have htj : ∀ α, 1 ≤ α → α < k → t * j α = j α * t := fun α h1 h2 =>
    eq_of_eq_on_and_orth (M := M₀) (fun v hv => by
      have hjv : j α v ∈ M₀ := hinv₀ _ (IsOmegaOps.j_mem h1 h2) v hv
      rw [mul_apply_eq_comp, mul_apply_eq_comp, ht0 _ hjv, ht0 v hv]
      exact hTj α h1 h2 ⟨v, hv⟩ hjv)
      (fun v hv => by
        rw [mul_apply_eq_comp, mul_apply_eq_comp,
          ht1 _ (hinv₀' _ (IsOmegaOps.j_mem h1 h2) v hv), ht1 v hv, map_zero])
  have htq : t * q = -(q * t) :=
    eq_of_eq_on_and_orth (M := M₀) (fun v hv => by
      have hqv : q v ∈ M₀ := hinv₀ _ IsOmegaOps.q_mem v hv
      rw [mul_apply_eq_comp, _root_.neg_apply, mul_apply_eq_comp, ht0 _ hqv, ht0 v hv]
      exact hTq ⟨v, hv⟩ hqv)
      (fun v hv => by
        rw [mul_apply_eq_comp, _root_.neg_apply, mul_apply_eq_comp,
          ht1 _ (hinv₀' _ IsOmegaOps.q_mem v hv), ht1 v hv, map_zero, neg_zero])
  -- the adjoint
  set ts := ContinuousLinearMap.adjoint t with htsdef
  have hts_mem : ∀ y, ts y ∈ M₀ := fun y => by
    have : ts = (M₀.subtypeL ∘L ContinuousLinearMap.adjoint Tc) ∘L M₁.orthogonalProjectionOnto := by
      rw [htsdef, htdef, ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp,
        Submodule.adjoint_orthogonalProjectionOnto, Submodule.adjoint_subtypeL]
    rw [this]
    exact Submodule.coe_mem _
  have hjskew : ∀ α, 1 ≤ α → α < k → ContinuousLinearMap.adjoint (j α) = -j α :=
    fun α h1 h2 => h.j_skew α h1 h2
  have htsj : ∀ α, 1 ≤ α → α < k → ts * j α = j α * ts := fun α h1 h2 => by
    have := congrArg star (htj α h1 h2)
    simp only [star_mul, ContinuousLinearMap.star_eq_adjoint, hjskew α h1 h2, ← htsdef,
      neg_mul, mul_neg, neg_inj] at this
    exact this.symm
  have htsq : ts * q = -(q * ts) := by
    have := congrArg star htq
    simp only [star_mul, star_neg, ContinuousLinearMap.star_eq_adjoint, h.q_skew hk, ← htsdef,
      neg_mul, mul_neg, neg_neg] at this
    exact this.symm
  obtain ⟨S, hSdef⟩ : ∃ S, S = ts * t := ⟨_, rfl⟩
  have hSj : ∀ α, 1 ≤ α → α < k → S * j α = j α * S := fun α h1 h2 => by
    rw [hSdef, mul_assoc, htj α h1 h2, ← mul_assoc, htsj α h1 h2, mul_assoc]
  have hSq : S * q = q * S := by
    rw [hSdef, mul_assoc, htq, mul_neg, ← mul_assoc, htsq, neg_mul, neg_neg, mul_assoc]
  have hSi : S * iWord k j = iWord k j * S := commute_iWord hSj
  have hSmem : ∀ v, S v ∈ M₀ := fun v => by rw [hSdef, mul_apply_eq_comp]; exact hts_mem _
  have hS1 : ∀ v ∈ M₀ᗮ, S v = 0 := fun v hv => by
    rw [hSdef, mul_apply_eq_comp, ht1 v hv, map_zero]
  have hSa : S * a = a * S :=
    eq_of_eq_on_and_orth (M := M₀) (fun v hv => by
      have hSiv : S (iWord k j v) = iWord k j (S v) := by
        simpa only [mul_apply_eq_comp] using congrArg (fun F : E →L[ℝ] E => F v) hSi
      rw [mul_apply_eq_comp, mul_apply_eq_comp, hc₀ v hv, hc₀ _ (hSmem v), map_smul, hSiv])
      (fun v hv => by
        rw [mul_apply_eq_comp, mul_apply_eq_comp, hS1 _ (hinv₀' _ IsOmegaOps.a_mem v hv),
          hS1 v hv, map_zero])
  have hSadj : ContinuousLinearMap.adjoint S = S := by
    rw [hSdef, ← ContinuousLinearMap.star_eq_adjoint, star_mul, htsdef,
      ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.star_eq_adjoint,
      ContinuousLinearMap.adjoint_adjoint]
  have hcomm : ∀ g ∈ omegaGens k a q j, ∀ v, S (g v) = g (S v) := by
    rintro g ((hg | hg) | ⟨α, h1, h2, rfl⟩) v
    · rw [Set.mem_singleton_iff.1 (show g ∈ ({a} : Set (E →L[ℝ] E)) from hg)]
      rw [← mul_apply_eq_comp, hSa, mul_apply_eq_comp]
    · rw [Set.mem_singleton_iff.1 hg, ← mul_apply_eq_comp, hSq, mul_apply_eq_comp]
    · rw [← mul_apply_eq_comp, hSj α h1 h2, mul_apply_eq_comp]
  obtain ⟨μ, hμ⟩ := hM₀.exists_scalar hSadj (fun v _ => hSmem v) hcomm
  -- `⟪S v, w⟫ = ⟪t v, t w⟫`
  have hinner : ∀ v w, ⟪S v, w⟫ = ⟪t v, t w⟫ := fun v w => by
    rw [hSdef, mul_apply_eq_comp, htsdef, ContinuousLinearMap.adjoint_inner_left]
  have hμpos : 0 < μ := by
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hM₀.1
    have h1 := hinner v v
    rw [hμ v hv, real_inner_smul_left, real_inner_self_eq_norm_sq,
      real_inner_self_eq_norm_sq] at h1
    have htv : t v ≠ 0 := by
      rw [ht0 v hv]
      intro h0
      have : T ⟨v, hv⟩ = 0 := Subtype.ext h0
      rw [LinearEquiv.map_eq_zero_iff] at this
      exact hv0 (congrArg Subtype.val this)
    have hpos : 0 < ‖t v‖ ^ 2 := by positivity
    have hv2 : 0 < ‖v‖ ^ 2 := by positivity
    nlinarith
  refine ⟨(Real.sqrt μ)⁻¹ • t, fun v hv => ?_, fun w hw => ?_, fun v hv w hw => ?_,
    fun α h1 h2 v hv => ?_, fun v hv => ?_⟩
  · rw [_root_.smul_apply, ht0 v hv]
    exact M₁.smul_mem _ (T ⟨v, hv⟩).2
  · refine ⟨Real.sqrt μ • (T.symm ⟨w, hw⟩ : E), M₀.smul_mem _ (T.symm ⟨w, hw⟩).2, ?_⟩
    rw [_root_.smul_apply, map_smul, ht0 _ (T.symm ⟨w, hw⟩).2, smul_smul,
      inv_mul_cancel₀ (Real.sqrt_pos.2 hμpos).ne', one_smul]
    simp
  · rw [_root_.smul_apply, _root_.smul_apply, real_inner_smul_left, real_inner_smul_right,
      ← hinner, hμ v hv, real_inner_smul_left, ← mul_assoc, ← mul_inv, Real.mul_self_sqrt hμpos.le]
    field_simp
  · rw [_root_.smul_apply, _root_.smul_apply, map_smul, ← mul_apply_eq_comp t, htj α h1 h2,
      mul_apply_eq_comp]
  · rw [_root_.smul_apply, _root_.smul_apply, map_smul, ← mul_apply_eq_comp t, htq,
      _root_.neg_apply, mul_apply_eq_comp, smul_neg]

end Iso

section Transport
open Morse Matrix
open scoped RealInnerProductSpace
variable {ι : Type} [Fintype ι] [DecidableEq ι]
set_option linter.unusedSectionVars false

/-- A subspace of `ℝ^ι` as a subspace of `EuclideanSpace ℝ ι`. -/
def cm (M : Submodule ℝ (ι → ℝ)) : Submodule ℝ (EuclideanSpace ℝ ι) :=
  M.comap (WithLp.linearEquiv 2 ℝ (ι → ℝ) : EuclideanSpace ℝ ι →ₗ[ℝ] (ι → ℝ))

theorem mem_cm {M : Submodule ℝ (ι → ℝ)} {x : EuclideanSpace ℝ ι} : x ∈ cm M ↔ x.ofLp ∈ M :=
  Iff.rfl

theorem matE_ofLp (X : Mat ι) (x : EuclideanSpace ℝ ι) : (matE ι X x).ofLp = X *ᵥ x.ofLp :=
  Matrix.ofLp_toEuclideanCLM X x

theorem matE_toLp (X : Mat ι) (v : ι → ℝ) : matE ι X (WithLp.toLp 2 v) = WithLp.toLp 2 (X *ᵥ v) :=
  rfl

theorem finrank_cm (M : Submodule ℝ (ι → ℝ)) : finrank ℝ (cm M) = finrank ℝ M := by
  rw [cm, Submodule.comap_equiv_eq_map_symm, LinearEquiv.finrank_map_eq]

theorem iProd_eq (Js : ℕ → Mat ι) : ∀ m, iProd Js m = ((List.range m).map fun i => Js (i + 1)).prod
  | 0 => by simp [iProd]
  | m + 1 => by
    rw [List.range_succ, List.map_append, List.prod_append, ← iProd_eq Js m]
    simp [iProd]

theorem iProd_eq_iWordM (Js : ℕ → Mat ι) (k : ℕ) : iProd Js (k - 1) = iWordM Js k :=
  iProd_eq Js (k - 1)

theorem transpose_eq_neg' {J : Mat ι} (hJ : IsCplxStr J) : Jᵀ = -J := by
  have h1 : Jᵀ * J = 1 := by
    have := hJ.1
    rw [Matrix.mem_orthogonalGroup_iff'] at this
    simpa [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] using this
  calc Jᵀ = Jᵀ * (J * -J) := by rw [Matrix.mul_neg, hJ.2, neg_neg, Matrix.mul_one]
    _ = -J := by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]

theorem omegaK_props {Js : ℕ → Mat ι} {k : ℕ} (hk : k ≠ 0) {J : Mat ι} (hJ : J ∈ OmegaK Js k) :
    IsCplxStr J ∧ ∀ α, 1 ≤ α → α ≤ k - 1 → J * Js α = -(Js α * J) := by
  obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  exact ⟨hJ.1, fun α h1 h2 => hJ.2 α h1 (by omega)⟩

theorem isOmegaOps_B {Js : ℕ → Mat ι} {k : ℕ} (hk : k ≠ 0) (hJs : IsACFam Js (k - 1))
    {J A : Mat ι} (hJ : J ∈ OmegaK Js k) (hA : IsSkew A) (hAJ : AntiComm A J)
    (hAα : ∀ α, 1 ≤ α → α ≤ k - 1 → Commute A (Js α)) :
    IsOmegaOps k (matE ι A) (matE ι J) (fun α => matE ι (Js α)) where
  a_skew := adjoint_matE_of_skew (by rw [conjTranspose_eq_transpose_of_trivial]; exact hA)
  q_zero hk' := absurd hk' hk
  q_sq _ := by rw [← map_mul, (omegaK_props hk hJ).1.2, map_neg, map_one]
  q_skew _ := adjoint_matE_of_skew (by
    rw [conjTranspose_eq_transpose_of_trivial]; exact transpose_eq_neg' (omegaK_props hk hJ).1)
  aq _ := by rw [← map_mul, hAJ, map_neg, map_mul]
  j_sq α h1 h2 := by rw [← map_mul, (hJs.1 α h1 (by omega)).2, map_neg, map_one]
  j_skew α h1 h2 := adjoint_matE_of_skew (by
    rw [conjTranspose_eq_transpose_of_trivial]; exact transpose_eq_neg' (hJs.1 α h1 (by omega)))
  j_anti α β h1 h2 h3 h4 hne := by
    rw [← map_mul, hJs.2 α β h1 (by omega) h3 (by omega) hne, map_neg, map_mul]
  jq α h1 h2 := by
    rw [← map_mul, ← map_mul, ← map_neg]
    congr 1
    have := (omegaK_props hk hJ).2 α h1 (by omega)
    rw [this, neg_neg]
  ja α h1 h2 := by rw [← map_mul, ← (hAα α h1 (by omega)).eq, map_mul]

theorem isCentralI_B {Js : ℕ → Mat ι} {k : ℕ} (hk : k = 2 ∨ k = 6) (hJs : IsACFam Js (k - 1)) :
    IsCentralI Js k (iWordM Js k) := by
  rcases hk with rfl | rfl
  · rw [iWordM_two]; exact isCentralI_two ⟨hJs.1, hJs.2⟩
  · rw [iWordM_six]; exact isCentralI_six ⟨hJs.1, hJs.2⟩

theorem isIOps_B {Js : ℕ → Mat ι} {k : ℕ} (hk : k = 2 ∨ k = 6) (hJs : IsACFam Js (k - 1))
    {J A : Mat ι} (hJ : J ∈ OmegaK Js k)
    (hAα : ∀ α, 1 ≤ α → α ≤ k - 1 → Commute A (Js α)) :
    IsIOps k (matE ι A) (matE ι J) (fun α => matE ι (Js α)) := by
  have hii := isCentralI_B hk hJs
  have hk0 : k ≠ 0 := by omega
  refine ⟨?_, ?_, ?_, ?_, fun α h1 h2 => ?_⟩
  · rw [iWord_matE, ← map_mul, hii.sq, map_neg, map_one]
  · rw [iWord_matE]
    exact adjoint_matE_of_skew (by rw [conjTranspose_eq_transpose_of_trivial]; exact hii.skew)
  · rw [iWord_matE, ← map_mul, ← map_mul,
      hii.comm A fun α h1 h2 => (hAα α h1 (by omega)).eq]
  · rw [iWord_matE, ← map_mul, ← map_mul, ← map_neg]
    congr 1
    have := hii.anti J fun α h1 h2 => by
      rw [(omegaK_props hk0 hJ).2 α h1 (by omega), neg_neg]
    rw [this, neg_neg]
  · rw [iWord_matE, ← map_mul, ← map_mul, hii.jcomm α h1 h2]

theorem isMinInvar_cm {Js : ℕ → Mat ι} {k : ℕ} (_hk : k ≠ 0) {J A : Mat ι}
    {M : Submodule ℝ (ι → ℝ)} (hM : IsMinF (famA Js k J A) M) :
    IsMinInvar (omegaGens k (matE ι A) (matE ι J) (fun α => matE ι (Js α))) (cm M) := by
  have hgen : ∀ g ∈ omegaGens k (matE ι A) (matE ι J) (fun α => matE ι (Js α)),
      ∃ X ∈ famA Js k J A, g = matE ι X := by
    rintro g ((hg | hg) | ⟨α, h1, h2, rfl⟩)
    · exact ⟨A, Or.inr (Or.inr rfl), hg⟩
    · exact ⟨J, Or.inr (Or.inl rfl), Set.mem_singleton_iff.1 hg⟩
    · exact ⟨Js α, Or.inl ⟨α, h1, by omega, rfl⟩, rfl⟩
  have hfam : ∀ X ∈ famA Js k J A,
      matE ι X ∈ omegaGens k (matE ι A) (matE ι J) (fun α => matE ι (Js α)) := by
    rintro X (⟨α, h1, h2, rfl⟩ | rfl | rfl)
    · exact Or.inr ⟨α, h1, by omega, rfl⟩
    · exact Or.inl (Or.inr rfl)
    · exact Or.inl (Or.inl rfl)
  refine ⟨?_, ?_, fun W hW hWi => ?_⟩
  · intro h0
    apply hM.1
    rw [eq_bot_iff]
    intro v hv
    have : WithLp.toLp 2 v ∈ cm M := hv
    rw [h0, Submodule.mem_bot] at this
    rw [Submodule.mem_bot]
    exact congrArg WithLp.ofLp this
  · intro g hg x hx
    obtain ⟨X, hX, rfl⟩ := hgen g hg
    rw [mem_cm, matE_ofLp]
    exact hM.2.1 X hX _ hx
  · set W₀ := W.map (WithLp.linearEquiv 2 ℝ (ι → ℝ) : EuclideanSpace ℝ ι →ₗ[ℝ] (ι → ℝ))
      with hW₀
    have hWW : W = cm W₀ := by
      rw [cm, hW₀, Submodule.comap_map_eq_of_injective (WithLp.linearEquiv 2 ℝ (ι → ℝ)).injective]
    have hW₀M : W₀ ≤ M := by
      rintro _ ⟨x, hx, rfl⟩
      exact hW hx
    have hW₀c : ClosedF (famA Js k J A) W₀ := by
      rintro X hX _ ⟨x, hx, rfl⟩
      refine ⟨matE ι X x, hWi _ (hfam X hX) x hx, ?_⟩
      exact matE_ofLp X x
    rcases hM.2.2 W₀ hW₀M hW₀c with h0 | h0
    · left; rw [hWW, h0, cm, Submodule.comap_bot]
      exact LinearEquiv.ker _
    · right; rw [hWW, h0]

end Transport

open Matrix in
theorem A_to_B : A → B := by
  classical
  rintro ⟨hsc, hodd, -, hinter⟩
  intro n k Js hk hJs J hJ A hA hAJ hAα hexp r M hmin horth hsup
  have hk0 : k ≠ 0 := by omega
  set aE := Morse.matE (Fin n) A
  set qE := Morse.matE (Fin n) J
  set jE : ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
    fun α => Morse.matE (Fin n) (Js α)
  have hO : Morse.IsOmegaOps k aE qE jE := isOmegaOps_B hk0 hJs hJ hA hAJ hAα
  have hI : Morse.IsIOps k aE qE jE := isIOps_B hk hJs hJ hAα
  have hii := isCentralI_B hk hJs
  have hiw : Morse.iWord k jE = Morse.matE (Fin n) (Morse.iWordM Js k) := Morse.iWord_matE
  have hiP : iProd Js (k - 1) = Morse.iWordM Js k := iProd_eq_iWordM Js k
  have hmin' : ∀ h, Morse.IsMinInvar (Morse.omegaGens k aE qE jE) (cm (M h)) := fun h =>
    isMinInvar_cm hk0 (hmin h)
  -- the scalars `a_h`
  have hsc' : ∀ h, ∃ c : ℝ, ∀ v ∈ cm (M h), aE v = c • Morse.iWord k jE v := fun h =>
    hsc hO hI hk0 (hmin' h)
  choose c hc using hsc'
  have hcv : ∀ h, ∀ v ∈ M h, A *ᵥ v = c h • (iProd Js (k - 1) *ᵥ v) := fun h v hv => by
    have := congrArg WithLp.ofLp (hc h (WithLp.toLp 2 v) hv)
    rw [hiw, hiP] at *
    simpa [aE, matE_ofLp] using this
  have hc0 : ∀ h, c h ≠ 0 := fun h => by
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (hmin h).1
    obtain ⟨m, hm⟩ := hodd (A := A) (ii := Morse.iWordM Js k)
      (by rw [conjTranspose_eq_transpose_of_trivial]; exact hii.skew) hii.sq
      (hii.comm A fun α h1 h2 => (hAα α h1 (by omega)).eq) hexp hv0
      (by rw [← hiP]; exact hcv h v hv)
    intro h0
    rw [h0] at hm
    have : (2 * m + 1 : ℤ) = 0 := by exact_mod_cast hm.symm
    omega
  -- dimensions
  have hdim : ∀ h, finrank ℝ (M h) = mK k := fun h => by
    rw [← finrank_cm]
    have hk8 : k + 1 ≤ 8 := by omega
    have := Morse.finrank_eq_milnorM_of_isMinimal hk8
      (hO.isClifford_cliffFam (hM := (hmin' h).2.1) (s := (c h)⁻¹)
        (Morse.a_a_of_eq_smul hI (Morse.iWord_mem_of_isInvar (hmin' h).2.1) (hc h))
        (by field_simp [hc0 h]))
      (hO.isMinimal_cliffFam (hmin' h) (inv_ne_zero (hc0 h)))
    rw [this]
    rcases hk with rfl | rfl <;> decide
  -- closed under `i`
  have hiclosed : ∀ W : Submodule ℝ (Fin n → ℝ), ClosedF (famA Js k J J) W →
      ∀ m, m ≤ k - 1 → ∀ v ∈ W, iProd Js m *ᵥ v ∈ W := by
    intro W hW m
    induction m with
    | zero => intro _ v hv; simpa [iProd] using hv
    | succ m ih =>
      intro hm v hv
      rw [iProd, ← Matrix.mulVec_mulVec]
      exact ih (by omega) _ (hW _ (Or.inl ⟨m + 1, by omega, hm, rfl⟩) v hv)
  refine ⟨⟨c, hcv, ?_⟩, fun h => ⟨⟨(hmin h).1, fun X hX => (hmin h).2.1 X ?_, fun W hWM hWc => ?_⟩,
    hdim h⟩, fun h h' => ?_⟩
  · -- the trace
    have htrA : trace A = 0 := by
      have h' := congrArg trace hA
      rw [trace_transpose, trace_neg] at h'
      linarith
    have hint : DirectSum.IsInternal (fun h => cm (M h)) := by
      refine DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top ?_ ?_
      · refine OrthogonalFamily.independent (orthogonalFamily_iff_pairwise.2 fun h h' hne => ?_)
        show cm (M h) ⟂ cm (M h')
        rw [Submodule.isOrtho_iff_inner_eq]
        intro x hx y hy
        rw [EuclideanSpace.inner_eq_star_dotProduct]
        change y.ofLp ⬝ᵥ x.ofLp = 0
        rw [dotProduct_comm]
        exact horth h h' hne _ hx _ hy
      · rw [eq_top_iff]
        intro x _
        have hx : x.ofLp ∈ ⨆ h, M h := by rw [hsup]; exact Submodule.mem_top
        have hle : (⨆ h, M h).comap (WithLp.linearEquiv 2 ℝ (Fin n → ℝ) :
            EuclideanSpace ℝ (Fin n) →ₗ[ℝ] (Fin n → ℝ)) ≤ ⨆ h, cm (M h) := by
          rw [Submodule.comap_equiv_eq_map_symm, Submodule.map_iSup]
          exact iSup_mono fun h => (Submodule.comap_equiv_eq_map_symm _ _).symm.le
        exact hle hx
    set f : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) :=
      ((aE * Morse.iWord k jE : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) :
        EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)) with hfdef
    have hf : ∀ h, Set.MapsTo f (cm (M h)) (cm (M h)) := fun h v hv =>
      (hmin' h).2.1 aE Morse.IsOmegaOps.a_mem _ (Morse.iWord_mem_of_isInvar (hmin' h).2.1 v hv)
    have hres : ∀ h, f.restrict (hf h) = (-(c h)) • LinearMap.id := fun h => by
      apply LinearMap.ext
      rintro ⟨v, hv⟩
      apply Subtype.ext
      have hee : Morse.iWord k jE (Morse.iWord k jE v) = -v := by
        have := congrArg (fun F : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) => F v)
          hI.sq
        simpa using this
      simp only [LinearMap.restrict_apply, LinearMap.smul_apply, LinearMap.id_apply,
        SetLike.val_smul, hfdef]
      change aE (Morse.iWord k jE v) = _
      rw [hc h _ (Morse.iWord_mem_of_isInvar (hmin' h).2.1 v hv), hee, smul_neg, ← neg_smul]
    have htr : trace (A * iProd Js (k - 1)) = -((mK k : ℝ) * ∑ h, c h) := by
      rw [← Morse.trace_matE, hiP, map_mul, ← hiw]
      change LinearMap.trace ℝ _ f = _
      rw [LinearMap.trace_eq_sum_trace_restrict hint hf]
      simp only [hres, map_smul, LinearMap.trace_id, finrank_cm, hdim, smul_eq_mul,
        neg_mul, Finset.sum_neg_distrib, mul_comm]
      rw [Finset.sum_mul]
    rw [ctr_eq' (iProd Js (k - 1)) A htrA, htr]
    push_cast
    ring
  · rcases hX with ⟨α, h1, h2, rfl⟩ | rfl | rfl
    · exact Or.inl ⟨α, h1, h2, rfl⟩
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inl rfl)
  · -- minimal for `J_1, …, J_{k−1}, J`
    refine (hmin h).2.2 W hWM fun X hX v hv => ?_
    rcases hX with ⟨α, h1, h2, rfl⟩ | rfl | rfl
    · exact hWc _ (Or.inl ⟨α, h1, h2, rfl⟩) v hv
    · exact hWc _ (Or.inr (Or.inl rfl)) v hv
    · rw [hcv h v (hWM hv)]
      exact W.smul_mem _ (hiclosed W hWc (k - 1) le_rfl v hv)
  · -- the isometries
    obtain ⟨T, hTj, hTq⟩ := hinter hO hI hk0 (by omega) (by omega) (hmin' h) (hmin' h')
      (hc0 h) (hc0 h') (hc h) (hc h')
    obtain ⟨U, hU1, hU2, hU3, hU4, hU5⟩ := exists_isometry_inter hO hk0 (hmin' h) (hc h) T hTj hTq
    have hDv : ∀ v, (Morse.matE (Fin n)).symm U *ᵥ v = (U (WithLp.toLp 2 v)).ofLp := fun v => by
      rw [← matE_ofLp, StarAlgEquiv.apply_symm_apply]
    refine ⟨(Morse.matE (Fin n)).symm U, fun v hv => ?_, fun w hw => ?_, fun v hv w hw => ?_,
      fun α h1 h2 v hv => ?_, fun v hv => ?_⟩
    · rw [hDv]; exact hU1 _ hv
    · obtain ⟨x, hx, hxw⟩ := hU2 (WithLp.toLp 2 w) hw
      exact ⟨x.ofLp, hx, by rw [hDv]; change (U x).ofLp = w; rw [hxw]⟩
    · have := hU3 _ hw _ hv
      rw [EuclideanSpace.inner_eq_star_dotProduct, EuclideanSpace.inner_eq_star_dotProduct] at this
      rw [hDv, hDv]
      exact this
    · rw [hDv, hDv, ← matE_toLp, hU4 α h1 (by omega) _ hv]
      exact matE_ofLp _ _
    · rw [hDv, hDv, ← matE_toLp, hU5 _ hv]
      change (-(Morse.matE (Fin n) J) (U (WithLp.toLp 2 v))).ofLp = _
      rw [WithLp.ofLp_neg, matE_ofLp]

/-! ### B ⇒ A, only vacuously

A is about abstract inner product spaces and operators, with no `exp(πA) = −I` hypothesis in
three of its four theorems (B assumes it throughout), for an abstract `ii` in the oddness lemma,
and its splitting is an existence statement; nothing of A is an instance of B. A is re-proved
outright, by the project's arguments (non-item lemmas: `IsMinInvar.exists_scalar`,
`exists_minInvar_decomp`, `finrank_eq_milnorM_of_isMinimal`, `exists_iso_of_isMinimal`,
`isMinimal_cliffFam_k`, the matrix exponential lemmas). -/

section Outright
open Morse
open scoped RealInnerProductSpace

section Ops
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {k : ℕ} {a q : E →L[ℝ] E} {j : ℕ → E →L[ℝ] E}

theorem exists_eq_smul_iWord' (h : IsOmegaOps k a q j) (hI : IsIOps k a q j)
    (hk : k ≠ 0) {M : Submodule ℝ E} (hM : IsMinInvar (omegaGens k a q j) M) :
    ∃ c : ℝ, ∀ v ∈ M, a v = c • iWord k j v := by
  set e := iWord k j with he
  have heM := iWord_mem_of_isInvar hM.2.1
  have hS : ContinuousLinearMap.adjoint (a * e) = a * e := by
    rw [← ContinuousLinearMap.star_eq_adjoint, star_mul, ContinuousLinearMap.star_eq_adjoint,
      ContinuousLinearMap.star_eq_adjoint, hI.skew, h.a_skew, neg_mul_neg, hI.ia]
  have hSM : ∀ v ∈ M, (a * e) v ∈ M := fun v hv =>
    hM.2.1 a IsOmegaOps.a_mem _ (heM v hv)
  have hcomm : ∀ g ∈ omegaGens k a q j, ∀ v, (a * e) (g v) = g ((a * e) v) := by
    rintro g ((hg | hg) | ⟨α, h1, h2, rfl⟩) v
    · rw [Set.mem_singleton_iff.1 (show g ∈ ({a} : Set (E →L[ℝ] E)) from hg)]
      change a (e (a v)) = a (a (e v))
      rw [← mul_apply_eq_comp e a, hI.ia]; rfl
    · rw [Set.mem_singleton_iff.1 hg]
      change a (e (q v)) = q (a (e v))
      have h1 := congrArg (fun F : E →L[ℝ] E => F v) hI.iq
      have h2 := congrArg (fun F : E →L[ℝ] E => F (e v)) (h.aq hk)
      simp only [mul_apply_eq_comp, _root_.neg_apply] at h1 h2
      rw [h1, map_neg, h2, neg_neg]
    · change a (e (j α v)) = j α (a (e v))
      have h3 := congrArg (fun F : E →L[ℝ] E => F v) (hI.ij α h1 h2)
      have h4 := congrArg (fun F : E →L[ℝ] E => F (e v)) (h.ja α h1 h2)
      simp only [mul_apply_eq_comp] at h3 h4
      rw [h3, h4]
  obtain ⟨c₀, hc₀⟩ := hM.exists_scalar hS hSM hcomm
  refine ⟨-c₀, fun v hv => ?_⟩
  have h1 := hc₀ (e v) (heM v hv)
  have hee : e (e v) = -v := by
    have := congrArg (fun F : E →L[ℝ] E => F v) hI.sq
    simpa using this
  change a (e (e v)) = c₀ • e v at h1
  rw [hee, map_neg] at h1
  rw [neg_smul, ← h1, neg_neg]

theorem exists_inter_two' (h : IsOmegaOps k a q j) (hI : IsIOps k a q j) (hk : k ≠ 0)
    (hk8 : k ≤ 8) (hk3 : k % 4 ≠ 3) {M₀ M₁ : Submodule ℝ E}
    (hM₀ : IsMinInvar (omegaGens k a q j) M₀) (hM₁ : IsMinInvar (omegaGens k a q j) M₁)
    {c₀ c₁ : ℝ} (hc₀0 : c₀ ≠ 0) (hc₁0 : c₁ ≠ 0) (hc₀ : ∀ v ∈ M₀, a v = c₀ • iWord k j v)
    (hc₁ : ∀ v ∈ M₁, a v = c₁ • iWord k j v) :
    ∃ T : M₀ ≃ₗ[ℝ] M₁, (∀ α, 1 ≤ α → α < k → ∀ (x : M₀) (hx : j α x ∈ M₀),
      (T ⟨j α x, hx⟩ : E) = j α (T x)) ∧
      ∀ (x : M₀) (hx : q x ∈ M₀), (T ⟨q x, hx⟩ : E) = -q (T x) := by
  have h' := h.neg_q hk
  have hM₁' := isInvar_omegaGens_neg_q hM₁.2.1
  have hC₀ := (h.isClifford_cliffFam (hM := hM₀.2.1) (s := c₀⁻¹)
    (a_a_of_eq_smul hI (iWord_mem_of_isInvar hM₀.2.1) hc₀) (by field_simp)).mono (Nat.le_succ k)
  have hC₁ := (h'.isClifford_cliffFam (hM := hM₁') (s := c₁⁻¹)
    (a_a_of_eq_smul hI (iWord_mem_of_isInvar hM₁.2.1) hc₁) (by field_simp)).mono (Nat.le_succ k)
  have hm₀ := isMinimal_cliffFam_k hk hM₀ hc₀ (fun _ hW => hW) hM₀.2.1 c₀⁻¹
  have hm₁ := isMinimal_cliffFam_k hk hM₁ hc₁ (q' := (-1 : ℝ) • q) (fun W hW w hw => by
    have := W.smul_mem (-1 : ℝ) (hW w hw)
    rwa [_root_.smul_apply, smul_smul, neg_one_mul, neg_neg, one_smul] at this)
    hM₁' c₁⁻¹
  obtain ⟨T, hT⟩ := exists_iso_of_isMinimal hk8 hk3 hC₀ hC₁ hm₀ hm₁
  refine ⟨T, fun α h1 h2 x hx => ?_, fun x hx => ?_⟩
  · have e : (⟨j α x, hx⟩ : M₀) = cliffFam k a q j M₀ hM₀.2.1 c₀⁻¹ α x :=
      Subtype.ext (by rw [cliffFam_lt hM₀.2.1 c₀⁻¹ h1 h2])
    rw [e, hT α h1 h2.le, cliffFam_lt hM₁' c₁⁻¹ h1 h2]
  · have e : (⟨q x, hx⟩ : M₀) = cliffFam k a q j M₀ hM₀.2.1 c₀⁻¹ k x :=
      Subtype.ext (by rw [cliffFam_k])
    rw [e, hT k (Nat.one_le_iff_ne_zero.2 hk) le_rfl, cliffFam_k,
      _root_.smul_apply, neg_one_smul]

theorem exists_decomp_two' (h : IsOmegaOps k a q j) (hI : IsIOps k a q j) (hk : k ≠ 0)
    (hk8 : k + 1 ≤ 8)
    (hodd : ∀ M : Submodule ℝ E, IsMinInvar (omegaGens k a q j) M → ∀ c : ℝ,
      (∀ v ∈ M, a v = c • iWord k j v) → ∃ n : ℤ, c = 2 * n + 1) :
    ∃ (L : List (Submodule ℝ E)) (cs : Fin L.length → ℤ),
      (∀ i, IsMinInvar (omegaGens k a q j) (L.get i)) ∧
      (∀ i i', i ≠ i' → L.get i ⟂ L.get i') ∧
      (∀ i, ∀ v ∈ L.get i, a v = (cs i : ℝ) • iWord k j v) ∧ (∀ i, Odd (cs i)) ∧
      L.length * milnorM (k + 1) = finrank ℝ E ∧
      LinearMap.trace ℝ E ((a * iWord k j : E →L[ℝ] E) : E →ₗ[ℝ] E) =
        -((milnorM (k + 1) : ℝ) * ∑ i, (cs i : ℝ)) ∧
      ((∀ i, cs i ^ 2 = 1) → a * a = -1) := by
  classical
  obtain ⟨L, hL1, hL2, hL3, hL4⟩ := exists_minInvar_decomp h.isStarSigned ⊤ isInvar_top
  have hmin : ∀ i : Fin L.length, IsMinInvar (omegaGens k a q j) (L.get i) := fun i =>
    (hL1 _ (List.get_mem L i)).1
  have hsc : ∀ i : Fin L.length, ∃ n : ℤ,
      ∀ v ∈ L.get i, a v = ((2 * n + 1 : ℤ) : ℝ) • iWord k j v := fun i => by
    obtain ⟨c, hc⟩ := exists_eq_smul_iWord' h hI hk (hmin i)
    obtain ⟨n, rfl⟩ := hodd _ (hmin i) c hc
    exact ⟨n, by push_cast; exact hc⟩
  choose n hn using hsc
  set cs : Fin L.length → ℤ := fun i => 2 * n i + 1 with hcsdef
  have hodd' : ∀ i, Odd (cs i) := fun i => ⟨n i, rfl⟩
  have hcs0 : ∀ i, (cs i : ℝ) ≠ 0 := fun i h0 => by
    have : cs i = 0 := by exact_mod_cast h0
    exact (Int.not_even_iff_odd.2 (hodd' i)) (this ▸ Even.zero)
  have hn' : ∀ i, ∀ v ∈ L.get i, a v = (cs i : ℝ) • iWord k j v := hn
  have horth : ∀ i i', i ≠ i' → L.get i ⟂ L.get i' := by
    intro i i' hii'
    have hp := List.pairwise_iff_get.1 hL2
    rcases lt_or_gt_of_ne hii' with hlt | hgt
    · exact hp i i' hlt
    · exact (hp i' i hgt).symm
  have hdimi : ∀ i : Fin L.length, finrank ℝ (L.get i) = milnorM (k + 1) := fun i =>
    finrank_eq_milnorM_of_isMinimal hk8
      (h.isClifford_cliffFam (hM := (hmin i).2.1) (s := (cs i : ℝ)⁻¹)
        (a_a_of_eq_smul hI (iWord_mem_of_isInvar (hmin i).2.1) (hn' i)) (by field_simp [hcs0 i]))
      (h.isMinimal_cliffFam (hmin i) (inv_ne_zero (hcs0 i)))
  have hdimM : ∀ M ∈ L, finrank ℝ M = milnorM (k + 1) := fun M hM => by
    obtain ⟨i, rfl⟩ := List.mem_iff_get.1 hM
    exact hdimi i
  have hsum : L.length * milnorM (k + 1) = finrank ℝ E := by
    rw [← finrank_top ℝ E, ← hL3, List.map_congr_left hdimM, List.map_const', List.sum_replicate,
      smul_eq_mul]
  have hint : DirectSum.IsInternal (fun i : Fin L.length => L.get i) := by
    refine DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top ?_ ?_
    · exact OrthogonalFamily.independent
        (orthogonalFamily_iff_pairwise.2 fun i i' hii' => horth i i' hii')
    · exact eq_top_iff.2 (hL4.trans (foldr_sup_le_iSup L))
  set f : E →ₗ[ℝ] E := ((a * iWord k j : E →L[ℝ] E) : E →ₗ[ℝ] E) with hfdef
  have hf : ∀ i, MapsTo f (L.get i) (L.get i) := fun i v hv =>
    (hmin i).2.1 a IsOmegaOps.a_mem _ (iWord_mem_of_isInvar (hmin i).2.1 v hv)
  have hres : ∀ i, f.restrict (hf i) = (-(cs i : ℝ)) • LinearMap.id := fun i => by
    ext ⟨v, hv⟩
    have hee : iWord k j (iWord k j v) = -v := by
      have := congrArg (fun F : E →L[ℝ] E => F v) hI.sq
      simpa using this
    simp only [LinearMap.restrict_apply, LinearMap.smul_apply, LinearMap.id_apply,
      SetLike.val_smul, hfdef]
    change a (iWord k j v) = _
    rw [hn' i _ (iWord_mem_of_isInvar (hmin i).2.1 v hv), hee, smul_neg, ← neg_smul]
  refine ⟨L, cs, hmin, horth, hn', hodd', hsum, ?_, fun hall => ?_⟩
  swap
  · set K := LinearMap.ker (((a * a + 1 : E →L[ℝ] E)) : E →ₗ[ℝ] E) with hK
    have hle : ∀ i, L.get i ≤ K := fun i v hv => by
      change (a * a + 1 : E →L[ℝ] E) v = 0
      have h2 : ((cs i : ℝ)) ^ 2 = 1 := by exact_mod_cast hall i
      rw [_root_.add_apply, mul_apply_eq_comp,
        one_apply_eq_self,
        a_a_of_eq_smul hI (iWord_mem_of_isInvar (hmin i).2.1) (hn' i) v hv, h2, one_smul,
        neg_add_cancel]
    have htop : (⊤ : Submodule ℝ E) ≤ K := (hL4.trans (foldr_sup_le_iSup L)).trans (iSup_le hle)
    refine ContinuousLinearMap.ext fun v => ?_
    have hv : (a * a + 1 : E →L[ℝ] E) v = 0 := htop Submodule.mem_top
    rw [_root_.add_apply, one_apply_eq_self] at hv
    rw [_root_.neg_apply, one_apply_eq_self]
    exact eq_neg_of_add_eq_zero_left hv
  rw [LinearMap.trace_eq_sum_trace_restrict hint hf]
  simp only [hres, map_smul, LinearMap.trace_id, hdimi, smul_eq_mul, Finset.mul_sum]
  simp only [neg_mul, Finset.sum_neg_distrib, mul_comm]

end Ops

section Mat
open scoped Morse.MatrixInner
variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem exists_odd_of_mulVec' {A ii : Matrix ι ι ℝ} (hiiH : iiᴴ = -ii) (hii : ii * ii = -1)
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

end Mat

end Outright

theorem B_to_A : B → A := fun _ =>
  ⟨fun h hI hk _ hM => exists_eq_smul_iWord' h hI hk hM, @exists_odd_of_mulVec',
    fun h hI hk hk8 hodd => exists_decomp_two' h hI hk hk8 hodd,
    fun h hI hk hk8 hk3 _ _ hM₀ hM₁ _ _ h0 h1 hc₀ hc₁ =>
      exists_inter_two' h hI hk hk8 hk3 hM₀ hM₁ h0 h1 hc₀ hc₁⟩

#rt_check RoundTrip.V15_37.A_to_B [Morse.IsOmegaOps.exists_eq_smul_iWord, Morse.exists_odd_of_mulVec,
  Morse.exists_decomp_two, Morse.exists_inter_two]
#rt_check RoundTrip.V15_37.B_to_A [Morse.IsOmegaOps.exists_eq_smul_iWord, Morse.exists_odd_of_mulVec,
  Morse.exists_decomp_two, Morse.exists_inter_two]
#rt_overlap RoundTrip.V15_37.B_to_A [Morse.IsOmegaOps.exists_eq_smul_iWord,
  Morse.exists_odd_of_mulVec, Morse.exists_decomp_two, Morse.exists_inter_two]

end RoundTrip.V15_37
