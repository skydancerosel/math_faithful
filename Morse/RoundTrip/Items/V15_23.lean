import Morse
import RoundTrip.Check
import RoundTrip.Blind.V15_23

open Matrix Set Filter Topology Module
open scoped ContDiff

namespace RoundTrip.V15_23

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-- The project's statement (universes instantiated at `0`, any finite index type, any sequence
`J`): `dim 𝒯` is constant along `t ↦ x exp(tA)`; the stratum `omegaStratum J k p` (the points of
`Ω_k(n)` where `dim 𝒯 = dim 𝒯_p`) is open in `Ω_k(n)`, closed and compact; it is a slice
submanifold of `Mₙ(ℝ)` modelled on `𝒯_p` (Lemma 24.4 (i)), and a totally geodesic set of
orthogonal matrices in the sense of `Morse.IsTotGeo` (with `T = 𝒯`); for `k = 0` the stratum is
`Ω_0(n) = O(n)`. -/
def A : Prop :=
  type_of% @Morse.finrank_tanAlg_mul_exp.{0} ∧ type_of% @Morse.eventually_mem_omegaStratum.{0} ∧
    type_of% @Morse.isClosed_omegaStratum.{0} ∧ type_of% @Morse.isCompact_omegaStratum.{0} ∧
    type_of% @Morse.isSliceSubmanifold_omegaStratum.{0} ∧
    type_of% @Morse.isTotGeo_omegaStratum.{0} ∧ type_of% @Morse.omegaStratum_zero.{0}

theorem A_holds : A :=
  ⟨@Morse.finrank_tanAlg_mul_exp.{0}, @Morse.eventually_mem_omegaStratum.{0},
    @Morse.isClosed_omegaStratum.{0}, @Morse.isCompact_omegaStratum.{0},
    @Morse.isSliceSubmanifold_omegaStratum.{0}, @Morse.isTotGeo_omegaStratum.{0},
    @Morse.omegaStratum_zero.{0}⟩

/-! ## Vocabulary -/

section Vocab
variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem isACFam_iff (Js : ℕ → Mat ι) (m : ℕ) : IsACFam Js m ↔ Morse.IsAnticommFamily Js m :=
  ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.cs, h.anti⟩⟩

theorem omegaK_eq_omega (Js : ℕ → Mat ι) (k : ℕ) : OmegaK Js k = Morse.Omega Js k := by
  cases k with
  | zero => rfl
  | succ k =>
    ext J
    simp only [OmegaK, Morse.Omega, IsCplxStr, Morse.IsComplexStructure, AntiComm,
      Set.mem_ofPred_eq]
    refine and_congr Iff.rfl (forall_congr' fun α => forall_congr' fun _ => forall_congr' fun _ =>
      ⟨fun h => by rw [h, neg_neg], fun h => by rw [h, neg_neg]⟩)

theorem omegaK_subset_orth (Js : ℕ → Mat ι) (k : ℕ) : OmegaK Js k ⊆ Orth ι := by
  cases k with
  | zero => exact le_rfl
  | succ k => exact fun J hJ => hJ.1.1

theorem orth_iff {X : Mat ι} : X ∈ Orth ι ↔ Xᵀ * X = 1 := by
  rw [Orth, SetLike.mem_coe, mem_orthogonalGroup_iff']

theorem orth_iff' {X : Mat ι} : X ∈ Orth ι ↔ X * Xᵀ = 1 := by
  rw [Orth, SetLike.mem_coe, mem_orthogonalGroup_iff]

/-- The family where `J_k` is replaced by a point `x ∈ Ω_k(n)` (Milnor's `J_1, …, J_{k-1}, x`). -/
def famAt (Js : ℕ → Mat ι) (k : ℕ) (x : Mat ι) : ℕ → Mat ι := Function.update Js k x

theorem omega_famAt (Js : ℕ → Mat ι) (k : ℕ) (x : Mat ι) :
    Morse.Omega (famAt Js k x) k = Morse.Omega Js k := by
  cases k with
  | zero => rfl
  | succ k =>
    ext J
    simp only [Morse.Omega, Set.mem_ofPred_eq, famAt]
    refine and_congr Iff.rfl (forall_congr' fun α => forall_congr' fun _ => forall_congr' fun h => ?_)
    rw [Function.update_of_ne (by omega)]

theorem tanAlg_famAt (Js : ℕ → Mat ι) (k : ℕ) (x y : Mat ι) :
    Morse.tanAlg (famAt Js k x) k y = Morse.tanAlg Js k y := by
  ext A
  simp only [Morse.mem_tanAlg, famAt]
  refine and_congr Iff.rfl (and_congr Iff.rfl (forall_congr' fun α => forall_congr' fun _ =>
    forall_congr' fun h => ?_))
  rw [Function.update_of_ne (by omega)]

theorem omegaStratum_famAt (Js : ℕ → Mat ι) (k : ℕ) (x p : Mat ι) :
    Morse.omegaStratum (famAt Js k x) k p = Morse.omegaStratum Js k p := by
  ext y
  simp only [Morse.omegaStratum, Set.mem_ofPred_eq, omega_famAt]
  rw [tanAlg_famAt, tanAlg_famAt]

/-- For `x ∈ Ω_k(n)` (`J_1, …, J_{k-1}` anticommuting complex structures), `J_1, …, J_{k-1}, x` is
an anticommuting family (`k ≥ 1`; for `k = 0` the empty family). -/
theorem isAnticommFamily_famAt {Js : ℕ → Mat ι} {k : ℕ} (hJ : IsACFam Js (k - 1)) {x : Mat ι}
    (hx : x ∈ OmegaK Js k) : Morse.IsAnticommFamily (famAt Js k x) k := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exact ⟨fun α h1 h2 => absurd h2 (by omega), fun α _ h1 h2 _ _ _ => absurd h2 (by omega)⟩
  obtain ⟨k, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have hx' := hx
  simp only [Nat.add_sub_cancel] at hJ
  refine ⟨fun α h1 h2 => ?_, fun α β h1 h2 h3 h4 hne => ?_⟩
  · by_cases hα : α = k + 1
    · subst hα; simp only [famAt, Function.update_self]; exact hx.1
    · simp only [famAt, Function.update_of_ne hα]; exact hJ.1 α h1 (by omega)
  · by_cases hα : α = k + 1
    · subst hα
      simp only [famAt, Function.update_self, Function.update_of_ne (Ne.symm hne)]
      have := hx.2 β h3 (by omega)
      exact this
    · by_cases hβ : β = k + 1
      · subst hβ
        simp only [famAt, Function.update_self, Function.update_of_ne hα]
        have := hx.2 α h1 (by omega)
        rw [this, neg_neg]
      · simp only [famAt, Function.update_of_ne hα, Function.update_of_ne hβ]
        exact hJ.2 α β h1 (by omega) h3 (by omega) hne

end Vocab

/-! ## Calculus on `Mₙ(ℝ)` (Frobenius normed algebra; same topology, hence same derivatives, as
the blind files' elementwise norm) -/

section Calc
open scoped Morse.MatrixInner RealInnerProductSpace
variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem contDiffOn_frob_of_elem {c : ℝ → Mat ι} {s : Set ℝ}
    (hc : @ContDiffOn ℝ _ ℝ _ _ (Mat ι) Matrix.normedAddCommGroup Matrix.normedSpace ∞ c s) :
    ContDiffOn ℝ ∞ c s :=
  @ContDiff.comp_contDiffOn ℝ ℝ (Mat ι) (Mat ι) _ _ _ Matrix.normedAddCommGroup
    Matrix.normedSpace _ _ ∞ s _ c
    (@ContinuousLinearMap.contDiff ℝ (Mat ι) (Mat ι) _ Matrix.normedAddCommGroup
      Matrix.normedSpace _ _ ∞ (ContinuousLinearMap.id ℝ (Mat ι))) hc

theorem contDiffOn_elem_of_frob {c : ℝ → Mat ι} {s : Set ℝ} (hc : ContDiffOn ℝ ∞ c s) :
    @ContDiffOn ℝ _ ℝ _ _ (Mat ι) Matrix.normedAddCommGroup Matrix.normedSpace ∞ c s :=
  @ContDiff.comp_contDiffOn ℝ ℝ (Mat ι) (Mat ι) _ _ _ _ _ Matrix.normedAddCommGroup
    Matrix.normedSpace ∞ s _ c
    (@ContinuousLinearMap.contDiff ℝ (Mat ι) (Mat ι) _ _ _ Matrix.normedAddCommGroup
      Matrix.normedSpace ∞ (ContinuousLinearMap.id ℝ (Mat ι))) hc

theorem contDiff_elem_of_frob {c : ℝ → Mat ι} (hc : ContDiff ℝ ∞ c) :
    @ContDiff ℝ _ ℝ _ _ (Mat ι) Matrix.normedAddCommGroup Matrix.normedSpace ∞ c :=
  (@contDiffOn_univ ℝ _ ℝ _ _ (Mat ι) Matrix.normedAddCommGroup Matrix.normedSpace c ∞).1
    (contDiffOn_elem_of_frob hc.contDiffOn)

/-- The transpose, as a continuous linear map. -/
def trCLM : Mat ι →L[ℝ] Mat ι where
  toFun := Matrix.transpose
  map_add' := transpose_add
  map_smul' := transpose_smul
  cont := continuous_id.matrix_transpose

theorem hasDerivWithinAt_tr {c : ℝ → Mat ι} {v : Mat ι} {s : Set ℝ} {t : ℝ}
    (h : HasDerivWithinAt c v s t) : HasDerivWithinAt (fun u => (c u)ᵀ) vᵀ s t :=
  (trCLM (ι := ι)).hasFDerivAt.comp_hasDerivWithinAt t h

theorem hasDerivAt_tr {c : ℝ → Mat ι} {v : Mat ι} {t : ℝ}
    (h : HasDerivAt c v t) : HasDerivAt (fun u => (c u)ᵀ) vᵀ t :=
  (trCLM (ι := ι)).hasFDerivAt.comp_hasDerivAt t h

theorem eq_of_hasDerivWithinAt_eqOn {F G : ℝ → Mat ι} {F' G' : Mat ι} {s : Set ℝ} {t : ℝ}
    (hs : UniqueDiffWithinAt ℝ s t) (ht : t ∈ s) (hF : HasDerivWithinAt F F' s t)
    (hG : HasDerivWithinAt G G' s t) (h : EqOn F G s) : F' = G' :=
  hs.eq_deriv _ (hF.congr_of_mem (fun y hy => (h hy).symm) ht) hG

theorem frob_eq_inner (X Y : Mat ι) : frob X Y = ⟪X, Y⟫ := by
  rw [Morse.inner_def, frob, ← trace_transpose, transpose_mul, transpose_transpose,
    trace_mul_comm]
  rfl

theorem inner_sym_skew {S K : Mat ι} (hS : Sᵀ = S) (hK : Kᵀ = -K) : ⟪S, K⟫ = 0 :=
  Morse.inner_eq_zero_of_hermitian_of_skew (by rwa [conjTranspose_eq_transpose_of_trivial])
    (by rwa [conjTranspose_eq_transpose_of_trivial])

/-- In `O(n)`: a tangent vector at `p` is `p·S` with `S = pᵀv` skew. -/
theorem skew_of_mem_tanSet_orth {p v : Mat ι} (hv : v ∈ TanSet (Orth ι) p) :
    (pᵀ * v)ᵀ = -(pᵀ * v) := by
  obtain ⟨c, -, hcN, hc0, hcv⟩ := hv
  have h1 : HasDerivAt (fun s => (c s)ᵀ * c s) (vᵀ * c 0 + (c 0)ᵀ * v) 0 :=
    (hasDerivAt_tr hcv).mul hcv
  have h2 : (fun s => (c s)ᵀ * c s) = fun _ => (1 : Mat ι) := funext fun s => orth_iff.1 (hcN s)
  rw [h2] at h1
  have h3 := h1.unique (hasDerivAt_const 0 _)
  rw [hc0] at h3
  rw [transpose_mul, transpose_transpose, eq_neg_iff_add_eq_zero, h3]

/-- For `x ∈ Ω_k(n)` and `A ∈ 𝒯_x`, `xA` is a tangent vector of `Ω_k(n)` at `x` (the curve
`s ↦ x exp(sA)`). -/
theorem mul_mem_tanSet {Js : ℕ → Mat ι} {k : ℕ} {x A : Mat ι} (hx : x ∈ OmegaK Js k)
    (hA : A ∈ Morse.tanAlg Js k x) : x * A ∈ TanSet (OmegaK Js k) x := by
  refine ⟨fun s => x * NormedSpace.exp (s • A), contDiff_elem_of_frob
    (contDiff_const.mul (Morse.contDiff_exp_smul A)), fun s => ?_, by simp, ?_⟩
  · rw [omegaK_eq_omega] at hx ⊢
    exact Morse.mul_exp_mem_omega hx ((Morse.tanAlg Js k x).smul_mem s hA)
  · have := Morse.hasDerivAt_mul_exp_smul x A 0
    simpa using this

end Calc

/-! ## Slice charts of the project → the blind smooth charts `Mₙ(ℝ) ⊇ U → Mₙ(ℝ)` -/

section Chart
open scoped Manifold
variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- `C^∞` for the Frobenius norm on both sides gives `C^∞` for the elementwise norm. -/
theorem contDiffOn_mat_elem_of_frob {f : Mat ι → Mat ι} {s : Set (Mat ι)}
    (hf : @ContDiffOn ℝ _ (Mat ι) Morse.MatrixInner.normedAddCommGroup
      Morse.MatrixInner.normedSpace (Mat ι) Morse.MatrixInner.normedAddCommGroup
      Morse.MatrixInner.normedSpace ∞ f s) :
    @ContDiffOn ℝ _ (Mat ι) Matrix.normedAddCommGroup Matrix.normedSpace (Mat ι)
      Matrix.normedAddCommGroup Matrix.normedSpace ∞ f s := by
  have h1 := @ContDiffOn.comp ℝ (Mat ι) (Mat ι) (Mat ι) _ Matrix.normedAddCommGroup
    Matrix.normedSpace Morse.MatrixInner.normedAddCommGroup Morse.MatrixInner.normedSpace
    Morse.MatrixInner.normedAddCommGroup Morse.MatrixInner.normedSpace ∞ s s f id hf
    (@ContDiff.contDiffOn ℝ _ (Mat ι) Matrix.normedAddCommGroup Matrix.normedSpace (Mat ι)
      Morse.MatrixInner.normedAddCommGroup Morse.MatrixInner.normedSpace s id ∞
      (@ContinuousLinearMap.contDiff ℝ (Mat ι) (Mat ι) _ Matrix.normedAddCommGroup
      Matrix.normedSpace Morse.MatrixInner.normedAddCommGroup Morse.MatrixInner.normedSpace ∞
      (ContinuousLinearMap.id ℝ (Mat ι)))) (mapsTo_id s)
  exact @ContDiff.comp_contDiffOn ℝ (Mat ι) (Mat ι) (Mat ι) _ Matrix.normedAddCommGroup
    Matrix.normedSpace Morse.MatrixInner.normedAddCommGroup Morse.MatrixInner.normedSpace
    Matrix.normedAddCommGroup Matrix.normedSpace ∞ s id (f ∘ id)
    (@ContinuousLinearMap.contDiff ℝ (Mat ι) (Mat ι) _ Morse.MatrixInner.normedAddCommGroup
      Morse.MatrixInner.normedSpace Matrix.normedAddCommGroup Matrix.normedSpace ∞
      (ContinuousLinearMap.id ℝ (Mat ι))) h1

open scoped Morse.MatrixInner

/-- `(z, w) ↦ z + w`, `Z × Z^⊥ ≅ Mₙ(ℝ)`. -/
def sumEquiv (K : Submodule ℝ (Mat ι)) : (K × Kᗮ) ≃L[ℝ] Mat ι :=
  (Submodule.prodEquivOfIsCompl K Kᗮ K.isCompl_orthogonal).toContinuousLinearEquiv

theorem sumEquiv_apply (K : Submodule ℝ (Mat ι)) (q : K × Kᗮ) :
    sumEquiv K q = (q.1 : Mat ι) + (q.2 : Mat ι) := rfl

theorem sumEquiv_mem_iff (K : Submodule ℝ (Mat ι)) (q : K × Kᗮ) :
    sumEquiv K q ∈ K ↔ q.2 = 0 := by
  rw [sumEquiv_apply]
  constructor
  · intro h
    have h2 : (q.2 : Mat ι) ∈ K := by
      have := K.sub_mem h q.1.2
      rwa [add_sub_cancel_left] at this
    have h3 := Submodule.inf_orthogonal_eq_bot K
    ext1
    have : (q.2 : Mat ι) ∈ K ⊓ Kᗮ := ⟨h2, q.2.2⟩
    rw [h3] at this
    exact (Submodule.mem_bot ℝ).1 this
  · intro h; rw [h]; simpa using q.1.2

/-- **From slice submanifolds to the blind charts**: if near each point `p` of `S'`, `S'` agrees
with a slice submanifold `T ∋ p` of `Mₙ(ℝ)` modelled on `K × K^⊥`, then `S'` is a smooth
submanifold in the blind sense (`IsSmSubmfd`). -/
theorem isSmSubmfd_of_slice {S' : Set (Mat ι)}
    (h : ∀ p ∈ S', ∃ (K : Submodule ℝ (Mat ι)) (T : Set (Mat ι)),
      Milnor.IsSliceSubmanifold 𝓘(ℝ, Mat ι) K Kᗮ T ∧ p ∈ T ∧ ∀ᶠ y in 𝓝 p, (y ∈ S' ↔ y ∈ T)) :
    IsSmSubmfd S' := by
  intro p hp
  obtain ⟨K, T, hT, hpT, hev⟩ := h p hp
  obtain ⟨σ, hpσ⟩ := hT p hpT
  obtain ⟨U, hUev, hUo, hpU⟩ := mem_nhds_iff.1 hev
  set Lin := sumEquiv K
  set e₀ := σ.φ.toOpenPartialHomeomorph.trans Lin.toHomeomorph.toOpenPartialHomeomorph with he₀
  set e := e₀.restrOpen U hUo with hedef
  have hsrc : e.source = σ.φ.source ∩ U := by
    simp [hedef, he₀, OpenPartialHomeomorph.restrOpen_source, OpenPartialHomeomorph.trans_source]
  have happ : ∀ x, e x = Lin (σ.φ x) := fun x => rfl
  have hsymm : ∀ y, e.symm y = σ.φ.invFun (Lin.symm y) := fun y => rfl
  have htgt : e.target ⊆ Lin '' σ.φ.target := by
    intro y hy
    have hy' : e.symm y ∈ e.source := e.map_target hy
    refine ⟨σ.φ (e.symm y), σ.φ.map_source (by rw [hsrc] at hy'; exact hy'.1), ?_⟩
    rw [← happ, e.right_inv hy]
  refine ⟨e, K, by rw [hsrc]; exact ⟨hpσ, hpU⟩, ?_, ?_, ?_⟩
  · rw [hsrc]
    refine contDiffOn_mat_elem_of_frob ?_
    have h1 := (contMDiffOn_iff_contDiffOn.1 σ.φ.contMDiffOn_toFun).mono
      (inter_subset_left : σ.φ.source ∩ U ⊆ σ.φ.source)
    exact Lin.contDiff.comp_contDiffOn h1
  · refine contDiffOn_mat_elem_of_frob ?_
    have h1 := contMDiffOn_iff_contDiffOn.1 σ.φ.contMDiffOn_invFun
    have h2 : ContDiffOn ℝ ∞ (σ.φ.invFun ∘ Lin.symm) e.target := by
      refine h1.comp Lin.symm.contDiff.contDiffOn fun y hy => ?_
      obtain ⟨z, hz, rfl⟩ := htgt hy
      simp only [ContinuousLinearEquiv.symm_apply_apply]; exact hz
    exact h2
  · ext y
    constructor
    · rintro ⟨x, ⟨hx, hxS⟩, rfl⟩
      refine ⟨e.map_source hx, ?_⟩
      rw [hsrc] at hx
      have hxT := (hUev hx.2).1 hxS
      rw [SetLike.mem_coe, happ, sumEquiv_mem_iff]
      exact (σ.slice x hx.1).1 hxT
    · rintro ⟨hy, hyK⟩
      refine ⟨e.symm y, ⟨e.map_target hy, ?_⟩, e.right_inv hy⟩
      have hx := e.map_target hy
      rw [hsrc] at hx
      refine (hUev hx.2).2 ((σ.slice _ hx.1).2 ?_)
      rw [SetLike.mem_coe, ← e.right_inv hy, happ, sumEquiv_mem_iff] at hyK
      exact hyK

end Chart

/-! ## Total geodesy (Milnor's footnote): every geodesic of `Ω_k(n)` is a geodesic of `O(n)`

Proved directly for the blind induced-metric notions: along a geodesic `γ` of `Ω_k(n)`,
`X = γᵀγ'` lies in `𝒯_γ` (differentiate `γᵀγ = I`, `γ² = −I`, `γJ_α = −J_αγ`), and so does `X'`;
`X' = γ'ᵀγ' + γᵀγ''` and `γX' ∈ T_γΩ_k(n)` give `⟨X', X'⟩ = 0`, so `γᵀγ''` is symmetric, i.e.
`γ''` is normal to `O(n)` (whose tangent vectors at `γ` are the `γS`, `S` skew). -/

section Elem
open scoped Matrix.Norms.Elementwise
variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem iteratedDerivWithin_two_eq (γ : ℝ → Mat ι) (s : Set ℝ) (t : ℝ) :
    iteratedDerivWithin 2 γ s t = derivWithin (derivWithin γ s) s t := by
  rw [iteratedDerivWithin_eq_iterate]; rfl

end Elem

section TotGeo
open scoped Morse.MatrixInner RealInnerProductSpace
variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem omegaK_sq {Js : ℕ → Mat ι} {k : ℕ} (hk : k ≠ 0) {x : Mat ι} (hx : x ∈ OmegaK Js k) :
    x * x = -1 := by
  obtain ⟨k, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  exact hx.1.2

theorem omegaK_anti {Js : ℕ → Mat ι} {k : ℕ} {x : Mat ι} (hx : x ∈ OmegaK Js k) {α : ℕ}
    (h1 : 1 ≤ α) (h2 : α < k) : x * Js α = -(Js α * x) := by
  obtain ⟨k, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  exact hx.2 α h1 (by omega)

theorem transpose_cs {J : Mat ι} (hJ : IsCplxStr J) : Jᵀ = -J := by
  have h1 : Jᵀ * J = 1 := orth_iff.1 hJ.1
  calc Jᵀ = Jᵀ * (-(J * J)) := by rw [hJ.2, neg_neg, Matrix.mul_one]
    _ = -J := by rw [Matrix.mul_neg, ← Matrix.mul_assoc, h1, Matrix.one_mul]

theorem isGeodOn_orth_of_omegaK {Js : ℕ → Mat ι} {k : ℕ} (hJ : IsACFam Js (k - 1))
    {γ : ℝ → Mat ι} {a b : ℝ} (h : IsGeodOn (OmegaK Js k) γ a b) : IsGeodOn (Orth ι) γ a b := by
  obtain ⟨hab, hsm, hmem, hnorm⟩ := h
  refine ⟨hab, hsm, fun t ht => omegaK_subset_orth Js k (hmem t ht), fun t ht v hv => ?_⟩
  set s := Icc a b with hsdef
  have hs : UniqueDiffOn ℝ s := uniqueDiffOn_Icc hab
  have hsm' : ContDiffOn ℝ ∞ γ s := contDiffOn_frob_of_elem hsm
  set D1 := derivWithin γ s with hD1def
  set D2 := derivWithin D1 s with hD2def
  have hD1sm : ContDiffOn ℝ ∞ D1 s := hsm'.derivWithin hs (by simp)
  have hγd : ∀ u ∈ s, HasDerivWithinAt γ (D1 u) s u := fun u hu =>
    ((hsm'.differentiableOn (by simp)) u hu).hasDerivWithinAt
  have hD1d : ∀ u ∈ s, HasDerivWithinAt D1 (D2 u) s u := fun u hu =>
    ((hD1sm.differentiableOn (by simp)) u hu).hasDerivWithinAt
  have hγo : ∀ u ∈ s, (γ u)ᵀ * γ u = 1 := fun u hu =>
    orth_iff.1 (omegaK_subset_orth Js k (hmem u hu))
  have hγo' : ∀ u ∈ s, γ u * (γ u)ᵀ = 1 := fun u hu =>
    orth_iff'.1 (omegaK_subset_orth Js k (hmem u hu))
  set X : ℝ → Mat ι := fun u => (γ u)ᵀ * D1 u with hXdef
  have hD1X : ∀ u ∈ s, D1 u = γ u * X u := fun u hu => by
    simp only [X]; rw [← Matrix.mul_assoc, hγo' u hu, Matrix.one_mul]
  have hJcs : ∀ α, 1 ≤ α → α < k → IsCplxStr (Js α) := fun α h1 h2 => hJ.1 α h1 (by omega)
  -- `X ∈ 𝒯_γ` on `[a, b]`
  have hXa : ∀ u ∈ s, (X u)ᵀ = -(X u) := fun u hu => by
    have e := eq_of_hasDerivWithinAt_eqOn (hs u hu) hu
      ((hasDerivWithinAt_tr (hγd u hu)).mul (hγd u hu)) (hasDerivWithinAt_const u s (1 : Mat ι))
      (fun y hy => hγo y hy)
    simp only [X, transpose_mul, transpose_transpose]
    rw [eq_neg_iff_add_eq_zero]; exact e
  have hXb : k ≠ 0 → ∀ u ∈ s, X u * γ u = -(γ u * X u) := fun hk u hu => by
    have e := eq_of_hasDerivWithinAt_eqOn (hs u hu) hu ((hγd u hu).mul (hγd u hu))
      (hasDerivWithinAt_const u s (-1 : Mat ι)) (fun y hy => omegaK_sq hk (hmem y hy))
    rw [hD1X u hu] at e
    have e2 := congrArg (fun M => (γ u)ᵀ * M) e
    simp only [Matrix.mul_add, Matrix.mul_zero, ← Matrix.mul_assoc, hγo u hu,
      Matrix.one_mul] at e2
    rw [eq_neg_iff_add_eq_zero]; exact e2
  have hXc : ∀ α, 1 ≤ α → α < k → ∀ u ∈ s, X u * Js α = Js α * X u := fun α h1 h2 u hu => by
    have e := eq_of_hasDerivWithinAt_eqOn (hs u hu) hu ((hγd u hu).mul_const (Js α))
      ((hγd u hu).const_mul (Js α)).neg (fun y hy => omegaK_anti (hmem y hy) h1 h2)
    have hJT := transpose_cs (hJcs α h1 h2)
    have hγJ : Js α * (γ u)ᵀ = -((γ u)ᵀ * Js α) := by
      have := congrArg Matrix.transpose (omegaK_anti (hmem u hu) h1 h2)
      simp only [transpose_mul, transpose_neg, hJT, Matrix.neg_mul, Matrix.mul_neg,
        neg_neg] at this
      rw [← this, neg_neg]
    simp only [X]
    rw [Matrix.mul_assoc, e, ← Matrix.mul_assoc, hγJ]
    simp only [Matrix.neg_mul, Matrix.mul_neg, neg_neg, Matrix.mul_assoc]
  -- `X'` at `t`
  set X' := (D1 t)ᵀ * D1 t + (γ t)ᵀ * D2 t with hX'def
  have hXd : ∀ u ∈ s, HasDerivWithinAt X ((D1 u)ᵀ * D1 u + (γ u)ᵀ * D2 u) s u := fun u hu =>
    (hasDerivWithinAt_tr (hγd u hu)).mul (hD1d u hu)
  have hX't : X' ∈ Morse.tanAlg Js k (γ t) := by
    refine ⟨?_, fun hk => ?_, fun α h1 h2 => ?_⟩
    · rw [conjTranspose_eq_transpose_of_trivial]
      exact eq_of_hasDerivWithinAt_eqOn (hs t ht) ht (hasDerivWithinAt_tr (hXd t ht))
        (hXd t ht).neg (fun u hu => hXa u hu)
    · have e : X' * γ t + X t * D1 t = -(D1 t * X t + γ t * X') :=
        eq_of_hasDerivWithinAt_eqOn (hs t ht) ht ((hXd t ht).mul (hγd t ht))
          ((hγd t ht).mul (hXd t ht)).neg (fun u hu => hXb hk u hu)
      have e2 : X t * D1 t = -(γ t * X t * X t) := by
        rw [hD1X t ht, ← Matrix.mul_assoc, hXb hk t ht, Matrix.neg_mul]
      have e3 : D1 t * X t = γ t * X t * X t := by rw [hD1X t ht]
      rw [e2, e3] at e
      calc X' * γ t = X' * γ t + -(γ t * X t * X t) + γ t * X t * X t := by abel
        _ = -(γ t * X') := by rw [e]; abel
    · exact eq_of_hasDerivWithinAt_eqOn (hs t ht) ht ((hXd t ht).mul_const (Js α))
        ((hXd t ht).const_mul (Js α)) (fun u hu => hXc α h1 h2 u hu)
  have hX'skew : X'ᵀ = -X' := by
    have := hX't.1; rwa [conjTranspose_eq_transpose_of_trivial] at this
  -- the geodesic equation of `Ω_k(n)` against `γX' ∈ T_γΩ_k(n)`
  have hn := hnorm t ht _ (mul_mem_tanSet (hmem t ht) hX't)
  rw [iteratedDerivWithin_two_eq] at hn
  change frob (D2 t) _ = 0 at hn
  rw [frob_eq_inner, real_inner_comm, Morse.inner_mul_left_adj,
    conjTranspose_eq_transpose_of_trivial] at hn
  have hγD2 : (γ t)ᵀ * D2 t = X' - (D1 t)ᵀ * D1 t := by rw [hX'def]; abel
  have hsym : ((D1 t)ᵀ * D1 t)ᵀ = (D1 t)ᵀ * D1 t := by
    rw [transpose_mul, transpose_transpose]
  rw [hγD2, inner_sub_right, real_inner_comm ((D1 t)ᵀ * D1 t) X', inner_sym_skew hsym hX'skew,
    sub_zero,
    real_inner_self_eq_norm_sq] at hn
  have hX'0 : X' = 0 := norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 hn)
  -- the conclusion for `O(n)`
  have hS := skew_of_mem_tanSet_orth hv
  have hv' : v = γ t * ((γ t)ᵀ * v) := by rw [← Matrix.mul_assoc, hγo' t ht, Matrix.one_mul]
  rw [iteratedDerivWithin_two_eq]
  change frob (D2 t) _ = 0
  rw [frob_eq_inner, hv', real_inner_comm, Morse.inner_mul_left_adj,
    conjTranspose_eq_transpose_of_trivial, hγD2, hX'0, zero_sub, inner_neg_right,
    real_inner_comm ((D1 t)ᵀ * D1 t), inner_sym_skew hsym hS, neg_zero]

end TotGeo


/-- The two conjuncts of `A` used for `B` (the stratum is open in `Ω_k(n)`, and it is a slice
submanifold). `#rt_check` cannot be run on a proof from `A` itself: A's conjunct
`isTotGeo_omegaStratum` has the *proof* `isSliceSubmanifold_omegaStratum hJ p` inside its statement
(`IsTotGeo (isSliceSubmanifold_omegaStratum hJ p) (tanAlg J k)`), so every term mentioning `A`
reaches that banned theorem. -/
def A2 : Prop :=
  type_of% @Morse.eventually_mem_omegaStratum.{0} ∧ type_of% @Morse.isSliceSubmanifold_omegaStratum.{0}

theorem A_to_A2 (hA : A) : A2 := ⟨hA.2.1, hA.2.2.2.2.1⟩

/-- A ⇒ B (through `A2`). `Ω_k(n) ⊆ O(n)` is definitional. **Submanifold**: at `p ∈ Ω_k(n)`, take
the family `J_1, …, J_{k-1}, p` (anticommuting, `famAt`), so that A's
`isSliceSubmanifold_omegaStratum` makes the stratum of `p` a slice submanifold modelled on
`𝒯_p × 𝒯_p^⊥`, and A's `eventually_mem_omegaStratum` says that near `p`, `Ω_k(n)` is that stratum;
the slice chart, followed by `(z, w) ↦ z + w`, is a blind chart (`isSmSubmfd_of_slice`).
**Totally geodesic**: the blind notion (geodesics of `Ω_k(n)` are geodesics of `O(n)` for the
induced metric) is proved directly (`isGeodOn_orth_of_omegaK`); A's `isTotGeo_omegaStratum` (a
description of the stratum's geodesics in the project's vocabulary) is not used. -/
theorem A2_to_B : A2 → B := by
  rintro ⟨hev, hslice⟩ n k Js hJ
  refine ⟨omegaK_subset_orth Js k, isSmSubmfd_of_slice fun p hp => ?_,
    fun γ a b h => isGeodOn_orth_of_omegaK hJ h⟩
  have hJ' := isAnticommFamily_famAt hJ hp
  have hpΩ : p ∈ Morse.Omega (famAt Js k p) k := by
    rw [omega_famAt, ← omegaK_eq_omega]; exact hp
  have hpS : p ∈ Morse.omegaStratum (famAt Js k p) k p := ⟨hpΩ, rfl⟩
  refine ⟨Morse.tanAlg (famAt Js k p) k p, Morse.omegaStratum (famAt Js k p) k p,
    hslice hJ' p, hpS, ?_⟩
  filter_upwards [hev hJ' hpS] with y hy
  rw [omegaK_eq_omega, ← omega_famAt Js k p]
  exact ⟨hy, fun h => h.1⟩

theorem A_to_B : A → B := fun hA => A2_to_B (A_to_A2 hA)

#rt_check RoundTrip.V15_23.A2_to_B [Morse.finrank_tanAlg_mul_exp, Morse.eventually_mem_omegaStratum,
  Morse.isClosed_omegaStratum, Morse.isCompact_omegaStratum, Morse.isSliceSubmanifold_omegaStratum,
  Morse.isTotGeo_omegaStratum, Morse.omegaStratum_zero]

/-! ## B ⇒ A, only vacuously: A re-proved outright (the project's proofs, copied) -/

section Outright
open scoped Morse.MatrixInner RealInnerProductSpace Manifold
variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem finrank_tanAlg_mul_exp' {J : ℕ → Mat ι} {k : ℕ} {x : Mat ι} {A : Matrix ι ι ℝ} (hA : A ∈ Morse.tanAlg J k x) :
    finrank ℝ (Morse.tanAlg J k (x * NormedSpace.exp A)) = finrank ℝ (Morse.tanAlg J k x) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [Morse.tanAlg_zero J _ x]
  obtain ⟨h1, h2, h3⟩ := hA
  set g := NormedSpace.exp ((1 / 2 : ℝ) • A) with hgdef
  have hA2 : ((1 / 2 : ℝ) • A)ᴴ = -((1 / 2 : ℝ) • A) := by
    rw [conjTranspose_smul, star_trivial, h1, smul_neg]
  have hg : gᴴ * g = 1 := Morse.exp_conjTranspose_mul_exp_of_skew hA2
  have hgJ : ∀ α, 1 ≤ α → α < k → g * J α = J α * g := fun α ha hb =>
    (((show Commute A (J α) from h3 α ha hb).smul_left (1 / 2 : ℝ)).exp_left).eq
  have hgx : gᴴ * x * g = x * NormedSpace.exp A := by
    have hAx : (1 / 2 : ℝ) • A * x = -(x * ((1 / 2 : ℝ) • A)) := by
      rw [smul_mul_assoc, h2 hk.ne', mul_smul_comm, smul_neg]
    have e1 := Morse.mul_exp_eq_exp_neg_mul hAx
    have hgH : gᴴ = NormedSpace.exp (-((1 / 2 : ℝ) • A)) := by
      rw [hgdef, ← Matrix.exp_conjTranspose, hA2]
    rw [hgH, ← e1, Matrix.mul_assoc, hgdef, Morse.exp_smul_mul_exp_smul]
    norm_num
  rw [← hgx, Morse.finrank_tanAlg_conj hg hgJ]

theorem eventually_finrank_tanAlg' {J : ℕ → Mat ι} {k : ℕ} (hJ : Morse.IsAnticommFamily J k) {x : Matrix ι ι ℝ}
    (hx : x ∈ Morse.Omega J k) :
    ∀ᶠ y in 𝓝 x, y ∈ Morse.Omega J k → finrank ℝ (Morse.tanAlg J k y) = finrank ℝ (Morse.tanAlg J k x) := by
  obtain ⟨L, -, hL⟩ := Morse.exists_local_log hJ hx
  filter_upwards [hL] with y hy hyΩ
  obtain ⟨hmem, hxy⟩ := hy hyΩ
  rw [← hxy, finrank_tanAlg_mul_exp' hmem]

theorem eventually_mem_omegaStratum' {J : ℕ → Mat ι} {k : ℕ} (hJ : Morse.IsAnticommFamily J k) {p x : Matrix ι ι ℝ}
    (hx : x ∈ Morse.omegaStratum J k p) : ∀ᶠ y in 𝓝 x, y ∈ Morse.Omega J k → y ∈ Morse.omegaStratum J k p := by
  filter_upwards [eventually_finrank_tanAlg' hJ hx.1] with y hy hyΩ
  exact ⟨hyΩ, (hy hyΩ).trans hx.2⟩

theorem isClosed_omegaStratum' {J : ℕ → Mat ι} {k : ℕ} (hJ : Morse.IsAnticommFamily J k) (p : Matrix ι ι ℝ) :
    IsClosed (Morse.omegaStratum J k p) := by
  refine isClosed_of_closure_subset fun y hy => ?_
  have hyΩ : y ∈ Morse.Omega J k :=
    closure_minimal (Morse.omegaStratum_subset p) (Morse.isClosed_omega J k) hy
  have h := eventually_finrank_tanAlg' hJ hyΩ
  obtain ⟨z, hz, hzS⟩ := mem_closure_iff_nhds.1 hy _ h
  exact ⟨hyΩ, ((hz hzS.1).symm.trans hzS.2)⟩

theorem isCompact_omegaStratum' {J : ℕ → Mat ι} {k : ℕ} (hJ : Morse.IsAnticommFamily J k) (p : Matrix ι ι ℝ) :
    IsCompact (Morse.omegaStratum J k p) :=
  (Morse.isCompact_omega J k).of_isClosed_subset (isClosed_omegaStratum' hJ p) (Morse.omegaStratum_subset p)

theorem isSliceSubmanifold_omegaStratum' {J : ℕ → Mat ι} {k : ℕ} (hJ : Morse.IsAnticommFamily J k) (p : Matrix ι ι ℝ) :
    Milnor.IsSliceSubmanifold 𝓘(ℝ, Matrix ι ι ℝ) (Morse.tanAlg J k p) (Morse.tanAlg J k p)ᗮ
      (Morse.omegaStratum J k p) := by
  refine Morse.isSliceSubmanifold_of_param fun x hx => ?_
  set K := Morse.tanAlg J k x with hKdef
  have hxo := Morse.omega_orth hx.1
  have hK : finrank ℝ (Morse.tanAlg J k p) = finrank ℝ K := hx.2.symm
  have hKo : finrank ℝ (Morse.tanAlg J k p)ᗮ = finrank ℝ Kᗮ := by
    have h1 := Submodule.finrank_add_finrank_orthogonal (Morse.tanAlg J k p)
    have h2 := Submodule.finrank_add_finrank_orthogonal K
    omega
  set Lz : Morse.tanAlg J k p ≃L[ℝ] K := ContinuousLinearEquiv.ofFinrankEq hK
  set Lw : (Morse.tanAlg J k p)ᗮ ≃L[ℝ] Kᗮ := ContinuousLinearEquiv.ofFinrankEq hKo
  set Ψ : Morse.tanAlg J k p × (Morse.tanAlg J k p)ᗮ → Matrix ι ι ℝ := fun q =>
    x * (NormedSpace.exp ((Lz q.1 : K) : Matrix ι ι ℝ) + ((Lw q.2 : Kᗮ) : Matrix ι ι ℝ))
    with hΨdef
  set f₁ : Morse.tanAlg J k p × (Morse.tanAlg J k p)ᗮ → Matrix ι ι ℝ := fun q => ((Lz q.1 : K) : Matrix ι ι ℝ)
  set f₂ : Morse.tanAlg J k p × (Morse.tanAlg J k p)ᗮ → Matrix ι ι ℝ := fun q => ((Lw q.2 : Kᗮ) : Matrix ι ι ℝ)
  set F₁ : Morse.tanAlg J k p × (Morse.tanAlg J k p)ᗮ →L[ℝ] Matrix ι ι ℝ :=
    (K.subtypeL.comp (Lz : _ →L[ℝ] K)).comp (ContinuousLinearMap.fst ℝ _ _)
  set F₂ : Morse.tanAlg J k p × (Morse.tanAlg J k p)ᗮ →L[ℝ] Matrix ι ι ℝ :=
    (Kᗮ.subtypeL.comp (Lw : _ →L[ℝ] Kᗮ)).comp (ContinuousLinearMap.snd ℝ _ _)
  have hf₁ : f₁ = F₁ := rfl
  have hf₂ : f₂ = F₂ := rfl
  have hΨc : ContDiff ℝ ∞ Ψ := by
    refine contDiff_const.mul (ContDiff.add ?_ ?_)
    · exact Morse.contDiff_exp_matrix.comp F₁.contDiff
    · exact F₂.contDiff
  have hΨ0 : Ψ 0 = x := by simp [hΨdef]
  -- the derivative at `0`
  have hcompl : IsCompl K Kᗮ := Submodule.isCompl_orthogonal K
  set e : (Morse.tanAlg J k p × (Morse.tanAlg J k p)ᗮ) ≃L[ℝ] Matrix ι ι ℝ :=
    ((Lz.prodCongr Lw).trans
      (Submodule.prodEquivOfIsCompl K Kᗮ hcompl).toContinuousLinearEquiv).trans
      (Morse.mulLeftIso x hxo).toContinuousLinearEquiv with hedef
  have he : ∀ q, e q = x * (((Lz q.1 : K) : Matrix ι ι ℝ) + ((Lw q.2 : Kᗮ) : Matrix ι ι ℝ)) :=
    fun q => rfl
  have hexp : HasFDerivAt (NormedSpace.exp : Matrix ι ι ℝ → Matrix ι ι ℝ)
      (ContinuousLinearMap.id ℝ (Matrix ι ι ℝ)) (f₁ 0) := by
    have := (hasStrictFDerivAt_exp_zero_of_radius_pos (𝕂 := ℝ) (𝔸 := Matrix ι ι ℝ)
      (by rw [NormedSpace.expSeries_radius_eq_top]; exact ENNReal.zero_lt_top)).hasFDerivAt
    have h0 : f₁ 0 = 0 := by simp [f₁]
    rw [h0]
    exact this.congr_fderiv (by ext; simp)
  refine ⟨Ψ, hΨc, hΨ0, ⟨e, ?_⟩, ?_⟩
  · have h1 := hexp.comp (0 : Morse.tanAlg J k p × (Morse.tanAlg J k p)ᗮ) F₁.hasFDerivAt
    have h3 := ((Morse.mulLeftIso x hxo).toContinuousLinearEquiv : Matrix ι ι ℝ →L[ℝ]
      Matrix ι ι ℝ).hasFDerivAt.comp (0 : Morse.tanAlg J k p × (Morse.tanAlg J k p)ᗮ)
      (h1.add F₂.hasFDerivAt)
    have hEq : (((Morse.mulLeftIso x hxo).toContinuousLinearEquiv : Matrix ι ι ℝ →L[ℝ]
      Matrix ι ι ℝ).comp ((ContinuousLinearMap.id ℝ (Matrix ι ι ℝ)).comp F₁ + F₂)) =
        (e : _ →L[ℝ] Matrix ι ι ℝ) := by
      refine ContinuousLinearMap.ext fun q => ?_
      simp only [ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.id_apply, ContinuousLinearEquiv.coe_coe, he, _root_.add_apply]
      rfl
    have h4 := h3.congr_fderiv hEq
    exact h4.congr_of_eventuallyEq (Eventually.of_forall fun q => rfl)
  refine ⟨?_, ?_⟩
  · refine Eventually.of_forall fun q hq => ?_
    have hq' : Ψ q = x * NormedSpace.exp ((Lz q.1 : K) : Matrix ι ι ℝ) := by
      simp [hΨdef, hq]
    rw [hq']
    exact ⟨Morse.mul_exp_mem_omega hx.1 (Lz q.1).2,
      (finrank_tanAlg_mul_exp' (Lz q.1).2).trans hx.2⟩
  · obtain ⟨L, hLt, hLev⟩ := Morse.exists_local_log hJ hx.1
    set P := K.starProjection
    set g : Morse.tanAlg J k p × (Morse.tanAlg J k p)ᗮ → Morse.tanAlg J k p := fun q =>
      Lz.symm ⟨P (L (Ψ q)), K.starProjection_apply_mem _⟩
    have hΨt : Tendsto Ψ (𝓝 0) (𝓝 x) := by
      have := hΨc.continuous.tendsto 0
      rwa [hΨ0] at this
    refine ⟨g, ?_, ?_⟩
    · have h1 : Tendsto (fun q => (⟨P (L (Ψ q)), K.starProjection_apply_mem _⟩ : K)) (𝓝 0)
          (𝓝 0) := by
        rw [tendsto_subtype_rng]
        have := (P.continuous.tendsto 0).comp (hLt.comp hΨt)
        rw [map_zero] at this
        exact this
      have := (Lz.symm.continuous.tendsto 0).comp h1
      rw [map_zero] at this
      exact this
    · filter_upwards [hΨt.eventually hLev] with q hq hqS
      obtain ⟨hmem, hxq⟩ := hq hqS.1
      have hP : P (L (Ψ q)) = L (Ψ q) := Submodule.starProjection_eq_self_iff.2 hmem
      have : ((Lz (g q) : K) : Matrix ι ι ℝ) = L (Ψ q) := by
        simp only [g, ContinuousLinearEquiv.apply_symm_apply]
        exact hP
      simp only [hΨdef, map_zero, ZeroMemClass.coe_zero, add_zero]
      rw [this]
      exact hxq

theorem isTotGeo_omegaStratum' {J : ℕ → Mat ι} {k : ℕ} (hJ : Morse.IsAnticommFamily J k) (p : Matrix ι ι ℝ) :
    Morse.IsTotGeo (isSliceSubmanifold_omegaStratum' hJ p) (Morse.tanAlg J k) where
  unitary _ hx := Morse.omega_orth hx.1
  skew _ _ _ hA := hA.1
  mul_exp_mem _ hx _ hA :=
    ⟨Morse.mul_exp_mem_omega hx.1 hA, (finrank_tanAlg_mul_exp' hA).trans hx.2⟩
  mem_mul_exp _ _ _ hA := Morse.mem_tanAlg_mul_exp hA
  finrank_eq _ hx := hx.2

theorem omegaStratum_zero' (J : ℕ → Matrix ι ι ℝ) (p : Matrix ι ι ℝ) :
    Morse.omegaStratum J 0 p = Morse.Omega J 0 := by
  ext x
  exact ⟨fun h => h.1, fun h => ⟨h, by rw [Morse.tanAlg_zero J x p]⟩⟩

end Outright

section AbsSec
open scoped Morse.MatrixInner Manifold

/-- `A` with the proof `isSliceSubmanifold_omegaStratum hJ p` inside its sixth conjunct abstracted
(equivalent to `A` by proof irrelevance), so that `#rt_check` can run. -/
def Aabs : Prop :=
  type_of% @Morse.finrank_tanAlg_mul_exp.{0} ∧ type_of% @Morse.eventually_mem_omegaStratum.{0} ∧
    type_of% @Morse.isClosed_omegaStratum.{0} ∧ type_of% @Morse.isCompact_omegaStratum.{0} ∧
    type_of% @Morse.isSliceSubmanifold_omegaStratum.{0} ∧
    (∀ {ι : Type} [Fintype ι] [DecidableEq ι] {J : ℕ → Matrix ι ι ℝ} {k : ℕ},
      Morse.IsAnticommFamily J k → ∀ (p : Matrix ι ι ℝ)
      (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, Matrix ι ι ℝ) (Morse.tanAlg J k p)
        (Morse.tanAlg J k p)ᗮ (Morse.omegaStratum J k p)), Morse.IsTotGeo hN (Morse.tanAlg J k)) ∧
    type_of% @Morse.omegaStratum_zero.{0}

/-- B ⇒ `Aabs`, only vacuously: proved outright. B says that `Ω_k(n)` is a submanifold (charts of
varying dimension) and totally geodesic in Milnor's sense; A's statements about the strata
(constancy of `dim 𝒯` along geodesics, openness, closedness, compactness, slice structure modelled
on `𝒯_p × 𝒯_p^⊥`, the `IsTotGeo` structure) are not consequences of B. -/
theorem B_to_Aabs : B → Aabs := fun _ =>
  ⟨@fun ι _ _ J k x A hA => finrank_tanAlg_mul_exp' hA,
    @fun ι _ _ J k hJ p x hx => eventually_mem_omegaStratum' hJ hx,
    @fun ι _ _ J k hJ p => isClosed_omegaStratum' hJ p,
    @fun ι _ _ J k hJ p => isCompact_omegaStratum' hJ p,
    @fun ι _ _ J k hJ p => isSliceSubmanifold_omegaStratum' hJ p,
    @fun ι _ _ J k hJ p hN => isTotGeo_omegaStratum' hJ p,
    @fun ι _ _ J p => omegaStratum_zero' J p⟩

theorem Aabs_to_A (h : Aabs) : A :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1,
    @fun ι _ _ J k hJ p => h.2.2.2.2.2.1 hJ p (Morse.isSliceSubmanifold_omegaStratum hJ p),
    h.2.2.2.2.2.2⟩

theorem B_to_A : B → A := fun hB => Aabs_to_A (B_to_Aabs hB)

end AbsSec

#rt_check RoundTrip.V15_23.B_to_Aabs [Morse.finrank_tanAlg_mul_exp,
  Morse.eventually_mem_omegaStratum, Morse.isClosed_omegaStratum, Morse.isCompact_omegaStratum,
  Morse.isSliceSubmanifold_omegaStratum, Morse.isTotGeo_omegaStratum, Morse.omegaStratum_zero]
#rt_overlap RoundTrip.V15_23.B_to_Aabs [Morse.finrank_tanAlg_mul_exp,
  Morse.eventually_mem_omegaStratum, Morse.isClosed_omegaStratum, Morse.isCompact_omegaStratum,
  Morse.isSliceSubmanifold_omegaStratum, Morse.isTotGeo_omegaStratum, Morse.omegaStratum_zero]

end

end RoundTrip.V15_23
