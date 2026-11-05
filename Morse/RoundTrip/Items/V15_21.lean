import Morse
import RoundTrip.Check
import RoundTrip.Blind.V15_21

open Matrix Set Filter Topology Module
open scoped ContDiff

namespace RoundTrip.V15_21

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-- The project's statement (universes instantiated at `0`): **a set with local parametrizations is
a slice submanifold** (`isSliceSubmanifold_of_param`, inverse function theorem), and, for a
**totally geodesic set of orthogonal matrices** `IsTotGeo hN T` (a slice submanifold `N` of
orthogonal matrices with spaces `T x` of skew matrices, `dim T x = dim N`, `x exp A ∈ N` and
`A ∈ T(x exp A)` for `A ∈ T x`): the tangent space at `x` is `x·T x`; `t ↦ x exp(tA)`, `A ∈ T x`, is a
geodesic of `N` on `ℝ`; every unbroken geodesic `[0, 1] → N` from `p` is `t ↦ p exp(tV)`,
`V ∈ T p`; `exp_x(xA) = x exp A`; `N` is geodesically complete. -/
def A : Prop :=
  type_of% @Morse.isSliceSubmanifold_of_param.{0, 0, 0} ∧
    type_of% @Morse.IsTotGeo.tangentSubspace_eq.{0, 0, 0} ∧
    type_of% @Morse.IsTotGeo.isGeodesicOn_mul_exp_smul.{0, 0, 0} ∧
    type_of% @Morse.IsTotGeo.eqOn_of_isUnbrokenGeodesic.{0, 0, 0} ∧
    type_of% @Morse.IsTotGeo.exp_eq.{0, 0, 0} ∧
    type_of% @Morse.IsTotGeo.isGeodesicallyComplete.{0, 0, 0}

theorem A_holds : A :=
  ⟨@Morse.isSliceSubmanifold_of_param.{0, 0, 0}, @Morse.IsTotGeo.tangentSubspace_eq.{0, 0, 0},
    @Morse.IsTotGeo.isGeodesicOn_mul_exp_smul.{0, 0, 0},
    @Morse.IsTotGeo.eqOn_of_isUnbrokenGeodesic.{0, 0, 0}, @Morse.IsTotGeo.exp_eq.{0, 0, 0},
    @Morse.IsTotGeo.isGeodesicallyComplete.{0, 0, 0}⟩

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
submanifold in the blind sense (`IsEmbSubmfd`). -/
theorem isEmbSubmfd_of_slice {S' : Set (Mat ι)}
    (h : ∀ p ∈ S', ∃ (K : Submodule ℝ (Mat ι)) (T : Set (Mat ι)),
      Milnor.IsSliceSubmanifold 𝓘(ℝ, Mat ι) K Kᗮ T ∧ p ∈ T ∧ ∀ᶠ y in 𝓝 p, (y ∈ S' ↔ y ∈ T)) :
    IsEmbSubmfd S' := by
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
    · rintro ⟨x, ⟨hxS, hx⟩, rfl⟩
      refine ⟨?_, e.map_source hx⟩
      rw [hsrc] at hx
      have hxT := (hUev hx.2).1 hxS
      rw [SetLike.mem_coe, happ, sumEquiv_mem_iff]
      exact (σ.slice x hx.1).1 hxT
    · rintro ⟨hyK, hy⟩
      refine ⟨e.symm y, ⟨?_, e.map_target hy⟩, e.right_inv hy⟩
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


/-! ## The strata of `Ω_k(n)` are slice submanifolds, from A's `isSliceSubmanifold_of_param`

(The project's proof of `Morse.isSliceSubmanifold_omegaStratum`, run with the hypothesis in place of
`Morse.isSliceSubmanifold_of_param`.) -/

section Slice
open scoped Morse.MatrixInner Manifold
variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem slice_of_param (hparam : type_of% @Morse.isSliceSubmanifold_of_param.{0, 0, 0})
    {J : ℕ → Mat ι} {k : ℕ} (hJ : Morse.IsAnticommFamily J k) (p : Matrix ι ι ℝ) :
    Milnor.IsSliceSubmanifold 𝓘(ℝ, Matrix ι ι ℝ) (Morse.tanAlg J k p) (Morse.tanAlg J k p)ᗮ
      (Morse.omegaStratum J k p) := by
  refine hparam fun x hx => ?_
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
      (Morse.finrank_tanAlg_mul_exp (Lz q.1).2).trans hx.2⟩
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

end Slice

/-- A ⇒ B. `Ω_k(n) ⊆ O(n)` is definitional. **Submanifold**: at `p ∈ Ω_k(n)`, with the family
`J_1, …, J_{k-1}, p` (anticommuting, `famAt`), A's `isSliceSubmanifold_of_param` applied to the
parametrization `(a, w) ↦ x(exp a + w)` (`a ∈ 𝒯_x`, `w ⊥ 𝒯_x`; the project's argument, with
Assertions 1, 2 and the local logarithm `Morse.exists_local_log`) makes the stratum of `p` a slice
submanifold; near `p`, `Ω_k(n)` is that stratum (`Morse.eventually_mem_omegaStratum`); the slice
chart followed by `(z, w) ↦ z + w` is a blind chart. **Totally geodesic** (Milnor's footnote
definition, for the blind induced-metric geodesics): proved directly (`isGeodOn_orth_of_omegaK`),
without A's `IsTotGeo` lemmas (which describe the geodesics of `N` itself in the project's
vocabulary, not the comparison with `O(n)`). -/
theorem A_to_B : A → B := by
  rintro ⟨hparam, -⟩ n k Js hJ
  refine ⟨omegaK_subset_orth Js k, isEmbSubmfd_of_slice fun p hp => ?_,
    fun γ a b h => isGeodOn_orth_of_omegaK hJ h⟩
  have hJ' := isAnticommFamily_famAt hJ hp
  have hpΩ : p ∈ Morse.Omega (famAt Js k p) k := by
    rw [omega_famAt, ← omegaK_eq_omega]; exact hp
  have hpS : p ∈ Morse.omegaStratum (famAt Js k p) k p := ⟨hpΩ, rfl⟩
  refine ⟨Morse.tanAlg (famAt Js k p) k p, Morse.omegaStratum (famAt Js k p) k p,
    slice_of_param hparam hJ' p, hpS, ?_⟩
  filter_upwards [Morse.eventually_mem_omegaStratum hJ' hpS] with y hy
  rw [omegaK_eq_omega, ← omega_famAt Js k p]
  exact ⟨hy, fun h => h.1⟩

#rt_check RoundTrip.V15_21.A_to_B [Morse.isSliceSubmanifold_of_param,
  Morse.IsTotGeo.tangentSubspace_eq, Morse.IsTotGeo.isGeodesicOn_mul_exp_smul,
  Morse.IsTotGeo.eqOn_of_isUnbrokenGeodesic, Morse.IsTotGeo.exp_eq,
  Morse.IsTotGeo.isGeodesicallyComplete]

/-! ## B ⇒ A, only vacuously: A re-proved outright (the project's proofs, copied) -/

section OutrightSlice
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
open scoped Manifold

theorem isSliceSubmanifold_of_param' {S : Set V}
    (h : ∀ x ∈ S, ∃ Φ : Z × W → V, ContDiff ℝ ∞ Φ ∧ Φ 0 = x ∧
      (∃ e : (Z × W) ≃L[ℝ] V, HasFDerivAt Φ (e : (Z × W) →L[ℝ] V) 0) ∧
      (∀ᶠ q in 𝓝 (0 : Z × W), q.2 = 0 → Φ q ∈ S) ∧
      ∃ g : Z × W → Z, Tendsto g (𝓝 0) (𝓝 0) ∧
        ∀ᶠ q in 𝓝 (0 : Z × W), Φ q ∈ S → Φ (g q, 0) = Φ q) :
    Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W S := by
  intro x hx
  obtain ⟨Φ, hΦ, hΦ0, ⟨e, he⟩, h0, g, hg, hgΦ⟩ := h x hx
  have hinv : (mfderiv 𝓘(ℝ, Z × W) 𝓘(ℝ, V) Φ 0).IsInvertible := by
    rw [mfderiv_eq_fderiv, he.fderiv]
    exact ⟨e, rfl⟩
  obtain ⟨Ψ, h0Ψ, hΨ⟩ := Milnor.ContMDiff.isLocalDiffeomorphAt_of_isInvertible_mfderiv
    hΦ.contMDiff (by simp) hinv
  have hsrc : Ψ.source ∈ 𝓝 (0 : Z × W) := Ψ.open_source.mem_nhds h0Ψ
  have hg' : Tendsto (fun q : Z × W => ((g q, 0) : Z × W)) (𝓝 0) (𝓝 0) := by
    have := hg.prodMk_nhds (tendsto_const_nhds (x := (0 : W)))
    rwa [← Prod.zero_eq_mk] at this
  have hev : ∀ᶠ q in 𝓝 (0 : Z × W), (Φ q ∈ S ↔ q.2 = 0) := by
    filter_upwards [h0, hgΦ, hsrc, hg'.eventually hsrc] with q hq0 hqg hqs hqs'
    refine ⟨fun hq => ?_, hq0⟩
    have e1 : Ψ.toFun (g q, 0) = Ψ.toFun q := by
      rw [← hΨ hqs', ← hΨ hqs]; exact hqg hq
    have := Ψ.toPartialEquiv.injOn hqs' hqs e1
    rw [← this]
  obtain ⟨U, hUev, hUo, h0U⟩ := mem_nhds_iff.1 hev
  set Ψ' := Ψ.restrOpen U hUo with hΨ'
  have hxt : x ∈ Ψ'.target := ⟨0, ⟨h0Ψ, h0U⟩, by rw [← hΦ0]; exact (hΨ h0Ψ).symm⟩
  refine ⟨⟨Ψ'.symm, x, hx, hxt, fun p hp => ?_⟩, hxt⟩
  obtain ⟨q, hq, rfl⟩ := hp
  have hq' : Ψ'.toPartialEquiv.symm (Ψ'.toFun q) = q := Ψ'.toPartialEquiv.left_inv hq
  change Ψ'.toFun q ∈ S ↔ (Ψ'.toPartialEquiv.symm (Ψ'.toFun q)).2 = 0
  rw [hq']
  have : Ψ'.toFun q = Φ q := (hΨ hq.1).symm
  rw [this]
  exact hUev hq.2

end OutrightSlice

section OutrightTotGeo
open scoped Morse.MatrixInner RealInnerProductSpace Manifold
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {N : Set (Matrix ι ι ℝ)}

theorem tangentSubspace_eq' {hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, Matrix ι ι ℝ) Z W N} {T : Matrix ι ι ℝ → Submodule ℝ (Matrix ι ι ℝ)} (h : Morse.IsTotGeo hN T) (x : N) :
    Morse.tangentSubspace hN x = Morse.IsTotGeo.leftT T x.1 (h.unitary x x.2) := by
  symm
  refine Submodule.eq_of_le_of_finrank_eq (K := ℝ) (V := Matrix ι ι ℝ) ?_ ?_
  · intro v hv
    rw [Morse.IsTotGeo.mem_leftT_iff] at hv
    set X := x.1ᴴ * v with hXdef
    have hvX : v = x.1 * X := by
      rw [hXdef, ← Matrix.mul_assoc, h.mul_conjTranspose x.2, Matrix.one_mul]
    have hc : HasDerivAt (fun t : ℝ => x.1 * NormedSpace.exp (t • X)) (x.1 * X) 0 := by
      have := (hasDerivAt_exp_smul_const X (0 : ℝ)).const_mul x.1
      simpa using this
    have hmem : ∀ᶠ s in 𝓝 (0 : ℝ), x.1 * NormedSpace.exp (s • X) ∈ N :=
      Filter.Eventually.of_forall fun s => h.mul_exp_smul_mem x.2 hv s
    have hT := Morse.hasDerivAt_mem_tangentSubspace hN hc hmem
    have hx0 : (⟨x.1 * NormedSpace.exp ((0 : ℝ) • X), hmem.self_of_nhds⟩ : N) = x := by
      ext1; simp
    rw [hx0] at hT
    rw [hvX]
    exact hT
  · have h1 := Morse.finrank_tanAt hN x.2
    rw [Morse.tanAt_of_mem hN x.2] at h1
    rw [Morse.IsTotGeo.leftT, LinearEquiv.finrank_map_eq, h.finrank_eq x x.2]
    exact h1.symm

theorem mem_tangentSubspace_iff' {hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, Matrix ι ι ℝ) Z W N} {T : Matrix ι ι ℝ → Submodule ℝ (Matrix ι ι ℝ)} (h : Morse.IsTotGeo hN T) (x : N) {v : Matrix ι ι ℝ} :
    v ∈ Morse.tangentSubspace hN x ↔ x.1ᴴ * v ∈ T x.1 := by
  rw [tangentSubspace_eq' h, Morse.IsTotGeo.mem_leftT_iff]

theorem isGeodesicOn_mul_exp_smul' {hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, Matrix ι ι ℝ) Z W N} {T : Matrix ι ι ℝ → Submodule ℝ (Matrix ι ι ℝ)} (h : Morse.IsTotGeo hN T) {x : Matrix ι ι ℝ} (hx : x ∈ N) {A : Matrix ι ι ℝ}
    (hA : A ∈ T x) : Morse.IsGeodesicOn hN (fun t => x * NormedSpace.exp (t • A)) univ where
  isOpen := isOpen_univ
  mem t _ := h.mul_exp_smul_mem hx hA t
  contDiffOn := (contDiff_const.mul (Morse.contDiff_exp_smul A)).contDiffOn
  normal t _ := by
    rw [Morse.deriv_deriv_mul_exp_smul, Submodule.mem_orthogonal]
    intro u hu
    set q : N := ⟨x * NormedSpace.exp (t • A), h.mul_exp_smul_mem hx hA t⟩
    change u ∈ Morse.tangentSubspace hN q at hu
    rw [mem_tangentSubspace_iff' h] at hu
    have hu' : u = q.1 * (q.1ᴴ * u) := by
      rw [← Matrix.mul_assoc, h.mul_conjTranspose q.2, Matrix.one_mul]
    have hXX : x * NormedSpace.exp (t • A) * A * A = q.1 * (A * A) := by
      simp only [q, Matrix.mul_assoc]
    rw [hu', hXX, Morse.inner_mul_left_of_unitary (h.unitary q q.2)]
    have hXX' : (A * A)ᴴ = A * A := by
      rw [conjTranspose_mul, h.skew x hx A hA, neg_mul_neg]
    rw [real_inner_comm]
    exact Morse.inner_eq_zero_of_hermitian_of_skew hXX' (h.skew _ q.2 _ hu)

theorem eqOn_mul_exp_smul' {hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, Matrix ι ι ℝ) Z W N} {T : Matrix ι ι ℝ → Submodule ℝ (Matrix ι ι ℝ)} (h : Morse.IsTotGeo hN T) {γ : ℝ → Matrix ι ι ℝ} {s : Set ℝ} (hγ : Morse.IsGeodesicOn hN γ s)
    (hs : IsPreconnected s) {t₀ : ℝ} (ht₀ : t₀ ∈ s) :
    (γ t₀)ᴴ * deriv γ t₀ ∈ T (γ t₀) ∧
      EqOn γ (fun t => γ t₀ * NormedSpace.exp ((t - t₀) • ((γ t₀)ᴴ * deriv γ t₀))) s := by
  set g := γ t₀ with hgdef
  have hg : g ∈ N := hγ.mem t₀ ht₀
  set X := gᴴ * deriv γ t₀ with hXdef
  have hX : X ∈ T g := by
    have := hγ.deriv_mem ht₀
    rwa [mem_tangentSubspace_iff' h] at this
  refine ⟨hX, ?_⟩
  set g' := g * NormedSpace.exp ((-t₀) • X)
  have hg' : g' ∈ N := h.mul_exp_smul_mem hg hX _
  have hX' : X ∈ T g' := by
    have := h.mem_mul_exp g hg _ ((T g).smul_mem (-t₀) hX)
    have h2 := (T g').smul_mem (-t₀)⁻¹ this
    by_cases ht : t₀ = 0
    · have hg'' : g' = g := by simp [g', ht]
      rw [hg'']; exact hX
    · rwa [smul_smul, inv_mul_cancel₀ (neg_ne_zero.2 ht), one_smul] at h2
  have hc : (fun t => g' * NormedSpace.exp (t • X)) =
      fun t => g * NormedSpace.exp ((t - t₀) • X) := by
    funext t
    rw [Matrix.mul_assoc, Morse.exp_smul_mul_exp_smul, neg_add_eq_sub]
  have hgeo := (isGeodesicOn_mul_exp_smul' h hg' hX').mono hγ.isOpen (subset_univ s)
  rw [hc] at hgeo
  refine hγ.eqOn hgeo hs ht₀ (by simp [hgdef]) ?_
  have hd : HasDerivAt (fun t => g * NormedSpace.exp ((t - t₀) • X)) (g * X) t₀ := by
    have := Morse.hasDerivAt_mul_exp_smul g' X t₀
    rw [hc] at this
    convert this using 1
    simp only [g', Matrix.mul_assoc, Morse.exp_smul_mul_exp_smul, neg_add_cancel, zero_smul,
      NormedSpace.exp_zero, Matrix.one_mul]
  rw [hd.deriv, hXdef, ← Matrix.mul_assoc, h.mul_conjTranspose hg, Matrix.one_mul]

theorem exp_eq' {hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, Matrix ι ι ℝ) Z W N} {T : Matrix ι ι ℝ → Submodule ℝ (Matrix ι ι ℝ)} (h : Morse.IsTotGeo hN T) {x : Matrix ι ι ℝ} (hx : x ∈ N) {A : Matrix ι ι ℝ} (hA : A ∈ T x) :
    Morse.exp hN x (x * A) = x * NormedSpace.exp A := by
  have hfrom : Morse.IsGeodesicFrom hN (fun t => x * NormedSpace.exp (t • A)) x (x * A) := by
    refine ⟨1, one_pos, (isGeodesicOn_mul_exp_smul' h hx hA).mono isOpen_Ioo (subset_univ _), ?_,
      ?_⟩
    · simp
    · rw [Morse.deriv_mul_exp_smul]
      simp
  rw [hfrom.exp_eq, one_smul]

theorem isGeodesicallyComplete' {hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, Matrix ι ι ℝ) Z W N} {T : Matrix ι ι ℝ → Submodule ℝ (Matrix ι ι ℝ)} (h : Morse.IsTotGeo hN T) : Morse.IsGeodesicallyComplete hN := by
  intro q v hv
  rw [mem_tangentSubspace_iff' h] at hv
  have hv' : v = q.1 * (q.1ᴴ * v) := by
    rw [← Matrix.mul_assoc, h.mul_conjTranspose q.2, Matrix.one_mul]
  refine ⟨fun t => q.1 * NormedSpace.exp (t • (q.1ᴴ * v)), 1, one_pos,
    (isGeodesicOn_mul_exp_smul' h q.2 hv).mono isOpen_Ioo (subset_univ _), by simp, ?_⟩
  rw [Morse.deriv_mul_exp_smul]
  simp only [zero_smul, NormedSpace.exp_zero, Matrix.mul_one]
  exact hv'.symm

theorem eqOn_of_isUnbrokenGeodesic' {hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, Matrix ι ι ℝ) Z W N} {T : Matrix ι ι ℝ → Submodule ℝ (Matrix ι ι ℝ)} (h : Morse.IsTotGeo hN T) {γ : ℝ → Matrix ι ι ℝ} {p q : Matrix ι ι ℝ}
    (hγ : γ ∈ Morse.pathSpace N p q) (hgeo : Morse.IsUnbrokenGeodesic hN γ) :
    ∃ V ∈ T p, EqOn γ (fun s : ℝ => p * NormedSpace.exp (s • V)) (Icc 0 1) := by
  have hhalf : (1 / 2 : ℝ) ∈ Ioo (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  obtain ⟨hX, heq⟩ := eqOn_mul_exp_smul' h hgeo.2 isPreconnected_Ioo hhalf
  set g := γ (1 / 2) with hgdef
  have hg : g ∈ N := hgeo.2.mem _ hhalf
  set X := gᴴ * deriv γ (1 / 2) with hXdef
  set φ : ℝ → Matrix ι ι ℝ := fun t => g * NormedSpace.exp ((t - 1 / 2) • X)
  have hφc : Continuous φ :=
    continuous_const.mul ((Morse.contDiff_exp_smul X).continuous.comp
      (continuous_id.sub continuous_const))
  have heqI : EqOn γ φ (Icc 0 1) :=
    heq.of_subset_closure hgeo.1.continuousOn hφc.continuousOn Ioo_subset_Icc_self
      (by rw [closure_Ioo zero_ne_one])
  set g' := g * NormedSpace.exp ((-(1 / 2 : ℝ)) • X)
  have hX' : X ∈ T g' := by
    have := h.mem_mul_exp g hg _ ((T g).smul_mem (-(1 / 2 : ℝ)) hX)
    have h2 := (T g').smul_mem (-2 : ℝ) this
    rwa [smul_smul, show (-2 : ℝ) * -(1 / 2) = 1 by norm_num, one_smul] at h2
  have hφ : ∀ t, φ t = g' * NormedSpace.exp (t • X) := fun t => by
    simp only [φ, g', Matrix.mul_assoc, Morse.exp_smul_mul_exp_smul]
    congr 3; ring
  have hp : g' = p := by
    have := heqI ⟨le_rfl, zero_le_one⟩
    rw [hγ.2.2.1, hφ] at this
    simpa using this.symm
  refine ⟨X, hp ▸ hX', fun t ht => ?_⟩
  rw [heqI ht, hφ, hp]

end OutrightTotGeo

/-- B ⇒ A, only vacuously: A is proved outright. A is a general theory (a submanifold criterion for
arbitrary normed spaces, and the geometry of any `IsTotGeo` set of orthogonal matrices); B is about
`Ω_k(n)` only. -/
theorem B_to_A : B → A := fun _ =>
  ⟨@fun V _ _ Z _ _ _ W _ _ _ S h => isSliceSubmanifold_of_param' h,
    @fun ι _ _ Z _ _ W _ _ N hN T h _ _ x => tangentSubspace_eq' h x,
    @fun ι _ _ Z _ _ W _ _ N hN T h _ _ x hx A hA => isGeodesicOn_mul_exp_smul' h hx hA,
    @fun ι _ _ Z _ _ W _ _ N hN T h _ _ γ p q hγ hgeo => eqOn_of_isUnbrokenGeodesic' h hγ hgeo,
    @fun ι _ _ Z _ _ W _ _ N hN T h _ _ x hx A hA => exp_eq' h hx hA,
    @fun ι _ _ Z _ _ W _ _ N hN T h _ _ => isGeodesicallyComplete' h⟩

#rt_check RoundTrip.V15_21.B_to_A [Morse.isSliceSubmanifold_of_param,
  Morse.IsTotGeo.tangentSubspace_eq, Morse.IsTotGeo.isGeodesicOn_mul_exp_smul,
  Morse.IsTotGeo.eqOn_of_isUnbrokenGeodesic, Morse.IsTotGeo.exp_eq,
  Morse.IsTotGeo.isGeodesicallyComplete]
#rt_overlap RoundTrip.V15_21.B_to_A [Morse.isSliceSubmanifold_of_param,
  Morse.IsTotGeo.tangentSubspace_eq, Morse.IsTotGeo.isGeodesicOn_mul_exp_smul,
  Morse.IsTotGeo.eqOn_of_isUnbrokenGeodesic, Morse.IsTotGeo.exp_eq,
  Morse.IsTotGeo.isGeodesicallyComplete]

end

end RoundTrip.V15_21
