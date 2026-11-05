import Morse
import RoundTrip.Check
import RoundTrip.Blind.V12_12

/-!
# V12_12 (Milnor §21, proof of Theorem 21.7, p. 117): the non-zero eigenvalues of `K_V` occur in pairs

`A` (universe `0`): the conjunction of `Morse.jacobiOp_of_lie_lie`, `Morse.lie_lie_of_jacobiOp`,
`Morse.lie_mem_eigenspace`, `Morse.eigenJ_comp_self`, `Morse.eigenJ_isometry`,
`Morse.even_finrank_of_comp_self_eq_neg_id`, `Morse.even_finrank_eigenspace` — for an arbitrary real Lie algebra
`L` (and bilinear `B`, ad-invariant / positive definite where needed): `K_V W = μ W ↔ ad_V² W = −4μ W`; `ad_V`
preserves the eigenspaces `E_μ` of `K_V = jacobiOp L V`; on `E_μ`, `μ > 0`, `eigenJ V = (2√μ)⁻¹ ad_V`
(vocabulary) is a `B`-orthogonal complex structure; a complex structure forces even dimension; hence
`dim E_μ` is even for `μ ≠ 0` (`L` finite-dimensional).  Pure linear algebra.

`B` (blind): on a Lie group with a bi-invariant metric and Levi-Civita connection, (1) for every `v ∈ 𝔤` an
`ip`-orthonormal basis `e` in which `ad_v` is block diagonal with blocks `(0 a_i; −a_i 0)` and `ad_v²` is
`diag(−a_0², −a_0², …, 0, …)`; (2) at every `p` and `V ∈ T_pG`, every non-zero eigenvalue `μ` of
`K_V = R(V, ·)V` (pointwise `curvR`) is `> 0` and its eigenspace is even-dimensional.

* `B → A`: vacuous (A re-proved outright).
* `A → B` fails.  Two independent gaps:
  - geometry (as in V12_8/V12_11): `Core` (`X ⊢ X = 0` and metric compatibility on left-invariant fields,
    giving (d) and 21.3(a)) and `Tens` (tensoriality of the curvature, so that the blind `curvR` is
    computed by Milnor's field formula) are not formalized for Lie groups;
  - linear algebra: (1), Milnor's orthonormal block normal form of the skew `ad_v`, is *not* in the
    project, which proves only its consequence for eigenspaces (BiInvariant.lean: "the orthonormal block normal
    form of `ad_V` itself (only its consequence for eigenspaces)" is not formalized).  (1) is true (spectral
    theorem for `K_v` + an orthonormal basis `w, Jw, …` of each `E_μ`, from `eigenJ_isometry`), so this part
    is effort only.
* **Bridge** (`Beig_of_core`, uses `A`, `#rt_check_soft`ed): `Core ∧ Tens` ⇒ (2) on every group: `K_V` at `p`
  is `jacobiOp 𝔤 v` conjugated by `dL_p : 𝔤 ≅ T_pG` (`KV_liv`), so the eigenspace of `K_V` at `p` is the image
  of `E_μ` and `A`'s `even_finrank_eigenspace` gives evenness (positivity: the project's
  `Morse.eigenvalue_nonneg`, an item of V12_11).
-/

open scoped ContDiff Manifold
open Bundle

set_option linter.unusedSectionVars false

namespace RoundTrip.V12_12

/-- The project's statement (universe `0`). -/
def A : Prop := type_of% @Morse.jacobiOp_of_lie_lie.{0} ∧ type_of% @Morse.lie_lie_of_jacobiOp.{0} ∧
  type_of% @Morse.lie_mem_eigenspace.{0} ∧ type_of% @Morse.eigenJ_comp_self.{0} ∧
  type_of% @Morse.eigenJ_isometry.{0} ∧ type_of% @Morse.even_finrank_of_comp_self_eq_neg_id.{0} ∧
  type_of% @Morse.even_finrank_eigenspace.{0}

theorem A_holds : A :=
  ⟨@Morse.jacobiOp_of_lie_lie.{0}, @Morse.lie_lie_of_jacobiOp.{0}, @Morse.lie_mem_eigenspace.{0},
    @Morse.eigenJ_comp_self.{0}, @Morse.eigenJ_isometry.{0}, @Morse.even_finrank_of_comp_self_eq_neg_id.{0},
    @Morse.even_finrank_eigenspace.{0}⟩

/-! ## `A` re-proved outright (for `B_to_A`) -/

namespace Re

theorem even_finrank_of_comp_self_eq_neg_id {E : Type} [AddCommGroup E] [Module ℝ E]
    [FiniteDimensional ℝ E] (J : E →ₗ[ℝ] E) (hJ : J ∘ₗ J = -LinearMap.id) :
    Even (Module.finrank ℝ E) := by
  have h := congrArg LinearMap.det hJ
  rw [LinearMap.det_comp, show (-LinearMap.id : E →ₗ[ℝ] E) = (-1 : ℝ) • LinearMap.id by simp,
    LinearMap.det_smul, LinearMap.det_id, mul_one] at h
  rcases Nat.even_or_odd (Module.finrank ℝ E) with he | ho
  · exact he
  · rw [ho.neg_one_pow] at h
    nlinarith [mul_self_nonneg (LinearMap.det J)]

variable {L : Type} [LieRing L] [LieAlgebra ℝ L] {B : LinearMap.BilinForm ℝ L}

theorem jacobiOp_of_lie_lie {V W : L} {a : ℝ} (h : ⁅V, ⁅V, W⁆⁆ = -(a ^ 2) • W) :
    Morse.jacobiOp L V W = (a ^ 2 / 4) • W := by
  rw [Morse.jacobiOp_apply, h, smul_smul]
  congr 1; ring

theorem lie_lie_of_jacobiOp {V W : L} {μ : ℝ} (h : Morse.jacobiOp L V W = μ • W) :
    ⁅V, ⁅V, W⁆⁆ = -(4 * μ) • W := by
  rw [Morse.jacobiOp_apply] at h
  have : ⁅V, ⁅V, W⁆⁆ = (-4 : ℝ) • (-(1 / 4 : ℝ) • ⁅V, ⁅V, W⁆⁆) := by
    rw [smul_smul]; norm_num
  rw [this, h, smul_smul]
  congr 1; ring

theorem lie_mem_eigenspace {V W : L} {μ : ℝ} (h : W ∈ Module.End.eigenspace (Morse.jacobiOp L V) μ) :
    ⁅V, W⁆ ∈ Module.End.eigenspace (Morse.jacobiOp L V) μ := by
  rw [Module.End.mem_eigenspace_iff] at h ⊢
  rw [Morse.jacobiOp_apply] at h ⊢
  rw [← lie_smul, h, lie_smul]

theorem eigenJ_comp_self (V : L) {μ : ℝ} (hμ : 0 < μ) :
    Morse.eigenJ V ∘ₗ Morse.eigenJ V =
      -LinearMap.id (R := ℝ) (M := Module.End.eigenspace (Morse.jacobiOp L V) μ) := by
  ext W
  have hW := W.2
  rw [Module.End.mem_eigenspace_iff] at hW
  have h := lie_lie_of_jacobiOp hW
  simp only [LinearMap.comp_apply, Morse.eigenJ_apply, lie_smul, smul_smul, h, LinearMap.neg_apply,
    LinearMap.id_apply, Submodule.coe_neg]
  have hs : Real.sqrt μ ^ 2 = μ := Real.sq_sqrt hμ.le
  have hs0 : Real.sqrt μ ≠ 0 := (Real.sqrt_pos.2 hμ).ne'
  rw [← neg_one_smul ℝ (W : L)]
  congr 1
  field_simp
  nlinarith [hs]

theorem even_finrank_eigenspace [FiniteDimensional ℝ L] (hB : Morse.IsAdInvariant B)
    (hpos : ∀ x : L, x ≠ 0 → 0 < B x x) (V : L) {μ : ℝ} (hμ : μ ≠ 0) :
    Even (Module.finrank ℝ (Module.End.eigenspace (Morse.jacobiOp L V) μ)) := by
  rcases lt_or_gt_of_ne hμ with hneg | hpos'
  · have : Module.End.eigenspace (Morse.jacobiOp L V) μ = ⊥ := by
      rw [eq_bot_iff]
      intro W hW
      rw [Module.End.mem_eigenspace_iff] at hW
      by_contra hW0
      have := Morse.eigenvalue_nonneg hB hpos hW0 hW
      linarith
    rw [this, finrank_bot]
    exact ⟨0, rfl⟩
  · exact even_finrank_of_comp_self_eq_neg_id _ (eigenJ_comp_self V hpos')

theorem eigenJ_isometry (hB : Morse.IsAdInvariant B) (V : L) {μ : ℝ} (hμ : 0 < μ)
    (W W' : Module.End.eigenspace (Morse.jacobiOp L V) μ) :
    B (Morse.eigenJ V W) (Morse.eigenJ V W') = B W W' := by
  have hW' := W'.2
  rw [Module.End.mem_eigenspace_iff] at hW'
  have h := lie_lie_of_jacobiOp hW'
  simp only [Morse.eigenJ_apply, map_smul, LinearMap.smul_apply, smul_eq_mul]
  rw [Morse.ad_skew hB V (W : L) ⁅V, (W' : L)⁆, h]
  simp only [map_smul, smul_eq_mul]
  have hs : Real.sqrt μ ^ 2 = μ := Real.sq_sqrt hμ.le
  have hs0 : Real.sqrt μ ≠ 0 := (Real.sqrt_pos.2 hμ).ne'
  field_simp
  rw [hs]
  ring

end Re

/-- Vacuous: `A` re-proved outright, `B` is not used. -/
theorem B_to_A : B → A := fun _ =>
  ⟨@Re.jacobiOp_of_lie_lie, @Re.lie_lie_of_jacobiOp, @Re.lie_mem_eigenspace, @Re.eigenJ_comp_self,
    @Re.eigenJ_isometry, @Re.even_finrank_of_comp_self_eq_neg_id, @Re.even_finrank_eigenspace⟩

/-! ## Dictionary: the group `G` and its Lie algebra `𝔤 = GroupLieAlgebra`
(the first lemmas are copied from `Items/V12_1`–`V12_6`; `d_of_geod` and `adInv_of_geod` are the bridges of
V12_2 and V12_3 with the project's `Morse.IsLeviCivita.conn_eq` / `.isAdInvariant` in place of their `A`). -/

namespace Dict

variable {n : ℕ} {G : Type} [Group G] [TopologicalSpace G] [ChartedSpace (Rn n) G]
  [LieGroup 𝓘(ℝ, Rn n) ∞ G]

/-- Mathlib: `[X_u, X_v] = X_{⁅u,v⁆}`. -/
theorem liv_bracket (u v : GroupLieAlgebra 𝓘(ℝ, Rn n) G) :
    VectorField.mlieBracket 𝓘(ℝ, Rn n) (liv u) (liv v) = liv ⁅u, v⁆ :=
  (mulInvariantVector_mlieBracket u v).symm

theorem liv_one (u : GroupLieAlgebra 𝓘(ℝ, Rn n) G) : liv u (1 : G) = u := by
  have h : ∀ f : G → G, f = id → (mfderiv 𝓘(ℝ, Rn n) 𝓘(ℝ, Rn n) f 1 : Rn n →L[ℝ] Rn n) u = u := by
    rintro f rfl; simp [mfderiv_id]
  exact h _ (funext one_mul)

set_option backward.isDefEq.respectTransparency false in
/-- Left-invariant fields are `C^∞` (Mathlib's `contMDiff_mulInvariantVectorField` is only `C²`;
same proof, with `∞`). -/
theorem isSmoothVF_liv (v : GroupLieAlgebra 𝓘(ℝ, Rn n) G) : IsSmoothVF (n := n) (liv v) := by
  let fg : G → TangentBundle 𝓘(ℝ, Rn n) G := fun g ↦ Bundle.TotalSpace.mk' (Rn n) g 0
  have sfg : ContMDiff 𝓘(ℝ, Rn n) (𝓘(ℝ, Rn n)).tangent ∞ fg := contMDiff_zeroSection _ _
  let fv : G → TangentBundle 𝓘(ℝ, Rn n) G := fun _ ↦ Bundle.TotalSpace.mk' (Rn n) 1 v
  have sfv : ContMDiff 𝓘(ℝ, Rn n) (𝓘(ℝ, Rn n)).tangent ∞ fv := contMDiff_const
  have S₁ := sfg.prodMk sfv
  let F₂ : (TangentBundle 𝓘(ℝ, Rn n) G × TangentBundle 𝓘(ℝ, Rn n) G) →
      TangentBundle (𝓘(ℝ, Rn n).prod 𝓘(ℝ, Rn n)) (G × G) :=
    (equivTangentBundleProd 𝓘(ℝ, Rn n) G 𝓘(ℝ, Rn n) G).symm
  have S₂ : ContMDiff ((𝓘(ℝ, Rn n)).tangent.prod (𝓘(ℝ, Rn n)).tangent)
      (𝓘(ℝ, Rn n).prod 𝓘(ℝ, Rn n)).tangent ∞ F₂ := contMDiff_equivTangentBundleProd_symm
  let F₃ : TangentBundle (𝓘(ℝ, Rn n).prod 𝓘(ℝ, Rn n)) (G × G) → TangentBundle 𝓘(ℝ, Rn n) G :=
    tangentMap (𝓘(ℝ, Rn n).prod 𝓘(ℝ, Rn n)) 𝓘(ℝ, Rn n) (fun (p : G × G) ↦ p.1 * p.2)
  have S₃ : ContMDiff (𝓘(ℝ, Rn n).prod 𝓘(ℝ, Rn n)).tangent (𝓘(ℝ, Rn n)).tangent ∞ F₃ := by
    apply ContMDiff.contMDiff_tangentMap _ (m := ∞) (n := ∞) le_rfl
    exact contMDiff_mul 𝓘(ℝ, Rn n) ∞
  have S := (S₃.comp S₂).comp S₁
  unfold IsSmoothVF
  convert! S with g
  · simp [F₂, F₃, fg, fv]
  · simp only [Function.comp_apply, tangentMap, F₃, F₂, fg, fv]
    rw [mfderiv_prod_eq_add_apply ((contMDiff_mul 𝓘(ℝ, Rn n) ∞).mdifferentiableAt (by simp))]
    simp +instances [mulInvariantVectorField]
    rfl

theorem mdiffAt_liv (v : GroupLieAlgebra 𝓘(ℝ, Rn n) G) (p : G) :
    MDifferentiableAt 𝓘(ℝ, Rn n) (𝓘(ℝ, Rn n)).tangent
      (fun q => (⟨q, liv v q⟩ : TangentBundle 𝓘(ℝ, Rn n) G)) p :=
  mdifferentiableAt_mulInvariantVectorField v

/-- The connection on `𝔤` read at the point `p` through a linear map `Φ : T_pG → 𝔤`:
`(u, v) ↦ Φ ((X_u ⊢ X_v)(p))`, bilinear. -/
noncomputable def connAt (cov : Conn n G) (p : G) (Φ : Rn n →L[ℝ] Rn n) :
    GroupLieAlgebra 𝓘(ℝ, Rn n) G →ₗ[ℝ] GroupLieAlgebra 𝓘(ℝ, Rn n) G →ₗ[ℝ] GroupLieAlgebra 𝓘(ℝ, Rn n) G :=
  LinearMap.mk₂ ℝ (fun u v => Φ (cov (liv v) p (liv u p)))
    (fun a b c => by
      simp only [liv, mulInvariantVectorField_add, Pi.add_apply, map_add]
      exact Φ.map_add _ _)
    (fun r a b => by
      simp only [liv, mulInvariantVectorField_smul, Pi.smul_apply, map_smul]
      exact Φ.map_smul r _)
    (fun a b c => by
      simp only [liv, mulInvariantVectorField_add]
      rw [cov.isCovariantDerivativeOnUniv.add (mdiffAt_liv b p) (mdiffAt_liv c p)]
      exact Φ.map_add _ _)
    (fun r a b => by
      simp only [liv, mulInvariantVectorField_smul]
      rw [cov.isCovariantDerivativeOnUniv.smul_const r (mdiffAt_liv b p)]
      exact Φ.map_smul r _)

theorem connAt_apply (cov : Conn n G) (p : G) (Φ : Rn n →L[ℝ] Rn n) (u v : GroupLieAlgebra 𝓘(ℝ, Rn n) G) :
    connAt cov p Φ u v = Φ (covF cov (liv u) (liv v) p) := rfl

/-- `d(L_a)_{bh} ∘ d(L_b)_h = id` when `a b = 1`, with the base point of the first factor any `k = b h`. -/
theorem dL_comp_dL (a b h k : G) (hab : a * b = 1) (hk : k = b * h) :
    (mfderiv 𝓘(ℝ, Rn n) 𝓘(ℝ, Rn n) (fun x => a * x) k : Rn n →L[ℝ] Rn n).comp
      (mfderiv 𝓘(ℝ, Rn n) 𝓘(ℝ, Rn n) (fun x => b * x) h : Rn n →L[ℝ] Rn n) = ContinuousLinearMap.id ℝ (Rn n) := by
  subst hk
  have e : (fun x => a * x) ∘ (fun x => b * x) = id := by ext x; simp [← mul_assoc, hab]
  have := mfderiv_comp (I' := 𝓘(ℝ, Rn n)) (I := 𝓘(ℝ, Rn n)) (I'' := 𝓘(ℝ, Rn n)) h
    ((contMDiff_mul_left (I := 𝓘(ℝ, Rn n)) (n := ∞) (a := a)).contMDiffAt.mdifferentiableAt (by simp))
    ((contMDiff_mul_left (I := 𝓘(ℝ, Rn n)) (n := ∞) (a := b)).contMDiffAt.mdifferentiableAt (by simp))
  rw [e, mfderiv_id] at this
  exact this.symm

theorem liv_add (a b : GroupLieAlgebra 𝓘(ℝ, Rn n) G) : liv (a + b) = liv a + liv b :=
  mulInvariantVectorField_add a b

theorem liv_smul (c : ℝ) (a : GroupLieAlgebra 𝓘(ℝ, Rn n) G) : liv (c • a) = c • liv a :=
  mulInvariantVectorField_smul c a

theorem liv_neg (a : GroupLieAlgebra 𝓘(ℝ, Rn n) G) : liv (-a) = -liv a := by
  rw [← neg_one_smul ℝ a, liv_smul, neg_one_smul]

theorem liv_eq_zero_iff (a : GroupLieAlgebra 𝓘(ℝ, Rn n) G) : liv a = 0 ↔ a = 0 := by
  constructor
  · intro h
    have := congrFun h 1
    rwa [liv_one] at this
  · rintro rfl
    rw [← zero_smul ℝ (0 : GroupLieAlgebra 𝓘(ℝ, Rn n) G), liv_smul, zero_smul]

/-- Under Milnor's (d), the field curvature `R(X_u, X_v)X_w` is the left-invariant field of the
project's algebraic `Morse.curv (Morse.halfLie 𝔤) u v w`. -/
theorem curvF_liv_of_d (cov : Conn n G)
    (hd : ∀ a b : GroupLieAlgebra 𝓘(ℝ, Rn n) G,
      covF cov (liv a) (liv b) = (1 / 2 : ℝ) • VectorField.mlieBracket 𝓘(ℝ, Rn n) (liv a) (liv b))
    (u v w : GroupLieAlgebra 𝓘(ℝ, Rn n) G) :
    curvF cov (liv u) (liv v) (liv w) = liv (Morse.curv (Morse.halfLie (GroupLieAlgebra 𝓘(ℝ, Rn n) G)) u v w) := by
  have hd' : ∀ a b : GroupLieAlgebra 𝓘(ℝ, Rn n) G,
      covF cov (liv a) (liv b) = liv (Morse.halfLie (GroupLieAlgebra 𝓘(ℝ, Rn n) G) a b) := by
    intro a b; rw [hd, liv_bracket, Morse.halfLie_apply, liv_smul]
  have e : curvF cov (liv u) (liv v) (liv w) = covF cov (liv v) (covF cov (liv u) (liv w))
      - covF cov (liv u) (covF cov (liv v) (liv w))
      + covF cov (VectorField.mlieBracket 𝓘(ℝ, Rn n) (liv u) (liv v)) (liv w) := rfl
  rw [e, hd' u w, hd' v w, hd' v, hd' u, liv_bracket, hd', Morse.curv, liv_add, liv_add, liv_neg]
  abel

/-- Milnor's (d) `X ⊢ Y = ½[X, Y]` from the geometric input `X ⊢ X = 0` (one-parameter subgroups are
geodesics) for a symmetric connection, via the project's `Morse.IsLeviCivita.conn_eq` (bridge of V12_2). -/
theorem d_of_geod (cov : Conn n G) (hsymm : IsSymm cov)
    (hgeod : ∀ v : GroupLieAlgebra 𝓘(ℝ, Rn n) G, covF cov (liv v) (liv v) = 0)
    (u v : GroupLieAlgebra 𝓘(ℝ, Rn n) G) :
    covF cov (liv u) (liv v) = (1 / 2 : ℝ) • VectorField.mlieBracket 𝓘(ℝ, Rn n) (liv u) (liv v) := by
  funext p
  let Φ : Rn n →L[ℝ] Rn n := mfderiv 𝓘(ℝ, Rn n) 𝓘(ℝ, Rn n) (fun x => p⁻¹ * x) (p * 1)
  let dL : Rn n →L[ℝ] Rn n := mfderiv 𝓘(ℝ, Rn n) 𝓘(ℝ, Rn n) (fun x => p * x) 1
  have hΦdL : Φ.comp dL = ContinuousLinearMap.id ℝ (Rn n) :=
    dL_comp_dL p⁻¹ p 1 (p * 1) (inv_mul_cancel p) rfl
  have hdLΦ : dL.comp Φ = ContinuousLinearMap.id ℝ (Rn n) :=
    dL_comp_dL p p⁻¹ (p * 1) 1 (mul_inv_cancel p) (by group)
  have hΦliv : ∀ w : GroupLieAlgebra 𝓘(ℝ, Rn n) G, Φ (liv w p) = w := fun w =>
    congrArg (fun f : Rn n →L[ℝ] Rn n => f w) hΦdL
  have hdL : ∀ y : Rn n, dL (Φ y) = y := fun y => congrArg (fun f : Rn n →L[ℝ] Rn n => f y) hdLΦ
  let D := connAt cov p Φ
  have hLC : Morse.IsLeviCivita (0 : LinearMap.BilinForm ℝ (GroupLieAlgebra 𝓘(ℝ, Rn n) G)) D := by
    refine ⟨fun X Y => ?_, fun X Y Z => by simp⟩
    have h := hsymm (liv X) (liv Y) (isSmoothVF_liv X) (isSmoothVF_liv Y) p
    rw [liv_bracket] at h
    show Φ (cov (liv Y) p (liv X p)) - Φ (cov (liv X) p (liv Y p)) = ⁅X, Y⁆
    refine (Φ.map_sub _ _).symm.trans ?_
    exact (congrArg Φ h).trans (hΦliv _)
  have hD0 : ∀ X, D X X = 0 := fun X => by
    show Φ (covF cov (liv X) (liv X) p) = 0
    rw [hgeod X]; exact Φ.map_zero
  have key := Morse.IsLeviCivita.conn_eq hLC hD0 u v
  rw [Pi.smul_apply, liv_bracket]
  have e1 : dL (D u v) = (1 / 2 : ℝ) • dL (⁅u, v⁆ : GroupLieAlgebra 𝓘(ℝ, Rn n) G) := by
    rw [key]; exact dL.map_smul _ _
  have e2 : dL (D u v) = covF cov (liv u) (liv v) p := hdL _
  exact e2.symm.trans e1

variable [Bundle.RiemannianBundle (fun x : G => TangentSpace 𝓘(ℝ, Rn n) x)]

omit [LieGroup 𝓘(ℝ, Rn n) ∞ G] in
/-- `⟨X_u, X_v⟩` is the constant `⟨u, v⟩` (left invariance of the metric). -/
theorem inner_liv (hL : LeftInvMetric n G) (u v : GroupLieAlgebra 𝓘(ℝ, Rn n) G) (p : G) :
    inner ℝ (liv u p) (liv v p) = ip u v := by
  have key : ∀ q : G, p * 1 = q → ∀ x y : Rn n,
      @inner ℝ (TangentSpace 𝓘(ℝ, Rn n) q) _ x y = @inner ℝ (TangentSpace 𝓘(ℝ, Rn n) (p * 1)) _ x y := by
    rintro q rfl x y; rfl
  exact (key p (mul_one p) _ _).trans (hL p 1 u v)

omit [LieGroup 𝓘(ℝ, Rn n) ∞ G] in
/-- `⟨ , ⟩` on `𝔤 = T_1G` as a Mathlib bilinear form. -/
noncomputable def ipForm : LinearMap.BilinForm ℝ (GroupLieAlgebra 𝓘(ℝ, Rn n) G) :=
  LinearMap.mk₂ ℝ ip
    (fun a b c => inner_add_left (𝕜 := ℝ) (E := TangentSpace 𝓘(ℝ, Rn n) (1 : G)) a b c)
    (fun r a b => real_inner_smul_left (F := TangentSpace 𝓘(ℝ, Rn n) (1 : G)) a b r)
    (fun a b c => inner_add_right (𝕜 := ℝ) (E := TangentSpace 𝓘(ℝ, Rn n) (1 : G)) a b c)
    (fun r a b => real_inner_smul_right (F := TangentSpace 𝓘(ℝ, Rn n) (1 : G)) a b r)

omit [LieGroup 𝓘(ℝ, Rn n) ∞ G] in
theorem ipForm_apply (u v : GroupLieAlgebra 𝓘(ℝ, Rn n) G) : ipForm u v = ip u v := rfl

omit [LieGroup 𝓘(ℝ, Rn n) ∞ G] in
theorem ip_symm (u v : GroupLieAlgebra 𝓘(ℝ, Rn n) G) : ip u v = ip v u :=
  real_inner_comm (F := TangentSpace 𝓘(ℝ, Rn n) (1 : G)) _ _

omit [LieGroup 𝓘(ℝ, Rn n) ∞ G] in
theorem ip_pos (u : GroupLieAlgebra 𝓘(ℝ, Rn n) G) (hu : u ≠ 0) : 0 < ip u u :=
  real_inner_self_pos (F := TangentSpace 𝓘(ℝ, Rn n) (1 : G)) |>.2 hu

/-- Metric compatibility in derivative form (Milnor 8.4) on left-invariant fields:
`X_v⟨X_u, X_w⟩ = ⟨X_v ⊢ X_u, X_w⟩ + ⟨X_u, X_v ⊢ X_w⟩` (B of V12_3 (ii)). -/
def Bii (cov : Conn n G) : Prop :=
  ∀ (u v w : GroupLieAlgebra 𝓘(ℝ, Rn n) G) (p : G), dirD (fun q => inner ℝ (liv u q) (liv w q)) p (liv v p)
    = inner ℝ (covF cov (liv v) (liv u) p) (liv w p) + inner ℝ (liv u p) (covF cov (liv v) (liv w) p)

/-- 21.3(a) on `𝔤` from the geometric inputs (`Bii` and `X ⊢ X = 0`), via the project's
`Morse.IsLeviCivita.isAdInvariant` (bridge of V12_3). -/
theorem adInv_of_geod (hL : LeftInvMetric n G) (cov : Conn n G) (hsymm : IsSymm cov)
    (hii : Bii cov) (hgeod : ∀ v : GroupLieAlgebra 𝓘(ℝ, Rn n) G, covF cov (liv v) (liv v) = 0) :
    Morse.IsAdInvariant (ipForm (n := n) (G := G)) := by
  let D := connAt cov 1 (ContinuousLinearMap.id ℝ (Rn n))
  have hLC : Morse.IsLeviCivita (ipForm (n := n) (G := G)) D := by
    refine ⟨fun X Y => ?_, fun X Y Z => ?_⟩
    · have h := hsymm (liv X) (liv Y) (isSmoothVF_liv X) (isSmoothVF_liv Y) 1
      rw [liv_bracket, liv_one ⁅X, Y⁆] at h
      exact h
    · have h := hii Y X Z 1
      have hf : (fun q => inner ℝ (liv Y q) (liv Z q)) = fun _ => ip Y Z := funext (inner_liv hL Y Z)
      rw [hf, dirD, mfderiv_const] at h
      rw [liv_one Y, liv_one Z] at h
      exact h.symm
  have hD0 : ∀ X, D X X = 0 := fun X => by
    show covF cov (liv X) (liv X) 1 = 0
    rw [hgeod X]; rfl
  exact Morse.IsLeviCivita.isAdInvariant hLC hD0

end Dict

open Dict

/-- The geometric inputs that the project does not formalize for Lie groups (Milnor p. 113–114), on every
Lie group with a bi-invariant metric and Levi-Civita connection: `X ⊢ X = 0` for left-invariant `X`
(one-parameter subgroups are geodesics, B of V12_2 (iii)) and metric compatibility in derivative form on
left-invariant fields (B of V12_3 (ii)). -/
def Core : Prop :=
  ∀ (n : ℕ) (G : Type) [Group G] [TopologicalSpace G] [T2Space G] [ChartedSpace (Rn n) G] [LieGroup 𝓘(ℝ, Rn n) ∞ G] [Bundle.RiemannianBundle (fun x : G => TangentSpace 𝓘(ℝ, Rn n) x)] [IsContMDiffRiemannianBundle 𝓘(ℝ, Rn n) ∞ (Rn n) (fun x : G => TangentSpace 𝓘(ℝ, Rn n) x)],
    BiInvMetric n G → ∀ cov : Conn n G, IsLC cov →
      (∀ v : GroupLieAlgebra 𝓘(ℝ, Rn n) G, covF cov (liv v) (liv v) = 0) ∧ Bii cov

/-- Tensoriality of Milnor's field formula for `R` (his Lemma 9.1, not formalized for Mathlib manifolds):
`IsCurvVal` has a value for all tangent vectors, so that the blind `curvR` is the curvature tensor. -/
def Tens : Prop :=
  ∀ (n : ℕ) (G : Type) [Group G] [TopologicalSpace G] [T2Space G] [ChartedSpace (Rn n) G] [LieGroup 𝓘(ℝ, Rn n) ∞ G] [Bundle.RiemannianBundle (fun x : G => TangentSpace 𝓘(ℝ, Rn n) x)] [IsContMDiffRiemannianBundle 𝓘(ℝ, Rn n) ∞ (Rn n) (fun x : G => TangentSpace 𝓘(ℝ, Rn n) x)],
    BiInvMetric n G → ∀ cov : Conn n G, IsLC cov →
      ∀ (p : G) (x y z : TangentSpace 𝓘(ℝ, Rn n) p), ∃ r, IsCurvVal cov p x y z r

section
variable {n : ℕ} {G : Type} [Group G] [TopologicalSpace G] [ChartedSpace (Rn n) G]
  [LieGroup 𝓘(ℝ, Rn n) ∞ G] [Bundle.RiemannianBundle (fun x : G => TangentSpace 𝓘(ℝ, Rn n) x)]

/-- When `IsCurvVal` has a value, `curvR` on left-invariant vectors is Milnor's field formula `curvF`. -/
theorem curvR_liv (cov : Conn n G) (p : G) (u v w : GroupLieAlgebra 𝓘(ℝ, Rn n) G)
    (h : ∃ r, IsCurvVal cov p (liv u p) (liv v p) (liv w p) r) :
    curvR cov p (liv u p) (liv v p) (liv w p) = curvF cov (liv u) (liv v) (liv w) p := by
  unfold curvR
  rw [dif_pos h]
  exact h.choose_spec (liv u) (liv v) (liv w) (isSmoothVF_liv u) (isSmoothVF_liv v) (isSmoothVF_liv w)
    rfl rfl rfl

/-- Under (d) and tensoriality, `K_V` at `p` on left-invariant vectors is the project's `jacobiOp`. -/
theorem KV_liv (cov : Conn n G)
    (hd : ∀ a b : GroupLieAlgebra 𝓘(ℝ, Rn n) G,
      covF cov (liv a) (liv b) = (1 / 2 : ℝ) • VectorField.mlieBracket 𝓘(ℝ, Rn n) (liv a) (liv b))
    (p : G) (ht : ∀ x y z : TangentSpace 𝓘(ℝ, Rn n) p, ∃ r, IsCurvVal cov p x y z r)
    (v w : GroupLieAlgebra 𝓘(ℝ, Rn n) G) :
    KV cov p (liv v p) (liv w p) = liv (Morse.jacobiOp (GroupLieAlgebra 𝓘(ℝ, Rn n) G) v w) p := by
  show curvR cov p (liv v p) (liv w p) (liv v p) = _
  rw [curvR_liv cov p v w v (ht _ _ _), curvF_liv_of_d cov hd, Morse.curv_halfLie_eq_jacobiOp]
end

/-- **Bridge** (uses `A`): `Core ∧ Tens` ⇒ `B`'s eigenvalue conjunct (2). -/
theorem Beig_of_core (hA : A) : Core → Tens →
    ∀ (n : ℕ) (G : Type) [Group G] [TopologicalSpace G] [T2Space G] [ChartedSpace (Rn n) G] [LieGroup 𝓘(ℝ, Rn n) ∞ G] [Bundle.RiemannianBundle (fun x : G => TangentSpace 𝓘(ℝ, Rn n) x)] [IsContMDiffRiemannianBundle 𝓘(ℝ, Rn n) ∞ (Rn n) (fun x : G => TangentSpace 𝓘(ℝ, Rn n) x)],
    BiInvMetric n G → ∀ cov : Conn n G, IsLC cov →
      (∀ (p : G) (V : TangentSpace 𝓘(ℝ, Rn n) p) (μ : ℝ), μ ≠ 0 →
        (∃ W : TangentSpace 𝓘(ℝ, Rn n) p, W ≠ 0 ∧ KV cov p V W = μ • W) →
          0 < μ ∧ Even (Module.finrank ℝ (Submodule.span ℝ (eigSet cov p V μ)))) := by
  intro hc ht n G _ _ _ _ _ _ _ hbi cov hLC p V μ hμ hex
  obtain ⟨hgeod, hii⟩ := hc n G hbi cov hLC
  have hd := d_of_geod cov hLC.2.1 hgeod
  have hadj := adInv_of_geod hbi.1 cov hLC.2.1 hii hgeod
  have hpos : ∀ x : GroupLieAlgebra 𝓘(ℝ, Rn n) G, x ≠ 0 → 0 < ipForm x x := fun x hx => ip_pos x hx
  have : FiniteDimensional ℝ (GroupLieAlgebra 𝓘(ℝ, Rn n) G) := inferInstanceAs (FiniteDimensional ℝ (Rn n))
  let Φ : Rn n →L[ℝ] Rn n := mfderiv 𝓘(ℝ, Rn n) 𝓘(ℝ, Rn n) (fun x => p⁻¹ * x) (p * 1)
  let dL : Rn n →L[ℝ] Rn n := mfderiv 𝓘(ℝ, Rn n) 𝓘(ℝ, Rn n) (fun x => p * x) 1
  have hΦdL : Φ.comp dL = ContinuousLinearMap.id ℝ (Rn n) :=
    dL_comp_dL p⁻¹ p 1 (p * 1) (inv_mul_cancel p) rfl
  have hdLΦ : dL.comp Φ = ContinuousLinearMap.id ℝ (Rn n) :=
    dL_comp_dL p p⁻¹ (p * 1) 1 (mul_inv_cancel p) (by group)
  have hΦ : ∀ y : Rn n, Φ (dL y) = y := fun y => congrArg (fun f : Rn n →L[ℝ] Rn n => f y) hΦdL
  have hdL : ∀ y : Rn n, dL (Φ y) = y := fun y => congrArg (fun f : Rn n →L[ℝ] Rn n => f y) hdLΦ
  let e : TangentSpace 𝓘(ℝ, Rn n) p ≃ₗ[ℝ] GroupLieAlgebra 𝓘(ℝ, Rn n) G :=
    { toFun := fun W => Φ W
      invFun := fun w => dL w
      map_add' := fun a b => Φ.map_add a b
      map_smul' := fun c a => Φ.map_smul c a
      left_inv := fun W => hdL W
      right_inv := fun w => hΦ w }
  set E := Module.End.eigenspace (Morse.jacobiOp (GroupLieAlgebra 𝓘(ℝ, Rn n) G) (e V)) μ with hE
  have hKV : ∀ W : TangentSpace 𝓘(ℝ, Rn n) p,
      KV cov p V W = dL (Morse.jacobiOp (GroupLieAlgebra 𝓘(ℝ, Rn n) G) (e V) (e W)) := by
    intro W
    have e1 : liv (e V) p = V := hdL V
    have e2 : liv (e W) p = W := hdL W
    calc KV cov p V W = KV cov p (liv (e V) p) (liv (e W) p) := by rw [e1, e2]
      _ = _ := KV_liv cov hd p (ht n G hbi cov hLC p) _ _
  have hmem : ∀ W, W ∈ eigSet cov p V μ ↔ e W ∈ E := by
    intro W
    rw [hE, Module.End.mem_eigenspace_iff]
    show KV cov p V W = μ • W ↔ _
    rw [hKV W]
    constructor
    · intro h
      have := congrArg Φ h
      exact (hΦ _).symm.trans (this.trans (Φ.map_smul μ W))
    · intro h
      rw [h]
      show dL (μ • Φ W) = μ • W
      rw [dL.map_smul]
      exact congrArg (μ • ·) (hdL W)
  have hS : eigSet cov p V μ = (Submodule.comap (e : TangentSpace 𝓘(ℝ, Rn n) p →ₗ[ℝ] GroupLieAlgebra 𝓘(ℝ, Rn n) G) E : Set _) :=
    Set.ext hmem
  obtain ⟨W, hW0, hW⟩ := hex
  have heW : e W ∈ E := (hmem W).1 hW
  have heW0 : e W ≠ 0 := fun h => hW0 (by simpa using congrArg e.symm h)
  have hμpos : 0 < μ := by
    have := Morse.eigenvalue_nonneg hadj hpos heW0 ((Module.End.mem_eigenspace_iff).1 heW)
    exact lt_of_le_of_ne this (Ne.symm hμ)
  refine ⟨hμpos, ?_⟩
  rw [hS, Submodule.span_eq, Submodule.comap_equiv_eq_map_symm, LinearEquiv.finrank_map_eq]
  exact hA.2.2.2.2.2.2 hadj hpos (e V) hμ

-- `#rt_check` fails only because `A`'s vocabulary `Morse.eigenJ` uses `lie_mem_eigenspace` in its proof field
-- (the restriction of `(2√μ)⁻¹ ad_V` to `E_μ`); `Re.lie_mem_eigenspace` re-proves it.
#rt_check_soft RoundTrip.V12_12.B_to_A [Morse.jacobiOp_of_lie_lie, Morse.lie_lie_of_jacobiOp, Morse.lie_mem_eigenspace, Morse.eigenJ_comp_self, Morse.eigenJ_isometry, Morse.even_finrank_of_comp_self_eq_neg_id, Morse.even_finrank_eigenspace]
#rt_overlap RoundTrip.V12_12.B_to_A [Morse.jacobiOp_of_lie_lie, Morse.lie_lie_of_jacobiOp, Morse.lie_mem_eigenspace, Morse.eigenJ_comp_self, Morse.eigenJ_isometry, Morse.even_finrank_of_comp_self_eq_neg_id, Morse.even_finrank_eigenspace]
-- same for the bridge
#rt_check_soft RoundTrip.V12_12.Beig_of_core [Morse.jacobiOp_of_lie_lie, Morse.lie_lie_of_jacobiOp, Morse.lie_mem_eigenspace, Morse.eigenJ_comp_self, Morse.eigenJ_isometry, Morse.even_finrank_of_comp_self_eq_neg_id, Morse.even_finrank_eigenspace]

end RoundTrip.V12_12
