import Morse
import RoundTrip.Check
import RoundTrip.Blind.V12_11

/-!
# V12_11 (Milnor §21, proof of Theorem 21.7, pp. 116–117): the operator `K_V = −¼ (Ad V)²`

`A` (universe `0`): the conjunction of `Morse.jacobiOp_apply`, `Morse.ad_skew`, `Morse.jacobiOp_symm`,
`Morse.jacobiOp_self`, `Morse.jacobiOp_self_nonneg`, `Morse.jacobiOp_eq_zero_iff`, `Morse.eigenvalue_nonneg`,
`Morse.ad_eigenvalue_eq_zero` — for an arbitrary real Lie algebra `L` and bilinear form `B` (ad-invariant, and
positive definite where needed): `jacobiOp L V := −¼ ad_V ∘ ad_V` (vocabulary) satisfies
`jacobiOp L V W = −¼ ⁅V,⁅V,W⁆⁆`; `ad_V` is `B`-skew; `K_V` is `B`-self-adjoint, `⟨K_V W, W⟩ = ¼|⁅V,W⁆|² ≥ 0`,
`ker K_V = ` centralizer of `V`, eigenvalues of `K_V` are `≥ 0`, and the only real eigenvalue of `ad_V` is `0`.
Pure algebra.

`B` (blind): on a Lie group with a bi-invariant metric and Levi-Civita connection, at every `p`, for
`V = X_v(p)`, `W = X_w(p)`: (i) `K_V(W) = R(V,W)V = ¼[[V,W],V](p)` with `R` the pointwise curvature tensor
`curvR` (defined by choice from `IsCurvVal`, i.e. through the tensoriality of Milnor's field formula);
(ii) `K_V(W) = −¼[V,[V,W]](p)`; (iii) `⟨[V,W],W'⟩ = −⟨W,[V,W']⟩` at `p`.

* `B → A`: vacuous (A re-proved outright).
* `A → B` fails: `A` says nothing about Lie groups.  `B` needs (1) the geometric inputs `Core` (`X ⊢ X = 0`
  on left-invariant fields and the derivative form of metric compatibility; neither is formalized by the
  project for Lie groups) and, for (i)–(ii), (2) the tensoriality of the curvature (`Tens`: the blind `curvR`
  is only meaningful if Milnor's field formula has a value independent of the extensions; Milnor's 9.1, not
  formalized for Mathlib manifolds).
* **Bridges** (`#rt_check`ed): `Biii_of_core` (uses `A`'s `ad_skew`): `Core` ⇒ (iii) at every point;
  `Bi_ii_of_core`: `Core ∧ Tens` ⇒ (i) ∧ (ii) (pure dictionary + the project's `Morse.curv_halfLie`;
  `A`'s formula `K_V = −¼ ad_V²` is the same algebra); `B_of_core (hA) : Core → Tens → B`.
-/

open scoped ContDiff Manifold
open Bundle

set_option linter.unusedSectionVars false

namespace RoundTrip.V12_11

/-- The project's statement (universe `0`). -/
def A : Prop := type_of% @Morse.jacobiOp_apply.{0} ∧ type_of% @Morse.ad_skew.{0} ∧
  type_of% @Morse.jacobiOp_symm.{0} ∧ type_of% @Morse.jacobiOp_self.{0} ∧
  type_of% @Morse.jacobiOp_self_nonneg.{0} ∧ type_of% @Morse.jacobiOp_eq_zero_iff.{0} ∧
  type_of% @Morse.eigenvalue_nonneg.{0} ∧ type_of% @Morse.ad_eigenvalue_eq_zero.{0}

theorem A_holds : A :=
  ⟨@Morse.jacobiOp_apply.{0}, @Morse.ad_skew.{0}, @Morse.jacobiOp_symm.{0}, @Morse.jacobiOp_self.{0},
    @Morse.jacobiOp_self_nonneg.{0}, @Morse.jacobiOp_eq_zero_iff.{0}, @Morse.eigenvalue_nonneg.{0},
    @Morse.ad_eigenvalue_eq_zero.{0}⟩

/-! ## `A` re-proved outright (for `B_to_A`) -/

namespace Re

variable {L : Type} [LieRing L] [LieAlgebra ℝ L] {B : LinearMap.BilinForm ℝ L}

theorem jacobiOp_apply (V W : L) : Morse.jacobiOp L V W = -(1 / 4 : ℝ) • ⁅V, ⁅V, W⁆⁆ := by
  simp [Morse.jacobiOp]

theorem ad_skew (hB : Morse.IsAdInvariant B) (V X Y : L) : B ⁅V, X⁆ Y = -B X ⁅V, Y⁆ := by
  have := hB X V Y
  rw [← lie_skew, map_neg, LinearMap.neg_apply] at this
  linarith

theorem jacobiOp_symm (hB : Morse.IsAdInvariant B) (V W W' : L) :
    B (Morse.jacobiOp L V W) W' = B W (Morse.jacobiOp L V W') := by
  rw [jacobiOp_apply, jacobiOp_apply, map_smul, LinearMap.smul_apply, map_smul, smul_eq_mul,
    smul_eq_mul, ad_skew hB, ad_skew hB V W ⁅V, W'⁆]
  ring

theorem jacobiOp_self (hB : Morse.IsAdInvariant B) (V W : L) :
    B (Morse.jacobiOp L V W) W = (1 / 4 : ℝ) * B ⁅V, W⁆ ⁅V, W⁆ := by
  rw [jacobiOp_apply, map_smul, LinearMap.smul_apply, smul_eq_mul, ad_skew hB V ⁅V, W⁆ W]
  ring

theorem jacobiOp_self_nonneg (hB : Morse.IsAdInvariant B) (hpos : ∀ x : L, x ≠ 0 → 0 < B x x)
    (V W : L) : 0 ≤ B (Morse.jacobiOp L V W) W := by
  rw [jacobiOp_self hB]
  have := Morse.sq_nonneg_of_pos hpos ⁅V, W⁆
  positivity

theorem jacobiOp_eq_zero_iff (hB : Morse.IsAdInvariant B) (hpos : ∀ x : L, x ≠ 0 → 0 < B x x)
    (V W : L) : Morse.jacobiOp L V W = 0 ↔ ⁅V, W⁆ = 0 := by
  constructor
  · intro h
    have h1 := jacobiOp_self hB V W
    rw [h, map_zero, LinearMap.zero_apply] at h1
    by_contra hne
    have := hpos _ hne
    linarith
  · intro h; simp [jacobiOp_apply, h]

theorem eigenvalue_nonneg (hB : Morse.IsAdInvariant B) (hpos : ∀ x : L, x ≠ 0 → 0 < B x x)
    {V W : L} {μ : ℝ} (hW : W ≠ 0) (h : Morse.jacobiOp L V W = μ • W) : 0 ≤ μ := by
  have h1 := jacobiOp_self_nonneg hB hpos V W
  rw [h, map_smul, LinearMap.smul_apply, smul_eq_mul] at h1
  have h2 := hpos W hW
  by_contra hμ
  push Not at hμ
  nlinarith

theorem ad_eigenvalue_eq_zero (hB : Morse.IsAdInvariant B) (hpos : ∀ x : L, x ≠ 0 → 0 < B x x)
    {V X : L} {a : ℝ} (hX : X ≠ 0) (h : ⁅V, X⁆ = a • X) : a = 0 := by
  have h1 := ad_skew hB V X X
  rw [h] at h1
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul] at h1
  have h2 := hpos X hX
  have : a * B X X = 0 := by linarith
  rcases mul_eq_zero.1 this with h | h
  · exact h
  · linarith

end Re

/-- Vacuous: `A` re-proved outright, `B` is not used. -/
theorem B_to_A : B → A := fun _ =>
  ⟨@Re.jacobiOp_apply, @Re.ad_skew, @Re.jacobiOp_symm, @Re.jacobiOp_self, @Re.jacobiOp_self_nonneg,
    @Re.jacobiOp_eq_zero_iff, @Re.eigenvalue_nonneg, @Re.ad_eigenvalue_eq_zero⟩

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
end

/-- **Bridge** (uses `A`'s `ad_skew`): `Core` ⇒ `B`'s (iii) at every point. -/
theorem Biii_of_core (hA : A) : Core →
    ∀ (n : ℕ) (G : Type) [Group G] [TopologicalSpace G] [T2Space G] [ChartedSpace (Rn n) G] [LieGroup 𝓘(ℝ, Rn n) ∞ G] [Bundle.RiemannianBundle (fun x : G => TangentSpace 𝓘(ℝ, Rn n) x)] [IsContMDiffRiemannianBundle 𝓘(ℝ, Rn n) ∞ (Rn n) (fun x : G => TangentSpace 𝓘(ℝ, Rn n) x)],
    BiInvMetric n G → ∀ cov : Conn n G, IsLC cov →
      (∀ (v w w' : GroupLieAlgebra 𝓘(ℝ, Rn n) G) (p : G),
        inner ℝ (VectorField.mlieBracket 𝓘(ℝ, Rn n) (liv v) (liv w) p) (liv w' p)
          = -inner ℝ (liv w p) (VectorField.mlieBracket 𝓘(ℝ, Rn n) (liv v) (liv w') p)) := by
  intro hc n G _ _ _ _ _ _ _ hbi cov hLC v w w' p
  obtain ⟨hgeod, hii⟩ := hc n G hbi cov hLC
  have hadj := adInv_of_geod hbi.1 cov hLC.2.1 hii hgeod
  rw [liv_bracket, liv_bracket, inner_liv hbi.1, inner_liv hbi.1]
  exact hA.2.1 hadj v w w'

/-- **Bridge** (dictionary only): `Core ∧ Tens` ⇒ `B`'s (i) and (ii). -/
theorem Bi_ii_of_core : Core → Tens →
    ∀ (n : ℕ) (G : Type) [Group G] [TopologicalSpace G] [T2Space G] [ChartedSpace (Rn n) G] [LieGroup 𝓘(ℝ, Rn n) ∞ G] [Bundle.RiemannianBundle (fun x : G => TangentSpace 𝓘(ℝ, Rn n) x)] [IsContMDiffRiemannianBundle 𝓘(ℝ, Rn n) ∞ (Rn n) (fun x : G => TangentSpace 𝓘(ℝ, Rn n) x)],
    BiInvMetric n G → ∀ cov : Conn n G, IsLC cov →
      (∀ (v w : GroupLieAlgebra 𝓘(ℝ, Rn n) G) (p : G),
        KV cov p (liv v p) (liv w p)
          = (1 / 4 : ℝ) • VectorField.mlieBracket 𝓘(ℝ, Rn n) (VectorField.mlieBracket 𝓘(ℝ, Rn n) (liv v) (liv w)) (liv v) p) ∧
      (∀ (v w : GroupLieAlgebra 𝓘(ℝ, Rn n) G) (p : G),
        KV cov p (liv v p) (liv w p)
          = -((1 / 4 : ℝ) • VectorField.mlieBracket 𝓘(ℝ, Rn n) (liv v) (VectorField.mlieBracket 𝓘(ℝ, Rn n) (liv v) (liv w)) p)) := by
  intro hc ht n G _ _ _ _ _ _ _ hbi cov hLC
  obtain ⟨hgeod, -⟩ := hc n G hbi cov hLC
  have hd := d_of_geod cov hLC.2.1 hgeod
  have key : ∀ (v w : GroupLieAlgebra 𝓘(ℝ, Rn n) G) (p : G),
      KV cov p (liv v p) (liv w p) = liv ((1 / 4 : ℝ) • ⁅⁅v, w⁆, v⁆) p := by
    intro v w p
    show curvR cov p (liv v p) (liv w p) (liv v p) = _
    rw [curvR_liv cov p v w v (ht n G hbi cov hLC p _ _ _), curvF_liv_of_d cov hd, Morse.curv_halfLie]
  refine ⟨fun v w p => ?_, fun v w p => ?_⟩
  · rw [key, liv_bracket, liv_bracket, liv_smul]; rfl
  · rw [key, liv_bracket, liv_bracket, ← lie_skew ⁅v, w⁆ v, smul_neg, liv_neg, liv_smul]; rfl

/-- **Bridge**: given `A`, `Core` and `Tens` imply `B`. -/
theorem B_of_core (hA : A) : Core → Tens → B := by
  intro hc ht n G _ _ _ _ _ _ _ hbi cov hLC
  obtain ⟨h1, h2⟩ := Bi_ii_of_core hc ht n G hbi cov hLC
  exact ⟨h1, h2, Biii_of_core hA hc n G hbi cov hLC⟩

#rt_check RoundTrip.V12_11.B_to_A [Morse.jacobiOp_apply, Morse.ad_skew, Morse.jacobiOp_symm, Morse.jacobiOp_self, Morse.jacobiOp_self_nonneg, Morse.jacobiOp_eq_zero_iff, Morse.eigenvalue_nonneg, Morse.ad_eigenvalue_eq_zero]
#rt_overlap RoundTrip.V12_11.B_to_A [Morse.jacobiOp_apply, Morse.ad_skew, Morse.jacobiOp_symm, Morse.jacobiOp_self, Morse.jacobiOp_self_nonneg, Morse.jacobiOp_eq_zero_iff, Morse.eigenvalue_nonneg, Morse.ad_eigenvalue_eq_zero]
#rt_check RoundTrip.V12_11.B_of_core [Morse.jacobiOp_apply, Morse.ad_skew, Morse.jacobiOp_symm, Morse.jacobiOp_self, Morse.jacobiOp_self_nonneg, Morse.jacobiOp_eq_zero_iff, Morse.eigenvalue_nonneg, Morse.ad_eigenvalue_eq_zero]

end RoundTrip.V12_11
