import Morse
import RoundTrip.Check
import RoundTrip.Blind.V12_8

/-!
# V12_8 (Milnor §21, Corollary 21.4): the sectional curvature `⟨R(X,Y)X,Y⟩ = ¼|[X,Y]|² ≥ 0`

`A` (universe `0`): `Morse.sectional ∧ Morse.sectional_nonneg ∧ Morse.sectional_eq_zero_iff ∧
Morse.sectional_std` — for an arbitrary real Lie algebra `L` and an ad-invariant bilinear form `B`
(`Morse.IsAdInvariant`; positive definite for `sectional_nonneg`, `sectional_eq_zero_iff`):
`B (curv (halfLie L) X Y X) Y = ¼ B ⁅X,Y⁆ ⁅X,Y⁆`, it is `≥ 0` and `= 0 ↔ ⁅X,Y⁆ = 0` (for positive `B`), and
`B (−curv (halfLie L) X Y Y) X = ¼ B ⁅X,Y⁆ ⁅X,Y⁆` (usual sign).  Pure algebra; `curv (halfLie L)` is Milnor's
field formula for `R` with the connection `X ⊢ Y = ½[X,Y]` of (d).

`B` (blind): on a Lie group `G` (Mathlib `LieGroup`) with a smooth bi-invariant metric and a Levi-Civita
connection `cov`, for left-invariant `X_u, X_v` and every `p`: `⟨R(X_u,X_v)X_u, X_v⟩(p) = ¼|[X_u,X_v](p)|²`,
`≥ 0`, and `= 0 ↔ [X_u, X_v] = 0` (`curvF`, Milnor's field formula).

* `B → A`: vacuous (A re-proved outright from `Morse.curv_inner`, which is not an item theorem).
* `A → B` fails: `A` says nothing about Lie groups.  The project does not formalize the passage from the
  group to the algebra (BiInvariant.lean, "Not formalized"): that left-invariant fields satisfy
  `X ⊢ X = 0` (one-parameter subgroups are geodesics) and the derivative form of metric compatibility.
* **Bridge** (`B_of_core`, uses `A`, `#rt_check`ed): exactly those two geometric inputs (`Core`) imply `B`.
  With them, the project's `Morse.IsLeviCivita.conn_eq` gives (d) and `Morse.IsLeviCivita.isAdInvariant`
  gives 21.3(a) for the metric at `1` (`ipForm`); then `curvF` on left-invariant fields is
  `liv (curv (halfLie 𝔤) u v u)`, `⟨X_a, X_b⟩ ≡ ⟨a, b⟩`, `[X_u, X_v] = X_{⁅u,v⁆}`, and `A` applied to
  `𝔤 = GroupLieAlgebra` with `ipForm` (positive definite) is `B`.  So `A` carries exactly the algebraic step.
-/

open scoped ContDiff Manifold
open Bundle

set_option linter.unusedSectionVars false

namespace RoundTrip.V12_8

/-- The project's statement (universe `0`). -/
def A : Prop := type_of% @Morse.sectional.{0} ∧ type_of% @Morse.sectional_nonneg.{0} ∧
  type_of% @Morse.sectional_eq_zero_iff.{0} ∧ type_of% @Morse.sectional_std.{0}

theorem A_holds : A :=
  ⟨@Morse.sectional.{0}, @Morse.sectional_nonneg.{0}, @Morse.sectional_eq_zero_iff.{0}, @Morse.sectional_std.{0}⟩

/-- Vacuous: `A` re-proved outright from `Morse.curv_inner` (21.3(c)), `B` is not used. -/
theorem B_to_A : B → A := by
  intro _
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro L _ _ Bf hB X Y
    exact Morse.curv_inner hB X Y X Y
  · intro L _ _ Bf hB hpos X Y
    rw [Morse.curv_inner hB]
    have := Morse.sq_nonneg_of_pos hpos ⁅X, Y⁆
    positivity
  · intro L _ _ Bf hB hpos X Y
    rw [Morse.curv_inner hB]
    constructor
    · intro h
      by_contra hne
      have := hpos _ hne
      linarith
    · intro h; simp [h]
  · intro L _ _ Bf hB X Y
    rw [map_neg, LinearMap.neg_apply, Morse.curv_inner hB, ← lie_skew Y X, map_neg]
    ring

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

/-- **Bridge** (uses `A`): the geometric inputs `Core` imply `B`. -/
theorem B_of_core (hA : A) : Core → B := by
  intro hc n G _ _ _ _ _ _ _ hbi cov hLC u v p
  obtain ⟨hgeod, hii⟩ := hc n G hbi cov hLC
  have hd := d_of_geod cov hLC.2.1 hgeod
  have hadj := adInv_of_geod hbi.1 cov hLC.2.1 hii hgeod
  have hpos : ∀ x : GroupLieAlgebra 𝓘(ℝ, Rn n) G, x ≠ 0 → 0 < ipForm x x := fun x hx => ip_pos x hx
  obtain ⟨h1, h2, h3, -⟩ := hA
  rw [curvF_liv_of_d cov hd u v u, liv_bracket, inner_liv hbi.1, inner_liv hbi.1, liv_eq_zero_iff]
  exact ⟨h1 hadj u v, h2 hadj hpos u v, h3 hadj hpos u v⟩

#rt_check RoundTrip.V12_8.B_to_A [Morse.sectional, Morse.sectional_nonneg, Morse.sectional_eq_zero_iff, Morse.sectional_std]
#rt_overlap RoundTrip.V12_8.B_to_A [Morse.sectional, Morse.sectional_nonneg, Morse.sectional_eq_zero_iff, Morse.sectional_std]
#rt_check RoundTrip.V12_8.B_of_core [Morse.sectional, Morse.sectional_nonneg, Morse.sectional_eq_zero_iff, Morse.sectional_std]

end RoundTrip.V12_8
