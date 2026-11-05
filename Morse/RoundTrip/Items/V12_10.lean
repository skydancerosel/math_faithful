import Morse
import RoundTrip.Check
import RoundTrip.Blind.V12_10

/-!
# V12_10 (Milnor §21, Corollary 21.6 and its proof, pp. 115–116): splitting off the centre

`A` (universe `0`): `Morse.mem_centerCompl ∧ Morse.isCompl_center_centerCompl ∧
Morse.eq_zero_of_mem_centerCompl` — for an arbitrary real Lie algebra `L` with an ad-invariant bilinear form `B`
(symmetric, positive definite, `L` finite-dimensional where needed): `centerCompl hB` (vocabulary: Mathlib's
`LieAlgebra.InvariantForm.orthogonal B _ (center)`, a Lie *ideal*) is `{X | ∀ C ∈ 𝔠, B C X = 0}`, it is a
complement of the centre `𝔠` (`IsCompl`), and it has trivial centre.  Pure algebra.

`B` (blind): for a simply connected Lie group `G` with a bi-invariant metric, in `𝔤 = T_1G` with the metric at
`1`: (i) `⟨[X,Y],C⟩ = ⟨X,[Y,C]⟩ = 0` for `X, Y ∈ 𝔤' = 𝔠^⊥`, `C ∈ 𝔠`; (ii) `𝔤'` is closed under brackets;
(iii) `𝔤 = 𝔤' ⊕ 𝔠` (unique decomposition); and (iv) the splitting: `G ≅ G' × ℝᵏ` as Lie groups, `G'` compact
Hausdorff with Lie algebra of trivial centre.

* `B → A`: vacuous (A re-proved outright, Mathlib's `InvariantForm.orthogonal`).
* `A → B` fails, genuinely: (iv) is Lie theory far beyond the project (the Lie group–Lie algebra
  correspondence for simply connected groups, the compactness of `G'` from 21.5/Myers on an abstract
  manifold); the project formalizes nothing of the splitting of `G`.  (i)–(iii) need, besides `A`, only 21.3(a)
  for the metric at `1` (`AdInv`), a geometric input (from right invariance, or from `Core` and a Levi-Civita
  connection: `adInv_of_core`).
* **Bridge** (`Balg_of_adInv`, uses `A`, `#rt_check`ed): `AdInv` ⇒ (i) ∧ (ii) ∧ (iii) on every such group.
  `A` supplies (iii) (`IsCompl`) and the membership criterion; (ii) is the ideal property built into the
  vocabulary `centerCompl` (Mathlib).  `A`'s third conjunct (`𝔤'` has trivial centre) is not used by `B`'s
  (i)–(iii): in `B` it is part of (iv) (the centre of `Lie(G')`).
-/

open scoped ContDiff Manifold
open Bundle

set_option linter.unusedSectionVars false

namespace RoundTrip.V12_10

/-- The project's statement (universe `0`). -/
def A : Prop := type_of% @Morse.mem_centerCompl.{0} ∧ type_of% @Morse.isCompl_center_centerCompl.{0} ∧
  type_of% @Morse.eq_zero_of_mem_centerCompl.{0}

theorem A_holds : A :=
  ⟨@Morse.mem_centerCompl.{0}, @Morse.isCompl_center_centerCompl.{0}, @Morse.eq_zero_of_mem_centerCompl.{0}⟩

/-! ## `A` re-proved outright (for `B_to_A`) -/

namespace Re

variable {L : Type} [LieRing L] [LieAlgebra ℝ L] {B : LinearMap.BilinForm ℝ L}

theorem mem_centerCompl (hB : Morse.IsAdInvariant B) (X : L) :
    X ∈ Morse.centerCompl hB ↔ ∀ C ∈ LieAlgebra.center ℝ L, B C X = 0 :=
  LieAlgebra.InvariantForm.mem_orthogonal _ _ _ _

theorem isCompl_center_centerCompl [FiniteDimensional ℝ L] (hB : Morse.IsAdInvariant B)
    (hsymm : ∀ x y : L, B x y = B y x) (hpos : ∀ x : L, x ≠ 0 → 0 < B x x) :
    IsCompl (LieAlgebra.center ℝ L).toSubmodule (Morse.centerCompl hB).toSubmodule := by
  rw [Morse.centerCompl, LieAlgebra.InvariantForm.orthogonal_toSubmodule,
    LinearMap.BilinForm.isCompl_orthogonal_iff_disjoint
      (LinearMap.BilinForm.isSymm_def.2 hsymm).isRefl]
  rw [Submodule.disjoint_def]
  intro x hx hx'
  rw [LinearMap.BilinForm.mem_orthogonal_iff] at hx'
  by_contra h
  have := hpos x h
  rw [hx' x hx] at this
  exact lt_irrefl _ this

theorem eq_zero_of_mem_centerCompl [FiniteDimensional ℝ L] (hB : Morse.IsAdInvariant B)
    (hsymm : ∀ x y : L, B x y = B y x) (hpos : ∀ x : L, x ≠ 0 → 0 < B x x) {X : L}
    (hX : X ∈ Morse.centerCompl hB) (hcomm : ∀ Y ∈ Morse.centerCompl hB, ⁅X, Y⁆ = 0) : X = 0 := by
  have hcompl := isCompl_center_centerCompl hB hsymm hpos
  have hcen : X ∈ LieAlgebra.center ℝ L := by
    rw [LieAlgebra.center, LieModule.mem_maxTrivSubmodule]
    intro Z
    have hZ : Z ∈ (LieAlgebra.center ℝ L).toSubmodule ⊔ (Morse.centerCompl hB).toSubmodule := by
      rw [hcompl.sup_eq_top]; exact Submodule.mem_top
    obtain ⟨c, hc, y, hy, rfl⟩ := Submodule.mem_sup.1 hZ
    have hc' : ⁅c, X⁆ = 0 := by
      rw [← lie_skew, (LieModule.mem_maxTrivSubmodule ℝ L L c).1 hc X, neg_zero]
    rw [add_lie, hc', zero_add, ← lie_skew, hcomm y hy, neg_zero]
  have : X ∈ (LieAlgebra.center ℝ L).toSubmodule ⊓ (Morse.centerCompl hB).toSubmodule := ⟨hcen, hX⟩
  rw [hcompl.inf_eq_bot] at this
  exact this

end Re

/-- Vacuous: `A` re-proved outright, `B` is not used. -/
theorem B_to_A : B → A := fun _ =>
  ⟨@Re.mem_centerCompl, @Re.isCompl_center_centerCompl, @Re.eq_zero_of_mem_centerCompl⟩

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

/-- The geometric input of (i)–(iii): 21.3(a) for the metric at `1`, on every Lie group with a bi-invariant
metric (`B` itself has no connection). -/
def AdInv : Prop :=
  ∀ (n : ℕ) (G : Type) [Group G] [TopologicalSpace G] [T2Space G] [ChartedSpace (Rn n) G] [LieGroup 𝓘(ℝ, Rn n) ∞ G] [Bundle.RiemannianBundle (fun x : G => TangentSpace 𝓘(ℝ, Rn n) x)] [IsContMDiffRiemannianBundle 𝓘(ℝ, Rn n) ∞ (Rn n) (fun x : G => TangentSpace 𝓘(ℝ, Rn n) x)],
    BiInvMetric n G → Morse.IsAdInvariant (ipForm (n := n) (G := G))

/-- `AdInv` follows from `Core` and the existence of a Levi-Civita connection (Milnor 8.6, not formalized for
Mathlib manifolds). -/
theorem adInv_of_core : Core →
    (∀ (n : ℕ) (G : Type) [Group G] [TopologicalSpace G] [T2Space G] [ChartedSpace (Rn n) G] [LieGroup 𝓘(ℝ, Rn n) ∞ G] [Bundle.RiemannianBundle (fun x : G => TangentSpace 𝓘(ℝ, Rn n) x)] [IsContMDiffRiemannianBundle 𝓘(ℝ, Rn n) ∞ (Rn n) (fun x : G => TangentSpace 𝓘(ℝ, Rn n) x)],
      BiInvMetric n G → ∃ cov : Conn n G, IsLC cov) → AdInv := by
  intro hc hex n G _ _ _ _ _ _ _ hbi
  obtain ⟨cov, hLC⟩ := hex n G hbi
  obtain ⟨hgeod, hii⟩ := hc n G hbi cov hLC
  exact adInv_of_geod hbi.1 cov hLC.2.1 hii hgeod

/-- `B`'s algebraic conjuncts (i)–(iii). -/
def Balg : Prop :=
  ∀ (n : ℕ) (G : Type) [Group G] [TopologicalSpace G] [T2Space G] [ChartedSpace (Rn n) G] [LieGroup 𝓘(ℝ, Rn n) ∞ G] [Bundle.RiemannianBundle (fun x : G => TangentSpace 𝓘(ℝ, Rn n) x)] [IsContMDiffRiemannianBundle 𝓘(ℝ, Rn n) ∞ (Rn n) (fun x : G => TangentSpace 𝓘(ℝ, Rn n) x)],
    BiInvMetric n G → SimplyConnectedSpace G →
      (∀ X Y C : GroupLieAlgebra 𝓘(ℝ, Rn n) G, InPerpCentre X → InPerpCentre Y → C ∈ LieAlgebra.center ℝ (GroupLieAlgebra 𝓘(ℝ, Rn n) G) →
          ip ⁅X, Y⁆ C = ip X ⁅Y, C⁆ ∧ ip X ⁅Y, C⁆ = 0) ∧
      (∀ X Y : GroupLieAlgebra 𝓘(ℝ, Rn n) G, InPerpCentre X → InPerpCentre Y → InPerpCentre ⁅X, Y⁆) ∧
      (∀ Z : GroupLieAlgebra 𝓘(ℝ, Rn n) G, ∃! q : GroupLieAlgebra 𝓘(ℝ, Rn n) G × GroupLieAlgebra 𝓘(ℝ, Rn n) G, InPerpCentre q.1 ∧ q.2 ∈ LieAlgebra.center ℝ (GroupLieAlgebra 𝓘(ℝ, Rn n) G) ∧ Z = q.1 + q.2)

/-- `B` is `Balg` plus the splitting (iv). -/
theorem B_iff : B ↔ Balg ∧
    ∀ (n : ℕ) (G : Type) [Group G] [TopologicalSpace G] [T2Space G] [ChartedSpace (Rn n) G] [LieGroup 𝓘(ℝ, Rn n) ∞ G] [Bundle.RiemannianBundle (fun x : G => TangentSpace 𝓘(ℝ, Rn n) x)] [IsContMDiffRiemannianBundle 𝓘(ℝ, Rn n) ∞ (Rn n) (fun x : G => TangentSpace 𝓘(ℝ, Rn n) x)],
    BiInvMetric n G → SimplyConnectedSpace G →
      ∃ (m k : ℕ) (G' : Type) (_ : Group G') (_ : TopologicalSpace G') (_ : T2Space G') (_ : ChartedSpace (Rn m) G')
        (_ : LieGroup 𝓘(ℝ, Rn m) ∞ G'),
        CompactSpace G' ∧ LieAlgebra.center ℝ (GroupLieAlgebra 𝓘(ℝ, Rn m) G') = ⊥ ∧
        ∃ φ : Diffeomorph ((𝓘(ℝ, Rn m)).prod 𝓘(ℝ, Rn k)) 𝓘(ℝ, Rn n) (G' × Rn k) G ∞,
          ∀ (a a' : G') (x x' : Rn k), φ (a * a', x + x') = φ (a, x) * φ (a', x') := by
  constructor
  · intro hB
    refine ⟨fun n G _ _ _ _ _ _ _ hbi hsc => ?_, fun n G _ _ _ _ _ _ _ hbi hsc => ?_⟩
    · obtain ⟨a, b, c, -⟩ := hB n G hbi hsc
      exact ⟨a, b, c⟩
    · obtain ⟨-, -, -, d⟩ := hB n G hbi hsc
      exact d
  · rintro ⟨h1, h2⟩ n G _ _ _ _ _ _ _ hbi hsc
    obtain ⟨a, b, c⟩ := h1 n G hbi hsc
    exact ⟨a, b, c, h2 n G hbi hsc⟩

/-- **Bridge** (uses `A`): 21.3(a) at `1` implies `B`'s algebraic conjuncts (i)–(iii). -/
theorem Balg_of_adInv (hA : A) : AdInv → Balg := by
  intro hadjAll n G _ _ _ _ _ _ _ hbi _
  have hadj := hadjAll n G hbi
  obtain ⟨hmem, hcompl, -⟩ := hA
  have : FiniteDimensional ℝ (GroupLieAlgebra 𝓘(ℝ, Rn n) G) := inferInstanceAs (FiniteDimensional ℝ (Rn n))
  have hsymm : ∀ x y : GroupLieAlgebra 𝓘(ℝ, Rn n) G, ipForm x y = ipForm y x := fun x y => ip_symm x y
  have hpos : ∀ x : GroupLieAlgebra 𝓘(ℝ, Rn n) G, x ≠ 0 → 0 < ipForm x x := fun x hx => ip_pos x hx
  have hperp : ∀ X, InPerpCentre X ↔ X ∈ Morse.centerCompl hadj := by
    intro X
    rw [hmem hadj X]
    exact forall₂_congr fun C _ => by rw [ipForm_apply, ip_symm]
  have hc := hcompl hadj hsymm hpos
  refine ⟨?_, ?_, ?_⟩
  · intro X Y C _ _ hC
    have hYC : ⁅Y, C⁆ = 0 := (LieModule.mem_maxTrivSubmodule ℝ _ _ C).1 hC Y
    refine ⟨hadj X Y C, ?_⟩
    rw [hYC]
    exact (ipForm (n := n) (G := G) X).map_zero
  · intro X Y hX hY
    rw [hperp] at hX hY ⊢
    exact (Morse.centerCompl hadj).lie_mem hY
  · intro Z
    have hZ : Z ∈ (LieAlgebra.center ℝ (GroupLieAlgebra 𝓘(ℝ, Rn n) G)).toSubmodule ⊔
        (Morse.centerCompl hadj).toSubmodule := by
      rw [hc.sup_eq_top]; exact Submodule.mem_top
    obtain ⟨c, hcmem, y, hy, rfl⟩ := Submodule.mem_sup.1 hZ
    refine ⟨(y, c), ⟨(hperp y).2 hy, hcmem, add_comm _ _⟩, ?_⟩
    rintro ⟨y', c'⟩ ⟨hy', hc', he⟩
    have he' : y' - y = c - c' := by
      simp only at he
      rw [sub_eq_sub_iff_add_eq_add, ← he, add_comm]
    have h1 : y' - y ∈ (Morse.centerCompl hadj).toSubmodule := sub_mem ((hperp y').1 hy') hy
    have h2 : y' - y ∈ (LieAlgebra.center ℝ (GroupLieAlgebra 𝓘(ℝ, Rn n) G)).toSubmodule := by
      rw [he']; exact sub_mem hcmem hc'
    have h0 : y' - y = 0 := Submodule.disjoint_def.1 hc.disjoint _ h2 h1
    have hyy : y' = y := sub_eq_zero.1 h0
    have hcc : c' = c := by
      rw [h0] at he'
      exact (sub_eq_zero.1 he'.symm).symm
    simp only [hyy, hcc]

#rt_check RoundTrip.V12_10.B_to_A [Morse.mem_centerCompl, Morse.isCompl_center_centerCompl, Morse.eq_zero_of_mem_centerCompl]
#rt_overlap RoundTrip.V12_10.B_to_A [Morse.mem_centerCompl, Morse.isCompl_center_centerCompl, Morse.eq_zero_of_mem_centerCompl]
#rt_check RoundTrip.V12_10.Balg_of_adInv [Morse.mem_centerCompl, Morse.isCompl_center_centerCompl, Morse.eq_zero_of_mem_centerCompl]
#rt_check RoundTrip.V12_10.adInv_of_core [Morse.mem_centerCompl, Morse.isCompl_center_centerCompl, Morse.eq_zero_of_mem_centerCompl]

end RoundTrip.V12_10
