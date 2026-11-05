import Morse
import RoundTrip.Check
import RoundTrip.Blind.V12_2

/-!
# V12_2 (Milnor §21, proof of Theorem 21.3 (d)): `X ⊢ Y = ½[X, Y]`

`A` (universe `0`): `Morse.IsLeviCivita.conn_eq` — for an arbitrary real Lie algebra `L`, bilinear form `B`
and bilinear `D : L →ₗ L →ₗ L` with `IsLeviCivita B D` (torsion `D X Y − D Y X = ⁅X,Y⁆` and
`B (D X Y) Z + B Y (D X Z) = 0`), if `D X X = 0` for all `X` then `D X Y = ½⁅X,Y⁆`.  Pure algebra.

`B` (blind): on a Lie group with a bi-invariant metric and a Levi-Civita connection, (i) integral curves of
`X_v` are left translates of one-parameter subgroups, (ii) they are geodesics, (iii) `X_v ⊢ X_v = 0`,
(iv) `X_v ⊢ X_w = ½[X_v, X_w]` as fields.

* `B → A`: vacuous (A re-proved outright: Milnor's two-line expansion).
* `A → B` fails: (i)–(iii) are geometry absent from the project (the project starts from `D X X = 0` as
  a hypothesis; "the passage from the group to the algebra" is not formalized).
* Bridge (`d_of_geod`, uses `A` as hypothesis, `#rt_check`ed): (iii) ⇒ (iv) on every Lie group for any
  *symmetric* connection.  At each `p : G`, `D u v := (dL_p)⁻¹ ((X_u ⊢ X_v)(p))` is a bilinear map on
  `𝔤 = GroupLieAlgebra` with torsion `⁅u, v⁆` (Milnor 8.5, `[X_u, X_v] = X_{⁅u,v⁆}`), so `A` applies
  (with `B := 0`: `A`'s metric hypothesis is not needed for this step).  Hence
  `B ↔ (i) ∧ (ii) ∧ (iii)` given `A` (`B_iff_core`): the algebraic content of `B` is exactly `A`.
-/

open scoped ContDiff Manifold
open Bundle

set_option linter.unusedSectionVars false

namespace RoundTrip.V12_2

/-- The project's statement (universe `0`). -/
def A : Prop := type_of% @Morse.IsLeviCivita.conn_eq.{0}

theorem A_holds : A := @Morse.IsLeviCivita.conn_eq.{0}

/-- Vacuous: `A` re-proved outright (Milnor's expansion of `(X+Y) ⊢ (X+Y) = 0`), `B` is not used. -/
theorem B_to_A : B → A := by
  intro _ L _ _ Bf D hD hgeod X Y
  have h1 : D X Y + D Y X = 0 := by
    have := hgeod (X + Y)
    simp only [map_add, LinearMap.add_apply, hgeod X, hgeod Y, zero_add, add_zero] at this
    rw [add_comm]; exact this
  have h2 := hD.torsion_free X Y
  have : (2 : ℝ) • D X Y = ⁅X, Y⁆ := by
    rw [two_smul]
    calc D X Y + D X Y = (D X Y + D Y X) + (D X Y - D Y X) := by abel
      _ = ⁅X, Y⁆ := by rw [h1, h2, zero_add]
  rw [← this, smul_smul]; norm_num

/-! ## Dictionary: the group `G` and its Lie algebra `𝔤 = GroupLieAlgebra` -/

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
`(u, v) ↦ Φ ((X_u ⊢ X_v)(p))`, bilinear (Mathlib's additivity and `smul_const` of covariant derivatives on
the differentiable sections `X_v`). -/
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

/-- `d(L_a)_{bh} ∘ d(L_b)_h = id` when `a b = 1` (Mathlib's computation in `inverse_mfderiv_mul_left`), with
the base point of the first factor given as any `k = b h`. -/
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

end Dict

open Dict

/-- **Bridge** (uses `A`): on any Lie group, for any symmetric connection, `X ⊢ X = 0` for all
left-invariant `X` implies Milnor's (d) `X ⊢ Y = ½[X, Y]` as fields.  At `p`, `A` is applied to
`𝔤`, the zero form and `D u v = (dL_p)⁻¹ ((X_u ⊢ X_v)(p))`. -/
theorem d_of_geod (hA : A) {n : ℕ} {G : Type} [Group G] [TopologicalSpace G] [ChartedSpace (Rn n) G]
    [LieGroup 𝓘(ℝ, Rn n) ∞ G] (cov : Conn n G) (hsymm : IsSymm cov)
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
  have key := @hA (GroupLieAlgebra 𝓘(ℝ, Rn n) G) _ _ 0 D hLC hD0 u v
  rw [Pi.smul_apply, liv_bracket]
  have e1 : dL (D u v) = (1 / 2 : ℝ) • dL (⁅u, v⁆ : GroupLieAlgebra 𝓘(ℝ, Rn n) G) := by
    rw [key]; exact dL.map_smul _ _
  have e2 : dL (D u v) = covF cov (liv u) (liv v) p := hdL _
  exact e2.symm.trans e1

/-- `B` without its algebraic conjunct (iv): (i)–(iii), the genuinely geometric part. -/
def Bcore : Prop :=
  ∀ (n : ℕ) (G : Type) [Group G] [TopologicalSpace G] [T2Space G] [ChartedSpace (Rn n) G] [LieGroup 𝓘(ℝ, Rn n) ∞ G] [Bundle.RiemannianBundle (fun x : G => TangentSpace 𝓘(ℝ, Rn n) x)] [IsContMDiffRiemannianBundle 𝓘(ℝ, Rn n) ∞ (Rn n) (fun x : G => TangentSpace 𝓘(ℝ, Rn n) x)],
    BiInvMetric n G → ∀ cov : Conn n G, IsLC cov →
      (∀ (v : GroupLieAlgebra 𝓘(ℝ, Rn n) G) (c : ℝ → G), IsMIntegralCurve c (liv v) →
        (∃ φ : ℝ → G, (∀ s t : ℝ, φ (s + t) = φ s * φ t) ∧ ∀ t : ℝ, c t = c 0 * φ t) ∧
        IsGeodesic cov c Set.univ) ∧
      (∀ v : GroupLieAlgebra 𝓘(ℝ, Rn n) G, covF cov (liv v) (liv v) = 0)

/-- Given `A`, `B` is exactly its geometric core (i)–(iii). -/
theorem B_iff_core (hA : A) : B ↔ Bcore := by
  constructor
  · intro hB n G _ _ _ _ _ _ _ hbi cov hLC
    obtain ⟨h1, h2, _⟩ := hB n G hbi cov hLC
    exact ⟨h1, h2⟩
  · intro hB n G _ _ _ _ _ _ _ hbi cov hLC
    obtain ⟨h1, h2⟩ := hB n G hbi cov hLC
    exact ⟨h1, h2, fun v w => d_of_geod hA cov hLC.2.1 h2 v w⟩

#rt_check RoundTrip.V12_2.B_to_A [Morse.IsLeviCivita.conn_eq]
#rt_overlap RoundTrip.V12_2.B_to_A [Morse.IsLeviCivita.conn_eq]
#rt_check RoundTrip.V12_2.d_of_geod [Morse.IsLeviCivita.conn_eq]
#rt_check RoundTrip.V12_2.B_iff_core [Morse.IsLeviCivita.conn_eq]

end RoundTrip.V12_2
