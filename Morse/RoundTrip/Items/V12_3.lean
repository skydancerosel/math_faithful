import Morse
import RoundTrip.Check
import RoundTrip.Blind.V12_3

/-!
# V12_3 (Milnor §21, Theorem 21.3 (a)): the bi-invariant metric is ad-invariant

`A` (universe `0`): `Morse.IsLeviCivita.isAdInvariant` — for an arbitrary real Lie algebra `L`, bilinear
form `B` and bilinear `D` with `IsLeviCivita B D` (torsion `⁅X,Y⁆`, `B (D X Y) Z + B Y (D X Z) = 0`) and
`D X X = 0` for all `X`: `B ⁅X,Y⁆ Z = B X ⁅Y,Z⁆`.  Pure algebra.

`B` (blind): on a Lie group with a bi-invariant metric and a Levi-Civita connection, for left-invariant
`X_u, X_v, X_w`: (i) `⟨X_u, X_w⟩` is constant; (ii) `Y⟨X,Z⟩ = ⟨Y ⊢ X, Z⟩ + ⟨X, Y ⊢ Z⟩`; (iii)
`⟨[X,Y],Z⟩ = ⟨X,[Y,Z]⟩` at every point.

* `B → A`: vacuous (A re-proved outright).
* `A → B` fails: (ii) is the derivative form of metric compatibility, which needs parallel transport /
  frames on an abstract manifold (the blind `IsCompat` is the parallel-transport definition), and (iii)
  needs `X ⊢ X = 0` (one-parameter subgroups are geodesics) — both absent from the project.
* Glue: (i) holds outright (`Bi_holds`, left invariance).  **Bridge** (`adInv_of_A`, uses `A`): (ii) and
  `X ⊢ X = 0` (B of V12_2 (iii)) imply (iii), by applying `A` to `𝔤 = GroupLieAlgebra` with the metric at
  `1` and `D u v = (X_u ⊢ X_v)(1)` — Milnor's proof, with (ii) at `1` giving `IsLeviCivita`'s metric
  clause because `⟨X, Z⟩` is constant.  Only *left* invariance of the metric is used: right invariance
  enters only through `X ⊢ X = 0`.
-/

open scoped ContDiff Manifold
open Bundle

set_option linter.unusedSectionVars false

namespace RoundTrip.V12_3

/-- The project's statement (universe `0`). -/
def A : Prop := type_of% @Morse.IsLeviCivita.isAdInvariant.{0}

theorem A_holds : A := @Morse.IsLeviCivita.isAdInvariant.{0}

/-- Vacuous: `A` re-proved outright (Milnor's (d) then the metric clause), `B` is not used. -/
theorem B_to_A : B → A := by
  intro _ L _ _ Bf D hD hgeod
  have d : ∀ X Y : L, D X Y = (1 / 2 : ℝ) • ⁅X, Y⁆ := by
    intro X Y
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
  intro X Y Z
  have := hD.metric Y X Z
  rw [d, d, map_smul, LinearMap.smul_apply, map_smul,
    smul_eq_mul, smul_eq_mul, ← lie_skew, map_neg, LinearMap.neg_apply] at this
  linarith

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

variable {n : ℕ} {G : Type} [Group G] [TopologicalSpace G] [ChartedSpace (Rn n) G]
  [LieGroup 𝓘(ℝ, Rn n) ∞ G] [Bundle.RiemannianBundle (fun x : G => TangentSpace 𝓘(ℝ, Rn n) x)]

/-- `B`'s conjunct (i) holds outright for a left-invariant metric. -/
theorem Bi_holds (hL : LeftInvMetric n G) (u w : GroupLieAlgebra 𝓘(ℝ, Rn n) G) (p q : G) :
    inner ℝ (liv u p) (liv w p) = inner ℝ (liv u q) (liv w q) := by
  rw [inner_liv hL, inner_liv hL]

/-- `B`'s conjunct (ii) (the derivative form of metric compatibility) for `G, cov`. -/
def Bii (cov : Conn n G) : Prop :=
  ∀ (u v w : GroupLieAlgebra 𝓘(ℝ, Rn n) G) (p : G), dirD (fun q => inner ℝ (liv u q) (liv w q)) p (liv v p)
    = inner ℝ (covF cov (liv v) (liv u) p) (liv w p) + inner ℝ (liv u p) (covF cov (liv v) (liv w) p)

/-- **Bridge** (uses `A`): for a left-invariant metric and a symmetric connection satisfying (ii), with
`X ⊢ X = 0` for left-invariant `X`, the conclusion (iii) of `B` holds (Milnor's proof of 21.3(a)). -/
theorem adInv_of_A (hA : A) (hL : LeftInvMetric n G) (cov : Conn n G) (hsymm : IsSymm cov)
    (hii : Bii cov) (hgeod : ∀ v : GroupLieAlgebra 𝓘(ℝ, Rn n) G, covF cov (liv v) (liv v) = 0)
    (u v w : GroupLieAlgebra 𝓘(ℝ, Rn n) G) (p : G) :
    inner ℝ (VectorField.mlieBracket 𝓘(ℝ, Rn n) (liv u) (liv v) p) (liv w p)
      = inner ℝ (liv u p) (VectorField.mlieBracket 𝓘(ℝ, Rn n) (liv v) (liv w) p) := by
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
  have key := @hA (GroupLieAlgebra 𝓘(ℝ, Rn n) G) _ _ ipForm D hLC hD0 u v w
  rw [liv_bracket, liv_bracket, inner_liv hL, inner_liv hL]
  exact key

/-- The geometric inputs: `B`'s (ii) and `X ⊢ X = 0` (B of V12_2 (iii)). -/
def Bcore : Prop :=
  ∀ (n : ℕ) (G : Type) [Group G] [TopologicalSpace G] [T2Space G] [ChartedSpace (Rn n) G] [LieGroup 𝓘(ℝ, Rn n) ∞ G] [Bundle.RiemannianBundle (fun x : G => TangentSpace 𝓘(ℝ, Rn n) x)] [IsContMDiffRiemannianBundle 𝓘(ℝ, Rn n) ∞ (Rn n) (fun x : G => TangentSpace 𝓘(ℝ, Rn n) x)],
    BiInvMetric n G → ∀ cov : Conn n G, IsLC cov →
      Bii cov ∧ ∀ v : GroupLieAlgebra 𝓘(ℝ, Rn n) G, covF cov (liv v) (liv v) = 0

/-- Given `A`, the geometric core implies `B`. -/
theorem B_of_core (hA : A) : Bcore → B := by
  intro hc n G _ _ _ _ _ _ _ hbi cov hLC
  obtain ⟨hii, hgeod⟩ := hc n G hbi cov hLC
  exact ⟨Bi_holds hbi.1, hii, adInv_of_A hA hbi.1 cov hLC.2.1 hii hgeod⟩

#rt_check RoundTrip.V12_3.B_to_A [Morse.IsLeviCivita.isAdInvariant]
#rt_overlap RoundTrip.V12_3.B_to_A [Morse.IsLeviCivita.isAdInvariant]
#rt_check RoundTrip.V12_3.adInv_of_A [Morse.IsLeviCivita.isAdInvariant]
#rt_check RoundTrip.V12_3.B_of_core [Morse.IsLeviCivita.isAdInvariant]

end RoundTrip.V12_3
