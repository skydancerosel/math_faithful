import Morse
import RoundTrip.Check
import RoundTrip.Blind.V12_9

/-!
# V12_9 (Milnor §21, Corollary 21.5): trivial centre ⇒ positive Ricci curvature ⇒ compact, finite `π₁`

`A` (universe `0`): `Morse.curv_halfLie_eq_jacobiOp ∧ Morse.trace_jacobiOp ∧ Morse.trace_eq_sum_of_isOrtho ∧
Morse.trace_jacobiOp_pos ∧ Morse.killingForm_neg` — for an arbitrary real Lie algebra `L` (finite-dimensional,
with an ad-invariant symmetric positive definite `B` where needed): `curv (halfLie L) V W V = jacobiOp L V W`
(`K_V = R(V,·)V`); `tr K_V = −¼ κ(V,V)` (Mathlib's `killingForm`); the diagonal coefficient of `T` in a
`B`-orthogonal basis is `B(T bᵢ, bᵢ)/B(bᵢ, bᵢ)`; if the centre is trivial, `tr K_V > 0` for `V ≠ 0`, i.e. `κ` is
negative definite.  Pure algebra: the *pointwise* positivity of Ricci on `𝔤`.

`B` (blind): for a connected Lie group with a bi-invariant metric, Levi-Civita connection and `𝔤` with trivial
centre: (R) `∃ c > 0`, `K(U,U) ≥ c` for every unit `U ∈ T_pG`, every `p` (blind `ricci` = trace of the pointwise
`W ↦ curvR(U,W)U`); (T) `G` is compact and `π₁(G, 1)` is finite.

* `B → A`: vacuous (A re-proved outright).
* `A → B` fails.
  - (T) is genuinely out of reach: it needs Myers' theorem (19.5) for abstract complete Riemannian manifolds
    (the project has it only for embedded submanifolds, `Morse.corollary_19_5`, and not the `π₁` part), the
    completeness of a bi-invariant metric, and covering-space theory.
  - (R) needs the geometric inputs `Core` (`X ⊢ X = 0` and metric compatibility on left-invariant fields) and
    `Tens` (tensoriality of the curvature, so that the blind `curvR`/`ricci` are computed by Milnor's field
    formula), and "bounded away from zero", which `A` lacks (`A` gives `tr K_V > 0` for each `V ≠ 0`; the
    uniform bound is a compactness argument not in the project, BiInvariant.lean "Not formalized").
* **Bridge** (`BRic_of_core`, uses `A`, `#rt_check`ed): `Core ∧ Tens` ⇒ (R), on every such group.  Glue: a
  compactness lemma (`quad_bound`: two positive definite quadratic forms on a finite-dimensional space are
  comparable, via the minimum of their quotient on the unit sphere), `ricci p U U = tr (dL_p ∘ K_u ∘ dL_p⁻¹) =
  tr K_u` with `u = dL_p⁻¹ U` (`LinearMap.trace_conj'`), and `ip u u = ‖U‖² = 1` (left invariance); `A` supplies
  `K_u = curv (halfLie 𝔤) u · u`, `tr K_u = −¼ κ(u,u)` and its positivity.
-/

open scoped ContDiff Manifold
open Bundle

set_option linter.unusedSectionVars false

namespace RoundTrip.V12_9

/-- The project's statement (universe `0`). -/
def A : Prop := type_of% @Morse.curv_halfLie_eq_jacobiOp.{0} ∧ type_of% @Morse.trace_jacobiOp.{0} ∧
  type_of% @Morse.trace_eq_sum_of_isOrtho.{0} ∧ type_of% @Morse.trace_jacobiOp_pos.{0} ∧
  type_of% @Morse.killingForm_neg.{0}

theorem A_holds : A :=
  ⟨@Morse.curv_halfLie_eq_jacobiOp.{0}, @Morse.trace_jacobiOp.{0}, @Morse.trace_eq_sum_of_isOrtho.{0},
    @Morse.trace_jacobiOp_pos.{0}, @Morse.killingForm_neg.{0}⟩

/-! ## `A` re-proved outright (for `B_to_A`) -/

namespace Re

variable {L : Type} [LieRing L] [LieAlgebra ℝ L] {B : LinearMap.BilinForm ℝ L}

theorem curv_halfLie_eq_jacobiOp (V W : L) : Morse.curv (Morse.halfLie L) V W V = Morse.jacobiOp L V W := by
  rw [Morse.curv_halfLie, Morse.jacobiOp_apply, ← lie_skew ⁅V, W⁆ V, smul_neg, neg_smul]

theorem trace_jacobiOp (V : L) :
    LinearMap.trace ℝ L (Morse.jacobiOp L V) = -(1 / 4 : ℝ) * killingForm ℝ L V V := by
  rw [Morse.jacobiOp, LinearMap.map_smul_of_tower, smul_eq_mul, LieModule.traceForm_apply_apply]
  rfl

theorem trace_eq_sum_of_isOrtho {n : ℕ} (b : Module.Basis (Fin n) ℝ L)
    (hb : B.IsOrthoᵢ b) (T : Module.End ℝ L) (i : Fin n) :
    B (T (b i)) (b i) = b.repr (T (b i)) i * B (b i) (b i) := by
  conv_lhs => rw [← b.sum_repr (T (b i))]
  rw [map_sum, LinearMap.sum_apply, Finset.sum_eq_single i]
  · rw [map_smul, LinearMap.smul_apply, smul_eq_mul]
  · intro j _ hj
    rw [map_smul, LinearMap.smul_apply, smul_eq_mul, hb hj, mul_zero]
  · simp

theorem trace_jacobiOp_pos [FiniteDimensional ℝ L] (hB : Morse.IsAdInvariant B)
    (hsymm : ∀ x y : L, B x y = B y x) (hpos : ∀ x : L, x ≠ 0 → 0 < B x x)
    (hc : LieAlgebra.center ℝ L = ⊥) {V : L} (hV : V ≠ 0) :
    0 < LinearMap.trace ℝ L (Morse.jacobiOp L V) := by
  have : Invertible (2 : ℝ) := invertibleOfNonzero two_ne_zero
  obtain ⟨b, hb⟩ := LinearMap.BilinForm.exists_orthogonal_basis
    (B := B) (LinearMap.BilinForm.isSymm_iff.1 (LinearMap.BilinForm.isSymm_def.2 hsymm))
  rw [LinearMap.trace_eq_matrix_trace ℝ b, Matrix.trace]
  have hbi : ∀ i, 0 < B (b i) (b i) := fun i => hpos _ (b.ne_zero i)
  have hdiag : ∀ i, LinearMap.toMatrix b b (Morse.jacobiOp L V) i i =
      B (Morse.jacobiOp L V (b i)) (b i) / B (b i) (b i) := by
    intro i
    rw [LinearMap.toMatrix_apply, trace_eq_sum_of_isOrtho b hb, mul_div_cancel_right₀ _
      (hbi i).ne']
  simp only [Matrix.diag_apply, hdiag]
  obtain ⟨i, hi⟩ : ∃ i, ⁅V, b i⁆ ≠ 0 := by
    by_contra h
    push Not at h
    have hcen : V ∈ LieAlgebra.center ℝ L := by
      rw [LieAlgebra.center, LieModule.mem_maxTrivSubmodule]
      intro x
      have : LieAlgebra.ad ℝ L V = 0 := b.ext fun i => by simpa using h i
      rw [← lie_skew, neg_eq_zero]
      exact LinearMap.congr_fun this x
    rw [hc] at hcen
    exact hV hcen
  refine lt_of_lt_of_le ?_ (Finset.single_le_sum (f := fun j =>
    B (Morse.jacobiOp L V (b j)) (b j) / B (b j) (b j))
    (fun j _ => div_nonneg (Morse.jacobiOp_self_nonneg hB hpos V (b j)) (hbi j).le) (Finset.mem_univ i))
  rw [Morse.jacobiOp_self hB]
  have := hpos _ hi
  have := hbi i
  positivity

theorem killingForm_neg [FiniteDimensional ℝ L] (hB : Morse.IsAdInvariant B)
    (hsymm : ∀ x y : L, B x y = B y x) (hpos : ∀ x : L, x ≠ 0 → 0 < B x x)
    (hc : LieAlgebra.center ℝ L = ⊥) {V : L} (hV : V ≠ 0) :
    killingForm ℝ L V V < 0 := by
  have := trace_jacobiOp_pos hB hsymm hpos hc hV
  rw [trace_jacobiOp] at this
  linarith

end Re

/-- Vacuous: `A` re-proved outright, `B` is not used. -/
theorem B_to_A : B → A := fun _ =>
  ⟨@Re.curv_halfLie_eq_jacobiOp, @Re.trace_jacobiOp, @Re.trace_eq_sum_of_isOrtho, @Re.trace_jacobiOp_pos,
    @Re.killingForm_neg⟩

/-! ## Compactness glue: positive definite quadratic forms are comparable -/

section Quad
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem cont_quad (F : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) : Continuous fun u => F u u := by
  let F' : E →L[ℝ] E →L[ℝ] ℝ := LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap : (E →ₗ[ℝ] ℝ) ≃ₗ[ℝ] (E →L[ℝ] ℝ)).toLinearMap ∘ₗ F)
  have : (fun u => F u u) = fun u => F' u u := by ext u; simp [F']
  rw [this]
  exact F'.continuous.clm_apply continuous_id

/-- Two positive definite quadratic forms on a finite-dimensional space: `c Q ≤ F` for some `c > 0`. -/
theorem quad_bound (F Q : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hF : ∀ u, u ≠ 0 → 0 < F u u)
    (hQ : ∀ u, u ≠ 0 → 0 < Q u u) : ∃ c, 0 < c ∧ ∀ u, c * Q u u ≤ F u u := by
  by_cases hE : ∃ u : E, u ≠ 0
  · obtain ⟨u0, hu0⟩ := hE
    let S := Metric.sphere (0 : E) 1
    have hSc : IsCompact S := isCompact_sphere 0 1
    have hSne : S.Nonempty := ⟨‖u0‖⁻¹ • u0, by
      rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.2 hu0)]⟩
    have hS0 : ∀ u ∈ S, u ≠ 0 := fun u hu h => by
      rw [h, mem_sphere_zero_iff_norm, norm_zero] at hu; exact zero_ne_one hu
    have hcont : ContinuousOn (fun u => F u u / Q u u) S :=
      (cont_quad F).continuousOn.div (cont_quad Q).continuousOn fun u hu => (hQ u (hS0 u hu)).ne'
    obtain ⟨x0, hx0, hmin⟩ := hSc.exists_isMinOn hSne hcont
    refine ⟨F x0 x0 / Q x0 x0, div_pos (hF _ (hS0 _ hx0)) (hQ _ (hS0 _ hx0)), fun u => ?_⟩
    rcases eq_or_ne u 0 with rfl | hu
    · simp
    · have hn : 0 < ‖u‖ := norm_pos_iff.2 hu
      have hv : ‖u‖⁻¹ • u ∈ S := by
        rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']
      have h := isMinOn_iff.1 hmin _ hv
      simp only [map_smul, LinearMap.smul_apply, smul_eq_mul] at h
      have hQu := hQ u hu
      have e : ‖u‖⁻¹ * (‖u‖⁻¹ * F u u) / (‖u‖⁻¹ * (‖u‖⁻¹ * Q u u)) = F u u / Q u u := by
        field_simp
      rw [e, le_div_iff₀ hQu] at h
      exact h
  · push Not at hE
    refine ⟨1, one_pos, fun u => ?_⟩
    rw [hE u]; simp

end Quad

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
`IsCurvVal` has a value for all tangent vectors, so that the blind `curvR` (and `ricci`) is the curvature
tensor. -/
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

/-- `B`'s conjunct (R): the Ricci curvature is bounded below by a positive constant. -/
def BRic : Prop :=
  ∀ (n : ℕ) (G : Type) [Group G] [TopologicalSpace G] [T2Space G] [ChartedSpace (Rn n) G] [LieGroup 𝓘(ℝ, Rn n) ∞ G] [ConnectedSpace G] [Bundle.RiemannianBundle (fun x : G => TangentSpace 𝓘(ℝ, Rn n) x)] [IsContMDiffRiemannianBundle 𝓘(ℝ, Rn n) ∞ (Rn n) (fun x : G => TangentSpace 𝓘(ℝ, Rn n) x)],
    BiInvMetric n G → ∀ cov : Conn n G, IsLC cov →
      LieAlgebra.center ℝ (GroupLieAlgebra 𝓘(ℝ, Rn n) G) = ⊥ → ∃ c : ℝ, 0 < c ∧ RicciGE cov c

/-- `B`'s conjunct (T): compactness and finite fundamental group. -/
def BTop : Prop :=
  ∀ (n : ℕ) (G : Type) [Group G] [TopologicalSpace G] [T2Space G] [ChartedSpace (Rn n) G] [LieGroup 𝓘(ℝ, Rn n) ∞ G] [ConnectedSpace G] [Bundle.RiemannianBundle (fun x : G => TangentSpace 𝓘(ℝ, Rn n) x)] [IsContMDiffRiemannianBundle 𝓘(ℝ, Rn n) ∞ (Rn n) (fun x : G => TangentSpace 𝓘(ℝ, Rn n) x)],
    BiInvMetric n G → ∀ cov : Conn n G, IsLC cov →
      LieAlgebra.center ℝ (GroupLieAlgebra 𝓘(ℝ, Rn n) G) = ⊥ → CompactSpace G ∧ Finite (FundamentalGroup G 1)

theorem B_iff : B ↔ BRic ∧ BTop := by
  constructor
  · intro hB
    exact ⟨fun n G _ _ _ _ _ _ _ _ hbi cov hLC hc => (hB n G hbi cov hLC hc).1,
      fun n G _ _ _ _ _ _ _ _ hbi cov hLC hc => (hB n G hbi cov hLC hc).2⟩
  · rintro ⟨h1, h2⟩ n G _ _ _ _ _ _ _ _ hbi cov hLC hc
    exact ⟨h1 n G hbi cov hLC hc, h2 n G hbi cov hLC hc⟩

/-- **Bridge** (uses `A`): `Core ∧ Tens` ⇒ `B`'s Ricci conjunct (R). -/
theorem BRic_of_core (hA : A) : Core → Tens → BRic := by
  intro hc ht n G _ _ _ _ _ _ _ _ hbi cov hLC hcen
  obtain ⟨hgeod, hii⟩ := hc n G hbi cov hLC
  have hd := d_of_geod cov hLC.2.1 hgeod
  have hadj := adInv_of_geod hbi.1 cov hLC.2.1 hii hgeod
  have hsymm : ∀ x y : GroupLieAlgebra 𝓘(ℝ, Rn n) G, ipForm x y = ipForm y x := fun x y => ip_symm x y
  have hpos : ∀ x : GroupLieAlgebra 𝓘(ℝ, Rn n) G, x ≠ 0 → 0 < ipForm x x := fun x hx => ip_pos x hx
  have : FiniteDimensional ℝ (GroupLieAlgebra 𝓘(ℝ, Rn n) G) := inferInstanceAs (FiniteDimensional ℝ (Rn n))
  obtain ⟨h1, h2, -, h4, -⟩ := hA
  -- the uniform bound on `𝔤`
  let F : Rn n →ₗ[ℝ] Rn n →ₗ[ℝ] ℝ := (-(1 / 4 : ℝ)) • killingForm ℝ (GroupLieAlgebra 𝓘(ℝ, Rn n) G)
  let Q : Rn n →ₗ[ℝ] Rn n →ₗ[ℝ] ℝ := ipForm (n := n) (G := G)
  have hF : ∀ u : GroupLieAlgebra 𝓘(ℝ, Rn n) G,
      F u u = LinearMap.trace ℝ _ (Morse.jacobiOp (GroupLieAlgebra 𝓘(ℝ, Rn n) G) u) := by
    intro u
    rw [h2]
    rfl
  have hFpos : ∀ u : Rn n, u ≠ 0 → 0 < F u u := fun u hu => by
    rw [hF u]; exact h4 hadj hsymm hpos hcen hu
  obtain ⟨c, hc0, hcb⟩ := quad_bound F Q hFpos hpos
  refine ⟨c, hc0, fun p U hU => ?_⟩
  -- transport from `p` to `1`
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
  have e1 : liv (e U) p = U := hdL U
  have hU0 : U ≠ 0 := by
    intro h; rw [h, norm_zero] at hU; exact zero_ne_one hU
  have hu0 : e U ≠ 0 := fun h => hU0 (by simpa using congrArg e.symm h)
  have hipu : ip (e U) (e U) = 1 := by
    rw [← inner_liv hbi.1 (e U) (e U) p, e1, real_inner_self_eq_norm_sq, hU, one_pow]
  have hKV : ∀ W : Rn n, curvR cov p U W U =
      e.symm (Morse.jacobiOp (GroupLieAlgebra 𝓘(ℝ, Rn n) G) (e U) (e W)) := by
    intro W
    have e2 : liv (e W) p = W := hdL W
    calc curvR cov p U W U = curvR cov p (liv (e U) p) (liv (e W) p) (liv (e U) p) := by rw [e1, e2]
      _ = curvF cov (liv (e U)) (liv (e W)) (liv (e U)) p :=
          curvR_liv cov p _ _ _ (ht n G hbi cov hLC p _ _ _)
      _ = liv (Morse.curv (Morse.halfLie (GroupLieAlgebra 𝓘(ℝ, Rn n) G)) (e U) (e W) (e U)) p := by
          rw [curvF_liv_of_d cov hd]
      _ = _ := by rw [h1]; rfl
  let L0 : Rn n →ₗ[ℝ] Rn n := e.symm.conj (Morse.jacobiOp (GroupLieAlgebra 𝓘(ℝ, Rn n) G) (e U))
  have hL0 : ∀ W : Rn n, L0 W = curvR cov p U W U := by
    intro W
    rw [hKV W]
    rfl
  have hex : ∃ L : Rn n →ₗ[ℝ] Rn n, ∀ W : Rn n, L W = curvR cov p U W U := ⟨L0, hL0⟩
  have hch : hex.choose = L0 := LinearMap.ext fun W => (hex.choose_spec W).trans (hL0 W).symm
  have hric : ricci cov p U U = LinearMap.trace ℝ (GroupLieAlgebra 𝓘(ℝ, Rn n) G)
      (Morse.jacobiOp (GroupLieAlgebra 𝓘(ℝ, Rn n) G) (e U)) := by
    unfold ricci
    rw [dif_pos hex, hch]
    exact LinearMap.trace_conj' _ e.symm
  rw [hric, ← hF]
  have := hcb (e U)
  rw [show Q (e U) (e U) = 1 from hipu, mul_one] at this
  exact this

#rt_check RoundTrip.V12_9.B_to_A [Morse.curv_halfLie_eq_jacobiOp, Morse.trace_jacobiOp, Morse.trace_eq_sum_of_isOrtho, Morse.trace_jacobiOp_pos, Morse.killingForm_neg]
#rt_overlap RoundTrip.V12_9.B_to_A [Morse.curv_halfLie_eq_jacobiOp, Morse.trace_jacobiOp, Morse.trace_eq_sum_of_isOrtho, Morse.trace_jacobiOp_pos, Morse.killingForm_neg]
#rt_check RoundTrip.V12_9.BRic_of_core [Morse.curv_halfLie_eq_jacobiOp, Morse.trace_jacobiOp, Morse.trace_eq_sum_of_isOrtho, Morse.trace_jacobiOp_pos, Morse.killingForm_neg]

end RoundTrip.V12_9
