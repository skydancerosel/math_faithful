import Morse
import RoundTrip.Check
import RoundTrip.Blind.V12_1

/-!
# V12_1 (Milnor §21, p. 113): the algebraic model of a bi-invariant metric

`A` (universe `0`): `Morse.isAdInvariant_iff_lieInvariant` — for an arbitrary real Lie algebra `L` and an
arbitrary bilinear form `B`, the project's `IsAdInvariant B` (`⟨[X,Y],Z⟩ = ⟨X,[Y,Z]⟩`) is Mathlib's
`B.lieInvariant L`.  The other two declarations of the item (`Morse.IsAdInvariant`, `Morse.IsLeviCivita`)
are vocabulary: the project formalizes §21 for an *abstract* Lie algebra with a bilinear form `B` and an
abstract bilinear "connection" `D : L →ₗ L →ₗ L`; the passage from the group to the algebra is not
formalized (BiInvariant.lean, "Not formalized").

`B` (blind): for a Lie group `G` with a bi-invariant metric and a Levi-Civita connection, six facts about
left-invariant fields `X_u = liv u`.

Neither direction is non-vacuous.  `B → A` is proved outright (`A` is a two-line algebraic identity).
`A → B` fails: `A` says nothing about Lie groups.  The dictionary below makes precise what each side has:
* `B` conjuncts (1), (2), (4) are proved here outright from Mathlib and the hypotheses (`B1_holds`,
  `B2_holds`, `B4_holds`; the last needs `C^∞` smoothness of left-invariant fields, `isSmoothVF_liv`,
  which Mathlib only has in class `C²`);
* with `𝔤 = GroupLieAlgebra`, `ipForm` = the metric at `1` as a Mathlib bilinear form and
  `connAt cov 1 id` = `(u, v) ↦ (X_u ⊢ X_v)(1)` as a bilinear map, `B`'s (4) ∧ (5) is *exactly* the
  project's `Morse.IsLeviCivita ipForm (connAt cov 1 id)` (`isLeviCivita_iff`) and `B`'s (6) is
  exactly `Morse.IsAdInvariant ipForm`, hence, by `A`, Mathlib's `ipForm.lieInvariant`
  (`B6_iff_lieInvariant`, which uses `A` as hypothesis);
* what is missing for `A → B` is geometry: (3) left-invariance of `X_u ⊢ X_v`, (5) the derivative form
  of metric compatibility (from the blind parallel-transport definition), and (6) 21.3(a) itself
  (which needs `X ⊢ X = 0`, i.e. that one-parameter subgroups are geodesics).
-/

open scoped ContDiff Manifold
open Bundle

set_option linter.unusedSectionVars false

namespace RoundTrip.V12_1

/-- The project's statement (universe `0`). -/
def A : Prop := type_of% @Morse.isAdInvariant_iff_lieInvariant.{0}

theorem A_holds : A := @Morse.isAdInvariant_iff_lieInvariant.{0}

/-- Vacuous: `A` is re-proved outright (Lie skew-symmetry), `B` is not used. -/
theorem B_to_A : B → A := by
  intro _ L _ _ Bf
  constructor
  · intro h x y z
    have := h y x z
    rw [← lie_skew, map_neg, LinearMap.neg_apply] at this
    linarith
  · intro h X Y Z
    have := h Y X Z
    rw [← lie_skew, map_neg, LinearMap.neg_apply] at this
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

/-- `B`'s conjunct (1) holds outright (Mathlib's `mulInvariantVector_mlieBracket`). -/
theorem B1_holds (u v : GroupLieAlgebra 𝓘(ℝ, Rn n) G) :
    VectorField.mlieBracket 𝓘(ℝ, Rn n) (liv u) (liv v) = liv ⁅u, v⁆ := liv_bracket u v

/-- `B`'s conjunct (2) holds outright for a left-invariant metric. -/
theorem B2_holds (hbi : BiInvMetric n G) (u v : GroupLieAlgebra 𝓘(ℝ, Rn n) G) (p : G) :
    inner ℝ (liv u p) (liv v p) = ip u v := inner_liv hbi.1 u v p

/-- `B`'s conjunct (4) holds outright for a symmetric connection (Milnor 8.5 at `1`). -/
theorem B4_holds (cov : Conn n G) (hLC : IsLC cov) (u v : GroupLieAlgebra 𝓘(ℝ, Rn n) G) :
    covF cov (liv u) (liv v) 1 - covF cov (liv v) (liv u) 1 = ⁅u, v⁆ := by
  have h := hLC.2.1 (liv u) (liv v) (isSmoothVF_liv u) (isSmoothVF_liv v) 1
  rw [liv_bracket, liv_one ⁅u, v⁆] at h
  exact h

/-- The project's `IsLeviCivita` on `𝔤` is exactly `B`'s conjuncts (4) ∧ (5), for the metric at `1`
(`ipForm`) and the connection `(u, v) ↦ (X_u ⊢ X_v)(1)` (`connAt cov 1 id`). -/
theorem isLeviCivita_iff (cov : Conn n G) :
    Morse.IsLeviCivita (ipForm (n := n) (G := G)) (connAt cov 1 (ContinuousLinearMap.id ℝ (Rn n))) ↔
      ((∀ u v : GroupLieAlgebra 𝓘(ℝ, Rn n) G, covF cov (liv u) (liv v) 1 - covF cov (liv v) (liv u) 1 = ⁅u, v⁆) ∧
       (∀ u v w : GroupLieAlgebra 𝓘(ℝ, Rn n) G,
          ip (covF cov (liv w) (liv u) 1) v + ip u (covF cov (liv w) (liv v) 1) = 0)) :=
  ⟨fun h => ⟨h.torsion_free, fun u v w => h.metric w u v⟩, fun h => ⟨h.1, fun X Y Z => h.2 Y Z X⟩⟩

/-- `B`'s conjunct (6) is the project's `IsAdInvariant` of the metric at `1`, hence (by `A`) Mathlib's
`lieInvariant`. -/
theorem B6_iff_lieInvariant (hA : A) :
    (∀ u v w : GroupLieAlgebra 𝓘(ℝ, Rn n) G, ip ⁅u, v⁆ w = ip u ⁅v, w⁆) ↔
      (ipForm (n := n) (G := G)).lieInvariant (GroupLieAlgebra 𝓘(ℝ, Rn n) G) :=
  (Iff.rfl : _ ↔ Morse.IsAdInvariant (ipForm (n := n) (G := G))).trans (hA _)

/-- What `B` adds to `(1), (2), (4)` (all proved above): for every group and Levi-Civita connection,
`B` is equivalent to (3) ∧ (5) ∧ (6) — left-invariance of `X_u ⊢ X_v`, metric compatibility on `𝔤`, and
21.3(a). -/
theorem B_iff_geometric_core :
    B ↔ ∀ (n : ℕ) (G : Type) [Group G] [TopologicalSpace G] [T2Space G] [ChartedSpace (Rn n) G]
      [LieGroup 𝓘(ℝ, Rn n) ∞ G] [Bundle.RiemannianBundle (fun x : G => TangentSpace 𝓘(ℝ, Rn n) x)]
      [IsContMDiffRiemannianBundle 𝓘(ℝ, Rn n) ∞ (Rn n) (fun x : G => TangentSpace 𝓘(ℝ, Rn n) x)],
      BiInvMetric n G → ∀ cov : Conn n G, IsLC cov →
        (∀ u v : GroupLieAlgebra 𝓘(ℝ, Rn n) G, covF cov (liv u) (liv v) = liv (covF cov (liv u) (liv v) 1)) ∧
        (∀ u v w : GroupLieAlgebra 𝓘(ℝ, Rn n) G,
          ip (covF cov (liv w) (liv u) 1) v + ip u (covF cov (liv w) (liv v) 1) = 0) ∧
        Morse.IsAdInvariant (ipForm (n := n) (G := G)) := by
  constructor
  · intro hB n G _ _ _ _ _ _ _ hbi cov hLC
    obtain ⟨_, _, h3, _, h5, h6⟩ := hB n G hbi cov hLC
    exact ⟨h3, h5, h6⟩
  · intro h n G _ _ _ _ _ _ _ hbi cov hLC
    obtain ⟨h3, h5, h6⟩ := h n G hbi cov hLC
    exact ⟨B1_holds, B2_holds hbi, h3, B4_holds cov hLC, h5, h6⟩

#rt_check RoundTrip.V12_1.B_to_A [Morse.isAdInvariant_iff_lieInvariant]
#rt_overlap RoundTrip.V12_1.B_to_A [Morse.isAdInvariant_iff_lieInvariant]
#rt_check RoundTrip.V12_1.B6_iff_lieInvariant [Morse.isAdInvariant_iff_lieInvariant]
#rt_check RoundTrip.V12_1.B_iff_geometric_core [Morse.isAdInvariant_iff_lieInvariant]

end RoundTrip.V12_1
