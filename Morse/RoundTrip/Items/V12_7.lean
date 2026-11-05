import Morse
import RoundTrip.Check
import RoundTrip.Blind.V12_7

/-!
# V12_7 (Milnor §21, footnote p. 114): Cartan's 3-form

`A` (universe `0`): `Morse.cartan_form_swap₁₂ ∧ Morse.cartan_form_swap₂₃` — for an arbitrary real Lie
algebra `L` and bilinear form `B`: `B ⁅Y,X⁆ Z = −B ⁅X,Y⁆ Z`, and, if `B` is ad-invariant,
`B ⁅X,Z⁆ Y = −B ⁅X,Y⁆ Z`.  Pure algebra (skew-symmetry of `⟨[X,Y],Z⟩` under two transpositions).

`B` (blind): (A) for a Lie group with a bi-invariant metric, (i) `⟨[X,Y],Z⟩` on left-invariant fields changes
sign under each of the three transpositions (at every point), (ii) there is a smooth left-invariant
alternating 3-form on `G` restricting to `⟨[X,Y],Z⟩` on `𝔤`; (B) Cartan's theorem: `H₃(G; ℝ) ≠ 0` (Mathlib
singular homology) for every compact connected non-abelian Lie group.

* `B → A`: vacuous (A re-proved outright).
* `A → B` fails genuinely: (B) (Cartan's `H³(G) ≠ 0`) is far beyond the project, which has no cohomology of
  Lie groups and no de Rham theory; (A)(ii) (constructing the left-invariant form, its smoothness via the
  left trivialization of `TG`) is not in the project either; (A)(i) needs 21.3(a) on the group (V12_3).
* **Bridge** (`Bi_of_A`, uses `A`): with ad-invariance of the metric at `1` (B of V12_1 (6)) and left
  invariance, `A` applied to `𝔤 = GroupLieAlgebra` with the metric at `1` gives (A)(i) at every point (the
  third transposition is a composite of `A`'s two).
-/

open scoped ContDiff Manifold
open Bundle

set_option linter.unusedSectionVars false

namespace RoundTrip.V12_7

/-- The project's statement (universe `0`). -/
def A : Prop := type_of% @Morse.cartan_form_swap₁₂.{0} ∧ type_of% @Morse.cartan_form_swap₂₃.{0}

theorem A_holds : A := ⟨@Morse.cartan_form_swap₁₂.{0}, @Morse.cartan_form_swap₂₃.{0}⟩

/-- Vacuous: `A` re-proved outright, `B` is not used. -/
theorem B_to_A : B → A := by
  intro _
  refine ⟨fun {L} _ _ {Bf} X Y Z => ?_, fun {L} _ _ {Bf} hB X Y Z => ?_⟩
  · rw [← lie_skew, map_neg, LinearMap.neg_apply]
  · rw [hB, hB, ← lie_skew, map_neg]

/-! ## Dictionary: the group `G` and its Lie algebra `𝔤 = GroupLieAlgebra` -/

namespace Dict

variable {n : ℕ} {G : Type} [Group G] [TopologicalSpace G] [ChartedSpace (Rn n) G]

/-- Mathlib: `[X_u, X_v] = X_{⁅u,v⁆}`. -/
theorem liv_bracket [LieGroup 𝓘(ℝ, Rn n) ∞ G] (u v : GroupLieAlgebra 𝓘(ℝ, Rn n) G) :
    VectorField.mlieBracket 𝓘(ℝ, Rn n) (liv u) (liv v) = liv ⁅u, v⁆ :=
  (mulInvariantVector_mlieBracket u v).symm

variable [Bundle.RiemannianBundle (fun x : G => TangentSpace 𝓘(ℝ, Rn n) x)]

/-- `⟨X_u, X_v⟩` is the constant `⟨u, v⟩` (left invariance of the metric). -/
theorem inner_liv (hL : LeftInvMetric n G) (u v : GroupLieAlgebra 𝓘(ℝ, Rn n) G) (p : G) :
    inner ℝ (liv u p) (liv v p) = ip u v := by
  have key : ∀ q : G, p * 1 = q → ∀ x y : Rn n,
      @inner ℝ (TangentSpace 𝓘(ℝ, Rn n) q) _ x y = @inner ℝ (TangentSpace 𝓘(ℝ, Rn n) (p * 1)) _ x y := by
    rintro q rfl x y; rfl
  exact (key p (mul_one p) _ _).trans (hL p 1 u v)

/-- `⟨ , ⟩` on `𝔤 = T_1G` as a Mathlib bilinear form. -/
noncomputable def ipForm : LinearMap.BilinForm ℝ (GroupLieAlgebra 𝓘(ℝ, Rn n) G) :=
  LinearMap.mk₂ ℝ ip
    (fun a b c => inner_add_left (𝕜 := ℝ) (E := TangentSpace 𝓘(ℝ, Rn n) (1 : G)) a b c)
    (fun r a b => real_inner_smul_left (F := TangentSpace 𝓘(ℝ, Rn n) (1 : G)) a b r)
    (fun a b c => inner_add_right (𝕜 := ℝ) (E := TangentSpace 𝓘(ℝ, Rn n) (1 : G)) a b c)
    (fun r a b => real_inner_smul_right (F := TangentSpace 𝓘(ℝ, Rn n) (1 : G)) a b r)

theorem ipForm_apply (u v : GroupLieAlgebra 𝓘(ℝ, Rn n) G) : ipForm u v = ip u v := rfl

end Dict

open Dict

/-- **Bridge** (uses `A`): for a left-invariant metric whose restriction to `𝔤` is ad-invariant (21.3(a),
B of V12_1 (6)), `B`'s (A)(i) holds at every point. -/
theorem Bi_of_A (hA : A) {n : ℕ} {G : Type} [Group G] [TopologicalSpace G] [ChartedSpace (Rn n) G]
    [LieGroup 𝓘(ℝ, Rn n) ∞ G] [Bundle.RiemannianBundle (fun x : G => TangentSpace 𝓘(ℝ, Rn n) x)]
    (hL : LeftInvMetric n G) (hadj : ∀ a b c : GroupLieAlgebra 𝓘(ℝ, Rn n) G, ip ⁅a, b⁆ c = ip a ⁅b, c⁆)
    (u v w : GroupLieAlgebra 𝓘(ℝ, Rn n) G) (p : G) :
    inner ℝ (VectorField.mlieBracket 𝓘(ℝ, Rn n) (liv u) (liv v) p) (liv w p) = - inner ℝ (VectorField.mlieBracket 𝓘(ℝ, Rn n) (liv v) (liv u) p) (liv w p) ∧
    inner ℝ (VectorField.mlieBracket 𝓘(ℝ, Rn n) (liv u) (liv v) p) (liv w p) = - inner ℝ (VectorField.mlieBracket 𝓘(ℝ, Rn n) (liv u) (liv w) p) (liv v p) ∧
    inner ℝ (VectorField.mlieBracket 𝓘(ℝ, Rn n) (liv u) (liv v) p) (liv w p) = - inner ℝ (VectorField.mlieBracket 𝓘(ℝ, Rn n) (liv w) (liv v) p) (liv u p) := by
  obtain ⟨hA1, hA2⟩ := hA
  simp only [liv_bracket, inner_liv hL]
  have s12 : ∀ X Y Z : GroupLieAlgebra 𝓘(ℝ, Rn n) G, ip ⁅Y, X⁆ Z = - ip ⁅X, Y⁆ Z :=
    fun X Y Z => @hA1 (GroupLieAlgebra 𝓘(ℝ, Rn n) G) _ _ ipForm X Y Z
  have s23 : ∀ X Y Z : GroupLieAlgebra 𝓘(ℝ, Rn n) G, ip ⁅X, Z⁆ Y = - ip ⁅X, Y⁆ Z :=
    fun X Y Z => @hA2 (GroupLieAlgebra 𝓘(ℝ, Rn n) G) _ _ ipForm hadj X Y Z
  refine ⟨s12 v u w, ?_, ?_⟩
  · have := s23 u v w; linarith
  · have h1 := s12 v w u
    have h2 := s23 v u w
    have h3 := s12 u v w
    linarith

#rt_check RoundTrip.V12_7.B_to_A [Morse.cartan_form_swap₁₂, Morse.cartan_form_swap₂₃]
#rt_overlap RoundTrip.V12_7.B_to_A [Morse.cartan_form_swap₁₂, Morse.cartan_form_swap₂₃]
#rt_check RoundTrip.V12_7.Bi_of_A [Morse.cartan_form_swap₁₂, Morse.cartan_form_swap₂₃]

end RoundTrip.V12_7
