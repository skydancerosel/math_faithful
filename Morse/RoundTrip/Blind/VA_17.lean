import Morse
/-! Blind formalization of VA_17 (Milnor Appendix, Corollary p. 153). Choices:
- Telescope vocabulary as in VA_2. "Has the homotopy type of a CW-complex" = `HasCWType`: homotopy equivalent (`ContinuousMap.HomotopyEquiv`) to some Hausdorff space `Y : Type` carrying a Mathlib `CWComplex (Set.univ : Set Y)` structure (each `X_i` as a subspace `↥(S i)`).
- Claim: if `X` is the homotopy direct limit of `{X_i}` and every `X_i` has the homotopy type of a CW complex then so does `X`.
-/
open scoped ContDiff Manifold unitInterval
open Topology Bundle
namespace RoundTrip.VA_17



section Tele
variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

/-- The telescope `X_Σ = X₀×[0,1] ∪ X₁×[1,2] ∪ ⋯ ⊆ X × ℝ` (as a subset of `X × ℝ`; the type `↥(tel S)` carries the subspace topology). -/
def tel (S : ℕ → Set X) : Set (X × ℝ) := {z | ∃ i : ℕ, z.1 ∈ S i ∧ (i : ℝ) ≤ z.2 ∧ z.2 ≤ i + 1}

/-- The projection `p : X_Σ → X`, `p(x, τ) = x`. -/
def telProj (S : ℕ → Set X) : C(↥(tel S), X) :=
  ⟨fun z => z.1.1, continuous_fst.comp continuous_subtype_val⟩

/-- `f` is a homotopy equivalence: it has a continuous homotopy inverse. -/
def IsHE {A B : Type} [TopologicalSpace A] [TopologicalSpace B] (f : C(A, B)) : Prop :=
  ∃ g : C(B, A), (f.comp g).Homotopic (ContinuousMap.id B) ∧ (g.comp f).Homotopic (ContinuousMap.id A)

/-- `X` is the homotopy direct limit of the increasing sequence `S₀ ⊆ S₁ ⊆ ⋯` of subspaces:
the projection `p : X_Σ → X` is a homotopy equivalence. -/
def IsHDL (S : ℕ → Set X) : Prop := Monotone S ∧ IsHE (telProj S)

/-- `f` maps `A` into `B`; the restriction `A → B`. -/
def resC (f : C(X, Y)) {A : Set X} {B : Set Y} (h : ∀ x ∈ A, f x ∈ B) : C(↥A, ↥B) :=
  ⟨fun x => ⟨f x, h x x.2⟩, (f.continuous.comp continuous_subtype_val).subtype_mk _⟩

/-- Inclusion of subspaces. -/
def inclC {A B : Set X} (h : A ⊆ B) : C(↥A, ↥B) := ⟨Set.inclusion h, continuous_inclusion h⟩

theorem fSig_mem (f : C(X, Y)) {S : ℕ → Set X} {T : ℕ → Set Y} (h : ∀ i, ∀ x ∈ S i, f x ∈ T i)
    (z : ↥(tel S)) : (f z.1.1, z.1.2) ∈ tel T := by
  obtain ⟨i, hi, h1, h2⟩ := z.2
  exact ⟨i, h i _ hi, h1, h2⟩

/-- `f_Σ : X_Σ → Y_Σ`, `f_Σ(x, t) = (f x, t)`, for `f` carrying each `X_i` into `Y_i`. -/
def fSig (f : C(X, Y)) {S : ℕ → Set X} {T : ℕ → Set Y} (h : ∀ i, ∀ x ∈ S i, f x ∈ T i) :
    C(↥(tel S), ↥(tel T)) :=
  ⟨fun z => ⟨(f z.1.1, z.1.2), fSig_mem f h z⟩,
    ((f.continuous.comp (continuous_fst.comp continuous_subtype_val)).prodMk
      (continuous_snd.comp continuous_subtype_val)).subtype_mk _⟩

/-- The truncation `X_Σ^n = {(x, τ) ∈ X_Σ | τ ≤ n}` as a subset of `X × ℝ`. -/
def truncSet (S : ℕ → Set X) (n : ℕ) : Set (X × ℝ) := {z | z ∈ tel S ∧ z.2 ≤ n}

/-- The truncation `X_Σ^n` as a subset of the space `X_Σ`. -/
def truncSub (S : ℕ → Set X) (n : ℕ) : Set ↥(tel S) := {z | z.1.2 ≤ n}

/-- Deformation retract (strong: the homotopy fixes `A` pointwise) of `A` in `X'`, inside an ambient space `Y'`. -/
def IsDefRetract {Y' : Type} [TopologicalSpace Y'] (X' A : Set Y') : Prop :=
  A ⊆ X' ∧ ∃ H : unitInterval → Y' → Y', ContinuousOn (fun z : unitInterval × Y' => H z.1 z.2) (Set.univ ×ˢ X') ∧
    (∀ x ∈ X', H 0 x = x) ∧ (∀ x ∈ X', H 1 x ∈ A) ∧ (∀ x ∈ X', ∀ s, H s x ∈ X') ∧ ∀ a ∈ A, ∀ s, H s a = a

omit [TopologicalSpace X] in
/-- A point `(x, τ)` of `X_Σ` has `x ∈ X_{⌊τ⌋}`. -/
theorem mem_floor {S : ℕ → Set X} (hS : Monotone S) {z : X × ℝ} (hz : z ∈ tel S) : z.1 ∈ S ⌊z.2⌋₊ := by
  obtain ⟨i, hi, h1, h2⟩ := hz
  exact hS (Nat.le_floor h1) hi

/-- Has the homotopy type of a CW complex (Mathlib `CWComplex`, Hausdorff `Y`). -/
def HasCWType (A : Type) [TopologicalSpace A] : Prop :=
  ∃ (Y : Type) (_ : TopologicalSpace Y) (_ : T2Space Y) (_ : CWComplex (Set.univ : Set Y)),
    Nonempty (ContinuousMap.HomotopyEquiv A Y)
end Tele


/-- Milnor's claim. -/
def B : Prop :=
  ∀ (X : Type) [TopologicalSpace X] (S : ℕ → Set X), IsHDL S → (∀ i, HasCWType ↥(S i)) → HasCWType X

end RoundTrip.VA_17
