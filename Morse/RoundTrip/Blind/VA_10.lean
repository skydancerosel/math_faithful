import Morse
/-! Blind formalization of VA_10 (Milnor Appendix, Case 1, pp. 150-152). Choices:
- Telescope vocabulary as in VA_2; `S` increasing. Case 1: `Y_i = X_i`, `f : X → X` carrying each `X_i` into itself (`hf`) with `f_i ≃ id` via homotopies `h^n_u` (`H n : Homotopy (f_n) (id)`, `h^n_0 = f_n`, `h^n_1 = id`).
- Milnor's homotopy `h_u : X_Σ → X_Σ` (`hmapSig`, with `n = ⌊τ⌋`, `t = τ − n`): `(h^n_u(x), n+2t)` for `t ≤ ½`; `(h^n_{(3−4t)u}(x), n+1)` for `½ ≤ t ≤ ¾`; `(h^{n+1}_{(4t−3)u}(x), n+1)` for `¾ ≤ t ≤ 1`.
- MISPRINT: Milnor's text has `(4 − 3t)u` in the last piece; with it the homotopy is discontinuous at `t = ¾` (value `1.75u` vs `0`), and `u = 0` would not give `f`. I formalize the corrected `(4t − 3)u` (equal to `0` at `t = ¾`, `u` at `t = 1`, matching the next piece), as the item title indicates. So the literal printed formula would make `B` false.
- Claims: (a) `f_Σ` is a homotopy equivalence (Case 1); (b) `h_u` is a continuous homotopy `X_Σ → X_Σ` (a `ContinuousMap.Homotopy` `K` between `K 0` and `K 1`, with `K(u,·) = h_u` on underlying points); (c) `h_0 = K 0` is homotopic to `f_Σ`; (d) `h_1 = K 1` has the properties of VA.9 (`IsH1`).
-/
open scoped ContDiff Manifold unitInterval
open Topology Bundle
namespace RoundTrip.VA_10



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

/-- The properties of Milnor's `h₁ : X_Σ → X_Σ` (Appendix p. 151): `h₁(x, n+t) = (x, n+2t)` for `0 ≤ t ≤ ½`, and
`h₁(x, n+t) ∈ X_{n+1} × [n+1]` for `½ ≤ t ≤ 1`. -/
def IsH1 {X : Type} [TopologicalSpace X] (S : ℕ → Set X) (h₁ : C(↥(tel S), ↥(tel S))) : Prop :=
  (∀ (z : ↥(tel S)) (n : ℕ) (t : ℝ), 0 ≤ t → t ≤ 1 / 2 → z.1.2 = n + t → (h₁ z).1 = (z.1.1, (n : ℝ) + 2 * t)) ∧
  (∀ (z : ↥(tel S)) (n : ℕ) (t : ℝ), 1 / 2 ≤ t → t ≤ 1 → z.1.2 = n + t →
    (h₁ z).1.1 ∈ S (n + 1) ∧ (h₁ z).1.2 = (n : ℝ) + 1)


section Case1
variable {X : Type} [TopologicalSpace X]

/-- Milnor's `h_u` in Case 1, valued in `X × ℝ` (corrected last piece `(4t−3)u`). -/
noncomputable def hmapSig {S : ℕ → Set X} (hS : Monotone S) (f : C(X, X)) (hf : ∀ i, ∀ x ∈ S i, f x ∈ S i)
    (H : ∀ n, ContinuousMap.Homotopy (resC f (hf n)) (ContinuousMap.id ↥(S n))) (u : unitInterval) (z : ↥(tel S)) :
    X × ℝ :=
  if z.1.2 - ⌊z.1.2⌋₊ ≤ 1 / 2 then
    ((H ⌊z.1.2⌋₊ (u, ⟨z.1.1, mem_floor hS z.2⟩) : ↥(S ⌊z.1.2⌋₊)).1, (⌊z.1.2⌋₊ : ℝ) + 2 * (z.1.2 - ⌊z.1.2⌋₊))
  else if z.1.2 - ⌊z.1.2⌋₊ ≤ 3 / 4 then
    ((H ⌊z.1.2⌋₊ (Set.projIcc (0 : ℝ) 1 zero_le_one ((3 - 4 * (z.1.2 - ⌊z.1.2⌋₊)) * u), ⟨z.1.1, mem_floor hS z.2⟩) :
      ↥(S ⌊z.1.2⌋₊)).1, (⌊z.1.2⌋₊ : ℝ) + 1)
  else
    ((H (⌊z.1.2⌋₊ + 1) (Set.projIcc (0 : ℝ) 1 zero_le_one ((4 * (z.1.2 - ⌊z.1.2⌋₊) - 3) * u),
      ⟨z.1.1, hS (Nat.le_succ _) (mem_floor hS z.2)⟩) : ↥(S (⌊z.1.2⌋₊ + 1))).1, (⌊z.1.2⌋₊ : ℝ) + 1)
end Case1

/-- Milnor's claim. -/
def B : Prop :=
  ∀ (X : Type) [TopologicalSpace X] (S : ℕ → Set X) (hS : Monotone S) (f : C(X, X)) (hf : ∀ i, ∀ x ∈ S i, f x ∈ S i)
    (H : ∀ n, ContinuousMap.Homotopy (resC f (hf n)) (ContinuousMap.id ↥(S n))),
    IsHE (fSig f hf) ∧
    ∃ (k₀ k₁ : C(↥(tel S), ↥(tel S))) (K : ContinuousMap.Homotopy k₀ k₁),
      (∀ (u : unitInterval) (z : ↥(tel S)), (K (u, z)).1 = hmapSig hS f hf H u z) ∧
      k₀.Homotopic (fSig f hf) ∧ IsH1 S k₁

end RoundTrip.VA_10
