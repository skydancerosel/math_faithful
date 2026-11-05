import Morse
/-! Blind formalization of VA_11 (Milnor Appendix, Case 2, pp. 152-153). Choices:
- Telescope vocabulary as in VA_2; Case-2 data is `Case2 f S T` (increasing `S`, `T`; `f` carries `X_i` into `Y_i`; `g_n` homotopy inverse of `f_n`; `H n` the homotopy `h^n_u` from `i_n g_n` to `g_{n+1} j_n`), `Gmap D` is Milnor's `G` (valued in `X × ℝ`).
- Claims: (a) `G` is a continuous map `Y_Σ → X_Σ`; (b) for each `n`, `G f_Σ` carries `X_Σ^n` into itself by a map homotopic to the identity of `X_Σ^n`; (c) hence (Case 1 on `{X_Σ^n}`, using VA.6) `G f_Σ` is a homotopy equivalence, and likewise `f_Σ G`; (d) `f_Σ` has a left and a right homotopy inverse and is a homotopy equivalence. (The "similarly" in (c) and (d) are taken as claims of Case 2, with the same `G`.)
-/
open scoped ContDiff Manifold unitInterval
open Topology Bundle
namespace RoundTrip.VA_11



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

section Case2
variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

/-- The data of Case 2 of Theorem A: `f : X → Y` carrying `X_i` into `Y_i` by a homotopy equivalence `f_i`, with homotopy
inverses `g_n` (so `g_n f_n ≃ id`, `f_n g_n ≃ id`) and homotopies `h^n_u` from `i_n g_n` to `g_{n+1} j_n`
(`i_n : X_n → X_{n+1}`, `j_n : Y_n → Y_{n+1}` the inclusions). -/
structure Case2 (f : C(X, Y)) (S : ℕ → Set X) (T : ℕ → Set Y) where
  hS : Monotone S
  hT : Monotone T
  hf : ∀ i, ∀ x ∈ S i, f x ∈ T i
  g : ∀ n, C(↥(T n), ↥(S n))
  hg₁ : ∀ n, ((g n).comp (resC f (hf n))).Homotopic (ContinuousMap.id _)
  hg₂ : ∀ n, ((resC f (hf n)).comp (g n)).Homotopic (ContinuousMap.id _)
  H : ∀ n, ContinuousMap.Homotopy ((inclC (hS (Nat.le_succ n))).comp (g n)) ((g (n + 1)).comp (inclC (hT (Nat.le_succ n))))

/-- Milnor's `G : Y_Σ → X_Σ`: `G(y, n + t) = (g_n(y), n + 2t)` for `t ≤ ½` and `(h^n_{2t-1}(y), n + 1)` for `t ≥ ½`
(`n = ⌊τ⌋`; values in `X × ℝ`). -/
noncomputable def Gmap {f : C(X, Y)} {S : ℕ → Set X} {T : ℕ → Set Y} (D : Case2 f S T) (z : ↥(tel T)) : X × ℝ :=
  if z.1.2 - ⌊z.1.2⌋₊ ≤ 1 / 2 then
    ((D.g ⌊z.1.2⌋₊ ⟨z.1.1, mem_floor D.hT z.2⟩ : ↥(S ⌊z.1.2⌋₊)).1, (⌊z.1.2⌋₊ : ℝ) + 2 * (z.1.2 - ⌊z.1.2⌋₊))
  else
    ((D.H ⌊z.1.2⌋₊ (Set.projIcc (0 : ℝ) 1 zero_le_one (2 * (z.1.2 - ⌊z.1.2⌋₊) - 1), ⟨z.1.1, mem_floor D.hT z.2⟩) :
      ↥(S (⌊z.1.2⌋₊ + 1))).1, (⌊z.1.2⌋₊ : ℝ) + 1)
end Case2


/-- Milnor's claim. -/
def B : Prop :=
  ∀ (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y)) (S : ℕ → Set X) (T : ℕ → Set Y)
    (D : Case2 f S T),
    ∃ Gc : C(↥(tel T), ↥(tel S)), (∀ z, (Gc z).1 = Gmap D z) ∧
      (∀ n : ℕ, ∃ hn : C(↥(truncSub S n), ↥(truncSub S n)),
        (∀ z, ((hn z).1 : ↥(tel S)) = Gc (fSig f D.hf z.1)) ∧ hn.Homotopic (ContinuousMap.id _)) ∧
      IsHE (Gc.comp (fSig f D.hf)) ∧ IsHE ((fSig f D.hf).comp Gc) ∧
      (∃ L R : C(↥(tel T), ↥(tel S)), (L.comp (fSig f D.hf)).Homotopic (ContinuousMap.id _) ∧
        ((fSig f D.hf).comp R).Homotopic (ContinuousMap.id _)) ∧
      IsHE (fSig f D.hf)

end RoundTrip.VA_11
