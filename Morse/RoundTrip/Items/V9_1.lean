import Morse
import RoundTrip.Check
import RoundTrip.Blind.V9_1

open Set Filter Topology
open scoped ContDiff Manifold

namespace RoundTrip.V9_1

/-- The project's statement (universes instantiated at 0): pure linear ODE theory on a Banach space
`E`, for `x' = A(t)x` with `A : ℝ → E →L[ℝ] E`: (1) global existence on `ℝ` through any initial
value for continuous `A`; (2) for continuous `A`, a function continuous on `[a, b]` (`a < b`)
solving the equation on `(a, b)` agrees on `[a, b]` with the propagator `linSol A s (f s)` (the
global solution with value `f s` at `s`; `linSol` is a definition, by choice) for any `s ∈ [a, b]`
— uniqueness by the value at any point; (3) a solution on `[a, b]` with `A` smooth on `[a, b]` is
smooth on `[a, b]`. Nothing about Jacobi fields, curvature or manifolds. -/
def A : Prop :=
  type_of% @Morse.exists_linearODE.{0} ∧ type_of% @Morse.eqOn_Icc_linSol.{0} ∧
    type_of% @Morse.contDiffOn_Icc_of_hasDerivAt.{0}

theorem A_holds : A :=
  ⟨@Morse.exists_linearODE, @Morse.eqOn_Icc_linSol, @Morse.contDiffOn_Icc_of_hasDerivAt⟩

/-! ### B ⇒ A: only vacuously

A is proved outright by re-running the project's proofs (truncated Picard–Lindelöf on intervals
`Morse.exists_linearODE_Ioo` — a project theorem outside the item — glued by uniqueness; the
propagator's properties re-derived from that existence proof, since the project's `linSol_spec`
uses the banned `exists_linearODE`; the bootstrap for smoothness). B (about Jacobi fields on
abstract manifolds) is not used and could not be. -/

namespace Aux

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem exists_linearODE' [CompleteSpace E] {A : ℝ → E →L[ℝ] E} (hA : Continuous A) (t₀ : ℝ)
    (x₀ : E) : ∃ α : ℝ → E, α t₀ = x₀ ∧ ∀ t, HasDerivAt α (A t (α t)) t := by
  choose β hβ0 hβ using fun a : {a : ℝ // 0 < a} => Morse.exists_linearODE_Ioo hA t₀ x₀ a.2
  have key : ∀ (a b : {a : ℝ // 0 < a}) (t : ℝ), |t - t₀| < a → |t - t₀| < b →
      β a t = β b t := by
    intro a b t ha hb
    have hmin1 := min_le_left a.1 b.1
    have hmin2 := min_le_right a.1 b.1
    refine Morse.linearODE_eqOn hA (a := t₀ - min a.1 b.1) (b := t₀ + min a.1 b.1) (t₀ := t₀)
      ⟨by linarith [lt_min a.2 b.2], by linarith [lt_min a.2 b.2]⟩
      (fun s hs => hβ a s ⟨by linarith [hs.1], by linarith [hs.2]⟩)
      (fun s hs => hβ b s ⟨by linarith [hs.1], by linarith [hs.2]⟩) (by rw [hβ0, hβ0]) ?_
    have hlt : |t - t₀| < min a.1 b.1 := lt_min ha hb
    rw [abs_lt] at hlt
    exact ⟨by linarith [hlt.1], by linarith [hlt.2]⟩
  refine ⟨fun t => β ⟨|t - t₀| + 1, by positivity⟩ t, hβ0 _, fun t => ?_⟩
  have ht : t ∈ Ioo (t₀ - (|t - t₀| + 1)) (t₀ + (|t - t₀| + 1)) := by
    constructor <;> linarith [neg_abs_le (t - t₀), le_abs_self (t - t₀)]
  refine (hβ _ t ht).congr_of_eventuallyEq ?_
  filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
  refine key _ _ s (lt_add_one _) ?_
  rw [abs_lt]
  exact ⟨by linarith [hs.1], by linarith [hs.2]⟩

section Propagator
variable [CompleteSpace E] {A : ℝ → E →L[ℝ] E}

theorem linSol_spec' (hA : Continuous A) (s : ℝ) (ξ : E) :
    Morse.linSol A s ξ s = ξ ∧
      ∀ t, HasDerivAt (Morse.linSol A s ξ) (A t (Morse.linSol A s ξ t)) t := by
  have h := exists_linearODE' hA s ξ
  rw [Morse.linSol, dif_pos h]
  exact h.choose_spec

theorem eq_linSol' (hA : Continuous A) {α : ℝ → E} (hα : ∀ t, HasDerivAt α (A t (α t)) t)
    (s : ℝ) : α = Morse.linSol A s (α s) :=
  Morse.linearODE_eq hA hα (linSol_spec' hA s _).2 (linSol_spec' hA s _).1.symm

theorem continuous_linSol' (hA : Continuous A) (s : ℝ) (ξ : E) :
    Continuous (Morse.linSol A s ξ) :=
  continuous_iff_continuousAt.2 fun t => ((linSol_spec' hA s ξ).2 t).continuousAt

theorem eqOn_Icc_linSol' (hA : Continuous A) {f : ℝ → E} {a b : ℝ} (hab : a < b)
    (hf : ContinuousOn f (Icc a b)) (hd : ∀ t ∈ Ioo a b, HasDerivAt f (A t (f t)) t) {s : ℝ}
    (hs : s ∈ Icc a b) : EqOn f (Morse.linSol A s (f s)) (Icc a b) := by
  set m := (a + b) / 2
  have hm : m ∈ Ioo a b := ⟨by simp only [m]; linarith, by simp only [m]; linarith⟩
  set g := Morse.linSol A m (f m)
  have h1 : EqOn f g (Ioo a b) := Morse.linearODE_eqOn hA hm hd
    (fun t _ => (linSol_spec' hA m _).2 t) (linSol_spec' hA m _).1.symm
  have h2 : EqOn f g (Icc a b) := by
    have hcl : Icc a b ⊆ closure (Ioo a b) := by rw [closure_Ioo hab.ne]
    exact h1.of_subset_closure hf (continuous_linSol' hA m _).continuousOn Ioo_subset_Icc_self hcl
  have h3 : g = Morse.linSol A s (f s) := by
    have h4 : g s = f s := (h2 hs).symm
    have := eq_linSol' hA (linSol_spec' hA m (f m)).2 s
    change g = Morse.linSol A s (g s) at this
    rw [h4] at this
    exact this
  rw [← h3]
  exact h2

end Propagator

theorem contDiffOn_Icc_of_hasDerivAt' {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {A : ℝ → E →L[ℝ] E} {f : ℝ → E} {a b : ℝ} (hab : a < b)
    (hA : ContDiffOn ℝ ∞ A (Icc a b)) (hf : ∀ t ∈ Icc a b, HasDerivAt f (A t (f t)) t) :
    ContDiffOn ℝ ∞ f (Icc a b) := by
  have hu := uniqueDiffOn_Icc hab
  have key : ∀ n : ℕ, ContDiffOn ℝ n f (Icc a b) := by
    intro n
    induction n with
    | zero =>
      simp only [Nat.cast_zero, contDiffOn_zero]
      exact fun t ht => (hf t ht).continuousAt.continuousWithinAt
    | succ n ih =>
      push_cast
      refine (contDiffOn_succ_iff_derivWithin hu).2 ⟨fun t ht =>
        (hf t ht).differentiableAt.differentiableWithinAt, by simp, ?_⟩
      have h1 : ContDiffOn ℝ n (fun t => A t (f t)) (Icc a b) :=
        (hA.of_le (by exact_mod_cast le_top)).clm_apply ih
      exact h1.congr fun t ht => ((hf t ht).hasDerivWithinAt.derivWithin (hu t ht))
  exact contDiffOn_infty.2 fun n => key n

end Aux

/-- Vacuous: A is proved outright; B is not used. -/
theorem B_to_A : B → A := fun _ =>
  ⟨@Aux.exists_linearODE', @Aux.eqOn_Icc_linSol', @Aux.contDiffOn_Icc_of_hasDerivAt'⟩

#rt_check RoundTrip.V9_1.B_to_A [Morse.exists_linearODE, Morse.eqOn_Icc_linSol, Morse.contDiffOn_Icc_of_hasDerivAt]
#rt_overlap RoundTrip.V9_1.B_to_A [Morse.exists_linearODE, Morse.eqOn_Icc_linSol, Morse.contDiffOn_Icc_of_hasDerivAt]

/-! A ⇒ B is not proved; see `V9_1.json`. -/

end RoundTrip.V9_1
