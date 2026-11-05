import Morse
/-! Blind formalization of V3_41 (Milnor §4, p. 26: `ℂPⁿ` and Milnor's coordinates on `U_0`). Choices:
- No earlier blind file models `ℂPⁿ`; built from Milnor's definition: `Sph n` = unit vectors `Σ |z_j|² = 1` of `ℂ^{n+1}`
  (subspace of `Fin (n+1) → ℂ`), `CPn n` = its quotient by `z ∼ λz`, `|λ| = 1` (the equivalence Milnor's "equivalence
  classes" refers to), with the quotient topology. `cls z` = Milnor's `(z_0 : … : z_n)`.
- `U k` = classes with `z_k ≠ 0`. Milnor's coordinates on `U_k`: `x_j + i y_j = |z_k| z_j / z_k` for `j ≠ k`, the
  indices `j ≠ k` enumerated increasingly by `k.succAbove : Fin n → Fin (n+1)` (for `k = 0`: `j = 1, …, n`, Milnor's
  `x_1, y_1, …, x_n, y_n`). `ℝ^{2n}` = `EuclideanSpace ℝ (Fin n × Fin 2)`, coordinate `(j,0)` = `x`, `(j,1)` = `y`
  (Euclidean norm `Σ x_j² + y_j²`, so "open unit ball" = `Metric.ball 0 1`). The formula is well defined on classes
  (`ccoord_smul`); off `U k` it has the junk value given by `x/0 = 0`, irrelevant since only `U k` is used.
- "Diffeomorphically": `CPn n` has no smooth structure in Mathlib and Milnor does not give one beyond these coordinates.
  `IsMilnorChart k`: in a given smooth structure on `CPn n` (compatible with its quotient topology, modelled on `ℝ^{2n}`),
  the coordinate map of `U k` is a diffeomorphism of the open set `U k` onto the open unit ball (Mathlib
  `PartialDiffeomorph` with source `U k`, target the ball, agreeing with the coordinates on `U k`).
- B ("the required coordinate functions"): there is a smooth (`C^∞`) manifold structure on `ℂPⁿ` in which the coordinates
  of `U_0`, and likewise (Milnor's "similarly", p. 27) those of every `U_k`, are diffeomorphisms onto the open unit ball.
  All `k` are included because `U_0` alone does not cover `ℂPⁿ` and the later items use all `U_k`; the quoted case is `k = 0`.
  `n = 0` allowed (`ℂP⁰` a point, `ℝ⁰`). -/
open scoped ContDiff Manifold
namespace RoundTrip.V3_41

/-- Unit vectors of `ℂ^{n+1}`: `Σ |z_j|² = 1`. -/
abbrev Sph (n : ℕ) : Type := {z : Fin (n + 1) → ℂ // ∑ j, ‖z j‖ ^ 2 = 1}

/-- `z ∼ w` iff `w = λ z` with `|λ| = 1`. -/
def Rel (n : ℕ) (z w : Sph n) : Prop := ∃ c : ℂ, ‖c‖ = 1 ∧ w.1 = c • z.1

/-- `ℂPⁿ`: equivalence classes of unit vectors of `ℂ^{n+1}`, with the quotient topology. -/
def CPn (n : ℕ) : Type := Quot (Rel n)

instance (n : ℕ) : TopologicalSpace (CPn n) := inferInstanceAs (TopologicalSpace (Quot (Rel n)))

/-- The class `(z_0 : … : z_n)`. -/
def cls {n : ℕ} (z : Sph n) : CPn n := Quot.mk _ z

/-- `U_k`: classes with `z_k ≠ 0`. -/
def U {n : ℕ} (k : Fin (n + 1)) : Set (CPn n) := cls '' {z | z.1 k ≠ 0}

/-- The model `ℝ^{2n}`, coordinates `(j, 0) = x_j`, `(j, 1) = y_j`. -/
abbrev Model (n : ℕ) : Type := EuclideanSpace ℝ (Fin n × Fin 2)

/-- Milnor's complex coordinates `|z_k| z_j / z_k` (`j ≠ k`, enumerated by `k.succAbove`). -/
noncomputable def ccoord {n : ℕ} (k : Fin (n + 1)) (z : Fin (n + 1) → ℂ) (j : Fin n) : ℂ :=
  (‖z k‖ : ℂ) * z (k.succAbove j) / z k

theorem ccoord_smul {n : ℕ} (k : Fin (n + 1)) (z : Fin (n + 1) → ℂ) (c : ℂ) (hc : ‖c‖ = 1) :
    ccoord k (c • z) = ccoord k z := by
  funext j
  have hc0 : c ≠ 0 := by rintro rfl; simp at hc
  simp only [ccoord, Pi.smul_apply, smul_eq_mul, norm_mul, hc, one_mul]
  by_cases hz : z k = 0
  · simp [hz]
  · field_simp

/-- Milnor's real coordinates `(x_j, y_j)` on representatives. -/
noncomputable def phiS {n : ℕ} (k : Fin (n + 1)) (z : Sph n) : Model n :=
  WithLp.toLp 2 (fun p : Fin n × Fin 2 => if p.2 = 0 then (ccoord k z.1 p.1).re else (ccoord k z.1 p.1).im)

/-- Milnor's coordinates `x_1, y_1, …, x_n, y_n` of `U_k`, as a map on `ℂPⁿ` (well defined on classes). -/
noncomputable def phi {n : ℕ} (k : Fin (n + 1)) : CPn n → Model n :=
  Quot.lift (phiS k) (by
    rintro z w ⟨c, hc, hw⟩
    simp only [phiS, hw, ccoord_smul k z.1 c hc])

/-- In the smooth structure at hand, the coordinates of `U_k` map `U_k` diffeomorphically onto the open unit ball. -/
def IsMilnorChart (n : ℕ) [ChartedSpace (Model n) (CPn n)] (k : Fin (n + 1)) : Prop :=
  ∃ Φ : PartialDiffeomorph 𝓘(ℝ, Model n) 𝓘(ℝ, Model n) (CPn n) (Model n) ∞,
    Φ.source = U k ∧ Φ.target = Metric.ball (0 : Model n) 1 ∧ ∀ x ∈ U k, Φ x = phi k x

/-- `ℂPⁿ` is a smooth `2n`-manifold in which Milnor's coordinates map each `U_k` (in particular `U_0`)
diffeomorphically onto the open unit ball of `ℝ^{2n}`. -/
def B : Prop :=
  ∀ n : ℕ, ∃ (_ : ChartedSpace (Model n) (CPn n)),
    IsManifold 𝓘(ℝ, Model n) ∞ (CPn n) ∧ ∀ k : Fin (n + 1), IsMilnorChart n k

end RoundTrip.V3_41
