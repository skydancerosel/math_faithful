import Morse
/-! Blind formalization of V3_42 (Milnor §4, pp. 26–27: the function `Σ c_j |z_j|²` on `ℂPⁿ`). Choices:
- `ℂPⁿ`, `U_k` and Milnor's coordinates exactly as in the V3_41 blind file (copied): `CPn n` = unit vectors of `ℂ^{n+1}`
  modulo `z ∼ λz`, `|λ| = 1`, quotient topology; coordinates `x_j + i y_j = |z_k| z_j / z_k` (`j ≠ k`, enumerated by
  `k.succAbove`) on `U_k = {z_k ≠ 0}`, valued in `ℝ^{2n}` = `EuclideanSpace ℝ (Fin n × Fin 2)`.
- Smooth structure: B is stated for EVERY smooth (`C^∞`) manifold structure on `CPn n` (compatible with the quotient
  topology, modelled on `ℝ^{2n}`) in which all of Milnor's coordinate maps are diffeomorphisms `U_k → ` open unit ball
  (`IsMilnorChart`, as in V3_41; existence of such a structure is the claim of V3_41). Critical point, non-degenerate,
  index: the project's `Morse.IsCriticalPointM`, `Morse.IsNondegenerateCriticalPointM`, `Morse.indexM`.
- `f(z_0 : … : z_n) = Σ c_j |z_j|²` (the scan's `c_j|z_j|` is a misprint, as the context note says; the display is used),
  with distinct real constants (`Function.Injective c`). `p_k` = class of the `k`-th unit vector.
- B: (0) `f` is smooth; (1) on `U_k`, `f = c_k + Σ_{j≠k} (c_j − c_k)(x_j² + y_j²)` (Milnor writes `k = 0`, "similarly"
  for the others); (2) the only critical point of `f` in `U_k` is `p_k`; (3) `p_0, …, p_n` are the only critical points;
  (4) `p_k` is non-degenerate of index `2·#{j | c_j < c_k}`; (5) "every possible even index between 0 and 2n occurs exactly
  once": for each `i`, the number of critical points of index `i` is `1` if `i` is even and `≤ 2n`, else `0`.
  `n = 0` allowed. -/
open scoped ContDiff Manifold
namespace RoundTrip.V3_42

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

/-- Milnor's function `f(z_0 : … : z_n) = Σ c_j |z_j|²` (well defined on classes). -/
noncomputable def fC {n : ℕ} (c : Fin (n + 1) → ℝ) : CPn n → ℝ :=
  Quot.lift (fun z : Sph n => ∑ j, c j * ‖z.1 j‖ ^ 2) (by
    rintro z w ⟨a, ha, hw⟩
    simp only [hw, Pi.smul_apply, smul_eq_mul, norm_mul, ha, one_mul])

theorem single_mem {n : ℕ} (k : Fin (n + 1)) : ∑ j, ‖(Pi.single k (1 : ℂ) : Fin (n + 1) → ℂ) j‖ ^ 2 = 1 := by
  rw [Finset.sum_eq_single k]
  · simp
  · intro j _ hj; simp [hj]
  · simp

/-- The point `p_k = (0 : … : 1 : … : 0)` (`1` in place `k`). -/
def pt {n : ℕ} (k : Fin (n + 1)) : CPn n := cls ⟨Pi.single k 1, single_mem k⟩

/-- The number of `j` with `c_j < c_k`. -/
noncomputable def rk {n : ℕ} (c : Fin (n + 1) → ℝ) (k : Fin (n + 1)) : ℕ :=
  (Finset.univ.filter fun j => c j < c k).card

/-- Milnor's analysis of `f = Σ c_j |z_j|²` on `ℂPⁿ`: coordinate form, critical points `p_k` of index `2·#{c_j < c_k}`,
every even index in `[0, 2n]` exactly once. -/
def B : Prop :=
  ∀ (n : ℕ) (c : Fin (n + 1) → ℝ), Function.Injective c →
    ∀ (_ : ChartedSpace (Model n) (CPn n)), IsManifold 𝓘(ℝ, Model n) ∞ (CPn n) →
      (∀ k, IsMilnorChart n k) →
      ContMDiff 𝓘(ℝ, Model n) 𝓘(ℝ) ∞ (fC c) ∧
      (∀ k, ∀ x ∈ U k, fC c x =
        c k + ∑ j : Fin n, (c (k.succAbove j) - c k) * ((phi k x) (j, 0) ^ 2 + (phi k x) (j, 1) ^ 2)) ∧
      (∀ k, ∀ x ∈ U k, Morse.IsCriticalPointM (Model n) (fC c) x ↔ x = pt k) ∧
      (∀ x, Morse.IsCriticalPointM (Model n) (fC c) x ↔ ∃ k, x = pt k) ∧
      (∀ k, Morse.IsNondegenerateCriticalPointM (Model n) (fC c) (pt k) ∧
        Morse.indexM (Model n) (fC c) (pt k) = 2 * rk c k) ∧
      (∀ i : ℕ, {x | Morse.IsCriticalPointM (Model n) (fC c) x ∧ Morse.indexM (Model n) (fC c) x = i}.ncard =
        if Even i ∧ i ≤ 2 * n then 1 else 0)

end RoundTrip.V3_42
