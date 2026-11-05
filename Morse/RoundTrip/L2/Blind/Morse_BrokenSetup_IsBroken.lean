import Morse
/-! Layer-2 blind definition of Morse_BrokenSetup_IsBroken. Textbook: Milnor, *Morse Theory*,
§16, p. 88: for a subdivision `0 = t₀ < ⋯ < t_k = 1`, `Ω(t₀, …, t_k)` is the set of paths
`ω ∈ Ω(M; p, q)` (so `ω(0) = p`, `ω(1) = q`, `ω` piecewise smooth) whose restriction to each
`[t_{i-1}, t_i]` is a geodesic (smooth with `D/dt (dω/dt) = 0`).
Choices: the setup `B` is the setting; only its subdivision (the field `B.t : Fin (m + 2) → ℝ`,
strictly increasing from `0` to `1`) and its points `p`, `q` are used; the energy bound `c` and
the other data of `B` are not (no `E(ω) < c` condition: that is `Int Ω^c(t₀, …, t_k)`, not
`Ω(t₀, …, t_k)`). `γ : ℝ → V`, only its values on `[0, 1]` matter: continuous on `[0, 1]`,
`γ([0, 1]) ⊆ N`, `γ 0 = p`, `γ 1 = q`, and on each piece `s = [t_i, t_{i+1}]` `γ` is `C^∞`
(`ContDiffOn`, one-sided derivatives at the ends) with acceleration
`derivWithin (derivWithin γ s) s t` orthogonal to `T_{γ(t)}N` for every `t ∈ s` (`D/dt` in
`N ⊆ V` is the tangential part of the ordinary derivative; no finite-dimensionality is carried,
so "tangential part = 0" is stated via the orthogonal complement). The tangent space is defined
from scratch: span of the velocities `c'(0)` of smooth curves `c : (−ε, ε) → N` through the
point. -/
namespace RoundTrip.L2.Morse_BrokenSetup_IsBroken

open scoped ContDiff
open Set

section
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- `v` is the velocity `γ'(0)` of a smooth curve `γ : (−ε, ε) → N` with `γ(0) = q`. -/
def IsVelocity (N : Set V) (q v : V) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ∃ γ : ℝ → V, ContDiffOn ℝ ∞ γ (Ioo (-ε) ε) ∧
    MapsTo γ (Ioo (-ε) ε) N ∧ γ 0 = q ∧ HasDerivAt γ v 0

/-- The tangent space `T_qN ⊆ V` (span of the velocities at `q`). -/
def tangentSpace (N : Set V) (q : V) : Submodule ℝ V :=
  Submodule.span ℝ {v | IsVelocity N q v}

end

/-- The textbook notion: `γ ∈ Ω(t₀, …, t_{m+1})`, a broken geodesic from `p` to `q` for the
subdivision of `B`. -/
def T {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {Z : Type*}
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {N : Set V} {hN : Milnor.IsSliceSubmanifold (modelWithCornersSelf ℝ V) Z W N} {p q : V}
    {c : ℝ} {m : ℕ} (B : Morse.BrokenSetup hN p q c m) (γ : ℝ → V) : Prop :=
  ContinuousOn γ (Icc 0 1) ∧ MapsTo γ (Icc 0 1) N ∧ γ 0 = p ∧ γ 1 = q ∧
    ∀ i : Fin (m + 1),
      ContDiffOn ℝ ∞ γ (Icc (B.t i.castSucc) (B.t i.succ)) ∧
        ∀ t ∈ Icc (B.t i.castSucc) (B.t i.succ),
          derivWithin (derivWithin γ (Icc (B.t i.castSucc) (B.t i.succ)))
              (Icc (B.t i.castSucc) (B.t i.succ)) t ∈ (tangentSpace N (γ t))ᗮ

end RoundTrip.L2.Morse_BrokenSetup_IsBroken
