import Morse
/-! Layer-2 blind definition of Morse_NormalCoord. Textbook: Milnor, *Morse Theory*, §10, p. 57-58
(Lemma 10.3): normal coordinates of radius `ε` at `q`: `exp_q` restricts to a diffeomorphism from
the open `ε`-ball `B_ε` of `T_qN` onto an open neighbourhood `U` of `q` in `N`; the coordinate
map is its inverse `exp_q⁻¹ : U → B_ε ⊆ T_qN`.
Choices: `hN` (`N` a smooth slice submanifold of `V`) is the setting and is not used. Tangent
spaces from scratch (span of velocities of smooth curves in `N`), with the norm of `V`; geodesics
of `N ⊆ V` (induced metric): `C^∞`, values in `N`, acceleration orthogonal to `T_{γ(t)}N`.
`exp_q(v) = γ(1)` for the geodesic on the closed interval `[0, 1]` with `γ(0) = q`, `γ'(0) = v`
(chosen by `Classical.choose`; unique), `q` if there is none. `B_ε = {w ∈ T_qN : ‖w‖ < ε}` (open
ball of the subtype `T_qN`), `U = exp_q(B_ε)`. "Diffeomorphism from `B_ε` onto an open
neighbourhood of `q` in `N`" is spelled out as: `ε > 0`; `exp_q` is defined (the geodesic exists
on `[0,1]`) on all of `B_ε`; `U` is open in `N` (`U = O ∩ N`, `O` open in `V`) and contains `q`;
`exp_q : B_ε → V` is `C^∞`; and there is an inverse `ψ : U → T_qN` (`ψ ∘ exp_q = id` on `B_ε`,
hence `exp_q|B_ε` is a bijection onto `U`) that is smooth on `U` in the sense of maps on a subset
of a submanifold: near each point of `U` it agrees on `U` with a `C^∞` map on an open subset of
`V`.
Encoding of the `Type`: `T` is the type of structures `NormalChart` whose data is the coordinate
map `chart : U → T_qN` (defined on the subtype `U`) together with the proofs of the properties
above (with `ψ = chart`). Since `chart` is determined by `chart ∘ exp_q = id` on `B_ε`, `T` is a
subsingleton, inhabited iff `exp_q|B_ε` is a diffeomorphism onto an open neighbourhood of `q`
(coordinates valued in `T_qN`; no orthonormal basis / `ℝⁿ` is chosen). -/
namespace RoundTrip.L2.Morse_NormalCoord

open scoped ContDiff
open Set

section
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- `v` is the velocity `c'(0)` of a smooth curve `c : (−ε, ε) → N` with `c(0) = q`. -/
def IsVelocity (N : Set V) (q v : V) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ∃ c : ℝ → V, ContDiffOn ℝ ∞ c (Ioo (-ε) ε) ∧
    MapsTo c (Ioo (-ε) ε) N ∧ c 0 = q ∧ HasDerivAt c v 0

/-- The tangent space `T_qN ⊆ V` (span of the velocities at `q`). -/
def tangentSpace (N : Set V) (q : V) : Submodule ℝ V :=
  Submodule.span ℝ {v | IsVelocity N q v}

/-- `γ` is a geodesic of `N` on `s`: `C^∞` on `s`, `γ(s) ⊆ N`, and the acceleration `γ''(t)` is
orthogonal to `T_{γ(t)}N` for `t ∈ s` (derivatives within `s`). -/
def IsGeo (N : Set V) (γ : ℝ → V) (s : Set ℝ) : Prop :=
  ContDiffOn ℝ ∞ γ s ∧ MapsTo γ s N ∧
    ∀ t ∈ s, ∀ w ∈ tangentSpace N (γ t), inner ℝ (derivWithin (derivWithin γ s) s t) w = 0

/-- `γ` is a geodesic of `N` on `[0, 1]` with `γ(0) = q`, `γ'(0) = v` (right derivative). -/
def IsGeoFrom (N : Set V) (q v : V) (γ : ℝ → V) : Prop :=
  IsGeo N γ (Icc 0 1) ∧ γ 0 = q ∧ HasDerivWithinAt γ v (Icc 0 1) 0

/-- `exp_q(v) = γ(1)` for the geodesic `γ` on `[0,1]` with `γ(0) = q`, `γ'(0) = v` (a chosen
one; unique on `[0,1]`), and `q` if there is none. -/
noncomputable def expQ (N : Set V) (q v : V) : V :=
  open Classical in if h : ∃ γ : ℝ → V, IsGeoFrom N q v γ then Classical.choose h 1 else q

/-- `U = exp_q(B_ε)`, the image of the open `ε`-ball `B_ε` of `T_qN`. -/
def expBall (N : Set V) (q : V) (ε : ℝ) : Set V :=
  (fun w : tangentSpace N q => expQ N q w) '' Metric.ball 0 ε

/-- Normal coordinates of radius `ε` at `q`: the inverse `chart = exp_q⁻¹ : U → T_qN` of
`exp_q|B_ε`, with the properties making `exp_q|B_ε` a diffeomorphism onto the open
neighbourhood `U = exp_q(B_ε)` of `q` in `N`. -/
structure NormalChart (N : Set V) (q : V) (ε : ℝ) where
  /-- the normal coordinate map `exp_q⁻¹ : U → T_qN` -/
  chart : expBall N q ε → tangentSpace N q
  pos : 0 < ε
  defined : ∀ w : tangentSpace N q, ‖w‖ < ε → ∃ γ : ℝ → V, IsGeoFrom N q w γ
  isOpen : ∃ O : Set V, IsOpen O ∧ O ∩ N = expBall N q ε
  mem : q ∈ expBall N q ε
  smooth_exp : ContDiffOn ℝ ∞ (fun w : tangentSpace N q => expQ N q w) (Metric.ball 0 ε)
  left_inv : ∀ (w : tangentSpace N q) (hw : w ∈ Metric.ball (0 : tangentSpace N q) ε),
    chart ⟨expQ N q w, mem_image_of_mem _ hw⟩ = w
  smooth_chart : ∀ x ∈ expBall N q ε, ∃ O : Set V, IsOpen O ∧ x ∈ O ∧
    ∃ G : V → tangentSpace N q, ContDiffOn ℝ ∞ G O ∧
      ∀ (y : V) (hy : y ∈ expBall N q ε), y ∈ O → G y = chart ⟨y, hy⟩

end

/-- The textbook notion: the (sub)type of normal coordinate charts of radius `ε` at `q`. -/
def T {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {Z : Type*}
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {N : Set V} (_hN : Milnor.IsSliceSubmanifold (modelWithCornersSelf ℝ V) Z W N)
    (q : ↑N) (ε : ℝ) : Type _ :=
  NormalChart N (q : V) ε

end RoundTrip.L2.Morse_NormalCoord
