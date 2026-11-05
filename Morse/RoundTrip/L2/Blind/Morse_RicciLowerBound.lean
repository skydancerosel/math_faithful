import Morse
/-! Layer-2 blind definition of Morse_RicciLowerBound. Textbook: Milnor, *Morse Theory*, §19,
Theorem 19.4 (Myers), p. 104: the hypothesis that the Ricci curvature satisfies
`K(U, U) ≥ (n − 1)/r²` for every unit tangent vector `U` at every point of the
`n`-dimensional Riemannian manifold `N`; `K(U₁, U₂)` = trace of `W ↦ R(U₁, W)U₂` on `T_qN`,
`R` in MILNOR'S SIGN CONVENTION (§9) `R(X, Y)Z = −∇_X∇_Y Z + ∇_Y∇_X Z + ∇_{[X,Y]} Z` (so
`K(U, U) = (n − 1)/r²` on the round sphere of radius `r`).
Choices: `hN` (`N` a smooth slice submanifold of Euclidean `V`, modelled on `Z × W`) is the
setting; `n = dim N` is taken as `Module.finrank ℝ Z` (the model of `N`), cast to `ℝ` before
subtracting `1`. No sign condition on `r` is imposed (Milnor has `r > 0`; for `r = 0` Lean's
`x / 0 = 0` makes the bound `K(U, U) ≥ 0`). Tangent spaces are defined from scratch (span of
velocities `γ'(0)` of smooth curves in `N` through the point), `P_p` = orthogonal projection
onto `T_pN`; unit = norm `1` in `V`. `R` is the curvature of the induced metric by the Gauss
equation (Milnor's sign) `⟨R(X, Y)Z, U⟩ = ⟨II(X, Z), II(Y, U)⟩ − ⟨II(Y, Z), II(X, U)⟩`, i.e.
`R(X,Y)Z = (II(Y,·))*(II(X,Z)) − (II(X,·))*(II(Y,Z))` (`LinearMap.adjoint` on `T_qN`), with
`II(v, w) = (1 − P_q)((dP_q v) w)` (Gauss formula; `dP_q` the derivative within `N`,
`fderivWithin`, of `p ↦ P_p`; in the smooth setting `= (1 − P_q)(D_v W)` for the tangent field
`W(p) = P_p w`). Trace = `LinearMap.trace` on `T_qN`. -/
namespace RoundTrip.L2.Morse_RicciLowerBound

open scoped ContDiff

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- `v` is the velocity `γ'(0)` of a smooth curve `γ : (−ε, ε) → N` with `γ(0) = q`. -/
def IsVelocity (N : Set V) (q v : V) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ∃ γ : ℝ → V, ContDiffOn ℝ ∞ γ (Set.Ioo (-ε) ε) ∧
    Set.MapsTo γ (Set.Ioo (-ε) ε) N ∧ γ 0 = q ∧ HasDerivAt γ v 0

/-- The tangent space `T_qN ⊆ V` (span of the velocities at `q`; `⊥` for `q ∉ N`). -/
def tangentSpace (N : Set V) (q : V) : Submodule ℝ V :=
  Submodule.span ℝ {v | IsVelocity N q v}

variable [FiniteDimensional ℝ V]

/-- The orthogonal projection `P_q : V → V` onto `T_qN`. -/
noncomputable def proj (N : Set V) (q : V) : V →L[ℝ] V :=
  (tangentSpace N q).starProjection

/-- Second fundamental form at `q`: `II(v, w) = (1 − P_q)((dP_q v) w)`, `dP_q` the derivative
within `N` of `p ↦ P_p`. -/
noncomputable def II (N : Set V) (q : V) : V →L[ℝ] V →L[ℝ] V :=
  (ContinuousLinearMap.compL ℝ V V V (1 - proj N q)).comp (fderivWithin ℝ (fun p => proj N p) N q)

/-- A trilinear map built from a function additive and homogeneous in each argument. -/
def mk₃ {M : Type*} [AddCommGroup M] [Module ℝ M] (f : M → M → M → M)
    (a₁ : ∀ x x' y z, f (x + x') y z = f x y z + f x' y z)
    (s₁ : ∀ (c : ℝ) x y z, f (c • x) y z = c • f x y z)
    (a₂ : ∀ x y y' z, f x (y + y') z = f x y z + f x y' z)
    (s₂ : ∀ (c : ℝ) x y z, f x (c • y) z = c • f x y z)
    (a₃ : ∀ x y z z', f x y (z + z') = f x y z + f x y z')
    (s₃ : ∀ (c : ℝ) x y z, f x y (c • z) = c • f x y z) :
    M →ₗ[ℝ] M →ₗ[ℝ] M →ₗ[ℝ] M where
  toFun x :=
    { toFun := fun y =>
        { toFun := fun z => f x y z
          map_add' := a₃ x y
          map_smul' := fun c z => s₃ c x y z }
      map_add' := fun y y' => by ext z; exact a₂ x y y' z
      map_smul' := fun c y => by ext z; exact s₂ c x y z }
  map_add' x x' := by ext y z; exact a₁ x x' y z
  map_smul' c x := by ext y z; exact s₁ c x y z

/-- Curvature tensor from a second fundamental form `b` on `V`, restricted to `K = T_qN`, by the
Gauss equation in Milnor's sign: `R(X,Y)Z = (b(Y,·)|_K)* (b(X,Z)) − (b(X,·)|_K)* (b(Y,Z))`. -/
noncomputable def gaussCurv (K : Submodule ℝ V) (b : V →L[ℝ] V →L[ℝ] V) :
    K →ₗ[ℝ] K →ₗ[ℝ] K →ₗ[ℝ] K :=
  let B : K →ₗ[ℝ] K →ₗ[ℝ] V := (b.toLinearMap₁₂).compl₁₂ K.subtype K.subtype
  mk₃ (fun X Y Z => LinearMap.adjoint (B Y) (B X Z) - LinearMap.adjoint (B X) (B Y Z))
    (by intros; simp only [map_add, LinearMap.add_apply]; abel)
    (by intros; simp only [map_smul, LinearMap.smul_apply, smul_sub])
    (by intros; simp only [map_add, LinearMap.add_apply]; abel)
    (by intros; simp only [map_smul, LinearMap.smul_apply, smul_sub])
    (by intros; simp only [map_add]; abel)
    (by intros; simp only [map_smul, smul_sub])

/-- Milnor's curvature tensor `R(X, Y)Z` of `N` on `T_qN` (Gauss equation). -/
noncomputable def curv (N : Set V) (q : V) :
    tangentSpace N q →ₗ[ℝ] tangentSpace N q →ₗ[ℝ] tangentSpace N q →ₗ[ℝ] tangentSpace N q :=
  gaussCurv (tangentSpace N q) (II N q)

/-- Milnor's Ricci curvature `K(U₁, U₂) = trace (W ↦ R(U₁, W)U₂)` at `q`. -/
noncomputable def ricci (N : Set V) (q : V) (U₁ U₂ : tangentSpace N q) : ℝ :=
  LinearMap.trace ℝ (tangentSpace N q) ((curv N q U₁).flip U₂)

/-- The textbook notion: `K(U, U) ≥ (n − 1)/r²` for every unit `U ∈ T_qN`, every `q ∈ N`. -/
def T {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] {N : Set V}
    (_hN : Milnor.IsSliceSubmanifold (modelWithCornersSelf ℝ V) Z W N) (r : ℝ) : Prop :=
  ∀ q ∈ N, ∀ U : tangentSpace N q, ‖U‖ = 1 →
    ((Module.finrank ℝ Z : ℝ) - 1) / r ^ 2 ≤ ricci N q U U

end RoundTrip.L2.Morse_RicciLowerBound
