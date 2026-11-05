import Morse
/-! Layer-2 blind definition of Morse_curvTensor. Textbook: Milnor, *Morse Theory*, §9, p. 51
(Lemma 9.1), for `N ⊆ V` (Euclidean space) with the induced metric, in MILNOR'S SIGN CONVENTION
`R(X, Y)Z = −∇_X∇_Y Z + ∇_Y∇_X Z + ∇_{[X,Y]} Z` (minus the usual one), so that `⟨R(X,Y)X, Y⟩` is
the sectional curvature of the plane of orthonormal `X, Y` (`+1` on the unit sphere). For a
submanifold of Euclidean space it is given by the Gauss equation (in this sign convention):
`⟨R(X, Y)Z, U⟩ = ⟨II(X, Z), II(Y, U)⟩ − ⟨II(Y, Z), II(X, U)⟩` for `X, Y, Z, U ∈ T_qN`;
`T q X Y Z = R(X, Y)Z` is the unique vector of `T_qN` with these inner products, i.e.
`R(X,Y)Z = A_{II(X,Z)} Y − A_{II(Y,Z)} X` with `⟨A_ν Y, U⟩ = ⟨ν, II(Y, U)⟩` (`A_ν = (II(Y,·))*`,
`LinearMap.adjoint`).
Choices: `hN` (smooth slice submanifold) is the setting; `[FiniteDimensional ℝ Z]` is unused.
The tangent space is the setting's `Morse.tangentSubspace hN p` (it is the result type), used
as `T_pN` at every `p ∈ N` (`⊥` off `N`, irrelevant). `P_p` = orthogonal projection onto `T_pN`.
Second fundamental form (Gauss formula): `II(v, w) = (1 − P_q)((dP_q v) w)`, `dP_q` the derivative
within `N` (`fderivWithin`) of `p ↦ P_p`; in the smooth setting this is `(1 − P_q)(D_v W)` for the
tangent field `W(p) = P_p w` extending `w` (the textbook definition), and this form makes `II`
bilinear by construction. -/
namespace RoundTrip.L2.Morse_curvTensor

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

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

section
variable {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] {W : Type*} [NormedAddCommGroup W]
  [NormedSpace ℝ W] {N : Set V}

/-- The tangent space `T_pN` of the setting at `p ∈ N` (`⊥` for `p ∉ N`). -/
noncomputable def tan (hN : Milnor.IsSliceSubmanifold (modelWithCornersSelf ℝ V) Z W N)
    (p : V) : Submodule ℝ V :=
  open Classical in if h : p ∈ N then Morse.tangentSubspace hN ⟨p, h⟩ else ⊥

/-- Second fundamental form at `q`: `II(v, w) = (1 − P_q)((dP_q v) w)`, `dP_q` the derivative
within `N` of `p ↦ P_p`. -/
noncomputable def II (hN : Milnor.IsSliceSubmanifold (modelWithCornersSelf ℝ V) Z W N)
    (q : ↑N) : V →L[ℝ] V →L[ℝ] V :=
  (ContinuousLinearMap.compL ℝ V V V (1 - (Morse.tangentSubspace hN q).starProjection)).comp
    (fderivWithin ℝ (fun p => (tan hN p).starProjection) N q)

/-- The textbook notion: Milnor's curvature tensor `R(X, Y)Z` on `T_qN` (Gauss equation). -/
noncomputable def T (hN : Milnor.IsSliceSubmanifold (modelWithCornersSelf ℝ V) Z W N)
    [FiniteDimensional ℝ Z] (q : ↑N) :
    Morse.tangentSubspace hN q →ₗ[ℝ] Morse.tangentSubspace hN q →ₗ[ℝ]
      Morse.tangentSubspace hN q →ₗ[ℝ] Morse.tangentSubspace hN q :=
  gaussCurv (Morse.tangentSubspace hN q) (II hN q)

end

end RoundTrip.L2.Morse_curvTensor
