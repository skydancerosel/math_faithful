import Morse
/-! Blind formalization of V14_22 (Milnor §23, Theorem 23.3 (Bott), p. 128). Choices:
- Setting for `Ω` exactly as in the blind files V13_1–V13_5 (prelude copied verbatim; only the definitions needed
  here): `M : Type` an abstract smooth Hausdorff connected manifold modelled on `ℝⁿ = EuclideanSpace ℝ (Fin n)` with a
  smooth Mathlib `RiemannianBundle` metric; `Om n p q = Ω(M;p,q)` (piecewise smooth paths `ℝ → M`, only `[0,1]`
  matters, topology of Milnor's metric `d`), `OmD n p q = Ω^d = E⁻¹[0, ρ(p,q)²]` (the space of minimal geodesics,
  V13_1), `inclD : Ω^d → Ω`; homotopy groups are Mathlib's `π_ i X x` (`HomotopyGroup (Fin i)`; `π_ 0` = path
  components, a set; groups for `i ≥ 1`), `piMap f x` = the induced map `f_*`.
- `SU(2m)` with Milnor's bi-invariant metric (p. 125: `⟨A, B⟩ = Re tr(AB*)`, the Euclidean metric of
  `M_{2m}(ℂ) = ℝ^{8m²}` restricted to `SU(2m)`). Mathlib gives `SU(k)` no manifold structure, so — as the round sphere
  of V10_24/V13_6 (`IsRoundSphere`) — the Riemannian manifold `SU(k)` is an abstract `M` as above with `ψ : M → M_k(ℂ)`
  a smooth topological embedding onto Mathlib's `Matrix.specialUnitaryGroup (Fin k) ℂ` whose differential is isometric
  for the metric of `M` and `Re tr(AB*)` (`IsSUModel k ψ`, modelled by hand); `I`, `−I` are the points `p`, `q` with
  `ψ p = 1`, `ψ q = -1`. `B` is claimed for every such model. As a topological space (in `π_{i+1}SU(2m)`) `SU(2m)` is
  the Mathlib subtype `SU (2*m)` (matrix-group prelude of the blind file V14_23, copied verbatim). `m = 0` is allowed
  (then every space involved is a point). No connection is quantified (`Ω`, `Ω^d` and the claim depend only on the
  metric); `T2Space M` and `ConnectedSpace M` are kept as in the V13 files (they follow from `IsSUModel`).
- `G_m(ℂ^{2m}) = Grass (2m) m`: the `m`-dimensional subspaces `W ⊆ ℂ^{2m}`, modelled by their orthogonal projections
  `P` (Hermitian idempotents of rank `m`), with the subspace topology of `M_{2m}(ℂ)`.
- "The inclusion map `G_m(ℂ^{2m}) → Ω(SU(2m); I, −I)`" is Milnor's identification of `G_m(ℂ^{2m})` with the space
  `Ω^d` of minimal geodesics (Lemma 23.1) followed by `Ω^d ⊆ Ω`: `W ↦ (t ↦ exp(tA_W))`, `A_W = iπ(2P_W − I)`
  (`velA`; eigenvalue `iπ` on `W`, `−iπ` on `W^⊥`; `exp` = Mathlib's `NormedSpace.exp`). Using `W^⊥` instead of `W`
  composes with a homeomorphism of `G_m` and changes nothing. Both forms are included: (a) `inclD : Ω^d → Ω` induces
  bijections `π_i(Ω^d, x₀) → π_i(Ω, x₀)` for `0 ≤ i ≤ 2m` and every `x₀ ∈ Ω^d`, group isomorphisms for `1 ≤ i ≤ 2m`;
  (b) there is a continuous `j : G_m(ℂ^{2m}) → Ω` with `ψ ∘ (j W) = (t ↦ exp(tA_W))` on `[0,1]` (paths are compared on
  `[0,1]` only; any two such `j` are homotopic, as paths agreeing on `[0,1]` are topologically indistinguishable in
  `Ω`), and `j` induces bijections on `π_i`, `0 ≤ i ≤ 2m`, at every base point, group isomorphisms for `i ≥ 1`. That the
  image of `j` is `Ω^d` (Lemma 23.1) is not claimed here.
- "Isomorphisms of homotopy groups in dimensions `≤ 2m`": `0 ≤ i ≤ 2m` (for `i = 0` a bijection of sets of path
  components). "Hence `π_iG_m(ℂ^{2m}) ≅ π_{i+1}SU(2m)` for `0 ≤ i ≤ 2m`": at all base points, `π_i G_m ≃ π_{i+1}SU(2m)`
  as sets for `0 ≤ i ≤ 2m` and `≃*` as groups for `1 ≤ i ≤ 2m` (abstract isomorphisms, Milnor names none).
-/
open scoped ContDiff Manifold unitInterval Matrix
open Topology Bundle

namespace RoundTrip.V14_22

abbrev Rn (k : ℕ) := EuclideanSpace ℝ (Fin k)

section Ch7
variable {n : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (Rn n) M] [IsManifold 𝓘(ℝ, Rn n) ∞ M]
  [Bundle.RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, Rn n) x)]

/-- Piecewise smooth path on `[a, b]`: a subdivision `a = t₀ < ... < t_k = b` with each `pth|[t_{i-1}, t_i]` smooth. -/
def IsPW (pth : ℝ → M) (a b : ℝ) : Prop :=
  ∃ (k : ℕ) (t : ℕ → ℝ), t 0 = a ∧ t k = b ∧ (∀ i < k, t i < t (i + 1)) ∧
    ∀ i < k, ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, Rn n) ∞ pth (Set.Icc (t i) (t (i + 1)))

/-- Arc length `∫_a^b ‖dpth/dt‖ dt` (the derivative exists off a finite set). -/
noncomputable def arcLen (pth : ℝ → M) (a b : ℝ) : ℝ :=
  ∫ t in a..b, ‖(mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, Rn n) pth t (1 : ℝ) : TangentSpace 𝓘(ℝ, Rn n) (pth t))‖

/-- `ρ(p, q)`: greatest lower bound of the arc lengths of piecewise smooth paths joining `p` and `q`. -/
noncomputable def rho (p q : M) : ℝ :=
  sInf {L | ∃ (pth : ℝ → M) (a b : ℝ), a ≤ b ∧ IsPW (n := n) pth a b ∧ pth a = p ∧ pth b = q ∧ arcLen (n := n) pth a b = L}
end Ch7

section Ch8
variable {n : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (Rn n) M] [IsManifold 𝓘(ℝ, Rn n) ∞ M]
  [Bundle.RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, Rn n) x)]

/-- `pw ∈ Ω(M; p, q)`: a piecewise smooth path `[0,1] → M` from `p` to `q` (only values on `[0,1]` matter). -/
def InOmega (p q : M) (pw : ℝ → M) : Prop := IsPW (n := n) pw 0 1 ∧ pw 0 = p ∧ pw 1 = q

/-- Energy `E_a^b(pw) = ∫_a^b ‖dpw/dt‖² dt`. -/
noncomputable def energy (pw : ℝ → M) (a b : ℝ) : ℝ :=
  ∫ t in a..b, ‖(mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, Rn n) pw t (1 : ℝ) : TangentSpace 𝓘(ℝ, Rn n) (pw t))‖ ^ 2

/-- `E = E_0^1`. -/
noncomputable def Efun (pw : ℝ → M) : ℝ := energy (n := n) pw 0 1
end Ch8

section Ch9
variable {n : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (Rn n) M] [IsManifold 𝓘(ℝ, Rn n) ∞ M]
  [Bundle.RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, Rn n) x)]

/-- Arc length function `s(t)` of `w` from `0` to `t` and its derivative `ds/dt`. -/
noncomputable def dsdt (w : ℝ → M) (t : ℝ) : ℝ := deriv (fun x => arcLen (n := n) w 0 x) t

/-- Milnor's distance `d(w,w') = max_t ρ(w(t),w'(t)) + [∫₀¹ (ds/dt − ds'/dt)² dt]^{1/2}`. -/
noncomputable def dOm (w w' : ℝ → M) : ℝ :=
  (⨆ t : Set.Icc (0 : ℝ) 1, rho (n := n) (w t) (w' t)) +
    Real.sqrt (∫ t in (0 : ℝ)..1, (dsdt (n := n) w t - dsdt (n := n) w' t) ^ 2)
end Ch9

section Ch10
variable (n : ℕ) {M : Type} [TopologicalSpace M] [ChartedSpace (Rn n) M] [IsManifold 𝓘(ℝ, Rn n) ∞ M]
  [Bundle.RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, Rn n) x)]

/-- `Ω = Ω(M; p, q)` as a type: piecewise smooth paths from `p` to `q` (maps `ℝ → M`, only `[0,1]` matters). -/
def Om (p q : M) : Type := {w : ℝ → M // InOmega (n := n) p q w}

/-- Milnor's topology on `Ω`: generated by the open `d`-balls (`d = dOm`); this is the topology of the (pseudo)metric `d`
(two paths agreeing on `[0,1]` are not distinguished by `d`, hence topologically indistinguishable). -/
instance omTopology (p q : M) : TopologicalSpace (Om n p q) :=
  TopologicalSpace.generateFrom {S | ∃ (w : Om n p q) (ε : ℝ), S = {w' | dOm (n := n) w.1 w'.1 < ε}}

/-- `Ω^c = E⁻¹[0,c]`, as a subset of `Ω`. -/
def OmLe (p q : M) (c : ℝ) : Set (Om n p q) := {w | Efun (n := n) w.1 ≤ c}
end Ch10

section Ch22
variable (n : ℕ) {M : Type} [TopologicalSpace M] [ChartedSpace (Rn n) M] [IsManifold 𝓘(ℝ, Rn n) ∞ M]
  [Bundle.RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, Rn n) x)]

/-- `d = ρ(p, q)²`. -/
noncomputable def dPQ (p q : M) : ℝ := rho (n := n) p q ^ 2

/-- `Ω^d = E⁻¹[0, d] ⊆ Ω = Ω(M; p, q)` with `d = ρ(p, q)²` (Milnor's notation `Ω^c`, here `c = d`); as a type it carries
the subspace topology of `Ω` (Milnor's `d`-topology). -/
def OmD (p q : M) : Set (Om n p q) := OmLe n p q (dPQ n p q)

/-- The inclusion `Ω^d → Ω`. -/
def inclD (p q : M) : C(↥(OmD n p q), Om n p q) := ⟨Subtype.val, continuous_subtype_val⟩
end Ch22

section Htpy
/-- `f ∘ γ` for a generalized loop `γ : (I^N, ∂I^N) → (X, x)`. -/
def genLoopMap {N X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y)) {x : X}
    (γ : ↥(GenLoop N X x)) : ↥(GenLoop N Y (f x)) :=
  ⟨f.comp γ.1, fun y hy => by simp [GenLoop.boundary γ y hy]⟩

/-- The homomorphism `f_* : π_N(X, x) → π_N(Y, f x)` induced by a map `f` (Mathlib's `HomotopyGroup`). -/
def piMap {N X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y)) (x : X) :
    HomotopyGroup N X x → HomotopyGroup N Y (f x) :=
  Quotient.map' (genLoopMap f) (fun _ _ h => ContinuousMap.HomotopicRel.comp_continuousMap h f)
end Htpy

section MatrixGroups

/-- `M_k(ℂ)`: complex `k × k` matrices (Mathlib's `Matrix`, product topology). -/
abbrev Mat (k : ℕ) := Matrix (Fin k) (Fin k) ℂ

/-- `U(k)`: Mathlib's unitary group, a topological group with the subspace topology of `M_k(ℂ)`. -/
abbrev U (k : ℕ) := ↥(Matrix.unitaryGroup (Fin k) ℂ)

/-- `SU(k)`: Mathlib's special unitary group. -/
abbrev SU (k : ℕ) := ↥(Matrix.specialUnitaryGroup (Fin k) ℂ)

/-- `diag(1,…,1,0,…,0)` (`j` ones): the orthogonal projection of `ℂ^k` onto `ℂ^j ⊕ 0`. -/
def topProj (k j : ℕ) : Mat k := Matrix.diagonal fun i => if (i : ℕ) < j then 1 else 0

/-- `diag(0,…,0,1,…,1)` (`j` zeros): the orthogonal projection of `ℂ^k` onto `0 ⊕ ℂ^{k-j}`. -/
def botProj (k j : ℕ) : Mat k := Matrix.diagonal fun i => if (i : ℕ) < j then 0 else 1

/-- Milnor's `U(j) ⊆ U(k)` (`j ≤ k`): unitary matrices fixing the basis vectors `e_i`, `i ≥ j`, i.e. the matrices
`diag(B, I_{k-j})` with `B ∈ U(j)` (`g · botProj = botProj` says the last `k - j` columns of `g` are those of `I`). -/
def fixSub (k j : ℕ) : Subgroup (U k) where
  carrier := {g | (g : Mat k) * botProj k j = botProj k j}
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq, Matrix.UnitaryGroup.mul_val] at *
    rw [Matrix.mul_assoc, hb, ha]
  one_mem' := by simp
  inv_mem' := by
    intro a ha
    simp only [Set.mem_ofPred_eq, Matrix.UnitaryGroup.inv_val] at *
    calc star (a : Mat k) * botProj k j = star (a : Mat k) * ((a : Mat k) * botProj k j) := by rw [ha]
      _ = botProj k j := by rw [← Matrix.mul_assoc, Matrix.UnitaryGroup.star_mul_self, Matrix.one_mul]

/-- Milnor's `U(j) × U(k-j) ⊆ U(k)`: the block-diagonal unitary matrices `diag(A, B)`, i.e. those commuting with
`topProj k j` (preserving `ℂ^j ⊕ 0` and its orthogonal complement). -/
def blockSub (k j : ℕ) : Subgroup (U k) where
  carrier := {g | (g : Mat k) * topProj k j = topProj k j * (g : Mat k)}
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq, Matrix.UnitaryGroup.mul_val] at *
    rw [Matrix.mul_assoc, hb, ← Matrix.mul_assoc, ha, Matrix.mul_assoc]
  one_mem' := by simp
  inv_mem' := by
    intro a ha
    simp only [Set.mem_ofPred_eq, Matrix.UnitaryGroup.inv_val] at *
    have hs : star (topProj k j) = topProj k j := by
      ext i i'
      by_cases h : i = i'
      · subst h; by_cases h' : (i : ℕ) < j <;> simp [topProj, Matrix.star_apply, h']
      · simp [topProj, Matrix.star_apply, Matrix.diagonal_apply, h, Ne.symm h]
    have := congrArg star ha
    rw [star_mul, star_mul, hs] at this
    exact this.symm

/-- `diag(B, I_{k-j})` for `B ∈ M_j(ℂ)`: the standard inclusion `M_j(ℂ) → M_k(ℂ)` (`j ≤ k`). -/
def blockIncl (k j : ℕ) (B : Mat j) : Mat k :=
  Matrix.of fun a b => if h : (a : ℕ) < j ∧ (b : ℕ) < j then B ⟨a, h.1⟩ ⟨b, h.2⟩ else (1 : Mat k) a b

/-- `S^{2m+1}`: the unit sphere of `ℂ^{m+1}` (product topology). -/
def Sph (m : ℕ) : Set (Fin (m + 1) → ℂ) := {v | ∑ i, Complex.normSq (v i) = 1}

/-- `G_m(ℂ^k)`: the `m`-dimensional subspaces of `ℂ^k`, modelled by their orthogonal projections (Hermitian
idempotent matrices of rank `m`), with the subspace topology of `M_k(ℂ)`. -/
def Grass (k m : ℕ) : Set (Mat k) := {P | P.conjTranspose = P ∧ P * P = P ∧ P.rank = m}
end MatrixGroups

section SUModel
variable {n : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (Rn n) M] [IsManifold 𝓘(ℝ, Rn n) ∞ M]
  [Bundle.RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, Rn n) x)]

/-- The differential `dψ_x(v)` of `ψ : M → M_k(ℂ)`, read as a matrix (derivative in the normed space
`Fin k → Fin k → ℂ` underlying `M_k(ℂ)`; sup norm, any norm gives the same derivative). -/
noncomputable def dMat (k : ℕ) (ψ : M → (Fin k → Fin k → ℂ)) (x : M) (v : TangentSpace 𝓘(ℝ, Rn n) x) : Mat k :=
  mfderiv 𝓘(ℝ, Rn n) 𝓘(ℝ, Fin k → Fin k → ℂ) ψ x v

/-- `M` is `SU(k)` with Milnor's bi-invariant metric `⟨A, B⟩ = Re tr(AB*)` (p. 125): `ψ : M → M_k(ℂ)` is a smooth
topological embedding onto `SU(k)` whose differential is isometric for the metric of `M` and `Re tr(AB*)` (the
Euclidean inner product of `M_k(ℂ) = ℝ^{2k²}`). -/
def IsSUModel (k : ℕ) (ψ : M → (Fin k → Fin k → ℂ)) : Prop :=
  ContMDiff 𝓘(ℝ, Rn n) 𝓘(ℝ, Fin k → Fin k → ℂ) ∞ ψ ∧ Topology.IsEmbedding ψ ∧
  Set.range ψ = (Matrix.specialUnitaryGroup (Fin k) ℂ : Set (Mat k)) ∧
  ∀ (x : M) (v w : TangentSpace 𝓘(ℝ, Rn n) x),
    inner ℝ v w = (Matrix.trace (dMat k ψ x v * (dMat k ψ x w)ᴴ)).re
end SUModel

/-- Milnor's `A_W = iπ(2P − I)` for the orthogonal projection `P` onto `W ∈ G_m(ℂ^{2m})`: the velocity of the minimal
geodesic `t ↦ exp(tA_W)` from `I` to `−I` in `SU(2m)` with `Eigen(iπ) = W` (Lemma 23.1). -/
noncomputable def velA {k : ℕ} (P : Mat k) : Mat k := (Complex.I * (Real.pi : ℂ)) • ((2 : ℂ) • P - 1)

/-- Bott: the inclusion `G_m(ℂ^{2m}) ≅ Ω^d ⊆ Ω(SU(2m); I, −I)` induces isomorphisms on `π_i`, `i ≤ 2m`; hence
`π_iG_m(ℂ^{2m}) ≅ π_{i+1}SU(2m)` for `0 ≤ i ≤ 2m`. -/
def B : Prop :=
  ∀ (m n : ℕ) (M : Type) [TopologicalSpace M] [T2Space M] [ChartedSpace (Rn n) M] [IsManifold 𝓘(ℝ, Rn n) ∞ M]
    [Bundle.RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, Rn n) x)]
    [IsContMDiffRiemannianBundle 𝓘(ℝ, Rn n) ∞ (Rn n) (fun x : M => TangentSpace 𝓘(ℝ, Rn n) x)]
    [ConnectedSpace M] (ψ : M → Mat (2 * m)), IsSUModel (n := n) (2 * m) ψ →
    ∀ p q : M, ψ p = 1 → ψ q = -1 →
      (∀ x₀ : ↥(OmD n p q),
        (∀ i : ℕ, i ≤ 2 * m → Function.Bijective (piMap (N := Fin i) (inclD n p q) x₀)) ∧
        ∀ k : ℕ, k + 1 ≤ 2 * m →
          ∃ e : π_ (k + 1) ↥(OmD n p q) x₀ ≃* π_ (k + 1) (Om n p q) (inclD n p q x₀),
            ⇑e = piMap (inclD n p q) x₀) ∧
      (∃ j : C(↥(Grass (2 * m) m), Om n p q),
        (∀ (P : ↥(Grass (2 * m) m)) (t : ℝ), t ∈ Set.Icc (0 : ℝ) 1 →
          ψ ((j P).1 t) = NormedSpace.exp ((t : ℂ) • velA (P : Mat (2 * m)))) ∧
        ∀ P : ↥(Grass (2 * m) m),
          (∀ i : ℕ, i ≤ 2 * m → Function.Bijective (piMap (N := Fin i) j P)) ∧
          ∀ k : ℕ, k + 1 ≤ 2 * m →
            ∃ e : π_ (k + 1) ↥(Grass (2 * m) m) P ≃* π_ (k + 1) (Om n p q) (j P), ⇑e = piMap j P) ∧
      (∀ i : ℕ, i ≤ 2 * m → ∀ (P : ↥(Grass (2 * m) m)) (h : SU (2 * m)),
        Nonempty (π_ i ↥(Grass (2 * m) m) P ≃ π_ (i + 1) (SU (2 * m)) h)) ∧
      (∀ k : ℕ, k + 1 ≤ 2 * m → ∀ (P : ↥(Grass (2 * m) m)) (h : SU (2 * m)),
        Nonempty (π_ (k + 1) ↥(Grass (2 * m) m) P ≃* π_ (k + 2) (SU (2 * m)) h))

end RoundTrip.V14_22
