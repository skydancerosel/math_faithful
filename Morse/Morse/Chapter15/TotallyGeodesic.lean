import Morse.Chapter12.GroupGeodesics

/-!
Milnor, *Morse Theory*, §24, Lemma 24.4 (i) (p. 137), and Exposition/Chapter15.md, §2, Lemma 2.2.

# Totally geodesic sets of orthogonal matrices

## Milnor's text, paraphrased

(p. 137) "Each `Ω_k(n)` is a smooth, totally geodesic submanifold of `O(n)`": near `J ∈ Ω_k(n)` the
points of `O(n)` are the `J exp A`, `A` small and skew, and those in `Ω_k(n)` are the
`J exp A` with `A ∈ 𝒯_J`; the curves `t ↦ J exp(tA)`, `A ∈ 𝒯_J`, are geodesics of `O(n)` which stay
in `Ω_k(n)`, and "this clearly implies" total geodesy.

## What is formalized

* `Morse.isSliceSubmanifold_of_param`: **a set is a slice submanifold as soon as it has local
  parametrizations** `Φ : Z × W → V` (smooth, `Φ 0 = x`, invertible derivative at `0`) with
  `Φ(z, 0) ∈ S` and every `Φ q ∈ S` near `0` of the form `Φ(g q, 0)`, `g q → 0`; the slice chart
  is a local inverse of `Φ` (the companion project's inverse function theorem).
* `Morse.IsTotGeo hN T`: a slice submanifold `N` of orthogonal matrices with spaces `T x` of skew
  matrices (`dim T x = dim N`) such that `x exp A ∈ N` and `A ∈ T(x exp A)` for `A ∈ T x`.  For it:
  `Morse.IsTotGeo.tangentSubspace_eq` (`T_xN = x·T x`),
  `Morse.IsTotGeo.isGeodesicOn_mul_exp_smul` (**`t ↦ x exp(tA)` is a geodesic of `N` on `ℝ`**: its
  acceleration `x exp(tA)A²` is normal, since `A²` is symmetric and `T_yN` consists of `y·skew`),
  `Morse.IsTotGeo.eqOn_mul_exp_smul` (**every geodesic of `N` is of this form**, by uniqueness),
  `Morse.IsTotGeo.eqOn_of_isUnbrokenGeodesic` (on `[0, 1]`, from `p`),
  `Morse.IsTotGeo.exp_eq` (`exp_x(xA) = x exp A`), `Morse.IsTotGeo.isGeodesicallyComplete`, and
  the energy and length `‖V‖²`, `‖V‖` of `t ↦ x exp(tV)`.

## What Milnor leaves implicit

* "Totally geodesic" is never used as a definition here: what Theorem 22.1 needs is the list of
  geodesics of `N` itself, and it follows directly from the normality of the acceleration, without
  comparing the connections of `N` and `O(n)` (the exposition's Lemma 2.2 (a), (b)).
* The manifold structure needs a chart, i.e. the inverse function theorem for the
  parametrization; Milnor's "`A ↦ J exp A` is a chart" uses that the "only if" halves of his
  Assertions hold for small `A` (`Morse/Chapter15/OmegaManifold.lean`).
-/

open Matrix Set Filter Topology Module
open scoped Morse.MatrixInner RealInnerProductSpace Manifold ContDiff

noncomputable section

namespace Morse

section Slice

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]

/-- **A set with local parametrizations is a slice submanifold**: if near each `x ∈ S` there is a
smooth `Φ : Z × W → V` with `Φ 0 = x` and invertible derivative at `0`, such that (near `0`) the
points `Φ(z, 0)` lie in `S` and every point `Φ q ∈ S` is also `Φ(g q, 0)` for some `g q → 0`,
then `S` is a slice submanifold modelled on `Z` (the slice chart is a local inverse of `Φ`, by the
inverse function theorem). -/
theorem isSliceSubmanifold_of_param {S : Set V}
    (h : ∀ x ∈ S, ∃ Φ : Z × W → V, ContDiff ℝ ∞ Φ ∧ Φ 0 = x ∧
      (∃ e : (Z × W) ≃L[ℝ] V, HasFDerivAt Φ (e : (Z × W) →L[ℝ] V) 0) ∧
      (∀ᶠ q in 𝓝 (0 : Z × W), q.2 = 0 → Φ q ∈ S) ∧
      ∃ g : Z × W → Z, Tendsto g (𝓝 0) (𝓝 0) ∧
        ∀ᶠ q in 𝓝 (0 : Z × W), Φ q ∈ S → Φ (g q, 0) = Φ q) :
    Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W S := by
  intro x hx
  obtain ⟨Φ, hΦ, hΦ0, ⟨e, he⟩, h0, g, hg, hgΦ⟩ := h x hx
  have hinv : (mfderiv 𝓘(ℝ, Z × W) 𝓘(ℝ, V) Φ 0).IsInvertible := by
    rw [mfderiv_eq_fderiv, he.fderiv]
    exact ⟨e, rfl⟩
  obtain ⟨Ψ, h0Ψ, hΨ⟩ := Milnor.ContMDiff.isLocalDiffeomorphAt_of_isInvertible_mfderiv
    hΦ.contMDiff (by simp) hinv
  have hsrc : Ψ.source ∈ 𝓝 (0 : Z × W) := Ψ.open_source.mem_nhds h0Ψ
  have hg' : Tendsto (fun q : Z × W => ((g q, 0) : Z × W)) (𝓝 0) (𝓝 0) := by
    have := hg.prodMk_nhds (tendsto_const_nhds (x := (0 : W)))
    rwa [← Prod.zero_eq_mk] at this
  have hev : ∀ᶠ q in 𝓝 (0 : Z × W), (Φ q ∈ S ↔ q.2 = 0) := by
    filter_upwards [h0, hgΦ, hsrc, hg'.eventually hsrc] with q hq0 hqg hqs hqs'
    refine ⟨fun hq => ?_, hq0⟩
    have e1 : Ψ.toFun (g q, 0) = Ψ.toFun q := by
      rw [← hΨ hqs', ← hΨ hqs]; exact hqg hq
    have := Ψ.toPartialEquiv.injOn hqs' hqs e1
    rw [← this]
  obtain ⟨U, hUev, hUo, h0U⟩ := mem_nhds_iff.1 hev
  set Ψ' := Ψ.restrOpen U hUo with hΨ'
  have hxt : x ∈ Ψ'.target := ⟨0, ⟨h0Ψ, h0U⟩, by rw [← hΦ0]; exact (hΨ h0Ψ).symm⟩
  refine ⟨⟨Ψ'.symm, x, hx, hxt, fun p hp => ?_⟩, hxt⟩
  obtain ⟨q, hq, rfl⟩ := hp
  have hq' : Ψ'.toPartialEquiv.symm (Ψ'.toFun q) = q := Ψ'.toPartialEquiv.left_inv hq
  change Ψ'.toFun q ∈ S ↔ (Ψ'.toPartialEquiv.symm (Ψ'.toFun q)).2 = 0
  rw [hq']
  have : Ψ'.toFun q = Φ q := (hΨ hq.1).symm
  rw [this]
  exact hUev hq.2

end Slice

section TotGeo

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  {N : Set (Matrix ι ι ℝ)}

/-- **A totally geodesic set of orthogonal matrices**: a slice submanifold `N ⊆ Mₙ(ℝ)` of
orthogonal matrices with, at each `x ∈ N`, a space `T x` of skew matrices of dimension `dim N`
such that `x exp A ∈ N` for `A ∈ T x`.  (For `O(n)`, `T x = 𝔬(n)`; for Milnor's `Ω_k(n)`,
`T x = 𝒯_x`.) -/
structure IsTotGeo (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, Matrix ι ι ℝ) Z W N)
    (T : Matrix ι ι ℝ → Submodule ℝ (Matrix ι ι ℝ)) : Prop where
  unitary : ∀ x ∈ N, xᴴ * x = 1
  skew : ∀ x ∈ N, ∀ A ∈ T x, Aᴴ = -A
  mul_exp_mem : ∀ x ∈ N, ∀ A ∈ T x, x * NormedSpace.exp A ∈ N
  mem_mul_exp : ∀ x ∈ N, ∀ A ∈ T x, A ∈ T (x * NormedSpace.exp A)
  finrank_eq : ∀ x ∈ N, finrank ℝ (T x) = finrank ℝ Z

namespace IsTotGeo

variable {hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, Matrix ι ι ℝ) Z W N}
  {T : Matrix ι ι ℝ → Submodule ℝ (Matrix ι ι ℝ)} (h : IsTotGeo hN T)
include h

theorem mul_conjTranspose {x : Matrix ι ι ℝ} (hx : x ∈ N) : x * xᴴ = 1 :=
  mul_conjTranspose_eq_one (h.unitary x hx)

theorem mul_exp_smul_mem {x : Matrix ι ι ℝ} (hx : x ∈ N) {A : Matrix ι ι ℝ} (hA : A ∈ T x)
    (t : ℝ) : x * NormedSpace.exp (t • A) ∈ N :=
  h.mul_exp_mem x hx _ ((T x).smul_mem t hA)

omit h in
/-- `x·T x`. -/
def leftT (T : Matrix ι ι ℝ → Submodule ℝ (Matrix ι ι ℝ)) (x : Matrix ι ι ℝ) (hx : xᴴ * x = 1) :
    Submodule ℝ (Matrix ι ι ℝ) :=
  (T x).map ((mulLeftIso x hx).toLinearEquiv : Matrix ι ι ℝ →ₗ[ℝ] Matrix ι ι ℝ)

omit h in
theorem mem_leftT_iff {x : Matrix ι ι ℝ} (hx : xᴴ * x = 1) {v : Matrix ι ι ℝ} :
    v ∈ leftT T x hx ↔ xᴴ * v ∈ T x := by
  rw [leftT, Submodule.mem_map]
  constructor
  · rintro ⟨X, hX, rfl⟩
    change xᴴ * (x * X) ∈ T x
    rwa [← Matrix.mul_assoc, hx, Matrix.one_mul]
  · intro hv
    refine ⟨xᴴ * v, hv, ?_⟩
    change x * (xᴴ * v) = v
    rw [← Matrix.mul_assoc, mul_conjTranspose_eq_one hx, Matrix.one_mul]

variable [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W]

/-- **The tangent space of `N` at `x` is `x·T x`**: the curves `t ↦ x exp(tA)`, `A ∈ T x`, lie
in `N` with velocity `xA` at `0`, and both spaces have dimension `dim N`. -/
theorem tangentSubspace_eq (x : N) :
    tangentSubspace hN x = leftT T x.1 (h.unitary x x.2) := by
  symm
  refine Submodule.eq_of_le_of_finrank_eq (K := ℝ) (V := Matrix ι ι ℝ) ?_ ?_
  · intro v hv
    rw [mem_leftT_iff] at hv
    set X := x.1ᴴ * v with hXdef
    have hvX : v = x.1 * X := by
      rw [hXdef, ← Matrix.mul_assoc, h.mul_conjTranspose x.2, Matrix.one_mul]
    have hc : HasDerivAt (fun t : ℝ => x.1 * NormedSpace.exp (t • X)) (x.1 * X) 0 := by
      have := (hasDerivAt_exp_smul_const X (0 : ℝ)).const_mul x.1
      simpa using this
    have hmem : ∀ᶠ s in 𝓝 (0 : ℝ), x.1 * NormedSpace.exp (s • X) ∈ N :=
      Filter.Eventually.of_forall fun s => h.mul_exp_smul_mem x.2 hv s
    have hT := hasDerivAt_mem_tangentSubspace hN hc hmem
    have hx0 : (⟨x.1 * NormedSpace.exp ((0 : ℝ) • X), hmem.self_of_nhds⟩ : N) = x := by
      ext1; simp
    rw [hx0] at hT
    rw [hvX]
    exact hT
  · have h1 := finrank_tanAt hN x.2
    rw [tanAt_of_mem hN x.2] at h1
    rw [leftT, LinearEquiv.finrank_map_eq, h.finrank_eq x x.2]
    exact h1.symm

theorem mem_tangentSubspace_iff (x : N) {v : Matrix ι ι ℝ} :
    v ∈ tangentSubspace hN x ↔ x.1ᴴ * v ∈ T x.1 := by
  rw [h.tangentSubspace_eq, mem_leftT_iff]

/-- **The geodesics `t ↦ x exp(tA)`**, `A ∈ T x`, on all of `ℝ`: the acceleration
`x exp(tA) A²` is normal, `A²` being symmetric and the tangent space `y·T y` consisting of
`y·(skew)`. -/
theorem isGeodesicOn_mul_exp_smul {x : Matrix ι ι ℝ} (hx : x ∈ N) {A : Matrix ι ι ℝ}
    (hA : A ∈ T x) : IsGeodesicOn hN (fun t => x * NormedSpace.exp (t • A)) univ where
  isOpen := isOpen_univ
  mem t _ := h.mul_exp_smul_mem hx hA t
  contDiffOn := (contDiff_const.mul (contDiff_exp_smul A)).contDiffOn
  normal t _ := by
    rw [deriv_deriv_mul_exp_smul, Submodule.mem_orthogonal]
    intro u hu
    set q : N := ⟨x * NormedSpace.exp (t • A), h.mul_exp_smul_mem hx hA t⟩
    change u ∈ tangentSubspace hN q at hu
    rw [h.mem_tangentSubspace_iff] at hu
    have hu' : u = q.1 * (q.1ᴴ * u) := by
      rw [← Matrix.mul_assoc, h.mul_conjTranspose q.2, Matrix.one_mul]
    have hXX : x * NormedSpace.exp (t • A) * A * A = q.1 * (A * A) := by
      simp only [q, Matrix.mul_assoc]
    rw [hu', hXX, inner_mul_left_of_unitary (h.unitary q q.2)]
    have hXX' : (A * A)ᴴ = A * A := by
      rw [conjTranspose_mul, h.skew x hx A hA, neg_mul_neg]
    rw [real_inner_comm]
    exact inner_eq_zero_of_hermitian_of_skew hXX' (h.skew _ q.2 _ hu)

/-- **Every geodesic of `N` is of the form `t ↦ x exp((t − t₀)X)`**, `X = xᴴγ'(t₀) ∈ T x`,
`x = γ(t₀)`, by the uniqueness of geodesics. -/
theorem eqOn_mul_exp_smul {γ : ℝ → Matrix ι ι ℝ} {s : Set ℝ} (hγ : IsGeodesicOn hN γ s)
    (hs : IsPreconnected s) {t₀ : ℝ} (ht₀ : t₀ ∈ s) :
    (γ t₀)ᴴ * deriv γ t₀ ∈ T (γ t₀) ∧
      EqOn γ (fun t => γ t₀ * NormedSpace.exp ((t - t₀) • ((γ t₀)ᴴ * deriv γ t₀))) s := by
  set g := γ t₀ with hgdef
  have hg : g ∈ N := hγ.mem t₀ ht₀
  set X := gᴴ * deriv γ t₀ with hXdef
  have hX : X ∈ T g := by
    have := hγ.deriv_mem ht₀
    rwa [h.mem_tangentSubspace_iff] at this
  refine ⟨hX, ?_⟩
  set g' := g * NormedSpace.exp ((-t₀) • X)
  have hg' : g' ∈ N := h.mul_exp_smul_mem hg hX _
  have hX' : X ∈ T g' := by
    have := h.mem_mul_exp g hg _ ((T g).smul_mem (-t₀) hX)
    have h2 := (T g').smul_mem (-t₀)⁻¹ this
    by_cases ht : t₀ = 0
    · have hg'' : g' = g := by simp [g', ht]
      rw [hg'']; exact hX
    · rwa [smul_smul, inv_mul_cancel₀ (neg_ne_zero.2 ht), one_smul] at h2
  have hc : (fun t => g' * NormedSpace.exp (t • X)) =
      fun t => g * NormedSpace.exp ((t - t₀) • X) := by
    funext t
    rw [Matrix.mul_assoc, exp_smul_mul_exp_smul, neg_add_eq_sub]
  have hgeo := (h.isGeodesicOn_mul_exp_smul hg' hX').mono hγ.isOpen (subset_univ s)
  rw [hc] at hgeo
  refine hγ.eqOn hgeo hs ht₀ (by simp [hgdef]) ?_
  have hd : HasDerivAt (fun t => g * NormedSpace.exp ((t - t₀) • X)) (g * X) t₀ := by
    have := hasDerivAt_mul_exp_smul g' X t₀
    rw [hc] at this
    convert this using 1
    simp only [g', Matrix.mul_assoc, exp_smul_mul_exp_smul, neg_add_cancel, zero_smul,
      NormedSpace.exp_zero, Matrix.one_mul]
  rw [hd.deriv, hXdef, ← Matrix.mul_assoc, h.mul_conjTranspose hg, Matrix.one_mul]

/-- **The Riemannian exponential map**: `exp_x(xA) = x exp A` for `A ∈ T x`. -/
theorem exp_eq {x : Matrix ι ι ℝ} (hx : x ∈ N) {A : Matrix ι ι ℝ} (hA : A ∈ T x) :
    Morse.exp hN x (x * A) = x * NormedSpace.exp A := by
  have hfrom : IsGeodesicFrom hN (fun t => x * NormedSpace.exp (t • A)) x (x * A) := by
    refine ⟨1, one_pos, (h.isGeodesicOn_mul_exp_smul hx hA).mono isOpen_Ioo (subset_univ _), ?_,
      ?_⟩
    · simp
    · rw [deriv_mul_exp_smul]
      simp
  rw [hfrom.exp_eq, one_smul]

/-- **`N` is geodesically complete**: every geodesic `t ↦ x exp(tA)` is defined on `ℝ`. -/
theorem isGeodesicallyComplete : IsGeodesicallyComplete hN := by
  intro q v hv
  rw [h.mem_tangentSubspace_iff] at hv
  have hv' : v = q.1 * (q.1ᴴ * v) := by
    rw [← Matrix.mul_assoc, h.mul_conjTranspose q.2, Matrix.one_mul]
  refine ⟨fun t => q.1 * NormedSpace.exp (t • (q.1ᴴ * v)), 1, one_pos,
    (h.isGeodesicOn_mul_exp_smul q.2 hv).mono isOpen_Ioo (subset_univ _), by simp, ?_⟩
  rw [deriv_mul_exp_smul]
  simp only [zero_smul, NormedSpace.exp_zero, Matrix.mul_one]
  exact hv'.symm

/-- **Every geodesic of `N` from `p` is `t ↦ p exp(tV)` on `[0, 1]`**, `V ∈ T p` (the
classification above at `t₀ = 1/2`, glued to the end points by continuity). -/
theorem eqOn_of_isUnbrokenGeodesic {γ : ℝ → Matrix ι ι ℝ} {p q : Matrix ι ι ℝ}
    (hγ : γ ∈ pathSpace N p q) (hgeo : IsUnbrokenGeodesic hN γ) :
    ∃ V ∈ T p, EqOn γ (fun s : ℝ => p * NormedSpace.exp (s • V)) (Icc 0 1) := by
  have hhalf : (1 / 2 : ℝ) ∈ Ioo (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  obtain ⟨hX, heq⟩ := h.eqOn_mul_exp_smul hgeo.2 isPreconnected_Ioo hhalf
  set g := γ (1 / 2) with hgdef
  have hg : g ∈ N := hgeo.2.mem _ hhalf
  set X := gᴴ * deriv γ (1 / 2) with hXdef
  set φ : ℝ → Matrix ι ι ℝ := fun t => g * NormedSpace.exp ((t - 1 / 2) • X)
  have hφc : Continuous φ :=
    continuous_const.mul ((contDiff_exp_smul X).continuous.comp
      (continuous_id.sub continuous_const))
  have heqI : EqOn γ φ (Icc 0 1) :=
    heq.of_subset_closure hgeo.1.continuousOn hφc.continuousOn Ioo_subset_Icc_self
      (by rw [closure_Ioo zero_ne_one])
  set g' := g * NormedSpace.exp ((-(1 / 2 : ℝ)) • X)
  have hX' : X ∈ T g' := by
    have := h.mem_mul_exp g hg _ ((T g).smul_mem (-(1 / 2 : ℝ)) hX)
    have h2 := (T g').smul_mem (-2 : ℝ) this
    rwa [smul_smul, show (-2 : ℝ) * -(1 / 2) = 1 by norm_num, one_smul] at h2
  have hφ : ∀ t, φ t = g' * NormedSpace.exp (t • X) := fun t => by
    simp only [φ, g', Matrix.mul_assoc, exp_smul_mul_exp_smul]
    congr 3; ring
  have hp : g' = p := by
    have := heqI ⟨le_rfl, zero_le_one⟩
    rw [hγ.2.2.1, hφ] at this
    simpa using this.symm
  refine ⟨X, hp ▸ hX', fun t ht => ?_⟩
  rw [heqI ht, hφ, hp]

omit h [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
/-- The speed of `t ↦ x exp(tV)` is `‖V‖`, for orthogonal `x` and skew `V`. -/
theorem norm_deriv_mul_exp_smul {x V : Matrix ι ι ℝ} (hx : xᴴ * x = 1) (hV : Vᴴ = -V) (t : ℝ) :
    ‖deriv (fun s : ℝ => x * NormedSpace.exp (s • V)) t‖ = ‖V‖ := by
  rw [deriv_mul_exp_smul]
  have hu : (NormedSpace.exp (t • V))ᴴ * NormedSpace.exp (t • V) = 1 :=
    exp_conjTranspose_mul_exp_of_skew (by rw [conjTranspose_smul, star_trivial, hV, smul_neg])
  change ‖x * NormedSpace.exp (t • V) * V‖ = ‖V‖
  rw [Matrix.mul_assoc, ← mulLeftIso_apply _ hx, LinearIsometryEquiv.norm_map,
    ← mulLeftIso_apply _ hu, LinearIsometryEquiv.norm_map]

omit h [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
theorem energy_mul_exp_smul {x V : Matrix ι ι ℝ} (hx : xᴴ * x = 1) (hV : Vᴴ = -V) :
    energy (fun s : ℝ => x * NormedSpace.exp (s • V)) 0 1 = ‖V‖ ^ 2 := by
  have h := energy_eq_of_norm_deriv (k := ‖V‖)
    (IsPiecewiseSmooth.of_contDiff (contDiff_const.mul (contDiff_exp_smul V))
      zero_le_one).isAdmissible
    (fun t _ _ => norm_deriv_mul_exp_smul hx hV t)
  rw [h, sub_zero, mul_one]

omit h [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
theorem pathLength_mul_exp_smul {x V : Matrix ι ι ℝ} (hx : xᴴ * x = 1) (hV : Vᴴ = -V) :
    pathLength (fun s : ℝ => x * NormedSpace.exp (s • V)) 0 1 = ‖V‖ := by
  have h := pathLength_eq_of_norm_deriv (k := ‖V‖)
    (IsPiecewiseSmooth.of_contDiff (contDiff_const.mul (contDiff_exp_smul V))
      zero_le_one).isAdmissible
    (fun t _ _ => norm_deriv_mul_exp_smul hx hV t)
  rw [h, sub_zero, mul_one]

omit [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
/-- `t ↦ p exp(tV)` is a path in `Ω(N; p, p exp V)`. -/
theorem mem_pathSpace_mul_exp {p V : Matrix ι ι ℝ} (hp : p ∈ N) (hV : V ∈ T p) :
    (fun s : ℝ => p * NormedSpace.exp (s • V)) ∈ pathSpace N p (p * NormedSpace.exp V) :=
  ⟨IsPiecewiseSmooth.of_contDiff (contDiff_const.mul (contDiff_exp_smul V)) zero_le_one,
    fun t _ => h.mul_exp_smul_mem hp hV t, by simp, by simp⟩

/-- It is an unbroken geodesic. -/
theorem isUnbrokenGeodesic_mul_exp {p V : Matrix ι ι ℝ} (hp : p ∈ N) (hV : V ∈ T p) :
    IsUnbrokenGeodesic hN (fun s : ℝ => p * NormedSpace.exp (s • V)) :=
  ⟨(contDiff_const.mul (contDiff_exp_smul V)).contDiffOn,
    (h.isGeodesicOn_mul_exp_smul hp hV).mono isOpen_Ioo (subset_univ _)⟩

end IsTotGeo

end TotGeo

end Morse
