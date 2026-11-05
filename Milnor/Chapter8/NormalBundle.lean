import Milnor.Chapter8.LocalSlice
import Milnor.Chapter6.Tubular4
import Milnor.Chapter6.Opens
import Milnor.Chapter1.InverseFunction

/-!
# Problem 11: the normal bundle and the ε-neighbourhood theorem

Milnor, *Topology from the Differentiable Viewpoint*, §8, Problem 11 (the analogue for the normal
bundle of Problem 10 on the tangent bundle). Let `M ⊆ ℝᵏ` be a smooth manifold of dimension `m`,
given as a slice submanifold with complement `ℝʷ`, `m + w = k`.

* `normalBundleSet hM`: the normal bundle space `E = {(x, v) ∈ M × ℝᵏ | v ⊥ TMₓ}`, where `TMₓ` is
  the range of the derivative of the inclusion `M → ℝᵏ`;
* `isSliceSubmanifold_normalBundle`: **first part**, `E` is a smooth manifold of dimension `k`
  (a slice submanifold of `ℝᵏ × ℝᵏ` modelled on `ℝᵏ`);
* `normalTube hM ε = {(x, v) ∈ E | ‖v‖ < ε}` and `eucTube M ε = {y ∈ ℝᵏ | dist(y, M) < ε}`, both
  open (`normalTubeOpens`, `eucTubeOpens`), hence open submanifolds;
* `exists_normalTube_diffeomorph`: **second part**, if `M` is compact and nonempty (and `k = K + 1`,
  as in Chapter 6) then for some `ε > 0` the map `(x, v) ↦ x + v` is a diffeomorphism from
  `normalTube hM ε` onto `eucTube M ε`. The radius can be taken to be `normalε`
  (`exists_diffeomorph_normalε`);
* `normalRetraction_eq`: for this radius the nearest-point retraction `r = Tub.tubr` of Chapter 6
  satisfies `r (x + v) = x` on `normalTube hM ε` (used in Problem 12).

## Proof

*The manifold structure.* Near `p ∈ M` let `σ` be the slice chart of `M` at `p`, `φ z = σ⁻¹ (z, 0)`
the local parametrization, and `B a = (dφ_{c a})†` the adjoint of its derivative at the chart
coordinate `c a = (σ a).1`. On `V × ℝᵏ` (`V` the chart domain) the normal bundle is the zero set of
`g (a, v) = ((σ a).2, B a v) ∈ ℝʷ × ℝᵐ`: the first component cuts out `M`, and since
`TMₐ = range dφ_{c a}`, `v ⊥ TMₐ` if and only if `B a v = 0`. The derivative
`dg (u, h) = ((dσ u).2, B a h + (dB u) v)` is onto because `dσ` is invertible and `B a` is onto (the
adjoint of an injective map). The local form of Milnor's Lemma 1,
`IsSliceSubmanifold.of_locally_preimage`, gives the manifold structure.

*Local injectivity.* By Lemma 2 (`IsSliceSubmanifold.range_mfderiv_val_eq_ker`), the tangent space
of `E` at `(x, 0)` is `ker dg`, which consists of pairs `(u, h)` with `u ∈ TMₓ` and `h ⊥ TMₓ` (the
term `(dB u) v` vanishes at `v = 0`). So the derivative `(u, h) ↦ u + h` of `S (x, v) = x + v` at
`(x, 0)` is injective: `u + h = 0` gives `‖u‖² = -⟪h, u⟫ = 0`. Hence it is invertible, and by the
inverse function theorem `S` is injective on a neighbourhood `{‖a - x‖ < r, ‖v‖ < r}` of `(x, 0)`
in `E`.

*A uniform radius.* Cover the compact `M` by finitely many balls `B(xᵢ, rᵢ / 2)` and take
`ε ≤ rᵢ / 4` for all `i`. If `a + v = b + w` with `‖v‖, ‖w‖ < ε` and `‖a - xᵢ‖ < rᵢ / 2`, then
`‖b - xᵢ‖ ≤ ‖a - xᵢ‖ + ‖v‖ + ‖w‖ < rᵢ`, so both points lie in the injectivity neighbourhood of
`(xᵢ, 0)` and are equal. We also take `ε` at most the tubular radius of Chapter 6.

*The diffeomorphism.* `S` maps `normalTube ε` into `N_ε` because `dist(x + v, M) ≤ ‖v‖`. The inverse
is `y ↦ (r y, y - r y)`: by Chapter 6, `r` is smooth on `N_ε`, `y - r y ⊥ T M_{r y}` and
`‖y - r y‖ = dist(y, M) < ε`. Clearly `S (r y, y - r y) = y`. Conversely the points
`(r (x + v), x + v - r (x + v))` and `(x, v)` both lie in `normalTube ε` and have the same image
under `S`, so they are equal by injectivity; this is `r (x + v) = x`.
-/

open Set Filter Topology Function Metric Module
open scoped ContDiff Manifold RealInnerProductSpace

noncomputable section

local notation "𝔼" n:max => EuclideanSpace ℝ (Fin n)

namespace Milnor

namespace Problems

section NormalBundle

variable {k m w : ℕ} {M : Set (EuclideanSpace ℝ (Fin k))}
  (hM : IsSliceSubmanifold 𝓘(ℝ, EuclideanSpace ℝ (Fin k)) (EuclideanSpace ℝ (Fin m))
    (EuclideanSpace ℝ (Fin w)) M)

/-- The **normal bundle space** `E = {(x, v) ∈ M × ℝᵏ | v ⊥ TMₓ}`, where the tangent space `TMₓ`
is the range of the derivative of the inclusion `M → ℝᵏ`. -/
def normalBundleSet : Set (EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin k)) :=
  letI := hM.chartedSpace
  {q | ∃ hx : q.1 ∈ M, ∀ t ∈ LinearMap.range ((mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin m))
      𝓘(ℝ, EuclideanSpace ℝ (Fin k)) (Subtype.val : M → EuclideanSpace ℝ (Fin k)) ⟨q.1, hx⟩ :
        EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin k)) :
        EuclideanSpace ℝ (Fin m) →ₗ[ℝ] EuclideanSpace ℝ (Fin k)), ⟪q.2, t⟫ = 0}

namespace NormalAux

/-! ### A local defining function for the normal bundle

Near `p ∈ M` we use the slice chart `σ = Tub.σ hM p` of `M`, with parametrization
`Tub.φ hM p z = σ.φ⁻¹ (z, 0)`. For `a` in `V p` (the chart domain, cut down so that the first
chart coordinate `c a = (σ.φ a).1` lies in the parametrization domain) we put
`B a = (dφ_{c a})† : ℝᵏ → ℝᵐ`. The local defining function is `g (a, v) = ((σ.φ a).2, B a v)`. -/

variable (p : M)

/-- The domain of the local defining function (in the first factor). -/
def V : Set (𝔼 k) :=
  (Tub.σ hM p).φ.source ∩ (fun a => ((Tub.σ hM p).φ a).1) ⁻¹' Tub.Ω hM p

theorem isOpen_V : IsOpen (V hM p) :=
  (continuous_fst.comp_continuousOn (Tub.σ hM p).φ.contMDiffOn.continuousOn).isOpen_inter_preimage
    (Tub.σ hM p).φ.open_source (Tub.isOpen_Ω hM p)

theorem mem_V : p.1 ∈ V hM p :=
  ⟨Tub.mem_source hM p, Tub.c_mem_Ω hM p (Tub.mem_source hM p)⟩

/-- `B a = (dφ_{c a})†`. -/
def B (a : 𝔼 k) : 𝔼 k →L[ℝ] 𝔼 m := Tub.A hM p ((Tub.σ hM p).φ a).1

theorem contDiffOn_B : ContDiffOn ℝ ∞ (B hM p) (V hM p) :=
  (Tub.contDiffOn_A hM p).comp
    (contDiff_fst.comp_contDiffOn ((Tub.contDiffOn_σφ hM p).mono inter_subset_left))
    (fun _ ha => ha.2)

/-- The local defining function `g (a, v) = ((σ.φ a).2, B a v)`. -/
def g (q : 𝔼 k × 𝔼 k) : 𝔼 w × 𝔼 m := (((Tub.σ hM p).φ q.1).2, B hM p q.1 q.2)

theorem contDiffOn_g : ContDiffOn ℝ ∞ (g hM p) (V hM p ×ˢ univ) := by
  have h1 : ContDiffOn ℝ ∞ (fun q : 𝔼 k × 𝔼 k => ((Tub.σ hM p).φ q.1).2) (V hM p ×ˢ univ) :=
    contDiff_snd.comp_contDiffOn (((Tub.contDiffOn_σφ hM p).mono inter_subset_left).comp
      contDiff_fst.contDiffOn fun _ hq => hq.1)
  have h2 : ContDiffOn ℝ ∞ (fun q : 𝔼 k × 𝔼 k => B hM p q.1) (V hM p ×ˢ univ) :=
    (contDiffOn_B hM p).comp contDiff_fst.contDiffOn fun _ hq => hq.1
  exact h1.prodMk (h2.clm_apply contDiff_snd.contDiffOn)

/-- On `V p × ℝᵏ`, the normal bundle is the zero set of `g`. -/
theorem mem_normalBundleSet_iff {q : 𝔼 k × 𝔼 k} (hq : q.1 ∈ V hM p) :
    q ∈ normalBundleSet hM ↔ g hM p q = 0 := by
  let := hM.chartedSpace
  constructor
  · rintro ⟨hx, horth⟩
    have hT := Tub.range_mfd_val hM p ⟨q.1, hx⟩ hq.1
    refine Prod.ext ((Tub.σ hM p).slice q.1 hq.1 |>.1 hx) ?_
    show B hM p q.1 q.2 = 0
    refine inner_self_eq_zero (𝕜 := ℝ) |>.1 ?_
    rw [B, Tub.A_inner]
    refine horth _ ?_
    rw [hT]
    exact ⟨_, rfl⟩
  · intro h
    have h1 : ((Tub.σ hM p).φ q.1).2 = 0 := congrArg Prod.fst h
    have h2 : B hM p q.1 q.2 = 0 := congrArg Prod.snd h
    have hx : q.1 ∈ M := ((Tub.σ hM p).slice q.1 hq.1).2 h1
    refine ⟨hx, fun t ht => ?_⟩
    rw [Tub.range_mfd_val hM p ⟨q.1, hx⟩ hq.1] at ht
    obtain ⟨y, rfl⟩ := ht
    rw [ContinuousLinearMap.coe_coe, ← Tub.A_inner]
    show ⟪B hM p q.1 q.2, y⟫ = 0
    rw [h2, inner_zero_left]

/-- The derivative of the slice chart is surjective. -/
theorem surjective_fderiv_σφ {a : 𝔼 k} (ha : a ∈ (Tub.σ hM p).φ.source) :
    Surjective (fderiv ℝ (Tub.σ hM p).φ a) := by
  have hloc := (Tub.σ hM p).φ.isLocalDiffeomorphAt 𝓘(ℝ, 𝔼 k) 𝓘(ℝ, 𝔼 m × 𝔼 w) ∞ ha
  have h := (hloc.mfderivToContinuousLinearEquiv (by simp)).surjective
  rw [← mfderiv_eq_fderiv]
  exact h

/-- `B a` is surjective, being the adjoint of an injective map. -/
theorem surjective_B {a : 𝔼 k} (ha : a ∈ V hM p) : Surjective (B hM p a) := by
  set T := fderiv ℝ (Tub.φ hM p) ((Tub.σ hM p).φ a).1 with hT
  have hinj : Injective ((B hM p a).comp T) := by
    intro y₁ y₂ h
    apply Tub.injective_fderiv_φ hM p ha.2
    have h' : (B hM p a) (T (y₁ - y₂)) = 0 := by
      have := congrArg (fun z => z - (B hM p a).comp T y₂) h
      simpa [map_sub] using this
    have h0 : ⟪T (y₁ - y₂), T (y₁ - y₂)⟫ = 0 := by
      rw [hT, ← Tub.A_inner]
      show ⟪B hM p a (T (y₁ - y₂)), y₁ - y₂⟫ = 0
      rw [h', inner_zero_left]
    have := inner_self_eq_zero.1 h0
    rw [map_sub, sub_eq_zero] at this
    exact this
  have hsurj : Surjective ((B hM p a).comp T : 𝔼 m →ₗ[ℝ] 𝔼 m) :=
    LinearMap.injective_iff_surjective.1 hinj
  intro z
  obtain ⟨y, hy⟩ := hsurj z
  exact ⟨T y, hy⟩

/-- The derivative of `g`. -/
theorem hasFDerivAt_g {a : 𝔼 k} (ha : a ∈ V hM p) (v : 𝔼 k) :
    HasFDerivAt (g hM p)
      (((ContinuousLinearMap.snd ℝ (𝔼 m) (𝔼 w)).comp ((fderiv ℝ (Tub.σ hM p).φ a).comp
        (ContinuousLinearMap.fst ℝ (𝔼 k) (𝔼 k)))).prod
        ((B hM p a).comp (ContinuousLinearMap.snd ℝ (𝔼 k) (𝔼 k)) +
          ((fderiv ℝ (B hM p) a).comp (ContinuousLinearMap.fst ℝ (𝔼 k) (𝔼 k))).flip v)) (a, v) := by
  have hφ := Tub.hasFDerivAt_σφ hM p ha.1
  have hB : HasFDerivAt (B hM p) (fderiv ℝ (B hM p) a) a :=
    (((contDiffOn_B hM p).differentiableOn (by simp)) a ha).differentiableAt
      ((isOpen_V hM p).mem_nhds ha) |>.hasFDerivAt
  have hfst : HasFDerivAt (Prod.fst : 𝔼 k × 𝔼 k → 𝔼 k)
      (ContinuousLinearMap.fst ℝ (𝔼 k) (𝔼 k)) (a, v) := hasFDerivAt_fst
  have h0 : HasFDerivAt (fun q : 𝔼 k × 𝔼 k => (Tub.σ hM p).φ q.1)
      ((fderiv ℝ (Tub.σ hM p).φ a).comp (ContinuousLinearMap.fst ℝ (𝔼 k) (𝔼 k))) (a, v) :=
    hφ.comp (a, v) hfst
  have hB' : HasFDerivAt (fun q : 𝔼 k × 𝔼 k => B hM p q.1)
      ((fderiv ℝ (B hM p) a).comp (ContinuousLinearMap.fst ℝ (𝔼 k) (𝔼 k))) (a, v) :=
    HasFDerivAt.comp (a, v) (g := B hM p) hB hfst
  exact h0.snd.prodMk (hB'.clm_apply hasFDerivAt_snd)

theorem fderiv_g_apply {a : 𝔼 k} (ha : a ∈ V hM p) (v u h : 𝔼 k) :
    fderiv ℝ (g hM p) (a, v) (u, h) =
      ((fderiv ℝ (Tub.σ hM p).φ a u).2, B hM p a h + fderiv ℝ (B hM p) a u v) := by
  rw [(hasFDerivAt_g hM p ha v).fderiv]
  rfl

/-- The derivative of `g` is surjective at every point of `V p × ℝᵏ`. -/
theorem surjective_fderiv_g {a : 𝔼 k} (ha : a ∈ V hM p) (v : 𝔼 k) :
    Surjective (fderiv ℝ (g hM p) (a, v)) := by
  rintro ⟨s, z⟩
  obtain ⟨u, hu⟩ := surjective_fderiv_σφ hM p ha.1 (0, s)
  obtain ⟨h, hh⟩ := surjective_B hM p ha (z - fderiv ℝ (B hM p) a u v)
  refine ⟨(u, h), ?_⟩
  rw [fderiv_g_apply hM p ha, hu, hh, sub_add_cancel]

end NormalAux

/-- **Problem 11, first part.** The normal bundle space `E ⊆ ℝᵏ × ℝᵏ` is a smooth manifold of
dimension `k` (a slice submanifold modelled on `ℝᵏ`). -/
theorem isSliceSubmanifold_normalBundle (hmk : m + w = k) :
    IsSliceSubmanifold 𝓘(ℝ, EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin k))
      (EuclideanSpace ℝ (Fin k)) (EuclideanSpace ℝ (Fin w) × EuclideanSpace ℝ (Fin m))
      (normalBundleSet hM) := by
  refine IsSliceSubmanifold.of_locally_preimage ?_ ?_
  · simp only [finrank_prod, finrank_euclideanSpace_fin]
    omega
  · rintro q ⟨hx, -⟩
    refine ⟨NormalAux.V hM ⟨q.1, hx⟩ ×ˢ univ, (NormalAux.isOpen_V hM _).prod isOpen_univ,
      ⟨NormalAux.mem_V hM _, mem_univ _⟩, NormalAux.g hM ⟨q.1, hx⟩, ?_, ?_, ?_⟩
    · rw [contMDiffOn_iff_contDiffOn]
      exact NormalAux.contDiffOn_g hM _
    · rintro y ⟨hy, -⟩
      exact NormalAux.mem_normalBundleSet_iff hM _ hy
    · rintro ⟨a, v⟩ ⟨ha, -⟩ -
      rw [mfderiv_eq_fderiv]
      exact NormalAux.surjective_fderiv_g hM _ ha v

/-! ### The map `(x, v) ↦ x + v` near the zero section -/

/-- The ε-neighbourhood of `M × 0` in the normal bundle, `{(x, v) ∈ E | ‖v‖ < ε}`. -/
def normalTube (ε : ℝ) : Set (normalBundleSet hM) := {q | ‖q.1.2‖ < ε}

theorem isOpen_normalTube (ε : ℝ) : IsOpen (normalTube hM ε) :=
  isOpen_lt (continuous_norm.comp (continuous_snd.comp continuous_subtype_val)) continuous_const

/-- `normalTube hM ε` as an open subset of the normal bundle (hence an open submanifold). -/
def normalTubeOpens (ε : ℝ) : TopologicalSpace.Opens (normalBundleSet hM) :=
  ⟨normalTube hM ε, isOpen_normalTube hM ε⟩

variable (M) in
/-- The ε-neighbourhood `N_ε = {y ∈ ℝᵏ | dist(y, M) < ε}` of `M`. -/
def eucTube (ε : ℝ) : Set (EuclideanSpace ℝ (Fin k)) := {y | Metric.infDist y M < ε}

variable (M) in
theorem isOpen_eucTube (ε : ℝ) : IsOpen (eucTube M ε) :=
  isOpen_lt (continuous_infDist_pt M) continuous_const

variable (M) in
/-- `eucTube M ε` as an open subset of `ℝᵏ`. -/
def eucTubeOpens (ε : ℝ) : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin k)) :=
  ⟨eucTube M ε, isOpen_eucTube M ε⟩

/-- The point `(x, 0)` of the normal bundle. -/
def normalZero (x : M) : normalBundleSet hM := ⟨(x.1, 0), x.2, fun _ _ => inner_zero_left _⟩

/-- The map `S (x, v) = x + v` on the normal bundle. -/
def normalSum (q : normalBundleSet hM) : EuclideanSpace ℝ (Fin k) := q.1.1 + q.1.2

variable (hmk : m + w = k)

theorem contMDiff_normalSum :
    letI := (isSliceSubmanifold_normalBundle hM hmk).chartedSpace
    ContMDiff 𝓘(ℝ, 𝔼 k) 𝓘(ℝ, 𝔼 k) ∞ (normalSum hM) := by
  let := (isSliceSubmanifold_normalBundle hM hmk).chartedSpace
  have := (isSliceSubmanifold_normalBundle hM hmk).isManifold
  have h2 : ContMDiff 𝓘(ℝ, 𝔼 k × 𝔼 k) 𝓘(ℝ, 𝔼 k) ∞ (fun q : 𝔼 k × 𝔼 k => q.1 + q.2) :=
    (contDiff_fst.add contDiff_snd).contMDiff
  exact h2.comp (isSliceSubmanifold_normalBundle hM hmk).contMDiff_val

theorem mfd_normalSum_apply (q : normalBundleSet hM) (z : 𝔼 k) :
    letI := (isSliceSubmanifold_normalBundle hM hmk).chartedSpace
    mfd 𝓘(ℝ, 𝔼 k) 𝓘(ℝ, 𝔼 k) (normalSum hM) q z =
      (mfd 𝓘(ℝ, 𝔼 k) 𝓘(ℝ, 𝔼 k × 𝔼 k) (Subtype.val : normalBundleSet hM → 𝔼 k × 𝔼 k) q z).1 +
      (mfd 𝓘(ℝ, 𝔼 k) 𝓘(ℝ, 𝔼 k × 𝔼 k) (Subtype.val : normalBundleSet hM → 𝔼 k × 𝔼 k) q z).2 := by
  let := (isSliceSubmanifold_normalBundle hM hmk).chartedSpace
  have := (isSliceSubmanifold_normalBundle hM hmk).isManifold
  have hval : MDifferentiableAt 𝓘(ℝ, 𝔼 k) 𝓘(ℝ, 𝔼 k × 𝔼 k)
      (Subtype.val : normalBundleSet hM → 𝔼 k × 𝔼 k) q :=
    (isSliceSubmanifold_normalBundle hM hmk).contMDiff_val.mdifferentiableAt (by simp)
  have hadd : HasFDerivAt (fun p : 𝔼 k × 𝔼 k => p.1 + p.2)
      (ContinuousLinearMap.fst ℝ (𝔼 k) (𝔼 k) + ContinuousLinearMap.snd ℝ (𝔼 k) (𝔼 k)) q.1 :=
    hasFDerivAt_fst.add hasFDerivAt_snd
  have h1 := HasMFDerivAt.mfd_eq (hadd.hasMFDerivAt.comp q (hasMFDerivAt_mfd hval))
  have h2 : mfd 𝓘(ℝ, 𝔼 k) 𝓘(ℝ, 𝔼 k) (normalSum hM) q =
      (ContinuousLinearMap.fst ℝ (𝔼 k) (𝔼 k) + ContinuousLinearMap.snd ℝ (𝔼 k) (𝔼 k)).comp
        (mfd 𝓘(ℝ, 𝔼 k) 𝓘(ℝ, 𝔼 k × 𝔼 k) (Subtype.val : normalBundleSet hM → 𝔼 k × 𝔼 k) q) :=
    h1
  rw [h2]
  rfl

/-- **The derivative of `S` at `(x, 0)` is injective.** The tangent space of `E` at `(x, 0)` is the
kernel of `dg`, i.e. consists of pairs `(u, h)` with `u ∈ TMₓ` and `h ⊥ TMₓ`; if `u + h = 0` then
`‖u‖² = -⟪h, u⟫ = 0`. -/
theorem injective_mfd_normalSum (x : M) :
    letI := (isSliceSubmanifold_normalBundle hM hmk).chartedSpace
    Injective (mfd 𝓘(ℝ, 𝔼 k) 𝓘(ℝ, 𝔼 k) (normalSum hM) (normalZero hM x)) := by
  have hN := isSliceSubmanifold_normalBundle hM hmk
  let := hN.chartedSpace
  have := hN.isManifold
  let := hM.chartedSpace
  have := hM.isManifold
  have hZ : finrank ℝ (𝔼 k) + finrank ℝ (𝔼 w × 𝔼 m) = finrank ℝ (𝔼 k × 𝔼 k) := by
    simp only [finrank_prod, finrank_euclideanSpace_fin]
    omega
  have hZM : finrank ℝ (𝔼 m) + finrank ℝ (𝔼 w) = finrank ℝ (𝔼 k) := by
    simp only [finrank_euclideanSpace_fin]
    omega
  -- the tangent space of `E` at `(x, 0)` is the kernel of `dg`
  have hker := hN.range_mfderiv_val_eq_ker hZ (normalZero hM x)
    ((NormalAux.isOpen_V hM x).prod isOpen_univ) ⟨NormalAux.mem_V hM x, mem_univ _⟩
    (g := NormalAux.g hM x)
    (contMDiffOn_iff_contDiffOn.2 (NormalAux.contDiffOn_g hM x))
    (fun y hy hyS => (NormalAux.mem_normalBundleSet_iff hM x hy.1).1 hyS)
    (by rw [mfderiv_eq_fderiv]; exact NormalAux.surjective_fderiv_g hM x (NormalAux.mem_V hM x) 0)
  rw [injective_iff_map_eq_zero]
  intro z hz
  rw [mfd_normalSum_apply hM hmk] at hz
  obtain ⟨uh, huh⟩ : ∃ uh, mfd 𝓘(ℝ, 𝔼 k) 𝓘(ℝ, 𝔼 k × 𝔼 k)
      (Subtype.val : normalBundleSet hM → 𝔼 k × 𝔼 k) (normalZero hM x) z = uh := ⟨_, rfl⟩
  rw [huh] at hz
  have hmem : uh ∈ LinearMap.ker (mfd 𝓘(ℝ, 𝔼 k × 𝔼 k) 𝓘(ℝ, 𝔼 w × 𝔼 m) (NormalAux.g hM x)
      (normalZero hM x).1 : (𝔼 k × 𝔼 k) →ₗ[ℝ] 𝔼 w × 𝔼 m) := by
    rw [← hker]
    exact ⟨z, huh⟩
  rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe] at hmem
  have hmem' : fderiv ℝ (NormalAux.g hM x) (x.1, 0) (uh.1, uh.2) = 0 := by
    rw [← mfderiv_eq_fderiv]
    exact hmem
  rw [NormalAux.fderiv_g_apply hM x (NormalAux.mem_V hM x), map_zero, add_zero] at hmem'
  have hu : (fderiv ℝ (Tub.σ hM x).φ x.1 uh.1).2 = 0 := congrArg Prod.fst hmem'
  have hh : NormalAux.B hM x x.1 uh.2 = 0 := congrArg Prod.snd hmem'
  -- `uh.1` is tangent to `M`
  have hg' : ContMDiffOn 𝓘(ℝ, 𝔼 k) 𝓘(ℝ, 𝔼 w) ∞ (fun a => ((Tub.σ hM x).φ a).2)
      (Tub.σ hM x).φ.source :=
    contMDiffOn_iff_contDiffOn.2 (contDiff_snd.comp_contDiffOn (Tub.contDiffOn_σφ hM x))
  have hd' : HasFDerivAt (fun a => ((Tub.σ hM x).φ a).2)
      ((ContinuousLinearMap.snd ℝ (𝔼 m) (𝔼 w)).comp (fderiv ℝ (Tub.σ hM x).φ x.1)) x.1 :=
    (Tub.hasFDerivAt_σφ hM x (Tub.mem_source hM x)).snd
  have huT : ∃ w' : 𝔼 m, mfderiv 𝓘(ℝ, 𝔼 m) 𝓘(ℝ, 𝔼 k) (Subtype.val : M → 𝔼 k) x w' = uh.1 := by
    rw [hM.mem_range_mfderiv_val_iff_of_local hZM x (Tub.σ hM x).φ.open_source
      (Tub.mem_source hM x) hg' (fun y hy hyM => ((Tub.σ hM x).slice y hy).1 hyM) ?_,
      mfderiv_eq_fderiv, hd'.fderiv]
    · exact hu
    · rw [mfderiv_eq_fderiv, hd'.fderiv]
      intro s
      obtain ⟨u, hu⟩ := NormalAux.surjective_fderiv_σφ hM x (Tub.mem_source hM x) (0, s)
      refine ⟨u, ?_⟩
      show ((fderiv ℝ (Tub.σ hM x).φ x.1) u).2 = s
      rw [hu]
  obtain ⟨w', hw'⟩ := huT
  -- `uh.2` is orthogonal to `TMₓ`
  have horth : ⟪uh.2, uh.1⟫ = 0 := by
    have hT := Tub.range_mfd_val hM x x (Tub.mem_source hM x)
    have h1 : uh.1 ∈ LinearMap.range ((mfd 𝓘(ℝ, 𝔼 m) 𝓘(ℝ, 𝔼 k) (Subtype.val : M → 𝔼 k) x :
        𝔼 m →L[ℝ] 𝔼 k) : 𝔼 m →ₗ[ℝ] 𝔼 k) := ⟨w', hw'⟩
    rw [hT] at h1
    obtain ⟨y, hy⟩ := h1
    rw [← hy, ContinuousLinearMap.coe_coe, ← Tub.A_inner]
    show ⟪NormalAux.B hM x x.1 uh.2, y⟫ = 0
    rw [hh, inner_zero_left]
  have h1 : uh.2 = -uh.1 := eq_neg_of_add_eq_zero_right hz
  rw [h1, inner_neg_left, neg_eq_zero, inner_self_eq_zero] at horth
  have huh0 : uh = 0 := Prod.ext horth (by rw [h1, horth, neg_zero]; rfl)
  have h0 : mfd 𝓘(ℝ, 𝔼 k) 𝓘(ℝ, 𝔼 k × 𝔼 k) (Subtype.val : normalBundleSet hM → 𝔼 k × 𝔼 k)
      (normalZero hM x) z = mfd 𝓘(ℝ, 𝔼 k) 𝓘(ℝ, 𝔼 k × 𝔼 k)
        (Subtype.val : normalBundleSet hM → 𝔼 k × 𝔼 k) (normalZero hM x) 0 := by
    rw [map_zero]
    exact huh.trans huh0
  exact injective_mfderiv_val hN (normalZero hM x) h0

theorem isInvertible_mfderiv_normalSum (x : M) :
    letI := (isSliceSubmanifold_normalBundle hM hmk).chartedSpace
    (mfderiv 𝓘(ℝ, 𝔼 k) 𝓘(ℝ, 𝔼 k) (normalSum hM) (normalZero hM x)).IsInvertible := by
  let := (isSliceSubmanifold_normalBundle hM hmk).chartedSpace
  have hinj := injective_mfd_normalSum hM hmk x
  obtain ⟨L, hL⟩ : ∃ L : 𝔼 k →L[ℝ] 𝔼 k,
      mfd 𝓘(ℝ, 𝔼 k) 𝓘(ℝ, 𝔼 k) (normalSum hM) (normalZero hM x) = L := ⟨_, rfl⟩
  rw [hL] at hinj
  have hsurj : Surjective (L : 𝔼 k →ₗ[ℝ] 𝔼 k) := LinearMap.injective_iff_surjective.1 hinj
  have he : ((ContinuousLinearEquiv.ofBijective L (LinearMap.ker_eq_bot.2 hinj)
      (LinearMap.range_eq_top.2 hsurj) : 𝔼 k ≃L[ℝ] 𝔼 k) : 𝔼 k →L[ℝ] 𝔼 k) =
      mfd 𝓘(ℝ, 𝔼 k) 𝓘(ℝ, 𝔼 k) (normalSum hM) (normalZero hM x) := by
    rw [ContinuousLinearEquiv.coe_ofBijective]
    exact hL.symm
  exact ⟨_, he⟩

include hmk in
/-- **Local injectivity.** Near `(x, 0)`, the map `(a, v) ↦ a + v` is injective on the normal
bundle (inverse function theorem). -/
theorem exists_radius_normalSum_injective (x : M) : ∃ r > 0, ∀ q₁ q₂ : normalBundleSet hM,
    ‖q₁.1.1 - x.1‖ < r → ‖q₁.1.2‖ < r → ‖q₂.1.1 - x.1‖ < r → ‖q₂.1.2‖ < r →
    q₁.1.1 + q₁.1.2 = q₂.1.1 + q₂.1.2 → q₁ = q₂ := by
  let := (isSliceSubmanifold_normalBundle hM hmk).chartedSpace
  have := (isSliceSubmanifold_normalBundle hM hmk).isManifold
  obtain ⟨Φ, hxΦ, hΦ⟩ := Milnor.ContMDiff.isLocalDiffeomorphAt_of_isInvertible_mfderiv
    (contMDiff_normalSum hM hmk) (by simp) (isInvertible_mfderiv_normalSum hM hmk x)
  obtain ⟨t, ht, hts⟩ := isOpen_induced_iff.1 Φ.open_source
  have hxt : (x.1, (0 : 𝔼 k)) ∈ t := by
    rw [← hts] at hxΦ
    exact hxΦ
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 ht _ hxt
  have hmem : ∀ q : normalBundleSet hM, ‖q.1.1 - x.1‖ < r → ‖q.1.2‖ < r → q ∈ Φ.source := by
    intro q ha hv
    rw [← hts]
    apply hball
    rw [Metric.mem_ball, Prod.dist_eq, dist_eq_norm, dist_eq_norm, sub_zero]
    exact max_lt ha hv
  refine ⟨r, hr, fun q₁ q₂ h1 h2 h3 h4 heq => ?_⟩
  have hq₁ := hmem q₁ h1 h2
  have hq₂ := hmem q₂ h3 h4
  refine Φ.toPartialEquiv.injOn hq₁ hq₂ ?_
  rw [← hΦ hq₁, ← hΦ hq₂]
  exact heq

include hmk in
/-- **Uniform injectivity radius.** For compact `M`, there is `ε > 0` such that `(a, v) ↦ a + v`
is injective on `{(a, v) ∈ E | ‖v‖ < ε}`. -/
theorem exists_eps_normalSum_injective (hMc : IsCompact M) (hne : M.Nonempty) :
    ∃ ε > 0, ∀ q₁ q₂ : normalBundleSet hM, ‖q₁.1.2‖ < ε → ‖q₂.1.2‖ < ε →
      q₁.1.1 + q₁.1.2 = q₂.1.1 + q₂.1.2 → q₁ = q₂ := by
  choose r hr hinj using exists_radius_normalSum_injective hM hmk
  obtain ⟨t, ht⟩ := hMc.elim_finite_subcover (fun x : M => ball x.1 (r x / 2))
    (fun _ => isOpen_ball) (fun a ha => mem_iUnion.2 ⟨⟨a, ha⟩, mem_ball_self (half_pos (hr _))⟩)
  have htne : t.Nonempty := by
    obtain ⟨a, ha⟩ := hne
    obtain ⟨i, hi, -⟩ := mem_iUnion₂.1 (ht ha)
    exact ⟨i, hi⟩
  refine ⟨t.inf' htne (fun x => r x / 4),
    (Finset.lt_inf'_iff htne).2 fun x _ => by have := hr x; positivity,
    fun q₁ q₂ h1 h2 heq => ?_⟩
  obtain ⟨hx₁, -⟩ := q₁.2
  obtain ⟨i, hi, hai⟩ := mem_iUnion₂.1 (ht hx₁)
  have hεi : t.inf' htne (fun x => r x / 4) ≤ r i / 4 := Finset.inf'_le _ hi
  rw [mem_ball, dist_eq_norm] at hai
  have hri := hr i
  refine hinj i q₁ q₂ (by linarith) (by linarith) ?_ (by linarith) heq
  have heq' : q₂.1.1 - i.1 = (q₁.1.1 - i.1) + (q₁.1.2 - q₂.1.2) := by
    rw [eq_sub_of_add_eq heq.symm]
    abel
  rw [heq']
  calc ‖(q₁.1.1 - i.1) + (q₁.1.2 - q₂.1.2)‖ ≤ ‖q₁.1.1 - i.1‖ + ‖q₁.1.2 - q₂.1.2‖ :=
        norm_add_le _ _
    _ ≤ ‖q₁.1.1 - i.1‖ + (‖q₁.1.2‖ + ‖q₂.1.2‖) := by gcongr; exact norm_sub_le _ _
    _ < r i := by linarith

end NormalBundle

section Tube

/-! ### The ε-neighbourhood theorem -/

variable {K m w : ℕ} {M : Set (EuclideanSpace ℝ (Fin (K + 1)))}
  (hM : IsSliceSubmanifold 𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1))) (EuclideanSpace ℝ (Fin m))
    (EuclideanSpace ℝ (Fin w)) M) (hMc : IsCompact M) (hne : M.Nonempty) (hmk : m + w = K + 1)

/-- The radius of Problem 11: the minimum of a uniform injectivity radius of `(x, v) ↦ x + v` and
the tubular radius of Chapter 6. -/
def normalε : ℝ := min (exists_eps_normalSum_injective hM hmk hMc hne).choose (Tub.tubε hM hMc hne)

theorem normalε_pos : 0 < normalε hM hMc hne hmk :=
  lt_min (exists_eps_normalSum_injective hM hmk hMc hne).choose_spec.1 (Tub.tubε_pos hM hMc hne)

theorem normalε_le_tubε : normalε hM hMc hne hmk ≤ Tub.tubε hM hMc hne := min_le_right _ _

theorem normalε_injective (q₁ q₂ : normalBundleSet hM) (h₁ : ‖q₁.1.2‖ < normalε hM hMc hne hmk)
    (h₂ : ‖q₂.1.2‖ < normalε hM hMc hne hmk) (h : q₁.1.1 + q₁.1.2 = q₂.1.1 + q₂.1.2) :
    q₁ = q₂ :=
  (exists_eps_normalSum_injective hM hmk hMc hne).choose_spec.2 q₁ q₂
    (h₁.trans_le (min_le_left _ _)) (h₂.trans_le (min_le_left _ _)) h

theorem normalSum_infDist_le {x : 𝔼 (K + 1)} (hx : x ∈ M) (v : 𝔼 (K + 1)) :
    infDist (x + v) M ≤ ‖v‖ := by
  have h := infDist_le_dist_of_mem (x := x + v) hx
  rwa [dist_eq_norm, add_sub_cancel_left] at h

/-- `(r y, y - r y)` lies in the normal bundle for `y` in the tubular neighbourhood. -/
theorem tubr_mem_normalBundleSet {y : 𝔼 (K + 1)} (hy : infDist y M < Tub.tubε hM hMc hne) :
    ((Tub.tubr hM hMc hne y).1, y - (Tub.tubr hM hMc hne y).1) ∈ normalBundleSet hM :=
  ⟨(Tub.tubr hM hMc hne y).2, fun t ht => (Tub.tubr_spec hM hMc hne).2.2.2.2.1 y hy t ht⟩

/-- **The retraction of Problem 12**: `r (x + v) = x` for `(x, v)` in the ε-neighbourhood of
`M × 0` in the normal bundle. -/
theorem normalRetraction_eq (q : normalBundleSet hM)
    (hq : q ∈ normalTube hM (normalε hM hMc hne hmk)) :
    (Tub.tubr hM hMc hne (q.1.1 + q.1.2) : EuclideanSpace ℝ (Fin (K + 1))) = q.1.1 := by
  have hq' : ‖q.1.2‖ < normalε hM hMc hne hmk := hq
  obtain ⟨hx, -⟩ := q.2
  have hdist := normalSum_infDist_le hx q.1.2
  have hyε : infDist (q.1.1 + q.1.2) M < Tub.tubε hM hMc hne :=
    hdist.trans_lt (hq'.trans_le (normalε_le_tubε hM hMc hne hmk))
  have hr : ‖(q.1.1 + q.1.2) - (Tub.tubr hM hMc hne (q.1.1 + q.1.2)).1‖ =
      infDist (q.1.1 + q.1.2) M := by
    rw [← dist_eq_norm]
    exact (Tub.tubr_spec hM hMc hne).1 _
  have h := normalε_injective hM hMc hne hmk ⟨_, tubr_mem_normalBundleSet hM hMc hne hyε⟩ q
    (by show ‖_ - _‖ < _; rw [hr]; exact hdist.trans_lt hq') hq' (add_sub_cancel _ _)
  exact congrArg (fun q : normalBundleSet hM => q.1.1) h

/-- **Problem 11, second part**, with the explicit radius `normalε`. The inverse of `Φ` is
`y ↦ (r y, y - r y)`, `r = Tub.tubr` the nearest-point retraction. -/
theorem exists_diffeomorph_normalε :
    letI := (isSliceSubmanifold_normalBundle hM hmk).chartedSpace
    ∃ Φ : Diffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1))) 𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1)))
        (normalTubeOpens hM (normalε hM hMc hne hmk)) (eucTubeOpens M (normalε hM hMc hne hmk)) ∞,
      ∀ q, (Φ q).1 = q.1.1.1 + q.1.1.2 := by
  let := (isSliceSubmanifold_normalBundle hM hmk).chartedSpace
  have := (isSliceSubmanifold_normalBundle hM hmk).isManifold
  have hε := normalε_le_tubε hM hMc hne hmk
  -- the forward map `(x, v) ↦ x + v`
  let F : normalTubeOpens hM (normalε hM hMc hne hmk) → eucTubeOpens M (normalε hM hMc hne hmk) :=
    fun q => ⟨q.1.1.1 + q.1.1.2, (normalSum_infDist_le q.1.2.fst q.1.1.2).trans_lt q.2⟩
  -- the inverse map `y ↦ (r y, y - r y)`
  have hyN : ∀ y : eucTubeOpens M (normalε hM hMc hne hmk),
      infDist y.1 M < Tub.tubε hM hMc hne := fun y => lt_of_lt_of_le y.2 hε
  have hGmem : ∀ y : eucTubeOpens M (normalε hM hMc hne hmk),
      (⟨_, tubr_mem_normalBundleSet hM hMc hne (hyN y)⟩ : normalBundleSet hM) ∈
        normalTubeOpens hM (normalε hM hMc hne hmk) := by
    intro y
    show ‖y.1 - (Tub.tubr hM hMc hne y.1).1‖ < _
    rw [← dist_eq_norm, (Tub.tubr_spec hM hMc hne).1]
    exact y.2
  let G : eucTubeOpens M (normalε hM hMc hne hmk) → normalTubeOpens hM (normalε hM hMc hne hmk) :=
    fun y => ⟨⟨_, tubr_mem_normalBundleSet hM hMc hne (hyN y)⟩, hGmem y⟩
  have hFsmooth : ContMDiff 𝓘(ℝ, 𝔼 (K + 1)) 𝓘(ℝ, 𝔼 (K + 1)) ∞ F :=
    (ContMDiff.subtypeVal_comp_iff (eucTubeOpens M (normalε hM hMc hne hmk)) F).1
      ((contMDiff_normalSum hM hmk).comp contMDiff_subtype_val)
  have hr : ContMDiff 𝓘(ℝ, 𝔼 (K + 1)) 𝓘(ℝ, 𝔼 (K + 1)) ∞
      (fun y : eucTubeOpens M (normalε hM hMc hne hmk) => (Tub.tubr hM hMc hne y.1).1) := by
    intro y
    have h := (Tub.tubr_spec hM hMc hne).2.2.2.1 y.1 (hyN y)
    rw [← contMDiffAt_iff_contDiffAt] at h
    exact contMDiffAt_subtype_iff.2 h
  have hpair : ContMDiff 𝓘(ℝ, 𝔼 (K + 1)) 𝓘(ℝ, 𝔼 (K + 1) × 𝔼 (K + 1)) ∞
      (fun y : eucTubeOpens M (normalε hM hMc hne hmk) =>
        ((Tub.tubr hM hMc hne y.1).1, y.1 - (Tub.tubr hM hMc hne y.1).1)) :=
    hr.prodMk_space (contMDiff_subtype_val.sub hr)
  have hGsmooth : ContMDiff 𝓘(ℝ, 𝔼 (K + 1)) 𝓘(ℝ, 𝔼 (K + 1)) ∞ G :=
    (ContMDiff.subtypeVal_comp_iff (normalTubeOpens hM (normalε hM hMc hne hmk)) G).1
      ((isSliceSubmanifold_normalBundle hM hmk).contMDiff_codRestrict hpair
        fun y => tubr_mem_normalBundleSet hM hMc hne (hyN y))
  refine ⟨
    { toFun := F
      invFun := G
      left_inv := ?_
      right_inv := ?_
      contMDiff_toFun := hFsmooth
      contMDiff_invFun := hGsmooth }, fun q => rfl⟩
  · intro q
    have h := normalRetraction_eq hM hMc hne hmk q.1 q.2
    refine Subtype.ext (Subtype.ext (Prod.ext h ?_))
    show (q.1.1.1 + q.1.1.2) - (Tub.tubr hM hMc hne (q.1.1.1 + q.1.1.2)).1 = q.1.1.2
    rw [h, add_sub_cancel_left]
  · intro y
    exact Subtype.ext (add_sub_cancel _ _)

include hMc hne in
/-- **Problem 11, second part.** For some `ε > 0`, `(x, v) ↦ x + v` is a diffeomorphism from the
ε-neighbourhood of `M × 0` in the normal bundle onto the ε-neighbourhood of `M`. -/
theorem exists_normalTube_diffeomorph :
    letI := (isSliceSubmanifold_normalBundle hM hmk).chartedSpace
    ∃ ε > 0, ∃ Φ : Diffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1)))
        𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1))) (normalTubeOpens hM ε) (eucTubeOpens M ε) ∞,
      ∀ q, (Φ q).1 = q.1.1.1 + q.1.1.2 :=
  ⟨normalε hM hMc hne hmk, normalε_pos hM hMc hne hmk, exists_diffeomorph_normalε hM hMc hne hmk⟩

end Tube

end Problems

end Milnor
