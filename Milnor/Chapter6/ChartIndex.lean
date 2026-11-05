import Milnor.Chapter6.PoincareHopf
import Milnor.Chapter6.Nondegenerate

/-!
# The chart definition of the index, and Milnor's Lemma 5 (pp. 33 and 37)

Milnor defines the index of a zero `q` of a vector field `v` on a manifold `M ⊆ ℝᴷ⁺¹` **through a
parametrization** (p. 33): a local parametrization `ψ : Ω → M` of a neighbourhood of `q` in `M`,
with `Ω ⊆ ℝⁿ` open and `ψ u₀ = q`, carries `v` back to a vector field `ψ* v` on `Ω`, and the index
of `v` at `q` is *defined* to be the index of `ψ* v` at `u₀`.  His Lemma 1 of §6 — the invariance
of the index under a diffeomorphism, here `Milnor.Sphere.index_eq_of_diffeo` — makes this
independent of the chosen parametrization.

This development instead *defines* the index of `v` at `q` as the index at `q` of the field
`w x = v (r x) + (x - r x)` extended to a tubular neighbourhood of `M`, where `r` is the
nearest-point retraction (`Milnor.Tub.indexN`; this is the field that Milnor himself uses in his
proof of the Poincaré–Hopf theorem on p. 38).  The present file formalizes both the chart
definition (`Milnor.Tub.chartIndexN`) and the agreement of the two definitions at a non-degenerate
zero (`Milnor.Tub.chartIndexN_eq_indexN`).

The bridge between the two is Milnor's **Lemma 5** (p. 37): at a zero of `v` the derivative of `v`
carries the tangent space into itself (`Milnor.Tub.dvr_mem_tanN`, `Milnor.Tub.mfd_mem_tanN`).  With
it, the derivative at `q` of the extended field is `dv_q ∘ P + (id - P)` with `P = dr_q` the
orthogonal projection onto the tangent space (`Milnor.Tub.fderiv_w₀`,
`Milnor.Tub.dret_apply_of_mem_tanN`, `Milnor.Tub.ker_dret`), so its determinant is the determinant
of `dv_q` restricted to the tangent space (`Milnor.Tub.det_fderiv_w₀`); the same determinant
computes the derivative of the pulled-back field in a parametrization, and Milnor's Lemma 4
(`Milnor.Sphere.index_eq_sgn_det`) turns both indices into its sign.

Only the non-degenerate case of the agreement is proved, which is what Milnor's Lemma 5 gives and
what the rest of the book uses.  For an arbitrary isolated zero the two indices are degrees of maps
of spheres of *different* dimensions — `S^K` for the extended field, `Sⁿ⁻¹` for the pulled-back one
— so no invariance-under-diffeomorphism argument can compare them directly: one would first have to
prove that the index of a field of the shape `(u, y) ↦ (ṽ u, y)` on `ℝⁿ × ℝᴷ⁺¹⁻ⁿ` is the index of
`ṽ`, a product formula for the degree which this development does not have.

Throughout, `N` is compact, because the tubular neighbourhood and the retraction `r` are available
here only for a compact submanifold; Milnor's Lemma 5 itself needs no compactness.

Dimensions: `N` is an `n`-dimensional submanifold of `ℝᴷ⁺¹`, and both indices are degrees of maps
of spheres, so the ambient index needs `K ≥ 1` and the index computed in an `n`-dimensional
parametrization needs `n ≥ 2` (the index of a field on `ℝⁿ` is a degree on `Sⁿ⁻¹`, and
`Milnor.Sphere.deg` is available only for positive-dimensional spheres).  Accordingly `n` is
written `d + 1` throughout, and the chart statements carry the hypothesis `0 < d`.
-/

open Set Filter Topology Function Module Metric
open scoped ContDiff Manifold RealInnerProductSpace

noncomputable section

namespace Milnor

/-! ### Two lemmas of linear algebra -/

/-- An endomorphism of a finite-dimensional real vector space is bijective exactly when its
determinant is nonzero. -/
theorem bijective_iff_det_ne_zero {V : Type*} [AddCommGroup V] [Module ℝ V]
    [FiniteDimensional ℝ V] (L : V →ₗ[ℝ] V) : Bijective L ↔ LinearMap.det L ≠ 0 := by
  constructor
  · intro h
    exact isUnit_iff_ne_zero.1 (LinearEquiv.ofBijective L h).isUnit_det'
  · intro h
    have hker : LinearMap.ker L = ⊥ := by
      by_contra hk
      exact h (LinearMap.det_eq_zero_iff_ker_ne_bot.2 hk)
    have hinj : Injective L := LinearMap.ker_eq_bot.1 hker
    exact ⟨hinj, LinearMap.injective_iff_surjective.1 hinj⟩

/-- **The determinant of a map that is the identity on the orthogonal complement.**  If `L`
carries a subspace `T` into itself and is the identity on `Tᗮ`, then `det L` is the determinant of
the restriction of `L` to `T`. -/
theorem det_eq_det_restrict {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] {T : Submodule ℝ V} {L : V →ₗ[ℝ] V} (hLT : ∀ t ∈ T, L t ∈ T)
    (hLC : ∀ c ∈ Tᗮ, L c = c) : LinearMap.det L = LinearMap.det (L.restrict hLT) := by
  classical
  set Ψ := T.prodEquivOfIsCompl Tᗮ T.isCompl_orthogonal with hΨ
  have hkey : (Ψ.symm : V →ₗ[ℝ] (T × Tᗮ)) ∘ₗ L ∘ₗ (Ψ : (T × Tᗮ) →ₗ[ℝ] V)
      = LinearMap.prodMap (L.restrict hLT) LinearMap.id := by
    refine LinearMap.ext fun x => ?_
    have h1 : L (Ψ x) = Ψ (L.restrict hLT x.1, x.2) := by
      rw [hΨ, Submodule.coe_prodEquivOfIsCompl', Submodule.coe_prodEquivOfIsCompl', map_add,
        hLC _ x.2.2]
      rfl
    show Ψ.symm (L (Ψ x)) = _
    rw [h1, LinearEquiv.symm_apply_apply]
    rfl
  have hconj := LinearMap.det_conj L Ψ.symm
  rw [LinearEquiv.symm_symm] at hconj
  rw [← hconj, hkey, LinearMap.det_prodMap, LinearMap.det_id, mul_one]

/-- The derivative of `F` along the line `s ↦ x + s • c`, at `s = 0`. -/
theorem hasDerivAt_line {E' F' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    [NormedAddCommGroup F'] [NormedSpace ℝ F'] {F : E' → F'} {L : E' →L[ℝ] F'} {x : E'}
    (hF : HasFDerivAt F L x) (c : E') : HasDerivAt (fun s : ℝ => F (x + s • c)) (L c) 0 := by
  have h1 : HasDerivAt (fun s : ℝ => x + s • c) c 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const c).const_add x
  have h2 : HasFDerivAt F L (x + (0 : ℝ) • c) := by simpa using hF
  simpa [Function.comp_def] using h2.comp_hasDerivAt (0 : ℝ) h1

namespace Tub

variable {K d m : ℕ}

local notation "𝔼" => EuclideanSpace ℝ (Fin (K + 1))
local notation "𝔻" => EuclideanSpace ℝ (Fin (d + 1))
local notation "𝕄" => EuclideanSpace ℝ (Fin m)

variable {N : Set (EuclideanSpace ℝ (Fin (K + 1)))}
  (hN : IsSliceSubmanifold 𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1))) (EuclideanSpace ℝ (Fin (d + 1)))
    (EuclideanSpace ℝ (Fin m)) N) (hNc : IsCompact N) (hne : N.Nonempty)

/-! ### The tangent space, and the derivative of the retraction -/

/-- The tangent space `T_q N ⊆ ℝᴷ⁺¹`: the range of the derivative at `q` of the inclusion
`N → ℝᴷ⁺¹`.  This is the subspace occurring in the ε-neighbourhood theorem
`Milnor.Tub.tubr_spec`. -/
def tanN (q : N) : Submodule ℝ 𝔼 :=
  letI := hN.chartedSpace
  LinearMap.range ((mfd 𝓘(ℝ, 𝔻) 𝓘(ℝ, 𝔼) (Subtype.val : N → 𝔼) q : 𝔻 →L[ℝ] 𝔼) : 𝔻 →ₗ[ℝ] 𝔼)

/-- `v` is a **tangent** vector field on `N`: `v q` lies in the tangent space at `q`.  This is the
hypothesis `hvT` of `Milnor.Tub.poincare_hopf`. -/
def IsTangent (v : N → 𝔼) : Prop := ∀ q : N, v q ∈ tanN hN q

/-- Points of `N` lie in the tubular neighbourhood. -/
theorem mem_Nε_of_mem {x : 𝔼} (hx : x ∈ N) : x ∈ Nε hN hNc hne :=
  X_subset_Nε hN hNc hne (N_subset_X hN hNc hne hx)

/-- The retraction fixes the points of `N`. -/
theorem tubr_val (q : N) : tubr hN hNc hne q.1 = q :=
  Subtype.ext ((tubr_spec hN hNc hne).2.2.1 q.1 q.2)

/-- The retraction is smooth at each point of the tubular neighbourhood. -/
theorem contDiffAt_tubr {x : 𝔼} (hx : x ∈ Nε hN hNc hne) :
    ContDiffAt ℝ ∞ (fun y => (tubr hN hNc hne y).1) x :=
  (tubr_spec hN hNc hne).2.2.2.1 x hx

/-- The retraction is smooth on the tubular neighbourhood. -/
theorem contDiffOn_tubr : ContDiffOn ℝ ∞ (fun y => (tubr hN hNc hne y).1) (Nε hN hNc hne) :=
  fun _x hx => (contDiffAt_tubr hN hNc hne hx).contDiffWithinAt

/-- The retraction has a derivative at each point of the tubular neighbourhood. -/
theorem hasFDerivAt_tubr {x : 𝔼} (hx : x ∈ Nε hN hNc hne) :
    HasFDerivAt (fun y => (tubr hN hNc hne y).1)
      (fderiv ℝ (fun y => (tubr hN hNc hne y).1) x) x :=
  ((contDiffAt_tubr hN hNc hne hx).differentiableAt (by simp)).hasFDerivAt

/-- **Milnor's `dr_q`**: the derivative at a point `q` of `N` of the nearest-point retraction,
read as a linear map of the ambient space `ℝᴷ⁺¹`. -/
def dret (q : N) : 𝔼 →L[ℝ] 𝔼 := fderiv ℝ (fun y => (tubr hN hNc hne y).1) q.1

/-- `dr_q` takes values in the tangent space at `q`. -/
theorem dret_mem_tanN (q : N) (w : 𝔼) : dret hN hNc hne q w ∈ tanN hN q := by
  letI := hN.chartedSpace
  have h := (tubr_spec hN hNc hne).2.2.2.2.2.1 q.1 (mem_Nε_of_mem hN hNc hne q.2) w
  rwa [tubr_val hN hNc hne q] at h

/-- `dr_q` composed with the derivative of the inclusion is the derivative of the inclusion:
`r ∘ ι = ι`. -/
theorem dret_comp_mfd_val (q : N) :
    letI := hN.chartedSpace
    (dret hN hNc hne q).comp (mfd 𝓘(ℝ, 𝔻) 𝓘(ℝ, 𝔼) (Subtype.val : N → 𝔼) q) =
      mfd 𝓘(ℝ, 𝔻) 𝓘(ℝ, 𝔼) (Subtype.val : N → 𝔼) q := by
  letI := hN.chartedSpace
  haveI := hN.isManifold
  have hvalq : MDifferentiableAt 𝓘(ℝ, 𝔻) 𝓘(ℝ, 𝔼) (Subtype.val : N → 𝔼) q :=
    (hN.contMDiff_val q).mdifferentiableAt (by simp)
  have hρ : MDifferentiableAt 𝓘(ℝ, 𝔼) 𝓘(ℝ, 𝔼) (fun y => (tubr hN hNc hne y).1) q.1 :=
    ((contDiffAt_tubr hN hNc hne (mem_Nε_of_mem hN hNc hne q.2)).differentiableAt
      (by simp)).mdifferentiableAt
  have hcomp := mfderiv_comp (I' := 𝓘(ℝ, 𝔼)) q hρ hvalq
  have heq : ((fun y => (tubr hN hNc hne y).1) ∘ (Subtype.val : N → 𝔼)) = Subtype.val := by
    funext p; exact (tubr_spec hN hNc hne).2.2.1 p.1 p.2
  rw [heq, mfderiv_eq_fderiv] at hcomp
  exact hcomp.symm

/-- `dr_q` is the identity on the tangent space at `q`. -/
theorem dret_apply_of_mem_tanN (q : N) {t : 𝔼} (ht : t ∈ tanN hN q) :
    dret hN hNc hne q t = t := by
  letI := hN.chartedSpace
  obtain ⟨a, rfl⟩ := ht
  have h := congrArg (fun L : 𝔻 →L[ℝ] 𝔼 => L a) (dret_comp_mfd_val hN hNc hne q)
  simpa using h

/-- The image of `dr_q` is exactly the tangent space at `q`. -/
theorem range_dret (q : N) :
    LinearMap.range ((dret hN hNc hne q : 𝔼 →L[ℝ] 𝔼) : 𝔼 →ₗ[ℝ] 𝔼) = tanN hN q := by
  refine le_antisymm ?_ ?_
  · rintro w ⟨a, rfl⟩
    exact dret_mem_tanN hN hNc hne q a
  · intro t ht
    exact ⟨t, dret_apply_of_mem_tanN hN hNc hne q ht⟩

/-- `dr_q` is a projection: `dr_q ∘ dr_q = dr_q`. -/
theorem dret_dret (q : N) (w : 𝔼) :
    dret hN hNc hne q (dret hN hNc hne q w) = dret hN hNc hne q w :=
  dret_apply_of_mem_tanN hN hNc hne q (dret_mem_tanN hN hNc hne q w)

/-- `dr_q` kills the normal space at `q`: the retraction is constant along the short normal
segments. -/
theorem dret_apply_of_mem_orthogonal (q : N) {c : 𝔼} (hc : c ∈ (tanN hN q)ᗮ) :
    dret hN hNc hne q c = 0 := by
  letI := hN.chartedSpace
  have hnorm : ∀ w ∈ LinearMap.range ((mfd 𝓘(ℝ, 𝔻) 𝓘(ℝ, 𝔼) (Subtype.val : N → 𝔼)
      ⟨q.1, q.2⟩ : 𝔻 →L[ℝ] 𝔼) : 𝔻 →ₗ[ℝ] 𝔼), ⟪c, w⟫ = 0 := by
    intro w hw
    rw [real_inner_comm]
    exact hc w hw
  have hG := (tubr_spec hN hNc hne).2.2.2.2.2.2 q.1 q.2 c hnorm
  have h1 : HasDerivAt (fun s : ℝ => (tubr hN hNc hne (q.1 + s • c)).1)
      (dret hN hNc hne q c) 0 :=
    hasDerivAt_line (hasFDerivAt_tubr hN hNc hne (mem_Nε_of_mem hN hNc hne q.2)) c
  have h2 : HasDerivAt (fun s : ℝ => (tubr hN hNc hne (q.1 + s • c)).1) 0 0 :=
    (hasDerivAt_const (0 : ℝ) q.1).congr_of_eventuallyEq hG
  exact h1.unique h2

/-- The kernel of `dr_q` is exactly the normal space: `dr_q` is the orthogonal projection of
`ℝᴷ⁺¹` onto the tangent space `T_q N`. -/
theorem ker_dret (q : N) :
    LinearMap.ker ((dret hN hNc hne q : 𝔼 →L[ℝ] 𝔼) : 𝔼 →ₗ[ℝ] 𝔼) = (tanN hN q)ᗮ := by
  refine le_antisymm (fun x hx => ?_) (fun c hc => ?_)
  · have hx0 : dret hN hNc hne q x = 0 := hx
    have hsup : x ∈ tanN hN q ⊔ (tanN hN q)ᗮ := by
      rw [(tanN hN q).isCompl_orthogonal.sup_eq_top]; trivial
    obtain ⟨t, ht, c, hc, rfl⟩ := Submodule.mem_sup.1 hsup
    have ht0 : t = 0 := by
      have := dret_apply_of_mem_tanN hN hNc hne q ht
      rw [map_add, this, dret_apply_of_mem_orthogonal hN hNc hne q hc, add_zero] at hx0
      exact hx0
    rw [ht0, zero_add]
    exact hc
  · exact dret_apply_of_mem_orthogonal hN hNc hne q hc

/-! ### Milnor's Lemma 5 -/

section field

variable {v : N → EuclideanSpace ℝ (Fin (K + 1))}

/-- The field `v` carried to the tubular neighbourhood by the retraction, `x ↦ v (r x)`, is the
first summand of `Milnor.Tub.w₀`. -/
theorem vr_eq (x : 𝔼) :
    v (tubr hN hNc hne x) = w₀ hN hNc hne v x - (x - (tubr hN hNc hne x).1) := by
  unfold w₀; abel

/-- `x ↦ v (r x)` is smooth on the tubular neighbourhood. -/
theorem contDiffAt_vr (hv : letI := hN.chartedSpace; ContMDiff 𝓘(ℝ, 𝔻) 𝓘(ℝ, 𝔼) ∞ v)
    {x : 𝔼} (hx : x ∈ Nε hN hNc hne) :
    ContDiffAt ℝ ∞ (fun y => v (tubr hN hNc hne y)) x := by
  have h1 : ContDiffAt ℝ ∞ (w₀ hN hNc hne v) x := by
    rw [← contMDiffAt_iff_contDiffAt]
    exact (contMDiffOn_w₀ hN hNc hne hv).contMDiffAt ((isOpen_Nε hN hNc hne).mem_nhds hx)
  have h2 : ContDiffAt ℝ ∞ (fun y : 𝔼 => y - (tubr hN hNc hne y).1) x :=
    contDiffAt_id.sub (contDiffAt_tubr hN hNc hne hx)
  have heq : (fun y => v (tubr hN hNc hne y))
      = fun y => w₀ hN hNc hne v y - (y - (tubr hN hNc hne y).1) :=
    funext (vr_eq hN hNc hne)
  rw [heq]
  exact h1.sub h2

/-- **The derivative of `v` at `q`**, read through the retraction: the derivative at `q` of the
map `x ↦ v (r x)` of the ambient space.  On the tangent space it agrees with the intrinsic
derivative of `v : N → ℝᴷ⁺¹` (`Milnor.Tub.mfd_eq_dvr_comp`). -/
def dvr (v : N → 𝔼) (q : N) : 𝔼 →L[ℝ] 𝔼 := fderiv ℝ (fun x => v (tubr hN hNc hne x)) q.1

/-- The derivative of `x ↦ v (r x)`. -/
theorem hasFDerivAt_vr (hv : letI := hN.chartedSpace; ContMDiff 𝓘(ℝ, 𝔻) 𝓘(ℝ, 𝔼) ∞ v) (q : N) :
    HasFDerivAt (fun x => v (tubr hN hNc hne x)) (dvr hN hNc hne v q) q.1 :=
  ((contDiffAt_vr hN hNc hne hv (mem_Nε_of_mem hN hNc hne q.2)).differentiableAt
    (by simp)).hasFDerivAt

/-- The intrinsic derivative of `v : N → ℝᴷ⁺¹` is `dv_q` composed with the derivative of the
inclusion. -/
theorem mfd_eq_dvr_comp (hv : letI := hN.chartedSpace; ContMDiff 𝓘(ℝ, 𝔻) 𝓘(ℝ, 𝔼) ∞ v) (q : N) :
    letI := hN.chartedSpace
    mfd 𝓘(ℝ, 𝔻) 𝓘(ℝ, 𝔼) v q =
      (dvr hN hNc hne v q).comp (mfd 𝓘(ℝ, 𝔻) 𝓘(ℝ, 𝔼) (Subtype.val : N → 𝔼) q) := by
  letI := hN.chartedSpace
  haveI := hN.isManifold
  have hvalq : MDifferentiableAt 𝓘(ℝ, 𝔻) 𝓘(ℝ, 𝔼) (Subtype.val : N → 𝔼) q :=
    (hN.contMDiff_val q).mdifferentiableAt (by simp)
  have hY : MDifferentiableAt 𝓘(ℝ, 𝔼) 𝓘(ℝ, 𝔼) (fun x => v (tubr hN hNc hne x)) q.1 :=
    ((contDiffAt_vr hN hNc hne hv (mem_Nε_of_mem hN hNc hne q.2)).differentiableAt
      (by simp)).mdifferentiableAt
  have hcomp := mfderiv_comp (I' := 𝓘(ℝ, 𝔼)) q hY hvalq
  have heq : ((fun x => v (tubr hN hNc hne x)) ∘ (Subtype.val : N → 𝔼)) = v := by
    funext p; rw [Function.comp_apply, tubr_val hN hNc hne p]
  rw [heq, mfderiv_eq_fderiv] at hcomp
  exact hcomp

/-- **Milnor's Lemma 5** (p. 37).  Let `v` be a smooth tangent vector field on `N` with `v q = 0`.
Then the derivative of `v` at `q` carries the tangent space `T_q N` into itself.  Here the
derivative is read through the retraction, as the derivative at `q` of the ambient map
`x ↦ v (r x)`; the hypothesis `v q = 0` is essential — without it the derivative of `v` at `q`
has no invariant meaning as an endomorphism of `T_q N`, and indeed
`d(v ∘ r)_q` need not take values in `T_q N`. -/
theorem dvr_mem_tanN (hv : letI := hN.chartedSpace; ContMDiff 𝓘(ℝ, 𝔻) 𝓘(ℝ, 𝔼) ∞ v)
    (hvT : IsTangent hN v) {q : N} (hvq : v q = 0) (a : 𝔼) :
    dvr hN hNc hne v q a ∈ tanN hN q := by
  letI := hN.chartedSpace
  have hq : q.1 ∈ Nε hN hNc hne := mem_Nε_of_mem hN hNc hne q.2
  have hρq : (tubr hN hNc hne q.1).1 = q.1 := (tubr_spec hN hNc hne).2.2.1 q.1 q.2
  -- `id - dr_{r x}` kills the tangent space at `r x`, so it kills `v (r x)`
  have hvanish : ∀ x ∈ Nε hN hNc hne,
      (ContinuousLinearMap.id ℝ 𝔼 - dret hN hNc hne (tubr hN hNc hne x))
        (v (tubr hN hNc hne x)) = 0 := by
    intro x _
    simp only [sub_apply, ContinuousLinearMap.id_apply,
      dret_apply_of_mem_tanN hN hNc hne _ (hvT (tubr hN hNc hne x)), sub_self]
  -- the family `x ↦ id - dr_{r x}` is smooth near `q`
  have hfd : ContDiffOn ℝ ∞ (fderiv ℝ (fun y => (tubr hN hNc hne y).1)) (Nε hN hNc hne) :=
    (contDiffOn_tubr hN hNc hne).fderiv_of_isOpen (isOpen_Nε hN hNc hne) (by simp)
  have hΛd : DifferentiableAt ℝ
      (fun x => ContinuousLinearMap.id ℝ 𝔼 - dret hN hNc hne (tubr hN hNc hne x)) q.1 := by
    have h1 : ContDiffAt ℝ ∞ (fderiv ℝ (fun y => (tubr hN hNc hne y).1))
        ((tubr hN hNc hne q.1).1) := by
      rw [hρq]
      exact hfd.contDiffAt ((isOpen_Nε hN hNc hne).mem_nhds hq)
    have h2 : ContDiffAt ℝ ∞ (fun y => (tubr hN hNc hne y).1) q.1 := contDiffAt_tubr hN hNc hne hq
    have h3 : ContDiffAt ℝ ∞
        (fun x => fderiv ℝ (fun y => (tubr hN hNc hne y).1) ((tubr hN hNc hne x).1)) q.1 :=
      h1.comp q.1 h2
    exact (contDiffAt_const.sub h3).differentiableAt (by simp)
  -- differentiate the identically vanishing map `x ↦ (id - dr_{r x}) (v (r x))`
  have hprod := hΛd.hasFDerivAt.clm_apply (hasFDerivAt_vr hN hNc hne hv q)
  have hzero : HasFDerivAt (fun x => (ContinuousLinearMap.id ℝ 𝔼 -
      dret hN hNc hne (tubr hN hNc hne x)) (v (tubr hN hNc hne x)))
      (0 : EuclideanSpace ℝ (Fin (K + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (K + 1))) q.1 := by
    refine (hasFDerivAt_const (0 : 𝔼) q.1).congr_of_eventuallyEq ?_
    filter_upwards [(isOpen_Nε hN hNc hne).mem_nhds hq] with y hy
    exact hvanish y hy
  have hvq0 : v (tubr hN hNc hne q.1) = 0 := by rw [tubr_val hN hNc hne q]; exact hvq
  simp only [hvq0, map_zero, add_zero] at hprod
  have hcomp := hprod.unique hzero
  rw [tubr_val hN hNc hne q] at hcomp
  have hkey := congrArg (fun L : 𝔼 →L[ℝ] 𝔼 => L a) hcomp
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, zero_apply,
    sub_apply, ContinuousLinearMap.id_apply] at hkey
  have hfix : dret hN hNc hne q (dvr hN hNc hne v q a) = dvr hN hNc hne v q a :=
    (sub_eq_zero.1 hkey).symm
  rw [← hfix]
  exact dret_mem_tanN hN hNc hne q _

include hNc hne in
/-- **Milnor's Lemma 5, intrinsic form.**  At a zero `q` of a smooth tangent field `v` on `N`, the
derivative of `v : N → ℝᴷ⁺¹` sends every tangent vector of `N` at `q` — that is, every vector in
the image of the derivative of the inclusion — into the tangent space at `q`. -/
theorem mfd_mem_tanN (hv : letI := hN.chartedSpace; ContMDiff 𝓘(ℝ, 𝔻) 𝓘(ℝ, 𝔼) ∞ v)
    (hvT : IsTangent hN v) {q : N} (hvq : v q = 0) (a : 𝔻) :
    letI := hN.chartedSpace
    mfd 𝓘(ℝ, 𝔻) 𝓘(ℝ, 𝔼) v q a ∈ tanN hN q := by
  letI := hN.chartedSpace
  rw [mfd_eq_dvr_comp hN hNc hne hv q]
  exact dvr_mem_tanN hN hNc hne hv hvT hvq _

/-! ### The derivative of the extended field -/

/-- **The derivative of the extended field.**  At a point `q` of `N` the derivative of
`w₀ = v ∘ r + (id - r)` is `dv_q + (id - P)` with `P = dr_q` the orthogonal projection onto the
tangent space; as `dv_q = dv_q ∘ P` (`Milnor.Tub.dvr_apply_of_mem_orthogonal`), this is Milnor's
`dv_q ∘ P + (id - P)`. -/
theorem hasFDerivAt_w₀ (hv : letI := hN.chartedSpace; ContMDiff 𝓘(ℝ, 𝔻) 𝓘(ℝ, 𝔼) ∞ v) (q : N) :
    HasFDerivAt (w₀ hN hNc hne v)
      (dvr hN hNc hne v q + (ContinuousLinearMap.id ℝ 𝔼 - dret hN hNc hne q)) q.1 := by
  have h1 := hasFDerivAt_vr hN hNc hne hv q
  have h2 : HasFDerivAt (fun y : 𝔼 => y - (tubr hN hNc hne y).1)
      (ContinuousLinearMap.id ℝ 𝔼 - dret hN hNc hne q) q.1 :=
    (hasFDerivAt_id q.1).sub (hasFDerivAt_tubr hN hNc hne (mem_Nε_of_mem hN hNc hne q.2))
  exact h1.add h2

/-- The derivative of the extended field, as an equality of linear maps. -/
theorem fderiv_w₀ (hv : letI := hN.chartedSpace; ContMDiff 𝓘(ℝ, 𝔻) 𝓘(ℝ, 𝔼) ∞ v) (q : N) :
    fderiv ℝ (w₀ hN hNc hne v) q.1
      = dvr hN hNc hne v q + (ContinuousLinearMap.id ℝ 𝔼 - dret hN hNc hne q) :=
  (hasFDerivAt_w₀ hN hNc hne hv q).fderiv

/-- **The extended field is the identity in the normal directions.**  At a point `q` of `N` where
`v` vanishes, the derivative of `w₀` is the identity on the normal space `(T_q N)ᗮ`. -/
theorem fderiv_w₀_apply_of_mem_orthogonal
    (hv : letI := hN.chartedSpace; ContMDiff 𝓘(ℝ, 𝔻) 𝓘(ℝ, 𝔼) ∞ v) {q : N}
    {c : 𝔼} (hc : c ∈ (tanN hN q)ᗮ) : fderiv ℝ (w₀ hN hNc hne v) q.1 c = c := by
  letI := hN.chartedSpace
  have hnorm : ∀ w ∈ LinearMap.range ((mfd 𝓘(ℝ, 𝔻) 𝓘(ℝ, 𝔼) (Subtype.val : N → 𝔼)
      ⟨q.1, q.2⟩ : 𝔻 →L[ℝ] 𝔼) : 𝔻 →ₗ[ℝ] 𝔼), ⟪c, w⟫ = 0 := by
    intro w hw
    rw [real_inner_comm]
    exact hc w hw
  have hG := (tubr_spec hN hNc hne).2.2.2.2.2.2 q.1 q.2 c hnorm
  rw [fderiv_w₀ hN hNc hne hv q]
  -- along a short normal segment the extended field is `v q + s • c = s • c`
  have h1 : HasDerivAt (fun s : ℝ => w₀ hN hNc hne v (q.1 + s • c))
      ((dvr hN hNc hne v q + (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin (K + 1)))
        - dret hN hNc hne q)) c) 0 :=
    hasDerivAt_line (hasFDerivAt_w₀ hN hNc hne hv q) c
  have h2 : HasDerivAt (fun s : ℝ => w₀ hN hNc hne v (q.1 + s • c)) c 0 := by
    have h3 : HasDerivAt (fun s : ℝ => v q + s • c) c 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const c).const_add (v q)
    refine h3.congr_of_eventuallyEq ?_
    filter_upwards [hG] with s hs
    have hq' : tubr hN hNc hne (q.1 + s • c) = q := Subtype.ext hs
    show w₀ hN hNc hne v (q.1 + s • c) = v q + s • c
    unfold w₀
    rw [hq']
    abel
  exact h1.unique h2

/-- `dv_q` kills the normal space: `dv_q = dv_q ∘ P`, so the derivative of the extended field is
Milnor's `dv_q ∘ P + (id - P)`. -/
theorem dvr_apply_of_mem_orthogonal
    (hv : letI := hN.chartedSpace; ContMDiff 𝓘(ℝ, 𝔻) 𝓘(ℝ, 𝔼) ∞ v) {q : N}
    {c : 𝔼} (hc : c ∈ (tanN hN q)ᗮ) : dvr hN hNc hne v q c = 0 := by
  have h := fderiv_w₀_apply_of_mem_orthogonal hN hNc hne hv hc
  rw [fderiv_w₀ hN hNc hne hv q] at h
  simp only [add_apply, sub_apply,
    ContinuousLinearMap.id_apply, dret_apply_of_mem_orthogonal hN hNc hne q hc, sub_zero] at h
  simpa using sub_eq_zero.2 h

/-- The restriction of `dv_q` to the tangent space, an endomorphism of `T_q N` by Milnor's
Lemma 5. -/
def dvT (v : N → 𝔼) (hv : letI := hN.chartedSpace; ContMDiff 𝓘(ℝ, 𝔻) 𝓘(ℝ, 𝔼) ∞ v)
    (hvT : IsTangent hN v) (q : N) (hvq : v q = 0) : tanN hN q →ₗ[ℝ] tanN hN q :=
  LinearMap.restrict ((dvr hN hNc hne v q : 𝔼 →L[ℝ] 𝔼) : 𝔼 →ₗ[ℝ] 𝔼)
    (fun t _ => dvr_mem_tanN hN hNc hne hv hvT hvq t)

/-- On the tangent space the derivative of the extended field is the derivative of `v`. -/
theorem fderiv_w₀_apply_of_mem_tanN
    (hv : letI := hN.chartedSpace; ContMDiff 𝓘(ℝ, 𝔻) 𝓘(ℝ, 𝔼) ∞ v) (q : N) {t : 𝔼}
    (ht : t ∈ tanN hN q) :
    fderiv ℝ (w₀ hN hNc hne v) q.1 t = dvr hN hNc hne v q t := by
  rw [fderiv_w₀ hN hNc hne hv q]
  simp only [add_apply, sub_apply, ContinuousLinearMap.id_apply,
    dret_apply_of_mem_tanN hN hNc hne q ht, sub_self, add_zero]

include hNc hne in
/-- **The determinant of the derivative of the extended field at a zero** is the determinant of
`dv_q` restricted to the tangent space: in the splitting `ℝᴷ⁺¹ = T_q N ⊕ (T_q N)ᗮ` the derivative
of `w₀` is `dv_q` on the tangent part and the identity on the normal part. -/
theorem det_fderiv_w₀ (hv : letI := hN.chartedSpace; ContMDiff 𝓘(ℝ, 𝔻) 𝓘(ℝ, 𝔼) ∞ v)
    (hvT : IsTangent hN v) {q : N} (hvq : v q = 0) :
    LinearMap.det ((fderiv ℝ (w₀ hN hNc hne v) q.1 : 𝔼 →L[ℝ] 𝔼) : 𝔼 →ₗ[ℝ] 𝔼)
      = LinearMap.det (dvT hN hNc hne v hv hvT q hvq) := by
  have hLT : ∀ t ∈ tanN hN q,
      ((fderiv ℝ (w₀ hN hNc hne v) q.1 : 𝔼 →L[ℝ] 𝔼) : 𝔼 →ₗ[ℝ] 𝔼) t ∈ tanN hN q := by
    intro t ht
    rw [ContinuousLinearMap.coe_coe, fderiv_w₀_apply_of_mem_tanN hN hNc hne hv q ht]
    exact dvr_mem_tanN hN hNc hne hv hvT hvq t
  have hLC : ∀ c ∈ (tanN hN q)ᗮ,
      ((fderiv ℝ (w₀ hN hNc hne v) q.1 : 𝔼 →L[ℝ] 𝔼) : 𝔼 →ₗ[ℝ] 𝔼) c = c := by
    intro c hc
    rw [ContinuousLinearMap.coe_coe]
    exact fderiv_w₀_apply_of_mem_orthogonal hN hNc hne hv hc
  rw [det_eq_det_restrict hLT hLC]
  congr 1
  refine LinearMap.ext fun t => Subtype.ext ?_
  simp only [LinearMap.restrict_apply, dvT, ContinuousLinearMap.coe_coe]
  exact fderiv_w₀_apply_of_mem_tanN hN hNc hne hv q t.2

include hNc hne in
/-- **The extended field has a non-degenerate zero at `q` exactly when `dv_q` is invertible on the
tangent space.** -/
theorem bijective_fderiv_w₀_iff (hv : letI := hN.chartedSpace; ContMDiff 𝓘(ℝ, 𝔻) 𝓘(ℝ, 𝔼) ∞ v)
    (hvT : IsTangent hN v) {q : N} (hvq : v q = 0) :
    Bijective (fderiv ℝ (w₀ hN hNc hne v) q.1) ↔
      Bijective (dvT hN hNc hne v hv hvT q hvq) := by
  have h1 := bijective_iff_det_ne_zero
    ((fderiv ℝ (w₀ hN hNc hne v) q.1 : 𝔼 →L[ℝ] 𝔼) : 𝔼 →ₗ[ℝ] 𝔼)
  have h2 := bijective_iff_det_ne_zero (dvT hN hNc hne v hv hvT q hvq)
  rw [det_fderiv_w₀ hN hNc hne hv hvT hvq] at h1
  exact h1.trans h2.symm

/-! ### The index computed in a parametrization -/

/-- The chart of `N` at `q`, read in the ambient space: the first component of the slice chart.
It is inverse to the local parametrization `Milnor.Tub.φ`. -/
def chartMap (q : N) : 𝔼 → 𝔻 := fun x => ((σ hN q).φ x).1

/-- The chart is smooth on the domain of the slice chart. -/
theorem contDiffOn_chartMap (q : N) : ContDiffOn ℝ ∞ (chartMap hN q) (σ hN q).φ.source :=
  contDiff_fst.comp_contDiffOn (contDiffOn_σφ hN q)

/-- The chart is a left inverse of the parametrization. -/
theorem chartMap_φ (q : N) {z : 𝔻} (hz : z ∈ Ω hN q) : chartMap hN q (φ hN q z) = z :=
  c_φ hN q hz

/-- The chart is a right inverse of the parametrization on `N`. -/
theorem φ_chartMap (q : N) {x : 𝔼} (hx : x ∈ N) (hxs : x ∈ (σ hN q).φ.source) :
    φ hN q (chartMap hN q x) = x :=
  φ_c hN q (q := ⟨x, hx⟩) hxs

/-- The chart has a derivative at every point of the domain of the slice chart. -/
theorem hasFDerivAt_chartMap (q : N) {x : 𝔼} (hx : x ∈ (σ hN q).φ.source) :
    HasFDerivAt (chartMap hN q) (fderiv ℝ (chartMap hN q) x) x :=
  ((((contDiffOn_chartMap hN q).differentiableOn (by simp)) x hx).differentiableAt
    ((σ hN q).φ.open_source.mem_nhds hx)).hasFDerivAt

/-- `dχ_q ∘ dφ_q = id`: the derivative of the chart inverts the derivative of the
parametrization. -/
theorem fderiv_chartMap_comp_fderiv_φ (q : N) {z : 𝔻} (hz : z ∈ Ω hN q) :
    (fderiv ℝ (chartMap hN q) (φ hN q z)).comp (fderiv ℝ (φ hN q) z)
      = ContinuousLinearMap.id ℝ 𝔻 := by
  have h1 : HasFDerivAt (φ hN q) (fderiv ℝ (φ hN q) z) z := hasFDerivAt_φ hN q hz
  have h2 := hasFDerivAt_chartMap hN q (φ_mem_source hN q hz)
  have h3 := h2.comp z h1
  have h4 : (chartMap hN q ∘ φ hN q) =ᶠ[𝓝 z] id := by
    filter_upwards [(isOpen_Ω hN q).mem_nhds hz] with y hy
    exact chartMap_φ hN q hy
  exact (h3.congr_of_eventuallyEq h4.symm).unique (hasFDerivAt_id z)

/-- **The field `v` pulled back through the parametrization `φ_q`** (Milnor, p. 33): the field
`u ↦ dχ_q (v (φ_q u))` on the parameter domain `Ω_q ⊆ ℝⁿ`.  On `Ω_q` it is the unique field with
`dφ_q (chartField u) = v (φ_q u)`. -/
def chartField (v : N → 𝔼) (q : N) (u : 𝔻) : 𝔻 :=
  fderiv ℝ (chartMap hN q) (φ hN q u) (w₀ hN hNc hne v (φ hN q u))

/-- The pulled-back field is smooth on the parameter domain. -/
theorem contMDiffOn_chartField (hv : letI := hN.chartedSpace; ContMDiff 𝓘(ℝ, 𝔻) 𝓘(ℝ, 𝔼) ∞ v)
    (q : N) :
    ContMDiffOn 𝓘(ℝ, 𝔻) 𝓘(ℝ, 𝔻) ∞ (chartField hN hNc hne v q) (Ω hN q) := by
  rw [contMDiffOn_iff_contDiffOn]
  have hφ : ContDiffOn ℝ ∞ (φ hN q) (Ω hN q) := contDiffOn_φ hN q
  have hmapsrc : MapsTo (φ hN q) (Ω hN q) (σ hN q).φ.source := fun z hz => φ_mem_source hN q hz
  have hmapNε : MapsTo (φ hN q) (Ω hN q) (Nε hN hNc hne) := fun z hz =>
    mem_Nε_of_mem hN hNc hne (φ_mem hN q hz)
  have h1 : ContDiffOn ℝ ∞ (fun u => fderiv ℝ (chartMap hN q) (φ hN q u)) (Ω hN q) :=
    ((contDiffOn_chartMap hN q).fderiv_of_isOpen (σ hN q).φ.open_source (by simp)).comp hφ hmapsrc
  have h2 : ContDiffOn ℝ ∞ (fun u => w₀ hN hNc hne v (φ hN q u)) (Ω hN q) := by
    have hw : ContDiffOn ℝ ∞ (w₀ hN hNc hne v) (Nε hN hNc hne) := by
      rw [← contMDiffOn_iff_contDiffOn]
      exact contMDiffOn_w₀ hN hNc hne hv
    exact hw.comp hφ hmapNε
  exact h1.clm_apply h2

/-- On the parameter domain the field `Milnor.Tub.chartField` is the pull-back of `v` itself: the
auxiliary extension `w₀` is used only to make the formula total. -/
theorem chartField_eq (q : N) {u : 𝔻} (hu : u ∈ Ω hN q) :
    chartField hN hNc hne v q u
      = fderiv ℝ (chartMap hN q) (φ hN q u) (v ⟨φ hN q u, φ_mem hN q hu⟩) := by
  unfold chartField
  rw [w₀_of_mem hN hNc hne (φ_mem hN q hu)]

include hNc hne in
/-- **The defining property of the pull-back**: `dφ_q` carries `chartField u` to `v (φ_q u)`, for
`u` in the parameter domain.  (It is the unique such vector, `dφ_q` being injective.) -/
theorem fderiv_φ_chartField (hvT : IsTangent hN v) (q : N) {u : 𝔻} (hu : u ∈ Ω hN q) :
    fderiv ℝ (φ hN q) u (chartField hN hNc hne v q u) = v ⟨φ hN q u, φ_mem hN q hu⟩ := by
  letI := hN.chartedSpace
  have hcu : c hN q ⟨φ hN q u, φ_mem hN q hu⟩ = u := chartMap_φ hN q hu
  have htan : tanN hN ⟨φ hN q u, φ_mem hN q hu⟩
      = LinearMap.range ((fderiv ℝ (φ hN q) u : 𝔻 →L[ℝ] 𝔼) : 𝔻 →ₗ[ℝ] 𝔼) := by
    have h := range_mfd_val hN q ⟨φ hN q u, φ_mem hN q hu⟩ (φ_mem_source hN q hu)
    rwa [hcu] at h
  obtain ⟨b, hb⟩ := htan.le (hvT ⟨φ hN q u, φ_mem hN q hu⟩)
  rw [ContinuousLinearMap.coe_coe] at hb
  rw [chartField_eq hN hNc hne q hu, ← hb]
  have h2 := congrArg (fun L : 𝔻 →L[ℝ] 𝔻 => L b) (fderiv_chartMap_comp_fderiv_φ hN q hu)
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, ContinuousLinearMap.id_apply] at h2
  rw [h2]

/-- A globally smooth field on `ℝⁿ` agreeing with the pulled-back field near the parameter point
of `q`; the index of `v` at `q` is computed from it. -/
def chartExt (v : N → 𝔼) (hv : letI := hN.chartedSpace; ContMDiff 𝓘(ℝ, 𝔻) 𝓘(ℝ, 𝔼) ∞ v) (q : N) :
    𝔻 → 𝔻 :=
  (exists_extension (isOpen_Ω hN q) (contMDiffOn_chartField hN hNc hne hv q) isCompact_singleton
    (singleton_subset_iff.2 (z₀_mem hN q))).choose

/-- The chosen extension is globally smooth. -/
theorem chartExt_smooth (hv : letI := hN.chartedSpace; ContMDiff 𝓘(ℝ, 𝔻) 𝓘(ℝ, 𝔼) ∞ v) (q : N) :
    ContMDiff 𝓘(ℝ, 𝔻) 𝓘(ℝ, 𝔻) ∞ (chartExt hN hNc hne v hv q) :=
  (exists_extension (isOpen_Ω hN q) (contMDiffOn_chartField hN hNc hne hv q) isCompact_singleton
    (singleton_subset_iff.2 (z₀_mem hN q))).choose_spec.1

/-- The chosen extension agrees with the pulled-back field near the parameter point. -/
theorem chartExt_eq (hv : letI := hN.chartedSpace; ContMDiff 𝓘(ℝ, 𝔻) 𝓘(ℝ, 𝔼) ∞ v) (q : N) :
    chartExt hN hNc hne v hv q =ᶠ[𝓝 (z₀ hN q)] chartField hN hNc hne v q := by
  have h := (exists_extension (isOpen_Ω hN q) (contMDiffOn_chartField hN hNc hne hv q)
    isCompact_singleton (singleton_subset_iff.2 (z₀_mem hN q))).choose_spec.2
  exact eventually_nhdsSet_iff_forall.1 h _ rfl

/-- **Milnor's index of `v` at `q`, computed in a parametrization** (p. 33): the index at the
parameter point `z₀` of the field `v` pulled back through the slice-chart parametrization `φ_q`
of `N` at `q`.  It requires `n ≥ 2`, i.e. `d ≥ 1` below, because the index of a field on `ℝⁿ` is a
degree on the sphere `Sⁿ⁻¹`. -/
def chartIndexN (v : N → 𝔼) (hv : letI := hN.chartedSpace; ContMDiff 𝓘(ℝ, 𝔻) 𝓘(ℝ, 𝔼) ∞ v)
    (q : N) : ℤ :=
  Sphere.index (chartExt hN hNc hne v hv q) (z₀ hN q)

include hNc hne in
/-- **The parametrized index depends neither on the parametrization nor on the extension.**  Let
`ψ : Ω' → N ⊆ ℝᴷ⁺¹` be any smooth local parametrization of `N` at `q` — `Ω' ⊆ ℝⁿ` open,
`ψ u₀ = q`, with a smooth chart `χ` defined on an open `W ⊇ ψ(Ω')` of the ambient space inverse to
it on `N`, and with `dψ_u` spanning the tangent space at `ψ u` — and let `V` be any globally
smooth field on `ℝⁿ` agreeing near `u₀` with the pull-back `u ↦ dχ (v (ψ u))` and having an
isolated zero at `u₀`.  Then the index of `V` at `u₀` is `Milnor.Tub.chartIndexN`.  (Milnor's
Lemma 1 of §6, `Milnor.Sphere.index_eq_of_diffeo`, applied to the transition map
`χ_q ∘ ψ`.) -/
theorem index_eq_chartIndexN (hd : 0 < d)
    (hv : letI := hN.chartedSpace; ContMDiff 𝓘(ℝ, 𝔻) 𝓘(ℝ, 𝔼) ∞ v) (hvT : IsTangent hN v) (q : N)
    {Ω' : Set 𝔻} (hΩ' : IsOpen Ω') {u₀ : 𝔻} (hu₀ : u₀ ∈ Ω') {ψ : 𝔻 → 𝔼}
    (hψ : ContDiffOn ℝ ∞ ψ Ω') (hψN : ∀ u ∈ Ω', ψ u ∈ N) (hψq : ψ u₀ = q.1) {W : Set 𝔼}
    (hW : IsOpen W) {χ : 𝔼 → 𝔻} (hχ : ContDiffOn ℝ ∞ χ W) (hψW : MapsTo ψ Ω' W)
    (hχψ : ∀ u ∈ Ω', χ (ψ u) = u) (hψχ : ∀ x ∈ W, x ∈ N → ψ (χ x) = x)
    (hspan : ∀ u (hu : u ∈ Ω'),
      tanN hN ⟨ψ u, hψN u hu⟩ ≤ LinearMap.range ((fderiv ℝ ψ u : 𝔻 →L[ℝ] 𝔼) : 𝔻 →ₗ[ℝ] 𝔼))
    {V : 𝔻 → 𝔻} (hV : ContMDiff 𝓘(ℝ, 𝔻) 𝓘(ℝ, 𝔻) ∞ V)
    (hVpb : ∀ᶠ u in 𝓝 u₀, V u = fderiv ℝ χ (ψ u) (w₀ hN hNc hne v (ψ u)))
    {r : ℝ} (hr : 0 < r) (hiso : Sphere.IsolatedZero V u₀ r) :
    Sphere.index V u₀ = chartIndexN hN hNc hne v hv q := by
  classical
  letI := hN.chartedSpace
  obtain ⟨τ, hτ⟩ : ∃ τ : 𝔻 → 𝔻, τ = fun u => chartMap hN q (ψ u) := ⟨_, rfl⟩
  obtain ⟨τ', hτ'⟩ : ∃ τ' : 𝔻 → 𝔻, τ' = fun z => χ (φ hN q z) := ⟨_, rfl⟩
  have hz₀ : z₀ hN q ∈ Ω hN q := z₀_mem hN q
  have hφz₀ : φ hN q (z₀ hN q) = q.1 := φ_z₀ hN q
  have hqsrc : q.1 ∈ (σ hN q).φ.source := mem_source hN q
  have hqW : q.1 ∈ W := by rw [← hψq]; exact hψW hu₀
  have hτu₀ : τ u₀ = z₀ hN q := by rw [hτ]; show chartMap hN q (ψ u₀) = z₀ hN q; rw [hψq]; rfl
  -- the derivative of the chart inverts the derivative of `ψ`
  have hdχψ : ∀ u ∈ Ω', (fderiv ℝ χ (ψ u)).comp (fderiv ℝ ψ u) = ContinuousLinearMap.id ℝ 𝔻 := by
    intro u hu
    have h1 : HasFDerivAt ψ (fderiv ℝ ψ u) u :=
      (((hψ.differentiableOn (by simp)) u hu).differentiableAt (hΩ'.mem_nhds hu)).hasFDerivAt
    have h2 : HasFDerivAt χ (fderiv ℝ χ (ψ u)) (ψ u) :=
      (((hχ.differentiableOn (by simp)) _ (hψW hu)).differentiableAt
        (hW.mem_nhds (hψW hu))).hasFDerivAt
    have h4 : (χ ∘ ψ) =ᶠ[𝓝 u] id := by
      filter_upwards [hΩ'.mem_nhds hu] with y hy
      exact hχψ y hy
    exact ((h2.comp u h1).congr_of_eventuallyEq h4.symm).unique (hasFDerivAt_id u)
  -- the pull-back through `ψ` is a genuine pull-back
  have hpb : ∀ u ∈ Ω', fderiv ℝ ψ u (fderiv ℝ χ (ψ u) (w₀ hN hNc hne v (ψ u)))
      = w₀ hN hNc hne v (ψ u) := by
    intro u hu
    have hmem : w₀ hN hNc hne v (ψ u) ∈
        LinearMap.range ((fderiv ℝ ψ u : 𝔻 →L[ℝ] 𝔼) : 𝔻 →ₗ[ℝ] 𝔼) := by
      rw [w₀_of_mem hN hNc hne (hψN u hu)]
      exact hspan u hu (hvT ⟨ψ u, hψN u hu⟩)
    obtain ⟨b, hb⟩ := hmem
    rw [ContinuousLinearMap.coe_coe] at hb
    rw [← hb]
    have := congrArg (fun L : 𝔻 →L[ℝ] 𝔻 => L b) (hdχψ u hu)
    simp only [ContinuousLinearMap.coe_comp, Function.comp_apply,
      ContinuousLinearMap.id_apply] at this
    rw [this]
  -- the two neighbourhoods on which the fields are the pull-backs
  obtain ⟨O, hOsub, hO, hu₀O⟩ := _root_.mem_nhds_iff.1 hVpb
  obtain ⟨O', hO'sub, hO', hz₀O'⟩ := _root_.mem_nhds_iff.1 (chartExt_eq hN hNc hne hv q)
  -- the domains of the transition diffeomorphism
  obtain ⟨A, hA⟩ : ∃ A : Set 𝔻, A = (Ω' ∩ O) ∩ ψ ⁻¹' (σ hN q).φ.source := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : Set 𝔻, B = (Ω hN q ∩ O') ∩ (φ hN q) ⁻¹' W := ⟨_, rfl⟩
  have hAsub : A ⊆ Ω' := by rw [hA]; exact fun u hu => hu.1.1
  have hBsub : B ⊆ Ω hN q := by rw [hB]; exact fun z hz => hz.1.1
  have hAopen : IsOpen A := by
    rw [hA]
    exact ContinuousOn.isOpen_inter_preimage (hψ.continuousOn.mono inter_subset_left)
      (hΩ'.inter hO) (σ hN q).φ.open_source
  have hBopen : IsOpen B := by
    rw [hB]
    exact ContinuousOn.isOpen_inter_preimage
      ((contDiffOn_φ hN q).continuousOn.mono inter_subset_left)
      ((isOpen_Ω hN q).inter hO') hW
  have hτcont : ContinuousOn τ A := by
    rw [hτ]
    refine (contDiffOn_chartMap hN q).continuousOn.comp (hψ.continuousOn.mono hAsub) ?_
    rw [hA]; exact fun u hu => hu.2
  have hτ'cont : ContinuousOn τ' B := by
    rw [hτ']
    refine hχ.continuousOn.comp ((contDiffOn_φ hN q).continuousOn.mono hBsub) ?_
    rw [hB]; exact fun z hz => hz.2
  obtain ⟨U, hU⟩ : ∃ U : Set 𝔻, U = A ∩ τ ⁻¹' B := ⟨_, rfl⟩
  obtain ⟨U', hU'⟩ : ∃ U' : Set 𝔻, U' = B ∩ τ' ⁻¹' U := ⟨_, rfl⟩
  have hUopen : IsOpen U := by
    rw [hU]; exact ContinuousOn.isOpen_inter_preimage hτcont hAopen hBopen
  have hU'open : IsOpen U' := by
    rw [hU']; exact ContinuousOn.isOpen_inter_preimage hτ'cont hBopen hUopen
  have hUA : U ⊆ A := by rw [hU]; exact fun u hu => hu.1
  have hU'B : U' ⊆ B := by rw [hU']; exact fun z hz => hz.1
  -- the transition maps are mutually inverse
  have hτ'τ : ∀ u ∈ A, τ' (τ u) = u := by
    intro u hu
    have hu1 : u ∈ Ω' := hAsub hu
    have hus : ψ u ∈ (σ hN q).φ.source := by rw [hA] at hu; exact hu.2
    rw [hτ, hτ']
    show χ (φ hN q (chartMap hN q (ψ u))) = u
    rw [φ_chartMap hN q (hψN u hu1) hus]
    exact hχψ u hu1
  have hττ' : ∀ z ∈ B, τ (τ' z) = z := by
    intro z hz
    have hzΩ : z ∈ Ω hN q := hBsub hz
    have hzW : φ hN q z ∈ W := by rw [hB] at hz; exact hz.2
    rw [hτ, hτ']
    show chartMap hN q (ψ (χ (φ hN q z))) = z
    rw [hψχ _ hzW (φ_mem hN q hzΩ)]
    exact chartMap_φ hN q hzΩ
  have hmapsτ : MapsTo τ U U' := by
    intro u hu
    rw [hU']
    refine ⟨by rw [hU] at hu; exact hu.2, ?_⟩
    show τ' (τ u) ∈ U
    rw [hτ'τ u (hUA hu)]
    exact hu
  have hmapsτ' : MapsTo τ' U' U := by
    intro z hz
    rw [hU'] at hz
    exact hz.2
  have hτ'τU : ∀ u ∈ U, τ' (τ u) = u := fun u hu => hτ'τ u (hUA hu)
  have hττ'U : ∀ z ∈ U', τ (τ' z) = z := fun z hz => hττ' z (hU'B hz)
  -- smoothness of the transition maps
  have hτsmooth : ContDiffOn ℝ ∞ τ U := by
    rw [hτ]
    refine (contDiffOn_chartMap hN q).comp (hψ.mono (hUA.trans hAsub)) ?_
    intro u hu
    have := hUA hu
    rw [hA] at this
    exact this.2
  have hτ'smooth : ContDiffOn ℝ ∞ τ' U' := by
    rw [hτ']
    refine hχ.comp ((contDiffOn_φ hN q).mono (hU'B.trans hBsub)) ?_
    intro z hz
    have := hU'B hz
    rw [hB] at this
    exact this.2
  -- `u₀` is an interior point of `U`
  have hu₀U : u₀ ∈ U := by
    rw [hU]
    refine ⟨?_, ?_⟩
    · rw [hA]
      refine ⟨⟨hu₀, hu₀O⟩, ?_⟩
      show ψ u₀ ∈ (σ hN q).φ.source
      rw [hψq]
      exact hqsrc
    · show τ u₀ ∈ B
      rw [hτu₀, hB]
      refine ⟨⟨hz₀, hz₀O'⟩, ?_⟩
      show φ hN q (z₀ hN q) ∈ W
      rw [hφz₀]
      exact hqW
  obtain ⟨s, hs, hsU⟩ := Metric.isOpen_iff.1 hUopen u₀ hu₀U
  obtain ⟨r', hr', hr'r, hr'ball⟩ : ∃ r' > 0, r' ≤ r ∧ closedBall u₀ r' ⊆ U := by
    refine ⟨min r (s / 2), lt_min hr (by positivity), min_le_left _ _, fun x hx => ?_⟩
    refine hsU (Metric.mem_ball.2 (lt_of_le_of_lt ?_ (by linarith : s / 2 < s)))
    exact le_trans (Metric.mem_closedBall.1 hx) (min_le_right _ _)
  have hiso' : Sphere.IsolatedZero V u₀ r' :=
    ⟨hiso.1, fun x hx hxu => hiso.2 x (hx.trans hr'r) hxu⟩
  -- the pulled-back field is the transport of `V`
  have hwv : ∀ y ∈ τ '' closedBall u₀ r',
      chartExt hN hNc hne v hv q y = fderiv ℝ τ (τ' y) (V (τ' y)) := by
    rintro y ⟨u, hu, rfl⟩
    have huU : u ∈ U := hr'ball hu
    have huA : u ∈ A := hUA huU
    have huΩ' : u ∈ Ω' := hAsub huA
    have hus : ψ u ∈ (σ hN q).φ.source := by rw [hA] at huA; exact huA.2
    have huO : u ∈ O := by rw [hA] at huA; exact huA.1.2
    have hτuB : τ u ∈ B := by rw [hU] at huU; exact huU.2
    -- the extension agrees with the pull-back at `τ u`
    have h1 : chartExt hN hNc hne v hv q (τ u) = chartField hN hNc hne v q (τ u) := by
      refine hO'sub ?_
      rw [hB] at hτuB
      exact hτuB.1.2
    have hφτ : φ hN q (τ u) = ψ u := by
      rw [hτ]
      show φ hN q (chartMap hN q (ψ u)) = ψ u
      exact φ_chartMap hN q (hψN u huΩ') hus
    have h2 : chartField hN hNc hne v q (τ u)
        = fderiv ℝ (chartMap hN q) (ψ u) (w₀ hN hNc hne v (ψ u)) := by
      unfold chartField
      rw [hφτ]
    -- the derivative of the transition map
    have h3 : fderiv ℝ τ u = (fderiv ℝ (chartMap hN q) (ψ u)).comp (fderiv ℝ ψ u) := by
      rw [hτ]
      have h5 : HasFDerivAt ψ (fderiv ℝ ψ u) u :=
        (((hψ.differentiableOn (by simp)) u huΩ').differentiableAt
          (hΩ'.mem_nhds huΩ')).hasFDerivAt
      exact ((hasFDerivAt_chartMap hN q hus).comp u h5).fderiv
    rw [hτ'τU u huU, h1, h2, h3, hOsub huO]
    simp only [ContinuousLinearMap.coe_comp, Function.comp_apply]
    rw [hpb u huΩ']
  -- Milnor's Lemma 1 of §6
  have hmain := Sphere.index_eq_of_diffeo hd hUopen hU'open hτsmooth hτ'smooth hmapsτ hmapsτ'
    hτ'τU hττ'U hV hr' hr'ball hiso' (chartExt_smooth hN hNc hne hv q) hwv
  rw [hτu₀] at hmain
  exact hmain.symm

/-! ### The agreement of the two definitions -/

include hNc hne in
/-- **The index of the extended field at a non-degenerate zero** is the sign of the determinant of
`dv_q` on the tangent space (Milnor's Lemma 4 of §6, `Milnor.Sphere.index_eq_sgn_det`, together
with `Milnor.Tub.det_fderiv_w₀`). -/
theorem indexN_eq_sgn_det (hK : 0 < K)
    (hv : letI := hN.chartedSpace; ContMDiff 𝓘(ℝ, 𝔻) 𝓘(ℝ, 𝔼) ∞ v) (hvT : IsTangent hN v) {q : N}
    (hvq : v q = 0) (hbij : Bijective (dvT hN hNc hne v hv hvT q hvq)) :
    indexN hN hNc hne v hv q = sgn (LinearMap.det (dvT hN hNc hne v hv hvT q hvq)) := by
  have hev : wext hN hNc hne v hv =ᶠ[𝓝 q.1] w₀ hN hNc hne v :=
    eventually_nhdsSet_iff_forall.1 (wext_eq hN hNc hne v hv) q.1 (N_subset_X hN hNc hne q.2)
  have hfd : fderiv ℝ (wext hN hNc hne v hv) q.1 = fderiv ℝ (w₀ hN hNc hne v) q.1 := hev.fderiv_eq
  have hz : wext hN hNc hne v hv q.1 = 0 := by
    rw [hev.self_of_nhds, w₀_of_mem hN hNc hne q.2]
    exact hvq
  have hbij' : Bijective (fderiv ℝ (wext hN hNc hne v hv) q.1) := by
    rw [hfd]
    exact (bijective_fderiv_w₀_iff hN hNc hne hv hvT hvq).2 hbij
  show Sphere.index (wext hN hNc hne v hv) q.1 = _
  rw [Sphere.index_eq_sgn_det hK (wext_smooth hN hNc hne v hv) hz hbij', hfd,
    det_fderiv_w₀ hN hNc hne hv hvT hvq]

include hNc hne in
/-- **The index computed in a parametrization at a non-degenerate zero** is the same sign.  The
derivative at the parameter point of the pulled-back field is `dχ_q ∘ dw₀_q ∘ dφ_q`, which the
isomorphism `dφ_q : ℝⁿ → T_q N` conjugates into the restriction of `dv_q` to the tangent
space. -/
theorem chartIndexN_eq_sgn_det (hd : 0 < d)
    (hv : letI := hN.chartedSpace; ContMDiff 𝓘(ℝ, 𝔻) 𝓘(ℝ, 𝔼) ∞ v) (hvT : IsTangent hN v) {q : N}
    (hvq : v q = 0) (hbij : Bijective (dvT hN hNc hne v hv hvT q hvq)) :
    chartIndexN hN hNc hne v hv q = sgn (LinearMap.det (dvT hN hNc hne v hv hvT q hvq)) := by
  letI := hN.chartedSpace
  have hz₀ : z₀ hN q ∈ Ω hN q := z₀_mem hN q
  have hφz₀ : φ hN q (z₀ hN q) = q.1 := φ_z₀ hN q
  have hqsrc : q.1 ∈ (σ hN q).φ.source := mem_source hN q
  obtain ⟨J, hJ⟩ : ∃ J : 𝔻 →L[ℝ] 𝔼, J = fderiv ℝ (φ hN q) (z₀ hN q) := ⟨_, rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q : 𝔼 →L[ℝ] 𝔻, Q = fderiv ℝ (chartMap hN q) q.1 := ⟨_, rfl⟩
  obtain ⟨M, hM⟩ : ∃ M : 𝔼 →L[ℝ] 𝔼, M = fderiv ℝ (w₀ hN hNc hne v) q.1 := ⟨_, rfl⟩
  -- the tangent space is the image of `dφ_q`, on which `dχ_q` is inverse to `dφ_q`
  have htanJ : tanN hN q = LinearMap.range ((J : 𝔻 →L[ℝ] 𝔼) : 𝔻 →ₗ[ℝ] 𝔼) := by
    rw [hJ]
    exact range_mfd_val hN q q hqsrc
  have hQJ : ∀ a : 𝔻, Q (J a) = a := by
    intro a
    have h := congrArg (fun L : 𝔻 →L[ℝ] 𝔻 => L a)
      (fderiv_chartMap_comp_fderiv_φ hN q hz₀)
    simp only [ContinuousLinearMap.coe_comp, Function.comp_apply,
      ContinuousLinearMap.id_apply] at h
    rw [hQ, hJ, ← hφz₀]
    exact h
  have hJmem : ∀ a : 𝔻, J a ∈ tanN hN q := fun a => by rw [htanJ]; exact ⟨a, rfl⟩
  -- the derivative of the pulled-back field at the parameter point
  have hw₀q : w₀ hN hNc hne v (φ hN q (z₀ hN q)) = 0 := by
    rw [hφz₀, w₀_of_mem hN hNc hne q.2]
    exact hvq
  have hcf0 : chartField hN hNc hne v q (z₀ hN q) = 0 := by
    unfold chartField
    rw [hw₀q, map_zero]
  have hdcf : fderiv ℝ (chartField hN hNc hne v q) (z₀ hN q) = Q.comp (M.comp J) := by
    have hc : HasFDerivAt (fun u => fderiv ℝ (chartMap hN q) (φ hN q u))
        (fderiv ℝ (fun u => fderiv ℝ (chartMap hN q) (φ hN q u)) (z₀ hN q)) (z₀ hN q) := by
      have h1 : ContDiffOn ℝ ∞ (fun u => fderiv ℝ (chartMap hN q) (φ hN q u)) (Ω hN q) :=
        ((contDiffOn_chartMap hN q).fderiv_of_isOpen (σ hN q).φ.open_source (by simp)).comp
          (contDiffOn_φ hN q) (fun z hz => φ_mem_source hN q hz)
      exact (((h1.differentiableOn (by simp)) _ hz₀).differentiableAt
        ((isOpen_Ω hN q).mem_nhds hz₀)).hasFDerivAt
    have hu : HasFDerivAt (fun u => w₀ hN hNc hne v (φ hN q u)) (M.comp J) (z₀ hN q) := by
      rw [hM, hJ]
      have h2 : HasFDerivAt (w₀ hN hNc hne v) (fderiv ℝ (w₀ hN hNc hne v) q.1)
          (φ hN q (z₀ hN q)) := by
        rw [hφz₀]
        exact (hasFDerivAt_w₀ hN hNc hne hv q).differentiableAt.hasFDerivAt
      exact h2.comp (z₀ hN q) (hasFDerivAt_φ hN q hz₀)
    have hprod := hc.clm_apply hu
    rw [hw₀q, map_zero, add_zero] at hprod
    have hfd2 := hprod.fderiv
    unfold chartField
    rw [hfd2, hQ, hφz₀]
  -- the sign of the determinant
  have hdet : LinearMap.det ((Q.comp (M.comp J) : 𝔻 →L[ℝ] 𝔻) : 𝔻 →ₗ[ℝ] 𝔻)
      = LinearMap.det (dvT hN hNc hne v hv hvT q hvq) := by
    -- `dφ_q : ℝⁿ → T_q N` is an isomorphism
    have hJinj : Injective J := by rw [hJ]; exact injective_fderiv_φ hN q hz₀
    obtain ⟨J₀, hJ₀⟩ : ∃ J₀ : 𝔻 ≃ₗ[ℝ] tanN hN q, ∀ a, (J₀ a : 𝔼) = J a := by
      refine ⟨LinearEquiv.ofBijective
        (LinearMap.codRestrict (tanN hN q) ((J : 𝔻 →L[ℝ] 𝔼) : 𝔻 →ₗ[ℝ] 𝔼) hJmem)
        ⟨fun a b hab => hJinj (congrArg Subtype.val hab), fun t => ?_⟩, fun a => rfl⟩
      obtain ⟨a, ha⟩ := htanJ.le t.2
      exact ⟨a, Subtype.ext ha⟩
    have hkey : ∀ a : 𝔻, J (Q (M (J a))) = dvr hN hNc hne v q (J a) := by
      intro a
      have h1 : M (J a) = dvr hN hNc hne v q (J a) := by
        rw [hM]
        exact fderiv_w₀_apply_of_mem_tanN hN hNc hne hv q (hJmem a)
      have h2 : dvr hN hNc hne v q (J a) ∈ tanN hN q :=
        dvr_mem_tanN hN hNc hne hv hvT hvq (J a)
      rw [htanJ] at h2
      obtain ⟨b, hb⟩ := h2
      rw [ContinuousLinearMap.coe_coe] at hb
      rw [h1, ← hb, hQJ b]
    have hmap : (J₀.symm : tanN hN q →ₗ[ℝ] 𝔻) ∘ₗ (dvT hN hNc hne v hv hvT q hvq) ∘ₗ
        (J₀ : 𝔻 →ₗ[ℝ] tanN hN q) = ((Q.comp (M.comp J) : 𝔻 →L[ℝ] 𝔻) : 𝔻 →ₗ[ℝ] 𝔻) := by
      refine LinearMap.ext fun a => ?_
      show J₀.symm (dvT hN hNc hne v hv hvT q hvq (J₀ a)) = Q (M (J a))
      refine J₀.injective ?_
      rw [J₀.apply_symm_apply]
      refine Subtype.ext ?_
      rw [hJ₀ (Q (M (J a)))]
      show (dvr hN hNc hne v q (J₀ a : 𝔼)) = J (Q (M (J a)))
      rw [hJ₀ a, hkey a]
    have hconj := LinearMap.det_conj (dvT hN hNc hne v hv hvT q hvq) J₀.symm
    rw [LinearEquiv.symm_symm] at hconj
    rw [← hmap, hconj]
  -- Milnor's Lemma 4 of §6 applied to the pulled-back field
  have hev := chartExt_eq hN hNc hne hv q
  have hfd : fderiv ℝ (chartExt hN hNc hne v hv q) (z₀ hN q)
      = fderiv ℝ (chartField hN hNc hne v q) (z₀ hN q) := hev.fderiv_eq
  have hz : chartExt hN hNc hne v hv q (z₀ hN q) = 0 := by
    rw [hev.self_of_nhds]; exact hcf0
  have hbij' : Bijective (fderiv ℝ (chartExt hN hNc hne v hv q) (z₀ hN q)) := by
    rw [hfd, hdcf]
    refine (bijective_iff_det_ne_zero _).2 ?_
    rw [hdet]
    exact (bijective_iff_det_ne_zero _).1 hbij
  show Sphere.index (chartExt hN hNc hne v hv q) (z₀ hN q) = _
  rw [Sphere.index_eq_sgn_det hd (chartExt_smooth hN hNc hne hv q) hz hbij', hfd, hdcf, hdet]

include hNc hne in
/-- **Milnor's chart definition of the index agrees with the index of the extended field, at a
non-degenerate zero** (Milnor, pp. 33, 37): if `v` is a smooth tangent field on `N` with `v q = 0`
and the restriction of `dv_q` to the tangent space `T_q N` is invertible, then the index of `v` at
`q` computed in a parametrization of `N` equals the index of `v` at `q` computed from the field
extended to a tubular neighbourhood; both are the sign of the determinant of that restriction. -/
theorem chartIndexN_eq_indexN (hK : 0 < K) (hd : 0 < d)
    (hv : letI := hN.chartedSpace; ContMDiff 𝓘(ℝ, 𝔻) 𝓘(ℝ, 𝔼) ∞ v) (hvT : IsTangent hN v) {q : N}
    (hvq : v q = 0) (hbij : Bijective (dvT hN hNc hne v hv hvT q hvq)) :
    chartIndexN hN hNc hne v hv q = indexN hN hNc hne v hv q := by
  rw [chartIndexN_eq_sgn_det hN hNc hne hd hv hvT hvq hbij,
    indexN_eq_sgn_det hN hNc hne hK hv hvT hvq hbij]

end field

end Tub

end Milnor
