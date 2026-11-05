import Milnor.Chapter1.RegularValue
import Mathlib.Topology.Connected.TotallyDisconnected

/-!
Milnor, *Topology from the Differentiable Viewpoint*, §1, pp. 8–9.

# The counting argument behind the fundamental theorem of algebra

Milnor's proof of the fundamental theorem of algebra (p. 9) ends with the following argument,
which uses nothing specific to polynomials or spheres:

> "The set of regular values of `f`, being a sphere with finitely many points removed, is therefore
> connected. Hence the locally constant function `#f⁻¹(y)` must actually be constant on this set.
> Since `#f⁻¹(y)` can't be zero everywhere, we conclude that it is zero nowhere. Thus `f` is an
> onto mapping."

We isolate it: if `f : M → N` is a smooth map between manifolds of the same dimension, `M` is
compact, the set of regular values of `f` is preconnected, and some regular value lies in the
image of `f`, then `f` is surjective. (Critical values are in the image by definition.)
-/

open Set Filter Topology Manifold Module

noncomputable section

namespace Milnor

variable {𝕜 : Type*} [RCLike 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {H : Type*} [TopologicalSpace H] {G : Type*} [TopologicalSpace G]
  {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 F G}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  {n : WithTop ℕ∞}
  [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F]
  [I.Boundaryless] [J.Boundaryless] [IsManifold I n M] [IsManifold J n N]
  {f : M → N}

variable (I J) in
/-- The set of regular values of `f`. -/
def regularValues (f : M → N) : Set N := {y | IsRegularValue I J f y}

/-- The fibre count `y ↦ #f⁻¹(y)` is constant on any preconnected set of regular values. -/
theorem ncard_preimage_eq_of_isPreconnected [CompactSpace M] [T2Space M] [T2Space N]
    (hdim : finrank 𝕜 E = finrank 𝕜 F) (hf : ContMDiff I J n f) (hn : n ≠ 0)
    {R : Set N} (hR : R ⊆ regularValues I J f) (hconn : IsPreconnected R)
    {y y' : N} (hy : y ∈ R) (hy' : y' ∈ R) :
    (f ⁻¹' {y}).ncard = (f ⁻¹' {y'}).ncard := by
  -- The count is locally constant on `R`, hence continuous into the discrete space `ℕ`.
  have hcont : ContinuousOn (fun z => (f ⁻¹' {z}).ncard) R := fun z hz => by
    have h := (hR hz).eventually_ncard_preimage_eq hdim hf hn
    exact ((continuousAt_const (y := (f ⁻¹' {z}).ncard)).congr
      (h.mono fun z' hz' => hz'.symm)).continuousWithinAt
  exact hconn.constant hcont hy hy'

/-- **Milnor's counting argument**, local form. If `M` is compact, `f : M → N` is smooth between
manifolds of the same dimension, `R` is a preconnected set of regular values of `f`, and some
point of `R` is in the image of `f`, then all of `R` is in the image of `f`. -/
theorem subset_range_of_isPreconnected [CompactSpace M] [T2Space M] [T2Space N]
    (hdim : finrank 𝕜 E = finrank 𝕜 F) (hf : ContMDiff I J n f) (hn : n ≠ 0)
    {R : Set N} (hR : R ⊆ regularValues I J f) (hconn : IsPreconnected R)
    (hne : ∃ y₀ ∈ R, y₀ ∈ range f) : R ⊆ range f := by
  obtain ⟨y₀, hy₀, x₀, hx₀⟩ := hne
  intro y hy
  have hcount : (f ⁻¹' {y}).ncard = (f ⁻¹' {y₀}).ncard :=
    ncard_preimage_eq_of_isPreconnected hdim hf hn hR hconn hy hy₀
  have hpos : (f ⁻¹' {y₀}).ncard ≠ 0 :=
    Set.ncard_ne_zero_of_mem (a := x₀) (by simpa using hx₀)
      ((hR hy₀).finite_preimage hdim hf hn)
  obtain ⟨x, hx⟩ := Set.nonempty_of_ncard_ne_zero (hcount ▸ hpos)
  exact ⟨x, by simpa using hx⟩

/-- **Milnor's counting argument**, global form (Milnor p. 9). If `M` is compact, `f : M → N` is
smooth between manifolds of the same dimension, the set of regular values of `f` is preconnected,
and some regular value is in the image of `f`, then `f` is surjective. (Critical values are in the
image by definition.) -/
theorem surjective_of_isPreconnected_regularValues [CompactSpace M] [T2Space M] [T2Space N]
    (hdim : finrank 𝕜 E = finrank 𝕜 F) (hf : ContMDiff I J n f) (hn : n ≠ 0)
    (hconn : IsPreconnected (regularValues I J f))
    (hne : ∃ y₀ ∈ regularValues I J f, y₀ ∈ range f) :
    Function.Surjective f := by
  intro y
  by_cases hy : IsRegularValue I J f y
  · exact subset_range_of_isPreconnected hdim hf hn subset_rfl hconn hne hy
  · rw [isRegularValue_iff_not_isCriticalValue, not_not] at hy
    obtain ⟨x, hx, -⟩ := hy
    exact ⟨x, hx⟩

end Milnor
