import Morse
/-! Layer-2 blind definition of Morse_IsCompatible. Textbook: Milnor, *Morse Theory*, §8,
pp. 47–48 (Cor. 8.4): a connection `⊢` on a Riemannian manifold `M` is compatible with the metric
iff `X_x⟨Y, Y'⟩ = ⟨X_x ⊢ Y, Y'_x⟩ + ⟨Y_x, X_x ⊢ Y'⟩` for every tangent vector `X_x` and all
(smooth) vector fields `Y, Y'` (equivalently: parallel translation preserves inner products).
Choices: the metric is the one of `[Bundle.RiemannianBundle]` (inner product on each
`TangentSpace I x` via the scoped `Bundle` instances); Mathlib's `CovariantDerivative` convention
`cov σ x v = (∇_v σ)(x)`. Vector fields `Y, Y'` range over the globally `C^∞` sections of the
tangent bundle (Milnor's smooth vector fields); `X_x` over all `v ∈ T_xM`, all `x`. `X_x f` for
`f = ⟨Y, Y'⟩ : M → ℝ` is `mfderiv I 𝓘(ℝ, ℝ) f x v` (if `f` is not differentiable at `x` this is
`0`, but for smooth `Y, Y'` and a smooth metric it is the true derivative; no smoothness of the
metric is assumed in the signature, and none is imposed). Mathlib's
`CovariantDerivative.IsMetricCompatible` needs instances absent from the signature
(`IsContMDiffRiemannianBundle`, finite-dimensional `E`), so the condition is written out. -/
namespace RoundTrip.L2.Morse_IsCompatible

open Bundle
open scoped Manifold ContDiff

/-- The textbook notion: `v⟨Y, Y'⟩ = ⟨∇_v Y, Y'⟩ + ⟨Y, ∇_v Y'⟩` for all smooth `Y, Y'` and all
tangent vectors `v`. -/
def T {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I (↑(⊤ : ℕ∞)) M] [Bundle.RiemannianBundle fun x : M => TangentSpace I x]
    (cov : CovariantDerivative I E (TangentSpace I (M := M))) : Prop :=
  ∀ Y Y' : (x : M) → TangentSpace I x,
    ContMDiff I I.tangent ∞ (fun x => (⟨x, Y x⟩ : TangentBundle I M)) →
    ContMDiff I I.tangent ∞ (fun x => (⟨x, Y' x⟩ : TangentBundle I M)) →
    ∀ (x : M) (v : TangentSpace I x),
      mfderiv I 𝓘(ℝ, ℝ) (fun y => inner ℝ (Y y) (Y' y)) x v =
        inner ℝ (cov Y x v) (Y' x) + inner ℝ (Y x) (cov Y' x v)

end RoundTrip.L2.Morse_IsCompatible
