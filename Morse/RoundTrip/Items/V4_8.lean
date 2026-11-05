import Morse
import RoundTrip.Check
import RoundTrip.Blind.V4_8

namespace RoundTrip.V4_8

/-- The project's statement: the four listed theorems; no universe parameters. -/
def A : Prop :=
  type_of% @Morse.mem_range_mfd_val_normalBundle_iff ∧
  type_of% @Morse.hasMFDerivAt_normalEnd ∧
  type_of% @Morse.finrank_ker_mfd_normalEnd ∧
  type_of% @Morse.endpointNullity_eq_nullity

theorem A_holds : A :=
  ⟨@Morse.mem_range_mfd_val_normalBundle_iff, @Morse.hasMFDerivAt_normalEnd,
    @Morse.finrank_ker_mfd_normalEnd, @Morse.endpointNullity_eq_nullity⟩

/-! Neither direction is proved; see the `.json` diagnosis.

A works on the normal bundle `N` as a slice submanifold of `ℝⁿ × ℝⁿ` with its canonical
structure and **no normal frame**: it describes `T_{(q,v)}N` (pairs `(dx ξ, h)` with
`⟪h, ∂x/∂η⟫ + ⟪v, ∂²x/∂ξ∂η⟫ = 0`), the manifold derivative of `(q, v) ↦ Γ q + v` on `N`, and the
nullity of `dE` as the nullity of `g − v·ℓ` in the project's parametrization `xParam`.

B is a statement of multivariable calculus on `ℝᵏ × ℝᵐ`, with no manifold `N` at all: for a
parametrization `x` and an orthonormal normal frame `w_α` (smooth on an open `U`), Milnor's
`n × n` matrix `P` of inner products of the partials of `Ẽ(u, t) = x(u) + Σ t^α w_α(u)` with
`∂x/∂u^j, w_β` has upper-left block `g − Σ t^α w_α·ℓ`, lower blocks `0` and `I`, the rank of the
Jacobian `dẼ`, rank `rank(A) + m`, and `dim ker dẼ = k − rank A`. B is true (block-triangular
rank count; the upper-left entries by differentiating `⟪w_α, ∂x/∂u^j⟫ = 0`), but A cannot reach
it: A never introduces frames or Milnor's `(u, t)` coordinates, and B does not even assert that
`(u, t) ↦ (x(u), Σ t^α w_α(u))` is a chart of `N`, so the two Jacobians are never linked.
B ⇒ A fails for the same reason (B has no tangent space of `N`, no `mfderiv`, no `endpointNullity`,
no generalized endpoint map `Γ`). -/

end RoundTrip.V4_8
