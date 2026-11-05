import Morse
/-! Layer-2 blind definition of Morse_cdet. Textbook: Milnor, *Morse Theory*, §24, p. 140: a
complex structure `J` on `ℝ^{2m}` makes `ℝ^{2m}` a complex vector space `(ℝ^{2m}, J) ≅ ℂᵐ`, with
`i · v = J v`; a real linear map `M` commuting with `J` is then complex linear, and `det_ℂ M` is
its determinant as a complex-linear map.
Choices: `ii` is the complex structure `J`, `ℝ^{2m}` is `ι → ℝ`, matrices act by `mulVec`. The
complex structure on `ι → ℝ` is `(a + b i) • v = a v + b (J v)` (Mathlib's `Complex.lift` of `J`
into `End_ℝ(ι → ℝ)`, then `Module.compHom`); `det_ℂ` is Mathlib's `LinearMap.det` over `ℂ` (basis
independent). Convention: `i` acts as `+J` (acting as `−J` would conjugate `det_ℂ`).
Outside the textbook's hypotheses, i.e. unless `J² = −I` and `JM = MJ`, the value is `0`
(arbitrary). Orthogonality of `J` (part of Milnor's "complex structure") plays no role in `det_ℂ`
and is not checked. -/
namespace RoundTrip.L2.Morse_cdet

open scoped Matrix

section Aux
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The `ℝ`-algebra map `ℂ → End_ℝ(ι → ℝ)`, `a + b i ↦ a + b J`, for `J² = −I`. -/
noncomputable def cplxHom (J : Matrix ι ι ℝ) (hJ : J * J = -1) :
    ℂ →ₐ[ℝ] Module.End ℝ (ι → ℝ) :=
  (Matrix.toLinAlgEquiv' : Matrix ι ι ℝ ≃ₐ[ℝ] Module.End ℝ (ι → ℝ)).toAlgHom.comp
    (Complex.lift ⟨J, hJ⟩)

/-- `(ι → ℝ, J)` as a complex vector space: `z • v = (Re z) v + (Im z) J v`. -/
@[reducible] noncomputable def cplxModule (J : Matrix ι ι ℝ) (hJ : J * J = -1) :
    Module ℂ (ι → ℝ) :=
  Module.compHom (ι → ℝ) (cplxHom J hJ).toRingHom

lemma cplx_smul (J : Matrix ι ι ℝ) (hJ : J * J = -1) (z : ℂ) (v : ι → ℝ) :
    @HSMul.hSMul ℂ (ι → ℝ) (ι → ℝ) (@instHSMul _ _ (cplxModule J hJ).toSMul) z v =
      (algebraMap ℝ (Matrix ι ι ℝ) z.re + z.im • J) *ᵥ v := by
  rfl

/-- A real matrix `M` commuting with `J` as a `ℂ`-linear map of `(ι → ℝ, J)`. -/
noncomputable def cLin (J M : Matrix ι ι ℝ) (hJ : J * J = -1) (hM : J * M = M * J) :
    letI := cplxModule J hJ
    (ι → ℝ) →ₗ[ℂ] (ι → ℝ) :=
  letI := cplxModule J hJ
  { toFun := fun v => M *ᵥ v
    map_add' := Matrix.mulVec_add M
    map_smul' := fun z v => by
      rw [RingHom.id_apply, cplx_smul, cplx_smul, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
      congr 1
      rw [mul_add, add_mul, Algebra.commutes, mul_smul_comm, smul_mul_assoc, hM] }

end Aux

/-- The textbook notion: the determinant of `M` as a complex-linear map of `(ℝ^ι, J)`, `J = ii`
(`0` unless `ii² = −I` and `ii M = M ii`). -/
noncomputable def T {ι : Type*} [Fintype ι] [DecidableEq ι] (ii M : Matrix ι ι ℝ) : ℂ :=
  if h : ii * ii = -1 ∧ ii * M = M * ii then
    letI := cplxModule ii h.1
    LinearMap.det (cLin ii M h.1 h.2)
  else 0

end RoundTrip.L2.Morse_cdet
