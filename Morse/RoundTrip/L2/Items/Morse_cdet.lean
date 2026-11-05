import Morse
import RoundTrip.L2.Blind.Morse_cdet

/-! Layer-2 check of `Morse.cdet ii M = det(M_ℂ P₊ + P₋)` (`P_± = (1 ∓ √−1·ii)/2`, a polynomial in
the entries) against the blind textbook definition (`LinearMap.det` over `ℂ` of `M` on the complex
vector space `(ℝ^ι, ii)`, `√−1` acting as `+ii`; junk `0` unless `ii² = −1`, `ii M = M ii`).

On the textbook's domain (`ii² = −1`, `ii M = M ii`) they are equal (`agree_of`): the map
`ψ (v, w) = P₊ v + w` is a `ℂ`-linear isomorphism `(ℝ^ι, ii) × ker P₊ ≃ ℂ^ι` (`P₊ ii = √−1 P₊`),
and it conjugates `M_ℂ P₊ + P₋` to `M × id`, so `det(M_ℂ P₊ + P₋) = det_ℂ M · 1`. In particular the
two conventions agree (`P₊` is the projection onto the `+√−1`-eigenspace of `ii`, i.e. `√−1` acts
as `+ii` in both). Outside the domain the values differ (`differ`: `ii = 0`, `M = 1`), which is
only junk. Orthogonality of `ii` is used by neither. -/

namespace RoundTrip.L2.Morse_cdet

open Matrix

/-- A real vector as a complex vector. -/
def ofRealV {ι : Type*} (v : ι → ℝ) : ι → ℂ := fun i => (v i : ℂ)

theorem ofRealV_add {ι : Type*} (v w : ι → ℝ) : ofRealV (v + w) = ofRealV v + ofRealV w := by
  ext i; simp [ofRealV]

theorem ofRealV_eq_zero {ι : Type*} {v : ι → ℝ} (h : ofRealV v = 0) : v = 0 := by
  ext i
  have := congrFun h i
  simpa [ofRealV] using this

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem cplx_mulVec (M : Matrix ι ι ℝ) (v : ι → ℝ) :
    Morse.cplx M *ᵥ ofRealV v = ofRealV (M *ᵥ v) := by
  ext i
  exact (RingHom.map_mulVec Complex.ofRealHom M v i).symm

theorem projP_mul_cplx {ii : Matrix ι ι ℝ} (hJ : ii * ii = -1) :
    Morse.projP ii * Morse.cplx ii = Complex.I • Morse.projP ii := by
  rw [Morse.projP, Matrix.smul_mul, Matrix.sub_mul, Matrix.one_mul, Matrix.smul_mul,
    Morse.cplx_sq hJ, smul_sub, smul_smul, smul_smul]
  match_scalars <;> ring_nf <;> simp [Complex.I_sq] <;> norm_num

theorem cplx_smul_re_im (ii : Matrix ι ι ℝ) (z : ℂ) :
    Morse.cplx (algebraMap ℝ (Matrix ι ι ℝ) z.re + z.im • ii) =
      (z.re : ℂ) • (1 : Matrix ι ι ℂ) + (z.im : ℂ) • Morse.cplx ii := by
  rw [map_add, Morse.cplx_smul, Algebra.algebraMap_eq_smul_one, Morse.cplx_smul, map_one]
  ext i j
  simp [Complex.real_smul]

theorem projP_cplx_re_im {ii : Matrix ι ι ℝ} (hJ : ii * ii = -1) (z : ℂ) :
    Morse.projP ii * Morse.cplx (algebraMap ℝ (Matrix ι ι ℝ) z.re + z.im • ii) =
      z • Morse.projP ii := by
  rw [cplx_smul_re_im, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_one, Matrix.mul_smul,
    projP_mul_cplx hJ, smul_smul, ← add_smul]
  congr 1
  conv_rhs => rw [← Complex.re_add_im z]

/-- `v ↦ P₊ v`, `ℂ`-linear from `(ℝ^ι, J)` to `ℂ^ι` (`P₊ J = √−1 P₊`). -/
noncomputable def Φ (ii : Matrix ι ι ℝ) (hJ : ii * ii = -1) :
    letI := cplxModule ii hJ
    (ι → ℝ) →ₗ[ℂ] (ι → ℂ) :=
  letI := cplxModule ii hJ
  { toFun := fun v => Morse.projP ii *ᵥ ofRealV v
    map_add' := fun v w => by rw [ofRealV_add, Matrix.mulVec_add]
    map_smul' := fun z v => by
      rw [RingHom.id_apply, cplx_smul, ← cplx_mulVec, Matrix.mulVec_mulVec, projP_cplx_re_im hJ,
        Matrix.smul_mulVec] }

theorem Φ_apply (ii : Matrix ι ι ℝ) (hJ : ii * ii = -1) (v : ι → ℝ) :
    Φ ii hJ v = Morse.projP ii *ᵥ ofRealV v := rfl

/-- `P₋ = 1 − P₊`. -/
theorem projM_eq (ii : Matrix ι ι ℝ) : Morse.projM ii = 1 - Morse.projP ii := by
  rw [← Morse.projP_add_projM (ii := ii), add_sub_cancel_left]

/-- The `−√−1`-eigenspace `ker P₊` of `ii` in `ℂ^ι`. -/
noncomputable def K (ii : Matrix ι ι ℝ) : Submodule ℂ (ι → ℂ) :=
  LinearMap.ker (Matrix.toLin' (Morse.projP ii))

theorem mem_K {ii : Matrix ι ι ℝ} {w : ι → ℂ} : w ∈ K ii ↔ Morse.projP ii *ᵥ w = 0 := by
  rw [K, LinearMap.mem_ker, Matrix.toLin'_apply]

/-- `ψ (v, w) = P₊ v + w`, `ℂ`-linear from `(ℝ^ι, J) × ker P₊` to `ℂ^ι`. -/
noncomputable def ψ (ii : Matrix ι ι ℝ) (hJ : ii * ii = -1) :
    letI := cplxModule ii hJ
    (ι → ℝ) × K ii →ₗ[ℂ] (ι → ℂ) :=
  letI := cplxModule ii hJ
  (Φ ii hJ).coprod (K ii).subtype

theorem ψ_apply (ii : Matrix ι ι ℝ) (hJ : ii * ii = -1) (x : (ι → ℝ) × K ii) :
    ψ ii hJ x = Morse.projP ii *ᵥ ofRealV x.1 + (x.2 : ι → ℂ) := rfl

theorem ψ_injective {ii : Matrix ι ι ℝ} (hJ : ii * ii = -1) : Function.Injective (ψ ii hJ) := by
  let _ := cplxModule ii hJ
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  rintro ⟨v, w, hw⟩ h
  rw [ψ_apply] at h
  rw [mem_K] at hw
  have hP : Morse.projP ii *ᵥ ofRealV v = 0 := by
    have := congrArg (Morse.projP ii *ᵥ ·) h
    simp only [Matrix.mulVec_add, Matrix.mulVec_mulVec, Morse.projP_mul_projP hJ, hw, add_zero,
      Matrix.mulVec_zero] at this
    exact this
  have hw0 : w = 0 := by simpa [hP] using h
  -- `P₊ v = 0` forces `v = √−1 · J v`, whose real part is `0`
  have hv : v = 0 := by
    rw [Morse.projP, Matrix.smul_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec,
      cplx_mulVec] at hP
    ext i
    have h1 := congrFun hP i
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Pi.zero_apply, ofRealV] at h1
    have h2 := congrArg Complex.re h1
    simp at h2
    exact h2
  subst hv hw0
  rfl

theorem ψ_surjective {ii : Matrix ι ι ℝ} (hJ : ii * ii = -1) : Function.Surjective (ψ ii hJ) := by
  let _ := cplxModule ii hJ
  intro u
  set a : ι → ℝ := fun i => (u i).re
  set b : ι → ℝ := fun i => (u i).im
  have hu : u = ofRealV a + Complex.I • ofRealV b := by
    ext i
    simp only [a, b, ofRealV, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [mul_comm]
    exact (Complex.re_add_im _).symm
  have hw : Morse.projM ii *ᵥ u ∈ K ii := by
    rw [mem_K, Matrix.mulVec_mulVec, Morse.projP_mul_projM hJ, Matrix.zero_mulVec]
  refine ⟨(a + ii *ᵥ b, ⟨_, hw⟩), ?_⟩
  rw [ψ_apply]
  dsimp only
  rw [ofRealV_add, ← cplx_mulVec, Matrix.mulVec_add, Matrix.mulVec_mulVec, projP_mul_cplx hJ,
    Matrix.smul_mulVec, ← Matrix.mulVec_smul, ← Matrix.mulVec_add, ← hu,
    ← Matrix.add_mulVec, Morse.projP_add_projM, Matrix.one_mulVec]

theorem det_toLin'_eq (ii M : Matrix ι ι ℝ) (hJ : ii * ii = -1) (hM : ii * M = M * ii) :
    letI := cplxModule ii hJ
    Matrix.toLin' (Morse.cplx M * Morse.projP ii + Morse.projM ii) ∘ₗ ψ ii hJ =
      ψ ii hJ ∘ₗ LinearMap.prodMap (cLin ii M hJ hM) LinearMap.id := by
  let _ := cplxModule ii hJ
  refine LinearMap.ext fun x => ?_
  obtain ⟨v, w, hw'⟩ := x
  have hw : Morse.projP ii *ᵥ w = 0 := mem_K.1 hw'
  show (Morse.cplx M * Morse.projP ii + Morse.projM ii) *ᵥ (Morse.projP ii *ᵥ ofRealV v + w) =
    Morse.projP ii *ᵥ ofRealV (M *ᵥ v) + w
  have hPM : Morse.cplx M * Morse.projP ii = Morse.projP ii * Morse.cplx M :=
    Morse.cplx_comm_projP hM.symm
  have e1 : (Morse.cplx M * Morse.projP ii + Morse.projM ii) * Morse.projP ii =
      Morse.cplx M * Morse.projP ii := by
    rw [Matrix.add_mul, Matrix.mul_assoc, Morse.projP_mul_projP hJ, Morse.projM_mul_projP hJ,
      add_zero]
  have e2 : (Morse.cplx M * Morse.projP ii + Morse.projM ii) *ᵥ w = w := by
    rw [Matrix.add_mulVec, ← Matrix.mulVec_mulVec, hw, Matrix.mulVec_zero, zero_add, projM_eq,
      Matrix.sub_mulVec, Matrix.one_mulVec, hw, sub_zero]
  rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, e1, e2, ← cplx_mulVec, Matrix.mulVec_mulVec, ← hPM]

/-- **Agreement on the textbook's domain**: `J² = −I` and `JM = MJ`. -/
theorem agree_of (ii M : Matrix ι ι ℝ) (hJ : ii * ii = -1) (hM : ii * M = M * ii) :
    Morse.cdet ii M = T ii M := by
  rw [T, dif_pos ⟨hJ, hM⟩]
  let _ := cplxModule ii hJ
  let e : ((ι → ℝ) × K ii) ≃ₗ[ℂ] (ι → ℂ) :=
    LinearEquiv.ofBijective (ψ ii hJ) ⟨ψ_injective hJ, ψ_surjective hJ⟩
  have : Module.Finite ℂ (ι → ℝ) :=
    Module.Finite.of_surjective ((LinearMap.fst ℂ (ι → ℝ) (K ii)) ∘ₗ e.symm.toLinearMap)
      fun v => ⟨e (v, 0), by simp⟩
  have hA : Matrix.toLin' (Morse.cplx M * Morse.projP ii + Morse.projM ii) =
      (e : ((ι → ℝ) × K ii) →ₗ[ℂ] (ι → ℂ)) ∘ₗ
        LinearMap.prodMap (cLin ii M hJ hM) LinearMap.id ∘ₗ
        (e.symm : (ι → ℂ) →ₗ[ℂ] ((ι → ℝ) × K ii)) := by
    have h := det_toLin'_eq ii M hJ hM
    refine LinearMap.ext fun u => ?_
    obtain ⟨x, rfl⟩ := ψ_surjective hJ u
    have hx : e.symm (ψ ii hJ x) = x := e.symm_apply_apply x
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, hx]
    exact LinearMap.congr_fun h x
  rw [Morse.cdet, ← LinearMap.det_toLin', hA, LinearMap.det_conj, LinearMap.det_prodMap,
    LinearMap.det_id, mul_one]

/-- Outside the textbook's domain the blind value is the junk `0`: for `ii = 0` (not a complex
structure) and `M = 1`, the project's polynomial gives `det(½ + ½) = 1`. -/
theorem differ :
    Morse.cdet (0 : Matrix (Fin 1) (Fin 1) ℝ) 1 ≠ T (0 : Matrix (Fin 1) (Fin 1) ℝ) 1 := by
  have hT : T (0 : Matrix (Fin 1) (Fin 1) ℝ) 1 = 0 := by
    rw [T, dif_neg]
    rintro ⟨h, -⟩
    have := congrFun (congrFun h 0) 0
    simp at this
  have hP : Morse.cdet (0 : Matrix (Fin 1) (Fin 1) ℝ) 1 = 1 := by
    rw [Morse.cdet, map_one, Matrix.one_mul, Morse.projP_add_projM, Matrix.det_one]
  rw [hT, hP]
  exact one_ne_zero

end RoundTrip.L2.Morse_cdet
