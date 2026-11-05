import Mathlib.Algebra.Quaternion
import Mathlib.Algebra.QuaternionBasis
import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Morse.Chapter15.Clifford

/-!
Milnor, *Morse Theory*, §24, pp. 139–145: the dimensions of Clifford modules.

# The dimension facts behind Lemma 24.8

## Milnor's text, paraphrased

* **Definition** (p. 143).  A space `V` with anticommuting complex structures `J_1, …, J_k` is
  *minimal* if no proper non-trivial subspace is closed under `J_1, …, J_k`.
* **Lemma 24.8** (Bott–Shapiro, p. 143).  For `k ≢ 3 (mod 4)` any two minimal
  `(J_1, …, J_k)`-spaces are isomorphic.  The proof "follows that of 24.6": minimal spaces are
  lines over `ℝ, ℂ, ℍ` for `k ≤ 2`; `H`, `H'` (with `J_3 = ±J_1J_2`) for `k = 3`; `H ⊕ H'` for
  `k = 4, 5, 6`; `L`, `L'` (with `J_7 = ±J_1⋯J_6`) for `k = 7`; `L ⊕ L'` for `k = 8`.  Their
  dimensions are `m_0 = 1, m_1 = 2, m_2 = m_3 = 4, m_4 = ⋯ = m_7 = 8, m_8 = 16`, and
  `m_k = 16 m_{k−8}` "can be shown".
* **Where this is used**: in the proof of Theorem 24.5 (pp. 144–148) `ℝⁿ` splits into minimal
  summands `M_1 ⊕ ⋯ ⊕ M_s`; Milnor needs (a) `s = n/m_{k+1}` (or `n/m_k`) *tends to infinity
  with `n`*, and (b) `M_h ≅ M̄_j` (uniqueness), to build eigenvectors of `K_A`.  In Lemma 24.6
  (pp. 139–141) he needs the dimensions of `V_1 = {θ₃ = 1}`, `W`, `X`, `X_1` in `ℝ^{16r}`:
  `8r, 4r, 2r, r`.

## What is formalized

For an abstract finite-dimensional real vector space `V` and `J : ℕ → Module.End ℝ V` with
`Morse.IsClifford J k` (no inner product is needed for any of this):

* `Morse.two_dvd_finrank_of_sq` (`k ≥ 1`: `V` is a `ℂ`-module), `Morse.four_dvd_finrank_of_anticomm`
  (`k ≥ 2`: `V` is an `ℍ`-module, via Mathlib's `QuaternionAlgebra.lift`),
  `Morse.eight_dvd_finrank` (`k ≥ 4`: `V = V₁ ⊕ J₄V₁` with `V₁ = {θ₃ = 1}` quaternionic), and
  `Morse.finrank_chain`/`Morse.finrank_eq_sixteen_mul` (`k = 8`: `dim V = 2 dim V₁ = 4 dim W =
  8 dim X = 16 dim X₁`, by halving four times with `J_4`, `J_2`, `J_1`, `J_7J_8`; this is exactly
  the chain of subspaces of Lemma 24.6).  Together: **`Morse.milnorM_dvd_finrank`: `m_k` divides
  the dimension of every `(J_1, …, J_k)`-space, `k ≤ 8`**, and `Morse.isLeast_milnorM`: `m_k` is
  the least positive dimension of such a space (existence from `Morse/Chapter15/Clifford.lean`).
* `Morse.finrank_jointEigen_bott16r`: in `ℝ^{16r}` with Milnor's structures, `X₁` has dimension
  `r` (and `X`, `W`, `V₁` have `2r`, `4r`, `8r`).
* The Clifford algebra: `Morse.cliffQ k` (`Q(x) = −Σxᵢ²`), `Morse.cliffordLift` (Mathlib's
  universal property: a `(J_1, …, J_k)`-space is a `C_k`-module), `Morse.finrank_cliffordAlgebra`
  (`dim C_k = 2^k`, from Mathlib's `CliffordAlgebra.equivExterior` and the basis of the exterior
  algebra).  Consequently **`Morse.finrank_le_two_pow`: a minimal space has dimension `≤ 2^k`**
  (it is spanned by the `J_S u`), which already gives Milnor's (a): the number of minimal
  summands of `ℝⁿ` is at least `n/2^{k+1}`, hence tends to infinity with `n`.
* `Morse.isMinimal_of_finrank_eq_milnorM`: a space of dimension `m_k` is minimal; so the explicit
  `ℝ^{m_k}` are minimal spaces.  `Morse.milnorM_le_finrank_le`: a minimal space has
  `m_k ≤ dim ≤ 2^k`; `Morse.finrank_eq_milnorM_of_le_two`: for `k ≤ 2` it has dimension exactly
  `m_k` (lines over `ℝ`, `ℂ`, `ℍ`).

## How far Mathlib's `CliffordAlgebra` gets you

Mathlib (v4.33.1) provides the universal property (`CliffordAlgebra.lift`), the identifications
`C_1 ≅ ℂ` (`CliffordAlgebraComplex.equiv`) and `C_2 ≅ ℍ` (`CliffordAlgebraQuaternion.equiv`),
the linear isomorphism with the exterior algebra (`CliffordAlgebra.equivExterior`), hence
`dim C_k = 2^k`, and the graded tensor product decomposition `C(Q₁ ⊕ Q₂) ≅ C(Q₁) ⊗̂ C(Q₂)`
(`CliffordAlgebra.equivProd`).  It has nothing on the matrix-algebra structure of `C_k`
(`ℍ ⊕ ℍ`, `ℍ(2)`, `ℂ(4)`, `ℝ(8)`, `ℝ(8) ⊕ ℝ(8)`, `ℝ(16)`), on its irreducible modules, or on
`C_{k+8} ≅ C_k ⊗ ℝ(16)`.  The algebra column of the table is therefore not derived here; the
module-theoretic facts Milnor actually uses (the dimensions `m_k`, uniqueness of minimal modules)
are proved directly, using only `dim C_k = 2^k` and the universal property from Mathlib.

That every minimal space has dimension exactly `m_k`, and the uniqueness statement of Lemma 24.8
(Milnor's (b)), are proved in `Morse/Chapter15/MinimalModules.lean` from the results here.  Not
formalized: the two classes for `k = 3, 7`, and `m_{k+8} = 16 m_k` beyond `k = 0` (it is the
definition of `Morse.milnorM`).

## Gaps in Milnor's text

* p. 143: "The proof of 24.8 follows that of 24.6" — the dimension count needs that the
  involutions `θ` split each minimal space into equal halves, i.e. that some invertible element
  anticommutes with each new `θ` (`J_4`, `J_2`, `J_1`, `J_7J_8`; Milnor uses all of them in
  24.6 without comment).
* p. 145: "Hence the dimension of `M_h` is `m_{k+1}`": only the upper bound is needed for
  `s → ∞`, and it follows from `dim C_{k+1} = 2^{k+1}`.
-/

open Module Quaternion Finset

noncomputable section

namespace Morse

section Divisibility

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- `k ≥ 1`: a complex structure makes `V` a complex vector space, so `dim V` is even. -/
theorem two_dvd_finrank_of_sq (J : Module.End ℝ V) (h : J * J = -1) : 2 ∣ finrank ℝ V := by
  let φ : ℂ →ₐ[ℝ] Module.End ℝ V := Complex.lift ⟨J, h⟩
  let _ : Module ℂ V := Module.compHom V φ.toRingHom
  have : IsScalarTower ℝ ℂ V := by
    constructor
    intro r q v
    change φ (r • q) v = r • φ q v
    rw [map_smul]; rfl
  have := Module.finrank_mul_finrank ℝ ℂ V
  rw [Complex.finrank_real_complex] at this
  exact ⟨_, this.symm⟩

/-- `k ≥ 2`: two anticommuting complex structures `J₁, J₂` are the units `i, j` of a
quaternionic structure (`k = J₁J₂`). -/
def quatBasis (J₁ J₂ : Module.End ℝ V) (h1 : J₁ * J₁ = -1) (h2 : J₂ * J₂ = -1)
    (h12 : J₂ * J₁ = -(J₁ * J₂)) : QuaternionAlgebra.Basis (Module.End ℝ V) (-1 : ℝ) 0 (-1) where
  i := J₁
  j := J₂
  k := J₁ * J₂
  i_mul_i := by rw [h1]; simp
  j_mul_j := by rw [h2]; simp
  i_mul_j := rfl
  j_mul_i := by rw [h12]; simp

/-- `k ≥ 2`: `V` is an `ℍ`-module, so `4 ∣ dim V`. -/
theorem four_dvd_finrank_of_anticomm (J₁ J₂ : Module.End ℝ V) (h1 : J₁ * J₁ = -1)
    (h2 : J₂ * J₂ = -1) (h12 : J₂ * J₁ = -(J₁ * J₂)) : 4 ∣ finrank ℝ V := by
  let φ : ℍ[ℝ] →ₐ[ℝ] Module.End ℝ V := QuaternionAlgebra.lift (quatBasis J₁ J₂ h1 h2 h12)
  let _ : Module ℍ[ℝ] V := Module.compHom V φ.toRingHom
  have : IsScalarTower ℝ ℍ[ℝ] V := by
    constructor
    intro r q v
    change φ (r • q) v = r • φ q v
    rw [map_smul]; rfl
  have := Module.finrank_mul_finrank ℝ ℍ[ℝ] V
  rw [Quaternion.finrank_eq_four] at this
  exact ⟨_, this.symm⟩


variable [FiniteDimensional ℝ V]

omit [FiniteDimensional ℝ V] in
theorem mem_ker_sub_one_iff (θ : Module.End ℝ V) (v : V) :
    v ∈ LinearMap.ker (θ - 1) ↔ θ v = v := by
  simp [sub_eq_zero]

/-- **Halving**: if `θ² = 1` and an injective `P` anticommutes with `θ`, then `P` exchanges the
`±1`-eigenspaces of `θ`, which therefore have the same dimension. -/
theorem finrank_eq_two_mul_of_anticomm (θ P : Module.End ℝ V) (hθ : θ * θ = 1)
    (hP : Function.Injective P) (hPθ : P * θ = -(θ * P)) :
    finrank ℝ V = 2 * finrank ℝ (LinearMap.ker (θ - 1)) := by
  set Vp := LinearMap.ker (θ - 1) with hVp
  set Vm := LinearMap.ker (θ + 1) with hVm
  have hθv : ∀ v, θ (θ v) = v := fun v => by
    have := congrArg (fun f : Module.End ℝ V => f v) hθ; simpa using this
  have hPv : ∀ v, P (θ v) = -θ (P v) := fun v => by
    have := congrArg (fun f : Module.End ℝ V => f v) hPθ; simpa using this
  have hmemp : ∀ v, v ∈ Vp ↔ θ v = v := fun v => by simp [hVp, sub_eq_zero]
  have hmemm : ∀ v, v ∈ Vm ↔ θ v = -v := fun v => by simp [hVm, add_eq_zero_iff_eq_neg]
  have hcompl : IsCompl Vp Vm := by
    constructor
    · rw [Submodule.disjoint_def]
      intro v hp hm
      rw [hmemp] at hp; rw [hmemm] at hm
      have : v = -v := hp.symm.trans hm
      have h2 : (2 : ℝ) • v = 0 := by rw [two_smul]; nth_rewrite 2 [this]; exact add_neg_cancel v
      exact (smul_eq_zero.1 h2).resolve_left two_ne_zero
    · rw [codisjoint_iff, eq_top_iff]
      intro v _
      have h1 : (1 / 2 : ℝ) • (v + θ v) ∈ Vp := by
        rw [hmemp, map_smul, map_add, hθv, add_comm]
      have h2 : (1 / 2 : ℝ) • (v - θ v) ∈ Vm := by
        rw [hmemm, map_smul, map_sub, hθv, ← smul_neg, neg_sub]
      have : v = (1 / 2 : ℝ) • (v + θ v) + (1 / 2 : ℝ) • (v - θ v) := by module
      rw [this]
      exact Submodule.add_mem_sup h1 h2
  have hle1 : finrank ℝ Vp ≤ finrank ℝ Vm := by
    have hmap : ∀ v ∈ Vp, P v ∈ Vm := fun v hv => by
      rw [hmemp] at hv; rw [hmemm]
      have := hPv v; rw [hv] at this
      exact neg_eq_iff_eq_neg.1 this.symm
    exact LinearMap.finrank_le_finrank_of_injective (f := P.restrict hmap)
      (fun a b hab => Subtype.ext (hP (congrArg Subtype.val hab)))
  have hle2 : finrank ℝ Vm ≤ finrank ℝ Vp := by
    have hmap : ∀ v ∈ Vm, P v ∈ Vp := fun v hv => by
      rw [hmemm] at hv; rw [hmemp]
      have := hPv v; rw [hv, map_neg] at this
      exact (neg_inj.1 this).symm
    exact LinearMap.finrank_le_finrank_of_injective (f := P.restrict hmap)
      (fun a b hab => Subtype.ext (hP (congrArg Subtype.val hab)))
  rw [← Submodule.finrank_add_eq_of_isCompl hcompl]
  omega


omit [FiniteDimensional ℝ V] in
theorem injective_of_mul_self_eq_neg_one {P : Module.End ℝ V} (h : P * P = -1) :
    Function.Injective P := by
  have hv : ∀ v, P (P v) = -v := fun v => by
    rw [← Module.End.mul_apply, h, LinearMap.neg_apply, Module.End.one_apply]
  intro a b hab
  rw [← neg_neg a, ← neg_neg b, ← hv a, ← hv b, hab]

omit [FiniteDimensional ℝ V] in
theorem mapsTo_ker_of_commute {A θ : Module.End ℝ V} (h : A * θ = θ * A) {v : V}
    (hv : v ∈ LinearMap.ker (θ - 1)) : A v ∈ LinearMap.ker (θ - 1) := by
  rw [mem_ker_sub_one_iff] at hv ⊢
  have := congrArg (fun f : Module.End ℝ V => f v) h
  simp only [Module.End.mul_apply] at this
  rw [← this, hv]

/-- Halving inside a subspace preserved by `θ` and `P`. -/
theorem finrank_submodule_eq_two_mul (U : Submodule ℝ V) (θ P : Module.End ℝ V)
    (hθ : θ * θ = 1) (hP : Function.Injective P) (hPθ : P * θ = -(θ * P))
    (hθU : ∀ v ∈ U, θ v ∈ U) (hPU : ∀ v ∈ U, P v ∈ U) :
    finrank ℝ U = 2 * finrank ℝ ↥(U ⊓ LinearMap.ker (θ - 1)) := by
  have h := finrank_eq_two_mul_of_anticomm (θ.restrict hθU) (P.restrict hPU)
    (by ext v; have := congrArg (fun f : Module.End ℝ V => f v) hθ; simpa using this)
    (fun a b hab => Subtype.ext (hP (congrArg Subtype.val hab)))
    (by ext v; have := congrArg (fun f : Module.End ℝ V => f v) hPθ; simpa using this)
  rw [h]
  congr 1
  have hmap : Submodule.map U.subtype (LinearMap.ker (θ.restrict hθU - 1)) =
      U ⊓ LinearMap.ker (θ - 1) := by
    ext v
    simp only [Submodule.mem_map, LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply,
      sub_eq_zero, Submodule.mem_inf, Submodule.subtype_apply]
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨w.2, by simpa using congrArg Subtype.val hw⟩
    · rintro ⟨hU, hv⟩
      exact ⟨⟨v, hU⟩, Subtype.ext (by simpa using hv), rfl⟩
  rw [← hmap, LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ U.injective_subtype _)]



omit [FiniteDimensional ℝ V] in
theorem mapsTo_inf {U₁ U₂ : Submodule ℝ V} {A : Module.End ℝ V} (h1 : ∀ v ∈ U₁, A v ∈ U₁)
    (h2 : ∀ v ∈ U₂, A v ∈ U₂) : ∀ v ∈ U₁ ⊓ U₂, A v ∈ U₁ ⊓ U₂ :=
  fun v hv => ⟨h1 v hv.1, h2 v hv.2⟩

omit [FiniteDimensional ℝ V] in
theorem restrict_mul_self {W : Submodule ℝ V} {f : Module.End ℝ V} (hf : ∀ w ∈ W, f w ∈ W)
    (h : f * f = -1) : f.restrict hf * f.restrict hf = -1 := by
  ext w
  have := congrArg (fun g : Module.End ℝ V => g w) h
  simpa using this

omit [FiniteDimensional ℝ V] in
theorem restrict_anticomm {W : Submodule ℝ V} {f g : Module.End ℝ V} (hf : ∀ w ∈ W, f w ∈ W)
    (hg : ∀ w ∈ W, g w ∈ W) (h : g * f = -(f * g)) :
    g.restrict hg * f.restrict hf = -(f.restrict hf * g.restrict hg) := by
  ext w
  have := congrArg (fun k : Module.End ℝ V => k w) h
  simpa using this

/-- **`k ≥ 4`**: a space with four anticommuting complex structures has dimension divisible by 8. -/
theorem eight_dvd_finrank {J : ℕ → Module.End ℝ V} (h : IsClifford J 4) : 8 ∣ finrank ℝ V := by
  obtain ⟨hθ, hc1, hc2, -⟩ := θ₃_spec (h.mono (by norm_num))
  have hθ4 : J 4 * θ₃ J = -(θ₃ J * J 4) := by
    have := θ₃_anticommute h le_rfl le_rfl
    unfold AntiCommute at this
    rw [this, neg_neg]
  have hJ4 : J 4 * J 4 = -1 := h.sq 4 (by norm_num) le_rfl
  have hhalf := finrank_eq_two_mul_of_anticomm (θ₃ J) (J 4) hθ
    (injective_of_mul_self_eq_neg_one hJ4) hθ4
  have hm1 : ∀ v ∈ LinearMap.ker (θ₃ J - 1), J 1 v ∈ LinearMap.ker (θ₃ J - 1) :=
    fun v hv => mapsTo_ker_of_commute hc1.eq.symm hv
  have hm2 : ∀ v ∈ LinearMap.ker (θ₃ J - 1), J 2 v ∈ LinearMap.ker (θ₃ J - 1) :=
    fun v hv => mapsTo_ker_of_commute hc2.eq.symm hv
  have h4 := four_dvd_finrank_of_anticomm ((J 1).restrict hm1) ((J 2).restrict hm2)
    (restrict_mul_self hm1 (h.sq 1 le_rfl (by norm_num)))
    (restrict_mul_self hm2 (h.sq 2 (by norm_num) (by norm_num)))
    (restrict_anticomm hm1 hm2 (h.anti 2 1 (by norm_num) (by norm_num) le_rfl (by norm_num)
      (by norm_num)))
  rw [hhalf]
  obtain ⟨c, hc⟩ := h4
  exact ⟨c, by rw [hc]; ring⟩


omit [FiniteDimensional ℝ V] in
theorem anticomm_symm {a b : Module.End ℝ V} (h : AntiCommute a b) : b * a = -(a * b) := by
  unfold AntiCommute at h; rw [h, neg_neg]

/-- Milnor's `V_1 = {θ₃ = 1}` (p. 139). -/
def eigV₁ (J : ℕ → Module.End ℝ V) : Submodule ℝ V := LinearMap.ker (θ₃ J - 1)

/-- Milnor's `W = V_1 ∩ {θ₅ = 1}` (p. 140). -/
def eigW (J : ℕ → Module.End ℝ V) : Submodule ℝ V := eigV₁ J ⊓ LinearMap.ker (θ₅ J - 1)

/-- Milnor's `X = W ∩ {θ₆ = 1}` (p. 141). -/
def eigX (J : ℕ → Module.End ℝ V) : Submodule ℝ V := eigW J ⊓ LinearMap.ker (θ₆ J - 1)

/-- Milnor's `X_1 = X ∩ {θ₇ = 1}` (p. 141), the joint `+1`-eigenspace of `θ₃, θ₅, θ₆, θ₇`. -/
def jointEigen (J : ℕ → Module.End ℝ V) : Submodule ℝ V := eigX J ⊓ LinearMap.ker (θ₇ J - 1)

/-- First halving (`k ≥ 4`): `dim V = 2 dim V₁`, `J_4` exchanging the eigenspaces of `θ₃`. -/
theorem finrank_eq_two_mul_eigV₁ {J : ℕ → Module.End ℝ V} (h : IsClifford J 4) :
    finrank ℝ V = 2 * finrank ℝ (eigV₁ J) :=
  finrank_eq_two_mul_of_anticomm (θ₃ J) (J 4) (θ₃_spec (h.mono (by norm_num))).1
    (injective_of_mul_self_eq_neg_one (h.sq 4 (by norm_num) le_rfl))
    (anticomm_symm (θ₃_anticommute h le_rfl le_rfl))

/-- Second halving (`k ≥ 5`): `dim V₁ = 2 dim W`, by `J_2`. -/
theorem finrank_eigV₁_eq {J : ℕ → Module.End ℝ V} (h : IsClifford J 5) :
    finrank ℝ (eigV₁ J) = 2 * finrank ℝ (eigW J) := by
  obtain ⟨-, -, h3c2, -⟩ := θ₃_spec (h.mono (by norm_num))
  obtain ⟨h5sq, -, -, -, h5a2, -, h53⟩ := θ₅_spec h
  exact finrank_submodule_eq_two_mul (eigV₁ J) (θ₅ J) (J 2) h5sq
    (injective_of_mul_self_eq_neg_one (h.sq 2 (by norm_num) (by norm_num))) (anticomm_symm h5a2)
    (fun v hv => mapsTo_ker_of_commute h53.eq hv)
    (fun v hv => mapsTo_ker_of_commute h3c2.eq.symm hv)

/-- Third halving (`k ≥ 6`): `dim W = 2 dim X`, by `J_1`. -/
theorem finrank_eigW_eq {J : ℕ → Module.End ℝ V} (h : IsClifford J 6) :
    finrank ℝ (eigW J) = 2 * finrank ℝ (eigX J) := by
  obtain ⟨-, h3c1, -, -⟩ := θ₃_spec (h.mono (by norm_num))
  obtain ⟨-, h5c1, -, -, -, -, -⟩ := θ₅_spec (h.mono (by norm_num))
  obtain ⟨h6sq, -, -, -, h6a1, -, -, h63, h65⟩ := θ₆_spec h
  exact finrank_submodule_eq_two_mul (eigW J) (θ₆ J) (J 1) h6sq
    (injective_of_mul_self_eq_neg_one (h.sq 1 le_rfl (by norm_num))) (anticomm_symm h6a1)
    (mapsTo_inf (fun v hv => mapsTo_ker_of_commute h63.eq hv)
      (fun v hv => mapsTo_ker_of_commute h65.eq hv))
    (mapsTo_inf (fun v hv => mapsTo_ker_of_commute h3c1.eq.symm hv)
      (fun v hv => mapsTo_ker_of_commute h5c1.eq.symm hv))

/-- Fourth halving (`k ≥ 8`): `dim X = 2 dim X₁`, by `J_7J_8`. -/
theorem finrank_eigX_eq {J : ℕ → Module.End ℝ V} (h : IsClifford J 8) :
    finrank ℝ (eigX J) = 2 * finrank ℝ (jointEigen J) := by
  obtain ⟨h7sq, -, -, -, -, -, -, -, h73, h75, h76⟩ := θ₇_spec (h.mono (by norm_num))
  obtain ⟨h78c3, h78c5, h78c6, h78a7⟩ := J₇J₈_spec h
  have hJ78 : J 7 * J 8 * (J 7 * J 8) = -1 := by clifford_simp h
  exact finrank_submodule_eq_two_mul (eigX J) (θ₇ J) (J 7 * J 8) h7sq
    (injective_of_mul_self_eq_neg_one hJ78) h78a7
    (mapsTo_inf (mapsTo_inf (fun v hv => mapsTo_ker_of_commute h73.eq hv)
      (fun v hv => mapsTo_ker_of_commute h75.eq hv))
      (fun v hv => mapsTo_ker_of_commute h76.eq hv))
    (mapsTo_inf (mapsTo_inf (fun v hv => mapsTo_ker_of_commute h78c3.eq hv)
      (fun v hv => mapsTo_ker_of_commute h78c5.eq hv))
      (fun v hv => mapsTo_ker_of_commute h78c6.eq hv))

/-- **The chain of Lemma 24.6** (`k = 8`): `dim V = 2 dim V₁`, `dim V₁ = 2 dim W`,
`dim W = 2 dim X`, `dim X = 2 dim X₁`, halving with `J_4`, `J_2`, `J_1`, `J_7J_8`. -/
theorem finrank_chain {J : ℕ → Module.End ℝ V} (h : IsClifford J 8) :
    finrank ℝ V = 2 * finrank ℝ (eigV₁ J) ∧ finrank ℝ (eigV₁ J) = 2 * finrank ℝ (eigW J) ∧
      finrank ℝ (eigW J) = 2 * finrank ℝ (eigX J) ∧
      finrank ℝ (eigX J) = 2 * finrank ℝ (jointEigen J) :=
  ⟨finrank_eq_two_mul_eigV₁ (h.mono (by norm_num)), finrank_eigV₁_eq (h.mono (by norm_num)),
    finrank_eigW_eq (h.mono (by norm_num)), finrank_eigX_eq h⟩

/-- **`k = 8`**: `dim V = 16 · dim X₁`; in particular `16 ∣ dim V`. -/
theorem finrank_eq_sixteen_mul {J : ℕ → Module.End ℝ V} (h : IsClifford J 8) :
    finrank ℝ V = 16 * finrank ℝ (jointEigen J) := by
  obtain ⟨s1, s2, s3, s4⟩ := finrank_chain h
  rw [s1, s2, s3, s4]
  ring

/-- **The dimension facts behind Milnor's `m_k`** (Lemma 24.8, p. 143), lower bound: for
`k ≤ 8`, the dimension of every space with `k` anticommuting complex structures is divisible by
`m_k`. -/
theorem milnorM_dvd_finrank {J : ℕ → Module.End ℝ V} {k : ℕ}
    (hk : k ≤ 8) (h : IsClifford J k) : milnorM k ∣ finrank ℝ V := by
  have h1 : ∀ (hk : 1 ≤ k), 2 ∣ finrank ℝ V := fun hk1 =>
    two_dvd_finrank_of_sq (J 1) (h.sq 1 le_rfl hk1)
  have h2 : ∀ (hk : 2 ≤ k), 4 ∣ finrank ℝ V := fun hk2 =>
    four_dvd_finrank_of_anticomm (J 1) (J 2) (h.sq 1 le_rfl (by omega)) (h.sq 2 (by norm_num) hk2)
      (h.anti 2 1 (by norm_num) hk2 le_rfl (by omega) (by norm_num))
  have h4 : ∀ (hk : 4 ≤ k), 8 ∣ finrank ℝ V := fun hk4 => eight_dvd_finrank (h.mono hk4)
  interval_cases k
  · exact one_dvd _
  · exact h1 le_rfl
  · exact h2 le_rfl
  · exact h2 (by norm_num)
  · exact h4 le_rfl
  · exact h4 (by norm_num)
  · exact h4 (by norm_num)
  · exact h4 (by norm_num)
  · exact ⟨_, finrank_eq_sixteen_mul h⟩

end Divisibility


section Matrices

variable {n : Type*} [Fintype n] [DecidableEq n]

theorem IsAnticommFamily.isClifford_toLin' {J : ℕ → Matrix n n ℝ} {k : ℕ}
    (h : IsAnticommFamily J k) : IsClifford (fun α => Matrix.toLinAlgEquiv' (J α)) k := by
  refine ⟨fun a h1 h2 => ?_, fun a b h1 h2 h3 h4 hab => ?_⟩
  · rw [← map_mul, (h.cs a h1 h2).2, map_neg, map_one]
  · rw [← map_mul, ← map_mul, h.anti a b h1 h2 h3 h4 hab, map_neg]

/-- For `k ≤ 8`, if `ℝⁿ` carries `k` anticommuting complex structures then `m_k ∣ n`. -/
theorem milnorM_dvd_card {J : ℕ → Matrix n n ℝ} {k : ℕ} (hk : k ≤ 8)
    (h : IsAnticommFamily J k) : milnorM k ∣ Fintype.card n := by
  have := milnorM_dvd_finrank hk h.isClifford_toLin'
  rwa [Module.finrank_fintype_fun_eq_card] at this

theorem milnorM_pos (k : ℕ) : 0 < milnorM k := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    match k, ih with
    | 0, _ => decide
    | 1, _ => decide
    | 2, _ => decide
    | 3, _ => decide
    | 4, _ => decide
    | 5, _ => decide
    | 6, _ => decide
    | 7, _ => decide
    | k + 8, ih => exact Nat.mul_pos (by norm_num) (ih k (by omega))

/-- **Milnor's `m_k` is the least dimension** of a nonzero real vector space carrying `k`
anticommuting complex structures, `k ≤ 8` (the table `m_0, …, m_8` of p. 143). -/
theorem isLeast_milnorM {k : ℕ} (hk : k ≤ 8) :
    IsLeast {d | 0 < d ∧ ∃ J : ℕ → Matrix (Fin d) (Fin d) ℝ, IsAnticommFamily J k}
      (milnorM k) := by
  refine ⟨⟨milnorM_pos k, exists_isAnticommFamily_fin hk⟩, ?_⟩
  rintro d ⟨hd, J, hJ⟩
  have := milnorM_dvd_card hk hJ
  rw [Fintype.card_fin] at this
  exact Nat.le_of_dvd hd this

/-- **Lemma 24.6, dimensions** (pp. 139–141): in `ℝ^{16r}` with Milnor's structures
`J_α = J'_α ⊕ ⋯ ⊕ J'_α`, the subspaces `X₁ ⊂ X ⊂ W ⊂ V₁` have dimensions `r, 2r, 4r, 8r`
(Milnor's `V₁ ≅ ℍ^{2r}`, `X ≅ ℝ^{2r}`, and `dim X₁ = r` for the base point `J₇`). -/
theorem finrank_jointEigen_bott16r (r : ℕ) :
    let J : ℕ → Module.End ℝ (I16 × Fin r → ℝ) :=
      fun α => Matrix.toLinAlgEquiv' (Matrix.blockDiagonal fun _ : Fin r => bott16 α)
    finrank ℝ (jointEigen J) = r ∧ finrank ℝ (eigX J) = 2 * r ∧ finrank ℝ (eigW J) = 4 * r ∧
      finrank ℝ (eigV₁ J) = 8 * r := by
  intro J
  have hJ : IsClifford J 8 := (isAnticommFamily_bott16r r).isClifford_toLin'
  obtain ⟨s1, s2, s3, s4⟩ := finrank_chain hJ
  have hV : finrank ℝ (I16 × Fin r → ℝ) = 16 * r := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_prod, Fintype.card_fin]
    simp
  omega

end Matrices

section CliffordAlgebra

variable {A : Type*} [Ring A] [Algebra ℝ A]

def cliffQ (k : ℕ) : QuadraticForm ℝ (Fin k → ℝ) :=
  QuadraticMap.weightedSumSquares ℝ (fun _ : Fin k => (-1 : ℝ))

theorem cliffQ_apply (k : ℕ) (x : Fin k → ℝ) : cliffQ k x = -∑ i, x i ^ 2 := by
  simp [cliffQ, QuadraticMap.weightedSumSquares_apply, sq]

/-- `x ↦ Σ xᵢ J_{i+1}`, the map to be extended to `C_k`. -/
def cliffGen (k : ℕ) (J : ℕ → A) : (Fin k → ℝ) →ₗ[ℝ] A where
  toFun x := ∑ i : Fin k, x i • J (i + 1)
  map_add' x y := by simp [add_smul, sum_add_distrib]
  map_smul' c x := by simp [smul_sum, smul_smul]

/-- `(Σ xᵢ J_{i+1})² = −Σ xᵢ²`: the relations of `C_k` (symmetrize the double sum). -/
theorem cliffGen_mul_self (k : ℕ) (J : ℕ → A)
    (hsq : ∀ i : Fin k, J (i + 1) * J (i + 1) = -1)
    (hanti : ∀ i j : Fin k, i ≠ j → J (i + 1) * J (j + 1) = -(J (j + 1) * J (i + 1)))
    (x : Fin k → ℝ) : cliffGen k J x * cliffGen k J x = algebraMap ℝ A (cliffQ k x) := by
  simp only [cliffGen, LinearMap.coe_mk, AddHom.coe_mk, sum_mul_sum, smul_mul_smul_comm]
  set S := ∑ i : Fin k, ∑ j : Fin k, (x i * x j) • (J (i + 1) * J (j + 1)) with hS
  have key : ∀ i j : Fin k, J (i + 1) * J (j + 1) + J (j + 1) * J (i + 1) =
      if i = j then (-2 : ℝ) • (1 : A) else 0 := by
    intro i j
    split_ifs with h
    · subst h; rw [hsq, ← two_smul ℝ (-1 : A), smul_neg, neg_smul]
    · rw [hanti i j h, neg_add_cancel]
  have h2 : (2 : ℝ) • S = ∑ i : Fin k, (x i * x i) • ((-2 : ℝ) • (1 : A)) := by
    rw [two_smul]
    conv_lhs => arg 2; rw [hS, Finset.sum_comm]
    rw [hS, ← sum_add_distrib]
    refine sum_congr rfl fun i _ => ?_
    rw [← sum_add_distrib]
    simp_rw [mul_comm (x _) (x i), ← smul_add, key, smul_ite, smul_zero]
    rw [sum_ite_eq]
    simp
  have : S = (1 / 2 : ℝ) • ((2 : ℝ) • S) := by rw [smul_smul]; norm_num
  rw [this, h2, cliffQ_apply, Algebra.algebraMap_eq_smul_one, smul_sum]
  simp only [smul_smul, ← sum_smul]
  congr 1
  rw [← sum_neg_distrib]
  refine sum_congr rfl fun i _ => ?_
  ring




/-- `dim C_k = 2^k`, from Mathlib: `C_k ≅ Λ(ℝ^k)` as vector spaces, and the exterior algebra has
the basis indexed by the subsets of `{1, …, k}`. -/
theorem finrank_cliffordAlgebra (k : ℕ) :
    finrank ℝ (CliffordAlgebra (cliffQ k)) = 2 ^ k := by
  have : Invertible (2 : ℝ) := invertibleOfNonzero two_ne_zero
  rw [(CliffordAlgebra.equivExterior (cliffQ k)).finrank_eq,
    finrank_eq_card_basis (Pi.basisFun ℝ (Fin k)).ExteriorAlgebra, Fintype.card_finset,
    Fintype.card_fin]

instance (k : ℕ) : Module.Finite ℝ (CliffordAlgebra (cliffQ k)) := by
  have : Invertible (2 : ℝ) := invertibleOfNonzero two_ne_zero
  have : Module.Finite ℝ (ExteriorAlgebra ℝ (Fin k → ℝ)) :=
    Module.Finite.of_basis (Pi.basisFun ℝ (Fin k)).ExteriorAlgebra
  exact Module.Finite.equiv (CliffordAlgebra.equivExterior (cliffQ k)).symm

/-- The algebra homomorphism `C_k → A` sending `e_i` to `J_{i+1}` (Milnor's footnote, p. 136:
"these structures make `ℝⁿ` into a module over a suitable Clifford algebra"). -/
def cliffordLift {k : ℕ} {J : ℕ → A} (h : IsClifford J k) : CliffordAlgebra (cliffQ k) →ₐ[ℝ] A :=
  CliffordAlgebra.lift (cliffQ k) ⟨cliffGen k J,
    cliffGen_mul_self k J (fun i => h.sq _ (by omega) (by omega))
      (fun i j hij => h.anti _ _ (by omega) (by omega) (by omega) (by omega)
        (fun e => hij (Fin.ext (by omega))))⟩

theorem cliffordLift_ι {k : ℕ} {J : ℕ → A} (h : IsClifford J k) (i : Fin k) :
    cliffordLift h (CliffordAlgebra.ι (cliffQ k) (Pi.single i 1)) = J (i + 1) := by
  rw [cliffordLift, CliffordAlgebra.lift_ι_apply]
  simp only [cliffGen, LinearMap.coe_mk, AddHom.coe_mk]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj; simp [hj]
  · simp

end CliffordAlgebra

section Minimal

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]

/-- Milnor's *minimal* `(J_1, …, J_k)`-space (p. 143): non-zero, with no proper non-trivial
subspace closed under `J_1, …, J_k`. -/
def IsMinimalCliffordModule (J : ℕ → Module.End ℝ V) (k : ℕ) : Prop :=
  Nontrivial V ∧ ∀ W : Submodule ℝ V, (∀ α, 1 ≤ α → α ≤ k → ∀ w ∈ W, J α w ∈ W) → W = ⊥ ∨ W = ⊤

omit [FiniteDimensional ℝ V] in
/-- **A minimal `(J_1, …, J_k)`-space has dimension at most `2^k`**: it is spanned by the
`J_S u`, i.e. it is the image of `C_k` under `c ↦ c·u` (Mathlib: `dim C_k = 2^k`). -/
theorem finrank_le_two_pow {J : ℕ → Module.End ℝ V} {k : ℕ} (h : IsClifford J k)
    (hmin : IsMinimalCliffordModule J k) : finrank ℝ V ≤ 2 ^ k := by
  obtain ⟨hnt, hmin⟩ := hmin
  obtain ⟨u, hu⟩ := exists_ne (0 : V)
  set φ := cliffordLift (A := Module.End ℝ V) h
  set T : CliffordAlgebra (cliffQ k) →ₗ[ℝ] V := (LinearMap.applyₗ u) ∘ₗ φ.toLinearMap
  have hT : ∀ c, T c = φ c u := fun c => rfl
  have hinv : ∀ α, 1 ≤ α → α ≤ k → ∀ w ∈ LinearMap.range T, J α w ∈ LinearMap.range T := by
    rintro α h1 h2 _ ⟨c, rfl⟩
    refine ⟨CliffordAlgebra.ι (cliffQ k) (Pi.single ⟨α - 1, by omega⟩ 1) * c, ?_⟩
    rw [hT, hT, map_mul, cliffordLift_ι, Module.End.mul_apply]
    congr 2
    simp only
    omega
  rcases hmin _ hinv with hbot | htop
  · exfalso
    have : u ∈ LinearMap.range T := ⟨1, by rw [hT, map_one, Module.End.one_apply]⟩
    rw [hbot, Submodule.mem_bot] at this
    exact hu this
  · rw [← finrank_cliffordAlgebra k, ← finrank_top ℝ V, ← htop]
    exact LinearMap.finrank_range_le T

omit [FiniteDimensional ℝ V] in
/-- A subspace closed under `J_1, …, J_k` is again a `(J_1, …, J_k)`-space. -/
theorem IsClifford.exists_restrict {J : ℕ → Module.End ℝ V} {k : ℕ} (h : IsClifford J k)
    (W : Submodule ℝ V) (hW : ∀ α, 1 ≤ α → α ≤ k → ∀ w ∈ W, J α w ∈ W) :
    ∃ J' : ℕ → Module.End ℝ W, IsClifford J' k := by
  classical
  refine ⟨fun α => if hα : 1 ≤ α ∧ α ≤ k then (J α).restrict (hW α hα.1 hα.2) else 0,
    fun a h1 h2 => ?_, fun a b h1 h2 h3 h4 hab => ?_⟩
  · simp only [dif_pos (And.intro h1 h2)]
    exact restrict_mul_self _ (h.sq a h1 h2)
  · simp only [dif_pos (And.intro h1 h2), dif_pos (And.intro h3 h4)]
    exact restrict_anticomm _ _ (h.anti a b h1 h2 h3 h4 hab)

/-- **A `(J_1, …, J_k)`-space of dimension `m_k` is minimal** (`k ≤ 8`): every invariant
subspace has dimension divisible by `m_k`.  So the explicit spaces `ℝ^{m_k}` of
`Morse.exists_isAnticommFamily_fin` are minimal. -/
theorem isMinimal_of_finrank_eq_milnorM {J : ℕ → Module.End ℝ V} {k : ℕ} (hk : k ≤ 8)
    (h : IsClifford J k) (hdim : finrank ℝ V = milnorM k) : IsMinimalCliffordModule J k := by
  refine ⟨Module.nontrivial_of_finrank_pos (hdim ▸ milnorM_pos k), fun W hW => ?_⟩
  obtain ⟨J', hJ'⟩ := h.exists_restrict W hW
  have hd := milnorM_dvd_finrank hk hJ'
  have hle : finrank ℝ W ≤ milnorM k := hdim ▸ Submodule.finrank_le W
  rcases Nat.eq_zero_or_pos (finrank ℝ W) with h0 | hpos
  · exact Or.inl (Submodule.finrank_eq_zero.1 h0)
  · exact Or.inr (Submodule.eq_top_of_finrank_eq
      (le_antisymm (Submodule.finrank_le W) (hdim ▸ Nat.le_of_dvd hpos hd)))

/-- A minimal `(J_1, …, J_k)`-space has `m_k ≤ dim ≤ 2^k` (`k ≤ 8`). -/
theorem milnorM_le_finrank_le {J : ℕ → Module.End ℝ V} {k : ℕ} (hk : k ≤ 8)
    (h : IsClifford J k) (hmin : IsMinimalCliffordModule J k) :
    milnorM k ≤ finrank ℝ V ∧ finrank ℝ V ≤ 2 ^ k := by
  have := hmin.1
  exact ⟨Nat.le_of_dvd Module.finrank_pos (milnorM_dvd_finrank hk h), finrank_le_two_pow h hmin⟩

/-- For `k ≤ 2` the minimal spaces are exactly the lines over `ℝ`, `ℂ`, `ℍ` (p. 143):
`dim = m_k = 2^k`. -/
theorem finrank_eq_milnorM_of_le_two {J : ℕ → Module.End ℝ V} {k : ℕ} (hk : k ≤ 2)
    (h : IsClifford J k) (hmin : IsMinimalCliffordModule J k) : finrank ℝ V = milnorM k := by
  obtain ⟨h1, h2⟩ := milnorM_le_finrank_le (hk.trans (by norm_num)) h hmin
  interval_cases k <;> simp_all [milnorM] <;> omega

end Minimal

end Morse
