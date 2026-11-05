import Morse.Chapter9.JacobiSystem

/-!
Milnor, *Morse Theory*, §14, pp. 77–80: the space of Jacobi fields, conjugate points and their
multiplicity, Theorem 14.1 (the nullity of `E_**`), Remark 14.2 and Lemma 14.3, for a submanifold
`N ⊆ ℝᴷ` with the induced metric.

# Jacobi fields, conjugate points, and the nullity of the Hessian

## Milnor's text, paraphrased

* (p. 77) The Jacobi equation has `2n` linearly independent solutions, all defined along `γ`; a
  Jacobi field is determined by `J(0)`, `DJ/dt(0)`.  For `a ≠ b`, `p = γ(a)` and `q = γ(b)` are
  *conjugate along `γ`* if some nonzero Jacobi field vanishes for `t = a` and `t = b`; the
  *multiplicity* is the dimension of the space of all such fields.  (Footnote: if `γ` has self
  intersections one should say that the parameter values `a` and `b` are conjugate.)
* **Theorem 14.1** (p. 78): `W₁ ∈ TΩ_γ` is in the null space of `E_**` iff it is a Jacobi field;
  so `E_**` is degenerate iff the end points are conjugate, and the nullity of `E_**` is their
  multiplicity.  (p. 79) Hence the nullity is finite.
* **Remark 14.2** (p. 79): `0 ≤ ν < n`.  The Jacobi fields vanishing at `t = 0` form a space of
  dimension exactly `n`, so `ν ≤ n`; and `J_t = t V_t` is a Jacobi field vanishing at `0` but not
  at `1` (`D²J/dt² = 0`, `R(V, tV)V = 0`).
* **Lemma 14.3** (p. 80): if `α : (−ε, ε) × [0, 1] → M` is a smooth variation of `γ` through
  geodesics (end points not fixed), its variation field `∂α/∂u (0, t)` is a Jacobi field: apply
  `D/∂u` to `D/∂t ∂α/∂t = 0` and use Lemmas 9.2 and 8.7.

## In the embedded setting

* `Morse.jacobiSpace hc`: the Jacobi fields along `γ` (`Morse.IsJacobiField` of Chapter 8),
  normalized to be constant off `[0, 1]` (`J(t) = J(projIcc t)`), so that a field along
  `γ : [0, 1] → N` is one element.  `Morse.jacEquiv hc s`: **Corollary 14.B of the exposition**,
  `J ↦ (J(s), DJ/dt(s))` is an isomorphism onto `T_{γ(s)}N × T_{γ(s)}N` for every `s ∈ [0, 1]`;
  `Morse.finrank_jacobiSpace`: **the dimension is `2n`**, `n = dim N`.
* `Morse.IsConjugate hN γ a b` (Milnor's definition, for parameter values as in his footnote),
  `Morse.conjSpace hc a b` (the Jacobi fields vanishing at `a` and `b`),
  `Morse.conjMultiplicity hc a b`
  (its dimension, the multiplicity); `Morse.isConjugate_iff`: conjugate iff multiplicity `> 0`.
* **Theorem 14.1, nullity**: `Morse.hessNullSpace` is the null space of `E_**` read on fields
  along `γ|[0, 1]` (elements of `TΩ_γ` are functions on `ℝ` whose values off `[0, 1]` play no
  role, so the null space of the bilinear form `Morse.energyHessian` itself contains all fields
  vanishing on `[0, 1]`); `Morse.hessNullSpace_eq`: it is the space of Jacobi fields vanishing at
  `0` and `1`; `Morse.theorem_14_1_nullity`: the nullity is the multiplicity of `γ(0)`, `γ(1)` as
  conjugate points; `Morse.hessNullity_pos_iff`: `E_**` is degenerate iff they are conjugate.
* **Remark 14.2**: `Morse.remark_14_2` (`ν < n`, `n ≥ 1`); `Morse.finrank_jacobiSpace_zero`
  (the Jacobi fields vanishing at `0` form an `n`-dimensional space);
  `Morse.isJacobiField_smul_vel` (`t V_t` is a Jacobi field).
* **Lemma 14.3**: `Morse.lemma_14_3` (in `Morse/Chapter9/JacobiVariation.lean`); its converse,
  **Lemma 14.4**, is `Morse.lemma_14_4` (in `Morse/Chapter9/GeodesicVariation.lean`).

## What Milnor leaves implicit

* **Remark 14.2 needs `γ` non-constant** (`J₁ = V₁ ≠ 0`).  For a constant geodesic (`p = q`) the
  Jacobi fields are `t ↦ x + t y`, `x, y ∈ T_pN`, and the nullity is `0`; this case is handled
  separately here (`Morse.isJacobiField_const_curve`).  Also `ν < n` needs `n ≥ 1`: for `n = 0`
  the nullity is `0 = n`.
* "The nullity is always finite": `TΩ_γ` is infinite dimensional, and finiteness needs the
  identification with a subspace of the `2n`-dimensional space of Jacobi fields.
-/

open Set Filter Topology Function Module
open scoped ContDiff Manifold RealInnerProductSpace

noncomputable section

namespace Morse

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {N : Set V} {hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N} {γ : ℝ → V}

/-! ### Jacobi fields as a vector space -/

omit [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
/-- Being a Jacobi field only depends on the values on `[0, 1]`. -/
theorem IsJacobiField.congr {J J' : ℝ → V} (hJ : IsJacobiField hN γ J)
    (heq : EqOn J J' (Icc 0 1)) : IsJacobiField hN γ J' where
  contDiffOn := hJ.contDiffOn.congr fun t ht => (heq ht).symm
  tangent t ht := by rw [← heq ht]; exact hJ.tangent t ht
  eq t ht := by
    have hev : J =ᶠ[𝓝 t] J' := eventually_of_mem (Icc_mem_nhds ht.1 ht.2) heq
    have hev' : covD hN γ J =ᶠ[𝓝 t] covD hN γ J' := by
      filter_upwards [eventually_eventually_nhds.2 hev] with x hx
      rw [covD, covD, (show J =ᶠ[𝓝 x] J' from hx).deriv_eq]
    have := hJ.eq t ht
    rwa [jacobiExpr, covD, hev'.deriv_eq, heq (Ioo_subset_Icc_self ht)] at this

theorem projIcc_projIcc (t : ℝ) :
    ((projIcc (0 : ℝ) 1 zero_le_one (projIcc (0 : ℝ) 1 zero_le_one t) : ℝ)) =
      projIcc (0 : ℝ) 1 zero_le_one t := by
  rw [projIcc_val]

variable (hc : IsSmoothCurveIn hN γ)
include hc

/-- Jacobi fields are exactly the first components of the solutions of the Jacobi system with
tangent initial data at `0`. -/
theorem isJacobiField_iff {J : ℝ → V} :
    IsJacobiField hN γ J ↔ ∃ ζ : V × V, prj hN (γ 0) ζ.1 = ζ.1 ∧ prj hN (γ 0) ζ.2 = ζ.2 ∧
      EqOn J (fun t => (jacSol hN γ 0 ζ t).1) (Icc 0 1) := by
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  constructor
  · intro hJ
    refine ⟨(J 0, covAlong hN γ J 0), hJ.tangent 0 h0, prj_prj hN _ _, fun t ht => ?_⟩
    exact congrArg Prod.fst (hJ.eqOn_jacSol hc h0 ht)
  · rintro ⟨ζ, h1, h2, heq⟩
    exact (isJacobiField_jacSol hc h0 h1 h2).1.congr fun t ht => (heq ht).symm

variable (hN γ) in
/-- **The vector space `𝒥(γ)` of Jacobi fields along `γ`** (Milnor p. 77), each normalized to be
constant outside `[0, 1]`. -/
def jacobiSpace (_hc : IsSmoothCurveIn hN γ) : Submodule ℝ (ℝ → V) where
  carrier := {J | IsJacobiField hN γ J ∧ ∀ t, J t = J (projIcc (0 : ℝ) 1 zero_le_one t)}
  add_mem' := by
    rintro J J' ⟨hJ, hJn⟩ ⟨hJ', hJn'⟩
    obtain ⟨ζ, h1, h2, heq⟩ := (isJacobiField_iff _hc).1 hJ
    obtain ⟨ζ', h1', h2', heq'⟩ := (isJacobiField_iff _hc).1 hJ'
    refine ⟨(isJacobiField_iff _hc).2 ⟨ζ + ζ', ?_, ?_, fun t ht => ?_⟩, fun t => ?_⟩
    · simp [h1, h1']
    · simp [h2, h2']
    · simp only [Pi.add_apply, heq ht, heq' ht, jacSol_add _hc, Prod.fst_add]
    · simp only [Pi.add_apply, ← hJn, ← hJn']
  zero_mem' := ⟨(isJacobiField_iff _hc).2 ⟨0, by simp, by simp, fun t _ => by
    simp [jacSol_zero _hc]⟩, fun _ => rfl⟩
  smul_mem' := by
    rintro c J ⟨hJ, hJn⟩
    obtain ⟨ζ, h1, h2, heq⟩ := (isJacobiField_iff _hc).1 hJ
    refine ⟨(isJacobiField_iff _hc).2 ⟨c • ζ, ?_, ?_, fun t ht => ?_⟩, fun t => ?_⟩
    · simp [h1]
    · simp [h2]
    · simp only [Pi.smul_apply, heq ht, jacSol_smul _hc, Prod.smul_fst]
    · simp only [Pi.smul_apply, ← hJn]

theorem mem_jacobiSpace {J : ℝ → V} : J ∈ jacobiSpace hN γ hc ↔
    IsJacobiField hN γ J ∧ ∀ t, J t = J (projIcc (0 : ℝ) 1 zero_le_one t) := Iff.rfl

/-- The normalization `J ∘ projIcc` of a Jacobi field lies in `𝒥(γ)`. -/
theorem IsJacobiField.comp_projIcc_mem {J : ℝ → V} (hJ : IsJacobiField hN γ J) :
    (fun t => J (projIcc (0 : ℝ) 1 zero_le_one t)) ∈ jacobiSpace hN γ hc :=
  ⟨hJ.congr fun t ht => by simp [projIcc_of_mem _ ht], fun t => by simp only [projIcc_val]⟩

/-- An element of `𝒥(γ)` vanishing on `[0, 1]` is zero. -/
theorem jacobiSpace_eq_zero {J : ℝ → V} (hJ : J ∈ jacobiSpace hN γ hc)
    (h0 : EqOn J 0 (Icc 0 1)) : J = 0 := by
  funext t
  rw [hJ.2 t]
  exact h0 (projIcc (0 : ℝ) 1 zero_le_one t).2

omit [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] hc in
theorem covAlong_add {X Y : ℝ → V} {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1)
    (hX : ContDiffOn ℝ ∞ X (Icc 0 1)) (hY : ContDiffOn ℝ ∞ Y (Icc 0 1)) :
    covAlong hN γ (X + Y) s = covAlong hN γ X s + covAlong hN γ Y s := by
  rw [covAlong, covAlong, covAlong, ← map_add, derivWithin_add
    ((hX.differentiableOn (by simp)) s hs) ((hY.differentiableOn (by simp)) s hs)]

omit [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] hc in
theorem covAlong_smul {X : ℝ → V} {s : ℝ} (c : ℝ) :
    covAlong hN γ (c • X) s = c • covAlong hN γ X s := by
  rw [covAlong, covAlong, ← map_smul, derivWithin_const_smul_field]

/-- `J ↦ (J(s), DJ/dt(s))` as a linear map `𝒥(γ) → T_{γ(s)}N × T_{γ(s)}N`. -/
def jacEval {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    jacobiSpace hN γ hc →ₗ[ℝ] tanAt hN (γ s) × tanAt hN (γ s) where
  toFun J := (⟨(J : ℝ → V) s, (mem_tanAt hN (hc.mem s hs)).2 (J.2.1.tangent s hs)⟩,
    ⟨covAlong hN γ J s, prj_mem_tanAt hN (hc.mem s hs) _⟩)
  map_add' J J' := by
    ext
    · simp
    · simp [covAlong_add hs J.2.1.contDiffOn J'.2.1.contDiffOn]
  map_smul' c J := by
    ext
    · simp
    · simp [covAlong_smul]

/-- **Corollary 14.B of the exposition** (Milnor p. 77, "a Jacobi field is completely determined
by `J(0)`, `DJ/dt(0)`", and every initial value occurs): for every `s ∈ [0, 1]`,
`J ↦ (J(s), DJ/dt(s))` is bijective. -/
theorem jacEval_bijective {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) : Bijective (jacEval hc hs) := by
  constructor
  · rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro J hJ
    rw [LinearMap.mem_ker] at hJ
    have h1 : (J : ℝ → V) s = 0 := congrArg (fun z => (z.1 : V)) hJ
    have h2 : covAlong hN γ J s = 0 := congrArg (fun z => (z.2 : V)) hJ
    exact (Submodule.mem_bot ℝ).2 (Subtype.ext (jacobiSpace_eq_zero hc J.2
      (J.2.1.eqOn_zero hc hs h1 h2)))
  · rintro ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
    have hx' : prj hN (γ s) x = x := (mem_tanAt hN (hc.mem s hs)).1 hx
    have hy' : prj hN (γ s) y = y := (mem_tanAt hN (hc.mem s hs)).1 hy
    obtain ⟨hJ, hcov⟩ := isJacobiField_jacSol hc hs (ζ := (x, y)) hx' hy'
    refine ⟨⟨_, hJ.comp_projIcc_mem hc⟩, ?_⟩
    have heq : EqOn (fun t => (jacSol hN γ s (x, y) (projIcc (0 : ℝ) 1 zero_le_one t)).1)
        (fun t => (jacSol hN γ s (x, y) t).1) (Icc 0 1) := fun t ht => by
      simp [projIcc_of_mem _ ht]
    have hcov' : covAlong hN γ (fun t => (jacSol hN γ s (x, y)
        (projIcc (0 : ℝ) 1 zero_le_one t)).1) s = y := by
      rw [covAlong, derivWithin_congr heq (heq hs)]
      have := hcov s hs
      rw [covAlong, jacSol_self hc] at this
      exact this
    ext
    · change (jacSol hN γ s (x, y) (projIcc (0 : ℝ) 1 zero_le_one s)).1 = x
      rw [projIcc_of_mem _ hs, jacSol_self hc]
    · exact hcov'

/-- **Corollary 14.B**: `𝒥(γ) ≅ T_{γ(s)}N × T_{γ(s)}N`. -/
def jacEquiv {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    jacobiSpace hN γ hc ≃ₗ[ℝ] tanAt hN (γ s) × tanAt hN (γ s) :=
  LinearEquiv.ofBijective (jacEval hc hs) (jacEval_bijective hc hs)

instance : FiniteDimensional ℝ (jacobiSpace hN γ hc) :=
  LinearEquiv.finiteDimensional (jacEquiv hc (s := 0) ⟨le_rfl, zero_le_one⟩).symm

/-- **The space of Jacobi fields has dimension `2n`** (Milnor p. 77, "`2n` linearly independent
solutions"), `n = dim N`. -/
theorem finrank_jacobiSpace : finrank ℝ (jacobiSpace hN γ hc) = 2 * finrank ℝ Z := by
  rw [(jacEquiv hc (s := 0) ⟨le_rfl, zero_le_one⟩).finrank_eq, Module.finrank_prod,
    finrank_tanAt hN (hc.mem 0 ⟨le_rfl, zero_le_one⟩)]
  ring

/-- Existence of Jacobi fields with given `J(s)`, `DJ/dt(s)`. -/
theorem exists_jacobi {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) {x y : V} (hx : prj hN (γ s) x = x)
    (hy : prj hN (γ s) y = y) :
    ∃ J ∈ jacobiSpace hN γ hc, J s = x ∧ covAlong hN γ J s = y := by
  obtain ⟨J, hJ⟩ := (jacEval_bijective hc hs).2 (⟨x, (mem_tanAt hN (hc.mem s hs)).2 hx⟩,
    ⟨y, (mem_tanAt hN (hc.mem s hs)).2 hy⟩)
  exact ⟨J, J.2, congrArg (fun z => (z.1 : V)) hJ, congrArg (fun z => (z.2 : V)) hJ⟩

/-! ### Conjugate points -/

omit hc in
variable (hN γ) in
/-- **Conjugate parameter values** (Milnor p. 77, with the footnote): `a ≠ b` in `[0, 1]` are
conjugate along `γ` if a nonzero Jacobi field along `γ` vanishes at `t = a` and `t = b`. -/
def IsConjugate (a b : ℝ) : Prop :=
  a ∈ Icc (0 : ℝ) 1 ∧ b ∈ Icc (0 : ℝ) 1 ∧ a ≠ b ∧
    ∃ J, IsJacobiField hN γ J ∧ J a = 0 ∧ J b = 0 ∧ ∃ t ∈ Icc (0 : ℝ) 1, J t ≠ 0

variable (hN γ) in
/-- The space of Jacobi fields vanishing at `a` and `b`. -/
def conjSpace (_hc : IsSmoothCurveIn hN γ) (a b : ℝ) : Submodule ℝ (ℝ → V) :=
  jacobiSpace hN γ _hc ⊓ (LinearMap.ker (LinearMap.proj (R := ℝ) (φ := fun _ : ℝ => V) a) ⊓
    LinearMap.ker (LinearMap.proj (R := ℝ) (φ := fun _ : ℝ => V) b))

theorem mem_conjSpace {a b : ℝ} {J : ℝ → V} :
    J ∈ conjSpace hN γ hc a b ↔ J ∈ jacobiSpace hN γ hc ∧ J a = 0 ∧ J b = 0 := by
  simp [conjSpace]

theorem conjSpace_le_jacobiSpace (a b : ℝ) : conjSpace hN γ hc a b ≤ jacobiSpace hN γ hc :=
  inf_le_left

instance (a b : ℝ) : FiniteDimensional ℝ (conjSpace hN γ hc a b) :=
  Submodule.finiteDimensional_of_le (conjSpace_le_jacobiSpace hc a b)

variable (hN γ) in
/-- **The multiplicity** of `a` and `b` as conjugate parameter values (Milnor p. 77): the
dimension of the space of Jacobi fields vanishing at `a` and `b` (`0` if they are not
conjugate). -/
def conjMultiplicity (_hc : IsSmoothCurveIn hN γ) (a b : ℝ) : ℕ :=
  finrank ℝ (conjSpace hN γ _hc a b)

/-- Conjugate iff the multiplicity is positive. -/
theorem isConjugate_iff {a b : ℝ} : IsConjugate hN γ a b ↔
    a ∈ Icc (0 : ℝ) 1 ∧ b ∈ Icc (0 : ℝ) 1 ∧ a ≠ b ∧ 0 < conjMultiplicity hN γ hc a b := by
  constructor
  · rintro ⟨ha, hb, hab, J, hJ, hJa, hJb, t, ht, hJt⟩
    refine ⟨ha, hb, hab, Module.finrank_pos_iff_exists_ne_zero.2
      ⟨⟨fun t => J (projIcc (0 : ℝ) 1 zero_le_one t), ?_⟩, ?_⟩⟩
    · exact (mem_conjSpace hc).2 ⟨hJ.comp_projIcc_mem hc, by simp [projIcc_of_mem _ ha, hJa],
        by simp [projIcc_of_mem _ hb, hJb]⟩
    · intro h
      have := congrFun (congrArg Subtype.val h) t
      exact hJt (by simpa [projIcc_of_mem _ ht] using this)
  · rintro ⟨ha, hb, hab, hpos⟩
    obtain ⟨⟨J, hJ⟩, hJ0⟩ := Module.finrank_pos_iff_exists_ne_zero.1 hpos
    obtain ⟨hJs, hJa, hJb⟩ := (mem_conjSpace hc).1 hJ
    refine ⟨ha, hb, hab, J, hJs.1, hJa, hJb, ?_⟩
    by_contra hall
    push Not at hall
    exact hJ0 (Subtype.ext (jacobiSpace_eq_zero hc hJs hall))

/-! ### Theorem 14.1: the nullity of `E_**` -/

omit hc in
variable (V) in
/-- Restriction of a function to `[0, 1]`, extended as a constant: `X ↦ X ∘ projIcc`. -/
def restrictIcc : (ℝ → V) →ₗ[ℝ] (ℝ → V) where
  toFun X t := X (projIcc (0 : ℝ) 1 zero_le_one t)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit hc in
variable (hN) in
/-- **The null space of `E_**`** (Milnor p. 77), as a space of fields along `γ|[0, 1]`: the image
of the null space of `Morse.energyHessian` under restriction to `[0, 1]`.  (An element of
`TΩ_γ = Morse.pathTangent hN γ` is a function on `ℝ` whose values off `[0, 1]` play no role, and
`E_**` vanishes identically on the fields that vanish on `[0, 1]`.) -/
def hessNullSpace {p q : V} (hγ : γ ∈ pathSpace N p q) : Submodule ℝ (ℝ → V) :=
  (LinearMap.ker (energyHessian hN hγ)).map (restrictIcc V ∘ₗ (pathTangent hN γ).subtype)

omit hc in
variable (hN) in
/-- **The nullity of `E_**`** (Milnor p. 77): the dimension of its null space. -/
def hessNullity {p q : V} (hγ : γ ∈ pathSpace N p q) : ℕ := finrank ℝ (hessNullSpace hN hγ)

omit hc in
/-- **Theorem 14.1, the null space** (Milnor p. 78): the null space of `E_**` is the space of
Jacobi fields vanishing at `0` and `1`. -/
theorem hessNullSpace_eq {p q : V} (hγ : γ ∈ pathSpace N p q) (hgeo : IsUnbrokenGeodesic hN γ) :
    hessNullSpace hN hγ = conjSpace hN γ (hgeo.isSmoothCurveIn hN hγ) 0 1 := by
  set hc := hgeo.isSmoothCurveIn hN hγ
  ext J
  rw [mem_conjSpace hc]
  constructor
  · rintro ⟨X, hX, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker] at hX
    have hJ : IsJacobiField hN γ X := (theorem_14_1 hγ hgeo X).1 fun Y => by
      simpa using congrArg (fun f => f Y) hX
    refine ⟨hJ.comp_projIcc_mem hc, ?_, ?_⟩
    · simp [restrictIcc,
        X.2.2.2.1]
    · simp [restrictIcc,
        X.2.2.2.2]
  · rintro ⟨hJ, h0, h1⟩
    refine ⟨⟨J, hJ.1.mem_pathTangent h0 h1⟩, ?_, ?_⟩
    · rw [SetLike.mem_coe, LinearMap.mem_ker]
      ext Y
      exact (theorem_14_1 hγ hgeo ⟨J, hJ.1.mem_pathTangent h0 h1⟩).2 hJ.1 Y
    · funext t
      exact (hJ.2 t).symm

omit hc in
/-- **Theorem 14.1, the nullity** (Milnor p. 78): the nullity of `E_**` is the multiplicity of
`γ(0)` and `γ(1)` as conjugate points; in particular it is finite. -/
theorem theorem_14_1_nullity {p q : V} (hγ : γ ∈ pathSpace N p q)
    (hgeo : IsUnbrokenGeodesic hN γ) :
    hessNullity hN hγ = conjMultiplicity hN γ (hgeo.isSmoothCurveIn hN hγ) 0 1 := by
  rw [hessNullity, hessNullSpace_eq hγ hgeo, conjMultiplicity]

omit hc in
/-- **Theorem 14.1** (Milnor p. 78): `E_**` is degenerate iff the end points are conjugate
along `γ`. -/
theorem hessNullity_pos_iff {p q : V} (hγ : γ ∈ pathSpace N p q)
    (hgeo : IsUnbrokenGeodesic hN γ) : 0 < hessNullity hN hγ ↔ IsConjugate hN γ 0 1 := by
  rw [theorem_14_1_nullity hγ hgeo, isConjugate_iff (hgeo.isSmoothCurveIn hN hγ)]
  simp [zero_ne_one]

/-! ### Remark 14.2 -/

/-- **The Jacobi fields vanishing at `0` form an `n`-dimensional space** (Milnor p. 79). -/
theorem finrank_jacobiSpace_zero :
    finrank ℝ (jacobiSpace hN γ hc ⊓ LinearMap.ker (LinearMap.proj (R := ℝ)
      (φ := fun _ : ℝ => V) 0) : Submodule ℝ (ℝ → V)) = finrank ℝ Z := by
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  set J₀ := (jacobiSpace hN γ hc ⊓ LinearMap.ker (LinearMap.proj (R := ℝ)
    (φ := fun _ : ℝ => V) 0) : Submodule ℝ (ℝ → V))
  have hle : J₀ ≤ jacobiSpace hN γ hc := inf_le_left
  -- `J ↦ DJ/dt(0)` is an isomorphism `J₀ ≅ T_{γ(0)}N`
  set L : J₀ →ₗ[ℝ] tanAt hN (γ 0) :=
    (LinearMap.snd ℝ _ _).comp ((jacEval hc h0).comp (Submodule.inclusion hle))
  have hbij : Bijective L := by
    constructor
    · rw [← LinearMap.ker_eq_bot, eq_bot_iff]
      intro J hJ
      rw [LinearMap.mem_ker] at hJ
      have h2 : covAlong hN γ J 0 = 0 := congrArg Subtype.val hJ
      have h1 : (J : ℝ → V) 0 = 0 := by
        have := J.2.2
        simpa using this
      exact (Submodule.mem_bot ℝ).2 (Subtype.ext (jacobiSpace_eq_zero hc (hle J.2)
        ((hle J.2).1.eqOn_zero hc h0 h1 h2)))
    · rintro ⟨y, hy⟩
      obtain ⟨J, hJ, hJ0, hJ1⟩ := exists_jacobi hc h0 (x := 0) (y := y) (by simp)
        ((mem_tanAt hN (hc.mem 0 h0)).1 hy)
      exact ⟨⟨J, hJ, by simpa using hJ0⟩, Subtype.ext hJ1⟩
  rw [(LinearEquiv.ofBijective L hbij).finrank_eq, finrank_tanAt hN (hc.mem 0 h0)]

/-- `t ↦ t V_t` is a Jacobi field along a geodesic (Milnor p. 79). -/
theorem isJacobiField_smul_vel (hgeo : IsGeodesicOn hN γ (Ioo 0 1)) :
    IsJacobiField hN γ (fun t => t • velAlong γ t) where
  contDiffOn := contDiffOn_id.smul hc.contDiffOn_velAlong
  tangent t ht := by rw [map_smul, hc.velAlong_mem ht]
  eq t ht := by
    have ht' := Ioo_subset_Icc_self ht
    have hev : velAlong γ =ᶠ[𝓝 t] deriv γ := by
      filter_upwards [Ioo_mem_nhds ht.1 ht.2] with x hx
      exact hc.velAlong_eq hx
    have hd : ∀ x ∈ Ioo (0 : ℝ) 1, HasDerivAt (fun t => t • velAlong γ t)
        (velAlong γ x + x • deriv (deriv γ) x) x := by
      intro x hx
      have hev' : velAlong γ =ᶠ[𝓝 x] deriv γ := by
        filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
        exact hc.velAlong_eq hy
      have hev2 : (fun t => t • velAlong γ t) =ᶠ[𝓝 x] fun t => t • deriv γ t :=
        hev'.mono fun y hy => by simp only [hy]
      have h1 := ((hasDerivAt_id x).smul (hgeo.hasDerivAt_deriv hx)).congr_of_eventuallyEq hev2
      simpa [hc.velAlong_eq hx, add_comm] using h1
    -- `D/dt (t V) = V`
    have hcov : covD hN γ (fun t => t • velAlong γ t) =ᶠ[𝓝 t] velAlong γ := by
      filter_upwards [Ioo_mem_nhds ht.1 ht.2] with x hx
      rw [covD, (hd x hx).deriv, map_add, map_smul, hc.velAlong_mem (Ioo_subset_Icc_self hx)]
      have hN' := hgeo.mem x hx
      have := hgeo.tanProj_deriv_deriv hx
      rw [← prj_of_mem hN hN'] at this
      rw [this, smul_zero, add_zero]
    rw [jacobiExpr, covD, hcov.deriv_eq, hev.deriv_eq]
    have hN' := hgeo.mem t ht
    have h1 : prj hN (γ t) (deriv (deriv γ) t) = 0 := by
      rw [prj_of_mem hN hN']
      exact hgeo.tanProj_deriv_deriv ht
    rw [h1, zero_add, curvR_of_mem hN hN', hc.velAlong_eq ht, curvOp_smul_right]
    simp [curvOp]

omit [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] hc in
/-- Along a constant curve, `t ↦ t y` is a Jacobi field for every tangent `y`. -/
theorem isJacobiField_const_curve {x : V} (hγx : ∀ t ∈ Icc (0 : ℝ) 1, γ t = x) {y : V}
    (hy : prj hN x y = y) : IsJacobiField hN γ (fun t => t • y) where
  contDiffOn := contDiffOn_id.smul contDiffOn_const
  tangent t ht := by rw [hγx t ht, map_smul, hy]
  eq t ht := by
    have hev : ∀ᶠ s in 𝓝 t, γ s = x := eventually_of_mem (Icc_mem_nhds ht.1 ht.2) hγx
    have hcov : covD hN γ (fun t => t • y) =ᶠ[𝓝 t] fun _ => y := by
      filter_upwards [hev] with s hs
      rw [covD, hs, show deriv (fun t : ℝ => t • y) s = y by
        simpa using ((hasDerivAt_id s).smul_const y).deriv, hy]
    have hγ' : deriv γ t = 0 := by
      rw [(show γ =ᶠ[𝓝 t] fun _ => x from hev).deriv_eq]
      exact deriv_const _ _
    rw [jacobiExpr, covD, hcov.deriv_eq, deriv_const, map_zero, zero_add, hγ']
    by_cases hN' : γ t ∈ N
    · rw [curvR_of_mem hN hN']; simp
    · simp [curvR, hN']

/-- A geodesic on `[0, 1]` whose velocity vanishes at `t = 1` is constant (constant speed). -/
theorem eq_const_of_velAlong_one_eq_zero (hgeo : IsGeodesicOn hN γ (Ioo 0 1))
    (hV : velAlong γ 1 = 0) : ∀ t ∈ Icc (0 : ℝ) 1, γ t = γ 0 := by
  have h1 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  have hmid : (1 / 2 : ℝ) ∈ Ioo (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  set c := ‖velAlong γ (1 / 2)‖
  have hk : ∀ t ∈ Ioo (0 : ℝ) 1, ‖velAlong γ t‖ = c := fun t ht => by
    change ‖velAlong γ t‖ = ‖velAlong γ (1 / 2)‖
    rw [hc.velAlong_eq ht, hc.velAlong_eq hmid]
    exact hgeo.norm_deriv_eq isPreconnected_Ioo ht hmid
  have hc1 : ContinuousOn (fun t => ‖velAlong γ t‖) (Icc 0 1) :=
    hc.contDiffOn_velAlong.continuousOn.norm
  have hlim : Tendsto (fun t => ‖velAlong γ t‖) (𝓝[Ioo 0 1] 1) (𝓝 ‖velAlong γ 1‖) :=
    ((hc1 1 h1).mono Ioo_subset_Icc_self).tendsto
  have hlim' : Tendsto (fun t => ‖velAlong γ t‖) (𝓝[Ioo 0 1] 1) (𝓝 c) :=
    tendsto_const_nhds.congr' (eventually_nhdsWithin_of_forall fun t ht => (hk t ht).symm)
  have : (𝓝[Ioo (0 : ℝ) 1] 1).NeBot := by
    rw [← mem_closure_iff_nhdsWithin_neBot, closure_Ioo zero_ne_one]
    exact h1
  have hc0 : c = 0 := by
    rw [← tendsto_nhds_unique hlim hlim', hV, norm_zero]
  intro t ht
  rcases eq_or_lt_of_le ht.1 with h | h
  · rw [← h]
  have hd : ∀ x ∈ Ioo 0 t, HasDerivAt γ 0 x := fun x hx => by
    have hx' : x ∈ Ioo (0 : ℝ) 1 := ⟨hx.1, lt_of_lt_of_le hx.2 ht.2⟩
    have := hgeo.hasDerivAt hx'
    have h0 : deriv γ x = 0 := by
      rw [← hc.velAlong_eq hx', ← norm_eq_zero, hk x hx', hc0]
    rwa [h0] at this
  have := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le h.le
    (hc.contDiffOn.continuousOn.mono (Icc_subset_Icc le_rfl ht.2)) hd intervalIntegrable_const
  simp only [intervalIntegral.integral_zero] at this
  exact (sub_eq_zero.1 this.symm)

omit hc in
/-- **Remark 14.2** (Milnor p. 79): `0 ≤ ν < n` for the nullity `ν` of `E_**` at a geodesic, if
`n = dim N ≥ 1`.  The Jacobi fields vanishing at `0` form an `n`-dimensional space containing
the null space; it contains `t V_t`, which does not vanish at `1` unless `γ` is constant, and in
that case it contains `t y`, `0 ≠ y ∈ T_{γ(0)}N`. -/
theorem remark_14_2 {p q : V} (hγ : γ ∈ pathSpace N p q) (hgeo : IsUnbrokenGeodesic hN γ)
    (hn : 0 < finrank ℝ Z) : hessNullity hN hγ < finrank ℝ Z := by
  set hc := hgeo.isSmoothCurveIn hN hγ
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have h1 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  set J₀ := (jacobiSpace hN γ hc ⊓ LinearMap.ker (LinearMap.proj (R := ℝ)
    (φ := fun _ : ℝ => V) 0) : Submodule ℝ (ℝ → V))
  rw [theorem_14_1_nullity hγ hgeo, conjMultiplicity, ← finrank_jacobiSpace_zero hc]
  -- a Jacobi field vanishing at `0` but not at `1`
  have hex : ∃ J, IsJacobiField hN γ J ∧ J 0 = 0 ∧ J 1 ≠ 0 := by
    by_cases hV : velAlong γ 1 = 0
    · -- `γ` is constant
      have hconst := eq_const_of_velAlong_one_eq_zero hc hgeo.2 hV
      obtain ⟨y, hy, hy0⟩ : ∃ y ∈ tanAt hN (γ 0), y ≠ 0 := by
        have : 0 < finrank ℝ (tanAt hN (γ 0)) := by rwa [finrank_tanAt hN (hc.mem 0 h0)]
        obtain ⟨⟨y, hy⟩, hy0⟩ := Module.finrank_pos_iff_exists_ne_zero.1 this
        exact ⟨y, hy, fun h => hy0 (Subtype.ext h)⟩
      refine ⟨fun t => t • y, isJacobiField_const_curve hconst
        ((mem_tanAt hN (hc.mem 0 h0)).1 hy), by simp, by simpa using hy0⟩
    · exact ⟨fun t => t • velAlong γ t, isJacobiField_smul_vel hc hgeo.2, by simp,
        by simpa using hV⟩
  obtain ⟨J, hJ, hJ0, hJ1⟩ := hex
  refine Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne ?_ fun heq => hJ1 ?_)
  · intro K hK
    obtain ⟨hKs, hK0, -⟩ := (mem_conjSpace hc).1 hK
    exact ⟨hKs, by simpa using hK0⟩
  · have hmem : (fun t => J (projIcc (0 : ℝ) 1 zero_le_one t)) ∈ J₀ :=
      ⟨hJ.comp_projIcc_mem hc, by simp [hJ0]⟩
    have hmem' : (fun t => J (projIcc (0 : ℝ) 1 zero_le_one t)) ∈ conjSpace hN γ hc 0 1 := by
      rw [heq]; exact hmem
    have := ((mem_conjSpace hc).1 hmem').2.2
    simpa [projIcc_of_mem _ h1] using this

end Morse
