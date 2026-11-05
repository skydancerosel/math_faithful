import Milnor.Chapter6.ChartIndex

/-!
# The Euler number of the sphere (Milnor, p. 39)

Milnor's example on p. 39: the integer produced by the Poincaré–Hopf theorem
(`Milnor.Tub.poincare_hopf`) for the sphere `Sⁿ ⊆ ℝⁿ⁺¹` is `1 + (-1)ⁿ`, so it is `2` for `n` even
and `0` for `n` odd.

The field is Milnor's own: fix a unit vector `e` and put `v x = e - ⟪e, x⟫ x`, the tangential part
of the constant field `e` — the gradient on `Sⁿ` of the height function `x ↦ ⟪e, x⟫`.  Its zeros
are exactly `e` and `-e`.  At `e` the derivative of `v`, restricted to the tangent space
`T_e Sⁿ = e^⊥`, is minus the identity, of determinant `(-1)ⁿ`; at `-e` it is the identity, of
determinant `1`.  Both are non-singular, so Milnor's Lemma 5 in the form
`Milnor.Tub.indexN_eq_sgn_det` gives the two indices `(-1)ⁿ` and `1`, and the Poincaré–Hopf theorem
turns their sum into the index sum of *every* smooth tangent field on `Sⁿ` with finitely many
zeros (`Milnor.Sphere.indexSum_sph`).

For `n` odd the answer is checked a second way, independently of the derivative computation: §5
provides a nowhere-zero tangent field on `Sⁿ` (`Milnor.Sphere.exists_nonvanishing_field`), and a
field with no zeros has an empty index sum, so the integer is `0`
(`Milnor.Sphere.indexSum_sph_of_nonvanishing`).  That the two computations agree is
`Milnor.Sphere.indexSum_sph_odd_agree`.

## What is and is not proved here

What is proved is the value of the integer of `Milnor.Tub.poincare_hopf`, which Milnor calls the
**Euler number** of the manifold.  What is **not** proved — and cannot be in the present setting —
is that this integer is the **Euler characteristic** `χ(Sⁿ)` of the sphere: Mathlib has no Euler
characteristic of a topological space, no Betti numbers and no cellular homology, so the statement
`χ(Sⁿ) = 1 + (-1)ⁿ` cannot even be written down.  Nothing below mentions the Euler
characteristic; every statement is about the index sum of vector fields.

## The `ℝ¹` model

The tubular machinery of §6 (`Milnor.Tub`) is written for a submanifold of `ℝᴷ⁺¹` whose slice
charts have complement model `ℝᵐ`, whereas the sphere of §5 (`Milnor.Sphere.sphS`) is presented as
a level set of a real-valued function and so has complement model `ℝ`.  The first section below
therefore presents `Sⁿ` again as the zero set of an `ℝ¹`-valued function (`Milnor.Sphere.sphG1`),
giving `Milnor.Sphere.sphSub`, and proves for that structure the two facts about it that are
needed: its tangent space at `q` is `q^⊥` (`Milnor.Sphere.mem_range_mfd_val_iff`) and has dimension
`n` (`Milnor.Sphere.finrank_range_mfd_val`).
-/

open Set Filter Topology Function Module Metric
open scoped ContDiff Manifold RealInnerProductSpace

noncomputable section

namespace Milnor

/-- **The determinant of minus the identity** of a finite-dimensional real vector space is
`(-1)^dim`. -/
theorem det_neg_id {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V] :
    LinearMap.det (-LinearMap.id : V →ₗ[ℝ] V) = (-1) ^ finrank ℝ V := by
  rw [← neg_one_smul ℝ (LinearMap.id : V →ₗ[ℝ] V), LinearMap.det_smul, LinearMap.det_id, mul_one]

namespace Tub

variable {K d m : ℕ} {N : Set (EuclideanSpace ℝ (Fin (K + 1)))}
  (hN : IsSliceSubmanifold 𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1))) (EuclideanSpace ℝ (Fin (d + 1)))
    (EuclideanSpace ℝ (Fin m)) N) (hNc : IsCompact N) (hne : N.Nonempty)

/-- **The derivative through the retraction of a field that comes from the ambient space.**  If the
tangent field on `N` is the restriction of a smooth field `V` of `ℝᴷ⁺¹`, then Milnor's `dv_q`
(the derivative at `q` of `v ∘ r`) is `dV_q ∘ dr_q`; in particular it agrees with `dV_q` on the
tangent space, where `dr_q` is the identity. -/
theorem dvr_of_ambient {V : EuclideanSpace ℝ (Fin (K + 1)) → EuclideanSpace ℝ (Fin (K + 1))}
    (hV : ContDiff ℝ ∞ V) (q : N) :
    dvr hN hNc hne (fun p : N => V p.1) q = (fderiv ℝ V q.1).comp (dret hN hNc hne q) := by
  have hpt : (tubr hN hNc hne q.1).1 = q.1 := congrArg Subtype.val (tubr_val hN hNc hne q)
  have hout : HasFDerivAt V (fderiv ℝ V q.1) ((tubr hN hNc hne q.1).1) := by
    rw [hpt]
    exact ((hV.differentiable (by simp)) q.1).hasFDerivAt
  have hin : HasFDerivAt (fun y => (tubr hN hNc hne y).1) (dret hN hNc hne q) q.1 :=
    hasFDerivAt_tubr hN hNc hne (mem_Nε_of_mem hN hNc hne q.2)
  have h : HasFDerivAt (fun x => V (tubr hN hNc hne x).1)
      ((fderiv ℝ V q.1).comp (dret hN hNc hne q)) q.1 := hout.comp q.1 hin
  exact h.fderiv

end Tub

namespace Sphere

variable {n : ℕ}

/-! ### The sign of a power of `-1` -/

/-- The sign of `(-1)^k` is `(-1)^k`.  (A copy, for §6, of `Milnor.sgn_neg_one_pow` of §8.) -/
theorem sgn_neg_one_pow (k : ℕ) : sgn ((-1 : ℝ) ^ k) = (-1) ^ k := by
  rcases Nat.even_or_odd k with hk | hk
  · rw [hk.neg_one_pow, hk.neg_one_pow, sgn_one]
  · rw [hk.neg_one_pow, hk.neg_one_pow, sgn_neg (by norm_num)]

/-! ### The sphere as a slice submanifold with complement model `ℝ¹` -/

/-- The linear isomorphism `ℝ ≅ ℝ¹`, used to read the defining function `⟪x, x⟫ - 1` of the sphere
as a map with values in the model space `ℝ¹`. -/
def e1 : ℝ ≃L[ℝ] EuclideanSpace ℝ (Fin 1) :=
  ((EuclideanSpace.equiv (Fin 1) ℝ).trans (ContinuousLinearEquiv.funUnique (Fin 1) ℝ ℝ)).symm

/-- The defining function of the unit sphere, with values in `ℝ¹`. -/
def sphG1 (x : EuclideanSpace ℝ (Fin (n + 1))) : EuclideanSpace ℝ (Fin 1) := e1 (sphG x)

/-- `sphG1` is smooth. -/
theorem contMDiff_sphG1 : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))
    𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) ∞ (sphG1 (n := n)) :=
  contMDiff_iff_contDiff.2 ((e1 : ℝ →L[ℝ] EuclideanSpace ℝ (Fin 1)).contDiff.comp contDiff_sphG)

/-- The zero set of `sphG1` is the sphere. -/
theorem preimage_sphG1 : (sphG1 (n := n)) ⁻¹' {0} = Sph n := by
  ext x
  simp only [mem_preimage, mem_singleton_iff, sphG1]
  rw [← e1.map_zero]
  exact ⟨fun h => e1.injective h, fun h => by rw [h]⟩

/-- `0` is a regular value of `sphG1`. -/
theorem isRegularValue_sphG1 : IsRegularValue 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))
    𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) (sphG1 (n := n)) 0 := by
  intro x hx
  show Function.Surjective (mfderiv _ _ (sphG1 (n := n)) x)
  have hxS : x ∈ Sph n := by rw [← preimage_sphG1]; exact hx
  have h1 : Function.Surjective (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) 𝓘(ℝ, ℝ) sphG x) :=
    isRegularValue_sphG x hxS
  have h2 : mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) 𝓘(ℝ, EuclideanSpace ℝ (Fin 1))
      (sphG1 (n := n)) x =
      (e1 : ℝ →L[ℝ] EuclideanSpace ℝ (Fin 1)).comp
        (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) 𝓘(ℝ, ℝ) sphG x) := by
    rw [mfderiv_eq_fderiv, mfderiv_eq_fderiv]
    have hd : HasFDerivAt (sphG1 (n := n))
        ((e1 : ℝ →L[ℝ] EuclideanSpace ℝ (Fin 1)).comp (fderiv ℝ (sphG (n := n)) x)) x :=
      (e1 : ℝ →L[ℝ] EuclideanSpace ℝ (Fin 1)).hasFDerivAt.comp x
        ((contDiff_sphG.differentiable (by simp)) x).hasFDerivAt
    exact hd.fderiv
  rw [h2]
  exact e1.surjective.comp h1

/-- `dim ℝⁿ + dim ℝ¹ = dim ℝⁿ⁺¹`. -/
theorem finrank_add_one (n : ℕ) :
    finrank ℝ (EuclideanSpace ℝ (Fin n)) + finrank ℝ (EuclideanSpace ℝ (Fin 1))
      = finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) := by
  simp

/-- **The sphere as a slice submanifold of `ℝⁿ⁺¹` with complement model `ℝ¹`**, the structure the
tubular machinery of §6 works with.  (`Milnor.Sphere.sphS` is the same submanifold with complement
model `ℝ`.) -/
theorem sphSub (n : ℕ) : IsSliceSubmanifold 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))
    (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin 1)) (Sph n) := by
  rw [← preimage_sphG1]
  exact isSliceSubmanifold_preimage (Z := EuclideanSpace ℝ (Fin n)) (finrank_add_one n)
    contMDiff_sphG1 isRegularValue_sphG1

/-- The sphere is compact. -/
theorem isCompact_sph : IsCompact (Sph n) := by
  show IsCompact ((sphG (n := n)) ⁻¹' {0})
  rw [preimage_eq_sphere]
  exact isCompact_sphere 0 1

/-- The sphere is nonempty. -/
theorem nonempty_sph_set : (Sph n).Nonempty :=
  ⟨EuclideanSpace.single 0 1, by rw [mem_iff_norm]; simp⟩

/-! ### The tangent space of the sphere -/

/-- The derivative of the inclusion `Sⁿ → ℝⁿ⁺¹` is injective. -/
theorem injective_mfd_val (q : Sph n) :
    letI := (sphSub n).chartedSpace
    Function.Injective (mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))
      (Subtype.val : Sph n → EuclideanSpace ℝ (Fin (n + 1))) q) :=
  injective_mfderiv_val (sphSub n) q

/-- **The tangent space of `Sⁿ` has dimension `n`.** -/
theorem finrank_range_mfd_val (q : Sph n) :
    letI := (sphSub n).chartedSpace
    finrank ℝ (LinearMap.range ((mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))
      (Subtype.val : Sph n → EuclideanSpace ℝ (Fin (n + 1))) q :
        EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin (n + 1))))) = n :=
  (LinearMap.finrank_range_of_inj (injective_mfd_val q)).trans hZ

/-- **The tangent space of `Sⁿ` at `q` is the orthogonal complement of `q`**: a vector `w` of
`ℝⁿ⁺¹` is the image of a tangent vector under the derivative of the inclusion exactly when
`⟪q, w⟫ = 0`.  This is Milnor's Lemma 2 of §2 for the defining function `⟪x, x⟫ - 1`, whose
derivative at `q` is `w ↦ 2⟪q, w⟫`: the range of `dι_q` lies in the kernel because `sphG` is
constant on the sphere, and both have dimension `n`. -/
theorem mem_range_mfd_val_iff (q : Sph n) (w : EuclideanSpace ℝ (Fin (n + 1))) :
    letI := (sphSub n).chartedSpace
    w ∈ LinearMap.range ((mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))
      (Subtype.val : Sph n → EuclideanSpace ℝ (Fin (n + 1))) q :
        EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin (n + 1)))) ↔ ⟪q.1, w⟫ = 0 := by
  let := (sphSub n).chartedSpace
  have := (sphSub n).isManifold
  have hmf : mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) 𝓘(ℝ, ℝ) (sphG (n := n)) q.1
      = fderiv ℝ (sphG (n := n)) q.1 := mfderiv_eq_fderiv
  -- the range lies in the kernel of `d(sphG)_q`, because `sphG ∘ ι` is constant
  have hcomp : ∀ a, fderiv ℝ (sphG (n := n)) q.1
      (mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))
        (Subtype.val : Sph n → EuclideanSpace ℝ (Fin (n + 1))) q a) = 0 := by
    have hval : MDifferentiableAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
        𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))
        (Subtype.val : Sph n → EuclideanSpace ℝ (Fin (n + 1))) q :=
      (sphSub n).contMDiff_val.mdifferentiableAt (by simp)
    have hgd : MDifferentiableAt 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) 𝓘(ℝ, ℝ)
        (sphG (n := n)) q.1 := contMDiff_sphG.mdifferentiableAt (by simp)
    have hch : mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, ℝ)
        (sphG ∘ (Subtype.val : Sph n → EuclideanSpace ℝ (Fin (n + 1)))) q =
        (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) 𝓘(ℝ, ℝ) (sphG (n := n)) q.1).comp
          (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))
            (Subtype.val : Sph n → EuclideanSpace ℝ (Fin (n + 1))) q) :=
      mfderiv_comp q hgd hval
    have hconst : (sphG ∘ (Subtype.val : Sph n → EuclideanSpace ℝ (Fin (n + 1))))
        = fun _ => (0 : ℝ) := funext fun p => p.2
    rw [hconst, mfderiv_const] at hch
    intro a
    rw [← hmf]
    exact (congrArg (fun L : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ => L a) hch).symm
  have hle : LinearMap.range ((mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))
      (Subtype.val : Sph n → EuclideanSpace ℝ (Fin (n + 1))) q :
        EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin (n + 1)))) ≤
      LinearMap.ker ((fderiv ℝ (sphG (n := n)) q.1 :
        EuclideanSpace ℝ (Fin (n + 1)) →ₗ[ℝ] ℝ)) := by
    rintro _ ⟨a, rfl⟩
    simpa using hcomp a
  -- both have dimension `n`
  have hsurj : Function.Surjective (fderiv ℝ (sphG (n := n)) q.1) := by
    have h : Function.Surjective (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) 𝓘(ℝ, ℝ)
        (sphG (n := n)) q.1) := isRegularValue_sphG q.1 q.2
    rwa [mfderiv_eq_fderiv] at h
  have h2 : finrank ℝ (LinearMap.ker ((fderiv ℝ (sphG (n := n)) q.1 :
      EuclideanSpace ℝ (Fin (n + 1)) →ₗ[ℝ] ℝ))) = n := by
    have hrk := LinearMap.finrank_range_add_finrank_ker
      ((fderiv ℝ (sphG (n := n)) q.1 : EuclideanSpace ℝ (Fin (n + 1)) →ₗ[ℝ] ℝ))
    rw [LinearMap.range_eq_top.2 hsurj, finrank_top, hE] at hrk
    have h3 : finrank ℝ ℝ = 1 := Module.finrank_self ℝ
    omega
  have heq : LinearMap.range ((mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))
      (Subtype.val : Sph n → EuclideanSpace ℝ (Fin (n + 1))) q :
        EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin (n + 1)))) =
      LinearMap.ker ((fderiv ℝ (sphG (n := n)) q.1 :
        EuclideanSpace ℝ (Fin (n + 1)) →ₗ[ℝ] ℝ)) :=
    Submodule.eq_of_le_of_finrank_eq hle (by rw [finrank_range_mfd_val q, h2])
  rw [heq, LinearMap.mem_ker, ContinuousLinearMap.coe_coe, fderiv_sphG]
  constructor
  · intro h; linarith
  · intro h; rw [h]; ring

/-! ### Smooth fields on the sphere coming from the ambient space -/

/-- A smooth field of `ℝⁿ⁺¹` restricts to a smooth field on `Sⁿ`. -/
theorem contMDiff_of_ambient {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    {f : EuclideanSpace ℝ (Fin (n + 1)) → E'} (hf : ContDiff ℝ ∞ f) :
    letI := (sphSub n).chartedSpace
    ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, E') ∞ (fun q : Sph n => f q.1) := by
  let := (sphSub n).chartedSpace
  exact (contMDiff_iff_contDiff.2 hf).comp (sphSub n).contMDiff_val

/-! ### Milnor's field: the gradient of the height function -/

/-- **Milnor's field** (p. 39): the tangential part `e - ⟪e, x⟫ x` of the constant field `e`, read
on all of `ℝⁿ⁺¹`.  On `Sⁿ` it is the gradient of the height function `x ↦ ⟪e, x⟫`. -/
def gradHeight (e x : EuclideanSpace ℝ (Fin (n + 1))) : EuclideanSpace ℝ (Fin (n + 1)) :=
  e - ⟪e, x⟫ • x

/-- Milnor's field is smooth. -/
theorem contDiff_gradHeight (e : EuclideanSpace ℝ (Fin (n + 1))) : ContDiff ℝ ∞ (gradHeight e) :=
  contDiff_const.sub ((contDiff_const.inner (𝕜 := ℝ) contDiff_id).smul contDiff_id)

/-- Milnor's field is tangent to the sphere: `⟪x, v x⟫ = 0` for `x ∈ Sⁿ`. -/
theorem inner_gradHeight (e : EuclideanSpace ℝ (Fin (n + 1))) {x : EuclideanSpace ℝ (Fin (n + 1))}
    (hx : x ∈ Sph n) : ⟪x, gradHeight e x⟫ = 0 := by
  simp only [gradHeight, inner_sub_right, real_inner_smul_right, inner_self_eq_one_of_mem hx,
    mul_one]
  rw [real_inner_comm]
  ring

/-- **The derivative of Milnor's field**: `dv_x(u) = -(⟪e, x⟫ u + ⟪e, u⟫ x)`. -/
theorem fderiv_gradHeight_apply (e x u : EuclideanSpace ℝ (Fin (n + 1))) :
    fderiv ℝ (gradHeight e) x u = -(⟪e, x⟫ • u + ⟪e, u⟫ • x) := by
  have h1 : HasFDerivAt (fun y : EuclideanSpace ℝ (Fin (n + 1)) => ⟪e, y⟫) (innerSL ℝ e) x :=
    (innerSL ℝ e).hasFDerivAt
  have h2 := h1.smul (hasFDerivAt_id x)
  have h3 : HasFDerivAt (gradHeight e)
      (0 - (⟪e, x⟫ • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin (n + 1))) +
        (innerSL ℝ e).smulRight x)) x := (hasFDerivAt_const e x).sub h2
  rw [h3.fderiv]
  simp

/-- **The zeros of Milnor's field on `Sⁿ` are exactly `e` and `-e`.** -/
theorem gradHeight_eq_zero_iff {e x : EuclideanSpace ℝ (Fin (n + 1))} (he : e ∈ Sph n)
    (hx : x ∈ Sph n) : gradHeight e x = 0 ↔ x = e ∨ x = -e := by
  have hee : ⟪e, e⟫ = (1 : ℝ) := inner_self_eq_one_of_mem he
  constructor
  · intro h0
    have hex : e = ⟪e, x⟫ • x := by
      have := sub_eq_zero.1 h0
      exact this
    have hnorm : |⟪e, x⟫| = 1 := by
      have h1 : ‖e‖ = ‖⟪e, x⟫ • x‖ := congrArg (fun y => ‖y‖) hex
      rw [norm_smul, Real.norm_eq_abs, mem_iff_norm.1 hx, mul_one, mem_iff_norm.1 he] at h1
      exact h1.symm
    rcases abs_eq (by norm_num : (0:ℝ) ≤ 1) |>.1 hnorm with h1 | h1
    · left
      rw [hex, h1, one_smul]
    · right
      rw [hex, h1]
      module
  · intro hxe
    rcases hxe with hxe | hxe
    · rw [hxe]
      show e - ⟪e, e⟫ • e = 0
      rw [hee, one_smul, sub_self]
    · rw [hxe]
      show e - ⟪e, -e⟫ • (-e) = 0
      rw [inner_neg_right, hee]
      module

/-- Milnor's field, as a field on the sphere. -/
def gradSph (e : EuclideanSpace ℝ (Fin (n + 1))) (q : Sph n) : EuclideanSpace ℝ (Fin (n + 1)) :=
  gradHeight e q.1

/-- Milnor's field on `Sⁿ` is smooth. -/
theorem contMDiff_gradSph (e : EuclideanSpace ℝ (Fin (n + 1))) :
    letI := (sphSub n).chartedSpace
    ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) ∞
      (gradSph e) :=
  contMDiff_of_ambient (contDiff_gradHeight e)

/-- Milnor's field on `Sⁿ` is tangent, in the sense of `Milnor.Tub.poincare_hopf`. -/
theorem tangent_gradSph (e : EuclideanSpace ℝ (Fin (n + 1))) (q : Sph n) :
    letI := (sphSub n).chartedSpace
    gradSph e q ∈ LinearMap.range ((mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))
      (Subtype.val : Sph n → EuclideanSpace ℝ (Fin (n + 1))) q :
        EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin (n + 1)))) :=
  (mem_range_mfd_val_iff q (gradSph e q)).2 (inner_gradHeight e q.2)

/-! ### Milnor's field of §5 in ambient linear form -/

/-- **Milnor's field of §5 (p. 30), in ambient linear form.**  For `n` odd, pairing the coordinates
`(x_a, x_b) ↦ (x_b, -x_a)` gives a linear map `J` of `ℝⁿ⁺¹` with `⟪x, J x⟫ = 0` and
`⟪J x, J x⟫ = ⟪x, x⟫`.

`Milnor.Sphere.exists_nonvanishing_field` is the same construction, packaged as a vector field on
`Sⁿ` that is smooth for the slice structure of §5, whose complement model is `ℝ`; §6 works with
the structure whose complement model is `ℝ¹` (`Milnor.Sphere.sphSub`), and smoothness of a map out
of `Sⁿ` is a statement about a charted-space structure, so it does not transfer from one to the
other without an argument.  The construction is therefore repeated here in a form that mentions no
manifold structure at all, from which the field for either structure is a restriction of an
ambient smooth map. -/
theorem exists_perp_linear (hn : Odd n) :
    ∃ J : EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (n + 1)),
      (∀ x, ⟪x, J x⟫ = 0) ∧ ∀ x, ⟪J x, J x⟫ = ⟪x, x⟫ := by
  obtain ⟨m, hm⟩ := hn
  have h : n + 1 = (m + 1) + (m + 1) := by omega
  let e : Fin (n + 1) ≃ Fin (m + 1) ⊕ Fin (m + 1) := (finCongr h).trans finSumFinEquiv.symm
  let Jc : (Fin (n + 1) → ℝ) →L[ℝ] (Fin (n + 1) → ℝ) :=
    ContinuousLinearMap.pi fun i => Sum.elim
      (fun j => ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (n + 1) => ℝ)
        (e.symm (Sum.inr j)))
      (fun j => -ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (n + 1) => ℝ)
        (e.symm (Sum.inl j)))
      (e i)
  let J : EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (n + 1)) :=
    ((EuclideanSpace.equiv (Fin (n + 1)) ℝ).symm : (Fin (n + 1) → ℝ) →L[ℝ] _).comp
      (Jc.comp (EuclideanSpace.equiv (Fin (n + 1)) ℝ : _ →L[ℝ] (Fin (n + 1) → ℝ)))
  have hJ : ∀ (x : EuclideanSpace ℝ (Fin (n + 1))) (i : Fin (n + 1)), J x i =
      Sum.elim (fun j => x (e.symm (Sum.inr j))) (fun j => -x (e.symm (Sum.inl j))) (e i) := by
    intro x i
    simp only [J, Jc, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe]
    show (ContinuousLinearMap.pi _ (EuclideanSpace.equiv (Fin (n + 1)) ℝ x)) i = _
    rw [ContinuousLinearMap.pi_apply]
    rcases e i with j | j <;> simp
  have hsum : ∀ f : Fin (n + 1) → ℝ, ∑ i, f i =
      ∑ j : Fin (m + 1), f (e.symm (Sum.inl j)) + ∑ j : Fin (m + 1), f (e.symm (Sum.inr j)) := by
    intro f
    rw [← Fintype.sum_equiv e.symm (fun s => f (e.symm s)) f (fun _ => rfl), Fintype.sum_sum_type]
  have hinner : ∀ x y : EuclideanSpace ℝ (Fin (n + 1)), ⟪x, y⟫ = ∑ i, x i * y i := by
    intro x y
    simp [PiLp.inner_apply, mul_comm]
  refine ⟨J, fun x => ?_, fun x => ?_⟩
  · rw [hinner, hsum]
    simp only [hJ, Equiv.apply_symm_apply, Sum.elim_inl, Sum.elim_inr]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun j _ => ?_
    ring
  · rw [hinner, hinner, hsum, hsum (fun i => x i * x i)]
    simp only [hJ, Equiv.apply_symm_apply, Sum.elim_inl, Sum.elim_inr]
    rw [add_comm]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    ring

/-- **For `n` odd there is a nowhere-zero smooth tangent field on `Sⁿ`** (Milnor p. 30), for the
slice structure `Milnor.Sphere.sphSub` used in §6. -/
theorem exists_nonvanishing_tangent (hn : Odd n) :
    ∃ v : Sph n → EuclideanSpace ℝ (Fin (n + 1)),
      (letI := (sphSub n).chartedSpace;
        ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) ∞ v) ∧
      (∀ q : Sph n, ⟪q.1, v q⟫ = 0) ∧ ∀ q : Sph n, v q ≠ 0 := by
  obtain ⟨J, hperp, hnorm⟩ := exists_perp_linear hn
  refine ⟨fun q : Sph n => J q.1, contMDiff_of_ambient J.contDiff, fun q => hperp q.1,
    fun q h0 => ?_⟩
  have h1 : ⟪J q.1, J q.1⟫ = (1 : ℝ) := by rw [hnorm, inner_self_eq_one_of_mem q.2]
  rw [show J q.1 = 0 from h0] at h1
  simp at h1

/-! ### The index of Milnor's field at its two zeros -/

section Index

variable {d : ℕ} {e : EuclideanSpace ℝ (Fin (d + 1 + 1))}

/-- The tangent space of `Sⁿ` at `q`, in the form used by the tubular machinery. -/
theorem mem_tanN_iff (q : Sph (d + 1)) (w : EuclideanSpace ℝ (Fin (d + 1 + 1))) :
    w ∈ Tub.tanN (sphSub (d + 1)) q ↔ ⟪q.1, w⟫ = 0 :=
  mem_range_mfd_val_iff q w

/-- The tangent space of `Sⁿ` has dimension `n`, in the form used by the tubular machinery. -/
theorem finrank_tanN (q : Sph (d + 1)) : finrank ℝ (Tub.tanN (sphSub (d + 1)) q) = d + 1 :=
  finrank_range_mfd_val q

/-- Milnor's field on `Sⁿ` is a tangent field in the sense of `Milnor.Tub.IsTangent`. -/
theorem isTangent_gradSph (e : EuclideanSpace ℝ (Fin (d + 1 + 1))) :
    Tub.IsTangent (sphSub (d + 1)) (gradSph e) := fun q => tangent_gradSph e q

/-- **Milnor's `dv_q` for his field, on the tangent space**: `dv_q(t) = -(⟪e, q⟫ t + ⟪e, t⟫ q)`. -/
theorem dvr_gradSph_apply (e : EuclideanSpace ℝ (Fin (d + 1 + 1))) (q : Sph (d + 1))
    {t : EuclideanSpace ℝ (Fin (d + 1 + 1))} (ht : t ∈ Tub.tanN (sphSub (d + 1)) q) :
    Tub.dvr (sphSub (d + 1)) isCompact_sph nonempty_sph_set (gradSph e) q t
      = -(⟪e, q.1⟫ • t + ⟪e, t⟫ • q.1) := by
  have hdvr : Tub.dvr (sphSub (d + 1)) isCompact_sph nonempty_sph_set (gradSph e) q
      = (fderiv ℝ (gradHeight e) q.1).comp
        (Tub.dret (sphSub (d + 1)) isCompact_sph nonempty_sph_set q) :=
    Tub.dvr_of_ambient (sphSub (d + 1)) isCompact_sph nonempty_sph_set (contDiff_gradHeight e) q
  rw [hdvr]
  show fderiv ℝ (gradHeight e) q.1
    (Tub.dret (sphSub (d + 1)) isCompact_sph nonempty_sph_set q t) = _
  rw [Tub.dret_apply_of_mem_tanN (sphSub (d + 1)) isCompact_sph nonempty_sph_set q ht,
    fderiv_gradHeight_apply]

/-- Milnor's field vanishes at `e`. -/
theorem gradSph_eq_zero_pos (he : e ∈ Sph (d + 1)) :
    gradSph e (⟨e, he⟩ : Sph (d + 1)) = 0 :=
  (gradHeight_eq_zero_iff he he).2 (Or.inl rfl)

/-- Milnor's field vanishes at `-e`. -/
theorem gradSph_eq_zero_neg (he : e ∈ Sph (d + 1)) :
    gradSph e (⟨-e, neg_mem he⟩ : Sph (d + 1)) = 0 :=
  (gradHeight_eq_zero_iff he (neg_mem he)).2 (Or.inr rfl)

/-- **At `e` the derivative of Milnor's field is minus the identity of the tangent space.** -/
theorem dvT_gradSph_pos (he : e ∈ Sph (d + 1)) :
    Tub.dvT (sphSub (d + 1)) isCompact_sph nonempty_sph_set (gradSph e) (contMDiff_gradSph e)
      (isTangent_gradSph e) ⟨e, he⟩ (gradSph_eq_zero_pos he) = -LinearMap.id := by
  refine LinearMap.ext fun t => Subtype.ext ?_
  have hperp : ⟪e, (t : EuclideanSpace ℝ (Fin (d + 1 + 1)))⟫ = 0 :=
    (mem_tanN_iff (⟨e, he⟩ : Sph (d + 1)) t.1).1 t.2
  have h1 : ((Tub.dvT (sphSub (d + 1)) isCompact_sph nonempty_sph_set (gradSph e)
      (contMDiff_gradSph e) (isTangent_gradSph e) ⟨e, he⟩ (gradSph_eq_zero_pos he) t :
        Tub.tanN (sphSub (d + 1)) (⟨e, he⟩ : Sph (d + 1))) :
      EuclideanSpace ℝ (Fin (d + 1 + 1)))
      = Tub.dvr (sphSub (d + 1)) isCompact_sph nonempty_sph_set (gradSph e)
        (⟨e, he⟩ : Sph (d + 1)) t.1 := rfl
  rw [h1, dvr_gradSph_apply e (⟨e, he⟩ : Sph (d + 1)) t.2]
  show -(⟪e, e⟫ • (t : EuclideanSpace ℝ (Fin (d + 1 + 1))) + ⟪e, t.1⟫ • e) = _
  rw [hperp, inner_self_eq_one_of_mem he]
  simp

/-- **At `-e` the derivative of Milnor's field is the identity of the tangent space.** -/
theorem dvT_gradSph_neg (he : e ∈ Sph (d + 1)) :
    Tub.dvT (sphSub (d + 1)) isCompact_sph nonempty_sph_set (gradSph e) (contMDiff_gradSph e)
      (isTangent_gradSph e) ⟨-e, neg_mem he⟩ (gradSph_eq_zero_neg he) = LinearMap.id := by
  refine LinearMap.ext fun t => Subtype.ext ?_
  have hperp : ⟪e, (t : EuclideanSpace ℝ (Fin (d + 1 + 1)))⟫ = 0 := by
    have h := (mem_tanN_iff (⟨-e, neg_mem he⟩ : Sph (d + 1)) t.1).1 t.2
    show ⟪e, t.1⟫ = 0
    have h2 : ⟪-e, t.1⟫ = -⟪e, t.1⟫ := inner_neg_left e t.1
    rw [h2] at h
    linarith
  have h1 : ((Tub.dvT (sphSub (d + 1)) isCompact_sph nonempty_sph_set (gradSph e)
      (contMDiff_gradSph e) (isTangent_gradSph e) ⟨-e, neg_mem he⟩ (gradSph_eq_zero_neg he) t :
        Tub.tanN (sphSub (d + 1)) (⟨-e, neg_mem he⟩ : Sph (d + 1))) :
      EuclideanSpace ℝ (Fin (d + 1 + 1)))
      = Tub.dvr (sphSub (d + 1)) isCompact_sph nonempty_sph_set (gradSph e)
        (⟨-e, neg_mem he⟩ : Sph (d + 1)) t.1 := rfl
  rw [h1, dvr_gradSph_apply e (⟨-e, neg_mem he⟩ : Sph (d + 1)) t.2]
  show -(⟪e, -e⟫ • (t : EuclideanSpace ℝ (Fin (d + 1 + 1))) + ⟪e, t.1⟫ • (-e)) = _
  rw [hperp, inner_neg_right, inner_self_eq_one_of_mem he]
  simp

/-- **The index of Milnor's field at `e` is `(-1)ⁿ`.** -/
theorem indexN_gradSph_pos (he : e ∈ Sph (d + 1)) :
    Tub.indexN (sphSub (d + 1)) isCompact_sph nonempty_sph_set (gradSph e) (contMDiff_gradSph e)
      ⟨e, he⟩ = (-1) ^ (d + 1) := by
  have hdet : LinearMap.det (Tub.dvT (sphSub (d + 1)) isCompact_sph nonempty_sph_set (gradSph e)
      (contMDiff_gradSph e) (isTangent_gradSph e) ⟨e, he⟩ (gradSph_eq_zero_pos he))
      = (-1 : ℝ) ^ (d + 1) := by
    rw [dvT_gradSph_pos he, det_neg_id, finrank_tanN]
  have hbij : Function.Bijective (Tub.dvT (sphSub (d + 1)) isCompact_sph nonempty_sph_set
      (gradSph e) (contMDiff_gradSph e) (isTangent_gradSph e) ⟨e, he⟩
      (gradSph_eq_zero_pos he)) :=
    (bijective_iff_det_ne_zero _).2 (by rw [hdet]; exact pow_ne_zero _ (by norm_num))
  rw [Tub.indexN_eq_sgn_det (sphSub (d + 1)) isCompact_sph nonempty_sph_set (Nat.succ_pos d)
    (contMDiff_gradSph e) (isTangent_gradSph e) (gradSph_eq_zero_pos he) hbij, hdet,
    sgn_neg_one_pow]

/-- **The index of Milnor's field at `-e` is `1`.** -/
theorem indexN_gradSph_neg (he : e ∈ Sph (d + 1)) :
    Tub.indexN (sphSub (d + 1)) isCompact_sph nonempty_sph_set (gradSph e) (contMDiff_gradSph e)
      ⟨-e, neg_mem he⟩ = 1 := by
  have hdet : LinearMap.det (Tub.dvT (sphSub (d + 1)) isCompact_sph nonempty_sph_set (gradSph e)
      (contMDiff_gradSph e) (isTangent_gradSph e) ⟨-e, neg_mem he⟩ (gradSph_eq_zero_neg he))
      = (1 : ℝ) := by
    rw [dvT_gradSph_neg he, LinearMap.det_id]
  have hbij : Function.Bijective (Tub.dvT (sphSub (d + 1)) isCompact_sph nonempty_sph_set
      (gradSph e) (contMDiff_gradSph e) (isTangent_gradSph e) ⟨-e, neg_mem he⟩
      (gradSph_eq_zero_neg he)) :=
    (bijective_iff_det_ne_zero _).2 (by rw [hdet]; norm_num)
  rw [Tub.indexN_eq_sgn_det (sphSub (d + 1)) isCompact_sph nonempty_sph_set (Nat.succ_pos d)
    (contMDiff_gradSph e) (isTangent_gradSph e) (gradSph_eq_zero_neg he) hbij, hdet, sgn_one]

/-- **The index sum of Milnor's field on `Sⁿ` is `1 + (-1)ⁿ`**, `n = d + 1`: the sum of the two
indices `(-1)ⁿ` at `e` and `1` at `-e`. -/
theorem indexSum_gradSph (he : e ∈ Sph (d + 1)) :
    ∃ (z : Fin 2 → Sph (d + 1)) (_ : Function.Injective z)
      (_ : ∀ q, gradSph e q = 0 ↔ ∃ i, q = z i),
      ∑ i, Tub.indexN (sphSub (d + 1)) isCompact_sph nonempty_sph_set (gradSph e)
        (contMDiff_gradSph e) (z i) = 1 + (-1) ^ (d + 1) := by
  classical
  set A : Sph (d + 1) := ⟨e, he⟩ with hA
  set B : Sph (d + 1) := ⟨-e, neg_mem he⟩ with hB
  set z : Fin 2 → Sph (d + 1) := fun i => if i = 0 then A else B with hzdef
  have h0 : z 0 = A := if_pos rfl
  have h1 : z 1 = B := if_neg (by decide)
  have key : ∀ i : Fin 2, i = 0 ∨ i = 1 := by decide
  have hAB : A ≠ B := by
    intro h
    have hev : ⟪e, e⟫ = (1 : ℝ) := inner_self_eq_one_of_mem he
    have hee : e = -e := congrArg Subtype.val h
    have h2 : ⟪e, -e⟫ = -(1 : ℝ) := by rw [inner_neg_right, hev]
    rw [← hee, hev] at h2
    norm_num at h2
  refine ⟨z, ?_, ?_, ?_⟩
  · intro a b hab
    rcases key a with ha | ha <;> rcases key b with hb | hb <;> subst ha <;> subst hb
    · rfl
    · rw [h0, h1] at hab; exact absurd hab hAB
    · rw [h0, h1] at hab; exact absurd hab.symm hAB
    · rfl
  · intro q
    have hq : gradSph e q = 0 ↔ q.1 = e ∨ q.1 = -e := gradHeight_eq_zero_iff he q.2
    rw [hq]
    constructor
    · rintro (h | h)
      · exact ⟨0, by rw [h0, hA]; exact Subtype.ext h⟩
      · exact ⟨1, by rw [h1, hB]; exact Subtype.ext h⟩
    · rintro ⟨i, hi⟩
      rcases key i with hik | hik <;> subst hik
      · rw [h0, hA] at hi; exact Or.inl (congrArg Subtype.val hi)
      · rw [h1, hB] at hi; exact Or.inr (congrArg Subtype.val hi)
  · rw [Fin.sum_univ_two, h0, h1, hA, hB, indexN_gradSph_pos he, indexN_gradSph_neg he]
    ring

end Index

/-! ### The Euler number of the sphere -/

/-- **The Euler number of `Sⁿ` is `1 + (-1)ⁿ`** (Milnor, p. 39).  For `n ≥ 1` and *every* smooth
tangent vector field `v` on `Sⁿ` whose zeros are the finitely many distinct points `z₁, …, z_j`,
the sum of the indices of `v` at the `zᵢ` is `1 + (-1)ⁿ`.  Tangency is the hypothesis
`⟪q, v q⟫ = 0`, which for the sphere is exactly the condition of
`Milnor.Tub.poincare_hopf` (`Milnor.Sphere.mem_range_mfd_val_iff`).

This computes the integer of the Poincaré–Hopf theorem — Milnor's Euler *number*.  It does **not**
identify that integer with the Euler *characteristic* of `Sⁿ`; see the module docstring. -/
theorem indexSum_sph (hn : 0 < n) (v : Sph n → EuclideanSpace ℝ (Fin (n + 1)))
    (hv : letI := (sphSub n).chartedSpace;
      ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) ∞ v)
    (hvT : ∀ q : Sph n, ⟪q.1, v q⟫ = 0) {j : ℕ} (z : Fin j → Sph n) (hz : Function.Injective z)
    (hzero : ∀ q, v q = 0 ↔ ∃ i, q = z i) :
    ∑ i, Tub.indexN (sphSub n) isCompact_sph nonempty_sph_set v hv (z i) = 1 + (-1) ^ n := by
  obtain ⟨d, rfl⟩ : ∃ d, n = d + 1 := ⟨n - 1, by omega⟩
  obtain ⟨χ, hχ⟩ := Tub.poincare_hopf (sphSub (d + 1)) isCompact_sph nonempty_sph_set
    (Nat.succ_pos d)
  -- the value of `χ`, from Milnor's field
  set e : EuclideanSpace ℝ (Fin (d + 1 + 1)) := EuclideanSpace.single 0 1 with hedef
  have he : e ∈ Sph (d + 1) := by rw [mem_iff_norm, hedef]; simp
  obtain ⟨z₀, hz₀, hzero₀, hsum₀⟩ := indexSum_gradSph he
  have hχval : χ = 1 + (-1) ^ (d + 1) := by
    rw [← hsum₀]
    exact (hχ (gradSph e) (contMDiff_gradSph e) (tangent_gradSph e) z₀ hz₀ hzero₀).symm
  rw [hχ v hv (fun q => (mem_range_mfd_val_iff q (v q)).2 (hvT q)) z hz hzero, hχval]

/-- **The integer of the Poincaré–Hopf theorem for `Sⁿ`, with its value.**  The same statement as
`Milnor.Tub.poincare_hopf` specialized to the sphere, together with the value `1 + (-1)ⁿ` of the
integer whose existence it asserts. -/
theorem poincare_hopf_sph (hn : 0 < n) :
    ∃ χN : ℤ, χN = 1 + (-1) ^ n ∧ ∀ (v : Sph n → EuclideanSpace ℝ (Fin (n + 1)))
      (hv : letI := (sphSub n).chartedSpace;
        ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) ∞ v)
      (_ : ∀ q : Sph n, ⟪q.1, v q⟫ = 0) {j : ℕ} (z : Fin j → Sph n)
      (_ : Function.Injective z) (_ : ∀ q, v q = 0 ↔ ∃ i, q = z i),
      ∑ i, Tub.indexN (sphSub n) isCompact_sph nonempty_sph_set v hv (z i) = χN := by
  refine ⟨1 + (-1) ^ n, rfl, ?_⟩
  intro v hv hvT j z hz hzero
  exact indexSum_sph hn v hv hvT z hz hzero

/-- **The integer is pinned down.**  Any integer with the property that `Milnor.Tub.poincare_hopf`
asserts of `χ(N)` — being the index sum of every smooth tangent field on `Sⁿ` with finitely many
zeros — equals `1 + (-1)ⁿ`, because Milnor's field has that index sum. -/
theorem eq_of_indexSum_sph (hn : 0 < n) {χN : ℤ}
    (h : ∀ (v : Sph n → EuclideanSpace ℝ (Fin (n + 1)))
      (hv : letI := (sphSub n).chartedSpace;
        ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) ∞ v)
      (_ : ∀ q : Sph n, ⟪q.1, v q⟫ = 0) {j : ℕ} (z : Fin j → Sph n)
      (_ : Function.Injective z) (_ : ∀ q, v q = 0 ↔ ∃ i, q = z i),
      ∑ i, Tub.indexN (sphSub n) isCompact_sph nonempty_sph_set v hv (z i) = χN) :
    χN = 1 + (-1) ^ n := by
  obtain ⟨d, rfl⟩ : ∃ d, n = d + 1 := ⟨n - 1, by omega⟩
  set e : EuclideanSpace ℝ (Fin (d + 1 + 1)) := EuclideanSpace.single 0 1 with hedef
  have he : e ∈ Sph (d + 1) := by rw [mem_iff_norm, hedef]; simp
  obtain ⟨z₀, hz₀, hzero₀, hsum₀⟩ := indexSum_gradSph he
  rw [← h (gradSph e) (contMDiff_gradSph e) (fun q => inner_gradHeight e q.2) z₀ hz₀ hzero₀]
  exact hsum₀

/-- **The Euler number of an even-dimensional sphere is `2`** (Milnor, p. 39). -/
theorem indexSum_sph_even (hn : 0 < n) (hev : Even n) (v : Sph n → EuclideanSpace ℝ (Fin (n + 1)))
    (hv : letI := (sphSub n).chartedSpace;
      ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) ∞ v)
    (hvT : ∀ q : Sph n, ⟪q.1, v q⟫ = 0) {j : ℕ} (z : Fin j → Sph n) (hz : Function.Injective z)
    (hzero : ∀ q, v q = 0 ↔ ∃ i, q = z i) :
    ∑ i, Tub.indexN (sphSub n) isCompact_sph nonempty_sph_set v hv (z i) = 2 := by
  rw [indexSum_sph hn v hv hvT z hz hzero, hev.neg_one_pow]
  norm_num

/-- **The Euler number of an odd-dimensional sphere is `0`** (Milnor, p. 39). -/
theorem indexSum_sph_odd (hn : 0 < n) (hod : Odd n) (v : Sph n → EuclideanSpace ℝ (Fin (n + 1)))
    (hv : letI := (sphSub n).chartedSpace;
      ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) ∞ v)
    (hvT : ∀ q : Sph n, ⟪q.1, v q⟫ = 0) {j : ℕ} (z : Fin j → Sph n) (hz : Function.Injective z)
    (hzero : ∀ q, v q = 0 ↔ ∃ i, q = z i) :
    ∑ i, Tub.indexN (sphSub n) isCompact_sph nonempty_sph_set v hv (z i) = 0 := by
  rw [indexSum_sph hn v hv hvT z hz hzero, hod.neg_one_pow]
  ring

/-- **The Euler number of `Sⁿ` is even** (Milnor, p. 39). -/
theorem even_indexSum_sph (hn : 0 < n) (v : Sph n → EuclideanSpace ℝ (Fin (n + 1)))
    (hv : letI := (sphSub n).chartedSpace;
      ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) ∞ v)
    (hvT : ∀ q : Sph n, ⟪q.1, v q⟫ = 0) {j : ℕ} (z : Fin j → Sph n) (hz : Function.Injective z)
    (hzero : ∀ q, v q = 0 ↔ ∃ i, q = z i) :
    Even (∑ i, Tub.indexN (sphSub n) isCompact_sph nonempty_sph_set v hv (z i)) := by
  rw [indexSum_sph hn v hv hvT z hz hzero]
  rcases Nat.even_or_odd n with hp | hp
  · rw [hp.neg_one_pow]; exact ⟨1, rfl⟩
  · rw [hp.neg_one_pow]; exact ⟨0, rfl⟩

/-! ### The odd case, a second time -/

/-- **The odd case, computed independently of the derivatives** (Milnor, §5, p. 30): for `n` odd
the sphere carries a nowhere-zero smooth tangent field, whose family of zeros is empty, so the
index sum of every smooth tangent field on `Sⁿ` with finitely many zeros is the empty sum `0`.
The derivative computation is not used. -/
theorem indexSum_sph_of_nonvanishing (hn : 0 < n) (hod : Odd n)
    (v : Sph n → EuclideanSpace ℝ (Fin (n + 1)))
    (hv : letI := (sphSub n).chartedSpace;
      ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) ∞ v)
    (hvT : ∀ q : Sph n, ⟪q.1, v q⟫ = 0) {j : ℕ} (z : Fin j → Sph n) (hz : Function.Injective z)
    (hzero : ∀ q, v q = 0 ↔ ∃ i, q = z i) :
    ∑ i, Tub.indexN (sphSub n) isCompact_sph nonempty_sph_set v hv (z i) = 0 := by
  obtain ⟨χ, hχ⟩ := Tub.poincare_hopf (sphSub n) isCompact_sph nonempty_sph_set hn
  obtain ⟨v₀, hv₀, ht₀, hne₀⟩ := exists_nonvanishing_tangent hod
  have hχ0 := hχ v₀ hv₀ (fun q => (mem_range_mfd_val_iff q (v₀ q)).2 (ht₀ q))
    (j := 0) (fun i => i.elim0) (fun a _ _ => a.elim0)
    (fun q => ⟨fun h => absurd h (hne₀ q), fun h => h.elim fun i _ => i.elim0⟩)
  rw [hχ v hv (fun q => (mem_range_mfd_val_iff q (v q)).2 (hvT q)) z hz hzero, ← hχ0]
  simp

/-- **The two computations of the odd case agree.**  Applying both
`Milnor.Sphere.indexSum_sph` — the index sum is `1 + (-1)ⁿ` — and
`Milnor.Sphere.indexSum_sph_of_nonvanishing` — the index sum is `0` — to a nowhere-zero tangent
field on an odd-dimensional sphere gives `1 + (-1)ⁿ = 0`, as it must. -/
theorem indexSum_sph_odd_agree (hn : 0 < n) (hod : Odd n) : (1 : ℤ) + (-1) ^ n = 0 := by
  obtain ⟨v₀, hv₀, ht₀, hne₀⟩ := exists_nonvanishing_tangent hod
  have hz : Function.Injective (fun i : Fin 0 => (i.elim0 : Sph n)) := fun a _ _ => a.elim0
  have hzero : ∀ q, v₀ q = 0 ↔ ∃ i : Fin 0, q = (fun i : Fin 0 => (i.elim0 : Sph n)) i :=
    fun q => ⟨fun h => absurd h (hne₀ q), fun h => h.elim fun i _ => i.elim0⟩
  have h1 := indexSum_sph hn v₀ hv₀ ht₀ (fun i : Fin 0 => (i.elim0 : Sph n)) hz hzero
  have h2 := indexSum_sph_of_nonvanishing hn hod v₀ hv₀ ht₀
    (fun i : Fin 0 => (i.elim0 : Sph n)) hz hzero
  rw [h2] at h1
  exact h1.symm

end Sphere

end Milnor
