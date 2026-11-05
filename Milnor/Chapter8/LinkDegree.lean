import Milnor.Chapter8.PreimOrient
import Milnor.Chapter8.LinkingDefs
import Milnor.Chapter8.ProperDegree
import Milnor.Chapter8.LinkAlg

/-!
# Linking numbers of preimages are local degrees (Milnor §8, Problem 14)

The key technical step for the Hopf invariant.  Let `S = S^{2d+1}` (written `Sph (d + (d + 1))`)
and let `g, f : S → S^{d+1}` be smooth with regular values `y` of `g` and `z` of `f`.  The
preimages carry the orientations `preimOr` (for positive bases `ey`, `ez` of the tangent spaces at
`y` and `z`), and `linkingNumberRot` is their linking number after a rotation `R` of `ℝ^{2d+2}`
and the stereographic projection `stN` from the north pole.

* `domR R ⊆ S × S`: the open set of pairs `(x, x')` with `R x ≠ north`, `R x' ≠ north`, `x ≠ x'`;
* `phiR g f R (x, x') = ((g x, f x'), λ(x, x'))`, `λ(x, x') = nv0 (stN (R x) − stN (R x'))`,
  smooth on `domR R` (`contMDiffAt_phiR`);
* `orDomR R`, `orTarget`: the product orientations of `domR R ⊆ S × S` and of
  `(S^{d+1} × S^{d+1}) × S^{2d}`;
* `isRegularValue_phiR`, `degAt_phiR_eq_linkingNumberRot`: if `g⁻¹(y)` and `f⁻¹(z)` are disjoint
  and avoid `R⁻¹(north)`, and `e` is a regular value of their linking map, then `((y, z), e)` is a
  regular value of `Φ = phiR g f R ∘ Subtype.val` on `domR R`, and the local degree of `Φ` at
  `((y, z), e)` is the linking number;
* `linkingNumberRot_eq_of_homotopy`: the linking number is invariant under homotopies of `g` and
  `f` during which the preimages stay disjoint and away from `R⁻¹(north)`.

**The degree formula.**  `(x, x') ↦ (x, x')` maps the preimage of `e` under the linking map of
`g⁻¹(y) × f⁻¹(z)` bijectively onto the preimage of `((y, z), e)` under `Φ`.  At corresponding
points `dΦ = ((dg, df), dλ)`, the derivative of the linking map is `dλ ∘ (dι × dι')` for the
inclusions `ι, ι'` of the preimages, and `range dι = ker dg`, `range dι' = ker df`.  By
`preimOr_or_eq` the preimage orientations are frame orientations for lifts of `ey`, `ez`, and the
block computation `LinkDeg.orSign_pair_preimage₂` (the version of `orSign_pair_preimage` with
different ambient orientations at `x` and `x'`) shows that the signs agree, the factor being
`(-1)^(d (d+1)) = 1` (`LinkDeg.signAt_phiR_eq`).

**Homotopy invariance.**  Choose `e` regular for the linking maps at both ends (their regular
values are open and dense), and closed neighbourhoods `V₁ ∋ y`, `V₂ ∋ z` whose preimages under
`G_t`, `F_t` (`t ∈ [0, 1]`) still give pairs in `domR R` (a compactness argument,
`LinkDeg.exists_isClosed_nhds_domR`).  Then the part of the preimage of `V₁ × V₂ × S^{2d}` under
the homotopy `Φ_t` over `[0, 1]` is compact, and `degAt_eq_of_homotopy_of_isCompact` applies.

Auxiliary definitions and lemmas live in the namespace `Milnor.Problems.LinkDeg`.
-/

open Set Filter Topology Function Module TopologicalSpace
open scoped ContDiff Manifold RealInnerProductSpace

noncomputable section

namespace Milnor

namespace Problems

open Sphere Framed

local notation "𝔼 " n:max => EuclideanSpace ℝ (Fin n)

variable {d : ℕ}

/-! ### The domain `D_R` and the map `Φ` -/

/-- The open set `D_R ⊆ S × S` where both points avoid `R⁻¹(north)` and are distinct. -/
def domR (R : 𝔼 (d + d + 2) ≃ₗᵢ[ℝ] 𝔼 (d + d + 2)) :
    Opens (Sph (d + (d + 1)) × Sph (d + (d + 1))) where
  carrier := {q | R q.1.1 ≠ (north : Sph (d + d + 1)).1 ∧
    R q.2.1 ≠ (north : Sph (d + d + 1)).1 ∧ q.1 ≠ q.2}
  is_open' := by
    refine IsOpen.and ?_ (IsOpen.and ?_ ?_)
    · exact isOpen_ne_fun (R.continuous.comp (continuous_subtype_val.comp continuous_fst))
        continuous_const
    · exact isOpen_ne_fun (R.continuous.comp (continuous_subtype_val.comp continuous_snd))
        continuous_const
    · exact isOpen_ne_fun continuous_fst continuous_snd

theorem mem_domR {R : 𝔼 (d + d + 2) ≃ₗᵢ[ℝ] 𝔼 (d + d + 2)}
    {q : Sph (d + (d + 1)) × Sph (d + (d + 1))} :
    q ∈ domR R ↔ R q.1.1 ≠ (north : Sph (d + d + 1)).1 ∧
      R q.2.1 ≠ (north : Sph (d + d + 1)).1 ∧ q.1 ≠ q.2 := Iff.rfl

namespace LinkDeg

/-- The direction map `λ(x, x') = nv0 (stN (R x) − stN (R x'))` on `S × S`. -/
def lamR (R : 𝔼 (d + d + 2) ≃ₗᵢ[ℝ] 𝔼 (d + d + 2))
    (q : Sph (d + (d + 1)) × Sph (d + (d + 1))) : Sph (d + d) :=
  nv0 (stN (R q.1.1) - stN (R q.2.1))

theorem contMDiffAt_stN_rot (R : 𝔼 (d + d + 2) ≃ₗᵢ[ℝ] 𝔼 (d + d + 2))
    {x : Sph (d + (d + 1))} (hx : R x.1 ≠ (north : Sph (d + d + 1)).1) :
    ContMDiffAt 𝓘(ℝ, 𝔼 (d + (d + 1))) 𝓘(ℝ, 𝔼 (d + d + 1)) ∞
      (fun x : Sph (d + (d + 1)) => stN (R x.1)) x := by
  have hR : ContMDiff 𝓘(ℝ, 𝔼 (d + (d + 1))) 𝓘(ℝ, 𝔼 (d + d + 2)) ∞
      (fun x : Sph (d + (d + 1)) => R x.1) :=
    (R.toContinuousLinearEquiv.toContinuousLinearMap.contDiff.contMDiff).comp contMDiff_val
  have hlast : (R x.1) (Fin.last (d + d + 1)) ≠ 1 :=
    (last_lt_one_of_mem_of_ne (k := d + d) (rotation_mem_sph R x) hx).ne
  exact ContMDiffAt.comp (g := stN) (f := fun x : Sph (d + (d + 1)) => R x.1) x
    (contDiffAt_stN hlast).contMDiffAt (hR x)

/-- `λ` is smooth on `D_R`. -/
theorem contMDiffAt_lamR {R : 𝔼 (d + d + 2) ≃ₗᵢ[ℝ] 𝔼 (d + d + 2)}
    {q : Sph (d + (d + 1)) × Sph (d + (d + 1))} (hq : q ∈ domR R) :
    ContMDiffAt ((𝓘(ℝ, 𝔼 (d + (d + 1)))).prod 𝓘(ℝ, 𝔼 (d + (d + 1)))) 𝓘(ℝ, 𝔼 (d + d)) ∞
      (lamR R) q := by
  refine contMDiffAt_nv0_comp (p := d + d)
    (w := fun q : Sph (d + (d + 1)) × Sph (d + (d + 1)) => stN (R q.1.1) - stN (R q.2.1))
    (domR R) (fun q hq => ?_) (fun q hq => ?_) hq
  · exact ((contMDiffAt_stN_rot R (mem_domR.1 hq).1).comp q contMDiffAt_fst).sub
      ((contMDiffAt_stN_rot R (mem_domR.1 hq).2.1).comp q contMDiffAt_snd)
  · have hq' := mem_domR.1 hq
    have hu : (⟨R q.1.1, rotation_mem_sph R q.1⟩ : Sph (d + d + 1)) ≠ north :=
      fun h => hq'.1 (congrArg Subtype.val h)
    have hv : (⟨R q.2.1, rotation_mem_sph R q.2⟩ : Sph (d + d + 1)) ≠ north :=
      fun h => hq'.2.1 (congrArg Subtype.val h)
    have huv : (⟨R q.1.1, rotation_mem_sph R q.1⟩ : Sph (d + d + 1)) ≠
        ⟨R q.2.1, rotation_mem_sph R q.2⟩ := fun h =>
      hq'.2.2 (Subtype.ext (R.injective (congrArg Subtype.val h)))
    -- elaborate first, then compare (unifying against the goal directly unfolds `stN`)
    have h := stN_sub_ne_zero hu hv huv
    exact h

end LinkDeg

open LinkDeg

/-- `Φ(x, x') = ((g x, f x'), nv0 (stN (R x) − stN (R x')))`, a total function on `S × S`
(junk off `D_R`); the map of Problem 14 is its restriction `phiR g f R ∘ Subtype.val` to
`domR R`. -/
def phiR (g f : Sph (d + (d + 1)) → Sph (d + 1)) (R : 𝔼 (d + d + 2) ≃ₗᵢ[ℝ] 𝔼 (d + d + 2))
    (q : Sph (d + (d + 1)) × Sph (d + (d + 1))) : (Sph (d + 1) × Sph (d + 1)) × Sph (d + d) :=
  ((g q.1, f q.2), nv0 (stN (R q.1.1) - stN (R q.2.1)))

/-- `Φ` is smooth on `D_R`. -/
theorem contMDiffAt_phiR {g f : Sph (d + (d + 1)) → Sph (d + 1)}
    (hg : ContMDiff 𝓘(ℝ, 𝔼 (d + (d + 1))) 𝓘(ℝ, 𝔼 (d + 1)) ∞ g)
    (hf : ContMDiff 𝓘(ℝ, 𝔼 (d + (d + 1))) 𝓘(ℝ, 𝔼 (d + 1)) ∞ f)
    {R : 𝔼 (d + d + 2) ≃ₗᵢ[ℝ] 𝔼 (d + d + 2)}
    (q : Sph (d + (d + 1)) × Sph (d + (d + 1))) (hq : q ∈ domR R) :
    ContMDiffAt ((𝓘(ℝ, 𝔼 (d + (d + 1)))).prod 𝓘(ℝ, 𝔼 (d + (d + 1))))
      ((𝓘(ℝ, 𝔼 (d + 1)).prod 𝓘(ℝ, 𝔼 (d + 1))).prod 𝓘(ℝ, 𝔼 (d + d))) ∞
      (phiR g f R) q :=
  (((hg.comp contMDiff_fst).prodMk (hf.comp contMDiff_snd)) q).prodMk (contMDiffAt_lamR hq)

/-! ### The orientations -/

/-- The product orientation of `S × S`, restricted to `D_R` (index
`(d + (d+1)) + (d + (d+1))` cast to `((d+1) + (d+1)) + (d + d)`). -/
def orDomR (R : 𝔼 (d + d + 2) ≃ₗᵢ[ℝ] 𝔼 (d + d + 2)) :
    Orient ((𝓘(ℝ, 𝔼 (d + (d + 1)))).prod 𝓘(ℝ, 𝔼 (d + (d + 1)))) (domR R)
      (((d + 1) + (d + 1)) + (d + d)) :=
  (((sphOrStd (d + (d + 1))).prod hZ hZ (sphOrStd (d + (d + 1)))).restrict (domR R)).cast
    (by omega)

/-- The product orientation of `(S^{d+1} × S^{d+1}) × S^{2d}`. -/
def orTarget :
    Orient ((𝓘(ℝ, 𝔼 (d + 1)).prod 𝓘(ℝ, 𝔼 (d + 1))).prod 𝓘(ℝ, 𝔼 (d + d)))
      ((Sph (d + 1) × Sph (d + 1)) × Sph (d + d)) (((d + 1) + (d + 1)) + (d + d)) :=
  ((sphOrStd (d + 1)).prod hZ hZ (sphOrStd (d + 1))).prod (finrank_prod_eq hZ hZ) hZ
    (sphOrStd (d + d))

/-! ### Linear algebra: two preimages with different ambient orientations -/

namespace LinkDeg

open LinkAlg

section linear

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
  {Z' : Type*} [NormedAddCommGroup Z'] [NormedSpace ℝ Z'] [FiniteDimensional ℝ Z']
  {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G] {d p k : ℕ}

/-- `orSign_pair_preimage` (`LinkAlg.lean`) with independent orientations `oV, oV'` of the two
source factors and `oF, oF'` of the two target factors: the sign of
`(x, x') ↦ ((D x, D' x'), L (x, x'))` is `(-1)^(d p)` times the sign of `L ∘ (ι × ι')`. -/
theorem orSign_pair_preimage₂ (hk : d + d = k) (hdim : (d + p) + (d + p) = (p + p) + k)
    (hV : finrank ℝ V = d + p) (hF : finrank ℝ F = p) (hZ : finrank ℝ Z = d)
    (hZ' : finrank ℝ Z' = d) (hG : finrank ℝ G = k)
    (oV oV' : Orientation ℝ V (Fin (d + p))) (oF oF' : Orientation ℝ F (Fin p))
    (oG : Orientation ℝ G (Fin k))
    (ι : Z →L[ℝ] V) (D : V →L[ℝ] F) (hι : Function.Injective ι)
    (hker : LinearMap.range (ι : Z →ₗ[ℝ] V) = LinearMap.ker (D : V →ₗ[ℝ] F))
    (u : Fin p → V) (hu : LinearIndependent ℝ (fun i => D (u i)))
    (huo : (basisOfLinearIndependentOfCardEqFinrank' _ hu (by simp [hF])).orientation = oF)
    (ι' : Z' →L[ℝ] V) (D' : V →L[ℝ] F) (hι' : Function.Injective ι')
    (hker' : LinearMap.range (ι' : Z' →ₗ[ℝ] V) = LinearMap.ker (D' : V →ₗ[ℝ] F))
    (u' : Fin p → V) (hu' : LinearIndependent ℝ (fun i => D' (u' i)))
    (huo' : (basisOfLinearIndependentOfCardEqFinrank' _ hu' (by simp [hF])).orientation = oF')
    (L : V × V →L[ℝ] G) :
    orSign (Orientation.reindex ℝ (V × V) (finCongr hdim) (orProdGen hV hV oV oV'))
        (orProdGen (finrank_prod_eq hF hF) hG (orProdGen hF hF oF oF') oG)
        ((D.prodMap D').prod L) =
      (-1) ^ (d * p) *
        orSign (Orientation.reindex ℝ (Z × Z') (finCongr hk)
            (orProdGen hZ hZ' (frameOr hZ oV u ι) (frameOr hZ' oV' u' ι')))
          oG (L.comp (ι.prodMap ι')) := by
  have hdim₁ : (d + p) + (d + p) = p + (p + k) := by omega
  have hk₁ : d + (d + p) = p + k := by omega
  -- compose with the associator `(F × F) × G → F × (F × G)`
  have h1 := orSign_comp ((finrank_prod_eq hV hV).trans hdim)
    (finrank_prod_eq (finrank_prod_eq hF hF) hG)
    (Orientation.reindex ℝ (V × V) (finCongr hdim) (orProdGen hV hV oV oV'))
    (orProdGen (finrank_prod_eq hF hF) hG (orProdGen hF hF oF oF') oG)
    (Orientation.reindex ℝ (F × F × G) (finCongr (Nat.add_assoc p p k).symm)
      (orProdGen hF (finrank_prod_eq hF hG) oF (orProdGen hF hG oF' oG)))
    ((D.prodMap D').prod L)
    (((ContinuousLinearMap.fst ℝ F F).comp (ContinuousLinearMap.fst ℝ (F × F) G)).prod
        (((ContinuousLinearMap.snd ℝ F F).comp (ContinuousLinearMap.fst ℝ (F × F) G)).prod
          (ContinuousLinearMap.snd ℝ (F × F) G)))
  have hT : (((ContinuousLinearMap.fst ℝ F F).comp (ContinuousLinearMap.fst ℝ (F × F) G)).prod
        (((ContinuousLinearMap.snd ℝ F F).comp (ContinuousLinearMap.fst ℝ (F × F) G)).prod
          (ContinuousLinearMap.snd ℝ (F × F) G))).comp ((D.prodMap D').prod L) =
      (D.comp (ContinuousLinearMap.fst ℝ V V)).prod
        ((D'.comp (ContinuousLinearMap.snd ℝ V V)).prod L) := by
    refine ContinuousLinearMap.ext fun x => ?_
    simp
  rw [hT, orSign_prodAssoc, one_mul,
    orSign_reindex_reindex' hdim (Nat.add_assoc p p k).symm hdim₁] at h1
  -- the first preimage, with `W = V` oriented by `oV'`
  rw [← h1, orSign_single_preimage hk₁ hdim₁ hV hF hZ (finrank_prod_eq hF hG) hV oV oF
    (orProdGen hF hG oF' oG) oV' ι D hι hker u hu huo]
  have hL : ((D'.comp (ContinuousLinearMap.snd ℝ V V)).prod L).comp
      (ι.prodMap (ContinuousLinearMap.id ℝ V)) =
      (D'.comp (ContinuousLinearMap.snd ℝ Z V)).prod
        (L.comp (ι.prodMap (ContinuousLinearMap.id ℝ V))) := by
    refine ContinuousLinearMap.ext fun x => ?_
    simp
  -- the second preimage, with `W = Z`
  rw [hL, orSign_single_preimage_right hk hk₁ hV hF hZ' hG hZ oV' oF' oG (frameOr hZ oV u ι)
    ι' D' hι' hker' u' hu' huo']
  have hL' : (L.comp (ι.prodMap (ContinuousLinearMap.id ℝ V))).comp
      ((ContinuousLinearMap.id ℝ Z).prodMap ι') = L.comp (ι.prodMap ι') := by
    refine ContinuousLinearMap.ext fun x => ?_
    rcases x with ⟨x₁, x₂⟩
    simp
  rw [hL']

end linear

/-! ### Signs at corresponding points -/

section preim

variable {g f : Sph (d + (d + 1)) → Sph (d + 1)}
  (hg : ContMDiff 𝓘(ℝ, 𝔼 (d + (d + 1))) 𝓘(ℝ, 𝔼 (d + 1)) ∞ g)
  (hf : ContMDiff 𝓘(ℝ, 𝔼 (d + (d + 1))) 𝓘(ℝ, 𝔼 (d + 1)) ∞ f)
  {y z : Sph (d + 1)}
  (hy : IsRegularValue 𝓘(ℝ, 𝔼 (d + (d + 1))) 𝓘(ℝ, 𝔼 (d + 1)) g y)
  (hz : IsRegularValue 𝓘(ℝ, 𝔼 (d + (d + 1))) 𝓘(ℝ, 𝔼 (d + 1)) f z)

include hg hy in
/-- The tangent space of `g⁻¹(y)` is the kernel of `dg`. -/
theorem range_mfd_val_eq_ker (q : g ⁻¹' {y}) :
    letI := (isSliceSubmanifold_preim hg hy).chartedSpace
    LinearMap.range (mfd 𝓘(ℝ, 𝔼 d) 𝓘(ℝ, 𝔼 (d + (d + 1)))
        (Subtype.val : g ⁻¹' {y} → Sph (d + (d + 1))) q : 𝔼 d →ₗ[ℝ] 𝔼 (d + (d + 1))) =
      LinearMap.ker (mfd 𝓘(ℝ, 𝔼 (d + (d + 1))) 𝓘(ℝ, 𝔼 (d + 1)) g q.1 :
        𝔼 (d + (d + 1)) →ₗ[ℝ] 𝔼 (d + 1)) := by
  let _ := (isSliceSubmanifold_preim hg hy).chartedSpace
  ext v
  rw [LinearMap.mem_range, LinearMap.mem_ker]
  exact mem_range_mfderiv_val_iff preimDim hg hy q v

include hg hf hy hz in
/-- **Equality of signs at corresponding points.**  At `q = (x, x') ∈ D_R` with `x ∈ g⁻¹(y)` and
`x' ∈ f⁻¹(z)`, the sign of `Φ` equals the sign of the linking map of the preimages. -/
theorem signAt_phiR_eq (ey : Basis (Fin (d + 1)) ℝ (𝔼 (d + 1)))
    (hey : ey.orientation = (sphOrStd (d + 1)).or y)
    (ez : Basis (Fin (d + 1)) ℝ (𝔼 (d + 1))) (hez : ez.orientation = (sphOrStd (d + 1)).or z)
    (R : 𝔼 (d + d + 2) ≃ₗᵢ[ℝ] 𝔼 (d + d + 2)) :
    letI := (isSliceSubmanifold_preim hg hy).chartedSpace
    haveI := (isSliceSubmanifold_preim hg hy).isManifold
    letI := (isSliceSubmanifold_preim hf hz).chartedSpace
    haveI := (isSliceSubmanifold_preim hf hz).isManifold
    ∀ (p : g ⁻¹' {y} × f ⁻¹' {z}) (q : domR R), q.1 = (p.1.1, p.2.1) →
      signAt (orDomR R) orTarget (phiR g f R ∘ Subtype.val) q =
        signAt (((preimOr hg hy ey hey).prod hZ hZ (preimOr hf hz ez hez)).cast rfl)
          (sphOrStd (d + d))
          (linkMap (fun x : g ⁻¹' {y} => stN (R x.1.1)) (fun x : f ⁻¹' {z} => stN (R x.1.1)))
          p := by
  let _ := (isSliceSubmanifold_preim hg hy).chartedSpace
  have _ := (isSliceSubmanifold_preim hg hy).isManifold
  let _ := (isSliceSubmanifold_preim hf hz).chartedSpace
  have _ := (isSliceSubmanifold_preim hf hz).isManifold
  intro p q hqp
  rcases q with ⟨q, hq⟩
  change q = _ at hqp
  subst hqp
  have hgx : g p.1.1 = y := p.1.2
  have hfx : f p.2.1 = z := p.2.2
  have hlam : MDifferentiableAt ((𝓘(ℝ, 𝔼 (d + (d + 1)))).prod 𝓘(ℝ, 𝔼 (d + (d + 1))))
      𝓘(ℝ, 𝔼 (d + d)) (lamR R) (p.1.1, p.2.1) :=
    (contMDiffAt_lamR hq).mdifferentiableAt (by simp)
  have hgd : MDifferentiableAt 𝓘(ℝ, 𝔼 (d + (d + 1))) 𝓘(ℝ, 𝔼 (d + 1)) g p.1.1 :=
    hg.mdifferentiableAt (by simp)
  have hfd : MDifferentiableAt 𝓘(ℝ, 𝔼 (d + (d + 1))) 𝓘(ℝ, 𝔼 (d + 1)) f p.2.1 :=
    hf.mdifferentiableAt (by simp)
  -- the derivative of `Φ` is `((dg, df), dλ)`
  have hΦ : HasMFDerivAt ((𝓘(ℝ, 𝔼 (d + (d + 1)))).prod 𝓘(ℝ, 𝔼 (d + (d + 1))))
      ((𝓘(ℝ, 𝔼 (d + 1)).prod 𝓘(ℝ, 𝔼 (d + 1))).prod 𝓘(ℝ, 𝔼 (d + d)))
      (phiR g f R) (p.1.1, p.2.1)
      ((((mfd 𝓘(ℝ, 𝔼 (d + (d + 1))) 𝓘(ℝ, 𝔼 (d + 1)) g p.1.1).prodMap
        (mfd 𝓘(ℝ, 𝔼 (d + (d + 1))) 𝓘(ℝ, 𝔼 (d + 1)) f p.2.1)).prod
        (mfd ((𝓘(ℝ, 𝔼 (d + (d + 1)))).prod 𝓘(ℝ, 𝔼 (d + (d + 1)))) 𝓘(ℝ, 𝔼 (d + d))
          (lamR R) (p.1.1, p.2.1)) :)) :=
    ((hasMFDerivAt_mfd hgd).prodMap (hasMFDerivAt_mfd hfd)).prodMk (hasMFDerivAt_mfd hlam)
  -- the derivative of the linking map is `dλ ∘ (dι × dι')`
  have hι₁ : MDifferentiableAt 𝓘(ℝ, 𝔼 d) 𝓘(ℝ, 𝔼 (d + (d + 1)))
      (Subtype.val : g ⁻¹' {y} → Sph (d + (d + 1))) p.1 :=
    (isSliceSubmanifold_preim hg hy).contMDiff_val.mdifferentiableAt (by simp)
  have hι₂ : MDifferentiableAt 𝓘(ℝ, 𝔼 d) 𝓘(ℝ, 𝔼 (d + (d + 1)))
      (Subtype.val : f ⁻¹' {z} → Sph (d + (d + 1))) p.2 :=
    (isSliceSubmanifold_preim hf hz).contMDiff_val.mdifferentiableAt (by simp)
  have hlink : HasMFDerivAt ((𝓘(ℝ, 𝔼 d)).prod 𝓘(ℝ, 𝔼 d)) 𝓘(ℝ, 𝔼 (d + d))
      (linkMap (fun x : g ⁻¹' {y} => stN (R x.1.1)) (fun x : f ⁻¹' {z} => stN (R x.1.1))) p
      (((mfd ((𝓘(ℝ, 𝔼 (d + (d + 1)))).prod 𝓘(ℝ, 𝔼 (d + (d + 1)))) 𝓘(ℝ, 𝔼 (d + d))
          (lamR R) (p.1.1, p.2.1)).comp
        ((mfd 𝓘(ℝ, 𝔼 d) 𝓘(ℝ, 𝔼 (d + (d + 1)))
            (Subtype.val : g ⁻¹' {y} → Sph (d + (d + 1))) p.1).prodMap
          (mfd 𝓘(ℝ, 𝔼 d) 𝓘(ℝ, 𝔼 (d + (d + 1)))
            (Subtype.val : f ⁻¹' {z} → Sph (d + (d + 1))) p.2)) :)) :=
    HasMFDerivAt.comp (g := lamR R)
      (f := Prod.map (Subtype.val : g ⁻¹' {y} → Sph (d + (d + 1)))
        (Subtype.val : f ⁻¹' {z} → Sph (d + (d + 1)))) p
      (hasMFDerivAt_mfd hlam) ((hasMFDerivAt_mfd hι₁).prodMap (hasMFDerivAt_mfd hι₂))
  unfold signAt
  rw [mfd_comp_subtype_val (domR R) (y := ⟨(p.1.1, p.2.1), hq⟩) hΦ.mdifferentiableAt,
    HasMFDerivAt.mfd_eq hΦ, HasMFDerivAt.mfd_eq hlink, Orient.cast_or, Orient.prod_or]
  -- lifts of the positive bases, and the chart description of the preimage orientations
  obtain ⟨u, hu⟩ : ∃ u : Fin (d + 1) → 𝔼 (d + (d + 1)),
      ∀ i, mfd 𝓘(ℝ, 𝔼 (d + (d + 1))) 𝓘(ℝ, 𝔼 (d + 1)) g p.1.1 (u i) = ey i :=
    ⟨fun i => surjInv (surjective_mfd_preim hy p.1) (ey i), fun i => surjInv_eq _ _⟩
  obtain ⟨u', hu'⟩ : ∃ u : Fin (d + 1) → 𝔼 (d + (d + 1)),
      ∀ i, mfd 𝓘(ℝ, 𝔼 (d + (d + 1))) 𝓘(ℝ, 𝔼 (d + 1)) f p.2.1 (u i) = ez i :=
    ⟨fun i => surjInv (surjective_mfd_preim hz p.2) (ez i), fun i => surjInv_eq _ _⟩
  rw [preimOr_or_eq hg hy ey hey p.1 u hu, preimOr_or_eq hf hz ez hez p.2 u' hu']
  have hli : LinearIndependent ℝ
      (fun i => mfd 𝓘(ℝ, 𝔼 (d + (d + 1))) 𝓘(ℝ, 𝔼 (d + 1)) g p.1.1 (u i)) := by
    simpa only [hu] using ey.linearIndependent
  have hli' : LinearIndependent ℝ
      (fun i => mfd 𝓘(ℝ, 𝔼 (d + (d + 1))) 𝓘(ℝ, 𝔼 (d + 1)) f p.2.1 (u' i)) := by
    simpa only [hu'] using ez.linearIndependent
  have huo := (LinkAlg.orientation_basisOfLinearIndependent' ey hu hli (by simp)).trans
    (hey.trans (congrArg (sphOrStd (d + 1)).or hgx.symm))
  have huo' := (LinkAlg.orientation_basisOfLinearIndependent' ez hu' hli' (by simp)).trans
    (hez.trans (congrArg (sphOrStd (d + 1)).or hfx.symm))
  -- the block computation, with the sign `(-1)^(d (d+1)) = 1`
  have key := orSign_pair_preimage₂ (d := d) (p := d + 1) (k := d + d) rfl (by omega)
    hZ hZ hZ hZ hZ
    ((sphOrStd (d + (d + 1))).or p.1.1) ((sphOrStd (d + (d + 1))).or p.2.1)
    ((sphOrStd (d + 1)).or (g p.1.1)) ((sphOrStd (d + 1)).or (f p.2.1))
    ((sphOrStd (d + d)).or (lamR R (p.1.1, p.2.1)))
    (mfd 𝓘(ℝ, 𝔼 d) 𝓘(ℝ, 𝔼 (d + (d + 1)))
      (Subtype.val : g ⁻¹' {y} → Sph (d + (d + 1))) p.1)
    (mfd 𝓘(ℝ, 𝔼 (d + (d + 1))) 𝓘(ℝ, 𝔼 (d + 1)) g p.1.1)
    (injective_mfderiv_val (isSliceSubmanifold_preim hg hy) p.1)
    (range_mfd_val_eq_ker hg hy p.1) u hli huo
    (mfd 𝓘(ℝ, 𝔼 d) 𝓘(ℝ, 𝔼 (d + (d + 1)))
      (Subtype.val : f ⁻¹' {z} → Sph (d + (d + 1))) p.2)
    (mfd 𝓘(ℝ, 𝔼 (d + (d + 1))) 𝓘(ℝ, 𝔼 (d + 1)) f p.2.1)
    (injective_mfderiv_val (isSliceSubmanifold_preim hf hz) p.2)
    (range_mfd_val_eq_ker hf hz p.2) u' hli' huo'
    (mfd ((𝓘(ℝ, 𝔼 (d + (d + 1)))).prod 𝓘(ℝ, 𝔼 (d + (d + 1)))) 𝓘(ℝ, 𝔼 (d + d))
      (lamR R) (p.1.1, p.2.1))
  rw [(Nat.even_mul_succ_self d).neg_one_pow, one_mul] at key
  exact key

include hg hf hy hz in
/-- Smoothness of the linking map of the preimages (after projecting from `R⁻¹(north)`). -/
theorem contMDiff_linkMap_preim (hdisj : ∀ x x', g x = y → f x' = z → x ≠ x')
    (R : 𝔼 (d + d + 2) ≃ₗᵢ[ℝ] 𝔼 (d + d + 2))
    (hRy : ∀ x, g x = y → R x.1 ≠ (north : Sph (d + d + 1)).1)
    (hRz : ∀ x, f x = z → R x.1 ≠ (north : Sph (d + d + 1)).1) :
    letI := (isSliceSubmanifold_preim hg hy).chartedSpace
    letI := (isSliceSubmanifold_preim hf hz).chartedSpace
    ContMDiff (𝓘(ℝ, 𝔼 d).prod 𝓘(ℝ, 𝔼 d)) 𝓘(ℝ, 𝔼 (d + d)) ∞
      (linkMap (fun x : g ⁻¹' {y} => stN (R x.1.1)) (fun x : f ⁻¹' {z} => stN (R x.1.1))) := by
  let _ := (isSliceSubmanifold_preim hg hy).chartedSpace
  have _ := (isSliceSubmanifold_preim hg hy).isManifold
  let _ := (isSliceSubmanifold_preim hf hz).chartedSpace
  have _ := (isSliceSubmanifold_preim hf hz).isManifold
  have hRα : ∀ x : g ⁻¹' {y}, R (x : Sph (d + (d + 1))).1 ≠ (north : Sph (d + d + 1)).1 :=
    fun x => hRy x.1 x.2
  have hRβ : ∀ x : f ⁻¹' {z}, R (x : Sph (d + (d + 1))).1 ≠ (north : Sph (d + d + 1)).1 :=
    fun x => hRz x.1 x.2
  have hα := contMDiff_stN_comp (k := d + d) (α := Subtype.val)
    (isSliceSubmanifold_preim hg hy).contMDiff_val R hRα
  have hβ := contMDiff_stN_comp (k := d + d) (α := Subtype.val)
    (isSliceSubmanifold_preim hf hz).contMDiff_val R hRβ
  have hdisj' := stN_comp_disjoint (k := d + d) (α := (Subtype.val : g ⁻¹' {y} → _))
    (β := (Subtype.val : f ⁻¹' {z} → _)) (fun a b => hdisj a.1 b.1 a.2 b.2) R hRα hRβ
  exact contMDiff_linkMap hα hβ hdisj'

end preim

end LinkDeg

/-! ### Linking numbers of preimages are local degrees -/

/-- **`((y, z), e)` is a regular value of the restricted `Φ`** when `e` is a regular value of the
linking map of `g⁻¹(y)` and `f⁻¹(z)` (after projecting from `R⁻¹(north)`). -/
theorem isRegularValue_phiR (_hd : 1 ≤ d) {f g : Sph (d + (d + 1)) → Sph (d + 1)}
    (hf : ContMDiff 𝓘(ℝ, 𝔼 (d + (d + 1))) 𝓘(ℝ, 𝔼 (d + 1)) ∞ f)
    (hg : ContMDiff 𝓘(ℝ, 𝔼 (d + (d + 1))) 𝓘(ℝ, 𝔼 (d + 1)) ∞ g) {y z : Sph (d + 1)}
    (hy : IsRegularValue 𝓘(ℝ, 𝔼 (d + (d + 1))) 𝓘(ℝ, 𝔼 (d + 1)) g y)
    (hz : IsRegularValue 𝓘(ℝ, 𝔼 (d + (d + 1))) 𝓘(ℝ, 𝔼 (d + 1)) f z)
    (ey : Basis (Fin (d + 1)) ℝ (𝔼 (d + 1))) (hey : ey.orientation = (sphOrStd (d + 1)).or y)
    (ez : Basis (Fin (d + 1)) ℝ (𝔼 (d + 1))) (hez : ez.orientation = (sphOrStd (d + 1)).or z)
    (_hdisj : ∀ x x', g x = y → f x' = z → x ≠ x')
    {R : 𝔼 (d + d + 2) ≃ₗᵢ[ℝ] 𝔼 (d + d + 2)} (_hR : IsRotation R)
    (_hRy : ∀ x, g x = y → R x.1 ≠ (north : Sph (d + d + 1)).1)
    (_hRz : ∀ x, f x = z → R x.1 ≠ (north : Sph (d + d + 1)).1)
    {e : Sph (d + d)}
    (he : letI := (isSliceSubmanifold_preim hg hy).chartedSpace
      letI := (isSliceSubmanifold_preim hf hz).chartedSpace
      IsRegularValue (𝓘(ℝ, 𝔼 d).prod 𝓘(ℝ, 𝔼 d)) 𝓘(ℝ, 𝔼 (d + d))
        (linkMap (fun x : g ⁻¹' {y} => stN (R x.1.1)) (fun x : f ⁻¹' {z} => stN (R x.1.1)))
        e) :
    IsRegularValue ((𝓘(ℝ, 𝔼 (d + (d + 1)))).prod 𝓘(ℝ, 𝔼 (d + (d + 1))))
      ((𝓘(ℝ, 𝔼 (d + 1)).prod 𝓘(ℝ, 𝔼 (d + 1))).prod 𝓘(ℝ, 𝔼 (d + d)))
      (phiR g f R ∘ (Subtype.val : domR R → Sph (d + (d + 1)) × Sph (d + (d + 1))))
      ((y, z), e) := by
  let _ := (isSliceSubmanifold_preim hg hy).chartedSpace
  have _ := (isSliceSubmanifold_preim hg hy).isManifold
  let _ := (isSliceSubmanifold_preim hf hz).chartedSpace
  have _ := (isSliceSubmanifold_preim hf hz).isManifold
  intro q hq
  have h1 : g q.1.1 = y := congrArg (fun w => w.1.1) hq
  have h2 : f q.1.2 = z := congrArg (fun w => w.1.2) hq
  have h3 : linkMap (fun x : g ⁻¹' {y} => stN (R x.1.1)) (fun x : f ⁻¹' {z} => stN (R x.1.1))
      (⟨q.1.1, h1⟩, ⟨q.1.2, h2⟩) = e := congrArg Prod.snd hq
  have hsign := signAt_phiR_eq hg hf hy hz ey hey ez hez R (⟨q.1.1, h1⟩, ⟨q.1.2, h2⟩) q rfl
  have hne := IsRegularPoint.signAt_ne_zero (finrank_prod_eq hZ hZ) hZ
    (((preimOr hg hy ey hey).prod hZ hZ (preimOr hf hz ez hez)).cast rfl) (sphOrStd (d + d))
    (he _ h3)
  rw [← hsign] at hne
  exact ((signAt_ne_zero_iff ((finrank_prod_eq hZ hZ).trans (by omega))
    (finrank_prod_eq (finrank_prod_eq hZ hZ) hZ) _ _ _ _).1 hne).2

/-- **(1) Linking numbers of preimages are local degrees**: the local degree of
`Φ = phiR g f R ∘ Subtype.val` on `D_R` at `((y, z), e)` is the linking number of `g⁻¹(y)` and
`f⁻¹(z)` (for the preimage orientations), for any regular value `e` of their linking map. -/
theorem degAt_phiR_eq_linkingNumberRot (hd : 1 ≤ d) {f g : Sph (d + (d + 1)) → Sph (d + 1)}
    (hf : ContMDiff 𝓘(ℝ, 𝔼 (d + (d + 1))) 𝓘(ℝ, 𝔼 (d + 1)) ∞ f)
    (hg : ContMDiff 𝓘(ℝ, 𝔼 (d + (d + 1))) 𝓘(ℝ, 𝔼 (d + 1)) ∞ g) {y z : Sph (d + 1)}
    (hy : IsRegularValue 𝓘(ℝ, 𝔼 (d + (d + 1))) 𝓘(ℝ, 𝔼 (d + 1)) g y)
    (hz : IsRegularValue 𝓘(ℝ, 𝔼 (d + (d + 1))) 𝓘(ℝ, 𝔼 (d + 1)) f z)
    (ey : Basis (Fin (d + 1)) ℝ (𝔼 (d + 1))) (hey : ey.orientation = (sphOrStd (d + 1)).or y)
    (ez : Basis (Fin (d + 1)) ℝ (𝔼 (d + 1))) (hez : ez.orientation = (sphOrStd (d + 1)).or z)
    (hdisj : ∀ x x', g x = y → f x' = z → x ≠ x')
    {R : 𝔼 (d + d + 2) ≃ₗᵢ[ℝ] 𝔼 (d + d + 2)} (_hR : IsRotation R)
    (hRy : ∀ x, g x = y → R x.1 ≠ (north : Sph (d + d + 1)).1)
    (hRz : ∀ x, f x = z → R x.1 ≠ (north : Sph (d + d + 1)).1)
    {e : Sph (d + d)}
    (he : letI := (isSliceSubmanifold_preim hg hy).chartedSpace
      letI := (isSliceSubmanifold_preim hf hz).chartedSpace
      IsRegularValue (𝓘(ℝ, 𝔼 d).prod 𝓘(ℝ, 𝔼 d)) 𝓘(ℝ, 𝔼 (d + d))
        (linkMap (fun x : g ⁻¹' {y} => stN (R x.1.1)) (fun x : f ⁻¹' {z} => stN (R x.1.1)))
        e) :
    letI := (isSliceSubmanifold_preim hg hy).chartedSpace
    haveI := (isSliceSubmanifold_preim hg hy).isManifold
    letI := (isSliceSubmanifold_preim hf hz).chartedSpace
    haveI := (isSliceSubmanifold_preim hf hz).isManifold
    degAt (orDomR R) orTarget (phiR g f R ∘ Subtype.val) ((y, z), e) =
      linkingNumberRot rfl (preimOr hg hy ey hey) (preimOr hf hz ez hez) Subtype.val Subtype.val
        R := by
  let _ := (isSliceSubmanifold_preim hg hy).chartedSpace
  have _ := (isSliceSubmanifold_preim hg hy).isManifold
  let _ := (isSliceSubmanifold_preim hf hz).chartedSpace
  have _ := (isSliceSubmanifold_preim hf hz).isManifold
  have : CompactSpace (g ⁻¹' {y}) :=
    isCompact_iff_compactSpace.1 (isClosed_singleton.preimage hg.continuous).isCompact
  have : CompactSpace (f ⁻¹' {z}) :=
    isCompact_iff_compactSpace.1 (isClosed_singleton.preimage hf.continuous).isCompact
  have := preconnectedSpace (show 0 < d + d by omega)
  have hlink := contMDiff_linkMap_preim hg hf hy hz hdisj R hRy hRz
  -- the map `g⁻¹(y) × f⁻¹(z) → D_R`, `(x, x') ↦ (x, x')`
  obtain ⟨φ, hφ⟩ : ∃ φ : g ⁻¹' {y} × f ⁻¹' {z} → domR R, ∀ p, (φ p).1 = (p.1.1, p.2.1) :=
    ⟨fun p => ⟨(p.1.1, p.2.1), mem_domR.2 ⟨hRy p.1.1 p.1.2, hRz p.2.1 p.2.2,
      hdisj p.1.1 p.2.1 p.1.2 p.2.2⟩⟩, fun p => rfl⟩
  rw [linkingNumberRot, linkingNumber, deg_eq (finrank_prod_eq hZ hZ) hZ _ _ hlink he]
  unfold degAt
  symm
  -- it is a bijection between the preimages, with equal signs at corresponding points
  refine finsum_mem_eq_of_bijOn φ ⟨fun p hp => ?_, fun p _ p' _ h => ?_, fun q hq => ?_⟩
    fun p _ => (signAt_phiR_eq hg hf hy hz ey hey ez hez R p (φ p) (hφ p)).symm
  · have h1 : g p.1.1 = y := p.1.2
    have h2 : f p.2.1 = z := p.2.2
    have h3 : linkMap (fun x : g ⁻¹' {y} => stN (R x.1.1)) (fun x : f ⁻¹' {z} => stN (R x.1.1))
        p = e := hp
    change phiR g f R (φ p).1 = ((y, z), e)
    rw [hφ]
    exact Prod.ext (Prod.ext h1 h2) h3
  · have h' := (hφ p).symm.trans ((congrArg Subtype.val h).trans (hφ p'))
    exact Prod.ext (Subtype.ext (congrArg Prod.fst h')) (Subtype.ext (congrArg Prod.snd h'))
  · have hq' : phiR g f R q.1 = ((y, z), e) := hq
    have h1 : g q.1.1 = y := congrArg (fun w => w.1.1) hq'
    have h2 : f q.1.2 = z := congrArg (fun w => w.1.2) hq'
    refine ⟨(⟨q.1.1, h1⟩, ⟨q.1.2, h2⟩), congrArg Prod.snd hq', ?_⟩
    exact Subtype.ext (hφ _)

/-! ### Homotopy invariance -/

namespace LinkDeg

/-- Closed neighbourhoods `V₁ ∋ y`, `V₂ ∋ z` such that for `t ∈ [0, 1]`, pairs of points of
`G_t⁻¹(V₁)` and `F_t⁻¹(V₂)` lie in `D_R`. -/
theorem exists_isClosed_nhds_domR {G F : Sph (d + (d + 1)) × ℝ → Sph (d + 1)}
    (hGc : Continuous G) (hFc : Continuous F) {y z : Sph (d + 1)}
    (hdisj : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x x', G (x, t) = y → F (x', t) = z → x ≠ x')
    {R : 𝔼 (d + d + 2) ≃ₗᵢ[ℝ] 𝔼 (d + d + 2)}
    (hRN : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x, (G (x, t) = y ∨ F (x, t) = z) →
      R x.1 ≠ (north : Sph (d + d + 1)).1) :
    ∃ V₁ ∈ 𝓝 y, ∃ V₂ ∈ 𝓝 z, IsClosed V₁ ∧ IsClosed V₂ ∧
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ x x', G (x, t) ∈ V₁ → F (x', t) ∈ V₂ →
        (x, x') ∈ domR R := by
  have hK : IsCompact ((univ : Set (Sph (d + (d + 1)))) ×ˢ Icc (0 : ℝ) 1) :=
    isCompact_univ.prod isCompact_Icc
  -- the compact set of points over `R⁻¹(north)`
  obtain ⟨N, hN⟩ : ∃ N : Set (Sph (d + (d + 1)) × ℝ),
      N = {x : Sph (d + (d + 1)) | R x.1 = (north : Sph (d + d + 1)).1} ×ˢ Icc (0 : ℝ) 1 :=
    ⟨_, rfl⟩
  have hNc : IsCompact N := by
    rw [hN]
    refine hK.of_isClosed_subset ((isClosed_eq (R.continuous.comp continuous_subtype_val)
      continuous_const).prod isClosed_Icc) ?_
    exact prod_mono (subset_univ _) subset_rfl
  have hA : IsClosed (G '' N) := (hNc.image hGc).isClosed
  have hB : IsClosed (F '' N) := (hNc.image hFc).isClosed
  have hyA : y ∉ G '' N := by
    rintro ⟨w, hw, hwy⟩
    rw [hN] at hw
    exact hRN w.2 hw.2 w.1 (Or.inl hwy) hw.1
  have hzB : z ∉ F '' N := by
    rintro ⟨w, hw, hwz⟩
    rw [hN] at hw
    exact hRN w.2 hw.2 w.1 (Or.inr hwz) hw.1
  -- the compact set of values of `(G, F)` on the diagonal
  have hP : IsClosed ((fun w => (G w, F w)) '' ((univ : Set (Sph (d + (d + 1)))) ×ˢ
      Icc (0 : ℝ) 1)) := (hK.image (hGc.prodMk hFc)).isClosed
  have hyzP : (y, z) ∉ (fun w => (G w, F w)) '' ((univ : Set (Sph (d + (d + 1)))) ×ˢ
      Icc (0 : ℝ) 1) := by
    rintro ⟨w, hw, hwyz⟩
    exact hdisj w.2 hw.2 w.1 w.1 (congrArg Prod.fst hwyz) (congrArg Prod.snd hwyz) rfl
  obtain ⟨u, hu, v, hv, huv⟩ := mem_nhds_prod_iff.1 (hP.isOpen_compl.mem_nhds hyzP)
  obtain ⟨V₁, hV₁, hV₁c, hV₁s⟩ :=
    exists_mem_nhds_isClosed_subset (inter_mem hu (hA.isOpen_compl.mem_nhds hyA))
  obtain ⟨V₂, hV₂, hV₂c, hV₂s⟩ :=
    exists_mem_nhds_isClosed_subset (inter_mem hv (hB.isOpen_compl.mem_nhds hzB))
  refine ⟨V₁, hV₁, V₂, hV₂, hV₁c, hV₂c, fun t ht x x' hx hx' =>
    mem_domR.2 ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩⟩
  · refine (hV₁s hx).2 ⟨(x, t), ?_, rfl⟩
    rw [hN]
    exact mk_mem_prod h ht
  · refine (hV₂s hx').2 ⟨(x', t), ?_, rfl⟩
    rw [hN]
    exact mk_mem_prod h ht
  · change x = x' at h
    subst h
    exact huv (mk_mem_prod (hV₁s hx).1 (hV₂s hx').1)
      ⟨(x, t), mk_mem_prod (mem_univ _) ht, rfl⟩

end LinkDeg

/-- **(2) Homotopy invariance.** `G, F : S × ℝ → S^{d+1}` smooth; for `t ∈ [0,1]` the preimages
`G_t⁻¹(y)`, `F_t⁻¹(z)` are disjoint and avoid `R⁻¹(north)`; `y` is regular for `G_0, G_1` and
`z` for `F_0, F_1`.  Then the linking numbers at `t = 0` and `t = 1` agree. -/
theorem linkingNumberRot_eq_of_homotopy (hd : 1 ≤ d)
    {G F : Sph (d + (d + 1)) × ℝ → Sph (d + 1)}
    (hG : ContMDiff (𝓘(ℝ, 𝔼 (d + (d + 1))).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, 𝔼 (d + 1)) ∞ G)
    (hF : ContMDiff (𝓘(ℝ, 𝔼 (d + (d + 1))).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, 𝔼 (d + 1)) ∞ F)
    (hG0 : ContMDiff 𝓘(ℝ, 𝔼 (d + (d + 1))) 𝓘(ℝ, 𝔼 (d + 1)) ∞ (fun x => G (x, 0)))
    (hG1 : ContMDiff 𝓘(ℝ, 𝔼 (d + (d + 1))) 𝓘(ℝ, 𝔼 (d + 1)) ∞ (fun x => G (x, 1)))
    (hF0 : ContMDiff 𝓘(ℝ, 𝔼 (d + (d + 1))) 𝓘(ℝ, 𝔼 (d + 1)) ∞ (fun x => F (x, 0)))
    (hF1 : ContMDiff 𝓘(ℝ, 𝔼 (d + (d + 1))) 𝓘(ℝ, 𝔼 (d + 1)) ∞ (fun x => F (x, 1)))
    {y z : Sph (d + 1)}
    (hy0 : IsRegularValue 𝓘(ℝ, 𝔼 (d + (d + 1))) 𝓘(ℝ, 𝔼 (d + 1)) (fun x => G (x, 0)) y)
    (hy1 : IsRegularValue 𝓘(ℝ, 𝔼 (d + (d + 1))) 𝓘(ℝ, 𝔼 (d + 1)) (fun x => G (x, 1)) y)
    (hz0 : IsRegularValue 𝓘(ℝ, 𝔼 (d + (d + 1))) 𝓘(ℝ, 𝔼 (d + 1)) (fun x => F (x, 0)) z)
    (hz1 : IsRegularValue 𝓘(ℝ, 𝔼 (d + (d + 1))) 𝓘(ℝ, 𝔼 (d + 1)) (fun x => F (x, 1)) z)
    (ey : Basis (Fin (d + 1)) ℝ (𝔼 (d + 1))) (hey : ey.orientation = (sphOrStd (d + 1)).or y)
    (ez : Basis (Fin (d + 1)) ℝ (𝔼 (d + 1))) (hez : ez.orientation = (sphOrStd (d + 1)).or z)
    (hdisj : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ x x', G (x, t) = y → F (x', t) = z → x ≠ x')
    {R : 𝔼 (d + d + 2) ≃ₗᵢ[ℝ] 𝔼 (d + d + 2)} (hR : IsRotation R)
    (hRN : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ x, (G (x, t) = y ∨ F (x, t) = z) →
      R x.1 ≠ (north : Sph (d + d + 1)).1) :
    letI := (isSliceSubmanifold_preim hG0 hy0).chartedSpace
    haveI := (isSliceSubmanifold_preim hG0 hy0).isManifold
    letI := (isSliceSubmanifold_preim hF0 hz0).chartedSpace
    haveI := (isSliceSubmanifold_preim hF0 hz0).isManifold
    letI := (isSliceSubmanifold_preim hG1 hy1).chartedSpace
    haveI := (isSliceSubmanifold_preim hG1 hy1).isManifold
    letI := (isSliceSubmanifold_preim hF1 hz1).chartedSpace
    haveI := (isSliceSubmanifold_preim hF1 hz1).isManifold
    linkingNumberRot rfl (preimOr hG0 hy0 ey hey) (preimOr hF0 hz0 ez hez) Subtype.val
        Subtype.val R =
      linkingNumberRot rfl (preimOr hG1 hy1 ey hey) (preimOr hF1 hz1 ez hez) Subtype.val
        Subtype.val R := by
  let _ := (isSliceSubmanifold_preim hG0 hy0).chartedSpace
  have _ := (isSliceSubmanifold_preim hG0 hy0).isManifold
  let _ := (isSliceSubmanifold_preim hF0 hz0).chartedSpace
  have _ := (isSliceSubmanifold_preim hF0 hz0).isManifold
  let _ := (isSliceSubmanifold_preim hG1 hy1).chartedSpace
  have _ := (isSliceSubmanifold_preim hG1 hy1).isManifold
  let _ := (isSliceSubmanifold_preim hF1 hz1).chartedSpace
  have _ := (isSliceSubmanifold_preim hF1 hz1).isManifold
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have h1 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  -- the hypotheses of (1) at both ends
  have hdisj0 : ∀ x x', G (x, 0) = y → F (x', 0) = z → x ≠ x' := hdisj 0 h0
  have hdisj1 : ∀ x x', G (x, 1) = y → F (x', 1) = z → x ≠ x' := hdisj 1 h1
  have hRy0 : ∀ x, G (x, 0) = y → R x.1 ≠ (north : Sph (d + d + 1)).1 :=
    fun x hx => hRN 0 h0 x (Or.inl hx)
  have hRz0 : ∀ x, F (x, 0) = z → R x.1 ≠ (north : Sph (d + d + 1)).1 :=
    fun x hx => hRN 0 h0 x (Or.inr hx)
  have hRy1 : ∀ x, G (x, 1) = y → R x.1 ≠ (north : Sph (d + d + 1)).1 :=
    fun x hx => hRN 1 h1 x (Or.inl hx)
  have hRz1 : ∀ x, F (x, 1) = z → R x.1 ≠ (north : Sph (d + d + 1)).1 :=
    fun x hx => hRN 1 h1 x (Or.inr hx)
  -- a common regular value `e` of the linking maps at both ends
  have : CompactSpace ((fun x => G (x, 0)) ⁻¹' {y}) :=
    isCompact_iff_compactSpace.1 (isClosed_singleton.preimage hG0.continuous).isCompact
  have : CompactSpace ((fun x => F (x, 0)) ⁻¹' {z}) :=
    isCompact_iff_compactSpace.1 (isClosed_singleton.preimage hF0.continuous).isCompact
  have : CompactSpace ((fun x => G (x, 1)) ⁻¹' {y}) :=
    isCompact_iff_compactSpace.1 (isClosed_singleton.preimage hG1.continuous).isCompact
  have : CompactSpace ((fun x => F (x, 1)) ⁻¹' {z}) :=
    isCompact_iff_compactSpace.1 (isClosed_singleton.preimage hF1.continuous).isCompact
  have hr0 := dense_isOpen_regularValues (finrank_prod_eq hZ hZ) hZ
    (((preimOr hG0 hy0 ey hey).prod hZ hZ (preimOr hF0 hz0 ez hez)).cast rfl)
    (sphOrStd (d + d)) (contMDiff_linkMap_preim hG0 hF0 hy0 hz0 hdisj0 R hRy0 hRz0)
  have hr1 := dense_isOpen_regularValues (finrank_prod_eq hZ hZ) hZ
    (((preimOr hG1 hy1 ey hey).prod hZ hZ (preimOr hF1 hz1 ez hez)).cast rfl)
    (sphOrStd (d + d)) (contMDiff_linkMap_preim hG1 hF1 hy1 hz1 hdisj1 R hRy1 hRz1)
  obtain ⟨e, he0, he1⟩ := (hr0.1.inter_of_isOpen_left hr1.1 hr0.2).nonempty
  have hreg0 := isRegularValue_phiR hd hF0 hG0 hy0 hz0 ey hey ez hez hdisj0 hR hRy0 hRz0 he0
  have hreg1 := isRegularValue_phiR hd hF1 hG1 hy1 hz1 ey hey ez hez hdisj1 hR hRy1 hRz1 he1
  -- the homotopy `Ψ_t = Φ(G_t, F_t)` on `D_R`
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : domR R × ℝ → (Sph (d + 1) × Sph (d + 1)) × Sph (d + d),
      ∀ w, Ψ w = ((G (w.1.1.1, w.2), F (w.1.1.2, w.2)), lamR R w.1.1) := ⟨_, fun _ => rfl⟩
  have hΨs : ContMDiff
      (((𝓘(ℝ, 𝔼 (d + (d + 1)))).prod 𝓘(ℝ, 𝔼 (d + (d + 1)))).prod 𝓘(ℝ, ℝ))
      ((𝓘(ℝ, 𝔼 (d + 1)).prod 𝓘(ℝ, 𝔼 (d + 1))).prod 𝓘(ℝ, 𝔼 (d + d))) ∞ Ψ := by
    have heq : Ψ = fun w => ((G (w.1.1.1, w.2), F (w.1.1.2, w.2)), lamR R w.1.1) :=
      funext hΨ
    rw [heq]
    have hval : ContMDiff
        (((𝓘(ℝ, 𝔼 (d + (d + 1)))).prod 𝓘(ℝ, 𝔼 (d + (d + 1)))).prod 𝓘(ℝ, ℝ))
        ((𝓘(ℝ, 𝔼 (d + (d + 1)))).prod 𝓘(ℝ, 𝔼 (d + (d + 1)))) ∞
        (fun w : domR R × ℝ => w.1.1) :=
      contMDiff_subtype_val.comp contMDiff_fst
    have hlamU : ContMDiff ((𝓘(ℝ, 𝔼 (d + (d + 1)))).prod 𝓘(ℝ, 𝔼 (d + (d + 1))))
        𝓘(ℝ, 𝔼 (d + d)) ∞ (fun q : domR R => lamR R q.1) :=
      fun q => (contMDiffAt_lamR q.2).comp q contMDiff_subtype_val.contMDiffAt
    exact ((hG.comp ((contMDiff_fst.comp hval).prodMk contMDiff_snd)).prodMk
      (hF.comp ((contMDiff_snd.comp hval).prodMk contMDiff_snd))).prodMk
      (hlamU.comp contMDiff_fst)
  have hΨ0 : (fun x => Ψ (x, 0)) =
      phiR (fun x => G (x, 0)) (fun x => F (x, 0)) R ∘ Subtype.val :=
    funext fun x => hΨ (x, 0)
  have hΨ1 : (fun x => Ψ (x, 1)) =
      phiR (fun x => G (x, 1)) (fun x => F (x, 1)) R ∘ Subtype.val :=
    funext fun x => hΨ (x, 1)
  -- compactness of the part of `Ψ⁻¹(V₁ × V₂ × S^{2d})` over `[0, 1]`
  obtain ⟨V₁, hV₁, V₂, hV₂, hV₁c, hV₂c, hV⟩ :=
    exists_isClosed_nhds_domR hG.continuous hF.continuous hdisj hRN
  have hK : IsCompact {w : domR R × ℝ |
      Ψ w ∈ (V₁ ×ˢ V₂) ×ˢ (univ : Set (Sph (d + d))) ∧ w.2 ∈ Icc (0 : ℝ) 1} := by
    have hemb : IsEmbedding (fun w : domR R × ℝ => (w.1.1, w.2)) :=
      IsEmbedding.subtypeVal.prodMap IsEmbedding.id
    rw [hemb.isCompact_iff]
    have himg : (fun w : domR R × ℝ => (w.1.1, w.2)) '' {w : domR R × ℝ |
        Ψ w ∈ (V₁ ×ˢ V₂) ×ˢ (univ : Set (Sph (d + d))) ∧ w.2 ∈ Icc (0 : ℝ) 1} =
        {v : (Sph (d + (d + 1)) × Sph (d + (d + 1))) × ℝ |
          (G (v.1.1, v.2) ∈ V₁ ∧ F (v.1.2, v.2) ∈ V₂) ∧ v.2 ∈ Icc (0 : ℝ) 1} := by
      ext v
      constructor
      · rintro ⟨w, ⟨hw1, hw2⟩, rfl⟩
        rw [hΨ] at hw1
        exact ⟨hw1.1, hw2⟩
      · rintro ⟨⟨hv1, hv2⟩, hv3⟩
        refine ⟨(⟨v.1, hV v.2 hv3 v.1.1 v.1.2 hv1 hv2⟩, v.2), ⟨?_, hv3⟩, rfl⟩
        rw [hΨ]
        exact mk_mem_prod (mk_mem_prod hv1 hv2) (mem_univ _)
    rw [himg]
    refine (isCompact_univ.prod isCompact_Icc).of_isClosed_subset ?_
      fun v hv => mk_mem_prod (mem_univ _) hv.2
    refine IsClosed.and (IsClosed.and ?_ ?_) (isClosed_Icc.preimage continuous_snd)
    · exact hV₁c.preimage (hG.continuous.comp
        ((continuous_fst.comp continuous_fst).prodMk continuous_snd))
    · exact hV₂c.preimage (hF.continuous.comp
        ((continuous_snd.comp continuous_fst).prodMk continuous_snd))
  -- homotopy invariance of the local degree, and (1) at both ends
  have hdeg := degAt_eq_of_homotopy_of_isCompact ((finrank_prod_eq hZ hZ).trans (by omega))
    (finrank_prod_eq (finrank_prod_eq hZ hZ) hZ) (orDomR R) orTarget hΨs (y := ((y, z), e))
    (by rw [hΨ0]; exact hreg0) (by rw [hΨ1]; exact hreg1)
    (prod_mem_nhds (prod_mem_nhds hV₁ hV₂) univ_mem) hK
  rw [hΨ0, hΨ1,
    degAt_phiR_eq_linkingNumberRot hd hF0 hG0 hy0 hz0 ey hey ez hez hdisj0 hR hRy0 hRz0 he0,
    degAt_phiR_eq_linkingNumberRot hd hF1 hG1 hy1 hz1 ey hey ez hez hdisj1 hR hRy1 hRz1 he1]
    at hdeg
  exact hdeg

end Problems

end Milnor
