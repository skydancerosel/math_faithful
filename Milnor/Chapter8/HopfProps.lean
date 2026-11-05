import Milnor.Chapter8.HopfInvariant
import Milnor.Chapter8.HopfMap
import Milnor.Chapter8.HopfSign
import Milnor.Chapter8.HopfComp

/-!
# Properties of the Hopf invariant (Milnor §8, Problem 15)

Milnor: "If the dimension `p` is odd, prove that `H(f) = 0`.  For a composition
`S^{2p−1} →f S^p →g S^p` prove that `H(g ∘ f)` is equal to `H(f)` multiplied by the square of
the degree of `g`.  The Hopf fibration `π : S³ → S²` is defined by
`π(x₁, x₂, x₃, x₄) = h⁻¹((x₁ + i x₂)/(x₃ + i x₄))` where `h` denotes stereographic projection to
the complex plane.  Prove that `H(π) = 1`."

Here `p = d + 1` with `d ≥ 1`, `S^{2p−1}` is `Sph (d + (d + 1))`, and `H = hopfInvariant`
(`HopfInvariant.lean`).

* `hopfInvariant_eq_zero_of_odd`: `H(f) = 0` for odd `p`.
* `hopfInvariant_comp`: `H(g ∘ f) = (deg g)² · H(f)`.
* `hopfInvariant_hopfMap`: `H(π) = −1` for the Hopf fibration `π = hopfMap` (`HopfMap.lean`, where
  `hopfMap_eq_milnor` identifies it with Milnor's formula).  With the conventions of the book taken
  literally (`sphOrStd` is "outward normal first", preimages carry the orientation of §5, and the
  linking number is the degree of `(x, x') ↦ (x − x')/‖x − x'‖` for the product orientation) the
  value is `−1`, not Milnor's `1`; see `HopfSign.lean`.

## Proofs

1. **Odd `p`.**  For distinct regular values `y ≠ z` of `f` and a rotation `R` sending a point
   outside `f⁻¹{y, z}` to the north pole, both `l(f⁻¹(y), f⁻¹(z))` and `l(f⁻¹(z), f⁻¹(y))` are
   Euclidean linking numbers of the projected preimages (`linkPre_eq_linkingNumberRot`), related by
   the symmetry `l(N, M) = (−1)^{(d+1)(d+1)} l(M, N)` of Problem 13 (`linkingNumber_symm`).  Both
   are `H(f)` (`linkPre_eq_hopfInvariant`), so `H(f) = −H(f)` for odd `d + 1`.
2. **Composition.**  For distinct common regular values `y ≠ z` of `g` and `g ∘ f`
   (`HopfProps.exists_regular_pair_comp`) and a rotation `R` sending a point outside
   `(g ∘ f)⁻¹{y, z}` to the north pole, the composition formula `linkingNumberRot_comp_eq_finsum'`
   (`HopfComp.lean`) writes `l((g∘f)⁻¹(y), (g∘f)⁻¹(z))` as
   `∑ᵢ ∑ⱼ sgn_{yᵢ} g · sgn_{zⱼ} g · l(f⁻¹(yᵢ), f⁻¹(zⱼ))` over `yᵢ ∈ g⁻¹(y)`, `zⱼ ∈ g⁻¹(z)`.  Every
   `l(f⁻¹(yᵢ), f⁻¹(zⱼ))` is `H(f)` (`yᵢ ≠ zⱼ` are regular values of `f`), and the two sums of signs
   are `deg g` (`finsum_signAt_eq_deg`).
3. **Hopf fibration.**  `(1, 0, 0) ≠ (−1, 0, 0)` are regular values of `π`, the identity rotation is
   admissible for their fibres, and the linking number of the fibres is `−1`
   (`linkingNumberRot_hopfMap`, `HopfSign.lean`).

Auxiliary lemmas live in the namespace `Milnor.Problems.HopfProps`.
-/

open Set Filter Topology Function Module TopologicalSpace
open scoped ContDiff Manifold

noncomputable section

namespace Milnor

namespace Problems

open Sphere Framed

local notation "𝔼" n:max => EuclideanSpace ℝ (Fin n)

variable {d : ℕ}

namespace HopfProps

/-- A rotation sending `q` to the north pole moves every other point off the north pole. -/
theorem rot_ne_north_of_ne {k : ℕ} {R : 𝔼 (k + 2) ≃ₗᵢ[ℝ] 𝔼 (k + 2)} {q : Sph (k + 1)}
    (hRq : R q.1 = (north : Sph (k + 1)).1) {x : Sph (k + 1)} (hx : x ≠ q) :
    R x.1 ≠ (north : Sph (k + 1)).1 := fun h =>
  hx (Subtype.ext (R.injective (h.trans hRq.symm)))

/-- **Two distinct common regular values of `g` and `g ∘ f`**: the regular values of maps from
compact manifolds form open dense sets (Brown), and a point of `S^{d+1}` is meagre. -/
theorem exists_regular_pair_comp (hd : 1 ≤ d) {f : Sph (d + (d + 1)) → Sph (d + 1)}
    {g : Sph (d + 1) → Sph (d + 1)}
    (hf : ContMDiff 𝓘(ℝ, 𝔼 (d + (d + 1))) 𝓘(ℝ, 𝔼 (d + 1)) ∞ f)
    (hg : ContMDiff 𝓘(ℝ, 𝔼 (d + 1)) 𝓘(ℝ, 𝔼 (d + 1)) ∞ g) :
    ∃ y z : Sph (d + 1), y ≠ z ∧
      IsRegularValue 𝓘(ℝ, 𝔼 (d + 1)) 𝓘(ℝ, 𝔼 (d + 1)) g y ∧
      IsRegularValue 𝓘(ℝ, 𝔼 (d + 1)) 𝓘(ℝ, 𝔼 (d + 1)) g z ∧
      IsRegularValue 𝓘(ℝ, 𝔼 (d + (d + 1))) 𝓘(ℝ, 𝔼 (d + 1)) (g ∘ f) y ∧
      IsRegularValue 𝓘(ℝ, 𝔼 (d + (d + 1))) 𝓘(ℝ, 𝔼 (d + 1)) (g ∘ f) z := by
  have hgf : ContMDiff 𝓘(ℝ, 𝔼 (d + (d + 1))) 𝓘(ℝ, 𝔼 (d + 1)) ∞ (g ∘ f) := hg.comp hf
  have ho : IsOpen (regularValues 𝓘(ℝ, 𝔼 (d + 1)) 𝓘(ℝ, 𝔼 (d + 1)) g ∩
      regularValues 𝓘(ℝ, 𝔼 (d + (d + 1))) 𝓘(ℝ, 𝔼 (d + 1)) (g ∘ f)) :=
    (HopfInv.isOpen_setOf_isRegularValue hg).inter (HopfInv.isOpen_setOf_isRegularValue hgf)
  have hdense : Dense (regularValues 𝓘(ℝ, 𝔼 (d + 1)) 𝓘(ℝ, 𝔼 (d + 1)) g ∩
      regularValues 𝓘(ℝ, 𝔼 (d + (d + 1))) 𝓘(ℝ, 𝔼 (d + 1)) (g ∘ f)) :=
    (dense_regularValues hg).inter_of_isOpen_right (dense_regularValues hgf)
      (HopfInv.isOpen_setOf_isRegularValue hgf)
  obtain ⟨y, hy⟩ := hdense.nonempty
  have hpm : IsMeagre ({y} : Set (Sph (d + 1))) := by
    have h := isMeagre_image_of_finrank_lt (I := 𝓘(ℝ, ℝ)) (J := 𝓘(ℝ, 𝔼 (d + 1)))
      (g := fun _ : ℝ => y) (U := univ)
      (by rw [Module.finrank_self, finrank_euclideanSpace_fin]; omega) isOpen_univ
      contMDiffOn_const
    rwa [univ_nonempty.image_const] at h
  obtain ⟨z, hz, hzy⟩ := exists_mem_open_not_mem_of_isMeagre ho ⟨y, hy⟩ hpm
  exact ⟨y, z, fun h => hzy (mem_singleton_iff.2 h.symm), hy.1, hz.1, hy.2, hz.2⟩

end HopfProps

/-- **Problem 15, odd `p`** (`p = d + 1`): the Hopf invariant of a smooth map
`f : S^{2p−1} → S^p` vanishes when `p` is odd. -/
theorem hopfInvariant_eq_zero_of_odd (hd : 1 ≤ d) (hodd : Odd (d + 1))
    {f : Sph (d + (d + 1)) → Sph (d + 1)}
    (hf : ContMDiff 𝓘(ℝ, 𝔼 (d + (d + 1))) 𝓘(ℝ, 𝔼 (d + 1)) ∞ f) : hopfInvariant f = 0 := by
  obtain ⟨y, z, hyz, hy, hz⟩ := HopfInv.exists_regular_pair hd hf
  obtain ⟨q, hqy, hqz⟩ := HopfInv.exists_ne_ne hf hy hf hz
  obtain ⟨R, hR, hRq⟩ := exists_rotation_to_north (k := d + d) q
  have hRy : ∀ x, f x = y → R x.1 ≠ (north : Sph (d + d + 1)).1 := fun x hx =>
    HopfProps.rot_ne_north_of_ne hRq (by rintro rfl; exact hqy hx)
  have hRz : ∀ x, f x = z → R x.1 ≠ (north : Sph (d + d + 1)).1 := fun x hx =>
    HopfProps.rot_ne_north_of_ne hRq (by rintro rfl; exact hqz hx)
  have h1 := linkPre_eq_linkingNumberRot hd hf hy hf hz hR hRy hRz
    (fun x hx hx' => hyz (hx.symm.trans hx'))
  have h2 := linkPre_eq_linkingNumberRot hd hf hz hf hy hR hRz hRy
    (fun x hx hx' => hyz (hx'.symm.trans hx))
  let _ := (isSliceSubmanifold_preim hf hy).chartedSpace
  have _ := (isSliceSubmanifold_preim hf hy).isManifold
  let _ := (isSliceSubmanifold_preim hf hz).chartedSpace
  have _ := (isSliceSubmanifold_preim hf hz).isManifold
  have : CompactSpace (f ⁻¹' {y}) :=
    isCompact_iff_compactSpace.1 (isClosed_singleton.preimage hf.continuous).isCompact
  have : CompactSpace (f ⁻¹' {z}) :=
    isCompact_iff_compactSpace.1 (isClosed_singleton.preimage hf.continuous).isCompact
  have hdisj : ∀ (a : f ⁻¹' {y}) (b : f ⁻¹' {z}), (a : Sph (d + (d + 1))) ≠ b := fun a b h =>
    hyz ((a.2 : f a.1 = y).symm.trans ((congrArg f h).trans (b.2 : f b.1 = z)))
  -- the symmetry of Problem 13 for the projected preimages
  have hsymm := linkingNumber_symm (a := d) (b := d) (k := d + d) rfl rfl (by omega)
    (oA := preimOr hf hy (posB y) (posB_orientation y))
    (oB := preimOr hf hz (posB z) (posB_orientation z))
    (contMDiff_stN_comp (isSliceSubmanifold_preim hf hy).contMDiff_val R fun x => hRy x.1 x.2)
    (contMDiff_stN_comp (isSliceSubmanifold_preim hf hz).contMDiff_val R fun x => hRz x.1 x.2)
    (stN_comp_disjoint hdisj R (fun x => hRy x.1 x.2) (fun x => hRz x.1 x.2))
  have hsign : ((-1 : ℤ) ^ ((d + 1) * (d + 1))) = -1 := (hodd.mul hodd).neg_one_pow
  rw [hsign, neg_one_mul] at hsymm
  have key : linkPre hf hz hf hy = -linkPre hf hy hf hz :=
    h2.trans (hsymm.trans (congrArg Neg.neg h1.symm))
  rw [linkPre_eq_hopfInvariant hd hf hy hz hyz, linkPre_eq_hopfInvariant hd hf hz hy hyz.symm]
    at key
  omega

/-- **Problem 15, composition**: for smooth `f : S^{2p−1} → S^p` and `g : S^p → S^p`,
`H(g ∘ f) = (deg g)² · H(f)`. -/
theorem hopfInvariant_comp (hd : 1 ≤ d) {f : Sph (d + (d + 1)) → Sph (d + 1)}
    (hf : ContMDiff 𝓘(ℝ, 𝔼 (d + (d + 1))) 𝓘(ℝ, 𝔼 (d + 1)) ∞ f) {g : Sph (d + 1) → Sph (d + 1)}
    (hg : ContMDiff 𝓘(ℝ, 𝔼 (d + 1)) 𝓘(ℝ, 𝔼 (d + 1)) ∞ g) :
    hopfInvariant (g ∘ f) =
      deg (sphOrStd (d + 1)) (sphOrStd (d + 1)) g ^ 2 * hopfInvariant f := by
  obtain ⟨y, z, hyz, hy, hz, hgfy, hgfz⟩ := HopfProps.exists_regular_pair_comp hd hf hg
  obtain ⟨q, hqy, hqz⟩ := HopfInv.exists_ne_ne (hg.comp hf) hgfy (hg.comp hf) hgfz
  obtain ⟨R, hR, hRq⟩ := exists_rotation_to_north (k := d + d) q
  have hRN : ∀ x, (g (f x) = y ∨ g (f x) = z) → R x.1 ≠ (north : Sph (d + d + 1)).1 := by
    intro x hx
    refine HopfProps.rot_ne_north_of_ne hRq ?_
    rintro rfl
    rcases hx with h | h
    · exact hqy h
    · exact hqz h
  have h1 := linkPre_eq_hopfInvariant hd (hg.comp hf) hgfy hgfz hyz
  have h2 := linkPre_eq_linkingNumberRot hd (hg.comp hf) hgfy (hg.comp hf) hgfz hR
    (fun x hx => hRN x (Or.inl hx)) (fun x hx => hRN x (Or.inr hx))
    (fun x hx hx' => hyz (hx.symm.trans hx'))
  have h3 := linkingNumberRot_comp_eq_finsum' hd hf hg hy hz hgfy hgfz hyz posB posB_orientation
    hR hRN
  rw [← h1]
  refine h2.trans (h3.trans ?_)
  calc _ = ∑ᶠ yᵢ ∈ g ⁻¹' {y}, ∑ᶠ zⱼ ∈ g ⁻¹' {z},
        signAt (sphOrStd (d + 1)) (sphOrStd (d + 1)) g yᵢ *
          signAt (sphOrStd (d + 1)) (sphOrStd (d + 1)) g zⱼ * hopfInvariant f := by
        refine finsum_congr fun yᵢ => finsum_congr fun hyᵢ => finsum_congr fun zⱼ =>
          finsum_congr fun hzⱼ => ?_
        congr 1
        -- each inner linking number is `H(f)`
        have hyᵢ' : g yᵢ = y := hyᵢ
        have hzⱼ' : g zⱼ = z := hzⱼ
        have hne : yᵢ ≠ zⱼ := fun h => hyz (by rw [← hyᵢ', ← hzⱼ', h])
        have hRy : ∀ x, f x = yᵢ → R x.1 ≠ (north : Sph (d + d + 1)).1 :=
          fun x hx => hRN x (Or.inl ((congrArg g hx).trans hyᵢ'))
        have hRz : ∀ x, f x = zⱼ → R x.1 ≠ (north : Sph (d + d + 1)).1 :=
          fun x hx => hRN x (Or.inr ((congrArg g hx).trans hzⱼ'))
        exact (linkPre_eq_linkingNumberRot hd hf
          (HopfComp.isRegularValue_of_comp rfl hf hg hgfy hyᵢ) hf
          (HopfComp.isRegularValue_of_comp rfl hf hg hgfz hzⱼ) hR hRy hRz
          (fun x hx hx' => hne (hx.symm.trans hx'))).symm.trans
          (linkPre_eq_hopfInvariant hd hf _ _ hne)
    _ = ∑ᶠ yᵢ ∈ g ⁻¹' {y}, signAt (sphOrStd (d + 1)) (sphOrStd (d + 1)) g yᵢ *
          ((∑ᶠ zⱼ ∈ g ⁻¹' {z}, signAt (sphOrStd (d + 1)) (sphOrStd (d + 1)) g zⱼ) *
            hopfInvariant f) := by
        refine finsum_congr fun yᵢ => finsum_congr fun _ => ?_
        rw [finsum_mem_mul, mul_finsum_mem]
        refine finsum_congr fun zⱼ => finsum_congr fun _ => ?_
        ring
    _ = deg (sphOrStd (d + 1)) (sphOrStd (d + 1)) g ^ 2 * hopfInvariant f := by
        rw [finsum_signAt_eq_deg hg hz, ← finsum_mem_mul, finsum_signAt_eq_deg hg hy]
        ring

/-- **Problem 15, the Hopf fibration**: `H(π) = −1` for `π = hopfMap : S³ → S²`.  Milnor states
`H(π) = 1`; with the book's conventions taken literally (outward normal first on the sphere, the
preimage orientation of §5, the linking number as the degree of `(x − x')/‖x − x'‖`) the linking
number of the two fibres is `−1` (`linkingNumberRot_hopfMap`, `HopfSign.lean`). -/
theorem hopfInvariant_hopfMap : hopfInvariant (d := 1) hopfMap = -1 := by
  have h1 := linkPre_eq_hopfInvariant (d := 1) le_rfl contMDiff_hopfMap
    (isRegularValue_hopfMap hopfY) (isRegularValue_hopfMap hopfZ) HopfSign.hopfY_ne_hopfZ
  have h2 := linkPre_eq_linkingNumberRot (d := 1) le_rfl contMDiff_hopfMap
    (isRegularValue_hopfMap hopfY) contMDiff_hopfMap (isRegularValue_hopfMap hopfZ)
    HopfSign.isRotation_refl HopfSign.hopf_north_y HopfSign.hopf_north_z
    (fun x hx hx' => HopfSign.hopf_disj x x hx hx' rfl)
  exact h1.symm.trans (h2.trans (linkingNumberRot_hopfMap (posB hopfY) (posB_orientation hopfY)
    (posB hopfZ) (posB_orientation hopfZ)))

end Problems

end Milnor
