import Milnor.Chapter8.LinkDegree
import Milnor.Chapter8.DegComp

/-!
# The composition formula for linking numbers of preimages (Milnor §8, Problem 15)

The formula `H(g ∘ f) = (deg g)² · H(f)` for the Hopf invariant rests on a formula for linking
numbers after a fixed rotation.  Let `S = S^{2d+1}` (written `Sph (d + (d + 1))`),
`f : S → S^{d+1}` and `g : S^{d+1} → S^{d+1}` smooth, and `y ≠ z` regular values of `g` and of
`g ∘ f`.  Then `g⁻¹(y)` and `g⁻¹(z)` are finite, every `yᵢ ∈ g⁻¹(y)` and `zⱼ ∈ g⁻¹(z)` is a regular
value of `f` (`HopfComp.isRegularValue_of_comp`), and `(g ∘ f)⁻¹(y) = ⋃ᵢ f⁻¹(yᵢ)`.

* `degAt_comp_eq_finsum`: **the local composition formula** — for `Φ : M → N`, `G : N → P` smooth
  between oriented manifolds of the same dimension, with `G⁻¹(w)` and `(G ∘ Φ)⁻¹(w)` finite,
  `degAt (G ∘ Φ) w = ∑_{w' ∈ G⁻¹(w)} signAt G w' · degAt Φ w'`.
* `finsum_signAt_eq_deg`: `∑_{yᵢ ∈ g⁻¹(y)} signAt g yᵢ = deg g` for a regular value `y` of `g`.
* `linkingNumberRot_comp_eq_finsum`: for an admissible rotation `R` and a direction `e` which is a
  regular value of all the linking maps involved,
  `l_R((g∘f)⁻¹(y), (g∘f)⁻¹(z)) = ∑ᵢ ∑ⱼ signAt g yᵢ · signAt g zⱼ · l_R(f⁻¹(yᵢ), f⁻¹(zⱼ))`.
* `linkingNumberRot_comp_eq_finsum'`: the same formula without `e` (a common regular value of the
  finitely many linking maps always exists).

**Proof.**  By `degAt_phiR_eq_linkingNumberRot` both linking numbers are local degrees of the maps
`Φ_h = phiR h h R ∘ Subtype.val : D_R → (S^{d+1} × S^{d+1}) × S^{2d}` (`h = g ∘ f`, resp. `h = f`),
at `((y, z), e)`, resp. `((yᵢ, zⱼ), e)`.  Now `Φ_{g ∘ f} = G ∘ Φ_f` for
`G = (g × g) × id`, whose fibre over `((y, z), e)` is `(g⁻¹(y) × g⁻¹(z)) × {e}`, and the sign of `G`
at `((yᵢ, zⱼ), e)` is `signAt g yᵢ · signAt g zⱼ` (`signAt_prodMap`).  The local composition formula
applies; its finiteness hypothesis for `Φ_{g ∘ f}` holds because its fibre over `((y, z), e)` is the
image of the (finite) fibre of the linking map of the compact manifold
`(g ∘ f)⁻¹(y) × (g ∘ f)⁻¹(z)` over its regular value `e` (`HopfComp.finite_preimage_phiR`).

Auxiliary lemmas live in the namespace `Milnor.Problems.HopfComp`.
-/

open Set Filter Topology Function Module TopologicalSpace
open scoped ContDiff Manifold

noncomputable section

namespace Milnor

namespace Problems

open Sphere

local notation "𝔼 " n:max => EuclideanSpace ℝ (Fin n)

/-! ### The local composition formula -/

section general

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N]
  {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℝ F'] [FiniteDimensional ℝ F']
  {H'' : Type*} [TopologicalSpace H''] {K : ModelWithCorners ℝ F' H''}
  {P : Type*} [TopologicalSpace P] [ChartedSpace H'' P] [IsManifold K ∞ P] {n : ℕ}

namespace HopfComp

omit [IsManifold I ∞ M] [IsManifold J ∞ N] [IsManifold K ∞ P] in
/-- If `z` is a regular value of `g ∘ f` and `g : N → P` is a map between manifolds of the same
dimension, then every `y ∈ g⁻¹(z)` is a regular value of `f` (for any dimension of `M`): `dg ∘ df`
onto forces `dg` onto, hence one-to-one, hence `df` onto.  (`isRegularValue_of_isRegularValue_comp`
of `DegComp.lean` assumes that `M` has the same dimension as well.) -/
theorem isRegularValue_of_comp (hFF' : finrank ℝ F = finrank ℝ F') {f : M → N} {g : N → P}
    (hf : ContMDiff I J ∞ f) (hg : ContMDiff J K ∞ g) {z : P}
    (hz : IsRegularValue I K (fun x => g (f x)) z) {y : N} (hy : g y = z) :
    IsRegularValue I J f y := by
  intro x hx
  have hc : mfd I K (fun x => g (f x)) x = (mfd J K g (f x)).comp (mfd I J f x) :=
    HasMFDerivAt.mfd_eq ((hasMFDerivAt_mfd (I := J) (J := K)
      (hg.mdifferentiableAt (x := f x) (by simp))).comp x
      (hasMFDerivAt_mfd (I := I) (J := J) (hf.mdifferentiableAt (by simp))))
  have hsurj : Surjective (mfd I K (fun x => g (f x)) x) := hz x (by simp only [hx, hy])
  rw [hc, ContinuousLinearMap.coe_comp] at hsurj
  have hinj : Injective (mfd J K g (f x)) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (f := (mfd J K g (f x) : F →ₗ[ℝ] F')) hFF').2 hsurj.of_comp
  show Surjective (mfd I J f x)
  intro v
  obtain ⟨u, hu⟩ := hsurj (mfd J K g (f x) v)
  exact ⟨u, hinj hu⟩

end HopfComp

/-- **General local composition formula.**  `Φ : M → N`, `G : N → P` smooth, all of the same
dimension `n` and oriented; `w ∈ P` with `G⁻¹(w)` and `(G ∘ Φ)⁻¹(w)` finite.  Then
`degAt (G ∘ Φ) w = ∑ᶠ w' ∈ G⁻¹(w), signAt G w' * degAt Φ w'`.  (The fibres `Φ⁻¹(w')`,
`w' ∈ G⁻¹(w)`, are finite as subsets of `(G ∘ Φ)⁻¹(w)`; no regular value hypothesis is needed.) -/
theorem degAt_comp_eq_finsum (hE : finrank ℝ E = n) (hF : finrank ℝ F = n)
    (oM : Orient I M n) (oN : Orient J N n) (oP : Orient K P n) {Φ : M → N} {G : N → P}
    (hΦ : ContMDiff I J ∞ Φ) (hG : ContMDiff J K ∞ G) {w : P} (hGw : (G ⁻¹' {w}).Finite)
    (hGΦw : ((fun x => G (Φ x)) ⁻¹' {w}).Finite) :
    degAt oM oP (fun x => G (Φ x)) w =
      ∑ᶠ w' ∈ G ⁻¹' {w}, signAt oN oP G w' * degAt oM oN Φ w' := by
  have hfin : ∀ w' ∈ G ⁻¹' {w}, (Φ ⁻¹' {w'}).Finite := fun w' hw' =>
    hGΦw.subset fun x hx => by
      have hx' : Φ x = w' := hx
      have hw'' : G w' = w := hw'
      show G (Φ x) = w
      rw [hx', hw'']
  -- `(G ∘ Φ)⁻¹(w)` is the disjoint union of the fibres `Φ⁻¹(w')`, `w' ∈ G⁻¹(w)`
  have hunion : (fun x => G (Φ x)) ⁻¹' {w} = ⋃ w' ∈ G ⁻¹' {w}, Φ ⁻¹' {w'} := by
    ext x
    simp
  have hdisj : (G ⁻¹' {w}).PairwiseDisjoint (fun w' => Φ ⁻¹' {w'}) := by
    intro w₁ _ w₂ _ hne
    exact Set.disjoint_left.2 fun x hx1 hx2 => hne ((hx1 : Φ x = w₁).symm.trans hx2)
  unfold degAt
  rw [hunion, finsum_mem_biUnion hdisj hGw hfin]
  refine finsum_mem_congr rfl fun w' _ => ?_
  rw [mul_finsum_mem]
  refine finsum_mem_congr rfl fun x hx => ?_
  have hx' : Φ x = w' := hx
  rw [signAt_comp' hE hF oM oN oP (hΦ.mdifferentiableAt (by simp))
    (hG.mdifferentiableAt (by simp)), hx']

end general

/-! ### Auxiliary lemmas -/

namespace HopfComp

/-- A finite sum over a product of finite sets is an iterated finite sum. -/
theorem finsum_mem_prod_eq {α β M : Type*} [AddCommMonoid M] {s : Set α} {t : Set β}
    (F : α × β → M) (hs : s.Finite) (ht : t.Finite) :
    ∑ᶠ p ∈ s ×ˢ t, F p = ∑ᶠ a ∈ s, ∑ᶠ b ∈ t, F (a, b) := by
  lift s to Finset α using hs
  lift t to Finset β using ht
  rw [← Finset.coe_product, finsum_mem_coe_finset, Finset.sum_product]
  simp only [finsum_mem_coe_finset]

variable {d : ℕ}

/-- The fibre of `Φ = phiR g f R ∘ Subtype.val` over `((y, z), e)` is finite when `e` is a regular
value of the linking map of `g⁻¹(y)` and `f⁻¹(z)`: it is the image of the fibre of the linking map
of the compact manifold `g⁻¹(y) × f⁻¹(z)` over `e`. -/
theorem finite_preimage_phiR {f g : Sph (d + (d + 1)) → Sph (d + 1)}
    (hf : ContMDiff 𝓘(ℝ, 𝔼 (d + (d + 1))) 𝓘(ℝ, 𝔼 (d + 1)) ∞ f)
    (hg : ContMDiff 𝓘(ℝ, 𝔼 (d + (d + 1))) 𝓘(ℝ, 𝔼 (d + 1)) ∞ g) {y z : Sph (d + 1)}
    (hy : IsRegularValue 𝓘(ℝ, 𝔼 (d + (d + 1))) 𝓘(ℝ, 𝔼 (d + 1)) g y)
    (hz : IsRegularValue 𝓘(ℝ, 𝔼 (d + (d + 1))) 𝓘(ℝ, 𝔼 (d + 1)) f z)
    (hdisj : ∀ x x', g x = y → f x' = z → x ≠ x')
    {R : 𝔼 (d + d + 2) ≃ₗᵢ[ℝ] 𝔼 (d + d + 2)}
    (hRy : ∀ x, g x = y → R x.1 ≠ (north : Sph (d + d + 1)).1)
    (hRz : ∀ x, f x = z → R x.1 ≠ (north : Sph (d + d + 1)).1)
    {e : Sph (d + d)}
    (he : letI := (isSliceSubmanifold_preim hg hy).chartedSpace
      letI := (isSliceSubmanifold_preim hf hz).chartedSpace
      IsRegularValue (𝓘(ℝ, 𝔼 d).prod 𝓘(ℝ, 𝔼 d)) 𝓘(ℝ, 𝔼 (d + d))
        (linkMap (fun x : g ⁻¹' {y} => stN (R x.1.1)) (fun x : f ⁻¹' {z} => stN (R x.1.1)))
        e) :
    ((phiR g f R ∘ (Subtype.val : domR R → Sph (d + (d + 1)) × Sph (d + (d + 1)))) ⁻¹'
      {((y, z), e)}).Finite := by
  let _ := (isSliceSubmanifold_preim hg hy).chartedSpace
  have _ := (isSliceSubmanifold_preim hg hy).isManifold
  let _ := (isSliceSubmanifold_preim hf hz).chartedSpace
  have _ := (isSliceSubmanifold_preim hf hz).isManifold
  have : CompactSpace (g ⁻¹' {y}) :=
    isCompact_iff_compactSpace.1 (isClosed_singleton.preimage hg.continuous).isCompact
  have : CompactSpace (f ⁻¹' {z}) :=
    isCompact_iff_compactSpace.1 (isClosed_singleton.preimage hf.continuous).isCompact
  have hlink := LinkDeg.contMDiff_linkMap_preim hg hf hy hz hdisj R hRy hRz
  have hfin := he.finite_preimage ((finrank_prod_eq hZ hZ).trans hZ.symm) hlink (by simp)
  -- the map `g⁻¹(y) × f⁻¹(z) → D_R`, `(x, x') ↦ (x, x')`, is onto the fibre of `Φ`
  obtain ⟨φ, hφ⟩ : ∃ φ : g ⁻¹' {y} × f ⁻¹' {z} → domR R, ∀ p, (φ p).1 = (p.1.1, p.2.1) :=
    ⟨fun p => ⟨(p.1.1, p.2.1), mem_domR.2 ⟨hRy p.1.1 p.1.2, hRz p.2.1 p.2.2,
      hdisj p.1.1 p.2.1 p.1.2 p.2.2⟩⟩, fun p => rfl⟩
  refine (hfin.image φ).subset fun q hq => ?_
  have hq' : phiR g f R q.1 = ((y, z), e) := hq
  have h1 : g q.1.1 = y := congrArg (fun w => w.1.1) hq'
  have h2 : f q.1.2 = z := congrArg (fun w => w.1.2) hq'
  refine ⟨(⟨q.1.1, h1⟩, ⟨q.1.2, h2⟩), congrArg Prod.snd hq', ?_⟩
  exact Subtype.ext (hφ _)

end HopfComp

/-! ### The composition formula for linking numbers -/

variable {d : ℕ}

/-- `∑ᶠ yᵢ ∈ g⁻¹(y), signAt g yᵢ = deg g` for a regular value `y` of `g`. -/
theorem finsum_signAt_eq_deg {g : Sph (d + 1) → Sph (d + 1)}
    (hg : ContMDiff 𝓘(ℝ, 𝔼 (d + 1)) 𝓘(ℝ, 𝔼 (d + 1)) ∞ g) {y : Sph (d + 1)}
    (hy : IsRegularValue 𝓘(ℝ, 𝔼 (d + 1)) 𝓘(ℝ, 𝔼 (d + 1)) g y) :
    ∑ᶠ yᵢ ∈ g ⁻¹' {y}, signAt (sphOrStd (d + 1)) (sphOrStd (d + 1)) g yᵢ =
      deg (sphOrStd (d + 1)) (sphOrStd (d + 1)) g := by
  have := preconnectedSpace (show 0 < d + 1 by omega)
  exact (deg_eq hZ hZ _ _ hg hy).symm

/-- **The composition formula for linking numbers of preimages.**  `f : S^{2d+1} → S^{d+1}` and
`g : S^{d+1} → S^{d+1}` smooth, `y ≠ z` regular values of `g` and of `g ∘ f`, `B` a choice of
positive bases of the tangent spaces of `S^{d+1}`.  For an admissible rotation `R` (all points of
`(g ∘ f)⁻¹ {y, z}` avoid `R⁻¹(north)`) and a direction `e` that is a regular value of the linking
map of `(g∘f)⁻¹(y) × (g∘f)⁻¹(z)` and of every `f⁻¹(yᵢ) × f⁻¹(zⱼ)`:
`l_R((g∘f)⁻¹(y), (g∘f)⁻¹(z)) = ∑ᵢ ∑ⱼ signAt g yᵢ * signAt g zⱼ * l_R(f⁻¹(yᵢ), f⁻¹(zⱼ))`.  Each
`yᵢ ∈ g⁻¹(y)` is a regular value of `f` by `HopfComp.isRegularValue_of_comp`, which provides the
submanifold structure of `f⁻¹(yᵢ)`. -/
theorem linkingNumberRot_comp_eq_finsum (hd : 1 ≤ d) {f : Sph (d + (d + 1)) → Sph (d + 1)}
    {g : Sph (d + 1) → Sph (d + 1)}
    (hf : ContMDiff 𝓘(ℝ, 𝔼 (d + (d + 1))) 𝓘(ℝ, 𝔼 (d + 1)) ∞ f)
    (hg : ContMDiff 𝓘(ℝ, 𝔼 (d + 1)) 𝓘(ℝ, 𝔼 (d + 1)) ∞ g) {y z : Sph (d + 1)}
    (hy : IsRegularValue 𝓘(ℝ, 𝔼 (d + 1)) 𝓘(ℝ, 𝔼 (d + 1)) g y)
    (hz : IsRegularValue 𝓘(ℝ, 𝔼 (d + 1)) 𝓘(ℝ, 𝔼 (d + 1)) g z)
    (hgfy : IsRegularValue 𝓘(ℝ, 𝔼 (d + (d + 1))) 𝓘(ℝ, 𝔼 (d + 1)) (g ∘ f) y)
    (hgfz : IsRegularValue 𝓘(ℝ, 𝔼 (d + (d + 1))) 𝓘(ℝ, 𝔼 (d + 1)) (g ∘ f) z) (hyz : y ≠ z)
    (B : Sph (d + 1) → Basis (Fin (d + 1)) ℝ (𝔼 (d + 1)))
    (hB : ∀ y, (B y).orientation = (sphOrStd (d + 1)).or y)
    {R : 𝔼 (d + d + 2) ≃ₗᵢ[ℝ] 𝔼 (d + d + 2)} (hR : IsRotation R)
    (hRN : ∀ x, (g (f x) = y ∨ g (f x) = z) → R x.1 ≠ (north : Sph (d + d + 1)).1)
    {e : Sph (d + d)}
    (he : letI := (isSliceSubmanifold_preim (hg.comp hf) hgfy).chartedSpace
      letI := (isSliceSubmanifold_preim (hg.comp hf) hgfz).chartedSpace
      IsRegularValue (𝓘(ℝ, 𝔼 d).prod 𝓘(ℝ, 𝔼 d)) 𝓘(ℝ, 𝔼 (d + d))
        (linkMap (fun x : (g ∘ f) ⁻¹' {y} => stN (R x.1.1))
          (fun x : (g ∘ f) ⁻¹' {z} => stN (R x.1.1))) e)
    (he' : ∀ (yᵢ zⱼ : Sph (d + 1)) (hyᵢ : g yᵢ = y) (hzⱼ : g zⱼ = z),
      letI := (isSliceSubmanifold_preim hf
        (HopfComp.isRegularValue_of_comp rfl hf hg hgfy hyᵢ)).chartedSpace
      letI := (isSliceSubmanifold_preim hf
        (HopfComp.isRegularValue_of_comp rfl hf hg hgfz hzⱼ)).chartedSpace
      IsRegularValue (𝓘(ℝ, 𝔼 d).prod 𝓘(ℝ, 𝔼 d)) 𝓘(ℝ, 𝔼 (d + d))
        (linkMap (fun x : f ⁻¹' {yᵢ} => stN (R x.1.1)) (fun x : f ⁻¹' {zⱼ} => stN (R x.1.1))) e) :
    letI := (isSliceSubmanifold_preim (hg.comp hf) hgfy).chartedSpace
    haveI := (isSliceSubmanifold_preim (hg.comp hf) hgfy).isManifold
    letI := (isSliceSubmanifold_preim (hg.comp hf) hgfz).chartedSpace
    haveI := (isSliceSubmanifold_preim (hg.comp hf) hgfz).isManifold
    linkingNumberRot rfl (preimOr (hg.comp hf) hgfy (B y) (hB y))
        (preimOr (hg.comp hf) hgfz (B z) (hB z)) Subtype.val Subtype.val R =
      ∑ᶠ (yᵢ) (hyᵢ : yᵢ ∈ g ⁻¹' {y}), ∑ᶠ (zⱼ) (hzⱼ : zⱼ ∈ g ⁻¹' {z}),
        signAt (sphOrStd (d + 1)) (sphOrStd (d + 1)) g yᵢ *
          signAt (sphOrStd (d + 1)) (sphOrStd (d + 1)) g zⱼ *
          (letI := (isSliceSubmanifold_preim hf
            (HopfComp.isRegularValue_of_comp rfl hf hg hgfy hyᵢ)).chartedSpace
           haveI := (isSliceSubmanifold_preim hf
            (HopfComp.isRegularValue_of_comp rfl hf hg hgfy hyᵢ)).isManifold
           letI := (isSliceSubmanifold_preim hf
            (HopfComp.isRegularValue_of_comp rfl hf hg hgfz hzⱼ)).chartedSpace
           haveI := (isSliceSubmanifold_preim hf
            (HopfComp.isRegularValue_of_comp rfl hf hg hgfz hzⱼ)).isManifold
           linkingNumberRot rfl
            (preimOr hf (HopfComp.isRegularValue_of_comp rfl hf hg hgfy hyᵢ) (B yᵢ) (hB yᵢ))
            (preimOr hf (HopfComp.isRegularValue_of_comp rfl hf hg hgfz hzⱼ) (B zⱼ) (hB zⱼ))
            Subtype.val Subtype.val R) := by
  let _ := (isSliceSubmanifold_preim (hg.comp hf) hgfy).chartedSpace
  have _ := (isSliceSubmanifold_preim (hg.comp hf) hgfy).isManifold
  let _ := (isSliceSubmanifold_preim (hg.comp hf) hgfz).chartedSpace
  have _ := (isSliceSubmanifold_preim (hg.comp hf) hgfz).isManifold
  have hdisj : ∀ x x', (g ∘ f) x = y → (g ∘ f) x' = z → x ≠ x' := fun x x' hx hx' hxx' =>
    hyz (hx.symm.trans (hxx' ▸ hx'))
  have hRy : ∀ x, (g ∘ f) x = y → R x.1 ≠ (north : Sph (d + d + 1)).1 :=
    fun x hx => hRN x (Or.inl hx)
  have hRz : ∀ x, (g ∘ f) x = z → R x.1 ≠ (north : Sph (d + d + 1)).1 :=
    fun x hx => hRN x (Or.inr hx)
  -- the left side is the local degree of `Φ_{g ∘ f}` at `((y, z), e)`
  rw [← degAt_phiR_eq_linkingNumberRot hd (hg.comp hf) (hg.comp hf) hgfy hgfz (B y) (hB y) (B z)
    (hB z) hdisj hR hRy hRz he]
  -- the factorization `Φ_{g ∘ f} = G ∘ Φ_f` with `G = (g × g) × id`
  have hΦ : ContMDiff ((𝓘(ℝ, 𝔼 (d + (d + 1)))).prod 𝓘(ℝ, 𝔼 (d + (d + 1))))
      ((𝓘(ℝ, 𝔼 (d + 1)).prod 𝓘(ℝ, 𝔼 (d + 1))).prod 𝓘(ℝ, 𝔼 (d + d))) ∞
      (phiR f f R ∘ (Subtype.val : domR R → Sph (d + (d + 1)) × Sph (d + (d + 1)))) :=
    fun q => (contMDiffAt_phiR hf hf q.1 q.2).comp q contMDiff_subtype_val.contMDiffAt
  have hG : ContMDiff ((𝓘(ℝ, 𝔼 (d + 1)).prod 𝓘(ℝ, 𝔼 (d + 1))).prod 𝓘(ℝ, 𝔼 (d + d)))
      ((𝓘(ℝ, 𝔼 (d + 1)).prod 𝓘(ℝ, 𝔼 (d + 1))).prod 𝓘(ℝ, 𝔼 (d + d))) ∞
      (Prod.map (Prod.map g g) (id : Sph (d + d) → Sph (d + d))) :=
    (hg.prodMap hg).prodMap contMDiff_id
  have hgy : (g ⁻¹' {y}).Finite := hy.finite_preimage rfl hg (by simp)
  have hgz : (g ⁻¹' {z}).Finite := hz.finite_preimage rfl hg (by simp)
  have hpre : Prod.map (Prod.map g g) (id : Sph (d + d) → Sph (d + d)) ⁻¹' {((y, z), e)} =
      ((g ⁻¹' {y}) ×ˢ (g ⁻¹' {z})) ×ˢ {e} := by
    ext ⟨⟨a, b⟩, c⟩
    simp [and_assoc]
  have hfinG : (Prod.map (Prod.map g g) (id : Sph (d + d) → Sph (d + d)) ⁻¹'
      {((y, z), e)}).Finite := by
    rw [hpre]
    exact (hgy.prod hgz).prod (finite_singleton e)
  have hfinGΦ :=
    HopfComp.finite_preimage_phiR (hg.comp hf) (hg.comp hf) hgfy hgfz hdisj hRy hRz he
  have hE : finrank ℝ (𝔼 (d + (d + 1)) × 𝔼 (d + (d + 1))) = ((d + 1) + (d + 1)) + (d + d) :=
    (finrank_prod_eq hZ hZ).trans (by omega)
  have hF : finrank ℝ ((𝔼 (d + 1) × 𝔼 (d + 1)) × 𝔼 (d + d)) = ((d + 1) + (d + 1)) + (d + d) :=
    finrank_prod_eq (finrank_prod_eq hZ hZ) hZ
  refine (degAt_comp_eq_finsum hE hF (orDomR R) orTarget orTarget hΦ hG hfinG hfinGΦ).trans ?_
  -- the sum over `G⁻¹((y, z), e) = (g⁻¹(y) × g⁻¹(z)) × {e}` as a double sum
  rw [hpre, Set.prod_singleton, finsum_mem_image (fun p _ q _ h => (Prod.ext_iff.1 h).1),
    HopfComp.finsum_mem_prod_eq _ hgy hgz]
  refine finsum_congr fun yᵢ => finsum_congr fun hyᵢ => finsum_congr fun zⱼ =>
    finsum_congr fun hzⱼ => ?_
  have hyᵢ' : g yᵢ = y := hyᵢ
  have hzⱼ' : g zⱼ = z := hzⱼ
  -- the sign of `G` at `((yᵢ, zⱼ), e)`
  have hsG : signAt orTarget orTarget (Prod.map (Prod.map g g) (id : Sph (d + d) → Sph (d + d)))
      ((yᵢ, zⱼ), e) = signAt (sphOrStd (d + 1)) (sphOrStd (d + 1)) g yᵢ *
        signAt (sphOrStd (d + 1)) (sphOrStd (d + 1)) g zⱼ := by
    have h1 : signAt orTarget orTarget (Prod.map (Prod.map g g) (id : Sph (d + d) → Sph (d + d)))
        ((yᵢ, zⱼ), e) =
        signAt ((sphOrStd (d + 1)).prod hZ hZ (sphOrStd (d + 1)))
          ((sphOrStd (d + 1)).prod hZ hZ (sphOrStd (d + 1))) (Prod.map g g) (yᵢ, zⱼ) *
        signAt (sphOrStd (d + d)) (sphOrStd (d + d)) id e :=
      signAt_prodMap (finrank_prod_eq hZ hZ) hZ (finrank_prod_eq hZ hZ) hZ _ _ _ _
        ((hg.prodMap hg).mdifferentiableAt (by simp)) mdifferentiableAt_id
    have h2 : signAt ((sphOrStd (d + 1)).prod hZ hZ (sphOrStd (d + 1)))
        ((sphOrStd (d + 1)).prod hZ hZ (sphOrStd (d + 1))) (Prod.map g g) (yᵢ, zⱼ) =
        signAt (sphOrStd (d + 1)) (sphOrStd (d + 1)) g yᵢ *
          signAt (sphOrStd (d + 1)) (sphOrStd (d + 1)) g zⱼ :=
      signAt_prodMap hZ hZ hZ hZ _ _ _ _ (hg.mdifferentiableAt (by simp))
        (hg.mdifferentiableAt (by simp))
    rw [h1, h2, signAt_id, mul_one]
  -- the local degree of `Φ_f` at `((yᵢ, zⱼ), e)` is the linking number of `f⁻¹(yᵢ)`, `f⁻¹(zⱼ)`
  have hdisj' : ∀ x x', f x = yᵢ → f x' = zⱼ → x ≠ x' := by
    rintro x x' hx hx' rfl
    exact hyz (by rw [← hyᵢ', ← hzⱼ', ← hx, ← hx'])
  have hRy' : ∀ x, f x = yᵢ → R x.1 ≠ (north : Sph (d + d + 1)).1 :=
    fun x hx => hRN x (Or.inl ((congrArg g hx).trans hyᵢ'))
  have hRz' : ∀ x, f x = zⱼ → R x.1 ≠ (north : Sph (d + d + 1)).1 :=
    fun x hx => hRN x (Or.inr ((congrArg g hx).trans hzⱼ'))
  rw [hsG, degAt_phiR_eq_linkingNumberRot hd hf hf
    (HopfComp.isRegularValue_of_comp rfl hf hg hgfy hyᵢ)
    (HopfComp.isRegularValue_of_comp rfl hf hg hgfz hzⱼ) (B yᵢ) (hB yᵢ) (B zⱼ) (hB zⱼ) hdisj' hR
    hRy' hRz' (he' yᵢ zⱼ hyᵢ hzⱼ)]

/-- **The composition formula for linking numbers of preimages**, without the auxiliary direction:
the finitely many linking maps of `(g∘f)⁻¹(y) × (g∘f)⁻¹(z)` and of the `f⁻¹(yᵢ) × f⁻¹(zⱼ)` have a
common regular value `e`, to which `linkingNumberRot_comp_eq_finsum` applies. -/
theorem linkingNumberRot_comp_eq_finsum' (hd : 1 ≤ d) {f : Sph (d + (d + 1)) → Sph (d + 1)}
    {g : Sph (d + 1) → Sph (d + 1)}
    (hf : ContMDiff 𝓘(ℝ, 𝔼 (d + (d + 1))) 𝓘(ℝ, 𝔼 (d + 1)) ∞ f)
    (hg : ContMDiff 𝓘(ℝ, 𝔼 (d + 1)) 𝓘(ℝ, 𝔼 (d + 1)) ∞ g) {y z : Sph (d + 1)}
    (hy : IsRegularValue 𝓘(ℝ, 𝔼 (d + 1)) 𝓘(ℝ, 𝔼 (d + 1)) g y)
    (hz : IsRegularValue 𝓘(ℝ, 𝔼 (d + 1)) 𝓘(ℝ, 𝔼 (d + 1)) g z)
    (hgfy : IsRegularValue 𝓘(ℝ, 𝔼 (d + (d + 1))) 𝓘(ℝ, 𝔼 (d + 1)) (g ∘ f) y)
    (hgfz : IsRegularValue 𝓘(ℝ, 𝔼 (d + (d + 1))) 𝓘(ℝ, 𝔼 (d + 1)) (g ∘ f) z) (hyz : y ≠ z)
    (B : Sph (d + 1) → Basis (Fin (d + 1)) ℝ (𝔼 (d + 1)))
    (hB : ∀ y, (B y).orientation = (sphOrStd (d + 1)).or y)
    {R : 𝔼 (d + d + 2) ≃ₗᵢ[ℝ] 𝔼 (d + d + 2)} (hR : IsRotation R)
    (hRN : ∀ x, (g (f x) = y ∨ g (f x) = z) → R x.1 ≠ (north : Sph (d + d + 1)).1) :
    letI := (isSliceSubmanifold_preim (hg.comp hf) hgfy).chartedSpace
    haveI := (isSliceSubmanifold_preim (hg.comp hf) hgfy).isManifold
    letI := (isSliceSubmanifold_preim (hg.comp hf) hgfz).chartedSpace
    haveI := (isSliceSubmanifold_preim (hg.comp hf) hgfz).isManifold
    linkingNumberRot rfl (preimOr (hg.comp hf) hgfy (B y) (hB y))
        (preimOr (hg.comp hf) hgfz (B z) (hB z)) Subtype.val Subtype.val R =
      ∑ᶠ (yᵢ) (hyᵢ : yᵢ ∈ g ⁻¹' {y}), ∑ᶠ (zⱼ) (hzⱼ : zⱼ ∈ g ⁻¹' {z}),
        signAt (sphOrStd (d + 1)) (sphOrStd (d + 1)) g yᵢ *
          signAt (sphOrStd (d + 1)) (sphOrStd (d + 1)) g zⱼ *
          (letI := (isSliceSubmanifold_preim hf
            (HopfComp.isRegularValue_of_comp rfl hf hg hgfy hyᵢ)).chartedSpace
           haveI := (isSliceSubmanifold_preim hf
            (HopfComp.isRegularValue_of_comp rfl hf hg hgfy hyᵢ)).isManifold
           letI := (isSliceSubmanifold_preim hf
            (HopfComp.isRegularValue_of_comp rfl hf hg hgfz hzⱼ)).chartedSpace
           haveI := (isSliceSubmanifold_preim hf
            (HopfComp.isRegularValue_of_comp rfl hf hg hgfz hzⱼ)).isManifold
           linkingNumberRot rfl
            (preimOr hf (HopfComp.isRegularValue_of_comp rfl hf hg hgfy hyᵢ) (B yᵢ) (hB yᵢ))
            (preimOr hf (HopfComp.isRegularValue_of_comp rfl hf hg hgfz hzⱼ) (B zⱼ) (hB zⱼ))
            Subtype.val Subtype.val R) := by
  have hgy : (g ⁻¹' {y}).Finite := hy.finite_preimage rfl hg (by simp)
  have hgz : (g ⁻¹' {z}).Finite := hz.finite_preimage rfl hg (by simp)
  have : Finite (g ⁻¹' {y} × g ⁻¹' {z}) := by
    have := hgy.to_subtype
    have := hgz.to_subtype
    infer_instance
  have hdisj : ∀ x x', (g ∘ f) x = y → (g ∘ f) x' = z → x ≠ x' := fun x x' hx hx' hxx' =>
    hyz (hx.symm.trans (hxx' ▸ hx'))
  have hRy : ∀ x, (g ∘ f) x = y → R x.1 ≠ (north : Sph (d + d + 1)).1 :=
    fun x hx => hRN x (Or.inl hx)
  have hRz : ∀ x, (g ∘ f) x = z → R x.1 ≠ (north : Sph (d + d + 1)).1 :=
    fun x hx => hRN x (Or.inr hx)
  -- the regular values of the linking map of `(g ∘ f)⁻¹(y) × (g ∘ f)⁻¹(z)` are dense
  have hs : letI := (isSliceSubmanifold_preim (hg.comp hf) hgfy).chartedSpace
      letI := (isSliceSubmanifold_preim (hg.comp hf) hgfz).chartedSpace
      Dense (regularValues (𝓘(ℝ, 𝔼 d).prod 𝓘(ℝ, 𝔼 d)) 𝓘(ℝ, 𝔼 (d + d))
        (linkMap (fun x : (g ∘ f) ⁻¹' {y} => stN (R x.1.1))
          (fun x : (g ∘ f) ⁻¹' {z} => stN (R x.1.1)))) := by
    let _ := (isSliceSubmanifold_preim (hg.comp hf) hgfy).chartedSpace
    have _ := (isSliceSubmanifold_preim (hg.comp hf) hgfy).isManifold
    let _ := (isSliceSubmanifold_preim (hg.comp hf) hgfz).chartedSpace
    have _ := (isSliceSubmanifold_preim (hg.comp hf) hgfz).isManifold
    exact dense_regularValues
      (LinkDeg.contMDiff_linkMap_preim (hg.comp hf) (hg.comp hf) hgfy hgfz hdisj R hRy hRz)
  -- those of the linking maps of the `f⁻¹(yᵢ) × f⁻¹(zⱼ)` are dense and open
  have ht : ∀ i : g ⁻¹' {y} × g ⁻¹' {z},
      letI := (isSliceSubmanifold_preim hf
        (HopfComp.isRegularValue_of_comp rfl hf hg hgfy i.1.2)).chartedSpace
      letI := (isSliceSubmanifold_preim hf
        (HopfComp.isRegularValue_of_comp rfl hf hg hgfz i.2.2)).chartedSpace
      Dense (regularValues (𝓘(ℝ, 𝔼 d).prod 𝓘(ℝ, 𝔼 d)) 𝓘(ℝ, 𝔼 (d + d))
        (linkMap (fun x : f ⁻¹' {i.1.1} => stN (R x.1.1))
          (fun x : f ⁻¹' {i.2.1} => stN (R x.1.1)))) ∧
      IsOpen (regularValues (𝓘(ℝ, 𝔼 d).prod 𝓘(ℝ, 𝔼 d)) 𝓘(ℝ, 𝔼 (d + d))
        (linkMap (fun x : f ⁻¹' {i.1.1} => stN (R x.1.1))
          (fun x : f ⁻¹' {i.2.1} => stN (R x.1.1)))) := by
    rintro ⟨⟨yᵢ, hyᵢ⟩, ⟨zⱼ, hzⱼ⟩⟩
    have hyᵢ' : g yᵢ = y := hyᵢ
    have hzⱼ' : g zⱼ = z := hzⱼ
    let _ := (isSliceSubmanifold_preim hf
      (HopfComp.isRegularValue_of_comp rfl hf hg hgfy hyᵢ)).chartedSpace
    have _ := (isSliceSubmanifold_preim hf
      (HopfComp.isRegularValue_of_comp rfl hf hg hgfy hyᵢ)).isManifold
    let _ := (isSliceSubmanifold_preim hf
      (HopfComp.isRegularValue_of_comp rfl hf hg hgfz hzⱼ)).chartedSpace
    have _ := (isSliceSubmanifold_preim hf
      (HopfComp.isRegularValue_of_comp rfl hf hg hgfz hzⱼ)).isManifold
    have : CompactSpace (f ⁻¹' {yᵢ}) :=
      isCompact_iff_compactSpace.1 (isClosed_singleton.preimage hf.continuous).isCompact
    have : CompactSpace (f ⁻¹' {zⱼ}) :=
      isCompact_iff_compactSpace.1 (isClosed_singleton.preimage hf.continuous).isCompact
    have hdisj' : ∀ x x', f x = yᵢ → f x' = zⱼ → x ≠ x' := by
      rintro x x' hx hx' rfl
      exact hyz (by rw [← hyᵢ', ← hzⱼ', ← hx, ← hx'])
    have hRy' : ∀ x, f x = yᵢ → R x.1 ≠ (north : Sph (d + d + 1)).1 :=
      fun x hx => hRN x (Or.inl ((congrArg g hx).trans hyᵢ'))
    have hRz' : ∀ x, f x = zⱼ → R x.1 ≠ (north : Sph (d + d + 1)).1 :=
      fun x hx => hRN x (Or.inr ((congrArg g hx).trans hzⱼ'))
    exact dense_isOpen_regularValues (finrank_prod_eq hZ hZ) hZ
      (((preimOr hf (HopfComp.isRegularValue_of_comp rfl hf hg hgfy hyᵢ) (B yᵢ) (hB yᵢ)).prod
        hZ hZ (preimOr hf (HopfComp.isRegularValue_of_comp rfl hf hg hgfz hzⱼ) (B zⱼ)
          (hB zⱼ))).cast rfl)
      (sphOrStd (d + d))
      (LinkDeg.contMDiff_linkMap_preim hf hf (HopfComp.isRegularValue_of_comp rfl hf hg hgfy hyᵢ)
        (HopfComp.isRegularValue_of_comp rfl hf hg hgfz hzⱼ) hdisj' R hRy' hRz')
  obtain ⟨e, he, he'⟩ := exists_mem_of_dense_of_isOpen hs (fun i => (ht i).1) fun i => (ht i).2
  exact linkingNumberRot_comp_eq_finsum hd hf hg hy hz hgfy hgfz hyz B hB hR hRN he
    fun yᵢ zⱼ hyᵢ hzⱼ => he' (⟨yᵢ, hyᵢ⟩, ⟨zⱼ, hzⱼ⟩)

end Problems

end Milnor
