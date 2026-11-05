import Morse.Chapter2.Submanifold
import Morse.Chapter3.EulerChar
import Morse.Chapter3.ReebMorse
import Morse.Chapter3.ReebGluing

/-!
Milnor, *Morse Theory*, §4, p. 25: Theorem 4.1 (Reeb), and Remarks 1 and 2.

# Reeb's theorem: two non-degenerate critical points make a sphere

## Milnor's text, paraphrased

**Theorem 4.1 (Reeb).**  A compact manifold `M` carrying a differentiable function `f` with just
two critical points, both non-degenerate, is homeomorphic to a sphere.

*Milnor's proof* (eight lines, with a figure of the flow lines of `grad f` sweeping a small cap at
the bottom of `M` up to the top): Theorem 3.1 and the Lemma of Morse (2.2) do it.  The two
critical points are the minimum `p` and the maximum `q`; normalize `f(p) = 0`, `f(q) = 1`.  For
small `ε`, Lemma 2.2 shows that `M^ε = f⁻¹[0, ε]` and `f⁻¹[1 - ε, 1]` are closed `n`-cells, and
Theorem 3.1 that `M^ε` is homeomorphic to `M^{1-ε}`.  So `M` is the union of the two closed
`n`-cells `M^{1-ε}` and `f⁻¹[1 - ε, 1]`, matched along their common boundary, and Milnor leaves the
construction of a homeomorphism with `Sⁿ` to the reader as easy.

**Remark 1.**  The theorem stays true when the two critical points are allowed to be degenerate,
but the proof is harder (Milnor refers to his paper in Bull. Soc. Math. France 87 (1959),
Theorem 1(3), and to an abstract of R. Rosen, Notices Amer. Math. Soc. 7 (1960), Lemma 1).

**Remark 2.**  `M` need not be *diffeomorphic* to `Sⁿ` with its usual differentiable structure:
in *On manifolds homeomorphic to the 7-sphere* (Ann. of Math. 64 (1956)) Milnor proves that a
7-manifold with a non-standard differentiable structure is homeomorphic to `S⁷` by exhibiting on it
a function with two non-degenerate critical points.

## What is formalized

* `Morse.reeb`: **Reeb's theorem.**  Let `N ⊆ V` be a compact slice submanifold
  (`Milnor.IsSliceSubmanifold`) of dimension `n` of a finite-dimensional real normed space `V`,
  and `f = F|N` the restriction of a smooth `F : V → ℝ`.  If `f` has exactly two critical points
  (`{q | IsCriticalPointM Z f q}.ncard = 2`), both non-degenerate, then `N` is homeomorphic to the
  unit sphere `Sⁿ` of `EuclideanSpace ℝ (Fin (n + 1))`.  For `n ≥ 1` this is Milnor's proof
  (`Morse.reeb_of_finrank_pos`); the case `n = 0` is `Morse.reeb_of_finrank_eq_zero`.
* `Morse.reeb_of_contMDiff`: the same for a compact submanifold `N ⊆ ℝᴷ⁺¹` and *any* smooth
  `f : N → ℝ` (such an `f` is the restriction of a smooth function on `ℝᴷ⁺¹`,
  `Morse.exists_contDiff_comp_val_eq`): Milnor's statement for compact submanifolds of Euclidean
  space.

For `n ≥ 1` the proof is Milnor's, made complete in four steps.

1. **The critical points are the minimum and the maximum** (`Morse.exists_min_max_of_ncard_eq_two`,
   on any compact manifold): `f` attains its minimum at some `p` and its maximum at some `q`; both
   are critical, of index `0` and `n` (`Morse/Chapter3/ReebMorse.lean`).  `f(p) < f(q)`, since
   otherwise `f` is constant and `p` is also a maximum, of index `n ≠ 0`.  So `p ≠ q` are the two
   critical points, and every other point `x` has `f(p) < f(x) < f(q)`, a point where an extreme
   value is attained being critical.
2. **Two small closed `n`-cells** (`Morse.exists_morse_chart_of_isLocalMin`,
   `Morse.exists_morse_chart_of_isLocalMax`, `Morse.exists_image_closedBall_eq_sublevel`): in Morse
   charts `f = f(p) + ‖y‖²` near `p` and `f = f(q) - ‖y‖²` near `q`; for small `ε`, the map
   `v ↦ y⁻¹(√ε v)` carries the closed unit ball `Dⁿ` onto `{f ≤ f(p) + ε}` and the sphere `Sⁿ⁻¹`
   onto `{f = f(p) + ε}`, and similarly at `q` for `{f ≥ f(q) - ε}`.
3. **Stretching the lower cell** (`Morse.exists_diffeomorph_image_sublevel_level`): Theorem 3.1 on
   `[f(p) + ε, f(q) - ε]`, which contains no critical value, gives a diffeomorphism `Φ` of `N` with
   `Φ(N^{f(p)+ε}) = N^{f(q)-ε}` and `Φ(f⁻¹(f(p) + ε)) = f⁻¹(f(q) - ε)`.
4. **Gluing** (`Morse.nonempty_homeomorph_sphere_of_union_closedBall`,
   `Morse/Chapter3/ReebGluing.lean`): `N` is the union of the closed cells
   `D₁ = Φ(N^{f(p)+ε}) = {f ≤ f(q) - ε}` and `D₂ = {f ≥ f(q) - ε}`, which meet exactly in their
   common boundary sphere `{f = f(q) - ε}`; Alexander's trick extends the boundary identification
   over `D₂`, and the two cells become the two hemispheres of `Sⁿ`.

## What Milnor's proof leaves implicit

* **"The two critical points must be the minimum and maximum points."**  Compactness gives the
  extrema and Fermat's rule makes them critical; that the minimum and the maximum are *different*
  points needs `n ≥ 1` and the non-degeneracy (here: `p` would be a minimum and a maximum, of
  indices `0` and `n`).  That no other point takes an extreme value is used in Step 2.
* **The indices `0` and `n`**, without which Lemma 2.2 does not give cells (`ReebMorse.lean`).
* **"If `ε` is small enough"**: the whole set `f⁻¹[0, ε]` must lie inside the Morse chart, which
  needs compactness and the uniqueness of the minimum (`ReebMorse.lean`).
* **The boundaries must correspond.**  The gluing needs a homeomorphism `M^ε ≅ M^{1-ε}` which also
  carries the level `f⁻¹(ε)` onto `f⁻¹(1 - ε)`.  The *statement* of Theorem 3.1 does not say so;
  its proof does: the flow moves the levels of the slab at unit speed (`IsSlabFlow.image_level`).
  `Morse.theorem_3_1_submanifold` records only the sublevel sets, so its construction is repeated
  here with the extra conclusion.  (Without it, identifying the boundary of a cell would need
  invariance of domain.)
* **"It is now easy to construct a homeomorphism"**: the two cells are glued by a homeomorphism of
  `Sⁿ⁻¹`, which has to be extended over one of them (Alexander's trick); then the pasting lemma,
  and a continuous bijection from a compact space to a Hausdorff space is a homeomorphism
  (`ReebGluing.lean`).
* **Which sphere**: `Sⁿ` with `n = dim M`.  The normalization `f(p) = 0`, `f(q) = 1` is not needed.

## Differences from Milnor's setting

* `M` is a compact submanifold of a Euclidean (or finite-dimensional normed) space with a
  slice-chart atlas, as in `Morse.theorem_3_1_submanifold`, on which the proof rests.  Steps 1, 2
  and 4 are proved for abstract manifolds and topological spaces.  The abstract case is reduced to
  this one by Mathlib's Whitney embedding for compact manifolds in `Morse/Chapter4/Whitney.lean`:
  `Morse.reeb_of_compactSpace` is Reeb's theorem for an abstract compact Hausdorff manifold.
* **Dimension `0`** is treated separately (`Morse.reeb_of_finrank_eq_zero`): Milnor's proof does
  not apply, since `f` may be constant (a function on two points), but every point is critical, so
  `M` has two points, as `S⁰` does.
* "Only two critical points" is read as exactly two (`ncard = 2`); on a non-empty compact
  manifold of positive dimension the minimum and maximum give at least two.

## Not formalized

* **Remark 1** (degenerate critical points).  A proof is in `Exposition/Chapter3.md`, §1: Step 1
  still holds; Theorem 3.1 exhausts `M ∖ {q}` by an increasing sequence of images of a coordinate
  ball, so `M ∖ {q} ≅ ℝⁿ` by M. Brown's monotone union theorem (Proc. Amer. Math. Soc. 12 (1961)),
  and `M` is its one-point compactification.  Brown's theorem is not in Mathlib.
* **Remark 2** (homeomorphic, not diffeomorphic): Milnor's exotic `7`-spheres need characteristic
  classes and the signature theorem.  The proof above shows where smoothness is lost: Alexander's
  cone is in general not differentiable at the centre of the cell.
-/

open Set Filter Topology Function Module Metric
open scoped ContDiff Manifold

noncomputable section

namespace Morse

/-! ### Theorem 3.1 also matches the level sets -/

/-- A slab flow carries the level `a` onto the level `b`: `φ_{b-a}(F⁻¹(a)) = F⁻¹(b)`. -/
theorem IsSlabFlow.image_level {T : Type*} [TopologicalSpace T] {F : T → ℝ} {a b : ℝ}
    {φ : ℝ → T → T} (h : IsSlabFlow F a b φ) (hab : a ≤ b) :
    φ (b - a) '' (F ⁻¹' {a}) = F ⁻¹' {b} := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hx' : F x = a := hx
    have := h.apply_eq_add (x := x) ⟨hx'.ge, hx' ▸ hab⟩ (t := b - a) ⟨by linarith, by linarith⟩
    change F (φ (b - a) x) = b
    rw [this, hx']
    ring
  · intro hy
    have hy' : F y = b := hy
    refine ⟨φ (a - b) y, ?_, ?_⟩
    · have := h.apply_eq_add (x := y) ⟨hy' ▸ hab, hy'.le⟩ (t := a - b) ⟨by linarith, by linarith⟩
      change F (φ (a - b) y) = a
      rw [this, hy']
      ring
    · rw [← h.add, show b - a + (a - b) = 0 by ring, h.zero]

section Submanifold

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  {N : Set V}

/-- **Theorem 3.1 with the boundary levels** (the first half of `Morse.theorem_3_1_submanifold`,
with one more conclusion read off from its proof).  If `f = F|N` has no critical point in the
compact set `f⁻¹[a, b]`, there is a diffeomorphism `Φ` of `N` with `Φ(N^a) = N^b` *and*
`Φ(f⁻¹(a)) = f⁻¹(b)`: the time-`(b - a)` map of the flow of the same field. -/
theorem exists_diffeomorph_image_sublevel_level (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N)
    {F : V → ℝ} (hF : ContDiff ℝ ∞ F) {a b : ℝ} (hab : a ≤ b)
    (hK : IsCompact ((F ∘ Subtype.val : N → ℝ) ⁻¹' Icc a b))
    (hcrit : letI := hN.chartedSpace;
      ∀ q : N, F q ∈ Icc a b → ¬IsCriticalPointM Z (F ∘ Subtype.val) q) :
    letI := hN.chartedSpace
    ∃ Φ : Diffeomorph 𝓘(ℝ, Z) 𝓘(ℝ, Z) N N ∞,
      Φ '' sublevel (F ∘ Subtype.val) a = sublevel (F ∘ Subtype.val) b ∧
        Φ '' ((F ∘ Subtype.val) ⁻¹' {a}) = (F ∘ Subtype.val) ⁻¹' {b} := by
  let _ := hN.chartedSpace
  have := hN.isManifold
  -- the compact set `K = N ∩ F⁻¹[a, b]` in `V`
  set K : Set V := Subtype.val '' ((F ∘ Subtype.val : N → ℝ) ⁻¹' Icc a b) with hK_def
  have hKc : IsCompact K := hK.image continuous_subtype_val
  have hKN : K ⊆ N := by
    rintro _ ⟨q, -, rfl⟩
    exact q.2
  have hKF : ∀ x ∈ K, F x ∈ Icc a b := by
    rintro _ ⟨q, hq, rfl⟩
    exact hq
  -- the field `X = ρ Y` of the proof of `Morse.theorem_3_1_submanifold`
  obtain ⟨Y, hY, hYN, hYpos⟩ := exists_tangent_field hN hF hKc hKN
    fun q hq => hcrit q (hKF _ hq)
  have hg : ContDiff ℝ ∞ fun x => fderiv ℝ F x (Y x) :=
    (hF.fderiv_right (by simp)).clm_apply hY
  obtain ⟨ρ, hρ, hρs, hρO, -, hρK⟩ := exists_cutoff_mul hg hKc isOpen_chartDomain
    (hKN.trans (subset_chartDomain hN)) fun x hx => (hYpos x hx).ne'
  set X : V → V := fun x => ρ x • Y x with hX_def
  have hX : ContDiff ℝ ∞ X := hρ.smul hY
  have hXs : HasCompactSupport X := hρs.smul_right
  have hXN : ∀ q : N, X q ∈ tangentSubspace hN q := fun q => Submodule.smul_mem _ _ (hYN q)
  have hXO : tsupport X ⊆ chartDomain Z W N := (tsupport_smul_subset_left _ _).trans hρO
  have hXF : ∀ x ∈ K, fderiv ℝ F x (X x) = 1 := fun x hx => by
    rw [hX_def, map_smul, smul_eq_mul, hρK x hx]
  have hb := IsBddLipschitz.of_contDiff (hX.of_le (by simp)) hXs
  -- the flow preserves `N` and is a slab flow for `F|N`
  have hinv : ∀ x ∈ N, ∀ t, flow X t x ∈ N := fun x hx t =>
    flow_mem_of_tangent hN hX hXs hXN hXO hx t
  let φ : ℝ → N → N := fun t q => ⟨flow X t q, hinv q q.2 t⟩
  have hslab : IsSlabFlow (F ∘ Subtype.val : N → ℝ) a b φ :=
    { continuous := (hb.continuous_flow.comp (continuous_fst.prodMk
        (continuous_subtype_val.comp continuous_snd))).subtype_mk _
      zero := fun q => Subtype.ext (hb.flow_zero q)
      add := fun s t q => Subtype.ext (hb.flow_add s t q)
      continuous_F := hF.continuous.comp continuous_subtype_val
      hasDerivAt := fun q t ht => by
        have h1 := ((hF.differentiable (by simp)) (flow X t q)).hasFDerivAt.comp_hasDerivAt t
          (hb.hasDerivAt_flow t q)
        rw [hXF _ ⟨φ t q, ht, rfl⟩] at h1
        exact h1 }
  have hsmooth : ∀ t, ContMDiff 𝓘(ℝ, Z) 𝓘(ℝ, Z) ∞ (φ t) := fun t =>
    hN.contMDiff_codRestrict ((contDiff_flow (n := ⊤) hX le_top hXs t).contMDiff.comp
      hN.contMDiff_val) _
  let Φ : Diffeomorph 𝓘(ℝ, Z) 𝓘(ℝ, Z) N N ∞ :=
    { toFun := φ (b - a)
      invFun := φ (-(b - a))
      left_inv := fun q => Subtype.ext (hb.flow_neg_flow _ q)
      right_inv := fun q => Subtype.ext (hb.flow_flow_neg _ q)
      contMDiff_toFun := hsmooth _
      contMDiff_invFun := hsmooth _ }
  exact ⟨Φ, hslab.image_sublevel le_rfl hab le_rfl, hslab.image_level hab⟩

end Submanifold

/-! ### Step 1: the two critical points are the minimum and the maximum -/

section Step1

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

/-- **Step 1 of Reeb's theorem.**  Let `M` be a compact manifold of dimension `n ≥ 1` and `f` a
smooth function on `M` with exactly two critical points, both non-degenerate.  Then they are a
point `p` where `f` attains its minimum and a point `q` where it attains its maximum, `f` takes
values strictly between `f(p)` and `f(q)` at every other point, and the indices are `0` at `p` and
`n` at `q`. -/
theorem exists_min_max_of_ncard_eq_two [CompactSpace M] (hn : 0 < finrank ℝ E) {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (htwo : {x : M | IsCriticalPointM E f x}.ncard = 2)
    (hnd : ∀ x, IsCriticalPointM E f x → IsNondegenerate (hessianM E f x)) :
    ∃ p q : M, f p < f q ∧ (∀ x, IsCriticalPointM E f x ↔ x = p ∨ x = q) ∧
      (∀ x, x ≠ p → f p < f x) ∧ (∀ x, x ≠ q → f x < f q) ∧
      indexM E f p = 0 ∧ indexM E f q = finrank ℝ E := by
  have hfc : Continuous f := hf.continuous
  have : Nonempty M := by
    obtain ⟨x, -, -, -⟩ := Set.ncard_eq_two.1 htwo
    exact ⟨x⟩
  obtain ⟨p, -, hp⟩ := isCompact_univ.exists_isMinOn univ_nonempty hfc.continuousOn
  obtain ⟨q, -, hq⟩ := isCompact_univ.exists_isMaxOn univ_nonempty hfc.continuousOn
  have hp' : ∀ x, f p ≤ f x := fun x => isMinOn_iff.1 hp x (mem_univ x)
  have hq' : ∀ x, f x ≤ f q := fun x => isMaxOn_iff.1 hq x (mem_univ x)
  have hfU : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f univ := hf.contMDiffOn
  -- a point where the minimum (maximum) is attained is a local minimum (maximum)
  have hmin : ∀ x, f x = f p → IsLocalMin f x := fun x hx =>
    (isMinOn_iff.2 fun y _ => hx ▸ hp' y : IsMinOn f univ x).isLocalMin univ_mem
  have hmax : ∀ x, f x = f q → IsLocalMax f x := fun x hx =>
    (isMaxOn_iff.2 fun y _ => hx ▸ hq' y : IsMaxOn f univ x).isLocalMax univ_mem
  have hpc : IsCriticalPointM E f p := isCriticalPointM_of_isLocalMin (hmin p rfl)
  have hqc : IsCriticalPointM E f q := isCriticalPointM_of_isLocalMax (hmax q rfl)
  have hpi : indexM E f p = 0 :=
    indexM_eq_zero_of_isLocalMin isOpen_univ (mem_univ p) hfU ⟨hpc, hnd p hpc⟩ (hmin p rfl)
  have hqi : indexM E f q = finrank ℝ E :=
    indexM_eq_finrank_of_isLocalMax isOpen_univ (mem_univ q) hfU ⟨hqc, hnd q hqc⟩ (hmax q rfl)
  -- `f` is not constant: otherwise `p` would be a maximum too, of index `n ≠ 0`
  have hlt : f p < f q := by
    refine lt_of_le_of_ne (hp' q) fun heq => ?_
    have := indexM_eq_finrank_of_isLocalMax isOpen_univ (mem_univ p) hfU ⟨hpc, hnd p hpc⟩
      (hmax p heq)
    omega
  have hpq : p ≠ q := fun h => hlt.ne (h ▸ rfl)
  -- the critical set is `{p, q}`
  have hcrit : {p, q} = {x : M | IsCriticalPointM E f x} := by
    refine Set.eq_of_subset_of_ncard_le ?_ ?_ ?_
    · rintro x (rfl | rfl)
      exacts [hpc, hqc]
    · rw [htwo, Set.ncard_pair hpq]
    · exact Set.finite_of_ncard_ne_zero (by rw [htwo]; norm_num)
  have hcrit' : ∀ x, IsCriticalPointM E f x ↔ x = p ∨ x = q := fun x => by
    have h := congrArg (x ∈ ·) hcrit
    simp only [mem_insert_iff, mem_singleton_iff, eq_iff_iff] at h
    exact h.symm
  refine ⟨p, q, hlt, hcrit', fun x hx => ?_, fun x hx => ?_, hpi, hqi⟩
  · refine lt_of_le_of_ne (hp' x) fun heq => ?_
    rcases (hcrit' x).1 (isCriticalPointM_of_isLocalMin (hmin x heq.symm)) with h | h
    · exact hx h
    · rw [h] at heq
      exact hlt.ne heq
  · refine lt_of_le_of_ne (hq' x) fun heq => ?_
    rcases (hcrit' x).1 (isCriticalPointM_of_isLocalMax (hmax x heq)) with h | h
    · rw [h] at heq
      exact hlt.ne heq
    · exact hx h

end Step1

/-! ### Reeb's theorem -/

section Reeb

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  {N : Set V}

/-- **Theorem 4.1 (Reeb) in dimension `n ≥ 1`**, Milnor's proof.  Let `N ⊆ V` be a compact
submanifold of dimension `n ≥ 1` of a finite-dimensional real normed space, and `f = F|N` the
restriction of a smooth function `F : V → ℝ`.  If `f` has exactly two critical points, both
non-degenerate, then `N` is homeomorphic to the unit sphere `Sⁿ ⊆ ℝⁿ⁺¹`. -/
theorem reeb_of_finrank_pos (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N) (hNc : IsCompact N)
    {n : ℕ} (hn : finrank ℝ Z = n) (hn0 : 0 < n) {F : V → ℝ} (hF : ContDiff ℝ ∞ F)
    (htwo : letI := hN.chartedSpace;
      {q : N | IsCriticalPointM Z (F ∘ Subtype.val) q}.ncard = 2)
    (hnd : letI := hN.chartedSpace; ∀ q : N, IsCriticalPointM Z (F ∘ Subtype.val) q →
      IsNondegenerate (hessianM Z (F ∘ Subtype.val) q)) :
    Nonempty (N ≃ₜ sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) := by
  subst hn
  let _ := hN.chartedSpace
  have := hN.isManifold
  have : CompactSpace N := isCompact_iff_compactSpace.1 hNc
  set f : N → ℝ := F ∘ Subtype.val with hf_def
  have hfs : ContMDiff 𝓘(ℝ, Z) 𝓘(ℝ, ℝ) ∞ f := contMDiff_comp_val hN hF
  have hfc : Continuous f := hfs.continuous
  -- Step 1: the critical points are the minimum `p` and the maximum `q`
  obtain ⟨p, q, hlt, hcrit, hpmin, hqmax, -, -⟩ :=
    exists_min_max_of_ncard_eq_two hn0 hfs htwo hnd
  have hpc : IsCriticalPointM Z f p := (hcrit p).2 (Or.inl rfl)
  have hqc : IsCriticalPointM Z f q := (hcrit q).2 (Or.inr rfl)
  have hpl : IsLocalMin f p := (isMinOn_iff.2 fun x _ => by
    rcases eq_or_ne x p with rfl | h
    · exact le_rfl
    · exact (hpmin x h).le : IsMinOn f univ p).isLocalMin univ_mem
  have hql : IsLocalMax f q := (isMaxOn_iff.2 fun x _ => by
    rcases eq_or_ne x q with rfl | h
    · exact le_rfl
    · exact (hqmax x h).le : IsMaxOn f univ q).isLocalMax univ_mem
  -- Step 2: Morse charts `f = f(p) + ‖y‖²` near `p` and `f = f(q) - ‖y‖²` near `q`; the small
  -- sublevel sets `f ≤ f(p) + ε` and `f ≥ f(q) - ε` are closed balls
  obtain ⟨yp, -, hpy, -, hyp0, hfyp⟩ := exists_morse_chart_of_isLocalMin isOpen_univ (mem_univ p)
    hfs.contMDiffOn ⟨hpc, hnd p hpc⟩ hpl
  obtain ⟨yq, -, hqy, -, hyq0, hfyq⟩ := exists_morse_chart_of_isLocalMax isOpen_univ (mem_univ q)
    hfs.contMDiffOn ⟨hqc, hnd q hqc⟩ hql
  obtain ⟨δ₁, hδ₁, hball₁⟩ := exists_image_closedBall_eq_sublevel hfc hpmin yp hpy hyp0 hfyp
  obtain ⟨δ₂, hδ₂, hball₂⟩ := exists_image_closedBall_eq_sublevel (f := fun x => -f x) hfc.neg
    (fun x hx => neg_lt_neg (hqmax x hx)) yq hqy hyq0 (fun x hx => by rw [hfyq x hx]; ring)
  set ε := min (min δ₁ δ₂) (f q - f p) / 4 with hε_def
  have hm : 0 < min (min δ₁ δ₂) (f q - f p) := lt_min (lt_min hδ₁ hδ₂) (sub_pos.2 hlt)
  have hm₁ : min (min δ₁ δ₂) (f q - f p) ≤ δ₁ := (min_le_left _ _).trans (min_le_left _ _)
  have hm₂ : min (min δ₁ δ₂) (f q - f p) ≤ δ₂ := (min_le_left _ _).trans (min_le_right _ _)
  have hm₃ : min (min δ₁ δ₂) (f q - f p) ≤ f q - f p := min_le_right _ _
  have hε : 0 < ε := by positivity
  have hε₁ : ε < δ₁ := by linarith
  have hε₂ : ε < δ₂ := by linarith
  have hε₃ : f p + ε ≤ f q - ε := by linarith
  obtain ⟨hc₀, hi₀, himg₀, hsph₀⟩ := hball₁ ε hε hε₁
  obtain ⟨hc₂, hi₂, himg₂, hsph₂⟩ := hball₂ ε hε hε₂
  -- Step 3: Theorem 3.1 on `[f(p) + ε, f(q) - ε]`
  obtain ⟨Φ, hΦ, hΦl⟩ := exists_diffeomorph_image_sublevel_level hN hF hε₃
    (isClosed_Icc.preimage hfc).isCompact (by
      intro x hx hxc
      rcases (hcrit x).1 hxc with rfl | rfl
      · have : f x ∈ Icc (f x + ε) (f q - ε) := hx
        linarith [this.1]
      · have : f x ∈ Icc (f p + ε) (f x - ε) := hx
        linarith [this.2])
  have hΦ' : Φ '' {x | f x ≤ f p + ε} = {x | f x ≤ f q - ε} := hΦ
  have hΦl' : Φ '' {x | f x = f p + ε} = {x | f x = f q - ε} := hΦl
  -- Step 4: two closed balls glued along their boundary spheres
  refine nonempty_homeomorph_sphere_of_union_closedBall
    (h₁ := Φ ∘ fun v => yp.symm (√ε • v)) (h₂ := fun v => yq.symm (√ε • v))
    (Φ.continuous.comp_continuousOn hc₀) hc₂ (Φ.toHomeomorph.injective.comp_injOn hi₀) hi₂
    ?_ ?_ ?_
  · rw [image_comp, himg₀, hΦ', himg₂]
    ext x
    simp only [mem_union, mem_ofPred_eq, mem_univ, iff_true]
    by_contra h
    push Not at h
    linarith [h.1, h.2]
  · rw [image_comp, image_comp, himg₀, hsph₀, hΦ', hΦl', himg₂]
    ext x
    simp only [mem_inter_iff, mem_ofPred_eq]
    constructor
    · rintro ⟨h1, h2⟩
      linarith
    · intro h
      exact ⟨h.le, by linarith⟩
  · rw [hsph₂, image_comp, hsph₀, hΦl']
    ext x
    simp only [mem_ofPred_eq]
    constructor <;> intro h <;> linarith

omit [FiniteDimensional ℝ V] in
/-- **Theorem 4.1 (Reeb) in dimension `0`**: every point of `N` is critical, so `N` has exactly
two points, like `S⁰`.  (The gluing lemma, with two one-point balls and `S⁻¹ = ∅`, provides the
homeomorphism.) -/
theorem reeb_of_finrank_eq_zero (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N)
    (hZ : finrank ℝ Z = 0) {f : N → ℝ}
    (htwo : letI := hN.chartedSpace; {q : N | IsCriticalPointM Z f q}.ncard = 2) :
    Nonempty (N ≃ₜ sphere (0 : EuclideanSpace ℝ (Fin 1)) 1) := by
  let _ := hN.chartedSpace
  -- on a `0`-dimensional manifold every point is critical
  have hcrit : ∀ q : N, IsCriticalPointM Z f q := by
    intro q
    change mfderiv 𝓘(ℝ, Z) 𝓘(ℝ, ℝ) f q = 0
    ext v
    have hv : v = (0 : TangentSpace 𝓘(ℝ, Z) q) := finrank_zero_iff_forall_zero.1 hZ v
    rw [hv, map_zero, map_zero]
  have huniv : {q : N | IsCriticalPointM Z f q} = univ := eq_univ_of_forall hcrit
  rw [huniv] at htwo
  obtain ⟨p, q, hpq, hpq'⟩ := Set.ncard_eq_two.1 htwo
  -- the closed ball of `ℝ⁰` is a point and its boundary sphere is empty
  have hB : closedBall (0 : EuclideanSpace ℝ (Fin 0)) 1 = {0} := by
    ext x
    simp [Subsingleton.elim x 0]
  have hS : sphere (0 : EuclideanSpace ℝ (Fin 0)) 1 = ∅ := by
    ext x
    simp [Subsingleton.elim x 0]
  refine nonempty_homeomorph_sphere_of_union_closedBall (n := 0) (h₁ := fun _ => p)
    (h₂ := fun _ => q) continuousOn_const continuousOn_const
    (fun x _ y _ _ => Subsingleton.elim x y) (fun x _ y _ _ => Subsingleton.elim x y) ?_ ?_ ?_
  · rw [hB, image_singleton, image_singleton, hpq', insert_eq]
  · rw [hB, hS, image_singleton, image_singleton, image_empty]
    ext x
    simp only [mem_inter_iff, mem_singleton_iff, mem_empty_iff_false, iff_false, not_and]
    rintro rfl
    exact hpq
  · rw [hS, image_empty, image_empty]

/-- **Theorem 4.1 (Reeb)** (Milnor, p. 25).  Let `N ⊆ V` be a compact submanifold of dimension
`n` of a finite-dimensional real normed space `V`, and `f = F|N` the restriction of a smooth
function `F : V → ℝ`.  If `f` has exactly two critical points, both non-degenerate, then `N` is
homeomorphic to the unit sphere `Sⁿ ⊆ ℝⁿ⁺¹`.  (For `n ≥ 1` this is Milnor's proof,
`Morse.reeb_of_finrank_pos`; for `n = 0` it is trivial, `Morse.reeb_of_finrank_eq_zero`.) -/
theorem reeb (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N) (hNc : IsCompact N)
    {n : ℕ} (hn : finrank ℝ Z = n) {F : V → ℝ} (hF : ContDiff ℝ ∞ F)
    (htwo : letI := hN.chartedSpace;
      {q : N | IsCriticalPointM Z (F ∘ Subtype.val) q}.ncard = 2)
    (hnd : letI := hN.chartedSpace; ∀ q : N, IsCriticalPointM Z (F ∘ Subtype.val) q →
      IsNondegenerate (hessianM Z (F ∘ Subtype.val) q)) :
    Nonempty (N ≃ₜ sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn0
  · exact reeb_of_finrank_eq_zero hN hn htwo
  · exact reeb_of_finrank_pos hN hNc hn hn0 hF htwo hnd

/-- **Theorem 4.1 (Reeb)** (Milnor, p. 25) **for a smooth function on a compact submanifold of
`ℝᴷ⁺¹`.**  If `N ⊆ ℝᴷ⁺¹` is a compact submanifold of dimension `d + 1 ≥ 1` and the smooth function
`f : N → ℝ` has exactly two critical points, both non-degenerate, then `N` is homeomorphic to the
unit sphere `S^{d+1} ⊆ ℝ^{d+2}`.  (`f` extends to a smooth function on `ℝᴷ⁺¹`,
`Morse.exists_contDiff_comp_val_eq`, and `Morse.reeb` applies.) -/
theorem reeb_of_contMDiff {K d m : ℕ} {N : Set (EuclideanSpace ℝ (Fin (K + 1)))}
    (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1)))
      (EuclideanSpace ℝ (Fin (d + 1))) (EuclideanSpace ℝ (Fin m)) N)
    (hNc : IsCompact N) {f : N → ℝ}
    (hf : letI := hN.chartedSpace;
      ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin (d + 1))) 𝓘(ℝ, ℝ) ∞ f)
    (htwo : letI := hN.chartedSpace;
      {q : N | IsCriticalPointM (EuclideanSpace ℝ (Fin (d + 1))) f q}.ncard = 2)
    (hnd : letI := hN.chartedSpace;
      ∀ q : N, IsCriticalPointM (EuclideanSpace ℝ (Fin (d + 1))) f q →
        IsNondegenerate (hessianM (EuclideanSpace ℝ (Fin (d + 1))) f q)) :
    Nonempty (N ≃ₜ sphere (0 : EuclideanSpace ℝ (Fin (d + 2))) 1) := by
  let _ := hN.chartedSpace
  have hne : N.Nonempty := by
    obtain ⟨x, -, -, -⟩ := Set.ncard_eq_two.1 htwo
    exact ⟨x, x.2⟩
  obtain ⟨F, hF, rfl⟩ := exists_contDiff_comp_val_eq hN hNc hne hf
  exact reeb hN hNc finrank_euclideanSpace_fin hF htwo hnd

end Reeb

end Morse
