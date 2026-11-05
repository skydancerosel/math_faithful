import Morse.Chapter11.PositiveRicci
import Morse.Chapter10.PathHomology

/-!
Milnor, *Morse Theory*, §19, p. 106 (Theorem 19.6) with §17, p. 96 (homology read off from the
cells): the homological consequence of Theorem 19.6, for a submanifold `N ⊆ ℝᴷ` with the induced
metric.

# The homology of the path space in positive Ricci curvature

## Milnor's text, paraphrased

Theorem 19.6 (p. 106) gives `Ω(M; p, q)` the homotopy type of a CW complex with only finitely many
cells in each dimension.  Milnor does not draw the homological consequence, which cellular
homology makes immediate: `H_i(Ω; 𝕜)` is finite-dimensional for every `i`.  (On p. 96 he computes
`H_*(ΩSⁿ)` from the cells in this way.)

## In the embedded setting

* `Morse.slabEnergies`, `Morse.slab_homology`: for levels `a ≤ b` that are not energies of
  geodesics, `H_j(Ω^b, Ω^a; 𝕜)` is finite-dimensional, and it vanishes if no geodesic with energy
  in `(a, b)` has index `j`: by induction on the number of energies in `(a, b)`; a single energy
  is the slab computation of `Morse/Chapter10/PathHomology.lean`
  (`Morse.BrokenSetup.finrank_subsetHomology_Omega`), and several are separated by a regular level
  between the two smallest, with the exact sequence of the triple.
* `Morse.finiteDimensional_spaceHomology_omega`,
  `Morse.finiteDimensional_spaceHomology_omega_of_compact`: **`H_i(Ω(N; p, q); 𝕜)` is
  finite-dimensional for every `i`**, under the hypotheses of Theorem 19.6 (compact `N`,
  `dim N ≥ 2`, positive definite Ricci tensor), for end points not conjugate along any geodesic.

## What is used instead of cellular homology

The cell complexes of `Morse.IsCountableCellComplexType` have non-cellular attaching maps, so
cellular homology is not available; the homology is computed from the energy filtration of `Ω`
(Milnor's §3 and §5).  By the index estimate of 19.6, every geodesic of energy above
`((i + 2)πr)²` has index `≥ i + 2`, so the slabs above that level have no homology in degrees `i`
and `i + 1`; as every compact subset of `Ω` lies in some `Ω^a`, `H_i(Ω^a) ≅ H_i(Ω)` for a regular
level `a` above it (`Morse.Homology.spaceHomologyEquivOfSteps`), and `H_i(Ω^a)` is
finite-dimensional.  End points conjugate along some geodesic are not treated (see
`Morse/Chapter11/PositiveRicci.lean`).
-/

open Set Filter Topology Function Module Metric Real
open scoped ContDiff Manifold RealInnerProductSpace

universe u

noncomputable section

namespace Morse

open Morse.Homology

variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {N : Set V} {hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N}

variable (hN) in
/-- The energies in `(a, b)` of the geodesics from `p` to `q`. -/
def slabEnergies (p q : V) (a b : ℝ) : Set ℝ :=
  {e | ∃ γ ∈ pathSpace N p q, IsUnbrokenGeodesic hN γ ∧ energy γ 0 1 = e ∧ a < e ∧ e < b}

/-- **The homology of a slab of `Ω`** between two levels which are not energies of geodesics
(Milnor §3 in the path space, by induction on the number of critical values in the slab): it is
finite-dimensional in each degree, and vanishes in degree `j` if no geodesic in the slab has
index `j`. -/
theorem slab_homology {𝕜 : Type u} [Field 𝕜] (hcl : IsClosed N) {p q : V} (hp : p ∈ N)
    (hq : q ∈ N)
    (hnd : ∀ γ (hγ : γ ∈ pathSpace N p q), IsUnbrokenGeodesic hN γ → hessNullity hN hγ = 0)
    (n : ℕ) : ∀ {a b : ℝ} (hab : a ≤ b), (slabEnergies hN p q a b).ncard = n →
      (∀ γ ∈ pathSpace N p q, IsUnbrokenGeodesic hN γ → energy γ 0 1 ≠ a) →
      (∀ γ ∈ pathSpace N p q, IsUnbrokenGeodesic hN γ → energy γ 0 1 ≠ b) → ∀ j : ℕ,
      FiniteDimensional 𝕜 (subsetHomology 𝕜 j (sublevel_mono (PathSp.energyC N p q) hab)) ∧
        ((∀ γ ∈ pathSpace N p q, IsUnbrokenGeodesic hN γ → a < energy γ 0 1 →
          energy γ 0 1 < b → geodesicIndex hN p q γ ≠ j) →
          Subsingleton (subsetHomology 𝕜 j (sublevel_mono (PathSp.energyC N p q) hab))) := by
  induction n using Nat.strong_induction_on with
  | _ n ih => ?_
  intro a b hab hn hra hrb j
  have hfinS : (slabEnergies hN p q a b).Finite :=
    (finite_geodesicEnergies hcl hp hq hnd b).subset fun e ⟨γ, hγ, hg, he, _, heb⟩ =>
      ⟨γ, hγ, hg, he, he ▸ heb.le⟩
  rcases le_or_gt n 1 with hn1 | hn1
  · -- at most one critical value: the slab homology of Theorem 3.2 in the path space
    obtain ⟨m, ⟨B⟩⟩ := exists_brokenSetup_uniform hN hp hq (c := max b 0 + 1) (by positivity)
      (isCompact_closedRiemBall_of_isClosed hN hcl p _)
    have hb : b < max b 0 + 1 := by linarith [le_max_left b 0]
    have hone : ∀ e ∈ slabEnergies hN p q a b, ∀ e' ∈ slabEnergies hN p q a b, e = e' :=
      (Set.ncard_le_one hfinS).1 (hn ▸ hn1)
    obtain ⟨hfd, hfr⟩ := B.finrank_subsetHomology_Omega (𝕜 := 𝕜) hab hb
      (fun y hy hyg => by
        rw [← B.energy_path hy]
        exact ⟨hra _ (B.path_mem_pathSpace hy) hyg, hrb _ (B.path_mem_pathSpace hy) hyg⟩)
      (fun y hy hyg _ => hnd _ _ hyg)
      (fun y y' hy hy' hyg hyg' h1 h2 h3 h4 => hone _
        ⟨_, B.path_mem_pathSpace hy, hyg, B.energy_path hy, h1, h2⟩ _
        ⟨_, B.path_mem_pathSpace hy', hyg', B.energy_path hy', h3, h4⟩) j
    refine ⟨hfd, fun hidx => ?_⟩
    have h0 : finrank 𝕜 (subsetHomology 𝕜 j (sublevel_mono (PathSp.energyC N p q) hab)) = 0 := by
      have hempty : {y | y ∈ B.nodes ∧ IsUnbrokenGeodesic hN (B.path y) ∧ a < B.energy' y ∧
          B.energy' y < b ∧ B.geodIndex y = j} = ∅ := by
        refine eq_empty_of_forall_notMem fun y ⟨hy, hyg, h1, h2, hj⟩ => ?_
        refine hidx _ (B.path_mem_pathSpace hy) hyg (by rwa [B.energy_path hy])
          (by rwa [B.energy_path hy]) ?_
        rw [← B.geodIndex_eq_geodesicIndex hy, hj]
      rw [hfr, hempty, Set.ncard_empty]
    exact Module.finrank_zero_iff.1 h0
  · -- several critical values: split the slab between the two smallest ones
    set S := slabEnergies hN p q a b with hS_def
    have hne : S.Nonempty := Set.nonempty_of_ncard_ne_zero (by omega)
    set e₁ := hfinS.toFinset.min' (by simpa using hne) with he₁_def
    have he₁S : e₁ ∈ S := hfinS.mem_toFinset.1 (Finset.min'_mem _ _)
    have he₁min : ∀ e ∈ S, e₁ ≤ e := fun e he => Finset.min'_le _ _ (hfinS.mem_toFinset.2 he)
    have hS' : (S \ {e₁}).Finite := hfinS.sdiff
    have hS'card : (S \ {e₁}).ncard = n - 1 := by
      rw [Set.ncard_sdiff_singleton_of_mem he₁S, hn]
    have hne' : (S \ {e₁}).Nonempty := Set.nonempty_of_ncard_ne_zero (by omega)
    set e₂ := hS'.toFinset.min' (by simpa using hne') with he₂_def
    have he₂S : e₂ ∈ S \ {e₁} := hS'.mem_toFinset.1 (Finset.min'_mem _ _)
    have he₂min : ∀ e ∈ S \ {e₁}, e₂ ≤ e := fun e he => Finset.min'_le _ _ (hS'.mem_toFinset.2 he)
    have h12 : e₁ < e₂ := lt_of_le_of_ne (he₁min e₂ he₂S.1) (Ne.symm he₂S.2)
    obtain ⟨-, -, -, -, ha₁, -⟩ := id he₁S
    obtain ⟨-, -, -, -, -, hb₂⟩ := id he₂S.1
    set c := (e₁ + e₂) / 2 with hc_def
    have hac : a ≤ c := by linarith
    have hcb : c ≤ b := by linarith
    have hmid : ∀ e ∈ S, e ≠ e₁ → c < e := fun e he he1 => by
      have := he₂min e ⟨he, he1⟩
      linarith
    -- `c` is not the energy of a geodesic
    have hrc : ∀ γ ∈ pathSpace N p q, IsUnbrokenGeodesic hN γ → energy γ 0 1 ≠ c := by
      intro γ hγ hg he
      have hS : energy γ 0 1 ∈ S := ⟨γ, hγ, hg, rfl, by linarith, by linarith⟩
      have := hmid _ hS (by rw [he]; linarith)
      linarith
    -- the two halves
    have hSac : slabEnergies hN p q a c = {e₁} := by
      ext e
      constructor
      · rintro ⟨γ, hγ, hg, rfl, h1, h2⟩
        by_contra hne1
        have := hmid _ ⟨γ, hγ, hg, rfl, h1, by linarith⟩ hne1
        linarith
      · rintro rfl
        obtain ⟨γ, hγ, hg, he, h1, -⟩ := he₁S
        exact ⟨γ, hγ, hg, he, h1, by linarith⟩
    have hScb : slabEnergies hN p q c b = S \ {e₁} := by
      ext e
      constructor
      · rintro ⟨γ, hγ, hg, rfl, h1, h2⟩
        exact ⟨⟨γ, hγ, hg, rfl, by linarith, h2⟩, fun h => by
          rw [mem_singleton_iff] at h
          linarith⟩
      · rintro ⟨⟨γ, hγ, hg, rfl, h1, h2⟩, hne1⟩
        exact ⟨γ, hγ, hg, rfl, hmid _ ⟨γ, hγ, hg, rfl, h1, h2⟩ hne1, h2⟩
    obtain ⟨hfd1, hz1⟩ := ih 1 (by omega) hac (by rw [hSac, Set.ncard_singleton]) hra hrc j
    obtain ⟨hfd2, hz2⟩ := ih (n - 1) (by omega) hcb (by rw [hScb, hS'card]) hrc hrb j
    have E := subsetTripleLongExactSeq 𝕜 (sublevel_mono (PathSp.energyC N p q) hac)
      (sublevel_mono (PathSp.energyC N p q) hcb)
    refine ⟨E.finiteDimensional_middle j, fun hidx => E.subsingleton_B (hz1 fun γ hγ hg h1 h2 =>
      hidx γ hγ hg h1 (by linarith)) (hz2 fun γ hγ hg h1 h2 => hidx γ hγ hg (by linarith) h2)⟩

/-- **The homology of `Ω` is finite-dimensional in each degree** (the homological content of
Theorem 19.6): if `N` is closed in `V`, of dimension `≥ 2`, with `K(U, U) ≥ (n − 1)/r²`, and `q`
is not conjugate to `p` along any geodesic, then `H_i(Ω(N; p, q); 𝕜)` is finite-dimensional for
every `i`.  Below a level `a`, `Ω^a` has finite-dimensional homology (`Morse.slab_homology`); above
the energy `((i + 2)πr)²` every geodesic has index `≥ i + 2`, so the slabs have no homology in
degrees `i`, `i + 1`, and `H_i(Ω^a) ≅ H_i(Ω)`. -/
theorem finiteDimensional_spaceHomology_omega {𝕜 : Type u} [Field 𝕜] (hcl : IsClosed N)
    {r : ℝ} (hr : 0 < r) (hn : 2 ≤ finrank ℝ Z) (hRic : RicciLowerBound hN r) {p q : V}
    (hp : p ∈ N) (hq : q ∈ N) (hnc : q ∉ conjLocus hN p) (i : ℕ) :
    FiniteDimensional 𝕜 (spaceHomology 𝕜 i (PathSp N p q)) := by
  have hnd : ∀ γ (hγ : γ ∈ pathSpace N p q), IsUnbrokenGeodesic hN γ → hessNullity hN hγ = 0 :=
    fun _ hγ hgeo => hessNullity_eq_zero_of_notMem_conjLocus hnc hγ hgeo
  have hE0 : ∀ γ : ℝ → V, 0 ≤ energy γ 0 1 := fun γ => PathSp.energy_nonneg_of_le zero_le_one
  -- regular levels `a (k + 1) ∈ (k, k + 1)`, `a 0 = -1`
  have hlev : ∀ k : ℕ, ∃ x ∈ Ioo (k : ℝ) (k + 1), x ∉ {e | ∃ γ ∈ pathSpace N p q,
      IsUnbrokenGeodesic hN γ ∧ energy γ 0 1 = e ∧ e ≤ k + 1} := fun k =>
    ((Ioo_infinite (by linarith : (k : ℝ) < k + 1)).sdiff
      (finite_geodesicEnergies hcl hp hq hnd (k + 1))).nonempty
  choose x hx hxreg using hlev
  let a : ℕ → ℝ := fun k => match k with
    | 0 => -1
    | k + 1 => x k
  have ha0 : a 0 = -1 := rfl
  have haS : ∀ k, a (k + 1) = x k := fun k => rfl
  have ha_gt : ∀ k : ℕ, (k : ℝ) - 1 ≤ a k := by
    intro k
    cases k with
    | zero => simp [ha0]
    | succ k => rw [haS]; push_cast; linarith [(hx k).1]
  have ha_lt : ∀ k, a k < k := by
    intro k
    cases k with
    | zero => simp [ha0]
    | succ k => rw [haS]; push_cast; exact (hx k).2
  have ha : Monotone a := monotone_nat_of_le_succ fun k => by
    have h1 := ha_lt k
    have h2 := ha_gt (k + 1)
    push_cast at h2
    linarith
  have hreg : ∀ k, ∀ γ ∈ pathSpace N p q, IsUnbrokenGeodesic hN γ → energy γ 0 1 ≠ a k := by
    intro k γ hγ hgeo heq
    cases k with
    | zero => linarith [hE0 γ, ha0 ▸ heq]
    | succ k =>
      rw [haS] at heq
      exact hxreg k ⟨γ, hγ, hgeo, heq, (hx k).2.le⟩
  -- the filtration of `Ω` by the sublevel sets `Ω^{a k}`
  set E := PathSp.energyC N p q with hE_def
  set A : ℕ → Set (PathSp N p q) := fun k => sublevel E (a k) with hA_def
  have hA : Monotone A := fun k l h => sublevel_mono E (ha h)
  have hcpt : ∀ K : Set (PathSp N p q), IsCompact K → ∃ k, K ⊆ A k := fun K hK =>
    exists_subset_sublevel_of_isCompact E.continuous (fun s => by
      obtain ⟨k, hk⟩ := exists_nat_gt (s + 1)
      exact ⟨k, by linarith [ha_gt k]⟩) hK
  -- above the energy `((i + 2)πr)²`, geodesics have index `≥ i + 2`
  obtain ⟨k₀, hk₀⟩ := exists_nat_gt (((((i + 1 : ℕ) + 1 : ℕ) : ℝ) * π * r) ^ 2 + 1)
  have hsteps : ∀ j ≤ i + 1, ∀ k, k₀ ≤ k →
      Subsingleton (subsetHomology 𝕜 j (hA (Nat.le_succ k))) := by
    intro j hj k hk
    refine (slab_homology hcl hp hq hnd _ (ha (Nat.le_succ k)) rfl (hreg k) (hreg (k + 1))
      j).2 fun γ hγ hg h1 _ hidx => ?_
    have hE := energy_le_of_geodesicIndex_le hr hn hRic hγ hg (hidx.trans_le hj)
    have h3 : a k₀ ≤ a k := ha hk
    have h4 := ha_gt k₀
    linarith
  have e := spaceHomologyEquivOfSteps (𝕜 := 𝕜) hA hcpt (i := i) (k₀ := k₀)
    (hsteps i (by omega)) (hsteps (i + 1) le_rfl)
  -- `H_i(Ω^{a k₀})` is finite-dimensional (`Ω^{a 0} = ∅`)
  have hA0 : A 0 = ∅ := eq_empty_of_forall_notMem fun γ hγ => by
    have h1 : energy (γ : ℝ → V) 0 1 ≤ -1 := hγ
    linarith [hE0 γ]
  have := (slab_homology (𝕜 := 𝕜) hcl hp hq hnd _ (ha (Nat.zero_le k₀)) rfl (hreg 0) (hreg k₀)
    i).1
  have : FiniteDimensional 𝕜 (subsetHomology 𝕜 i (empty_subset (A k₀))) :=
    finiteDimensional_subsetHomology_congr (hA (Nat.zero_le k₀)) (empty_subset _) hA0 rfl i
  exact e.finiteDimensional

/-- **The homology of `Ω` is finite-dimensional in each degree, under Milnor's hypotheses of
Theorem 19.6**: `N` compact, of dimension `≥ 2`, with positive definite Ricci tensor, and `q` not
conjugate to `p` along any geodesic. -/
theorem finiteDimensional_spaceHomology_omega_of_compact {𝕜 : Type u} [Field 𝕜]
    (hNc : IsCompact N) (hn : 2 ≤ finrank ℝ Z)
    (hpos : ∀ q : N, ∀ U : tangentSubspace hN q, U ≠ 0 → 0 < ricci hN q U U) {p q : V}
    (hp : p ∈ N) (hq : q ∈ N) (hnc : q ∉ conjLocus hN p) (i : ℕ) :
    FiniteDimensional 𝕜 (spaceHomology 𝕜 i (PathSp N p q)) := by
  obtain ⟨r, hr, hRic⟩ := exists_ricciLowerBound hNc hn hpos
  exact finiteDimensional_spaceHomology_omega hNc.isClosed hr hn hRic hp hq hnc i

end Morse
