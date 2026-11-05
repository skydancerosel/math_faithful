import Milnor.Chapter6.Tubular4

/-!
# The Poincaré–Hopf theorem (Milnor, p. 35 and p. 38)

For a compact submanifold `N ⊆ ℝᴷ⁺¹` and a smooth tangent vector field `v` on `N` with finitely
many zeros, the sum of the indices of `v` at its zeros does not depend on `v`: it equals the
degree of the Gauss map of the boundary of the tubular neighbourhood `N_{ε/2}`.

The index of `v` at a zero `q` is defined here (following Milnor's proof, p. 38) as the index at
`q` of the extended field `w x = v (r x) + (x - r x)` on the tubular neighbourhood, where `r` is
the nearest-point retraction; `index_eq_of_eventuallyEq` shows it depends only on the germ of
`w` at `q`.
-/

open Set Filter Topology Function Metric Module
open scoped ContDiff Manifold RealInnerProductSpace

noncomputable section

namespace Milnor

namespace Sphere

variable {n : ℕ}

/-- **The index depends only on the germ of the field at the zero.** -/
theorem index_eq_of_eventuallyEq (hn : 0 < n)
    {w w' : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))}
    (hw : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) ∞ w)
    (hw' : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) ∞ w')
    {z : EuclideanSpace ℝ (Fin (n + 1))} (hev : w =ᶠ[𝓝 z] w') {r : ℝ} (hr : 0 < r)
    (h : IsolatedZero w z r) : index w z = index w' z := by
  obtain ⟨δ, hδ, hδev⟩ := Metric.eventually_nhds_iff.1 hev
  set ε := min r (δ / 2) with hε
  have hε0 : 0 < ε := lt_min hr (by linarith)
  have hεr : ε ≤ r := min_le_left _ _
  have hεδ : ε < δ := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  have h' : IsolatedZero w' z ε := by
    refine ⟨?_, fun x hx hxz => ?_⟩
    · rw [← hδev (by rw [dist_self]; exact hδ)]; exact h.1
    · rw [← hδev (lt_of_le_of_lt hx hεδ)]; exact h.2 x (hx.trans hεr) hxz
  rw [index_eq hn hw hr h hε0 hεr, index_eq hn hw' hε0 h' hε0 le_rfl]
  unfold indexAt
  congr 1
  funext u
  have hu : ‖u.1‖ = 1 := mem_iff_norm.1 u.2
  have : w (z + ε • u.1) = w' (z + ε • u.1) := by
    apply hδev
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, hu, mul_one, Real.norm_eq_abs, abs_of_pos hε0]
    exact hεδ
  unfold sphMap
  simp only [this]

end Sphere

namespace Tub

variable {K n m : ℕ} {N : Set (EuclideanSpace ℝ (Fin (K + 1)))}
  (hN : IsSliceSubmanifold 𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1))) (EuclideanSpace ℝ (Fin n))
    (EuclideanSpace ℝ (Fin m)) N) (hNc : IsCompact N) (hne : N.Nonempty)

/-- The chosen globally smooth extension of `w₀ v = v ∘ r + (id - r)`. -/
def wext (v : N → EuclideanSpace ℝ (Fin (K + 1)))
    (hv : letI := hN.chartedSpace;
      ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1))) ∞ v) :
    EuclideanSpace ℝ (Fin (K + 1)) → EuclideanSpace ℝ (Fin (K + 1)) :=
  (exists_extension (isOpen_Nε hN hNc hne) (contMDiffOn_w₀ hN hNc hne hv) (isCompact_X hN hNc hne)
    (X_subset_Nε hN hNc hne)).choose

theorem wext_smooth (v : N → EuclideanSpace ℝ (Fin (K + 1)))
    (hv : letI := hN.chartedSpace;
      ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1))) ∞ v) :
    ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1))) 𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1))) ∞
      (wext hN hNc hne v hv) :=
  (exists_extension (isOpen_Nε hN hNc hne) (contMDiffOn_w₀ hN hNc hne hv) (isCompact_X hN hNc hne)
    (X_subset_Nε hN hNc hne)).choose_spec.1

theorem wext_eq (v : N → EuclideanSpace ℝ (Fin (K + 1)))
    (hv : letI := hN.chartedSpace;
      ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1))) ∞ v) :
    ∀ᶠ x in 𝓝ˢ (X hN hNc hne), wext hN hNc hne v hv x = w₀ hN hNc hne v x :=
  (exists_extension (isOpen_Nε hN hNc hne) (contMDiffOn_w₀ hN hNc hne hv) (isCompact_X hN hNc hne)
    (X_subset_Nε hN hNc hne)).choose_spec.2

/-- **The index of a tangent vector field on `N ⊆ ℝᴷ⁺¹` at a point `q`** (Milnor, p. 38): the
index at `q` of the extension `x ↦ v (r x) + (x - r x)` to the tubular neighbourhood. -/
def indexN (v : N → EuclideanSpace ℝ (Fin (K + 1)))
    (hv : letI := hN.chartedSpace;
      ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1))) ∞ v)
    (q : N) : ℤ :=
  Sphere.index (wext hN hNc hne v hv) q.1

/-- The index is the index of any smooth field agreeing with `v ∘ r + (id - r)` near `q`. -/
theorem indexN_eq (hK : 0 < K) (v : N → EuclideanSpace ℝ (Fin (K + 1)))
    (hv : letI := hN.chartedSpace;
      ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1))) ∞ v)
    (q : N) {w' : EuclideanSpace ℝ (Fin (K + 1)) → EuclideanSpace ℝ (Fin (K + 1))}
    (hw' : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1))) 𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1))) ∞ w')
    (hev : w' =ᶠ[𝓝 q.1] w₀ hN hNc hne v) {r : ℝ} (hr : 0 < r)
    (hiso : Sphere.IsolatedZero (wext hN hNc hne v hv) q.1 r) :
    indexN hN hNc hne v hv q = Sphere.index w' q.1 := by
  have h1 : wext hN hNc hne v hv =ᶠ[𝓝 q.1] w' := by
    have h2 : wext hN hNc hne v hv =ᶠ[𝓝 q.1] w₀ hN hNc hne v :=
      eventually_nhdsSet_iff_forall.1 (wext_eq hN hNc hne v hv) q.1 (N_subset_X hN hNc hne q.2)
    exact h2.trans hev.symm
  exact Sphere.index_eq_of_eventuallyEq hK (wext_smooth hN hNc hne v hv) hw' h1 hr hiso

/-- **The Poincaré–Hopf theorem** (Milnor, p. 35).  For a compact submanifold `N ⊆ ℝᴷ⁺¹`
(`K ≥ 1`) there is an integer `χ(N)` such that, for every smooth tangent vector field `v` on `N`
whose zeros are finitely many points `z₁, …, z_j`, the sum of the indices of `v` at the `zᵢ`
equals `χ(N)`.  (`χ(N)` is the degree of the Gauss map of the boundary of the tubular
neighbourhood `N_{ε/2}`.) -/
theorem poincare_hopf (hK : 0 < K) :
    ∃ χN : ℤ, ∀ (v : N → EuclideanSpace ℝ (Fin (K + 1)))
      (hv : letI := hN.chartedSpace;
        ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1))) ∞ v)
      (_hvT : letI := hN.chartedSpace; ∀ q : N, v q ∈ LinearMap.range
        ((mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1)))
          (Subtype.val : N → EuclideanSpace ℝ (Fin (K + 1))) q :
            EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin (K + 1))) :
            EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin (K + 1))))
      {j : ℕ} (z : Fin j → N) (_hz : Injective z) (_hzero : ∀ q, v q = 0 ↔ ∃ i, q = z i),
      ∑ i, indexN hN hNc hne v hv (z i) = χN := by
  classical
  letI := hN.chartedSpace
  haveI := hN.isManifold
  obtain ⟨G, hG, hGX, hGG⟩ := exists_G hN hNc hne
  have hG0 := isRegularValue_G hN hNc hne hG hGX hGG
  have hXc : IsCompact {x | 0 ≤ G x} := by rw [hGX]; exact isCompact_X hN hNc hne
  letI := (isSliceSubmanifold_preimage (Z := EuclideanSpace ℝ (Fin K))
    (finrank_Z_add Sphere.hE Sphere.hZ) hG.contMDiff hG0).chartedSpace
  refine ⟨deg ((levelOrientM Sphere.hE Sphere.hZ
      (Orient.const (finBasisOfFinrankEq ℝ _ Sphere.hE).orientation) hG.contMDiff hG0).neg Sphere.hZ)
      (Sphere.sphOr K) (fun q : G ⁻¹' {0} => Sphere.nv0 (-gradient G q.1)), ?_⟩
  intro v hv hvT j z hz hzero
  set w := wext hN hNc hne v hv with hwdef
  have hw := wext_smooth hN hNc hne v hv
  have hwX' : ∀ x ∈ X hN hNc hne, w x = w₀ hN hNc hne v x := fun x hx =>
    (wext_eq hN hNc hne v hv).self_of_nhdsSet x hx
  -- a positive lower bound for the distances between distinct zeros
  obtain ⟨d, hd, hdd⟩ : ∃ d > 0, ∀ i i', i ≠ i' → d ≤ dist (z i).1 (z i').1 := by
    by_cases hj : ∃ p : Fin j × Fin j, p.1 ≠ p.2
    · set S := (Finset.univ.filter (fun p : Fin j × Fin j => p.1 ≠ p.2)).image
        (fun p => dist (z p.1).1 (z p.2).1) with hS
      have hSne : S.Nonempty := by
        obtain ⟨p, hp⟩ := hj
        exact ⟨_, Finset.mem_image.2 ⟨p, Finset.mem_filter.2 ⟨Finset.mem_univ _, hp⟩, rfl⟩⟩
      refine ⟨S.min' hSne, ?_, fun i i' hii => ?_⟩
      · obtain ⟨p, hp, hpe⟩ := Finset.mem_image.1 (S.min'_mem hSne)
        rw [← hpe]
        have : p.1 ≠ p.2 := (Finset.mem_filter.1 hp).2
        exact dist_pos.2 fun h => this (hz (Subtype.ext h))
      · exact S.min'_le _ (Finset.mem_image.2 ⟨(i, i'), Finset.mem_filter.2 ⟨Finset.mem_univ _, hii⟩, rfl⟩)
    · push_neg at hj
      exact ⟨1, one_pos, fun i i' hii => absurd (hj (i, i')) hii⟩
  set ε' := min (tubε hN hNc hne / 4) (d / 4) with hε'
  have htε := tubε_pos hN hNc hne
  have hε'0 : 0 < ε' := lt_min (by linarith) (by linarith)
  have hε'ε : ε' < tubε hN hNc hne / 2 := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hε'd : 2 * ε' < d := by
    have := min_le_right (tubε hN hNc hne / 4) (d / 4); linarith
  -- the hypotheses of Hopf's lemma
  have hzin : ∀ i x, dist x (z i).1 ≤ ε' → 0 < G x := by
    intro i x hx
    have h1 : infDist x N ≤ ε' := (infDist_le_dist_of_mem (z i).2).trans hx
    have hxX : x ∈ X hN hNc hne := by
      show infDist x N ≤ _
      exact h1.trans hε'ε.le
    rw [hGG.self_of_nhdsSet x hxX, G₀_eq]
    have h0 : 0 ≤ infDist x N := infDist_nonneg
    nlinarith
  have hdisj : ∀ i i', i ≠ i' → 2 * ε' < dist (z i).1 (z i').1 := fun i i' h =>
    lt_of_lt_of_le hε'd (hdd i i' h)
  have hzeroX : ∀ x, 0 ≤ G x → w x = 0 → ∃ i, x = (z i).1 := by
    intro x hGx hwx
    have hxX : x ∈ X hN hNc hne := by rw [← hGX]; exact hGx
    rw [hwX' x hxX] at hwx
    obtain ⟨hxN, hv0⟩ := w₀_eq_zero hN hNc hne hvT (X_subset_Nε hN hNc hne hxX) hwx
    obtain ⟨i, hi⟩ := (hzero _).1 hv0
    exact ⟨i, congrArg Subtype.val hi⟩
  have hout : ∀ x, G x = 0 → fderiv ℝ G x (w x) < 0 := by
    intro x hGx
    have hxX : x ∈ X hN hNc hne := by rw [← hGX]; exact le_of_eq hGx.symm
    have hxN := X_subset_Nε hN hNc hne hxX
    have hev : G =ᶠ[𝓝 x] G₀ hN hNc hne := eventually_nhdsSet_iff_forall.1 hGG x hxX
    rw [hev.fderiv_eq, hwX' x hxX, fderiv_G₀_w₀ hN hNc hne hvT hxN]
    have hne0 : x - (tubr hN hNc hne x).1 ≠ 0 := by
      intro h
      have := hev.self_of_nhds
      rw [hGx] at this
      unfold G₀ at this
      rw [h, norm_zero] at this
      nlinarith
    have := norm_pos_iff.2 hne0
    nlinarith
  have hHopf := Sphere.hopf_lemma hK hw hG hG0 hXc hε'0 hzin hdisj hzeroX hout
  rw [← hHopf]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hiso : Sphere.IsolatedZero w (z i).1 ε' := by
    refine ⟨?_, fun x hx hxz hwx => ?_⟩
    · rw [hwX' _ (N_subset_X hN hNc hne (z i).2), w₀_of_mem hN hNc hne (z i).2]
      exact (hzero (z i)).2 ⟨i, rfl⟩
    · have hGx := hzin i x hx
      obtain ⟨i', hi'⟩ := hzeroX x hGx.le hwx
      by_cases hii : i' = i
      · subst hii; exact hxz hi'
      · have := hdisj i' i hii
        rw [← hi'] at this
        linarith
  exact Sphere.index_eq hK hw hε'0 hiso hε'0 le_rfl

end Tub

end Milnor
