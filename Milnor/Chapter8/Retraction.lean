import Milnor.Chapter8.Smoothing
import Milnor.Chapter6.Tubular4

/-!
# Problem 12: the nearest-point retraction, and smoothing maps into a compact submanifold

Let `M ⊆ ℝᴷ⁺¹` be a compact nonempty submanifold of dimension `m`, with tubular radius `ε` and
nearest-point retraction `r : N_ε → M`, `r(x + v) = x` (Chapter 6, `Milnor.Tub`).

* `r(y)` is strictly closer to `y` than any other point of `M` (`tubr_dist_lt`).
* `r` is smooth on `N_ε` as a map into the manifold `M` (`contMDiffOn_tubr`).
* **Problem 12**, the analogue of Problem 4 with `Sᵖ` replaced by `M`.  Let `X ⊆ ℝᴸ⁺¹` be a
  compact manifold.  Every continuous map `X → M` is uniformly approximated by smooth maps:
  approximate it within `δ` by a smooth map `Q` into `ℝᴷ⁺¹` (Stone–Weierstrass) and retract,
  `‖r(Q x) - G x‖ ≤ ‖r(Q x) - Q x‖ + ‖Q x - G x‖ ≤ 2 ‖Q x - G x‖`.  Smooth maps `f, g : X → M`
  with `‖f x - g x‖ < ε` are smoothly homotopic by the retracted straight-line homotopy
  `r((1 - s) f + s g)`.  Hence two smooth maps which are continuously homotopic are smoothly
  homotopic: approximate the homotopy on the compact set `X × [0,1]` within `ε/4` by a smooth `Q`
  and retract `(x, t) ↦ r(Q(x, σ t))`; its ends are within `ε/2` of `f` and `g`.
-/

open Set Filter Topology Function Metric
open scoped ContDiff Manifold

noncomputable section

namespace Milnor

namespace Problems

variable {K m w : ℕ} {M : Set (EuclideanSpace ℝ (Fin (K + 1)))}
  (hM : IsSliceSubmanifold 𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1))) (EuclideanSpace ℝ (Fin m))
    (EuclideanSpace ℝ (Fin w)) M) (hMc : IsCompact M) (hne : M.Nonempty)

/-! ### The nearest-point retraction -/

/-- `r(y)` is strictly closer to `y` than any other point of `M` (within the tubular
neighbourhood). -/
theorem tubr_dist_lt {y : EuclideanSpace ℝ (Fin (K + 1))}
    (hy : Metric.infDist y M < Tub.tubε hM hMc hne) (x' : M)
    (hx' : x' ≠ Tub.tubr hM hMc hne y) : ‖y - (Tub.tubr hM hMc hne y).1‖ < ‖y - x'.1‖ := by
  have h1 : ‖y - (Tub.tubr hM hMc hne y).1‖ = infDist y M := by
    rw [← dist_eq_norm]; exact (Tub.tubr_spec hM hMc hne).1 y
  have h2 : infDist y M ≤ ‖y - x'.1‖ := by
    rw [← dist_eq_norm]; exact infDist_le_dist_of_mem x'.2
  rw [h1]
  refine lt_of_le_of_ne h2 fun heq => hx' ?_
  refine (Tub.tubr_spec hM hMc hne).2.1 y hy x' fun q hq => ?_
  rw [dist_eq_norm, ← heq]
  exact infDist_le_dist_of_mem hq

/-- The retraction is smooth, as a map into `M`, at each point of the tubular neighbourhood. -/
theorem contMDiffAt_tubr {y : EuclideanSpace ℝ (Fin (K + 1))} (hy : y ∈ Tub.Nε hM hMc hne) :
    letI := hM.chartedSpace; haveI := hM.isManifold;
    ContMDiffAt 𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1))) 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) ∞
      (Tub.tubr hM hMc hne) y := by
  let _ := hM.chartedSpace
  have _ := hM.isManifold
  let U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin (K + 1))) :=
    ⟨Tub.Nε hM hMc hne, Tub.isOpen_Nε hM hMc hne⟩
  -- `x ↦ (r x).1` is smooth on `U`, as a map into `ℝᴷ⁺¹` ...
  have hrU : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1)))
      𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1))) ∞ (fun x : U => (Tub.tubr hM hMc hne x.1).1) := by
    intro x
    have := (Tub.tubr_spec hM hMc hne).2.2.2.1 x.1 x.2
    rw [← contMDiffAt_iff_contDiffAt] at this
    exact (contMDiffAt_subtype_iff (U := U) (f := fun y => (Tub.tubr hM hMc hne y).1)
      (x := x)).2 this
  -- ... hence smooth on `U` as a map into `M`
  have hrM : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1))) 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) ∞
      (fun x : U => Tub.tubr hM hMc hne x.1) := by
    have := hM.contMDiff_codRestrict hrU fun x => (Tub.tubr hM hMc hne x.1).2
    convert this using 1
  exact (contMDiffAt_subtype_iff (U := U) (f := Tub.tubr hM hMc hne) (x := ⟨y, hy⟩)).1
    (hrM ⟨y, hy⟩)

/-- The retraction is smooth on the tubular neighbourhood, as a map into `M`. -/
theorem contMDiffOn_tubr : letI := hM.chartedSpace; haveI := hM.isManifold;
    ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1))) 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) ∞
      (Tub.tubr hM hMc hne) (Tub.Nε hM hMc hne) := by
  let _ := hM.chartedSpace
  have _ := hM.isManifold
  exact fun y hy => (contMDiffAt_tubr hM hMc hne hy).contMDiffWithinAt

/-- The retraction moves a point `y` at most as far as any point of `M`:
`‖y - r y‖ ≤ ‖y - z‖` for `z ∈ M`. -/
theorem norm_sub_tubr_le (y : EuclideanSpace ℝ (Fin (K + 1))) (z : M) :
    ‖y - (Tub.tubr hM hMc hne y).1‖ ≤ ‖y - z.1‖ := by
  rw [← dist_eq_norm, ← dist_eq_norm, (Tub.tubr_spec hM hMc hne).1]
  exact infDist_le_dist_of_mem z.2

/-- A point within `ε` of a point of `M` lies in the tubular neighbourhood. -/
theorem mem_Nε_of_norm_sub_lt {y : EuclideanSpace ℝ (Fin (K + 1))} (z : M)
    (h : ‖y - z.1‖ < Tub.tubε hM hMc hne) : y ∈ Tub.Nε hM hMc hne := by
  show infDist y M < Tub.tubε hM hMc hne
  calc infDist y M ≤ dist y z.1 := infDist_le_dist_of_mem z.2
    _ = ‖y - z.1‖ := dist_eq_norm _ _
    _ < _ := h

/-! ### Problem 12 -/

variable {L l u : ℕ} {X : Set (EuclideanSpace ℝ (Fin (L + 1)))}
  (hX : IsSliceSubmanifold 𝓘(ℝ, EuclideanSpace ℝ (Fin (L + 1))) (EuclideanSpace ℝ (Fin l))
    (EuclideanSpace ℝ (Fin u)) X) (hXc : IsCompact X)

include hMc hne hXc in
/-- **Problem 12, approximation.** Every continuous map from a compact manifold `X` to a compact
submanifold `M ⊆ ℝᴷ⁺¹` can be uniformly approximated by a smooth map. -/
theorem exists_smooth_approx_mfld (G : C(X, M)) {ε : ℝ} (hε : 0 < ε) :
    letI := hX.chartedSpace; haveI := hX.isManifold; letI := hM.chartedSpace;
    haveI := hM.isManifold;
    ∃ f : X → M, ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin l)) 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) ∞ f ∧
      ∀ x, ‖(f x).1 - (G x).1‖ < ε := by
  let _ := hX.chartedSpace
  have _ := hX.isManifold
  let _ := hM.chartedSpace
  have _ := hM.isManifold
  classical
  -- `G`, extended by `0`, is continuous on the compact set `X`
  obtain ⟨G', hG'⟩ : ∃ G' : EuclideanSpace ℝ (Fin (L + 1)) → EuclideanSpace ℝ (Fin (K + 1)),
      ∀ x, G' x = if hx : x ∈ X then (G ⟨x, hx⟩).1 else 0 := ⟨_, fun _ => rfl⟩
  have hG'X : ∀ x : X, G' x.1 = (G x).1 := fun x => by rw [hG', dif_pos x.2]
  have hG'c : ContinuousOn G' X := by
    rw [continuousOn_iff_continuous_domRestrict]
    have : X.domRestrict G' = fun x : X => (G x).1 := funext hG'X
    rw [this]
    exact continuous_subtype_val.comp G.continuous
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = min (ε / 2) (Tub.tubε hM hMc hne) := ⟨_, rfl⟩
  have hδpos : 0 < δ := by rw [hδ]; exact lt_min (half_pos hε) (Tub.tubε_pos hM hMc hne)
  have hδε : 2 * δ ≤ ε := by rw [hδ]; linarith [min_le_left (ε / 2) (Tub.tubε hM hMc hne)]
  have hδr : δ ≤ Tub.tubε hM hMc hne := by rw [hδ]; exact min_le_right _ _
  obtain ⟨Q, hQ, hQG⟩ := exists_contDiff_approx_of_isCompact hXc hG'c hδpos
  have hQx : ∀ x : X, ‖Q x.1 - (G x).1‖ < δ := fun x => by rw [← hG'X x]; exact hQG x.1 x.2
  have hQN : ∀ x : X, Q x.1 ∈ Tub.Nε hM hMc hne := fun x =>
    mem_Nε_of_norm_sub_lt hM hMc hne (G x) (lt_of_lt_of_le (hQx x) hδr)
  have hQv : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin l)) 𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1))) ∞
      (fun x : X => Q x.1) := hQ.contMDiff.comp hX.contMDiff_val
  -- the smooth approximation `x ↦ r (Q x)`
  refine ⟨fun x => Tub.tubr hM hMc hne (Q x.1),
    fun x => (contMDiffAt_tubr hM hMc hne (hQN x)).comp x (hQv x), fun x => ?_⟩
  have h1 := norm_sub_tubr_le hM hMc hne (Q x.1) (G x)
  calc ‖(Tub.tubr hM hMc hne (Q x.1)).1 - (G x).1‖
      ≤ ‖(Tub.tubr hM hMc hne (Q x.1)).1 - Q x.1‖ + ‖Q x.1 - (G x).1‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ 2 * ‖Q x.1 - (G x).1‖ := by rw [norm_sub_rev]; linarith
    _ < 2 * δ := by linarith [hQx x]
    _ ≤ ε := hδε

/-- Nearby smooth maps into `M` are smoothly homotopic (the homotopy `r((1-s) f + s g)`). -/
theorem smoothHomotopic_of_dist_lt_mfld {f g : X → M}
    (hf : letI := hX.chartedSpace; haveI := hX.isManifold; letI := hM.chartedSpace;
      haveI := hM.isManifold;
      ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin l)) 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) ∞ f)
    (hg : letI := hX.chartedSpace; haveI := hX.isManifold; letI := hM.chartedSpace;
      haveI := hM.isManifold;
      ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin l)) 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) ∞ g)
    (h : ∀ x, ‖(f x).1 - (g x).1‖ < Tub.tubε hM hMc hne) :
    letI := hX.chartedSpace; letI := hM.chartedSpace;
    SmoothHomotopic 𝓘(ℝ, EuclideanSpace ℝ (Fin l)) 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) f g := by
  let _ := hX.chartedSpace
  have _ := hX.isManifold
  let _ := hM.chartedSpace
  have _ := hM.isManifold
  -- the straight-line homotopy in `ℝᴷ⁺¹`
  obtain ⟨c, hc⟩ : ∃ c : X × ℝ → EuclideanSpace ℝ (Fin (K + 1)), ∀ q,
      c q = (1 - Real.smoothTransition q.2) • (f q.1).1 + Real.smoothTransition q.2 • (g q.1).1 :=
    ⟨_, fun _ => rfl⟩
  have hcN : ∀ q, c q ∈ Tub.Nε hM hMc hne := by
    intro q
    refine mem_Nε_of_norm_sub_lt hM hMc hne (f q.1) ?_
    have hs0 := Real.smoothTransition.nonneg q.2
    have hs1 := Real.smoothTransition.le_one q.2
    have h1 : c q - (f q.1).1 = Real.smoothTransition q.2 • ((g q.1).1 - (f q.1).1) := by
      rw [hc]; module
    have h2 := norm_nonneg ((g q.1).1 - (f q.1).1)
    rw [h1, norm_smul, Real.norm_eq_abs, abs_of_nonneg hs0]
    calc Real.smoothTransition q.2 * ‖(g q.1).1 - (f q.1).1‖ ≤ ‖(g q.1).1 - (f q.1).1‖ := by
          nlinarith
      _ < Tub.tubε hM hMc hne := by rw [norm_sub_rev]; exact h q.1
  have hcs : ContMDiff ((𝓘(ℝ, EuclideanSpace ℝ (Fin l))).prod 𝓘(ℝ, ℝ))
      𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1))) ∞ c := by
    have hfun : c = fun q => (1 - Real.smoothTransition q.2) • (f q.1).1 +
        Real.smoothTransition q.2 • (g q.1).1 := funext hc
    rw [hfun]
    have hfv : ContMDiff ((𝓘(ℝ, EuclideanSpace ℝ (Fin l))).prod 𝓘(ℝ, ℝ))
        𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1))) ∞ (fun q : X × ℝ => (f q.1).1) :=
      hM.contMDiff_val.comp (hf.comp contMDiff_fst)
    have hgv : ContMDiff ((𝓘(ℝ, EuclideanSpace ℝ (Fin l))).prod 𝓘(ℝ, ℝ))
        𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1))) ∞ (fun q : X × ℝ => (g q.1).1) :=
      hM.contMDiff_val.comp (hg.comp contMDiff_fst)
    have hσq : ContMDiff ((𝓘(ℝ, EuclideanSpace ℝ (Fin l))).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
        (fun q : X × ℝ => Real.smoothTransition q.2) :=
      (Real.smoothTransition.contDiff (n := ⊤)).contMDiff.comp contMDiff_snd
    exact ((contMDiff_const.sub hσq).smul hfv).add (hσq.smul hgv)
  -- retract it onto `M`
  refine ⟨fun q => Tub.tubr hM hMc hne (c q),
    fun q => (contMDiffAt_tubr hM hMc hne (hcN q)).comp q (hcs q), fun x => ?_, fun x => ?_⟩
  · apply Subtype.ext
    change (Tub.tubr hM hMc hne (c (x, 0))).1 = (f x).1
    rw [hc]
    simp only [Real.smoothTransition.zero, sub_zero, one_smul, zero_smul, add_zero]
    exact (Tub.tubr_spec hM hMc hne).2.2.1 _ (f x).2
  · apply Subtype.ext
    change (Tub.tubr hM hMc hne (c (x, 1))).1 = (g x).1
    rw [hc]
    simp only [Real.smoothTransition.one, sub_self, zero_smul, one_smul, zero_add]
    exact (Tub.tubr_spec hM hMc hne).2.2.1 _ (g x).2

include hMc hne hXc in
/-- **Problem 12, homotopy.** Two smooth maps from a compact manifold `X` to a compact
submanifold `M ⊆ ℝᴷ⁺¹` which are continuously homotopic are smoothly homotopic. -/
theorem smoothHomotopic_of_homotopic_mfld {f g : X → M}
    (hf : letI := hX.chartedSpace; haveI := hX.isManifold; letI := hM.chartedSpace;
      haveI := hM.isManifold;
      ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin l)) 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) ∞ f)
    (hg : letI := hX.chartedSpace; haveI := hX.isManifold; letI := hM.chartedSpace;
      haveI := hM.isManifold;
      ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin l)) 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) ∞ g)
    (h : letI := hX.chartedSpace; letI := hM.chartedSpace;
      (⟨f, hf.continuous⟩ : C(X, M)).Homotopic ⟨g, hg.continuous⟩) :
    letI := hX.chartedSpace; letI := hM.chartedSpace;
    SmoothHomotopic 𝓘(ℝ, EuclideanSpace ℝ (Fin l)) 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) f g := by
  let _ := hX.chartedSpace
  have _ := hX.isManifold
  let _ := hM.chartedSpace
  have _ := hM.isManifold
  classical
  obtain ⟨H⟩ := h
  -- the homotopy as a function on the compact set `X × [0,1] ⊆ ℝᴸ⁺¹ × ℝ`
  obtain ⟨G', hG'⟩ : ∃ G' : EuclideanSpace ℝ (Fin (L + 1)) × ℝ → EuclideanSpace ℝ (Fin (K + 1)),
      ∀ q, G' q = if hq : q.1 ∈ X ∧ q.2 ∈ Icc (0 : ℝ) 1 then (H (⟨q.2, hq.2⟩, ⟨q.1, hq.1⟩)).1
        else 0 := ⟨_, fun _ => rfl⟩
  have hG'S : ∀ (x : X) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1), G' (x.1, t) = (H (⟨t, ht⟩, x)).1 :=
    fun x t ht => by rw [hG', dif_pos ⟨x.2, ht⟩]
  have hSc : IsCompact (X ×ˢ Icc (0 : ℝ) 1) := hXc.prod isCompact_Icc
  have hG'c : ContinuousOn G' (X ×ˢ Icc (0 : ℝ) 1) := by
    rw [continuousOn_iff_continuous_domRestrict]
    have : (X ×ˢ Icc (0 : ℝ) 1).domRestrict G' = fun q : ↥(X ×ˢ Icc (0 : ℝ) 1) =>
        (H (⟨q.1.2, (Set.mem_prod.1 q.2).2⟩, ⟨q.1.1, (Set.mem_prod.1 q.2).1⟩)).1 := by
      funext q
      exact hG'S ⟨q.1.1, (Set.mem_prod.1 q.2).1⟩ q.1.2 (Set.mem_prod.1 q.2).2
    rw [this]
    refine continuous_subtype_val.comp (H.continuous.comp ?_)
    exact ((continuous_snd.comp continuous_subtype_val).subtype_mk _).prodMk
      ((continuous_fst.comp continuous_subtype_val).subtype_mk _)
  have hε := Tub.tubε_pos hM hMc hne
  obtain ⟨Q, hQ, hQG⟩ :=
    exists_contDiff_approx_of_isCompact hSc hG'c (by linarith : (0 : ℝ) < Tub.tubε hM hMc hne / 4)
  -- the smooth homotopy `(x, t) ↦ r (Q (x, σ t))`
  have hσ01 : ∀ t : ℝ, Real.smoothTransition t ∈ Icc (0 : ℝ) 1 := fun t =>
    ⟨Real.smoothTransition.nonneg t, Real.smoothTransition.le_one t⟩
  have hQM : ∀ (x : X) (t : ℝ),
      ‖Q (x.1, Real.smoothTransition t) - (H (⟨_, hσ01 t⟩, x)).1‖ < Tub.tubε hM hMc hne / 4 := by
    intro x t
    rw [← hG'S x _ (hσ01 t)]
    exact hQG _ (Set.mem_prod.2 ⟨x.2, hσ01 t⟩)
  have hQN : ∀ q : X × ℝ, Q (q.1.1, Real.smoothTransition q.2) ∈ Tub.Nε hM hMc hne := fun q =>
    mem_Nε_of_norm_sub_lt hM hMc hne (H (⟨_, hσ01 q.2⟩, q.1)) (by linarith [hQM q.1 q.2])
  have hw : ContMDiff ((𝓘(ℝ, EuclideanSpace ℝ (Fin l))).prod 𝓘(ℝ, ℝ))
      𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1))) ∞
      (fun q : X × ℝ => Q (q.1.1, Real.smoothTransition q.2)) := by
    have h1 : ContMDiff ((𝓘(ℝ, EuclideanSpace ℝ (Fin l))).prod 𝓘(ℝ, ℝ))
        𝓘(ℝ, EuclideanSpace ℝ (Fin (L + 1))) ∞ (fun q : X × ℝ => q.1.1) :=
      hX.contMDiff_val.comp contMDiff_fst
    have h2 : ContMDiff ((𝓘(ℝ, EuclideanSpace ℝ (Fin l))).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
        (fun q : X × ℝ => Real.smoothTransition q.2) :=
      (Real.smoothTransition.contDiff (n := ⊤)).contMDiff.comp contMDiff_snd
    exact hQ.contMDiff.comp (h1.prodMk_space h2)
  obtain ⟨Ht, hHt⟩ : ∃ Ht : X × ℝ → M,
      ∀ q, Ht q = Tub.tubr hM hMc hne (Q (q.1.1, Real.smoothTransition q.2)) :=
    ⟨_, fun _ => rfl⟩
  have hHts : ContMDiff ((𝓘(ℝ, EuclideanSpace ℝ (Fin l))).prod 𝓘(ℝ, ℝ))
      𝓘(ℝ, EuclideanSpace ℝ (Fin m)) ∞ Ht := by
    have hfun : Ht = fun q => Tub.tubr hM hMc hne (Q (q.1.1, Real.smoothTransition q.2)) :=
      funext hHt
    rw [hfun]
    exact fun q => (contMDiffAt_tubr hM hMc hne (hQN q)).comp q (hw q)
  -- its ends are near `f` and `g`
  have hend : ∀ (t : ℝ) (k : X → M), (∀ x, H (⟨_, hσ01 t⟩, x) = k x) →
      ∀ x, ‖(k x).1 - (Ht (x, t)).1‖ < Tub.tubε hM hMc hne := by
    intro t k hk x
    have h1 := hQM x t
    rw [hk x] at h1
    have h2 := norm_sub_tubr_le hM hMc hne (Q (x.1, Real.smoothTransition t)) (k x)
    rw [hHt]
    calc ‖(k x).1 - (Tub.tubr hM hMc hne (Q (x.1, Real.smoothTransition t))).1‖
        ≤ ‖(k x).1 - Q (x.1, Real.smoothTransition t)‖ + ‖Q (x.1, Real.smoothTransition t) -
            (Tub.tubr hM hMc hne (Q (x.1, Real.smoothTransition t))).1‖ :=
          norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ < Tub.tubε hM hMc hne := by rw [norm_sub_rev]; linarith
  have hH0 : ∀ x, H (⟨_, hσ01 0⟩, x) = f x := fun x => by
    have : (⟨_, hσ01 0⟩ : unitInterval) = 0 := Subtype.ext Real.smoothTransition.zero
    rw [this, H.apply_zero]
    rfl
  have hH1 : ∀ x, H (⟨_, hσ01 1⟩, x) = g x := fun x => by
    have : (⟨_, hσ01 1⟩ : unitInterval) = 1 := Subtype.ext Real.smoothTransition.one
    rw [this, H.apply_one]
    rfl
  have hk : ∀ t : ℝ, ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin l)) 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) ∞
      (fun x : X => Ht (x, t)) := fun t => hHts.comp (contMDiff_id.prodMk contMDiff_const)
  have hA : SmoothHomotopic 𝓘(ℝ, EuclideanSpace ℝ (Fin l)) 𝓘(ℝ, EuclideanSpace ℝ (Fin m))
      f (fun x => Ht (x, 0)) :=
    smoothHomotopic_of_dist_lt_mfld hM hMc hne hX hf (hk 0) (hend 0 f hH0)
  have hB : SmoothHomotopic 𝓘(ℝ, EuclideanSpace ℝ (Fin l)) 𝓘(ℝ, EuclideanSpace ℝ (Fin m))
      (fun x => Ht (x, 0)) (fun x => Ht (x, 1)) :=
    ⟨Ht, hHts, fun _ => rfl, fun _ => rfl⟩
  have hC : SmoothHomotopic 𝓘(ℝ, EuclideanSpace ℝ (Fin l)) 𝓘(ℝ, EuclideanSpace ℝ (Fin m))
      g (fun x => Ht (x, 1)) :=
    smoothHomotopic_of_dist_lt_mfld hM hMc hne hX hg (hk 1) (hend 1 g hH1)
  exact (hA.trans hB).trans hC.symm

end Problems

end Milnor
