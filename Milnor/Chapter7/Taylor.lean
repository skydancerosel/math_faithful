import Milnor.Chapter7.ThmB

/-!
# A uniform first-order estimate on a tube

Let `N` be a compact manifold, `P` a finite-dimensional real normed space and `F` a real normed
space.  If `Φ : N × P → F` is smooth on an open set `W ⊇ N × {0}`, vanishes on `N × {0}` and has
fibre derivative `L` at every point of `N × {0}`, then for every `κ > 0` there is `δ > 0` with
`‖Φ (x, s) - L s‖ ≤ κ * ‖s‖` for all `x` and all `‖s‖ < δ`.

The proof: the fibre derivative `q ↦ fderiv ℝ (Φ (q.1, ·) - L) q.2` is (jointly) continuous on `W`
(`ContMDiffAt.mfderiv`), vanishes on `N × {0}`, so is `< κ` in norm on a tube `N × ball 0 δ`
(tube lemma, `N` compact); the mean value inequality on the convex ball finishes the argument.
-/

open Set Filter Topology Function Module Metric
open scoped ContDiff Manifold

noncomputable section

namespace Milnor

theorem exists_uniform_taylor
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {N : Type*} [TopologicalSpace N] [ChartedSpace H N]
    [IsManifold I ∞ N] [CompactSpace N]
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {Φ : N × P → F} {W : Set (N × P)} (hW : IsOpen W) (hW0 : ∀ x : N, (x, (0 : P)) ∈ W)
    (hΦ : ContMDiffOn (I.prod 𝓘(ℝ, P)) 𝓘(ℝ, F) ∞ Φ W)
    (hΦ0 : ∀ x, Φ (x, 0) = 0) {L : P →L[ℝ] F}
    (hΦd : ∀ x, HasFDerivAt (fun s => Φ (x, s)) L 0) {κ : ℝ} (hκ : 0 < κ) :
    ∃ δ > 0, ∀ x : N, ∀ s : P, ‖s‖ < δ → ‖Φ (x, s) - L s‖ ≤ κ * ‖s‖ := by
  -- the remainder `R q = Φ q - L q.2` is smooth on `W`
  have hR : ContMDiffOn (I.prod 𝓘(ℝ, P)) 𝓘(ℝ, F) ∞ (fun q : N × P => Φ q - L q.2) W :=
    hΦ.sub ((L.contMDiff.comp (contMDiff_snd (I := I) (J := 𝓘(ℝ, P)) (M := N) (N := P)
      (n := ∞))).contMDiffOn)
  -- `R` restricted to a fibre is smooth at every point of `W`
  have hRfib : ∀ q : N × P, q ∈ W →
      ContMDiffAt 𝓘(ℝ, P) 𝓘(ℝ, F) ∞ (fun s' : P => Φ (q.1, s') - L s') q.2 := by
    intro q hq
    have h1 : ContMDiffAt (I.prod 𝓘(ℝ, P)) 𝓘(ℝ, F) ∞ (fun q : N × P => Φ q - L q.2) q :=
      hR.contMDiffAt (hW.mem_nhds hq)
    have h2 : ContMDiffAt 𝓘(ℝ, P) (I.prod 𝓘(ℝ, P)) ∞ (fun s' : P => (q.1, s')) q.2 :=
      contMDiffAt_const.prodMk contMDiffAt_id
    exact h1.comp q.2 h2
  -- joint continuity of the fibre derivative on `W`
  have hD : ∀ q₀ : N × P, q₀ ∈ W →
      ContinuousAt (fun q : N × P => fderiv ℝ (fun s' : P => Φ (q.1, s') - L s') q.2) q₀ := by
    intro q₀ hq₀
    have hf : ContMDiffAt ((I.prod 𝓘(ℝ, P)).prod 𝓘(ℝ, P)) 𝓘(ℝ, F) ∞
        (Function.uncurry (fun (q : N × P) (s' : P) => Φ (q.1, s') - L s')) (q₀, q₀.2) := by
      have h1 : ContMDiffAt (I.prod 𝓘(ℝ, P)) 𝓘(ℝ, F) ∞ (fun q : N × P => Φ q - L q.2)
          (q₀.1, q₀.2) := hR.contMDiffAt (hW.mem_nhds hq₀)
      have h2 : ContMDiffAt ((I.prod 𝓘(ℝ, P)).prod 𝓘(ℝ, P)) (I.prod 𝓘(ℝ, P)) ∞
          (fun p : (N × P) × P => (p.1.1, p.2)) (q₀, q₀.2) :=
        (contMDiffAt_fst.comp _ contMDiffAt_fst).prodMk contMDiffAt_snd
      exact h1.comp (q₀, q₀.2) h2
    have hg : ContMDiffAt (I.prod 𝓘(ℝ, P)) 𝓘(ℝ, P) ∞ (fun q : N × P => q.2) q₀ :=
      contMDiffAt_snd
    have hmn : (∞ : WithTop ℕ∞) + 1 ≤ ∞ := by simp
    have h := ContMDiffAt.mfderiv (I := 𝓘(ℝ, P)) (I' := 𝓘(ℝ, F)) (J := I.prod 𝓘(ℝ, P))
      (f := fun (q : N × P) (s' : P) => Φ (q.1, s') - L s') (g := fun q : N × P => q.2)
      hf hg hmn
    simp only [inTangentCoordinates_model_space, mfderiv_eq_fderiv] at h
    exact h.continuousAt
  -- the fibre derivative vanishes on `N × {0}`
  have hD0 : ∀ x : N, fderiv ℝ (fun s' : P => Φ (x, s') - L s') 0 = 0 := by
    intro x
    have h : HasFDerivAt (fun s' : P => Φ (x, s') - L s') (L - L) 0 :=
      (hΦd x).sub L.hasFDerivAt
    rw [h.fderiv, sub_self]
  -- the set where the fibre derivative is small is open and contains `N × {0}`
  set A : Set (N × P) :=
    {q | q ∈ W ∧ ‖fderiv ℝ (fun s' : P => Φ (q.1, s') - L s') q.2‖ < κ} with hA_def
  have hA_open : IsOpen A := by
    rw [isOpen_iff_mem_nhds]
    intro q hq
    have h1 : W ∈ 𝓝 q := hW.mem_nhds hq.1
    have h2 : {q' : N × P | ‖fderiv ℝ (fun s' : P => Φ (q'.1, s') - L s') q'.2‖ < κ} ∈ 𝓝 q :=
      ((hD q hq.1).norm).eventually_lt continuousAt_const hq.2
    exact Filter.inter_mem h1 h2
  have hsub : (univ : Set N) ×ˢ ({0} : Set P) ⊆ A := by
    rintro ⟨x, s⟩ ⟨-, hs⟩
    rw [mem_singleton_iff] at hs
    subst hs
    refine ⟨hW0 x, ?_⟩
    simp only [hD0, norm_zero]
    exact hκ
  obtain ⟨u, v, -, hv_open, hu, hv0, huv⟩ :=
    generalized_tube_lemma isCompact_univ isCompact_singleton hA_open hsub
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 hv_open 0 (hv0 rfl)
  refine ⟨δ, hδ, fun x s hs => ?_⟩
  -- every point of the tube `N × ball 0 δ` lies in `A`
  have hmemA : ∀ s' : P, s' ∈ ball (0 : P) δ → (x, s') ∈ A := fun s' hs' =>
    huv ⟨hu (mem_univ x), hball hs'⟩
  have hdiff : ∀ s' ∈ ball (0 : P) δ,
      DifferentiableAt ℝ (fun s' : P => Φ (x, s') - L s') s' := fun s' hs' =>
    (contMDiffAt_iff_contDiffAt.1 (hRfib (x, s') (hmemA s' hs').1)).differentiableAt (by simp)
  have hbound : ∀ s' ∈ ball (0 : P) δ,
      ‖fderiv ℝ (fun s' : P => Φ (x, s') - L s') s'‖ ≤ κ := fun s' hs' =>
    (hmemA s' hs').2.le
  have hmvt := (convex_ball (0 : P) δ).norm_image_sub_le_of_norm_fderiv_le hdiff hbound
    (mem_ball_self hδ) (mem_ball_zero_iff.2 hs)
  simpa [hΦ0] using hmvt
