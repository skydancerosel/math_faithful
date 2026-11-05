import Milnor.Chapter5.LevelArc

/-!
# The sign along an arc of the level set

Along a closed arc of `A = {g ≥ 0} ⊆ S` from a boundary point `p` to a boundary point `q`, the
quantity `sign(f, c) · monoAt(c ∘ γ)` (for any chart function `c` at the current point) is
independent of `c`, locally constant, hence constant.  At the ends, `c = g` is a chart function
and `g ∘ γ` is increasing at `p` (start) and decreasing at `q` (end), so
`sign(f, g)(p) = - sign(f, g)(q)`: **the two ends of an arc have opposite signs**.
-/

open Set Module Filter Topology Function
open scoped ContDiff Manifold

noncomputable section

namespace Milnor

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G} [J.Boundaryless]
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N] {n : ℕ}
  {S : Type*} [TopologicalSpace S] [ChartedSpace ℝ S] [IsManifold 𝓘(ℝ, ℝ) ∞ S] [T2Space S]

variable (hE : finrank ℝ E = n + 1) (hF : finrank ℝ F = n)
  (oM : Orient I M (n + 1)) (oN : Orient J N n)
  {f : M → N} (hf : ContMDiff I J ∞ f) {y : N} (hy : IsRegularValue I J f y)
  {ι : S → M} (hι : ContMDiff 𝓘(ℝ, ℝ) I ∞ ι) (hιinj : Function.Injective ι)
  (hιf : ∀ a, f (ι a) = y)
  (hιker : ∀ a v, (∃ w, mfd 𝓘(ℝ, ℝ) I ι a w = v) ↔ mfd I J f (ι a) v = 0)
  {g : M → ℝ} (hg : ContMDiff I 𝓘(ℝ, ℝ) ∞ g)
  (hreg : ∀ x, f x = y → g x = 0 → ∃ v, mfd I J f x v = 0 ∧ mfd I 𝓘(ℝ, ℝ) g x v ≠ 0)
  {A : Set S} (hA : ∀ a ∈ A, 0 ≤ g (ι a))

/-- The sign of `(f, g)` at a point of `M`. -/
def bdrySign (f : M → N) (g : M → ℝ) (m : M) : ℤ := signAt oM (oN.prodReal hF) (pairMap f g) m

section arc

variable (Ar : OneManifold.Arc A {a : A | g (ι a.1) = 0})

include hE hF hf hy hιf in
/-- A chosen chart function at each point of the arc. -/
def cfAt (t : ℝ) : ChartFun I J f (ι (Ar.invFun t).1) :=
  Classical.choice (exists_chartFun hE hF hf hy _ (hιf _))

/-- The point of `M` at arc parameter `t`. -/
def arcPt (t : ℝ) : M := ι (Ar.invFun t).1

/-- The invariant along the arc: `sign(f, c) · monoAt (c ∘ γ)` for the chosen chart function. -/
def arcEps (t : ℝ) : ℤ :=
  (cfAt hE hF hf hy hιf Ar t).sign hF oM oN *
    monoAt (fun t' => (cfAt hE hF hf hy hιf Ar t).c (ι (Ar.invFun t').1)) Ar.target t

include hι hιinj in
/-- Near `t₀ ∈ target`, for a chart function `c` at the point, `c ∘ γ` is continuous and injective
on a small interval, and `γ` stays in any given open neighbourhood of the point. -/
theorem exists_ball_good {t₀ : ℝ} (ht₀ : t₀ ∈ Ar.target) (cf : ChartFun I J f (ι (Ar.invFun t₀).1))
    {V : Set S} (hV : IsOpen V) (haV : (Ar.invFun t₀).1 ∈ V) (hinj : InjOn (cf.c ∘ ι) V) :
    ∃ δ > 0, (∀ t ∈ Ar.target ∩ Ioo (t₀ - δ) (t₀ + δ), (Ar.invFun t).1 ∈ V ∧ ι (Ar.invFun t).1 ∈ cf.W) ∧
      ContinuousOn (fun t => cf.c (ι (Ar.invFun t).1)) (Ar.target ∩ Ioo (t₀ - δ) (t₀ + δ)) ∧
      InjOn (fun t => cf.c (ι (Ar.invFun t).1)) (Ar.target ∩ Ioo (t₀ - δ) (t₀ + δ)) := by
  have hγ : ContinuousWithinAt (fun t => (Ar.invFun t).1) Ar.target t₀ :=
    continuous_subtype_val.continuousAt.comp_continuousWithinAt (Ar.continuousOn_invFun t₀ ht₀)
  have hU : IsOpen (V ∩ ι ⁻¹' cf.W) := hV.inter (cf.open_W.preimage hι.continuous)
  have hmem : V ∩ ι ⁻¹' cf.W ∈ 𝓝 (Ar.invFun t₀).1 := hU.mem_nhds ⟨haV, cf.mem_W⟩
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhdsWithin_iff.1 (hγ.preimage_mem_nhdsWithin hmem)
  rw [Real.ball_eq_Ioo] at hball
  have hgood : ∀ t ∈ Ar.target ∩ Ioo (t₀ - δ) (t₀ + δ), (Ar.invFun t).1 ∈ V ∧
      ι (Ar.invFun t).1 ∈ cf.W := fun t ht => hball ⟨ht.2, ht.1⟩
  refine ⟨δ, hδ, hgood, ?_, ?_⟩
  · refine (cf.smooth.continuousOn.comp (hι.continuous.comp_continuousOn
      ((continuous_subtype_val.comp_continuousOn (Ar.continuousOn_invFun.mono inter_subset_left)))) ?_)
    intro t ht
    exact (hgood t ht).2
  · intro t₁ ht₁ t₂ ht₂ h
    have h1 := hinj (hgood t₁ ht₁).1 (hgood t₂ ht₂).1 h
    have h2 : Ar.invFun t₁ = Ar.invFun t₂ := Subtype.ext h1
    rw [← Ar.right_inv ht₁.1, ← Ar.right_inv ht₂.1, h2]

include hE hF hf hy hι hιinj hιf hιker in
/-- **Well-definedness**: for any chart function `c` at the point of parameter `t`,
`sign(f, c) · monoAt (c ∘ γ) = arcEps t`. -/
theorem sign_mul_monoAt_eq {t : ℝ} (ht : t ∈ Ar.target) (cf : ChartFun I J f (ι (Ar.invFun t).1)) :
    cf.sign hF oM oN * monoAt (fun t' => cf.c (ι (Ar.invFun t').1)) Ar.target t =
      arcEps hE hF oM oN hf hy hιf Ar t := by
  set cf' := cfAt hE hF hf hy hιf Ar t with hcf'
  have hfa : f (ι (Ar.invFun t).1) = y := hιf _
  have hv0 : mfd 𝓘(ℝ, ℝ) I ι (Ar.invFun t).1 1 ≠ 0 := mfd_ι_one_ne_zero hE hF hy hιf hιker _
  have hvker : mfd I J f (ι (Ar.invFun t).1) (mfd 𝓘(ℝ, ℝ) I ι (Ar.invFun t).1 1) = 0 :=
    mfd_f_mfd_ι hιker _
  obtain ⟨V, D, k, hVo, haV, hinj, hVk, hk⟩ := exists_transition hE hF hf hy hι hιf hιker cf cf'
  obtain ⟨δ, hδ, hgood, hcont, hinj'⟩ := exists_ball_good hι hιinj Ar ht cf hVo haV hinj
  have hs := Ar.ordConnected_target
  have hsn := Ar.nontrivial_target
  set h := fun t' => cf.c (ι (Ar.invFun t').1) with hh
  set h' := fun t' => cf'.c (ι (Ar.invFun t').1) with hh'
  have hor := strictMonoOn_or_strictAntiOn_near hs hsn ht hδ hcont hinj'
  have heq : EqOn h' (k ∘ h) (Ar.target ∩ Ioo (t - δ) (t + δ)) := fun t' ht' => by
    simp only [h', h, Function.comp]
    exact (hVk _ (hgood t' ht').1).2.symm
  have hmaps : MapsTo h (Ar.target ∩ Ioo (t - δ) (t + δ)) D := fun t' ht' =>
    (hVk _ (hgood t' ht').1).1
  have hprod := cf.sign_mul_sign hE hF hf hy oM oN hfa cf' hvker hv0
  have hsm := cf.sign_ne_zero hE hF hf hy oM oN hfa
  have hsm' := cf'.sign_ne_zero hE hF hf hy oM oN hfa
  have hm1 : cf.sign hF oM oN = 1 ∨ cf.sign hF oM oN = -1 := by
    rcases signAt_mem hE (finrank_prod_real hF) oM (oN.prodReal hF) (pairMap f cf.c)
      (ι (Ar.invFun t).1) with h1 | h1 | h1
    · exact Or.inl h1
    · exact Or.inr h1
    · exact absurd h1 hsm
  have hm2 : cf'.sign hF oM oN = 1 ∨ cf'.sign hF oM oN = -1 := by
    rcases signAt_mem hE (finrank_prod_real hF) oM (oN.prodReal hF) (pairMap f cf'.c)
      (ι (Ar.invFun t).1) with h1 | h1 | h1
    · exact Or.inl h1
    · exact Or.inr h1
    · exact absurd h1 hsm'
  unfold arcEps
  rw [← hcf']
  show cf.sign hF oM oN * monoAt h Ar.target t = cf'.sign hF oM oN * monoAt h' Ar.target t
  rcases hk with ⟨hkm, hpos⟩ | ⟨hka, hneg⟩
  · have hor' : StrictMonoOn (k ∘ h) (Ar.target ∩ Ioo (t - δ) (t + δ)) ∨
        StrictAntiOn (k ∘ h) (Ar.target ∩ Ioo (t - δ) (t + δ)) :=
      hor.elim (fun h1 => Or.inl (hkm.comp h1 hmaps))
        (fun h1 => Or.inr (hkm.comp_strictAntiOn h1 hmaps))
    rw [← monoAt_congr hs hsn ht hδ heq.symm hor']
    rw [monoAt_comp_of_strictMonoOn hs hsn ht hδ hor hkm hmaps]
    rw [sgn_pos hpos] at hprod
    have : cf.sign hF oM oN = cf'.sign hF oM oN := by
      rcases hm1 with h1 | h1 <;> rcases hm2 with h2 | h2 <;> rw [h1, h2] at hprod ⊢ <;> omega
    rw [this]
  · have hor' : StrictMonoOn (k ∘ h) (Ar.target ∩ Ioo (t - δ) (t + δ)) ∨
        StrictAntiOn (k ∘ h) (Ar.target ∩ Ioo (t - δ) (t + δ)) :=
      hor.elim (fun h1 => Or.inr (hka.comp_strictMonoOn h1 hmaps))
        (fun h1 => Or.inl (hka.comp h1 hmaps))
    rw [← monoAt_congr hs hsn ht hδ heq.symm hor']
    rw [monoAt_comp_of_strictAntiOn hs hsn ht hδ hor hka hmaps]
    rw [sgn_neg hneg] at hprod
    have : cf'.sign hF oM oN = -cf.sign hF oM oN := by
      rcases hm1 with h1 | h1 <;> rcases hm2 with h2 | h2 <;> rw [h1, h2] at hprod ⊢ <;> omega
    rw [this]; ring

include hE hF hf hy hι hιinj hιf hιker in
/-- **Local constancy** of `arcEps` along the arc. -/
theorem eventually_arcEps_eq {t₀ : ℝ} (ht₀ : t₀ ∈ Ar.target) :
    ∀ᶠ t in 𝓝[Ar.target] t₀, arcEps hE hF oM oN hf hy hιf Ar t =
      arcEps hE hF oM oN hf hy hιf Ar t₀ := by
  set cf := cfAt hE hF hf hy hιf Ar t₀ with hcf
  have hfa : f (ι (Ar.invFun t₀).1) = y := hιf _
  obtain ⟨V, D, k, hVo, haV, hinj, -, -⟩ := exists_transition hE hF hf hy hι hιf hιker cf cf
  obtain ⟨δ, hδ, hgood, hcont, hinj'⟩ := exists_ball_good hι hιinj Ar ht₀ cf hVo haV hinj
  have hs := Ar.ordConnected_target
  have hsn := Ar.nontrivial_target
  have hor := strictMonoOn_or_strictAntiOn_near hs hsn ht₀ hδ hcont hinj'
  -- the chart function `cf` moves to nearby points of the arc
  have hγ : ContinuousWithinAt (fun t => ι (Ar.invFun t).1) Ar.target t₀ :=
    hι.continuous.continuousAt.comp_continuousWithinAt
      (continuous_subtype_val.continuousAt.comp_continuousWithinAt (Ar.continuousOn_invFun t₀ ht₀))
  have hmove := hγ.tendsto.eventually (cf.eventually_move hE hF hf hy oM oN hfa)
  have hsign := hγ.tendsto.eventually (cf.eventually_signAt_eq hE hF hf hy oM oN hfa)
  have hball : ∀ᶠ t in 𝓝[Ar.target] t₀, t ∈ Ar.target ∧ |t - t₀| < δ / 2 := by
    have h1 : ∀ᶠ t in 𝓝[Ar.target] t₀, t ∈ Ar.target := self_mem_nhdsWithin
    have h2 : ∀ᶠ t in 𝓝[Ar.target] t₀, |t - t₀| < δ / 2 := by
      have : ∀ᶠ t in 𝓝 t₀, |t - t₀| < δ / 2 := by
        have := Metric.ball_mem_nhds t₀ (half_pos hδ)
        filter_upwards [this] with t ht
        rwa [Metric.mem_ball, Real.dist_eq] at ht
      exact nhdsWithin_le_nhds this
    exact h1.and h2
  filter_upwards [hmove, hsign, hball] with t hmv hsg hb
  obtain ⟨hW, hregt⟩ := hmv
  let cft : ChartFun I J f (ι (Ar.invFun t).1) :=
    cf.move hE hF _ hW (hf.mdifferentiableAt (by simp)) hregt
  rw [← sign_mul_monoAt_eq hE hF oM oN hf hy hι hιinj hιf hιker Ar hb.1 cft]
  have h1 : cft.sign hF oM oN = cf.sign hF oM oN := hsg
  have h2 : monoAt (fun t' => cft.c (ι (Ar.invFun t').1)) Ar.target t =
      monoAt (fun t' => cf.c (ι (Ar.invFun t').1)) Ar.target t₀ :=
    monoAt_eq_of_near hs hsn ht₀ hδ hor hb.1 hb.2
  rw [h1, h2]
  rfl

include hE hF hf hy hι hιinj hιf hιker hg hreg hA in
/-- **The two ends of an arc have opposite signs.** For a closed arc of `A` from a boundary
point `p` (parameter `0`) to the boundary point `q` at parameter `sSup target`,
`bdrySign p = - bdrySign q`. -/
theorem bdrySign_end_eq_neg {p : A} (hp : g (ι p.1) = 0) (hfrom : OneManifold.IsFrom Ar p)
    (hsup : sSup Ar.target ∈ Ar.target) :
    bdrySign hF oM oN f g (ι p.1) = -bdrySign hF oM oN f g (ι (Ar.invFun (sSup Ar.target)).1) := by
  have hIcc : Ar.target = Icc 0 (sSup Ar.target) := hfrom.target_eq_Icc hsup
  set T := sSup Ar.target with hT
  have h0 : (0 : ℝ) ∈ Ar.target := hfrom.2.2.1
  have hγ0 : Ar.invFun 0 = p := by
    have := Ar.left_inv hfrom.1
    rwa [hfrom.2.1] at this
  have hs := Ar.ordConnected_target
  have hsn := Ar.nontrivial_target
  -- `q` is a boundary point
  have hq : g (ι (Ar.invFun (sSup Ar.target)).1) = 0 := by
    have hqB : Ar.invFun (sSup Ar.target) ∈ {a : A | g (ι a.1) = 0} := by
      rw [Ar.bdry _ (Ar.map_target hsup), Ar.right_inv hsup, hIcc, interior_Icc]
      simp
    exact hqB
  -- constancy of `arcEps`
  have hcont : ContinuousOn (arcEps hE hF oM oN hf hy hιf Ar) Ar.target := by
    intro t ht
    rw [ContinuousWithinAt, nhds_discrete ℤ, Filter.tendsto_pure]
    exact eventually_arcEps_eq hE hF oM oN hf hy hι hιinj hιf hιker Ar ht
  have hpc : IsPreconnected Ar.target := by rw [hIcc]; exact isPreconnected_Icc
  have hconst := hpc.constant hcont h0 hsup
  -- the value at `0`
  let gcf₀ : ChartFun I J f (ι (Ar.invFun 0).1) :=
    gChartFun hE hF hy hg hreg _ (hιf _) (by rw [hγ0]; exact hp)
  have hv0 := sign_mul_monoAt_eq hE hF oM oN hf hy hι hιinj hιf hιker Ar h0 gcf₀
  have hm0 : monoAt (fun t' => gcf₀.c (ι (Ar.invFun t').1)) Ar.target 0 = 1 := by
    obtain ⟨V, D, k, hVo, haV, hinj, -, -⟩ :=
      exists_transition hE hF hf hy hι hιf hιker gcf₀ gcf₀
    obtain ⟨δ, hδ, -, hcont', hinj'⟩ := exists_ball_good hι hιinj Ar h0 gcf₀ hVo haV hinj
    refine monoAt_eq_one_of_left_min hs hsn h0 hδ hcont' hinj' (fun t ht => ?_) (fun t ht => ?_)
    · show g (ι (Ar.invFun 0).1) ≤ g (ι (Ar.invFun t).1)
      rw [hγ0, hp]
      exact hA _ (Ar.invFun t).2
    · rw [hIcc] at ht; exact ht.1
  -- the value at `sSup target`
  let gcfT : ChartFun I J f (ι (Ar.invFun (sSup Ar.target)).1) :=
    gChartFun hE hF hy hg hreg _ (hιf _) hq
  have hvT := sign_mul_monoAt_eq hE hF oM oN hf hy hι hιinj hιf hιker Ar hsup gcfT
  have hmT : monoAt (fun t' => gcfT.c (ι (Ar.invFun t').1)) Ar.target (sSup Ar.target) = -1 := by
    obtain ⟨V, D, k, hVo, haV, hinj, -, -⟩ :=
      exists_transition hE hF hf hy hι hιf hιker gcfT gcfT
    obtain ⟨δ, hδ, -, hcont', hinj'⟩ := exists_ball_good hι hιinj Ar hsup gcfT hVo haV hinj
    refine monoAt_eq_neg_one_of_right_min hs hsn hsup hδ hcont' hinj' (fun t ht => ?_)
      (fun t ht => ?_)
    · show g (ι (Ar.invFun (sSup Ar.target)).1) ≤ g (ι (Ar.invFun t).1)
      rw [hq]
      exact hA _ (Ar.invFun t).2
    · rw [hIcc] at ht; exact ht.2
  rw [hm0, mul_one] at hv0
  rw [hmT] at hvT
  have e0 : gcf₀.sign hF oM oN = bdrySign hF oM oN f g (ι p.1) := by
    show signAt oM (oN.prodReal hF) (pairMap f g) (ι (Ar.invFun 0).1) = _
    rw [hγ0]; rfl
  have eT : gcfT.sign hF oM oN = bdrySign hF oM oN f g (ι (Ar.invFun (sSup Ar.target)).1) := rfl
  rw [e0] at hv0
  rw [eT] at hvT
  rw [hv0, hconst, ← hvT]
  ring

end arc

end Milnor
