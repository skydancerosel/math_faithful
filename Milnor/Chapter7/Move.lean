import Milnor.Chapter7.MoveH
import Milnor.Chapter7.ChartSign
import Milnor.Chapter7.Cobordism

/-!
# Moving a framed point inside a chart ball (Milnor §7, p. 51, "moving points")

If `F` is a framed `0`-manifold, `x₀ ∈ F.N` lies in a chart ball `U` whose closure contains no
other point of `F.N`, `x₁ ∈ U`, and `v₁` is a frame at `x₁` whose determinant **read in the chart
of the ball** is of the same sign as that of the frame of `F` at `x₀`, then `F` is framed cobordant
to the framed `0`-manifold obtained by replacing `(x₀, v₀)` with `(x₁, v₁)`.  The cobordism is the
Pontryagin manifold of the moving homotopy `H = glueH (moveΦ …) k`, `k` the Theorem-B map of `F`
supported away from the frontier of `U`.

**No orientation of `M` occurs.**  The sign hypothesis is stated with the chart sign
`chartSign hM x_c · ·` of `Chapter7/ChartSign.lean`, which mentions no orientation; on a ball on
which a chart is orientation-preserving it agrees with equality of the frame signs
(`frameSign_eq_iff_chartSign_eq`), so the oriented statement is a corollary — that is how
`move_in_ball_frameSign` and `exists_reach` of `Chapter7/Reach.lean` are obtained.
-/

open Set Filter Topology Function Module Metric
open scoped ContDiff Manifold RealInnerProductSpace Classical

noncomputable section

namespace Milnor

open Sphere

namespace Framed

variable {K m w : ℕ} {M : Set (EuclideanSpace ℝ (Fin (K + 1)))}
  {hM : IsSliceSubmanifold 𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1))) (EuclideanSpace ℝ (Fin m))
    (EuclideanSpace ℝ (Fin w)) M} (hMc : IsCompact M) (hne : M.Nonempty)

section ident

variable {x_c : M} {R : ℝ} (hR : 0 < R)
  (hRt : letI := hM.chartedSpace;
    closedBall (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) x_c x_c) R ⊆
      (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) x_c).target)
  {b : Fin m → EuclideanSpace ℝ (Fin m)} (hb : LinearIndependent ℝ b) {c : ℝ} (hc : 0 < c)
  {ε₀ μ : ℝ} (hsouth : ∀ z, ε₀ / 2 ≤ ‖z‖ → collapse hb c z = south) (hμ : 0 < μ)
  (hε₀ : ε₀ = μ * R / 2)
  {τ : ℝ → Fin m → EuclideanSpace ℝ (Fin m)} (hτ : ContDiff ℝ ∞ (fun t => basisCLM (τ t)))
  (hτi : ∀ t, LinearIndependent ℝ (τ t)) (hτμ : ∀ t z, μ * ‖z‖ ≤ ‖basisCLM (τ t) z‖)
  {γ : ℝ → EuclideanSpace ℝ (Fin m)} (hγ : ContDiff ℝ ∞ γ)
  (hγR : letI := hM.chartedSpace; ∀ t, ‖γ t - extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) x_c x_c‖ < R / 4)
  {k : M → Sph m}
  {O : Set M} (hO : IsOpen O) (hOU : closure (ballU hM x_c R) \ ballU hM x_c R ⊆ O)
  (hkO : ∀ z ∈ O, k z = south)

include hc hτi in
/-- The preimage of `north` under the slice at time `t`, when `γ t` is the chart image of a point
`x_t` of the ball. -/
theorem moveH_slice_preimage (t : ℝ) {x_t : M} (hx_t : x_t ∈ ballU hM x_c R)
    (hφ : letI := hM.chartedSpace; extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) x_c x_t = γ t) :
    letI := hM.chartedSpace
    (fun x => glueH hM x_c R (moveΦ hb c τ γ) k (x, t)) ⁻¹' {north} =
      (k ⁻¹' {north} \ ballU hM x_c R) ∪ {x_t} := by
  letI := hM.chartedSpace
  haveI := hM.isManifold
  ext x
  simp only [mem_preimage, mem_singleton_iff, mem_union, Set.mem_sdiff]
  rw [moveH_eq_north_iff (hb := hb) (γ := γ) (k := k) (hc := hc) (hτi := hτi) t x]
  constructor
  · rintro (⟨hxU, hx⟩ | ⟨hxU, hx⟩)
    · right
      rw [← hφ] at hx
      exact (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) x_c).injOn (mem_ballU.1 hxU).1
        (mem_ballU.1 hx_t).1 hx
    · left; exact ⟨hx, hxU⟩
  · rintro (⟨hx, hxU⟩ | rfl)
    · right; exact ⟨hxU, hx⟩
    · left; exact ⟨hx_t, hφ⟩

include hR hRt hsouth hμ hε₀ hτμ hγR hO hOU hkO in
/-- Off the chart ball the slice has the frames of `k`. -/
theorem pontV_moveH_slice_of_notMem (t : ℝ)
    (hf : letI := hM.chartedSpace; haveI := hM.isManifold;
      ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) ∞
        (fun x => glueH hM x_c R (moveΦ hb c τ γ) k (x, t)))
    {x : EuclideanSpace ℝ (Fin (K + 1))} (hx : x ∈ M) (hxU : (⟨x, hx⟩ : M) ∉ ballU hM x_c R)
    (hfx : glueH hM x_c R (moveΦ hb c τ γ) k (⟨x, hx⟩, t) = north) (hkx : k ⟨x, hx⟩ = north)
    (b' : Fin m → EuclideanSpace ℝ (Fin m)) (i : Fin m) :
    pontV hM hMc hne (fun x => glueH hM x_c R (moveΦ hb c τ γ) k (x, t)) north b' i ⟨⟨x, hx⟩, hfx⟩ =
      pontV hM hMc hne k north b' i ⟨⟨x, hx⟩, hkx⟩ := by
  letI := hM.chartedSpace
  haveI := hM.isManifold
  refine pontV_congr hM hMc hne hx hfx hkx ?_ b' i
  exact glueH_slice_eventually_eq_of_notMem (Φ := moveΦ hb c τ γ) hR hRt
    (moveΦ_south_of_le (hM := hM) (x_c := x_c) (hR := hR) (hb := hb) (hsouth := hsouth)
      (hμ := hμ) (hε₀ := hε₀) (hτμ := hτμ) (hγR := hγR)) hO hOU hkO hxU t

include hτ hγ in
/-- At the moving point the slice has the prescribed frame. -/
theorem pontV_moveH_slice_of_mem (t : ℝ)
    (hf : letI := hM.chartedSpace; haveI := hM.isManifold;
      ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) ∞
        (fun x => glueH hM x_c R (moveΦ hb c τ γ) k (x, t)))
    (hn : letI := hM.chartedSpace; haveI := hM.isManifold;
      IsRegularValue 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin m))
        (fun x => glueH hM x_c R (moveΦ hb c τ γ) k (x, t)) north)
    {x_t : M} (hx_t : x_t ∈ ballU hM x_c R)
    (hφ : letI := hM.chartedSpace; extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) x_c x_t = γ t)
    (hfx : glueH hM x_c R (moveΦ hb c τ γ) k (x_t, t) = north)
    {v : Fin m → EuclideanSpace ℝ (Fin (K + 1))} (hvT : ∀ i, v i ∈ tangentM hM x_t)
    (hinv : (basisCLM (τ t)).comp (chartFrameCLM hM x_c x_t v) = ContinuousLinearMap.id ℝ _)
    (hcb : LinearIndependent ℝ (fun i => c • b i)) (i : Fin m) :
    pontV hM hMc hne (fun x => glueH hM x_c R (moveΦ hb c τ γ) k (x, t)) north
      (fun i => c • b i) i ⟨x_t, hfx⟩ = v i := by
  letI := hM.chartedSpace
  haveI := hM.isManifold
  refine pontV_eq_of hM hMc hne hf hn (zero_add m) ⟨x_t, hfx⟩ (hvT i) ?_ _ i ?_
  · intro u hu
    rw [tangentN_eq_bot_of_dim_zero, Submodule.mem_bot] at hu
    rw [hu, inner_zero_right]
  · have hv : v i = mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1)))
        (Subtype.val : M → EuclideanSpace ℝ (Fin (K + 1))) x_t (chartCoord hM x_t (v i)) :=
      (mfd_val_chartCoord hM (hvT i)).symm
    rw [hv, At_apply_mfd_val hM hMc hne hf hfx,
      mfd_moveH_slice_of_mem (hb := hb) (c := c) (k := k) (hτ := hτ) (hγ := hγ) hx_t hφ]
    have h1 : mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin m))
        (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) x_c) x_t (chartCoord hM x_t (v i)) =
        chartFrameCLM hM x_c x_t v (EuclideanSpace.single i 1) := by
      simp [chartFrameCLM, basisCLM_single]
    have h2 := congrArg (fun T => T (EuclideanSpace.single i 1)) hinv
    simp only [ContinuousLinearMap.coe_comp', Function.comp_apply,
      ContinuousLinearMap.id_apply] at h2
    simp only [ContinuousLinearMap.coe_comp', Function.comp_apply]
    rw [h1, h2, ContinuousLinearMap.smul_apply, basisCLM_single]

end ident

include hMc hne in
/-- **Moving a framed point.**  The two frames are compared by the sign of their determinants read
in the chart of the ball; no orientation of `M` is involved. -/
theorem exists_move (hm : 0 < m)
    (F : FramedSub hM 0 m) (x_c : M) {R : ℝ} (hR : 0 < R)
    (hRt : letI := hM.chartedSpace;
      closedBall (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) x_c x_c) R ⊆
        (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) x_c).target)
    {x₀ : M} (hx₀ : x₀ ∈ F.N) (hx₀U : x₀ ∈ ballU hM x_c (R / 4))
    (hFU : ∀ x ∈ F.N, x ≠ x₀ → x ∉ closure (ballU hM x_c R))
    {x₁ : M} (hx₁U : x₁ ∈ ballU hM x_c (R / 4))
    {v₁ : Fin m → EuclideanSpace ℝ (Fin (K + 1))} (hv₁T : ∀ i, v₁ i ∈ tangentM hM x₁)
    (hv₁ : LinearIndependent ℝ v₁)
    (hsign : chartSign hM x_c x₁ v₁ = chartSign hM x_c x₀ (fun i => F.v i ⟨x₀, hx₀⟩)) :
    ∃ F' : FramedSub hM 0 m, F'.N = (F.N \ {x₀}) ∪ {x₁} ∧
      (∀ i x (hx : x ∈ F.N) (hxx : x ≠ x₀) (hx' : x ∈ F'.N), F'.v i ⟨x, hx'⟩ = F.v i ⟨x, hx⟩) ∧
      (∀ i (hx' : x₁ ∈ F'.N), F'.v i ⟨x₁, hx'⟩ = v₁ i) ∧ FramedCobordant hM F F' := by
  letI := hM.chartedSpace
  haveI := hM.isManifold
  haveI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  set φ := extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) x_c with hφdef
  have hsub : ∀ r, r ≤ R → ballU hM x_c r ⊆ ballU hM x_c R := fun r hr z hz => by
    rw [mem_ballU] at hz ⊢; exact ⟨hz.1, lt_of_lt_of_le hz.2 hr⟩
  have hx₀U' : x₀ ∈ ballU hM x_c R := hsub _ (by linarith) hx₀U
  have hx₁U' : x₁ ∈ ballU hM x_c R := hsub _ (by linarith) hx₁U
  -- the frames and their dual tuples
  set v₀ : Fin m → EuclideanSpace ℝ (Fin (K + 1)) := fun i => F.v i ⟨x₀, hx₀⟩ with hv₀def
  have hv₀T : ∀ i, v₀ i ∈ tangentM hM x₀ := fun i => by
    show F.v i ⟨x₀, hx₀⟩ ∈ tangentM hM x₀
    exact F.tangent i ⟨x₀, hx₀⟩
  have hv₀ : LinearIndependent ℝ v₀ := F.indep ⟨x₀, hx₀⟩
  obtain ⟨τ₀, hτ₀i, -, hc₀2, hs₀⟩ := exists_dualTuple (mem_ballU.1 hx₀U').1 hv₀T hv₀
  obtain ⟨τ₁, hτ₁i, -, hc₁2, hs₁⟩ := exists_dualTuple (mem_ballU.1 hx₁U').1 hv₁T hv₁
  set e₀ := basisOfLinearIndependentOfCardEqFinrank hτ₀i (by simp) with he₀def
  set e₁ := basisOfLinearIndependentOfCardEqFinrank hτ₁i (by simp) with he₁def
  have he₀ : ⇑e₀ = τ₀ := coe_basisOfLinearIndependentOfCardEqFinrank _ _
  have he₁ : ⇑e₁ = τ₁ := coe_basisOfLinearIndependentOfCardEqFinrank _ _
  -- the dual tuples have the chart signs of the two frames
  have k₀ : orSign (stdOr m) (stdOr m) (basisCLM τ₀) = chartSign hM x_c x₀ v₀ := by
    rw [orSign_self_eq_sgn_det finrank_E]; exact hs₀
  have k₁ : orSign (stdOr m) (stdOr m) (basisCLM τ₁) = chartSign hM x_c x₁ v₁ := by
    rw [orSign_self_eq_sgn_det finrank_E]; exact hs₁
  have hor : e₀.orientation = e₁.orientation := by
    refine orientation_eq_of_orSign_basisCLM_eq hm (o := stdOr m) e₀ e₁ ?_
    rw [he₀, he₁, k₀, k₁, hsign]
  -- the path of tuples and the path of centres
  obtain ⟨τ, -, hτ0, hτ1, hτi, hτ, μ, hμ, hτμ⟩ :=
    exists_tuplePath e₀ e₁ hor (ε := 1 / 4) (by norm_num) (by norm_num)
  obtain ⟨σ, hσ, hσ0, hσ1, hσ01, -⟩ := exists_timeTransition (ε := 1 / 4) (by norm_num) (by norm_num)
  set γ : ℝ → EuclideanSpace ℝ (Fin m) := fun t => φ x₀ + σ t • (φ x₁ - φ x₀) with hγdef
  have hγ : ContDiff ℝ ∞ γ := contDiff_const.add (hσ.smul contDiff_const)
  have hγ0 : ∀ t, t ≤ 1 / 4 → γ t = φ x₀ := fun t ht => by simp [hγdef, hσ0 t ht]
  have hγ1 : ∀ t, 1 - 1 / 4 ≤ t → γ t = φ x₁ := fun t ht => by simp [hγdef, hσ1 t ht]
  have hγR : ∀ t, ‖γ t - φ x_c‖ < R / 4 := by
    intro t
    have h0 : ‖φ x₀ - φ x_c‖ < R / 4 := (mem_ballU.1 hx₀U).2
    have h1 : ‖φ x₁ - φ x_c‖ < R / 4 := (mem_ballU.1 hx₁U).2
    obtain ⟨hs0, hs1⟩ := hσ01 t
    have heq : γ t - φ x_c = (1 - σ t) • (φ x₀ - φ x_c) + σ t • (φ x₁ - φ x_c) := by
      simp only [hγdef]; module
    rw [heq]
    calc ‖(1 - σ t) • (φ x₀ - φ x_c) + σ t • (φ x₁ - φ x_c)‖
        ≤ ‖(1 - σ t) • (φ x₀ - φ x_c)‖ + ‖σ t • (φ x₁ - φ x_c)‖ := norm_add_le _ _
      _ = (1 - σ t) * ‖φ x₀ - φ x_c‖ + σ t * ‖φ x₁ - φ x_c‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_nonneg (by linarith), abs_of_nonneg hs0]
      _ ≤ (1 - σ t) * max ‖φ x₀ - φ x_c‖ ‖φ x₁ - φ x_c‖ +
          σ t * max ‖φ x₀ - φ x_c‖ ‖φ x₁ - φ x_c‖ :=
        add_le_add (mul_le_mul_of_nonneg_left (le_max_left _ _) (by linarith))
          (mul_le_mul_of_nonneg_left (le_max_right _ _) hs0)
      _ = max ‖φ x₀ - φ x_c‖ ‖φ x₁ - φ x_c‖ := by ring
      _ < R / 4 := max_lt h0 h1
  -- the collapse basis and scale
  set b : Fin m → EuclideanSpace ℝ (Fin m) := fun i => EuclideanSpace.single i 1 with hbdef
  have hb : LinearIndependent ℝ b := by
    have := (EuclideanSpace.basisFun (Fin m) ℝ).toBasis.linearIndependent
    have h3 : ⇑((EuclideanSpace.basisFun (Fin m) ℝ).toBasis) = b := by
      funext i; simp [hbdef]
    rw [h3] at this; exact this
  have hR4 : 0 < μ * R / 2 := by positivity
  obtain ⟨c₁, hc₁, hc₁s⟩ := exists_scale_all hb hR4
  -- the Theorem-B map supported away from the frontier of the ball
  set W : Set M := (closure (ballU hM x_c R))ᶜ ∪ ballU hM x_c (R / 2) with hWdef
  have hW : IsOpen W := isClosed_closure.isOpen_compl.union (isOpen_ballU _ _)
  have hNW : F.N ⊆ W := by
    intro x hx
    by_cases hxx : x = x₀
    · right
      rw [hxx]
      have h := mem_ballU.1 hx₀U
      exact mem_ballU.2 ⟨h.1, by linarith [h.2]⟩
    · left; exact hFU x hx hxx
  obtain ⟨k, hk, hkn, c, hc, hcb, hc₁c, hkF, Kc, hKc, hKcW, hkS⟩ :=
    exists_map_of_framedSub_subset hM hMc hne F b hb W hW hNW c₁
  have hsouth : ∀ z, μ * R / 2 / 2 ≤ ‖z‖ → collapse hb c z = south := hc₁s c hc₁c
  have hO : IsOpen Kcᶜ := hKc.isClosed.isOpen_compl
  have hOU : closure (ballU hM x_c R) \ ballU hM x_c R ⊆ Kcᶜ := by
    rintro z ⟨hz1, hz2⟩ hzK
    rcases hKcW hzK with h | h
    · exact h hz1
    · exact hz2 (hsub _ (by linarith) h)
  have hkO : ∀ z ∈ Kcᶜ, k z = south := fun z hz => hkS z hz
  have hkN : k ⁻¹' {north} = F.N := congrArg FramedSub.N hkF
  -- the homotopy
  set H := glueH hM x_c R (moveΦ hb c τ γ) k with hHdef
  have hH : ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin m)).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, EuclideanSpace ℝ (Fin m))
      ∞ H :=
    contMDiff_moveH (hM := hM) (x_c := x_c) hR hRt hb hsouth hμ rfl hτ hτμ hγ hγR hk hO hOU hkO
  have hHn : IsRegularValue (𝓘(ℝ, EuclideanSpace ℝ (Fin m)).prod 𝓘(ℝ, ℝ))
      𝓘(ℝ, EuclideanSpace ℝ (Fin m)) H north :=
    isRegularValue_moveH hR hRt hb hc hsouth hμ rfl hτ hτi hτμ hγ hγR hk hkn hO hOU hkO
  have hslice : ∀ t, IsRegularValue 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin m))
      (fun x => H (x, t)) north := fun t =>
    isRegularValue_moveH_slice hR hRt hb hc hsouth hμ rfl hτ hτi hτμ hγ hγR hkn hO hOU hkO t
  have hH0 : ∀ x t, t ≤ 1 / 4 → H (x, t) = H (x, 0) := by
    intro x t ht
    by_cases hx : x ∈ ballU hM x_c R
    · rw [hHdef, glueH_of_mem hx, glueH_of_mem hx]
      exact moveΦ_congr_time hb c (by rw [hτ0 t ht, hτ0 0 (by norm_num)])
        (by rw [hγ0 t ht, hγ0 0 (by norm_num)]) _
    · rw [hHdef, glueH_of_notMem hx, glueH_of_notMem hx]
  have hH1 : ∀ x t, 1 - 1 / 4 ≤ t → H (x, t) = H (x, 1) := by
    intro x t ht
    by_cases hx : x ∈ ballU hM x_c R
    · rw [hHdef, glueH_of_mem hx, glueH_of_mem hx]
      exact moveΦ_congr_time hb c (by rw [hτ1 t ht, hτ1 1 (by norm_num)])
        (by rw [hγ1 t ht, hγ1 1 (by norm_num)]) _
    · rw [hHdef, glueH_of_notMem hx, glueH_of_notMem hx]
  have hf0 : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) ∞
      (fun x => H (x, 0)) := hH.comp (contMDiff_id.prodMk contMDiff_const)
  have hf1 : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) ∞
      (fun x => H (x, 1)) := hH.comp (contMDiff_id.prodMk contMDiff_const)
  have hcob := framedCobordant_of_homotopy hM hMc hne (zero_add m) (ε := 1 / 4) (by norm_num)
    (by norm_num) hH hHn hH0 hH1 hf0 (hslice 0) hf1 (hslice 1) (fun i => c • b i) hcb
  -- the two ends
  have hφ0 : φ x₀ = γ 0 := (hγ0 0 (by norm_num)).symm
  have hφ1 : φ x₁ = γ 1 := (hγ1 1 (by norm_num)).symm
  have hpre0 := moveH_slice_preimage (hb := hb) (k := k) hc hτi 0 hx₀U' hφ0
  have hpre1 := moveH_slice_preimage (hb := hb) (k := k) hc hτi 1 hx₁U' hφ1
  rw [hkN] at hpre0 hpre1
  have hN0 : (fun x => H (x, 0)) ⁻¹' {north} = F.N := by
    rw [hpre0]
    ext x
    simp only [mem_union, mem_diff, mem_singleton_iff]
    constructor
    · rintro (⟨hx, -⟩ | rfl)
      · exact hx
      · exact hx₀
    · intro hx
      by_cases hxx : x = x₀
      · right; exact hxx
      · left; exact ⟨hx, fun hU => hFU x hx hxx (subset_closure hU)⟩
  have hN1 : (fun x => H (x, 1)) ⁻¹' {north} = (F.N \ {x₀}) ∪ {x₁} := by
    rw [hpre1]
    ext x
    simp only [mem_union, mem_diff, mem_singleton_iff]
    constructor
    · rintro (⟨hx, hxU⟩ | rfl)
      · left; exact ⟨hx, fun hxx => hxU (hxx ▸ hx₀U')⟩
      · right; rfl
    · rintro (⟨hx, hxx⟩ | rfl)
      · left; exact ⟨hx, fun hU => hFU x hx hxx (subset_closure hU)⟩
      · right; rfl
  -- identification of the framings
  have hP0 : pontryagin hM hMc hne hf0 (hslice 0) (zero_add m) (fun i => c • b i) hcb = F := by
    refine FramedSub.ext' hM hN0 ?_
    intro i x hx hx'
    by_cases hxx : x = x₀
    · subst hxx
      exact pontV_moveH_slice_of_mem hMc hne (hb := hb) (k := k) hτ hγ 0 hf0 (hslice 0) hx₀U' hφ0 hx
        hv₀T (by rw [hτ0 0 (by norm_num), he₀]; exact hc₀2) hcb i
    · have hxU : x ∉ ballU hM x_c R := fun hU => hFU x hx' hxx (subset_closure hU)
      have hkx : k x = north := by rw [← mem_singleton_iff, ← mem_preimage, hkN]; exact hx'
      have h1 := pontV_moveH_slice_of_notMem hMc hne (hb := hb) (k := k) hR hRt hsouth hμ rfl hτμ
        hγR hO hOU hkO 0 hf0 x.2 hxU hx hkx (fun i => c • b i) i
      have h2 := FramedSub.v_congr hkF i ⟨x, hkx⟩
      simp only at h2
      exact h1.trans h2
  -- the new framed `0`-manifold
  refine ⟨pontryagin hM hMc hne hf1 (hslice 1) (zero_add m) (fun i => c • b i) hcb, hN1, ?_, ?_, ?_⟩
  · intro i x hx hxx hx'
    have hxU : x ∉ ballU hM x_c R := fun hU => hFU x hx hxx (subset_closure hU)
    have hkx : k x = north := by rw [← mem_singleton_iff, ← mem_preimage, hkN]; exact hx
    have h1 := pontV_moveH_slice_of_notMem hMc hne (hb := hb) (k := k) hR hRt hsouth hμ rfl hτμ
      hγR hO hOU hkO 1 hf1 x.2 hxU hx' hkx (fun i => c • b i) i
    have h2 := FramedSub.v_congr hkF i ⟨x, hkx⟩
    simp only at h2
    exact h1.trans h2
  · intro i hx'
    exact pontV_moveH_slice_of_mem hMc hne (hb := hb) (k := k) hτ hγ 1 hf1 (hslice 1) hx₁U' hφ1 hx'
      hv₁T (by rw [hτ1 1 (by norm_num), he₁]; exact hc₁2) hcb i
  · rw [← hP0]; exact hcob

end Framed

end Milnor
