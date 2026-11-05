import Milnor.Chapter7.TubeData
import Milnor.Chapter7.Taylor
import Milnor.Chapter7.Collapse

/-!
# Deformation to the standard form near a framed submanifold (Milnor §7, p. 48)

Let `(N, v)` be a framed submanifold with product neighbourhood `G : N × B_ε → V`, and let
`k : M → Sᵖ` be a smooth map with `k⁻¹(y) = N` whose derivative along the framing is `c • bᵢ`
in the chart `φ` at `y` (`c > 0`).  Then `k` is smoothly homotopic to a map `k'` which is the
"standard" map `G(x, s) ↦ φ⁻¹(φ(y) + ∑ sᵢ bᵢ)` near `N` and does not take the value `y` off `N`.
The homotopy is `φ⁻¹(φ(y) + Φ + τ χ (L s - Φ))` in the chart, with `Φ` the chart representative
of `k ∘ G`, `L s = ∑ sᵢ bᵢ` and `χ` a bump function; the uniform Taylor estimate
`‖Φ(x,s) - c L s‖ ≤ κ ‖s‖` keeps the zero set equal to `N` throughout.
-/

open Set Filter Topology Function Module Metric
open scoped ContDiff Manifold RealInnerProductSpace Classical

noncomputable section

namespace Milnor

/-- A tube around `N × {0}` inside an open set (`N` compact). -/
theorem exists_tube_subset {N P : Type*} [TopologicalSpace N] [CompactSpace N]
    [NormedAddCommGroup P] {W : Set (N × P)} (hW : IsOpen W) (hW0 : ∀ x : N, (x, (0 : P)) ∈ W) :
    ∃ δ > 0, ∀ (x : N) (s : P), ‖s‖ < δ → (x, s) ∈ W := by
  have hsub : (univ : Set N) ×ˢ ({0} : Set P) ⊆ W := by
    rintro ⟨x, s⟩ ⟨-, hs⟩
    have hs' : s = 0 := hs
    rw [hs']; exact hW0 x
  obtain ⟨u, v, -, hv, hu, hv0, huv⟩ :=
    generalized_tube_lemma isCompact_univ isCompact_singleton hW hsub
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 hv 0 (hv0 (mem_singleton 0))
  refine ⟨δ, hδ, fun x s hs => huv ⟨hu (mem_univ x), hball (mem_ball_zero_iff.2 hs)⟩⟩

open Sphere

namespace Framed

variable {K m w : ℕ} {M : Set (EuclideanSpace ℝ (Fin (K + 1)))}
  {hM : IsSliceSubmanifold 𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1))) (EuclideanSpace ℝ (Fin m))
    (EuclideanSpace ℝ (Fin w)) M} (hMc : IsCompact M) (hne : M.Nonempty)
  {n p : ℕ} {F : FramedSub hM n p}

/-- **The deformation lemma.** -/
theorem exists_deform [Nonempty F.N] (T : TubeData hMc hne F) {y : Sph p} {k : M → Sph p}
    (hk : letI := hM.chartedSpace; haveI := hM.isManifold;
      ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) ∞ k)
    (hkN : ∀ z : M, k z = y ↔ z ∈ F.N) {b : Fin p → EuclideanSpace ℝ (Fin p)}
    (hb : LinearIndependent ℝ b) {c : ℝ} (hc : 0 < c)
    (hAk : ∀ (x : F.N) (i : Fin p), At hM hMc hne k y x.1.1 (F.v i x) = c • b i) :
    letI := hM.chartedSpace; haveI := hM.isManifold;
    ∃ (Hk : M × ℝ → Sph p) (δ : ℝ), 0 < δ ∧ δ ≤ T.ε ∧
      ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin m)).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) ∞ Hk ∧
      (∀ z, Hk (z, 0) = k z) ∧
      (∀ (x : F.N) (s : EuclideanSpace ℝ (Fin p)), ‖s‖ < δ →
        Hk (T.G (x, s), 1) = (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) y).symm
          (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) y y + basisCLM b s)) ∧
      (∀ z, z ∉ F.N → Hk (z, 1) ≠ y) := by
  letI := hM.chartedSpace
  haveI := hM.isManifold
  letI := F.hN.chartedSpace
  haveI := F.hN.isManifold
  haveI : CompactSpace F.N := isCompact_iff_compactSpace.1 F.compact
  set φ := extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) y with hφ
  have hφy : y ∈ φ.source := mem_extChartAt_source y
  set L := basisCLM b with hL
  -- the tube on which `k ∘ G` lands in the chart
  set W₀ : Set (F.N × EuclideanSpace ℝ (Fin p)) :=
    {q | q ∈ PN.tube F.N p T.ε ∧ k (T.G q) ∈ φ.source} with hW₀
  have hW₀o : IsOpen W₀ := by
    refine (PN.isOpen_tube _).inter ?_
    exact (isOpen_extChartAt_source y).preimage (hk.continuous.comp T.hG.continuous)
  have hW₀0 : ∀ x : F.N, (x, (0 : EuclideanSpace ℝ (Fin p))) ∈ W₀ := fun x => by
    refine ⟨by show ‖(0 : EuclideanSpace ℝ (Fin p))‖ < T.ε; rw [norm_zero]; exact T.hε, ?_⟩
    rw [T.G_zero, (hkN x.1).2 x.2]; exact hφy
  obtain ⟨δ₀, hδ₀, hW₀δ⟩ := exists_tube_subset hW₀o hW₀0
  -- the chart representative
  set Φ : F.N × EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p) :=
    fun q => φ (k (T.G q)) - φ y with hΦdef
  have hΦ0 : ∀ x : F.N, Φ (x, 0) = 0 := fun x => by
    simp only [hΦdef]
    rw [T.G_zero, (hkN x.1).2 x.2, sub_self]
  have hΦ : ContMDiffOn (𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin p)))
      𝓘(ℝ, EuclideanSpace ℝ (Fin p)) ∞ Φ W₀ := by
    intro q hq
    have h1 : ContMDiffAt (𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin p)))
        𝓘(ℝ, EuclideanSpace ℝ (Fin p)) ∞ (fun q => φ (k (T.G q))) q := by
      have h2 : ContMDiffAt 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) ∞ φ
          (k (T.G q)) :=
        contMDiffAt_extChartAt' (n := ∞)
          (by rw [← extChartAt_source 𝓘(ℝ, EuclideanSpace ℝ (Fin p))]; exact hq.2)
      exact h2.comp q (hk.contMDiffAt.comp q T.hG.contMDiffAt)
    exact (h1.sub contMDiffAt_const).contMDiffWithinAt
  -- the fibre derivative at `0` is `c • L`
  have hΦd : ∀ x : F.N, HasFDerivAt (fun s => Φ (x, s)) (c • L) 0 := by
    intro x
    have hdiff : DifferentiableAt ℝ (fun s => Φ (x, s)) 0 := by
      have h1 : ContMDiffAt 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) ∞
          (fun s => Φ (x, s)) 0 := by
        have h2 : ContMDiffAt (𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin p)))
            𝓘(ℝ, EuclideanSpace ℝ (Fin p)) ∞ Φ (x, 0) :=
          hΦ.contMDiffAt (hW₀o.mem_nhds (hW₀0 x))
        have h3 : ContMDiffAt 𝓘(ℝ, EuclideanSpace ℝ (Fin p))
            (𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin p))) ∞
            (fun s : EuclideanSpace ℝ (Fin p) => (x, s)) 0 :=
          contMDiffAt_const.prodMk contMDiffAt_id
        exact h2.comp 0 h3
      rw [contMDiffAt_iff_contDiffAt] at h1
      exact h1.differentiableAt (by simp)
    have hD := hdiff.hasFDerivAt
    -- directional derivatives along `s ↦ s eᵢ`
    have hdir : ∀ i : Fin p, HasDerivAt (fun s : ℝ => Φ (x, s • EuclideanSpace.single i (1 : ℝ)))
        (c • b i) 0 := by
      intro i
      have hxN : x.1 ∈ F.N := x.2
      have hfx : k x.1 = y := (hkN x.1).2 hxN
      have hsrc : k ⟨x.1.1, x.1.2⟩ ∈ φ.source := by rw [Subtype.coe_eta, hfx]; exact hφy
      have hxW : x.1.1 ∈ Wt hM hMc hne k y := mem_Wt_of_mem hM hMc hne x.1.2 hsrc
      have hd1 : HasDerivAt (fun s : ℝ => Ft hM hMc hne k y (x.1.1 + s • F.v i x))
          (At hM hMc hne k y x.1.1 (F.v i x)) 0 := by
        have h1 : HasDerivAt (fun s : ℝ => x.1.1 + s • F.v i x) (F.v i x) 0 := by
          have := (hasDerivAt_id (0 : ℝ)).smul_const (F.v i x)
          simpa using (this.const_add x.1.1)
        have h2 : HasFDerivAt (Ft hM hMc hne k y) (At hM hMc hne k y x.1.1)
            (x.1.1 + (0 : ℝ) • F.v i x) := by
          rw [zero_smul, add_zero]; exact hasFDerivAt_Ft hM hMc hne hk hxW
        exact h2.comp_hasDerivAt (0 : ℝ) h1
      rw [hAk x i] at hd1
      have hd2 := hd1.sub_const (φ y)
      refine hd2.congr_of_eventuallyEq ?_
      have hev : ∀ᶠ s : ℝ in 𝓝 0, |s| ≤ T.a₀ := by
        filter_upwards [Metric.ball_mem_nhds (0 : ℝ) T.ha₀] with s hs
        have := mem_ball.1 hs
        rw [Real.dist_eq, sub_zero] at this
        exact this.le
      filter_upwards [hev] with s hs
      simp only [hΦdef]
      rw [T.G_line x i hs]
      rfl
    -- the Fréchet derivative agrees with `c • L` on the basis
    have hext : fderiv ℝ (fun s => Φ (x, s)) 0 = c • L := by
      apply ContinuousLinearMap.coe_injective
      apply (EuclideanSpace.basisFun (Fin p) ℝ).toBasis.ext
      intro i
      simp only [OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply,
        ContinuousLinearMap.coe_coe]
      have h1 : HasDerivAt (fun s : ℝ => Φ (x, s • EuclideanSpace.single i (1 : ℝ)))
          (fderiv ℝ (fun s => Φ (x, s)) 0 (EuclideanSpace.single i 1)) 0 := by
        have hl : HasDerivAt (fun s : ℝ => s • EuclideanSpace.single i (1 : ℝ))
            (EuclideanSpace.single i (1 : ℝ)) 0 := by
          simpa using (hasDerivAt_id (0 : ℝ)).smul_const (EuclideanSpace.single i (1 : ℝ))
        have hD' : HasFDerivAt (fun s => Φ (x, s)) (fderiv ℝ (fun s => Φ (x, s)) 0)
            ((0 : ℝ) • EuclideanSpace.single i (1 : ℝ)) := by rw [zero_smul]; exact hD
        exact hD'.comp_hasDerivAt (0 : ℝ) hl
      rw [h1.unique (hdir i)]
      simp [hL, basisCLM_single]
    rw [← hext]; exact hD
  -- the antilipschitz constant of `L`
  set Kc : NNReal := ‖((Be hb).symm : EuclideanSpace ℝ (Fin p) →L[ℝ] EuclideanSpace ℝ (Fin p))‖₊
    with hKc
  have hanti : AntilipschitzWith Kc (Be hb) := (Be hb).antilipschitz
  set m₀ : ℝ := 1 / (Kc + 1) with hm₀
  have hm₀pos : 0 < m₀ := by positivity
  have hLlow : ∀ s, m₀ * ‖s‖ ≤ ‖L s‖ := by
    intro s
    have h1 : ‖s‖ ≤ Kc * ‖Be hb s‖ := by
      have := hanti.le_mul_dist s 0
      simpa [dist_zero_right] using this
    have h2 : ‖s‖ ≤ (Kc + 1) * ‖L s‖ := by
      rw [← Be_apply hb]; nlinarith [norm_nonneg (Be hb s)]
    rw [hm₀, div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]
    linarith
  -- the Taylor estimate
  set κ : ℝ := min 1 c * m₀ / 2 with hκ
  have hκpos : 0 < κ := by
    have : 0 < min 1 c := lt_min one_pos hc
    positivity
  obtain ⟨δ₁, hδ₁, htay⟩ := exists_uniform_taylor hW₀o hW₀0 hΦ hΦ0 hΦd hκpos
  -- the chart target contains a ball
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 (isOpen_extChartAt_target y) (φ y)
    (φ.map_source hφy)
  set δ₂ : ℝ := r / (κ + c * ‖L‖ + ‖L‖ + 1) with hδ₂
  have hδ₂pos : 0 < δ₂ := by positivity
  -- the radius
  set δ : ℝ := min (min δ₀ δ₁) (min δ₂ T.ε) with hδ
  have hδpos : 0 < δ := lt_min (lt_min hδ₀ hδ₁) (lt_min hδ₂pos T.hε)
  have hδ0 : δ ≤ δ₀ := (min_le_left _ _).trans (min_le_left _ _)
  have hδ1 : δ ≤ δ₁ := (min_le_left _ _).trans (min_le_right _ _)
  have hδ2 : δ ≤ δ₂ := (min_le_right _ _).trans (min_le_left _ _)
  have hδε : δ ≤ T.ε := (min_le_right _ _).trans (min_le_right _ _)
  -- estimates inside the tube
  have hnormL : ∀ s : EuclideanSpace ℝ (Fin p), ‖s‖ < δ → ‖L s‖ < r := by
    intro s hs
    calc ‖L s‖ ≤ ‖L‖ * ‖s‖ := L.le_opNorm s
      _ ≤ ‖L‖ * δ₂ := by gcongr; exact hs.le.trans hδ2
      _ < r := by
        rw [hδ₂, mul_div_assoc']
        rw [div_lt_iff₀ (by positivity)]
        have : 0 < r * (κ + c * ‖L‖ + 1) := by positivity
        nlinarith
  have hnormΦ : ∀ (x : F.N) (s : EuclideanSpace ℝ (Fin p)), ‖s‖ < δ → ‖Φ (x, s)‖ < r := by
    intro x s hs
    have h1 := htay x s (hs.trans_le hδ1)
    have h2 : ‖Φ (x, s)‖ ≤ ‖Φ (x, s) - (c • L) s‖ + ‖(c • L) s‖ := norm_le_norm_sub_add _ _
    have h3 : ‖(c • L) s‖ ≤ c * ‖L‖ * ‖s‖ := by
      rw [ContinuousLinearMap.smul_apply, norm_smul, Real.norm_eq_abs, abs_of_pos hc, mul_assoc]
      exact mul_le_mul_of_nonneg_left (L.le_opNorm s) hc.le
    have h4 : ‖s‖ ≤ δ₂ := hs.le.trans hδ2
    have h5 : (κ + c * ‖L‖) * ‖s‖ ≤ (κ + c * ‖L‖) * δ₂ :=
      mul_le_mul_of_nonneg_left h4 (add_nonneg hκpos.le (mul_nonneg hc.le (norm_nonneg L)))
    calc ‖Φ (x, s)‖ ≤ κ * ‖s‖ + c * ‖L‖ * ‖s‖ := by linarith
      _ = (κ + c * ‖L‖) * ‖s‖ := by ring
      _ ≤ (κ + c * ‖L‖) * δ₂ := h5
      _ < r := by
        rw [hδ₂, mul_div_assoc', div_lt_iff₀ (by positivity)]
        have : 0 < r * (‖L‖ + 1) := by positivity
        nlinarith
  -- the bump function and the time cutoff
  set χ : ContDiffBump (0 : EuclideanSpace ℝ (Fin p)) := ⟨δ / 4, δ / 2, by positivity, by linarith⟩
    with hχ
  obtain ⟨ρ, hρs, hρ0, hρ1, hρ01, -⟩ := exists_timeTransition (ε := 1 / 4) (by norm_num) (by norm_num)
  -- the homotopy in the chart
  set Ψ : F.N × EuclideanSpace ℝ (Fin p) → ℝ → EuclideanSpace ℝ (Fin p) :=
    fun q τ => Φ q + (ρ τ * χ q.2) • (L q.2 - Φ q) with hΨ
  have hΨmem : ∀ q : F.N × EuclideanSpace ℝ (Fin p), ‖q.2‖ < δ → ∀ τ, φ y + Ψ q τ ∈ φ.target := by
    rintro ⟨x, s⟩ hs τ
    apply hball
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left]
    have hθ0 : 0 ≤ ρ τ * χ s := mul_nonneg (hρ01 τ).1 χ.nonneg
    have hθ1 : ρ τ * χ s ≤ 1 := by
      calc ρ τ * χ s ≤ 1 * 1 := mul_le_mul (hρ01 τ).2 χ.le_one χ.nonneg zero_le_one
        _ = 1 := one_mul 1
    have h1 := hnormL s hs
    have h2 := hnormΦ x s hs
    simp only [hΨ]
    have heq : Φ (x, s) + (ρ τ * χ s) • (L s - Φ (x, s)) =
        (1 - ρ τ * χ s) • Φ (x, s) + (ρ τ * χ s) • L s := by
      simp only [smul_sub, sub_smul, one_smul]; abel
    rw [heq]
    calc ‖(1 - ρ τ * χ s) • Φ (x, s) + (ρ τ * χ s) • L s‖
        ≤ ‖(1 - ρ τ * χ s) • Φ (x, s)‖ + ‖(ρ τ * χ s) • L s‖ := norm_add_le _ _
      _ = (1 - ρ τ * χ s) * ‖Φ (x, s)‖ + (ρ τ * χ s) * ‖L s‖ := by
          rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
            abs_of_nonneg (by linarith), abs_of_nonneg hθ0]
      _ < (1 - ρ τ * χ s) * r + (ρ τ * χ s) * r := by
          rcases eq_or_lt_of_le hθ1 with h | h
          · rw [h]; simp only [sub_self, zero_mul, zero_add, one_mul]; exact h1
          · rcases eq_or_lt_of_le hθ0 with h' | h'
            · rw [← h']; simp only [sub_zero, one_mul, zero_mul, add_zero]; exact h2
            · have := mul_lt_mul_of_pos_left h2 (by linarith : 0 < 1 - ρ τ * χ s)
              have := mul_lt_mul_of_pos_left h1 h'
              linarith
      _ = r := by ring
  -- the image of the small tube
  set Vδ : Set M := T.G '' PN.tube F.N p δ with hVδ
  have htube_sub : PN.tube F.N p δ ⊆ PN.tube F.N p T.ε := fun q hq => lt_of_lt_of_le hq hδε
  have hVδo : IsOpen Vδ := PN.isOpen_image_tube T.hG (fun q hq => T.hbij q (htube_sub hq))
  have hGinv_mem : ∀ z ∈ Vδ, T.Ginv z ∈ PN.tube F.N p δ := by
    rintro z ⟨q, hq, rfl⟩
    rw [T.Ginv_G (htube_sub hq)]; exact hq
  have hGinv_W : ∀ z ∈ Vδ, T.Ginv z ∈ W₀ := fun z hz =>
    hW₀δ (T.Ginv z).1 (T.Ginv z).2 (lt_of_lt_of_le (hGinv_mem z hz) hδ0)
  have hVT : Vδ ⊆ T.V := Set.image_mono htube_sub
  have hk_src : ∀ z ∈ Vδ, k z ∈ φ.source := fun z hz => by
    have := (hGinv_W z hz).2
    rwa [T.G_Ginv (hVT hz)] at this
  have hΦ_eq : ∀ z ∈ Vδ, φ.symm (φ y + Φ (T.Ginv z)) = k z := fun z hz => by
    simp only [hΦdef]
    rw [T.G_Ginv (hVT hz), add_sub_cancel]
    exact φ.left_inv (hk_src z hz)
  -- the homotopy
  set Hk : M × ℝ → Sph p := fun zt =>
    if zt.1 ∈ Vδ then φ.symm (φ y + Ψ (T.Ginv zt.1) zt.2) else k zt.1 with hHk
  have hHk_mem : ∀ z ∈ Vδ, ∀ τ, Hk (z, τ) = φ.symm (φ y + Ψ (T.Ginv z) τ) := fun z hz τ => by
    simp [hHk, hz]
  have hHk_not : ∀ z ∉ Vδ, ∀ τ, Hk (z, τ) = k z := fun z hz τ => by simp [hHk, hz]
  have hΨ_of_zero : ∀ q τ, ρ τ * χ q.2 = 0 → Ψ q τ = Φ q := fun q τ h => by
    simp only [hΨ, h, zero_smul, add_zero]
  -- the closed core
  set Cl : Set M := T.G '' (univ ×ˢ closedBall (0 : EuclideanSpace ℝ (Fin p)) (δ / 2)) with hCl
  have hClc : IsCompact Cl :=
    (isCompact_univ.prod (isCompact_closedBall _ _)).image T.hG.continuous
  have hClV : Cl ⊆ Vδ := by
    rintro _ ⟨q, ⟨-, hq⟩, rfl⟩
    exact ⟨q, (mem_closedBall_zero_iff.1 hq).trans_lt (by linarith), rfl⟩
  have hHk_k : ∀ z ∉ Cl, ∀ τ, Hk (z, τ) = k z := by
    intro z hz τ
    by_cases hzV : z ∈ Vδ
    · rw [hHk_mem z hzV]
      have hχ : χ (T.Ginv z).2 = 0 := by
        apply χ.zero_of_le_dist
        rw [dist_zero_right]
        by_contra hlt
        push_neg at hlt
        exact hz ⟨T.Ginv z, ⟨mem_univ _, mem_closedBall_zero_iff.2 hlt.le⟩, T.G_Ginv (hVT hzV)⟩
      rw [hΨ_of_zero _ _ (by rw [hχ, mul_zero]), hΦ_eq z hzV]
    · exact hHk_not z hzV τ
  -- smoothness
  have hHk : ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin m)).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) ∞
      Hk := by
    rintro ⟨z, τ⟩
    by_cases hz : z ∈ Vδ
    · -- the chart expression is smooth
      have hfst : ContMDiffAt (𝓘(ℝ, EuclideanSpace ℝ (Fin m)).prod 𝓘(ℝ, ℝ))
          𝓘(ℝ, EuclideanSpace ℝ (Fin m)) ∞ (Prod.fst : M × ℝ → M) (z, τ) :=
        (contMDiff_fst (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin m))) (J := 𝓘(ℝ, ℝ)) (M := M) (N := ℝ)).contMDiffAt
      have hsnd : ContMDiffAt (𝓘(ℝ, EuclideanSpace ℝ (Fin m)).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
          (Prod.snd : M × ℝ → ℝ) (z, τ) :=
        (contMDiff_snd (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin m))) (J := 𝓘(ℝ, ℝ)) (M := M) (N := ℝ)).contMDiffAt
      have hGi : ContMDiffAt (𝓘(ℝ, EuclideanSpace ℝ (Fin m)).prod 𝓘(ℝ, ℝ))
          (𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin p))) ∞
          (fun zt : M × ℝ => T.Ginv zt.1) (z, τ) :=
        (T.contMDiffAt_Ginv (hVT hz)).comp (z, τ) hfst
      have hΦi : ContMDiffAt (𝓘(ℝ, EuclideanSpace ℝ (Fin m)).prod 𝓘(ℝ, ℝ))
          𝓘(ℝ, EuclideanSpace ℝ (Fin p)) ∞ (fun zt : M × ℝ => Φ (T.Ginv zt.1)) (z, τ) :=
        ContMDiffAt.comp (z, τ) (g := Φ) (f := fun zt : M × ℝ => T.Ginv zt.1)
          (hΦ.contMDiffAt (hW₀o.mem_nhds (hGinv_W z hz))) hGi
      have hs : ContMDiffAt (𝓘(ℝ, EuclideanSpace ℝ (Fin m)).prod 𝓘(ℝ, ℝ))
          𝓘(ℝ, EuclideanSpace ℝ (Fin p)) ∞ (fun zt : M × ℝ => (T.Ginv zt.1).2) (z, τ) :=
        (contMDiff_snd (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (J := 𝓘(ℝ, EuclideanSpace ℝ (Fin p)))
          (M := F.N) (N := EuclideanSpace ℝ (Fin p))).contMDiffAt.comp (z, τ) hGi
      have hχi : ContMDiffAt (𝓘(ℝ, EuclideanSpace ℝ (Fin m)).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
          (fun zt : M × ℝ => χ (T.Ginv zt.1).2) (z, τ) :=
        (contMDiff_iff_contDiff.2 χ.contDiff).contMDiffAt.comp (z, τ) hs
      have hρi : ContMDiffAt (𝓘(ℝ, EuclideanSpace ℝ (Fin m)).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
          (fun zt : M × ℝ => ρ zt.2) (z, τ) :=
        (contMDiff_iff_contDiff.2 hρs).contMDiffAt.comp (z, τ) hsnd
      have hLi : ContMDiffAt (𝓘(ℝ, EuclideanSpace ℝ (Fin m)).prod 𝓘(ℝ, ℝ))
          𝓘(ℝ, EuclideanSpace ℝ (Fin p)) ∞ (fun zt : M × ℝ => L (T.Ginv zt.1).2) (z, τ) :=
        (contMDiff_iff_contDiff.2 L.contDiff).contMDiffAt.comp (z, τ) hs
      have hΨi : ContMDiffAt (𝓘(ℝ, EuclideanSpace ℝ (Fin m)).prod 𝓘(ℝ, ℝ))
          𝓘(ℝ, EuclideanSpace ℝ (Fin p)) ∞ (fun zt : M × ℝ => φ y + Ψ (T.Ginv zt.1) zt.2) (z, τ) := by
        simp only [hΨ]
        exact contMDiffAt_const.add (hΦi.add ((hρi.mul hχi).smul (hLi.sub hΦi)))
      have hsymm : ContMDiffAt 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) ∞ φ.symm
          (φ y + Ψ (T.Ginv z) τ) :=
        (contMDiffOn_extChartAt_symm y).contMDiffAt
          ((isOpen_extChartAt_target y).mem_nhds (hΨmem _ (hGinv_mem z hz) τ))
      have h1 := hsymm.comp (z, τ) hΨi
      refine h1.congr_of_eventuallyEq ?_
      have hopen : IsOpen {zt : M × ℝ | zt.1 ∈ Vδ} := hVδo.preimage continuous_fst
      filter_upwards [hopen.mem_nhds (show z ∈ Vδ from hz)] with zt hzt
      exact hHk_mem zt.1 hzt zt.2
    · have hzC : z ∉ Cl := fun h => hz (hClV h)
      have h1 : ContMDiffAt (𝓘(ℝ, EuclideanSpace ℝ (Fin m)).prod 𝓘(ℝ, ℝ))
          𝓘(ℝ, EuclideanSpace ℝ (Fin p)) ∞ (fun zt : M × ℝ => k zt.1) (z, τ) :=
        hk.contMDiffAt.comp (z, τ)
          (contMDiff_fst (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin m))) (J := 𝓘(ℝ, ℝ)) (M := M) (N := ℝ)).contMDiffAt
      refine h1.congr_of_eventuallyEq ?_
      have hopen : IsOpen {zt : M × ℝ | zt.1 ∉ Cl} := hClc.isClosed.isOpen_compl.preimage continuous_fst
      filter_upwards [hopen.mem_nhds (show z ∉ Cl from hzC)] with zt hzt
      exact hHk_k zt.1 hzt zt.2
  refine ⟨Hk, δ / 4, by positivity, by linarith, hHk, ?_, ?_, ?_⟩
  · -- `Hk (·, 0) = k`
    intro z
    by_cases hz : z ∈ Vδ
    · rw [hHk_mem z hz, hΨ_of_zero _ _ (by rw [hρ0 0 (by norm_num), zero_mul]), hΦ_eq z hz]
    · exact hHk_not z hz 0
  · -- the standard form near `N`
    intro x s hs
    have hq : (x, s) ∈ PN.tube F.N p δ := by show ‖s‖ < δ; linarith
    have hzV : T.G (x, s) ∈ Vδ := ⟨(x, s), hq, rfl⟩
    rw [hHk_mem _ hzV, T.Ginv_G (htube_sub hq)]
    have hχ : χ s = 1 := χ.one_of_mem_closedBall (by rw [mem_closedBall_zero_iff]; exact hs.le)
    have hρ : ρ 1 = 1 := hρ1 1 (by norm_num)
    simp only [hΨ, hχ, hρ, mul_one, one_smul, add_sub_cancel]
  · -- no other preimage of `y`
    intro z hzN hzy
    by_cases hz : z ∈ Vδ
    · rw [hHk_mem z hz] at hzy
      have hqδ0 := hGinv_mem z hz
      have hqW := hGinv_W z hz
      have hGq0 : T.G (T.Ginv z) = z := T.G_Ginv (hVT hz)
      obtain ⟨q, hq⟩ : ∃ q, T.Ginv z = q := ⟨_, rfl⟩
      rw [hq] at hzy hqδ0 hqW hGq0
      have hqδ : q ∈ PN.tube F.N p δ := hqδ0
      have hs0 : q.2 ≠ 0 := by
        intro h0
        apply hzN
        have h1 : T.G q = z := hGq0
        have h2 : q = (q.1, 0) := Prod.ext rfl h0
        rw [h2, T.G_zero] at h1
        rw [← h1]; exact q.1.2
      have hmem := hΨmem q hqδ 1
      have h1 : φ y + Ψ q 1 = φ y := by
        have := congrArg φ hzy
        rwa [φ.right_inv hmem] at this
      have hΨ0 : Ψ q 1 = 0 := by simpa using h1
      have hρ : ρ 1 = 1 := hρ1 1 (by norm_num)
      have hΨ0'' : Φ q + (ρ 1 * χ q.2) • (L q.2 - Φ q) = 0 := hΨ0
      have hθ0' : 0 ≤ χ q.2 := χ.nonneg
      have hθ1' : χ q.2 ≤ 1 := χ.le_one
      obtain ⟨θ, hθ⟩ : ∃ θ, χ q.2 = θ := ⟨_, rfl⟩
      rw [hθ] at hΨ0'' hθ0' hθ1'
      have hθ0 : 0 ≤ θ := hθ0'
      have hθ1 : θ ≤ 1 := hθ1'
      have hΨ0' : Φ q + θ • (L q.2 - Φ q) = 0 := by
        rw [hρ, one_mul] at hΨ0''; exact hΨ0''
      have key : ((1 - θ) * c + θ) • L q.2 = -((1 - θ) • (Φ q - (c • L) q.2)) := by
        have e : ((1 - θ) * c + θ) • L q.2 + (1 - θ) • (Φ q - (c • L) q.2) =
            Φ q + θ • (L q.2 - Φ q) := by
          simp only [ContinuousLinearMap.smul_apply]
          module
        rw [eq_neg_iff_add_eq_zero, e]
        exact hΨ0'
      have htay' := htay q.1 q.2 (lt_of_lt_of_le hqδ hδ1)
      have hΦq : Φ q = Φ (q.1, q.2) := rfl
      rw [← hΦq] at htay'
      have hcnn : 0 ≤ (1 - θ) * c + θ := add_nonneg (mul_nonneg (by linarith) hc.le) hθ0
      have hn1 : ‖((1 - θ) * c + θ) • L q.2‖ = ((1 - θ) * c + θ) * ‖L q.2‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hcnn]
      have hn2 : ‖-((1 - θ) • (Φ q - (c • L) q.2))‖ ≤ ‖Φ q - (c • L) q.2‖ := by
        rw [norm_neg, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
        exact mul_le_of_le_one_left (norm_nonneg _) (by linarith)
      have hcoef : min 1 c ≤ (1 - θ) * c + θ := by
        rcases le_total 1 c with h | h
        · rw [min_eq_left h]
          have := mul_le_mul_of_nonneg_left h (by linarith : (0 : ℝ) ≤ 1 - θ)
          linarith
        · rw [min_eq_right h]
          have := mul_nonneg hθ0 (by linarith : (0 : ℝ) ≤ 1 - c)
          linarith
      have hLq := hLlow q.2
      have hspos : 0 < ‖q.2‖ := norm_pos_iff.2 hs0
      have hmin : 0 < min 1 c := lt_min one_pos hc
      -- `2κ‖s‖ ≤ LHS = RHS ≤ κ‖s‖`
      have h2 : min 1 c * (m₀ * ‖q.2‖) ≤ ((1 - θ) * c + θ) * ‖L q.2‖ :=
        mul_le_mul hcoef hLq (by positivity) hcnn
      have h3 : ((1 - θ) * c + θ) * ‖L q.2‖ ≤ κ * ‖q.2‖ := by
        rw [← hn1, key]; exact hn2.trans htay'
      have h4 : κ * ‖q.2‖ < min 1 c * (m₀ * ‖q.2‖) := by
        rw [hκ]
        have h5 : 0 < min 1 c * m₀ * ‖q.2‖ := by positivity
        linarith
      linarith
    · rw [hHk_not z hz] at hzy
      exact hzN ((hkN z).1 hzy)

end Framed

end Milnor
