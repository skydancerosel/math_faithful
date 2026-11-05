import Milnor.Chapter7.ThmB

/-!
# Stereographic coordinates and the straight-line homotopy

Stereographic projection `stereo y : ℝᵖ⁺¹ → y^⊥` from a point `y ∈ Sᵖ`, its inverse
`stereoInv y : y^⊥ → Sᵖ ∖ {y}`, and the straight-line homotopy in these coordinates: two smooth
maps `f, g : X → Sᵖ` which agree on an open set `U` and never hit `y` outside `U` are smoothly
homotopic through a homotopy which is constant on `U` (Milnor, Chapter 7, proof of Theorem B).
-/

open Set Filter Topology Function Module Metric
open scoped ContDiff Manifold RealInnerProductSpace Classical

noncomputable section

namespace Milnor

namespace Sphere

variable {p : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin (p + 1))

/-! ### Stereographic projection from a point `y` -/

/-- Stereographic projection from `y`, onto the hyperplane `y^⊥`. -/
def stereo (y : Sph p) (u : E) : E := (1 - ⟪u, y.1⟫)⁻¹ • (u - ⟪u, y.1⟫ • y.1)

/-- Inverse stereographic projection: `y^⊥ → Sᵖ ∖ {y}`. -/
def stereoInv (y : Sph p) (w : E) : E :=
  (2 / (‖w‖ ^ 2 + 1)) • w + ((‖w‖ ^ 2 - 1) / (‖w‖ ^ 2 + 1)) • y.1

theorem inner_lt_one_of_ne {y u : Sph p} (h : u ≠ y) : ⟪u.1, y.1⟫ < 1 := by
  have hu : ‖u.1‖ = 1 := mem_iff_norm.1 u.2
  have hy : ‖y.1‖ = 1 := mem_iff_norm.1 y.2
  refine lt_of_le_of_ne ?_ ?_
  · have := real_inner_le_norm u.1 y.1
    rwa [hu, hy, one_mul] at this
  · intro h1
    exact h (Subtype.ext ((inner_eq_one_iff_of_norm_eq_one hu hy).1 h1))

theorem inner_stereo_y (y : Sph p) (u : E) : ⟪stereo y u, y.1⟫ = 0 := by
  have hy : ⟪y.1, y.1⟫ = 1 := inner_self_eq_one_of_mem y.2
  simp only [stereo, real_inner_smul_left, inner_sub_left, hy, mul_one, sub_self, mul_zero]

theorem norm_stereoInv_sq (y : Sph p) {w : E} (hw : ⟪w, y.1⟫ = 0) :
    ‖stereoInv y w‖ ^ 2 = 1 := by
  have hy : ‖y.1‖ = 1 := mem_iff_norm.1 y.2
  have hd : ‖w‖ ^ 2 + 1 ≠ 0 := by positivity
  rw [stereoInv, norm_add_sq_real, real_inner_smul_left, real_inner_smul_right, hw, norm_smul,
    norm_smul, hy, Real.norm_eq_abs, Real.norm_eq_abs, mul_pow, mul_pow, sq_abs, sq_abs]
  field_simp
  ring

theorem stereoInv_mem (y : Sph p) {w : E} (hw : ⟪w, y.1⟫ = 0) : stereoInv y w ∈ Sph p := by
  rw [mem_iff_norm]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by norm_num)).1 (norm_stereoInv_sq y hw)

theorem inner_stereoInv_y (y : Sph p) {w : E} (hw : ⟪w, y.1⟫ = 0) :
    ⟪stereoInv y w, y.1⟫ = (‖w‖ ^ 2 - 1) / (‖w‖ ^ 2 + 1) := by
  have hy : ⟪y.1, y.1⟫ = 1 := inner_self_eq_one_of_mem y.2
  simp only [stereoInv, inner_add_left, real_inner_smul_left, hw, hy, mul_zero, mul_one, zero_add]

theorem stereoInv_ne (y : Sph p) {w : E} (hw : ⟪w, y.1⟫ = 0) : stereoInv y w ≠ y.1 := by
  intro h
  have h1 := inner_stereoInv_y y hw
  rw [h, inner_self_eq_one_of_mem y.2] at h1
  have hd : ‖w‖ ^ 2 + 1 ≠ 0 := by positivity
  field_simp at h1
  linarith

theorem norm_stereo_sq {y u : Sph p} (h : u ≠ y) :
    ‖stereo y u.1‖ ^ 2 = (1 + ⟪u.1, y.1⟫) / (1 - ⟪u.1, y.1⟫) := by
  have hu : ‖u.1‖ = 1 := mem_iff_norm.1 u.2
  have hy : ‖y.1‖ = 1 := mem_iff_norm.1 y.2
  have ha : ⟪u.1, y.1⟫ < 1 := inner_lt_one_of_ne h
  have ha' : 1 - ⟪u.1, y.1⟫ ≠ 0 := by linarith
  rw [stereo, norm_smul, mul_pow, norm_inv, Real.norm_eq_abs, inv_pow, sq_abs, norm_sub_sq_real,
    real_inner_smul_right, norm_smul, hy, hu, Real.norm_eq_abs, mul_pow, sq_abs]
  field_simp
  ring

theorem stereoInv_stereo {y u : Sph p} (h : u ≠ y) : stereoInv y (stereo y u.1) = u.1 := by
  have ha : ⟪u.1, y.1⟫ < 1 := inner_lt_one_of_ne h
  have ha' : 1 - ⟪u.1, y.1⟫ ≠ 0 := by linarith
  have hc1 : 2 / (‖stereo y u.1‖ ^ 2 + 1) = 1 - ⟪u.1, y.1⟫ := by
    rw [norm_stereo_sq h]; field_simp; ring
  have hc2 : (‖stereo y u.1‖ ^ 2 - 1) / (‖stereo y u.1‖ ^ 2 + 1) = ⟪u.1, y.1⟫ := by
    rw [norm_stereo_sq h]; field_simp; ring
  rw [stereoInv, hc1, hc2, stereo, smul_smul, mul_inv_cancel₀ ha', one_smul, sub_add_cancel]

/-! ### Smoothness -/

theorem contDiffAt_stereo (y : Sph p) {u : E} (hu : ⟪u, y.1⟫ < 1) :
    ContDiffAt ℝ ∞ (stereo y) u := by
  have hinner : ContDiff ℝ ∞ (fun u : E => ⟪u, y.1⟫) :=
    contDiff_id.inner (𝕜 := ℝ) contDiff_const
  have h1 : ContDiffAt ℝ ∞ (fun u : E => (1 - ⟪u, y.1⟫)⁻¹) u :=
    (contDiff_const.sub hinner).contDiffAt.inv (by linarith)
  have h2 : ContDiffAt ℝ ∞ (fun u : E => u - ⟪u, y.1⟫ • y.1) u :=
    contDiffAt_id.sub (hinner.contDiffAt.smul contDiffAt_const)
  exact h1.smul h2

theorem contDiff_stereoInv (y : Sph p) : ContDiff ℝ ∞ (stereoInv y) := by
  have hs : ContDiff ℝ ∞ (fun w : E => ‖w‖ ^ 2) := contDiff_norm_sq ℝ
  have hd : ∀ w : E, ‖w‖ ^ 2 + 1 ≠ 0 := fun w => by positivity
  have h1 : ContDiff ℝ ∞ (fun w : E => 2 / (‖w‖ ^ 2 + 1)) :=
    contDiff_const.div (hs.add contDiff_const) hd
  have h2 : ContDiff ℝ ∞ (fun w : E => (‖w‖ ^ 2 - 1) / (‖w‖ ^ 2 + 1)) :=
    (hs.sub contDiff_const).div (hs.add contDiff_const) hd
  exact (h1.smul contDiff_id).add (h2.smul contDiff_const)

/-- Pointwise smoothness of `nv0 ∘ w` on an open set where `w` is smooth and nonvanishing. -/
theorem contMDiffAt_nv0_comp {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
    {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M'] [IsManifold I' ∞ M']
    {w : M' → E} (V : TopologicalSpace.Opens M')
    (hw : ∀ x ∈ V, ContMDiffAt I' 𝓘(ℝ, E) ∞ w x) (hne : ∀ x ∈ V, w x ≠ 0)
    {x : M'} (hx : x ∈ V) :
    ContMDiffAt I' 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) ∞ (fun x => nv0 (w x)) x := by
  have h1 : ContMDiff I' 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) ∞ (fun r : V => nv0 (w r.1)) :=
    contMDiff_nv0_comp (w := fun r : V => w r.1)
      (fun r => (hw r.1 r.2).comp r (contMDiff_subtype_val (I := I')).contMDiffAt)
      (fun r => hne r.1 r.2)
  exact (contMDiffAt_subtype_iff (I := I') (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin p))) (n := ∞)
    (U := V) (f := fun x => nv0 (w x)) (x := ⟨x, hx⟩)).1 (h1 ⟨x, hx⟩)

/-! ### The straight-line homotopy in stereographic coordinates -/

variable {EX : Type*} [NormedAddCommGroup EX] [NormedSpace ℝ EX] {HX : Type*} [TopologicalSpace HX]
  {IX : ModelWithCorners ℝ EX HX} {X : Type*} [TopologicalSpace X] [ChartedSpace HX X]
  [IsManifold IX ∞ X]

/-- Two smooth maps `f, g : X → Sᵖ` which agree on an open set `U` and never hit `y` outside `U`
are smoothly homotopic by a homotopy which is constant (equal to `f`) on `U`. -/
theorem exists_homotopy_of_eqOn {y : Sph p} {f g : X → Sph p}
    (hf : ContMDiff IX 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) ∞ f)
    (hg : ContMDiff IX 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) ∞ g)
    {U : Set X} (hU : IsOpen U) (hfg : ∀ x ∈ U, f x = g x)
    (hfy : ∀ x, x ∉ U → f x ≠ y) (hgy : ∀ x, x ∉ U → g x ≠ y) :
    ∃ H : X × ℝ → Sph p,
      ContMDiff (IX.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) ∞ H ∧
      (∀ x, H (x, 0) = f x) ∧ (∀ x, H (x, 1) = g x) ∧ (∀ x ∈ U, ∀ t, H (x, t) = f x) := by
  -- the ambient segment map and its image under inverse stereographic projection
  obtain ⟨Hamb, hHamb⟩ : ∃ Hamb : X × ℝ → E, ∀ q,
      Hamb q = (1 - q.2) • stereo y (f q.1).1 + q.2 • stereo y (g q.1).1 := ⟨_, fun _ => rfl⟩
  obtain ⟨Hs, hHs⟩ : ∃ Hs : X × ℝ → E, ∀ q, Hs q = stereoInv y (Hamb q) := ⟨_, fun _ => rfl⟩
  obtain ⟨H, hH⟩ : ∃ H : X × ℝ → Sph p, ∀ q, H q = if q.1 ∈ U then f q.1 else nv0 (Hs q) :=
    ⟨_, fun _ => rfl⟩
  have hHamb_inner : ∀ q, ⟪Hamb q, y.1⟫ = 0 := by
    intro q
    rw [hHamb, inner_add_left, real_inner_smul_left, real_inner_smul_left, inner_stereo_y,
      inner_stereo_y, mul_zero, mul_zero, add_zero]
  have hHs_mem : ∀ q, Hs q ∈ Sph p := fun q => by rw [hHs]; exact stereoInv_mem y (hHamb_inner q)
  have hHs_ne : ∀ q, Hs q ≠ 0 := fun q h => by
    have := mem_iff_norm.1 (hHs_mem q)
    rw [h, norm_zero] at this
    exact zero_ne_one this
  have hnv0 : ∀ q, nv0 (Hs q) = ⟨Hs q, hHs_mem q⟩ := fun q => Subtype.ext (by
    rw [nv0_val (hHs_ne q), normalize, mem_iff_norm.1 (hHs_mem q), inv_one, one_smul])
  -- values on the segment endpoints
  have hHs0 : ∀ x, x ∉ U → Hs (x, 0) = (f x).1 := by
    intro x hx
    rw [hHs, hHamb]
    simp only [sub_zero, one_smul, zero_smul, add_zero]
    exact stereoInv_stereo (hfy x hx)
  have hHs1 : ∀ x, x ∉ U → Hs (x, 1) = (g x).1 := by
    intro x hx
    rw [hHs, hHamb]
    simp only [sub_self, zero_smul, one_smul, zero_add]
    exact stereoInv_stereo (hgy x hx)
  -- on the open set `V = {f ≠ y ∧ g ≠ y} × ℝ`, `H = nv0 ∘ Hs`
  have hVo : IsOpen {q : X × ℝ | f q.1 ≠ y ∧ g q.1 ≠ y} :=
    IsOpen.inter ((isOpen_ne_fun hf.continuous continuous_const).preimage continuous_fst)
      ((isOpen_ne_fun hg.continuous continuous_const).preimage continuous_fst)
  have hH_V : ∀ q, f q.1 ≠ y → g q.1 ≠ y → H q = nv0 (Hs q) := by
    intro q hfq hgq
    rw [hH]
    split_ifs with hq
    · rw [hnv0]
      apply Subtype.ext
      show (f q.1).1 = Hs q
      rw [hHs, hHamb, ← hfg q.1 hq, ← add_smul, sub_add_cancel, one_smul, stereoInv_stereo hfq]
    · rfl
  refine ⟨H, ?_, ?_, ?_, ?_⟩
  · -- smoothness
    intro q
    by_cases hq : q.1 ∈ U
    · have h1 : ContMDiffAt (IX.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) ∞
          (fun q : X × ℝ => f q.1) q :=
        (hf.comp (contMDiff_fst (I := IX) (J := 𝓘(ℝ, ℝ)) (M := X) (N := ℝ))).contMDiffAt
      refine h1.congr_of_eventuallyEq ?_
      filter_upwards [(hU.preimage continuous_fst).mem_nhds hq] with q' hq'
      rw [hH, if_pos (show q'.1 ∈ U from hq')]
    · have hqV : q ∈ {q : X × ℝ | f q.1 ≠ y ∧ g q.1 ≠ y} := ⟨hfy _ hq, hgy _ hq⟩
      let V : TopologicalSpace.Opens (X × ℝ) := ⟨{q : X × ℝ | f q.1 ≠ y ∧ g q.1 ≠ y}, hVo⟩
      have hval : ContMDiff (IX.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) ∞ (fun q : X × ℝ => (f q.1).1) :=
        contMDiff_val.comp (hf.comp (contMDiff_fst (I := IX) (J := 𝓘(ℝ, ℝ)) (M := X) (N := ℝ)))
      have hval' : ContMDiff (IX.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) ∞ (fun q : X × ℝ => (g q.1).1) :=
        contMDiff_val.comp (hg.comp (contMDiff_fst (I := IX) (J := 𝓘(ℝ, ℝ)) (M := X) (N := ℝ)))
      have hsnd : ContMDiff (IX.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ (fun q : X × ℝ => q.2) :=
        contMDiff_snd (I := IX) (J := 𝓘(ℝ, ℝ)) (M := X) (N := ℝ)
      have hw : ∀ q' ∈ V, ContMDiffAt (IX.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) ∞ Hs q' := by
        intro q' hq'
        have hsf : ContMDiffAt (IX.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) ∞
            (fun q : X × ℝ => stereo y (f q.1).1) q' :=
          ContMDiffAt.comp (g := stereo y) (f := fun q : X × ℝ => (f q.1).1) q'
            (contDiffAt_stereo y (inner_lt_one_of_ne hq'.1)).contMDiffAt (hval q')
        have hsg : ContMDiffAt (IX.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) ∞
            (fun q : X × ℝ => stereo y (g q.1).1) q' :=
          ContMDiffAt.comp (g := stereo y) (f := fun q : X × ℝ => (g q.1).1) q'
            (contDiffAt_stereo y (inner_lt_one_of_ne hq'.2)).contMDiffAt (hval' q')
        have hamb : ContMDiffAt (IX.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) ∞ Hamb q' := by
          have hfun : Hamb = fun q => (1 - q.2) • stereo y (f q.1).1 + q.2 • stereo y (g q.1).1 := by
            funext q; exact hHamb q
          rw [hfun]
          exact ((contMDiff_const.sub hsnd).contMDiffAt.smul hsf).add (hsnd.contMDiffAt.smul hsg)
        have hfun : Hs = fun q => stereoInv y (Hamb q) := by funext q; exact hHs q
        rw [hfun]
        exact (contDiff_stereoInv y).contDiffAt.contMDiffAt.comp q' hamb
      have h1 : ContMDiffAt (IX.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) ∞
          (fun q => nv0 (Hs q)) q :=
        contMDiffAt_nv0_comp V hw (fun q' _ => hHs_ne q') hqV
      refine h1.congr_of_eventuallyEq ?_
      filter_upwards [hVo.mem_nhds hqV] with q' hq'
      exact hH_V q' hq'.1 hq'.2
  · -- `t = 0`
    intro x
    rw [hH]
    split_ifs with hx
    · rfl
    · rw [hnv0]
      exact Subtype.ext (hHs0 x hx)
  · -- `t = 1`
    intro x
    rw [hH]
    split_ifs with hx
    · exact hfg x hx
    · rw [hnv0]
      exact Subtype.ext (hHs1 x hx)
  · -- constant on `U`
    intro x hx t
    rw [hH, if_pos hx]

end Sphere

end Milnor
