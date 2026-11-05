import Morse
/-! Layer-2 blind definition of Morse_Homotopy_changeBaseEquiv. Textbook: Hatcher, *Algebraic
Topology*, §4.1 (change of base point, before Prop. 4.1: the map `β_γ`), Milnor, *Morse Theory*,
§17: for a path `γ` from `y₀` to `y₁`, a class `[f] ∈ π_n(Y, y₀)` is sent to `[γ·f]`, where `γ·f`
is `f` shrunk to a smaller concentric cube, with the path inserted along each radial segment of the
collar between that cube and `∂Iⁿ`; the inverse is the same construction for the reversed path.
Choices: homotopy groups are Mathlib's `HomotopyGroup N Y y` (generalized loops
`(I^N, ∂I^N) → (Y, y)` up to homotopy rel `∂I^N`). Radial structure via the sup-norm radius
`r(t) = maxᵢ |2tᵢ − 1|` (`∂I^N = {r = 1}`): `Φ_γ f = f ∘ (rescale by 2)` on `r ≤ 1/2`, and
`γ(2r − 1)` on `1/2 ≤ r ≤ 1` (so `γ` runs from `y₀` on the inner cube to `y₁` on `∂I^N`; in
Hatcher's notation, where `β_h : π_n(X, x₁) → π_n(X, x₀)` for `h` from `x₀` to `x₁`, this is
`β_{γ̄}`). `T γ = [f] ↦ [Φ_γ f]`, with inverse `[f] ↦ [Φ_{γ⁻¹} f]` (proved inverse here by
explicit homotopies). Only the bijection is required by the signature (it is a group isomorphism
for `N` nonempty, not recorded). For `N` empty (`π_0`), `r ≡ 0` and `Φ_γ f = f`: the identity on
path components, as expected. -/
namespace RoundTrip.L2.Morse_Homotopy_changeBaseEquiv

open scoped unitInterval Topology Topology.Homotopy

section Cube
variable {N : Type*}

/-- Centred coordinates `t ↦ (2 tᵢ - 1)ᵢ ∈ [-1, 1]^N`. -/
def ctr (t : I^N) : N → ℝ := fun i => 2 * (t i : ℝ) - 1

/-- Radial rescaling of the cube by the factor `k` about its centre, clamped to the cube. -/
noncomputable def sh (k : ℝ) (t : I^N) : I^N :=
  fun i => Set.projIcc 0 1 zero_le_one (k * ((t i : ℝ) - 1 / 2) + 1 / 2)

theorem continuous_ctr : Continuous (ctr : (I^N) → N → ℝ) := by
  unfold ctr; fun_prop

theorem continuous_sh : Continuous (fun q : ℝ × (I^N) => sh q.1 q.2) := by
  unfold sh
  refine continuous_pi fun i => continuous_projIcc.comp ?_
  fun_prop

theorem sh_mem_boundary_of_mem {t : I^N} {k : ℝ} (hk : 1 ≤ k) (ht : t ∈ Cube.boundary N) :
    sh k t ∈ Cube.boundary N := by
  obtain ⟨i, hi⟩ := ht
  refine ⟨i, ?_⟩
  rcases hi with hi | hi
  · left; simp only [sh, hi]; rw [Set.projIcc_of_le_left]; · rfl
    · simp; nlinarith
  · right; simp only [sh, hi]; rw [Set.projIcc_of_right_le]; · rfl
    · simp; nlinarith

theorem sh_one (t : I^N) : sh 1 t = t := by
  funext i; simp [sh]

end Cube

section Radius
variable {N : Type*} [Fintype N] {Y : Type*} [TopologicalSpace Y]

/-- Sup-norm radius `r(t) = maxᵢ |2 tᵢ - 1|` (`0` for `N` empty); `∂I^N = {r = 1}`. -/
noncomputable def rad (t : I^N) : ℝ := ‖ctr t‖

theorem continuous_rad : Continuous (rad : (I^N) → ℝ) :=
  continuous_norm.comp continuous_ctr

theorem abs_ctr_le_rad (t : I^N) (i : N) : |ctr t i| ≤ rad t := by
  have := norm_le_pi_norm (ctr t) i
  simpa [rad, Real.norm_eq_abs] using this

theorem rad_le_one (t : I^N) : rad t ≤ 1 := by
  unfold rad
  refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => ?_
  rw [Real.norm_eq_abs, abs_le]
  have h0 := (t i).2.1; have h1 := (t i).2.2
  simp only [ctr]; constructor <;> linarith

theorem rad_eq_one_of_mem_boundary {t : I^N} (ht : t ∈ Cube.boundary N) : rad t = 1 := by
  obtain ⟨i, hi⟩ := ht
  refine le_antisymm (rad_le_one t) ?_
  have := abs_ctr_le_rad t i
  rcases hi with hi | hi <;> simp [ctr, hi] at this <;> norm_num at this <;> linarith

/-- If `a ≤ r(t)` with `a > 0`, rescaling by `a⁻¹` sends `t` to the boundary. -/
theorem sh_mem_boundary {t : I^N} {a : ℝ} (ha : 0 < a) (h : a ≤ rad t) :
    sh a⁻¹ t ∈ Cube.boundary N := by
  have : ¬ ∀ i, ‖ctr t i‖ < a := by
    rw [← pi_norm_lt_iff ha]; exact not_lt.2 h
  simp only [not_forall, not_lt] at this
  obtain ⟨i, hi⟩ := this
  refine ⟨i, ?_⟩
  rw [Real.norm_eq_abs, le_abs] at hi
  simp only [ctr] at hi
  rcases hi with hi | hi
  · right
    simp only [sh]
    rw [Set.projIcc_of_right_le]
    · rfl
    · have : a⁻¹ * ((t i : ℝ) - 1 / 2) ≥ 1 / 2 := by
        rw [ge_iff_le, ← sub_nonneg]
        have : a⁻¹ * ((t i : ℝ) - 1 / 2) - 1 / 2 = a⁻¹ * ((2 * (t i : ℝ) - 1 - a) / 2) := by
          field_simp
        rw [this]; positivity
      linarith
  · left
    simp only [sh]
    rw [Set.projIcc_of_le_left]
    · rfl
    · have : a⁻¹ * ((t i : ℝ) - 1 / 2) ≤ -(1 / 2) := by
        rw [← sub_nonneg]
        have : -(1 / 2) - a⁻¹ * ((t i : ℝ) - 1 / 2) = a⁻¹ * ((-(2 * (t i : ℝ) - 1) - a) / 2) := by
          field_simp; ring
        rw [this]; apply mul_nonneg (inv_nonneg.2 ha.le); linarith
      linarith

/-- The collar construction: `F` rescaled into the inner cube `r ≤ a`, and `p (r t)` on the
collar `r ≥ a` (so `p` runs along the radial segments). -/
noncomputable def collar (F : (I^N) → Y) (a : ℝ) (p : ℝ → Y) (t : I^N) : Y :=
  if rad t ≤ a then F (sh a⁻¹ t) else p (rad t)

theorem continuous_collar {S : Type*} [TopologicalSpace S] {F : S → (I^N) → Y}
    (hF : Continuous (fun q : S × (I^N) => F q.1 q.2)) {a : S → ℝ} (ha : Continuous a)
    (ha0 : ∀ s, 0 < a s) {p : S → ℝ → Y} (hp : Continuous (fun q : S × ℝ => p q.1 q.2))
    (hFp : ∀ s, ∀ t ∈ Cube.boundary N, F s t = p s (a s)) :
    Continuous (fun q : S × (I^N) => collar (F q.1) (a q.1) (p q.1) q.2) := by
  unfold collar
  refine Continuous.if_le ?_ ?_ (continuous_rad.comp continuous_snd) (ha.comp continuous_fst) ?_
  · have h1 : Continuous (fun q : S × (I^N) => (a q.1)⁻¹) :=
      (ha.comp continuous_fst).inv₀ fun q => (ha0 q.1).ne'
    exact hF.comp (continuous_fst.prodMk (continuous_sh.comp (h1.prodMk continuous_snd)))
  · exact hp.comp (continuous_fst.prodMk (continuous_rad.comp continuous_snd))
  · rintro ⟨s, t⟩ h
    simp only at h ⊢
    rw [hFp s _ (sh_mem_boundary (ha0 s) h.ge), h]

variable {y₀ y₁ : Y}

/-- `Φ_γ f`: `f` on the inner cube `r ≤ 1/2` (rescaled by `2`), and `γ` along each radial
segment of the collar `1/2 ≤ r ≤ 1`, from `γ 0 = y₀` at `r = 1/2` to `γ 1 = y₁` on `∂I^N`. -/
noncomputable def chgFun (γ : Path y₀ y₁) (f : (I^N) → Y) : (I^N) → Y :=
  collar f (1 / 2) (fun u => γ.extend (2 * u - 1))

theorem chgFun_boundary (γ : Path y₀ y₁) (f : (I^N) → Y) {t : I^N} (ht : t ∈ Cube.boundary N) :
    chgFun γ f t = y₁ := by
  simp only [chgFun, collar, rad_eq_one_of_mem_boundary ht]
  norm_num

/-- `Φ_γ` on generalized loops: `Ω^N(Y, y₀) → Ω^N(Y, y₁)`. -/
noncomputable def chg (γ : Path y₀ y₁) (f : Ω^ N Y y₀) : Ω^ N Y y₁ :=
  ⟨⟨chgFun γ f, by
    have := continuous_collar (S := Unit) (F := fun _ => (f : (I^N) → Y)) (a := fun _ => 1 / 2)
      (p := fun _ u => γ.extend (2 * u - 1)) (f.1.continuous.comp continuous_snd)
      continuous_const (fun _ => by norm_num)
      (γ.continuous_extend.comp (by fun_prop)) (fun _ t ht => by
        simp [GenLoop.boundary f t ht])
    exact this.comp (f := fun t : (I^N) => ((), t)) (by fun_prop)⟩,
    fun t ht => chgFun_boundary γ f ht⟩

theorem chg_apply (γ : Path y₀ y₁) (f : Ω^ N Y y₀) (t : I^N) : chg γ f t = chgFun γ f t := rfl

/-- `Φ_γ` respects homotopy rel `∂I^N`. -/
theorem chg_homotopic (γ : Path y₀ y₁) {f g : Ω^ N Y y₀} (h : GenLoop.Homotopic f g) :
    GenLoop.Homotopic (chg γ f) (chg γ g) := by
  obtain ⟨H⟩ := h
  refine ⟨{
    toFun := fun q => collar (fun t => H (q.1, t)) (1 / 2) (fun u => γ.extend (2 * u - 1)) q.2
    continuous_toFun := continuous_collar (F := fun s t => H (s, t)) (a := fun _ => 1 / 2)
      (p := fun _ u => γ.extend (2 * u - 1)) H.continuous continuous_const
      (fun _ => by norm_num) (γ.continuous_extend.comp (by fun_prop)) (fun s t ht => by
        rw [H.eq_fst s ht]; simp [GenLoop.boundary f t ht])
    map_zero_left := fun t => by simp [chg_apply, chgFun]
    map_one_left := fun t => by simp [chg_apply, chgFun]
    prop' := fun s t ht => by
      change collar (fun t => H (s, t)) (1 / 2) (fun u => γ.extend (2 * u - 1)) t = chgFun γ f t
      rw [chgFun_boundary γ f ht]
      simp only [collar, rad_eq_one_of_mem_boundary ht]
      norm_num }⟩

theorem sh_two_val {t : I^N} (h : rad t ≤ 1 / 2) (i : N) :
    (sh 2 t i : ℝ) = 2 * (t i : ℝ) - 1 / 2 := by
  have := abs_ctr_le_rad t i
  rw [abs_le] at this
  simp only [ctr] at this
  simp only [sh]
  rw [Set.projIcc_of_mem]
  · ring
  · constructor <;> linarith

theorem rad_sh_two {t : I^N} (h : rad t ≤ 1 / 2) : rad (sh 2 t) = 2 * rad t := by
  have : ctr (sh 2 t) = (2 : ℝ) • ctr t := by
    funext i; simp only [ctr, sh_two_val h, Pi.smul_apply, smul_eq_mul]; ring
  simp only [rad, this, norm_smul, Real.norm_two]

theorem sh_two_sh_two {t : I^N} (h : rad t ≤ 1 / 2) : sh 2 (sh 2 t) = sh 4 t := by
  funext i
  simp only [sh]
  rw [show ((Set.projIcc 0 1 zero_le_one (2 * ((t i : ℝ) - 1 / 2) + 1 / 2) : I) : ℝ)
      = 2 * (t i : ℝ) - 1 / 2 from sh_two_val h i]
  congr 2; ring

theorem chgFun_symm_chgFun (γ : Path y₀ y₁) (f : (I^N) → Y) (t : I^N) :
    chgFun γ.symm (chgFun γ f) t =
      collar f (1 / 4) (fun u => γ.extend (min (4 * u - 1) (2 - 2 * u))) t := by
  simp only [chgFun, collar]
  have e2 : ((1 : ℝ) / 2)⁻¹ = 2 := by norm_num
  have e4 : ((1 : ℝ) / 4)⁻¹ = 4 := by norm_num
  rw [e2, e4]
  by_cases h1 : rad t ≤ 1 / 4
  · have h1' : rad t ≤ 1 / 2 := by linarith
    rw [if_pos h1', rad_sh_two h1', if_pos (by linarith), sh_two_sh_two h1', if_pos h1]
  · by_cases h2 : rad t ≤ 1 / 2
    · rw [if_pos h2, rad_sh_two h2, if_neg (by linarith), if_neg h1]
      congr 1; rw [min_eq_left (by linarith)]; ring
    · rw [if_neg h2, if_neg h1, Path.extend_symm_apply]
      congr 1; rw [min_eq_right (by linarith)]; ring

/-- `f` rescaled into the cube `r ≤ 1/4` (constant `y₀` outside). -/
noncomputable def shrink4 (f : Ω^ N Y y₀) : C(I^N, Y) :=
  ⟨fun t => f (sh 4 t), f.1.continuous.comp
    (continuous_sh.comp (Continuous.prodMk continuous_const continuous_id))⟩

/-- First homotopy: contract the radial loop `γ · γ⁻¹` of `Φ_{γ⁻¹} Φ_γ f` to the constant `y₀`. -/
noncomputable def homA (γ : Path y₀ y₁) (f : Ω^ N Y y₀) :
    ContinuousMap.HomotopyRel (chg γ.symm (chg γ f)).1 (shrink4 f) (Cube.boundary N) where
  toFun q :=
    collar f (1 / 4) (fun u => γ.extend ((1 - (q.1 : ℝ)) * min (4 * u - 1) (2 - 2 * u))) q.2
  continuous_toFun := continuous_collar (F := fun (_ : I) t => f t) (a := fun _ => 1 / 4)
    (p := fun s u => γ.extend ((1 - (s : ℝ)) * min (4 * u - 1) (2 - 2 * u)))
    (f.1.continuous.comp continuous_snd) continuous_const (fun _ => by norm_num)
    (γ.continuous_extend.comp (by fun_prop)) (fun s t ht => by
      rw [GenLoop.boundary f t ht]; norm_num)
  map_zero_left t := by
    change collar f (1 / 4) _ t = chgFun γ.symm (chgFun γ f) t
    rw [chgFun_symm_chgFun]; simp
  map_one_left t := by
    change collar f (1 / 4) _ t = f (sh 4 t)
    simp only [collar, Set.Icc.coe_one, sub_self, zero_mul, Path.extend_zero]
    have e4 : ((1 : ℝ) / 4)⁻¹ = 4 := by norm_num
    rw [e4]
    split_ifs with h
    · rfl
    · have hb : sh ((1 : ℝ) / 4)⁻¹ t ∈ Cube.boundary N :=
        sh_mem_boundary (by norm_num) (by linarith)
      rw [e4] at hb
      rw [GenLoop.boundary f _ hb]
  prop' s t ht := by
    change collar f (1 / 4) (fun u => γ.extend ((1 - (s : ℝ)) * min (4 * u - 1) (2 - 2 * u))) t =
      chgFun γ.symm (chgFun γ f) t
    rw [chgFun_boundary γ.symm _ ht]
    simp only [collar, rad_eq_one_of_mem_boundary ht]
    norm_num

/-- Second homotopy: expand the inner cube from `r ≤ 1/4` back to the whole cube. -/
noncomputable def homB (f : Ω^ N Y y₀) :
    ContinuousMap.HomotopyRel (shrink4 f) f.1 (Cube.boundary N) where
  toFun q := f (sh (1 / 4 + 3 / 4 * (q.1 : ℝ))⁻¹ q.2)
  continuous_toFun := by
    refine f.1.continuous.comp (continuous_sh.comp (Continuous.prodMk ?_ continuous_snd))
    refine Continuous.inv₀ (by fun_prop) fun q => ?_
    have := q.1.2.1; positivity
  map_zero_left t := by
    change f (sh _ t) = f (sh 4 t)
    norm_num
  map_one_left t := by
    change f (sh _ t) = f t
    norm_num [sh_one]
  prop' s t ht := by
    change f (sh _ t) = f (sh 4 t)
    have hs0 := s.2.1; have hs1 := s.2.2
    have hk : (1 : ℝ) ≤ (1 / 4 + 3 / 4 * (s : ℝ))⁻¹ := by
      rw [one_le_inv₀ (by positivity)]; linarith
    rw [GenLoop.boundary f _ (sh_mem_boundary_of_mem hk ht),
      GenLoop.boundary f _ (sh_mem_boundary_of_mem (k := 4) (by norm_num) ht)]

theorem chg_symm_chg (γ : Path y₀ y₁) (f : Ω^ N Y y₀) :
    GenLoop.Homotopic (chg γ.symm (chg γ f)) f :=
  ContinuousMap.HomotopicRel.trans ⟨homA γ f⟩ ⟨homB f⟩

/-- The change-of-base-point bijection `π_N(Y, y₀) ≃ π_N(Y, y₁)` along `γ`. -/
noncomputable def T (γ : Path y₀ y₁) : HomotopyGroup N Y y₀ ≃ HomotopyGroup N Y y₁ where
  toFun := Quotient.map' (chg γ) (fun _ _ h => chg_homotopic γ h)
  invFun := Quotient.map' (chg γ.symm) (fun _ _ h => chg_homotopic γ.symm h)
  left_inv := by
    rintro ⟨f⟩
    exact Quotient.sound (chg_symm_chg γ f)
  right_inv := by
    rintro ⟨f⟩
    have := chg_symm_chg γ.symm f
    rw [Path.symm_symm] at this
    exact Quotient.sound this

end Radius

end RoundTrip.L2.Morse_Homotopy_changeBaseEquiv
