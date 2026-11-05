import Milnor.Chapter6.Radial
import Milnor.Chapter6.LevelZero

/-!
# Orientations from complementary frames

Let `S` be a manifold of dimension `d` (modelled on `Z`), immersed in a vector space `E` of
dimension `d + k` by `ι : S → E`, and let `ν : S → Eᵏ` be a continuous family of `k`-frames
complementary to the tangent spaces.  For an orientation `o` of `E`, represented by a volume
form `Ω`, a basis `z` of `T_qS` is declared positive iff
`Ω(ν₁(q), …, ν_k(q), dι z₁, …, dι z_d) > 0`.

* `frameCurry Ω ν`: the `d`-form `w ↦ Ω(ν₀, …, ν_{k-1}, w₀, …, w_{d-1})`;
* `frameForm Ω ν T`: its pullback along a linear map `T : Z → E`;
* `frameOr`: the orientation of `Z` it represents;
* `Orient.ofFrame`: the resulting orientation of `S` (continuity by a chart argument);
* `signAt_ofFrame`: an ambient formula for the sign of a map between two such manifolds;
* `Orient.eq_or_eq_neg`: on a connected manifold two orientations agree or are opposite;
* `Sphere.sphOrStd`: Milnor's orientation of `Sⁿ` as the boundary of the disk ("outward normal
  first") for the standard orientation of `ℝⁿ⁺¹`; it is `± sphOr n`, and the antipodal map has
  degree `(-1)ⁿ⁺¹` for it.
-/

open Set Filter Topology Function Module
open scoped ContDiff Manifold RealInnerProductSpace

noncomputable section

namespace Milnor

/-! ### Inserting a frame in front of a tuple -/

section tuple

variable {α : Type*} {d : ℕ}

/-- The tuple `(ν₀, …, ν_{k-1}, w₀, …, w_{d-1})`, indexed by `Fin (d + k)`. -/
def frameTuple : {k : ℕ} → (Fin k → α) → (Fin d → α) → Fin (d + k) → α
  | 0, _, w => w
  | k + 1, ν, w => (Matrix.vecCons (ν 0) (frameTuple (Fin.tail ν) w) : Fin (d + k + 1) → α)

theorem frameTuple_zero (ν : Fin 0 → α) (w : Fin d → α) : frameTuple ν w = w := rfl

theorem frameTuple_succ {k : ℕ} (ν : Fin (k + 1) → α) (w : Fin d → α) :
    frameTuple ν w = (Matrix.vecCons (ν 0) (frameTuple (Fin.tail ν) w) : Fin (d + k + 1) → α) :=
  rfl

theorem frameTuple_one (v : α) (w : Fin d → α) : frameTuple ![v] w = Matrix.vecCons v w := rfl

theorem continuous_frameTuple [TopologicalSpace α] :
    ∀ {k : ℕ}, Continuous (fun p : (Fin k → α) × (Fin d → α) => frameTuple p.1 p.2)
  | 0 => continuous_snd
  | k + 1 => by
    have h1 : Continuous (fun p : (Fin (k + 1) → α) × (Fin d → α) => p.1 0) :=
      (continuous_apply 0).comp continuous_fst
    have h2 : Continuous (fun p : (Fin (k + 1) → α) × (Fin d → α) => (Fin.tail p.1, p.2)) :=
      ((continuous_pi fun i => (continuous_apply i.succ).comp continuous_fst)).prodMk
        continuous_snd
    exact h1.matrixVecCons ((continuous_frameTuple (k := k)).comp h2)

end tuple

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] {d : ℕ}

/-! ### Inserting a frame in front of a form -/

/-- Insert `k` frame vectors in front: `frameCurry Ω ν w = Ω(ν₀, …, ν_{k-1}, w₀, …, w_{d-1})`.
Defined by recursion on `k` with `curryLeft`, using that `d + (k+1) = (d + k) + 1`
definitionally. -/
def frameCurry : {k : ℕ} → (E [⋀^Fin (d + k)]→ₗ[ℝ] ℝ) → (Fin k → E) → (E [⋀^Fin d]→ₗ[ℝ] ℝ)
  | 0, Ω, _ => Ω
  | k + 1, Ω, ν => frameCurry ((Ω : E [⋀^Fin (d + k + 1)]→ₗ[ℝ] ℝ).curryLeft (ν 0)) (Fin.tail ν)

theorem frameCurry_zero (Ω : E [⋀^Fin (d + 0)]→ₗ[ℝ] ℝ) (ν : Fin 0 → E) :
    frameCurry Ω ν = Ω := rfl

theorem frameCurry_succ {k : ℕ} (Ω : E [⋀^Fin (d + (k + 1))]→ₗ[ℝ] ℝ) (ν : Fin (k + 1) → E) :
    frameCurry Ω ν =
      frameCurry ((Ω : E [⋀^Fin (d + k + 1)]→ₗ[ℝ] ℝ).curryLeft (ν 0)) (Fin.tail ν) := rfl

theorem frameCurry_apply {k : ℕ} (Ω : E [⋀^Fin (d + k)]→ₗ[ℝ] ℝ) (ν : Fin k → E)
    (w : Fin d → E) : frameCurry Ω ν w = Ω (frameTuple ν w) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [frameCurry_succ, ih, AlternatingMap.curryLeft_apply_apply]
    rfl

theorem frameCurry_smul {k : ℕ} (c : ℝ) (Ω : E [⋀^Fin (d + k)]→ₗ[ℝ] ℝ) (ν : Fin k → E) :
    frameCurry (c • Ω) ν = c • frameCurry Ω ν := by
  ext w
  rw [frameCurry_apply, AlternatingMap.smul_apply, AlternatingMap.smul_apply, frameCurry_apply]

/-- A top-degree form is a continuous function of its arguments. -/
theorem continuous_alternatingMap_of_finrank [FiniteDimensional ℝ E] {m : ℕ}
    (hE : finrank ℝ E = m) (Ω : E [⋀^Fin m]→ₗ[ℝ] ℝ) : Continuous (fun v : Fin m → E => Ω v) := by
  set e := finBasisOfFinrankEq ℝ E hE
  have h1 : (fun v : Fin m → E => Ω v) = fun v => Ω e * (e.toMatrix v).det := funext fun v => by
    conv_lhs => rw [Ω.eq_smul_basis_det e]
    rw [AlternatingMap.smul_apply, smul_eq_mul, Basis.det_apply]
  have houter : Continuous (fun v : Fin m → E => e.toMatrix v) := by
    refine continuous_matrix fun i j => ?_
    simp only [Basis.toMatrix_apply]
    exact ((e.coord i).continuous_of_finiteDimensional).comp (continuous_apply j)
  rw [h1]
  exact continuous_const.mul (continuous_id.matrix_det.comp houter)

/-! ### The form of a frame along a linear map -/

/-- The `d`-form `z ↦ Ω(ν₀, …, ν_{k-1}, T z₀, …, T z_{d-1})` on `Z`. -/
def frameForm {k : ℕ} (Ω : E [⋀^Fin (d + k)]→ₗ[ℝ] ℝ) (ν : Fin k → E) (T : Z →L[ℝ] E) :
    Z [⋀^Fin d]→ₗ[ℝ] ℝ :=
  (frameCurry Ω ν).compLinearMap T.toLinearMap

theorem frameForm_apply {k : ℕ} (Ω : E [⋀^Fin (d + k)]→ₗ[ℝ] ℝ) (ν : Fin k → E) (T : Z →L[ℝ] E)
    (z : Fin d → Z) : frameForm Ω ν T z = Ω (frameTuple ν fun i => T (z i)) :=
  frameCurry_apply Ω ν _

theorem frameForm_smul {k : ℕ} (c : ℝ) (Ω : E [⋀^Fin (d + k)]→ₗ[ℝ] ℝ) (ν : Fin k → E)
    (T : Z →L[ℝ] E) : frameForm (c • Ω) ν T = c • frameForm Ω ν T := by
  ext z
  rw [AlternatingMap.smul_apply, frameForm_apply, frameForm_apply, AlternatingMap.smul_apply]

theorem frameForm_comp {k : ℕ} (Ω : E [⋀^Fin (d + k)]→ₗ[ℝ] ℝ) (ν : Fin k → E) (T : Z →L[ℝ] E)
    {Z' : Type*} [NormedAddCommGroup Z'] [NormedSpace ℝ Z'] (D : Z' →L[ℝ] Z) :
    (frameForm Ω ν T).compLinearMap D.toLinearMap = frameForm Ω ν (T.comp D) := rfl

/-- For a single vector the frame form is the contraction `contractForm` of `LevelOrient`. -/
theorem frameForm_one (Ω : E [⋀^Fin (d + 1)]→ₗ[ℝ] ℝ) (v : E) (T : Z →L[ℝ] E) :
    frameForm Ω ![v] T = contractForm Ω v T := rfl

open Classical in
/-- The orientation of `Z` defined by the frame (a default value when the form vanishes). -/
def frameOr [FiniteDimensional ℝ Z] {k : ℕ} (hZ : finrank ℝ Z = d)
    (o : Orientation ℝ E (Fin (d + k))) (ν : Fin k → E) (T : Z →L[ℝ] E) :
    Orientation ℝ Z (Fin d) :=
  if h : frameForm o.someVector ν T ≠ 0 then rayOfNeZero ℝ _ h
  else (finBasisOfFinrankEq ℝ Z hZ).orientation

/-- Any positive volume form of `E` represents `frameOr` after inserting the frame. -/
theorem frameOr_eq [FiniteDimensional ℝ Z] {k : ℕ} (hZ : finrank ℝ Z = d)
    {o : Orientation ℝ E (Fin (d + k))} {Ω : E [⋀^Fin (d + k)]→ₗ[ℝ] ℝ} (hΩ : Ω ≠ 0)
    (ho : rayOfNeZero ℝ Ω hΩ = o) {ν : Fin k → E} {T : Z →L[ℝ] E} (h : frameForm Ω ν T ≠ 0) :
    frameOr hZ o ν T = rayOfNeZero ℝ (frameForm Ω ν T) h := by
  have h1 : SameRay ℝ Ω o.someVector :=
    (ray_eq_iff hΩ o.someVector_ne_zero).1 (by rw [ho, Module.Ray.someVector_ray])
  obtain ⟨r, hr, hrΩ⟩ := h1.exists_pos_left hΩ o.someVector_ne_zero
  have h2 : frameForm o.someVector ν T = r • frameForm Ω ν T := by
    rw [← hrΩ, frameForm_smul]
  have h3 : frameForm o.someVector ν T ≠ 0 := by
    rw [h2]; exact smul_ne_zero hr.ne' h
  unfold frameOr
  rw [dif_pos h3, ray_eq_iff, h2]
  exact SameRay.sameRay_pos_smul_left (frameForm Ω ν T) hr

theorem frameOr_eq_someVector [FiniteDimensional ℝ Z] {k : ℕ} (hZ : finrank ℝ Z = d)
    (o : Orientation ℝ E (Fin (d + k))) {ν : Fin k → E} {T : Z →L[ℝ] E}
    (h : frameForm o.someVector ν T ≠ 0) :
    frameOr hZ o ν T = rayOfNeZero ℝ (frameForm o.someVector ν T) h :=
  frameOr_eq hZ o.someVector_ne_zero (Module.Ray.someVector_ray o) h

/-- For a single vector the frame orientation is `contractOr` of `LevelOrient`. -/
theorem frameOr_one [FiniteDimensional ℝ E] [FiniteDimensional ℝ Z] (hZ : finrank ℝ Z = d)
    (o : Orientation ℝ E (Fin (d + 1))) (v : E) (T : Z →L[ℝ] E) :
    frameOr hZ o ![v] T = contractOr hZ o v T := rfl

/-- **Nondegeneracy criterion**: the frame form does not vanish on `z` if
`(ν₀, …, ν_{k-1}, T z₀, …, T z_{d-1})` is linearly independent (`dim E = d + k`). -/
theorem frameForm_apply_ne_zero_of_linearIndependent [FiniteDimensional ℝ E] {k : ℕ}
    (hE : finrank ℝ E = d + k) {Ω : E [⋀^Fin (d + k)]→ₗ[ℝ] ℝ} (hΩ : Ω ≠ 0) {ν : Fin k → E}
    {T : Z →L[ℝ] E} {z : Fin d → Z} (h : LinearIndependent ℝ (frameTuple ν fun i => T (z i))) :
    frameForm Ω ν T z ≠ 0 := by
  rw [frameForm_apply]
  rcases Nat.eq_zero_or_pos (d + k) with h0 | h0
  · -- a form in no variables is a nonzero constant
    have : IsEmpty (Fin (d + k)) := by rw [h0]; infer_instance
    obtain ⟨v, hv⟩ := exists_ne_zero_of_ne_zero hΩ
    rwa [Subsingleton.elim (frameTuple ν fun i => T (z i)) v]
  · have : Nonempty (Fin (d + k)) := ⟨⟨0, h0⟩⟩
    let b : Basis (Fin (d + k)) ℝ E :=
      basisOfLinearIndependentOfCardEqFinrank h (by rw [Fintype.card_fin, hE])
    have hb : ⇑b = frameTuple ν fun i => T (z i) :=
      coe_basisOfLinearIndependentOfCardEqFinrank _ _
    rw [← hb]
    exact ne_zero_of_basis hΩ b

/-! ### The orientation of a manifold with a complementary frame -/

section manifold

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ Z]
  {S : Type*} [TopologicalSpace S] [ChartedSpace Z S] [IsManifold 𝓘(ℝ, Z) ∞ S]

/-- **Continuity of the frame orientation**: the chart at `q₀` carries the frame orientation at
nearby points to the one at `q₀`. -/
theorem Orient.ofFrame_cont {k : ℕ} (hZ : finrank ℝ Z = d) (hE : finrank ℝ E = d + k)
    (o : Orientation ℝ E (Fin (d + k))) {ι : S → E} (hι : ContMDiff 𝓘(ℝ, Z) 𝓘(ℝ, E) ∞ ι)
    {ν : S → Fin k → E} (hν : Continuous ν)
    (hnd : ∀ q, frameForm o.someVector (ν q) (mfd 𝓘(ℝ, Z) 𝓘(ℝ, E) ι q) ≠ 0) (q₀ : S) :
    ∀ᶠ q in 𝓝 q₀, orSign (frameOr hZ o (ν q) (mfd 𝓘(ℝ, Z) 𝓘(ℝ, E) ι q))
      (frameOr hZ o (ν q₀) (mfd 𝓘(ℝ, Z) 𝓘(ℝ, E) ι q₀))
      (mfd 𝓘(ℝ, Z) 𝓘(ℝ, Z) (extChartAt 𝓘(ℝ, Z) q₀) q) = 1 := by
  -- the chart at `q₀` and the parametrization `ψ = ι ∘ c₀⁻¹`
  set c₀ := extChartAt 𝓘(ℝ, Z) q₀ with hc₀
  obtain ⟨ψ, hψdef⟩ : ∃ ψ : Z → E, ψ = fun z => ι (c₀.symm z) := ⟨_, rfl⟩
  have hψ : ContDiffOn ℝ ∞ ψ c₀.target := by
    rw [hψdef, ← contMDiffOn_iff_contDiffOn]
    exact hι.comp_contMDiffOn (contMDiffOn_extChartAt_symm (I := 𝓘(ℝ, Z)) q₀)
  have hψd : ContinuousOn (fderiv ℝ ψ) c₀.target :=
    hψ.continuousOn_fderiv_of_isOpen (isOpen_extChartAt_target q₀) (by simp)
  -- chain rule: `dι_q = dψ_{c₀ q} ∘ dc₀_q`
  have hchain : ∀ q ∈ c₀.source, mfd 𝓘(ℝ, Z) 𝓘(ℝ, E) ι q =
      (fderiv ℝ ψ (c₀ q)).comp (mfd 𝓘(ℝ, Z) 𝓘(ℝ, Z) c₀ q) := by
    intro q hq
    have hψq : HasMFDerivAt 𝓘(ℝ, Z) 𝓘(ℝ, E) ψ (c₀ q) (fderiv ℝ ψ (c₀ q)) :=
      ((hψ.contDiffAt ((isOpen_extChartAt_target q₀).mem_nhds (c₀.map_source hq))).differentiableAt
        (by simp)).hasFDerivAt.hasMFDerivAt
    have hc := hasMFDerivAt_mfd (I := 𝓘(ℝ, Z)) (J := 𝓘(ℝ, Z)) ((contMDiffAt_extChartAt'
      (I := 𝓘(ℝ, Z)) (n := ∞) (x := q₀)
      (by rwa [← extChartAt_source 𝓘(ℝ, Z)] : q ∈ (chartAt Z q₀).source)).mdifferentiableAt
        (by simp))
    have h1 := hψq.comp q hc
    have h2 : ι =ᶠ[𝓝 q] (ψ ∘ c₀) := by
      filter_upwards [(isOpen_extChartAt_source q₀).mem_nhds hq] with z hz
      simp only [Function.comp, hψdef]
      rw [c₀.left_inv hz]
    exact HasMFDerivAt.mfd_eq (h1.congr_of_eventuallyEq h2)
  -- the family of `d`-forms `Φ q = frameForm Ω (ν q) (dψ_{c₀ q})`
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : S → (Z [⋀^Fin d]→ₗ[ℝ] ℝ),
      Φ = fun q => frameForm o.someVector (ν q) (fderiv ℝ ψ (c₀ q)) := ⟨_, rfl⟩
  have hrepΦ : ∀ q ∈ c₀.source, frameForm o.someVector (ν q) (mfd 𝓘(ℝ, Z) 𝓘(ℝ, E) ι q) =
      (Φ q).compLinearMap (mfd 𝓘(ℝ, Z) 𝓘(ℝ, Z) c₀ q).toLinearMap := by
    intro q hq
    rw [hchain q hq, hΦ, frameForm_comp]
  have hq₀src : q₀ ∈ c₀.source := mem_extChartAt_source q₀
  have hΦ₀ : Φ q₀ = frameForm o.someVector (ν q₀) (mfd 𝓘(ℝ, Z) 𝓘(ℝ, E) ι q₀) := by
    rw [hrepΦ q₀ hq₀src, mfd_extChartAt_self]
    simp only [ContinuousLinearMap.coe_id, AlternatingMap.compLinearMap_id]
  set u₀ := finBasisOfFinrankEq ℝ Z hZ with hu₀
  have hΦ₀u : Φ q₀ u₀ ≠ 0 := by rw [hΦ₀]; exact ne_zero_of_basis (hnd q₀) u₀
  have hΦ₀ne : Φ q₀ ≠ 0 := fun h => hΦ₀u (by rw [h]; rfl)
  -- continuity of `q ↦ Φ q u₀`
  have hLcont : ContinuousOn (fun q => Φ q u₀) c₀.source := by
    have hfd : ContinuousOn (fun q => fderiv ℝ ψ (c₀ q)) c₀.source :=
      hψd.comp (continuousOn_extChartAt q₀) (fun q hq => c₀.map_source hq)
    have hw : ContinuousOn (fun q => fun i => fderiv ℝ ψ (c₀ q) (u₀ i)) c₀.source :=
      continuousOn_pi.2 fun i => hfd.clm_apply continuousOn_const
    have h1 : (fun q => Φ q u₀) =
        fun q => o.someVector (frameTuple (ν q) fun i => fderiv ℝ ψ (c₀ q) (u₀ i)) := by
      funext q; rw [hΦ, frameForm_apply]
    rw [h1]
    exact (continuous_alternatingMap_of_finrank hE o.someVector).comp_continuousOn
      (continuous_frameTuple.comp_continuousOn (hν.continuousOn.prodMk hw))
  -- eventually `Φ q u₀` has the sign of `Φ q₀ u₀`
  have hev : ∀ᶠ q in 𝓝 q₀, 0 < Φ q u₀ * Φ q₀ u₀ := by
    have hc := hLcont.continuousAt ((isOpen_extChartAt_source q₀).mem_nhds hq₀src)
    rcases lt_or_gt_of_ne hΦ₀u with hneg | hpos
    · filter_upwards [hc.eventually_lt continuousAt_const hneg] with q hq
      exact mul_pos_of_neg_of_neg hq hneg
    · filter_upwards [continuousAt_const.eventually_lt hc hpos] with q hq
      exact mul_pos hq hpos
  filter_upwards [(isOpen_extChartAt_source q₀).mem_nhds hq₀src, hev] with q hq hpos
  -- `Φ q = c • Φ q₀` with `c > 0`
  obtain ⟨c, hc⟩ := exists_eq_smul_of_finrank hZ hΦ₀ne (Φ q)
  have hcpos : 0 < c := by
    have h1 : Φ q u₀ * Φ q₀ u₀ = (Φ q₀ u₀ * Φ q₀ u₀) * c := by
      rw [hc, AlternatingMap.smul_apply, smul_eq_mul]; ring
    rw [h1] at hpos
    exact (pos_iff_pos_of_mul_pos hpos).mp (mul_self_pos.2 hΦ₀u)
  have hkey : (frameForm o.someVector (ν q₀) (mfd 𝓘(ℝ, Z) 𝓘(ℝ, E) ι q₀)).compLinearMap
      (mfd 𝓘(ℝ, Z) 𝓘(ℝ, Z) c₀ q).toLinearMap =
      c⁻¹ • frameForm o.someVector (ν q) (mfd 𝓘(ℝ, Z) 𝓘(ℝ, E) ι q) := by
    rw [← hΦ₀, hrepΦ q hq, hc, smul_compLinearMap, smul_smul, inv_mul_cancel₀ hcpos.ne',
      one_smul]
  rw [frameOr_eq_someVector hZ o (hnd q), frameOr_eq_someVector hZ o (hnd q₀),
    orSign_eq_sgn (hnd q) (hnd q₀) rfl rfl hkey, sgn_pos (inv_pos.2 hcpos)]

/-- **Orientation from an immersion and a continuous complementary frame**: a basis `z` of
`T_qS` is positive iff `Ω(ν₁(q), …, ν_k(q), dι z₁, …, dι z_d) > 0` for a positive volume form
`Ω` of `E`. -/
def Orient.ofFrame {k : ℕ} (hZ : finrank ℝ Z = d) (hE : finrank ℝ E = d + k)
    (o : Orientation ℝ E (Fin (d + k))) {ι : S → E} (hι : ContMDiff 𝓘(ℝ, Z) 𝓘(ℝ, E) ∞ ι)
    {ν : S → Fin k → E} (hν : Continuous ν)
    (hnd : ∀ q, frameForm o.someVector (ν q) (mfd 𝓘(ℝ, Z) 𝓘(ℝ, E) ι q) ≠ 0) :
    Orient 𝓘(ℝ, Z) S d where
  or q := frameOr hZ o (ν q) (mfd 𝓘(ℝ, Z) 𝓘(ℝ, E) ι q)
  cont := Orient.ofFrame_cont hZ hE o hι hν hnd

theorem Orient.ofFrame_or {k : ℕ} (hZ : finrank ℝ Z = d) (hE : finrank ℝ E = d + k)
    (o : Orientation ℝ E (Fin (d + k))) {ι : S → E} (hι : ContMDiff 𝓘(ℝ, Z) 𝓘(ℝ, E) ∞ ι)
    {ν : S → Fin k → E} (hν : Continuous ν)
    (hnd : ∀ q, frameForm o.someVector (ν q) (mfd 𝓘(ℝ, Z) 𝓘(ℝ, E) ι q) ≠ 0) (q : S) :
    (Orient.ofFrame hZ hE o hι hν hnd).or q = frameOr hZ o (ν q) (mfd 𝓘(ℝ, Z) 𝓘(ℝ, E) ι q) :=
  rfl

/-- **Ambient sign formula.** For frame orientations on `S` (in `E`) and `S'` (in `E'`), both of
dimension `d`, the sign of `f : S → S'` at `q` is computed on any tuple `e` of `Z` on which the
source form does not vanish. -/
theorem signAt_ofFrame {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    [FiniteDimensional ℝ E'] {Z' : Type*} [NormedAddCommGroup Z'] [NormedSpace ℝ Z']
    [FiniteDimensional ℝ Z'] {S' : Type*} [TopologicalSpace S'] [ChartedSpace Z' S']
    [IsManifold 𝓘(ℝ, Z') ∞ S'] {k k' : ℕ}
    (hZ : finrank ℝ Z = d) (hE : finrank ℝ E = d + k) (o : Orientation ℝ E (Fin (d + k)))
    {ι : S → E} (hι : ContMDiff 𝓘(ℝ, Z) 𝓘(ℝ, E) ∞ ι) {ν : S → Fin k → E} (hν : Continuous ν)
    (hnd : ∀ q, frameForm o.someVector (ν q) (mfd 𝓘(ℝ, Z) 𝓘(ℝ, E) ι q) ≠ 0)
    (hZ' : finrank ℝ Z' = d) (hE' : finrank ℝ E' = d + k') (o' : Orientation ℝ E' (Fin (d + k')))
    {κ : S' → E'} (hκ : ContMDiff 𝓘(ℝ, Z') 𝓘(ℝ, E') ∞ κ) {μ : S' → Fin k' → E'}
    (hμ : Continuous μ)
    (hnd' : ∀ q, frameForm o'.someVector (μ q) (mfd 𝓘(ℝ, Z') 𝓘(ℝ, E') κ q) ≠ 0)
    {f : S → S'} (q : S) (_hf : MDifferentiableAt 𝓘(ℝ, Z) 𝓘(ℝ, Z') f q)
    (e : Fin d → Z) (he : frameForm o.someVector (ν q) (mfd 𝓘(ℝ, Z) 𝓘(ℝ, E) ι q) e ≠ 0) :
    signAt (Orient.ofFrame hZ hE o hι hν hnd) (Orient.ofFrame hZ' hE' o' hκ hμ hnd') f q =
      sgn (frameForm o'.someVector (μ (f q))
          ((mfd 𝓘(ℝ, Z') 𝓘(ℝ, E') κ (f q)).comp (mfd 𝓘(ℝ, Z) 𝓘(ℝ, Z') f q)) e *
        frameForm o.someVector (ν q) (mfd 𝓘(ℝ, Z) 𝓘(ℝ, E) ι q) e) := by
  unfold signAt
  rw [Orient.ofFrame_or, Orient.ofFrame_or, frameOr_eq_someVector hZ o (hnd q),
    frameOr_eq_someVector hZ' o' (hnd' (f q)), orSign_eq_sgn_mul hZ _ _ rfl rfl _ he,
    frameForm_comp]

end manifold

/-! ### Two orientations of a connected manifold -/

section connected

variable [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {n : ℕ}

/-- On a connected manifold, two orientations agree everywhere or are opposite everywhere. -/
theorem Orient.eq_or_eq_neg [PreconnectedSpace M] (hE : finrank ℝ E = n) (o₁ o₂ : Orient I M n) :
    o₁ = o₂ ∨ o₁ = o₂.neg hE := by
  have hor : ∀ x, o₁.or x = o₂.or x ∨ o₁.or x = -o₂.or x := fun x =>
    Orientation.eq_or_eq_neg _ _ (by rw [Fintype.card_fin, hE])
  have hopen1 : IsOpen {x | o₁.or x = o₂.or x} := by
    rw [isOpen_iff_mem_nhds]
    intro x hx
    have hx' : o₁.or x = o₂.or x := hx
    filter_upwards [o₁.cont x, o₂.cont x] with y h1 h2
    rcases hor y with h | h
    · exact h
    · exfalso
      rw [h, hx', orSign_neg_left hE, h2] at h1
      norm_num at h1
  have hopen2 : IsOpen {x | o₁.or x = o₂.or x}ᶜ := by
    rw [isOpen_iff_mem_nhds]
    intro x hx
    have hx' : o₁.or x = -o₂.or x := (hor x).resolve_left hx
    filter_upwards [o₁.cont x, o₂.cont x] with y h1 h2
    intro hy
    have hy' : o₁.or y = o₂.or y := hy
    rw [hy', hx', orSign_neg_right hE, h2] at h1
    norm_num at h1
  have hclopen : IsClopen {x | o₁.or x = o₂.or x} := ⟨isOpen_compl_iff.1 hopen2, hopen1⟩
  rcases isClopen_iff.1 hclopen with h | h
  · right
    refine Orient.ext' fun x => ?_
    have hx : x ∉ {x | o₁.or x = o₂.or x} := by rw [h]; exact notMem_empty x
    exact (hor x).resolve_left hx
  · left
    refine Orient.ext' fun x => ?_
    have hx : x ∈ {x | o₁.or x = o₂.or x} := by rw [h]; exact mem_univ x
    exact hx

end connected

/-! ### The standard orientation of the sphere -/

namespace Sphere

variable {n : ℕ}

/-- The standard orientation of `ℝⁿ⁺¹` (standard basis). -/
def stdOrE (n : ℕ) : Orientation ℝ (EuclideanSpace ℝ (Fin (n + 1))) (Fin (n + 1)) :=
  (EuclideanSpace.basisFun (Fin (n + 1)) ℝ).toBasis.orientation

theorem continuous_outward_frame : Continuous (fun q : Sph n => ![q.1]) :=
  continuous_subtype_val.matrixVecCons continuous_const

/-- The tangent space of `Sⁿ` at `q` is `q^⊥`, so the frame `(q)` is complementary. -/
theorem sph_frameForm_ne_zero (q : Sph n) :
    frameForm (stdOrE n).someVector ![q.1]
      (mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))
        (Subtype.val : Sph n → EuclideanSpace ℝ (Fin (n + 1))) q) ≠ 0 := by
  rw [frameForm_one]
  have hinj : Injective (mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))
      (Subtype.val : Sph n → EuclideanSpace ℝ (Fin (n + 1))) q) :=
    injective_mfderiv_val (sphS n) q
  have hT : ∀ w, fderiv ℝ sphG q.1
      (mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))
        (Subtype.val : Sph n → EuclideanSpace ℝ (Fin (n + 1))) q w) = 0 := fun w => by
    rw [← mfderiv_eq_fderiv]
    exact (mem_range_mfderiv_val_iff (finrank_Z_add hE hZ) contMDiff_sphG isRegularValue_sphG
      q _).1 ⟨w, rfl⟩
  have hv : fderiv ℝ sphG q.1 q.1 ≠ 0 := by
    rw [fderiv_sphG, inner_self_eq_one_of_mem q.2]; norm_num
  intro h
  exact contractForm_basis_ne_zero hE hZ (stdOrE n).someVector_ne_zero hinj hT hv
    (finBasisOfFinrankEq ℝ _ hZ) (by rw [h]; rfl)

/-- **Milnor's orientation of the sphere, as the boundary of the disk**: outward normal first,
for the standard orientation of `ℝⁿ⁺¹`. -/
def sphOrStd (n : ℕ) : Orient 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (Sph n) n :=
  Orient.ofFrame (k := 1) hZ hE (stdOrE n) (ι := Subtype.val) contMDiff_val
    (ν := fun q => ![q.1]) continuous_outward_frame sph_frameForm_ne_zero

theorem sphOrStd_or (q : Sph n) : (sphOrStd n).or q =
    frameOr hZ (stdOrE n) ![q.1]
      (mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))
        (Subtype.val : Sph n → EuclideanSpace ℝ (Fin (n + 1))) q) := rfl

/-- The ambient sign formula for maps of the sphere with the standard orientation. -/
theorem signAt_sphOrStd {f : Sph n → Sph n} (q : Sph n)
    (hf : MDifferentiableAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) f q)
    (e : Fin n → EuclideanSpace ℝ (Fin n))
    (he : frameForm (stdOrE n).someVector ![q.1]
      (mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))
        (Subtype.val : Sph n → EuclideanSpace ℝ (Fin (n + 1))) q) e ≠ 0) :
    signAt (sphOrStd n) (sphOrStd n) f q =
      sgn (frameForm (stdOrE n).someVector ![(f q).1]
          ((mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))
            (Subtype.val : Sph n → EuclideanSpace ℝ (Fin (n + 1))) (f q)).comp
            (mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) f q)) e *
        frameForm (stdOrE n).someVector ![q.1]
          (mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))
            (Subtype.val : Sph n → EuclideanSpace ℝ (Fin (n + 1))) q) e) :=
  signAt_ofFrame (k := 1) (k' := 1) hZ hE (stdOrE n) contMDiff_val continuous_outward_frame
    sph_frameForm_ne_zero hZ hE (stdOrE n) contMDiff_val continuous_outward_frame
    sph_frameForm_ne_zero q hf e he

theorem sphOrStd_eq_or_neg (hn : 0 < n) :
    sphOrStd n = sphOr n ∨ sphOrStd n = (sphOr n).neg hZ := by
  have := preconnectedSpace hn
  exact Orient.eq_or_eq_neg hZ _ _

/-- **The degree of the antipodal map is `(-1)ⁿ⁺¹`** for the standard orientation. -/
theorem deg_antip_std (hn : 0 < n) :
    deg (sphOrStd n) (sphOrStd n) (antip (n := n)) = (-1) ^ (n + 1) := by
  rcases sphOrStd_eq_or_neg hn with h | h
  · rw [h, deg_antip hn]
  · have := preconnectedSpace hn
    obtain ⟨y⟩ := nonempty_sph (n := n)
    rw [h, ← deg_antip hn, deg_eq hZ hZ _ _ contMDiff_antip (isRegularValue_antip y),
      deg_eq hZ hZ _ _ contMDiff_antip (isRegularValue_antip y)]
    unfold degAt
    refine finsum_mem_congr rfl fun q _ => ?_
    rw [signAt_neg_left hZ, signAt_neg_right hZ hZ, neg_neg]

end Sphere

end Milnor
