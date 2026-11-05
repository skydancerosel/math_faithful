import Milnor.Chapter6.Tubular2

/-!
# Tubular neighbourhoods, III: the nearest-point retraction

For a compact submanifold `N ⊆ ℝᵏ` there is `ε > 0` such that every `x` with `dist (x, N) < ε`
has a unique nearest point `r x ∈ N`; the map `r` is smooth there, `x - r x` is orthogonal to
`T_{r x} N`, `r` is the identity on `N`, and `d r_x` takes values in `T_{r x} N`.
(Milnor, §8, "the ε-neighborhood theorem", p. 53, in the form needed for §6.)
-/

open Set Filter Topology Function Metric
open scoped ContDiff Manifold RealInnerProductSpace

noncomputable section

namespace Milnor

namespace Tub

variable {k n m : ℕ} {N : Set (EuclideanSpace ℝ (Fin k))}
  (hN : IsSliceSubmanifold 𝓘(ℝ, EuclideanSpace ℝ (Fin k)) (EuclideanSpace ℝ (Fin n))
    (EuclideanSpace ℝ (Fin m)) N) (hNc : IsCompact N) (hne : N.Nonempty)

/-- A nearest point of `N` to `x`. -/
def nearestPt (x : EuclideanSpace ℝ (Fin k)) : N :=
  ⟨(hNc.exists_infDist_eq_dist hne x).choose, (hNc.exists_infDist_eq_dist hne x).choose_spec.1⟩

theorem infDist_eq_dist_nearestPt (x : EuclideanSpace ℝ (Fin k)) :
    infDist x N = dist x (nearestPt hNc hne x).1 :=
  (hNc.exists_infDist_eq_dist hne x).choose_spec.2

theorem nearestPt_min (x : EuclideanSpace ℝ (Fin k)) {q : EuclideanSpace ℝ (Fin k)} (hq : q ∈ N) :
    dist x (nearestPt hNc hne x).1 ≤ dist x q := by
  rw [← infDist_eq_dist_nearestPt]; exact infDist_le_dist_of_mem hq

/-- The chart coordinate of the base point. -/
def z₀ (p : N) : EuclideanSpace ℝ (Fin n) := c hN p p

theorem z₀_mem (p : N) : z₀ hN p ∈ Ω hN p := c_mem_Ω hN p (mem_source hN p)

theorem φ_z₀ (p : N) : φ hN p (z₀ hN p) = p.1 := φ_c hN p (mem_source hN p)

/-- **The good radius at `p`.**  Near `p`, every nearest point is `φ_p (U_p x)`, and `U_p` is
smooth with values in `Ω_p` solving the nearest-point equation. -/
theorem exists_good (p : N) : ∃ δ > 0, ∀ x, dist x p.1 < δ →
    (∀ q : N, (∀ q' ∈ N, dist x q.1 ≤ dist x q') → q.1 = φ hN p (U hN p (z₀_mem hN p) x)) ∧
    U hN p (z₀_mem hN p) x ∈ Ω hN p ∧ Fn hN p (U hN p (z₀_mem hN p) x) x = 0 ∧
    ContDiffAt ℝ ∞ (U hN p (z₀_mem hN p)) x := by
  have hz := z₀_mem hN p
  have hφ : φ hN p (z₀ hN p) = p.1 := φ_z₀ hN p
  -- existence and smoothness near `p`
  have ha := eventually_Fn_U hN p hz
  rw [hφ] at ha
  have hc := contDiffAt_U hN p hz
  rw [hφ] at hc
  have hc' : ∀ᶠ x in 𝓝 p.1, ContDiffAt ℝ ∞ (U hN p hz) x := by
    obtain ⟨V, hVo, hxV, hUV⟩ := exists_contDiffOn_U hN p hz
    rw [hφ] at hxV
    filter_upwards [hVo.mem_nhds hxV] with y hy
    exact hUV.contDiffAt (hVo.mem_nhds hy)
  have hU0 : U hN p hz p.1 = z₀ hN p := by
    have := U_self hN p hz; rwa [hφ] at this
  have hUΩ : ∀ᶠ x in 𝓝 p.1, U hN p hz x ∈ Ω hN p :=
    hc.continuousAt.eventually_mem ((isOpen_Ω hN p).mem_nhds (by rw [hU0]; exact hz))
  obtain ⟨δ₁, hδ₁, h₁⟩ := Metric.eventually_nhds_iff.1 (ha.and (hc'.and hUΩ))
  -- uniqueness near `(z₀, p)`
  have hb := eventually_eq_U hN p hz
  rw [hφ] at hb
  obtain ⟨δ₃, hδ₃, h₃⟩ := Metric.eventually_nhds_iff.1 hb
  -- continuity of the chart at `p`
  have hcont : ContinuousAt (fun y => ((σ hN p).φ y).1) p.1 :=
    continuous_fst.continuousAt.comp
      ((σ hN p).φ.contMDiffOn_toFun.continuousOn.continuousAt
        ((σ hN p).φ.open_source.mem_nhds (mem_source hN p)))
  obtain ⟨δ₄, hδ₄, h₄⟩ := Metric.continuousAt_iff.1 hcont δ₃ hδ₃
  obtain ⟨δ₅, hδ₅, h₅⟩ := Metric.isOpen_iff.1 (σ hN p).φ.open_source p.1 (mem_source hN p)
  refine ⟨min δ₁ (min δ₃ (min (δ₄ / 2) (δ₅ / 2))), by positivity, fun x hx => ?_⟩
  have hx₁ : dist x p.1 < δ₁ := lt_of_lt_of_le hx (min_le_left _ _)
  have hx₃ : dist x p.1 < δ₃ := lt_of_lt_of_le hx ((min_le_right _ _).trans (min_le_left _ _))
  have hx₄ : dist x p.1 < δ₄ / 2 :=
    lt_of_lt_of_le hx ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hx₅ : dist x p.1 < δ₅ / 2 :=
    lt_of_lt_of_le hx ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  obtain ⟨hFn, hcx, hΩx⟩ := h₁ hx₁
  refine ⟨fun q hq => ?_, hΩx, hFn, hcx⟩
  -- a nearest point `q` is close to `p`, hence in the chart, and satisfies the equation
  have hqx : dist q.1 x ≤ dist x p.1 := by rw [dist_comm]; exact hq p.1 p.2
  have hqp : dist q.1 p.1 < min δ₄ δ₅ := by
    have := dist_triangle q.1 x p.1
    rw [lt_min_iff]; constructor <;> linarith
  have hqsrc : q.1 ∈ (σ hN p).φ.source :=
    h₅ (Metric.mem_ball.2 (lt_of_lt_of_le hqp (min_le_right _ _)))
  have hqz : dist (c hN p q) (z₀ hN p) < δ₃ := h₄ (lt_of_lt_of_le hqp (min_le_left _ _))
  have hFq : Fn hN p (c hN p q) x = 0 := Fn_eq_zero_of_nearest hN p hqsrc hq
  have hnear : dist (c hN p q, x) (z₀ hN p, p.1) < δ₃ := by
    rw [Prod.dist_eq, max_lt_iff]; exact ⟨hqz, hx₃⟩
  have hcq : c hN p q = U hN p hz x := h₃ hnear hFq
  rw [← hcq]
  exact (φ_c hN p hqsrc).symm

/-- The good radius. -/
def δ (p : N) : ℝ := (exists_good hN p).choose

theorem δ_pos (p : N) : 0 < δ hN p := (exists_good hN p).choose_spec.1

theorem δ_spec (p : N) : ∀ x, dist x p.1 < δ hN p →
    (∀ q : N, (∀ q' ∈ N, dist x q.1 ≤ dist x q') → q.1 = φ hN p (U hN p (z₀_mem hN p) x)) ∧
    U hN p (z₀_mem hN p) x ∈ Ω hN p ∧ Fn hN p (U hN p (z₀_mem hN p) x) x = 0 ∧
    ContDiffAt ℝ ∞ (U hN p (z₀_mem hN p)) x :=
  (exists_good hN p).choose_spec.2

include hNc hne in
/-- **The uniform radius:** points close to `N` lie in a good ball. -/
theorem exists_eps : ∃ ε > 0, ∀ x, infDist x N < ε → ∃ p : N, dist x p.1 < δ hN p := by
  by_contra hcon
  push_neg at hcon
  have hseq : ∀ j : ℕ, ∃ x, infDist x N < 1 / ((j : ℝ) + 1) ∧ ∀ p : N, δ hN p ≤ dist x p.1 :=
    fun j => hcon (1 / ((j : ℝ) + 1)) (by positivity)
  choose x hx using hseq
  set q : ℕ → EuclideanSpace ℝ (Fin k) := fun j => (nearestPt hNc hne (x j)).1 with hq
  have hqN : ∀ j, q j ∈ N := fun j => (nearestPt hNc hne (x j)).2
  obtain ⟨p, hpN, ψ, hψ, hlim⟩ := hNc.tendsto_subseq hqN
  set P : N := ⟨p, hpN⟩ with hP
  -- `x (ψ j) → p`
  have hd : Tendsto (fun j => dist (x (ψ j)) p) atTop (𝓝 0) := by
    have h1 : Tendsto (fun j => 1 / ((ψ j : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat.comp hψ.tendsto_atTop
    have h2 : Tendsto (fun j => dist (q (ψ j)) p) atTop (𝓝 0) :=
      (tendsto_iff_dist_tendsto_zero.1 hlim)
    have h3 := h1.add h2
    rw [add_zero] at h3
    refine squeeze_zero (fun j => dist_nonneg) (fun j => ?_) h3
    calc dist (x (ψ j)) p ≤ dist (x (ψ j)) (q (ψ j)) + dist (q (ψ j)) p := dist_triangle _ _ _
      _ ≤ 1 / ((ψ j : ℝ) + 1) + dist (q (ψ j)) p := by
        have : dist (x (ψ j)) (q (ψ j)) = infDist (x (ψ j)) N :=
          (infDist_eq_dist_nearestPt hNc hne _).symm
        rw [this]
        exact add_le_add (hx (ψ j)).1.le le_rfl
  have hev : ∀ᶠ j in atTop, dist (x (ψ j)) p < δ hN P := hd.eventually_lt_const (δ_pos hN P)
  obtain ⟨j, hj⟩ := hev.exists
  exact absurd hj (not_lt.2 ((hx (ψ j)).2 P))

include hNc hne in
/-- **The nearest-point retraction and its properties on the tubular neighbourhood.** -/
theorem tubular : ∃ ε > 0, ∃ r : EuclideanSpace ℝ (Fin k) → N,
    letI := hN.chartedSpace
    (∀ x, dist x (r x).1 = infDist x N) ∧
    (∀ x, infDist x N < ε → ∀ q : N, (∀ q' ∈ N, dist x q.1 ≤ dist x q') → q = r x) ∧
    (∀ x ∈ N, (r x).1 = x) ∧
    (∀ x, infDist x N < ε → ContDiffAt ℝ ∞ (fun y => (r y).1) x) ∧
    (∀ x, infDist x N < ε → ∀ w ∈ LinearMap.range ((mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
        𝓘(ℝ, EuclideanSpace ℝ (Fin k)) (Subtype.val : N → EuclideanSpace ℝ (Fin k)) (r x) :
          EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin k)) :
          EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin k)),
      ⟪x - (r x).1, w⟫ = 0) ∧
    (∀ x, infDist x N < ε → ∀ w, fderiv ℝ (fun y => (r y).1) x w ∈
      LinearMap.range ((mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
        𝓘(ℝ, EuclideanSpace ℝ (Fin k)) (Subtype.val : N → EuclideanSpace ℝ (Fin k)) (r x) :
          EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin k)) :
          EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin k))) ∧
    (∀ x (hx : x ∈ N) (v : EuclideanSpace ℝ (Fin k)),
      (∀ w ∈ LinearMap.range ((mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
        𝓘(ℝ, EuclideanSpace ℝ (Fin k)) (Subtype.val : N → EuclideanSpace ℝ (Fin k)) ⟨x, hx⟩ :
          EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin k)) :
          EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin k)), ⟪v, w⟫ = 0) →
      ∀ᶠ s : ℝ in 𝓝 0, (r (x + s • v)).1 = x) := by
  letI := hN.chartedSpace
  obtain ⟨ε, hε, hgood⟩ := exists_eps hN hNc hne
  set r := nearestPt hNc hne with hr
  -- the local formula near a point of the tubular neighbourhood
  have hloc : ∀ x, infDist x N < ε → ∃ p : N, (∀ᶠ y in 𝓝 x, (r y).1 = φ hN p (U hN p (z₀_mem hN p) y)) ∧
      U hN p (z₀_mem hN p) x ∈ Ω hN p ∧ Fn hN p (U hN p (z₀_mem hN p) x) x = 0 ∧
      ContDiffAt ℝ ∞ (U hN p (z₀_mem hN p)) x := by
    intro x hx
    obtain ⟨p, hp⟩ := hgood x hx
    obtain ⟨-, hΩ, hFn, hc⟩ := δ_spec hN p x hp
    refine ⟨p, ?_, hΩ, hFn, hc⟩
    filter_upwards [Metric.isOpen_ball.mem_nhds (Metric.mem_ball.2 hp)] with y hy
    exact (δ_spec hN p y (Metric.mem_ball.1 hy)).1 (r y) (fun q' hq' => nearestPt_min hNc hne y hq')
  refine ⟨ε, hε, r, fun x => (infDist_eq_dist_nearestPt hNc hne x).symm, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx q hq
    obtain ⟨p, hev, -, -, -⟩ := hloc x hx
    obtain ⟨p', hp'⟩ := hgood x hx
    have h1 := (δ_spec hN p' x hp').1 q hq
    have h2 := (δ_spec hN p' x hp').1 (r x) (fun q' hq' => nearestPt_min hNc hne x hq')
    exact Subtype.ext (h1.trans h2.symm)
  · intro x hx
    have := nearestPt_min hNc hne x hx
    rw [dist_self] at this
    exact (dist_le_zero.1 this).symm
  · intro x hx
    obtain ⟨p, hev, hΩ, -, hc⟩ := hloc x hx
    refine ContDiffAt.congr_of_eventuallyEq ?_ hev
    exact ((contDiffOn_φ hN p).contDiffAt ((isOpen_Ω hN p).mem_nhds hΩ)).comp x hc
  · intro x hx w hw
    obtain ⟨p, hev, hΩ, hFn, -⟩ := hloc x hx
    have hrx : (r x).1 = φ hN p (U hN p (z₀_mem hN p) x) := hev.self_of_nhds
    have hsrc : (r x).1 ∈ (σ hN p).φ.source := by rw [hrx]; exact φ_mem_source hN p hΩ
    have hcr : c hN p (r x) = U hN p (z₀_mem hN p) x := by
      unfold c; rw [hrx]; exact c_φ hN p hΩ
    rw [range_mfd_val hN p (r x) hsrc, hcr] at hw
    obtain ⟨a, rfl⟩ := hw
    rw [hrx]
    have : ⟪Fn hN p (U hN p (z₀_mem hN p) x) x, a⟫ = 0 := by rw [hFn, inner_zero_left]
    unfold Fn at this
    rw [A_inner] at this
    exact this
  · intro x hx w
    obtain ⟨p, hev, hΩ, -, hc⟩ := hloc x hx
    have hrx : (r x).1 = φ hN p (U hN p (z₀_mem hN p) x) := hev.self_of_nhds
    have hsrc : (r x).1 ∈ (σ hN p).φ.source := by rw [hrx]; exact φ_mem_source hN p hΩ
    have hcr : c hN p (r x) = U hN p (z₀_mem hN p) x := by
      unfold c; rw [hrx]; exact c_φ hN p hΩ
    rw [range_mfd_val hN p (r x) hsrc, hcr]
    have hd : HasFDerivAt (fun y => (r y).1)
        ((fderiv ℝ (φ hN p) (U hN p (z₀_mem hN p) x)).comp
          (fderiv ℝ (U hN p (z₀_mem hN p)) x)) x :=
      ((hasFDerivAt_φ hN p hΩ).comp x (hc.differentiableAt (by simp)).hasFDerivAt).congr_of_eventuallyEq hev
    rw [hd.fderiv]
    exact ⟨_, rfl⟩
  · -- the retraction is constant along short normal segments
    intro x hx v hv
    set p : N := ⟨x, hx⟩ with hp
    have hz := z₀_mem hN p
    have hφz : φ hN p (z₀ hN p) = x := φ_z₀ hN p
    have huniq := eventually_eq_U hN p hz
    rw [hφz] at huniq
    obtain ⟨δ₁, hδ₁, h₁⟩ := Metric.eventually_nhds_iff.1 huniq
    have hδp := δ_pos hN p
    have hAn : A hN p (z₀ hN p) v = 0 := by
      have hT : ∀ a, ⟪A hN p (z₀ hN p) v, a⟫ = 0 := fun a => by
        rw [A_inner]
        apply hv
        rw [range_mfd_val hN p p (mem_source hN p)]
        exact ⟨a, rfl⟩
      exact inner_self_eq_zero.1 (hT _)
    have hcont : Continuous fun s : ℝ => ‖s • v‖ :=
      continuous_norm.comp (continuous_id.smul continuous_const)
    have hs : ∀ᶠ s : ℝ in 𝓝 0, ‖s • v‖ < min δ₁ (δ hN p) :=
      hcont.continuousAt.eventually_lt continuousAt_const (by simp; exact ⟨hδ₁, hδp⟩)
    filter_upwards [hs] with s hs
    have hy1 : dist (x + s • v) p.1 < δ hN p := by
      rw [dist_eq_norm, add_sub_cancel_left]
      exact lt_of_lt_of_le hs (min_le_right _ _)
    have hry : (r (x + s • v)).1 = φ hN p (U hN p hz (x + s • v)) :=
      (δ_spec hN p _ hy1).1 (r _) (fun q' hq' => nearestPt_min hNc hne _ hq')
    have hFn : Fn hN p (z₀ hN p) (x + s • v) = 0 := by
      unfold Fn
      rw [hφz, add_sub_cancel_left, map_smul, hAn, smul_zero]
    have hnear : dist (z₀ hN p, x + s • v) (z₀ hN p, x) < δ₁ := by
      rw [Prod.dist_eq, dist_self, dist_eq_norm, add_sub_cancel_left, max_lt_iff]
      exact ⟨hδ₁, lt_of_lt_of_le hs (min_le_left _ _)⟩
    have hU : z₀ hN p = U hN p hz (x + s • v) := h₁ hnear hFn
    rw [hry, ← hU, hφz]

end Tub

end Milnor
