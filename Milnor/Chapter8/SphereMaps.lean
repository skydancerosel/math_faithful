import Milnor.Chapter8.NearMaps

/-!
# Problems 6 and 7: fixed points and antipodal points of maps of spheres

* **Problem 6** (Brouwer): a smooth map `f : Sⁿ → Sⁿ` of degree `≠ (-1)ⁿ⁺¹` has a fixed point.
  Otherwise `f x` is never antipodal to `-x`, so by Problem 3 `f` is smoothly homotopic to the
  antipodal map, of degree `(-1)ⁿ⁺¹`.
* **Problem 7**: a smooth map `f : Sⁿ → Sⁿ` of odd degree carries some pair of antipodal points
  to a pair of antipodal points.  Otherwise `w x = f x + f (-x)` never vanishes, and the smooth
  even map `h = w / |w|` is never antipodal to `f`, so `deg f = deg h` by Problem 3.  But an even
  map has even degree: the preimage of a regular value is invariant under the fixed-point-free
  involution `x ↦ -x`, and each point of it contributes `±1`.
-/

open Set Module Filter Topology Function
open scoped ContDiff Manifold RealInnerProductSpace

noncomputable section

namespace Milnor

open Sphere

namespace Problems

variable {n : ℕ}

/-- Two points of the sphere which are not antipodal are at distance `< 2`. -/
theorem norm_sub_lt_two_of_ne_neg {a b : Sph n} (h : a.1 ≠ -b.1) : ‖a.1 - b.1‖ < 2 := by
  have hpar : ‖a.1 - b.1‖ ^ 2 + ‖a.1 + b.1‖ ^ 2 = 2 ^ 2 := by
    rw [norm_sub_sq_real, norm_add_sq_real, norm_sph, norm_sph]; ring
  have hab : a.1 + b.1 ≠ 0 := fun h0 => h (eq_neg_of_add_eq_zero_left h0)
  have hpos : 0 < ‖a.1 + b.1‖ ^ 2 := pow_pos (norm_pos_iff.2 hab) 2
  exact lt_of_pow_lt_pow_left₀ 2 (by norm_num) (by linarith)

/-- Smoothly homotopic maps of spheres have the same degree. -/
theorem deg_eq_of_smoothHomotopic (hn : 0 < n) {f g : Sph n → Sph n}
    (h : SmoothHomotopic 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) f g) :
    deg (sphOr n) (sphOr n) f = deg (sphOr n) (sphOr n) g := by
  obtain ⟨Hm, hH, h0, h1⟩ := h
  have := preconnectedSpace hn
  have hdeg := deg_eq_of_homotopy hZ hZ (sphOr n) (sphOr n) hH
  have e0 : (fun x => Hm (x, 0)) = f := funext h0
  have e1 : (fun x => Hm (x, 1)) = g := funext h1
  rwa [e0, e1] at hdeg

/-- **Problem 6** (Brouwer): a smooth map `Sⁿ → Sⁿ` of degree different from `(-1)ⁿ⁺¹` has a
fixed point. -/
theorem exists_fixedPoint_of_deg_ne (hn : 0 < n) {f : Sph n → Sph n}
    (hf : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ f)
    (hdeg : deg (sphOr n) (sphOr n) f ≠ (-1) ^ (n + 1)) : ∃ x, f x = x := by
  by_contra hcon
  push Not at hcon
  have hlt : ∀ x, ‖(f x).1 - (antip x).1‖ < 2 := fun x => by
    refine norm_sub_lt_two_of_ne_neg fun h => hcon x (Subtype.ext ?_)
    rw [h]
    exact neg_neg x.1
  exact hdeg ((deg_eq_of_smoothHomotopic hn
    (smoothHomotopic_of_norm_sub_lt_two hf contMDiff_antip hlt)).trans (deg_antip hn))

/-- The antipodal map has no fixed points. -/
theorem antip_ne (x : Sph n) : antip x ≠ x := by
  intro hx
  have h2 : -x.1 = x.1 := congrArg Subtype.val hx
  have h3 : (2 : ℝ) • x.1 = 0 := by
    rw [two_smul]
    nth_rewrite 1 [← h2]
    exact neg_add_cancel x.1
  have h4 : x.1 = 0 := (smul_eq_zero.1 h3).resolve_left (by norm_num)
  have h5 := norm_sph x
  rw [h4, norm_zero] at h5
  exact zero_ne_one h5

/-- Even maps have even degree. -/
theorem even_deg_of_even_map (hn : 0 < n) {h : Sph n → Sph n}
    (hh : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ h)
    (heven : ∀ x, h (antip x) = h x) : Even (deg (sphOr n) (sphOr n) h) := by
  have := preconnectedSpace hn
  obtain ⟨y, hy⟩ := (dense_regularValues hh).nonempty
  have hy' : IsRegularValue 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) h y :=
    hy
  rw [deg_eq hZ hZ (sphOr n) (sphOr n) hh hy', degAt]
  have hfin : (h ⁻¹' {y}).Finite := hy'.finite_preimage (hZ.trans hZ.symm) hh (by simp)
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin, ← ZMod.intCast_eq_zero_iff_even, Int.cast_sum]
  -- each point of the preimage contributes `1` modulo `2`
  have hs : ∀ z, h z = y → ((signAt (sphOr n) (sphOr n) h z : ℤ) : ZMod 2) = 1 := by
    intro z hz
    rcases signAt_mem hZ hZ (sphOr n) (sphOr n) h z with h1 | h1 | h1
    · rw [h1]; rfl
    · rw [h1]; rfl
    · exact absurd h1 (IsRegularPoint.signAt_ne_zero hZ hZ _ _ (hy' z hz))
  have hmem : ∀ z, z ∈ hfin.toFinset ↔ h z = y := fun z => by
    rw [Set.Finite.mem_toFinset]; rfl
  refine Finset.sum_involution (fun x _ => antip x) (fun x hx => ?_) (fun x _ _ => antip_ne x)
    (fun x hx => ?_) (fun x _ => antip_antip x)
  · rw [hs x ((hmem x).1 hx), hs (antip x) ((heven x).trans ((hmem x).1 hx))]
    decide
  · exact (hmem _).2 ((heven x).trans ((hmem x).1 hx))

/-- **Problem 7**: a smooth map `Sⁿ → Sⁿ` of odd degree carries some pair of antipodal points
into a pair of antipodal points. -/
theorem exists_antipodal_of_odd_deg (hn : 0 < n) {f : Sph n → Sph n}
    (hf : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ f)
    (hdeg : Odd (deg (sphOr n) (sphOr n) f)) : ∃ x, f (antip x) = antip (f x) := by
  by_contra hcon
  push Not at hcon
  obtain ⟨w, hw⟩ : ∃ w : Sph n → EuclideanSpace ℝ (Fin (n + 1)),
      ∀ x, w x = (f x).1 + (f (antip x)).1 := ⟨_, fun _ => rfl⟩
  have hw0 : ∀ x, w x ≠ 0 := by
    intro x h0
    rw [hw] at h0
    exact hcon x (Subtype.ext (eq_neg_of_add_eq_zero_right h0))
  have hwc :
      ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) ∞ w := by
    rw [show w = fun x => (f x).1 + (f (antip x)).1 from funext hw]
    exact (contMDiff_val.comp hf).add (contMDiff_val.comp (hf.comp contMDiff_antip))
  have hhc := contMDiff_nv0_comp hwc hw0
  have heven : ∀ x, nv0 (w (antip x)) = nv0 (w x) := fun x => by
    rw [hw, hw, antip_antip]
    exact congrArg _ (add_comm _ _)
  have hlt : ∀ x, ‖(f x).1 - (nv0 (w x)).1‖ < 2 := by
    intro x
    refine norm_sub_lt_two_of_ne_neg fun heq => ?_
    rw [nv0_val (hw0 x), Sphere.normalize] at heq
    have hwpos : 0 < ‖w x‖ := norm_pos_iff.2 (hw0 x)
    have h1 : ⟪(f x).1, w x⟫ = -‖w x‖ := by
      rw [heq, inner_neg_left, real_inner_smul_left, real_inner_self_eq_norm_sq, sq, ← mul_assoc,
        inv_mul_cancel₀ hwpos.ne', one_mul]
    have h2 : 0 ≤ ⟪(f x).1, w x⟫ := by
      have h3 := abs_real_inner_le_norm (f x).1 (f (antip x)).1
      rw [norm_sph, norm_sph, mul_one] at h3
      rw [hw, inner_add_right, real_inner_self_eq_norm_sq, norm_sph]
      linarith [neg_abs_le ⟪(f x).1, (f (antip x)).1⟫]
    linarith
  have hd := deg_eq_of_smoothHomotopic hn (smoothHomotopic_of_norm_sub_lt_two hf hhc hlt)
  have he := even_deg_of_even_map hn hhc heven
  rw [← hd] at he
  exact Int.not_even_iff_odd.2 hdeg he

end Problems

end Milnor
