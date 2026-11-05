import Morse
import RoundTrip.Check
import RoundTrip.Blind.V5_5

open Asymptotics ComplexConjugate

namespace RoundTrip.V5_5

/-- The project's statement (universe of `V` instantiated at 0). -/
def A : Prop := type_of% @Morse.inner_eq_zero_of_re_inner_eq_zero.{0}

theorem A_holds : A := @Morse.inner_eq_zero_of_re_inner_eq_zero.{0}

/-- The second-order Taylor expansion of a holomorphic function `h : ℂᵏ → ℂ` at `0`, with
the linear term written as `fderiv`: `h z - h 0 - dh₀ z - Q(z) = o(‖z‖²)`. (Not part of `A`.) -/
theorem taylor2 {k : ℕ} {h : EuclideanSpace ℂ (Fin k) → ℂ} (hh : AnalyticAt ℂ h 0) :
    ∃ b : Matrix (Fin k) (Fin k) ℂ,
      (fun z => h z - h 0 - fderiv ℂ h 0 z - Qz b z) =o[nhds 0] (fun z => ‖z‖ ^ 2) := by
  obtain ⟨p, hp⟩ := hh
  refine ⟨fun i j => p 2 ![EuclideanSpace.single i 1, EuclideanSpace.single j 1], ?_⟩
  have hO := hp.isBigO_sub_partialSum_pow 3
  have hlo : (fun z : EuclideanSpace ℂ (Fin k) => ‖z‖ ^ 3) =o[nhds 0] fun z => ‖z‖ ^ 2 :=
    isLittleO_norm_pow_norm_pow (by norm_num)
  refine (hO.trans_isLittleO hlo).congr_left fun z => ?_
  have h0 : p 0 (fun _ => z) = h 0 := hp.coeff_zero _
  have h1 : p 1 (fun _ => z) = fderiv ℂ h 0 z := by
    rw [hp.fderiv_eq]; simp only [continuousMultilinearCurryFin1_apply]
    congr 1
  have h2 : p 2 (fun _ => z) = Qz (fun i j => p 2 ![EuclideanSpace.single i 1,
      EuclideanSpace.single j 1]) z := by
    have hz : z = ∑ i, z i • EuclideanSpace.single i (1 : ℂ) := by
      ext j; simp [Pi.single_apply]
    have : (fun _ : Fin 2 => z) = fun _ => ∑ i, z i • EuclideanSpace.single i (1 : ℂ) := by
      rw [← hz]
    rw [this, ContinuousMultilinearMap.map_sum]
    simp only [ContinuousMultilinearMap.map_smul_univ, Qz, Fin.prod_univ_two]
    rw [← Fintype.sum_equiv (piFinTwoEquiv fun _ => Fin k).symm _ _ (fun _ => rfl),
      ← Fintype.sum_prod_type']
    refine Fintype.sum_congr _ _ fun r => ?_
    simp only [smul_eq_mul, piFinTwoEquiv_symm_apply, Fin.cons_zero, Fin.cons_one]
    have : (fun i : Fin 2 => EuclideanSpace.single ((Fin.cons r.1 (Fin.cons r.2 finZeroElim) : Fin 2 → Fin k) i)
        (1 : ℂ)) = ![EuclideanSpace.single r.1 1, EuclideanSpace.single r.2 1] := by
      ext i; fin_cases i <;> rfl
    rw [this]; ring
  simp only [FormalMultilinearSeries.partialSum, Finset.sum_range_succ, Finset.sum_range_zero,
    zero_add, h0, h1, h2]
  ring

/-- A ⇒ B: clause (1) is `A` applied to `T = range dw(0)`; clause (2) is the second-order
Taylor expansion of the holomorphic function `⟨v, w(z)⟩` (`taylor2`, Mathlib's power series),
whose linear term vanishes by (1). -/
theorem A_to_B : A → B := by
  intro hA n k w hw _ v hv
  have h1 : ∀ z, inner ℂ v (fderiv ℂ w 0 z) = 0 := by
    intro z
    have := hA (LinearMap.range (fderiv ℂ w 0 : _ →ₗ[ℂ] _)) v (by
      rintro a ⟨z', rfl⟩
      rw [← inner_conj_symm, Complex.conj_re]; exact hv z') (fderiv ℂ w 0 z) ⟨z, rfl⟩
    rw [← inner_conj_symm, this, map_zero]
  refine ⟨h1, ?_⟩
  have han : AnalyticAt ℂ (fun z => inner ℂ v (w z)) 0 :=
    ((innerSL ℂ v).analyticAt _).comp hw
  obtain ⟨b, hb⟩ := taylor2 han
  refine ⟨b, hb.congr_left fun z => ?_⟩
  have hd : fderiv ℂ (fun z => inner ℂ v (w z)) 0 = (innerSL ℂ v).comp (fderiv ℂ w 0) :=
    ((innerSL ℂ v).hasFDerivAt.comp 0 hw.differentiableAt.hasFDerivAt).fderiv
  rw [hd, ContinuousLinearMap.comp_apply, innerSL_apply_apply, h1, sub_zero]

/-- B ⇒ A: apply B to `w = id : ℂ¹ → ℂ¹` and `v' = conj⟨a, v⟩ e₀`, so that `⟨v', z⟩ = ⟨a, v⟩ z₀`
and the hypothesis `Re⟨v', z⟩ = Re⟨conj z₀ • a, v⟩ = 0` holds since `T` is complex. -/
theorem B_to_A : B → A := by
  intro hB V _ _ T v h a ha
  set c : ℂ := inner ℂ a v
  have hin : ∀ z : EuclideanSpace ℂ (Fin 1),
      inner ℂ (EuclideanSpace.single (0 : Fin 1) (conj c)) z = c * z 0 := by
    intro z
    simp [PiLp.inner_apply, mul_comm]
  have hid : fderiv ℂ (fun z : EuclideanSpace ℂ (Fin 1) => z) 0 = ContinuousLinearMap.id ℂ _ :=
    fderiv_fun_id
  have := (hB 1 1 (fun z => z) analyticAt_id (by rw [hid]; exact Function.injective_id)
    (EuclideanSpace.single 0 (conj c)) (fun z => by
      rw [hid, ContinuousLinearMap.id_apply, hin]
      have hm := h (conj (z 0) • a) (T.smul_mem _ ha)
      rw [inner_smul_left, Complex.conj_conj] at hm
      rwa [mul_comm] at hm)).1 (EuclideanSpace.single 0 1)
  rw [hid, ContinuousLinearMap.id_apply, hin] at this
  simpa using this

#rt_check RoundTrip.V5_5.A_to_B [Morse.inner_eq_zero_of_re_inner_eq_zero]
#rt_check RoundTrip.V5_5.B_to_A [Morse.inner_eq_zero_of_re_inner_eq_zero]
#rt_overlap RoundTrip.V5_5.B_to_A [Morse.inner_eq_zero_of_re_inner_eq_zero]

end RoundTrip.V5_5
