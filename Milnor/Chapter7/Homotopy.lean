import Milnor.Chapter7.Reparam

/-!
# Smooth homotopy is an equivalence relation

Two smooth maps `f g : X → Y` between manifolds are *smoothly homotopic* if there is a smooth
`H : X × ℝ → Y` with `H(·,0) = f` and `H(·,1) = g`. We show this relation is reflexive,
symmetric and transitive. Transitivity uses the reparametrization of `Milnor/Chapter7/Transition`
to make both homotopies constant near the ends of `[0,1]` before gluing them.
-/

open Set Filter Topology Function
open scoped ContDiff Manifold

noncomputable section

namespace Milnor

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {X : Type*} [TopologicalSpace X] [ChartedSpace H X]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] {H' : Type*} [TopologicalSpace H']
  {I' : ModelWithCorners ℝ E' H'} {Y : Type*} [TopologicalSpace Y] [ChartedSpace H' Y]

/-- Two maps are smoothly homotopic: there is a smooth `H : X × ℝ → Y` with `H(·,0) = f`, `H(·,1) = g`. -/
def SmoothHomotopic (I : ModelWithCorners ℝ E H) (I' : ModelWithCorners ℝ E' H') (f g : X → Y) : Prop :=
  ∃ Hm : X × ℝ → Y, ContMDiff (I.prod 𝓘(ℝ, ℝ)) I' ∞ Hm ∧ (∀ x, Hm (x, 0) = f x) ∧ (∀ x, Hm (x, 1) = g x)

/-- Precomposing a smooth map `X × ℝ → Y` with a smooth reparametrization of time. -/
theorem contMDiff_comp_time {Hm : X × ℝ → Y} (hH : ContMDiff (I.prod 𝓘(ℝ, ℝ)) I' ∞ Hm)
    {ρ : ℝ → ℝ} (hρ : ContDiff ℝ ∞ ρ) :
    ContMDiff (I.prod 𝓘(ℝ, ℝ)) I' ∞ (fun q : X × ℝ => Hm (q.1, ρ q.2)) := by
  have hΦ : ContMDiff (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, ℝ)) ∞ (fun q : X × ℝ => (q.1, ρ q.2)) :=
    contMDiff_fst.prodMk (hρ.contMDiff.comp contMDiff_snd)
  exact hH.comp hΦ

theorem SmoothHomotopic.refl {f : X → Y} (hf : ContMDiff I I' ∞ f) : SmoothHomotopic I I' f f :=
  ⟨fun q => f q.1, hf.comp contMDiff_fst, fun _ => rfl, fun _ => rfl⟩

theorem SmoothHomotopic.symm {f g : X → Y} (h : SmoothHomotopic I I' f g) : SmoothHomotopic I I' g f := by
  obtain ⟨Hm, hH, h0, h1⟩ := h
  refine ⟨fun q => Hm (q.1, 1 - q.2), contMDiff_comp_time hH (contDiff_const.sub contDiff_id), ?_, ?_⟩
  · intro x; simp only [sub_zero]; exact h1 x
  · intro x; simp only [sub_self]; exact h0 x

/-- A homotopy constant near the ends of `[0,1]`. -/
theorem SmoothHomotopic.exists_const_near_ends {f g : X → Y} (h : SmoothHomotopic I I' f g) {ε : ℝ}
    (hε : 0 < ε) (hε' : ε < 1 / 2) :
    ∃ Hm : X × ℝ → Y, ContMDiff (I.prod 𝓘(ℝ, ℝ)) I' ∞ Hm ∧ (∀ x t, t ≤ ε → Hm (x, t) = f x) ∧
      (∀ x t, 1 - ε ≤ t → Hm (x, t) = g x) := by
  obtain ⟨Hm, hH, h0, h1⟩ := h
  obtain ⟨ρ, hρs, hρ0, hρ1, -, -⟩ := exists_timeTransition hε hε'
  refine ⟨fun q => Hm (q.1, ρ q.2), contMDiff_comp_time hH hρs, ?_, ?_⟩
  · intro x t ht; simp only [hρ0 t ht]; exact h0 x
  · intro x t ht; simp only [hρ1 t ht]; exact h1 x

open scoped Classical in
theorem SmoothHomotopic.trans {f g k : X → Y} (h₁ : SmoothHomotopic I I' f g) (h₂ : SmoothHomotopic I I' g k) :
    SmoothHomotopic I I' f k := by
  have hq : (0 : ℝ) < 1 / 4 := by norm_num
  have hq' : (1 : ℝ) / 4 < 1 / 2 := by norm_num
  obtain ⟨H₁, hH₁, h₁0, h₁1⟩ := h₁.exists_const_near_ends hq hq'
  obtain ⟨H₂, hH₂, h₂0, h₂1⟩ := h₂.exists_const_near_ends hq hq'
  -- the two smooth pieces
  have hA : ContMDiff (I.prod 𝓘(ℝ, ℝ)) I' ∞ (fun q : X × ℝ => H₁ (q.1, 2 * q.2)) :=
    contMDiff_comp_time hH₁ (contDiff_const.mul contDiff_id)
  have hB : ContMDiff (I.prod 𝓘(ℝ, ℝ)) I' ∞ (fun q : X × ℝ => H₂ (q.1, 2 * q.2 - 1)) :=
    contMDiff_comp_time hH₂ ((contDiff_const.mul contDiff_id).sub contDiff_const)
  refine ⟨fun q => if q.2 ≤ 1 / 2 then H₁ (q.1, 2 * q.2) else H₂ (q.1, 2 * q.2 - 1), ?_, ?_, ?_⟩
  · intro q
    by_cases hq2 : q.2 < 5 / 8
    · -- near `t ≤ 1/2`: agrees with the first piece
      refine (hA q).congr_of_eventuallyEq ?_
      have hopen : IsOpen {p : X × ℝ | p.2 < 5 / 8} := isOpen_lt continuous_snd continuous_const
      filter_upwards [hopen.mem_nhds hq2] with p (hp : p.2 < 5 / 8)
      by_cases hle : p.2 ≤ 1 / 2
      · simp only [hle, if_true]
      · simp only [hle, if_false]
        have hle' : 1 / 2 < p.2 := lt_of_not_ge hle
        rw [h₂0 p.1 _ (by linarith), h₁1 p.1 _ (by linarith)]
    · -- near `t ≥ 1/2`: agrees with the second piece
      have hq2' : 5 / 8 ≤ q.2 := le_of_not_gt hq2
      refine (hB q).congr_of_eventuallyEq ?_
      have hopen : IsOpen {p : X × ℝ | 3 / 8 < p.2} := isOpen_lt continuous_const continuous_snd
      filter_upwards [hopen.mem_nhds (show 3 / 8 < q.2 by linarith)] with p (hp : 3 / 8 < p.2)
      by_cases hle : p.2 ≤ 1 / 2
      · simp only [hle, if_true]
        rw [h₂0 p.1 _ (by linarith), h₁1 p.1 _ (by linarith)]
      · simp only [hle, if_false]
  · intro x
    simp only [show (0 : ℝ) ≤ 1 / 2 by norm_num, if_true, mul_zero]
    exact h₁0 x 0 (by norm_num)
  · intro x
    simp only [show ¬ (1 : ℝ) ≤ 1 / 2 by norm_num, if_false, mul_one]
    exact h₂1 x (2 - 1) (by norm_num)


end Milnor
