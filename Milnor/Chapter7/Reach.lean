import Milnor.Chapter7.Move
import Milnor.Chapter7.ChartSign
import Milnor.Chapter7.CancelMap
import Milnor.Chapter7.Segment
import Milnor.Chapter7.Lemma1

/-!
# Reaching every point of a component (Milnor §7, p. 51)

* Framed cobordism is reflexive (Theorem B and the constant homotopy).
* At every point of an oriented `M` there are frames of both signs (`exists_frame_of_sign`); this
  is now only the oriented reading of the orientation-free `exists_frame_of_selfSign` of
  `Chapter7/ChartSign.lean`.
* **Good chart balls.**  `exists_goodBall_free` produces a chart ball around `y` inside a given
  open set whose closure misses a given finite set; no orientation.  `exists_goodBall` adds, for a
  given orientation of `M`, that the chart is orientation-preserving on the ball.
* **Moving inside a ball.**  `move_in_ball` moves a framed point inside such a ball to any frame of
  the same *chart sign* — no orientation of `M`.  `move_in_ball_frameSign` is its oriented reading,
  obtained on a ball where the chart is orientation-preserving through
  `frameSign_eq_iff_chartSign_eq`.
* **Reach.** If `x₀ ∈ F.N` and `y` lies in the connected component of `x₀` in `M \ (F.N \ {x₀})`,
  then `F` is framed cobordant to the framed `0`-manifold obtained by moving `(x₀, v₀)` to
  `(y, v)`, for any frame `v` at `y` of the same sign.  Proof: the set of reachable points is
  open and closed in the component (a move inside a small chart ball, `exists_move`).  This is the
  one statement of the local theory that an orientation genuinely runs: the sign is compared across
  a whole connected component, so it is kept in its oriented form and re-proved through the bridge
  of `Chapter7/ChartSign.lean`.
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

include hMc hne in
/-- Framed cobordism is reflexive. -/
theorem FramedCobordant.refl' (F : FramedSub hM 0 m) : FramedCobordant hM F F := by
  letI := hM.chartedSpace
  haveI := hM.isManifold
  obtain ⟨k, hk, hkn, c, hc, hcb, -, hkF, -⟩ := exists_map_of_framedSub_subset hM hMc hne F _
    (linearIndependent_single (m := m)) univ isOpen_univ (subset_univ _) 0
  have hH : ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin m)).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, EuclideanSpace ℝ (Fin m))
      ∞ (fun q : M × ℝ => k q.1) :=
    hk.comp contMDiff_fst
  have h := framedCobordant_of_homotopy hM hMc hne (zero_add m) (ε := 1 / 4) (by norm_num)
    (by norm_num) hH (isRegularValue_comp_fst hM hk hkn) (fun x t _ => rfl)
    (fun x t _ => rfl) hk hkn hk hkn _ hcb
  have hkF' : pontryagin hM hMc hne hk hkn (zero_add m) _ hcb = F := hkF
  rw [hkF'] at h
  exact h

/-! ### Frames of prescribed sign -/

/-- **At every point there are frames of both signs.**  The content is orientation-free: by the
bridge `frameSign_eq_orEps_mul_selfSign` the sign of a frame relative to `oM` is the sign of its
determinant read in the chart at the point, times a factor depending only on the point, so this is
`exists_frame_of_selfSign` of `Chapter7/ChartSign.lean` with that factor put back. -/
theorem exists_frame_of_sign (hm : 0 < m)
    (oM : letI := hM.chartedSpace; Orient 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) M m) (x : M) {s : ℤ}
    (hs : s = 1 ∨ s = -1) :
    ∃ v : Fin m → EuclideanSpace ℝ (Fin (K + 1)), (∀ i, v i ∈ tangentM hM x) ∧
      LinearIndependent ℝ v ∧ frameSign hM oM v x = s :=
  exists_frame_of_frameSign hM hm oM x hs

/-! ### Good chart balls -/

/-- **A good chart ball.**  A chart ball around `y` avoiding a finite set `P ∌ y`, inside an open
set `C ∋ y`.  No orientation of `M`. -/
theorem exists_goodBall_free (y : M) {P : Set M} (hP : P.Finite) (hyP : y ∉ P) {C : Set M}
    (hC : IsOpen C) (hyC : y ∈ C) :
    letI := hM.chartedSpace; haveI := hM.isManifold;
    ∃ R : ℝ, 0 < R ∧
      closedBall (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) y y) R ⊆
        (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) y).target ∧
      (∀ z ∈ closure (ballU hM y R), z ∉ P) ∧ ballU hM y R ⊆ C := by
  letI := hM.chartedSpace
  haveI := hM.isManifold
  have hS : Pᶜ ∩ C ∈ 𝓝 y :=
    Filter.inter_mem (hP.isClosed.isOpen_compl.mem_nhds hyP) (hC.mem_nhds hyC)
  obtain ⟨R₁, hR₁, hR₁t, hR₁S⟩ := exists_ballU_subset y hS
  have hsub : ballU hM y (R₁ / 2) ⊆ ballU hM y R₁ := fun z hz => by
    rw [mem_ballU] at hz ⊢; exact ⟨hz.1, by linarith [hz.2]⟩
  refine ⟨R₁ / 2, by positivity, ?_, ?_, ?_⟩
  · exact (closedBall_subset_closedBall (by linarith)).trans hR₁t
  · intro z hz
    have h1 := closure_ballU_subset y ((closedBall_subset_closedBall (by linarith)).trans hR₁t) hz
    have h2 : z ∈ ballU hM y R₁ := by
      rw [mem_ballU]; exact ⟨h1.1, by linarith [h1.2]⟩
    exact (hR₁S h2).1
  · intro z hz
    exact (hR₁S (hsub hz)).2

/-- A good chart ball on which moreover the chart at `y` is orientation-preserving.  It is
`exists_goodBall_free` applied inside the interior of the set on which the compatibility field of
`oM` holds at `y`. -/
theorem exists_goodBall (oM : letI := hM.chartedSpace; Orient 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) M m)
    (y : M) {P : Set M} (hP : P.Finite) (hyP : y ∉ P) {C : Set M} (hC : IsOpen C) (hyC : y ∈ C) :
    letI := hM.chartedSpace; haveI := hM.isManifold;
    ∃ R : ℝ, 0 < R ∧
      closedBall (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) y y) R ⊆
        (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) y).target ∧
      (∀ z ∈ ballU hM y R, orSign (oM.or z) (oM.or y) (mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin m))
        𝓘(ℝ, EuclideanSpace ℝ (Fin m)) (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) y) z) = 1) ∧
      (∀ z ∈ closure (ballU hM y R), z ∉ P) ∧ ballU hM y R ⊆ C := by
  letI := hM.chartedSpace
  haveI := hM.isManifold
  have hSy : y ∈ interior {z : M | orSign (oM.or z) (oM.or y)
      (mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin m))
        (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) y) z) = 1} :=
    mem_interior_iff_mem_nhds.2 (oM.cont y)
  obtain ⟨R, hR, hRt, hcl, hRC⟩ :=
    exists_goodBall_free y hP hyP (hC.inter isOpen_interior) ⟨hyC, hSy⟩
  refine ⟨R, hR, hRt, ?_, hcl, fun z hz => (hRC hz).1⟩
  intro z hz
  have h := interior_subset (hRC hz).2
  exact h

/-! ### Moving inside a ball, and reach -/

/-- The frames of `F'` agree with those of `F` away from `x₀`. -/
def AgreesOff (F F' : FramedSub hM 0 m) (x₀ : M) : Prop :=
  ∀ i x (hx : x ∈ F.N) (_ : x ≠ x₀) (hx' : x ∈ F'.N), F'.v i ⟨x, hx'⟩ = F.v i ⟨x, hx⟩

include hMc hne in
/-- Inside a good ball around `y`, a framed point at `y₁` can be moved to `y₂` with any frame of
the same **chart sign** relative to the centre `y` of the ball, keeping the other points of `F`.
No orientation of `M`. -/
theorem move_in_ball (hm : 0 < m)
    (F : FramedSub hM 0 m) {x₀ : M} (y : M) (hy : y ∉ F.N \ {x₀}) {C : Set M} (hC : IsOpen C)
    (hyC : y ∈ C) :
    ∃ R : ℝ, 0 < R ∧ ballU hM y R ⊆ C ∧
      ∀ y₁ ∈ ballU hM y (R / 4), ∀ y₂ ∈ ballU hM y (R / 4), ∀ F' : FramedSub hM 0 m,
        F'.N = (F.N \ {x₀}) ∪ {y₁} → AgreesOff F F' x₀ → ∀ (hy₁ : y₁ ∈ F'.N)
        (v₂ : Fin m → EuclideanSpace ℝ (Fin (K + 1))), (∀ i, v₂ i ∈ tangentM hM y₂) →
        LinearIndependent ℝ v₂ →
        chartSign hM y y₂ v₂ = chartSign hM y y₁ (fun i => F'.v i ⟨y₁, hy₁⟩) →
        ∃ F'' : FramedSub hM 0 m, F''.N = (F.N \ {x₀}) ∪ {y₂} ∧ AgreesOff F F'' x₀ ∧
          (∀ i (hy₂ : y₂ ∈ F''.N), F''.v i ⟨y₂, hy₂⟩ = v₂ i) ∧ FramedCobordant hM F' F'' := by
  letI := hM.chartedSpace
  haveI := hM.isManifold
  obtain ⟨R, hR, hRt, hcl, hRC⟩ :=
    exists_goodBall_free y (F.finite_N.diff) hy hC hyC
  refine ⟨R, hR, hRC, ?_⟩
  intro y₁ hy₁U y₂ hy₂U F' hN' hoff hy₁ v₂ hv₂T hv₂ hsign
  have hsub : ballU hM y (R / 4) ⊆ ballU hM y R := fun z hz => by
    rw [mem_ballU] at hz ⊢; exact ⟨hz.1, by linarith [hz.2]⟩
  have hy₁P : y₁ ∉ F.N \ {x₀} := hcl y₁ (subset_closure (hsub hy₁U))
  have hFU : ∀ x ∈ F'.N, x ≠ y₁ → x ∉ closure (ballU hM y R) := by
    intro x hx hxy hxc
    rw [hN'] at hx
    rcases hx with hx | hx
    · exact hcl x hxc hx
    · exact hxy hx
  obtain ⟨F'', hN'', hoff'', hv'', hcob⟩ :=
    exists_move hMc hne hm F' y hR hRt hy₁ hy₁U hFU hy₂U hv₂T hv₂ hsign
  refine ⟨F'', ?_, ?_, hv'', hcob⟩
  · rw [hN'', hN']
    ext z
    simp only [mem_union, Set.mem_sdiff, mem_singleton_iff]
    constructor
    · rintro (⟨⟨hz, hzx⟩ | rfl, hzy⟩ | rfl)
      · exact Or.inl ⟨hz, hzx⟩
      · exact absurd rfl hzy
      · exact Or.inr rfl
    · rintro (⟨hz, hzx⟩ | rfl)
      · exact Or.inl ⟨Or.inl ⟨hz, hzx⟩, fun h => hy₁P (h ▸ ⟨hz, hzx⟩)⟩
      · exact Or.inr rfl
  · intro i x hx hxx hx''
    have hxy₁ : x ≠ y₁ := fun h => hy₁P (h ▸ ⟨hx, hxx⟩)
    have hx' : x ∈ F'.N := by rw [hN']; exact Or.inl ⟨hx, hxx⟩
    rw [hoff'' i x hx' hxy₁ hx'', hoff i x hx hxx hx']

include hMc hne in
/-- The oriented reading of `move_in_ball`: the two frames are compared through an orientation `oM`
of `M`.  The ball is chosen so that the chart at its centre is orientation-preserving on it, and
there equality of frame signs is equality of chart signs
(`frameSign_eq_iff_chartSign_eq`). -/
theorem move_in_ball_frameSign (hm : 0 < m)
    (oM : letI := hM.chartedSpace; Orient 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) M m)
    (F : FramedSub hM 0 m) {x₀ : M} (y : M) (hy : y ∉ F.N \ {x₀}) {C : Set M} (hC : IsOpen C)
    (hyC : y ∈ C) :
    ∃ R : ℝ, 0 < R ∧ ballU hM y R ⊆ C ∧
      ∀ y₁ ∈ ballU hM y (R / 4), ∀ y₂ ∈ ballU hM y (R / 4), ∀ F' : FramedSub hM 0 m,
        F'.N = (F.N \ {x₀}) ∪ {y₁} → AgreesOff F F' x₀ → ∀ (hy₁ : y₁ ∈ F'.N)
        (v₂ : Fin m → EuclideanSpace ℝ (Fin (K + 1))), (∀ i, v₂ i ∈ tangentM hM y₂) →
        LinearIndependent ℝ v₂ →
        frameSign hM oM v₂ y₂ = frameSign hM oM (fun i => F'.v i ⟨y₁, hy₁⟩) y₁ →
        ∃ F'' : FramedSub hM 0 m, F''.N = (F.N \ {x₀}) ∪ {y₂} ∧ AgreesOff F F'' x₀ ∧
          (∀ i (hy₂ : y₂ ∈ F''.N), F''.v i ⟨y₂, hy₂⟩ = v₂ i) ∧ FramedCobordant hM F' F'' := by
  letI := hM.chartedSpace
  haveI := hM.isManifold
  have hSy : y ∈ interior {z : M | orSign (oM.or z) (oM.or y)
      (mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin m))
        (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) y) z) = 1} :=
    mem_interior_iff_mem_nhds.2 (oM.cont y)
  obtain ⟨R, hR, hRC, hmove⟩ :=
    move_in_ball hMc hne hm F (x₀ := x₀) y hy (hC.inter isOpen_interior) ⟨hyC, hSy⟩
  have hpos : ∀ z ∈ ballU hM y R, orSign (oM.or z) (oM.or y)
      (mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin m))
        (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) y) z) = 1 := by
    intro z hz
    have h := interior_subset (hRC hz).2
    exact h
  have hsub : ballU hM y (R / 4) ⊆ ballU hM y R := fun z hz => by
    rw [mem_ballU] at hz ⊢; exact ⟨hz.1, by linarith [hz.2]⟩
  refine ⟨R, hR, fun z hz => (hRC hz).1, ?_⟩
  intro y₁ hy₁U y₂ hy₂U F' hN' hoff hy₁ v₂ hv₂T hv₂ hsign
  exact hmove y₁ hy₁U y₂ hy₂U F' hN' hoff hy₁ v₂ hv₂T hv₂
    ((frameSign_eq_iff_chartSign_eq hM oM (hpos y₂ (hsub hy₂U)) (hpos y₁ (hsub hy₁U)) v₂
      (fun i => F'.v i ⟨y₁, hy₁⟩)).1 hsign)

include hMc hne in
/-- **Reach.** Every point of the component of `x₀` in `M \ (F.N \ {x₀})` can be reached, with
any frame of the right sign. -/
theorem exists_reach (hm : 0 < m)
    (oM : letI := hM.chartedSpace; Orient 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) M m)
    (F : FramedSub hM 0 m) {x₀ : M} (hx₀ : x₀ ∈ F.N) {y : M} (hy : y ∈ compl' F.N x₀)
    {v : Fin m → EuclideanSpace ℝ (Fin (K + 1))} (hvT : ∀ i, v i ∈ tangentM hM y)
    (hv : LinearIndependent ℝ v)
    (hs : frameSign hM oM v y = frameSign hM oM (fun i => F.v i ⟨x₀, hx₀⟩) x₀) :
    ∃ F' : FramedSub hM 0 m, F'.N = (F.N \ {x₀}) ∪ {y} ∧ AgreesOff F F' x₀ ∧
      (∀ i (hy' : y ∈ F'.N), F'.v i ⟨y, hy'⟩ = v i) ∧ FramedCobordant hM F F' := by
  letI := hM.chartedSpace
  haveI := hM.isManifold
  haveI := locallyConnectedSpace_M (hM := hM)
  set s := frameSign hM oM (fun i => F.v i ⟨x₀, hx₀⟩) x₀ with hsdef
  have hs' : s = 1 ∨ s = -1 := by
    have h1 := frameSign_ne_zero hM oM (fun i => F.tangent i ⟨x₀, hx₀⟩) (F.indep ⟨x₀, hx₀⟩)
    have h2 := orSign_eq_one_or_neg_one finrank_E finrank_E (stdOr m) (oM.or x₀)
      (basisCLM_bijective (linearIndependent_chartCoord hM (fun i => F.tangent i ⟨x₀, hx₀⟩)
        (F.indep ⟨x₀, hx₀⟩)))
    exact h2
  set C := compl' F.N x₀ with hCdef
  have hC : IsOpen C := isOpen_compl' F.finite_N x₀
  have hCP : ∀ z ∈ C, z ∉ F.N \ {x₀} := fun z hz => compl'_subset F.N x₀ hz
  -- the reachable points
  set Reach : Set M := {z | ∃ F' : FramedSub hM 0 m, F'.N = (F.N \ {x₀}) ∪ {z} ∧ AgreesOff F F' x₀ ∧
    (∃ hz : z ∈ F'.N, frameSign hM oM (fun i => F'.v i ⟨z, hz⟩) z = s) ∧ FramedCobordant hM F F'}
    with hReach
  have hx₀R : x₀ ∈ Reach := by
    refine ⟨F, ?_, fun i x hx _ hx' => rfl, ⟨hx₀, rfl⟩, FramedCobordant.refl' hMc hne F⟩
    ext z; simp only [mem_union, Set.mem_sdiff, mem_singleton_iff]
    constructor
    · intro hz; by_cases h : z = x₀
      · exact Or.inr h
      · exact Or.inl ⟨hz, h⟩
    · rintro (⟨hz, -⟩ | rfl); exact hz; exact hx₀
  -- the two open sets
  set u : Set M := {z | z ∈ C ∧ z ∈ Reach}
  set v' : Set M := C ∩ (closure Reach)ᶜ
  have hu : IsOpen u := by
    rw [isOpen_iff_forall_mem_open]
    rintro z ⟨hzC, hzR⟩
    obtain ⟨R, hR, hRC, hmove⟩ :=
      move_in_ball_frameSign hMc hne hm oM F (x₀ := x₀) z (hCP z hzC) hC hzC
    refine ⟨ballU hM z (R / 4), ?_, isOpen_ballU z (R / 4), x_c_mem_ballU z (by positivity)⟩
    intro y₂ hy₂
    have hsub' : ballU hM z (R / 4) ⊆ ballU hM z R := fun q hq => by
      rw [mem_ballU] at hq ⊢; exact ⟨hq.1, by linarith [hq.2]⟩
    have hy₂C : y₂ ∈ C := hRC (hsub' hy₂)
    obtain ⟨F', hN', hoff, ⟨hz', hsz⟩, hcob⟩ := hzR
    obtain ⟨v₂, hv₂T, hv₂, hv₂s⟩ := exists_frame_of_sign hm oM y₂ hs'
    obtain ⟨F'', hN'', hoff'', hv'', hcob'⟩ := hmove z (x_c_mem_ballU z (by positivity)) y₂ hy₂ F'
      hN' hoff hz' v₂ hv₂T hv₂ (by rw [hv₂s, hsz])
    have hy₂'' : y₂ ∈ F''.N := by rw [hN'']; exact Or.inr (mem_singleton y₂)
    refine ⟨hy₂C, F'', hN'', hoff'', ⟨hy₂'', ?_⟩, hcob.trans hcob'⟩
    have : (fun i => F''.v i ⟨y₂, hy₂''⟩) = v₂ := funext fun i => hv'' i hy₂''
    rw [this]; exact hv₂s
  have hv' : IsOpen v' := hC.inter isClosed_closure.isOpen_compl
  have hcover : C ⊆ u ∪ v' := by
    intro z hzC
    by_cases hzcl : z ∈ closure Reach
    · left
      refine ⟨hzC, ?_⟩
      obtain ⟨R, hR, hRC, hmove⟩ :=
        move_in_ball_frameSign hMc hne hm oM F (x₀ := x₀) z (hCP z hzC) hC hzC
      obtain ⟨y₁, hy₁U, hy₁R⟩ := mem_closure_iff.1 hzcl (ballU hM z (R / 4)) (isOpen_ballU _ _)
        (x_c_mem_ballU z (by positivity))
      obtain ⟨F', hN', hoff, ⟨hy₁', hsy₁⟩, hcob⟩ := hy₁R
      obtain ⟨v₂, hv₂T, hv₂, hv₂s⟩ := exists_frame_of_sign hm oM z hs'
      obtain ⟨F'', hN'', hoff'', hv'', hcob'⟩ := hmove y₁ hy₁U z (x_c_mem_ballU z (by positivity))
        F' hN' hoff hy₁' v₂ hv₂T hv₂ (by rw [hv₂s, hsy₁])
      have hz'' : z ∈ F''.N := by rw [hN'']; exact Or.inr (mem_singleton z)
      refine ⟨F'', hN'', hoff'', ⟨hz'', ?_⟩, hcob.trans hcob'⟩
      have : (fun i => F''.v i ⟨z, hz''⟩) = v₂ := funext fun i => hv'' i hz''
      rw [this]; exact hv₂s
    · right; exact ⟨hzC, hzcl⟩
  have hdisj : Disjoint u v' := by
    rw [Set.disjoint_left]
    rintro z ⟨-, hzR⟩ ⟨-, hzcl⟩
    exact hzcl (subset_closure hzR)
  have hCu : C ⊆ u :=
    (isPreconnected_connectedComponentIn).subset_left_of_subset_union hu hv' hdisj hcover
      ⟨x₀, mem_compl'_self, mem_compl'_self, hx₀R⟩
  -- `y` is reachable; adjust the frame
  obtain ⟨-, F₁, hN₁, hoff₁, ⟨hy₁, hsy₁⟩, hcob₁⟩ := hCu hy
  obtain ⟨R, hR, -, hmove⟩ :=
    move_in_ball_frameSign hMc hne hm oM F (x₀ := x₀) y (hCP y hy) isOpen_univ (mem_univ y)
  obtain ⟨F'', hN'', hoff'', hv'', hcob'⟩ := hmove y (x_c_mem_ballU y (by positivity)) y
    (x_c_mem_ballU y (by positivity)) F₁ hN₁ hoff₁ hy₁ v hvT hv (by rw [hs, hsy₁])
  exact ⟨F'', hN'', hoff'', hv'', hcob₁.trans hcob'⟩

end Framed

end Milnor
