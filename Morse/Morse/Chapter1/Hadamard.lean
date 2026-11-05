import Milnor.Chapter6.Hadamard
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Convex.Star

/-!
Milnor, *Morse Theory*, §2, p. 5.

# Hadamard's lemma (Milnor's Lemma 2.1)

**Lemma 2.1** (Milnor, p. 5), paraphrased: if `f` is `C^∞` on a convex neighbourhood `V` of `0`
in `ℝⁿ` and `f(0) = 0`, then `f(x) = ∑ᵢ xᵢ gᵢ(x)` on `V` for some `C^∞` functions `gᵢ` on `V`
with `gᵢ(0) = ∂f/∂xᵢ(0)`.  Milnor's proof writes `f(x)` as the integral over `t ∈ [0, 1]` of
`(d/dt) f(tx) = ∑ᵢ xᵢ ∂f/∂xᵢ(tx)` and takes `gᵢ(x) = ∫₀¹ ∂f/∂xᵢ(tx) dt`.

## Relation to the sister project

The sister project formalizing Milnor's *Topology from the Differentiable Viewpoint* proves, in
`Milnor/Chapter6/Hadamard.lean` (imported here), Hadamard's lemma for a *globally* defined smooth
`f` (`Milnor.exists_hadamard`: `f x = L x (x)`, `L x = ∫₀¹ d f_{t x} dt` smooth, `L 0 = d f₀`),
together with the smoothness of parametric integrals `x ↦ ∫₀¹ h (x, t) dt` for globally smooth
`h` (`Milnor.contDiff_intervalIntegral`, `Milnor.contDiff_intervalIntegral_infty`).  There it
served §6, Lemma 2, p. 33 of that book.  Milnor's Lemma 2.1 is local (`f` is only defined on
`V`), so this file proves the local versions, by the same method.

## What Milnor leaves implicit

* **Differentiation under the integral sign.**  The smoothness of `gᵢ` is not argued in the
  text.  It is the statement `Morse.contDiffOn_intervalIntegral`: a parametric integral over
  `[0, 1]` of a `Cⁿ` integrand is `Cⁿ`, proved by induction on `n` with a domination bound on a
  tube around the compact segment `{x} × [0, 1]`.  Milnor's `f` is only defined on `V`, so the
  integrand `(x, t) ↦ ∂f/∂xᵢ(tx)` is only defined (and smooth) on the open set
  `{(x, t) | tx ∈ V}`; this is why the local version is needed.
* **Convexity is used only through star-shapedness about `0`**: for `x ∈ V` and `t ∈ [0, 1]`,
  `tx ∈ V`.  We assume `V` open and star-shaped about `0` (`StarConvex ℝ 0 V`); a convex
  neighbourhood of `0` contains an open convex one (its interior), so nothing is lost.
* **The second-order form used on p. 6.**  In the proof of Lemma 2.2 Milnor applies 2.1 twice,
  `f = ∑ xᵢ xⱼ hᵢⱼ`, symmetrizes `h̄ᵢⱼ = ½ (hᵢⱼ + hⱼᵢ)`, and asserts without proof that
  `(h̄ᵢⱼ(0)) = (½ ∂²f/∂xⁱ∂xʲ(0))`.  (This follows by differentiating `f = ∑ xᵢ xⱼ h̄ᵢⱼ` twice at
  `0`, but he does not say so.)  We obtain the second-order form in one step from Taylor's formula
  with integral remainder, `B x = ∫₀¹ (1 - t) d²f_{tx} dt`, for which `B 0 = ½ d²f₀` is a
  one-line computation and the symmetry of `B x` is the symmetry of second derivatives:
  `Morse.exists_hadamard_two_on`.

## Main results

* `Morse.contDiffOn_intervalIntegral`, `Morse.contDiffOn_intervalIntegral_infty`: if
  `h : E × ℝ → F` is `Cⁿ` (resp. `C^∞`) on an open set `U ⊆ E × ℝ`, then
  `x ↦ ∫₀¹ h (x, t) dt` is `Cⁿ` (resp. `C^∞`) on any open `V ⊆ E` with `V × [0, 1] ⊆ U`.
* `Morse.exists_hadamard_on`: **Lemma 2.1, coordinate free**: if `f` is smooth on an open set
  `V` star-shaped about `0` and `f 0 = 0`, then `f x = L x (x)` on `V` with `L` smooth on `V`
  and `L 0 = d f₀`.
* `Morse.exists_hadamard_coord`: **Lemma 2.1 as Milnor states it**, in coordinates on `ℝⁿ`:
  `f x = ∑ᵢ xᵢ gᵢ(x)` with `gᵢ` smooth on `V` and `gᵢ(0) = ∂f/∂xᵢ(0)`.
* `Morse.exists_hadamard_two_on`: **the second-order form** used in the proof of Lemma 2.2:
  if moreover `d f₀ = 0` then `f x = B x (x) (x)` on `V` with `B` smooth on `V`, each `B x`
  a symmetric bilinear map, and `B 0 = ½ d²f₀`.
-/

open Set Filter MeasureTheory
open scoped ContDiff Interval Topology

noncomputable section

namespace Morse

universe u v

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {F : Type v} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-! ### Local versions: integrands defined on an open set

Milnor's `f` in Lemma 2.1 is only defined on the neighbourhood `V`, so the integrand
`(x, t) ↦ d f_{t x}` is only defined (and smooth) on the open set `{(x, t) | t x ∈ V}`. -/

omit [NormedSpace ℝ E] in
/-- **A tube around the segment `{x₀} × [0, 1]`.**  If `h` is continuous on an open set
`U ⊆ E × ℝ` containing `{x₀} × [0, 1]`, there are open sets `s ∋ x₀` and `w ⊇ [0, 1]` with
`s × w ⊆ U`, on which `h` is bounded. -/
theorem exists_tube_bound {X : Type*} [NormedAddCommGroup X] {h : E × ℝ → X}
    {U : Set (E × ℝ)} (hU : IsOpen U) (hh : ContinuousOn h U) {x₀ : E}
    (hx₀ : ∀ t ∈ Icc (0 : ℝ) 1, (x₀, t) ∈ U) :
    ∃ M : ℝ, ∃ s : Set E, ∃ w : Set ℝ, IsOpen s ∧ IsOpen w ∧ x₀ ∈ s ∧ Icc (0 : ℝ) 1 ⊆ w ∧
      s ×ˢ w ⊆ U ∧ ∀ p ∈ s ×ˢ w, ‖h p‖ ≤ M := by
  have hK : IsCompact (({x₀} : Set E) ×ˢ Icc (0 : ℝ) 1) := isCompact_singleton.prod isCompact_Icc
  have hKU : ({x₀} : Set E) ×ˢ Icc (0 : ℝ) 1 ⊆ U := by
    rintro ⟨x, t⟩ ⟨hx, ht⟩
    rw [mem_singleton_iff] at hx
    subst hx
    exact hx₀ t ht
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn (hh.mono hKU)
  have hopen : IsOpen (U ∩ h ⁻¹' {y | ‖y‖ < M + 1}) :=
    hh.isOpen_inter_preimage hU (isOpen_lt continuous_norm continuous_const)
  obtain ⟨s, w, hs, hw, hxs, hIw, hsw⟩ := generalized_tube_lemma isCompact_singleton
    isCompact_Icc hopen (fun p hp => ⟨hKU hp, lt_of_le_of_lt (hM p hp) (lt_add_one M)⟩)
  exact ⟨M + 1, s, w, hs, hw, singleton_subset_iff.1 hxs, hIw, fun p hp => (hsw hp).1,
    fun p hp => (hsw hp).2.le⟩

theorem uIoc_zero_one_subset : Ι (0 : ℝ) 1 ⊆ Icc 0 1 := by
  rw [uIoc_of_le zero_le_one]
  exact Ioc_subset_Icc_self

/-- The induction behind `Morse.contDiffOn_intervalIntegral`, the local version of the sister
project's `Milnor.contDiff_intervalIntegral`, with the same proof.  As there, the target lives in
the universe `max u v`, because each step of the induction replaces the target `G` by
`E →L[ℝ] G`. -/
private theorem contDiffOn_intervalIntegral_aux {V : Set E} (hV : IsOpen V) (n : ℕ) :
    ∀ {G : Type max u v} [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
      {h : E × ℝ → G} {U : Set (E × ℝ)}, IsOpen U →
      (∀ x ∈ V, ∀ t ∈ Icc (0 : ℝ) 1, (x, t) ∈ U) →
      ContDiffOn ℝ n h U → ContDiffOn ℝ n (fun x => ∫ t in (0 : ℝ)..1, h (x, t)) V := by
  induction n with
  | zero =>
      intro G _ _ _ h U hU hVU hh
      simp only [Nat.cast_zero, contDiffOn_zero] at hh ⊢
      intro x₀ hx₀
      obtain ⟨M, s, w, hs, -, hx₀s, hIw, hswU, hM⟩ := exists_tube_bound hU hh (hVU x₀ hx₀)
      have hcs : ∀ x ∈ s, ContinuousOn (fun t => h (x, t)) (Ι (0 : ℝ) 1) := fun x hx =>
        (hh.mono hswU).comp (continuousOn_const.prodMk continuousOn_id)
          (fun t ht => mk_mem_prod hx (hIw (uIoc_zero_one_subset ht)))
      refine ContinuousAt.continuousWithinAt ?_
      refine intervalIntegral.continuousAt_of_dominated_interval (bound := fun _ => M) ?_ ?_
        intervalIntegrable_const ?_
      · filter_upwards [hs.mem_nhds hx₀s] with x hx
        exact (hcs x hx).aestronglyMeasurable measurableSet_uIoc
      · filter_upwards [hs.mem_nhds hx₀s] with x hx
        exact .of_forall fun t ht => hM _ (mk_mem_prod hx (hIw (uIoc_zero_one_subset ht)))
      · refine .of_forall fun t ht => ?_
        have hat : ContinuousAt h (x₀, t) :=
          hh.continuousAt (hU.mem_nhds (hVU x₀ hx₀ t (uIoc_zero_one_subset ht)))
        exact hat.comp (f := fun x : E => (x, t)) (continuousAt_id.prodMk continuousAt_const)
  | succ n ih =>
      intro G _ _ _ h U hU hVU hh
      push_cast at hh ⊢
      have hc : ContinuousOn h U := hh.continuousOn
      have hdf : DifferentiableOn ℝ h U := hh.differentiableOn (by simp)
      have hD : ContDiffOn ℝ (n : WithTop ℕ∞)
          (fun p : E × ℝ => (fderiv ℝ h p).comp (ContinuousLinearMap.inl ℝ E ℝ)) U :=
        (hh.fderiv_of_isOpen hU le_rfl).clm_comp contDiffOn_const
      have hDc : ContinuousOn
          (fun p : E × ℝ => (fderiv ℝ h p).comp (ContinuousLinearMap.inl ℝ E ℝ)) U :=
        hD.continuousOn
      -- differentiation under the integral sign
      have key : ∀ x₀ ∈ V, HasFDerivAt (fun x => ∫ t in (0 : ℝ)..1, h (x, t))
          (∫ t in (0 : ℝ)..1, (fderiv ℝ h (x₀, t)).comp (ContinuousLinearMap.inl ℝ E ℝ)) x₀ := by
        intro x₀ hx₀
        obtain ⟨M, s, w, hs, -, hx₀s, hIw, hswU, hM⟩ := exists_tube_bound hU hDc (hVU x₀ hx₀)
        have hmem : ∀ x ∈ s, ∀ t ∈ Ι (0 : ℝ) 1, (x, t) ∈ s ×ˢ w := fun x hx t ht =>
          mk_mem_prod hx (hIw (uIoc_zero_one_subset ht))
        have hcs : ∀ x ∈ s, ContinuousOn (fun t => h (x, t)) (Ι (0 : ℝ) 1) := fun x hx =>
          (hc.mono hswU).comp (continuousOn_const.prodMk continuousOn_id) (hmem x hx)
        have hx₀I : ContinuousOn (fun t => h (x₀, t)) (uIcc (0 : ℝ) 1) := by
          rw [uIcc_of_le zero_le_one]
          exact hc.comp (continuousOn_const.prodMk continuousOn_id) (fun t ht => hVU x₀ hx₀ t ht)
        have hD₀ : ContinuousOn
            (fun t => (fderiv ℝ h (x₀, t)).comp (ContinuousLinearMap.inl ℝ E ℝ)) (Ι (0 : ℝ) 1) :=
          (hDc.mono hswU).comp (continuousOn_const.prodMk continuousOn_id) (hmem x₀ hx₀s)
        refine intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le
          (F := fun (x : E) (t : ℝ) => h (x, t))
          (F' := fun (x : E) (t : ℝ) => (fderiv ℝ h (x, t)).comp (ContinuousLinearMap.inl ℝ E ℝ))
          (bound := fun _ => M) (hs.mem_nhds hx₀s) ?_ (hx₀I.intervalIntegrable)
          (hD₀.aestronglyMeasurable measurableSet_uIoc)
          (.of_forall fun t ht x hx => hM _ (hmem x hx t ht)) intervalIntegrable_const
          (.of_forall fun t ht x hx => ?_)
        · filter_upwards [hs.mem_nhds hx₀s] with x hx
          exact (hcs x hx).aestronglyMeasurable measurableSet_uIoc
        · have hxt : (x, t) ∈ U := hswU (hmem x hx t ht)
          exact ((hdf _ hxt).differentiableAt (hU.mem_nhds hxt)).hasFDerivAt.comp x
            ((hasFDerivAt_id x).prodMk (hasFDerivAt_const t x))
      rw [contDiffOn_succ_iff_fderiv_of_isOpen hV]
      refine ⟨fun x hx => (key x hx).differentiableAt.differentiableWithinAt, by simp, ?_⟩
      exact (ih hU hVU hD).congr fun x hx => (key x hx).fderiv

/-- **Smoothness of a parametric integral, local version.**  Let `U ⊆ E × ℝ` be open and
`h : E × ℝ → F` be `Cⁿ` on `U` (`F` complete).  Then `x ↦ ∫ t in 0..1, h (x, t)` is `Cⁿ` on
every open `V ⊆ E` with `V × [0, 1] ⊆ U`. -/
theorem contDiffOn_intervalIntegral (n : ℕ) {h : E × ℝ → F} {U : Set (E × ℝ)} {V : Set E}
    (hU : IsOpen U) (hV : IsOpen V) (hVU : ∀ x ∈ V, ∀ t ∈ Icc (0 : ℝ) 1, (x, t) ∈ U)
    (hh : ContDiffOn ℝ n h U) : ContDiffOn ℝ n (fun x => ∫ t in (0 : ℝ)..1, h (x, t)) V := by
  -- move the target up to the universe `max u v`, as in `Milnor.contDiff_intervalIntegral`
  have e : F ≃L[ℝ] ULift.{u} F := ContinuousLinearEquiv.ulift.symm
  have hup : ContDiffOn ℝ (n : WithTop ℕ∞)
      (fun p : E × ℝ => (e : F →L[ℝ] ULift.{u} F) (h p)) U :=
    (e : F →L[ℝ] ULift.{u} F).contDiff.comp_contDiffOn hh
  have key := contDiffOn_intervalIntegral_aux hV n hU hVU hup
  have hdown : ContDiffOn ℝ (n : WithTop ℕ∞) (fun x =>
      (e.symm : ULift.{u} F →L[ℝ] F) (∫ t in (0 : ℝ)..1, (e : F →L[ℝ] ULift.{u} F) (h (x, t))))
      V :=
    (e.symm : ULift.{u} F →L[ℝ] F).contDiff.comp_contDiffOn key
  refine hdown.congr fun x hx => ?_
  have hint : IntervalIntegrable (fun t : ℝ => h (x, t)) volume 0 1 := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le zero_le_one]
    exact hh.continuousOn.comp (continuousOn_const.prodMk continuousOn_id)
      (fun t ht => hVU x hx t ht)
  rw [ContinuousLinearMap.intervalIntegral_comp_comm (e : F →L[ℝ] ULift.{u} F) hint]
  simp

/-- **Smoothness of a parametric integral, local `C^∞` version.** -/
theorem contDiffOn_intervalIntegral_infty {h : E × ℝ → F} {U : Set (E × ℝ)} {V : Set E}
    (hU : IsOpen U) (hV : IsOpen V) (hVU : ∀ x ∈ V, ∀ t ∈ Icc (0 : ℝ) 1, (x, t) ∈ U)
    (hh : ContDiffOn ℝ ∞ h U) : ContDiffOn ℝ ∞ (fun x => ∫ t in (0 : ℝ)..1, h (x, t)) V :=
  contDiffOn_infty.2 fun n =>
    contDiffOn_intervalIntegral n hU hV hVU (contDiffOn_infty.1 hh n)

/-- The integrals `x ↦ ∫₀¹ a(t) g(t x) dt` met in Hadamard's lemma are smooth on an open set
star-shaped about `0` on which `g` is smooth, for any smooth weight `a`. -/
theorem contDiffOn_integral_smul_comp {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    [CompleteSpace G] {g : E → G} {V : Set E} (hV : IsOpen V) (hV0 : StarConvex ℝ 0 V)
    {a : ℝ → ℝ} (ha : ContDiff ℝ ∞ a) (hg : ContDiffOn ℝ ∞ g V) :
    ContDiffOn ℝ ∞ (fun x => ∫ t in (0 : ℝ)..1, a t • g (t • x)) V := by
  have hc : Continuous fun p : E × ℝ => p.2 • p.1 := continuous_snd.smul continuous_fst
  refine contDiffOn_intervalIntegral_infty (h := fun p : E × ℝ => a p.2 • g (p.2 • p.1))
    (U := (fun p : E × ℝ => p.2 • p.1) ⁻¹' V) (hV.preimage hc) hV
    (fun x hx t ht => hV0.smul_mem hx ht.1 ht.2) ?_
  exact (ha.comp contDiff_snd).contDiffOn.smul
    (hg.comp (contDiff_snd.smul contDiff_fst).contDiffOn fun p hp => hp)

/-- **Hadamard's lemma on a star-shaped open set** (Milnor's Lemma 2.1, coordinate free).
Let `V ⊆ E` be open and star-shaped about `0`, and `f : E → F` smooth on `V` with `f 0 = 0`
(`F` complete).  Then `f x = L x (x)` for `x ∈ V`, where `L x = ∫₀¹ d f_{t x} dt` is smooth on
`V`, and `L 0 = d f₀`. -/
theorem exists_hadamard_on {f : E → F} {V : Set E} (hV : IsOpen V) (hV0 : StarConvex ℝ 0 V)
    (hf : ContDiffOn ℝ ∞ f V) (hf0 : f 0 = 0) :
    ∃ L : E → (E →L[ℝ] F), ContDiffOn ℝ ∞ L V ∧ (∀ x ∈ V, f x = L x x) ∧
      L 0 = fderiv ℝ f 0 := by
  have hfd : ContDiffOn ℝ ∞ (fderiv ℝ f) V := hf.fderiv_of_isOpen hV (by simp)
  refine ⟨fun x => ∫ t in (0 : ℝ)..1, fderiv ℝ f (t • x), ?_, ?_, ?_⟩
  · simpa using contDiffOn_integral_smul_comp hV hV0 contDiff_const hfd (a := fun _ => (1 : ℝ))
  · intro x hx
    have hseg : ∀ t ∈ Icc (0 : ℝ) 1, t • x ∈ V := fun t ht => hV0.smul_mem hx ht.1 ht.2
    -- the fundamental theorem of calculus along the segment from `0` to `x`
    have taylor := map_add_eq_sum_add_integral_iteratedFDeriv (n := 0) (f := f) (x := 0) (y := x)
      fun t ht => (hf.contDiffAt (hV.mem_nhds (by simpa using hseg t ht))).of_le (by simp)
    have hint : IntervalIntegrable (fun t : ℝ => fderiv ℝ f (t • x)) volume 0 1 := by
      refine ContinuousOn.intervalIntegrable ?_
      rw [uIcc_of_le zero_le_one]
      exact hfd.continuousOn.comp (continuous_id.smul continuous_const).continuousOn hseg
    have hpull : (∫ t in (0 : ℝ)..1, fderiv ℝ f (t • x)) x
        = ∫ t in (0 : ℝ)..1, fderiv ℝ f (t • x) x :=
      ((ContinuousLinearMap.apply ℝ F x).intervalIntegral_comp_comm hint).symm
    change f x = (∫ t in (0 : ℝ)..1, fderiv ℝ f (t • x)) x
    rw [hpull]
    simpa [hf0, iteratedFDeriv_one_apply] using taylor
  · simp

/-- **Milnor's Lemma 2.1, in coordinates** (p. 5).  Let `V ⊆ ℝⁿ` be an open convex neighbourhood
of `0` and `f` a smooth function on `V` with `f(0) = 0`.  Then
`f(x₁, …, xₙ) = ∑ᵢ xᵢ gᵢ(x₁, …, xₙ)` on `V` for some functions `gᵢ` smooth on `V` with
`gᵢ(0) = ∂f/∂xᵢ(0)`.  Here `ℝⁿ = Fin n → ℝ` and `∂f/∂xᵢ(0)` is `d f₀` applied to the `i`-th
basis vector `Pi.single i 1`. -/
theorem exists_hadamard_coord {n : ℕ} {V : Set (Fin n → ℝ)} (hV : IsOpen V) (hVc : Convex ℝ V)
    (h0 : (0 : Fin n → ℝ) ∈ V) {f : (Fin n → ℝ) → ℝ} (hf : ContDiffOn ℝ ∞ f V) (hf0 : f 0 = 0) :
    ∃ g : Fin n → (Fin n → ℝ) → ℝ, (∀ i, ContDiffOn ℝ ∞ (g i) V) ∧
      (∀ x ∈ V, f x = ∑ i, x i * g i x) ∧
      ∀ i, g i 0 = fderiv ℝ f 0 (Pi.single i 1) := by
  obtain ⟨L, hL, hfL, hL0⟩ := exists_hadamard_on hV (hVc.starConvex h0) hf hf0
  refine ⟨fun i x => L x (Pi.single i 1), fun i => hL.clm_apply contDiffOn_const, ?_, ?_⟩
  · intro x hx
    have hx' : x = ∑ i, x i • (Pi.single i (1 : ℝ) : Fin n → ℝ) := by
      ext j
      simp [Pi.single_apply]
    calc f x = L x x := hfL x hx
      _ = L x (∑ i, x i • (Pi.single i (1 : ℝ) : Fin n → ℝ)) := by rw [← hx']
      _ = ∑ i, x i * L x (Pi.single i 1) := by simp [map_sum, map_smul]
  · intro i
    simp [hL0]

/-- **Hadamard's lemma to second order** (the form of Lemma 2.1 used in the proof of Lemma 2.2,
p. 6).  Let `V ⊆ E` be open and star-shaped about `0`, and `f : E → F` smooth on `V` with
`f 0 = 0` and `d f₀ = 0`.  Then `f x = B x (x) (x)` for `x ∈ V`, where
`B x = ∫₀¹ (1 - t) d²f_{t x} dt` is smooth on `V`, each `B x` (`x ∈ V`) is a symmetric bilinear
map, and `B 0 = ½ d²f₀`.

Milnor obtains this by applying Lemma 2.1 twice and symmetrizing, and asserts without proof that
the symmetrized coefficients at `0` are `½ ∂²f/∂xⁱ∂xʲ(0)`.  Here it is Taylor's formula with
integral remainder (`map_add_eq_sum_add_integral_iteratedFDeriv` with `n = 1`), which gives that
value at once. -/
theorem exists_hadamard_two_on {f : E → F} {V : Set E} (hV : IsOpen V) (hV0 : StarConvex ℝ 0 V)
    (hf : ContDiffOn ℝ ∞ f V) (hf0 : f 0 = 0) (hdf0 : fderiv ℝ f 0 = 0) :
    ∃ B : E → (E →L[ℝ] E →L[ℝ] F), ContDiffOn ℝ ∞ B V ∧ (∀ x ∈ V, f x = B x x x) ∧
      (∀ x ∈ V, ∀ u w, B x u w = B x w u) ∧
      B 0 = (2 : ℝ)⁻¹ • fderiv ℝ (fderiv ℝ f) 0 := by
  have hfd : ContDiffOn ℝ ∞ (fderiv ℝ f) V := hf.fderiv_of_isOpen hV (by simp)
  have hfdd : ContDiffOn ℝ ∞ (fderiv ℝ (fderiv ℝ f)) V := hfd.fderiv_of_isOpen hV (by simp)
  set B : E → (E →L[ℝ] E →L[ℝ] F) :=
    fun x => ∫ t in (0 : ℝ)..1, (1 - t) • fderiv ℝ (fderiv ℝ f) (t • x) with hB
  have hseg : ∀ x ∈ V, ∀ t ∈ Icc (0 : ℝ) 1, t • x ∈ V := fun x hx t ht =>
    hV0.smul_mem hx ht.1 ht.2
  have hcont : ∀ x ∈ V, ContinuousOn
      (fun t : ℝ => (1 - t) • fderiv ℝ (fderiv ℝ f) (t • x)) (uIcc 0 1) := by
    intro x hx
    rw [uIcc_of_le zero_le_one]
    exact (continuous_const.sub continuous_id).continuousOn.smul
      (hfdd.continuousOn.comp (continuous_id.smul continuous_const).continuousOn (hseg x hx))
  -- evaluation commutes with the integral
  have hpull : ∀ x ∈ V, ∀ u w : E,
      B x u w = ∫ t in (0 : ℝ)..1, (1 - t) • fderiv ℝ (fderiv ℝ f) (t • x) u w := by
    intro x hx u w
    have h1 : (B x) u = ∫ t in (0 : ℝ)..1, ((1 - t) • fderiv ℝ (fderiv ℝ f) (t • x)) u :=
      ((ContinuousLinearMap.apply ℝ (E →L[ℝ] F) u).intervalIntegral_comp_comm
        (hcont x hx).intervalIntegrable).symm
    have hint' : IntervalIntegrable
        (fun t : ℝ => ((1 - t) • fderiv ℝ (fderiv ℝ f) (t • x)) u) volume 0 1 :=
      ((hcont x hx).clm_apply continuousOn_const).intervalIntegrable
    rw [h1]
    exact ((ContinuousLinearMap.apply ℝ F w).intervalIntegral_comp_comm hint').symm
  refine ⟨B, ?_, ?_, ?_, ?_⟩
  · exact contDiffOn_integral_smul_comp hV hV0 (contDiff_const.sub contDiff_id) hfdd
  · intro x hx
    have taylor := map_add_eq_sum_add_integral_iteratedFDeriv (n := 1) (f := f) (x := 0) (y := x)
      fun t ht => (hf.contDiffAt (hV.mem_nhds (by simpa using hseg x hx t ht))).of_le
        (by norm_cast)
    rw [hpull x hx]
    simpa [hf0, hdf0, iteratedFDeriv_one_apply, iteratedFDeriv_two_apply,
      Finset.sum_range_succ] using taylor
  · intro x hx u w
    rw [hpull x hx, hpull x hx]
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [uIcc_of_le zero_le_one] at ht
    have hsymm : IsSymmSndFDerivAt ℝ f (t • x) :=
      (hf.contDiffAt (hV.mem_nhds (hseg x hx t ht))).isSymmSndFDerivAt (by simp; norm_cast)
    rw [hsymm u w]
  · have h12 : ∫ t in (0 : ℝ)..1, (1 - t) = (2 : ℝ)⁻¹ := by
      rw [intervalIntegral.integral_sub intervalIntegrable_const
        intervalIntegral.intervalIntegrable_id]
      simp [integral_id]
      norm_num
    simp only [hB, smul_zero]
    rw [intervalIntegral.integral_smul_const, h12]

end Morse
