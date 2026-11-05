import Morse.Chapter13.ManifoldOfMinima
import Morse.Chapter10.Omega

/-!
Milnor, *Morse Theory*, §22, pp. 121–123: two ingredients of the proof of Theorem 22.1 in the
finite-dimensional model `B = Int Ω(t₀, …, t_k)^c` of the path space (Chapter 10).

# Minimal paths, and deforming a neighbourhood of them

## Milnor's text, paraphrased

(p. 118) `Ω^d`, `d = ρ(p, q)²`, is the space of minimal geodesics from `p` to `q`.
(p. 121, proof of Lemma 22.5) "`M⁰` is a retract of some neighbourhood `U` … taking `U` small,
we may assume that each point of `U` is joined to its image under the retraction by a unique
minimal geodesic; hence `U` can be deformed into `M⁰` within `M`."

## What is formalized

* `Morse.isUnbrokenGeodesic_of_minimal`: a path of `Ω` of least energy is an unbroken geodesic
  (a minimum of `E` is a critical point, Corollary 12.3).  So the minimal paths are the paths of
  energy `≤ d`, `d` the least energy, and they are broken geodesics for every subdivision; in
  particular Milnor's deformation `r_u` fixes them.
* `Morse.BrokenSetup.exists_pushesInto_nodes`: **Milnor's deformation of a neighbourhood into
  `M⁰`**, in the manifold `N^m ∩ O ⊆ B` of break points: if `{E ≤ d}` (`d < c`) is a retract of
  an open set of `Ω`, then `M⁰ = {y : E'(y) ≤ d}` has an open neighbourhood in `N^m ∩ O` which
  deforms into `M⁰` within `N^m ∩ O`, fixing `M⁰`: each break point `yᵢ` is moved to the
  corresponding break point of the retracted path along the short geodesic of Corollary 10.8
  (the product of the minimal geodesics in the factors `N`).

## What Milnor leaves implicit

* The deformation must stay in the open manifold `N^m ∩ O`; by compactness of `[0, 1]` (the tube
  lemma) this holds near `M⁰`, which is fixed.
* The retraction is assumed on a neighbourhood in `Ω` (Milnor applies Hanner's theorem to `Ω^d`
  inside the manifold `B`); it is transported to `B` by `ω ↦ (ω(t₁), …, ω(t_{k−1}))`.
-/

open Set Filter Topology Function Module Metric
open scoped ContDiff Manifold unitInterval ENNReal

noncomputable section

namespace Morse

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {N : Set V} {hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N}

include hN in
/-- **A path of least energy is an unbroken geodesic** (a minimum is a critical point of `E`,
Corollary 12.3). -/
theorem isUnbrokenGeodesic_of_minimal {p q : V} {γ : ℝ → V} (hγ : γ ∈ pathSpace N p q)
    (hmin : ∀ γ' ∈ pathSpace N p q, energy γ 0 1 ≤ energy γ' 0 1) : IsUnbrokenGeodesic hN γ := by
  rw [← corollary_12_3 hN hγ]
  intro U α Bv hα hαγ
  have hmin' : IsLocalMin (fun u => energy (α u) 0 1) 0 := by
    filter_upwards [hα.isOpen.mem_nhds hα.zero_mem] with u hu
    have hpath := hα.mem_pathSpace hu
    rw [show α 0 0 = p from (hαγ 0 ⟨le_rfl, zero_le_one⟩).trans hγ.2.2.1,
      show α 0 1 = q from (hαγ 1 ⟨zero_le_one, le_rfl⟩).trans hγ.2.2.2] at hpath
    calc energy (α 0) 0 1 = energy γ 0 1 := energy_congr hαγ
      _ ≤ energy (α u) 0 1 := hmin _ hpath
  have hd := hα.hasDerivAt_energy hN hα.zero_mem
  rw [hmin'.hasDerivAt_eq_zero hd] at hd
  exact hd

namespace BrokenSetup

variable {p q : V} {c : ℝ} {m : ℕ} (B : BrokenSetup hN p q c m)

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
/-- The break points of a broken geodesic lie in `S = {x : ρ(p, x) ≤ √c}`. -/
theorem mem_ball_of_mem_nodes {y : Fin m → V} (hy : y ∈ B.nodes) (i : Fin m) :
    y i ∈ closedRiemBall N p √c := by
  have := B.vert_mem_ball hy i.castSucc.succ
  rwa [vert_inner] at this

/-- The short join of a point with itself is `0`. -/
theorem joinVec_self {x : V} (hx : x ∈ closedRiemBall N p √c) : B.joinVec x x = 0 := by
  have h0 : riemDist (N := N) x x < ENNReal.ofReal B.δ := by
    rw [riemDist_self hx.1]; exact ENNReal.ofReal_pos.2 B.δ_pos
  exact ((B.joinVec_spec hx hx h0).2.2.2.2 0 (map_zero _) (by simpa using B.δ_pos)
    (exp_zero hx.1)).symm

/-- **Deforming a neighbourhood of the minima** (Milnor p. 121, in the manifold of break points):
let `N^m ∩ O ⊆ B` (`O` open) and `d < c`, and suppose `{γ ∈ Ω : E(γ) ≤ d}` is a retract of an open
set `Or ⊆ Ω` containing it.  Then `M⁰ = {y ∈ N^m ∩ O : E'(y) ≤ d}` has an open neighbourhood `U`
in `N^m ∩ O` from which it pushes maps (from any space `P`). -/
theorem exists_pushesInto_nodes {O : Set (Fin m → V)} (hO : IsOpen O)
    (hOU : (Set.pi univ fun _ => N) ∩ O ⊆ B.nodes) {d : ℝ} (hd : d < c)
    {Or : Set (PathSp N p q)} (hOr : IsOpen Or)
    (hΩOr : ∀ γ : PathSp N p q, energy γ 0 1 ≤ d → γ ∈ Or) {ρ : PathSp N p q → PathSp N p q}
    (hρc : ContinuousOn ρ Or) (hρ : ∀ γ ∈ Or, energy (ρ γ) 0 1 ≤ d)
    (hρid : ∀ γ : PathSp N p q, energy γ 0 1 ≤ d → ρ γ = γ) (P : Type*) [TopologicalSpace P] :
    ∃ U : Set ↥((Set.pi univ fun _ => N) ∩ O), IsOpen U ∧
      {y : ↥((Set.pi univ fun _ => N) ∩ O) | B.energy' y ≤ d} ⊆ U ∧
      PushesInto P {y : ↥((Set.pi univ fun _ => N) ∩ O) | B.energy' y ≤ d} U := by
  classical
  set S := (Set.pi univ fun _ => N) ∩ O with hS_def
  set A : Set S := {y | B.energy' y ≤ d} with hA_def
  -- the broken geodesic of a point of `S`, and the break points of its retraction
  let pth : S → PathSp N p q := fun y => B.pathP ⟨y.1, hOU y.2⟩
  have hpth : Continuous pth := B.continuous_pathP.comp (continuous_inclusion hOU)
  have hEpth : ∀ y : S, energy (pth y) 0 1 = B.energy' y := fun y => B.energy_path (hOU y.2)
  let sg : S → (Fin m → V) := fun y => B.nodeVal (ρ (pth y))
  set U₁ : Set S := pth ⁻¹' Or with hU₁_def
  have hU₁ : IsOpen U₁ := hOr.preimage hpth
  have hsgc : ContinuousOn sg U₁ :=
    B.continuous_nodeVal.comp_continuousOn (hρc.comp hpth.continuousOn fun y hy => hy)
  have hsgmem : ∀ y ∈ U₁, sg y ∈ B.nodes ∧ B.energy' (sg y) ≤ d := fun y hy => by
    have h := hρ _ hy
    obtain ⟨h1, h2⟩ := B.nodeVal_mem_nodes_of_energy_lt (ρ (pth y)).mem (lt_of_le_of_lt h hd)
    exact ⟨h1, h2.trans h⟩
  have hAU₁ : ∀ y ∈ A, y ∈ U₁ := fun y hy => hΩOr _ (by rw [hEpth]; exact hy)
  have hsgA : ∀ y ∈ A, sg y = y := fun y hy => by
    change B.nodeVal (ρ (pth y)) = y
    rw [hρid _ (by rw [hEpth]; exact hy)]
    exact B.nodeVal_path (hOU y.2)
  -- where the short joins exist
  set U₂ : Set S := {y | y ∈ U₁ ∧ ∀ i, riemDist (N := N) (y.1 i) (sg y i) < ENNReal.ofReal B.δ}
    with hU₂_def
  have hdcont : ∀ i, ∀ y ∈ U₁,
      ContinuousAt (fun y : S => riemDist (N := N) (y.1 i) (sg y i)) y := by
    intro i y hy
    have h1 : ContinuousOn (fun y : S => ((y.1 i, sg y i) : V × V)) U₁ :=
      ((continuous_apply i).comp continuous_subtype_val).continuousOn.prodMk
        ((continuous_apply i).comp_continuousOn hsgc)
    exact ((continuousOn_riemDist hN).comp h1 fun y hy =>
      ⟨y.2.1 i trivial, (hsgmem y hy).1.1 i⟩).continuousAt (hU₁.mem_nhds hy)
  have hU₂ : IsOpen U₂ := by
    rw [isOpen_iff_mem_nhds]
    rintro y ⟨hy1, hy2⟩
    filter_upwards [hU₁.mem_nhds hy1, Filter.eventually_all.2 fun i =>
      (hdcont i y hy1).eventually (isOpen_Iio.mem_nhds (hy2 i))] with y' h1 h2
    exact ⟨h1, h2⟩
  have hAU₂ : ∀ y ∈ A, y ∈ U₂ := fun y hy => ⟨hAU₁ y hy, fun i => by
    rw [hsgA y hy, riemDist_self (y.2.1 i trivial)]
    exact ENNReal.ofReal_pos.2 B.δ_pos⟩
  have hjoin : ∀ y ∈ U₂, ∀ i, ((y.1 i, sg y i) : V × V) ∈ B.joinable := fun y hy i =>
    ⟨B.mem_ball_of_mem_nodes (hOU y.2) i, B.mem_ball_of_mem_nodes (hsgmem y hy.1).1 i, hy.2 i⟩
  -- the deformation along the short geodesics
  let D : S × ℝ → (Fin m → V) := fun z i =>
    exp hN (z.1.1 i) (z.2 • B.joinVec (z.1.1 i) (sg z.1 i))
  have hDc : ContinuousOn D (U₂ ×ˢ Icc 0 1) := by
    refine continuousOn_pi.2 fun i => ?_
    rintro ⟨y, θ⟩ ⟨hy, hθ⟩
    have hg : ContinuousWithinAt (fun z : S × ℝ => (((z.1.1 i, sg z.1 i) : V × V), z.2))
        (U₂ ×ˢ Icc 0 1) (y, θ) := by
      refine ContinuousWithinAt.prodMk ?_ continuousWithinAt_snd
      refine ContinuousWithinAt.prodMk ?_ ?_
      · exact ((continuous_apply i).comp (continuous_subtype_val.comp continuous_fst))
          |>.continuousWithinAt
      · have := (hsgc.continuousAt (hU₁.mem_nhds hy.1)).comp_continuousWithinAt
          (continuous_fst.continuousWithinAt (s := U₂ ×ˢ Icc 0 1) (x := (y, θ)))
        exact ((continuous_apply i).continuousAt.comp_continuousWithinAt this)
    exact ContinuousWithinAt.comp
      (g := fun w : (V × V) × ℝ => exp hN w.1.1 (w.2 • B.joinVec w.1.1 w.1.2))
      (f := fun z : S × ℝ => (((z.1.1 i, sg z.1 i) : V × V), z.2))
      (t := B.joinable ×ˢ Icc 0 1) (B.continuousWithinAt_shortGeo (hjoin y hy i) hθ) hg
      fun z hz => ⟨hjoin z.1 hz.1 i, hz.2⟩
  have hDN : ∀ y ∈ U₂, ∀ θ ∈ Icc (0 : ℝ) 1, ∀ i, D (y, θ) i ∈ N := fun y hy θ hθ i =>
    exp_mem_of_mem_expDom (mem_expDom_smul (B.mem_expDom_joinVec
      (hjoin y hy i).1 (hjoin y hy i).2.1 (hjoin y hy i).2.2) hθ)
  have hD0 : ∀ y : S, D (y, 0) = y := fun y => funext fun i => by
    simp only [D, zero_smul]
    exact exp_zero (y.2.1 i trivial)
  have hD1 : ∀ y ∈ U₂, D (y, 1) = sg y := fun y hy => funext fun i => by
    simp only [D, one_smul]
    exact (B.joinVec_spec (hjoin y hy i).1 (hjoin y hy i).2.1 (hjoin y hy i).2.2).2.2.1
  have hDA : ∀ y ∈ A, ∀ θ, D (y, θ) = y := fun y hy θ => funext fun i => by
    simp only [D]
    rw [hsgA y hy, B.joinVec_self (B.mem_ball_of_mem_nodes (hOU y.2) i), smul_zero]
    exact exp_zero (y.2.1 i trivial)
  -- near `M⁰` the deformation stays in `O` (tube lemma)
  set U₃ : Set S := {y | y ∈ U₂ ∧ ∀ θ ∈ Icc (0 : ℝ) 1, D (y, θ) ∈ O} with hU₃_def
  have hAU₃ : ∀ y ∈ A, U₃ ∈ 𝓝 y := by
    intro a ha
    have hev : ∀ θ ∈ Icc (0 : ℝ) 1, ∀ᶠ z : S × ℝ in 𝓝 (a, θ),
        z.1 ∈ U₂ ∧ (z.2 ∈ Icc (0 : ℝ) 1 → D (z.1, z.2) ∈ O) := by
      intro θ hθ
      have hnhds : U₂ ×ˢ univ ∈ 𝓝 (a, θ) := prod_mem_nhds (hU₂.mem_nhds (hAU₂ a ha)) univ_mem
      have hcw : ContinuousWithinAt D (U₂ ×ˢ Icc 0 1) (a, θ) := hDc _ ⟨hAU₂ a ha, hθ⟩
      have hDa : D (a, θ) ∈ O := by rw [hDA a ha]; exact a.2.2
      have h1 : ∀ᶠ z in 𝓝[U₂ ×ˢ Icc 0 1] (a, θ), D z ∈ O := hcw (hO.mem_nhds hDa)
      rw [eventually_nhdsWithin_iff] at h1
      filter_upwards [h1, hnhds] with z hz hz'
      exact ⟨hz'.1, fun hz2 => hz ⟨hz'.1, hz2⟩⟩
    have := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).eventually_forall_of_forall_eventually
      (P := fun y θ => y ∈ U₂ ∧ (θ ∈ Icc (0 : ℝ) 1 → D (y, θ) ∈ O)) hev
    filter_upwards [this] with y hy
    obtain ⟨θ₀, hθ₀⟩ : ∃ θ₀ : ℝ, θ₀ ∈ Icc (0 : ℝ) 1 := ⟨0, le_rfl, zero_le_one⟩
    exact ⟨(hy θ₀ hθ₀).1, fun θ hθ => (hy θ hθ).2 hθ⟩
  refine ⟨interior U₃, isOpen_interior, fun y hy => mem_interior_iff_mem_nhds.2 (hAU₃ y hy), ?_⟩
  have hU₃ : ∀ y ∈ interior U₃, y ∈ U₃ := fun y hy => interior_subset hy
  let Dc : C(I × ↥(interior U₃), S) :=
    { toFun := fun z => ⟨D (z.2.1, z.1), fun i _ => hDN _ (hU₃ _ z.2.2).1 _ z.1.2 i,
        (hU₃ _ z.2.2).2 _ z.1.2⟩
      continuous_toFun := by
        refine Continuous.subtype_mk ?_ _
        refine hDc.comp_continuous (by fun_prop) fun z => ⟨(hU₃ _ z.2.2).1, z.1.2⟩ }
  refine pushesInto_of_deformation Dc (fun x => Subtype.ext (hD0 x.1)) (fun x => ?_)
    fun t x hx => Subtype.ext (hDA x.1 hx _)
  change B.energy' (D (x.1, 1)) ≤ d
  rw [hD1 x.1 (hU₃ _ x.2).1]
  exact (hsgmem x.1 (hU₃ _ x.2).1.1).2

end BrokenSetup

end Morse
