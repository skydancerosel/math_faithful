import Morse
import RoundTrip.Check
import RoundTrip.Bridge
import RoundTrip.Blind.V7_21

open Set Filter Topology
open scoped ContDiff Manifold ENNReal

namespace RoundTrip.V7_21

/-- The project's statement (universes instantiated at 0; `riemEMetricSpace`, `riemMetricSpace`
are definitions, i.e. vocabulary): `‖q − p‖ ≤ ρ(p, q)` for ANY subset `N ⊆ V` (chord bound);
`ρ = Morse.riemDist : V → V → ℝ≥0∞` is continuous on `N × N` for a slice submanifold `N`
(connected or not); `ρ < ∞` on a preconnected `N`; and the metric space `riemMetricSpace hN hconn`
(distance `ρ`, built with `replaceTopology`) has the topology of `N`, definitionally. -/
def A : Prop :=
  type_of% @Morse.ofReal_norm_sub_le_riemDist.{0} ∧
    type_of% @Morse.continuous_riemDist.{0,0,0} ∧
    type_of% @Morse.riemDist_ne_top.{0,0,0} ∧
    type_of% @Morse.riemMetricSpace_topology.{0,0,0}

theorem A_holds : A :=
  ⟨@Morse.ofReal_norm_sub_le_riemDist, @Morse.continuous_riemDist, @Morse.riemDist_ne_top,
    @Morse.riemMetricSpace_topology⟩

/-! ### Embedded special case

`B` applied to a connected slice submanifold `N ⊆ V` with model `ℝⁿ`, made a Mathlib Riemannian
manifold by `RoundTrip.Bridge` (`Bridge.Sub hN`, induced metric), gives the second and third
conjuncts of `A` for such `N` (finiteness from `B`'s joining paths; continuity from `B`'s
continuity of the real `ρ`). This is not `B → A`: `A` also has the chord bound (about the ambient
`V`, for any subset `N`), continuity on disconnected `N` (`ℝ≥0∞`-valued), arbitrary slice models
`Z`, and the (definitional) topology of `riemMetricSpace`. -/

section Embedded

set_option linter.unusedSectionVars false

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] {n : ℕ} {N : Set V}

theorem B_riemDist_ne_top_embedded (hB : B) (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N)
    (hconn : IsPreconnected N) {p q : V} (hp : p ∈ N) (hq : q ∈ N) :
    Morse.riemDist (N := N) p q ≠ ⊤ := by
  have : ConnectedSpace (Bridge.Sub hN) :=
    @ConnectedSpace.mk N _ (isPreconnected_iff_preconnectedSpace.1 hconn) ⟨⟨p, hp⟩⟩
  obtain ⟨hjoin, -, -, -⟩ := hB n (Bridge.Sub hN)
  set p' : Bridge.Sub hN := (⟨p, hp⟩ : N)
  set q' : Bridge.Sub hN := (⟨q, hq⟩ : N)
  obtain ⟨pth, a, b, hab, hpw, ha, hb⟩ := hjoin p' q'
  have hmem : ENNReal.ofReal (arcLen (n := n) pth a b) ∈
      Morse.pathLengths (N := N) (Bridge.incl hN p') (Bridge.incl hN q') := by
    rw [Bridge.pathLengths_eq]
    exact ⟨_, ⟨pth, a, b, hab, hpw, ha, hb, rfl⟩, rfl⟩
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top (sInf_le hmem)

theorem B_continuous_riemDist_embedded (hB : B)
    (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N) (hconn : IsPreconnected N) :
    Continuous (fun z : N × N => Morse.riemDist (N := N) (z.1 : V) z.2) := by
  rcases isEmpty_or_nonempty N with hN0 | ⟨⟨p, hp⟩⟩
  · exact continuous_of_discreteTopology
  have : ConnectedSpace (Bridge.Sub hN) :=
    @ConnectedSpace.mk N _ (isPreconnected_iff_preconnectedSpace.1 hconn) ⟨⟨p, hp⟩⟩
  obtain ⟨-, -, -, hcont⟩ := hB n (Bridge.Sub hN)
  show Continuous (fun z : Bridge.Sub hN × Bridge.Sub hN =>
    Morse.riemDist (N := N) (Bridge.incl hN z.1) (Bridge.incl hN z.2))
  have heq : (fun z : Bridge.Sub hN × Bridge.Sub hN =>
      Morse.riemDist (N := N) (Bridge.incl hN z.1) (Bridge.incl hN z.2)) =
      fun z => ENNReal.ofReal (rho (n := n) z.1 z.2) := by
    funext z
    rw [show rho (n := n) z.1 z.2 = _ from Bridge.rho_eq z.1 z.2]
    exact (ENNReal.ofReal_toReal
      (B_riemDist_ne_top_embedded hB hN hconn (z.1 : N).2 (z.2 : N).2)).symm
  rw [heq]
  exact ENNReal.continuous_ofReal.comp hcont

/-- `B`'s conclusion on `↥N` (with the induced metric). -/
def Bemb (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N) : Prop :=
  (∀ p q : Bridge.Sub hN, ∃ (pth : ℝ → Bridge.Sub hN) (a b : ℝ), a ≤ b ∧ IsPW (n := n) pth a b ∧
      pth a = p ∧ pth b = q) ∧
    (∀ p q : Bridge.Sub hN, 0 ≤ rho (n := n) p q ∧ (rho (n := n) p q = 0 ↔ p = q) ∧
      rho (n := n) p q = rho (n := n) q p ∧
      ∀ r : Bridge.Sub hN, rho (n := n) p r ≤ rho (n := n) p q + rho (n := n) q r) ∧
    (∀ U : Set (Bridge.Sub hN),
      IsOpen U ↔ ∀ p ∈ U, ∃ ε > 0, {q : Bridge.Sub hN | rho (n := n) p q < ε} ⊆ U) ∧
    Continuous (fun x : Bridge.Sub hN × Bridge.Sub hN => rho (n := n) x.1 x.2)

theorem B_to_Bemb (hB : B) (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N)
    [ConnectedSpace (Bridge.Sub hN)] : Bemb hN :=
  hB n (Bridge.Sub hN)

/-- The first three conjuncts of `A`. (`#rt_check` cannot be run on a proof from `A` itself:
`A`'s fourth conjunct mentions the definition `riemMetricSpace`, whose body contains a proof by
`riemDist_ne_top`, a banned name; the fourth conjunct is not needed below.) -/
def A3 : Prop :=
  type_of% @Morse.ofReal_norm_sub_le_riemDist.{0} ∧
    type_of% @Morse.continuous_riemDist.{0,0,0} ∧
    type_of% @Morse.riemDist_ne_top.{0,0,0}

theorem A_to_A3 (hA : A) : A3 := ⟨hA.1, hA.2.1, hA.2.2.1⟩

/-- **`A` ⇒ `B` on `↥N`** (connected `N`): finiteness gives the joining paths; continuity gives
the continuity of the real `ρ` and that `ρ`-balls are open; the chord bound `‖q − p‖ ≤ ρ(p, q)`
puts small `ρ`-balls inside any open set; the metric axioms come from the project's
`riemDist_comm`, `riemDist_triangle`, `eq_of_riemDist_eq_zero` (outside the item). -/
theorem A3_to_Bemb [FiniteDimensional ℝ W] (hA : A3)
    (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N) (hconn : IsPreconnected N) : Bemb hN := by
  have hfin : ∀ p q : Bridge.Sub hN,
      Morse.riemDist (N := N) (Bridge.incl hN p) (Bridge.incl hN q) ≠ ⊤ :=
    fun p q => hA.2.2 hN hconn (p : N).2 (q : N).2
  have hrho : ∀ p q : Bridge.Sub hN, rho (n := n) p q =
      (Morse.riemDist (N := N) (Bridge.incl hN p) (Bridge.incl hN q)).toReal :=
    fun p q => Bridge.rho_eq p q
  have hball : ∀ (x y : Bridge.Sub hN) (r : ℝ), 0 < r →
      (rho (n := n) x y < r ↔
        Morse.riemDist (N := N) (Bridge.incl hN x) (Bridge.incl hN y) < ENNReal.ofReal r) := by
    intro x y r hr
    rw [hrho, ← ENNReal.ofReal_lt_ofReal_iff hr, ENNReal.ofReal_toReal (hfin x y)]
  -- continuity of the real `ρ`
  have hcont : Continuous (fun x : Bridge.Sub hN × Bridge.Sub hN => rho (n := n) x.1 x.2) := by
    have h := hA.2.1 hN
    have h' : Continuous (fun z : Bridge.Sub hN × Bridge.Sub hN =>
        (Morse.riemDist (N := N) (Bridge.incl hN z.1) (Bridge.incl hN z.2)).toReal) :=
      ENNReal.continuousOn_toReal.comp_continuous h fun z => hfin z.1 z.2
    exact h'.congr fun z => (hrho z.1 z.2).symm
  refine ⟨fun p q => ?_, fun p q => ?_, fun U => ?_, hcont⟩
  · -- joining paths
    have hne : (Morse.pathLengths (N := N) (Bridge.incl hN p) (Bridge.incl hN q)).Nonempty := by
      by_contra h
      rw [not_nonempty_iff_eq_empty] at h
      apply hfin p q
      rw [Morse.riemDist, h, sInf_empty]
    obtain ⟨L, hL⟩ := hne
    rw [Bridge.pathLengths_eq] at hL
    obtain ⟨-, ⟨pth, a, b, hab, hpw, ha, hb, rfl⟩, -⟩ := hL
    exact ⟨pth, a, b, hab, hpw, ha, hb⟩
  · -- the metric axioms
    refine ⟨by rw [hrho]; exact ENNReal.toReal_nonneg, ⟨fun h => ?_, ?_⟩, ?_, fun r => ?_⟩
    · rw [hrho, ENNReal.toReal_eq_zero_iff] at h
      rcases h with h | h
      · exact Morse.eq_of_riemDist_eq_zero hN (p := (p : N)) (q := (q : N)) h
      · exact absurd h (hfin p q)
    · rintro rfl
      rw [hrho, show Morse.riemDist (N := N) (Bridge.incl hN p) (Bridge.incl hN p) = 0 from
        Morse.riemDist_self (p : N).2, ENNReal.toReal_zero]
    · rw [hrho, hrho, Morse.riemDist_comm]
    · rw [hrho, hrho, hrho, ← ENNReal.toReal_add (hfin p q) (hfin q r)]
      exact ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hfin p q, hfin q r⟩)
        (Morse.riemDist_triangle _ _ _)
  · -- compatibility with the topology
    constructor
    · intro hU p hp
      obtain ⟨O, hO, hOU⟩ := isOpen_induced_iff.1 hU
      have hpO : Bridge.incl hN p ∈ O := (Set.ext_iff.1 hOU p).2 hp
      obtain ⟨r, hr, hrO⟩ := Metric.isOpen_iff.1 hO _ hpO
      refine ⟨r, hr, fun q hq => ?_⟩
      have h1 := (hball p q r hr).1 hq
      have h2 := (hA.1 (N := N) (Bridge.incl hN p) (Bridge.incl hN q)).trans_lt h1
      rw [ENNReal.ofReal_lt_ofReal_iff hr] at h2
      have hqO : Bridge.incl hN q ∈ O := hrO (by rw [Metric.mem_ball, dist_eq_norm]; exact h2)
      exact (Set.ext_iff.1 hOU q).1 hqO
    · intro h
      refine isOpen_iff_mem_nhds.2 fun p hp => ?_
      obtain ⟨ε, hε, hsub⟩ := h p hp
      have hopen : IsOpen {q : Bridge.Sub hN | rho (n := n) p q < ε} :=
        isOpen_lt (hcont.comp (continuous_const.prodMk continuous_id)) continuous_const
      have hp' : p ∈ {q : Bridge.Sub hN | rho (n := n) p q < ε} := by
        show rho (n := n) p p < ε
        rw [hrho, show Morse.riemDist (N := N) (Bridge.incl hN p) (Bridge.incl hN p) = 0 from
          Morse.riemDist_self (p : N).2, ENNReal.toReal_zero]
        exact hε
      exact mem_of_superset (hopen.mem_nhds hp') hsub

end Embedded

#rt_check RoundTrip.V7_21.B_riemDist_ne_top_embedded [Morse.ofReal_norm_sub_le_riemDist,
  Morse.continuous_riemDist, Morse.riemDist_ne_top, Morse.riemEMetricSpace,
  Morse.riemMetricSpace, Morse.riemMetricSpace_topology]
#rt_check RoundTrip.V7_21.B_continuous_riemDist_embedded [Morse.ofReal_norm_sub_le_riemDist,
  Morse.continuous_riemDist, Morse.riemDist_ne_top, Morse.riemEMetricSpace,
  Morse.riemMetricSpace, Morse.riemMetricSpace_topology]
#rt_overlap RoundTrip.V7_21.B_continuous_riemDist_embedded [Morse.ofReal_norm_sub_le_riemDist,
  Morse.continuous_riemDist, Morse.riemDist_ne_top, Morse.riemEMetricSpace,
  Morse.riemMetricSpace, Morse.riemMetricSpace_topology]

#rt_check RoundTrip.V7_21.A3_to_Bemb [Morse.ofReal_norm_sub_le_riemDist,
  Morse.continuous_riemDist, Morse.riemDist_ne_top, Morse.riemMetricSpace_topology]

/-! No direction `A → B` / `B → A` is proved; see `V7_21.json`. -/

end RoundTrip.V7_21
