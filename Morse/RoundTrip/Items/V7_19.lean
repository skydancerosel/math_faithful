import Morse
import RoundTrip.Check
import RoundTrip.Bridge
import RoundTrip.Blind.«V7_19»

open Set Filter Topology
open scoped ContDiff Manifold ENNReal

namespace RoundTrip.«V7_19»

/-- The project's statement (universes instantiated at 0): for a slice submanifold `N ⊆ V` and a
normal radius `ε` at `p` (`nc : NormalCoord hN p ε`): `ρ(p, exp_p v) = ‖v‖` for `v ∈ T_pN`,
`‖v‖ < ε`; for `0 < r ≤ ε`, `ρ(p, y) < r ↔ y ∈ N ∩ exp_p(B_r(0))`; and the `ρ`-balls about `p`
form a basis of neighbourhoods of `p` in `N` (`ρ = Morse.riemDist`, `ℝ≥0∞`-valued, no
connectedness assumed). -/
def A : Prop :=
  type_of% @Morse.NormalCoord.riemDist_exp.{0,0,0} ∧
    type_of% @Morse.NormalCoord.riemDist_lt_iff.{0,0,0} ∧
    type_of% @Morse.hasBasis_nhdsWithin_riemDist.{0,0,0}

theorem A_holds : A :=
  ⟨@Morse.NormalCoord.riemDist_exp, @Morse.NormalCoord.riemDist_lt_iff,
    @Morse.hasBasis_nhdsWithin_riemDist⟩

/-! ### Embedded special case

`B` applied to a connected slice submanifold `N ⊆ V` with model `ℝⁿ`, made a Mathlib Riemannian
manifold by `RoundTrip.Bridge` (`Bridge.Sub hN`, induced metric), gives the third conjunct of `A`
(`hasBasis_nhdsWithin_riemDist`) for such `N`. This is not `B → A`: `A` also has
`riemDist_exp` and `riemDist_lt_iff` (normal balls are metric balls), arbitrary slice models `Z`,
and disconnected `N`. -/

section Embedded

set_option linter.unusedSectionVars false

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] {n : ℕ} {N : Set V}
  {hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N}

/-- The blind `ρ` of this file is the Bridge's (same definition, copied verbatim). -/
theorem rho_eq (p q : Bridge.Sub hN) :
    rho (n := n) p q = (Morse.riemDist (N := N) (Bridge.incl hN p) (Bridge.incl hN q)).toReal :=
  Bridge.rho_eq p q

theorem riemDist_self' (p : Bridge.Sub hN) :
    Morse.riemDist (N := N) (Bridge.incl hN p) (Bridge.incl hN p) = 0 :=
  Morse.riemDist_self (N := N) (p : N).2

/-- `B` on `↥N` forces `ρ < ∞` (a point at distance `∞` would lie in every `ρ`-ball, since its
blind `ρ` is `0`, contradicting `T₁`). -/
theorem riemDist_ne_top_of_B (hB : ∀ U : Set (Bridge.Sub hN),
      IsOpen U ↔ ∀ p ∈ U, ∃ ε > 0, {q : Bridge.Sub hN | rho (n := n) p q < ε} ⊆ U)
    (p q : Bridge.Sub hN) : Morse.riemDist (N := N) (Bridge.incl hN p) (Bridge.incl hN q) ≠ ⊤ := by
  intro htop
  have hpq : p ≠ q := by
    rintro rfl
    rw [riemDist_self'] at htop
    exact ENNReal.zero_ne_top htop
  have hU : IsOpen ({q}ᶜ : Set (Bridge.Sub hN)) := isOpen_compl_singleton
  obtain ⟨ε, hε, hsub⟩ := (hB _).1 hU p hpq
  have : q ∈ {q' : Bridge.Sub hN | rho (n := n) p q' < ε} := by
    show rho (n := n) p q < ε
    rw [rho_eq, htop, ENNReal.toReal_top]
    exact hε
  exact hsub this rfl

theorem B_hasBasis_embedded (hB : B) (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N)
    (hconn : IsPreconnected N) (p : N) :
    (𝓝[N] (p : V)).HasBasis (fun r : ℝ => 0 < r)
      (fun r => {y | Morse.riemDist (N := N) (p : V) y < ENNReal.ofReal r}) := by
  have : ConnectedSpace (Bridge.Sub hN) :=
    @ConnectedSpace.mk N _ (isPreconnected_iff_preconnectedSpace.1 hconn) ⟨p⟩
  have hB' := hB n (Bridge.Sub hN)
  have hfin := riemDist_ne_top_of_B (hN := hN) hB'
  set q : Bridge.Sub hN := p with hq
  have hqp : Bridge.incl hN q = (p : V) := rfl
  -- the blind `ρ`-balls are the project's `ρ`-balls
  have hball : ∀ (x y : Bridge.Sub hN) (r : ℝ), 0 < r →
      (rho (n := n) x y < r ↔
        Morse.riemDist (N := N) (Bridge.incl hN x) (Bridge.incl hN y) < ENNReal.ofReal r) := by
    intro x y r hr
    rw [rho_eq, ← ENNReal.ofReal_lt_ofReal_iff hr, ENNReal.ofReal_toReal (hfin x y)]
  refine ⟨fun t => ⟨fun ht => ?_, ?_⟩⟩
  · -- a neighbourhood of `p` contains a small `ρ`-ball
    have ht' : (Subtype.val ⁻¹' t : Set N) ∈ 𝓝 p := preimage_coe_mem_nhds_subtype.2 ht
    obtain ⟨U, hUt, hUo, hpU⟩ := mem_nhds_iff.1 ht'
    obtain ⟨ε, hε, hsub⟩ := (hB' (U : Set (Bridge.Sub hN))).1 hUo q hpU
    refine ⟨ε, hε, fun y hy => ?_⟩
    have hyN : y ∈ N := by
      by_contra h
      rw [mem_ofPred_eq, Morse.riemDist_eq_top_of_notMem h] at hy
      exact not_top_lt hy
    set y' : Bridge.Sub hN := (⟨y, hyN⟩ : N)
    have : y' ∈ U := hsub ((hball q y' ε hε).2 hy)
    exact hUt this
  · -- a `ρ`-ball is a neighbourhood of `p`
    rintro ⟨r, hr, hrt⟩
    set U : Set (Bridge.Sub hN) := {y | rho (n := n) q y < r} with hU
    have hUo : IsOpen U := by
      refine (hB' U).2 fun x hx => ⟨r - rho (n := n) q x, sub_pos.2 hx, fun z hz => ?_⟩
      have h1 : rho (n := n) q z ≤ rho (n := n) q x + rho (n := n) x z := by
        rw [rho_eq, rho_eq, rho_eq, ← ENNReal.toReal_add (hfin q x) (hfin x z)]
        exact ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hfin q x, hfin x z⟩)
          (Morse.riemDist_triangle _ _ _)
      show rho (n := n) q z < r
      have : rho (n := n) x z < r - rho (n := n) q x := hz
      linarith
    have hpU : q ∈ U := by
      show rho (n := n) q q < r
      rw [rho_eq, riemDist_self' q, ENNReal.toReal_zero]
      exact hr
    have hUt : U ⊆ ((Subtype.val ⁻¹' t : Set N) : Set (Bridge.Sub hN)) :=
      fun y hy => hrt ((hball q y r hr).1 hy)
    exact preimage_coe_mem_nhds_subtype.1 (mem_of_superset (hUo.mem_nhds hpU) hUt)

/-- `B`'s conclusion on `↥N` (with the induced metric). -/
def Bemb (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N) : Prop :=
  ∀ U : Set (Bridge.Sub hN),
    IsOpen U ↔ ∀ p ∈ U, ∃ ε > 0, {q : Bridge.Sub hN | rho (n := n) p q < ε} ⊆ U

theorem B_to_Bemb (hB : B) (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N)
    [ConnectedSpace (Bridge.Sub hN)] : Bemb hN :=
  hB n (Bridge.Sub hN)

/-- Finiteness of `ρ` on a connected `N` from the neighbourhood basis (the project's
`riemDist_ne_top` argument, run on `A`'s third conjunct). -/
theorem riemDist_ne_top_of_hasBasis
    (hb : ∀ p : N, (𝓝[N] (p : V)).HasBasis (fun r : ℝ => 0 < r)
      (fun r => {y | Morse.riemDist (N := N) (p : V) y < ENNReal.ofReal r}))
    (hconn : IsPreconnected N) (p q : N) : Morse.riemDist (N := N) (p : V) q ≠ ⊤ := by
  have := isPreconnected_iff_preconnectedSpace.1 hconn
  set T : Set N := {y | Morse.riemDist (N := N) (p : V) y ≠ ⊤} with hT
  have hnear : ∀ y : N, ∀ᶠ y' : N in 𝓝 y, Morse.riemDist (N := N) (y : V) y' < 1 := fun y =>
    (eventually_nhds_subtype_iff N y _).2 (by
      have := (hb y).mem_of_mem one_pos
      rw [ENNReal.ofReal_one] at this
      exact this)
  have hopen : IsOpen T := by
    rw [isOpen_iff_mem_nhds]
    intro y hy
    filter_upwards [hnear y] with y' hy'
    exact ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨hy, hy'.ne_top⟩)
      (Morse.riemDist_triangle _ _ _)
  have hclosed : IsClosed T := by
    rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
    intro y hy
    filter_upwards [hnear y] with y' hy' hy'T
    refine hy (ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨hy'T, ?_⟩)
      (Morse.riemDist_triangle (N := N) p y' y))
    rw [Morse.riemDist_comm]
    exact hy'.ne_top
  have huniv := IsClopen.eq_univ ⟨hclosed, hopen⟩ ⟨p, by
    change Morse.riemDist (N := N) (p : V) p ≠ ⊤
    rw [Morse.riemDist_self p.2]
    exact ENNReal.zero_ne_top⟩
  have : q ∈ T := by rw [huniv]; exact mem_univ _
  exact this

/-- **`A` ⇒ `B` on `↥N`** (connected `N`): `A`'s third conjunct, read with the blind `ρ`. -/
theorem A_to_Bemb [FiniteDimensional ℝ W] (hA : A)
    (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N) (hconn : IsPreconnected N) : Bemb hN := by
  have hb := hA.2.2 (hN := hN)
  have hfin : ∀ p q : Bridge.Sub hN,
      Morse.riemDist (N := N) (Bridge.incl hN p) (Bridge.incl hN q) ≠ ⊤ :=
    fun p q => riemDist_ne_top_of_hasBasis hb hconn p q
  have hball : ∀ (x y : Bridge.Sub hN) (r : ℝ), 0 < r →
      (rho (n := n) x y < r ↔
        Morse.riemDist (N := N) (Bridge.incl hN x) (Bridge.incl hN y) < ENNReal.ofReal r) := by
    intro x y r hr
    rw [rho_eq, ← ENNReal.ofReal_lt_ofReal_iff hr, ENNReal.ofReal_toReal (hfin x y)]
  have key : ∀ (p : Bridge.Sub hN) (U : Set (Bridge.Sub hN)),
      U ∈ 𝓝 p ↔ ∃ ε > 0, {q : Bridge.Sub hN | rho (n := n) p q < ε} ⊆ U := by
    intro p U
    have e1 : U ∈ 𝓝 p ↔ ∃ r, 0 < r ∧ {y | Morse.riemDist (N := N) (Bridge.incl hN p) y <
        ENNReal.ofReal r} ⊆ Subtype.val '' (show Set N from U) :=
      mem_nhds_subtype_iff_nhdsWithin.trans (hb p).mem_iff
    rw [e1]
    constructor
    · rintro ⟨r, hr, hsub⟩
      refine ⟨r, hr, fun q hq => ?_⟩
      obtain ⟨q', hq'U, hq'⟩ := hsub ((hball p q r hr).1 hq)
      have : q' = q := Subtype.ext hq'
      rw [← this]
      exact hq'U
    · rintro ⟨ε, hε, hsub⟩
      refine ⟨ε, hε, fun y hy => ?_⟩
      have hyN : y ∈ N := by
        by_contra h
        rw [mem_ofPred_eq, Morse.riemDist_eq_top_of_notMem h] at hy
        exact not_top_lt hy
      set y' : Bridge.Sub hN := (⟨y, hyN⟩ : N)
      exact ⟨y', hsub ((hball p y' ε hε).2 hy), rfl⟩
  intro U
  exact ⟨fun hU p hp => (key p U).1 (hU.mem_nhds hp),
    fun h => isOpen_iff_mem_nhds.2 fun p hp => (key p U).2 (h p hp)⟩

end Embedded

#rt_check RoundTrip.«V7_19».B_hasBasis_embedded [Morse.NormalCoord.riemDist_exp,
  Morse.NormalCoord.riemDist_lt_iff, Morse.hasBasis_nhdsWithin_riemDist]
#rt_overlap RoundTrip.«V7_19».B_hasBasis_embedded [Morse.NormalCoord.riemDist_exp,
  Morse.NormalCoord.riemDist_lt_iff, Morse.hasBasis_nhdsWithin_riemDist]

#rt_check RoundTrip.«V7_19».A_to_Bemb [Morse.NormalCoord.riemDist_exp,
  Morse.NormalCoord.riemDist_lt_iff, Morse.hasBasis_nhdsWithin_riemDist]

/-! No direction `A → B` / `B → A` is proved; see `V7_19.json`. -/

end RoundTrip.«V7_19»
