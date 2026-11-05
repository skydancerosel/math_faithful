import Mathlib
import Morse.Homotopy.Fibration
import Morse.Homotopy.LoopSpace

/-!
# The exact homotopy sequence of a Serre fibration

Let `p : E → B` be a Serre fibration (`Morse.Homotopy.IsSerreFibration`), for instance a locally
trivial map (`Morse/Homotopy/HomotopyLifting.lean`), `e₀ ∈ E`, and `F = p⁻¹(p e₀)` the fibre
through `e₀` (`Morse.Homotopy.fiber p e₀`, pointed by `e₀`). This file constructs the boundary map
`∂ : π_{n+1}(B, p e₀) → π_n(F, e₀)` and proves the exactness of

  `⋯ → π_{n+1}(B) →∂ π_n(F) →i_* π_n(E) →p_* π_n(B) →∂ π_{n-1}(F) → ⋯ → π_0(E) →p_* π_0(B)`

at every place, as pointed sets (kernel = image, the kernel being the preimage of the class of
the constant map). This is the sequence Milnor quotes from Steenrod in §§23–24 to compare the
homotopy groups of Grassmannians and of unitary groups. Injectivity statements, the group
homomorphisms and the consequences used by Milnor are in
`Morse/Homotopy/ExactSequenceIso.lean`.

## Conventions

Homotopy groups are Mathlib's `HomotopyGroup N X x` for an arbitrary finite index type `N`;
`π_{n+1}` is indexed by `Option N` (as in `Morse/Homotopy/LoopSpace.lean`), the extra coordinate
`none` being the *time* of the lifting problem. A generalized loop `α` on `I^{Option N}` gives
the map `(z, t) ↦ α(t, z)` on `Iᴺ × I` (`Morse.Homotopy.cubeOfLoop`), which sends the open box
`Iᴺ × {0} ∪ ∂Iᴺ × I` to `p e₀`. A **boundary lift** of `α` (`Morse.Homotopy.IsBoundaryLift`) is
a lift `G : Iᴺ × I → E` of it which is `e₀` on the open box; one exists by the relative lifting
property (`Morse.Homotopy.exists_isBoundaryLift`), and its top face `G(·, 1)` is a generalized
loop in `F` (`Morse.Homotopy.topFace`). The fibre is the subspace `p⁻¹(p e₀)` of `E`, its
inclusion `Morse.Homotopy.fiberIncl p e₀`, its base point `Morse.Homotopy.fiberPt p e₀`.

## Main results

* `Morse.Homotopy.homotopic_topFace`: the top faces of boundary lifts of homotopic generalized
  loops are homotopic in `F`. Lift the homotopy, as a map of the cube indexed by `Option N` (the
  homotopy parameter `s` and the cube `Iᴺ`) times the time; on the open box it is prescribed by
  the continuous formula `G(z, t - 2s)` for `s ≤ 1/2`, `G'(z, t - 2 + 2s)` for `s ≥ 1/2`.
* `Morse.Homotopy.boundaryMap`: hence `∂ [α] = [top face of any boundary lift of α]`
  (`Morse.Homotopy.boundaryMap_mk`).
* `Morse.Homotopy.exists_isBoundaryLift_topFace_eq`: a boundary lift can be modified to have any
  top face homotopic in `F` to its own: lift the constant homotopy of `α`, prescribing on the open
  box the path `G(z, ·)` followed by the homotopy in `F`, at the parameter `t(1 + s)`. This
  replaces all reparametrizations of cubes in the exactness proofs.
* **Exactness**: `Morse.Homotopy.exact_fiber` (`ker i_* = im ∂`), `Morse.Homotopy.exact_total`
  (`ker p_* = im i_*`), `Morse.Homotopy.exact_base` (`ker ∂ = im p_*`), for every finite `N`,
  including `N = ∅` (the end `π₁(B) → π₀(F) → π₀(E) → π₀(B)` of the sequence).
-/

open Set Function Topology
open scoped unitInterval Topology.Homotopy

noncomputable section

namespace Morse.Homotopy

variable {E B : Type*} [TopologicalSpace E] [TopologicalSpace B]

/-! ### Cubes indexed by `Option N` -/

section OptionCube

variable {N : Type*}

/-- The coordinates `y ∘ some` of a point of `I^{Option N}`. -/
def optionTail (y : Option N → I) : N → I :=
  fun j => y (some j)

theorem continuous_optionTail : Continuous (optionTail (N := N)) :=
  continuous_pi fun j => continuous_apply (some j)

@[simp]
theorem optionPoint_none (t : I) (z : N → I) : optionPoint t z none = t :=
  rfl

@[simp]
theorem optionPoint_some (t : I) (z : N → I) (j : N) : optionPoint t z (some j) = z j :=
  rfl

@[simp]
theorem optionTail_optionPoint (t : I) (z : N → I) : optionTail (optionPoint t z) = z :=
  rfl

theorem optionPoint_optionTail (y : Option N → I) : optionPoint (y none) (optionTail y) = y :=
  optionPoint_eta y

theorem mem_boundary_option_iff {y : Option N → I} :
    y ∈ Cube.boundary (Option N) ↔ (y none = 0 ∨ y none = 1) ∨ optionTail y ∈ Cube.boundary N := by
  constructor
  · rintro ⟨j, hj⟩
    cases j with
    | none => exact Or.inl hj
    | some j => exact Or.inr ⟨j, hj⟩
  · rintro (h | ⟨j, hj⟩)
    · exact ⟨none, h⟩
    · exact ⟨some j, hj⟩

theorem update_none_eq_optionPoint [DecidableEq N] (y : Option N → I) (v : I) :
    Function.update y none v = optionPoint v (optionTail y) := by
  funext j
  cases j with
  | none => simp
  | some j => simp [optionTail]

theorem update_some_optionPoint [DecidableEq N] (t : I) (z : N → I) (j : N) (v : I) :
    Function.update (optionPoint t z) (some j) v = optionPoint t (Function.update z j v) := by
  funext k
  cases k with
  | none => simp
  | some k =>
    by_cases hk : k = j
    · subst hk
      simp
    · rw [Function.update_of_ne (fun h => hk (Option.some_injective _ h)), optionPoint_some,
        optionPoint_some, Function.update_of_ne hk]

end OptionCube

/-- `projIcc` of a nonpositive number is `0 : I`. -/
theorem projIcc_eq_zero {x : ℝ} (h : x ≤ 0) : Set.projIcc (0 : ℝ) 1 zero_le_one x = 0 :=
  Set.projIcc_of_le_left _ h

/-- `projIcc` of a number `≥ 1` is `1 : I`. -/
theorem projIcc_eq_one {x : ℝ} (h : 1 ≤ x) : Set.projIcc (0 : ℝ) 1 zero_le_one x = 1 :=
  Set.projIcc_of_right_le _ h

/-! ### The fibre -/

/-- The fibre `p⁻¹(p e₀)` of `p` through `e₀`. -/
abbrev fiber (p : C(E, B)) (e₀ : E) : Set E :=
  p ⁻¹' {p e₀}

/-- The base point `e₀` of the fibre `p⁻¹(p e₀)`. -/
def fiberPt (p : C(E, B)) (e₀ : E) : fiber p e₀ :=
  ⟨e₀, rfl⟩

/-- The inclusion of the fibre `p⁻¹(p e₀)` into `E`. -/
def fiberIncl (p : C(E, B)) (e₀ : E) : C(fiber p e₀, E) :=
  ⟨Subtype.val, continuous_subtype_val⟩

@[simp]
theorem fiberIncl_apply (p : C(E, B)) (e₀ : E) (x : fiber p e₀) : fiberIncl p e₀ x = x :=
  rfl

theorem proj_fiber {p : C(E, B)} {e₀ : E} (x : fiber p e₀) : p x = p e₀ :=
  x.2

/-! ### Boundary lifts -/

section Lifts

variable {N : Type*} {p : C(E, B)} {e₀ : E}

/-- `G : Iᴺ × I → E` is a **boundary lift** of the generalized loop `α` on `I^{Option N}` (the
coordinate `none` being the time): it lies over `(z, t) ↦ α(t, z)` and is `e₀` on the open box
`Iᴺ × {0} ∪ ∂Iᴺ × I`. -/
structure IsBoundaryLift (p : C(E, B)) (e₀ : E) (α : Ω^ (Option N) B (p e₀))
    (G : C((N → I) × I, E)) : Prop where
  proj : ∀ z t, p (G (z, t)) = α (optionPoint t z)
  bot : ∀ z, G (z, 0) = e₀
  side : ∀ z ∈ Cube.boundary N, ∀ t, G (z, t) = e₀

theorem IsBoundaryLift.mem_fiber {α : Ω^ (Option N) B (p e₀)} {G : C((N → I) × I, E)}
    (hG : IsBoundaryLift p e₀ α G) (z : N → I) : G (z, 1) ∈ fiber p e₀ := by
  change p (G (z, 1)) = p e₀
  rw [hG.proj]
  exact GenLoop.boundary α _ (optionPoint_mem_boundary_of_left (Or.inr rfl) z)

/-- The **top face** `G(·, 1)` of a boundary lift, a generalized loop in the fibre. -/
def topFace {α : Ω^ (Option N) B (p e₀)} {G : C((N → I) × I, E)} (hG : IsBoundaryLift p e₀ α G) :
    Ω^ N (fiber p e₀) (fiberPt p e₀) :=
  ⟨⟨fun z => ⟨G (z, 1), hG.mem_fiber z⟩,
    (G.continuous.comp (continuous_id.prodMk continuous_const)).subtype_mk hG.mem_fiber⟩,
    fun z hz => Subtype.ext (hG.side z hz 1)⟩

@[simp]
theorem coe_topFace {α : Ω^ (Option N) B (p e₀)} {G : C((N → I) × I, E)}
    (hG : IsBoundaryLift p e₀ α G) (z : N → I) : (topFace hG z : E) = G (z, 1) :=
  rfl

/-- The map `(z, t) ↦ α(t, z)` of `Iᴺ × I`. -/
def cubeOfLoop {X : Type*} [TopologicalSpace X] {x : X} (α : Ω^ (Option N) X x) :
    C((N → I) × I, X) :=
  ⟨fun q => α (optionPoint q.2 q.1),
    α.1.continuous.comp (continuous_optionPoint.comp (continuous_snd.prodMk continuous_fst))⟩

/-- A generalized loop `β` in `E` is a boundary lift of `p ∘ β`. -/
theorem isBoundaryLift_genLoopMap (β : Ω^ (Option N) E e₀) :
    IsBoundaryLift p e₀ (genLoopMap p β) (cubeOfLoop β) where
  proj _ _ := rfl
  bot z := GenLoop.boundary β _ (optionPoint_mem_boundary_of_left (Or.inl rfl) z)
  side _ hz t := GenLoop.boundary β _ (optionPoint_mem_boundary_of_right t hz)

variable [Finite N]

/-- **Boundary lifts exist** for a Serre fibration. -/
theorem exists_isBoundaryLift (hp : IsSerreFibration p) (α : Ω^ (Option N) B (p e₀)) :
    ∃ G, IsBoundaryLift p e₀ α G := by
  obtain ⟨G, hG, hGg⟩ := hp.exists_lift (cubeOfLoop α) (fun _ => e₀) continuousOn_const
    fun q hq => by
      change p e₀ = α (optionPoint q.2 q.1)
      rcases hq with h | h
      · exact (GenLoop.boundary α _ (optionPoint_mem_boundary_of_left (Or.inl h) _)).symm
      · exact (GenLoop.boundary α _ (optionPoint_mem_boundary_of_right _ h)).symm
  exact ⟨G, fun z t => hG (z, t), fun z => hGg _ (mk_zero_mem_openBox z),
    fun z hz t => hGg _ (mk_mem_openBox_of_mem_boundary hz t)⟩

/-- **Homotopic loops have homotopic boundaries**: if `α ≃ α'` relative to the boundary, the top
faces of any boundary lifts of `α` and `α'` are homotopic in the fibre. The homotopy is lifted as
a map of `I^{Option N} × I` (homotopy parameter `s = y none`, cube `z = y ∘ some`, time `t`), with
the prescribed values `G(z, t - 2s)` for `s ≤ 1/2` and `G'(z, t - 2 + 2s)` for `s ≥ 1/2` (clamped
to `[0, 1]`), a continuous map which is right on the open box. -/
theorem homotopic_topFace (hp : IsSerreFibration p) {α α' : Ω^ (Option N) B (p e₀)}
    (h : GenLoop.Homotopic α α') {G G' : C((N → I) × I, E)} (hG : IsBoundaryLift p e₀ α G)
    (hG' : IsBoundaryLift p e₀ α' G') : GenLoop.Homotopic (topFace hG) (topFace hG') := by
  obtain ⟨K⟩ := h
  have hK : ∀ s, ∀ y ∈ Cube.boundary (Option N), K (s, y) = p e₀ := fun s y hy => by
    rw [K.eq_fst s hy]
    exact GenLoop.boundary α y hy
  let H : C((Option N → I) × I, B) :=
    ⟨fun q => K (q.1 none, optionPoint q.2 (optionTail q.1)),
      K.continuous.comp (((continuous_apply none).comp continuous_fst).prodMk
        (continuous_optionPoint.comp (continuous_snd.prodMk
          (continuous_optionTail.comp continuous_fst))))⟩
  let g : (Option N → I) × I → E := fun q =>
    if (q.1 none : ℝ) ≤ 1 / 2 then
      G (optionTail q.1, Set.projIcc 0 1 zero_le_one (q.2 - 2 * q.1 none))
    else G' (optionTail q.1, Set.projIcc 0 1 zero_le_one (q.2 - 2 + 2 * q.1 none))
  have hg : Continuous g := by
    refine Continuous.if_le (G.continuous.comp ((continuous_optionTail.comp continuous_fst).prodMk
      (continuous_projIcc.comp ((continuous_subtype_val.comp continuous_snd).sub
        (continuous_const.mul (continuous_subtype_val.comp ((continuous_apply none).comp
          continuous_fst)))))))
      (G'.continuous.comp ((continuous_optionTail.comp continuous_fst).prodMk
        (continuous_projIcc.comp (((continuous_subtype_val.comp continuous_snd).sub
          continuous_const).add (continuous_const.mul (continuous_subtype_val.comp
            ((continuous_apply none).comp continuous_fst)))))))
      (continuous_subtype_val.comp ((continuous_apply none).comp continuous_fst))
      continuous_const fun q hq => ?_
    rw [projIcc_eq_zero (by linarith [q.2.2.2]), projIcc_eq_zero (by linarith [q.2.2.2]),
      hG.bot, hG'.bot]
  have hpg : ∀ q ∈ openBox (Option N), p (g q) = H q := by
    rintro ⟨y, t⟩ hq
    change p (g (y, t)) = K (y none, optionPoint t (optionTail y))
    simp only [g]
    -- on the open box, `t = 0`, or `s ∈ {0, 1}`, or `z ∈ ∂Iᴺ`
    rcases hq with ht | hy
    · change t = 0 at ht
      subst ht
      rw [hK _ _ (optionPoint_mem_boundary_of_left (Or.inl rfl) _)]
      split_ifs
      · rw [projIcc_eq_zero (by simp; linarith [(y none).2.1]), hG.bot]
      · rw [projIcc_eq_zero (by simp; linarith [(y none).2.2]), hG'.bot]
    · change y ∈ Cube.boundary (Option N) at hy
      rcases mem_boundary_option_iff.1 hy with (h0 | h1) | hz
      · rw [h0]
        simp only [Set.Icc.coe_zero, mul_zero, sub_zero]
        rw [if_pos (by norm_num), Set.projIcc_val, hG.proj, K.apply_zero]
        rfl
      · rw [h1]
        simp only [Set.Icc.coe_one, mul_one]
        rw [if_neg (by norm_num), show (t : ℝ) - 2 + 2 = t by ring, Set.projIcc_val, hG'.proj,
          K.apply_one]
        rfl
      · rw [hK _ _ (optionPoint_mem_boundary_of_right _ hz)]
        split_ifs
        · rw [hG.side _ hz]
        · rw [hG'.side _ hz]
  obtain ⟨L, hL, hLg⟩ := hp.exists_lift H g hg.continuousOn hpg
  have hLmem : ∀ q : I × (N → I), L (optionPoint q.1 q.2, 1) ∈ fiber p e₀ := fun q => by
    change p (L (optionPoint q.1 q.2, 1)) = p e₀
    rw [hL]
    exact hK _ _ (optionPoint_mem_boundary_of_left (Or.inr rfl) _)
  have hLbox : ∀ s : I, ∀ z, optionPoint s z ∈ Cube.boundary (Option N) →
      L (optionPoint s z, 1) = g (optionPoint s z, 1) := fun s z hz =>
    hLg _ (mk_mem_openBox_of_mem_boundary hz 1)
  refine ⟨
    { toFun := fun q => ⟨L (optionPoint q.1 q.2, 1), hLmem q⟩
      continuous_toFun := (L.continuous.comp ((continuous_optionPoint.comp
        (continuous_fst.prodMk continuous_snd)).prodMk continuous_const)).subtype_mk _
      map_zero_left := fun z => Subtype.ext ?_
      map_one_left := fun z => Subtype.ext ?_
      prop' := fun s z hz => Subtype.ext ?_ }⟩
  · change L (optionPoint 0 z, 1) = G (z, 1)
    rw [hLbox 0 z (optionPoint_mem_boundary_of_left (Or.inl rfl) z)]
    simp only [g, optionPoint_none, Set.Icc.coe_zero, mul_zero, sub_zero, optionTail_optionPoint]
    rw [if_pos (by norm_num), Set.projIcc_val]
  · change L (optionPoint 1 z, 1) = G' (z, 1)
    rw [hLbox 1 z (optionPoint_mem_boundary_of_left (Or.inr rfl) z)]
    simp only [g, optionPoint_none, Set.Icc.coe_one, mul_one, optionTail_optionPoint]
    rw [if_neg (by norm_num), show (1 : ℝ) - 2 + 2 = ((1 : I) : ℝ) by simp, Set.projIcc_val]
  · change L (optionPoint s z, 1) = G (z, 1)
    rw [hLbox s z (optionPoint_mem_boundary_of_right s hz), hG.side z hz]
    simp only [g, optionTail_optionPoint]
    split_ifs
    · exact hG.side z hz _
    · exact hG'.side z hz _

/-- **Changing the top face of a boundary lift** within its homotopy class in the fibre: if the top
face of `G` is homotopic in `F` to `γ`, some boundary lift of the same `α` has top face exactly
`γ`. Lift the constant homotopy of `α` (cube `I^{Option N}`, time `s`), prescribing on the open
box the values `P(z, t (1 + s))` of the path `P(z, ·)`: `G(z, ·)` on `[0, 1]`, followed by the
homotopy from the top face of `G` to `γ` on `[1, 2]`. -/
theorem exists_isBoundaryLift_topFace_eq (hp : IsSerreFibration p)
    {α : Ω^ (Option N) B (p e₀)} {G : C((N → I) × I, E)} (hG : IsBoundaryLift p e₀ α G)
    {γ : Ω^ N (fiber p e₀) (fiberPt p e₀)} (h : GenLoop.Homotopic (topFace hG) γ) :
    ∃ G' : C((N → I) × I, E), ∃ hG' : IsBoundaryLift p e₀ α G', topFace hG' = γ := by
  obtain ⟨M⟩ := h
  -- the path `G(z, ·)` followed by `M(·, z)`, at the parameter `r ∈ [0, 2]`
  let P : (N → I) × ℝ → E := fun q =>
    if q.2 ≤ 1 then G (q.1, Set.projIcc 0 1 zero_le_one q.2)
    else (M (Set.projIcc 0 1 zero_le_one (q.2 - 1), q.1) : E)
  have hP : Continuous P := by
    refine Continuous.if_le (G.continuous.comp (continuous_fst.prodMk
      (continuous_projIcc.comp continuous_snd)))
      (continuous_subtype_val.comp (M.continuous.comp ((continuous_projIcc.comp
        (continuous_snd.sub continuous_const)).prodMk continuous_fst)))
      continuous_snd continuous_const fun q hq => ?_
    rw [hq, sub_self, projIcc_eq_zero le_rfl, projIcc_eq_one le_rfl, M.apply_zero]
    rfl
  have hPbot : ∀ z, P (z, 0) = e₀ := fun z => by
    simp only [P, if_pos zero_le_one]
    rw [projIcc_eq_zero le_rfl, hG.bot]
  have hPside : ∀ z ∈ Cube.boundary N, ∀ r, P (z, r) = e₀ := fun z hz r => by
    simp only [P]
    split_ifs
    · exact hG.side z hz _
    · rw [M.eq_fst _ hz]
      exact hG.side z hz 1
  have hPproj : ∀ z r, r ≤ 1 → p (P (z, r)) = α (optionPoint (Set.projIcc 0 1 zero_le_one r) z) :=
    fun z r hr => by
      simp only [P, if_pos hr]
      exact hG.proj _ _
  have hPfib : ∀ z r, p (P (z, r)) = p e₀ ∨ r ≤ 1 := fun z r => by
    by_cases hr : r ≤ 1
    · exact Or.inr hr
    · left
      simp only [P, if_neg hr]
      exact proj_fiber _
  let H : C((Option N → I) × I, B) := ⟨fun q => α q.1, α.1.continuous.comp continuous_fst⟩
  let g : (Option N → I) × I → E := fun q => P (optionTail q.1, (q.1 none : ℝ) * (1 + q.2))
  have hg : Continuous g := hP.comp ((continuous_optionTail.comp continuous_fst).prodMk
    ((continuous_subtype_val.comp ((continuous_apply none).comp continuous_fst)).mul
      (continuous_const.add (continuous_subtype_val.comp continuous_snd))))
  have hpg : ∀ q ∈ openBox (Option N), p (g q) = H q := by
    rintro ⟨y, s⟩ hq
    change p (P (optionTail y, (y none : ℝ) * (1 + s))) = α y
    rcases hq with hs | hy
    · change s = 0 at hs
      subst hs
      rw [Set.Icc.coe_zero, add_zero, mul_one, hPproj _ _ (y none).2.2, Set.projIcc_val,
        optionPoint_optionTail]
    · change y ∈ Cube.boundary (Option N) at hy
      rw [GenLoop.boundary α y hy]
      rcases hPfib (optionTail y) ((y none : ℝ) * (1 + s)) with h | hr
      · exact h
      · rw [hPproj _ _ hr]
        apply GenLoop.boundary α
        rcases mem_boundary_option_iff.1 hy with (h0 | h1) | hz
        · rw [h0, Set.Icc.coe_zero, zero_mul, projIcc_eq_zero le_rfl]
          exact optionPoint_mem_boundary_of_left (Or.inl rfl) _
        · rw [h1, Set.Icc.coe_one, one_mul] at hr ⊢
          rw [projIcc_eq_one (by linarith [s.2.1])]
          exact optionPoint_mem_boundary_of_left (Or.inr rfl) _
        · exact optionPoint_mem_boundary_of_right _ hz
  obtain ⟨L, hL, hLg⟩ := hp.exists_lift H g hg.continuousOn hpg
  have hLbox : ∀ t : I, ∀ z, optionPoint t z ∈ Cube.boundary (Option N) →
      L (optionPoint t z, 1) = P (z, (t : ℝ) * 2) := fun t z hz => by
    rw [hLg _ (mk_mem_openBox_of_mem_boundary hz 1)]
    change P (z, (t : ℝ) * (1 + 1)) = _
    norm_num
  let G' : C((N → I) × I, E) := L.comp ⟨fun q => (optionPoint q.2 q.1, 1),
    (continuous_optionPoint.comp (continuous_snd.prodMk continuous_fst)).prodMk continuous_const⟩
  have hG' : IsBoundaryLift p e₀ α G' :=
    { proj := fun z t => hL (optionPoint t z, 1)
      bot := fun z => by
        change L (optionPoint 0 z, 1) = e₀
        rw [hLbox 0 z (optionPoint_mem_boundary_of_left (Or.inl rfl) z), Set.Icc.coe_zero,
          zero_mul, hPbot]
      side := fun z hz t => by
        change L (optionPoint t z, 1) = e₀
        rw [hLbox t z (optionPoint_mem_boundary_of_right t hz), hPside z hz] }
  refine ⟨G', hG', ?_⟩
  ext z
  change L (optionPoint 1 z, 1) = (γ z : E)
  rw [hLbox 1 z (optionPoint_mem_boundary_of_left (Or.inr rfl) z), Set.Icc.coe_one, one_mul]
  simp only [P, if_neg (by norm_num : ¬ (2 : ℝ) ≤ 1)]
  rw [show (2 : ℝ) - 1 = 1 by norm_num, projIcc_eq_one le_rfl, M.apply_one]
  rfl

end Lifts

/-! ### The boundary map -/

section Boundary

variable {N : Type*} [Finite N] {p : C(E, B)}

/-- The top face of a chosen boundary lift. -/
def boundaryLoop (hp : IsSerreFibration p) (e₀ : E) (α : Ω^ (Option N) B (p e₀)) :
    Ω^ N (fiber p e₀) (fiberPt p e₀) :=
  topFace (Classical.choose_spec (exists_isBoundaryLift hp α))

/-- **The boundary map** `∂ : π_{n+1}(B, p e₀) → π_n(F, e₀)` of a Serre fibration: the class of
the top face of a boundary lift. -/
def boundaryMap (hp : IsSerreFibration p) (e₀ : E) :
    HomotopyGroup (Option N) B (p e₀) → HomotopyGroup N (fiber p e₀) (fiberPt p e₀) :=
  Quotient.lift (fun α => (⟦boundaryLoop hp e₀ α⟧ : HomotopyGroup N (fiber p e₀) _))
    fun _ _ h => Quotient.sound (homotopic_topFace hp h _ _)

/-- `∂ [α]` is the class of the top face of **any** boundary lift of `α`. -/
theorem boundaryMap_mk (hp : IsSerreFibration p) {e₀ : E} {α : Ω^ (Option N) B (p e₀)}
    {G : C((N → I) × I, E)} (hG : IsBoundaryLift p e₀ α G) :
    boundaryMap hp e₀ ⟦α⟧ = ⟦topFace hG⟧ :=
  Quotient.sound (homotopic_topFace hp (GenLoop.Homotopic.refl α) _ hG)

end Boundary

/-! ### Exactness -/

/-- Induced maps preserve the base points of the homotopy groups. -/
theorem homotopyGroupMap_const {N X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (x : X) :
    homotopyGroupMap (N := N) f x ⟦GenLoop.const⟧ = ⟦GenLoop.const⟧ :=
  congrArg _ (GenLoop.ext _ _ fun _ => rfl)

section Exactness

variable {N : Type*} [Finite N] {p : C(E, B)} (hp : IsSerreFibration p) (e₀ : E)
include hp

omit hp [Finite N] in
/-- `p ∘ i` is constant. -/
theorem homotopyGroupMap_proj_fiberIncl (c : HomotopyGroup N (fiber p e₀) (fiberPt p e₀)) :
    homotopyGroupMap p e₀ (homotopyGroupMap (fiberIncl p e₀) (fiberPt p e₀) c) =
      ⟦GenLoop.const⟧ := by
  induction c using Quotient.inductionOn with
  | h γ => exact congrArg _ (GenLoop.ext _ _ fun z => proj_fiber (γ z))

/-- **Exactness at `π_n(F)`**: `ker i_* = im ∂`. -/
theorem exact_fiber (c : HomotopyGroup N (fiber p e₀) (fiberPt p e₀)) :
    homotopyGroupMap (fiberIncl p e₀) (fiberPt p e₀) c = ⟦GenLoop.const⟧ ↔
      c ∈ range (boundaryMap hp e₀) := by
  induction c using Quotient.inductionOn with
  | h γ =>
  constructor
  · -- a null-homotopy `L` of `i ∘ γ` in `E`, run backwards, is a boundary lift of `p ∘ L`
    intro h
    obtain ⟨L⟩ := Quotient.exact h
    have hLp : ∀ s, ∀ z ∈ Cube.boundary N, p (L (s, z)) = p e₀ := fun _ _ hz => by
      rw [L.eq_fst _ hz]
      exact proj_fiber (γ _)
    let α : Ω^ (Option N) B (p e₀) :=
      ⟨⟨fun y => p (L (σ (y none), optionTail y)),
        p.continuous.comp (L.continuous.comp ((unitInterval.continuous_symm.comp
          (continuous_apply none)).prodMk continuous_optionTail))⟩, fun y hy => by
        change p (L (σ (y none), optionTail y)) = p e₀
        rcases mem_boundary_option_iff.1 hy with (h0 | h1) | hz
        · rw [h0, unitInterval.symm_zero, L.apply_one]
          rfl
        · rw [h1, unitInterval.symm_one, L.apply_zero]
          exact proj_fiber (γ _)
        · exact hLp _ _ hz⟩
    let G : C((N → I) × I, E) := L.toContinuousMap.comp ⟨fun q => (σ q.2, q.1),
      (unitInterval.continuous_symm.comp continuous_snd).prodMk continuous_fst⟩
    have hG : IsBoundaryLift p e₀ α G :=
      { proj := fun _ _ => rfl
        bot := fun z => by
          change L (σ 0, z) = e₀
          rw [unitInterval.symm_zero, L.apply_one]
          rfl
        side := fun z hz t => by
          change L (σ t, z) = e₀
          rw [L.eq_fst _ hz]
          exact congrArg Subtype.val (γ.2 z hz) }
    refine ⟨⟦α⟧, ?_⟩
    rw [boundaryMap_mk hp hG]
    congr 1
    ext z
    change L (σ 1, z) = (γ z : E)
    rw [unitInterval.symm_one, L.apply_zero]
    rfl
  · -- the boundary lift itself, run backwards, contracts `i ∘ (top face)` in `E`
    rintro ⟨c, hc⟩
    induction c using Quotient.inductionOn with
    | h α =>
    obtain ⟨G, hG⟩ := exists_isBoundaryLift hp α
    rw [boundaryMap_mk hp hG] at hc
    rw [← hc]
    refine Quotient.sound ⟨
      { toFun := fun q => G (q.2, σ q.1)
        continuous_toFun := G.continuous.comp (continuous_snd.prodMk
          (unitInterval.continuous_symm.comp continuous_fst))
        map_zero_left := fun z => by
          change G (z, σ 0) = G (z, 1)
          rw [unitInterval.symm_zero]
        map_one_left := fun z => by
          change G (z, σ 1) = e₀
          rw [unitInterval.symm_one, hG.bot]
        prop' := fun s z hz => by
          change G (z, σ s) = G (z, 1)
          rw [hG.side z hz, hG.side z hz] }⟩

/-- **Exactness at `π_n(E)`**: `ker p_* = im i_*`. -/
theorem exact_total (c : HomotopyGroup N E e₀) :
    homotopyGroupMap p e₀ c = ⟦GenLoop.const⟧ ↔
      c ∈ range (homotopyGroupMap (fiberIncl p e₀) (fiberPt p e₀)) := by
  induction c using Quotient.inductionOn with
  | h β =>
  constructor
  · -- lift a null-homotopy of `p ∘ β`, starting at `β`; its end is a loop in the fibre
    intro h
    obtain ⟨K⟩ := Quotient.exact h
    let H : C((N → I) × I, B) := K.toContinuousMap.comp ⟨Prod.swap, continuous_swap⟩
    obtain ⟨L, hL, hLg⟩ := hp.exists_lift H (fun q => β q.1)
      (β.1.continuous.comp continuous_fst).continuousOn fun q hq => by
        change p (β q.1) = K (q.2, q.1)
        rcases hq with h0 | hz
        · rw [h0, K.apply_zero]
          rfl
        · rw [K.eq_fst _ hz]
          rfl
    have hLmem : ∀ z, L (z, 1) ∈ fiber p e₀ := fun z => by
      change p (L (z, 1)) = p e₀
      rw [hL]
      change K (1, z) = p e₀
      rw [K.apply_one]
      rfl
    let γ : Ω^ N (fiber p e₀) (fiberPt p e₀) :=
      ⟨⟨fun z => ⟨L (z, 1), hLmem z⟩, (L.continuous.comp (continuous_id.prodMk
        continuous_const)).subtype_mk _⟩, fun z hz => Subtype.ext (by
          change L (z, 1) = e₀
          rw [hLg _ (mk_mem_openBox_of_mem_boundary hz 1)]
          exact GenLoop.boundary β z hz)⟩
    refine ⟨⟦γ⟧, Quotient.sound ⟨
      { toFun := fun q => L (q.2, σ q.1)
        continuous_toFun := L.continuous.comp (continuous_snd.prodMk
          (unitInterval.continuous_symm.comp continuous_fst))
        map_zero_left := fun z => by
          change L (z, σ 0) = L (z, 1)
          rw [unitInterval.symm_zero]
        map_one_left := fun z => by
          change L (z, σ 1) = β z
          rw [unitInterval.symm_one, hLg _ (mk_zero_mem_openBox z)]
        prop' := fun s z hz => by
          change L (z, σ s) = L (z, 1)
          rw [hLg _ (mk_mem_openBox_of_mem_boundary hz _),
            hLg _ (mk_mem_openBox_of_mem_boundary hz _)] }⟩⟩
  · rintro ⟨c, hc⟩
    rw [← hc]
    exact homotopyGroupMap_proj_fiberIncl e₀ c

/-- **Exactness at `π_{n+1}(B)`**: `ker ∂ = im p_*`. -/
theorem exact_base (c : HomotopyGroup (Option N) B (p e₀)) :
    boundaryMap hp e₀ c = ⟦GenLoop.const⟧ ↔ c ∈ range (homotopyGroupMap p e₀) := by
  induction c using Quotient.inductionOn with
  | h α =>
  constructor
  · -- a boundary lift with constant top face is a generalized loop in `E` over `α`
    intro h
    obtain ⟨G, hG⟩ := exists_isBoundaryLift hp α
    rw [boundaryMap_mk hp hG] at h
    obtain ⟨G', hG', htop⟩ := exists_isBoundaryLift_topFace_eq hp hG (Quotient.exact h)
    let β : Ω^ (Option N) E e₀ :=
      ⟨⟨fun y => G' (optionTail y, y none), G'.continuous.comp (continuous_optionTail.prodMk
        (continuous_apply none))⟩, fun y hy => by
        change G' (optionTail y, y none) = e₀
        rcases mem_boundary_option_iff.1 hy with (h0 | h1) | hz
        · rw [h0, hG'.bot]
        · rw [h1]
          have := congrArg Subtype.val (congrFun (congrArg DFunLike.coe htop) (optionTail y))
          exact this
        · exact hG'.side _ hz _⟩
    refine ⟨⟦β⟧, congrArg _ (GenLoop.ext _ _ fun y => ?_)⟩
    change p (G' (optionTail y, y none)) = α y
    rw [hG'.proj, optionPoint_optionTail]
  · rintro ⟨c, hc⟩
    rw [← hc]
    induction c using Quotient.inductionOn with
    | h β =>
    rw [homotopyGroupMap_mk, boundaryMap_mk hp (isBoundaryLift_genLoopMap β)]
    exact congrArg _ (GenLoop.ext _ _ fun z => Subtype.ext
      (GenLoop.boundary β _ (optionPoint_mem_boundary_of_left (Or.inr rfl) z)))

end Exactness

end Morse.Homotopy
