import Mathlib
import Morse.Homotopy.ExactSequence

/-!
# Isomorphisms from the exact homotopy sequence of a fibration

This file draws from the exact homotopy sequence of a Serre fibration `p : E → B`, with fibre
`F = p⁻¹(p e₀)` (`Morse/Homotopy/ExactSequence.lean`), the consequences Milnor uses in §§23–24:
when `E` (or `B`) has trivial homotopy groups in a range of degrees, the boundary map
`∂ : π_i(B) → π_{i-1}(F)` (or the inclusion `π_i(F) → π_i(E)`) is a bijection there.

## Injectivity

Exactness of pointed sets only says that the kernel is trivial. For injectivity we use two
arguments valid in all degrees, so also for `∂ : π₁(B) → π₀(F)` and `π₀(F) → π₀(E)`, whose
targets are not groups:

* `Morse.Homotopy.exists_homotopyGroupMap_eq_inv_mul`: if `∂ a = ∂ b`, then `b⁻¹ a` lies in the
  image of `p_* : π_{n+1}(E) → π_{n+1}(B)`. Choose boundary lifts `G`, `G'` of `α ∈ a`, `α' ∈ b`
  with the *same* top face (`Morse.Homotopy.exists_isBoundaryLift_topFace_eq`); `G` followed by
  `G'` run backwards is a generalized loop `β` in `E`, and `p ∘ β` is, on the nose, the product
  `transAt none α (symmAt none α')` representing `b⁻¹ a`. Hence `∂` is injective when
  `π_{n+1}(E) = 0` (`Morse.Homotopy.injective_boundaryMap`).
* `Morse.Homotopy.injective_homotopyGroupMap_fiberIncl`: `i_* : π_n(F) → π_n(E)` is injective
  when `π_{n+1}(B) = 0`. A homotopy `L` in `E` between loops in `F` projects to a generalized
  loop `p ∘ L` on `I^{Option N}` in `B`; lifting a null-homotopy of it, relative to the open box
  where `L` is prescribed, ends at a homotopy in `F`.

## Main results

* `Morse.Homotopy.homotopyGroupMap_mul`, `Morse.Homotopy.homotopyGroupHom`: induced maps are
  group homomorphisms; `Morse.Homotopy.boundaryMap_mul`, `Morse.Homotopy.boundaryHom`: so is
  `∂ : π_{n+1}(B) → π_n(F)` for `n ≥ 1` (the boundary lift of a product along a cube coordinate
  is the product of the boundary lifts).
* `Morse.Homotopy.bijective_boundaryMap`, `Morse.Homotopy.bijective_homotopyGroupMap_fiberIncl`,
  and the forms with `π_ i` (`Morse.Homotopy.boundaryMapPi`, `∂ : π_{j+1}(B) → π_j(F)`):
  **(a)** if `π_i(E) = 0` for all `i ≤ k`, then `∂ : π_i(B) → π_{i-1}(F)` is bijective for
  `1 ≤ i ≤ k` and onto for `i = k + 1` (`Morse.Homotopy.bijective_boundaryMapPi_of_le`,
  `Morse.Homotopy.surjective_boundaryMapPi_of_le`, `Morse.Homotopy.boundaryEquivPi`);
  **(b)** if `π_i(B) = 0` for all `i ≤ k`, then `π_i(F) → π_i(E)` is bijective for
  `i ≤ k - 1` and onto for `i = k` (`Morse.Homotopy.bijective_homotopyGroupMap_fiberIncl_of_le`,
  `Morse.Homotopy.surjective_homotopyGroupMap_fiberIncl_of_le`).
* **Two out of three**: if two of `π_n(F)`, `π_n(E)`, `π_n(B)` vanish in the appropriate
  degrees, so does the third (`Morse.Homotopy.subsingleton_homotopyGroup_total`,
  `Morse.Homotopy.subsingleton_homotopyGroup_base`,
  `Morse.Homotopy.subsingleton_homotopyGroup_fiber`, and the `π_ i` forms
  `Morse.Homotopy.subsingleton_pi_base`, `Morse.Homotopy.subsingleton_pi_fiber`).
-/

open Set Function Topology
open scoped unitInterval Topology.Homotopy

noncomputable section

namespace Morse.Homotopy

variable {E B : Type*} [TopologicalSpace E] [TopologicalSpace B]

/-! ### Group homomorphisms -/

section Hom

variable {N X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [DecidableEq N]

theorem genLoopMap_transAt (f : C(X, Y)) {x : X} (i : N) (γ γ' : Ω^ N X x) :
    genLoopMap f (GenLoop.transAt i γ γ') =
      GenLoop.transAt i (genLoopMap f γ) (genLoopMap f γ') := by
  ext y
  simp only [genLoopMap_apply, GenLoop.transAt, GenLoop.coe_copy]
  split_ifs <;> rfl

/-- **Induced maps are group homomorphisms.** -/
theorem homotopyGroupMap_mul [Nonempty N] (f : C(X, Y)) (x : X) (a b : HomotopyGroup N X x) :
    homotopyGroupMap f x (a * b) = homotopyGroupMap f x a * homotopyGroupMap f x b := by
  induction a using Quotient.inductionOn with
  | h γ =>
  induction b using Quotient.inductionOn with
  | h γ' =>
  let i := Classical.arbitrary N
  change homotopyGroupMap f x (((· * ·) : _ → _ → HomotopyGroup N X x) ⟦γ⟧ ⟦γ'⟧) =
    ((· * ·) : _ → _ → HomotopyGroup N Y (f x)) ⟦genLoopMap f γ⟧ ⟦genLoopMap f γ'⟧
  rw [HomotopyGroup.mul_spec (i := i), HomotopyGroup.mul_spec (i := i), homotopyGroupMap_mk,
    genLoopMap_transAt]

/-- The map induced by `f` on `π_N`, `N` nonempty, as a group homomorphism. -/
def homotopyGroupHom [Nonempty N] (f : C(X, Y)) (x : X) :
    HomotopyGroup N X x →* HomotopyGroup N Y (f x) where
  toFun := homotopyGroupMap f x
  map_one' := homotopyGroupMap_const f x
  map_mul' := homotopyGroupMap_mul f x

end Hom

variable {N : Type*} [Finite N] {p : C(E, B)} (hp : IsSerreFibration p) (e₀ : E)
include hp

/-- **The boundary map is a group homomorphism** `π_{n+1}(B) → π_n(F)` for `n ≥ 1`: a boundary
lift of a product along a cube coordinate `j` is the product of the boundary lifts along `j`. -/
theorem boundaryMap_mul [DecidableEq N] [Nonempty N] (a b : HomotopyGroup (Option N) B (p e₀)) :
    boundaryMap hp e₀ (a * b) = boundaryMap hp e₀ a * boundaryMap hp e₀ b := by
  induction a using Quotient.inductionOn with
  | h α =>
  induction b using Quotient.inductionOn with
  | h α' =>
  let j := Classical.arbitrary N
  obtain ⟨G, hG⟩ := exists_isBoundaryLift hp α
  obtain ⟨G', hG'⟩ := exists_isBoundaryLift hp α'
  -- the two lifts side by side in the coordinate `j`
  have hupd : ∀ (z : N → I) (v : I), (v = 0 ∨ v = 1) → Function.update z j v ∈ Cube.boundary N :=
    fun z v hv => ⟨j, by rwa [Function.update_self]⟩
  let GG : C((N → I) × I, E) :=
    ⟨fun q => if (q.1 j : ℝ) ≤ 1 / 2 then
        G' (Function.update q.1 j (Set.projIcc 0 1 zero_le_one (2 * q.1 j)), q.2)
      else G (Function.update q.1 j (Set.projIcc 0 1 zero_le_one (2 * q.1 j - 1)), q.2), by
      refine Continuous.if_le ?_ ?_ (continuous_subtype_val.comp ((continuous_apply j).comp
        continuous_fst)) continuous_const fun q hq => ?_
      · exact G'.continuous.comp ((continuous_fst.update j (continuous_projIcc.comp
          (continuous_const.mul (continuous_subtype_val.comp ((continuous_apply j).comp
            continuous_fst))))).prodMk continuous_snd)
      · exact G.continuous.comp ((continuous_fst.update j (continuous_projIcc.comp
          ((continuous_const.mul (continuous_subtype_val.comp ((continuous_apply j).comp
            continuous_fst))).sub continuous_const))).prodMk continuous_snd)
      · rw [hq, show (2 : ℝ) * (1 / 2) = 1 by norm_num, show (1 : ℝ) - 1 = 0 by norm_num,
          projIcc_eq_one le_rfl, projIcc_eq_zero le_rfl,
          hG'.side _ (hupd _ _ (Or.inr rfl)), hG.side _ (hupd _ _ (Or.inl rfl))]⟩
  have hGG : IsBoundaryLift p e₀ (GenLoop.transAt (some j) α' α) GG :=
    { proj := fun z t => by
        change p (if (z j : ℝ) ≤ 1 / 2 then _ else _) = _
        simp only [GenLoop.transAt, GenLoop.coe_copy, optionPoint_some,
          update_some_optionPoint]
        split_ifs
        · exact hG'.proj _ _
        · exact hG.proj _ _
      bot := fun z => by
        change (if (z j : ℝ) ≤ 1 / 2 then _ else _) = e₀
        split_ifs
        · exact hG'.bot _
        · exact hG.bot _
      side := fun z hz t => by
        change (if (z j : ℝ) ≤ 1 / 2 then
            G' (Function.update z j (Set.projIcc 0 1 zero_le_one (2 * z j)), t)
          else G (Function.update z j (Set.projIcc 0 1 zero_le_one (2 * z j - 1)), t)) = e₀
        obtain ⟨k, hk⟩ := hz
        by_cases hkj : k = j
        · subst hkj
          rcases hk with h0 | h1
          · rw [if_pos (by rw [h0]; norm_num), h0, Set.Icc.coe_zero, mul_zero,
              projIcc_eq_zero le_rfl, hG'.side _ (hupd _ _ (Or.inl rfl))]
          · rw [if_neg (by rw [h1]; norm_num), h1, Set.Icc.coe_one,
              show (2 : ℝ) * 1 - 1 = 1 by norm_num, projIcc_eq_one le_rfl,
              hG.side _ (hupd _ _ (Or.inr rfl))]
        · have hb : ∀ v, Function.update z j v ∈ Cube.boundary N := fun v =>
            ⟨k, by rwa [Function.update_of_ne hkj]⟩
          split_ifs
          · exact hG'.side _ (hb _) _
          · exact hG.side _ (hb _) _ }
  change boundaryMap hp e₀ (((· * ·) : _ → _ → HomotopyGroup (Option N) B (p e₀)) ⟦α⟧ ⟦α'⟧) =
    ((· * ·) : _ → _ → HomotopyGroup N (fiber p e₀) (fiberPt p e₀))
      (boundaryMap hp e₀ ⟦α⟧) (boundaryMap hp e₀ ⟦α'⟧)
  rw [HomotopyGroup.mul_spec (i := some j), boundaryMap_mk hp hGG, boundaryMap_mk hp hG,
    boundaryMap_mk hp hG', HomotopyGroup.mul_spec (i := j)]
  congr 1
  ext z
  change (if (z j : ℝ) ≤ 1 / 2 then _ else _) = _
  simp only [GenLoop.transAt, GenLoop.coe_copy]
  split_ifs <;> rfl

/-- The boundary map on `π_N`, `N` nonempty, as a group homomorphism. -/
def boundaryHom [DecidableEq N] [Nonempty N] :
    HomotopyGroup (Option N) B (p e₀) →* HomotopyGroup N (fiber p e₀) (fiberPt p e₀) where
  toFun := boundaryMap hp e₀
  map_one' := by
    rw [HomotopyGroup.one_def, HomotopyGroup.one_def]
    exact (exact_base hp e₀ _).2 ⟨_, homotopyGroupMap_const p e₀⟩
  map_mul' := boundaryMap_mul hp e₀

/-! ### Injectivity -/

/-- **`∂ a = ∂ b` forces `b⁻¹ a ∈ im p_*`.** -/
theorem exists_homotopyGroupMap_eq_inv_mul [DecidableEq N]
    {a b : HomotopyGroup (Option N) B (p e₀)} (h : boundaryMap hp e₀ a = boundaryMap hp e₀ b) :
    ∃ c : HomotopyGroup (Option N) E e₀, homotopyGroupMap p e₀ c = b⁻¹ * a := by
  induction a using Quotient.inductionOn with
  | h α =>
  induction b using Quotient.inductionOn with
  | h α' =>
  obtain ⟨G, hG⟩ := exists_isBoundaryLift hp α
  obtain ⟨G₁, hG₁⟩ := exists_isBoundaryLift hp α'
  rw [boundaryMap_mk hp hG, boundaryMap_mk hp hG₁] at h
  -- a boundary lift of `α'` with the same top face as `G`
  obtain ⟨G', hG', htop⟩ := exists_isBoundaryLift_topFace_eq hp hG₁ (Quotient.exact h.symm)
  have htop' : ∀ z, G' (z, 1) = G (z, 1) := fun z =>
    congrArg Subtype.val (congrFun (congrArg DFunLike.coe htop) z)
  -- `G` followed by `G'` backwards
  let β : Ω^ (Option N) E e₀ :=
    ⟨⟨fun y => if (y none : ℝ) ≤ 1 / 2 then
        G (optionTail y, Set.projIcc 0 1 zero_le_one (2 * y none))
      else G' (optionTail y, σ (Set.projIcc 0 1 zero_le_one (2 * y none - 1))), by
      refine Continuous.if_le ?_ ?_ (continuous_subtype_val.comp (continuous_apply none))
        continuous_const fun y hy => ?_
      · exact G.continuous.comp (continuous_optionTail.prodMk (continuous_projIcc.comp
          (continuous_const.mul (continuous_subtype_val.comp (continuous_apply none)))))
      · exact G'.continuous.comp (continuous_optionTail.prodMk
          (unitInterval.continuous_symm.comp (continuous_projIcc.comp ((continuous_const.mul
            (continuous_subtype_val.comp (continuous_apply none))).sub continuous_const))))
      · rw [hy, show (2 : ℝ) * (1 / 2) = 1 by norm_num, show (1 : ℝ) - 1 = 0 by norm_num,
          projIcc_eq_one le_rfl, projIcc_eq_zero le_rfl, unitInterval.symm_zero, htop']⟩,
      fun y hy => by
        change (if (y none : ℝ) ≤ 1 / 2 then _ else _) = e₀
        rcases mem_boundary_option_iff.1 hy with (h0 | h1) | hz
        · rw [if_pos (by rw [h0]; norm_num), h0, Set.Icc.coe_zero, mul_zero,
            projIcc_eq_zero le_rfl, hG.bot]
        · rw [if_neg (by rw [h1]; norm_num), h1, Set.Icc.coe_one,
            show (2 : ℝ) * 1 - 1 = 1 by norm_num, projIcc_eq_one le_rfl,
            unitInterval.symm_one, hG'.bot]
        · split_ifs
          · exact hG.side _ hz _
          · exact hG'.side _ hz _⟩
  refine ⟨⟦β⟧, ?_⟩
  change (⟦genLoopMap p β⟧ : HomotopyGroup (Option N) B (p e₀)) =
    ((· * ·) : _ → _ → HomotopyGroup (Option N) B (p e₀))
      (⟦α'⟧ : HomotopyGroup (Option N) B (p e₀))⁻¹ ⟦α⟧
  rw [HomotopyGroup.inv_spec (i := none), HomotopyGroup.mul_spec (i := none)]
  congr 1
  ext y
  change p (if (y none : ℝ) ≤ 1 / 2 then _ else _) = _
  simp only [GenLoop.transAt, GenLoop.symmAt, GenLoop.coe_copy, update_none_eq_optionPoint]
  split_ifs
  · rw [hG.proj]
  · rw [hG'.proj]
    congr 1
    funext k
    cases k with
    | none => rfl
    | some k => rfl

/-- **`∂` is injective on `π_{n+1}(B)` when `π_{n+1}(E)` is trivial.** -/
theorem injective_boundaryMap (hE : Subsingleton (HomotopyGroup (Option N) E e₀)) :
    Injective (boundaryMap (N := N) hp e₀) := by
  classical
  intro a b h
  obtain ⟨c, hc⟩ := exists_homotopyGroupMap_eq_inv_mul hp e₀ h
  have h1 : homotopyGroupMap p e₀ c = 1 := by
    rw [Subsingleton.elim c 1, HomotopyGroup.one_def, HomotopyGroup.one_def]
    exact homotopyGroupMap_const p e₀
  rw [h1] at hc
  exact (inv_mul_eq_one.1 hc.symm).symm

/-- **`i_*` is injective on `π_n(F)` when `π_{n+1}(B)` is trivial.** -/
theorem injective_homotopyGroupMap_fiberIncl
    (hB : Subsingleton (HomotopyGroup (Option N) B (p e₀))) :
    Injective (homotopyGroupMap (N := N) (fiberIncl p e₀) (fiberPt p e₀)) := by
  intro a b h
  induction a using Quotient.inductionOn with
  | h γ =>
  induction b using Quotient.inductionOn with
  | h γ' =>
  obtain ⟨L⟩ := Quotient.exact h
  have hLb : ∀ s, ∀ z ∈ Cube.boundary N, L (s, z) = e₀ := fun s z hz => by
    rw [L.eq_fst s hz]
    exact congrArg Subtype.val (γ.2 z hz)
  -- the projection of the homotopy `L`, a generalized loop on `I^{Option N}` in `B`
  let δ : Ω^ (Option N) B (p e₀) :=
    ⟨⟨fun y => p (L (y none, optionTail y)), p.continuous.comp (L.continuous.comp
      ((continuous_apply none).prodMk continuous_optionTail))⟩, fun y hy => by
      change p (L (y none, optionTail y)) = p e₀
      rcases mem_boundary_option_iff.1 hy with (h0 | h1) | hz
      · rw [h0, L.apply_zero]
        exact proj_fiber (γ _)
      · rw [h1, L.apply_one]
        exact proj_fiber (γ' _)
      · rw [hLb _ _ hz]⟩
  obtain ⟨Q⟩ : GenLoop.Homotopic δ GenLoop.const :=
    Quotient.exact (@Subsingleton.elim _ hB (⟦δ⟧ : HomotopyGroup (Option N) B (p e₀))
      ⟦GenLoop.const⟧)
  -- lift the null-homotopy `Q` of `δ`, starting at `L`
  let H : C((Option N → I) × I, B) := Q.toContinuousMap.comp ⟨Prod.swap, continuous_swap⟩
  obtain ⟨R, hR, hRg⟩ := hp.exists_lift H (fun q => L (q.1 none, optionTail q.1))
    (L.continuous.comp (((continuous_apply none).comp continuous_fst).prodMk
      (continuous_optionTail.comp continuous_fst))).continuousOn fun q hq => by
      change δ q.1 = Q (q.2, q.1)
      rcases hq with h0 | hy
      · rw [h0, Q.apply_zero]
        rfl
      · rw [Q.eq_fst _ hy]
        rfl
  have hRmem : ∀ q : I × (N → I), R (optionPoint q.1 q.2, 1) ∈ fiber p e₀ := fun q => by
    change p (R (optionPoint q.1 q.2, 1)) = p e₀
    rw [hR]
    change Q (1, optionPoint q.1 q.2) = p e₀
    rw [Q.apply_one]
    rfl
  have hRbox : ∀ s z, optionPoint s z ∈ Cube.boundary (Option N) →
      R (optionPoint s z, 1) = L (s, z) := fun s z hz =>
    hRg _ (mk_mem_openBox_of_mem_boundary hz 1)
  refine Quotient.sound ⟨
    { toFun := fun q => ⟨R (optionPoint q.1 q.2, 1), hRmem q⟩
      continuous_toFun := (R.continuous.comp ((continuous_optionPoint.comp
        (continuous_fst.prodMk continuous_snd)).prodMk continuous_const)).subtype_mk _
      map_zero_left := fun z => Subtype.ext ?_
      map_one_left := fun z => Subtype.ext ?_
      prop' := fun s z hz => Subtype.ext ?_ }⟩
  · change R (optionPoint 0 z, 1) = (γ z : E)
    rw [hRbox 0 z (optionPoint_mem_boundary_of_left (Or.inl rfl) z), L.apply_zero]
    rfl
  · change R (optionPoint 1 z, 1) = (γ' z : E)
    rw [hRbox 1 z (optionPoint_mem_boundary_of_left (Or.inr rfl) z), L.apply_one]
    rfl
  · change R (optionPoint s z, 1) = (γ z : E)
    rw [hRbox s z (optionPoint_mem_boundary_of_right s hz), L.eq_fst s hz]
    rfl

/-! ### Bijectivity -/

/-- `∂ : π_{n+1}(B) → π_n(F)` is onto when `π_n(E)` is trivial. -/
theorem surjective_boundaryMap (hE : Subsingleton (HomotopyGroup N E e₀)) :
    Surjective (boundaryMap (N := N) hp e₀) := fun c =>
  (exact_fiber hp e₀ c).1 (@Subsingleton.elim _ hE _ _)

/-- `∂ : π_{n+1}(B) → π_n(F)` is bijective when `π_{n+1}(E)` and `π_n(E)` are trivial. -/
theorem bijective_boundaryMap (hE₁ : Subsingleton (HomotopyGroup (Option N) E e₀))
    (hE₀ : Subsingleton (HomotopyGroup N E e₀)) : Bijective (boundaryMap (N := N) hp e₀) :=
  ⟨injective_boundaryMap hp e₀ hE₁, surjective_boundaryMap hp e₀ hE₀⟩

/-- `i_* : π_n(F) → π_n(E)` is onto when `π_n(B)` is trivial. -/
theorem surjective_homotopyGroupMap_fiberIncl (hB : Subsingleton (HomotopyGroup N B (p e₀))) :
    Surjective (homotopyGroupMap (N := N) (fiberIncl p e₀) (fiberPt p e₀)) := fun c =>
  (exact_total hp e₀ c).1 (@Subsingleton.elim _ hB _ _)

/-- `i_* : π_n(F) → π_n(E)` is bijective when `π_{n+1}(B)` and `π_n(B)` are trivial. -/
theorem bijective_homotopyGroupMap_fiberIncl
    (hB₁ : Subsingleton (HomotopyGroup (Option N) B (p e₀)))
    (hB₀ : Subsingleton (HomotopyGroup N B (p e₀))) :
    Bijective (homotopyGroupMap (N := N) (fiberIncl p e₀) (fiberPt p e₀)) :=
  ⟨injective_homotopyGroupMap_fiberIncl hp e₀ hB₁, surjective_homotopyGroupMap_fiberIncl hp e₀ hB₀⟩

/-! ### Two out of three -/

/-- If `π_n(F)` and `π_n(B)` are trivial, so is `π_n(E)`. -/
theorem subsingleton_homotopyGroup_total
    (hF : Subsingleton (HomotopyGroup N (fiber p e₀) (fiberPt p e₀)))
    (hB : Subsingleton (HomotopyGroup N B (p e₀))) : Subsingleton (HomotopyGroup N E e₀) :=
  (surjective_homotopyGroupMap_fiberIncl hp e₀ hB).subsingleton

/-- If `π_{n+1}(E)` and `π_n(F)` are trivial, so is `π_{n+1}(B)`. -/
theorem subsingleton_homotopyGroup_base (hE : Subsingleton (HomotopyGroup (Option N) E e₀))
    (hF : Subsingleton (HomotopyGroup N (fiber p e₀) (fiberPt p e₀))) :
    Subsingleton (HomotopyGroup (Option N) B (p e₀)) := by
  have key : ∀ c : HomotopyGroup (Option N) B (p e₀), c = ⟦GenLoop.const⟧ := fun c => by
    obtain ⟨c', hc'⟩ := (exact_base hp e₀ c).1 (@Subsingleton.elim _ hF _ _)
    rw [← hc', @Subsingleton.elim _ hE c' ⟦GenLoop.const⟧, homotopyGroupMap_const]
  exact ⟨fun a b => (key a).trans (key b).symm⟩

/-- If `π_{n+1}(B)` and `π_n(E)` are trivial, so is `π_n(F)`. -/
theorem subsingleton_homotopyGroup_fiber (hB : Subsingleton (HomotopyGroup (Option N) B (p e₀)))
    (hE : Subsingleton (HomotopyGroup N E e₀)) :
    Subsingleton (HomotopyGroup N (fiber p e₀) (fiberPt p e₀)) :=
  have : Subsingleton (HomotopyGroup N E (fiberIncl p e₀ (fiberPt p e₀))) := hE
  (injective_homotopyGroupMap_fiberIncl hp e₀ hB).subsingleton

/-! ### The forms with `π_ i` -/

omit hp in
theorem subsingleton_homotopyGroup_option {X : Type*} [TopologicalSpace X] {x : X} {j : ℕ}
    (h : Subsingleton (π_ (j + 1) X x)) : Subsingleton (HomotopyGroup (Option (Fin j)) X x) :=
  (homotopyGroupCongr (X := X) (x := x) (finSuccEquiv j)).symm.subsingleton

omit [Finite N] in
/-- **The boundary map** `∂ : π_{j+1}(B, p e₀) → π_j(F, e₀)` (`π_{j+1}` indexed by
`Option (Fin j)` through `finSuccEquiv`). -/
def boundaryMapPi (j : ℕ) : π_ (j + 1) B (p e₀) → π_ j (fiber p e₀) (fiberPt p e₀) :=
  boundaryMap hp e₀ ∘ homotopyGroupCongr (finSuccEquiv j)

omit [Finite N] in
/-- **(a), bijectivity**: if `π_i(E) = 0` for all `i ≤ k`, then `∂ : π_{j+1}(B) → π_j(F)` is
bijective for `j + 1 ≤ k`. -/
theorem bijective_boundaryMapPi_of_le {k : ℕ} (hE : ∀ i ≤ k, Subsingleton (π_ i E e₀)) {j : ℕ}
    (hj : j + 1 ≤ k) : Bijective (boundaryMapPi hp e₀ j) :=
  (bijective_boundaryMap hp e₀ (subsingleton_homotopyGroup_option (hE (j + 1) hj))
    (hE j (by omega))).comp (homotopyGroupCongr (finSuccEquiv j)).bijective

omit [Finite N] in
/-- **(a), surjectivity**: if `π_i(E) = 0` for all `i ≤ k`, then `∂ : π_{j+1}(B) → π_j(F)` is
onto for `j ≤ k`. -/
theorem surjective_boundaryMapPi_of_le {k : ℕ} (hE : ∀ i ≤ k, Subsingleton (π_ i E e₀)) {j : ℕ}
    (hj : j ≤ k) : Surjective (boundaryMapPi hp e₀ j) :=
  (surjective_boundaryMap hp e₀ (hE j hj)).comp (homotopyGroupCongr (finSuccEquiv j)).surjective

omit [Finite N] in
/-- **(a)** as an equivalence `π_{j+1}(B) ≃ π_j(F)`, for `j + 1 ≤ k`. -/
def boundaryEquivPi {k : ℕ} (hE : ∀ i ≤ k, Subsingleton (π_ i E e₀)) {j : ℕ} (hj : j + 1 ≤ k) :
    π_ (j + 1) B (p e₀) ≃ π_ j (fiber p e₀) (fiberPt p e₀) :=
  Equiv.ofBijective _ (bijective_boundaryMapPi_of_le hp e₀ hE hj)

omit [Finite N] in
/-- **(b), bijectivity**: if `π_i(B) = 0` for all `i ≤ k`, then `i_* : π_i(F) → π_i(E)` is
bijective for `i + 1 ≤ k`. -/
theorem bijective_homotopyGroupMap_fiberIncl_of_le {k : ℕ}
    (hB : ∀ i ≤ k, Subsingleton (π_ i B (p e₀))) {i : ℕ} (hi : i + 1 ≤ k) :
    Bijective (homotopyGroupMap (N := Fin i) (fiberIncl p e₀) (fiberPt p e₀)) :=
  bijective_homotopyGroupMap_fiberIncl hp e₀ (subsingleton_homotopyGroup_option (hB (i + 1) hi))
    (hB i (by omega))

omit [Finite N] in
/-- **(b), surjectivity**: if `π_i(B) = 0` for all `i ≤ k`, then `i_* : π_i(F) → π_i(E)` is onto
for `i ≤ k`. -/
theorem surjective_homotopyGroupMap_fiberIncl_of_le {k : ℕ}
    (hB : ∀ i ≤ k, Subsingleton (π_ i B (p e₀))) {i : ℕ} (hi : i ≤ k) :
    Surjective (homotopyGroupMap (N := Fin i) (fiberIncl p e₀) (fiberPt p e₀)) :=
  surjective_homotopyGroupMap_fiberIncl hp e₀ (hB i hi)

omit [Finite N] in
/-- If `π_{j+1}(E)` and `π_j(F)` are trivial, so is `π_{j+1}(B)`. -/
theorem subsingleton_pi_base {j : ℕ} (hE : Subsingleton (π_ (j + 1) E e₀))
    (hF : Subsingleton (π_ j (fiber p e₀) (fiberPt p e₀))) : Subsingleton (π_ (j + 1) B (p e₀)) :=
  have := subsingleton_homotopyGroup_base hp e₀ (subsingleton_homotopyGroup_option hE) hF
  (homotopyGroupCongr (finSuccEquiv j)).subsingleton

omit [Finite N] in
/-- If `π_{j+1}(B)` and `π_j(E)` are trivial, so is `π_j(F)`. -/
theorem subsingleton_pi_fiber {j : ℕ} (hB : Subsingleton (π_ (j + 1) B (p e₀)))
    (hE : Subsingleton (π_ j E e₀)) : Subsingleton (π_ j (fiber p e₀) (fiberPt p e₀)) :=
  subsingleton_homotopyGroup_fiber hp e₀ (subsingleton_homotopyGroup_option hB) hE

end Morse.Homotopy
