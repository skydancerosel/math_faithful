import Morse.Homotopy.ChangeOfBase
import Morse.Homotopy.ExactSequenceIso

/-!
# Change of basepoint is a group isomorphism

Milnor uses throughout Part IV that the isomorphisms `π_i Ω ≅ π_{i+1} M`, and those of Theorem
22.1, are isomorphisms of groups (for `i ≥ 1`).  In the project these isomorphisms are composites
of induced maps (homomorphisms, `Morse.Homotopy.homotopyGroupHom`), the loop-space isomorphism
(`Morse.Homotopy.homotopyGroupPiLoopMulEquiv`) and one change of basepoint
(`Morse.Homotopy.changeBaseEquiv`, the frame construction of `Morse/Homotopy/ChangeOfBase.lean`).
This file shows that the last is a homomorphism too.

## Main results

* `Morse.Homotopy.evalZeroHomotopyEquiv`: the free path space `C(I, Y)` is homotopy equivalent to
  `Y` by `ω ↦ ω(0)` (contraction `(t, ω) ↦ (s ↦ ω(ts))`).
* `Morse.Homotopy.changeBaseMap_mul`, `Morse.Homotopy.changeBaseMulEquiv`: **change of basepoint
  along any path is a group isomorphism** `π_N(Y, y₀) ≃* π_N(Y, y₁)`.

The proof avoids manipulating the frames: on the free path space, the homotopy `(s, ω) ↦ ω(s)`
from `ev₀` to `ev₁` gives `(ev₁)_* = c_ω ∘ (ev₀)_*` (`Morse.Homotopy.homotopyGroupMap_eq_changeBaseMap`)
at the basepoint `ω`, with `c_ω` the change along `ω` itself; `(ev₀)_*` is onto (`ev₀` is a
homotopy equivalence) and both `(evᵢ)_*` are homomorphisms, so `c_ω` is one.  A path `γ` in `Y`
is such an `ω`, up to the casts relating `γ(0)` to its source.
-/

open Set Function Topology
open scoped unitInterval Topology.Homotopy

noncomputable section

namespace Morse.Homotopy

variable {N : Type*} [Fintype N] [DecidableEq N] {Y : Type*} [TopologicalSpace Y]

/-- Evaluation of a free path at `s`. -/
def evalPath (s : I) : C(C(I, Y), Y) := ⟨fun ω => ω s, continuous_eval_const s⟩

/-- The constant paths, `Y → C(I, Y)`. -/
def constPath : C(Y, C(I, Y)) := ⟨fun y => ContinuousMap.const I y, ContinuousMap.continuous_const'⟩

/-- The free homotopy `ev₀ ≃ ev₁`, `(s, ω) ↦ ω(s)`, on the free path space. -/
def evalHomotopy : (evalPath (Y := Y) 0).Homotopy (evalPath 1) where
  toFun q := q.2 q.1
  continuous_toFun := continuous_eval.comp (continuous_snd.prodMk continuous_fst)
  map_zero_left _ := rfl
  map_one_left _ := rfl

/-- The contraction of the free path space onto the constant paths, `(t, ω) ↦ (s ↦ ω(ts))`. -/
def pathContraction : C(I × C(I, Y), C(I, Y)) :=
  ContinuousMap.curry ⟨fun q : (I × C(I, Y)) × I =>
    q.1.2 ⟨(q.1.1 : ℝ) * q.2, unitInterval.mul_mem q.1.1.2 q.2.2⟩,
    continuous_eval.comp ((continuous_snd.comp continuous_fst).prodMk
      (((continuous_subtype_val.comp (continuous_fst.comp continuous_fst)).mul
        (continuous_subtype_val.comp continuous_snd)).subtype_mk _))⟩

/-- **The free path space is homotopy equivalent to `Y`**, by `ω ↦ ω(0)`. -/
def evalZeroHomotopyEquiv : ContinuousMap.HomotopyEquiv (C(I, Y)) Y where
  toFun := evalPath 0
  invFun := constPath
  left_inv := ⟨{
    toFun := pathContraction
    continuous_toFun := pathContraction.continuous
    map_zero_left := fun ω => by
      ext s
      change ω _ = ω 0
      congr 1
      exact Subtype.ext (zero_mul _)
    map_one_left := fun ω => by
      ext s
      change ω _ = ω s
      congr 1
      exact Subtype.ext (one_mul _) }⟩
  right_inv := by
    have : (evalPath (Y := Y) 0).comp constPath = ContinuousMap.id Y := rfl
    rw [this]

variable [Nonempty N]

/-- Change of basepoint along the track `s ↦ ω(s)` of the free homotopy is multiplicative:
`(ev₁)_* = c_ω ∘ (ev₀)_*` with `(ev₀)_*` onto and both `(evᵢ)_*` homomorphisms. -/
theorem changeBaseMap_evalAt_mul (ω : C(I, Y)) (a b : HomotopyGroup N Y (evalPath 0 ω)) :
    changeBaseMap ((evalHomotopy (Y := Y)).evalAt ω) (a * b) =
      changeBaseMap ((evalHomotopy (Y := Y)).evalAt ω) a *
        changeBaseMap ((evalHomotopy (Y := Y)).evalAt ω) b := by
  have hs : Surjective (homotopyGroupMap (N := N) (evalPath (Y := Y) 0) ω) :=
    (bijective_homotopyGroupMap_of_homotopyEquiv (N := N) (evalZeroHomotopyEquiv (Y := Y)) ω).2
  obtain ⟨a', rfl⟩ := hs a
  obtain ⟨b', rfl⟩ := hs b
  have h := homotopyGroupMap_eq_changeBaseMap (N := N) (evalHomotopy (Y := Y)) ω
  have e : ∀ c, changeBaseMap ((evalHomotopy (Y := Y)).evalAt ω)
      (homotopyGroupMap (N := N) (evalPath 0) ω c) =
      homotopyGroupMap (N := N) (evalPath 1) ω c := fun c => (congrFun h c).symm
  rw [← homotopyGroupMap_mul, e, e, e, homotopyGroupMap_mul]

omit [Fintype N] [DecidableEq N] [Nonempty N] in
theorem changeBaseMap_cast [Fintype N] {a b a' b' : Y} (γ : Path a b) (γ' : Path a' b')
    (h : ∀ t, γ t = γ' t) (ha : a = a') (hb : b = b') (x : HomotopyGroup N Y a) :
    changeBaseMap γ' (cast (congrArg (HomotopyGroup N Y) ha) x) =
      cast (congrArg (HomotopyGroup N Y) hb) (changeBaseMap γ x) := by
  subst ha hb
  obtain rfl : γ = γ' := Path.ext (funext h)
  rfl

omit [Fintype N] in
theorem cast_mul {a a' : Y} (ha : a = a') (x y : HomotopyGroup N Y a) :
    cast (congrArg (HomotopyGroup N Y) ha) (x * y) =
      cast (congrArg (HomotopyGroup N Y) ha) x * cast (congrArg (HomotopyGroup N Y) ha) y := by
  subst ha
  rfl

/-- **Change of basepoint is a group homomorphism.** -/
theorem changeBaseMap_mul {y₀ y₁ : Y} (γ : Path y₀ y₁) (a b : HomotopyGroup N Y y₀) :
    changeBaseMap γ (a * b) = changeBaseMap γ a * changeBaseMap γ b := by
  have h : ∀ t, (evalHomotopy (Y := Y)).evalAt γ.toContinuousMap t = γ t := fun _ => rfl
  have h0 : (evalPath (Y := Y) 0) γ.toContinuousMap = y₀ := γ.source
  have h1 : (evalPath (Y := Y) 1) γ.toContinuousMap = y₁ := γ.target
  have key : ∀ x : HomotopyGroup N Y y₀, changeBaseMap γ x =
      cast (congrArg (HomotopyGroup N Y) h1)
        (changeBaseMap ((evalHomotopy (Y := Y)).evalAt γ.toContinuousMap)
          (cast (congrArg (HomotopyGroup N Y) h0.symm) x)) := by
    intro x
    rw [← changeBaseMap_cast _ γ h h0 h1]
    congr 1
    simp
  rw [key, key, key, cast_mul h0.symm, changeBaseMap_evalAt_mul, cast_mul h1]

/-- **Change of basepoint as a group isomorphism** `π_N(Y, y₀) ≃* π_N(Y, y₁)`. -/
def changeBaseMulEquiv {y₀ y₁ : Y} (γ : Path y₀ y₁) :
    HomotopyGroup N Y y₀ ≃* HomotopyGroup N Y y₁ :=
  { changeBaseEquiv γ with map_mul' := changeBaseMap_mul γ }

theorem changeBaseMulEquiv_apply {y₀ y₁ : Y} (γ : Path y₀ y₁) (x : HomotopyGroup N Y y₀) :
    changeBaseMulEquiv γ x = changeBaseMap γ x := rfl

end Morse.Homotopy
