import Morse
import RoundTrip.Check
import RoundTrip.Blind.V6_8
import RoundTrip.Bridge

namespace RoundTrip.V6_8

/-- The project's statement (universes instantiated at 0; `Morse.IsParallel` is a definition):
Lemma 8.2 for the induced connection on a slice submanifold `N ⊆ V` — along a smooth curve, every
tangent vector at `c(t₀)` extends to exactly one parallel field, and parallel fields are smooth. -/
def A : Prop :=
  type_of% @Morse.exists_unique_isParallel.{0,0,0} ∧ type_of% @Morse.IsParallel.contDiff.{0,0,0}

theorem A_holds : A := ⟨@Morse.exists_unique_isParallel, @Morse.IsParallel.contDiff⟩


/-! ## The embedded special case

B is specialized to `M = ↥N` (`RoundTrip.Bridge.Sub hN`) for a slice submanifold `N ⊆ V` with
model `ℝⁿ` and the induced connection `Bridge.conn` (`B_emb`). Fields along a curve in `↥N` are
read in `V` through `Bridge.ambA` and back through `liftA`; every `D/dt` of B for `Bridge.conn`
is the project's `covDeriv` read in `V` (`Emb.D_eq_covDeriv`, from the project's Lemma 8.1), so
B's parallel fields are the smooth parallel fields of the project (`Emb.isParallel_iff`). Then
`B_emb` is exactly A's Lemma 8.2 among smooth parallel fields (`A82`, any initial time by
shifting the curve). -/

open Set
open scoped ContDiff Manifold

namespace Emb

set_option linter.unusedSectionVars false

open RoundTrip.Bridge

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] {n : ℕ} {N : Set V}
  {hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N}

/-! Glue copied from `Items/V6_6.lean` (same blind vocabulary): fields along a curve in `↥N` are
read in `V` through `ambA` and back through `liftA`; Mathlib-level `D/dt` and project-level
operations correspond through `toProj` / `toMath`. -/

/-- A project-level operation on fields `ℝ → V` along `c` carries smooth tangent fields to smooth
tangent fields (B builds this into its notion of covariant derivative operator). -/
def PresSmooth (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N) (c : ℝ → N)
    (D : (ℝ → V) → ℝ → V) : Prop :=
  ∀ X : ℝ → V, ContDiff ℝ ∞ X → Morse.IsFieldAlong hN c X →
    ContDiff ℝ ∞ (D X) ∧ Morse.IsFieldAlong hN c (D X)

theorem isSmoothCurve_iff' {c : ℝ → Sub hN} :
    IsSmoothCurve (n := n) c ↔ ContDiff ℝ ∞ (incl hN ∘ c) := by
  unfold IsSmoothCurve
  rw [← contMDiffOn_univ, ← contDiffOn_univ]
  exact contMDiffOn_curve_iff

theorem isSmoothAlong_iff' {c : ℝ → Sub hN} {U : FieldAlong (n := n) c} :
    IsSmoothAlong (n := n) c U ↔ IsSmoothCurve (n := n) c ∧ ContDiff ℝ ∞ (ambA c U) := by
  unfold IsSmoothAlong IsSmoothCurve
  rw [← contMDiffOn_univ, ← contMDiffOn_univ, ← contDiffOn_univ]
  exact contMDiffOn_along_iff

theorem isFieldAlong_ambA (c : ℝ → Sub hN) (U : FieldAlong (n := n) c) :
    Morse.IsFieldAlong hN c (ambA c U) := fun t => D_mem (c t) (U t)

/-- `L ∘ X` for an ambient field `X : ℝ → V` along `c`. -/
noncomputable def liftA (c : ℝ → Sub hN) (X : ℝ → V) : FieldAlong (n := n) c :=
  fun t => L hN (c t) (X t)

theorem ambA_liftA {c : ℝ → Sub hN} {X : ℝ → V} (hX : Morse.IsFieldAlong hN c X) :
    ambA c (liftA c X) = X := funext fun t => D_L (hX t)

theorem liftA_ambA (c : ℝ → Sub hN) (U : FieldAlong (n := n) c) : liftA c (ambA c U) = U :=
  funext fun t => L_D (c t) (U t)

theorem isSmoothAlong_liftA {c : ℝ → Sub hN} (hc : IsSmoothCurve (n := n) c) {X : ℝ → V}
    (hX : ContDiff ℝ ∞ X) (hXT : Morse.IsFieldAlong hN c X) :
    IsSmoothAlong (n := n) c (liftA c X) :=
  isSmoothAlong_iff'.2 ⟨hc, by rw [ambA_liftA hXT]; exact hX⟩

/-- The velocity of B, read in `V`, is the project's `velocity`. -/
theorem D_velocity (c : ℝ → Sub hN) (t : ℝ) :
    D hN (c t) (velocity (n := n) c t) = Morse.velocity (N := N) c t :=
  D_mfderiv_curve c t

/-- The vector field `q ↦ L_q(Y q)` of a tangent map `Y : N → V`. -/
noncomputable def liftF (Y : N → V) : (p : Sub hN) → TangentSpace 𝓘(ℝ, Rn n) p :=
  fun q => L hN q (Y q)

theorem amb_liftF {Y : N → V} (hYT : Morse.IsTangentField hN Y) : amb (liftF (hN := hN) Y) = Y :=
  funext fun q => D_L (hYT q)

theorem conn_liftF {Y : N → V} (hYT : Morse.IsTangentField hN Y) (c : ℝ → Sub hN) (t : ℝ) :
    D hN (c t) (conn (liftF (hN := hN) Y) (c t) (velocity (n := n) c t)) =
      Morse.covAt hN (c t) (Morse.velocity (N := N) c t) Y := by
  rw [D_conn_apply, D_velocity, amb_liftF hYT]

/-- Mathlib-level `D/dt` read as a project-level operation on fields `ℝ → V`. -/
noncomputable def toProj (c : ℝ → Sub hN) (Dm : FieldAlong (n := n) c → FieldAlong (n := n) c) :
    (ℝ → V) → ℝ → V := fun X t => D hN (c t) (Dm (liftA c X) t)

/-- Project-level `D/dt` read as a Mathlib-level operation on fields along `c`. -/
noncomputable def toMath (c : ℝ → Sub hN) (Dp : (ℝ → V) → ℝ → V) :
    FieldAlong (n := n) c → FieldAlong (n := n) c := fun U t => L hN (c t) (Dp (ambA c U) t)

theorem toProj_isCovDerivAlong {c : ℝ → Sub hN} (hc : IsSmoothCurve (n := n) c)
    {Dm : FieldAlong (n := n) c → FieldAlong (n := n) c}
    (hD : IsCovDerivAlong (conn (hN := hN)) c Dm) :
    Morse.IsCovDerivAlong hN c (toProj c Dm) ∧ PresSmooth hN c (toProj c Dm) := by
  obtain ⟨h0, ha, hb, hi⟩ := hD
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · intro X Y hX hY hXT hYT t
    have e : liftA (n := n) c (fun s => X s + Y s) = fun s => liftA c X s + liftA c Y s :=
      funext fun s => map_add (L hN (c s)) _ _
    simp only [toProj]
    rw [e, congrFun (ha _ _ (isSmoothAlong_liftA hc hX hXT) (isSmoothAlong_liftA hc hY hYT)) t]
    exact map_add (D hN (c t)) _ _
  · intro f X hf hX hXT t
    have e : liftA (n := n) c (fun s => f s • X s) = fun s => f s • liftA c X s :=
      funext fun s => map_smul (L hN (c s)) _ _
    simp only [toProj]
    rw [e, congrFun (hb f hf _ (isSmoothAlong_liftA hc hX hXT)) t, D_tadd, D_tsmul, D_tsmul]
    rw [show D hN (c t) (liftA c X t) = X t from D_L (hXT t)]
  · intro Y hY hYT t
    have hY' : IsSmoothVF (liftF (hN := hN) Y) := by
      unfold IsSmoothVF
      rw [contMDiff_section_iff, amb_liftF hYT]
      exact hY
    have e : liftA (n := n) c (fun s => Y (c s)) = fun s => liftF (hN := hN) Y (c s) := rfl
    simp only [toProj]
    rw [e, congrFun (hi _ hY') t]
    exact conn_liftF hYT c t
  · intro X hX hXT
    have hs := isSmoothAlong_iff'.1 (h0 _ (isSmoothAlong_liftA hc hX hXT))
    exact ⟨hs.2, fun t => D_mem (c t) _⟩

theorem toMath_isCovDerivAlong {c : ℝ → Sub hN} (hc : IsSmoothCurve (n := n) c)
    {Dp : (ℝ → V) → ℝ → V} (hD : Morse.IsCovDerivAlong hN c Dp) (hS : PresSmooth hN c Dp) :
    IsCovDerivAlong (conn (hN := hN)) c (toMath c Dp) := by
  have hU : ∀ {U : FieldAlong (n := n) c}, IsSmoothAlong (n := n) c U → ContDiff ℝ ∞ (ambA c U) :=
    fun h => (isSmoothAlong_iff'.1 h).2
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro U hU'
    refine isSmoothAlong_iff'.2 ⟨hc, ?_⟩
    have e : ambA c (toMath c Dp U) = Dp (ambA c U) :=
      ambA_liftA (hS _ (hU hU') (isFieldAlong_ambA c U)).2
    rw [e]
    exact (hS _ (hU hU') (isFieldAlong_ambA c U)).1
  · intro U U' hU1 hU2
    funext t
    have e : ambA c (fun t => U t + U' t) = fun s => ambA c U s + ambA c U' s :=
      funext fun s => map_add (D hN (c s)) _ _
    simp only [toMath]
    rw [e, hD.add _ _ (hU hU1) (hU hU2) (isFieldAlong_ambA c U) (isFieldAlong_ambA c U') t]
    exact map_add (L hN (c t)) _ _
  · intro f hf U hU'
    funext t
    have e : ambA c (fun t => f t • U t) = fun s => f s • ambA c U s :=
      funext fun s => map_smul (D hN (c s)) _ _
    simp only [toMath]
    rw [e, hD.smul f _ hf (hU hU') (isFieldAlong_ambA c U) t, map_add, map_smul, map_smul]
    rw [show L hN (c t) (ambA c U t) = U t from L_D (c t) (U t)]
    rfl
  · intro Y hY
    funext t
    have e : ambA c (fun t => Y (c t)) = fun s => amb Y (c s) := rfl
    simp only [toMath]
    rw [e, hD.induced (amb Y) (contMDiff_amb hY) (isTangentField_amb Y) t]
    apply D_injective (c t)
    rw [D_conn_apply, D_velocity]
    exact D_L (Morse.covAt_mem hN _ _ _)

/-! New glue for this item. -/

/-- The project's `covDeriv` preserves smoothness along a smooth curve. -/
theorem presSmooth_covDeriv {c : ℝ → N} (hc : ContDiff ℝ ∞ (fun t => (c t : V))) :
    PresSmooth hN c (Morse.covDeriv hN c) := fun X hX _ =>
  ⟨(Morse.contDiff_tanProj_comp hN hc).clm_apply hX.deriv', fun t => Morse.covDeriv_mem hN c X t⟩

/-- `covDeriv`, transported to fields along `c` in `↥N`, satisfies B's axioms. -/
theorem isCovDerivAlong_toMath_covDeriv {c : ℝ → Sub hN} (hc : IsSmoothCurve (n := n) c) :
    IsCovDerivAlong (conn (hN := hN)) c (toMath c (Morse.covDeriv hN c)) :=
  toMath_isCovDerivAlong hc (Morse.isCovDerivAlong_covDeriv hN (isSmoothCurve_iff'.1 hc))
    (presSmooth_covDeriv (isSmoothCurve_iff'.1 hc))

/-- Every `D/dt` of B for the induced connection is `covDeriv`, read in `V`. -/
theorem D_eq_covDeriv {c : ℝ → Sub hN} (hc : IsSmoothCurve (n := n) c)
    {Dm : FieldAlong (n := n) c → FieldAlong (n := n) c}
    (hD : IsCovDerivAlong (conn (hN := hN)) c Dm) {U : FieldAlong (n := n) c}
    (hU : IsSmoothAlong (n := n) c U) (t : ℝ) :
    D hN (c t) (Dm U t) = Morse.covDeriv hN c (ambA c U) t := by
  have h := (toProj_isCovDerivAlong hc hD).1.eq_covDeriv hN (isSmoothCurve_iff'.1 hc)
    (isSmoothAlong_iff'.1 hU).2 (isFieldAlong_ambA c U) t
  simp only [toProj, liftA_ambA] at h
  exact h


/-- **Dictionary: parallel fields.** For a smooth curve in `↥N`, a field is parallel in B's sense
for the induced connection iff its ambient image is smooth and parallel in the project's sense. -/
theorem isParallel_iff {c : ℝ → Sub hN} (hc : IsSmoothCurve (n := n) c)
    {U : FieldAlong (n := n) c} :
    IsParallel (conn (hN := hN)) c U ↔
      ContDiff ℝ ∞ (ambA c U) ∧ Morse.IsParallel hN c (ambA c U) := by
  constructor
  · rintro ⟨hU, Dm, hDm, hDU⟩
    refine ⟨(isSmoothAlong_iff'.1 hU).2, ⟨isFieldAlong_ambA c U,
      (isSmoothAlong_iff'.1 hU).2.differentiable (by simp), fun t => ?_⟩⟩
    rw [← D_eq_covDeriv hc hDm hU t, congrFun hDU t]
    exact D_tzero (c t)
  · rintro ⟨hs, hp⟩
    refine ⟨isSmoothAlong_iff'.2 ⟨hc, hs⟩, _, isCovDerivAlong_toMath_covDeriv hc, ?_⟩
    funext t
    show L hN (c t) (Morse.covDeriv hN c (ambA c U) t) = 0
    rw [hp.covDeriv_eq_zero t]
    exact map_zero _

/-- Parallel fields of the project, shifted in time. -/
theorem isParallel_shift {c c' : ℝ → N} {a : ℝ} (hcc : ∀ s, c' s = c (s + a)) {X : ℝ → V}
    (hX : Morse.IsParallel hN c X) : Morse.IsParallel hN c' (fun s => X (s + a)) where
  mem s := by rw [hcc s]; exact hX.mem (s + a)
  differentiable := hX.differentiable.comp (differentiable_id.add_const a)
  covDeriv_eq_zero s := by
    show Morse.tanProj hN (c' s) (deriv (fun s => X (s + a)) s) = 0
    rw [deriv_comp_add_const, hcc s]
    exact hX.covDeriv_eq_zero (s + a)

/-- Lemma 8.2 for the induced connection in the project's vocabulary, among smooth parallel
fields (model `ℝⁿ`): through every tangent vector at `c(t₀)` there is exactly one smooth parallel
field. The part of A that `B_emb` covers. -/
def A82 : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (W : Type) [NormedAddCommGroup W] [NormedSpace ℝ W] (n : ℕ)
    (N : Set V) (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N) (c : ℝ → N),
    ContDiff ℝ ∞ (fun t => (c t : V)) → ∀ (t₀ : ℝ) (v : V), v ∈ Morse.tangentSubspace hN (c t₀) →
      ∃! X : ℝ → V, (Morse.IsParallel hN c X ∧ ContDiff ℝ ∞ X) ∧ X t₀ = v

end Emb

/-- B on embedded manifolds: `M = ↥N` with the induced connection (a special case of B, see
`B_to_B_emb`). -/
def B_emb : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (W : Type) [NormedAddCommGroup W] [NormedSpace ℝ W] (n : ℕ)
    (N : Set V) (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N)
    (c : ℝ → Bridge.Sub hN), IsSmoothCurve (n := n) c → ∀ V₀ : TangentSpace 𝓘(ℝ, Rn n) (c 0),
      ∃! U : FieldAlong (n := n) c, IsParallel (Bridge.conn (hN := hN)) c U ∧ U 0 = V₀

/-- `B_emb` is a special case of B (the induced connection is smooth, `Bridge.conn_contMDiff`). -/
theorem B_to_B_emb : B → B_emb := fun hB _ _ _ _ _ _ _ n _ hN =>
  hB n (Bridge.Sub hN) (Bridge.conn (hN := hN)) Bridge.conn_contMDiff

theorem A_to_A82 : A → Emb.A82 := by
  intro hA V _ _ _ W _ _ n N hN c hc t₀ v hv
  obtain ⟨X, ⟨hXp, hX0⟩, huniq⟩ := hA.1 hN hc hv
  exact ⟨X, ⟨⟨hXp, hA.2 hN hc hXp⟩, hX0⟩, fun Y ⟨⟨hYp, _⟩, hY0⟩ => huniq Y ⟨hYp, hY0⟩⟩

open Emb Bridge in
/-- **B on embedded manifolds is Lemma 8.2 among smooth parallel fields** (`A82`; B's initial
time `0` gives any initial time `t₀` by shifting the curve). -/
theorem B_emb_iff_A82 : B_emb ↔ A82 := by
  constructor
  · intro h V _ _ _ W _ _ n N hN c hc' t₀ v hv
    -- the shifted curve `c' s = c (s + t₀)`
    let c' : ℝ → Sub hN := fun s => c (s + t₀)
    have hc : IsSmoothCurve (n := n) c' :=
      isSmoothCurve_iff'.2 (hc'.comp (contDiff_id.add contDiff_const))
    have hv' : v ∈ Morse.tangentSubspace hN (c' 0) := by
      show v ∈ Morse.tangentSubspace hN (c (0 + t₀)); rw [zero_add]; exact hv
    obtain ⟨U, ⟨hUp, hU0⟩, huniq⟩ := h V W n N hN c' hc (L hN (c' 0) v)
    obtain ⟨hUs, hUp'⟩ := (isParallel_iff hc).1 hUp
    have hcc : ∀ s, c s = c' (s + -t₀) := fun s => by
      show c s = c (s + -t₀ + t₀); rw [neg_add_cancel_right]
    refine ⟨fun s => ambA c' U (s + -t₀),
      ⟨⟨isParallel_shift hcc hUp', hUs.comp (contDiff_id.add contDiff_const)⟩, ?_⟩, ?_⟩
    · show ambA c' U (t₀ + -t₀) = v
      rw [add_neg_cancel]
      show D hN (c' 0) (U 0) = v
      rw [hU0]; exact D_L hv'
    · rintro Y ⟨⟨hYp, hYs⟩, hY0⟩
      have hYp' : Morse.IsParallel hN c' (fun s => Y (s + t₀)) := isParallel_shift (fun _ => rfl) hYp
      have hYs' : ContDiff ℝ ∞ (fun s => Y (s + t₀)) := hYs.comp (contDiff_id.add contDiff_const)
      have hpar : IsParallel (conn (hN := hN)) c' (liftA c' (fun s => Y (s + t₀))) := by
        rw [isParallel_iff hc, ambA_liftA hYp'.mem]
        exact ⟨hYs', hYp'⟩
      have h0 : liftA c' (fun s => Y (s + t₀)) 0 = L hN (c' 0) v := by
        show L hN (c' 0) (Y (0 + t₀)) = _
        rw [zero_add, hY0]
      have hYU := congrArg (ambA c') (huniq _ ⟨hpar, h0⟩)
      rw [ambA_liftA hYp'.mem] at hYU
      funext s
      have := congrFun hYU (s + -t₀)
      simp only [neg_add_cancel_right] at this
      exact this
  · intro h V _ _ _ W _ _ n N hN c hc V₀
    obtain ⟨X, ⟨⟨hXp, hXs⟩, hX0⟩, huniq⟩ :=
      h V W n N hN c (isSmoothCurve_iff'.1 hc) 0 (D hN (c 0) V₀) (D_mem _ _)
    refine ⟨liftA c X, ⟨?_, ?_⟩, ?_⟩
    · rw [isParallel_iff hc, ambA_liftA hXp.mem]; exact ⟨hXs, hXp⟩
    · show L hN (c 0) (X 0) = V₀
      rw [hX0]; exact L_D _ _
    · rintro U ⟨hUp, hU0⟩
      obtain ⟨hUs, hUp'⟩ := (isParallel_iff hc).1 hUp
      rw [← liftA_ambA c U, huniq _ ⟨⟨hUp', hUs⟩, by show D hN (c 0) (U 0) = _; rw [hU0]⟩]

/-- **A implies B on embedded manifolds** (uses both of A's theorems). -/
theorem A_to_B_emb : A → B_emb := fun hA => B_emb_iff_A82.2 (A_to_A82 hA)

/-- **B implies Lemma 8.2 among smooth parallel fields in `N`** (`A82`, model `ℝⁿ`, any initial
time), by specializing B to `↥N`. -/
theorem B_to_A82 : B → Emb.A82 := fun hB => B_emb_iff_A82.1 (B_to_B_emb hB)

#rt_check RoundTrip.V6_8.A_to_B_emb [Morse.exists_unique_isParallel, Morse.IsParallel.contDiff]
#rt_check RoundTrip.V6_8.B_to_A82 [Morse.exists_unique_isParallel, Morse.IsParallel.contDiff]
#rt_overlap RoundTrip.V6_8.B_to_A82 [Morse.exists_unique_isParallel, Morse.IsParallel.contDiff]

end RoundTrip.V6_8
