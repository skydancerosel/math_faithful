import Morse
import RoundTrip.Check
import RoundTrip.Blind.V6_10
import RoundTrip.Bridge

open scoped RealInnerProductSpace

namespace RoundTrip.V6_10

/-- The project's statement (universes instantiated at 0): Lemma 8.3 for the induced metric on a
slice submanifold `N ⊆ V`, with `DX/dt = P_{c(t)} X'(t)`. -/
def A : Prop := type_of% @Morse.hasDerivAt_inner_covDeriv.{0,0,0}

theorem A_holds : A := @Morse.hasDerivAt_inner_covDeriv

/-- B ⇒ A holds only because A is provable outright (product rule in `V` plus
`⟨P X', Y⟩ = ⟨X', Y⟩` for tangent `Y`); B, about abstract manifolds with an arbitrary compatible
Mathlib connection, does not specialize to the project's embedded objects. -/
theorem B_to_A : B → A := by
  intro _ V _ _ _ Z _ _ W _ _ N hN c X Y hXT hYT t hX hY
  have h := hX.hasDerivAt.inner ℝ hY.hasDerivAt
  rw [Morse.covDeriv, Morse.covDeriv, Morse.inner_tanProj_of_mem hN _ (hYT t),
    ← Morse.inner_tanProj_left, Morse.tanProj_eq_self hN (hXT t), add_comm]
  exact h

#rt_check RoundTrip.V6_10.B_to_A [Morse.hasDerivAt_inner_covDeriv]
#rt_overlap RoundTrip.V6_10.B_to_A [Morse.hasDerivAt_inner_covDeriv]


/-! ## The embedded special case

B is specialized to `M = ↥N` (`RoundTrip.Bridge.Sub hN`) for a slice submanifold `N ⊆ V` with
model `ℝⁿ`, the induced metric and the induced connection `Bridge.conn` (`B_emb`). Fields along
a curve in `↥N` are read in `V` through `Bridge.ambA` and back through `liftA`; every `D/dt` of B
for `Bridge.conn` is the project's `covDeriv`, read in `V` (`Emb.D_eq_covDeriv`, from the
project's Lemma 8.1). Then `B_emb` is exactly A for smooth fields along smooth curves (`A83`). -/

open Set Bundle
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


/-- The induced connection is compatible with the induced metric in B's sense (from
`Bridge.conn_isCompat`, read with derivatives on all of `ℝ`). -/
theorem isCompatibleMetric_conn : IsCompatibleMetric (conn (hN := hN)) := by
  intro c hc P P' hP hP'
  have hc' : RoundTrip.BridgePrelude.IsSmoothCurve (n := n) c univ := contMDiffOn_univ.2 hc
  have toBP : ∀ {Q : FieldAlong (n := n) c}, IsParallel (conn (hN := hN)) c Q →
      RoundTrip.BridgePrelude.IsParallel (conn (hN := hN)) c univ Q := by
    rintro Q ⟨hQ, Dm, ⟨-, ha, hb, hi⟩, hDQ⟩
    refine ⟨contMDiffOn_univ.2 hQ, Dm, ⟨?_, ?_, ?_⟩, fun t _ => congrFun hDQ t⟩
    · intro U U' hU hU' t _
      exact congrFun (ha U U' (contMDiffOn_univ.1 hU) (contMDiffOn_univ.1 hU')) t
    · intro f hf U hU t _
      rw [derivWithin_univ]
      exact congrFun (hb f (contDiffOn_univ.1 hf) U (contMDiffOn_univ.1 hU)) t
    · intro Y hY t _
      rw [congrFun (hi Y hY) t]
      simp only [velocity, RoundTrip.BridgePrelude.vel, mfderivWithin_univ]
  exact ⟨inner ℝ (P 0) (P' 0), fun t =>
    conn_isCompat univ ⟨ordConnected_univ, uniqueDiffOn_univ⟩ c hc' P P' (toBP hP) (toBP hP') t
      (mem_univ t) 0 (mem_univ 0)⟩

/-- Lemma 8.3 for the induced metric in the project's vocabulary, for smooth fields along a smooth
curve (model `ℝⁿ`): the part of A that `B_emb` covers. -/
def A83 : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (W : Type) [NormedAddCommGroup W] [NormedSpace ℝ W] (n : ℕ)
    (N : Set V) (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N) (c : ℝ → N),
    ContDiff ℝ ∞ (fun t => (c t : V)) → ∀ X Y : ℝ → V, Morse.IsFieldAlong hN c X →
      Morse.IsFieldAlong hN c Y → ContDiff ℝ ∞ X → ContDiff ℝ ∞ Y → ∀ t,
        HasDerivAt (fun s => ⟪X s, Y s⟫)
          (⟪Morse.covDeriv hN c X t, Y t⟫ + ⟪X t, Morse.covDeriv hN c Y t⟫) t

end Emb

/-- B on embedded manifolds: `M = ↥N` with the induced metric and the induced connection (a
special case of B, see `B_to_B_emb`). -/
def B_emb : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (W : Type) [NormedAddCommGroup W] [NormedSpace ℝ W] (n : ℕ)
    (N : Set V) (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N)
    (c : ℝ → Bridge.Sub hN), IsSmoothCurve (n := n) c →
    ∀ Dm, IsCovDerivAlong (Bridge.conn (hN := hN)) c Dm →
      ∀ U U' : FieldAlong (n := n) c, IsSmoothAlong (n := n) c U → IsSmoothAlong (n := n) c U' →
        ∀ t : ℝ, HasDerivAt (fun s => inner ℝ (U s) (U' s))
          (inner ℝ (Dm U t) (U' t) + inner ℝ (U t) (Dm U' t)) t

/-- `B_emb` is a special case of B (the induced connection is smooth and compatible). -/
theorem B_to_B_emb : B → B_emb := fun hB _ _ _ _ _ _ _ n _ hN =>
  hB n (Bridge.Sub hN) (Bridge.conn (hN := hN)) Bridge.conn_contMDiff Emb.isCompatibleMetric_conn

theorem A_to_A83 : A → Emb.A83 := fun hA _ _ _ _ _ _ _ _ _ hN _ _ _ _ hXT hYT hX hY t =>
  hA hN hXT hYT (hX.differentiable (by simp) t) (hY.differentiable (by simp) t)

open Emb Bridge in
/-- **B on embedded manifolds is Lemma 8.3 for smooth fields along smooth curves** (`A83`). -/
theorem B_emb_iff_A83 : B_emb ↔ A83 := by
  constructor
  · intro h V _ _ _ W _ _ n N hN c hc' X Y hXT hYT hX hY t
    let c' : ℝ → Sub hN := c
    have hc : IsSmoothCurve (n := n) c' := isSmoothCurve_iff'.2 hc'
    have := h V W n N hN c' hc _ (isCovDerivAlong_toMath_covDeriv hc) _ _
      (isSmoothAlong_liftA hc hX hXT) (isSmoothAlong_liftA hc hY hYT) t
    have e : ∀ {Z : ℝ → V}, Morse.IsFieldAlong hN c Z → ∀ s, D hN (c' s) (liftA c' Z s) = Z s :=
      fun hZ s => D_L (hZ s)
    have h1 : ∀ {Z : ℝ → V}, Morse.IsFieldAlong hN c Z →
        D hN (c' t) (toMath c' (Morse.covDeriv hN c') (liftA c' Z) t) = Morse.covDeriv hN c Z t := by
      intro Z hZ
      show D hN (c t) (L hN (c t) (Morse.covDeriv hN c (ambA c' (liftA c' Z)) t)) = _
      rw [ambA_liftA hZ]
      exact D_L (Morse.covDeriv_mem hN c Z t)
    simp only [inner_eq, e hXT, e hYT, h1 hXT, h1 hYT] at this
    exact this
  · intro h V _ _ _ W _ _ n N hN c hc Dm hDm U U' hU hU' t
    have := h V W n N hN c (isSmoothCurve_iff'.1 hc) (ambA c U) (ambA c U')
      (isFieldAlong_ambA c U) (isFieldAlong_ambA c U') (isSmoothAlong_iff'.1 hU).2
      (isSmoothAlong_iff'.1 hU').2 t
    simp only [inner_eq, D_eq_covDeriv hc hDm hU t, D_eq_covDeriv hc hDm hU' t]
    exact this

/-- **A implies B on embedded manifolds** (uses A). -/
theorem A_to_B_emb : A → B_emb := fun hA => B_emb_iff_A83.2 (A_to_A83 hA)

/-- **B implies Lemma 8.3 for smooth fields along smooth curves in `N`** (`A83`, model `ℝⁿ`), by
specializing B to `↥N`. -/
theorem B_to_A83 : B → Emb.A83 := fun hB => B_emb_iff_A83.1 (B_to_B_emb hB)

#rt_check RoundTrip.V6_10.A_to_B_emb [Morse.hasDerivAt_inner_covDeriv]
#rt_check RoundTrip.V6_10.B_to_A83 [Morse.hasDerivAt_inner_covDeriv]
#rt_overlap RoundTrip.V6_10.B_to_A83 [Morse.hasDerivAt_inner_covDeriv]

end RoundTrip.V6_10
