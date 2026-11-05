import Morse
import RoundTrip.Check
import RoundTrip.Blind.V6_6
import RoundTrip.Bridge

open Set
open scoped ContDiff Manifold

namespace RoundTrip.V6_6

/-- The project's statement (universes instantiated at 0; `Morse.IsCovDerivAlong` is a
definition): Lemma 8.1 for the induced connection on a slice submanifold `N ⊆ V` —
`covDeriv` satisfies Milnor's axioms, and any operation satisfying them agrees with it on smooth
fields along a smooth curve. -/
def A : Prop :=
  type_of% @Morse.isCovDerivAlong_covDeriv.{0,0,0} ∧ type_of% @Morse.IsCovDerivAlong.eq_covDeriv.{0,0,0}

theorem A_holds : A := ⟨@Morse.isCovDerivAlong_covDeriv, @Morse.IsCovDerivAlong.eq_covDeriv⟩

/-! ## The embedded special case

B is specialized to `M = ↥N` (`RoundTrip.Bridge.Sub hN`) for a slice submanifold `N ⊆ V` with
model `ℝⁿ` and the induced connection `Bridge.conn` (`B_emb`). Fields along a curve in `↥N` are
read in `V` through `Bridge.ambA` (`U ↦ (t ↦ D_{c t}(U t))`) and back through `Bridge.L`. Two
transports of operations — Mathlib-level `D/dt` to project-level (`toProj`) and back (`toMath`) —
show that `B_emb` is exactly Lemma 8.1 in the project's vocabulary *with B's notion of
covariant derivative operator*, which carries smooth fields to smooth fields (`A81`); A implies
`A81` with `D = covDeriv`. A's uniqueness clause is slightly stronger than `A81`'s: it applies to
every operation satisfying the axioms, smoothness-preserving or not. -/

namespace Emb

set_option linter.unusedSectionVars false

open RoundTrip.Bridge

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] {n : ℕ} {N : Set V}
  {hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N}

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
noncomputable def liftA (c : ℝ → Sub hN) (X : ℝ → V) : FieldAlong (n := n) c := fun t => L hN (c t) (X t)

theorem ambA_liftA {c : ℝ → Sub hN} {X : ℝ → V} (hX : Morse.IsFieldAlong hN c X) :
    ambA c (liftA c X) = X := funext fun t => D_L (hX t)

theorem liftA_ambA (c : ℝ → Sub hN) (U : FieldAlong (n := n) c) : liftA c (ambA c U) = U :=
  funext fun t => L_D (c t) (U t)

theorem isSmoothAlong_liftA {c : ℝ → Sub hN} (hc : IsSmoothCurve (n := n) c) {X : ℝ → V}
    (hX : ContDiff ℝ ∞ X) (hXT : Morse.IsFieldAlong hN c X) : IsSmoothAlong (n := n) c (liftA c X) :=
  isSmoothAlong_iff'.2 ⟨hc, by rw [ambA_liftA hXT]; exact hX⟩

/-- The velocity of B, read in `V`, is the project's `velocity`. -/
theorem D_velocity (c : ℝ → Sub hN) (t : ℝ) :
    D hN (c t) (velocity (n := n) c t) = Morse.velocity (N := N) c t :=
  D_mfderiv_curve c t

/-- The vector field `q ↦ L_q(Y q)` of a tangent map `Y : N → V`. -/
noncomputable def liftF (Y : N → V) : (p : Sub hN) → TangentSpace 𝓘(ℝ, Rn n) p := fun q => L hN q (Y q)

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

/-- `toProj` of `toMath`: on smooth tangent fields, a smoothness-preserving project operation is
recovered. -/
theorem toProj_toMath {c : ℝ → Sub hN} {Dp : (ℝ → V) → ℝ → V} (hS : PresSmooth hN c Dp)
    {X : ℝ → V} (hX : ContDiff ℝ ∞ X) (hXT : Morse.IsFieldAlong hN c X) :
    toProj c (toMath c Dp) X = Dp X := by
  funext t
  simp only [toProj, toMath]
  rw [ambA_liftA hXT]
  exact D_L ((hS X hX hXT).2 t)

/-- Lemma 8.1 for the induced connection in the project's vocabulary, with B's notion of a
covariant derivative operator (axioms (a)–(c) and preservation of smoothness): such an operation
exists and is unique on smooth fields along `c`. This is the part of A that `B_emb` covers. -/
def A81 : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (W : Type) [NormedAddCommGroup W] [NormedSpace ℝ W] (n : ℕ)
    (N : Set V) (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N) (c : ℝ → N),
    ContDiff ℝ ∞ (fun t => (c t : V)) →
    ∃ D, Morse.IsCovDerivAlong hN c D ∧ PresSmooth hN c D ∧
      ∀ D', Morse.IsCovDerivAlong hN c D' → PresSmooth hN c D' →
        ∀ X, ContDiff ℝ ∞ X → Morse.IsFieldAlong hN c X → D' X = D X

end Emb

open Emb in
/-- B on embedded manifolds: `M = ↥N` with the induced connection (a special case of B, see
`B_to_B_emb`). -/
def B_emb : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (W : Type) [NormedAddCommGroup W] [NormedSpace ℝ W] (n : ℕ)
    (N : Set V) (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N)
    (c : ℝ → Bridge.Sub hN), IsSmoothCurve (n := n) c →
      ∃ D, IsCovDerivAlong (Bridge.conn (hN := hN)) c D ∧
        ∀ D', IsCovDerivAlong (Bridge.conn (hN := hN)) c D' →
          ∀ U, IsSmoothAlong (n := n) c U → D' U = D U

/-- `B_emb` is a special case of B (the induced connection is smooth, `Bridge.conn_contMDiff`). -/
theorem B_to_B_emb : B → B_emb := fun hB _ _ _ _ _ _ _ n _ hN =>
  hB n (Bridge.Sub hN) (Bridge.conn (hN := hN)) Bridge.conn_contMDiff

open Emb Bridge in
/-- **B on embedded manifolds is Lemma 8.1 in the project's vocabulary** (with B's notion of
`D/dt`), through the transports `toProj` / `toMath`. -/
theorem B_emb_iff_A81 : B_emb ↔ A81 := by
  constructor
  · intro h V _ _ _ W _ _ n N hN c hc'
    let c' : ℝ → Sub hN := c
    have hc : IsSmoothCurve (n := n) c' := isSmoothCurve_iff'.2 hc'
    obtain ⟨Dm, hDm, huniq⟩ := h V W n N hN c' hc
    obtain ⟨hP, hPS⟩ := toProj_isCovDerivAlong hc hDm
    refine ⟨toProj c' Dm, hP, hPS, fun D' hD' hS' X hX hXT => ?_⟩
    rw [← toProj_toMath hS' hX hXT]
    funext t
    simp only [toProj]
    rw [huniq _ (toMath_isCovDerivAlong hc hD' hS') _ (isSmoothAlong_liftA hc hX hXT)]
  · intro h V _ _ _ W _ _ n N hN c hc
    obtain ⟨Dp, hDp, hS, huniq⟩ := h V W n N hN c (isSmoothCurve_iff'.1 hc)
    refine ⟨toMath c Dp, toMath_isCovDerivAlong hc hDp hS, fun Dm hDm U hU => ?_⟩
    obtain ⟨hP, hPS⟩ := toProj_isCovDerivAlong hc hDm
    have hUc := (isSmoothAlong_iff'.1 hU).2
    have := huniq _ hP hPS _ hUc (isFieldAlong_ambA c U)
    funext t
    apply D_injective (c t)
    have h1 := congrFun this t
    simp only [toProj, liftA_ambA] at h1
    rw [h1]
    exact (D_L ((hS _ hUc (isFieldAlong_ambA c U)).2 t)).symm

open Emb in
/-- A implies `A81`: `D = covDeriv` (uses both of A's theorems). -/
theorem A_to_A81 : A → A81 := by
  intro hA V _ _ _ W _ _ n N hN c hc
  refine ⟨Morse.covDeriv hN c, hA.1 hN hc, fun X _ _ => ⟨?_, fun t => Morse.covDeriv_mem hN c X t⟩,
    fun D' hD' _ X hX hXT => funext fun t => hA.2 hN hD' hc hX hXT t⟩
  exact (Morse.contDiff_tanProj_comp hN hc).clm_apply (by assumption : ContDiff ℝ ∞ X).deriv'

/-- **A implies B on embedded manifolds.** -/
theorem A_to_B_emb : A → B_emb := fun hA => B_emb_iff_A81.2 (A_to_A81 hA)

/-- **B implies Lemma 8.1 in the project's vocabulary** (`A81`, for model `ℝⁿ`), by specializing
B to `↥N`. -/
theorem B_to_A81 : B → Emb.A81 := fun hB => B_emb_iff_A81.1 (B_to_B_emb hB)

#rt_check RoundTrip.V6_6.A_to_B_emb [Morse.isCovDerivAlong_covDeriv, Morse.IsCovDerivAlong.eq_covDeriv]
#rt_check RoundTrip.V6_6.B_to_A81 [Morse.isCovDerivAlong_covDeriv, Morse.IsCovDerivAlong.eq_covDeriv]
#rt_overlap RoundTrip.V6_6.B_to_A81 [Morse.isCovDerivAlong_covDeriv, Morse.IsCovDerivAlong.eq_covDeriv]

end RoundTrip.V6_6
