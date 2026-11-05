import Morse
import RoundTrip.Check
import RoundTrip.Blind.V6_11
import RoundTrip.Bridge

open Bundle Manifold VectorField FiberBundle
open scoped RealInnerProductSpace

namespace RoundTrip.V6_11

/-- The project's statement (universes instantiated at 0; `Morse.IsCompatible` is a definition —
Milnor's Corollary 8.4 formula itself, for fields differentiable at the point): Corollary 8.4 for
the induced connection `P(dY(v))` of a slice submanifold `N ⊆ V`, and, for a Mathlib connection on
an abstract Riemannian manifold, "the Corollary 8.4 formula holds" ↔ Mathlib's
`IsMetricCompatible`. -/
def A : Prop :=
  type_of% @Morse.dN_inner_eq_covAt.{0,0,0} ∧
    type_of% @Morse.isCompatible_iff_isMetricCompatible.{0,0,0}

theorem A_holds : A := ⟨@Morse.dN_inner_eq_covAt, @Morse.isCompatible_iff_isMetricCompatible⟩

/-- B ⇒ A holds only because A is provable outright: the embedded half is the product rule plus
`⟨P u, w⟩ = ⟨u, w⟩` for tangent `w`; the abstract half is Mathlib's
`isMetricCompatible_iff` (A's `IsCompatible` is that formula, taken as the definition). -/
theorem B_to_A : B → A := by
  intro _
  refine ⟨?_, ?_⟩
  · intro V _ _ _ Z _ _ W _ _ N hN Y Y' q hY hY' hYT hYT' v hv
    rw [Morse.dN_inner hN hY hY' hv, Morse.covAt, Morse.covAt, Morse.inner_tanProj_of_mem hN _ hYT',
      ← Morse.inner_tanProj_left, Morse.tanProj_eq_self hN hYT]
  · intro E _ _ H _ I M _ _ _ _ cov _ _
    rw [CovariantDerivative.isMetricCompatible_iff]
    exact ⟨fun h x X σ τ hX hσ hτ => h X σ τ x hX hσ hτ, fun h X Y Y' x hX hY hY' => h hX hY hY'⟩

#rt_check RoundTrip.V6_11.B_to_A [Morse.dN_inner_eq_covAt, Morse.isCompatible_iff_isMetricCompatible]
#rt_overlap RoundTrip.V6_11.B_to_A [Morse.dN_inner_eq_covAt,
  Morse.isCompatible_iff_isMetricCompatible]


/-! ## The embedded special case

B is specialized to `M = ↥N` (`RoundTrip.Bridge.Sub hN`) for a slice submanifold `N ⊆ V` with
model `ℝⁿ`, the induced metric and the induced connection `Bridge.conn` (`B_emb`; a genuine
instance of B since `conn` is smooth and compatible, `Bridge.conn_isGlobalConn`,
`Bridge.conn_isCompat`). Through the dictionary — `mfderiv F p v = dN F p (D_p v)` (`Emb.dN_D'`),
`D_p (conn Y p v) = covAt p (D_p v) (amb Y)` (`Bridge.D_conn_apply`), the Riemannian inner
product is the ambient one (`Bridge.inner_eq`) — `B_emb` is exactly A's first clause
(Corollary 8.4 for the induced connection) for model `ℝⁿ` and smooth tangent fields (`A84`). -/

open scoped ContDiff Manifold

namespace Emb

set_option linter.unusedSectionVars false

open RoundTrip.Bridge

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] {n : ℕ} {N : Set V}
  {hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N}

/-- `mfderiv` on `↥N` is the project's `dN`, through `D`. -/
theorem dN_D' {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (F : Sub hN → E) (q : Sub hN)
    (v : TangentSpace 𝓘(ℝ, Rn n) q) :
    Morse.dN hN F q (D hN q v) = mfderiv 𝓘(ℝ, Rn n) 𝓘(ℝ, E) F q v := by
  show mfderiv 𝓘(ℝ, Rn n) 𝓘(ℝ, E) F q (L hN q (D hN q v)) = _
  exact congrArg (mfderiv 𝓘(ℝ, Rn n) 𝓘(ℝ, E) F q) (L_D q v)

/-- The vector field `q ↦ L_q(Y q)` of a tangent map `Y : N → V`. -/
noncomputable def liftF (Y : N → V) : VF n (Sub hN) := fun q => L hN q (Y q)

theorem amb_liftF {Y : N → V} (hYT : Morse.IsTangentField hN Y) : amb (liftF (hN := hN) Y) = Y :=
  funext fun q => D_L (hYT q)

theorem isSmoothVF_liftF {Y : N → V} (hY : ContMDiff 𝓘(ℝ, Rn n) 𝓘(ℝ, V) ∞ (fun q : Sub hN => Y q))
    (hYT : Morse.IsTangentField hN Y) : IsSmoothVF (liftF (hN := hN) Y) := by
  unfold IsSmoothVF
  rw [contMDiff_section_iff, amb_liftF hYT]
  exact hY

/-- Corollary 8.4 for the induced connection in the project's vocabulary, for smooth tangent
fields (model `ℝⁿ`): the part of A that `B_emb` covers. -/
def A84 : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (W : Type) [NormedAddCommGroup W] [NormedSpace ℝ W] (n : ℕ)
    (N : Set V) (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N) (Y Y' : N → V),
    (letI := hN.chartedSpace; ContMDiff 𝓘(ℝ, Rn n) 𝓘(ℝ, V) ∞ Y) →
    (letI := hN.chartedSpace; ContMDiff 𝓘(ℝ, Rn n) 𝓘(ℝ, V) ∞ Y') →
    Morse.IsTangentField hN Y → Morse.IsTangentField hN Y' → ∀ (q : N) (v : V),
      v ∈ Morse.tangentSubspace hN q →
      Morse.dN hN (fun x => ⟪Y x, Y' x⟫) q v =
        ⟪Morse.covAt hN q v Y, Y' q⟫ + ⟪Y q, Morse.covAt hN q v Y'⟫

end Emb

open Bundle in
/-- B on embedded manifolds: `M = ↥N` with the induced metric and the induced connection (a
special case of B, see `B_to_B_emb`). -/
def B_emb : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (W : Type) [NormedAddCommGroup W] [NormedSpace ℝ W] (n : ℕ)
    (N : Set V) (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N)
    (Y Y' : VF n (Bridge.Sub hN)), IsSmoothVF Y → IsSmoothVF Y' →
    ∀ (p : Bridge.Sub hN) (v : TangentSpace 𝓘(ℝ, Rn n) p),
      mfderiv 𝓘(ℝ, Rn n) 𝓘(ℝ, ℝ) (fun y => inner ℝ (Y y) (Y' y)) p v
        = inner ℝ (Bridge.conn Y p v) (Y' p) + inner ℝ (Y p) (Bridge.conn Y' p v)

/-- `B_emb` is a special case of B (the induced connection is smooth and compatible). -/
theorem B_to_B_emb : B → B_emb := fun hB _ _ _ _ _ _ _ n _ hN =>
  hB n (Bridge.Sub hN) (Bridge.conn (hN := hN)) Bridge.conn_isGlobalConn Bridge.conn_isCompat

theorem A_to_A84 : A → Emb.A84 := fun hA _ _ _ _ _ _ _ _ _ hN _ _ hY hY' hYT hYT' q _ hv =>
  letI := hN.chartedSpace
  hA.1 hN (hY.mdifferentiableAt (by simp)) (hY'.mdifferentiableAt (by simp)) (hYT q) (hYT' q) hv

open Emb Bridge Bundle in
/-- **B on embedded manifolds is Corollary 8.4 for the induced connection, smooth fields**
(`A84`). -/
theorem B_emb_iff_A84 : B_emb ↔ A84 := by
  constructor
  · intro h V _ _ _ W _ _ n N hN Y Y' hY hY' hYT hYT' q v hv
    have := h V W n N hN (liftF Y) (liftF Y') (isSmoothVF_liftF hY hYT)
      (isSmoothVF_liftF hY' hYT') q (L hN q v)
    have hF : (fun y : Sub hN => ⟪amb (liftF (hN := hN) Y) y, amb (liftF (hN := hN) Y') y⟫) =
        fun y : Sub hN => ⟪Y y, Y' y⟫ :=
      funext fun y => congrArg₂ _ (D_L (hYT y)) (D_L (hYT' y))
    have h1 : ∀ {Z : N → V}, Morse.IsTangentField hN Z →
        D hN q (conn (liftF (hN := hN) Z) q (L hN q v)) = Morse.covAt hN q v Z := fun {Z} hZ =>
      (D_conn_apply _ q _).trans
        (congrArg₂ (fun w (G : Sub hN → V) => Morse.covAt hN q w G) (D_L hv) (amb_liftF hZ))
    have h2 : ∀ {Z : N → V}, Morse.IsTangentField hN Z → amb (liftF (hN := hN) Z) q = Z q :=
      fun hZ => D_L (hZ q)
    change mfderiv 𝓘(ℝ, Rn n) 𝓘(ℝ, ℝ)
        (fun y => ⟪amb (liftF (hN := hN) Y) y, amb (liftF (hN := hN) Y') y⟫) q (L hN q v) =
      ⟪D hN q (conn (liftF Y) q (L hN q v)), amb (liftF (hN := hN) Y') q⟫ +
        ⟪amb (liftF (hN := hN) Y) q, D hN q (conn (liftF Y') q (L hN q v))⟫ at this
    exact (congrArg (Morse.dN hN (fun x => ⟪Y x, Y' x⟫) q) (D_L hv).symm).trans
      ((dN_D' (fun y : Sub hN => ⟪Y y, Y' y⟫) q (L hN q v)).trans
        ((congrArg (fun F : Sub hN → ℝ => mfderiv 𝓘(ℝ, Rn n) 𝓘(ℝ, ℝ) F q (L hN q v)) hF.symm).trans
          (this.trans
            (congrArg₂ (· + ·) (congrArg₂ _ (h1 hYT) (h2 hYT')) (congrArg₂ _ (h2 hYT) (h1 hYT'))))))
  · intro h V _ _ _ W _ _ n N hN Y Y' hY hY' p v
    have := h V W n N hN (amb Y) (amb Y') (contMDiff_amb hY) (contMDiff_amb hY')
      (isTangentField_amb Y) (isTangentField_amb Y') p (D hN p v) (D_mem p v)
    change _ = ⟪D hN p (conn Y p v), amb Y' p⟫ + ⟪amb Y p, D hN p (conn Y' p v)⟫
    simp only [D_conn_apply, ← dN_D']
    exact this

/-- **A implies B on embedded manifolds** (uses A's first clause). -/
theorem A_to_B_emb : A → B_emb := fun hA => B_emb_iff_A84.2 (A_to_A84 hA)

/-- **B implies Corollary 8.4 for the induced connection on smooth tangent fields of `N`**
(`A84`, model `ℝⁿ`), by specializing B to `↥N`. -/
theorem B_to_A84 : B → Emb.A84 := fun hB => B_emb_iff_A84.1 (B_to_B_emb hB)

#rt_check RoundTrip.V6_11.A_to_B_emb [Morse.dN_inner_eq_covAt, Morse.isCompatible_iff_isMetricCompatible]
#rt_check RoundTrip.V6_11.B_to_A84 [Morse.dN_inner_eq_covAt, Morse.isCompatible_iff_isMetricCompatible]
#rt_overlap RoundTrip.V6_11.B_to_A84 [Morse.dN_inner_eq_covAt,
  Morse.isCompatible_iff_isMetricCompatible]

end RoundTrip.V6_11
