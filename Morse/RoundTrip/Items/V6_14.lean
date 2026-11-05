import Morse
import RoundTrip.Check
import RoundTrip.Blind.V6_14
import RoundTrip.Bridge

namespace RoundTrip.V6_14

/-- The project's statement (universes instantiated at 0; `IsSymmCompat` and `koszul` are
definitions). Embedded half (slice submanifold `N ⊆ V`, operations `D` on maps `N → V`): the
induced connection `P(dY(X))` is symmetric and compatible (existence), the Koszul formula for any
symmetric compatible `D`, and uniqueness on smooth tangent fields. Abstract half (Mathlib
`CovariantDerivative` on a Riemannian bundle, any model): the Koszul formula for connections
symmetric and compatible in the Corollary 8.4 sense, and uniqueness on fields differentiable at the
point (also with Mathlib's torsion / `IsMetricCompatible`). No abstract existence. -/
def A : Prop :=
  type_of% @Morse.isSymmCompat_leviCivita.{0,0,0} ∧
    type_of% @Morse.IsSymmCompat.two_mul_inner.{0,0,0} ∧
    type_of% @Morse.IsSymmCompat.eq_leviCivita.{0,0,0} ∧
    type_of% @Morse.two_mul_inner_cov_eq_koszul.{0,0,0} ∧
    type_of% @Morse.cov_eq_of_isSymmetric_of_isCompatible.{0,0,0} ∧
    type_of% @Morse.cov_eq_of_torsion_eq_zero_of_isMetricCompatible.{0,0,0}

theorem A_holds : A :=
  ⟨@Morse.isSymmCompat_leviCivita, @Morse.IsSymmCompat.two_mul_inner,
    @Morse.IsSymmCompat.eq_leviCivita, @Morse.two_mul_inner_cov_eq_koszul,
    @Morse.cov_eq_of_isSymmetric_of_isCompatible,
    @Morse.cov_eq_of_torsion_eq_zero_of_isMetricCompatible⟩


open scoped ContDiff Manifold RealInnerProductSpace

/-! ## The embedded special case

B is specialized to `M = ↥N` (`RoundTrip.Bridge.Sub hN`) for a slice submanifold `N ⊆ V` with
model `ℝⁿ` and the induced metric (`B_emb`). Its existence half holds outright
(`Bridge.conn_isLC`, no A needed). Its uniqueness half quantifies over ALL Levi-Civita
connections `cov` on `↥N` in Milnor's sense (compatibility = parallel transport preserves inner
products). A's embedded uniqueness (`IsSymmCompat.eq_leviCivita`) applies to `cov` transported
to an operation on maps `N → V` (`Emb.opOf`) as soon as `cov` satisfies Corollary 8.4
(`Emb.Cor84`): symmetry transfers through `Bridge.D_mlieBracket`. So A gives B_emb *modulo*
`Lemma83Emb` — "every Levi-Civita connection on `↥N` satisfies Corollary 8.4", i.e. Lemma 8.3
for an arbitrary compatible connection on `↥N` (`A_to_B_emb_of_lemma83`). That lemma needs
parallel transport for an arbitrary connection (a non-skew linear ODE along the curve and
parallel orthonormal frames); it is not in the project or the Bridge (cf. `Items/V6_11.lean`,
where it is proved only for `Bridge.conn`). -/

namespace Emb

set_option linter.unusedSectionVars false

open RoundTrip.Bridge VectorField Bundle

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] {n : ℕ} {N : Set V}
  {hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N}

/-- `mfderiv` on `↥N` is the project's `dN`, through `D`. -/
theorem dN_D' {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (F : Sub hN → E) (q : Sub hN)
    (v : TangentSpace 𝓘(ℝ, Rn n) q) :
    Morse.dN hN F q (D hN q v) = mfderiv 𝓘(ℝ, Rn n) 𝓘(ℝ, E) F q v := by
  show mfderiv 𝓘(ℝ, Rn n) 𝓘(ℝ, E) F q (L hN q (D hN q v)) = _
  exact congrArg (mfderiv 𝓘(ℝ, Rn n) 𝓘(ℝ, E) F q) (L_D q v)

/-- Mathlib's bracket on `↥N`, read in `V`, is the project's ambient bracket. -/
theorem D_mlieBracket' {X Y : VF n (Sub hN)} (p : Sub hN)
    (hX : MDifferentiableAt 𝓘(ℝ, Rn n) (𝓘(ℝ, Rn n)).tangent
      (fun p => (⟨p, X p⟩ : TangentBundle 𝓘(ℝ, Rn n) (Sub hN))) p)
    (hY : MDifferentiableAt 𝓘(ℝ, Rn n) (𝓘(ℝ, Rn n)).tangent
      (fun p => (⟨p, Y p⟩ : TangentBundle 𝓘(ℝ, Rn n) (Sub hN))) p) :
    D hN p (mlieBracket 𝓘(ℝ, Rn n) X Y p) = Morse.bracket hN (amb X) (amb Y) p :=
  (D_mlieBracket p X Y hX hY).trans
    (congrArg₂ (· - ·) (dN_D (amb Y) p (X p)).symm (dN_D (amb X) p (Y p)).symm)

/-- The vector field `q ↦ L_q(Y q)` of a tangent map `Y : N → V`. -/
noncomputable def liftF (Y : N → V) : VF n (Sub hN) := fun q => L hN q (Y q)

theorem amb_liftF {Y : N → V} (hYT : Morse.IsTangentField hN Y) : amb (liftF (hN := hN) Y) = Y :=
  funext fun q => D_L (hYT q)

theorem liftF_amb (Y : VF n (Sub hN)) : liftF (hN := hN) (amb Y) = Y :=
  funext fun q => L_D q (Y q)

theorem isSmoothVF_liftF {Y : N → V}
    (hY : ContMDiff 𝓘(ℝ, Rn n) 𝓘(ℝ, V) ∞ (fun q : Sub hN => Y q))
    (hYT : Morse.IsTangentField hN Y) : IsSmoothVF (liftF (hN := hN) Y) := by
  unfold IsSmoothVF
  rw [contMDiff_section_iff, amb_liftF hYT]
  exact hY

/-- Corollary 8.4 for a connection on `↥N` (the conclusion of `Items/V6_11.lean`'s B). -/
def Cor84 (cov : Conn n (Sub hN)) : Prop :=
  ∀ Y Y' : VF n (Sub hN), IsSmoothVF Y → IsSmoothVF Y' →
    ∀ (p : Sub hN) (v : TangentSpace 𝓘(ℝ, Rn n) p),
      mfderiv 𝓘(ℝ, Rn n) 𝓘(ℝ, ℝ) (fun y => inner ℝ (Y y) (Y' y)) p v =
        inner ℝ (cov Y p v) (Y' p) + inner ℝ (Y p) (cov Y' p v)

/-- A connection on `↥N`, transported to an operation on maps `N → V`. -/
noncomputable def opOf (cov : Conn n (Sub hN)) : (N → V) → (N → V) → N → V :=
  fun X Y q => D hN q (cov (liftF Y) q (liftF (hN := hN) X q))

/-- A symmetric connection on `↥N` satisfying Corollary 8.4 gives an operation with the
properties of A's Lemma 8.6. -/
theorem isSymmCompat_opOf {cov : Conn n (Sub hN)} (hS : IsSymm cov) (hC : Cor84 cov) :
    Morse.IsSymmCompat hN (opOf cov) where
  mem X Y _ _ _ _ q := D_mem q _
  symm X Y hX hY hXT hYT q := by
    have hX' := isSmoothVF_liftF hX hXT
    have hY' := isSmoothVF_liftF hY hYT
    have h := hS (liftF X) (liftF Y) hX' hY' q
    have h2 := D_mlieBracket' (X := liftF (hN := hN) X) (Y := liftF Y) q
      ((hX' q).mdifferentiableAt (by simp)) ((hY' q).mdifferentiableAt (by simp))
    exact (D_tsub_aux q _ _).symm.trans ((congrArg (D hN q) h).trans (h2.trans
      (congrArg₂ (fun (A B : N → V) => Morse.bracket hN A B q) (amb_liftF hXT) (amb_liftF hYT))))
  compat X Y Y' hX hY hY' hXT hYT hYT' q := by
    have hX' := isSmoothVF_liftF hX hXT
    have hY1 := isSmoothVF_liftF hY hYT
    have hY2 := isSmoothVF_liftF hY' hYT'
    have h := hC (liftF Y) (liftF Y') hY1 hY2 q (liftF X q)
    change mfderiv 𝓘(ℝ, Rn n) 𝓘(ℝ, ℝ)
        (fun y => ⟪amb (liftF (hN := hN) Y) y, amb (liftF (hN := hN) Y') y⟫) q (liftF X q) =
      ⟪D hN q (cov (liftF Y) q (liftF X q)), amb (liftF (hN := hN) Y') q⟫ +
        ⟪amb (liftF (hN := hN) Y) q, D hN q (cov (liftF Y') q (liftF X q))⟫ at h
    have hF : (fun y : Sub hN => ⟪amb (liftF (hN := hN) Y) y, amb (liftF (hN := hN) Y') y⟫) =
        fun y : Sub hN => ⟪Y y, Y' y⟫ :=
      funext fun y => congrArg₂ _ (D_L (hYT y)) (D_L (hYT' y))
    have h2 : ∀ {Z : N → V}, Morse.IsTangentField hN Z → amb (liftF (hN := hN) Z) q = Z q :=
      fun hZ => D_L (hZ q)
    exact (congrArg (Morse.dN hN (fun x => ⟪Y x, Y' x⟫) q) (D_L (hXT q)).symm).trans
      ((dN_D' (fun y : Sub hN => ⟪Y y, Y' y⟫) q (liftF X q)).trans
        ((congrArg (fun F : Sub hN → ℝ => mfderiv 𝓘(ℝ, Rn n) 𝓘(ℝ, ℝ) F q (liftF X q)) hF.symm).trans
          (h.trans (congrArg₂ (· + ·) (congrArg₂ _ rfl (h2 hYT')) (congrArg₂ _ (h2 hYT) rfl)))))

end Emb

open Bundle in
/-- B on embedded manifolds: `M = ↥N` with the induced metric (a special case of B, see
`B_to_B_emb`). -/
def B_emb : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (W : Type) [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] (n : ℕ)
    (N : Set V) (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N),
    (∃ cov : Conn n (Bridge.Sub hN), IsLC cov) ∧
    ∀ cov cov' : Conn n (Bridge.Sub hN), IsLC cov → IsLC cov' →
      ∀ Y : VF n (Bridge.Sub hN), IsSmoothVF Y → cov Y = cov' Y

theorem B_to_B_emb : B → B_emb := fun hB _ _ _ _ _ _ _ _ n _ hN => hB n (Bridge.Sub hN)

/-- The existence half of `B_emb` holds outright: the induced connection is Levi-Civita. -/
theorem B_emb_exists (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] (W : Type) [NormedAddCommGroup W] [NormedSpace ℝ W] (n : ℕ)
    (N : Set V) (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N) :
    ∃ cov : Conn n (Bridge.Sub hN), IsLC cov := ⟨Bridge.conn, Bridge.conn_isLC⟩

/-- The missing piece: Lemma 8.3 / Corollary 8.4 for an arbitrary Levi-Civita connection (in
Milnor's sense) on `↥N`. -/
def Lemma83Emb : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (W : Type) [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] (n : ℕ)
    (N : Set V) (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N)
    (cov : Conn n (Bridge.Sub hN)), IsLC cov → Emb.Cor84 cov

open Emb Bridge in
/-- **A implies B on embedded manifolds, given `Lemma83Emb`**: every Levi-Civita connection on
`↥N` satisfying Corollary 8.4 agrees with `Bridge.conn` on smooth fields, by A's
`IsSymmCompat.eq_leviCivita`. -/
theorem A_to_B_emb_of_lemma83 : A → Lemma83Emb → B_emb := by
  intro hA h83 V _ _ _ W _ _ _ n N hN
  have key : ∀ cov : Conn n (Sub hN), IsLC cov → ∀ Y : VF n (Sub hN), IsSmoothVF Y →
      cov Y = conn Y := by
    intro cov hcov Y hY
    have hD := isSymmCompat_opOf hcov.2.1 (h83 V W n N hN cov hcov)
    funext x
    refine ContinuousLinearMap.ext fun v => D_injective x ?_
    have hX : IsSmoothVF (ext (hN := hN) (D hN x v)) := isSmoothVF_ext _
    have h := hA.2.2.1 hN hD (X := amb (ext (hN := hN) (D hN x v))) (Y := amb Y)
      (contMDiff_amb hX) (contMDiff_amb hY) (isTangentField_amb _) (isTangentField_amb _) x
    have e1 : opOf cov (amb (ext (hN := hN) (D hN x v))) (amb Y) x = D hN x (cov Y x v) := by
      show D hN x (cov (liftF (amb Y)) x (liftF (amb (ext (hN := hN) (D hN x v))) x)) = _
      rw [liftF_amb, liftF_amb, ext_apply_D]
    have e2 : Morse.leviCivita hN (amb (ext (hN := hN) (D hN x v))) (amb Y) x =
        D hN x (conn Y x v) := by
      rw [← D_conn, ext_apply_D]
    rw [e1, e2] at h
    exact h
  exact ⟨B_emb_exists V W n N hN, fun cov cov' h h' Y hY => (key cov h Y hY).trans (key cov' h' Y hY).symm⟩

#rt_check RoundTrip.V6_14.A_to_B_emb_of_lemma83 [Morse.isSymmCompat_leviCivita,
  Morse.IsSymmCompat.two_mul_inner, Morse.IsSymmCompat.eq_leviCivita,
  Morse.two_mul_inner_cov_eq_koszul, Morse.cov_eq_of_isSymmetric_of_isCompatible,
  Morse.cov_eq_of_torsion_eq_zero_of_isMetricCompatible]

end RoundTrip.V6_14
