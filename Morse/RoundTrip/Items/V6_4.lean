import Morse
import RoundTrip.Check
import RoundTrip.Blind.V6_4
import RoundTrip.Bridge

open ContinuousLinearMap
open scoped ContDiff Manifold

namespace RoundTrip.V6_4

/-- The project's statement (universes instantiated at 0; `covAt`, `leviCivita` are definitions):
Milnor's rules (1)–(4) for the induced connection `(X ⊢ Y)_q = P_q(dY_q(X_q))` on a slice
submanifold `N ⊆ V`. -/
def A : Prop :=
  type_of% @Morse.contMDiff_leviCivita.{0,0,0} ∧ type_of% @Morse.leviCivita_add_left.{0,0,0} ∧
    type_of% @Morse.leviCivita_add_right.{0,0,0} ∧ type_of% @Morse.leviCivita_smul_left.{0,0,0} ∧
    type_of% @Morse.leviCivita_smul_right.{0,0,0}

theorem A_holds : A :=
  ⟨@Morse.contMDiff_leviCivita, @Morse.leviCivita_add_left, @Morse.leviCivita_add_right,
    @Morse.leviCivita_smul_left, @Morse.leviCivita_smul_right⟩

/-- B ⇒ A holds only because A is provable outright (the project's short proofs re-done from
`contMDiff_tanProj`, `contMDiff_dN_apply`, `dN_add`, `dN_smul`); B, about Mathlib connections
on abstract manifolds, does not mention the induced connection of an embedded `N`. -/
theorem B_to_A : B → A := by
  intro _
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro V _ _ _ Z _ _ W _ _ N hN _ X Y hX hY hXT
    let _ := hN.chartedSpace
    exact (Morse.contMDiff_tanProj hN).clm_apply (Morse.contMDiff_dN_apply hN hX hY hXT)
  · intro V _ _ _ Z _ _ W _ _ N hN X X' Y q
    simp only [Morse.leviCivita, Morse.covAt, map_add]
  · intro V _ _ _ Z _ _ W _ _ N hN X Y Y' q hY hY'
    simp only [Morse.leviCivita, Morse.covAt, Morse.dN_add hN hY hY', add_apply, map_add]
  · intro V _ _ _ Z _ _ W _ _ N hN f X Y q
    simp only [Morse.leviCivita, Morse.covAt, map_smul]
  · intro V _ _ _ Z _ _ W _ _ N hN f X Y q hf hY hX hYT
    simp only [Morse.leviCivita, Morse.covAt]
    rw [Morse.dN_smul hN hf hY hX, map_add, map_smul, map_smul, Morse.tanProj_eq_self hN hYT]

#rt_check RoundTrip.V6_4.B_to_A [Morse.contMDiff_leviCivita, Morse.leviCivita_add_left, Morse.leviCivita_add_right, Morse.leviCivita_smul_left, Morse.leviCivita_smul_right]
#rt_overlap RoundTrip.V6_4.B_to_A [Morse.contMDiff_leviCivita, Morse.leviCivita_add_left, Morse.leviCivita_add_right, Morse.leviCivita_smul_left, Morse.leviCivita_smul_right]

/-! ## The embedded special case

B is specialized to `M = ↥N` (`RoundTrip.Bridge.Sub hN`) for a slice submanifold `N ⊆ V` with
model `ℝⁿ` and the induced connection `Bridge.conn` (`B_emb`): (a) Milnor's rules (1)–(4) for
`X ⊢ Y = Bridge.conn Y · (X ·)`, and (b) Christoffel symbols of `Bridge.conn` in every chart of
the maximal atlas of `↥N`. Through the Bridge (`Bridge.amb_conn`: the induced connection read in
`V` is `Morse.leviCivita`; `Bridge.contMDiff_section_iff`: smooth sections are smooth tangent maps
`N → V`), part (a) is exactly A restricted to smooth tangent fields (`TanRules`), and follows from
A. Part (b) has no counterpart in A (the project has no Christoffel symbols) and is not proved. -/

namespace Emb

set_option linter.unusedSectionVars false

open RoundTrip.Bridge
open RoundTrip.BridgePrelude (VF)

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] {n : ℕ} {N : Set V}
  {hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N}

/-- A smooth tangent field `N → V` (the project's notion of smooth vector field). -/
def SF (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N) (X : N → V) : Prop :=
  (letI := hN.chartedSpace; ContMDiff 𝓘(ℝ, Rn n) 𝓘(ℝ, V) ∞ X) ∧ Morse.IsTangentField hN X

/-- A smooth function on `N`. -/
def SFn (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N) (f : N → ℝ) : Prop :=
  letI := hN.chartedSpace; ContMDiff 𝓘(ℝ, Rn n) 𝓘(ℝ) ∞ f

/-- Milnor's rules (1)–(4), in B's form, for the project's `leviCivita` on smooth tangent fields
(the part of A that `B_emb` (a) covers). -/
def TanRules (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N) : Prop :=
  (∀ X Y, SF hN X → SF hN Y → SF hN (Morse.leviCivita hN X Y)) ∧
  (∀ X X' Y, SF hN X → SF hN X' → SF hN Y → Morse.leviCivita hN (fun q => X q + X' q) Y =
      fun q => Morse.leviCivita hN X Y q + Morse.leviCivita hN X' Y q) ∧
  (∀ (a : ℝ) X Y, SF hN X → SF hN Y →
      Morse.leviCivita hN (fun q => a • X q) Y = fun q => a • Morse.leviCivita hN X Y q) ∧
  (∀ X Y Y', SF hN X → SF hN Y → SF hN Y' → Morse.leviCivita hN X (fun q => Y q + Y' q) =
      fun q => Morse.leviCivita hN X Y q + Morse.leviCivita hN X Y' q) ∧
  (∀ (a : ℝ) X Y, SF hN X → SF hN Y →
      Morse.leviCivita hN X (fun q => a • Y q) = fun q => a • Morse.leviCivita hN X Y q) ∧
  (∀ f X Y, SFn hN f → SF hN X → SF hN Y →
      Morse.leviCivita hN (fun q => f q • X q) Y = fun q => f q • Morse.leviCivita hN X Y q) ∧
  (∀ f X Y, SFn hN f → SF hN X → SF hN Y → Morse.leviCivita hN X (fun q => f q • Y q) =
      fun q => Morse.dN hN f q (X q) • Y q + f q • Morse.leviCivita hN X Y q)

theorem sf_amb {X : VF n (Sub hN)} (hX : IsSmoothVF X) : SF hN (amb X) :=
  ⟨contMDiff_section_iff.1 hX, isTangentField_amb X⟩

theorem isSmoothVF_of_sf {X : VF n (Sub hN)} (hX : SF hN (amb X)) : IsSmoothVF X :=
  contMDiff_section_iff.2 hX.1

/-- Every smooth tangent field `N → V` is `amb` of a smooth section. -/
theorem exists_amb {X : N → V} (hX : SF hN X) : ∃ X₀ : VF n (Sub hN), IsSmoothVF X₀ ∧ amb X₀ = X := by
  have e : amb (fun q : Sub hN => L hN q (X q)) = X := funext fun q => D_L (hX.2 q)
  refine ⟨fun q => L hN q (X q), ?_, e⟩
  refine contMDiff_section_iff.2 ?_
  rw [e]
  exact hX.1

theorem amb_injective {X Y : VF n (Sub hN)} (h : amb X = amb Y) : X = Y :=
  funext fun q => D_injective q (congrFun h q)

theorem amb_nab (X Y : VF n (Sub hN)) :
    amb (nab (conn (hN := hN)) X Y) = Morse.leviCivita hN (amb X) (amb Y) := amb_conn X Y

theorem amb_add (X Y : VF n (Sub hN)) :
    amb (fun p => X p + Y p) = fun q => amb X q + amb Y q := funext fun q => D_tadd q _ _

theorem amb_smul (a : ℝ) (X : VF n (Sub hN)) :
    amb (fun p => a • X p) = fun q => a • amb X q := funext fun q => D_tsmul q _ _

theorem amb_fsmul (f : Sub hN → ℝ) (X : VF n (Sub hN)) :
    amb (fun p => f p • X p) = fun q => f q • amb X q := funext fun q => D_tsmul q _ _

theorem dirDeriv_eq (X : VF n (Sub hN)) (f : Sub hN → ℝ) (p : Sub hN) :
    dirDeriv X f p = Morse.dN hN f p (amb X p) :=
  (congrArg (mfderiv 𝓘(ℝ, Rn n) 𝓘(ℝ, ℝ) f p) (L_D p (X p))).symm

theorem sf_add {X Y : N → V} (hX : SF hN X) (hY : SF hN Y) : SF hN (fun q => X q + Y q) := by
  let _ := hN.chartedSpace
  exact ⟨hX.1.add hY.1, fun q => Submodule.add_mem _ (hX.2 q) (hY.2 q)⟩

theorem sf_fsmul {f : N → ℝ} {X : N → V} (hf : SFn hN f) (hX : SF hN X) :
    SF hN (fun q => f q • X q) := by
  let _ := hN.chartedSpace
  exact ⟨hf.smul hX.1, fun q => Submodule.smul_mem _ _ (hX.2 q)⟩

/-- **Rules (1)–(4) for the induced connection ⇔ the same rules for `leviCivita` on smooth
tangent fields.** -/
theorem isMilnorRules_iff : IsMilnorRules (nab (conn (hN := hN))) ↔ TanRules hN := by
  constructor
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro X Y hX hY
      obtain ⟨X₀, hX₀, rfl⟩ := exists_amb hX
      obtain ⟨Y₀, hY₀, rfl⟩ := exists_amb hY
      rw [← amb_nab]
      exact sf_amb (h1 X₀ Y₀ hX₀ hY₀)
    · intro X X' Y hX hX' hY
      obtain ⟨X₀, hX₀, rfl⟩ := exists_amb hX
      obtain ⟨X₁, hX₁, rfl⟩ := exists_amb hX'
      obtain ⟨Y₀, hY₀, rfl⟩ := exists_amb hY
      have := congrArg amb (h2 X₀ X₁ Y₀ hX₀ hX₁ hY₀)
      rw [amb_nab, amb_add, amb_add, amb_nab, amb_nab] at this
      exact this
    · intro a X Y hX hY
      obtain ⟨X₀, hX₀, rfl⟩ := exists_amb hX
      obtain ⟨Y₀, hY₀, rfl⟩ := exists_amb hY
      have := congrArg amb (h3 a X₀ Y₀ hX₀ hY₀)
      rw [amb_nab, amb_smul, amb_smul, amb_nab] at this
      exact this
    · intro X Y Y' hX hY hY'
      obtain ⟨X₀, hX₀, rfl⟩ := exists_amb hX
      obtain ⟨Y₀, hY₀, rfl⟩ := exists_amb hY
      obtain ⟨Y₁, hY₁, rfl⟩ := exists_amb hY'
      have := congrArg amb (h4 X₀ Y₀ Y₁ hX₀ hY₀ hY₁)
      rw [amb_nab, amb_add, amb_add, amb_nab, amb_nab] at this
      exact this
    · intro a X Y hX hY
      obtain ⟨X₀, hX₀, rfl⟩ := exists_amb hX
      obtain ⟨Y₀, hY₀, rfl⟩ := exists_amb hY
      have := congrArg amb (h5 a X₀ Y₀ hX₀ hY₀)
      rw [amb_nab, amb_smul, amb_smul, amb_nab] at this
      exact this
    · intro (f : Sub hN → ℝ) X Y hf hX hY
      obtain ⟨X₀, hX₀, rfl⟩ := exists_amb hX
      obtain ⟨Y₀, hY₀, rfl⟩ := exists_amb hY
      have := congrArg amb (h6 f X₀ Y₀ hf hX₀ hY₀)
      rw [amb_nab, amb_fsmul, amb_fsmul, amb_nab] at this
      exact this
    · intro (f : Sub hN → ℝ) X Y hf hX hY
      obtain ⟨X₀, hX₀, rfl⟩ := exists_amb hX
      obtain ⟨Y₀, hY₀, rfl⟩ := exists_amb hY
      have := congrArg amb (h7 f X₀ Y₀ hf hX₀ hY₀)
      rw [amb_nab, amb_fsmul, amb_add, amb_fsmul, amb_fsmul, amb_nab] at this
      refine this.trans ?_
      funext q
      simp only [dirDeriv_eq]
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro X Y hX hY
      refine isSmoothVF_of_sf ?_
      rw [amb_nab]
      exact h1 _ _ (sf_amb hX) (sf_amb hY)
    · intro X X' Y hX hX' hY
      refine amb_injective ?_
      rw [amb_nab, amb_add, amb_add, amb_nab, amb_nab]
      exact h2 _ _ _ (sf_amb hX) (sf_amb hX') (sf_amb hY)
    · intro a X Y hX hY
      refine amb_injective ?_
      rw [amb_nab, amb_smul, amb_smul, amb_nab]
      exact h3 a _ _ (sf_amb hX) (sf_amb hY)
    · intro X Y Y' hX hY hY'
      refine amb_injective ?_
      rw [amb_nab, amb_add, amb_add, amb_nab, amb_nab]
      exact h4 _ _ _ (sf_amb hX) (sf_amb hY) (sf_amb hY')
    · intro a X Y hX hY
      refine amb_injective ?_
      rw [amb_nab, amb_smul, amb_smul, amb_nab]
      exact h5 a _ _ (sf_amb hX) (sf_amb hY)
    · intro f X Y hf hX hY
      refine amb_injective ?_
      rw [amb_nab, amb_fsmul, amb_fsmul, amb_nab]
      exact h6 f _ _ hf (sf_amb hX) (sf_amb hY)
    · intro f X Y hf hX hY
      refine amb_injective ?_
      rw [amb_nab, amb_fsmul, amb_add, amb_fsmul, amb_fsmul, amb_nab]
      refine (h7 f _ _ hf (sf_amb hX) (sf_amb hY)).trans ?_
      funext q
      beta_reduce
      rw [dirDeriv_eq X f q]

end Emb

/-- B on embedded manifolds: `M = ↥N` with the induced connection (a special case of B, see
`B_to_B_emb`). -/
def B_emb : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (W : Type) [NormedAddCommGroup W] [NormedSpace ℝ W] (n : ℕ)
    (N : Set V) (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N),
    IsMilnorRules (nab (Bridge.conn (hN := hN))) ∧
    ∀ e ∈ IsManifold.maximalAtlas 𝓘(ℝ, Rn n) ∞ (Bridge.Sub hN),
      ∃ Γ : Rn n → Fin n → Fin n → Fin n → ℝ,
        (∀ k i j, ContDiffOn ℝ ∞ (fun u => Γ u k i j) e.target) ∧
        ∀ (X Y : (p : Bridge.Sub hN) → TangentSpace 𝓘(ℝ, Rn n) p), IsSmoothVF X → IsSmoothVF Y →
          ∀ p ∈ e.source, ∀ k : Fin n,
            comp e p (nab (Bridge.conn (hN := hN)) X Y p) k =
              ∑ i, comp e p (X p) i *
                fderiv ℝ (fun u => comp e (e.symm u) (Y (e.symm u)) k) (e p) (EuclideanSpace.single i 1) +
              ∑ i, ∑ j, Γ (e p) k i j * comp e p (X p) i * comp e p (Y p) j

/-- Part (a) of `B_emb`: rules (1)–(4) for the induced connection. -/
def B_emb_rules : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (W : Type) [NormedAddCommGroup W] [NormedSpace ℝ W] (n : ℕ)
    (N : Set V) (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N),
    IsMilnorRules (nab (Bridge.conn (hN := hN)))

/-- A restricted to smooth tangent fields on slice submanifolds with model `ℝⁿ`. -/
def A_tan : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (W : Type) [NormedAddCommGroup W] [NormedSpace ℝ W] (n : ℕ)
    (N : Set V) (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N), Emb.TanRules hN

/-- `B_emb` is a special case of B (the induced connection is smooth, `Bridge.conn_contMDiff`). -/
theorem B_to_B_emb : B → B_emb := fun hB _ _ _ _ _ _ _ n _ hN =>
  hB n (Bridge.Sub hN) (Bridge.conn (hN := hN)) Bridge.conn_contMDiff

theorem B_emb_to_rules : B_emb → B_emb_rules := fun h V _ _ _ W _ _ n N hN => (h V W n N hN).1

theorem B_emb_rules_iff_A_tan : B_emb_rules ↔ A_tan :=
  ⟨fun h V _ _ _ W _ _ n N hN => Emb.isMilnorRules_iff.1 (h V W n N hN),
    fun h V _ _ _ W _ _ n N hN => Emb.isMilnorRules_iff.2 (h V W n N hN)⟩

open Emb in
/-- A restricted to smooth tangent fields (rule (2)/(3) for constants: `f` constant, whose `dN`
vanishes). -/
theorem A_to_A_tan : A → A_tan := by
  rintro ⟨h1, h2, h3, h4, h5⟩ V _ _ _ W _ _ n N hN
  let _ := hN.chartedSpace
  have md : ∀ {Y : N → V}, SF hN Y → ∀ q : N, MDifferentiableAt 𝓘(ℝ, Rn n) 𝓘(ℝ, V) Y q :=
    fun hY q => (hY.1 q).mdifferentiableAt (by simp)
  have mdf : ∀ {f : N → ℝ}, SFn hN f → ∀ q : N, MDifferentiableAt 𝓘(ℝ, Rn n) 𝓘(ℝ, ℝ) f q :=
    fun hf q => (hf q).mdifferentiableAt (by simp)
  have hconst : ∀ a : ℝ, SFn hN (fun _ => a) := fun a => contMDiff_const
  have hdN0 : ∀ (a : ℝ) (q : N) (v : V), Morse.dN hN (fun _ => a) q v = 0 := by
    intro a q v
    rw [Morse.dN_apply, mfderiv_const]
    rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro X Y hX hY
    exact ⟨h1 hN hX.1 hY.1 hX.2, Morse.leviCivita_mem hN X Y⟩
  · intro X X' Y _ _ _
    funext q; exact h2 hN X X' Y q
  · intro a X Y _ _
    funext q; exact h4 hN (fun _ => a) X Y q
  · intro X Y Y' _ hY hY'
    funext q; exact h3 hN X (md hY q) (md hY' q)
  · intro a X Y hX hY
    funext q
    have := h5 hN (f := fun _ => a) (mdf (hconst a) q) (md hY q) (hX.2 q) (hY.2 q)
    rw [this, hdN0, zero_smul, zero_add]
  · intro f X Y _ _ _
    funext q; exact h4 hN f X Y q
  · intro f X Y hf hX hY
    funext q; exact h5 hN (mdf hf q) (md hY q) (hX.2 q) (hY.2 q)

/-- **A implies part (a) of B on embedded manifolds** (rules (1)–(4) for the induced connection;
uses all five of A's theorems). Part (b), Christoffel symbols in arbitrary charts, is not in A. -/
theorem A_to_B_emb_rules : A → B_emb_rules := fun hA => B_emb_rules_iff_A_tan.2 (A_to_A_tan hA)

/-- **B implies A on smooth tangent fields**, by specializing B to `↥N`. -/
theorem B_to_A_tan : B → A_tan := fun hB => B_emb_rules_iff_A_tan.1 (B_emb_to_rules (B_to_B_emb hB))

#rt_check RoundTrip.V6_4.A_to_B_emb_rules [Morse.contMDiff_leviCivita, Morse.leviCivita_add_left, Morse.leviCivita_add_right, Morse.leviCivita_smul_left, Morse.leviCivita_smul_right]
#rt_check RoundTrip.V6_4.B_to_A_tan [Morse.contMDiff_leviCivita, Morse.leviCivita_add_left, Morse.leviCivita_add_right, Morse.leviCivita_smul_left, Morse.leviCivita_smul_right]
#rt_overlap RoundTrip.V6_4.B_to_A_tan [Morse.contMDiff_leviCivita, Morse.leviCivita_add_left, Morse.leviCivita_add_right, Morse.leviCivita_smul_left, Morse.leviCivita_smul_right]

end RoundTrip.V6_4
