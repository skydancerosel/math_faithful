import Morse
import RoundTrip.Check
import RoundTrip.Blind.V12_16
import RoundTrip.Bridge

/-!
# V12_16 (Milnor §21, Lemma 21.1): `I_τ(σ) = τσ⁻¹τ`; `G` is a symmetric space

`A` (universes `0`): `Morse.IsMatrixGroup.symmIso_mem ∧ symmIso_self ∧ symmIso_mul_exp_smul` — for a matrix
group `G ⊆ U(n)` (a slice submanifold of `Mₙ(𝕜)`, `Morse.IsMatrixGroup hG 𝔤`) and `τ ∈ G`, the linear isometry
`symmIso τ : A ↦ τAᴴτ` of `Mₙ(𝕜)` (vocabulary) maps `G` into `G`, fixes `τ`, and maps `τ exp(tX)` to
`τ exp(−tX)` for `X ∈ 𝔤`.

`B` (blind): for every abstract Lie group (Mathlib `LieGroup`, model `ℝⁿ`) with a bi-invariant metric and
every Levi-Civita connection, `I_τ` is an isometry (`C^∞` diffeomorphism preserving the metric), fixes `τ`,
reverses every geodesic through `τ` (on any interval); hence `G` is a symmetric space.

Neither direction is proved: `B` is about abstract Lie groups with an arbitrary bi-invariant metric, `A` about
matrix groups with the metric induced from `Mₙ(𝕜)` (and states the reversal only for the curves `τ exp(tX)`).

## The embedded special case

`B_emb`: `B` for a matrix group `G` with model `ℝᵐ`, as `Bridge.Sub hG` with the group structure of `G`
(`grp`, a Lie group by `lieGroup`: products and `ᴴ` are smooth ambient maps, corestricted), the induced metric
(bi-invariant, `biInv`) and the induced connection `Bridge.conn`.  `B → B_emb` (`B_to_B_emb`) and
`A → B_emb` (`A_to_B_emb`) are proved: `I_τ` is the corestriction of `symmIso τ` (`A`'s `symmIso_mem`), its
differential is `symmIso τ` read in `Mₙ(𝕜)` (`D_mfderiv_lift`), it fixes `τ` (`symmIso_self`), and every blind
geodesic through `τ` on an interval is `t ↦ τ exp(tX)` (`geod_eq_exp`, from the project's
`eqOn_mul_exp_smul` — Lemma 21.2's uniqueness argument, not one of this item's theorems — on the interior
and by continuity on the closed ends), which `symmIso τ` reverses (`symmIso_mul_exp_smul`).
-/

open Matrix Set Filter Topology Module
open scoped Morse.MatrixInner RealInnerProductSpace Manifold ContDiff

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace RoundTrip.V12_16

/-- The project's statement (universes `0`). -/
def A : Prop :=
  type_of% @Morse.IsMatrixGroup.symmIso_mem.{0,0,0,0} ∧
    type_of% @Morse.IsMatrixGroup.symmIso_self.{0,0,0,0} ∧
    type_of% @Morse.IsMatrixGroup.symmIso_mul_exp_smul.{0,0,0,0}

theorem A_holds : A :=
  ⟨@Morse.IsMatrixGroup.symmIso_mem, @Morse.IsMatrixGroup.symmIso_self,
    @Morse.IsMatrixGroup.symmIso_mul_exp_smul⟩

namespace Emb
open RoundTrip.Bridge
open RoundTrip.Bridge

variable {𝕜 : Type} [RCLike 𝕜] {k m : ℕ} {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [FiniteDimensional ℝ W]
  {G : Set (Matrix (Fin k) (Fin k) 𝕜)}
  {hG : Milnor.IsSliceSubmanifold 𝓘(ℝ, Matrix (Fin k) (Fin k) 𝕜) (Rn m) W G}
  {𝔤 : LieSubalgebra ℝ (Matrix (Fin k) (Fin k) 𝕜)}

/-- The group structure of `G` on `↥G = Bridge.Sub hG`. -/
@[reducible] def grp (h : Morse.IsMatrixGroup hG 𝔤) : Group (Bridge.Sub hG) where
  mul a b := (⟨a.1 * b.1, h.mul_mem _ a.2 _ b.2⟩ : G)
  one := (⟨1, h.one_mem⟩ : G)
  inv a := (⟨a.1ᴴ, h.star_mem _ a.2⟩ : G)
  mul_assoc a b c := Subtype.ext (Matrix.mul_assoc _ _ _)
  one_mul a := Subtype.ext (Matrix.one_mul _)
  mul_one a := Subtype.ext (Matrix.mul_one _)
  inv_mul_cancel a := Subtype.ext (h.unitary _ a.2)

theorem incl_mul (h : Morse.IsMatrixGroup hG 𝔤) (a b : Bridge.Sub hG) :
    incl hG (@HMul.hMul _ _ _ (@instHMul _ (grp h).toMul) a b) = incl hG a * incl hG b := rfl

theorem incl_inv (h : Morse.IsMatrixGroup hG 𝔤) (a : Bridge.Sub hG) :
    incl hG (@Inv.inv _ (grp h).toInv a) = (incl hG a)ᴴ := rfl

theorem incl_one (h : Morse.IsMatrixGroup hG 𝔤) :
    incl hG (@OfNat.ofNat _ 1 (@One.toOfNat1 _ (grp h).toOne)) = 1 := rfl

theorem lieGroup (h : Morse.IsMatrixGroup hG 𝔤) :
    @LieGroup ℝ _ (Rn m) _ (Rn m) _ _ 𝓘(ℝ, Rn m) ∞ (Bridge.Sub hG) (grp h) _ _ := by
  letI := grp h
  refine { contMDiff_mul := ?_, contMDiff_inv := ?_ }
  · have hF : ContMDiff (𝓘(ℝ, Rn m).prod 𝓘(ℝ, Rn m)) 𝓘(ℝ, Matrix (Fin k) (Fin k) 𝕜) ∞
        (fun p : Bridge.Sub hG × Bridge.Sub hG => incl hG p.1 * incl hG p.2) := by
      have h1 : ContMDiff (𝓘(ℝ, Rn m).prod 𝓘(ℝ, Rn m)) 𝓘(ℝ, Matrix (Fin k) (Fin k) 𝕜) ∞
          (fun p : Bridge.Sub hG × Bridge.Sub hG => incl hG p.1) := contMDiff_incl.comp contMDiff_fst
      have h2 : ContMDiff (𝓘(ℝ, Rn m).prod 𝓘(ℝ, Rn m)) 𝓘(ℝ, Matrix (Fin k) (Fin k) 𝕜) ∞
          (fun p : Bridge.Sub hG × Bridge.Sub hG => incl hG p.2) := contMDiff_incl.comp contMDiff_snd
      exact (contDiff_mul (𝕜 := ℝ) (𝔸 := Matrix (Fin k) (Fin k) 𝕜)).contMDiff.comp (h1.prodMk_space h2)
    exact hG.contMDiff_codRestrict hF (fun p => h.mul_mem _ p.1.2 _ p.2.2)
  · have hF : ContMDiff 𝓘(ℝ, Rn m) 𝓘(ℝ, Matrix (Fin k) (Fin k) 𝕜) ∞
        (fun p : Bridge.Sub hG => (incl hG p)ᴴ) :=
      (Morse.conjTransposeCLM (𝕜 := 𝕜) (ι := Fin k)).contDiff.contMDiff.comp contMDiff_incl
    exact hG.contMDiff_codRestrict hF (fun p => h.star_mem _ p.2)

/-- The derivative of a map `f : G → G` induced by an ambient map `F`, read in the ambient space:
`D_{f x} (df_x u) = dF_x (D_x u)`. -/
theorem D_mfderiv_lift {f : Bridge.Sub hG → Bridge.Sub hG}
    {F : Matrix (Fin k) (Fin k) 𝕜 → Matrix (Fin k) (Fin k) 𝕜} (x : Bridge.Sub hG)
    (hF : DifferentiableAt ℝ F (incl hG x)) (hfF : ∀ y, incl hG (f y) = F (incl hG y))
    (hf : MDifferentiableAt 𝓘(ℝ, Rn m) 𝓘(ℝ, Rn m) f x) (u : TangentSpace 𝓘(ℝ, Rn m) x) :
    D hG (f x) (mfderiv 𝓘(ℝ, Rn m) 𝓘(ℝ, Rn m) f x u) = fderiv ℝ F (incl hG x) (D hG x u) := by
  have e : incl hG ∘ f = F ∘ incl hG := funext hfF
  have hi : ∀ y : Bridge.Sub hG, MDifferentiableAt 𝓘(ℝ, Rn m) 𝓘(ℝ, Matrix (Fin k) (Fin k) 𝕜)
      (incl hG) y := fun y => contMDiff_incl.mdifferentiableAt (by simp)
  have h1 := mfderiv_comp x (hi (f x)) hf
  have h2 := mfderiv_comp x hF.mdifferentiableAt (hi x)
  rw [e, h2, mfderiv_eq_fderiv] at h1
  have := congrArg (fun L : Rn m →L[ℝ] Matrix (Fin k) (Fin k) 𝕜 => L u) h1
  exact this.symm

omit [FiniteDimensional ℝ W] in
theorem fderiv_mul_left' (a x w : Matrix (Fin k) (Fin k) 𝕜) :
    fderiv ℝ (fun y => a * y) x w = a * w := by
  have h : HasFDerivAt (fun y => a * y) (ContinuousLinearMap.mul ℝ (Matrix (Fin k) (Fin k) 𝕜) a) x :=
    (ContinuousLinearMap.mul ℝ (Matrix (Fin k) (Fin k) 𝕜) a).hasFDerivAt
  rw [h.fderiv]; rfl

omit [FiniteDimensional ℝ W] in
theorem fderiv_mul_right' (a x w : Matrix (Fin k) (Fin k) 𝕜) :
    fderiv ℝ (fun y => y * a) x w = w * a := by
  have h : HasFDerivAt (fun y => y * a)
      ((ContinuousLinearMap.mul ℝ (Matrix (Fin k) (Fin k) 𝕜)).flip a) x :=
    ((ContinuousLinearMap.mul ℝ (Matrix (Fin k) (Fin k) 𝕜)).flip a).hasFDerivAt
  rw [h.fderiv]; rfl

/-- Left and right translations of `G` are isometries of the induced metric. -/
theorem biInv (h : Morse.IsMatrixGroup hG 𝔤)
    (hL : ∀ U : Matrix (Fin k) (Fin k) 𝕜, Uᴴ * U = 1 → ∀ A B, ⟪U * A, U * B⟫ = ⟪A, B⟫)
    (hR : ∀ U : Matrix (Fin k) (Fin k) 𝕜, U * Uᴴ = 1 → ∀ A B, ⟪A * U, B * U⟫ = ⟪A, B⟫) :
    letI := grp h; haveI := lieGroup h; BiInvMetric m (Bridge.Sub hG) := by
  letI := grp h; haveI := lieGroup h
  constructor
  · intro g x u v
    have hd : ∀ w : TangentSpace 𝓘(ℝ, Rn m) x, D hG (g * x) (mfderiv 𝓘(ℝ, Rn m) 𝓘(ℝ, Rn m)
        (fun y => g * y) x w) = incl hG g * D hG x w := fun w => by
      rw [D_mfderiv_lift (F := fun y => incl hG g * y) x
        ((ContinuousLinearMap.mul ℝ (Matrix (Fin k) (Fin k) 𝕜) (incl hG g)).differentiableAt)
        (fun y => rfl) ((contMDiff_mul_left (I := 𝓘(ℝ, Rn m)) (n := ∞) (a := g)).mdifferentiableAt
          (by simp)), fderiv_mul_left']
    rw [inner_eq, inner_eq, hd, hd]
    exact hL _ (h.unitary _ g.2) _ _
  · intro g x u v
    have hd : ∀ w : TangentSpace 𝓘(ℝ, Rn m) x, D hG (x * g) (mfderiv 𝓘(ℝ, Rn m) 𝓘(ℝ, Rn m)
        (fun y => y * g) x w) = D hG x w * incl hG g := fun w => by
      rw [D_mfderiv_lift (F := fun y => y * incl hG g) x
        (((ContinuousLinearMap.mul ℝ (Matrix (Fin k) (Fin k) 𝕜)).flip (incl hG g)).differentiableAt)
        (fun y => rfl) ((contMDiff_mul_right (I := 𝓘(ℝ, Rn m)) (n := ∞) (a := g)).mdifferentiableAt
          (by simp)), fderiv_mul_right']
    rw [inner_eq, inner_eq, hd, hd]
    exact hR _ (Morse.mul_conjTranspose_eq_one (h.unitary _ g.2)) _ _

/-- A blind geodesic of the induced connection on `s` is a project geodesic on `interior s`. -/
theorem isGeodesicOn_interior {c : ℝ → Bridge.Sub hG} {s : Set ℝ}
    (hc : IsGeodesic (conn (hN := hG)) c s) :
    Morse.IsGeodesicOn hG (incl hG ∘ c) (interior s) := by
  obtain ⟨-, hcd, hP⟩ := isGeodesic_iff.1 hc
  refine ⟨isOpen_interior, fun t _ => (c t).2, hcd.mono interior_subset, fun t ht => ?_⟩
  have hs : s ∈ 𝓝 t := mem_interior_iff_mem_nhds.1 ht
  have h1 : deriv (incl hG ∘ c) =ᶠ[𝓝 t] derivWithin (incl hG ∘ c) s := by
    filter_upwards [isOpen_interior.mem_nhds ht] with τ hτ
    exact (derivWithin_of_mem_nhds (mem_interior_iff_mem_nhds.1 hτ)).symm
  have e : deriv (deriv (incl hG ∘ c)) t = derivWithin (derivWithin (incl hG ∘ c) s) s t := by
    rw [h1.deriv_eq, derivWithin_of_mem_nhds hs]
  refine (Morse.tanProj_eq_zero_iff hG).1 ?_
  rw [e]
  exact hP t (interior_subset ht)

/-- Every blind geodesic of `G` on an interval `s ∋ 0` is `t ↦ γ(0) exp(tX)` on `s`, `X ∈ 𝔤`, given the
project's `eqOn_mul_exp_smul` (for geodesics on open intervals) as `hE`: pass to `interior s` and back by
continuity. -/
theorem geod_eq_exp
    (hE : ∀ {γ : ℝ → Matrix (Fin k) (Fin k) 𝕜} {s : Set ℝ}, Morse.IsGeodesicOn hG γ s →
      IsPreconnected s → ∀ {t₀ : ℝ}, t₀ ∈ s → (γ t₀)ᴴ * deriv γ t₀ ∈ 𝔤 ∧
        EqOn γ (fun t => γ t₀ * NormedSpace.exp ((t - t₀) • ((γ t₀)ᴴ * deriv γ t₀))) s)
    {γ : ℝ → Bridge.Sub hG} {s : Set ℝ} (hγ : IsGeodesic (conn (hN := hG)) γ s) (h0 : (0 : ℝ) ∈ s) :
    ∃ X ∈ 𝔤, ∀ t ∈ s, incl hG (γ t) = incl hG (γ 0) * NormedSpace.exp (t • X) := by
  obtain ⟨⟨hsc, hsu⟩, hc, -⟩ := isGeodesic_iff.1 hγ
  obtain ⟨a, has, ha0⟩ : ∃ a ∈ s, a ≠ 0 := by
    have hacc := (hsu 0 h0).accPt
    rw [accPt_iff_nhds] at hacc
    obtain ⟨y, ⟨-, hy⟩, hy0⟩ := hacc univ univ_mem
    exact ⟨y, hy, hy0⟩
  have hint : (interior s).Nonempty := by
    refine ⟨a / 2, ?_⟩
    rcases lt_or_gt_of_ne ha0 with ha | ha
    · have hsub : Ioo a 0 ⊆ s := fun x hx => hsc.out has h0 ⟨hx.1.le, hx.2.le⟩
      exact interior_mono hsub (by rw [interior_Ioo]; constructor <;> linarith)
    · have hsub : Ioo 0 a ⊆ s := fun x hx => hsc.out h0 has ⟨hx.1.le, hx.2.le⟩
      exact interior_mono hsub (by rw [interior_Ioo]; constructor <;> linarith)
  obtain ⟨t₁, ht₁⟩ := hint
  obtain ⟨hX, heq⟩ := hE (isGeodesicOn_interior hγ) hsc.interior.isPreconnected ht₁
  set X := ((incl hG ∘ γ) t₁)ᴴ * deriv (incl hG ∘ γ) t₁ with hXdef
  have hcl : s ⊆ closure (interior s) := by
    rw [(hsc.convex (𝕜 := ℝ)).closure_interior_eq_closure_of_nonempty_interior ⟨t₁, ht₁⟩]
    exact subset_closure
  have hgc : Continuous fun t : ℝ => (incl hG ∘ γ) t₁ * NormedSpace.exp ((t - t₁) • X) :=
    continuous_const.mul ((Morse.contDiff_exp_smul X).continuous.comp (continuous_sub_right t₁))
  have heq' := heq.of_subset_closure hc.continuousOn hgc.continuousOn interior_subset hcl
  refine ⟨X, hX, fun t ht => ?_⟩
  have e0 := heq' h0
  have et := heq' ht
  simp only [Function.comp_apply] at e0 et
  rw [et, e0, Matrix.mul_assoc, Morse.exp_smul_mul_exp_smul]
  congr 3
  ring


/-! ### `I_τ` on `G` -/

theorem incl_Itau (h : Morse.IsMatrixGroup hG 𝔤) (τ σ : Bridge.Sub hG) :
    incl hG (@Itau _ (grp h) τ σ) = Morse.IsMatrixGroup.symmIso (incl hG τ) (h.unitary _ τ.2) (incl hG σ) :=
  rfl

/-- `I_τ` is an involution. -/
theorem Itau_Itau (h : Morse.IsMatrixGroup hG 𝔤) (τ σ : Bridge.Sub hG) :
    @Itau _ (grp h) τ (@Itau _ (grp h) τ σ) = σ := by
  letI := grp h
  simp only [Itau]
  group

/-- `A`'s `symmIso_mem`, `symmIso_self`, `symmIso_mul_exp_smul` give `B` on `G`. -/
theorem part1 (hA : A) (h : Morse.IsMatrixGroup hG 𝔤) (τ : Bridge.Sub hG) :
    letI := grp h; haveI := lieGroup h
    IsIsom (n := m) (Itau τ) ∧ Itau τ τ = τ ∧ ReversesGeod (conn (hN := hG)) (Itau τ) τ := by
  letI := grp h; haveI := lieGroup h
  obtain ⟨hA1, hA2, hA3⟩ := hA
  have hsm : ContMDiff 𝓘(ℝ, Rn m) 𝓘(ℝ, Rn m) ∞ (Itau τ) := by
    have hF : ContMDiff 𝓘(ℝ, Rn m) 𝓘(ℝ, Matrix (Fin k) (Fin k) 𝕜) ∞
        (fun σ : Bridge.Sub hG => Morse.IsMatrixGroup.symmIso (incl hG τ) (h.unitary _ τ.2) (incl hG σ)) :=
      (Morse.IsMatrixGroup.symmIso (incl hG τ) (h.unitary _ τ.2)).toContinuousLinearEquiv.contDiff.contMDiff.comp
        contMDiff_incl
    exact hG.contMDiff_codRestrict hF (fun σ => hA1 h τ.2 σ.2)
  refine ⟨⟨hsm, ⟨Itau τ, hsm, Itau_Itau h τ, Itau_Itau h τ⟩, fun σ u v => ?_⟩, ?_, ?_⟩
  · have hd : ∀ w : TangentSpace 𝓘(ℝ, Rn m) σ, D hG (Itau τ σ) (mfderiv 𝓘(ℝ, Rn m) 𝓘(ℝ, Rn m)
        (Itau τ) σ w) = Morse.IsMatrixGroup.symmIso (incl hG τ) (h.unitary _ τ.2) (D hG σ w) := fun w => by
      set S := Morse.IsMatrixGroup.symmIso (incl hG τ) (h.unitary _ τ.2)
      have hS : HasFDerivAt (fun y => S y) (S.toContinuousLinearEquiv : _ →L[ℝ] _) (incl hG σ) :=
        S.toContinuousLinearEquiv.hasFDerivAt
      rw [D_mfderiv_lift (F := fun y => S y) σ hS.differentiableAt (fun y => incl_Itau h τ y)
        (hsm.mdifferentiableAt (by simp)), hS.fderiv]
      rfl
    rw [inner_eq, inner_eq, hd, hd, LinearIsometryEquiv.inner_map_map]
  · exact Subtype.ext (hA2 h τ.2)
  · intro s γ hγ h0 hγ0 t ht hmt
    obtain ⟨X, hX, hγX⟩ := geod_eq_exp (Morse.IsMatrixGroup.eqOn_mul_exp_smul h) hγ h0
    apply Subtype.ext
    change incl hG (Itau τ (γ t)) = incl hG (γ (-t))
    rw [incl_Itau, hγX t ht, hγX (-t) hmt, hγ0]
    exact hA3 h τ.2 hX t

end Emb

open Emb

/-- `B` for a matrix group `G ⊆ Mₖ(𝕜)` modelled on `ℝᵐ`, as `Bridge.Sub hG` with its group structure, the
induced metric and the induced (Levi-Civita) connection `Bridge.conn`. -/
def B_emb : Prop :=
  ∀ (𝕜 : Type) [RCLike 𝕜] (k m : ℕ) (W : Type) [NormedAddCommGroup W] [NormedSpace ℝ W]
    [FiniteDimensional ℝ W] (G : Set (Matrix (Fin k) (Fin k) 𝕜))
    (hG : Milnor.IsSliceSubmanifold 𝓘(ℝ, Matrix (Fin k) (Fin k) 𝕜) (Rn m) W G)
    (𝔤 : LieSubalgebra ℝ (Matrix (Fin k) (Fin k) 𝕜)) (h : Morse.IsMatrixGroup hG 𝔤),
    letI := grp h; haveI := lieGroup h
    (∀ τ : Bridge.Sub hG, IsIsom (n := m) (Itau τ) ∧ Itau τ τ = τ ∧
        ReversesGeod (Bridge.conn (hN := hG)) (Itau τ) τ) ∧
      IsSymmSpace (Bridge.conn (hN := hG))

/-- `B_emb` is a special case of `B`: the induced metric is bi-invariant (`biInv`) and the induced connection
is Levi-Civita (`Bridge.conn_isLC`). -/
theorem B_to_B_emb : B → B_emb := by
  intro hB 𝕜 _ k m W _ _ _ G hG 𝔤 h
  letI := grp h; haveI := lieGroup h
  exact hB m (Bridge.Sub hG)
    (biInv h (fun _ hU => Morse.inner_mul_left_of_unitary hU)
      (fun _ hU => Morse.inner_mul_right_of_unitary hU))
    Bridge.conn Bridge.conn_isLC

theorem A_to_B_emb : A → B_emb := by
  intro hA 𝕜 _ k m W _ _ _ G hG 𝔤 h
  letI := grp h; haveI := lieGroup h
  exact ⟨part1 hA h, fun p => ⟨Itau p, part1 hA h p⟩⟩

#rt_check RoundTrip.V12_16.A_to_B_emb [Morse.IsMatrixGroup.symmIso_mem, Morse.IsMatrixGroup.symmIso_self,
  Morse.IsMatrixGroup.symmIso_mul_exp_smul]
#rt_check RoundTrip.V12_16.B_to_B_emb [Morse.IsMatrixGroup.symmIso_mem, Morse.IsMatrixGroup.symmIso_self,
  Morse.IsMatrixGroup.symmIso_mul_exp_smul]
#rt_overlap RoundTrip.V12_16.A_to_B_emb [Morse.IsMatrixGroup.symmIso_mem, Morse.IsMatrixGroup.symmIso_self,
  Morse.IsMatrixGroup.symmIso_mul_exp_smul]

end RoundTrip.V12_16
