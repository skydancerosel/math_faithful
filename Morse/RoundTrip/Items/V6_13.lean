import Morse
import RoundTrip.Check
import RoundTrip.Blind.V6_13
import RoundTrip.Bridge

open Set Filter Topology Function Module
open scoped ContDiff Manifold RealInnerProductSpace

namespace RoundTrip.V6_13

/-- The project's statement (universes instantiated at 0; `Morse.IsSymmetric` and `Morse.bracket`
are definitions): for a Mathlib connection on an abstract manifold (any model), Milnor's
symmetry (`X ⊢ Y − Y ⊢ X = [X, Y]`, Mathlib's `mlieBracket`, for fields differentiable at the
point) ↔ torsion zero; for a slice submanifold `N ⊆ V`: the ambient bracket `dY(X) − dX(Y)` of two
tangent fields is tangent, acts on functions as the Poisson bracket, and the induced connection is
symmetric. -/
def A : Prop :=
  type_of% @Morse.isSymmetric_iff_torsion_eq_zero.{0,0,0} ∧ type_of% @Morse.bracket_mem.{0,0,0} ∧
    type_of% @Morse.dN_bracket.{0,0,0} ∧ type_of% @Morse.leviCivita_sub_leviCivita.{0,0,0}

theorem A_holds : A := ⟨@Morse.isSymmetric_iff_torsion_eq_zero, @Morse.bracket_mem,
  @Morse.dN_bracket, @Morse.leviCivita_sub_leviCivita⟩

/-! ### Re-proofs of A outside the item (for the vacuous B ⇒ A) -/

section Reprove

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {Z : Type} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
  {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {N : Set V} (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N)

theorem rp_bracket_mem {X Y : N → V} (hXT : Morse.IsTangentField hN X)
    (hYT : Morse.IsTangentField hN Y)
    {q : N} (hX : letI := hN.chartedSpace; MDifferentiableAt 𝓘(ℝ, Z) 𝓘(ℝ, V) X q)
    (hY : letI := hN.chartedSpace; MDifferentiableAt 𝓘(ℝ, Z) 𝓘(ℝ, V) Y q) :
    Morse.bracket hN X Y q ∈ Morse.tangentSubspace hN q := by
  have h1 := Morse.secondFundForm_eq_sub_tanProj hN hYT hY (hXT q)
  have h2 := Morse.secondFundForm_eq_sub_tanProj hN hXT hX (hYT q)
  rw [Morse.secondFundForm_comm hN (hXT q) (hYT q)] at h1
  rw [← Morse.tanProj_eq_self_iff, Morse.bracket, map_sub]
  exact (sub_eq_sub_iff_sub_eq_sub.1 (h1.symm.trans h2)).symm

theorem rp_dN_bracket {f : N → ℝ} {X Y : N → V}
    (hf : letI := hN.chartedSpace; ContMDiff 𝓘(ℝ, Z) 𝓘(ℝ, ℝ) ∞ f)
    (hX : letI := hN.chartedSpace; ContMDiff 𝓘(ℝ, Z) 𝓘(ℝ, V) ∞ X)
    (hY : letI := hN.chartedSpace; ContMDiff 𝓘(ℝ, Z) 𝓘(ℝ, V) ∞ Y)
    (hXT : Morse.IsTangentField hN X) (hYT : Morse.IsTangentField hN Y) (q : N) :
    Morse.dN hN (fun x => Morse.dN hN f x (Y x)) q (X q) -
        Morse.dN hN (fun x => Morse.dN hN f x (X x)) q (Y q) =
      Morse.dN hN f q (Morse.bracket hN X Y q) := by
  let _ := hN.chartedSpace
  have := hN.isManifold
  obtain ⟨G, U, hU, hqU, hG, hfG⟩ := Morse.exists_contDiffOn_rep hN hf q
  have hUN : IsOpen {x : N | x.1 ∈ U} := hU.preimage continuous_subtype_val
  have hGq : ContDiffAt ℝ ∞ G q := hG.contDiffAt (hU.mem_nhds hqU)
  have hG' : ContDiffAt ℝ ∞ (fderiv ℝ G) q :=
    (hG.fderiv_of_isOpen hU (by simp)).contDiffAt (hU.mem_nhds hqU)
  have hfG' : ∀ x : N, x.1 ∈ U → ∀ v ∈ Morse.tangentSubspace hN x,
      Morse.dN hN f x v = fderiv ℝ G x v := by
    intro x hx v hv
    refine Morse.dN_eq_fderiv hN ((hG.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp))
      ?_ hv
    filter_upwards [hUN.mem_nhds hx] with y hy
    exact hfG y hy
  have hd1 : MDifferentiableAt 𝓘(ℝ, Z) 𝓘(ℝ, V →L[ℝ] ℝ) (fun x : N => fderiv ℝ G x) q :=
    ((hG'.differentiableAt (by simp)).mdifferentiableAt).comp q
      (hN.contMDiff_val.mdifferentiableAt (by simp))
  have key : ∀ A B : N → V, Morse.IsTangentField hN A →
      (letI := hN.chartedSpace; ContMDiff 𝓘(ℝ, Z) 𝓘(ℝ, V) ∞ A) →
      B q ∈ Morse.tangentSubspace hN q →
      Morse.dN hN (fun x => Morse.dN hN f x (A x)) q (B q) =
        fderiv ℝ (fderiv ℝ G) q (B q) (A q) + fderiv ℝ G q (Morse.dN hN A q (B q)) := by
    intro A B hAT hA hB
    have hev : (fun x => Morse.dN hN f x (A x)) =ᶠ[𝓝 q] fun x => fderiv ℝ G x (A x) := by
      filter_upwards [hUN.mem_nhds hqU] with x hx
      exact hfG' x hx (A x) (hAT x)
    rw [Morse.dN_congr hN hev, Morse.dN_clm_apply hN hd1 (hA.mdifferentiableAt (by simp)) hB,
      Morse.dN_comp_val hN (hG'.differentiableAt (by simp)) hB]
  rw [key Y X hYT hY (hXT q), key X Y hXT hX (hYT q),
    (hGq.isSymmSndFDerivAt (by
      simp only [minSmoothness_of_isRCLikeNormedField]; exact WithTop.coe_le_coe.2 le_top))
      (X q) (Y q),
    hfG' q hqU _ (rp_bracket_mem hN hXT hYT (hX.mdifferentiableAt (by simp))
      (hY.mdifferentiableAt (by simp))), Morse.bracket, map_sub]
  abel

end Reprove

/-- B ⇒ A holds only because A is provable outright: the abstract clause is Mathlib's
`torsion_eq_zero_iff`; the embedded clauses are the project's own proofs re-done from lemmas
outside the item (symmetry of the second fundamental form `secondFundForm_comm`, symmetry of
ambient second derivatives). B is about abstract manifolds and does not specialize to `N ⊆ V`. -/
theorem B_to_A : B → A := by
  intro _
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro E _ _ H _ I M _ _ _ cov _
    rw [CovariantDerivative.torsion_eq_zero_iff]
    exact ⟨fun h X Y x hX hY => h X Y x hX hY, fun h X Y x hX hY => h hX hY⟩
  · intro V _ _ _ Z _ _ W _ _ N hN _ _ X Y hXT hYT q hX hY
    exact rp_bracket_mem hN hXT hYT hX hY
  · intro V _ _ _ Z _ _ W _ _ N hN _ _ f X Y hf hX hY hXT hYT q
    exact rp_dN_bracket hN hf hX hY hXT hYT q
  · intro V _ _ _ Z _ _ W _ _ N hN _ _ X Y hXT hYT q hX hY
    rw [Morse.leviCivita, Morse.leviCivita, Morse.covAt, Morse.covAt, ← map_sub]
    exact Morse.tanProj_eq_self hN (rp_bracket_mem hN hXT hYT hX hY)

#rt_check RoundTrip.V6_13.B_to_A [Morse.isSymmetric_iff_torsion_eq_zero, Morse.bracket_mem,
  Morse.dN_bracket, Morse.leviCivita_sub_leviCivita]
#rt_overlap RoundTrip.V6_13.B_to_A [Morse.isSymmetric_iff_torsion_eq_zero, Morse.bracket_mem,
  Morse.dN_bracket, Morse.leviCivita_sub_leviCivita]


/-! ## The embedded special case

B is specialized to `M = ↥N` (`RoundTrip.Bridge.Sub hN`) for a slice submanifold `N ⊆ V` with
model `ℝⁿ` and the induced metric, and its connection clause to the induced connection
`Bridge.conn` (`B_emb`). Dictionary (namespace `Emb`): `mfderiv F p v = dN F p (D_p v)`
(`dN_D'`), so B's `X f` is the project's `dN f (X̂)` (`dirDeriv_eq`); Mathlib's bracket, read in
`V`, is the project's ambient bracket (`D_mlieBracket'`, from `Bridge.D_mlieBracket`); the
coordinate fields of a chart `extChartAt p` are, near each point of its source, Mathlib's
pull-backs of the constant fields `eᵢ` (`coordField_eventuallyEq`), hence smooth there with
vanishing brackets (`mlieBracket_coordField`). Then B's clause (i) on `↥N` is exactly A's
`dN_bracket` for model `ℝⁿ` (`A813`), and B's clause (ii) for `Bridge.conn` follows from A's
`leviCivita_sub_leviCivita` (Christoffel symmetry of the induced connection). -/

namespace Emb

set_option linter.unusedSectionVars false

open RoundTrip.Bridge VectorField

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] {n : ℕ} {N : Set V}
  {hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N}

/-- `mfderiv` on `↥N` is the project's `dN`, through `D`. -/
theorem dN_D' {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (F : Sub hN → E) (q : Sub hN)
    (v : TangentSpace 𝓘(ℝ, Rn n) q) :
    Morse.dN hN F q (D hN q v) = mfderiv 𝓘(ℝ, Rn n) 𝓘(ℝ, E) F q v := by
  show mfderiv 𝓘(ℝ, Rn n) 𝓘(ℝ, E) F q (L hN q (D hN q v)) = _
  exact congrArg (mfderiv 𝓘(ℝ, Rn n) 𝓘(ℝ, E) F q) (L_D q v)

/-- B's `X f = df(X)`, read with the project's `dN` and the ambient field `X̂ = amb X`. -/
theorem dirDeriv_eq (X : VF n (Sub hN)) (f : Sub hN → ℝ) :
    dirDeriv X f = fun x => Morse.dN hN f x (amb X x) :=
  funext fun x => (dN_D' f x (X x)).symm

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

theorem isSmoothVF_liftF {Y : N → V}
    (hY : ContMDiff 𝓘(ℝ, Rn n) 𝓘(ℝ, V) ∞ (fun q : Sub hN => Y q))
    (hYT : Morse.IsTangentField hN Y) : IsSmoothVF (liftF (hN := hN) Y) := by
  unfold IsSmoothVF
  rw [contMDiff_section_iff, amb_liftF hYT]
  exact hY

/-! #### Coordinate fields -/

/-- The constant vector field `eᵢ` on `ℝⁿ`. -/
noncomputable def eF (i : Fin n) : (u : Rn n) → TangentSpace 𝓘(ℝ, Rn n) u :=
  fun _ => EuclideanSpace.single i (1 : ℝ)

theorem mdifferentiableAt_eF (i : Fin n) (u : Rn n) :
    MDifferentiableAt 𝓘(ℝ, Rn n) (𝓘(ℝ, Rn n)).tangent
      (fun u => (⟨u, eF i u⟩ : TangentBundle 𝓘(ℝ, Rn n) (Rn n))) u :=
  (contMDiffAt_vectorSpace_iff_contDiffAt (n := 1).2 contDiffAt_const).mdifferentiableAt
    (by simp)

theorem mlieBracket_eF (i j : Fin n) : mlieBracket 𝓘(ℝ, Rn n) (eF i) (eF j) = 0 := by
  rw [← mlieBracketWithin_univ, mlieBracketWithin_eq_lieBracketWithin]
  funext u
  show fderivWithin ℝ (fun _ : Rn n => (EuclideanSpace.single j (1 : ℝ) : Rn n)) univ u
      (EuclideanSpace.single i 1) -
    fderivWithin ℝ (fun _ : Rn n => (EuclideanSpace.single i (1 : ℝ) : Rn n)) univ u
      (EuclideanSpace.single j 1) = 0
  simp

/-- Near a point of the chart's source, the coordinate field `∂ᵢ` of B is Mathlib's pull-back
of `eᵢ` by the chart. -/
theorem coordField_eventuallyEq (p : Sub hN) {x : Sub hN}
    (hx : x ∈ (extChartAt 𝓘(ℝ, Rn n) p).source) (i : Fin n) :
    coordField p i =ᶠ[𝓝 x] mpullback 𝓘(ℝ, Rn n) 𝓘(ℝ, Rn n) (extChartAt 𝓘(ℝ, Rn n) p) (eF i) := by
  filter_upwards [(isOpen_extChartAt_source p).mem_nhds hx] with y hy
  simp only [coordField, if_pos hy]
  rfl

theorem mdifferentiableAt_coordField (p : Sub hN) {x : Sub hN}
    (hx : x ∈ (extChartAt 𝓘(ℝ, Rn n) p).source) (i : Fin n) :
    MDifferentiableAt 𝓘(ℝ, Rn n) (𝓘(ℝ, Rn n)).tangent
      (fun y => (⟨y, coordField p i y⟩ : TangentBundle 𝓘(ℝ, Rn n) (Sub hN))) x := by
  have hx' : x ∈ (chartAt (Rn n) p).source := by rwa [extChartAt_source] at hx
  have h := MDifferentiableAt.mpullback_vectorField (mdifferentiableAt_eF i _)
    (contMDiffAt_extChartAt' (n := ∞) hx') (isInvertible_mfderiv_extChartAt hx)
    (WithTop.coe_le_coe.2 le_top)
  refine h.congr_of_eventuallyEq ?_
  filter_upwards [coordField_eventuallyEq p hx i] with y hy
  rw [hy]

/-- **Coordinate fields commute** (on the chart's source). -/
theorem mlieBracket_coordField (p : Sub hN) {x : Sub hN}
    (hx : x ∈ (extChartAt 𝓘(ℝ, Rn n) p).source) (i j : Fin n) :
    mlieBracket 𝓘(ℝ, Rn n) (coordField p i) (coordField p j) x = 0 := by
  have hx' : x ∈ (chartAt (Rn n) p).source := by rwa [extChartAt_source] at hx
  have h2 : minSmoothness ℝ 2 ≤ ∞ := by
    rw [minSmoothness_of_isRCLikeNormedField]; exact WithTop.coe_le_coe.2 le_top
  have : IsManifold 𝓘(ℝ, Rn n) (minSmoothness ℝ 2) (Sub hN) := IsManifold.of_le h2
  rw [(coordField_eventuallyEq p hx i).mlieBracket_vectorField_eq (coordField_eventuallyEq p hx j),
    ← mpullback_mlieBracket (mdifferentiableAt_eF i _) (mdifferentiableAt_eF j _)
      (contMDiffAt_extChartAt' (n := ∞) hx') h2, mlieBracket_eF]
  simp [mpullback_apply]

/-- A's `dN_bracket` for model `ℝⁿ`: the part of A that `B_emb` covers. -/
def A813 : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (W : Type) [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] (n : ℕ)
    (N : Set V) (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N) (f : N → ℝ) (X Y : N → V),
    (letI := hN.chartedSpace; ContMDiff 𝓘(ℝ, Rn n) 𝓘(ℝ, ℝ) ∞ f) →
    (letI := hN.chartedSpace; ContMDiff 𝓘(ℝ, Rn n) 𝓘(ℝ, V) ∞ X) →
    (letI := hN.chartedSpace; ContMDiff 𝓘(ℝ, Rn n) 𝓘(ℝ, V) ∞ Y) →
    Morse.IsTangentField hN X → Morse.IsTangentField hN Y → ∀ q : N,
      Morse.dN hN (fun x => Morse.dN hN f x (Y x)) q (X q) -
          Morse.dN hN (fun x => Morse.dN hN f x (X x)) q (Y q) =
        Morse.dN hN f q (Morse.bracket hN X Y q)

/-- B's clause (i) on `↥N` is A's `dN_bracket` (model `ℝⁿ`). -/
theorem poisson_iff_A813 :
    (∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
      (W : Type) [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] (n : ℕ)
      (N : Set V) (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N),
      ∀ X Y : VF n (Sub hN), IsSmoothVF X → IsSmoothVF Y → ∀ f : Sub hN → ℝ,
        ContMDiff 𝓘(ℝ, Rn n) 𝓘(ℝ, ℝ) ∞ f → ∀ p : Sub hN,
          dirDeriv (mlieBracket 𝓘(ℝ, Rn n) X Y) f p =
            dirDeriv X (dirDeriv Y f) p - dirDeriv Y (dirDeriv X f) p) ↔ A813 := by
  constructor
  · intro h V _ _ _ W _ _ _ n N hN f X Y hf hX hY hXT hYT q
    have hX' := isSmoothVF_liftF hX hXT
    have hY' := isSmoothVF_liftF hY hYT
    have := h V W n N hN (liftF X) (liftF Y) hX' hY' f hf q
    have e1 : dirDeriv (mlieBracket 𝓘(ℝ, Rn n) (liftF (hN := hN) X) (liftF Y)) f q =
        Morse.dN hN f q (Morse.bracket hN X Y q) := by
      refine (dN_D' f q _).symm.trans (congrArg (Morse.dN hN f q) ?_)
      refine (D_mlieBracket' q ((hX' q).mdifferentiableAt (by simp))
        ((hY' q).mdifferentiableAt (by simp))).trans ?_
      rw [amb_liftF hXT, amb_liftF hYT]
    have e2 : ∀ {A B : N → V}, Morse.IsTangentField hN A → Morse.IsTangentField hN B →
        dirDeriv (liftF (hN := hN) A) (dirDeriv (liftF (hN := hN) B) f) q =
          Morse.dN hN (fun x => Morse.dN hN f x (B x)) q (A q) := by
      intro A B hA hB
      rw [dirDeriv_eq (liftF B) f, amb_liftF hB]
      exact (dN_D' _ q _).symm.trans (congrArg _ (D_L (hA q)))
    rw [e1, e2 hXT hYT, e2 hYT hXT] at this
    exact this.symm
  · intro h V _ _ _ W _ _ _ n N hN X Y hX hY f hf p
    have := h V W n N hN f (amb X) (amb Y) hf (contMDiff_amb hX) (contMDiff_amb hY)
      (isTangentField_amb X) (isTangentField_amb Y) p
    rw [dirDeriv_eq (mlieBracket 𝓘(ℝ, Rn n) X Y) f, dirDeriv_eq X, dirDeriv_eq Y f,
      dirDeriv_eq Y, dirDeriv_eq X f]
    show Morse.dN hN f p (D hN p (mlieBracket 𝓘(ℝ, Rn n) X Y p)) = _
    rw [D_mlieBracket' p ((hX p).mdifferentiableAt (by simp)) ((hY p).mdifferentiableAt (by simp))]
    exact this.symm

/-- B's clause (ii) for the induced connection follows from A's `leviCivita_sub_leviCivita`:
the Christoffel symbols of `Bridge.conn` are symmetric in every chart `extChartAt p`. -/
theorem gam_symm
    (hLC : ∀ {X Y : N → V}, Morse.IsTangentField hN X → Morse.IsTangentField hN Y → ∀ {q : N},
      (letI := hN.chartedSpace; MDifferentiableAt 𝓘(ℝ, Rn n) 𝓘(ℝ, V) X q) →
      (letI := hN.chartedSpace; MDifferentiableAt 𝓘(ℝ, Rn n) 𝓘(ℝ, V) Y q) →
      Morse.leviCivita hN X Y q - Morse.leviCivita hN Y X q = Morse.bracket hN X Y q)
    (p x : Sub hN) (hx : x ∈ (extChartAt 𝓘(ℝ, Rn n) p).source) (i j k : Fin n) :
    Gam (conn (hN := hN)) p x i j k = Gam (conn (hN := hN)) p x j i k := by
  have hi := mdifferentiableAt_coordField p hx i
  have hj := mdifferentiableAt_coordField p hx j
  have key : conn (coordField p j) x (coordField p i x) = conn (coordField p i) x (coordField p j x) := by
    apply D_injective x
    have h1 := hLC (isTangentField_amb (coordField p i)) (isTangentField_amb (coordField p j))
      (q := x) (mdifferentiableAt_section_iff.1 hi) (mdifferentiableAt_section_iff.1 hj)
    rw [← D_conn, ← D_conn, ← D_mlieBracket' x hi hj, mlieBracket_coordField p hx i j,
      D_tzero] at h1
    exact sub_eq_zero.1 h1
  simp only [Gam, key]

end Emb

/-- B on embedded manifolds: `M = ↥N` with the induced metric, clause (ii) for the induced
connection (a special case of B, see `B_to_B_emb`). -/
def B_emb : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (W : Type) [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] (n : ℕ)
    (N : Set V) (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N),
    (∀ X Y : VF n (Bridge.Sub hN), IsSmoothVF X → IsSmoothVF Y → ∀ f : Bridge.Sub hN → ℝ,
      ContMDiff 𝓘(ℝ, Rn n) 𝓘(ℝ, ℝ) ∞ f → ∀ p : Bridge.Sub hN,
        dirDeriv (VectorField.mlieBracket 𝓘(ℝ, Rn n) X Y) f p =
          dirDeriv X (dirDeriv Y f) p - dirDeriv Y (dirDeriv X f) p) ∧
    (IsSymm (Bridge.conn (hN := hN)) ↔
      ∀ (p x : Bridge.Sub hN), x ∈ (extChartAt 𝓘(ℝ, Rn n) p).source → ∀ i j k : Fin n,
        Gam (Bridge.conn (hN := hN)) p x i j k = Gam (Bridge.conn (hN := hN)) p x j i k)

/-- `B_emb` is a special case of B (`Bridge.conn` is smooth). -/
theorem B_to_B_emb : B → B_emb := fun hB _ _ _ _ _ _ _ _ n _ hN =>
  ⟨(hB n (Bridge.Sub hN)).1, (hB n (Bridge.Sub hN)).2 (Bridge.conn (hN := hN)) Bridge.conn_isGlobalConn⟩

theorem A_to_A813 : A → Emb.A813 := fun hA _ _ _ _ _ _ _ _ _ _ hN _ _ _ hf hX hY hXT hYT q =>
  hA.2.2.1 hN hf hX hY hXT hYT q

/-- **A implies B on embedded manifolds**: clause (i) from A's `dN_bracket`, clause (ii) from A's
`leviCivita_sub_leviCivita` (its left side is `Bridge.conn_isSymm`). -/
theorem A_to_B_emb : A → B_emb := fun hA V _ _ _ W _ _ _ n N hN =>
  ⟨Emb.poisson_iff_A813.2 (A_to_A813 hA) V W n N hN,
    ⟨fun _ => Emb.gam_symm (hN := hN) (fun hXT hYT _ hX hY => hA.2.2.2 hN hXT hYT hX hY),
      fun _ => Bridge.conn_isSymm⟩⟩

/-- **B implies A's `dN_bracket`** (model `ℝⁿ`), by specializing B's clause (i) to `↥N`. -/
theorem B_to_A813 : B → Emb.A813 := fun hB =>
  Emb.poisson_iff_A813.1 fun V _ _ _ W _ _ _ n N hN => (B_to_B_emb hB V W n N hN).1

#rt_check RoundTrip.V6_13.A_to_B_emb [Morse.isSymmetric_iff_torsion_eq_zero, Morse.bracket_mem,
  Morse.dN_bracket, Morse.leviCivita_sub_leviCivita]
#rt_check RoundTrip.V6_13.B_to_A813 [Morse.isSymmetric_iff_torsion_eq_zero, Morse.bracket_mem,
  Morse.dN_bracket, Morse.leviCivita_sub_leviCivita]
#rt_overlap RoundTrip.V6_13.B_to_A813 [Morse.isSymmetric_iff_torsion_eq_zero, Morse.bracket_mem,
  Morse.dN_bracket, Morse.leviCivita_sub_leviCivita]

end RoundTrip.V6_13
