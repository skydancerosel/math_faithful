import Morse
import RoundTrip.Check
import RoundTrip.Blind.V11_9
import RoundTrip.Bridge

open Set Filter Topology Function Module MeasureTheory
open scoped ContDiff Manifold ENNReal unitInterval RealInnerProductSpace

namespace RoundTrip.V11_9

/-- The project's statement (universes instantiated at `0`; `Morse.ricci` is vocabulary): for a
slice submanifold `N ⊆ V` (model `Z`), `q ∈ N`, the Ricci tensor `K(U₁, U₂) = trace(W ↦ R(U₁, W)U₂)`
of `T_qN` equals `Σᵢ ⟨R(U₁, Eᵢ)U₂, Eᵢ⟩` in any orthonormal basis (`ricci_eq_sum`); it is symmetric
(`ricci_comm`); `R(x, x) = 0` (`curvOp_self`); and `K(E_{i₀}, E_{i₀}) = Σ_{i ≠ i₀}
⟨R(E_{i₀}, Eᵢ)E_{i₀}, Eᵢ⟩` (`ricci_eq_sum_erase`, Milnor's Assertion). -/
def A : Prop :=
  type_of% @Morse.ricci_eq_sum.{0,0,0,0} ∧ type_of% @Morse.ricci_comm.{0,0,0} ∧
    type_of% @Morse.curvOp_self.{0,0,0} ∧ type_of% @Morse.ricci_eq_sum_erase.{0,0,0,0}

theorem A_holds : A :=
  ⟨@Morse.ricci_eq_sum, @Morse.ricci_comm, @Morse.curvOp_self, @Morse.ricci_eq_sum_erase⟩

/-! ## `B ⇒ A`: A is provable outright

The four statements of A are short linear algebra on top of the project's curvature tensor; they
are re-proved here inline (from `LinearMap.trace_eq_sum_inner` and the pair symmetry of Lemma 9.3,
`Morse.isCurvatureTensor_curvTensor`), without B. -/

namespace Outright

theorem ricci_eq_sum {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [FiniteDimensional ℝ Z] {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] {N : Set V}
    {hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N} {q : N} {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ (Morse.tangentSubspace hN q)) (U₁ U₂ : Morse.tangentSubspace hN q) :
    Morse.ricci hN q U₁ U₂ = ∑ i, ⟪Morse.curvOp hN q U₁ (b i) U₂, (b i : V)⟫ := by
  rw [Morse.ricci, LinearMap.trace_eq_sum_inner _ b]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [real_inner_comm, Submodule.coe_inner]
  rfl

theorem ricci_comm {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [FiniteDimensional ℝ Z] {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    [FiniteDimensional ℝ W] {N : Set V} {hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N} (q : N)
    (U₁ U₂ : Morse.tangentSubspace hN q) :
    Morse.ricci hN q U₁ U₂ = Morse.ricci hN q U₂ U₁ := by
  set b := stdOrthonormalBasis ℝ (Morse.tangentSubspace hN q)
  rw [ricci_eq_sum b, ricci_eq_sum b]
  refine Finset.sum_congr rfl fun i _ => ?_
  have := (Morse.isCurvatureTensor_curvTensor hN q).inner_comm_pairs U₁ (b i) U₂ (b i)
  rwa [Submodule.coe_inner, Submodule.coe_inner, Morse.coe_curvTensor_apply,
    Morse.coe_curvTensor_apply] at this

theorem curvOp_self {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] {N : Set V}
    {hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N} (q : N) (x : V) : Morse.curvOp hN q x x = 0 := by
  simp [Morse.curvOp]

theorem ricci_eq_sum_erase {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [FiniteDimensional ℝ Z] {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] {N : Set V}
    {hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N} {q : N} {ι : Type*} [Fintype ι]
    [DecidableEq ι] (b : OrthonormalBasis ι ℝ (Morse.tangentSubspace hN q)) (i₀ : ι) :
    Morse.ricci hN q (b i₀) (b i₀) =
      ∑ i ∈ Finset.univ.erase i₀, ⟪Morse.curvOp hN q (b i₀) (b i) (b i₀), (b i : V)⟫ := by
  rw [ricci_eq_sum b, ← Finset.add_sum_erase _ _ (Finset.mem_univ i₀), curvOp_self,
    zero_apply, inner_zero_left, zero_add]

end Outright

/-- `B ⇒ A`, by proving A outright (B is not used). -/
theorem B_to_A : B → A := fun _ =>
  ⟨@Outright.ricci_eq_sum, @Outright.ricci_comm, @Outright.curvOp_self,
    @Outright.ricci_eq_sum_erase⟩

#rt_check RoundTrip.V11_9.B_to_A [Morse.ricci_eq_sum, Morse.ricci_comm, Morse.curvOp_self, Morse.ricci_eq_sum_erase]
#rt_overlap RoundTrip.V11_9.B_to_A [Morse.ricci_eq_sum, Morse.ricci_comm, Morse.curvOp_self, Morse.ricci_eq_sum_erase]

/-! ## The embedded special case

`B_emb`: B on `M = ↥N` (`Bridge.Sub hN`, model `ℝⁿ`, induced metric, connected), `cov =
Bridge.conn`. Dictionary: the blind curvature `R(a, b)c` (choice function over `IsCurvVal`) is
`L_x(curvOp(Da, Db, Dc))` (`Emb.curvR_eq`, from Items/V11_24.lean), so the blind linear map
`W ↦ R(U₁, W)U₂` of `ℝⁿ` is `eT⁻¹ ∘ (W ↦ R(U₁', W)U₂') ∘ eT` and the blind Ricci tensor is
`Morse.ricci` (`Emb.ricci_eq2`, trace invariant under conjugation); a blind orthonormal family of
`n` vectors becomes an orthonormal basis of `T_xN`. -/

namespace Emb

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open RoundTrip.Bridge

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] {n : ℕ} {N : Set V}
  {hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Bridge.Rn n) W N}

/-- The coordinate isomorphism `ℝⁿ ≃ T_xN`, `z ↦ D_x z`. -/
noncomputable def eT (x : Bridge.Sub hN) : Bridge.Rn n ≃ₗ[ℝ] Morse.tangentSubspace hN x :=
  LinearEquiv.ofBijective
    ((D hN x : Bridge.Rn n →ₗ[ℝ] V).codRestrict (Morse.tangentSubspace hN x) (D_mem x))
    ⟨fun _ _ h => D_injective x (congrArg Subtype.val h),
      fun v => ⟨L hN x v, Subtype.ext (D_L v.2)⟩⟩

/-- **Dictionary: curvature values.** -/
theorem curvR_eq (x : Bridge.Sub hN) (a b c : TangentSpace 𝓘(ℝ, Bridge.Rn n) x) :
    curvR (Bridge.conn (hN := hN)) x a b c =
      L hN x (Morse.curvOp hN x (D hN x a) (D hN x b) (D hN x c)) := by
  have hr : ∀ r, IsCurvVal (Bridge.conn (hN := hN)) x a b c r ↔
      D hN x r = Morse.curvOp hN x (D hN x a) (D hN x b) (D hN x c) := fun r => by
    have h := Bridge.isCurvVal_iff x a b c r
    have e : Morse.curvR hN (incl hN x) (D hN x a) (D hN x b) (D hN x c) =
        Morse.curvOp hN x (D hN x a) (D hN x b) (D hN x c) := Morse.curvR_of_mem hN x.2 _ _ _
    rw [e] at h
    exact h
  have hmem : Morse.curvOp hN x (D hN x a) (D hN x b) (D hN x c) ∈ Morse.tangentSubspace hN x :=
    Morse.curvOp_mem hN (D_mem x a) (D_mem x b) (D_mem x c)
  have hex : ∃ r, IsCurvVal (Bridge.conn (hN := hN)) x a b c r :=
    ⟨L hN x _, (hr _).2 (D_L hmem)⟩
  unfold curvR
  rw [dif_pos hex]
  apply D_injective x
  rw [(hr _).1 hex.choose_spec, D_L hmem]

theorem coe_eT (x : Bridge.Sub hN) (z : Bridge.Rn n) : (eT x z : V) = D hN x z := rfl

/-- The blind linear map `W ↦ R(U₁, W)U₂` of `ℝⁿ`, as a conjugate of the project's. -/
noncomputable def curvMap (x : Bridge.Sub hN) (U₁ U₂ : TangentSpace 𝓘(ℝ, Bridge.Rn n) x) :
    Bridge.Rn n →ₗ[ℝ] Bridge.Rn n :=
  (eT x).symm.conj ((Morse.curvTensor hN x (eT x U₁)).flip (eT x U₂))

theorem curvMap_apply (x : Bridge.Sub hN) (U₁ U₂ : TangentSpace 𝓘(ℝ, Bridge.Rn n) x)
    (W' : Bridge.Rn n) : curvMap x U₁ U₂ W' = curvR (Bridge.conn (hN := hN)) x U₁ W' U₂ := by
  have hmem : Morse.curvOp hN x (D hN x U₁) (D hN x W') (D hN x U₂) ∈
      Morse.tangentSubspace hN x :=
    Morse.curvOp_mem hN (D_mem x U₁) (D_mem x W') (D_mem x U₂)
  have h1 : curvMap x U₁ U₂ W' =
      (eT x).symm ((Morse.curvTensor hN x (eT x U₁)).flip (eT x U₂) (eT x W')) := rfl
  have h2 : (eT x).symm ((Morse.curvTensor hN x (eT x U₁)).flip (eT x U₂) (eT x W')) =
      L hN x (Morse.curvOp hN x (D hN x U₁) (D hN x W') (D hN x U₂)) := by
    apply (eT x).injective
    rw [LinearEquiv.apply_symm_apply]
    apply Subtype.ext
    show Morse.curvOp hN x (D hN x U₁) (D hN x W') (D hN x U₂) = D hN x (L hN x _)
    exact (D_L hmem).symm
  exact h1.trans (h2.trans (curvR_eq x U₁ W' U₂).symm)

/-- **Dictionary: the Ricci tensor.** For the induced connection, the blind `K(U₁, U₂)` is the
project's `Morse.ricci` at `D_x U₁, D_x U₂`. -/
theorem ricci_eq2 (x : Bridge.Sub hN) (U₁ U₂ : TangentSpace 𝓘(ℝ, Bridge.Rn n) x) :
    ricci (Bridge.conn (hN := hN)) x U₁ U₂ = Morse.ricci hN x (eT x U₁) (eT x U₂) := by
  have hex : ∃ L' : Bridge.Rn n →ₗ[ℝ] Bridge.Rn n, ∀ W' : Bridge.Rn n,
      L' W' = curvR (Bridge.conn (hN := hN)) x U₁ W' U₂ := ⟨_, curvMap_apply x U₁ U₂⟩
  have hch : hex.choose = curvMap x U₁ U₂ :=
    LinearMap.ext fun W' => (hex.choose_spec W').trans (curvMap_apply x U₁ U₂ W').symm
  unfold ricci
  rw [dif_pos hex, hch, curvMap, LinearMap.trace_conj']
  rfl

theorem finrank_tangent (x : Bridge.Sub hN) : finrank ℝ (Morse.tangentSubspace hN x) = n := by
  have := Morse.finrank_tanAt hN x.2
  rwa [Morse.tanAt_of_mem hN x.2, finrank_euclideanSpace_fin] at this

/-- Blind curvature values, read in `V`. -/
theorem D_of_isCurvVal {x : Bridge.Sub hN} {a b c r : TangentSpace 𝓘(ℝ, Bridge.Rn n) x}
    (h : IsCurvVal (Bridge.conn (hN := hN)) x a b c r) :
    D hN x r = Morse.curvOp hN x (D hN x a) (D hN x b) (D hN x c) := by
  rw [(Bridge.isCurvVal_iff x a b c r).1 h]
  exact Morse.curvR_of_mem hN x.2 _ _ _

end Emb

open Bundle in
/-- B on embedded manifolds: `M = ↥N` (model `ℝⁿ`, induced metric, connected), `cov = Bridge.conn`. -/
def B_emb : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (W : Type) [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] (n : ℕ)
    (N : Set V) (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N)
    [ConnectedSpace (Bridge.Sub hN)], ∀ p : Bridge.Sub hN,
    (∀ U₁ U₂ : TangentSpace 𝓘(ℝ, Rn n) p, ∃ L : Rn n →ₗ[ℝ] Rn n, ∀ W : Rn n,
      L W = curvR (Bridge.conn (hN := hN)) p U₁ W U₂) ∧
    (∀ (a : ℝ) (U U' V : TangentSpace 𝓘(ℝ, Rn n) p),
      ricci (Bridge.conn (hN := hN)) p (a • U + U') V =
        a * ricci (Bridge.conn (hN := hN)) p U V + ricci (Bridge.conn (hN := hN)) p U' V ∧
      ricci (Bridge.conn (hN := hN)) p V (a • U + U') =
        a * ricci (Bridge.conn (hN := hN)) p V U + ricci (Bridge.conn (hN := hN)) p V U') ∧
    (∀ U₁ U₂ : TangentSpace 𝓘(ℝ, Rn n) p,
      ricci (Bridge.conn (hN := hN)) p U₁ U₂ = ricci (Bridge.conn (hN := hN)) p U₂ U₁) ∧
    (∀ (hn : 0 < n) (U : Fin n → TangentSpace 𝓘(ℝ, Rn n) p), Orthonormal ℝ U →
      (∀ r : TangentSpace 𝓘(ℝ, Rn n) p,
        IsCurvVal (Bridge.conn (hN := hN)) p (U (lastIdx n hn)) (U (lastIdx n hn))
          (U (lastIdx n hn)) r →
        inner ℝ r (U (lastIdx n hn)) = 0) ∧
      ∀ r : Fin n → TangentSpace 𝓘(ℝ, Rn n) p,
        (∀ i, IsCurvVal (Bridge.conn (hN := hN)) p (U (lastIdx n hn)) (U i) (U (lastIdx n hn))
          (r i)) →
        ricci (Bridge.conn (hN := hN)) p (U (lastIdx n hn)) (U (lastIdx n hn)) =
          ∑ i ∈ (Finset.univ : Finset (Fin n)).filter (fun i => i ≠ lastIdx n hn),
            inner ℝ (r i) (U i))

/-- `B_emb` is a special case of B (the induced connection is Levi-Civita, `Bridge.conn_isLC`). -/
theorem B_to_B_emb : B → B_emb := fun hB _ _ _ _ _ _ _ _ n _ hN _ p =>
  hB n (Bridge.Sub hN) (Bridge.conn (hN := hN)) Bridge.conn_isLC p

open Emb Bridge Bundle in
/-- **A implies B on embedded manifolds** (uses A's `ricci_eq_sum` for bilinearity, `ricci_comm`
for symmetry, `curvOp_self` for the vanishing diagonal term and `ricci_eq_sum_erase` for the
Assertion). -/
theorem A_to_B_emb : A → B_emb := by
  intro hA V _ _ _ W _ _ _ n N hN _ p
  obtain ⟨hsum, hcomm, hself, herase⟩ := hA
  -- bilinearity of the project's Ricci tensor (a trace of a bilinear expression)
  have hlin1 : ∀ (a : ℝ) (U U' V' : Morse.tangentSubspace hN p),
      Morse.ricci hN p (a • U + U') V' = a * Morse.ricci hN p U V' + Morse.ricci hN p U' V' := by
    intro a U U' V'
    have e : (Morse.curvTensor hN p (a • U + U')).flip V' =
        a • (Morse.curvTensor hN p U).flip V' + (Morse.curvTensor hN p U').flip V' := by
      ext W'
      simp
    unfold Morse.ricci
    rw [e, map_add, map_smul, smul_eq_mul]
  have hlin2 : ∀ (a : ℝ) (U U' V' : Morse.tangentSubspace hN p),
      Morse.ricci hN p V' (a • U + U') = a * Morse.ricci hN p V' U + Morse.ricci hN p V' U' := by
    intro a U U' V'
    unfold Morse.ricci
    rw [map_add, map_smul, map_add, map_smul, smul_eq_mul]
  have heT_add : ∀ (a : ℝ) (U U' : TangentSpace 𝓘(ℝ, Rn n) p),
      eT p (a • U + U') = a • eT p U + eT p U' := fun a U U' =>
    ((eT p).map_add (a • U) U').trans (congrArg (· + eT p U') ((eT p).map_smul a U))
  refine ⟨fun U₁ U₂ => ⟨curvMap p U₁ U₂, curvMap_apply p U₁ U₂⟩, fun a U U' V' => ⟨?_, ?_⟩,
    fun U₁ U₂ => ?_, fun hn U hU => ⟨fun r hr => ?_, fun r hr => ?_⟩⟩
  · rw [ricci_eq2, ricci_eq2, ricci_eq2, heT_add, hlin1]
  · rw [ricci_eq2, ricci_eq2, ricci_eq2, heT_add, hlin2]
  · rw [ricci_eq2, ricci_eq2]
    exact hcomm (hN := hN) (show N from p) _ _
  · -- the diagonal term `⟨R(Uₙ, Uₙ)Uₙ, Uₙ⟩` vanishes
    have h := D_of_isCurvVal hr
    rw [hself (hN := hN) (show N from p), zero_apply] at h
    show ⟪D hN p r, D hN p (U (lastIdx n hn))⟫ = 0
    rw [h, inner_zero_left]
  · -- the Assertion, in the orthonormal basis `eT p ∘ U` of `T_pN`
    set b' : Fin n → Morse.tangentSubspace hN p := fun i => eT p (U i) with hb'
    have hon : Orthonormal ℝ b' := by
      rw [orthonormal_iff_ite] at hU ⊢
      intro i j
      exact hU i j
    have hcard : Fintype.card (Fin n) = finrank ℝ (Morse.tangentSubspace hN p) := by
      rw [Fintype.card_fin, finrank_tangent]
    set b := OrthonormalBasis.mk hon
      (hon.linearIndependent.span_eq_top_of_card_eq_finrank' hcard).ge with hb
    have hbi : ∀ i, b i = eT p (U i) := fun i => by
      rw [hb, OrthonormalBasis.coe_mk]
    rw [ricci_eq2, ← hbi, herase (hN := hN) (q := (show N from p)) b, Finset.filter_ne']
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hbi, hbi]
    show ⟪Morse.curvOp hN p (D hN p (U (lastIdx n hn))) (D hN p (U i)) (D hN p (U (lastIdx n hn))),
      D hN p (U i)⟫ = ⟪D hN p (r i), D hN p (U i)⟫
    rw [D_of_isCurvVal (hr i)]

#rt_check RoundTrip.V11_9.A_to_B_emb [Morse.ricci_eq_sum, Morse.ricci_comm, Morse.curvOp_self, Morse.ricci_eq_sum_erase]
#rt_overlap RoundTrip.V11_9.A_to_B_emb [Morse.ricci_eq_sum, Morse.ricci_comm, Morse.curvOp_self, Morse.ricci_eq_sum_erase]

end RoundTrip.V11_9
