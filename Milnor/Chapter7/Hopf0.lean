import Milnor.Chapter7.ThmAconv

/-!
# Framed 0-manifolds: finiteness, the sign of a framed point, the signed count (Milnor §7, p. 50)

For `n = 0` and `p = m` a framed submanifold of `M` is a finite set of points, each carrying a
basis of `T_x M`.  Relative to an orientation of `M` each point has a sign `±1`, and the
*signed count* is the sum of the signs.  For the Pontryagin manifold of `f : M → Sᵐ` at a
regular value `y` with a positive basis the sign of `x` is the sign of `df_x`, so the signed
count is the degree of `f`.
-/

open Set Filter Topology Function Module Metric
open scoped ContDiff Manifold RealInnerProductSpace Classical

noncomputable section

namespace Milnor

open Sphere

/-- A compact `0`-dimensional slice submanifold is finite. -/
theorem IsSliceSubmanifold.finite_of_dim_zero {E H : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {X : Type*}
    [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ∞ X] {W : Type*} [NormedAddCommGroup W]
    [NormedSpace ℝ W] {S : Set X}
    (hS : IsSliceSubmanifold I (EuclideanSpace ℝ (Fin 0)) W S) (hc : IsCompact S) : S.Finite := by
  classical
  -- around each point of `S` a slice chart whose source meets `S` only in that point
  have key : ∀ x ∈ S, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ S ∩ U ⊆ {x} := by
    intro x hx
    obtain ⟨σ, hxσ⟩ := hS x hx
    refine ⟨σ.φ.source, σ.φ.open_source, hxσ, ?_⟩
    rintro q ⟨hqS, hqσ⟩
    have h1 : (σ.φ q).2 = 0 := (σ.slice q hqσ).1 hqS
    have h2 : (σ.φ x).2 = 0 := (σ.slice x hxσ).1 hx
    have h3 : σ.φ q = σ.φ x := by
      refine Prod.ext ?_ (by rw [h1, h2])
      ext i; exact i.elim0
    exact σ.φ.toPartialEquiv.injOn hqσ hxσ h3
  choose U hUo hxU hSU using key
  let U' : X → Set X := fun x => if h : x ∈ S then U x h else univ
  have hU' : ∀ x ∈ S, U' x ∈ 𝓝 x := fun x hx => by
    simp only [U', dif_pos hx]; exact (hUo x hx).mem_nhds (hxU x hx)
  obtain ⟨t, htS, hcov⟩ := hc.elim_nhds_subcover U' hU'
  refine (t.finite_toSet).subset ?_
  intro y hy
  obtain ⟨x, hxt, hyU⟩ := Set.mem_iUnion₂.1 (hcov hy)
  have hxS := htS x hxt
  simp only [U', dif_pos hxS] at hyU
  have : y = x := hSU x hxS ⟨hy, hyU⟩
  rw [this]; exact hxt

namespace Framed

variable {K m w : ℕ} {M : Set (EuclideanSpace ℝ (Fin (K + 1)))}
  (hM : IsSliceSubmanifold 𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1))) (EuclideanSpace ℝ (Fin m))
    (EuclideanSpace ℝ (Fin w)) M) (hMc : IsCompact M) (hne : M.Nonempty)

/-- A framed `0`-manifold has finitely many points. -/
theorem FramedSub.finite_N (F : FramedSub hM 0 p) : F.N.Finite :=
  letI := hM.chartedSpace
  haveI := hM.isManifold
  F.hN.finite_of_dim_zero F.compact

/-- The tangent space of a `0`-dimensional submanifold is zero. -/
theorem tangentN_eq_bot_of_dim_zero {N : Set M} (hN : letI := hM.chartedSpace; haveI := hM.isManifold;
      IsSliceSubmanifold 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) (EuclideanSpace ℝ (Fin 0))
        (EuclideanSpace ℝ (Fin p)) N) (x : N) : tangentN hM hN x = ⊥ := by
  letI := hM.chartedSpace
  haveI := hM.isManifold
  letI := hN.chartedSpace
  unfold tangentN
  rw [LinearMap.range_eq_bot]
  apply LinearMap.ext
  intro v
  have hv : v = 0 := by ext i; exact i.elim0
  rw [hv, map_zero]; rfl

/-! ### Signs -/

/-- The standard orientation of `ℝᵐ`. -/
def stdOr (m : ℕ) : Orientation ℝ (EuclideanSpace ℝ (Fin m)) (Fin m) :=
  (EuclideanSpace.basisFun (Fin m) ℝ).toBasis.orientation

/-- The chart coordinates of an ambient vector tangent to `M` at `x`: the (unique) `w ∈ ℝᵐ` with
`dι_x w = v`, where `ι : M → ℝᴷ⁺¹` is the inclusion. -/
def chartCoord (x : M) (v : EuclideanSpace ℝ (Fin (K + 1))) : EuclideanSpace ℝ (Fin m) :=
  letI := hM.chartedSpace
  haveI := hM.isManifold
  Function.invFun (mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1)))
    (Subtype.val : M → EuclideanSpace ℝ (Fin (K + 1))) x) v

theorem mfd_val_chartCoord {x : M} {v : EuclideanSpace ℝ (Fin (K + 1))} (hv : v ∈ tangentM hM x) :
    letI := hM.chartedSpace; haveI := hM.isManifold;
    mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1)))
      (Subtype.val : M → EuclideanSpace ℝ (Fin (K + 1))) x (chartCoord hM x v) = v := by
  letI := hM.chartedSpace
  haveI := hM.isManifold
  obtain ⟨a, ha⟩ := (LinearMap.mem_range).1 hv
  exact Function.invFun_eq ⟨a, ha⟩

/-- The sign of a frame `v` (of `m` ambient vectors tangent to `M`) at `x`, relative to the
orientation `oM`: the sign of the linear map `ℝᵐ → ℝᵐ` sending the standard basis to the chart
coordinates of the frame. -/
def frameSign (oM : letI := hM.chartedSpace; Orient 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) M m)
    (v : Fin m → EuclideanSpace ℝ (Fin (K + 1))) (x : M) : ℤ :=
  letI := hM.chartedSpace
  orSign (stdOr m) (oM.or x) (basisCLM (fun i => chartCoord hM x (v i)))

/-- The signed count of a framed `0`-manifold. -/
def count (oM : letI := hM.chartedSpace; Orient 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) M m)
    (F : FramedSub hM 0 m) : ℤ :=
  ∑ᶠ x : F.N, frameSign hM oM (fun i => F.v i x) x.1

theorem finrank_E : finrank ℝ (EuclideanSpace ℝ (Fin m)) = m := finrank_euclideanSpace_fin

/-! ### The inclusion `M ↪ ℝᴷ⁺¹` and the chart coordinates

Three small facts used throughout the local theory of the chapter: the standard tuple of `ℝᵐ`
is a frame, the derivative of the inclusion is injective, and `chartCoord` inverts it. -/

/-- The standard basis tuple of `ℝᵐ` is linearly independent. -/
theorem linearIndependent_single :
    LinearIndependent ℝ (fun i : Fin m => EuclideanSpace.single i (1 : ℝ)) := by
  have := (EuclideanSpace.basisFun (Fin m) ℝ).toBasis.linearIndependent
  have h3 : ⇑((EuclideanSpace.basisFun (Fin m) ℝ).toBasis) =
      fun i : Fin m => EuclideanSpace.single i (1 : ℝ) := by
    funext i; simp
  rw [h3] at this; exact this

/-- The derivative at `x` of the inclusion `M ↪ ℝᴷ⁺¹` is injective: its range is the tangent space,
of dimension `m`, and its source `ℝᵐ` also has dimension `m`. -/
theorem injective_mfd_val (x : M) :
    letI := hM.chartedSpace; haveI := hM.isManifold;
    Function.Injective (mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1)))
      (Subtype.val : M → EuclideanSpace ℝ (Fin (K + 1))) x) := by
  letI := hM.chartedSpace
  haveI := hM.isManifold
  set L : EuclideanSpace ℝ (Fin m) →ₗ[ℝ] EuclideanSpace ℝ (Fin (K + 1)) :=
    ((mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1)))
      (Subtype.val : M → EuclideanSpace ℝ (Fin (K + 1))) x :
        EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin (K + 1))) :
        EuclideanSpace ℝ (Fin m) →ₗ[ℝ] EuclideanSpace ℝ (Fin (K + 1))) with hL
  have h1 := LinearMap.finrank_range_add_finrank_ker L
  have h2 : finrank ℝ (LinearMap.range L) = m := finrank_tangentM hM x
  rw [h2, finrank_E] at h1
  have h3 : finrank ℝ (LinearMap.ker L) = 0 := by omega
  have h4 : LinearMap.ker L = ⊥ := Submodule.finrank_eq_zero.1 h3
  exact LinearMap.ker_eq_bot.1 h4

/-- The chart coordinates of `dι_x u` are `u`. -/
theorem chartCoord_mfd_val (x : M) (u : EuclideanSpace ℝ (Fin m)) :
    letI := hM.chartedSpace; haveI := hM.isManifold;
    chartCoord hM x (mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1)))
      (Subtype.val : M → EuclideanSpace ℝ (Fin (K + 1))) x u) = u :=
  Function.leftInverse_invFun (injective_mfd_val hM x) u

/-- A positive basis `e` of `ℝᵐ` has sign `1` against the standard orientation. -/
theorem orSign_stdOr_basisCLM (e : Basis (Fin m) ℝ (EuclideanSpace ℝ (Fin m))) :
    orSign (stdOr m) e.orientation (basisCLM e) = 1 := by
  classical
  have hstd : rayOfNeZero ℝ _ (EuclideanSpace.basisFun (Fin m) ℝ).toBasis.det_ne_zero = stdOr m := rfl
  have he : rayOfNeZero ℝ _ e.det_ne_zero = e.orientation := rfl
  rw [orSign_eq_sgn _ _ hstd he (c := 1) ?_]
  · exact sgn_one
  ext v
  simp only [AlternatingMap.compLinearMap_apply, one_smul, ContinuousLinearMap.coe_coe]
  rw [Basis.det_apply, Basis.det_apply]
  congr 1
  ext i j
  simp only [Basis.toMatrix_apply, basisCLM_apply, map_sum, map_smul, Basis.repr_self,
    Finsupp.coe_finsetSum, Finsupp.coe_smul, Finset.sum_apply, Pi.smul_apply,
    Finsupp.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true, OrthonormalBasis.coe_toBasis_repr_apply,
    EuclideanSpace.basisFun_repr]

theorem frameSign_ne_zero (oM : letI := hM.chartedSpace; Orient 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) M m)
    {v : Fin m → EuclideanSpace ℝ (Fin (K + 1))} {x : M} (hT : ∀ i, v i ∈ tangentM hM x)
    (hv : LinearIndependent ℝ v) : frameSign hM oM v x ≠ 0 := by
  letI := hM.chartedSpace
  haveI := hM.isManifold
  rw [frameSign, orSign_ne_zero_iff finrank_E finrank_E]
  -- the chart coordinates are independent, hence a basis (dimension count)
  have hind : LinearIndependent ℝ (fun i => chartCoord hM x (v i)) := by
    have hcomp : v = fun i => mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin m))
        𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1))) (Subtype.val : M → EuclideanSpace ℝ (Fin (K + 1))) x
        (chartCoord hM x (v i)) := by
      funext i; rw [mfd_val_chartCoord hM (hT i)]
    rw [hcomp] at hv
    exact LinearIndependent.of_comp _ hv
  exact basisCLM_bijective hind

/-! ### The bridge to the degree -/

variable {hM} in
theorem basisCLM_comp_eq {T : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m)}
    {a b : Fin m → EuclideanSpace ℝ (Fin m)} (h : ∀ i, T (a i) = b i) :
    T.comp (basisCLM a) = basisCLM b := by
  ext s
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, basisCLM_apply, map_sum,
    map_smul, h]

variable {n p : ℕ}

/-- **The sign of a point of a Pontryagin manifold is the sign of the derivative.** For a
positive basis `e` at `y`, the frame `f^* e` at `x ∈ f⁻¹(y)` has sign `signAt f x`. -/
theorem frameSign_pontryagin (oM : letI := hM.chartedSpace; Orient 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) M m)
    {f : M → Sph m}
    (hf : letI := hM.chartedSpace; haveI := hM.isManifold;
      ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) ∞ f)
    {y : Sph m}
    (hy : letI := hM.chartedSpace; haveI := hM.isManifold;
      IsRegularValue 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) f y)
    (e : Basis (Fin m) ℝ (EuclideanSpace ℝ (Fin m))) (he : e.orientation = (sphOr m).or y)
    (q : f ⁻¹' {y}) :
    letI := hM.chartedSpace; haveI := hM.isManifold;
    frameSign hM oM (fun i => pontV hM hMc hne f y e i q) q.1 = signAt oM (sphOr m) f q.1 := by
  letI := hM.chartedSpace
  haveI := hM.isManifold
  have hfq : f q.1 = y := q.2
  -- the chart derivative of `f` carries the chart coordinates of the frame to `e`
  have hsrc : f ⟨q.1.1, q.1.2⟩ ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) y).source := by
    rw [Subtype.coe_eta, hfq]; exact mem_extChartAt_source y
  have hcomp := At_comp_mfd_val hM hMc hne hf q.1.2 hsrc
  rw [Subtype.coe_eta, hfq, mfd_extChartAt_self, ContinuousLinearMap.id_comp] at hcomp
  have hD : ∀ i, mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) f q.1
      (chartCoord hM q.1 (pontV hM hMc hne f y e i q)) = e i := by
    intro i
    have h1 := congrArg (fun T => T (chartCoord hM q.1 (pontV hM hMc hne f y e i q))) hcomp
    simp only [ContinuousLinearMap.coe_comp, Function.comp_apply] at h1
    rw [mfd_val_chartCoord hM (pontV_tangent hM hMc hne hf hy e i q), At_pontV hM hMc hne hf hy] at h1
    exact h1.symm
  have hcompB := basisCLM_comp_eq (T := mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin m))
    𝓘(ℝ, EuclideanSpace ℝ (Fin m)) f q.1) hD
  have hmul := orSign_comp finrank_E finrank_E (stdOr m) (oM.or q.1) ((sphOr m).or (f q.1))
    (basisCLM (fun i => chartCoord hM q.1 (pontV hM hMc hne f y e i q)))
    (mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) f q.1)
  rw [hcompB, hfq, ← he, orSign_stdOr_basisCLM] at hmul
  -- `1 = signAt * frameSign` with both integers, so they agree
  unfold frameSign signAt
  rw [hfq, ← he]
  have h := hmul.symm
  rcases Int.eq_one_or_neg_one_of_mul_eq_one' h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2]
  · rw [h1, h2]

/-- **The signed count of the Pontryagin manifold is the degree.** -/
theorem count_pontryagin (hm : 0 < m)
    (oM : letI := hM.chartedSpace; Orient 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) M m)
    {f : M → Sph m}
    (hf : letI := hM.chartedSpace; haveI := hM.isManifold;
      ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) ∞ f)
    {y : Sph m}
    (hy : letI := hM.chartedSpace; haveI := hM.isManifold;
      IsRegularValue 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) f y)
    (e : Basis (Fin m) ℝ (EuclideanSpace ℝ (Fin m))) (he : e.orientation = (sphOr m).or y) :
    letI := hM.chartedSpace; haveI := hM.isManifold;
    count hM oM (pontryagin hM hMc hne hf hy (zero_add m) e e.linearIndependent) =
      deg oM (sphOr m) f := by
  letI := hM.chartedSpace
  haveI := hM.isManifold
  haveI : CompactSpace M := isCompact_iff_compactSpace.1 hMc
  haveI : PreconnectedSpace (Sph m) := preconnectedSpace hm
  rw [deg_eq finrank_E finrank_E oM (sphOr m) hf hy, degAt, count]
  simp only [pontryagin]
  rw [← finsum_subtype_eq_finsum_cond]
  exact finsum_congr fun q => frameSign_pontryagin hM hMc hne oM hf hy e he q

/-! ### Small helpers -/

theorem linearIndependent_chartCoord {v : Fin m → EuclideanSpace ℝ (Fin (K + 1))} {x : M}
    (hT : ∀ i, v i ∈ tangentM hM x) (hv : LinearIndependent ℝ v) :
    LinearIndependent ℝ (fun i => chartCoord hM x (v i)) := by
  letI := hM.chartedSpace
  haveI := hM.isManifold
  have hcomp : v = fun i => mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin m))
      𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1))) (Subtype.val : M → EuclideanSpace ℝ (Fin (K + 1))) x
      (chartCoord hM x (v i)) := by
    funext i; rw [mfd_val_chartCoord hM (hT i)]
  rw [hcomp] at hv
  exact LinearIndependent.of_comp _ hv

theorem basisCLM_single_eq_id :
    basisCLM (fun i : Fin m => EuclideanSpace.single i (1 : ℝ)) =
      ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin m)) := by
  refine ContinuousLinearMap.ext fun s => ?_
  rw [basisCLM_apply, ContinuousLinearMap.id_apply]
  refine (EuclideanSpace.basisFun (Fin m) ℝ).toBasis.ext_elem fun j => ?_
  simp [EuclideanSpace.single_apply, EuclideanSpace.basisFun_repr]

/-- `At f north x ∘ dι_x = df_x` (in the chart at `north`). -/
theorem At_apply_mfd_val {f : M → Sph p}
    (hf : letI := hM.chartedSpace; haveI := hM.isManifold;
      ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) ∞ f)
    {y : Sph p} {x : M} (hx : f x = y) (u : EuclideanSpace ℝ (Fin m)) :
    letI := hM.chartedSpace; haveI := hM.isManifold;
    At hM hMc hne f y x.1 (mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1)))
      (Subtype.val : M → EuclideanSpace ℝ (Fin (K + 1))) x u) =
      mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) f x u := by
  letI := hM.chartedSpace
  haveI := hM.isManifold
  have hsrc : f ⟨x.1, x.2⟩ ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) y).source := by
    rw [Subtype.coe_eta, hx]; exact mem_extChartAt_source y
  have hcomp := At_comp_mfd_val hM hMc hne hf x.2 hsrc
  rw [Subtype.coe_eta, hx, mfd_extChartAt_self, ContinuousLinearMap.id_comp] at hcomp
  have := congrArg (fun T => T u) hcomp
  simpa using this

end Framed

end Milnor
