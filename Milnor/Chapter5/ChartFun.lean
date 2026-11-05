import Milnor.Chapter5.DegreeAt
import Milnor.Chapter2.WithBoundary

/-!
# Chart functions along a level set

Setting for Milnor's Lemma 1 (chapter 5): `f : M → N` smooth between manifolds without boundary
of dimensions `n + 1` and `n`, `y` a regular value.  At a point `m` of `f⁻¹(y)` the kernel of
`df_m` is a line.  A **chart function** at `m` is a real function `c`, smooth near `m`, whose
derivative does not vanish on that line; the pair `(f, c)` is then a local diffeomorphism at `m`
onto `N × ℝ`, and its sign relative to the orientations of `M` and `N × ℝ` is `±1`.

Two chart functions at `m` have signs whose product is the sign of `c'(v) c(v)` for any nonzero
`v` in the kernel; and the sign of `(f, c)` is locally constant in the point.  These are the
ingredients of the "the two ends of an arc have opposite signs" argument.
-/

open Set Module Filter Topology Function
open scoped ContDiff Manifold

noncomputable section

namespace Milnor

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G} [J.Boundaryless]
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N] {n : ℕ}

/-- The pair map `x ↦ (f x, c x)`. -/
def pairMap (f : M → N) (c : M → ℝ) : M → N × ℝ := fun x => (f x, c x)

theorem mfd_pairMap {f : M → N} {c : M → ℝ} {m : M} (hfm : MDifferentiableAt I J f m)
    (hcm : MDifferentiableAt I 𝓘(ℝ, ℝ) c m) :
    mfd I (J.prod 𝓘(ℝ, ℝ)) (pairMap f c) m = (mfd I J f m).prod (mfd I 𝓘(ℝ, ℝ) c m) :=
  HasMFDerivAt.mfd_eq ((hasMFDerivAt_mfd (I := I) (J := J) hfm).prodMk
    (hasMFDerivAt_mfd (I := I) (J := 𝓘(ℝ, ℝ)) hcm))

/-- A **chart function** at `m ∈ f⁻¹(y)`: smooth near `m`, with nonzero derivative on the
kernel line of `df_m`. -/
structure ChartFun (I : ModelWithCorners ℝ E H) (J : ModelWithCorners ℝ F G) (f : M → N) (m : M)
    where
  c : M → ℝ
  W : Set M
  open_W : IsOpen W
  mem_W : m ∈ W
  smooth : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ c W
  trans : ∀ v, mfd I J f m v = 0 → v ≠ 0 → mfd I 𝓘(ℝ, ℝ) c m v ≠ 0

/-- The kernel of a surjection `E → F` (`dim E = n + 1`, `dim F = n`) contains a nonzero vector. -/
theorem exists_ne_zero_of_surjective (hE : finrank ℝ E = n + 1) (hF : finrank ℝ F = n)
    {P : E →L[ℝ] F} (hP : Function.Surjective P) :
    ∃ v : E, P v = 0 ∧ v ≠ 0 := by
  have hker : LinearMap.ker (P : E →ₗ[ℝ] F) ≠ ⊥ := by
    intro hbot
    have h1 := LinearMap.finrank_range_add_finrank_ker (P : E →ₗ[ℝ] F)
    rw [hbot, finrank_bot, add_zero, LinearMap.range_eq_top.2 hP, finrank_top, hE, hF] at h1
    omega
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  exact ⟨v, LinearMap.mem_ker.1 hv, hv0⟩

/-- The kernel of such a surjection is a line: any two of its elements are proportional. -/
theorem exists_smul_eq_of_ker (hE : finrank ℝ E = n + 1) (hF : finrank ℝ F = n)
    {P : E →L[ℝ] F} (hP : Function.Surjective P) {v w : E}
    (hv : P v = 0) (hv0 : v ≠ 0) (hw : P w = 0) : ∃ a : ℝ, a • v = w := by
  have h1 := LinearMap.finrank_range_add_finrank_ker (P : E →ₗ[ℝ] F)
  rw [LinearMap.range_eq_top.2 hP, finrank_top, hE, hF] at h1
  have hk : finrank ℝ (LinearMap.ker (P : E →ₗ[ℝ] F)) = 1 := by omega
  obtain ⟨a, ha⟩ := (finrank_eq_one_iff_of_nonzero' (⟨v, LinearMap.mem_ker.2 hv⟩ :
    LinearMap.ker (P : E →ₗ[ℝ] F)) (fun h => hv0 (congrArg Subtype.val h))).1 hk
    ⟨w, LinearMap.mem_ker.2 hw⟩
  exact ⟨a, congrArg Subtype.val ha⟩

variable (hE : finrank ℝ E = n + 1) (hF : finrank ℝ F = n)
variable {f : M → N} (hf : ContMDiff I J ∞ f) {y : N} (hy : IsRegularValue I J f y)

namespace ChartFun

variable {m : M} (cf : ChartFun I J f m)

include hE hF hf hy in
/-- The pair map `(f, c)` is a submersion, hence a local diffeomorphism, at `m`. -/
theorem isRegularPoint (hm : f m = y) : IsRegularPoint I (J.prod 𝓘(ℝ, ℝ)) (pairMap f cf.c) m := by
  have hsurj : Function.Surjective (mfd I J f m) := hy m hm
  obtain ⟨v₀, hv₀, hv₀0⟩ := exists_ne_zero_of_surjective hE hF hsurj
  have hcv := cf.trans v₀ hv₀ hv₀0
  show Function.Surjective (mfd I (J.prod 𝓘(ℝ, ℝ)) (pairMap f cf.c) m)
  rw [mfd_pairMap (hf.mdifferentiableAt (by simp)) ((cf.smooth.contMDiffAt
    (cf.open_W.mem_nhds cf.mem_W)).mdifferentiableAt (by simp))]
  rintro ⟨w, s⟩
  obtain ⟨u, hu⟩ := hsurj w
  refine ⟨u + ((s - mfd I 𝓘(ℝ, ℝ) cf.c m u) / mfd I 𝓘(ℝ, ℝ) cf.c m v₀) • v₀, ?_⟩
  rw [ContinuousLinearMap.prod_apply]
  ext
  · simp [hu, hv₀]
  · simp only [map_add, map_smul, smul_eq_mul]
    field_simp
    ring

/-- The sign of the pair map `(f, c)` at `m`, relative to `oM` and the product orientation of
`N × ℝ`. -/
def sign (oM : Orient I M (n + 1)) (oN : Orient J N n) : ℤ :=
  signAt oM (oN.prodReal hF) (pairMap f cf.c) m

include hE hf hy in
theorem sign_ne_zero (oM : Orient I M (n + 1)) (oN : Orient J N n) (hm : f m = y) :
    cf.sign hF oM oN ≠ 0 :=
  (cf.isRegularPoint hE hF hf hy hm).signAt_ne_zero hE (finrank_prod_real hF) oM (oN.prodReal hF)

include hE hf hy in
/-- **Chart independence.** For two chart functions at `m`, the product of the signs is the sign
of `c(v) c'(v)` for any nonzero kernel vector `v`. -/
theorem sign_mul_sign (oM : Orient I M (n + 1)) (oN : Orient J N n) (hm : f m = y)
    (cf' : ChartFun I J f m) {v : E} (hv : mfd I J f m v = 0) (hv0 : v ≠ 0) :
    cf.sign hF oM oN * cf'.sign hF oM oN =
      sgn (mfd I 𝓘(ℝ, ℝ) cf.c m v * mfd I 𝓘(ℝ, ℝ) cf'.c m v) := by
  have hsurj : Function.Surjective (mfd I J f m) := hy m hm
  have hfm : MDifferentiableAt I J f m := hf.mdifferentiableAt (by simp)
  have hcm : MDifferentiableAt I 𝓘(ℝ, ℝ) cf.c m :=
    (cf.smooth.contMDiffAt (cf.open_W.mem_nhds cf.mem_W)).mdifferentiableAt (by simp)
  have hcm' : MDifferentiableAt I 𝓘(ℝ, ℝ) cf'.c m :=
    (cf'.smooth.contMDiffAt (cf'.open_W.mem_nhds cf'.mem_W)).mdifferentiableAt (by simp)
  have h := orSign_prodReal_mul hE hF (oM.or m) (oN.or (f m))
    (mfd I (J.prod 𝓘(ℝ, ℝ)) (pairMap f cf.c) m) (mfd I (J.prod 𝓘(ℝ, ℝ)) (pairMap f cf'.c) m)
    (mfd I J f m) (fun w => by rw [mfd_pairMap hfm hcm]; rfl)
    (fun w => by rw [mfd_pairMap hfm hcm']; rfl) hsurj hv0 hv
  have e1 : ∀ w, (mfd I (J.prod 𝓘(ℝ, ℝ)) (pairMap f cf.c) m w).2 = mfd I 𝓘(ℝ, ℝ) cf.c m w :=
    fun w => by rw [mfd_pairMap hfm hcm]; rfl
  have e2 : ∀ w, (mfd I (J.prod 𝓘(ℝ, ℝ)) (pairMap f cf'.c) m w).2 = mfd I 𝓘(ℝ, ℝ) cf'.c m w :=
    fun w => by rw [mfd_pairMap hfm hcm']; rfl
  rw [e1, e2] at h
  exact h

include hE hf hy in
/-- The sign of `(f, c)` is locally constant near `m`. -/
theorem eventually_signAt_eq (oM : Orient I M (n + 1)) (oN : Orient J N n) (hm : f m = y) :
    ∀ᶠ m' in 𝓝 m, signAt oM (oN.prodReal hF) (pairMap f cf.c) m' = cf.sign hF oM oN :=
  eventually_signAt_eq_of_contMDiffOn hE (finrank_prod_real hF) oM (oN.prodReal hF) cf.open_W
    (hf.contMDiffOn.prodMk cf.smooth) cf.mem_W (cf.isRegularPoint hE hF hf hy hm)

include hE hF in
/-- A chart function at `m` is a chart function at any `m' ∈ W` where `(f, c)` is regular. -/
def move (m' : M) (hW : m' ∈ cf.W) (hf' : MDifferentiableAt I J f m')
    (hreg : IsRegularPoint I (J.prod 𝓘(ℝ, ℝ)) (pairMap f cf.c) m') : ChartFun I J f m' where
  c := cf.c
  W := cf.W
  open_W := cf.open_W
  mem_W := hW
  smooth := cf.smooth
  trans := by
    intro v hv hv0 hcv
    have hcm : MDifferentiableAt I 𝓘(ℝ, ℝ) cf.c m' :=
      (cf.smooth.contMDiffAt (cf.open_W.mem_nhds hW)).mdifferentiableAt (by simp)
    have hsurj : Function.Surjective (mfd I (J.prod 𝓘(ℝ, ℝ)) (pairMap f cf.c) m') := hreg
    have hinj : Function.Injective (mfd I (J.prod 𝓘(ℝ, ℝ)) (pairMap f cf.c) m') :=
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
        (f := (mfd I (J.prod 𝓘(ℝ, ℝ)) (pairMap f cf.c) m' : E →ₗ[ℝ] F × ℝ))
        (hE.trans (finrank_prod_real hF).symm)).2 hsurj
    apply hv0
    apply hinj
    rw [mfd_pairMap hf' hcm, map_zero, ContinuousLinearMap.prod_apply, hv, hcv]
    rfl

@[simp] theorem move_c (m' : M) (hW : m' ∈ cf.W) (hf' : MDifferentiableAt I J f m')
    (hreg : IsRegularPoint I (J.prod 𝓘(ℝ, ℝ)) (pairMap f cf.c) m') :
    (cf.move hE hF m' hW hf' hreg).c = cf.c := rfl

include hE hF hf hy in
/-- Near `m`, every point of `W` where `(f, c)` is regular: eventually true. -/
theorem eventually_move (oM : Orient I M (n + 1)) (oN : Orient J N n) (hm : f m = y) :
    ∀ᶠ m' in 𝓝 m, m' ∈ cf.W ∧ IsRegularPoint I (J.prod 𝓘(ℝ, ℝ)) (pairMap f cf.c) m' := by
  filter_upwards [cf.open_W.mem_nhds cf.mem_W, cf.eventually_signAt_eq hE hF hf hy oM oN hm]
    with m' hW hs
  refine ⟨hW, ?_⟩
  have hne : signAt oM (oN.prodReal hF) (pairMap f cf.c) m' ≠ 0 := by
    rw [hs]; exact cf.sign_ne_zero hE hF hf hy oM oN hm
  exact ((signAt_ne_zero_iff hE (finrank_prod_real hF) _ _ _ _).1 hne).2

end ChartFun

include hE hF hf hy in
/-- **Existence of chart functions** at every point of `f⁻¹(y)`: a suitable coordinate of the
chart at `m`. -/
theorem exists_chartFun (m : M) (hm : f m = y) : Nonempty (ChartFun I J f m) := by
  have hsurj : Function.Surjective (mfd I J f m) := hy m hm
  obtain ⟨v₀, hv₀, hv₀0⟩ := exists_ne_zero_of_surjective hE hF hsurj
  -- the chart at `m` is a local diffeomorphism, so its derivative is injective
  have hloc : IsLocalDiffeomorphAt I 𝓘(ℝ, E) ∞ (extChartAt I m) m :=
    ⟨PartialDiffeomorph.ofExtChartAt I m, mem_extChartAt_source m, fun _ _ => rfl⟩
  have hDe : Function.Injective (mfd I 𝓘(ℝ, E) (extChartAt I m) m) := by
    have := hloc.mfderivToContinuousLinearEquiv_coe (by simp : (∞ : WithTop ℕ∞) ≠ 0)
    show Function.Injective (mfderiv I 𝓘(ℝ, E) (extChartAt I m) m)
    rw [← this]
    exact (hloc.mfderivToContinuousLinearEquiv (by simp)).injective
  set w := mfd I 𝓘(ℝ, E) (extChartAt I m) m v₀ with hw
  have hw0 : w ≠ 0 := fun h => hv₀0 (hDe (by rw [← hw, h, map_zero]))
  -- a coordinate functional not vanishing on `w`
  let e := finBasisOfFinrankEq ℝ E hE
  have hcoord : ∃ i, e.repr w i ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hw0 (e.repr.injective (Finsupp.ext fun i => by simp [hcon i]))
  obtain ⟨i, hi⟩ := hcoord
  let lam : E →L[ℝ] ℝ := LinearMap.toContinuousLinearMap (e.coord i)
  have hDe' := hasMFDerivAt_mfd (I := I) (J := 𝓘(ℝ, E)) ((contMDiffAt_extChartAt' (I := I)
    (n := ∞) (x := m) (by rw [← extChartAt_source I]; exact mem_extChartAt_source m)
    ).mdifferentiableAt (by simp))
  have hlam : HasMFDerivAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) lam (extChartAt I m m) lam :=
    lam.hasFDerivAt.hasMFDerivAt
  have hc := HasMFDerivAt.mfd_eq (hlam.comp m hDe')
  refine ⟨⟨fun x => lam (extChartAt I m x), (extChartAt I m).source, isOpen_extChartAt_source m,
    mem_extChartAt_source m, ?_, ?_⟩⟩
  · have h1 : ContMDiffOn I 𝓘(ℝ, E) ∞ (extChartAt I m) (extChartAt I m).source := by
      rw [extChartAt_source]; exact contMDiffOn_extChartAt
    exact lam.contMDiff.comp_contMDiffOn h1
  · intro v hv hv0
    obtain ⟨a, ha⟩ := exists_smul_eq_of_ker hE hF hsurj hv₀ hv₀0 hv
    have ha0 : a ≠ 0 := by rintro rfl; simp at ha; exact hv0 ha.symm
    show mfd I 𝓘(ℝ, ℝ) (lam ∘ extChartAt I m) m v ≠ 0
    rw [hc]
    show lam (mfd I 𝓘(ℝ, E) (extChartAt I m) m v) ≠ 0
    rw [← ha, map_smul, map_smul, ← hw]
    simp only [smul_eq_mul, ne_eq, mul_eq_zero, not_or]
    refine ⟨ha0, ?_⟩
    simpa [lam] using hi

end Milnor
