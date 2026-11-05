import Morse
import RoundTrip.Check
import RoundTrip.Bridge
import RoundTrip.Blind.V7_3

open Set Filter Topology
open scoped ContDiff Manifold

namespace RoundTrip.V7_3

/-- The project's statement (universes instantiated at 0): For a slice submanifold `N ⊆ V` (`geodesicSpray`, `chartSpray` are definitions): the geodesic equation `γ'' = II(γ', γ')` (both directions), its first-order form on `TN ⊆ V × V` (integral curves of the spray `(x,v) ↦ (v, II_x(v,v))`), and in a slice chart `σ` the coordinate spray `(u,w) ↦ (w, −Γ(u)(w,w))` is smooth and its integral curves give geodesics. -/
def A : Prop :=
  type_of% @Morse.IsGeodesicOn.deriv_deriv_eq.{0,0,0} ∧
    type_of% @Morse.isGeodesicOn_of_deriv_deriv_eq.{0,0,0} ∧
    type_of% @Morse.isGeodesicOn_iff_hasDerivAt_geodesicSpray.{0,0,0} ∧
    type_of% @Morse.contDiffOn_chartSpray.{0,0,0} ∧
    type_of% @Morse.isGeodesicOn_chart.{0,0,0}

theorem A_holds : A := ⟨@Morse.IsGeodesicOn.deriv_deriv_eq, @Morse.isGeodesicOn_of_deriv_deriv_eq, @Morse.isGeodesicOn_iff_hasDerivAt_geodesicSpray, @Morse.contDiffOn_chartSpray, @Morse.isGeodesicOn_chart⟩

/-! ## The embedded special case

B is specialized to `M = ↥N` (`RoundTrip.Bridge.Sub hN`) for a slice submanifold `N ⊆ V` with
model `ℝⁿ`, the induced metric and the induced Levi-Civita connection `Bridge.conn` (`B_emb`;
`B_to_B_emb`). The charts `extChartAt p` of `↥N` are the slice charts `σ = Morse.sliceAt hN p`.

**Christoffel dictionary** (`Emb.sum_gam_eq_chartAcc`): the blind Christoffel symbols of
`Bridge.conn` in the chart at `p`, contracted with `w`, are A's `Morse.chartAcc σ u w`
(`Γ(u)(w, w) = dx_u⁺ d²x_u(w, w)`), so the blind coordinate equation is exactly the integral-curve
equation of A's `Morse.chartSpray σ`. With it and the Bridge's geodesic dictionary (`P γ'' = 0`),
`Emb.coord_expr` identifies the blind coordinate expression with the `k`-th coordinate of
`A(P γ'')`, so `B_emb` holds outright (`B_emb_holds`); `A_to_B_emb` is therefore vacuous. B_emb
does not give A back: A's ambient equation `γ'' = II(γ', γ')`, the spray on `TN` and the chart
statements for an arbitrary slice chart (B_emb only sees the charts `sliceAt hN p` of the manifold
structure) are not consequences of it. -/

namespace Emb

set_option linter.unusedSectionVars false

open RoundTrip.Bridge

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] {n : ℕ} {N : Set V}
  {hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N} {p x : Bridge.Sub hN}

/-- The chart inverts its parametrization: `A ∘ B = id`. -/
theorem A_B (hx : x ∈ (chartAt (Rn n) p).source) (w : Rn n) :
    Bridge.A p (incl hN x) (Bridge.B p (chartAt (Rn n) p x) w) = w := by
  have h := Morse.fst_fderiv_sliceChart_fderiv_sliceParam (Morse.sliceAt hN p)
    (Morse.toChart_apply_mem_target _ hx) w
  rw [Morse.sliceParam_toChart (Morse.sliceAt hN p) hx] at h
  exact h

theorem B_mem (hx : x ∈ (chartAt (Rn n) p).source) (w : Rn n) :
    Bridge.B p (chartAt (Rn n) p x) w ∈ Morse.tangentSubspace hN x := by
  rw [Morse.tangentSubspace_eq_range_fderiv_sliceParam hN (Morse.sliceAt hN p) hx]
  exact ⟨w, rfl⟩

theorem mfderiv_extChartAt (hx : x ∈ (chartAt (Rn n) p).source) :
    mfderiv 𝓘(ℝ, Rn n) 𝓘(ℝ, Rn n) (extChartAt 𝓘(ℝ, Rn n) p) x =
      (Bridge.A p (incl hN x)).comp (D hN x) :=
  mfderiv_chartAt hx

theorem inverse_eq_of_inv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (M R : E →L[ℝ] E)
    (h1 : Function.LeftInverse R M) (h2 : Function.RightInverse R M) : M.inverse = R := by
  rw [show M = ((ContinuousLinearEquiv.equivOfInverse M R h1 h2 : E ≃L[ℝ] E) : E →L[ℝ] E) from rfl,
    ContinuousLinearMap.inverse_equiv]
  rfl

/-- The inverse of the chart derivative `d(chart_p)_x = A ∘ D` is `L_x ∘ B`. -/
theorem mfderiv_extChartAt_inverse (hx : x ∈ (chartAt (Rn n) p).source) :
    (mfderiv 𝓘(ℝ, Rn n) 𝓘(ℝ, Rn n) (extChartAt 𝓘(ℝ, Rn n) p) x).inverse =
      (L hN x).comp (Bridge.B p (chartAt (Rn n) p x)) := by
  rw [mfderiv_extChartAt hx]
  have h1 : Function.LeftInverse ((L hN x).comp (Bridge.B p (chartAt (Rn n) p x)))
      ((Bridge.A p (incl hN x)).comp (D hN x)) := fun v => by
    have e := DFunLike.congr_fun (D_eq_B hx) v
    simp only [ContinuousLinearMap.comp_apply] at e ⊢
    rw [← e]
    exact L_D x v
  have h2 : Function.RightInverse ((L hN x).comp (Bridge.B p (chartAt (Rn n) p x)))
      ((Bridge.A p (incl hN x)).comp (D hN x)) := fun w => by
    simp only [ContinuousLinearMap.comp_apply]
    rw [D_L (B_mem hx w)]
    exact A_B hx w
  exact inverse_eq_of_inv _ _ h1 h2

/-- The coordinate field `∂_i` of the chart at `p`, read in `V`, is `dx_u e_i`. -/
theorem D_coordField (hx : x ∈ (chartAt (Rn n) p).source) (i : Fin n) :
    D hN x (coordField (n := n) p i x) = Bridge.B p (chartAt (Rn n) p x) (EuclideanSpace.single i 1) := by
  have hx' : x ∈ (extChartAt 𝓘(ℝ, Rn n) p).source := by rwa [extChartAt_source]
  simp only [coordField, if_pos hx']
  rw [mfderiv_extChartAt_inverse hx]
  exact D_L (B_mem hx _)

theorem hasFDerivAt_G (hx : x ∈ (chartAt (Rn n) p).source) (e : Rn n) :
    HasFDerivAt (fun z : V => Bridge.B p ((Morse.sliceAt hN p).φ z).1 e)
      (((fderiv ℝ (Bridge.B p) (chartAt (Rn n) p x)).comp (Bridge.A p (incl hN x))).flip e)
      (incl hN x) := by
  set σ := Morse.sliceAt hN p
  have hu : chartAt (Rn n) p x ∈ σ.toChart.target := Morse.toChart_apply_mem_target σ hx
  have hφ : HasFDerivAt (fun z => (σ.φ z).1) (Bridge.A p (incl hN x)) (incl hN x) :=
    (Milnor.Problems.sliceChart_differentiableAt σ hx).hasFDerivAt.fst
  have hB : HasFDerivAt (Bridge.B p) (fderiv ℝ (Bridge.B p) (chartAt (Rn n) p x)) (chartAt (Rn n) p x) :=
    (((Morse.contDiffAt_sliceParam σ hu).fderiv_right (m := 1)
      (WithTop.coe_le_coe.2 le_top)).differentiableAt (by simp)).hasFDerivAt
  have hc := hB.comp (incl hN x) hφ
  have := hc.clm_apply (hasFDerivAt_const e (incl hN x))
  simpa using this

/-- `D_x(∇_{∂_i} ∂_j) = P_x(d²x_u(e_i, e_j))`. -/
theorem D_conn_coordField (hx : x ∈ (chartAt (Rn n) p).source) (i j : Fin n) :
    D hN x (conn (coordField (n := n) p j) x (coordField (n := n) p i x)) =
      P hN x (fderiv ℝ (Bridge.B p) (chartAt (Rn n) p x) (EuclideanSpace.single i 1)
        (EuclideanSpace.single j 1)) := by
  rw [D_conn']
  congr 1
  have hev : amb (coordField (n := n) p j) =ᶠ[𝓝 x]
      (fun z : V => Bridge.B p ((Morse.sliceAt hN p).φ z).1 (EuclideanSpace.single j 1)) ∘ incl hN := by
    filter_upwards [(chartAt (Rn n) p).open_source.mem_nhds hx] with y hy
    exact D_coordField hy j
  have hG := hasFDerivAt_G hx (EuclideanSpace.single j 1)
  unfold dV
  rw [hev.mfderiv_eq, mfderiv_comp x hG.differentiableAt.mdifferentiableAt
    (contMDiff_incl.mdifferentiableAt (by simp)), mfderiv_eq_fderiv, hG.fderiv]
  show fderiv ℝ (Bridge.B p) (chartAt (Rn n) p x)
    (Bridge.A p (incl hN x) (D hN x (coordField (n := n) p i x))) (EuclideanSpace.single j 1) = _
  rw [D_coordField hx i, A_B hx]

/-- **The blind Christoffel symbols of the induced connection**, in the chart at `p`. -/
theorem gam_eq (hx : x ∈ (chartAt (Rn n) p).source) (i j k : Fin n) :
    Gam (conn (hN := hN)) p x i j k = Bridge.A p (incl hN x) (P hN x (fderiv ℝ (Bridge.B p) (chartAt (Rn n) p x)
      (EuclideanSpace.single i 1) (EuclideanSpace.single j 1))) k := by
  simp only [Gam]
  rw [mfderiv_extChartAt hx]
  exact congrArg (fun v : Rn n => v k)
    (congrArg (Bridge.A p (incl hN x)) (D_conn_coordField hx i j))

theorem bilin_expand {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (T : Rn n →L[ℝ] Rn n →L[ℝ] F) (w w' : Rn n) :
    T w w' = ∑ i, ∑ j, (w i * w' j) • T (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) := by
  have hw : ∀ v : Rn n, v = ∑ i, v i • EuclideanSpace.single i (1 : ℝ) := fun v => by
    have := (EuclideanSpace.basisFun (Fin n) ℝ).sum_repr v
    simp only [EuclideanSpace.basisFun_apply, EuclideanSpace.basisFun_repr] at this
    exact this.symm
  conv_lhs => rw [hw w, hw w']
  simp only [map_sum, map_smul, _root_.sum_apply, _root_.smul_apply,
    Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [mul_comm]

/-- A's Christoffel term: `Γ(u)(w, w) = dx_u⁺ d²x_u(w, w) = A(P(d²x_u(w, w)))`. -/
theorem chartAcc_eq (hx : x ∈ (chartAt (Rn n) p).source) (w : Rn n) :
    Morse.chartAcc (Morse.sliceAt hN p) (chartAt (Rn n) p x) w =
      Bridge.A p (incl hN x) (P hN x (fderiv ℝ (Bridge.B p) (chartAt (Rn n) p x) w w)) := by
  have hP : P hN x = Morse.gramProj (Bridge.B p (chartAt (Rn n) p x)) :=
    Morse.tanProj_eq_gramProj hN (Morse.sliceAt hN p) hx
  rw [hP, Morse.gramProj_eq_comp_pinvL, ContinuousLinearMap.comp_apply, A_B hx]
  rfl

/-- **Christoffel dictionary**: `Σᵢⱼ Γᵏᵢⱼ(x) wⁱ wʲ = (Morse.chartAcc σ u w)ᵏ`, `σ` the slice chart
at `p`, `u` the coordinates of `x`. -/
theorem sum_gam_eq_chartAcc (hx : x ∈ (chartAt (Rn n) p).source) (w : Rn n) (k : Fin n) :
    ∑ i, ∑ j, Gam (conn (hN := hN)) p x i j k * w i * w j =
      Morse.chartAcc (Morse.sliceAt hN p) (chartAt (Rn n) p x) w k := by
  set σ := Morse.sliceAt hN p
  set T := fderiv ℝ (Bridge.B p) (chartAt (Rn n) p x)
  have hP : P hN x = Morse.gramProj (Bridge.B p (chartAt (Rn n) p x)) :=
    Morse.tanProj_eq_gramProj hN σ hx
  have hacc : Morse.chartAcc σ (chartAt (Rn n) p x) w = Bridge.A p (incl hN x) (P hN x (T w w)) := by
    rw [hP, Morse.gramProj_eq_comp_pinvL, ContinuousLinearMap.comp_apply, A_B hx]
    rfl
  rw [hacc, bilin_expand T w w]
  simp only [map_sum, map_smul, gam_eq hx]
  simp only [WithLp.ofLp_sum, WithLp.ofLp_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem derivWithin_coord {f : ℝ → Rn n} {s : Set ℝ} {τ : ℝ} (hf : DifferentiableWithinAt ℝ f s τ)
    (hs : UniqueDiffWithinAt ℝ s τ) (k : Fin n) :
    derivWithin (fun σ => f σ k) s τ = derivWithin f s τ k := by
  have h := ((EuclideanSpace.proj k : Rn n →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivWithinAt τ
    hf.hasDerivWithinAt).derivWithin hs
  simpa [Function.comp_def] using h

/-- **The coordinate form of the acceleration**: along a curve `c` smooth on the interval `s`,
in the chart at `p` (coordinates `u`), `u'' + Γ(u)(u', u') = A(P γ'')`, `γ = c` read in `V`. -/
theorem coord_eq {c : ℝ → Bridge.Sub hN} {s : Set ℝ} (hs : IsIntv s)
    (hc : ContDiffOn ℝ ∞ (incl hN ∘ c) s) {t : ℝ} (ht : t ∈ s)
    (hct : c t ∈ (chartAt (Rn n) p).source) :
    (∀ᶠ τ in 𝓝[s] t, DifferentiableWithinAt ℝ (fun τ => chartAt (Rn n) p (c τ)) s τ) ∧
    DifferentiableWithinAt ℝ (derivWithin (fun τ => chartAt (Rn n) p (c τ)) s) s t ∧
    derivWithin (derivWithin (fun τ => chartAt (Rn n) p (c τ)) s) s t +
      Morse.chartAcc (Morse.sliceAt hN p) (chartAt (Rn n) p (c t))
        (derivWithin (fun τ => chartAt (Rn n) p (c τ)) s t) =
      Bridge.A p (incl hN (c t)) (P hN (c t) (derivWithin (derivWithin (incl hN ∘ c) s) s t)) := by
  set σ := Morse.sliceAt hN p
  set u : ℝ → Rn n := fun τ => chartAt (Rn n) p (c τ) with hu
  set γ := incl hN ∘ c
  have hcont : ContinuousOn c s := (contMDiffOn_curve_iff.2 hc).continuousOn
  have hgood : ∀ τ ∈ s, c τ ∈ (chartAt (Rn n) p).source →
      ∀ᶠ τ' in 𝓝[s] τ, τ' ∈ s ∧ c τ' ∈ (chartAt (Rn n) p).source := fun τ hτ hcτ =>
    eventually_mem_nhdsWithin.and
      ((hcont τ hτ).preimage_mem_nhdsWithin ((chartAt (Rn n) p).open_source.mem_nhds hcτ))
  have hφ : ∀ y ∈ σ.φ.source, ContDiffAt ℝ ∞ (fun z : V => (σ.φ z).1) y := fun y hy =>
    contDiff_fst.contDiffAt.comp y
      ((Milnor.Problems.sliceChart_contDiffOn σ).contDiffAt (σ.φ.open_source.mem_nhds hy))
  have hu_cd : ∀ τ ∈ s, c τ ∈ (chartAt (Rn n) p).source → ContDiffWithinAt ℝ ∞ u s τ :=
    fun τ hτ hcτ => by
      show ContDiffWithinAt ℝ ∞ ((fun z : V => (σ.φ z).1) ∘ γ) s τ
      exact (hφ _ hcτ).comp_contDiffWithinAt τ (hc τ hτ)
  have hu_d : ∀ τ ∈ s, c τ ∈ (chartAt (Rn n) p).source →
      HasDerivWithinAt u (derivWithin u s τ) s τ := fun τ hτ hcτ =>
    ((hu_cd τ hτ hcτ).differentiableWithinAt (by simp)).hasDerivWithinAt
  have hsP : ∀ τ, c τ ∈ (chartAt (Rn n) p).source → γ τ = Morse.sliceParam σ (u τ) :=
    fun τ hcτ => (Morse.sliceParam_toChart σ hcτ).symm
  have hBd : ∀ τ, c τ ∈ (chartAt (Rn n) p).source →
      HasFDerivAt (Morse.sliceParam σ) (Bridge.B p (u τ)) (u τ) := fun τ hcτ =>
    ((Morse.contDiffAt_sliceParam σ (Morse.toChart_apply_mem_target σ hcτ)).differentiableAt
      (by simp)).hasFDerivAt
  have hγ' : ∀ τ ∈ s, c τ ∈ (chartAt (Rn n) p).source →
      derivWithin γ s τ = Bridge.B p (u τ) (derivWithin u s τ) := fun τ hτ hcτ => by
    have h1 : HasDerivWithinAt (Morse.sliceParam σ ∘ u) (Bridge.B p (u τ) (derivWithin u s τ)) s τ :=
      (hBd τ hcτ).comp_hasDerivWithinAt τ (hu_d τ hτ hcτ)
    have h2 : γ =ᶠ[𝓝[s] τ] Morse.sliceParam σ ∘ u :=
      (hgood τ hτ hcτ).mono fun τ' h => hsP τ' h.2
    exact (h1.congr_of_eventuallyEq h2 (hsP τ hcτ)).derivWithin (hs.2 τ hτ)
  have hev : derivWithin γ s =ᶠ[𝓝[s] t] fun τ => Bridge.B p (u τ) (derivWithin u s τ) :=
    (hgood t ht hct).mono fun τ h => hγ' τ h.1 h.2
  have hB2 : HasFDerivAt (Bridge.B p) (fderiv ℝ (Bridge.B p) (u t)) (u t) :=
    (((Morse.contDiffAt_sliceParam σ (Morse.toChart_apply_mem_target σ hct)).fderiv_right (m := 1)
      (WithTop.coe_le_coe.2 le_top)).differentiableAt (by simp)).hasFDerivAt
  have hu'dd : DifferentiableWithinAt ℝ (derivWithin u s) s t :=
    ((hu_cd t ht hct).derivWithin hs.2 (m := 1) (WithTop.coe_le_coe.2 le_top) ht).differentiableWithinAt
      (by simp)
  have hprod := (hB2.comp_hasDerivWithinAt t (hu_d t ht hct)).clm_apply hu'dd.hasDerivWithinAt
  have h2 : derivWithin (derivWithin γ s) s t =
      fderiv ℝ (Bridge.B p) (u t) (derivWithin u s t) (derivWithin u s t) +
        Bridge.B p (u t) (derivWithin (derivWithin u s) s t) := by
    rw [hev.derivWithin_eq (hγ' t ht hct)]
    exact hprod.derivWithin (hs.2 t ht)
  refine ⟨(hgood t ht hct).mono fun τ h => (hu_d τ h.1 h.2).differentiableWithinAt, hu'dd, ?_⟩
  have hPB : P hN (c t) (Bridge.B p (u t) (derivWithin (derivWithin u s) s t)) =
      Bridge.B p (u t) (derivWithin (derivWithin u s) s t) :=
    Morse.tanProj_eq_self hN (B_mem hct _)
  rw [h2, map_add, map_add, hPB, A_B hct, chartAcc_eq hct, add_comm]

/-- **The blind coordinate expression** of the geodesic equation, for the induced connection, is
the `k`-th coordinate of `A(P γ'')`. -/
theorem coord_expr {c : ℝ → Bridge.Sub hN} {s : Set ℝ} (hs : IsIntv s)
    (hc : ContDiffOn ℝ ∞ (incl hN ∘ c) s) {t : ℝ} (ht : t ∈ s)
    (hct : c t ∈ (chartAt (Rn n) p).source) (k : Fin n) :
    derivWithin (derivWithin (fun u => (extChartAt 𝓘(ℝ, Rn n) p (c u)) k) s) s t
        + ∑ i : Fin n, ∑ j : Fin n, Gam (conn (hN := hN)) p (c t) i j k *
          derivWithin (fun u => (extChartAt 𝓘(ℝ, Rn n) p (c u)) i) s t *
          derivWithin (fun u => (extChartAt 𝓘(ℝ, Rn n) p (c u)) j) s t =
      Bridge.A p (incl hN (c t)) (P hN (c t) (derivWithin (derivWithin (incl hN ∘ c) s) s t)) k := by
  have e : (extChartAt 𝓘(ℝ, Rn n) p : Bridge.Sub hN → Rn n) = chartAt (Rn n) p := rfl
  simp only [e]
  obtain ⟨hdev, hdd, hce⟩ := coord_eq hs hc ht hct
  have h1 : ∀ i, derivWithin (fun τ => (chartAt (Rn n) p (c τ)) i) s t =
      derivWithin (fun τ => chartAt (Rn n) p (c τ)) s t i := fun i =>
    derivWithin_coord (hdev.self_of_nhdsWithin ht) (hs.2 t ht) i
  have h2 : derivWithin (fun τ => derivWithin (fun σ => (chartAt (Rn n) p (c σ)) k) s τ) s t =
      derivWithin (derivWithin (fun τ => chartAt (Rn n) p (c τ)) s) s t k := by
    have hev : (fun τ => derivWithin (fun σ => (chartAt (Rn n) p (c σ)) k) s τ) =ᶠ[𝓝[s] t]
        fun τ => derivWithin (fun τ => chartAt (Rn n) p (c τ)) s τ k := by
      filter_upwards [hdev, eventually_mem_nhdsWithin] with τ hτ hτs
      exact derivWithin_coord hτ (hs.2 τ hτs) k
    rw [hev.derivWithin_eq (derivWithin_coord (hdev.self_of_nhdsWithin ht) (hs.2 t ht) k)]
    exact derivWithin_coord hdd (hs.2 t ht) k
  rw [h2]
  simp only [h1]
  rw [sum_gam_eq_chartAcc hct, ← hce]
  rfl

end Emb

/-- B on embedded manifolds: `M = ↥N` with the induced metric and the induced Levi-Civita
connection (a special case of B, see `B_to_B_emb`). -/
def B_emb : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (W : Type) [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] (n : ℕ)
    (N : Set V) (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N)
    [ConnectedSpace (Bridge.Sub hN)], ∀ (c : ℝ → Bridge.Sub hN) (s : Set ℝ), IsIntv s →
    IsSmoothCurve (n := n) c s →
    (IsGeodesic (Bridge.conn (hN := hN)) c s ↔ ∀ p : Bridge.Sub hN, ∀ t ∈ s,
      c t ∈ (extChartAt 𝓘(ℝ, Rn n) p).source → ∀ k : Fin n,
      derivWithin (derivWithin (fun u => (extChartAt 𝓘(ℝ, Rn n) p (c u)) k) s) s t
        + ∑ i : Fin n, ∑ j : Fin n, Gam (Bridge.conn (hN := hN)) p (c t) i j k *
          derivWithin (fun u => (extChartAt 𝓘(ℝ, Rn n) p (c u)) i) s t *
          derivWithin (fun u => (extChartAt 𝓘(ℝ, Rn n) p (c u)) j) s t = 0)

/-- `B_emb` is a special case of B (the induced connection is Levi-Civita, `Bridge.conn_isLC`). -/
theorem B_to_B_emb : B → B_emb := fun hB _ _ _ _ _ _ _ _ n _ hN _ =>
  hB n (Bridge.Sub hN) (Bridge.conn (hN := hN)) Bridge.conn_isLC

/-- **B on embedded manifolds holds outright**, by the Bridge's geodesic dictionary
(`isGeodesic_iff`: `P γ'' = 0`) and `Emb.coord_expr`; A is not used. -/
theorem B_emb_holds : B_emb := by
  intro V _ _ _ W _ _ _ n N hN _ c s hs hsm
  have hc : ContDiffOn ℝ ∞ (Bridge.incl hN ∘ c) s := Bridge.isSmoothCurve_iff.1 hsm
  show BridgePrelude.IsGeodesic _ _ _ ↔ _
  rw [Bridge.isGeodesic_iff]
  constructor
  · rintro ⟨-, -, hP⟩ p t ht hct k
    rw [extChartAt_source] at hct
    rw [Emb.coord_expr hs hc ht hct k, hP t ht, map_zero]
    rfl
  · intro H
    refine ⟨hs, hc, fun t ht => ?_⟩
    have hct : c t ∈ (chartAt (Rn n) (c t)).source := mem_chart_source _ _
    have hA : Bridge.A (c t) (Bridge.incl hN (c t))
        (Bridge.P hN (c t) (derivWithin (derivWithin (Bridge.incl hN ∘ c) s) s t)) = 0 := by
      ext k
      rw [← Emb.coord_expr hs hc ht hct k]
      exact H (c t) t ht (by rwa [extChartAt_source]) k
    set y := Bridge.P hN (c t) (derivWithin (derivWithin (Bridge.incl hN ∘ c) s) s t)
    have e1 : Bridge.D hN (c t) (Bridge.L hN (c t) y) = y := Bridge.D_L_P _ _
    have e2 := DFunLike.congr_fun (Bridge.D_eq_B hct) (Bridge.L hN (c t) y)
    simp only [ContinuousLinearMap.comp_apply, e1, hA, map_zero] at e2
    exact e2

/-- **A implies B on embedded manifolds** — vacuously (`B_emb_holds`). -/
theorem A_to_B_emb : A → B_emb := fun _ => B_emb_holds

#rt_check RoundTrip.V7_3.A_to_B_emb [Morse.IsGeodesicOn.deriv_deriv_eq,
  Morse.isGeodesicOn_of_deriv_deriv_eq, Morse.isGeodesicOn_iff_hasDerivAt_geodesicSpray,
  Morse.contDiffOn_chartSpray, Morse.isGeodesicOn_chart]
#rt_check RoundTrip.V7_3.B_emb_holds [Morse.IsGeodesicOn.deriv_deriv_eq,
  Morse.isGeodesicOn_of_deriv_deriv_eq, Morse.isGeodesicOn_iff_hasDerivAt_geodesicSpray,
  Morse.contDiffOn_chartSpray, Morse.isGeodesicOn_chart]

end RoundTrip.V7_3
