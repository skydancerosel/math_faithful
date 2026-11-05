import Morse.Chapter10.BrokenSplitting

/-!
Milnor, *Morse Theory*, §16, pp. 90–92: the index and the nullity of `E'` at its critical points
(Theorem 16.2, last assertion), for a submanifold `N ⊆ ℝᴷ` with the induced metric.

# The Hessian of `E'` is `E_**` on broken Jacobi fields

## Milnor's text, paraphrased

**Theorem 16.2** (p. 90, last assertion).  The index (or the nullity) of the Hessian `E'_**` at
each critical point `γ` of `E'` is equal to the index (or the nullity) of `E_**` at `γ`.

(p. 92) A variation `ᾱ : (−ε, ε) → B` of `γ` through broken geodesics has a broken Jacobi field as
variation field (14.3), which identifies `TB_γ` with `TΩ_γ(t₀, …, t_k)`; the assertion is then
"an immediate consequence of Lemma 15.4".

## In the embedded setting

Let `O ⊆ V^m` be open with `N^m ∩ O ⊆ U`, `F : V^m → ℝ` smooth with `F = E'` on `N^m ∩ O`, and
`y` a critical point of `E' = F|(N^m ∩ O)`, i.e. `γ = B.path y` an unbroken geodesic
(`Morse.BrokenSetup.isCriticalPointM_iff`).  In the slice chart `σ` of `N^m ∩ O` at `y`, with
parametrization `x = sliceParam σ` and `x(z₀) = y`:

* `Morse.hasDerivAt_deriv_line`: the second derivative of `u ↦ G(z₀ + u z)` at `0` is
  `G_**(z, z)` (the Hessian of `G = F ∘ x`).
* `Morse.BrokenSetup.hessian_eq_energyHessian`: **the Hessian of `E'` is `E_**` on broken Jacobi
  fields**: `(F ∘ x)_**(z, z') = E_**(Λ z, Λ z')`, where `Λ z` is the broken Jacobi field with
  values `dx_{z₀}(z)` at the break points.  Proof: `F(x(z₀ + u z)) = E(ᾱ(u))` for the variation `ᾱ`
  through broken geodesics with break points `x(z₀ + u z)`, so the second derivative is
  `E_**(W, W)` (Remark 13.5); `W = Λ z` because on each segment both are Jacobi fields (Lemma 14.3
  and an affine change of parameter) with the same values at the ends of a segment without
  conjugate points; then polarize.
* **Theorem 16.2, index and nullity**, `Morse.BrokenSetup.theorem_16_2_index`: the index of
  `E'_**` at `y` (`Morse.indexM`) is the index of `E_**` at `γ` (`Morse.formIndex`), and its
  nullity (`Morse.nullityM`) is the nullity of `E_**` (`Morse.hessNullity`): `Λ` is a linear
  isomorphism of `T_yB ≅ ∏ T_{y_j}N` onto `TΩ_γ(t₀, …, t_k)`, and Lemma 15.4 holds for the
  subdivision of §16 (`Morse/Chapter10/BrokenSplitting.lean`).

## What Milnor leaves implicit

* **"Clearly a broken Jacobi field"**: the variation field of a variation through broken
  geodesics is, on each segment, a Jacobi field for the reparametrized segment (Lemma 14.3 needs
  each segment parametrized by `[0, 1]`); comparing with the broken Jacobi field with the same
  values at the break points needs uniqueness, i.e. no conjugate points at the ends of the
  segments.
* **Polarization**: the identification is first obtained for the quadratic forms (second
  derivatives along lines in a chart), then for the bilinear forms by symmetry.
-/

open Set Filter Topology Function Module Metric MeasureTheory
open scoped ContDiff Manifold RealInnerProductSpace ENNReal Interval

noncomputable section

namespace Morse

/-! ### Calculus -/

section Calculus

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **The second derivative along a line is the Hessian**: for `G` of class `C²` at `z₀`,
`d²/du² G(z₀ + u z)` at `u = 0` is `G_**(z, z)`. -/
theorem hasDerivAt_deriv_line {G : E → ℝ} {z₀ : E} (hG : ContDiffAt ℝ 2 G z₀) (z : E) :
    HasDerivAt (deriv fun u : ℝ => G (z₀ + u • z)) (hessian G z₀ z z) 0 := by
  set ℓ : ℝ → E := fun u => z₀ + u • z
  have hℓ : ∀ u, HasDerivAt ℓ z u := fun u =>
    (((hasDerivAt_id u).smul_const z).const_add z₀).congr_deriv (one_smul ℝ z)
  have hℓ0 : z₀ = ℓ 0 := by simp [ℓ]
  have hGev : ∀ᶠ u in 𝓝 (0 : ℝ), DifferentiableAt ℝ G (ℓ u) := by
    have h1 : ∀ᶠ w in 𝓝 z₀, ContDiffAt ℝ 2 G w := hG.eventually (by simp)
    have h2 : Tendsto ℓ (𝓝 0) (𝓝 z₀) := by
      rw [hℓ0]; exact (hℓ 0).continuousAt.tendsto
    filter_upwards [h2.eventually h1] with u hu using hu.differentiableAt (by simp)
  have hev : deriv (fun u => G (ℓ u)) =ᶠ[𝓝 0] fun u => fderiv ℝ G (ℓ u) z := by
    filter_upwards [hGev] with u hu
    exact (hu.hasFDerivAt.comp_hasDerivAt u (hℓ u)).deriv
  have hH : HasFDerivAt (fderiv ℝ G) (hessian G z₀) z₀ :=
    ((hG.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
  have h1 : HasDerivAt (fun u => fderiv ℝ G (ℓ u)) (hessian G z₀ z) 0 :=
    hH.comp_hasDerivAt_of_eq 0 (hℓ 0) hℓ0
  have h2 : HasDerivAt (fun u => fderiv ℝ G (ℓ u) z) (hessian G z₀ z z) 0 := by
    simpa using h1.clm_apply (hasDerivAt_const (0 : ℝ) z)
  exact h2.congr_of_eventuallyEq hev

/-- **Polarization**: two symmetric bilinear forms with the same quadratic form are equal. -/
theorem eq_of_quadratic_eq {M : Type*} [AddCommGroup M] [Module ℝ M] {H K : M → M → ℝ}
    (hHadd : ∀ x y z, H (x + y) z = H x z + H y z) (hHadd' : ∀ x y z, H x (y + z) = H x y + H x z)
    (hKadd : ∀ x y z, K (x + y) z = K x z + K y z) (hKadd' : ∀ x y z, K x (y + z) = K x y + K x z)
    (hHs : ∀ x y, H x y = H y x) (hKs : ∀ x y, K x y = K y x) (hq : ∀ x, H x x = K x x)
    (x y : M) : H x y = K x y := by
  have h1 := hq (x + y)
  rw [hHadd, hHadd', hHadd', hKadd, hKadd', hKadd', hq x, hq y, hHs y x, hKs y x] at h1
  linarith

end Calculus

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {N : Set V} {hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N}

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [FiniteDimensional ℝ Z]
  [FiniteDimensional ℝ W] in
/-- The derivative of the parametrization of a slice chart is injective (for slice
submanifolds of any normed space; `Morse.injective_fderiv_sliceParam` is the case of an inner
product space). -/
theorem injective_fderiv_sliceParam' {V' Z' W' : Type*} [NormedAddCommGroup V']
    [NormedSpace ℝ V'] [NormedAddCommGroup Z'] [NormedSpace ℝ Z'] [NormedAddCommGroup W']
    [NormedSpace ℝ W'] {S : Set V'} (σ : Milnor.SliceChart 𝓘(ℝ, V') Z' W' S) {u : Z'}
    (hu : u ∈ σ.toChart.target) : Injective (fderiv ℝ (sliceParam σ) u) := by
  have hev : (fun u' => σ.φ (sliceParam σ u')) =ᶠ[𝓝 u] fun u' => (u', (0 : W')) := by
    filter_upwards [(isOpen_toChart_target σ).mem_nhds hu] with u' hu'
    exact σ.φ.apply_invFun hu'
  have hx := (contDiffAt_sliceParam σ hu).differentiableAt (by simp)
  have hmem : sliceParam σ u ∈ σ.φ.source := σ.φ.invFun_mem hu
  have hφ := differentiableAt_sliceChart σ hmem
  have h1 := (hφ.hasFDerivAt.comp u hx.hasFDerivAt).congr_of_eventuallyEq hev.symm
  have h2 : HasFDerivAt (fun u' : Z' => (u', (0 : W'))) (ContinuousLinearMap.inl ℝ Z' W') u :=
    (hasFDerivAt_id u).prodMk (hasFDerivAt_const _ _)
  have h3 := h1.unique h2
  intro w w' hww'
  have e1 : ContinuousLinearMap.inl ℝ Z' W' w = ContinuousLinearMap.inl ℝ Z' W' w' := by
    rw [← h3]; simp only [ContinuousLinearMap.comp_apply, hww']
  exact congrArg Prod.fst e1

namespace BrokenSetup

variable {p q : V} {c : ℝ} {m : ℕ} (B : BrokenSetup hN p q c m)

/-- **Jacobi fields along a segment are determined by their end values** (Remark 14.5 along the
radial geodesic `s ↦ exp_{xᵢ}(s vᵢ)`, `‖vᵢ‖ < δ` below a normal radius). -/
theorem eqOn_of_isJacobiField_seg {y : Fin m → V} (hy : y ∈ B.nodes) (i : Fin (m + 1))
    {J₁ J₂ : ℝ → V}
    (h₁ : IsJacobiField hN (fun s => exp hN (vert p q y i.castSucc)
      (s • B.joinVec (vert p q y i.castSucc) (vert p q y i.succ))) J₁)
    (h₂ : IsJacobiField hN (fun s => exp hN (vert p q y i.castSucc)
      (s • B.joinVec (vert p q y i.castSucc) (vert p q y i.succ))) J₂)
    (h0 : J₁ 0 = J₂ 0) (h1 : J₁ 1 = J₂ 1) : EqOn J₁ J₂ (Icc 0 1) := by
  set x := vert p q y i.castSucc
  have hxN : x ∈ N := B.vert_mem hy.1 _
  obtain ⟨ε, hδε, hnr⟩ := B.normal ⟨x, hxN⟩ (B.vert_mem_ball hy i.castSucc)
  have hv := B.joinVec_vert hy i
  have hvT := (prj_eq_self_iff hN hxN).1 hv.1
  have hvε := hv.2.1.trans_le hδε
  have hc := hnr.isSmoothCurveIn_ray hvT hvε
  have hinj := (remark_14_5_bijective hnr hvT hvε).1
  have heq := hinj (a₁ := ⟨_, h₁.comp_projIcc_mem hc⟩) (a₂ := ⟨_, h₂.comp_projIcc_mem hc⟩) (by
    ext
    · change J₁ (projIcc (0 : ℝ) 1 zero_le_one 0) = J₂ (projIcc (0 : ℝ) 1 zero_le_one 0)
      simp [h0]
    · change J₁ (projIcc (0 : ℝ) 1 zero_le_one 1) = J₂ (projIcc (0 : ℝ) 1 zero_le_one 1)
      simp [h1])
  intro s hs
  have := congrFun (congrArg Subtype.val heq) s
  simpa [projIcc_of_mem _ hs] using this

/-! ### Theorem 16.2: the index and the nullity -/

end BrokenSetup

variable (hN) in
/-- The derivative `dx_{z₀}` of the parametrization of the product chart of `N^m ∩ O` at `y`, as a
linear isomorphism onto `∏ T_{y_j}N`. -/
def chartTangentEquiv {m : ℕ} {O : Set (Fin m → V)} (hO : IsOpen O)
    (y : ↥((Set.pi univ fun _ => N) ∩ O)) : (Fin m → Z) ≃ₗ[ℝ]
    Submodule.pi univ fun j => tangentSubspace hN ⟨(y : Fin m → V) j, y.2.1 j trivial⟩ :=
  LinearEquiv.ofBijective
    (LinearMap.codRestrict _ ((fderiv ℝ (sliceParam (piInterChart hN hO y.2))
      ((piInterChart hN hO y.2).φ y).1 : (Fin m → Z) →L[ℝ] (Fin m → V)) :
        (Fin m → Z) →ₗ[ℝ] (Fin m → V)) fun z => by
      have h := tangentSubspace_eq_range_fderiv_sliceParam (isSliceSubmanifold_pi_inter hN hO)
        (piInterChart hN hO y.2) (mem_piInterChart_source hN hO y.2)
      rw [tangentSubspace_pi_inter hN hO y] at h
      rw [h]
      exact ⟨z, rfl⟩)
    ⟨fun z z' hzz' => injective_fderiv_sliceParam' (piInterChart hN hO y.2)
      (toChart_apply_mem_target (piInterChart hN hO y.2) (q := y)
        (mem_piInterChart_source hN hO y.2)) (congrArg Subtype.val hzz' :), by
      rintro ⟨w, hw⟩
      have h := tangentSubspace_eq_range_fderiv_sliceParam (isSliceSubmanifold_pi_inter hN hO)
        (piInterChart hN hO y.2) (mem_piInterChart_source hN hO y.2)
      rw [tangentSubspace_pi_inter hN hO y] at h
      rw [h] at hw
      obtain ⟨z, hz⟩ := hw
      exact ⟨z, Subtype.ext hz⟩⟩

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
theorem chartTangentEquiv_apply {m : ℕ} {O : Set (Fin m → V)} (hO : IsOpen O)
    (y : ↥((Set.pi univ fun _ => N) ∩ O)) (z : Fin m → Z) :
    ((chartTangentEquiv hN hO y z : Fin m → V)) =
      fderiv ℝ (sliceParam (piInterChart hN hO y.2)) ((piInterChart hN hO y.2).φ y).1 z := rfl

namespace BrokenSetup

variable {p q : V} {c : ℝ} {m : ℕ} (B : BrokenSetup hN p q c m)

section Index

/-- **The isomorphism `Λ`** from the coordinates of the chart at `y` to the broken Jacobi fields:
`z ↦` the broken Jacobi field with values `dx_{z₀}(z)` at the break points (Milnor's
identification of `TB_γ` with `TΩ_γ(t₀, …, t_k)`). -/
def chartBrokenEquiv {O : Set (Fin m → V)} (hO : IsOpen O)
    (hOU : (Set.pi univ fun _ => N) ∩ O ⊆ B.nodes) (y : ↥((Set.pi univ fun _ => N) ∩ O))
    (hgeo : IsUnbrokenGeodesic hN (B.path y)) : (Fin m → Z) ≃ₗ[ℝ]
    brokenSpace (B.isSmoothCurveIn_path (hOU y.2) hgeo) B.breaks 1 :=
  (chartTangentEquiv hN hO y).trans (B.brokenEquiv (hOU y.2) hgeo).symm

variable {O : Set (Fin m → V)} (hO : IsOpen O) (hOU : (Set.pi univ fun _ => N) ∩ O ⊆ B.nodes)
  {F : (Fin m → V) → ℝ} (hF : ContDiff ℝ ∞ F)
  (hFE : ∀ y ∈ (Set.pi univ fun _ => N) ∩ O, F y = B.energy' y)
  (y : ↥((Set.pi univ fun _ => N) ∩ O)) (hgeo : IsUnbrokenGeodesic hN (B.path y))

theorem chartBrokenEquiv_node (z : Fin m → Z) (j : Fin m) :
    (((B.chartBrokenEquiv hO hOU y hgeo z : pathTangent hN (B.path y)) : ℝ → V)
      (B.t j.castSucc.succ)) =
      fderiv ℝ (sliceParam (piInterChart hN hO y.2)) ((piInterChart hN hO y.2).φ y).1 z j := by
  have h := (B.brokenEquiv (hOU y.2) hgeo).apply_symm_apply (chartTangentEquiv hN hO y z)
  have := congrFun (congrArg Subtype.val h) j
  rw [brokenEquiv_apply] at this
  exact this

include hF hFE in
/-- **The second derivative of `E'` along a line of the chart is `E_**` on the broken Jacobi
field `Λ z`** (Milnor p. 92, via Lemma 14.3 and Remark 13.5). -/
theorem hessian_apply_self (z : Fin m → Z) :
    hessian (F ∘ sliceParam (piInterChart hN hO y.2)) ((piInterChart hN hO y.2).φ y).1 z z =
      energyHessian hN (B.path_mem_pathSpace (hOU y.2))
        (B.chartBrokenEquiv hO hOU y hgeo z) (B.chartBrokenEquiv hO hOU y hgeo z) := by
  set σ := piInterChart hN hO y.2
  set z₀ := (σ.φ y).1
  have hyσ : (y : Fin m → V) ∈ σ.φ.source := mem_piInterChart_source hN hO y.2
  have hz₀ : z₀ ∈ σ.toChart.target := toChart_apply_mem_target σ (q := y) hyσ
  have hx0 : sliceParam σ z₀ = y := sliceParam_toChart σ (q := y) hyσ
  have hy := hOU y.2
  have hγ := B.path_mem_pathSpace hy
  -- the line through `z₀` in the direction `z`, and the curve of break points
  set ℓ : ℝ → Fin m → Z := fun u => z₀ + u • z
  have hℓ : ContDiff ℝ ∞ ℓ := contDiff_const.add (contDiff_id.smul contDiff_const)
  set U₀ := ℓ ⁻¹' σ.toChart.target
  have hU₀ : IsOpen U₀ := (isOpen_toChart_target σ).preimage hℓ.continuous
  have h0 : (0 : ℝ) ∈ U₀ := by simpa [U₀, ℓ] using hz₀
  set yz : ℝ → Fin m → V := fun u => sliceParam σ (ℓ u)
  have hys : ContDiffOn ℝ ∞ yz U₀ := (contDiffOn_sliceParam σ).comp hℓ.contDiffOn fun u hu => hu
  have hyS : ∀ u ∈ U₀, yz u ∈ (Set.pi univ fun _ => N) ∩ O := fun u hu => sliceParam_mem σ hu
  have hyU : ∀ u ∈ U₀, yz u ∈ B.nodes := fun u hu => hOU (hyS u hu)
  have hy0 : yz 0 = y := by simp only [yz, ℓ, zero_smul, add_zero]; exact hx0
  have hyd : HasDerivAt yz (fderiv ℝ (sliceParam σ) z₀ z) 0 := by
    have hℓd : HasDerivAt ℓ z 0 :=
      (((hasDerivAt_id (0 : ℝ)).smul_const z).const_add z₀).congr_deriv (one_smul ℝ z)
    exact ((contDiffAt_sliceParam σ hz₀).differentiableAt
      (by simp)).hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hℓd (by simp [ℓ])
  -- the variation through broken geodesics
  obtain ⟨ε, hε, hsub, hstrips, hα⟩ := B.exists_variation_path hU₀ h0 hys hyU
  set α : ℝ → ℝ → V := fun u => B.path (yz u)
  have hαγ : ∀ t ∈ Icc (0 : ℝ) 1, α 0 t = B.path y t := fun t _ => by simp only [α, hy0]
  have hdd := hasDerivAt_deriv_energy hN hγ hgeo hα hαγ
  have hG : ContDiffAt ℝ 2 (F ∘ sliceParam σ) z₀ :=
    (hF.contDiffAt.comp z₀ (contDiffAt_sliceParam σ hz₀)).of_le (by norm_cast)
  have hline := hasDerivAt_deriv_line hG z
  have hev : (fun u : ℝ => (F ∘ sliceParam σ) (z₀ + u • z)) =ᶠ[𝓝 0]
      fun u => energy (α u) 0 1 := by
    filter_upwards [isOpen_Ioo.mem_nhds (show (0 : ℝ) ∈ Ioo (-ε) ε from ⟨by linarith, hε⟩)]
      with u hu
    simp only [Function.comp_apply, α]
    rw [hFE _ (hyS u (hsub hu)), B.energy_path (hyU u (hsub hu))]
  have hEq := (hline.congr_of_eventuallyEq hev.deriv.symm).unique hdd
  rw [hEq, energyHessian_apply, energyHessian_apply]
  congr 1
  -- the variation field is the broken Jacobi field `Λ z`
  set Λz := (B.chartBrokenEquiv hO hOU y hgeo z : pathTangent hN (B.path y))
  have hΛz : Λz ∈ brokenSpace (B.isSmoothCurveIn_path hy hgeo) B.breaks 1 :=
    (B.chartBrokenEquiv hO hOU y hgeo z).2
  have hWΛ : ∀ t ∈ Icc (0 : ℝ) 1, varField α t = (Λz : ℝ → V) t := by
    intro t ht
    have hti := B.mem_Icc_segOf ht
    generalize B.segOf t = i at hti
    have hl := B.len_pos i
    -- both fields at the division points
    have hnode : ∀ k : Fin (m + 2), varField α (B.t k) = (Λz : ℝ → V) (B.t k) := by
      intro k
      have hW := hα.varField_mem hN
      induction k using Fin.cases with
      | zero => rw [B.t_zero, hW.2.2.1, Λz.2.2.2.1]
      | succ k =>
        induction k using Fin.lastCases with
        | last => rw [Fin.succ_last, B.t_last, hW.2.2.2, Λz.2.2.2.2]
        | cast j =>
          rw [B.varField_path_node hU₀ h0 hyd hyU j, B.chartBrokenEquiv_node hO hOU y hgeo z j]
    -- the variation field on the segment, reparametrized, is a Jacobi field along the ray
    obtain ⟨hsm, hgeoi⟩ := hstrips i
    have hJ1 := lemma_14_3 hε hsm (fun u hu s hs => B.path_mem (hyU u (hsub hu)) _
      ⟨by nlinarith [B.t_nonneg i.castSucc, hs.1], by
        have : B.t i.succ = B.t i.castSucc + B.len i := by simp [Subdivision.len]
        nlinarith [B.t_le_one i.succ, hs.2]⟩) hgeoi
    have hray : EqOn (fun s => B.path (yz 0) (B.t i.castSucc + s * B.len i))
        (fun s => exp hN (vert p q y i.castSucc)
          (s • B.joinVec (vert p q y i.castSucc) (vert p q y i.succ))) (Icc 0 1) := by
      intro s hs
      have := B.path_affine_eq hy i hs
      simp only [hy0] at this ⊢
      rw [show B.t i.castSucc + s * B.len i = B.len i * s + B.t i.castSucc by ring]
      exact this
    have hJ1' := hJ1.congr_curve hray
    -- the broken Jacobi field on the segment, reparametrized
    have hpiece : ∀ b ∈ B.breaks, b ∉ Ioo (B.t i.castSucc) (B.t i.succ) := by
      intro b hb hbI
      obtain ⟨j, rfl⟩ := B.mem_breaks.1 hb
      have h1 := B.t_lt_iff.1 hbI.1
      have h2 := B.t_lt_iff.1 hbI.2
      rw [Fin.lt_def] at h1 h2
      simp only [Fin.val_succ, Fin.val_castSucc] at h1 h2
      omega
    obtain ⟨J, hJ, hΛJ⟩ := hΛz.2 _ _ (B.t_nonneg _) (B.t_lt_iff.2 Fin.castSucc_lt_succ)
      (B.t_le_one _) hpiece
    have hb : B.t i.castSucc + B.len i = B.t i.succ := by simp [Subdivision.len]
    have hJ2 := (hJ.1.comp_affine (B.t_nonneg i.castSucc) hl (by rw [hb]; exact B.t_le_one _))
    have hray' : EqOn (fun s => B.path y (B.len i * s + B.t i.castSucc))
        (fun s => exp hN (vert p q y i.castSucc)
          (s • B.joinVec (vert p q y i.castSucc) (vert p q y i.succ))) (Icc 0 1) :=
      B.path_affine_eq hy i
    have hJ2' := hJ2.congr_curve hray'
    -- compare: same values at both ends of the segment
    have hcmp := B.eqOn_of_isJacobiField_seg hy i hJ1' hJ2' (by
      simp only [zero_mul, add_zero, mul_zero, zero_add]
      rw [← hΛJ ⟨le_rfl, (B.t_lt_iff.2 Fin.castSucc_lt_succ).le⟩]
      exact hnode _) (by
      simp only [one_mul, mul_one]
      rw [show B.len i + B.t i.castSucc = B.t i.succ by rw [add_comm, hb],
        ← hΛJ ⟨(B.t_lt_iff.2 Fin.castSucc_lt_succ).le, le_rfl⟩]
      first
      | exact hnode _
      | (rw [show B.t i.castSucc + B.len i = B.t i.succ from hb]; exact hnode _))
    have hs : (t - B.t i.castSucc) / B.len i ∈ Icc (0 : ℝ) 1 :=
      ⟨div_nonneg (by linarith [hti.1]) hl.le, by rw [div_le_one hl]; linarith [hti.2, hb]⟩
    have := hcmp hs
    simp only at this
    rw [show B.t i.castSucc + (t - B.t i.castSucc) / B.len i * B.len i = t by field_simp; ring,
      show B.len i * ((t - B.t i.castSucc) / B.len i) + B.t i.castSucc = t by field_simp; ring]
      at this
    rw [hΛJ hti]
    exact this
  exact secondVariation_congr hN hWΛ hWΛ

include hF hFE in
/-- **The Hessian of `E'` is `E_**` on broken Jacobi fields** (Milnor p. 92): in the chart at
`y`, `(F ∘ x)_**(z, z') = E_**(Λ z, Λ z')`. -/
theorem hessian_eq_energyHessian (z z' : Fin m → Z) :
    hessian (F ∘ sliceParam (piInterChart hN hO y.2)) ((piInterChart hN hO y.2).φ y).1 z z' =
      energyHessian hN (B.path_mem_pathSpace (hOU y.2))
        (B.chartBrokenEquiv hO hOU y hgeo z) (B.chartBrokenEquiv hO hOU y hgeo z') := by
  set σ := piInterChart hN hO y.2
  set z₀ := (σ.φ y).1
  have hz₀ : z₀ ∈ σ.toChart.target :=
    toChart_apply_mem_target σ (q := y) (mem_piInterChart_source hN hO y.2)
  have hG : ContDiffAt ℝ 2 (F ∘ sliceParam σ) z₀ :=
    (hF.contDiffAt.comp z₀ (contDiffAt_sliceParam σ hz₀)).of_le (by norm_cast)
  set E := energyHessian hN (B.path_mem_pathSpace (hOU y.2))
  set Λ := B.chartBrokenEquiv hO hOU y hgeo
  have hsymm := energyHessian_isSymm hN (B.path_mem_pathSpace (hOU y.2))
  refine eq_of_quadratic_eq (H := fun z z' => hessian (F ∘ sliceParam σ) z₀ z z')
    (K := fun z z' => E (Λ z) (Λ z'))
    (fun _ _ _ => by simp only [map_add, add_apply])
    (fun _ _ _ => by simp only [map_add])
    (fun _ _ _ => by simp only [map_add, Submodule.coe_add, LinearMap.add_apply])
    (fun _ _ _ => by simp only [map_add, Submodule.coe_add]) (fun z z' => hessian_symm hG z z')
    (fun z z' => LinearMap.BilinForm.isSymm_def.1 hsymm _ _ ▸ rfl)
    (fun z => B.hessian_apply_self hO hOU hF hFE y hgeo z) z z'

include hF hFE hgeo in
/-- **Theorem 16.2, index and nullity** (Milnor p. 90): at a critical point `y` of `E'` (i.e.
`γ = B.path y` an unbroken geodesic, `Morse.BrokenSetup.isCriticalPointM_iff`), the index of the
Hessian of `E'` equals the index of `E_**` at `γ`, and the nullity of the Hessian of `E'` equals
the nullity of `E_**` at `γ`.  (`E' = F|(N^m ∩ O)` for any open `O` with `N^m ∩ O ⊆ U` and any
smooth `F` agreeing with `E'` there.) -/
theorem theorem_16_2_index :
    letI := (isSliceSubmanifold_pi_inter hN hO).chartedSpace
    (indexM (Fin m → Z) (F ∘ Subtype.val) y : ℕ∞) =
        formIndex (energyHessian hN (B.path_mem_pathSpace (hOU y.2))) ∧
      nullityM (Fin m → Z) (F ∘ Subtype.val) y =
        hessNullity hN (B.path_mem_pathSpace (hOU y.2)) := by
  let _ := (isSliceSubmanifold_pi_inter hN hO).chartedSpace
  set σ := piInterChart hN hO y.2
  have hyσ : (y : Fin m → V) ∈ σ.φ.source := mem_piInterChart_source hN hO y.2
  have hcrit := (B.isCriticalPointM_iff hO hOU hF hFE y).2 hgeo
  have hF2 : ContDiffAt ℝ 2 F y := hF.contDiffAt.of_le (by norm_cast)
  set H := hessian (F ∘ sliceParam σ) (σ.φ y).1
  set E := energyHessian hN (B.path_mem_pathSpace (hOU y.2))
  set BS := brokenSpace (B.isSmoothCurveIn_path (hOU y.2) hgeo) B.breaks 1
  set Λ := B.chartBrokenEquiv hO hOU y hgeo
  have hHΛ : ∀ z z', E.restrict BS (Λ z) (Λ z') = H z z' := fun z z' =>
    (B.hessian_eq_energyHessian hO hOU hF hFE y hgeo z z').symm
  constructor
  · rw [← index_hessian_comp_sliceParam (isSliceSubmanifold_pi_inter hN hO) σ hyσ hF2 hcrit,
      B.formIndex_brokenSpace (hOU y.2) hgeo]
    have h1 : (index H : ℕ∞) = formIndex (ContinuousLinearMap.toLinearMap₁₂ H) := by
      rw [formIndex_eq_sigNeg]; rfl
    rw [h1]
    exact formIndex_eq_of_equiv Λ fun z z' => hHΛ z z'
  · rw [← nullity_hessian_comp_sliceParam (isSliceSubmanifold_pi_inter hN hO) σ hyσ hF2 hcrit,
      ← B.finrank_ker_brokenSpace (hOU y.2) hgeo, nullity]
    have hns : nullSpace H = (LinearMap.ker (E.restrict BS)).comap (Λ : (Fin m → Z) →ₗ[ℝ] BS) := by
      ext z
      rw [mem_nullSpace, Submodule.mem_comap, LinearMap.mem_ker]
      change (∀ w, H z w = 0) ↔ (E.restrict BS) (Λ z) = 0
      constructor
      · intro h
        refine LinearMap.ext fun X => ?_
        obtain ⟨w, rfl⟩ := Λ.surjective X
        rw [hHΛ, h w]
        rfl
      · intro h w
        rw [← hHΛ, h]
        rfl
    rw [hns, Submodule.comap_equiv_eq_map_symm (Λ : (Fin m → Z) ≃ₗ[ℝ] BS)]
    exact LinearEquiv.finrank_map_eq _ _

end Index

end BrokenSetup

end Morse
