import Morse.Chapter9.BrokenJacobi

/-!
Milnor, *Morse Theory*, §15, pp. 84–86: Lemma 15.4 (the index of `E_**` is the index on the
finite dimensional space of broken Jacobi fields), and the first properties of the function
`λ(τ)` (Assertions (1) and (2), p. 85), for a submanifold `N ⊆ ℝᴷ` with the induced metric.

# The finite-dimensional reduction

* `Morse.isCompl_broken_nodeZero`: **Lemma 15.3, the splitting** `TΩ_γ = TΩ_γ(t₀, …, t_k) ⊕ T'`
  (along `γ|[0, τ]`); with `Morse.energyHessian_broken_nodeZero` (perpendicularity) and
  `Morse.energyHessian_nodeZero_pos` (positivity) this is all of Lemma 15.3.
* `Morse.lemma_15_4`: **Lemma 15.4, the index**: the index of `E_**` on the fields along
  `γ|[0, τ]` is its index on the broken Jacobi fields; `Morse.lemma_15_4_ker`: **the null
  space** is the null space on the broken Jacobi fields; `Morse.indexUpTo_lt_top`: the index is
  finite.
* `Morse.nodeEquiv`: the broken Jacobi fields are isomorphic to
  `Σ = T_{γ(t₁)}N ⊕ ⋯ ⊕ T_{γ(t_{k−1})}N` by `W ↦ (W(t_i))` (Milnor p. 86); `Morse.nodeSpace`.
* `Morse.finrank_ker_broken`: the nullity of `E_**` on the broken Jacobi fields along `γ|[0, τ]`
  is the multiplicity `ν(τ)` of `τ` as a conjugate point of `0` (a null broken Jacobi field has
  no jumps, `Morse.eq_jacobi_of_jumps_zero`, so it is one Jacobi field vanishing at `0` and `τ`).
* `Morse.indexUpTo hc τ`, Milnor's `λ(τ)` (p. 85): the index of `E_**` on the fields along
  `γ|[0, τ]` (extended by zero, which is Milnor's `(E_0^τ)_**` by Proposition 13.A).
  **Assertion (1)**: `Morse.indexUpTo_mono`; **Assertion (2)**: `Morse.indexUpTo_eq_zero`;
  `Morse.indexUpTo_one`: `λ(1)` is the index of `E_**`.

## What Milnor leaves implicit

* "`T'` contains no Jacobi fields other than zero" and "a broken Jacobi field is uniquely
  determined by its values at the break points" are the uniqueness on short segments.
* Assertion (2): "`γ_τ` is a minimal geodesic, hence `λ(τ) = 0` by Lemma 13.6"; here, for
  `τ ≤ h₀`, `E_**` is even positive definite on the fields along `γ|[0, τ]`
  (`Morse.hessForm_ge`).
-/

open Set Filter Topology Function Module
open scoped ContDiff Manifold RealInnerProductSpace

noncomputable section

namespace Morse

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {N : Set V} {hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N} {γ : ℝ → V}
  (hc : IsSmoothCurveIn hN γ)

/-! ### Lemma 15.3: the splitting -/

include hc in
/-- **A broken Jacobi field with given values at the division points** (Milnor p. 84: "let `W₁`
denote the unique broken Jacobi field such that `W₁(t_i) = W(t_i)`"). -/
theorem exists_brokenSpace_eq {B : Finset ℝ} {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (hB : IsFine hN γ hc B τ) (x : ℝ → V) (hx : ∀ b ∈ B, prj hN (γ b) (x b) = x b) :
    ∃ X ∈ brokenSpace hc B τ, ∀ b ∈ B, (X : ℝ → V) b = x b := by
  classical
  have h0B : (0 : ℝ) ∉ B := fun h => lt_irrefl _ (hB.1 0 h).1
  have hτB : τ ∉ B := fun h => lt_irrefl _ (hB.1 τ h).2
  obtain ⟨X, hX, hXx⟩ := exists_isBrokenJacobi hc B τ hτ hτ1 hB (fun t => if t ∈ B then x t else 0)
    fun t _ => by by_cases h : t ∈ B <;> simp [h, hx]
  set X' : ℝ → V := (Icc 0 τ).indicator X
  have hX' : IsBrokenJacobi hN γ hc B τ X' := fun s s' hs hss' hs' hp => by
    obtain ⟨J, hJ, hXJ⟩ := hX s s' hs hss' hs' hp
    exact ⟨J, hJ, fun t ht => by
      rw [show X' t = X t from
        indicator_of_mem (show t ∈ Icc 0 τ from ⟨hs.trans ht.1, ht.2.trans hs'⟩) X]
      exact hXJ ht⟩
  have hX'0 : X' 0 = 0 := by
    rw [show X' 0 = X 0 from indicator_of_mem (show (0 : ℝ) ∈ Icc 0 τ from ⟨le_rfl, hτ.le⟩) X,
      hXx 0 (by simp), if_neg h0B]
  have hX'τ : X' τ = 0 := by
    rw [show X' τ = X τ from indicator_of_mem (show τ ∈ Icc 0 τ from ⟨hτ.le, le_rfl⟩) X,
      hXx τ (by simp), if_neg hτB]
  have hout : ∀ t ∉ Icc (0 : ℝ) τ, X' t = 0 := fun t ht => indicator_of_notMem ht _
  refine ⟨⟨X', hX'.mem_pathTangent hc hτ hτ1 hB hX'0 hX'τ hout⟩, ⟨hout, hX'⟩, fun b hb => ?_⟩
  change X' b = x b
  rw [show X' b = X b from
    indicator_of_mem (show b ∈ Icc 0 τ from ⟨(hB.1 b hb).1.le, (hB.1 b hb).2.le⟩) X,
    hXx b (by simp [hb]), if_pos hb]

include hc in
/-- **Lemma 15.3, the splitting** (Milnor p. 84): the fields along `γ|[0, τ]` are the direct sum
of the broken Jacobi fields and the fields vanishing at the division points. -/
theorem isCompl_broken_nodeZero {B : Finset ℝ} {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (hB : IsFine hN γ hc B τ) :
    IsCompl ((brokenSpace hc B τ).comap (fieldsUpTo hN γ τ).subtype)
      ((nodeZero B τ).comap (fieldsUpTo hN γ τ).subtype) := by
  constructor
  · rw [Submodule.disjoint_def]
    intro X hXA hXC
    have h1 := IsBrokenJacobi.eqOn_zero hc hτ hτ1 hB hXA.2 (X : pathTangent hN γ).2.2.2.1
      (fieldsUpTo_apply_self hτ.le hτ1 X.2) hXC.2
    ext t
    by_cases ht : t ∈ Icc (0 : ℝ) τ
    · exact h1 ht
    · exact X.2 t ht
  · rw [codisjoint_iff, eq_top_iff]
    intro X _
    obtain ⟨Y, hY, hYX⟩ := exists_brokenSpace_eq hc hτ hτ1 hB (X : ℝ → V) fun b hb =>
      (X : pathTangent hN γ).2.2.1 b ⟨(hB.1 b hb).1.le, ((hB.1 b hb).2.trans_le hτ1).le⟩
    refine Submodule.mem_sup.2 ⟨⟨Y, brokenSpace_le_fieldsUpTo hc B τ hY⟩, hY,
      X - ⟨Y, brokenSpace_le_fieldsUpTo hc B τ hY⟩, ⟨fun t ht => ?_, fun b hb => ?_⟩, by abel⟩
    · simp [X.2 t ht, hY.1 t ht]
    · simp [hYX b hb]

/-! ### Lemma 15.4 -/

include hc in
/-- **Lemma 15.4, the index** (Milnor p. 85): the index of `E_**` on the fields along `γ|[0, τ]`
equals its index on the broken Jacobi fields. -/
theorem lemma_15_4 {B : Finset ℝ} {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1) (hB : IsFine hN γ hc B τ) :
    formIndex ((energyHessian hN hc.mem_pathSpace).restrict (fieldsUpTo hN γ τ)) =
      formIndex ((energyHessian hN hc.mem_pathSpace).restrict (brokenSpace hc B τ)) := by
  set E := energyHessian hN hc.mem_pathSpace
  rw [formIndex_eq_restrict_of_isCompl (isCompl_broken_nodeZero hc hτ hτ1 hB)
    (fun a ha c hc' => energyHessian_broken_nodeZero hc hτ hτ1 hB ha hc')
    (fun a ha c hc' => by
      change E c a = 0
      rw [LinearMap.BilinForm.isSymm_def.1 (energyHessian_isSymm hN hc.mem_pathSpace)]
      exact energyHessian_broken_nodeZero hc hτ hτ1 hB ha hc')
    (fun c hc' hc0 => energyHessian_nodeZero_pos hc hτ hτ1 hB hc' fun h =>
      hc0 (Subtype.ext h))]
  exact formIndex_eq_of_equiv (Submodule.comapSubtypeEquivOfLe
    (brokenSpace_le_fieldsUpTo hc B τ)) fun _ _ => rfl

include hc in
/-- **Lemma 15.4, the null space** (Milnor p. 85). -/
theorem lemma_15_4_ker {B : Finset ℝ} {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (hB : IsFine hN γ hc B τ) :
    LinearMap.ker ((energyHessian hN hc.mem_pathSpace).restrict (fieldsUpTo hN γ τ)) =
      (LinearMap.ker (((energyHessian hN hc.mem_pathSpace).restrict
        (fieldsUpTo hN γ τ)).restrict ((brokenSpace hc B τ).comap (fieldsUpTo hN γ τ).subtype))).map
        ((brokenSpace hc B τ).comap (fieldsUpTo hN γ τ).subtype).subtype :=
  ker_eq_map_ker_restrict (isCompl_broken_nodeZero hc hτ hτ1 hB)
    (fun _a ha _c hc' => energyHessian_broken_nodeZero hc hτ hτ1 hB ha hc')
    (fun _c hc' hc0 => energyHessian_nodeZero_pos hc hτ hτ1 hB hc' fun h => hc0 (Subtype.ext h))

/-! ### The space `Σ` of values at the division points -/

variable (hN γ) in
/-- `Σ = ⊕_{b ∈ B} T_{γ(b)}N` (Milnor p. 86), as tangent-vector-valued functions on `B`. -/
def nodeSpace (B : Finset ℝ) : Submodule ℝ (B → V) where
  carrier := {x | ∀ b : B, prj hN (γ b) (x b) = x b}
  add_mem' hx hy b := by simp [hx b, hy b]
  zero_mem' _ := by simp
  smul_mem' c x hx b := by simp [hx b]

/-- `W ↦ (W(t_i))_i`. -/
def nodeEval (B : Finset ℝ) (τ : ℝ) (hB : ∀ b ∈ B, b ∈ Ioo 0 τ) (hτ1 : τ ≤ 1) :
    brokenSpace hc B τ →ₗ[ℝ] nodeSpace hN γ B where
  toFun X := ⟨fun b => ((X : pathTangent hN γ) : ℝ → V) b, fun b =>
    (X : pathTangent hN γ).2.2.1 b ⟨(hB b b.2).1.le, ((hB b b.2).2.trans_le hτ1).le⟩⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- **Broken Jacobi fields correspond to their values at the division points** (Milnor p. 86:
"this vector space is isomorphic to the direct sum `Σ`"). -/
theorem nodeEval_bijective {B : Finset ℝ} {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (hB : IsFine hN γ hc B τ) : Bijective (nodeEval hc B τ hB.1 hτ1) := by
  constructor
  · rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro X hX
    rw [LinearMap.mem_ker] at hX
    have hnodes : ∀ b ∈ B, ((X : pathTangent hN γ) : ℝ → V) b = 0 := fun b hb =>
      congrFun (congrArg Subtype.val hX) ⟨b, hb⟩
    have h1 := IsBrokenJacobi.eqOn_zero hc hτ hτ1 hB X.2.2 (X : pathTangent hN γ).2.2.2.1
      (fieldsUpTo_apply_self hτ.le hτ1 (brokenSpace_le_fieldsUpTo hc B τ X.2)) hnodes
    refine (Submodule.mem_bot ℝ).2 (Subtype.ext (Subtype.ext (funext fun t => ?_)))
    by_cases ht : t ∈ Icc (0 : ℝ) τ
    · exact h1 ht
    · exact X.2.1 t ht
  · rintro ⟨x, hx⟩
    classical
    obtain ⟨X, hX, hXx⟩ := exists_brokenSpace_eq hc hτ hτ1 hB
      (fun t => if h : t ∈ B then x ⟨t, h⟩ else 0) fun b hb => by simp [hb, hx ⟨b, hb⟩]
    exact ⟨⟨X, hX⟩, Subtype.ext (funext fun b => by simp [nodeEval, hXx b b.2])⟩

/-- **`TΩ_γ(t₀, …, t_k) ≅ Σ`**. -/
def nodeEquiv {B : Finset ℝ} {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1) (hB : IsFine hN γ hc B τ) :
    brokenSpace hc B τ ≃ₗ[ℝ] nodeSpace hN γ B :=
  LinearEquiv.ofBijective _ (nodeEval_bijective hc hτ hτ1 hB)

theorem finiteDimensional_brokenSpace {B : Finset ℝ} {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (hB : IsFine hN γ hc B τ) : FiniteDimensional ℝ (brokenSpace hc B τ) :=
  LinearEquiv.finiteDimensional (nodeEquiv hc hτ hτ1 hB).symm

/-! ### The nullity on broken Jacobi fields -/

include hc in
/-- **A broken Jacobi field without jumps is a Jacobi field** (Milnor p. 79, "the Jacobi fields
fit together"): if `P Δ_b W' = 0` at every division point, `W` agrees on `[0, τ]` with one
Jacobi field. -/
theorem eq_jacobi_of_jumps_zero (B : Finset ℝ) : ∀ τ, τ ≤ 1 → (∀ b ∈ B, b ∈ Ioo 0 τ) →
    ∀ X : ℝ → V, IsBrokenJacobi hN γ hc B τ X → (∀ b ∈ B, prj hN (γ b) (jump X b) = 0) →
    0 < τ → ∃ J ∈ jacobiSpace hN γ hc, EqOn X J (Icc 0 τ) := by
  classical
  induction B using Finset.induction_on_max with
  | empty =>
    intro τ _ _ X hX _ hτ
    exact hX 0 τ le_rfl hτ le_rfl (by simp)
  | insert m B hmB ih =>
    intro τ hτ1 hB X hX hjump hτ
    have hm : m ∈ Ioo 0 τ := hB m (Finset.mem_insert_self _ _)
    have hm1 : m ∈ Ioo (0 : ℝ) 1 := ⟨hm.1, hm.2.trans_le hτ1⟩
    obtain ⟨J₁, hJ₁, hXJ₁⟩ := ih m (hm.2.le.trans hτ1)
      (fun b hb => ⟨(hB b (Finset.mem_insert_of_mem hb)).1, hmB b hb⟩) X
      (fun s s' hs hss' hs' hp => hX s s' hs hss' (hs'.trans hm.2.le) fun b hb => by
        rcases Finset.mem_insert.1 hb with rfl | hb
        · exact fun h => absurd hs' (not_le.2 h.2)
        · exact hp b hb)
      (fun b hb => hjump b (Finset.mem_insert_of_mem hb)) hm.1
    obtain ⟨J₂, hJ₂, hXJ₂⟩ := hX m τ hm.1.le hm.2 le_rfl fun b hb hbI => by
      rcases Finset.mem_insert.1 hb with rfl | hb
      · exact lt_irrefl _ hbI.1
      · exact absurd (hmB b hb) (not_lt.2 hbI.1.le)
    -- the one-sided derivatives of `X` at `m`
    have hd₁ : HasDerivAt J₁ (deriv J₁ m) m :=
      ((hJ₁.1.contDiffOn.contDiffAt (Icc_mem_nhds hm1.1 hm1.2)).differentiableAt
        (by simp)).hasDerivAt
    have hd₂ : HasDerivAt J₂ (deriv J₂ m) m :=
      ((hJ₂.1.contDiffOn.contDiffAt (Icc_mem_nhds hm1.1 hm1.2)).differentiableAt
        (by simp)).hasDerivAt
    have hL : derivWithin X (Iic m) m = deriv J₁ m := by
      refine (hd₁.hasDerivWithinAt.congr_of_eventuallyEq ?_ (hXJ₁ ⟨hm.1.le, le_rfl⟩)).derivWithin
        (uniqueDiffWithinAt_Iic m)
      filter_upwards [Icc_mem_nhdsLE hm.1] with t ht using hXJ₁ ht
    have hR : derivWithin X (Ici m) m = deriv J₂ m := by
      refine (hd₂.hasDerivWithinAt.congr_of_eventuallyEq ?_ (hXJ₂ ⟨le_rfl, hm.2.le⟩)).derivWithin
        (uniqueDiffWithinAt_Ici m)
      filter_upwards [Icc_mem_nhdsGE hm.2] with t ht using hXJ₂ ht
    have hcov : ∀ J : ℝ → V, J ∈ jacobiSpace hN γ hc →
        covAlong hN γ J m = prj hN (γ m) (deriv J m) := fun J hJ => by
      rw [covAlong, ((hJ.1.contDiffOn.contDiffAt (Icc_mem_nhds hm1.1 hm1.2)).differentiableAt
        (by simp)).hasDerivAt.hasDerivWithinAt.derivWithin
        (uniqueDiffOn_Icc zero_lt_one m (Ioo_subset_Icc_self hm1))]
    have hjm := hjump m (Finset.mem_insert_self _ _)
    rw [jump, hL, hR, map_sub, sub_eq_zero] at hjm
    -- `J₁ = J₂`
    have hval : (J₂ - J₁) m = 0 := by
      rw [Pi.sub_apply, ← hXJ₂ ⟨le_rfl, hm.2.le⟩, ← hXJ₁ ⟨hm.1.le, le_rfl⟩, sub_self]
    have hcov' : covAlong hN γ (J₂ - J₁) m = 0 := by
      have hmem := Submodule.sub_mem _ hJ₂ hJ₁
      rw [hcov _ hmem, deriv_sub hd₂.differentiableAt hd₁.differentiableAt, map_sub, hjm, sub_self]
    have hJJ := jacobiSpace_eq_zero hc (Submodule.sub_mem _ hJ₂ hJ₁)
      ((Submodule.sub_mem _ hJ₂ hJ₁).1.eqOn_zero hc (Ioo_subset_Icc_self hm1) hval hcov')
    have h12 : J₂ = J₁ := sub_eq_zero.1 hJJ
    refine ⟨J₁, hJ₁, fun t ht => ?_⟩
    by_cases htm : t ≤ m
    · exact hXJ₁ ⟨ht.1, htm⟩
    · rw [hXJ₂ ⟨(not_le.1 htm).le, ht.2⟩, h12]

include hc in
/-- A Jacobi field on `[0, 1]` that vanishes on a nonempty open interval vanishes. -/
theorem jacobiSpace_eq_zero_of_eqOn {J : ℝ → V} (hJ : J ∈ jacobiSpace hN γ hc) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1) (h0 : EqOn J 0 (Icc a b)) : J = 0 := by
  set m := (a + b) / 2
  have hm : m ∈ Ioo a b := ⟨by simp only [m]; linarith, by simp only [m]; linarith⟩
  have hm01 : m ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hm.1], by linarith [hm.2]⟩
  have hev : J =ᶠ[𝓝 m] 0 := eventually_of_mem (Icc_mem_nhds hm.1 hm.2) h0
  have hcovm : covAlong hN γ J m = 0 := by
    have hd : HasDerivAt J 0 m := (hasDerivAt_const m (0 : V)).congr_of_eventuallyEq hev
    rw [covAlong, hd.hasDerivWithinAt.derivWithin (uniqueDiffOn_Icc zero_lt_one m hm01), map_zero]
  exact jacobiSpace_eq_zero hc hJ (hJ.1.eqOn_zero hc hm01 hev.eq_of_nhds hcovm)

include hc in
/-- **The nullity on broken Jacobi fields is the multiplicity `ν(τ)`** (used in Milnor's proof of
Assertion (4), p. 86, with Lemma 15.4 and Theorem 14.1). -/
theorem finrank_ker_broken {B : Finset ℝ} {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (hB : IsFine hN γ hc B τ) :
    finrank ℝ (LinearMap.ker ((energyHessian hN hc.mem_pathSpace).restrict (brokenSpace hc B τ))) =
      conjMultiplicity hN γ hc 0 τ := by
  classical
  set E := energyHessian hN hc.mem_pathSpace
  set K := LinearMap.ker (E.restrict (brokenSpace hc B τ))
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  -- the cut-off of a Jacobi field vanishing at `0` and `τ`
  have hmemT : ∀ J ∈ conjSpace hN γ hc 0 τ, (Icc 0 τ).indicator J ∈ pathTangent hN γ :=
    fun J hJ => indicator_mem_pathTangent ((mem_conjSpace hc).1 hJ).1.1 le_rfl hτ.le hτ1
      ((mem_conjSpace hc).1 hJ).2.1 ((mem_conjSpace hc).1 hJ).2.2
  set φ : conjSpace hN γ hc 0 τ →ₗ[ℝ] pathTangent hN γ :=
    { toFun := fun J => ⟨(Icc 0 τ).indicator J, hmemT J J.2⟩
      map_add' := fun J J' => Subtype.ext (funext fun t => by
        by_cases h : t ∈ Icc 0 τ <;> simp [h])
      map_smul' := fun c J => Subtype.ext (funext fun t => by
        by_cases h : t ∈ Icc 0 τ <;> simp [h]) }
  have hφinj : Injective φ := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro J hJ
    rw [LinearMap.mem_ker] at hJ
    have hJ0 : EqOn (J : ℝ → V) 0 (Icc 0 τ) := fun t ht => by
      have := congrFun (congrArg Subtype.val hJ) t
      simpa [φ, indicator_of_mem ht] using this
    exact (Submodule.mem_bot ℝ).2 (Subtype.ext (jacobiSpace_eq_zero_of_eqOn hc
      ((mem_conjSpace hc).1 J.2).1 le_rfl hτ hτ1 hJ0))
  -- the range of `φ` is the null space
  have hrange : LinearMap.range φ = K.map (brokenSpace hc B τ).subtype := by
    ext X
    constructor
    · rintro ⟨J, rfl⟩
      obtain ⟨hJs, hJ0, hJτ⟩ := (mem_conjSpace hc).1 J.2
      have hbroken : φ J ∈ brokenSpace hc B τ := ⟨fun t ht => indicator_of_notMem ht _,
        fun s s' hs hss' hs' _ => ⟨(J : ℝ → V), hJs, fun t ht => by
          change (Icc 0 τ).indicator (J : ℝ → V) t = (J : ℝ → V) t
          rw [indicator_of_mem (show t ∈ Icc 0 τ from ⟨hs.trans ht.1, ht.2.trans hs'⟩)]⟩⟩
      refine ⟨⟨φ J, hbroken⟩, ?_, rfl⟩
      rw [SetLike.mem_coe, LinearMap.mem_ker]
      ext Y
      change E (φ J) (Y : pathTangent hN γ) = 0
      rw [energyHessian_broken_eq hc hτ hτ1 hB hbroken (brokenSpace_le_fieldsUpTo hc B τ Y.2)]
      rw [Finset.sum_eq_zero fun b hb => ?_, mul_zero]
      have hb := hB.1 b hb
      have hev : ((φ J : pathTangent hN γ) : ℝ → V) =ᶠ[𝓝 b] J := by
        filter_upwards [Ioo_mem_nhds hb.1 hb.2] with t ht
        exact indicator_of_mem (Ioo_subset_Icc_self ht) _
      have hd : DifferentiableAt ℝ (J : ℝ → V) b :=
        (hJs.1.contDiffOn.contDiffAt (Icc_mem_nhds hb.1 (hb.2.trans_le hτ1))).differentiableAt
          (by simp)
      rw [jump_congr hev, jump_eq_zero hd, map_zero, inner_zero_right]
    · rintro ⟨X, hX, rfl⟩
      rw [SetLike.mem_coe, LinearMap.mem_ker] at hX
      -- all jumps vanish: test against the broken Jacobi field with values `P Δ_b X'`
      have hjump : ∀ b ∈ B, prj hN (γ b) (jump ((X : pathTangent hN γ) : ℝ → V) b) = 0 := by
        obtain ⟨Y, hY, hYv⟩ := exists_brokenSpace_eq hc hτ hτ1 hB
          (fun b => prj hN (γ b) (jump ((X : pathTangent hN γ) : ℝ → V) b))
          fun b _ => prj_prj hN _ _
        have h1 : (E.restrict (brokenSpace hc B τ)) X ⟨Y, hY⟩ = 0 := by rw [hX]; rfl
        change E (X : pathTangent hN γ) Y = 0 at h1
        rw [energyHessian_broken_eq hc hτ hτ1 hB X.2 (brokenSpace_le_fieldsUpTo hc B τ hY)] at h1
        have h2 : ∑ b ∈ B, ‖prj hN (γ b) (jump ((X : pathTangent hN γ) : ℝ → V) b)‖ ^ 2 = 0 := by
          have : ∑ b ∈ B, ⟪(Y : ℝ → V) b,
              prj hN (γ b) (jump ((X : pathTangent hN γ) : ℝ → V) b)⟫ = 0 := by linarith
          rw [← this]
          refine Finset.sum_congr rfl fun b hb => ?_
          rw [hYv b hb, real_inner_self_eq_norm_sq]
        intro b hb
        have := (Finset.sum_eq_zero_iff_of_nonneg fun b _ => by positivity).1 h2 b hb
        rwa [pow_eq_zero_iff two_ne_zero, norm_eq_zero] at this
      obtain ⟨J, hJ, hXJ⟩ := eq_jacobi_of_jumps_zero hc B τ hτ1 hB.1 _ X.2.2 hjump hτ
      have hJ0 : J 0 = 0 := by
        rw [← hXJ ⟨le_rfl, hτ.le⟩]; exact (X : pathTangent hN γ).2.2.2.1
      have hJτ : J τ = 0 := by
        rw [← hXJ ⟨hτ.le, le_rfl⟩]
        exact fieldsUpTo_apply_self hτ.le hτ1 (brokenSpace_le_fieldsUpTo hc B τ X.2)
      refine ⟨⟨J, (mem_conjSpace hc).2 ⟨hJ, hJ0, hJτ⟩⟩, Subtype.ext (funext fun t => ?_)⟩
      change (Icc 0 τ).indicator J t = ((X : pathTangent hN γ) : ℝ → V) t
      by_cases ht : t ∈ Icc (0 : ℝ) τ
      · rw [indicator_of_mem ht, hXJ ht]
      · rw [indicator_of_notMem ht, X.2.1 t ht]
  have h1 := LinearMap.finrank_range_of_inj hφinj
  rw [hrange, ← (Submodule.equivMapOfInjective _ (Submodule.injective_subtype _) K).finrank_eq]
    at h1
  exact h1

/-! ### `λ(τ)` -/

variable (hN γ) in
/-- **Milnor's `λ(τ)`** (p. 85): the index of the Hessian along `γ|[0, τ]`, i.e. of `E_**` on the
fields along `γ|[0, τ]` vanishing at the ends (extended by zero). -/
def indexUpTo (hc : IsSmoothCurveIn hN γ) (τ : ℝ) : ℕ∞ :=
  formIndex ((energyHessian hN hc.mem_pathSpace).restrict (fieldsUpTo hN γ τ))

/-- **Assertion (1)** (Milnor p. 85): `λ` is monotone (a field along `γ|[0, τ]` extends by zero
to `γ|[0, τ']`, with the same Hessian). -/
theorem indexUpTo_mono {τ τ' : ℝ} (h : τ ≤ τ') : indexUpTo hN γ hc τ ≤ indexUpTo hN γ hc τ' :=
  formIndex_le_of_map (Submodule.inclusion (fieldsUpTo_mono h)) fun _ _ => rfl

theorem indexUpTo_le_finrank {B : Finset ℝ} {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (hB : IsFine hN γ hc B τ) :
    indexUpTo hN γ hc τ ≤ finrank ℝ (brokenSpace hc B τ) := by
  have := finiteDimensional_brokenSpace hc hτ hτ1 hB
  rw [indexUpTo, lemma_15_4 hc hτ hτ1 hB]
  exact formIndex_le fun S _ _ => by exact_mod_cast Submodule.finrank_le S

/-- **The index is finite** (Lemma 15.4). -/
theorem indexUpTo_lt_top {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1) : indexUpTo hN γ hc τ < ⊤ := by
  obtain ⟨B, hB, -⟩ := exists_isFine hc hτ
  exact (indexUpTo_le_finrank hc hτ hτ1 hB).trans_lt (ENat.natCast_lt_top _)

/-- **Assertion (2)** (Milnor p. 85): `λ(τ) = 0` for small `τ`. -/
theorem indexUpTo_eq_zero {τ : ℝ} (_hτ : 0 < τ) (hτh : τ ≤ fineMesh hN γ hc) :
    indexUpTo hN γ hc τ = 0 := by
  refine le_antisymm (formIndex_le fun S _ hneg => ?_) zero_le
  have : S = ⊥ := by
    rw [eq_bot_iff]
    intro X hX
    rw [Submodule.mem_bot]
    by_contra hX0
    have hneg' := hneg X hX hX0
    change energyHessian hN hc.mem_pathSpace X X < 0 at hneg'
    apply hX0
    have hzero : ∀ t ∈ Icc (0 : ℝ) 1, ∃ s ∈ Icc 0 t, t - s ≤ fineMesh hN γ hc ∧
        (((X : fieldsUpTo hN γ τ) : pathTangent hN γ) : ℝ → V) s = 0 := by
      intro t ht
      by_cases htτ : t ≤ τ
      · exact ⟨0, ⟨le_rfl, ht.1⟩, by linarith, (X : pathTangent hN γ).2.2.2.1⟩
      · exact ⟨t, ⟨ht.1, le_rfl⟩, by rw [sub_self]; exact (fineMesh_pos hc).le,
          X.2 t fun h => htτ h.2⟩
    have h0 : hessForm hN γ ((X : pathTangent hN γ) : ℝ → V) ((X : pathTangent hN γ) : ℝ → V) ≤
        0 := by
      rw [energyHessian_apply, secondVariation_eq_hessForm hN hc.mem_pathSpace
        (X : pathTangent hN γ).2 (X : pathTangent hN γ).2] at hneg'
      linarith
    have hX0' := eqOn_zero_of_hessForm hc hc.mem_pathSpace (X : pathTangent hN γ).2 hzero h0
    refine Subtype.ext (Subtype.ext (funext fun t => ?_))
    by_cases ht : t ∈ Icc (0 : ℝ) τ
    · exact hX0' ⟨ht.1, ht.2.trans (hτh.trans (by
        have := fineMesh_pos hc
        have := jacBound_nonneg hc
        rw [fineMesh, div_le_one (by linarith)]
        linarith))⟩
    · exact X.2 t ht
  subst this
  simp

include hc in
/-- `λ(1)` is the index of `E_**` on all of `TΩ_γ` (whose elements are only relevant on
`[0, 1]`). -/
theorem indexUpTo_one :
    indexUpTo hN γ hc 1 = formIndex (energyHessian hN hc.mem_pathSpace) := by
  refine le_antisymm (formIndex_restrict_le _ _) (formIndex_le_of_map ?_ fun X Y => ?_)
  · exact
      { toFun := fun X => ⟨⟨(Icc 0 1).indicator X, ⟨X.2.1.congr fun t ht => by
            simp [indicator_of_mem ht], fun t ht => by simp [indicator_of_mem ht, X.2.2.1 t ht],
            by simp [X.2.2.2.1], by simp [X.2.2.2.2]⟩⟩, fun t ht => indicator_of_notMem ht _⟩
        map_add' := fun X Y => by
          ext t; by_cases h : t ∈ Icc (0 : ℝ) 1 <;> simp [h]
        map_smul' := fun c X => by
          ext t; by_cases h : t ∈ Icc (0 : ℝ) 1 <;> simp [h] }
  · change energyHessian hN hc.mem_pathSpace ⟨(Icc 0 1).indicator X, _⟩
      ⟨(Icc 0 1).indicator Y, _⟩ = energyHessian hN hc.mem_pathSpace X Y
    rw [energyHessian_apply, energyHessian_apply]
    congr 1
    exact secondVariation_congr hN (fun t ht => by simp [indicator_of_mem ht])
      (fun t ht => by simp [indicator_of_mem ht])

end Morse
