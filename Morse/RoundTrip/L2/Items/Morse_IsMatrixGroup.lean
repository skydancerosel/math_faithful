import Morse
import RoundTrip.L2.Blind.Morse_IsMatrixGroup

/-! Layer-2 check of `Morse.IsMatrixGroup hG 𝔤` (`G ⊆ U(n)` closed under products and `ᴴ`, `𝔤`
skew-Hermitian and `Ad G`-invariant, `exp 𝔤 ⊆ G`, `dim G = dim 𝔤`; `G` a slice submanifold of
`Mₙ(𝕜)` modelled on `Z`) against the blind textbook notion (`G` a closed subgroup of `U(n)` and
`𝔤 = {X skew-Hermitian : exp(tX) ∈ G ∀ t}`).

* `P_imp_T`: the project's notion implies the textbook's. Closedness is not a field of the project's
  notion: it follows because a locally closed subgroup is closed (`isClosed_of_subgroup`, from a
  slice chart at `1`); `𝔤 ⊇ {X : exp(tX) ∈ G}` follows from the project's `T_gG = g·𝔤`.
* `P_iff`: exactly, project = textbook + `dim G = dim 𝔤` (`T_imp_P_of_finrank`; `Ad`-invariance
  from `exp(t gXg⁻¹) = g exp(tX) g⁻¹`).
* `finrank_le_of_T`: the textbook notion gives `𝔤 ⊆ T₁G`, so `dim 𝔤 ≤ dim G`; the reverse
  inequality (every tangent vector at `1` generates a one-parameter subgroup of the closed subgroup
  `G`, Cartan / von Neumann) is the one missing ingredient, not in Mathlib: `agree_of` assumes it.

Both sides carry the setting `hG`; `[FiniteDimensional ℝ Z]`, `[FiniteDimensional ℝ W]` are
assumed for the project's tangent-space lemmas (automatic when `G ≠ ∅`, and both notions force
`1 ∈ G`). -/

namespace RoundTrip.L2.Morse_IsMatrixGroup

open Matrix Set Filter Topology Module
open scoped Matrix Morse.MatrixInner Manifold

variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} [Fintype ι] [DecidableEq ι]
  {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  {G : Set (Matrix ι ι 𝕜)}

/-- A slice submanifold `G ⊆ U(n)` closed under products and `ᴴ` and containing `1` is closed
(a locally closed subgroup is closed). -/
theorem isClosed_of_subgroup (hG : Milnor.IsSliceSubmanifold 𝓘(ℝ, Matrix ι ι 𝕜) Z W G)
    (hU : ∀ g ∈ G, gᴴ * g = 1) (hmul : ∀ g ∈ G, ∀ h ∈ G, g * h ∈ G)
    (hstar : ∀ g ∈ G, gᴴ ∈ G) (h1 : (1 : Matrix ι ι 𝕜) ∈ G) : IsClosed G := by
  obtain ⟨σ, hσ⟩ := hG 1 h1
  have hO : IsOpen σ.φ.source := σ.φ.open_source
  have hcont : ContinuousOn σ.φ σ.φ.source := σ.φ.contMDiffOn.continuousOn
  -- near `1`, `G` is closed
  have key : ∀ x ∈ closure G, x ∈ σ.φ.source → x ∈ G := by
    intro x hx hxU
    have hx' : x ∈ closure (σ.φ.source ∩ G) := hO.inter_closure ⟨hxU, hx⟩
    have hca : ContinuousAt (fun p => (σ.φ p).2) x :=
      continuous_snd.continuousAt.comp (hcont.continuousAt (hO.mem_nhds hxU))
    have hmem := hca.continuousWithinAt.mem_closure_image hx'
    have himg : (fun p => (σ.φ p).2) '' (σ.φ.source ∩ G) ⊆ {0} := by
      rintro _ ⟨p, ⟨hpU, hpG⟩, rfl⟩
      exact (σ.slice p hpU).1 hpG
    have h0 : (σ.φ x).2 = 0 := by
      have := closure_mono himg hmem
      rwa [closure_singleton] at this
    exact (σ.slice x hxU).2 h0
  refine isClosed_of_closure_subset fun g hg => ?_
  have hclU : closure G ⊆ (unitaryGroup ι 𝕜 : Set (Matrix ι ι 𝕜)) :=
    closure_minimal (fun x hx => mem_unitaryGroup_iff'.2 (hU x hx)) Morse.isClosed_unitaryGroup
  have hgU : gᴴ * g = 1 := mem_unitaryGroup_iff'.1 (hclU hg)
  have hc2 : Continuous fun x : Matrix ι ι 𝕜 => xᴴ * g :=
    continuous_id.matrix_conjTranspose.mul continuous_const
  have hnhds : (fun x : Matrix ι ι 𝕜 => xᴴ * g) ⁻¹' σ.φ.source ∈ 𝓝 g :=
    hc2.continuousAt.preimage_mem_nhds (by rw [hgU]; exact hO.mem_nhds hσ)
  obtain ⟨k, hkU, hkG⟩ := mem_closure_iff_nhds.1 hg _ hnhds
  have hkg : kᴴ * g ∈ closure G :=
    map_mem_closure (continuous_const.mul continuous_id) hg fun x hx => hmul _ (hstar k hkG) x hx
  have := hmul k hkG _ (key _ hkg hkU)
  rwa [← Matrix.mul_assoc, Morse.mul_conjTranspose_eq_one (hU k hkG), Matrix.one_mul] at this

/-- **The project's notion implies the textbook's.** -/
theorem P_imp_T [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W]
    (hG : Milnor.IsSliceSubmanifold 𝓘(ℝ, Matrix ι ι 𝕜) Z W G)
    (𝔤 : LieSubalgebra ℝ (Matrix ι ι 𝕜)) (h : Morse.IsMatrixGroup hG 𝔤) : T hG 𝔤 := by
  refine ⟨⟨fun g hg => mem_unitaryGroup_iff'.2 (h.unitary g hg), h.one_mem, h.mul_mem,
    fun A hA => ?_, isClosed_of_subgroup hG h.unitary h.mul_mem h.star_mem h.one_mem⟩,
    fun X => ⟨fun hX => ⟨h.skew X hX, h.exp_smul_mem hX⟩, fun ⟨_, hX⟩ => ?_⟩⟩
  · rw [Matrix.inv_eq_left_inv (h.unitary A hA)]
    exact h.star_mem A hA
  · have hc : HasDerivAt (fun t : ℝ => NormedSpace.exp (t • X)) X 0 := by
      simpa using hasDerivAt_exp_smul_const X (0 : ℝ)
    have hT := Morse.hasDerivAt_mem_tangentSubspace hG hc (Eventually.of_forall hX)
    rw [h.mem_tangentSubspace_iff] at hT
    simpa using hT

/-- Under the textbook notion, `𝔤` is contained in the tangent space of `G` at `1` (the curves
`t ↦ exp(tX)`), so `dim 𝔤 ≤ dim G`. -/
theorem le_tangentSubspace_of_T [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W]
    (hG : Milnor.IsSliceSubmanifold 𝓘(ℝ, Matrix ι ι 𝕜) Z W G)
    (𝔤 : LieSubalgebra ℝ (Matrix ι ι 𝕜)) (hT : T hG 𝔤) :
    𝔤.toSubmodule ≤ Morse.tangentSubspace hG ⟨1, hT.1.2.1⟩ := by
  intro X hX
  have hc : HasDerivAt (fun t : ℝ => NormedSpace.exp (t • X)) X 0 := by
    simpa using hasDerivAt_exp_smul_const X (0 : ℝ)
  have hmem : ∀ t : ℝ, NormedSpace.exp (t • X) ∈ G := ((hT.2 X).1 hX).2
  have hT' := Morse.hasDerivAt_mem_tangentSubspace hG hc (Eventually.of_forall hmem)
  have h0 : (⟨NormedSpace.exp ((0 : ℝ) • X),
      (Eventually.of_forall (f := 𝓝 (0 : ℝ)) hmem).self_of_nhds⟩ : G) = ⟨1, hT.1.2.1⟩ := by
    ext1; simp
  rw [h0] at hT'
  exact hT'

theorem finrank_le_of_T [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W]
    (hG : Milnor.IsSliceSubmanifold 𝓘(ℝ, Matrix ι ι 𝕜) Z W G)
    (𝔤 : LieSubalgebra ℝ (Matrix ι ι 𝕜)) (hT : T hG 𝔤) :
    finrank ℝ 𝔤.toSubmodule ≤ finrank ℝ Z := by
  have h1 : (1 : Matrix ι ι 𝕜) ∈ G := hT.1.2.1
  rw [← Morse.finrank_tanAt hG h1, Morse.tanAt_of_mem hG h1]
  exact Submodule.finrank_mono (le_tangentSubspace_of_T hG 𝔤 hT)

/-- **The textbook notion plus `dim G = dim 𝔤` gives the project's.** -/
theorem T_imp_P_of_finrank (hG : Milnor.IsSliceSubmanifold 𝓘(ℝ, Matrix ι ι 𝕜) Z W G)
    (𝔤 : LieSubalgebra ℝ (Matrix ι ι 𝕜)) (hT : T hG 𝔤)
    (hdim : finrank ℝ Z = finrank ℝ 𝔤.toSubmodule) : Morse.IsMatrixGroup hG 𝔤 := by
  obtain ⟨⟨hsub, -, hmul, hinv, -⟩, hiff⟩ := hT
  have hU : ∀ g ∈ G, gᴴ * g = 1 := fun g hg => mem_unitaryGroup_iff'.1 (hsub hg)
  have hstar : ∀ g ∈ G, gᴴ ∈ G := fun g hg => by
    have := hinv g hg
    rwa [Matrix.inv_eq_left_inv (hU g hg)] at this
  refine ⟨hU, hmul, hstar, fun X hX => ((hiff X).1 hX).1, fun g hg X hX => ?_,
    fun X hX => by simpa using ((hiff X).1 hX).2 1, hdim⟩
  obtain ⟨hs, he⟩ := (hiff X).1 hX
  have hgi : g⁻¹ = gᴴ := Matrix.inv_eq_left_inv (hU g hg)
  have hunit : IsUnit g := ⟨⟨g, gᴴ, Morse.mul_conjTranspose_eq_one (hU g hg), hU g hg⟩, rfl⟩
  refine (hiff _).2 ⟨?_, fun t => ?_⟩
  · rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, hs]
    simp [Matrix.mul_assoc]
  · have := Matrix.exp_conj g (t • X) hunit
    rw [hgi, Matrix.mul_smul, Matrix.smul_mul] at this
    rw [this]
    exact hmul _ (hmul _ hg _ (he t)) _ (hstar g hg)

/-- **Exact comparison**: the project's notion is the textbook's together with `dim G = dim 𝔤`. -/
theorem P_iff [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W]
    (hG : Milnor.IsSliceSubmanifold 𝓘(ℝ, Matrix ι ι 𝕜) Z W G)
    (𝔤 : LieSubalgebra ℝ (Matrix ι ι 𝕜)) :
    Morse.IsMatrixGroup hG 𝔤 ↔ T hG 𝔤 ∧ finrank ℝ Z = finrank ℝ 𝔤.toSubmodule :=
  ⟨fun h => ⟨P_imp_T hG 𝔤 h, h.finrank_eq⟩, fun h => T_imp_P_of_finrank hG 𝔤 h.1 h.2⟩

/-- **Agreement, given that the Lie algebra exhausts the tangent space at `1`** (`T₁G ⊆ 𝔤`: every
tangent vector generates a one-parameter subgroup of `G`; for a closed subgroup this is the
closed-subgroup theorem of Cartan / von Neumann, which is not in Mathlib). -/
theorem agree_of [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W]
    (hG : Milnor.IsSliceSubmanifold 𝓘(ℝ, Matrix ι ι 𝕜) Z W G)
    (𝔤 : LieSubalgebra ℝ (Matrix ι ι 𝕜)) (h1 : (1 : Matrix ι ι 𝕜) ∈ G)
    (htan : Morse.tangentSubspace hG ⟨1, h1⟩ ≤ 𝔤.toSubmodule) :
    Morse.IsMatrixGroup hG 𝔤 ↔ T hG 𝔤 := by
  refine ⟨P_imp_T hG 𝔤, fun hT => T_imp_P_of_finrank hG 𝔤 hT ?_⟩
  refine le_antisymm ?_ (finrank_le_of_T hG 𝔤 hT)
  rw [← Morse.finrank_tanAt hG h1, Morse.tanAt_of_mem hG h1]
  exact Submodule.finrank_mono htan

end RoundTrip.L2.Morse_IsMatrixGroup
