import Morse
import RoundTrip.Check
import RoundTrip.Blind.V14_23

open Matrix Topology Function

noncomputable section

namespace RoundTrip.V14_23

/-- The project's statement (universes instantiated at `0`; `Stiefel` is vocabulary, the definition
`stiefelSphere` is read as the `Nonempty` of its type):
(1) `exists_triv_of_orbitSection`: for a topological group `G` acting on `E` and `B`, an equivariant
continuous `p : E → B`, `G` transitive on `B` and a continuous local section `s₀` of the orbit map
`g ↦ g • b₀` near `b₀`, every `b` has an open `U ∋ b` with `p⁻¹(U) ≃ₜ U × p⁻¹(b₀)` over `U`
(Steenrod's argument);
(2), (3) the explicit section `s(F)` near `F₀` is unitary and `s(F) F₀ = F` (any `RCLike 𝕜`);
(4) `U(ι₁ ⊕ κ)` acts transitively on orthonormal `κ`-frames;
(5) the restriction `V_{κ₁ ⊕ κ₂} → V_{κ₂}` of frames is locally trivial with fibre `V_{κ₁}(𝕜^{ι₁})`;
(6) the orbit map `U(ι₁ ⊕ κ₂) → V_{κ₂}`, `g ↦ g F₀`, is locally trivial with fibre `U(ι₁)`;
(7) `V₁(𝕜^ι) ≃ₜ` the unit sphere of `EuclideanSpace 𝕜 ι`;
(8) `g ↦ g e_{m+1}`, `U(m ⊕ 1) → S` (unit sphere of `𝕜^{m+1}`) is locally trivial with fibre `U(m)`. -/
def A : Prop :=
  type_of% @Morse.Homotopy.exists_triv_of_orbitSection.{0, 0, 0} ∧
  type_of% @Morse.Homotopy.secMat_mem_unitaryGroup.{0, 0, 0} ∧
  type_of% @Morse.Homotopy.secMat_mul_baseFrame.{0, 0, 0} ∧
  type_of% @Morse.Homotopy.exists_unitary_smul_baseFrame.{0, 0, 0} ∧
  type_of% @Morse.Homotopy.stiefelRestrict_locallyTrivial.{0, 0, 0, 0} ∧
  type_of% @Morse.Homotopy.unitaryOrbit_locallyTrivial.{0, 0, 0} ∧
  (∀ (𝕜 : Type) [RCLike 𝕜] (ι : Type) [Fintype ι],
    Nonempty (↥(Morse.Homotopy.Stiefel 𝕜 ι (Fin 1)) ≃ₜ ↥(Metric.sphere (0 : EuclideanSpace 𝕜 ι) 1))) ∧
  type_of% @Morse.Homotopy.isLocallyTrivial_sphereOrbit.{0}

theorem A_holds : A :=
  ⟨@Morse.Homotopy.exists_triv_of_orbitSection.{0, 0, 0},
    @Morse.Homotopy.secMat_mem_unitaryGroup.{0, 0, 0}, @Morse.Homotopy.secMat_mul_baseFrame.{0, 0, 0},
    @Morse.Homotopy.exists_unitary_smul_baseFrame.{0, 0, 0},
    @Morse.Homotopy.stiefelRestrict_locallyTrivial.{0, 0, 0, 0},
    @Morse.Homotopy.unitaryOrbit_locallyTrivial.{0, 0, 0},
    fun 𝕜 _ ι _ => ⟨Morse.Homotopy.stiefelSphere 𝕜 ι⟩,
    @Morse.Homotopy.isLocallyTrivial_sphereOrbit.{0}⟩

section Glue

/-- A continuous bijection-inducing map: the quotient of a compact group by the stabilizer of a
point of a transitive Hausdorff `G`-space is the space. -/
theorem exists_quotHomeo {G X : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [TopologicalSpace X] [T2Space X] (H : Subgroup G) (f : G → X)
    (hf : Continuous f) (hsurj : Surjective f) (hfib : ∀ g g' : G, f g = f g' ↔ g⁻¹ * g' ∈ H) :
    ∃ h : (G ⧸ H) ≃ₜ X, ∀ g : G, h (g : G ⧸ H) = f g := by
  let F : G ⧸ H → X := Quotient.lift f fun a b hab =>
    (hfib a b).2 (QuotientGroup.leftRel_apply.1 hab)
  have hF : Continuous F := hf.quotient_lift _
  have hinj : Injective F := by
    intro x y hxy
    induction x using QuotientGroup.induction_on with | H a => ?_
    induction y using QuotientGroup.induction_on with | H b => ?_
    exact QuotientGroup.eq.2 ((hfib a b).1 hxy)
  have hs : Surjective F := fun x => let ⟨g, hg⟩ := hsurj x; ⟨g, hg⟩
  exact ⟨Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective F ⟨hinj, hs⟩) hF, fun _ => rfl⟩

instance (k : ℕ) : CompactSpace (U k) :=
  isCompact_iff_compactSpace.1 (Morse.isCompact_unitaryGroup (ι := Fin k) (𝕜 := ℂ))

/-- `Fin a ⊕ Fin b ≃ Fin n` (`a + b = n`), `inl i ↦ i`, `inr j ↦ a + j`. -/
def sumEquiv {a b n : ℕ} (h : a + b = n) : Fin a ⊕ Fin b ≃ Fin n :=
  finSumFinEquiv.trans (finCongr h)

@[simp] theorem sumEquiv_inl {a b n : ℕ} (h : a + b = n) (i : Fin a) :
    ((sumEquiv h (Sum.inl i) : Fin n) : ℕ) = i := by simp [sumEquiv]

@[simp] theorem sumEquiv_inr {a b n : ℕ} (h : a + b = n) (j : Fin b) :
    ((sumEquiv h (Sum.inr j) : Fin n) : ℕ) = a + j := by simp [sumEquiv]

/-- Reindexing `U(n) → U(Fin a ⊕ Fin b)` as a group homomorphism. -/
def reHom {a b n : ℕ} (h : a + b = n) : U n →* ↥(unitaryGroup (Fin a ⊕ Fin b) ℂ) where
  toFun g := Morse.Homotopy.unitaryCongr (sumEquiv h).symm g
  map_one' := Subtype.ext (by simp [Morse.Homotopy.unitaryCongr])
  map_mul' g g' := Subtype.ext (by
    simp [Morse.Homotopy.unitaryCongr, Matrix.submatrix_mul_equiv])

theorem continuous_reHom {a b n : ℕ} (h : a + b = n) : Continuous (reHom h) :=
  (Morse.Homotopy.unitaryCongr (𝕜 := ℂ) (sumEquiv h).symm).continuous

/-- The orbit map `U(n) → V_b(ℂ^{a+b})`: the last `b` columns. -/
def orb {a b n : ℕ} (h : a + b = n) (g : U n) :
    ↥(Morse.Homotopy.Stiefel ℂ (Fin a ⊕ Fin b) (Fin b)) :=
  Morse.Homotopy.unitaryOrbit ℂ (Fin a) (Fin b) (reHom h g)

theorem continuous_orb {a b n : ℕ} (h : a + b = n) : Continuous (orb h) :=
  Morse.Homotopy.continuous_unitaryOrbit.comp (continuous_reHom h)

theorem orb_apply {a b n : ℕ} (h : a + b = n) (g : U n) (i : Fin a ⊕ Fin b) (j : Fin b) :
    (orb h g : Matrix (Fin a ⊕ Fin b) (Fin b) ℂ) i j = (g : Mat n) (sumEquiv h i) (sumEquiv h (Sum.inr j)) := by
  simp [orb, Morse.Homotopy.coe_unitaryOrbit, toCols₂, reHom, Morse.Homotopy.unitaryCongr]

/-- The stabilizer of the base frame is Milnor's `U(a) = fixSub n a`. -/
theorem orb_eq_base_iff {a b n : ℕ} (h : a + b = n) (g : U n) :
    orb h g = Morse.Homotopy.stiefelBase ↔ g ∈ fixSub n a := by
  change _ ↔ (g : Mat n) * botProj n a = botProj n a
  constructor
  · intro hg
    have hc := fun i j => congrFun (congrFun (congrArg Subtype.val hg) i) j
    ext x y
    simp only [botProj, mul_diagonal, diagonal_apply]
    by_cases hy : (y : ℕ) < a
    · simp only [hy, if_true, mul_zero]
      split_ifs with hxy hxa <;> first | rfl | (subst hxy; exact absurd hy hxa)
    · simp only [hy, if_false, mul_one]
      obtain ⟨j, rfl⟩ : ∃ j : Fin b, sumEquiv h (Sum.inr j) = y := by
        refine ⟨⟨y - a, by omega⟩, Fin.ext ?_⟩
        simp only [sumEquiv_inr]; omega
      obtain ⟨i, rfl⟩ : ∃ i, sumEquiv h i = x := ⟨(sumEquiv h).symm x, by simp⟩
      have := hc i j
      rw [orb_apply] at this
      rw [this]
      simp only [Morse.Homotopy.stiefelBase, Morse.Homotopy.baseFrame]
      rcases i with i | i
      · simp [(sumEquiv h).injective.eq_iff]
      · simp [(sumEquiv h).injective.eq_iff, Matrix.one_apply]
  · intro hg
    apply Subtype.ext
    ext i j
    rw [orb_apply]
    have := congrFun (congrFun hg (sumEquiv h i)) (sumEquiv h (Sum.inr j))
    simp only [botProj, mul_diagonal, diagonal_apply, sumEquiv_inr] at this
    simp only [show ¬ (a + (j : ℕ) < a) by omega, if_false, mul_one] at this
    rw [this]
    simp only [Morse.Homotopy.stiefelBase, Morse.Homotopy.baseFrame, (sumEquiv h).injective.eq_iff]
    rcases i with i | i
    · simp
    · simp [Matrix.one_apply]

theorem orb_eq_iff {a b n : ℕ} (h : a + b = n) (g g' : U n) :
    orb h g = orb h g' ↔ g⁻¹ * g' ∈ fixSub n a := by
  rw [← orb_eq_base_iff h]
  change reHom h g • Morse.Homotopy.stiefelBase = reHom h g' • Morse.Homotopy.stiefelBase ↔
    reHom h (g⁻¹ * g') • Morse.Homotopy.stiefelBase = Morse.Homotopy.stiefelBase
  rw [map_mul, map_inv, mul_smul, inv_smul_eq_iff, eq_comm]

theorem orb_surjective {a b n : ℕ} (h : a + b = n)
    (htrans : ∀ F : ↥(Morse.Homotopy.Stiefel ℂ (Fin a ⊕ Fin b) (Fin b)),
      ∃ g : ↥(unitaryGroup (Fin a ⊕ Fin b) ℂ), g • Morse.Homotopy.stiefelBase = F) :
    Surjective (orb h) := by
  intro F
  obtain ⟨g, rfl⟩ := htrans F
  refine ⟨Morse.Homotopy.unitaryCongr (sumEquiv h) g, ?_⟩
  change reHom h _ • _ = _
  congr 1
  apply Subtype.ext
  simp [reHom, Morse.Homotopy.unitaryCongr]

/-- `U(n)/U(a) ≅ V_b(ℂ^{a+b})` (`a + b = n`), `gU(a) ↦` the last `b` columns of `g`. -/
theorem exists_stiefelHomeo {a b n : ℕ} (h : a + b = n)
    (htrans : ∀ F : ↥(Morse.Homotopy.Stiefel ℂ (Fin a ⊕ Fin b) (Fin b)),
      ∃ g : ↥(unitaryGroup (Fin a ⊕ Fin b) ℂ), g • Morse.Homotopy.stiefelBase = F) :
    ∃ Φ : (U n ⧸ fixSub n a) ≃ₜ ↥(Morse.Homotopy.Stiefel ℂ (Fin a ⊕ Fin b) (Fin b)),
      ∀ g : U n, Φ (g : U n ⧸ fixSub n a) = orb h g :=
  exists_quotHomeo _ _ (continuous_orb h) (orb_surjective h htrans) (orb_eq_iff h)

/-- **Local trivializations à la the project give Mathlib trivializations** (adapted from
Mathlib's `IsEvenlyCovered.toTrivialization'`). -/
theorem isBundle_of_isLocallyTrivial {F Z Y : Type} [TopologicalSpace F] [TopologicalSpace Z]
    [TopologicalSpace Y] [Nonempty F] {proj : Z → Y} (hc : Continuous proj)
    (hp : Morse.Homotopy.IsLocallyTrivial proj F) : IsBundle F proj := by
  classical
  intro y
  obtain ⟨U, hU, hyU, H, hH⟩ := hp y
  exact ⟨
  { toFun e := if he : proj e ∈ U then ⟨((H ⟨e, he⟩).1 : Y), (H ⟨e, he⟩).2⟩
      else ⟨y, Classical.arbitrary F⟩
    invFun xi := H.symm (if hx : xi.1 ∈ U then ⟨xi.1, hx⟩ else ⟨y, hyU⟩, xi.2)
    source := proj ⁻¹' U
    target := U ×ˢ Set.univ
    map_source' e (he : proj e ∈ U) := by simp [he]
    map_target' _ _ := Subtype.coe_prop _
    left_inv' e (he : proj e ∈ U) := by simp [he]
    right_inv' xi := by rintro ⟨hx, -⟩; simpa [hx] using fun h ↦ (h (H.symm _).2).elim
    open_source := hU.preimage hc
    open_target := hU.prod isOpen_univ
    continuousOn_toFun := continuousOn_iff_continuous_domRestrict.mpr <|
      ((continuous_subtype_val.prodMap continuous_id).comp H.continuous).congr
      fun ⟨e, (he : proj e ∈ U)⟩ ↦ by simp [Prod.map, he]
    continuousOn_invFun := continuousOn_iff_continuous_domRestrict.mpr <|
      ((continuous_subtype_val.comp H.symm.continuous).comp (by fun_prop :
        Continuous fun ui : ↥(U ×ˢ (Set.univ : Set F)) ↦ (⟨_, ui.2.1⟩, ui.1.2))).congr
        fun ⟨⟨x, i⟩, ⟨hx, _⟩⟩ ↦ by simp [hx]
    baseSet := U
    open_baseSet := hU
    source_eq := rfl
    target_eq := rfl
    proj_toFun e (he : proj e ∈ U) := by simp [he, hH] }, hyU⟩

/-- Local trivializations give local sections. -/
theorem hasLocalSections_of_isLocallyTrivial {F Z Y : Type} [TopologicalSpace F]
    [TopologicalSpace Z] [TopologicalSpace Y] [Nonempty F] {proj : Z → Y}
    (hp : Morse.Homotopy.IsLocallyTrivial proj F) : HasLocalSections proj := by
  classical
  intro y
  obtain ⟨U, hU, hyU, H, hH⟩ := hp y
  let f₀ : F := Classical.arbitrary F
  let s : Y → Z := fun z => if hz : z ∈ U then (H.symm (⟨z, hz⟩, f₀) : Z)
    else (H.symm (⟨y, hyU⟩, f₀) : Z)
  refine ⟨U, hU, hyU, s, ?_, fun z hz => ?_⟩
  · rw [continuousOn_iff_continuous_domRestrict]
    have : U.domRestrict s = fun z : U => (H.symm (z, f₀) : Z) := by
      funext z
      simp [s, Set.domRestrict, z.2]
    rw [this]
    exact continuous_subtype_val.comp (H.symm.continuous.comp (continuous_id.prodMk continuous_const))
  · simp only [s, dif_pos hz]
    rw [← hH, H.apply_symm_apply]

/-- Local triviality along a homeomorphism of the total space. -/
theorem isLocallyTrivial_comp {E E' B F : Type} [TopologicalSpace E] [TopologicalSpace E']
    [TopologicalSpace B] [TopologicalSpace F] {p : E → B} (hp : Morse.Homotopy.IsLocallyTrivial p F)
    (α : E' ≃ₜ E) : Morse.Homotopy.IsLocallyTrivial (p ∘ α) F := by
  intro b
  obtain ⟨U, hU, hb, φ, hφ⟩ := hp b
  refine ⟨U, hU, hb, (α.subtype (p := fun x => x ∈ (p ∘ α) ⁻¹' U) (q := fun y => y ∈ p ⁻¹' U)
    (fun _ => Iff.rfl)).trans φ, fun x => ?_⟩
  exact hφ _

/-- Project-style local triviality from the `∃ U, φ` form with subtype-valued first component. -/
theorem isLocallyTrivial_of {E B F : Type} [TopologicalSpace E] [TopologicalSpace B]
    [TopologicalSpace F] {p : E → B}
    (h : ∀ b : B, ∃ U : Set B, IsOpen U ∧ b ∈ U ∧ ∃ φ : p ⁻¹' U ≃ₜ U × F,
      ∀ x, (φ x).1 = ⟨p x, x.2⟩) : Morse.Homotopy.IsLocallyTrivial p F := fun b => by
  obtain ⟨U, hU, hb, φ, hφ⟩ := h b
  exact ⟨U, hU, hb, φ, fun x => congrArg Subtype.val (hφ x)⟩

/-- Change of the model fibre along a homeomorphism. -/
theorem isLocallyTrivial_fiber {E B F F' : Type} [TopologicalSpace E] [TopologicalSpace B]
    [TopologicalSpace F] [TopologicalSpace F'] {p : E → B}
    (hp : Morse.Homotopy.IsLocallyTrivial p F) (e : F ≃ₜ F') :
    Morse.Homotopy.IsLocallyTrivial p F' := fun b => by
  obtain ⟨U, hU, hb, φ, hφ⟩ := hp b
  exact ⟨U, hU, hb, φ.trans ((Homeomorph.refl U).prodCongr e), fun x => hφ x⟩

/-- `U(n) → U(n)/U(a)` is locally trivial with fibre `U(a)`, given the local triviality of the
orbit map `g ↦ g F₀` and the transitivity of `U` on frames. -/
theorem isLocallyTrivial_mk {a b n : ℕ} (h : a + b = n)
    (htrans : ∀ F : ↥(Morse.Homotopy.Stiefel ℂ (Fin a ⊕ Fin b) (Fin b)),
      ∃ g : ↥(unitaryGroup (Fin a ⊕ Fin b) ℂ), g • Morse.Homotopy.stiefelBase = F)
    (hloc : Morse.Homotopy.IsLocallyTrivial (Morse.Homotopy.unitaryOrbit ℂ (Fin a) (Fin b)) (U a)) :
    Morse.Homotopy.IsLocallyTrivial (QuotientGroup.mk : U n → U n ⧸ fixSub n a) (U a) := by
  obtain ⟨Φ, hΦ⟩ := exists_stiefelHomeo h htrans
  have h1 := (isLocallyTrivial_comp hloc
    (Morse.Homotopy.unitaryCongr (𝕜 := ℂ) (sumEquiv h).symm)).homeomorph_comp Φ.symm
  convert h1 using 1
  funext g
  change (g : U n ⧸ fixSub n a) = Φ.symm (orb h g)
  rw [← hΦ, Φ.symm_apply_apply]

theorem sum_normSq_eq_one_iff {ι : Type} [Fintype ι] (w : ι → ℂ) :
    ∑ i, Complex.normSq (w i) = 1 ↔ ∑ i, star (w i) * w i = 1 := by
  rw [← Complex.ofReal_inj, Complex.ofReal_sum, Complex.ofReal_one]
  simp only [Complex.normSq_eq_conj_mul_self, Complex.star_def]

/-- `V₁(ℂ^{m ⊕ 1}) ≃ₜ S^{2m+1} ⊆ ℂ^{m+1}` (B's sphere). -/
def sphHomeo (m : ℕ) : ↥(Morse.Homotopy.Stiefel ℂ (Fin m ⊕ Fin 1) (Fin 1)) ≃ₜ ↥(Sph m) where
  toFun F := ⟨fun i => F.1 ((sumEquiv (rfl : m + 1 = m + 1)).symm i) 0, by
    change ∑ i, Complex.normSq _ = 1
    rw [sum_normSq_eq_one_iff, Equiv.sum_comp (sumEquiv (rfl : m + 1 = m + 1)).symm
      (fun j => star (F.1 j 0) * F.1 j 0)]
    exact Morse.Homotopy.mem_stiefel_fin_one.1 F.2⟩
  invFun v := ⟨Matrix.of fun i _ => v.1 (sumEquiv (rfl : m + 1 = m + 1) i), by
    rw [Morse.Homotopy.mem_stiefel_fin_one]
    have := (sum_normSq_eq_one_iff v.1).1 v.2
    rw [← Equiv.sum_comp (sumEquiv (rfl : m + 1 = m + 1))] at this
    simpa using this⟩
  left_inv F := Subtype.ext (by ext i j; rw [Subsingleton.elim j 0]; simp)
  right_inv v := Subtype.ext (by ext i; simp)
  continuous_toFun := Continuous.subtype_mk (continuous_pi fun i =>
    continuous_subtype_val.matrix_elem _ _) _
  continuous_invFun := by
    refine Continuous.subtype_mk ?_ _
    refine continuous_matrix fun i j => ?_
    simp only [Matrix.of_apply]
    exact (continuous_apply _).comp continuous_subtype_val

/-- **Steenrod's theorem from A's `exists_triv_of_orbitSection`**: a coset map with local
sections is a bundle with fibre `H`. -/
theorem steenrod (hA1 : type_of% @Morse.Homotopy.exists_triv_of_orbitSection.{0, 0, 0})
    (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (H : Subgroup G)
    (hs : HasLocalSections (QuotientGroup.mk : G → G ⧸ H)) :
    IsBundle ↥H (QuotientGroup.mk : G → G ⧸ H) := by
  obtain ⟨V, hV, h1V, s, hsc, hsV⟩ := hs ((1 : G) : G ⧸ H)
  have key := hA1 (E := G) (B := G ⧸ H) (G := G) QuotientGroup.mk QuotientGroup.continuous_mk
    (fun g x => rfl) ((1 : G) : G ⧸ H)
    (fun b => by
      induction b using QuotientGroup.induction_on with | H a => ?_
      exact ⟨a, by change ((a * 1 : G) : G ⧸ H) = a; rw [mul_one]⟩)
    hV h1V (fun b => s b) hsc.domRestrict
    (fun b => by change ((s b * 1 : G) : G ⧸ H) = b; rw [mul_one]; exact hsV b b.2)
  have hfib : (QuotientGroup.mk : G → G ⧸ H) ⁻¹' {((1 : G) : G ⧸ H)} = (H : Set G) := by
    ext x
    simp [QuotientGroup.eq]
  have : Nonempty ↥H := ⟨1⟩
  exact isBundle_of_isLocallyTrivial QuotientGroup.continuous_mk
    (isLocallyTrivial_fiber (isLocallyTrivial_of key) (Homeomorph.setCongr hfib))

end Glue

/-- Conjuncts (1)–(6) of A (A without the two conjuncts mentioning the unit sphere, whose statement
involves the definition `stiefelSphere` through `sphereOrbit`); this is all A ⇒ B uses. -/
def A_core : Prop :=
  type_of% @Morse.Homotopy.exists_triv_of_orbitSection.{0, 0, 0} ∧
  type_of% @Morse.Homotopy.secMat_mem_unitaryGroup.{0, 0, 0} ∧
  type_of% @Morse.Homotopy.secMat_mul_baseFrame.{0, 0, 0} ∧
  type_of% @Morse.Homotopy.exists_unitary_smul_baseFrame.{0, 0, 0} ∧
  type_of% @Morse.Homotopy.stiefelRestrict_locallyTrivial.{0, 0, 0, 0} ∧
  type_of% @Morse.Homotopy.unitaryOrbit_locallyTrivial.{0, 0, 0}

theorem A_core_of_A : A → A_core := fun h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1⟩

theorem A_core_to_B : A_core → B := by
  rintro ⟨hA1, -, -, hA4, -, hA6⟩
  have htrans : ∀ {a b : ℕ} (F : ↥(Morse.Homotopy.Stiefel ℂ (Fin a ⊕ Fin b) (Fin b))),
      ∃ g : ↥(unitaryGroup (Fin a ⊕ Fin b) ℂ), g • Morse.Homotopy.stiefelBase = F :=
    fun F => hA4 F
  have hloc : ∀ a b : ℕ,
      Morse.Homotopy.IsLocallyTrivial (Morse.Homotopy.unitaryOrbit ℂ (Fin a) (Fin b)) (U a) :=
    fun a b => isLocallyTrivial_of fun F => hA6 F
  refine ⟨fun G _ _ _ H hs => steenrod hA1 G H hs, fun m => ?_⟩
  have L1 := isLocallyTrivial_mk (rfl : m + 1 = m + 1) htrans (hloc m 1)
  have L2 := isLocallyTrivial_mk (two_mul m).symm htrans (hloc m m)
  refine ⟨?_, hasLocalSections_of_isLocallyTrivial L1, hasLocalSections_of_isLocallyTrivial L2,
    isBundle_of_isLocallyTrivial QuotientGroup.continuous_mk L1,
    isBundle_of_isLocallyTrivial QuotientGroup.continuous_mk L2⟩
  obtain ⟨Φ, hΦ⟩ := exists_stiefelHomeo (rfl : m + 1 = m + 1) htrans
  refine ⟨Φ.trans (sphHomeo m), fun g => ?_, ?_⟩
  · funext i
    simp only [Homeomorph.trans_apply, hΦ]
    change (orb (rfl : m + 1 = m + 1) g : Matrix (Fin m ⊕ Fin 1) (Fin 1) ℂ)
      ((sumEquiv (rfl : m + 1 = m + 1)).symm i) 0 = (g : Mat (m + 1)) i (Fin.last m)
    rw [orb_apply, Equiv.apply_symm_apply]
    congr 1
  · have : (fun g : U (m + 1) => (Φ.trans (sphHomeo m)) (g : U (m + 1) ⧸ fixSub (m + 1) m)) =
        sphHomeo m ∘ (Morse.Homotopy.unitaryOrbit ℂ (Fin m) (Fin 1) ∘
          Morse.Homotopy.unitaryCongr (𝕜 := ℂ) (sumEquiv (rfl : m + 1 = m + 1)).symm) := by
      funext g
      simp only [Homeomorph.trans_apply, hΦ]
      rfl
    rw [this]
    exact isBundle_of_isLocallyTrivial ((sphHomeo m).continuous.comp
      (Morse.Homotopy.continuous_unitaryOrbit.comp (Morse.Homotopy.unitaryCongr _).continuous))
      ((isLocallyTrivial_comp (hloc m 1) _).homeomorph_comp _)

theorem A_to_B : A → B := fun h => A_core_to_B (A_core_of_A h)

/-- A's (6) for `𝕜 = ℂ`, `ι₁ = Fin m`, `κ₂ = Fin 1`: the bundle `U(m) → U(m ⊕ 1) → V₁ = S^{2m+1}`. -/
def A6C1 : Prop :=
  ∀ (m : ℕ) (b : ↥(Morse.Homotopy.Stiefel ℂ (Fin m ⊕ Fin 1) (Fin 1))),
    ∃ V : Set ↥(Morse.Homotopy.Stiefel ℂ (Fin m ⊕ Fin 1) (Fin 1)), IsOpen V ∧ b ∈ V ∧
      ∃ φ : ↑(Morse.Homotopy.unitaryOrbit ℂ (Fin m) (Fin 1) ⁻¹' V) ≃ₜ ↑V × ↥(unitaryGroup (Fin m) ℂ),
        ∀ x, (φ x).1 = ⟨Morse.Homotopy.unitaryOrbit ℂ (Fin m) (Fin 1) x, x.2⟩

theorem A6C1_of_A : A → A6C1 := fun h _ b => h.2.2.2.2.2.1 b

/-- **B ⇒ A's (6) for `ℂ`, `ι₁ = Fin m`, `κ₂ = Fin 1`**: B's bundle `g ↦ g e_{m+1}`,
`U(m+1) → S^{2m+1}` (Mathlib trivializations ⇒ the project's `IsLocallyTrivial`), reindexed. -/
theorem B_to_A6C1 : B → A6C1 := by
  intro hB m b
  obtain ⟨h, hh, hbun⟩ := (hB.2 m).1
  have hloc := Morse.Homotopy.isLocallyTrivial_of_trivializations hbun
  have heq : Morse.Homotopy.unitaryOrbit ℂ (Fin m) (Fin 1) =
      (sphHomeo m).symm ∘ ((fun g : U (m + 1) => h (g : U (m + 1) ⧸ fixSub (m + 1) m)) ∘
        Morse.Homotopy.unitaryCongr (𝕜 := ℂ) (sumEquiv (rfl : m + 1 = m + 1))) := by
    funext g
    rw [Function.comp_apply, Homeomorph.eq_symm_apply]
    apply Subtype.ext
    funext x
    simp only [Function.comp_apply, hh]
    have : (sumEquiv (rfl : m + 1 = m + 1)).symm (Fin.last m) = Sum.inr 0 := by
      rw [Equiv.symm_apply_eq]; ext; simp
    change (Morse.Homotopy.unitaryOrbit ℂ (Fin m) (Fin 1) g : Matrix (Fin m ⊕ Fin 1) (Fin 1) ℂ)
        ((sumEquiv (rfl : m + 1 = m + 1)).symm x) 0 =
      (g : Matrix (Fin m ⊕ Fin 1) (Fin m ⊕ Fin 1) ℂ) ((sumEquiv (rfl : m + 1 = m + 1)).symm x)
        ((sumEquiv (rfl : m + 1 = m + 1)).symm (Fin.last m))
    rw [this, Morse.Homotopy.coe_unitaryOrbit]
    rfl
  have hL : Morse.Homotopy.IsLocallyTrivial (Morse.Homotopy.unitaryOrbit ℂ (Fin m) (Fin 1)) (U m) := by
    rw [heq]
    exact (isLocallyTrivial_comp hloc _).homeomorph_comp _
  obtain ⟨V, hV, hbV, φ, hφ⟩ := hL b
  exact ⟨V, hV, hbV, φ, fun x => Subtype.ext (hφ x)⟩

#rt_check RoundTrip.V14_23.B_to_A6C1 [Morse.Homotopy.exists_triv_of_orbitSection, Morse.Homotopy.secMat_mem_unitaryGroup, Morse.Homotopy.secMat_mul_baseFrame, Morse.Homotopy.exists_unitary_smul_baseFrame, Morse.Homotopy.stiefelRestrict_locallyTrivial, Morse.Homotopy.unitaryOrbit_locallyTrivial, Morse.Homotopy.stiefelSphere, Morse.Homotopy.isLocallyTrivial_sphereOrbit]
#rt_overlap RoundTrip.V14_23.B_to_A6C1 [Morse.Homotopy.exists_triv_of_orbitSection, Morse.Homotopy.secMat_mem_unitaryGroup, Morse.Homotopy.secMat_mul_baseFrame, Morse.Homotopy.exists_unitary_smul_baseFrame, Morse.Homotopy.stiefelRestrict_locallyTrivial, Morse.Homotopy.unitaryOrbit_locallyTrivial, Morse.Homotopy.stiefelSphere, Morse.Homotopy.isLocallyTrivial_sphereOrbit]
#rt_check RoundTrip.V14_23.A_core_to_B [Morse.Homotopy.exists_triv_of_orbitSection, Morse.Homotopy.secMat_mem_unitaryGroup, Morse.Homotopy.secMat_mul_baseFrame, Morse.Homotopy.exists_unitary_smul_baseFrame, Morse.Homotopy.stiefelRestrict_locallyTrivial, Morse.Homotopy.unitaryOrbit_locallyTrivial, Morse.Homotopy.stiefelSphere, Morse.Homotopy.isLocallyTrivial_sphereOrbit]
#rt_check RoundTrip.V14_23.A_to_B [Morse.Homotopy.exists_triv_of_orbitSection, Morse.Homotopy.secMat_mem_unitaryGroup, Morse.Homotopy.secMat_mul_baseFrame, Morse.Homotopy.exists_unitary_smul_baseFrame, Morse.Homotopy.stiefelRestrict_locallyTrivial, Morse.Homotopy.unitaryOrbit_locallyTrivial, Morse.Homotopy.isLocallyTrivial_sphereOrbit]
#rt_overlap RoundTrip.V14_23.A_core_to_B [Morse.Homotopy.exists_triv_of_orbitSection, Morse.Homotopy.secMat_mem_unitaryGroup, Morse.Homotopy.secMat_mul_baseFrame, Morse.Homotopy.exists_unitary_smul_baseFrame, Morse.Homotopy.stiefelRestrict_locallyTrivial, Morse.Homotopy.unitaryOrbit_locallyTrivial, Morse.Homotopy.stiefelSphere, Morse.Homotopy.isLocallyTrivial_sphereOrbit]

end RoundTrip.V14_23

end
