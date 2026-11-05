import Morse
import RoundTrip.Check
import RoundTrip.Blind.V14_24

open Matrix Topology Function

noncomputable section

namespace RoundTrip.V14_24

/-- The project's statement (universes instantiated at `0`; `Grassmannian` (Hermitian projections
of trace `m`) and `frameSpan` (`F ↦ FFᴴ`) are vocabulary): for any `RCLike 𝕜`,
(1) Hermitian projections `P, Q` with `PQ = Q` and `tr P = tr Q` are equal;
(2) every Hermitian projection of trace `m` is `FFᴴ` for an orthonormal `m`-frame `F`;
(3) the Gram–Schmidt frame `σ(P)` is continuous where the columns of `P F₀` are independent;
(4) `U(ι₁ ⊕ Fin m)` acts transitively on `G_m(𝕜^{ι₁ ⊕ Fin m})` (by `P ↦ gPgᴴ`);
(5) `frameSpan : V_m(𝕜^{ι₁ ⊕ Fin m}) → G_m(𝕜^{ι₁ ⊕ Fin m})` is locally trivial with fibre `U(m)`;
(6) `Morse.grassmannian ι m = Grassmannian ℂ ι m` (`rfl`). -/
def A : Prop :=
  type_of% @Morse.Homotopy.eq_of_mul_eq_of_trace_eq.{0, 0} ∧
  type_of% @Morse.Homotopy.exists_frame_of_mem_grassmannian.{0, 0} ∧
  type_of% @Morse.Homotopy.continuousAt_gsFrame.{0, 0} ∧
  type_of% @Morse.Homotopy.exists_unitary_smul_grassBase.{0, 0} ∧
  type_of% @Morse.Homotopy.frameSpan_locallyTrivial.{0, 0} ∧
  type_of% @Morse.Homotopy.grassmannian_eq_Grassmannian.{0}

theorem A_holds : A :=
  ⟨@Morse.Homotopy.eq_of_mul_eq_of_trace_eq.{0, 0},
    @Morse.Homotopy.exists_frame_of_mem_grassmannian.{0, 0},
    @Morse.Homotopy.continuousAt_gsFrame.{0, 0},
    @Morse.Homotopy.exists_unitary_smul_grassBase.{0, 0},
    @Morse.Homotopy.frameSpan_locallyTrivial.{0, 0},
    @Morse.Homotopy.grassmannian_eq_Grassmannian.{0}⟩

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

/-- For an idempotent matrix, `rank = trace`. -/
theorem rank_eq_trace {k : ℕ} {P : Mat k} (hP : P * P = P) : ((P.rank : ℕ) : ℂ) = P.trace := by
  have he : IsIdempotentElem (Matrix.toLin' P) := by
    change Matrix.toLin' P * Matrix.toLin' P = Matrix.toLin' P
    rw [Module.End.mul_eq_comp, ← Matrix.toLin'_mul, hP]
  have h := (LinearMap.IsIdempotentElem.isProj_range _ he).trace
  rw [Matrix.trace_toLin'_eq] at h
  rw [h, Matrix.rank, Matrix.toLin'_apply']

/-- The blind Grassmannian (rank `m`) is the project's (trace `m`). -/
theorem grass_eq (k m : ℕ) : Morse.Homotopy.Grassmannian ℂ (Fin k) m = Grass k m := by
  ext P
  simp only [Grass, Morse.Homotopy.Grassmannian, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, h2, ?_⟩
    rw [← rank_eq_trace h2] at h3
    exact_mod_cast h3
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, h2, by rw [← rank_eq_trace h2, h3]⟩

theorem compl_mem {m : ℕ} {P : Mat (2 * m)}
    (hP : P ∈ Morse.Homotopy.Grassmannian ℂ (Fin (2 * m)) m) :
    1 - P ∈ Morse.Homotopy.Grassmannian ℂ (Fin (2 * m)) m := by
  obtain ⟨h1, h2, h3⟩ := hP
  refine ⟨by rw [conjTranspose_sub, conjTranspose_one, h1], ?_, ?_⟩
  · simp [Matrix.sub_mul, Matrix.mul_sub, h2]
  · rw [trace_sub, trace_one, h3, Fintype.card_fin]
    push_cast
    ring

/-- The complement `P ↦ 1 − P` of `G_m(ℂ^{2m})`. -/
def complHomeo (m : ℕ) : ↥(Morse.Homotopy.Grassmannian ℂ (Fin (2 * m)) m) ≃ₜ
    ↥(Morse.Homotopy.Grassmannian ℂ (Fin (2 * m)) m) where
  toFun P := ⟨1 - P.1, compl_mem P.2⟩
  invFun P := ⟨1 - P.1, compl_mem P.2⟩
  left_inv P := Subtype.ext (sub_sub_cancel 1 P.1)
  right_inv P := Subtype.ext (sub_sub_cancel 1 P.1)
  continuous_toFun := (continuous_const.sub continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_const.sub continuous_subtype_val).subtype_mk _

/-- `Θ : G_m(ℂ^{Fin m ⊕ Fin m}) ≃ₜ G_m(ℂ^{2m})` (blind), `Q ↦ 1 − Q` (reindexed). -/
def Θ (m : ℕ) : ↥(Morse.Homotopy.Grassmannian ℂ (Fin m ⊕ Fin m) m) ≃ₜ ↥(Grass (2 * m) m) :=
  (Morse.Homotopy.grassCongr (sumEquiv (two_mul m).symm)).trans
    ((complHomeo m).trans (Homeomorph.setCongr (grass_eq (2 * m) m)))

theorem coe_Θ (m : ℕ) (Q : ↥(Morse.Homotopy.Grassmannian ℂ (Fin m ⊕ Fin m) m)) :
    ((Θ m Q : ↥(Grass (2 * m) m)) : Mat (2 * m)) = 1 - reindex (sumEquiv (two_mul m).symm)
      (sumEquiv (two_mul m).symm) Q.1 := rfl

theorem topProj_eq (m : ℕ) : topProj (2 * m) m = 1 - botProj (2 * m) m := by
  ext x y
  simp only [topProj, botProj, diagonal_apply, Matrix.sub_apply, Matrix.one_apply]
  split_ifs <;> simp

/-- The map `V_m → G_m`, read on cosets: `gU(m) ↦ g topProj gᴴ`. -/
theorem coe_Θ_frameSpan_orb (m : ℕ) (g : U (2 * m)) :
    ((Θ m (Morse.Homotopy.frameSpan ℂ (Fin m ⊕ Fin m) m (orb (two_mul m).symm g)) :
      ↥(Grass (2 * m) m)) : Mat (2 * m)) = (g : Mat (2 * m)) * topProj (2 * m) m * star (g : Mat (2 * m)) := by
  set e := sumEquiv (two_mul m).symm
  have key : reindex e e ((orb (two_mul m).symm g : Matrix (Fin m ⊕ Fin m) (Fin m) ℂ) *
      (orb (two_mul m).symm g : Matrix (Fin m ⊕ Fin m) (Fin m) ℂ)ᴴ) =
      (g : Mat (2 * m)) * botProj (2 * m) m * star (g : Mat (2 * m)) := by
    have hR : ∀ x y, ((g : Mat (2 * m)) * botProj (2 * m) m * star (g : Mat (2 * m))) x y =
        ∑ k, (g : Mat (2 * m)) x k * (if (k : ℕ) < m then 0 else 1) * star ((g : Mat (2 * m)) y k) := by
      intro x y
      rw [Matrix.mul_apply]
      simp only [botProj, mul_diagonal, star_apply]
    ext x y
    rw [hR]
    simp only [reindex_apply, submatrix_apply, Matrix.mul_apply, conjTranspose_apply, orb_apply]
    rw [← Equiv.sum_comp e, Fintype.sum_sum_type]
    simp [e]
  rw [coe_Θ]
  change 1 - reindex e e ((orb (two_mul m).symm g : Matrix (Fin m ⊕ Fin m) (Fin m) ℂ) *
      (orb (two_mul m).symm g : Matrix (Fin m ⊕ Fin m) (Fin m) ℂ)ᴴ) = _
  rw [key, topProj_eq, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one,
    Matrix.mem_unitaryGroup_iff.1 g.2]

end Glue

theorem A_to_B : A → B := by
  rintro ⟨-, -, -, hA4, hA5, -⟩ m
  have hab : m + m = 2 * m := (two_mul m).symm
  have htrans : ∀ F : ↥(Morse.Homotopy.Stiefel ℂ (Fin m ⊕ Fin m) (Fin m)),
      ∃ g : ↥(unitaryGroup (Fin m ⊕ Fin m) ℂ), g • Morse.Homotopy.stiefelBase = F :=
    fun F => Morse.Homotopy.exists_unitary_smul_baseFrame F
  obtain ⟨Φ, hΦ⟩ := exists_stiefelHomeo hab htrans
  let fB : U (2 * m) → ↥(Grass (2 * m) m) := fun g =>
    Θ m (Morse.Homotopy.frameSpan ℂ (Fin m ⊕ Fin m) m (orb hab g))
  have hfB : ∀ g, (fB g : Mat (2 * m)) = (g : Mat (2 * m)) * topProj (2 * m) m * star (g : Mat (2 * m)) :=
    coe_Θ_frameSpan_orb m
  have hfBc : Continuous fB :=
    (Θ m).continuous.comp (Morse.Homotopy.continuous_frameSpan.comp (continuous_orb hab))
  refine ⟨?_, ⟨fun x => Θ m (Morse.Homotopy.frameSpan ℂ (Fin m ⊕ Fin m) m (Φ x)), fun g => ?_, ?_⟩⟩
  · -- `U(2m)/(U(m) × U(m)) ≅ G_m(ℂ^{2m})`
    have hsurj : Surjective fB := by
      intro P
      obtain ⟨g', hg'⟩ := hA4 ((Θ m).symm P)
      refine ⟨Morse.Homotopy.unitaryCongr (sumEquiv hab) g', ?_⟩
      have h1 : reHom hab (Morse.Homotopy.unitaryCongr (sumEquiv hab) g') = g' :=
        Subtype.ext (by simp [reHom, Morse.Homotopy.unitaryCongr])
      change Θ m (Morse.Homotopy.frameSpan ℂ _ m
        (Morse.Homotopy.unitaryOrbit ℂ (Fin m) (Fin m) (reHom hab _))) = P
      rw [h1]
      change Θ m (Morse.Homotopy.frameSpan ℂ _ m (g' • Morse.Homotopy.stiefelBase)) = P
      rw [Morse.Homotopy.frameSpan_smul]
      change Θ m (g' • Morse.Homotopy.grassBase ℂ (Fin m) m) = P
      rw [hg', Homeomorph.apply_symm_apply]
    have hfib : ∀ g g' : U (2 * m), fB g = fB g' ↔ g⁻¹ * g' ∈ blockSub (2 * m) m := by
      intro g g'
      have hg : star (g : Mat (2 * m)) * g = 1 := Matrix.UnitaryGroup.star_mul_self g
      have hg' : (g' : Mat (2 * m)) * star (g' : Mat (2 * m)) = 1 := Matrix.mem_unitaryGroup_iff.1 g'.2
      have hg2 : (g : Mat (2 * m)) * star (g : Mat (2 * m)) = 1 := Matrix.mem_unitaryGroup_iff.1 g.2
      rw [← Subtype.coe_inj, hfB, hfB]
      change _ ↔ star (g : Mat (2 * m)) * g' * topProj (2 * m) m =
        topProj (2 * m) m * (star (g : Mat (2 * m)) * g')
      set T := topProj (2 * m) m
      constructor
      · intro h
        calc star (g : Mat (2 * m)) * g' * T
            = star (g : Mat (2 * m)) * (g' * T * star (g' : Mat (2 * m))) * g' := by
              simp only [Matrix.mul_assoc, Matrix.UnitaryGroup.star_mul_self g', Matrix.mul_one]
          _ = star (g : Mat (2 * m)) * ((g : Mat (2 * m)) * T * star (g : Mat (2 * m))) * g' := by rw [h]
          _ = T * (star (g : Mat (2 * m)) * g') := by
              simp only [← Matrix.mul_assoc, hg, Matrix.one_mul]
      · intro h
        set k := star (g : Mat (2 * m)) * g'
        have hg'eq : (g' : Mat (2 * m)) = g * k := by
          rw [← Matrix.mul_assoc, hg2, Matrix.one_mul]
        have hk : k * star k = 1 := by
          simp only [k, star_mul, star_star, Matrix.mul_assoc]
          rw [← Matrix.mul_assoc (g' : Mat (2 * m)), hg', Matrix.one_mul, hg]
        symm
        calc (g' : Mat (2 * m)) * T * star (g' : Mat (2 * m))
            = g * (k * T) * star k * star (g : Mat (2 * m)) := by
              rw [hg'eq, star_mul]; simp only [Matrix.mul_assoc]
          _ = g * (T * k) * star k * star (g : Mat (2 * m)) := by rw [h]
          _ = g * T * (k * star k) * star (g : Mat (2 * m)) := by simp only [Matrix.mul_assoc]
          _ = g * T * star (g : Mat (2 * m)) := by rw [hk, Matrix.mul_one]
    obtain ⟨h, hh⟩ := exists_quotHomeo (blockSub (2 * m) m) fB hfBc hsurj hfib
    exact ⟨h, fun g => by rw [hh, hfB]⟩
  · change ((Θ m (Morse.Homotopy.frameSpan ℂ (Fin m ⊕ Fin m) m (Φ (g : U (2 * m) ⧸ fixSub (2 * m) m))) :
      ↥(Grass (2 * m) m)) : Mat (2 * m)) = _
    rw [hΦ]
    exact hfB g
  · -- the bundle `U(m) → U(2m)/U(m) → G_m(ℂ^{2m})`
    have hloc : Morse.Homotopy.IsLocallyTrivial (Morse.Homotopy.frameSpan ℂ (Fin m ⊕ Fin m) m)
        (U m) := isLocallyTrivial_of fun P => hA5 P
    exact isBundle_of_isLocallyTrivial ((Θ m).continuous.comp
      (Morse.Homotopy.continuous_frameSpan.comp Φ.continuous))
      ((isLocallyTrivial_comp hloc Φ).homeomorph_comp (Θ m))

/-- A's (4), (5) for `𝕜 = ℂ` and `ι₁ = Fin m` (the case B is about). -/
def A45C : Prop :=
  (∀ (m : ℕ) (P : ↥(Morse.Homotopy.Grassmannian ℂ (Fin m ⊕ Fin m) m)),
    ∃ g : ↥(unitaryGroup (Fin m ⊕ Fin m) ℂ), g • Morse.Homotopy.grassBase ℂ (Fin m) m = P) ∧
  (∀ (m : ℕ) (b : ↥(Morse.Homotopy.Grassmannian ℂ (Fin m ⊕ Fin m) m)),
    ∃ V : Set ↥(Morse.Homotopy.Grassmannian ℂ (Fin m ⊕ Fin m) m), IsOpen V ∧ b ∈ V ∧
      ∃ φ : ↑(Morse.Homotopy.frameSpan ℂ (Fin m ⊕ Fin m) m ⁻¹' V) ≃ₜ ↑V × ↥(unitaryGroup (Fin m) ℂ),
        ∀ x, (φ x).1 = ⟨Morse.Homotopy.frameSpan ℂ (Fin m ⊕ Fin m) m x, x.2⟩)

theorem A45C_of_A : A → A45C := fun h => ⟨fun _ P => h.2.2.2.1 P, fun _ b => h.2.2.2.2.1 b⟩

/-- **B ⇒ A's (4), (5) for `ℂ`, `ι₁ = Fin m`**: transitivity from B's homeomorphism
`U(2m)/(U(m) × U(m)) ≃ₜ G_m`, local triviality of `frameSpan` from B's bundle
`U(2m)/U(m) → G_m` (Mathlib trivializations ⇒ the project's `IsLocallyTrivial`, transported along
`U(2m)/U(m) ≃ₜ V_m` and `Θ`). -/
theorem B_to_A45C : B → A45C := by
  intro hB
  have hab : ∀ m : ℕ, m + m = 2 * m := fun m => (two_mul m).symm
  have hfo : ∀ (m : ℕ) (g : U (2 * m)), Morse.Homotopy.frameSpan ℂ (Fin m ⊕ Fin m) m (orb (hab m) g) =
      reHom (hab m) g • Morse.Homotopy.grassBase ℂ (Fin m) m := by
    intro m g
    change Morse.Homotopy.frameSpan ℂ _ m (reHom (hab m) g • Morse.Homotopy.stiefelBase) = _
    rw [Morse.Homotopy.frameSpan_smul]
    rfl
  refine ⟨fun m P => ?_, fun m b => ?_⟩
  · obtain ⟨⟨h, hh⟩, -⟩ := hB m
    obtain ⟨x, hx⟩ := h.surjective (Θ m P)
    induction x using QuotientGroup.induction_on with | H g => ?_
    refine ⟨reHom (hab m) g, (Θ m).injective (Subtype.ext ?_)⟩
    rw [← hx, hh, ← hfo]
    exact coe_Θ_frameSpan_orb m g
  · obtain ⟨-, f, hf, hbun⟩ := hB m
    have htrans : ∀ F : ↥(Morse.Homotopy.Stiefel ℂ (Fin m ⊕ Fin m) (Fin m)),
        ∃ g : ↥(unitaryGroup (Fin m ⊕ Fin m) ℂ), g • Morse.Homotopy.stiefelBase = F :=
      fun F => Morse.Homotopy.exists_unitary_smul_baseFrame F
    obtain ⟨Φ, hΦ⟩ := exists_stiefelHomeo (hab m) htrans
    have hloc : Morse.Homotopy.IsLocallyTrivial f (U m) :=
      Morse.Homotopy.isLocallyTrivial_of_trivializations hbun
    have hfs : (Morse.Homotopy.frameSpan ℂ (Fin m ⊕ Fin m) m) = (Θ m).symm ∘ (f ∘ Φ.symm) := by
      funext F
      obtain ⟨g, rfl⟩ := orb_surjective (hab m) htrans F
      simp only [Function.comp_apply, ← hΦ, Homeomorph.symm_apply_apply]
      rw [Homeomorph.eq_symm_apply, hΦ]
      exact Subtype.ext ((coe_Θ_frameSpan_orb m g).trans (hf g).symm)
    have hL : Morse.Homotopy.IsLocallyTrivial (Morse.Homotopy.frameSpan ℂ (Fin m ⊕ Fin m) m)
        (U m) := by
      rw [hfs]
      exact (isLocallyTrivial_comp hloc Φ.symm).homeomorph_comp (Θ m).symm
    obtain ⟨V, hV, hbV, φ, hφ⟩ := hL b
    exact ⟨V, hV, hbV, φ, fun x => Subtype.ext (hφ x)⟩

#rt_check RoundTrip.V14_24.B_to_A45C [Morse.Homotopy.eq_of_mul_eq_of_trace_eq, Morse.Homotopy.exists_frame_of_mem_grassmannian, Morse.Homotopy.continuousAt_gsFrame, Morse.Homotopy.exists_unitary_smul_grassBase, Morse.Homotopy.frameSpan_locallyTrivial, Morse.Homotopy.grassmannian_eq_Grassmannian]
#rt_overlap RoundTrip.V14_24.B_to_A45C [Morse.Homotopy.eq_of_mul_eq_of_trace_eq, Morse.Homotopy.exists_frame_of_mem_grassmannian, Morse.Homotopy.continuousAt_gsFrame, Morse.Homotopy.exists_unitary_smul_grassBase, Morse.Homotopy.frameSpan_locallyTrivial, Morse.Homotopy.grassmannian_eq_Grassmannian]
#rt_check RoundTrip.V14_24.A_to_B [Morse.Homotopy.eq_of_mul_eq_of_trace_eq, Morse.Homotopy.exists_frame_of_mem_grassmannian, Morse.Homotopy.continuousAt_gsFrame, Morse.Homotopy.exists_unitary_smul_grassBase, Morse.Homotopy.frameSpan_locallyTrivial, Morse.Homotopy.grassmannian_eq_Grassmannian]
#rt_overlap RoundTrip.V14_24.A_to_B [Morse.Homotopy.eq_of_mul_eq_of_trace_eq, Morse.Homotopy.exists_frame_of_mem_grassmannian, Morse.Homotopy.continuousAt_gsFrame, Morse.Homotopy.exists_unitary_smul_grassBase, Morse.Homotopy.frameSpan_locallyTrivial, Morse.Homotopy.grassmannian_eq_Grassmannian]

end RoundTrip.V14_24

end
