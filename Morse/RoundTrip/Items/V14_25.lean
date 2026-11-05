import Morse
import RoundTrip.Check
import RoundTrip.Blind.V14_25

open Matrix Topology Function

noncomputable section

namespace RoundTrip.V14_25

/-- The project's statement (universes instantiated at `0`; `SphereConnected`, `unitaryInclC` are
vocabulary): (1) for any `RCLike 𝕜` with `SphereConnected 𝕜 d` (`π_i S^{dn−1} = 0` for
`i + 2 ≤ dn`), `π_i V_k(𝕜ⁿ) = 0` for `i + 1 ≤ d(n − k) + d − 1`; (2) the inclusion
`U(m) → U(m + k)` (`S ↦ diag(S, I_k)`, index type `Fin m ⊕ Fin k`) is bijective on `π_i` for
`i + 2 ≤ dm + d − 1`, at every base point; (3) `SphereConnected ℂ 2`; (4) `π_i V_k(ℂⁿ) = 0` for
`i ≤ 2(n − k)`; (5) `π_i U(m) → π_i U(m + k)` bijective for `i < 2m`; (6) onto for `i ≤ 2m`. -/
def A : Prop :=
  type_of% @Morse.Homotopy.subsingleton_pi_stiefel.{0} ∧
  type_of% @Morse.Homotopy.bijective_homotopyGroupMap_unitaryIncl.{0} ∧
  type_of% @Morse.Homotopy.sphereConnected_complex ∧
  type_of% @Morse.Homotopy.subsingleton_pi_stiefel_complex ∧
  type_of% @Morse.Homotopy.bijective_homotopyGroupMap_unitaryIncl_complex ∧
  type_of% @Morse.Homotopy.surjective_homotopyGroupMap_unitaryIncl_complex

theorem A_holds : A :=
  ⟨@Morse.Homotopy.subsingleton_pi_stiefel.{0}, @Morse.Homotopy.bijective_homotopyGroupMap_unitaryIncl.{0},
    @Morse.Homotopy.sphereConnected_complex, @Morse.Homotopy.subsingleton_pi_stiefel_complex,
    @Morse.Homotopy.bijective_homotopyGroupMap_unitaryIncl_complex,
    @Morse.Homotopy.surjective_homotopyGroupMap_unitaryIncl_complex⟩

section Glue

/-- B's `piMap` is the project's `homotopyGroupMap`. -/
theorem piMap_eq {K X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y)) (x : X) :
    piMap (N := K) f x = Morse.Homotopy.homotopyGroupMap f x := by
  funext c
  induction c using Quotient.inductionOn
  rfl

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

/-- `B ↦ diag(B, 1)` is Milnor's embedding `fromBlocks B 0 0 1` after reindexing. -/
theorem blockIncl_eq {n : ℕ} (g : U n) :
    blockIncl (n + 1) n (g : Mat n) =
      ((Morse.Homotopy.unitaryCongr (𝕜 := ℂ) (sumEquiv (rfl : n + 1 = n + 1))
        (Morse.Homotopy.unitaryInclC (𝕜 := ℂ) n 1 g) : _) : Mat (n + 1)) := by
  ext x y
  obtain ⟨i, rfl⟩ : ∃ i, sumEquiv (rfl : n + 1 = n + 1) i = x := ⟨(sumEquiv rfl).symm x, by simp⟩
  obtain ⟨j, rfl⟩ : ∃ j, sumEquiv (rfl : n + 1 = n + 1) j = y := ⟨(sumEquiv rfl).symm y, by simp⟩
  simp only [blockIncl, Matrix.of_apply, Morse.Homotopy.coe_unitaryCongr, Matrix.reindex_apply,
    Matrix.submatrix_apply, Equiv.symm_apply_apply, Morse.Homotopy.unitaryInclC,
    ContinuousMap.coe_mk, Morse.Homotopy.coe_unitaryIncl]
  rcases i with i | i <;> rcases j with j | j
  · simp
  · simp
  · simp
  · simp [Matrix.one_apply, Fin.ext_iff]

/-- `diag(S, I_k)` in `Fin (m + k)` coordinates is the project's `unitaryInclC m k`, reindexed. -/
theorem blockIncl_eq' {m k : ℕ} (g : U m) :
    blockIncl (m + k) m (g : Mat m) =
      ((Morse.Homotopy.unitaryCongr (𝕜 := ℂ) (sumEquiv (rfl : m + k = m + k))
        (Morse.Homotopy.unitaryInclC (𝕜 := ℂ) m k g) : _) : Mat (m + k)) := by
  ext x y
  obtain ⟨i, rfl⟩ : ∃ i, sumEquiv (rfl : m + k = m + k) i = x := ⟨(sumEquiv rfl).symm x, by simp⟩
  obtain ⟨j, rfl⟩ : ∃ j, sumEquiv (rfl : m + k = m + k) j = y := ⟨(sumEquiv rfl).symm y, by simp⟩
  simp only [blockIncl, Matrix.of_apply, Morse.Homotopy.coe_unitaryCongr, Matrix.reindex_apply,
    Matrix.submatrix_apply, Equiv.symm_apply_apply, Morse.Homotopy.unitaryInclC,
    ContinuousMap.coe_mk, Morse.Homotopy.coe_unitaryIncl]
  rcases i with i | i <;> rcases j with j | j
  · simp
  · simp
  · simp
  · simp [Matrix.one_apply, Fin.ext_iff]

/-- The project's `S ↦ diag(S, I_k)` in `Fin (m + k)` coordinates. -/
def J (m k : ℕ) : C(U m, U (m + k)) :=
  ((Morse.Homotopy.unitaryCongr (𝕜 := ℂ) (sumEquiv (rfl : m + k = m + k)) :
    ↥(unitaryGroup (Fin m ⊕ Fin k) ℂ) ≃ₜ U (m + k)) : C(_, U (m + k))).comp
    (Morse.Homotopy.unitaryInclC (𝕜 := ℂ) m k)

theorem J_apply (m k : ℕ) (g : U m) : (J m k g : Mat (m + k)) = blockIncl (m + k) m g :=
  (blockIncl_eq' g).symm

theorem blockIncl_blockIncl {m k : ℕ} (A : Mat m) :
    blockIncl (m + k + 1) (m + k) (blockIncl (m + k) m A) = blockIncl (m + (k + 1)) m A := by
  ext x y
  simp only [blockIncl, Matrix.of_apply]
  by_cases h1 : (x : ℕ) < m ∧ (y : ℕ) < m
  · have h2 : (x : ℕ) < m + k ∧ (y : ℕ) < m + k := ⟨by omega, by omega⟩
    rw [dif_pos h2, dif_pos h1, dif_pos h1]
  · rw [dif_neg h1]
    by_cases h2 : (x : ℕ) < m + k ∧ (y : ℕ) < m + k
    · rw [dif_pos h2, dif_neg h1]
      simp [Matrix.one_apply, Fin.ext_iff]
    · rw [dif_neg h2]

end Glue

theorem A_to_B : A → B := by
  rintro ⟨-, -, -, hA4, hA5, hA6⟩ m
  refine ⟨fun r => ?_, fun i hi x => ?_⟩
  · set n := m + r
    let eH : ↥(unitaryGroup (Fin n ⊕ Fin 1) ℂ) ≃ₜ U (n + 1) :=
      Morse.Homotopy.unitaryCongr (sumEquiv (rfl : n + 1 = n + 1))
    let κ : C(U n, U (n + 1)) :=
      (eH : C(↥(unitaryGroup (Fin n ⊕ Fin 1) ℂ), U (n + 1))).comp
        (Morse.Homotopy.unitaryInclC (𝕜 := ℂ) n 1)
    have hcomp : ∀ (K : Type) (g : U n), piMap (N := K) κ g =
        Morse.Homotopy.homotopyGroupMap (eH : C(↥(unitaryGroup (Fin n ⊕ Fin 1) ℂ), U (n + 1)))
            (Morse.Homotopy.unitaryInclC (𝕜 := ℂ) n 1 g) ∘
          Morse.Homotopy.homotopyGroupMap (Morse.Homotopy.unitaryInclC (𝕜 := ℂ) n 1) g := by
      intro K g
      rw [piMap_eq, Morse.Homotopy.homotopyGroupMap_comp]
    have hbij : ∀ j, j + 1 ≤ 2 * m → ∀ g : U n, Bijective (piMap (N := Fin j) κ g) := by
      intro j hj g
      rw [hcomp]
      exact (Morse.Homotopy.bijective_homotopyGroupMap_homeomorph _ _).comp
        (hA5 (m := n) (k := 1) (i := j) (by omega) g)
    refine ⟨κ, fun g => (blockIncl_eq g).symm, hbij, fun k hk g => ?_, fun hr g => ?_⟩
    · refine ⟨MulEquiv.ofBijective (Morse.Homotopy.homotopyGroupHom (N := Fin (k + 1)) κ g)
        (by have := hbij (k + 1) (by omega) g; rw [piMap_eq] at this; exact this), ?_⟩
      exact (piMap_eq _ _).symm
    · rw [hcomp]
      exact (Morse.Homotopy.bijective_homotopyGroupMap_homeomorph _ _).surjective.comp
        (hA6 (m := n) (k := 1) (i := 2 * m) (by omega) g)
  · obtain ⟨Φ, -⟩ := exists_stiefelHomeo (two_mul m).symm
      (fun F => Morse.Homotopy.exists_unitary_smul_baseFrame F)
    let e : ↥(Morse.Homotopy.Stiefel ℂ (Fin m ⊕ Fin m) (Fin m)) ≃ₜ
        ↥(Morse.Homotopy.Stiefel ℂ (Fin (2 * m)) (Fin m)) :=
      Morse.Homotopy.stiefelCongr (sumEquiv (two_mul m).symm) (Equiv.refl _)
    exact Morse.Homotopy.subsingleton_homotopyGroup_of_homeomorph (Φ.trans e) x
      (hA4 (k := m) (n := 2 * m) (i := i) (by omega) (by omega) _)

/-- A's conjuncts (5), (6): the complex stability `U(m) → U(m + k)`. -/
def A56 : Prop :=
  type_of% @Morse.Homotopy.bijective_homotopyGroupMap_unitaryIncl_complex ∧
  type_of% @Morse.Homotopy.surjective_homotopyGroupMap_unitaryIncl_complex

theorem A56_of_A : A → A56 := fun h => ⟨h.2.2.2.2.1, h.2.2.2.2.2⟩

/-- **B ⇒ A's complex stability (5), (6)**, by chaining B's one-step inclusions
`U(m + k) → U(m + k + 1)` (B at `m + k`, `r = 0`). -/
theorem B_to_A56 : B → A56 := by
  intro hB
  have step : ∀ m k : ℕ, ∃ ι : C(U (m + k), U (m + k + 1)),
      (∀ g, (ι g : Mat (m + k + 1)) = blockIncl (m + k + 1) (m + k) g) ∧
      (∀ j, j + 1 ≤ 2 * (m + k) → ∀ g,
        Bijective (Morse.Homotopy.homotopyGroupMap (N := Fin j) ι g)) ∧
      (∀ g, Surjective (Morse.Homotopy.homotopyGroupMap (N := Fin (2 * (m + k))) ι g)) := by
    intro m k
    obtain ⟨ι, h1, h2, -, h4⟩ := (hB (m + k)).1 0
    exact ⟨ι, h1, fun j hj g => by rw [← piMap_eq]; exact h2 j hj g,
      fun g => by rw [← piMap_eq]; exact h4 rfl g⟩
  have hJ : ∀ m k : ℕ,
      (∀ i, i < 2 * m → ∀ S, Bijective (Morse.Homotopy.homotopyGroupMap (N := Fin i) (J m k) S)) ∧
      (∀ i, i ≤ 2 * m → ∀ S, Surjective (Morse.Homotopy.homotopyGroupMap (N := Fin i) (J m k) S)) := by
    intro m k
    induction k with
    | zero =>
      have h0 : J m 0 = ContinuousMap.id (U m) := by
        ext S x y
        rw [J_apply]
        simp only [blockIncl, Matrix.of_apply, ContinuousMap.id_apply]
        rw [dif_pos ⟨x.2, y.2⟩]
        rfl
      rw [h0]
      refine ⟨fun i _ S => ?_, fun i _ S => ?_⟩
      · rw [Morse.Homotopy.homotopyGroupMap_id]; exact bijective_id
      · rw [Morse.Homotopy.homotopyGroupMap_id]; exact surjective_id
    | succ k ih =>
      obtain ⟨ι, hι, hb, hs⟩ := step m k
      have hcomp : J m (k + 1) = ι.comp (J m k) := by
        ext S x y
        change (J m (k + 1) S : Mat (m + k + 1)) x y = (ι (J m k S) : Mat (m + k + 1)) x y
        rw [J_apply, hι, J_apply, blockIncl_blockIncl]
      rw [hcomp]
      refine ⟨fun i hi S => ?_, fun i hi S => ?_⟩
      · rw [Morse.Homotopy.homotopyGroupMap_comp]
        exact (hb i (by omega) _).comp (ih.1 i hi S)
      · rw [Morse.Homotopy.homotopyGroupMap_comp]
        refine Surjective.comp ?_ (ih.2 i hi S)
        by_cases hik : i + 1 ≤ 2 * (m + k)
        · exact (hb i hik _).surjective
        · obtain rfl : k = 0 := by omega
          obtain rfl : i = 2 * m := by omega
          exact hs _
  refine ⟨fun {m k i} hi S => ?_, fun {m k i} hi S => ?_⟩
  · have h := (hJ m k).1 i hi S
    rw [J, Morse.Homotopy.homotopyGroupMap_comp] at h
    exact (Bijective.of_comp_iff' (Morse.Homotopy.bijective_homotopyGroupMap_homeomorph _ _) _).1 h
  · have h := (hJ m k).2 i hi S
    rw [J, Morse.Homotopy.homotopyGroupMap_comp] at h
    exact h.of_comp_left (Morse.Homotopy.bijective_homotopyGroupMap_homeomorph _ _).injective

#rt_check RoundTrip.V14_25.B_to_A56 [Morse.Homotopy.subsingleton_pi_stiefel, Morse.Homotopy.bijective_homotopyGroupMap_unitaryIncl, Morse.Homotopy.sphereConnected_complex, Morse.Homotopy.subsingleton_pi_stiefel_complex, Morse.Homotopy.bijective_homotopyGroupMap_unitaryIncl_complex, Morse.Homotopy.surjective_homotopyGroupMap_unitaryIncl_complex]
#rt_overlap RoundTrip.V14_25.B_to_A56 [Morse.Homotopy.subsingleton_pi_stiefel, Morse.Homotopy.bijective_homotopyGroupMap_unitaryIncl, Morse.Homotopy.sphereConnected_complex, Morse.Homotopy.subsingleton_pi_stiefel_complex, Morse.Homotopy.bijective_homotopyGroupMap_unitaryIncl_complex, Morse.Homotopy.surjective_homotopyGroupMap_unitaryIncl_complex]
#rt_check RoundTrip.V14_25.A_to_B [Morse.Homotopy.subsingleton_pi_stiefel, Morse.Homotopy.bijective_homotopyGroupMap_unitaryIncl, Morse.Homotopy.sphereConnected_complex, Morse.Homotopy.subsingleton_pi_stiefel_complex, Morse.Homotopy.bijective_homotopyGroupMap_unitaryIncl_complex, Morse.Homotopy.surjective_homotopyGroupMap_unitaryIncl_complex]
#rt_overlap RoundTrip.V14_25.A_to_B [Morse.Homotopy.subsingleton_pi_stiefel, Morse.Homotopy.bijective_homotopyGroupMap_unitaryIncl, Morse.Homotopy.sphereConnected_complex, Morse.Homotopy.subsingleton_pi_stiefel_complex, Morse.Homotopy.bijective_homotopyGroupMap_unitaryIncl_complex, Morse.Homotopy.surjective_homotopyGroupMap_unitaryIncl_complex]

end RoundTrip.V14_25

end
