import Morse
import RoundTrip.Check
import RoundTrip.Bridge
import RoundTrip.Blind.V14_22

/-! Round trip for V14_22 (Theorem 23.3). `B_to_A` is proved by instantiating `B` at the project's
own `SU(2m)` (slice submanifold of `M_{2m}(ℂ)`, model changed to `ℝⁿ` as in `Items/V7_28.lean`,
packaged by `RoundTrip.Bridge`); `A_to_B34` proves `B`'s last two conjuncts from `A`. -/

open Set Topology Function Module Matrix
open scoped ContDiff Manifold

noncomputable section

set_option linter.unusedSectionVars false

namespace RoundTrip.V14_22

/-- The project's statement (universes instantiated at `0`): for `|ι| = 2m` (`ι` nonempty) and every
`P ∈ G_m(ℂ^ι)` (`Morse.grassmannian ι m`, Hermitian projections of trace `m`),
`π_i(G_m(ℂ^ι), P) ≃ π_{i+1}(SU(ι), I)` for `i ≤ 2m` (bijection of sets), and `≃*` for
`1 ≤ i ≤ 2m`. -/
def A : Prop :=
  type_of% @Morse.theorem_23_3.{0} ∧ type_of% @Morse.theorem_23_3_mulEquiv.{0}

theorem A_holds : A := ⟨@Morse.theorem_23_3.{0}, @Morse.theorem_23_3_mulEquiv.{0}⟩


namespace Model

section ModelChange
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- A linear equivalence `Z ≃ ℝᵐ`, `m = dim Z` (copied from `Items/V7_28.lean`). -/
def eZ (Z : Type) [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z] :
    Z ≃L[ℝ] Bridge.Rn (finrank ℝ Z) :=
  ContinuousLinearEquiv.ofFinrankEq (by simp)

variable {Z : Type} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
  {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] {N : Set V}

/-- A slice chart modelled on `Z`, read in `ℝᵐ` (copied from `Items/V7_28.lean`). -/
def chartRn (σ : Milnor.SliceChart 𝓘(ℝ, V) Z W N) :
    Milnor.SliceChart 𝓘(ℝ, V) (Bridge.Rn (finrank ℝ Z)) W N where
  φ := σ.φ.trans ((eZ Z).prodCongr (ContinuousLinearEquiv.refl ℝ W)).toDiffeomorph.toPartialDiffeomorph
  x₀ := σ.x₀
  x₀_mem := σ.x₀_mem
  x₀_source := ⟨σ.x₀_source, trivial⟩
  slice := fun p hp => σ.slice p hp.1

/-- A slice submanifold modelled on `Z` is one modelled on `ℝᵐ` (copied from `Items/V7_28.lean`). -/
theorem isSliceRn (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N) :
    Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Bridge.Rn (finrank ℝ Z)) W N :=
  fun p hp => ⟨chartRn (hN p hp).choose, ⟨(hN p hp).choose_spec, trivial⟩⟩
end ModelChange

open scoped Morse.MatrixInner

variable (k : ℕ) [Nonempty (Fin k)]

/-- The dimension of `SU(k)`. -/
abbrev nSU : ℕ := finrank ℝ ↥(Morse.specialSkewHermitian (Fin k)).toSubmodule

theorem hSU : Milnor.IsSliceSubmanifold 𝓘(ℝ, Matrix (Fin k) (Fin k) ℂ) (Bridge.Rn (nSU k))
    (↥(Morse.hermitian ℂ (Fin k)) × ℝ) (Matrix.specialUnitaryGroup (Fin k) ℂ : Set (Matrix (Fin k) (Fin k) ℂ)) :=
  isSliceRn Morse.isSliceSubmanifold_specialUnitaryGroup

/-- `SU(k)` as an abstract Riemannian manifold (the project's slice submanifold, induced metric). -/
abbrev MSU : Type := Bridge.Sub (hSU k)

/-- The identity `M_k(ℂ)` (Frobenius) → `Fin k → Fin k → ℂ` (sup norm). -/
def Lid : Matrix (Fin k) (Fin k) ℂ →L[ℝ] (Fin k → Fin k → ℂ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun A => A, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }

theorem Lid_apply (A : Matrix (Fin k) (Fin k) ℂ) : Lid k A = A := rfl

/-- The embedding `ψ : SU(k) → M_k(ℂ)`. -/
def ψ : MSU k → (Fin k → Fin k → ℂ) := fun x => Lid k (Bridge.incl (hSU k) x)


omit [Nonempty (Fin k)] in
/-- `U(k)` is path connected (`π₀ U(k) ≅ π₀ S¹`, the project's stability from `U(1) = S¹`). -/
theorem pathConnected_U (hk : 1 ≤ k) : PathConnectedSpace ↥(Matrix.unitaryGroup (Fin k) ℂ) := by
  obtain ⟨e⟩ := Morse.Homotopy.nonempty_pi_unitary_equiv_circle (m := k) (i := 0) hk (by norm_num)
  have : Subsingleton (π_ 0 Circle 1) := Morse.Homotopy.subsingleton_pi_zero 1
  have h1 : Subsingleton (π_ 0 ↥(Matrix.unitaryGroup (Fin k) ℂ) 1) := e.subsingleton
  have hz : Subsingleton (ZerothHomotopy ↥(Matrix.unitaryGroup (Fin k) ℂ)) :=
    (HomotopyGroup.pi0EquivZerothHomotopy (x := (1 : ↥(Matrix.unitaryGroup (Fin k) ℂ)))).symm.subsingleton
  exact ⟨⟨1⟩, fun a b => Quotient.exact (s := pathSetoid _)
    (Subsingleton.elim (α := ZerothHomotopy _) (ZerothHomotopy.mk a) (ZerothHomotopy.mk b))⟩

omit [Nonempty (Fin k)] in
/-- `SU(k)` is path connected (`U(k) ≅ S¹ × SU(k)`, the project's `unitaryProd`). -/
theorem pathConnected_SU (hk : 1 ≤ k) :
    PathConnectedSpace ↥(Matrix.specialUnitaryGroup (Fin k) ℂ) := by
  have := pathConnected_U k hk
  let i₀ : Fin k := ⟨0, hk⟩
  refine Function.Surjective.pathConnectedSpace (f := fun g => (Morse.Homotopy.unitaryProd i₀ g).2)
    (fun s => ⟨(Morse.Homotopy.unitaryProd i₀).symm (1, s), by simp⟩)
    (continuous_snd.comp (Morse.Homotopy.unitaryProd i₀).continuous)

instance : ConnectedSpace (MSU k) := by
  have : PathConnectedSpace ↥(Matrix.specialUnitaryGroup (Fin k) ℂ) :=
    pathConnected_SU k (Fin.pos_iff_nonempty.2 inferInstance)
  exact inferInstanceAs (ConnectedSpace ↥(Matrix.specialUnitaryGroup (Fin k) ℂ))

theorem isSUModel_ψ : IsSUModel (n := nSU k) k (ψ k) := by
  have hc : ContMDiff 𝓘(ℝ, Bridge.Rn (nSU k)) 𝓘(ℝ, Fin k → Fin k → ℂ) ∞ (ψ k) :=
    (Lid k).contDiff.contMDiff.comp Bridge.contMDiff_incl
  refine ⟨hc, ?_, ?_, fun x v w => ?_⟩
  · exact Topology.IsEmbedding.subtypeVal
  · exact Subtype.range_val
  · have hd : ∀ u, dMat k (ψ k) x u = Bridge.D (hSU k) x u := by
      intro u
      have h1 : MDifferentiableAt 𝓘(ℝ, Bridge.Rn (nSU k)) 𝓘(ℝ, Matrix (Fin k) (Fin k) ℂ)
          (Bridge.incl (hSU k)) x :=
        Bridge.contMDiff_incl.mdifferentiableAt (by simp)
      have h2 := mfderiv_comp x ((Lid k).mdifferentiableAt) h1
      unfold dMat
      change mfderiv _ _ ((Lid k) ∘ Bridge.incl (hSU k)) x u = _
      rw [h2, ContinuousLinearMap.mfderiv_eq]
      rfl
    rw [hd, hd, Bridge.inner_eq]
    change RCLike.re (trace ((Bridge.D (hSU k) x v)ᴴ * Bridge.D (hSU k) x w)) = _
    rw [Matrix.trace_mul_comm, ← Matrix.conjTranspose_conjTranspose (Bridge.D (hSU k) x w * _),
      Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.trace_conjTranspose]
    simp

end Model

section Transport

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

theorem reindex_mem_su {ι ι' : Type} [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι']
    (e : ι ≃ ι') {g : Matrix ι ι ℂ} (hg : g ∈ Matrix.specialUnitaryGroup ι ℂ) :
    reindex e e g ∈ Matrix.specialUnitaryGroup ι' ℂ := by
  rw [Matrix.mem_specialUnitaryGroup_iff] at hg ⊢
  exact ⟨Morse.Homotopy.reindex_mem_unitaryGroup e hg.1, by rw [Matrix.det_reindex_self, hg.2]⟩

/-- Reindexing is a homeomorphism of special unitary groups. -/
def suCongr {ι ι' : Type} [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι'] (e : ι ≃ ι') :
    ↥(Matrix.specialUnitaryGroup ι ℂ) ≃ₜ ↥(Matrix.specialUnitaryGroup ι' ℂ) where
  toFun g := ⟨reindex e e g.1, reindex_mem_su e g.2⟩
  invFun g := ⟨reindex e.symm e.symm g.1, reindex_mem_su e.symm g.2⟩
  left_inv g := Subtype.ext (by simp)
  right_inv g := Subtype.ext (by simp)
  continuous_toFun := Continuous.subtype_mk (continuous_subtype_val.matrix_submatrix _ _) _
  continuous_invFun := Continuous.subtype_mk (continuous_subtype_val.matrix_submatrix _ _) _

end Transport

/-- The last two conjuncts of B (Milnor's "hence `π_iG_m(ℂ^{2m}) ≅ π_{i+1}SU(2m)`"), which do not
involve the model `M` of `SU(2m)`. -/
def B34 : Prop := ∀ m : ℕ,
  (∀ i : ℕ, i ≤ 2 * m → ∀ (P : ↥(Grass (2 * m) m)) (h : SU (2 * m)),
    Nonempty (π_ i ↥(Grass (2 * m) m) P ≃ π_ (i + 1) (SU (2 * m)) h)) ∧
  (∀ k : ℕ, k + 1 ≤ 2 * m → ∀ (P : ↥(Grass (2 * m) m)) (h : SU (2 * m)),
    Nonempty (π_ (k + 1) ↥(Grass (2 * m) m) P ≃* π_ (k + 2) (SU (2 * m)) h))

/-- **A ⇒ B's last two conjuncts** (all `m`, all base points; `m = 0`: both sides are points). -/
theorem A_to_B34 : A → B34 := by
  rintro ⟨hA1, hA2⟩ m
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · refine ⟨fun i hi P h => ?_, fun k hk => absurd hk (by omega)⟩
    obtain rfl : i = 0 := by omega
    have : IsEmpty (Fin (2 * 0)) := ⟨fun i => absurd i.2 (by omega)⟩
    have : Subsingleton ↥(Grass (2 * 0) 0) := ⟨fun a b => Subtype.ext (funext fun i => isEmptyElim i)⟩
    have : Subsingleton (SU (2 * 0)) := ⟨fun a b => Subtype.ext (funext fun i => isEmptyElim i)⟩
    have : Subsingleton (π_ 0 ↥(Grass (2 * 0) 0) P) :=
      Morse.Homotopy.subsingleton_homotopyGroup_of_subsingleton P
    have : Subsingleton (π_ 1 (SU (2 * 0)) h) :=
      Morse.Homotopy.subsingleton_homotopyGroup_of_subsingleton h
    exact ⟨equivOfSubsingletonOfSubsingleton (fun _ => Classical.arbitrary _)
      (fun _ => Classical.arbitrary _)⟩
  · have : Nonempty (Fin (2 * m)) := ⟨⟨0, by omega⟩⟩
    have hcard : Fintype.card (Fin (2 * m)) = 2 * m := Fintype.card_fin _
    let gH : ↥(Morse.grassmannian (Fin (2 * m)) m) ≃ₜ ↥(Grass (2 * m) m) :=
      Homeomorph.setCongr (grass_eq _ _)
    refine ⟨fun i hi P h => ?_, fun k hk P h => ?_⟩
    · obtain ⟨E⟩ := hA1 hcard (gH.symm P) hi
      exact ⟨(Morse.Homotopy.piEquivOfHomeomorph gH.symm rfl i).trans (E.trans
        (Morse.Homotopy.piEquivOfHomeomorph (Homeomorph.mulLeft h) (mul_one h) (i + 1)))⟩
    · obtain ⟨E⟩ := hA2 hcard (gH.symm P) hk
      obtain ⟨E₁⟩ := Morse.Homotopy.nonempty_mulEquiv_of_homeomorph gH.symm (x := P) rfl k
      obtain ⟨E₃⟩ := Morse.Homotopy.nonempty_mulEquiv_of_homeomorph (Homeomorph.mulLeft h)
        (x := 1) (mul_one h) (k + 1)
      exact ⟨E₁.trans (E.trans E₃)⟩

/-- **B ⇒ A**: instantiate B at the project's own `SU(2m)` (the slice submanifold of `M_{2m}(ℂ)`,
packaged as an abstract Riemannian manifold by `RoundTrip.Bridge`, `ψ` = the inclusion); its last two
conjuncts are A for `ι = Fin (2m)`, then reindex `ι ≃ Fin (2m)`. -/
theorem B_to_A : B → A := by
  intro hB
  have key : ∀ m : ℕ, 1 ≤ m →
      (∀ i : ℕ, i ≤ 2 * m → ∀ (P : ↥(Grass (2 * m) m)) (h : SU (2 * m)),
        Nonempty (π_ i ↥(Grass (2 * m) m) P ≃ π_ (i + 1) (SU (2 * m)) h)) ∧
      (∀ k : ℕ, k + 1 ≤ 2 * m → ∀ (P : ↥(Grass (2 * m) m)) (h : SU (2 * m)),
        Nonempty (π_ (k + 1) ↥(Grass (2 * m) m) P ≃* π_ (k + 2) (SU (2 * m)) h)) := by
    intro m hm
    have : Nonempty (Fin (2 * m)) := ⟨⟨0, by omega⟩⟩
    let p : Model.MSU (2 * m) := ⟨1, (Matrix.specialUnitaryGroup (Fin (2 * m)) ℂ).one_mem⟩
    let q : Model.MSU (2 * m) := ⟨-1, Morse.neg_one_mem_su (ι := Fin (2 * m)) (m := m) (by simp)⟩
    obtain ⟨-, -, h3, h4⟩ := hB m (Model.nSU (2 * m)) (Model.MSU (2 * m)) (Model.ψ (2 * m))
      (Model.isSUModel_ψ (2 * m)) p q rfl rfl
    exact ⟨h3, h4⟩
  refine ⟨fun {ι} _ _ _ {m} hcard P {i} hi => ?_, fun {ι} _ _ _ {m} hcard P {j} hj => ?_⟩
  · have hm : 1 ≤ m := by have := Fintype.card_pos (α := ι); omega
    let e : ι ≃ Fin (2 * m) := Fintype.equivFinOfCardEq hcard
    let gH : ↥(Morse.grassmannian ι m) ≃ₜ ↥(Grass (2 * m) m) :=
      (Morse.Homotopy.grassCongr e).trans (Homeomorph.setCongr (grass_eq _ _))
    obtain ⟨E⟩ := (key m hm).1 i hi (gH P) 1
    exact ⟨(Morse.Homotopy.piEquivOfHomeomorph gH rfl i).trans (E.trans
      (Morse.Homotopy.piEquivOfHomeomorph (suCongr e).symm (Subtype.ext (by simp [suCongr])) (i + 1)))⟩
  · have hm : 1 ≤ m := by have := Fintype.card_pos (α := ι); omega
    let e : ι ≃ Fin (2 * m) := Fintype.equivFinOfCardEq hcard
    let gH : ↥(Morse.grassmannian ι m) ≃ₜ ↥(Grass (2 * m) m) :=
      (Morse.Homotopy.grassCongr e).trans (Homeomorph.setCongr (grass_eq _ _))
    obtain ⟨E⟩ := (key m hm).2 j hj (gH P) 1
    obtain ⟨E₁⟩ := Morse.Homotopy.nonempty_mulEquiv_of_homeomorph gH (x := P) rfl j
    obtain ⟨E₃⟩ := Morse.Homotopy.nonempty_mulEquiv_of_homeomorph (suCongr e).symm
      (x := 1) (y := ⟨1, (Matrix.specialUnitaryGroup ι ℂ).one_mem⟩)
      (Subtype.ext (by simp [suCongr])) (j + 1)
    exact ⟨E₁.trans (E.trans E₃)⟩

/-! `A → B` is not proved. `B`'s first two conjuncts are Theorem 23.3's main assertion, on every
abstract Riemannian model `M` of `SU(2m)`: the inclusion `Ω^d → Ω(M; I, −I)` induces bijections
(group isomorphisms) on `π_i`, `i ≤ 2m`, and a map `j : G_m(ℂ^{2m}) → Ω` with
`ψ(j P t) = exp(t·iπ(2P − I))` induces bijections on `π_i`, `i ≤ 2m`. `A` (`theorem_23_3`,
`theorem_23_3_mulEquiv`) only asserts the existence of abstract bijections / isomorphisms
`π_i G_m(ℂ^{2m}) ≅ π_{i+1} SU(2m)` — Milnor's "hence" clause — which is `B34` (proved from `A` below,
`A_to_B34`). The inclusion statements are not consequences of such abstract isomorphisms; the project
has their ingredients only elsewhere (`theorem_22_1_bijective`, `minPathsHomotopyEquiv`,
`lemma_23_1`) and only for its embedded `SU(2m)`, so for an abstract `M` a transport along `ψ`
(that `ψ` is a diffeomorphism onto the slice submanifold, Milnor's `d`-topology on paths in `M` vs
the project's `PathSp`) would also be needed. -/

#rt_check RoundTrip.V14_22.B_to_A [Morse.theorem_23_3, Morse.theorem_23_3_mulEquiv]
#rt_check RoundTrip.V14_22.A_to_B34 [Morse.theorem_23_3, Morse.theorem_23_3_mulEquiv]
#rt_overlap RoundTrip.V14_22.B_to_A [Morse.theorem_23_3, Morse.theorem_23_3_mulEquiv]
#rt_overlap RoundTrip.V14_22.A_to_B34 [Morse.theorem_23_3, Morse.theorem_23_3_mulEquiv]

end RoundTrip.V14_22
