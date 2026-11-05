import Morse
import RoundTrip.Check
import RoundTrip.Blind.V14_27

open Matrix Function Topology

noncomputable section

namespace RoundTrip.V14_27

/-- The project's statement (universes instantiated at `0`; `Morse.Homotopy.suInclC`, the
inclusion `SU(n) → U(n)`, is vocabulary). `Morse.Homotopy.unitaryProd` is a definition (a
homeomorphism `U(n) ≃ₜ S¹ × SU(n)` whose first component is `det`); it is read as the existence
of such a homeomorphism with that first component. The three theorems are taken as they are:
(1) for every finite nonempty `ι`: `U(ι) ≃ₜ S¹ × SU(ι)` over `det`;
(2) `det : U(ι) → S¹` is locally trivial with fibre `SU(ι)` (`ι` nonempty);
(3) `π_{j+2}(S¹, z) = 0` for every `z`;
(4) Lemma 23.4: for nonempty finite `ι`, every `j` and every `A ∈ SU(ι)`, the inclusion induces a
bijection `π_{j+2}(SU(ι), A) → π_{j+2}(U(ι), A)`. -/
def A : Prop :=
  (∀ {ι : Type} [Fintype ι] [DecidableEq ι] (_i₀ : ι),
    ∃ h : ↥(Matrix.unitaryGroup ι ℂ) ≃ₜ Circle × ↥(Matrix.specialUnitaryGroup ι ℂ),
      ∀ g, ((h g).1 : ℂ) = (g : Matrix ι ι ℂ).det) ∧
  type_of% @Morse.Homotopy.isLocallyTrivial_detCircle.{0} ∧
  type_of% @Morse.Homotopy.subsingleton_pi_circle ∧
  type_of% @Morse.Homotopy.bijective_homotopyGroupMap_suInclC.{0}

theorem A_holds : A :=
  ⟨fun i₀ => ⟨Morse.Homotopy.unitaryProd i₀, fun _ => rfl⟩,
    @Morse.Homotopy.isLocallyTrivial_detCircle.{0}, @Morse.Homotopy.subsingleton_pi_circle,
    @Morse.Homotopy.bijective_homotopyGroupMap_suInclC.{0}⟩

/-! ### Glue -/

section Glue

open Morse.Homotopy

/-- Left translation by `g` moves the base point `1` to `g`. -/
def bc {G : Type} [TopologicalSpace G] [Group G] [ContinuousMul G] (g : G) (n : ℕ) :
    π_ n G 1 ≃ π_ n G g :=
  piEquivOfHomeomorph (Homeomorph.mulLeft g) (mul_one g) n

/-- The same as groups. -/
theorem bcM {G : Type} [TopologicalSpace G] [Group G] [ContinuousMul G] (g : G) (n : ℕ) :
    Nonempty (π_ (n + 1) G 1 ≃* π_ (n + 1) G g) :=
  nonempty_mulEquiv_of_homeomorph (Homeomorph.mulLeft g) (mul_one g) n

/-- Two one-point sets. -/
def equivOfSubsingletons {α β : Type} [Subsingleton α] [Subsingleton β] [Inhabited α]
    [Inhabited β] : α ≃ β where
  toFun _ := default
  invFun _ := default
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _

/-- Two trivial groups. -/
def mulEquivOfSubsingletons {α β : Type} [Mul α] [Mul β] [Subsingleton α] [Subsingleton β]
    [Inhabited α] [Inhabited β] : α ≃* β :=
  { equivOfSubsingletons with map_mul' := fun _ _ => Subsingleton.elim _ _ }

/-- `π_0(X, x)` trivial ⇒ `X` path-connected. -/
theorem pathConnected_of_pi0 {X : Type} [TopologicalSpace X] {x : X}
    (h : Subsingleton (π_ 0 X x)) : PathConnectedSpace X :=
  have := h
  pathConnectedSpace_iff_zerothHomotopy.2
    ⟨⟨ZerothHomotopy.mk x⟩, (HomotopyGroup.pi0EquivZerothHomotopy (x := x)).symm.subsingleton⟩

/-- `U(m)` is path-connected for `m ≥ 1` (from the project's `π_0 U(m) ≅ π_0 S¹`,
`Morse.Homotopy.nonempty_pi_unitary_equiv_circle`, item V14_29, outside this item). -/
theorem pathConnected_U {m : ℕ} (hm : 1 ≤ m) : PathConnectedSpace (U m) := by
  obtain ⟨e⟩ := nonempty_pi_unitary_equiv_circle (m := m) (i := 0) hm (by norm_num)
  have := subsingleton_pi_zero (1 : Circle)
  exact pathConnected_of_pi0 e.subsingleton

theorem subsingleton_U0 : Subsingleton (U 0) :=
  ⟨fun _ _ => Subtype.ext (Matrix.ext fun i => Fin.elim0 i)⟩

theorem subsingleton_SU0 : Subsingleton (SU 0) :=
  ⟨fun _ _ => Subtype.ext (Matrix.ext fun i => Fin.elim0 i)⟩

/-- `SU(1)` is a point. -/
theorem subsingleton_SU1 : Subsingleton (SU 1) := by
  refine ⟨fun a b => Subtype.ext (Matrix.ext fun i j => ?_)⟩
  have ha := (Matrix.mem_specialUnitaryGroup_iff.1 a.2).2
  have hb := (Matrix.mem_specialUnitaryGroup_iff.1 b.2).2
  rw [Matrix.det_fin_one] at ha hb
  fin_cases i; fin_cases j
  simp [ha, hb]

/-- A copy of the project's construction `U(n) ≃ₜ S¹ × SU(n)`, `g ↦ (det g, g D(det g)⁻¹)`
(`Morse.Homotopy.unitaryProd`, banned here), from the project's auxiliary `detCircle`,
`diagCircle` (vocabulary outside the item). -/
def prodHomeo {ι : Type} [Fintype ι] [DecidableEq ι] (i₀ : ι) :
    ↥(Matrix.unitaryGroup ι ℂ) ≃ₜ Circle × ↥(Matrix.specialUnitaryGroup ι ℂ) where
  toFun g := (detCircle ι g, ⟨(g * (diagCircle i₀ (detCircle ι g))⁻¹ : unitaryGroup ι ℂ),
    mem_specialUnitaryGroup_iff.2 ⟨Subtype.coe_prop _, det_mul_inv_diagCircle i₀ g⟩⟩)
  invFun q := ⟨q.2.1, (mem_specialUnitaryGroup_iff.1 q.2.2).1⟩ * diagCircle i₀ q.1
  left_inv g := by
    change (g * (diagCircle i₀ (detCircle ι g))⁻¹) * diagCircle i₀ (detCircle ι g) = g
    exact inv_mul_cancel_right _ _
  right_inv q := by
    obtain ⟨z, s⟩ := q
    have hz : detCircle ι (⟨s.1, (mem_specialUnitaryGroup_iff.1 s.2).1⟩ * diagCircle i₀ z) = z := by
      ext
      rw [coe_detCircle, Submonoid.coe_mul, det_mul, det_diagCircle,
        (mem_specialUnitaryGroup_iff.1 s.2).2, one_mul]
    refine Prod.ext hz (Subtype.ext ?_)
    change ((⟨s.1, _⟩ * diagCircle i₀ z * (diagCircle i₀ (detCircle ι
      (⟨s.1, (mem_specialUnitaryGroup_iff.1 s.2).1⟩ * diagCircle i₀ z)))⁻¹ :
        unitaryGroup ι ℂ) : Matrix ι ι ℂ) = s.1
    rw [hz, mul_inv_cancel_right]
  continuous_toFun := by
    refine (detCircle ι).continuous.prodMk (Continuous.subtype_mk ?_ _)
    exact continuous_subtype_val.comp (continuous_id.mul
      ((continuous_diagCircle i₀).comp (detCircle ι).continuous).inv)
  continuous_invFun := by
    refine Continuous.mul ?_ ((continuous_diagCircle i₀).comp continuous_fst)
    exact (continuous_subtype_val.comp continuous_snd).subtype_mk _

end Glue

open Morse.Homotopy in
/-- `A ⇒ B`. For `j = k + 2`: (4) at `h` gives `π_{k+2}(SU(m), h) ≃* π_{k+2}(U(m), h)`, moved to
any base point `g` by left translation. For `j = 0`: both `π_0` are points — `SU(m)` is
path-connected as the image of `U(m)` under the projection `S¹ × SU(m) → SU(m)` of (1), and `U(m)`
is path-connected by the project's `π_0 U(m) ≅ π_0 S¹` (outside the item: `A` says nothing about
`π_0`). For `m = 0` both groups are points. -/
theorem A_to_B : A → B := by
  rintro ⟨hprod, -, -, hbij⟩ m
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · have := subsingleton_U0
    have := subsingleton_SU0
    refine ⟨fun j _ g h => ?_, fun k g h => ?_⟩
    · have := subsingleton_homotopyGroup_of_subsingleton (N := Fin j) g
      have := subsingleton_homotopyGroup_of_subsingleton (N := Fin j) h
      exact ⟨equivOfSubsingletons⟩
    · have := subsingleton_homotopyGroup_of_subsingleton (N := Fin (k + 2)) g
      have := subsingleton_homotopyGroup_of_subsingleton (N := Fin (k + 2)) h
      exact ⟨mulEquivOfSubsingletons⟩
  · have : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
    have grp : ∀ k (g : U m) (h : SU m), Nonempty (π_ (k + 2) (U m) g ≃* π_ (k + 2) (SU m) h) := by
      intro k g h
      have e := MulEquiv.ofBijective (homotopyGroupHom (N := Fin (k + 2)) (suInclC (Fin m)) h)
        (hbij (j := k) h)
      obtain ⟨b₁⟩ := bcM (suInclC (Fin m) h) (k + 1)
      obtain ⟨b₂⟩ := bcM g (k + 1)
      exact ⟨b₂.symm.trans (b₁.trans e.symm)⟩
    refine ⟨fun j hj g h => ?_, grp⟩
    rcases j with _ | _ | k
    · have hU : PathConnectedSpace (U m) := pathConnected_U hm
      obtain ⟨Φ, -⟩ := hprod (ι := Fin m) ⟨0, hm⟩
      have hSU : PathConnectedSpace (SU m) :=
        (Prod.snd_surjective.comp Φ.surjective).pathConnectedSpace (continuous_snd.comp Φ.continuous)
      have := subsingleton_pi_zero g
      have := subsingleton_pi_zero h
      exact ⟨equivOfSubsingletons⟩
    · exact absurd rfl hj
    · obtain ⟨e⟩ := grp k g h
      exact ⟨e.toEquiv⟩

open Morse.Homotopy in
/-- `B ⇒ A`. Only (3) comes from `B`: at `m = 1`, `SU(1)` is a point, so `π_{j+2} U(1) = 0`, and
`U(1) ≅ S¹` (the project's `unitaryOneHomeomorph`, item V14_29, outside this item). The rest is
re-proved outright, not from `B`: (1) is a copy of the project's construction, (2) follows from
(1), and (4) is the project's exact-sequence argument (`bijective_homotopyGroupMap_of_fiber`,
`bijective_homotopyGroupMap_fiberIncl`, outside the item) for the Serre fibration (2), fed with
(3). `B` (abstract isomorphisms, `Fin m` only) cannot give the bijectivity of the specific map
induced by the inclusion. -/
theorem B_to_A : B → A := by
  intro hB
  have hprod : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (_i₀ : ι),
      ∃ h : ↥(Matrix.unitaryGroup ι ℂ) ≃ₜ Circle × ↥(Matrix.specialUnitaryGroup ι ℂ),
        ∀ g, ((h g).1 : ℂ) = (g : Matrix ι ι ℂ).det :=
    fun i₀ => ⟨prodHomeo i₀, fun _ => rfl⟩
  have hloc : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι],
      IsLocallyTrivial (detCircle ι) ↥(Matrix.specialUnitaryGroup ι ℂ) := by
    intro ι _ _ _
    obtain ⟨Φ, hΦ⟩ := hprod (Classical.arbitrary ι)
    exact isLocallyTrivial_of_homeomorph Φ fun g => Circle.ext (hΦ g)
  have hcirc : ∀ {j : ℕ} (z : Circle), Subsingleton (π_ (j + 2) Circle z) := by
    intro j z
    have := subsingleton_SU1
    have := subsingleton_homotopyGroup_of_subsingleton (N := Fin (j + 2)) (1 : SU 1)
    obtain ⟨e⟩ := (hB 1).2 j (unitaryOneHomeomorph.symm z) 1
    have : Subsingleton (π_ (j + 2) (U 1) (unitaryOneHomeomorph.symm z)) := e.toEquiv.subsingleton
    exact (piEquivOfHomeomorph unitaryOneHomeomorph (unitaryOneHomeomorph.apply_symm_apply z)
      (j + 2)).symm.subsingleton
  refine ⟨hprod, hloc, hcirc, fun {ι} _ _ _ {j} A => ?_⟩
  have hp := (hloc (ι := ι)).isSerreFibration
  exact bijective_homotopyGroupMap_of_fiber (suFibre A) (suInclC ι) (fun _ => rfl) A rfl
    (bijective_homotopyGroupMap_fiberIncl hp _
      (subsingleton_homotopyGroup_option (hcirc (j := j + 1) _))
      (hcirc _))

#rt_check RoundTrip.V14_27.A_to_B [Morse.Homotopy.unitaryProd, Morse.Homotopy.isLocallyTrivial_detCircle, Morse.Homotopy.subsingleton_pi_circle, Morse.Homotopy.bijective_homotopyGroupMap_suInclC]
#rt_check RoundTrip.V14_27.B_to_A [Morse.Homotopy.unitaryProd, Morse.Homotopy.isLocallyTrivial_detCircle, Morse.Homotopy.subsingleton_pi_circle, Morse.Homotopy.bijective_homotopyGroupMap_suInclC]
#rt_overlap RoundTrip.V14_27.B_to_A [Morse.Homotopy.unitaryProd, Morse.Homotopy.isLocallyTrivial_detCircle, Morse.Homotopy.subsingleton_pi_circle, Morse.Homotopy.bijective_homotopyGroupMap_suInclC]
#rt_overlap RoundTrip.V14_27.A_to_B [Morse.Homotopy.unitaryProd, Morse.Homotopy.isLocallyTrivial_detCircle, Morse.Homotopy.subsingleton_pi_circle, Morse.Homotopy.bijective_homotopyGroupMap_suInclC]

end RoundTrip.V14_27
