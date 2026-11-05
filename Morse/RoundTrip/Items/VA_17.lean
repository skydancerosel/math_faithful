import Morse
import RoundTrip.Check
import RoundTrip.Blind.VA_17

/-! # Round trip for VA_17 (Milnor, Appendix p. 153: the Corollary)

`A` is the conjunction of the types of `Morse.corollary_appendix` (universes `0, 0`) and
`Morse.corollary_cellComplex` (universe `0`): if `X` is the homotopy direct limit of `{X_n}` and
`X_n ≃ₕ K_n`, then `X ≃ₕ` the mapping telescope of a sequence `K₀ → K₁ → ⋯` (with the given
`K_n` as stages); in particular, if each `X_n` has the homotopy type of a finite iterated
adjunction space (`Morse.IsFiniteCellComplexType`), `X` has the homotopy type of the mapping
telescope of a sequence of such spaces.

`B`: if `X` is the homotopy direct limit of the increasing `{X_n}` and each `X_n` is homotopy
equivalent to a (Hausdorff) Mathlib `CWComplex`, then so is `X`.

* `A ⇒ B` **fails**: `A` stops at the mapping telescope; that a mapping telescope of CW complexes
  has the homotopy type of a CW complex needs cellular approximation (to make the maps cellular)
  and the CW structure of a mapping telescope, neither in Mathlib nor in the project. The
  reduction is proved: `A_to_B_of_telescope` derives `B` from `A` and that single missing
  statement (`TelescopeCW`).
* `B ⇒ A`: only vacuously; `A` is re-proved outright from the non-listed project theorem
  `Morse.nonempty_homotopyEquiv_mappingTelescope` (the Corollary's content in `A` is "`X` is the
  mapping telescope", which `B` does not state). -/

namespace RoundTrip.VA_17

open Set CategoryTheory

/-- `A`: the two listed theorems, universes at `0`. -/
def A : Prop :=
  (type_of% @Morse.corollary_appendix.{0, 0}) ∧ (type_of% @Morse.corollary_cellComplex.{0})

/-! ### Glue -/

section Glue

variable {X : Type} [TopologicalSpace X]

omit [TopologicalSpace X] in
theorem tel_eq_telescope (S : ℕ → Set X) : tel S = Morse.telescope S := by
  ext z
  simp only [tel, Morse.telescope, mem_iUnion, mem_prod, mem_Icc]; rfl

/-- The identity homeomorphism `tel S ≃ₜ telescope S`. -/
noncomputable def telHomeo (S : ℕ → Set X) : ↥(tel S) ≃ₜ ↥(Morse.telescope S) :=
  Homeomorph.setCongr (tel_eq_telescope S)

theorem telProj_eq (S : ℕ → Set X) :
    telProj S = (Morse.telescopeProj S).comp (telHomeo S : C(↥(tel S), ↥(Morse.telescope S))) :=
  rfl

theorem isHE_iff {P Q : Type} [TopologicalSpace P] [TopologicalSpace Q] (f : C(P, Q)) :
    IsHE f ↔ Morse.IsHomotopyEquiv f :=
  ⟨fun ⟨g, h₁, h₂⟩ => ⟨g, h₂, h₁⟩, fun ⟨g, h₁, h₂⟩ => ⟨g, h₂, h₁⟩⟩

theorem isHomotopyEquiv_comp_homeo_iff {P P' Q : Type} [TopologicalSpace P] [TopologicalSpace P']
    [TopologicalSpace Q] (f : C(P, Q)) (e : P' ≃ₜ P) :
    Morse.IsHomotopyEquiv (f.comp (e : C(P', P))) ↔ Morse.IsHomotopyEquiv f := by
  constructor
  · intro h
    have h' := (Morse.IsHomotopyEquiv.of_homeomorph e.symm).comp h
    have : (f.comp (e : C(P', P))).comp (e.symm : C(P, P')) = f := by
      ext x; simp
    rwa [this] at h'
  · intro h
    exact (Morse.IsHomotopyEquiv.of_homeomorph e).comp h

theorem isHDL_iff (S : ℕ → Set X) :
    IsHDL S ↔ Monotone S ∧ Morse.IsHomotopyDirectLimit S := by
  unfold IsHDL Morse.IsHomotopyDirectLimit
  rw [isHE_iff, telProj_eq, isHomotopyEquiv_comp_homeo_iff]

end Glue

/-! ### `A ⇒ B` modulo the missing CW fact -/

/-- The missing statement: a mapping telescope of spaces of CW homotopy type has CW homotopy
type (true, via cellular approximation and the CW structure of the mapping telescope of cellular
maps; not in Mathlib or the project). -/
def TelescopeCW : Prop :=
  ∀ F : ℕ ⥤ TopCat.{0}, (∀ n, HasCWType (F.obj n)) → HasCWType (Morse.MappingTelescope F)

/-- `A ∧ TelescopeCW ⇒ B` (uses `A`'s first clause). -/
theorem A_to_B_of_telescope (hA : A) (hT : TelescopeCW) : B := by
  intro X _ S hS hcw
  rw [isHDL_iff] at hS
  choose Y tY hY2 hYcw e using hcw
  have e' : ∀ n, ContinuousMap.HomotopyEquiv ↥(S n) (TopCat.of (Y n)) := fun n => (e n).some
  obtain ⟨F, hF, ⟨eX⟩⟩ := hA.1 hS.1 hS.2 (fun n => TopCat.of (Y n)) e'
  have hFcw : ∀ n, HasCWType (F.obj n) := by
    intro n
    rw [hF n]
    exact ⟨Y n, tY n, hY2 n, hYcw n, ⟨ContinuousMap.HomotopyEquiv.refl _⟩⟩
  obtain ⟨Z, tZ, hZ2, hZcw, ⟨eZ⟩⟩ := hT F hFcw
  exact ⟨Z, tZ, hZ2, hZcw, ⟨eX.trans eZ⟩⟩

/-! ### `B ⇒ A`, vacuously: `A` re-proved outright -/

/-- `Morse.corollary_appendix` at universe `0`, re-proved from
`Morse.nonempty_homotopyEquiv_mappingTelescope` (the project's proof). -/
theorem corollary_appendix' {X : Type} [TopologicalSpace X] {S : ℕ → Set X} (hS : Monotone S)
    (hX : Morse.IsHomotopyDirectLimit S) (K : ℕ → TopCat.{0})
    (e : ∀ n, ContinuousMap.HomotopyEquiv (S n) (K n)) :
    ∃ F : ℕ ⥤ TopCat.{0}, (∀ n, F.obj n = K n) ∧
      Nonempty (ContinuousMap.HomotopyEquiv X (Morse.MappingTelescope F)) := by
  let c : ∀ n, K n ⟶ K (n + 1) := fun n =>
    TopCat.ofHom ((e (n + 1)).toFun.comp ((Morse.up hS n).comp (e n).invFun))
  refine ⟨Functor.ofSequence c, fun n => rfl,
    Morse.nonempty_homotopyEquiv_mappingTelescope _ hS hX (fun n => (e n).toFun)
      (fun n => Morse.IsHomotopyEquiv.of_homotopyEquiv (e n)) fun n => ?_⟩
  have hc : Morse.tmap (Functor.ofSequence c) (Nat.le_add_right n 1) =
      (e (n + 1)).toFun.comp ((Morse.up hS n).comp (e n).invFun) := by
    simp only [Morse.tmap, Functor.ofSequence_map_homOfLE_succ]
    rfl
  rw [hc]
  change ((((e (n + 1)).toFun.comp ((Morse.up hS n).comp (e n).invFun)).comp (e n).toFun :
    C(S n, K (n + 1)))).Homotopic ((e (n + 1)).toFun.comp (Morse.up hS n))
  have := (ContinuousMap.Homotopic.refl ((e (n + 1)).toFun.comp (Morse.up hS n))).comp
    (e n).left_inv
  simpa only [ContinuousMap.comp_assoc, ContinuousMap.comp_id] using this

theorem A_holds' : A := by
  refine ⟨@fun X _ S hS hX K e => corollary_appendix' hS hX K e, ?_⟩
  intro X _ S hS hX cells h
  choose K hK e using h
  obtain ⟨F, hF, he⟩ := corollary_appendix' hS hX K fun n => (e n).some
  exact ⟨F, fun n => hF n ▸ hK n, he⟩

/-- `B ⇒ A`: vacuous (`A` holds outright). -/
theorem B_to_A : B → A := fun _ => A_holds'

#rt_check RoundTrip.VA_17.B_to_A [Morse.corollary_appendix, Morse.corollary_cellComplex]
#rt_check RoundTrip.VA_17.A_to_B_of_telescope [Morse.corollary_appendix, Morse.corollary_cellComplex]
#rt_overlap RoundTrip.VA_17.B_to_A [Morse.corollary_appendix, Morse.corollary_cellComplex]

end RoundTrip.VA_17
