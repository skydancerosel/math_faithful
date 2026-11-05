import Morse
import RoundTrip.Check
import RoundTrip.Blind.VA_7

/-! # Round trip for VA_7 (Milnor, Appendix p. 149: Example 1, and sublevel sets)

`A` is the conjunction of the types, universes at `0`, of `Morse.example1` (paracompact Hausdorff
`X`, increasing `X_i` whose interiors cover `X` ⇒ `X` is the homotopy direct limit of `{X_i}`)
and `Morse.isHomotopyDirectLimit_sublevel` (for ANY space `X`, a continuous `E : X → ℝ` and
`a_i ↗ ∞`, `X` is the homotopy direct limit of the sublevel sets `{E ≤ a_i}`).

`B`: under Example 1's hypotheses (paracompact read with Hausdorff, as in the project), there is
a continuous `f ≥ 0` with `f ≥ i + 1` off `X_i`, and `X` is a homotopy direct limit (`IsHDL`).

* `A ⇒ B`: `IsHDL` from `A`'s `example1` (glue `IsHDL ↔ Monotone ∧ IsHomotopyDirectLimit`);
  the level function is built outright (Milnor's partition of unity `f = Σ i φ_i`, Mathlib's
  `PartitionOfUnity.exists_isSubordinate`): `A` does not state its existence.
* `B ⇒ A`: `example1` is `B`'s second clause. For the sublevel clause, which concerns arbitrary
  (non-paracompact) spaces and is not an instance of Example 1, `B`'s FIRST clause is applied to
  the paracompact space `ℝ` with `X_i = (-∞, a_i]`, giving `f₀ : ℝ → ℝ`; then `f₀ ∘ E` is a level
  function on `X`, and the project's Lemma 2.1 (`Morse.isHomotopyDirectLimit_of_level`, item
  VA_6, not one of this item's theorems) concludes. -/

namespace RoundTrip.VA_7

open Set Filter

/-- `A`: the two listed theorems, universes at `0`. -/
def A : Prop :=
  (type_of% @Morse.example1.{0}) ∧ (type_of% @Morse.isHomotopyDirectLimit_sublevel.{0})

theorem A_holds : A :=
  ⟨Morse.example1, Morse.isHomotopyDirectLimit_sublevel⟩

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

/-! ### The level function of Example 1 (outright) -/

/-- Milnor's "using a partition of unity": `f = Σ_i i φ_i` for a partition of unity `{φ_i}`
subordinate to `{int X_i}`. -/
theorem exists_level {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X]
    {S : ℕ → Set X} (hS : Monotone S) (hint : ∀ x, ∃ i, x ∈ interior (S i)) :
    ∃ f : X → ℝ, Continuous f ∧ (∀ (i : ℕ) (x : X), x ∉ S i → (i : ℝ) + 1 ≤ f x) ∧
      ∀ x, 0 ≤ f x := by
  obtain ⟨ρ, hρ⟩ := PartitionOfUnity.exists_isSubordinate isClosed_univ (fun n => interior (S n))
    (fun _ => isOpen_interior) (fun x _ => mem_iUnion.2 (hint x))
  have hcont : Continuous fun x => ∑ᶠ n, ρ n x • (n : ℝ) :=
    ρ.continuous_finsum_smul fun _ _ _ => continuousAt_const
  refine ⟨_, hcont, ?_, fun x => finsum_nonneg fun n => smul_nonneg (ρ.nonneg n x)
    (Nat.cast_nonneg n)⟩
  intro i x hx
  have hz : ∀ j ≤ i, ρ j x = 0 := fun j hj => by
    by_contra h
    exact hx (hS hj (interior_subset (hρ j (subset_tsupport _ h))))
  have hfin : (Function.support fun j => ρ j x).Finite := ρ.locallyFinite.point_finite x
  calc (i : ℝ) + 1 = ∑ᶠ j, ρ j x * ((i : ℝ) + 1) := by
        rw [← finsum_mul, ρ.sum_eq_one (mem_univ x), one_mul]
    _ ≤ ∑ᶠ j, ρ j x • (j : ℝ) := by
        refine finsum_le_finsum' (hfin.subset ?_) (hfin.subset ?_) fun j => ?_
        · intro j hj
          exact fun h => hj (by simp [h])
        · intro j hj
          exact fun h => hj (by simp [h])
        · rcases le_or_gt j i with hj | hj
          · simp [hz j hj]
          · have : (i : ℝ) + 1 ≤ j := by exact_mod_cast hj
            rw [smul_eq_mul]
            exact mul_le_mul_of_nonneg_left this (ρ.nonneg j x)

/-! ### The round trip -/

/-- `A ⇒ B`: `IsHDL` from `example1`; the level function outright. -/
theorem A_to_B : A → B := by
  rintro ⟨hex, -⟩ X _ _ _ S hS hint
  exact ⟨exists_level hS hint, (isHDL_iff S).2 ⟨hS, hex hS hint⟩⟩

/-- `B ⇒ A`: `example1` from `B`'s second clause; the sublevel clause from `B`'s first clause on
`ℝ` (sets `(-∞, a_i]`) and Lemma 2.1. -/
theorem B_to_A : B → A := by
  intro hB
  refine ⟨fun hS hint => ((isHDL_iff _).1 (hB _ _ hS hint).2).2, ?_⟩
  intro X _ E a ha ha'
  have hSm : Monotone fun i => Iic (a i) := fun m n h => Iic_subset_Iic.2 (ha h)
  have hint : ∀ t : ℝ, ∃ i, t ∈ interior (Iic (a i)) := fun t => by
    obtain ⟨i, hi⟩ := (ha'.eventually_gt_atTop t).exists
    exact ⟨i, by rw [interior_Iic]; exact hi⟩
  obtain ⟨⟨f₀, hf₀c, hf₀, hf₀0⟩, -⟩ := hB ℝ (fun i => Iic (a i)) hSm hint
  refine Morse.isHomotopyDirectLimit_of_level (fun m n h x hx => le_trans hx (ha h))
    ⟨f₀ ∘ E, hf₀c.comp E.continuous⟩ (fun x => hf₀0 _) ?_
  intro n x hx
  exact hf₀ n (E x) hx

#rt_check RoundTrip.VA_7.A_to_B [Morse.example1, Morse.isHomotopyDirectLimit_sublevel]
#rt_check RoundTrip.VA_7.B_to_A [Morse.example1, Morse.isHomotopyDirectLimit_sublevel]
#rt_overlap RoundTrip.VA_7.B_to_A [Morse.example1, Morse.isHomotopyDirectLimit_sublevel]
#rt_overlap RoundTrip.VA_7.A_to_B [Morse.example1, Morse.isHomotopyDirectLimit_sublevel]

end RoundTrip.VA_7
