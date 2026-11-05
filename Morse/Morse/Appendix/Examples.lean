import Morse.Appendix.Telescope
import Morse.Chapter2.Crossing

/-!
Milnor, *Morse Theory*, Appendix, pp. 149–150: Examples 1, 2 and 3 of homotopy direct limits.

# When is `X` the homotopy direct limit of `X₀ ⊆ X₁ ⊆ ⋯`?

**Example 1** (p. 149), paraphrased: if every point of `X` is in the interior of some `X_i` and
`X` is paracompact, a partition of unity gives a map `f : X → ℝ` with `f ≥ 0` and `f(x) ≥ i + 1`
for `x ∉ X_i`; the graph of `f` is a deformation retract of `X_Σ`, so `X` is the homotopy direct
limit of `{X_i}` (`Morse.example1`).

**Example 2** (p. 149): a CW-complex is the homotopy direct limit of an increasing sequence of
subcomplexes with union `X`. Milnor's proof: `p` induces isomorphisms of all homotopy groups, and
Whitehead's theorem applies. **Not formalized**: Whitehead's theorem, the CW topology of products
and the fact that compact subsets of CW-complexes lie in finite subcomplexes are not in Mathlib.
For this reason the Lean form of the alternative proof of Theorem 17.3
(`Morse/Appendix/MonotoneUnion.lean`) uses the *telescope* of the complexes `K_i` as the countable
complex, not their union with the weak topology.

**Example 3** (p. 150): the unit interval is not the homotopy direct limit of the closed subsets
`[0] ∪ [1/i, 1]` (`Morse.example3`; here indexed from `0`, `{0} ∪ [1/(n+1), 1]`).

## What Milnor's text leaves implicit

* **Example 1, "using a partition of unity"**: the function is `f = Σ_i i φ_i` for a partition of
  unity `{φ_i}` subordinate to the open cover `{int X_i}`; it is `≥ i + 1` off `X_i` because
  `φ_j(x) = 0` for `j ≤ i` when `x ∉ X_i` (monotonicity). Mathlib's partitions of unity need `X`
  normal; Milnor's "paracompact" is read with the Hausdorff axiom (Dugundji's and Bourbaki's
  convention), and paracompact Hausdorff spaces are normal. The "clearly a deformation retract" is
  Lemma 2.1 (`Morse.isHomotopyDirectLimit_of_level`).
* **Sublevel sets need no paracompactness.** If `X_i = {E ≤ a_i}` for a continuous `E : X → ℝ` and
  `a_i ↗ ∞` (the situation of Theorem 17.3, with `E` the energy), the function
  `f = Σ_j min(1, max(0, E - a_j + 1))` is continuous (locally a finite sum) and `≥ i + 1` off
  `X_i`, so `X` is the homotopy direct limit of its sublevel sets for any space `X`
  (`Morse.isHomotopyDirectLimit_sublevel`). Milnor's application uses Example 1 and the
  paracompactness of the metric space `Ω`.
* **Example 3 has no proof in the book.** The subset `{0} × [0, ∞)` of the telescope is open and
  closed (a point `(x, τ)` of `X_Σ` with `x > 0` has `x ≥ 1/(⌊τ⌋ + 1)`), so `X_Σ` is not
  connected; but a space homotopy equivalent to `[0, 1]` is: the homotopy from `s ∘ p` to the
  identity joins every point of `X_Σ` to the path-connected image of `s`. Here `0` lies in every
  `X_i` but in the interior of none: the hypothesis of Example 1 fails at one point.

## Main results

* `Morse.example1`: **Example 1**.
* `Morse.isHomotopyDirectLimit_sublevel`: sublevel sets `{E ≤ a_i}`, `a_i ↗ ∞`.
* `Morse.example3`: **Example 3**, with `Morse.monotone_example3Set`, `Morse.isClosed_example3Set`,
  `Morse.iUnion_example3Set`.
-/

open Set Filter Topology Function
open scoped unitInterval

noncomputable section

namespace Morse

variable {X : Type*} [TopologicalSpace X] {A : ℕ → Set X}

/-! ### Example 1 -/

/-- **Example 1** (Milnor, p. 149). If each point of `X` lies in the interior of some `X_i`, and `X`
is paracompact (and Hausdorff), then `X` is the homotopy direct limit of `{X_i}`. The function
`f = Σ_i i φ_i`, for a partition of unity `{φ_i}` subordinate to `{int X_i}`, is `≥ i + 1` off
`X_i`, and Lemma 2.1 applies. -/
theorem example1 [ParacompactSpace X] [T2Space X] (hA : Monotone A)
    (hint : ∀ x, ∃ n, x ∈ interior (A n)) : IsHomotopyDirectLimit A := by
  obtain ⟨ρ, hρ⟩ := PartitionOfUnity.exists_isSubordinate isClosed_univ (fun n => interior (A n))
    (fun _ => isOpen_interior) (fun x _ => mem_iUnion.2 (hint x))
  have hcont : Continuous fun x => ∑ᶠ n, ρ n x • (n : ℝ) :=
    ρ.continuous_finsum_smul fun _ _ _ => continuousAt_const
  refine isHomotopyDirectLimit_of_level hA ⟨_, hcont⟩
    (fun x => finsum_nonneg fun n => smul_nonneg (ρ.nonneg n x) (Nat.cast_nonneg n)) ?_
  intro i x hx
  have hz : ∀ j ≤ i, ρ j x = 0 := fun j hj => by
    by_contra h
    exact hx (hA hj (interior_subset (hρ j (subset_tsupport _ h))))
  have hfin : (support fun j => ρ j x).Finite := ρ.locallyFinite.point_finite x
  change (i : ℝ) + 1 ≤ ∑ᶠ n, ρ n x • (n : ℝ)
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

/-! ### Sublevel sets of a continuous function -/

/-- **Sublevel sets.** If `E : X → ℝ` is continuous and `a_i ↗ ∞`, then `X` is the homotopy direct
limit of the sublevel sets `X^{a_i} = {E ≤ a_i}`, for any space `X` (no paracompactness): the
locally finite sum `f = Σ_j min(1, max(0, E - a_j + 1))` is `≥ i + 1` off `X^{a_i}`. -/
theorem isHomotopyDirectLimit_sublevel (E : C(X, ℝ)) {a : ℕ → ℝ} (ha : Monotone a)
    (ha' : Tendsto a atTop atTop) : IsHomotopyDirectLimit fun n => sublevel E (a n) := by
  set term : ℕ → X → ℝ := fun j x => max 0 (min 1 (E x - a j + 1)) with hterm
  have hcont : ∀ j, Continuous (term j) := fun j =>
    continuous_const.max (continuous_const.min ((E.continuous.sub continuous_const).add
      continuous_const))
  have hlf : LocallyFinite fun j => support (term j) := by
    intro x₀
    obtain ⟨N, hN⟩ := eventually_atTop.1 (ha'.eventually_ge_atTop (E x₀ + 2))
    refine ⟨{x | E x < E x₀ + 1}, (isOpen_lt E.continuous continuous_const).mem_nhds
      (by simp), (Set.finite_lt_nat N).subset ?_⟩
    rintro j ⟨x, hxs, hxU⟩
    by_contra hj
    have hj' : E x₀ + 2 ≤ a j := hN j (not_lt.1 hj)
    have hxU' : E x < E x₀ + 1 := hxU
    exact hxs (by simp only [hterm]; exact max_eq_left (min_le_of_right_le (by linarith)))
  have hsum : Continuous fun x => ∑ᶠ j, term j x := continuous_finsum hcont hlf
  refine isHomotopyDirectLimit_of_level (fun m n h x hx => le_trans hx (ha h)) ⟨_, hsum⟩
    (fun x => finsum_nonneg fun j => le_max_left _ _) ?_
  intro i x hx
  have hx' : a i < E x := not_le.1 hx
  have hone : ∀ j ≤ i, term j x = 1 := fun j hj => by
    have : a j ≤ a i := ha hj
    simp only [hterm]
    rw [min_eq_left (by linarith), max_eq_right zero_le_one]
  have hfin : (support fun j => term j x).Finite := hlf.point_finite x
  change (i : ℝ) + 1 ≤ ∑ᶠ j, term j x
  have hind : (∑ᶠ j, if j ≤ i then (1 : ℝ) else 0) = i + 1 := by
    rw [finsum_eq_sum_of_support_subset (s := Finset.range (i + 1))]
    · rw [Finset.sum_congr rfl fun j hj => if_pos (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj))]
      simp
    · intro j hj
      simp only [mem_support, ne_eq, ite_eq_right_iff, one_ne_zero, imp_false, not_not] at hj
      simpa [Finset.mem_range] using Nat.lt_succ_of_le hj
  rw [← hind]
  refine finsum_le_finsum' ((Finset.range (i + 1)).finite_toSet.subset ?_) hfin fun j => ?_
  · intro j hj
    simp only [mem_support, ne_eq, ite_eq_right_iff, one_ne_zero, imp_false, not_not] at hj
    simpa [Finset.mem_range] using Nat.lt_succ_of_le hj
  · by_cases hj : j ≤ i
    · simp [hj, hone j hj]
    · simp only [hj, if_false]
      exact le_max_left _ _

/-! ### Example 3 -/

/-- Milnor's closed subsets `[0] ∪ [1/i, 1]` of the unit interval (p. 150), indexed from `0`:
`{0} ∪ [1/(n+1), 1]`. -/
def example3Set (n : ℕ) : Set I :=
  {x | (x : ℝ) = 0 ∨ 1 / ((n : ℝ) + 1) ≤ x}

theorem monotone_example3Set : Monotone example3Set := by
  intro m n h x hx
  rcases hx with hx | hx
  · exact Or.inl hx
  · refine Or.inr (le_trans ?_ hx)
    have : (m : ℝ) ≤ n := by exact_mod_cast h
    gcongr

theorem isClosed_example3Set (n : ℕ) : IsClosed (example3Set n) :=
  (isClosed_eq continuous_subtype_val continuous_const).union
    (isClosed_le continuous_const continuous_subtype_val)

/-- The union of Milnor's sets is the whole interval. -/
theorem iUnion_example3Set : ⋃ n, example3Set n = univ := by
  refine eq_univ_of_forall fun x => mem_iUnion.2 ?_
  rcases eq_or_lt_of_le x.2.1 with h | h
  · exact ⟨0, Or.inl h.symm⟩
  · obtain ⟨n, hn⟩ := exists_nat_one_div_lt h
    exact ⟨n, Or.inr hn.le⟩

/-- **Example 3** (Milnor, p. 150): the unit interval `[0, 1]` is not the homotopy direct limit of
the closed subsets `{0} ∪ [1/(n+1), 1]`. The set `{0} × [0, ∞)` is open and closed in the
telescope, so the telescope is not connected, while a homotopy inverse `s` of `p` would connect
`(0, 0)` to `s(0)`, `s(0)` to `s(1)` and `s(1)` to `(1, 0)`. -/
theorem example3 : ¬ IsHomotopyDirectLimit example3Set := by
  rintro ⟨s, ⟨H⟩, -⟩
  set C : Set (telescope example3Set) := {z | (((z : I × ℝ).1 : I) : ℝ) = 0} with hCdef
  have hx : Continuous fun z : telescope example3Set => (((z : I × ℝ).1 : I) : ℝ) :=
    continuous_subtype_val.comp (continuous_fst.comp continuous_subtype_val)
  have hτ : Continuous fun z : telescope example3Set => (z : I × ℝ).2 :=
    continuous_snd.comp continuous_subtype_val
  have hC : IsClopen C := by
    refine ⟨isClosed_eq hx continuous_const, isOpen_iff_forall_mem_open.2 fun z hz => ?_⟩
    have hz0 := nonneg_of_mem_telescope z.2
    refine ⟨{w | (((w : I × ℝ).1 : I) : ℝ) < 1 / ((z : I × ℝ).2 + 2) ∧
      (w : I × ℝ).2 < (z : I × ℝ).2 + 1}, ?_, (isOpen_lt hx continuous_const).inter
        (isOpen_lt hτ continuous_const), ?_⟩
    · rintro w ⟨hw1, hw2⟩
      obtain ⟨n, hn, h1, -⟩ := mem_telescope.1 w.2
      rcases hn with hn | hn
      · exact hn
      · exfalso
        have hlt : 1 / ((n : ℝ) + 1) < 1 / ((z : I × ℝ).2 + 2) := lt_of_le_of_lt hn hw1
        rw [one_div_lt_one_div (by positivity) (by positivity)] at hlt
        linarith
    · refine ⟨?_, by linarith⟩
      have hz' : (((z : I × ℝ).1 : I) : ℝ) = 0 := hz
      rw [hz']
      positivity
  have key : ∀ γ : C(I, telescope example3Set), (γ 0 ∈ C ↔ γ 1 ∈ C) := by
    intro γ
    rcases isClopen_iff.1 (hC.preimage γ.continuous) with h | h
    · have h0 : γ 0 ∉ C := fun h' => by
        have : (0 : I) ∈ γ ⁻¹' C := h'
        rw [h] at this
        exact this
      have h1 : γ 1 ∉ C := fun h' => by
        have : (1 : I) ∈ γ ⁻¹' C := h'
        rw [h] at this
        exact this
      exact iff_of_false h0 h1
    · have h0 : (0 : I) ∈ γ ⁻¹' C := by rw [h]; trivial
      have h1 : (1 : I) ∈ γ ⁻¹' C := by rw [h]; trivial
      exact iff_of_true h0 h1
  have hz₀ : ((0 : I), (0 : ℝ)) ∈ telescope example3Set :=
    mem_telescope.2 ⟨0, Or.inl rfl, by norm_num, by norm_num⟩
  have hz₁ : ((1 : I), (0 : ℝ)) ∈ telescope example3Set :=
    mem_telescope.2 ⟨0, Or.inr (by norm_num), by norm_num, by norm_num⟩
  let z₀ : telescope example3Set := ⟨_, hz₀⟩
  let z₁ : telescope example3Set := ⟨_, hz₁⟩
  let path : telescope example3Set → C(I, telescope example3Set) := fun z =>
    H.toContinuousMap.comp ((ContinuousMap.id I).prodMk (ContinuousMap.const I z))
  have e₀ := key (path z₀)
  have e₁ := key s
  have e₂ := key (path z₁)
  have p0 : path z₀ 0 = s 0 := H.apply_zero z₀
  have p0' : path z₀ 1 = z₀ := H.apply_one z₀
  have p1 : path z₁ 0 = s 1 := H.apply_zero z₁
  have p1' : path z₁ 1 = z₁ := H.apply_one z₁
  rw [p0, p0'] at e₀
  rw [p1, p1'] at e₂
  have hz₀C : z₀ ∈ C := (rfl : ((0 : I) : ℝ) = 0)
  have hz₁C : z₁ ∉ C := fun h => by
    have : ((1 : I) : ℝ) = 0 := h
    norm_num at this
  exact hz₁C (e₂.1 (e₁.1 (e₀.2 hz₀C)))

end Morse
