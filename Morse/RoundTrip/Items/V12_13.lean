import Morse
import RoundTrip.Check
import RoundTrip.Blind.V12_13

/-!
# V12_13 (Milnor §21, proof of Theorem 21.7, p. 117): even index from paired eigenvalues

`A` (universe `0`): `Morse.even_spectralIndex` — for any finite family `e : κ → ℝ` ("the spectrum of `K_V`
with multiplicity") in which every positive value has even multiplicity, `Morse.spectralIndex e` (vocabulary:
`∑ᶠ t, #{i | t ∈ conjParams (e i)}`, with `conjParams e = {t ∈ (0,1) | e > 0, t ∈ (π/√e) ℤ}` the conjugate
parameters Theorem 20.5 attaches to an eigenvalue) is even.  Pure combinatorics: the project's model of
"index = Σ multiplicities of conjugate points" is the definition `spectralIndex`, not a theorem about geodesics.

`B` (blind): on a Lie group with a bi-invariant metric and Levi-Civita connection, for every geodesic
`γ : [0,1] → G`: (i) every `γ(t)`, `0 < t ≤ 1`, has even multiplicity as a conjugate point of `γ(0)` (blind
`conjMult`: dimension of Jacobi fields vanishing at `0` and `t`); (ii) the index `λ = lam 1 γ` (index of the
blind `E_**` on `TΩ_γ`) is even (and finite).

* `B → A`: vacuous (A re-proved outright from `Morse.spectralIndex_eq`).
* `A → B` fails, genuinely: `B` is about Jacobi fields and the Hessian of the energy on an abstract Lie group;
  the project has neither Theorem 20.5 (conjugate points of a locally symmetric space from the eigenvalues of
  `K_V`) nor the Index Theorem 15.1 for Mathlib manifolds (it has them in the embedded setting, and for `SU(n)`
  only), nor the bookkeeping "spectrum of `K_V` with multiplicity" (V12_12 gives even eigenspace dimensions).
* **Bridge** (`B_of_inputs`, uses `A`, `#rt_check`ed): given, for each geodesic, a finite spectrum `e` with
  (Paired) every positive value of even multiplicity, (Thm20_5) `conjMult γ 0 t = #{i | e_i > 0, t ∈ (π/√e_i) ℤ}`
  for `0 < t ≤ 1`, and (IndexThm) `λ = ∑ᶠ_{0<t<1} conjMult γ 0 t`, `B` follows: (ii) is `A` (after identifying
  the blind sum with `spectralIndex e`), and (i) is a fibrewise count from (Paired) alone (not part of `A`,
  which only concerns the total).
-/

open scoped ContDiff Manifold
open Bundle Finset

set_option linter.unusedSectionVars false

namespace RoundTrip.V12_13

/-- The project's statement (universe `0`). -/
def A : Prop := type_of% @Morse.even_spectralIndex.{0}

theorem A_holds : A := @Morse.even_spectralIndex.{0}

/-- Vacuous: `A` re-proved outright (`Morse.spectralIndex_eq`, the interchange of summations), `B` is not used. -/
theorem B_to_A : B → A := by
  intro _ κ _ e h
  classical
  rw [Morse.spectralIndex_eq, sum_comp (fun μ => (Morse.conjParams μ).ncard) e]
  refine even_sum _ fun μ _ => ?_
  rcases le_or_gt μ 0 with hμ | hμ
  · have : Morse.conjParams μ = ∅ := Set.eq_empty_of_forall_notMem fun t ht => not_lt.2 hμ ht.1
    simp [this]
  · rw [smul_eq_mul]
    exact (h μ hμ).mul_right _

/-! ## The inputs: Theorem 20.5, the Index Theorem and the pairing of eigenvalues -/

section Inputs
variable {n : ℕ} {G : Type} [TopologicalSpace G] [ChartedSpace (Rn n) G] [IsManifold 𝓘(ℝ, Rn n) ∞ G]
  [Bundle.RiemannianBundle (fun x : G => TangentSpace 𝓘(ℝ, Rn n) x)]

/-- 21.7 / V12_12: the positive eigenvalues have even multiplicity. -/
def Paired {k : ℕ} (e : Fin k → ℝ) : Prop := ∀ μ, 0 < μ → Even #{i | e i = μ}

open Classical in
/-- Theorem 20.5 for `γ` with spectrum `e` (eigenvalues of `K_V`, `V = γ'(0)`, with multiplicity): the
multiplicity of `γ(t)`, `0 < t ≤ 1`, is the number of `e_i > 0` with `t ∈ (π/√e_i) ℤ`. -/
def Thm20_5 (cov : Conn n G) (γ : ℝ → G) {k : ℕ} (e : Fin k → ℝ) : Prop :=
  ∀ t ∈ Set.Ioc (0 : ℝ) 1,
    conjMult cov γ 0 t = ((#{i | 0 < e i ∧ ∃ s : ℤ, t = Real.pi * s / Real.sqrt (e i)} : ℕ) : ℕ∞)

/-- The Index Theorem 15.1: `λ` is the number of conjugate points `γ(t)`, `0 < t < 1`, with multiplicity. -/
def IndexThm (cov : Conn n G) (γ : ℝ → G) : Prop :=
  lam (n := n) 1 γ = ∑ᶠ (t : ℝ) (_ : t ∈ Set.Ioo (0 : ℝ) 1), conjMult cov γ 0 t

end Inputs

/-- The inputs, for every geodesic of every Lie group with a bi-invariant metric. -/
def Inputs : Prop :=
  ∀ (n : ℕ) (G : Type) [Group G] [TopologicalSpace G] [T2Space G] [ChartedSpace (Rn n) G] [LieGroup 𝓘(ℝ, Rn n) ∞ G] [Bundle.RiemannianBundle (fun x : G => TangentSpace 𝓘(ℝ, Rn n) x)] [IsContMDiffRiemannianBundle 𝓘(ℝ, Rn n) ∞ (Rn n) (fun x : G => TangentSpace 𝓘(ℝ, Rn n) x)],
    BiInvMetric n G → ∀ cov : Conn n G, IsLC cov →
      ∀ γ : ℝ → G, IsGeodesic cov γ (Set.Icc 0 1) →
        ∃ (k : ℕ) (e : Fin k → ℝ), Paired e ∧ Thm20_5 cov γ e ∧ IndexThm cov γ

/-- Fibrewise count: a set of indices defined through the values `e i`, all positive, has even size. -/
theorem even_card_filter {k : ℕ} (e : Fin k → ℝ) (hpair : Paired e) (P : ℝ → Prop) [DecidablePred P]
    (hP : ∀ μ, P μ → 0 < μ) : Even #{i | P (e i)} := by
  classical
  rw [card_eq_sum_card_fiberwise (f := e) (t := univ.image e)
    (fun i _ => mem_image_of_mem e (mem_univ i))]
  refine even_sum _ fun μ _ => ?_
  by_cases h : P μ
  · have hXY : ({i ∈ ({i | P (e i)} : Finset (Fin k)) | e i = μ} : Finset (Fin k)) =
        ({i | e i = μ} : Finset (Fin k)) := by
      ext i
      simp only [mem_filter, mem_univ, true_and, and_iff_right_iff_imp]
      intro h'; rw [h']; exact h
    rw [hXY]
    exact hpair μ (hP μ h)
  · have h0 : ∀ i ∈ ({i | P (e i)} : Finset (Fin k)), ¬ e i = μ := by
      intro i hi h'
      rw [mem_filter] at hi
      exact h (h' ▸ hi.2)
    rw [filter_false_of_mem h0, card_empty]
    exact ⟨0, rfl⟩

/-- The blind sum of the Index Theorem is the project's `spectralIndex`, under Theorem 20.5. -/
theorem lam_eq_spectralIndex {n : ℕ} {G : Type} [TopologicalSpace G] [ChartedSpace (Rn n) G]
    [IsManifold 𝓘(ℝ, Rn n) ∞ G] [Bundle.RiemannianBundle (fun x : G => TangentSpace 𝓘(ℝ, Rn n) x)]
    (cov : Conn n G) (γ : ℝ → G) {k : ℕ} (e : Fin k → ℝ) (h205 : Thm20_5 cov γ e)
    (hidx : IndexThm cov γ) : lam (n := n) 1 γ = (Morse.spectralIndex e : ℕ∞) := by
  classical
  rw [hidx]
  have hfin : (Function.support (Morse.conjMult e)).Finite := by
    refine (Set.finite_iUnion fun i => Morse.conjParams_finite (e i)).subset ?_
    intro t ht
    simp only [Function.mem_support, Morse.conjMult, ne_eq, card_eq_zero, filter_eq_empty_iff,
      mem_univ, true_imp_iff, not_forall, not_not] at ht
    obtain ⟨i, hi⟩ := ht
    exact Set.mem_iUnion.2 ⟨i, hi⟩
  have hcongr : ∀ t ∈ Set.Ioo (0 : ℝ) 1, conjMult cov γ 0 t = ((Morse.conjMult e t : ℕ) : ℕ∞) := by
    intro t ht
    rw [h205 t ⟨ht.1, ht.2.le⟩, Morse.conjMult]
    refine congrArg (fun s : Finset (Fin k) => ((#s : ℕ) : ℕ∞)) (filter_congr fun i _ => ?_)
    simp only [Morse.conjParams, Set.mem_ofPred_eq]
    exact ⟨fun h => ⟨h.1, ht.1, ht.2, h.2⟩, fun h => ⟨h.1, h.2.2.2⟩⟩
  rw [finsum_mem_congr rfl hcongr]
  have hsupp : Function.support (fun t => ((Morse.conjMult e t : ℕ) : ℕ∞)) ⊆ Set.Ioo (0 : ℝ) 1 := by
    intro t ht
    simp only [Function.mem_support, ne_eq, Nat.cast_eq_zero, Morse.conjMult, card_eq_zero,
      filter_eq_empty_iff, mem_univ, true_imp_iff, not_forall, not_not] at ht
    obtain ⟨i, hi⟩ := ht
    exact ⟨hi.2.1, hi.2.2.1⟩
  rw [finsum_mem_def, Set.indicator_eq_self.2 hsupp, Morse.spectralIndex]
  exact ((Nat.castAddMonoidHom ℕ∞).map_finsum hfin).symm

/-- **Bridge** (uses `A`): the inputs imply `B`. -/
theorem B_of_inputs (hA : A) : Inputs → B := by
  intro hin n G _ _ _ _ _ _ _ hbi cov hLC γ hγ
  obtain ⟨k, e, hpair, h205, hidx⟩ := hin n G hbi cov hLC γ hγ
  refine ⟨fun t ht => ?_, ?_⟩
  · classical
    obtain ⟨m, hm⟩ := even_card_filter e hpair (fun μ => 0 < μ ∧ ∃ s : ℤ, t = Real.pi * s / Real.sqrt μ)
      (fun μ h => h.1)
    refine ⟨m, ?_⟩
    rw [h205 t ht]
    rw [two_mul, ← Nat.cast_add, ← hm]
  · obtain ⟨m, hm⟩ := hA e hpair
    refine ⟨m, ?_⟩
    rw [lam_eq_spectralIndex cov γ e h205 hidx, hm, two_mul, Nat.cast_add]

#rt_check RoundTrip.V12_13.B_to_A [Morse.even_spectralIndex]
#rt_overlap RoundTrip.V12_13.B_to_A [Morse.even_spectralIndex]
#rt_check RoundTrip.V12_13.B_of_inputs [Morse.even_spectralIndex]

end RoundTrip.V12_13
