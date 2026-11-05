import Morse.Chapter12.SUMinimal
import Morse.Chapter1.ManifoldSubmanifold
import Morse.Chapter4.WhitneySlice
import Morse.Homotopy.Grassmannian

/-!
Milnor, *Morse Theory*, §4, pp. 26–27 (complex projective space); Exposition/Chapter3.md, §3.

# Complex projective space as a submanifold of the Hermitian matrices

## Milnor's text, paraphrased

(p. 26) `ℂPⁿ` is the set of classes `(z₀ : ⋯ : zₙ)` of unit vectors of `ℂⁿ⁺¹` modulo a unit
complex factor.  On `U₀ = {z₀ ≠ 0}` the numbers `(|z₀|/z₀) z_j = x_j + i y_j`, `j = 1, …, n`, are
coordinates mapping `U₀` diffeomorphically onto the open unit ball of `ℝ²ⁿ`; similarly on each
`U_k = {z_k ≠ 0}`.

## What is formalized

`ℂPⁿ` is modelled, as everywhere in this project (Lemma 23.1, the Grassmannians of §23), by the
Hermitian projections of trace one, `Morse.grassmannian (Fin (n + 1)) 1 ⊆ Mₙ₊₁(ℂ)`: the class of
the unit vector `z` is the projection `P = z zᴴ`, `P_{ab} = z_a z̄_b`, and `|z_a|² = P_{aa}`.

* `Morse.CP.param k`: **Milnor's coordinates on `U_k`, inverted**: for `z ∈ ℝ²ⁿ`
  (`Morse.CP.Model n = Fin n × Fin 2 → ℝ`, the pairs `(x_j, y_j)`, `j ≠ k`) with
  `|z|² = Morse.CP.nsq z < 1`, the projection onto the line of the unit vector `v` with
  `v_k = √(1 − |z|²)` and `v_j = x_j + i y_j` for `j ≠ k` (`Morse.CP.param_mem`).
  `Morse.CP.coord k`: Milnor's coordinates `(|z_k|/z_k) z_j = P_{jk}/√P_{kk}` on
  `U_k = {Re P_{kk} > 0}`; they invert each other (`Morse.CP.coord_param`,
  `Morse.CP.nsq_coord_lt_and_param_coord`), and both are smooth
  (`Morse.CP.contDiffOn_param`, `Morse.CP.contDiffOn_coord`).
* `Morse.CP.exists_sliceChart`, `Morse.CP.isSliceSubmanifold`: **`ℂPⁿ` is a `2n`-dimensional
  submanifold of `Mₙ₊₁(ℂ) = ℝ^{2(n+1)²}`**, with a slice chart at every `x ∈ U_k` whose
  parametrization is Milnor's, `z ↦ param k (coord k x + z)`, near `0`.
* `Morse.CP.isCompact`: **`ℂPⁿ` is compact** (closed, and on the unit sphere of the Frobenius
  norm, `Morse.CP.norm_eq_one`).
* `Morse.exists_sliceChart_of_localParam` (general): a set with a local parametrization
  `Φ : Z × W → V`, smooth near `0` with invertible derivative there, has a slice chart at `Φ 0`
  whose parametrization is `z ↦ Φ (z, 0)` near `0` (a variant of
  `Morse.isSliceSubmanifold_of_param` that keeps track of the chart).

## What Milnor leaves implicit

* **The model.**  Milnor's `ℂPⁿ` is a quotient of `S²ⁿ⁺¹`; here it is the set of projections
  `z zᴴ`, a subset of a Euclidean space (every point is of this form,
  `Morse.CP.exists_vec_of_mem`, from `Morse.Homotopy.exists_frame_of_mem_grassmannian`).  The
  coordinates are then entries of `P`: `|z_j|² = P_{jj}` and `(|z_k|/z_k) z_j = P_{jk}/√P_{kk}`,
  visibly independent of the representative `z`.
* **That the coordinates form a smooth chart** (p. 26 "are coordinates") needs that the
  parametrization is an immersion and a homeomorphism onto the open set `U_k`; here this is the
  smoothness of `coord k` on `{Re P_{kk} > 0}` together with `coord k ∘ param k = id`.
* **The `U_k` cover `ℂPⁿ`**: `Σ_k P_{kk} = tr P = 1` (`Morse.CP.exists_re_diag_pos`).
-/

open Matrix Set Filter Topology Function Module
open scoped ContDiff Manifold

noncomputable section

namespace Morse

section Slice

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]

/-- **A local parametrization gives a slice chart**: if `Φ : Z × W → V` is smooth near `0`, with
invertible derivative at `0`, `Φ(z, 0) ∈ S` for small `z`, and every point `Φ q ∈ S` (`q` small) is
`Φ(g q, 0)` with `g q → 0`, then there is a slice chart `σ` of `S` at `x = Φ 0` with `σ x = 0`
whose parametrization `sliceParam σ` is `z ↦ Φ(z, 0)` near `0`. -/
theorem exists_sliceChart_of_localParam {S : Set V} {x : V} (Φ : Z × W → V)
    (hΦ : ∀ᶠ q in 𝓝 (0 : Z × W), ContDiffAt ℝ ∞ Φ q) (hΦ0 : Φ 0 = x)
    (hder : ∃ e : (Z × W) ≃L[ℝ] V, HasFDerivAt Φ (e : (Z × W) →L[ℝ] V) 0)
    (h0 : ∀ᶠ q in 𝓝 (0 : Z × W), q.2 = 0 → Φ q ∈ S)
    (g : Z × W → Z) (hg : Tendsto g (𝓝 0) (𝓝 0))
    (hgΦ : ∀ᶠ q in 𝓝 (0 : Z × W), Φ q ∈ S → Φ (g q, 0) = Φ q) (hx : x ∈ S) :
    ∃ σ : Milnor.SliceChart 𝓘(ℝ, V) Z W S, x ∈ σ.φ.source ∧ σ.φ x = 0 ∧
      ∀ᶠ z in 𝓝 (0 : Z), sliceParam σ z = Φ (z, 0) := by
  obtain ⟨e, he⟩ := hder
  have hinv : (mfderiv 𝓘(ℝ, Z × W) 𝓘(ℝ, V) Φ 0).IsInvertible := by
    rw [mfderiv_eq_fderiv, he.fderiv]
    exact ⟨e, rfl⟩
  obtain ⟨Ψ, h0Ψ, hΨ⟩ := Milnor.isLocalDiffeomorphAt_of_isInvertible_mfderiv
    (hΦ.mono fun q hq => hq.contMDiffAt) (by simp) hinv
  have hsrc : Ψ.source ∈ 𝓝 (0 : Z × W) := Ψ.open_source.mem_nhds h0Ψ
  have hg' : Tendsto (fun q : Z × W => ((g q, 0) : Z × W)) (𝓝 0) (𝓝 0) := by
    have := hg.prodMk_nhds (tendsto_const_nhds (x := (0 : W)))
    rwa [← Prod.zero_eq_mk] at this
  have hev : ∀ᶠ q in 𝓝 (0 : Z × W), (Φ q ∈ S ↔ q.2 = 0) := by
    filter_upwards [h0, hgΦ, hsrc, hg'.eventually hsrc] with q hq0 hqg hqs hqs'
    refine ⟨fun hq => ?_, hq0⟩
    have e1 : Ψ.toFun (g q, 0) = Ψ.toFun q := by
      rw [← hΨ hqs', ← hΨ hqs]; exact hqg hq
    have := Ψ.toPartialEquiv.injOn hqs' hqs e1
    rw [← this]
  obtain ⟨U, hUev, hUo, h0U⟩ := mem_nhds_iff.1 hev
  set Ψ' := Ψ.restrOpen U hUo with hΨ'
  have hxt : x ∈ Ψ'.target := ⟨0, ⟨h0Ψ, h0U⟩, by rw [← hΦ0]; exact (hΨ h0Ψ).symm⟩
  have h0s : (0 : Z × W) ∈ Ψ'.source := ⟨h0Ψ, h0U⟩
  have hΨx : Ψ'.toFun 0 = x := by rw [← hΦ0]; exact (hΨ h0Ψ).symm
  refine ⟨⟨Ψ'.symm, x, hx, hxt, fun p hp => ?_⟩, hxt, ?_, ?_⟩
  · obtain ⟨q, hq, rfl⟩ := hp
    have hq' : Ψ'.toPartialEquiv.symm (Ψ'.toFun q) = q := Ψ'.toPartialEquiv.left_inv hq
    change Ψ'.toFun q ∈ S ↔ (Ψ'.toPartialEquiv.symm (Ψ'.toFun q)).2 = 0
    rw [hq']
    have : Ψ'.toFun q = Φ q := (hΨ hq.1).symm
    rw [this]
    exact hUev hq.2
  · change Ψ'.toPartialEquiv.symm x = 0
    rw [← hΨx]
    exact Ψ'.toPartialEquiv.left_inv h0s
  · have hc : Tendsto (fun z : Z => ((z, 0) : Z × W)) (𝓝 0) (𝓝 0) := by
      have := (tendsto_id (x := 𝓝 (0 : Z))).prodMk_nhds (tendsto_const_nhds (x := (0 : W)))
      rwa [← Prod.zero_eq_mk] at this
    filter_upwards [hc.eventually (Ψ'.open_source.mem_nhds h0s)] with z hz
    change Ψ'.toFun (z, 0) = Φ (z, 0)
    exact (hΨ hz.1).symm

end Slice

namespace CP

variable {n : ℕ}

/-- The model space `ℝ²ⁿ` of `ℂPⁿ`: the pairs `(x_j, y_j)`. -/
abbrev Model (n : ℕ) := Fin n × Fin 2 → ℝ

/-- The complex coordinates `x_j + i y_j`. -/
def cz (z : Model n) (i : Fin n) : ℂ := ⟨z (i, 0), z (i, 1)⟩

/-- `|z|² = Σ (x_j² + y_j²)`. -/
def nsq (z : Model n) : ℝ := ∑ p, z p ^ 2

/-- The unit vector `v` with `v_k = √(1 − |z|²)`, `v_j = x_j + i y_j` (`j ≠ k`). -/
def vec (k : Fin (n + 1)) (z : Model n) : Fin (n + 1) → ℂ :=
  Fin.insertNth k ((Real.sqrt (1 - nsq z) : ℝ) : ℂ) (cz z)

/-- **Milnor's parametrization of `U_k`** (p. 26): `z ↦ v vᴴ`. -/
def param (k : Fin (n + 1)) (z : Model n) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
  Matrix.of fun a b => vec k z a * star (vec k z b)

/-- Milnor's complex coordinates `(|z_k|/z_k) z_j = P_{jk}/√P_{kk}` on `U_k`. -/
def coordC (k : Fin (n + 1)) (P : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (i : Fin n) : ℂ :=
  P (k.succAbove i) k / ((Real.sqrt (P k k).re : ℝ) : ℂ)

/-- **Milnor's real coordinates on `U_k`** (p. 26). -/
def coord (k : Fin (n + 1)) (P : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) : Model n :=
  fun p => if p.2 = 0 then (coordC k P p.1).re else (coordC k P p.1).im

theorem nsq_eq (z : Model n) : nsq z = ∑ i, Complex.normSq (cz z i) := by
  simp only [nsq, Fintype.sum_prod_type, Fin.sum_univ_two, cz, Complex.normSq_mk]
  refine Finset.sum_congr rfl fun i _ => by ring

theorem nsq_nonneg (z : Model n) : 0 ≤ nsq z := Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem cz_coord (k : Fin (n + 1)) (P : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :
    cz (coord k P) = coordC k P := by
  funext i
  apply Complex.ext <;> simp [cz, coord]

theorem sum_vec_mul_star (k : Fin (n + 1)) {z : Model n} (hz : nsq z ≤ 1) :
    ∑ a, vec k z a * star (vec k z a) = 1 := by
  rw [Fin.sum_univ_succAbove _ k]
  simp only [vec, Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]
  have h1 : ∀ w : ℂ, w * star w = (Complex.normSq w : ℂ) := fun w => Complex.mul_conj w
  simp only [h1, ← Complex.ofReal_sum, ← nsq_eq, Complex.normSq_ofReal]
  rw [Real.mul_self_sqrt (by linarith)]
  push_cast; ring

theorem param_mem (k : Fin (n + 1)) {z : Model n} (hz : nsq z ≤ 1) :
    param k z ∈ grassmannian (Fin (n + 1)) 1 := by
  refine ⟨?_, ?_, ?_⟩
  · ext a b; simp [param, mul_comm]
  · ext a b
    simp only [param, mul_apply, of_apply]
    have : ∀ c, vec k z a * star (vec k z c) * (vec k z c * star (vec k z b)) =
        vec k z a * star (vec k z b) * (vec k z c * star (vec k z c)) := fun c => by ring
    simp only [this, ← Finset.mul_sum, sum_vec_mul_star k hz, mul_one]
  · simp only [trace, diag, param, of_apply, sum_vec_mul_star k hz, Nat.cast_one]

theorem param_kk (k : Fin (n + 1)) {z : Model n} (hz : nsq z ≤ 1) :
    param k z k k = ((1 - nsq z : ℝ) : ℂ) := by
  simp only [param, of_apply, vec, Fin.insertNth_apply_same]
  rw [Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul, Real.mul_self_sqrt (by linarith)]

theorem param_succAbove_k (k : Fin (n + 1)) (z : Model n) (i : Fin n) :
    param k z (k.succAbove i) k = cz z i * ((Real.sqrt (1 - nsq z) : ℝ) : ℂ) := by
  simp only [param, of_apply, vec, Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]
  rw [Complex.star_def, Complex.conj_ofReal]

theorem coord_param (k : Fin (n + 1)) {z : Model n} (hz : nsq z < 1) : coord k (param k z) = z := by
  have hs : Real.sqrt (1 - nsq z) ≠ 0 := (Real.sqrt_pos.2 (by linarith)).ne'
  have hc : coordC k (param k z) = cz z := by
    funext i
    rw [coordC, param_kk k hz.le, Complex.ofReal_re, param_succAbove_k, mul_div_assoc,
      div_self (by exact_mod_cast hs), mul_one]
  funext p
  obtain ⟨i, b⟩ := p
  fin_cases b <;> simp [coord, hc, cz]

/-- A point of `ℂPⁿ` is `f f*` for a unit vector `f`. -/
theorem exists_vec_of_mem {P : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (hP : P ∈ grassmannian (Fin (n + 1)) 1) :
    ∃ f : Fin (n + 1) → ℂ, ∑ a, Complex.normSq (f a) = 1 ∧ ∀ a b, P a b = f a * star (f b) := by
  obtain ⟨F, hF, hFP⟩ := Homotopy.exists_frame_of_mem_grassmannian (𝕜 := ℂ) (m := 1) hP
  refine ⟨fun a => F a 0, ?_, fun a b => ?_⟩
  · have h := congrFun (congrFun (Homotopy.mem_stiefel.1 hF) 0) 0
    simp only [mul_apply, conjTranspose_apply, one_apply_eq] at h
    have : ∀ a, star (F a 0) * F a 0 = (Complex.normSq (F a 0) : ℂ) := fun a => by
      rw [mul_comm]; exact Complex.mul_conj _
    simp only [this, ← Complex.ofReal_sum] at h
    exact_mod_cast h
  · rw [← hFP, mul_apply, Fin.sum_univ_one, conjTranspose_apply]

theorem nsq_coord_lt_and_param_coord (k : Fin (n + 1)) {P : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (hP : P ∈ grassmannian (Fin (n + 1)) 1) (hk : 0 < (P k k).re) :
    nsq (coord k P) < 1 ∧ param k (coord k P) = P := by
  obtain ⟨f, hf1, hfP⟩ := exists_vec_of_mem hP
  have hkk : (P k k).re = Complex.normSq (f k) := by
    rw [hfP, Complex.star_def, Complex.mul_conj, Complex.ofReal_re]
  set r := Real.sqrt (Complex.normSq (f k)) with hr
  have hr0 : 0 < r := Real.sqrt_pos.2 (hkk ▸ hk)
  have hr2 : r * r = Complex.normSq (f k) := Real.mul_self_sqrt (Complex.normSq_nonneg _)
  set u₀ : ℂ := star (f k) / (r : ℂ) with hu₀
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr0.ne'
  have hc : ∀ i, coordC k P i = f (k.succAbove i) * u₀ := fun i => by
    rw [coordC, hkk, hfP, ← hr, hu₀, mul_div_assoc]
  have hu₀n : Complex.normSq u₀ = 1 := by
    rw [hu₀, Complex.normSq_div, Complex.normSq_ofReal, Complex.star_def, Complex.normSq_conj, hr2,
      div_self (by rw [← hr2]; positivity)]
  have hnsq : nsq (coord k P) = 1 - Complex.normSq (f k) := by
    rw [nsq_eq, cz_coord]
    simp only [hc, Complex.normSq_mul, hu₀n, mul_one]
    rw [← hf1, Fin.sum_univ_succAbove _ k]
    ring
  refine ⟨by rw [hnsq]; linarith [hkk ▸ hk], ?_⟩
  have hv : vec k (coord k P) = fun a => f a * u₀ := by
    funext a
    refine Fin.succAboveCases k ?_ (fun i => ?_) a
    · rw [vec, Fin.insertNth_apply_same, hnsq, sub_sub_cancel, ← hr, hu₀, mul_div_assoc',
        Complex.star_def, Complex.mul_conj, ← hr2, Complex.ofReal_mul, mul_div_assoc,
        div_self hrC, mul_one]
    · rw [vec, Fin.insertNth_apply_succAbove, cz_coord, hc]
  ext a b
  rw [param, of_apply, hv, hfP]
  simp only [star_mul']
  have : f a * u₀ * (star (f b) * star u₀) = f a * star (f b) * (u₀ * star u₀) := by ring
  rw [this, Complex.star_def, Complex.mul_conj, hu₀n, Complex.ofReal_one, mul_one]

open scoped Morse.MatrixInner

theorem contDiff_nsq : ContDiff ℝ ∞ (nsq : Model n → ℝ) := by
  unfold nsq; fun_prop

theorem contDiff_cz (i : Fin n) : ContDiff ℝ ∞ fun z : Model n => cz z i := by
  have : (fun z : Model n => cz z i) =
      fun z => Complex.equivRealProdCLM.symm (z (i, 0), z (i, 1)) := by
    funext z; rfl
  rw [this]
  exact Complex.equivRealProdCLM.symm.contDiff.comp (by fun_prop)

theorem contDiffOn_vec (k : Fin (n + 1)) (a : Fin (n + 1)) :
    ContDiffOn ℝ ∞ (fun z : Model n => vec k z a) {z | nsq z < 1} := by
  refine Fin.succAboveCases k ?_ (fun i => ?_) a
  · simp only [vec, Fin.insertNth_apply_same]
    refine Complex.ofRealCLM.contDiff.comp_contDiffOn ?_
    refine ContDiffOn.sqrt ((contDiff_const.sub contDiff_nsq).contDiffOn) fun z hz => ?_
    have : nsq z < 1 := hz
    linarith
  · simp only [vec, Fin.insertNth_apply_succAbove]
    exact (contDiff_cz i).contDiffOn

/-- The identification of `ι → ι → ℂ` with matrices, as a continuous `ℝ`-linear map for the
Frobenius norm. -/
def ofCLM : ((Fin (n + 1) → Fin (n + 1) → ℂ)) →L[ℝ] Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := Matrix.of, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }

theorem contDiffOn_param (k : Fin (n + 1)) :
    ContDiffOn ℝ ∞ (param k : Model n → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) {z | nsq z < 1} := by
  have : (param k : Model n → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) =
      fun z => ofCLM (fun a b => vec k z a * star (vec k z b)) := rfl
  rw [this]
  refine ofCLM.contDiff.comp_contDiffOn (contDiffOn_pi.2 fun a => contDiffOn_pi.2 fun b => ?_)
  exact (contDiffOn_vec k a).mul (Complex.conjCLE.contDiff.comp_contDiffOn (contDiffOn_vec k b))

theorem contDiffOn_coordC (k : Fin (n + 1)) (i : Fin n) :
    ContDiffOn ℝ ∞ (fun P : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ => coordC k P i)
      {P | 0 < (P k k).re} := by
  have : (fun P : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ => coordC k P i) =
      fun P => (Real.sqrt (P k k).re)⁻¹ • P (k.succAbove i) k := by
    funext P
    rw [coordC, div_eq_mul_inv, Complex.real_smul, Complex.ofReal_inv, mul_comm]
  rw [this]
  refine ContDiffOn.smul (𝕜 := ℝ) (𝕜' := ℝ) ?_
    (contDiff_entry (𝕜 := ℂ) (k.succAbove i) k).contDiffOn
  refine ContDiffOn.inv ?_ fun P hP => (Real.sqrt_pos.2 (hP : 0 < (P k k).re)).ne'
  exact ContDiffOn.sqrt (Complex.reCLM.contDiff.comp (contDiff_entry (𝕜 := ℂ) k k)).contDiffOn
    fun P hP => (hP : 0 < (P k k).re).ne'

theorem contDiffOn_coord (k : Fin (n + 1)) :
    ContDiffOn ℝ ∞ (coord k : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ → Model n)
      {P | 0 < (P k k).re} := by
  refine contDiffOn_pi.2 fun p => ?_
  by_cases h : p.2 = 0
  · simp only [coord, h, if_true]
    exact Complex.reCLM.contDiff.comp_contDiffOn (contDiffOn_coordC k p.1)
  · simp only [coord, h, if_false]
    exact Complex.imCLM.contDiff.comp_contDiffOn (contDiffOn_coordC k p.1)

theorem exists_re_diag_pos {P : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (hP : P ∈ grassmannian (Fin (n + 1)) 1) : ∃ k, 0 < (P k k).re := by
  by_contra h
  push Not at h
  have h1 : (trace P).re = 1 := by rw [hP.2.2]; simp
  have h2 : (trace P).re ≤ 0 := by
    rw [trace, Complex.re_sum]
    exact Finset.sum_nonpos fun k _ => h k
  linarith

/-- The normal model space: `dim Z + dim W = dim Mₙ₊₁(ℂ) = 2(n+1)²`. -/
abbrev Normal (n : ℕ) := Fin (2 * (n + 1) ^ 2 - 2 * n) → ℝ

theorem finrank_add : finrank ℝ (Model n) + finrank ℝ (Normal n) =
    finrank ℝ (Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) := by
  rw [Module.finrank_matrix, Module.finrank_fintype_fun_eq_card,
    Module.finrank_fintype_fun_eq_card, Complex.finrank_real_complex]
  simp only [Fintype.card_prod, Fintype.card_fin]
  have : 2 * n ≤ 2 * (n + 1) ^ 2 := by nlinarith
  zify [this]
  ring

/-- **The slice chart of `ℂPⁿ` at `x`, built from Milnor's coordinates on `U_k`.** -/
theorem exists_sliceChart (k : Fin (n + 1)) {x : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (hx : x ∈ grassmannian (Fin (n + 1)) 1) (hk : 0 < (x k k).re) :
    ∃ σ : Milnor.SliceChart 𝓘(ℝ, Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (Model n) (Normal n)
        (grassmannian (Fin (n + 1)) 1),
      x ∈ σ.φ.source ∧ σ.φ x = 0 ∧
      ∀ᶠ z in 𝓝 (0 : Model n), sliceParam σ z = param k (coord k x + z) := by
  set z₀ := coord k x with hz₀
  obtain ⟨hz₀1, hpz₀⟩ := nsq_coord_lt_and_param_coord k hx hk
  have hD : IsOpen {z : Model n | nsq z < 1} := isOpen_lt contDiff_nsq.continuous continuous_const
  have hU : IsOpen {P : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ | 0 < (P k k).re} :=
    isOpen_lt continuous_const (Complex.continuous_re.comp (contDiff_entry (𝕜 := ℂ) k k).continuous)
  have hpar : ContDiffAt ℝ ∞ (param k) z₀ := (contDiffOn_param k).contDiffAt (hD.mem_nhds hz₀1)
  have hcoord : ContDiffAt ℝ ∞ (coord k) x := (contDiffOn_coord k).contDiffAt (hU.mem_nhds hk)
  -- the derivative of the parametrization is injective
  have hev1 : ∀ᶠ z in 𝓝 z₀, coord k (param k z) = z := by
    filter_upwards [hD.mem_nhds hz₀1] with z hz using coord_param k hz
  have hinj : Injective (fderiv ℝ (param k) z₀) := by
    have hc' : DifferentiableAt ℝ (coord k) (param k z₀) := by
      rw [hpz₀]; exact hcoord.differentiableAt (by simp)
    have h1 := fderiv_comp z₀ hc' (hpar.differentiableAt (by simp))
    have h2 : fderiv ℝ (coord k ∘ param k) z₀ = ContinuousLinearMap.id ℝ _ := by
      have h3 : coord k ∘ param k =ᶠ[𝓝 z₀] id := hev1
      rw [h3.fderiv_eq, fderiv_id]
    intro v w hvw
    have := congrArg (fun T => T v) h2
    have h' := congrArg (fun T => T w) h2
    simp only [h1, ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] at this h'
    rw [← this, ← h', hvw]
  obtain ⟨L, D, hDL⟩ := exists_continuousLinearEquiv_coprod (fderiv ℝ (param k) z₀) hinj
    (ContinuousLinearEquiv.refl ℝ (Model n)) finrank_add
  set Φ : Model n × Normal n → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
    fun q => param k (z₀ + q.1) + L q.2 with hΦ
  have hshift : Tendsto (fun q : Model n × Normal n => z₀ + q.1) (𝓝 0) (𝓝 z₀) := by
    have : Continuous (fun q : Model n × Normal n => z₀ + q.1) := by fun_prop
    simpa using this.tendsto 0
  have hΦc : ContinuousAt Φ 0 := by
    refine ContinuousAt.add ?_ (L.continuous.comp continuous_snd).continuousAt
    exact hpar.continuousAt.comp_of_eq (by fun_prop) (by simp)
  have hΦ0 : Φ 0 = x := by simpa [Φ, hz₀] using hpz₀
  have hΦx : Tendsto Φ (𝓝 0) (𝓝 x) := hΦ0 ▸ hΦc.tendsto
  have hgt : Tendsto (fun q => coord k (Φ q) - z₀) (𝓝 0) (𝓝 0) := by
    have := (hcoord.continuousAt.tendsto.comp hΦx).sub_const z₀
    simpa [hz₀] using this
  have hA : ∀ᶠ q in 𝓝 (0 : Model n × Normal n), ContDiffAt ℝ ∞ Φ q := by
    filter_upwards [hshift.eventually (hD.mem_nhds hz₀1)] with q hq
    have hs : ContDiffAt ℝ ∞ (fun q : Model n × Normal n => z₀ + q.1) q :=
      (contDiff_const.add contDiff_fst).contDiffAt
    exact (ContDiffAt.comp (g := param k) q ((contDiffOn_param k).contDiffAt (hD.mem_nhds hq))
      hs).add (L.contDiff.comp contDiff_snd).contDiffAt
  have hB : HasFDerivAt Φ (D : (Model n × Normal n) →L[ℝ] _) 0 := by
    have h1 : HasFDerivAt (fun q : Model n × Normal n => param k (z₀ + q.1))
        ((fderiv ℝ (param k) z₀).comp (ContinuousLinearMap.fst ℝ _ _)) 0 := by
      have := (hpar.differentiableAt (by simp)).hasFDerivAt
      have h2 : HasFDerivAt (fun q : Model n × Normal n => z₀ + q.1)
          (ContinuousLinearMap.fst ℝ (Model n) (Normal n)) 0 :=
        (hasFDerivAt_fst).const_add z₀
      have this' : HasFDerivAt (param k) (fderiv ℝ (param k) z₀)
          (z₀ + (0 : Model n × Normal n).1) := by
        rw [Prod.fst_zero, add_zero]; exact this
      exact this'.comp (0 : Model n × Normal n) h2
    have h3 : HasFDerivAt (fun q : Model n × Normal n => L q.2)
        (L.comp (ContinuousLinearMap.snd ℝ _ _)) 0 :=
      L.hasFDerivAt.comp (0 : Model n × Normal n) hasFDerivAt_snd
    refine (h1.add h3).congr_fderiv (ContinuousLinearMap.ext fun p => ?_)
    rw [ContinuousLinearEquiv.coe_coe, hDL]
    rfl
  have hC : ∀ᶠ q in 𝓝 (0 : Model n × Normal n), q.2 = 0 → Φ q ∈ grassmannian (Fin (n + 1)) 1 := by
    filter_upwards [hshift.eventually (hD.mem_nhds hz₀1)] with q hq hq2
    simp only [Φ, hq2, map_zero, add_zero]
    exact param_mem k (le_of_lt hq)
  have hE : ∀ᶠ q in 𝓝 (0 : Model n × Normal n), Φ q ∈ grassmannian (Fin (n + 1)) 1 →
      Φ (coord k (Φ q) - z₀, 0) = Φ q := by
    filter_upwards [hΦx.eventually (hU.mem_nhds hk)] with q hq hqS
    simp only [Φ, add_sub_cancel, map_zero, add_zero]
    exact (nsq_coord_lt_and_param_coord k hqS hq).2
  obtain ⟨σ, hσx, hσ0, hσp⟩ :=
    exists_sliceChart_of_localParam Φ hA hΦ0 ⟨D, hB⟩ hC _ hgt hE hx
  refine ⟨σ, hσx, hσ0, ?_⟩
  filter_upwards [hσp] with z hz
  rw [hz]
  simp [Φ]

/-- **`ℂPⁿ` is a slice submanifold of `Mₙ₊₁(ℂ)`** of dimension `2n`. -/
theorem isSliceSubmanifold :
    Milnor.IsSliceSubmanifold 𝓘(ℝ, Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (Model n) (Normal n)
      (grassmannian (Fin (n + 1)) 1) := by
  intro x hx
  obtain ⟨k, hk⟩ := exists_re_diag_pos hx
  obtain ⟨σ, hσ, -⟩ := exists_sliceChart k hx hk
  exact ⟨σ, hσ⟩

theorem norm_eq_one {P : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (hP : P ∈ grassmannian (Fin (n + 1)) 1) : ‖P‖ = 1 := by
  have h := MatrixInner.re_trace_conjTranspose_mul_self P
  rw [← MatrixInner.norm_sq_eq, hP.1, hP.2.1, hP.2.2] at h
  have h1 : ‖P‖ ^ 2 = 1 := by rw [← h]; simp
  have := norm_nonneg P
  nlinarith

/-- **`ℂPⁿ` is compact**: closed, and contained in the unit sphere of the Frobenius norm. -/
theorem isCompact : IsCompact (grassmannian (Fin (n + 1)) 1) := by
  refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
  · have h1 : Continuous fun P : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ => Pᴴ :=
      continuous_id.matrix_conjTranspose
    have h2 : Continuous fun P : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ => P * P :=
      continuous_id.matrix_mul continuous_id
    have h3 : Continuous fun P : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ => trace P :=
      continuous_id.matrix_trace
    exact (isClosed_eq h1 continuous_id).inter ((isClosed_eq h2 continuous_id).inter
      (isClosed_eq h3 continuous_const))
  · refine (Metric.isBounded_closedBall (x := (0 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ))
      (r := 1)).subset fun P hP => ?_
    rw [Metric.mem_closedBall, dist_zero_right, norm_eq_one hP]

end CP
end Morse
