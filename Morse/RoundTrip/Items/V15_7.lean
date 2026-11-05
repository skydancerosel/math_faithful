import Morse
import RoundTrip.Check
import RoundTrip.Blind.V15_7

open Matrix
open scoped Matrix ContDiff Topology
open scoped Matrix.Norms.Elementwise

namespace RoundTrip.V15_7

/-- The project's statement (universes instantiated at `0`, arbitrary finite index types): Lemma
24.4 (iii) algebraically — `J' ∈ Ω_{k+1}(n)` iff `J' = J_kA` with `A = -J_kJ'` a complex structure
anticommuting with `J_k` and commuting with `J_1, …, J_{k-1}` (two theorems); the semicircle
`cos t·J_k + sin t·J'` lies in `Ω_k(n)` for every `t`; it equals `J_k exp(t·(-J_kJ'))` (for any `J_k`,
`J'` with `J_k² = (J_kJ')² = -1`); and anticommuting complex structures are orthogonal,
`tr(J'ᵀJ) = 0`. -/
def A : Prop :=
  type_of% @Morse.omega_succ_decomp.{0} ∧ type_of% @Morse.mul_mem_omega_succ.{0} ∧
    type_of% @Morse.semicircle_mem_omega.{0} ∧ type_of% @Morse.mul_exp_eq_semicircle.{0} ∧
    type_of% @Morse.trace_transpose_mul_eq_zero.{0}

theorem A_holds : A :=
  ⟨@Morse.omega_succ_decomp.{0}, @Morse.mul_mem_omega_succ.{0}, @Morse.semicircle_mem_omega.{0},
    @Morse.mul_exp_eq_semicircle.{0}, @Morse.trace_transpose_mul_eq_zero.{0}⟩

section Vocab
variable {ι : Type} [Fintype ι] [DecidableEq ι]
set_option linter.unusedSectionVars false

theorem isACFam_iff (Js : ℕ → Mat ι) (m : ℕ) : IsACFam Js m ↔ Morse.IsAnticommFamily Js m :=
  ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.cs, h.anti⟩⟩

theorem omegaK_eq_omega (Js : ℕ → Mat ι) (k : ℕ) : OmegaK Js k = Morse.Omega Js k := by
  cases k with
  | zero => rfl
  | succ k =>
    ext J
    simp only [OmegaK, Morse.Omega, IsCplxStr, Morse.IsComplexStructure, AntiComm,
      Set.mem_ofPred_eq]
    refine and_congr Iff.rfl (forall_congr' fun α => forall_congr' fun _ => forall_congr' fun _ =>
      ⟨fun h => by rw [h, neg_neg], fun h => by rw [h, neg_neg]⟩)

theorem omegaK_subset_orth (Js : ℕ → Mat ι) (k : ℕ) : OmegaK Js k ⊆ Orth ι := by
  cases k with
  | zero => exact le_rfl
  | succ k => exact fun J hJ => hJ.1.1

theorem frob_eq_sum (X Y : Mat ι) : frob X Y = ∑ i, ∑ j, X i j * Y i j := by
  simp [frob, Matrix.trace, Matrix.mul_apply]

/-- In a subset of `O(n)` every tangent vector at `p` is `frob`-orthogonal to `p` (`O(n)` lies on
the sphere `tr(ppᵀ) = n`). -/
theorem frob_tan_eq_zero {N : Set (Mat ι)} (hN : N ⊆ Orth ι) {p v : Mat ι}
    (hv : v ∈ TanSet N p) : frob p v = 0 := by
  obtain ⟨c, -, hcN, hc0, hcv⟩ := hv
  have hent : ∀ i j, HasDerivAt (fun s => c s i j) (v i j) 0 := fun i j =>
    hasDerivAt_pi.1 (hasDerivAt_pi.1 hcv i) j
  have hf : HasDerivAt (fun s => ∑ i, ∑ j, c s i j * c s i j)
      (∑ i, ∑ j, (v i j * c 0 i j + c 0 i j * v i j)) 0 :=
    HasDerivAt.fun_sum fun i _ => HasDerivAt.fun_sum fun j _ => (hent i j).mul (hent i j)
  have hconst : (fun s => ∑ i, ∑ j, c s i j * c s i j) = fun _ => (Fintype.card ι : ℝ) := by
    funext s
    have h1 : c s * (c s)ᵀ = 1 := by
      have := hN (hcN s)
      rw [SetLike.mem_coe, mem_orthogonalGroup_iff] at this
      simpa [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] using this
    have h2 := congrArg Matrix.trace h1
    rw [trace_one] at h2
    rw [← h2]
    simp [Matrix.trace, Matrix.mul_apply]
  rw [hconst] at hf
  have h0 := hf.unique (hasDerivAt_const 0 _)
  rw [frob_eq_sum, ← hc0]
  have : ∑ i, ∑ j, (v i j * c 0 i j + c 0 i j * v i j) = 2 * ∑ i, ∑ j, c 0 i j * v i j := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  linarith

/-- The great circle `t ↦ cos(πt)·P + sin(πt)·Q`. -/
noncomputable def circ (P Q : Mat ι) (t : ℝ) : Mat ι :=
  Real.cos (Real.pi * t) • P + Real.sin (Real.pi * t) • Q

theorem circ_contDiff (P Q : Mat ι) (m : WithTop ℕ∞) : ContDiff ℝ m (circ P Q) := by
  unfold circ; fun_prop

theorem circ_hasDerivAt (P Q : Mat ι) (t : ℝ) :
    HasDerivAt (circ P Q) ((-(Real.pi * Real.sin (Real.pi * t))) • P +
      (Real.pi * Real.cos (Real.pi * t)) • Q) t := by
  have hl : HasDerivAt (fun t : ℝ => Real.pi * t) Real.pi t := by
    simpa using (hasDerivAt_id t).const_mul Real.pi
  have hc := (Real.hasDerivAt_cos (Real.pi * t)).comp t hl
  have hs := (Real.hasDerivAt_sin (Real.pi * t)).comp t hl
  have h := (hc.smul_const P).add (hs.smul_const Q)
  have heq : (-(Real.pi * Real.sin (Real.pi * t))) • P + (Real.pi * Real.cos (Real.pi * t)) • Q =
      (-Real.sin (Real.pi * t) * Real.pi) • P + (Real.cos (Real.pi * t) * Real.pi) • Q := by
    module
  rw [heq]
  exact h

theorem deriv_circ (P Q : Mat ι) : deriv (circ P Q) =
    circ (Real.pi • Q) (-(Real.pi • P)) := by
  funext t
  refine (circ_hasDerivAt P Q t).deriv.trans ?_
  simp only [circ]
  module

theorem iteratedDeriv_two_circ (P Q : Mat ι) (t : ℝ) :
    iteratedDeriv 2 (circ P Q) t = (-(Real.pi ^ 2)) • circ P Q t := by
  rw [iteratedDeriv_succ, iteratedDeriv_one]
  erw [deriv_circ, deriv_circ]
  simp only [circ]
  module

/-- A great circle through points of `N ⊆ O(n)` that stays in `N` is a geodesic of `N`: its
acceleration `-π²γ` is normal to `N`. -/
theorem isGeodOn_circ {N : Set (Mat ι)} (hN : N ⊆ Orth ι) (P Q : Mat ι)
    (hmem : ∀ t, circ P Q t ∈ N) : IsGeodOn N (circ P Q) 0 1 := by
  refine ⟨zero_lt_one, (circ_contDiff P Q _).contDiffOn, fun t _ => hmem t, fun t ht v hv => ?_⟩
  rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc zero_lt_one)
    ((circ_contDiff P Q 2).contDiffAt) ht, iteratedDeriv_two_circ]
  have h := frob_tan_eq_zero hN hv
  rw [frob_eq_sum] at h ⊢
  simp only [Matrix.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum, h, mul_zero]

end Vocab

/-- A ⇒ B. The algebra (`A` a complex structure anticommuting with `J_k`, commuting with
`J_1, …, J_{k-1}`, and the converse) is A's `omega_succ_decomp` / `mul_mem_omega_succ`; A's
`mul_exp_eq_semicircle` turns `J_k exp(πtA)` into the great circle `cos(πt)J_k + sin(πt)J`, which
lies in `Ω_k(n)` by A's `semicircle_mem_omega` (whence the end points and the midpoint `J`). The
geodesic property for the metric induced by `tr(ABᵀ)` is not in A and is proved here: the
acceleration is `-π²γ`, and `Ω_k(n) ⊆ O(n)` lies on the sphere `tr(γγᵀ) = n`, so every tangent
vector is orthogonal to `γ`. -/
theorem A_to_B : A → B := by
  rintro ⟨hdec, hmul, hsemi, hexp, -⟩
  intro n k Js hk hJ
  have hJ' := (isACFam_iff Js k).1 hJ
  have hJk : Js k * Js k = -1 := (hJ.1 k hk le_rfl).2
  refine ⟨fun J A hJmem hJA => ?_, fun A hA hAk hAα => ?_⟩
  · rw [omegaK_eq_omega] at hJmem
    obtain ⟨hc, hak, hα, -⟩ := hdec hJ' hk hJmem
    have hAeq : A = -(Js k * J) := by
      rw [hJA, ← Matrix.mul_assoc, hJk, Matrix.neg_mul, Matrix.one_mul, neg_neg]
    subst hAeq
    have hgeo : semiGeo (Js k) (-(Js k * J)) = circ (Js k) J := by
      funext t
      rw [semiGeo, mexp, hexp hJk hc.2 (Real.pi * t)]
      rfl
    have hmemc : ∀ t, circ (Js k) J t ∈ OmegaK Js k := fun t => by
      rw [omegaK_eq_omega]; exact hsemi hJ' hk hJmem (Real.pi * t)
    refine ⟨hc, hak, fun α h1 h2 => hα α h1 (by omega), ?_, ?_, ?_, ?_⟩
    · rw [hgeo]; exact isGeodOn_circ (omegaK_subset_orth Js k) _ _ hmemc
    · rw [hgeo]; simp [circ]
    · rw [hgeo]; simp [circ]
    · rw [hgeo, circ, show Real.pi * (1 / 2) = Real.pi / 2 by ring, Real.cos_pi_div_two,
        Real.sin_pi_div_two]
      simp
  · rw [omegaK_eq_omega]
    exact hmul hJ' hk hA hAk fun α h1 h2 => (hAα α h1 (by omega)).eq

section Transport
variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
set_option linter.unusedSectionVars false

theorem r_mul (e : ι ≃ κ) (X Y : Mat ι) : reindex e e (X * Y) = reindex e e X * reindex e e Y := by
  simpa only [coe_reindexAlgEquiv] using map_mul (reindexAlgEquiv ℝ ℝ e) X Y

theorem r_neg (e : ι ≃ κ) (X : Mat ι) : reindex e e (-X) = -reindex e e X := by ext; simp

theorem r_one (e : ι ≃ κ) : reindex e e (1 : Mat ι) = 1 := by ext i j; simp [one_apply]

theorem r_inj (e : ι ≃ κ) {X Y : Mat ι} (h : reindex e e X = reindex e e Y) : X = Y :=
  (reindex e e).injective h

theorem r_cs_iff (e : ι ≃ κ) (X : Mat ι) :
    IsCplxStr (reindex e e X) ↔ Morse.IsComplexStructure X := by
  rw [show IsCplxStr (reindex e e X) ↔ Morse.IsComplexStructure (reindex e e X) from Iff.rfl,
    Morse.isComplexStructure_iff, Morse.isComplexStructure_iff, transpose_reindex, ← r_neg,
    ← r_mul, ← r_one e, ← r_neg]
  exact and_congr ⟨r_inj e, congrArg _⟩ ⟨r_inj e, congrArg _⟩

theorem r_eq_iff (e : ι ≃ κ) (X Y : Mat ι) : reindex e e X = reindex e e Y ↔ X = Y :=
  ⟨r_inj e, congrArg _⟩

theorem omega_iff_reindex (e : ι ≃ κ) (J : ℕ → Mat ι) (k : ℕ) (X : Mat ι) :
    X ∈ Morse.Omega J k ↔ reindex e e X ∈ Morse.Omega (fun α => reindex e e (J α)) k := by
  refine ⟨Morse.mem_omega_reindex e, fun h => ?_⟩
  have := Morse.mem_omega_reindex e.symm h
  simpa using this

end Transport

/-- B, transported to an arbitrary finite index type: for `J' ∈ Ω_{k+1}`, `A = -J_kJ'` is a complex
structure anticommuting with `J_k`, commuting with `J_1, …, J_{k-1}`, and the points
`J_k exp(πsA)`, `s ∈ [0, 1]`, lie in `Ω_k`. -/
theorem B_transport (hB : B) {ι : Type} [Fintype ι] [DecidableEq ι] {J : ℕ → Mat ι} {k : ℕ}
    (hJ : Morse.IsAnticommFamily J k) (hk : 1 ≤ k) {J' : Mat ι}
    (hJ' : J' ∈ Morse.Omega J (k + 1)) :
    Morse.IsComplexStructure (-(J k * J')) ∧ -(J k * J') * J k = -(J k * -(J k * J')) ∧
      (∀ α, 1 ≤ α → α < k → -(J k * J') * J α = J α * -(J k * J')) ∧
      ∀ s ∈ Set.Icc (0 : ℝ) 1, J k * NormedSpace.exp ((Real.pi * s) • -(J k * J')) ∈
        Morse.Omega J k := by
  set e := Fintype.equivFin ι
  have hJk : J k * J k = -1 := (hJ.cs k hk le_rfl).2
  have hJr := (isACFam_iff _ _).2 (hJ.reindex e)
  have hmem : reindex e e J' ∈ OmegaK (fun α => reindex e e (J α)) (k + 1) := by
    rw [omegaK_eq_omega]; exact (omega_iff_reindex e J (k + 1) J').1 hJ'
  have hJA : reindex e e J' = reindex e e (J k) * reindex e e (-(J k * J')) := by
    rw [← r_mul, r_eq_iff, Matrix.mul_neg, ← Matrix.mul_assoc, hJk, Matrix.neg_mul,
      Matrix.one_mul, neg_neg]
  obtain ⟨hc, ha, hα, hgeo, -⟩ := (hB _ k _ hk hJr).1 _ _ hmem hJA
  refine ⟨(r_cs_iff e _).1 hc, ?_, fun α h1 h2 => ?_, fun s hs => ?_⟩
  · have : reindex e e (-(J k * J') * J k) = reindex e e (-(J k * -(J k * J'))) := by
      rw [r_mul, r_neg (X := J k * -(J k * J')), r_mul]; exact ha
    exact r_inj e this
  · have : reindex e e (-(J k * J') * J α) = reindex e e (J α * -(J k * J')) := by
      rw [r_mul, r_mul]; exact (hα α h1 (by omega)).eq
    exact r_inj e this
  · have h := hgeo.2.2.1 s hs
    rw [omegaK_eq_omega] at h
    rw [omega_iff_reindex e]
    have hexp : reindex e e (NormedSpace.exp ((Real.pi * s) • -(J k * J'))) =
        NormedSpace.exp ((Real.pi * s) • reindex e e (-(J k * J'))) := by
      have hA2 : -(J k * J') * -(J k * J') = -1 := ((r_cs_iff e _).1 hc).2
      have hA2' : reindex e e (-(J k * J')) * reindex e e (-(J k * J')) = -1 := hc.2
      rw [Morse.exp_smul_of_mul_self_eq_neg_one hA2, Morse.exp_smul_of_mul_self_eq_neg_one hA2']
      ext i j; simp [one_apply]
    rw [r_mul, hexp]
    exact h

/-- B ⇒ A. The algebraic conjuncts come from B (transported from `Fin (card ι)` to an arbitrary finite
type `ι`): `omega_succ_decomp` is B's claim 1 (its last clause `J_k(-J_kJ') = J'` is one line of
algebra); `mul_mem_omega_succ` is B's claim 2; `semicircle_mem_omega` follows from B's geodesic
lying in `Ω_k` on `[0, 1]` — `J_k exp(πsA) = cos(πs)J_k + sin(πs)J'` (the project's `exp` formula,
outside the item) covers the angles in `[0, π]`, the angles in `[-π, 0]` come from `-J' ∈ Ω_{k+1}`,
and the rest by `2π`-periodicity. Not in B and re-proved outright: `mul_exp_eq_semicircle` (an
identity for any `J_k`, `J'` with `J_k² = (J_kJ')² = -1`, via the same `exp` formula) and
`trace_transpose_mul_eq_zero` (`tr(J'ᵀJ) = 0` for anticommuting complex structures, two lines). -/
theorem B_to_A : B → A := by
  intro hB
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro ι _ _ J k hJ hk J' hJ'
    obtain ⟨h1, h2, h3, -⟩ := B_transport hB hJ hk hJ'
    refine ⟨h1, h2, h3, ?_⟩
    have hJk : J k * J k = -1 := (hJ.cs k hk le_rfl).2
    rw [Matrix.mul_neg, ← Matrix.mul_assoc, hJk, Matrix.neg_mul, Matrix.one_mul, neg_neg]
  · intro ι _ _ J k hJ hk A hA hAk hAα
    set e := Fintype.equivFin ι
    have hJr := (isACFam_iff _ _).2 (hJ.reindex e)
    have h := (hB _ k _ hk hJr).2 (reindex e e A) ((r_cs_iff e A).2 hA)
      (by unfold AntiComm; rw [← r_mul, ← r_mul, hAk, r_neg])
      (fun α h1 h2 => by
        show reindex e e A * reindex e e (J α) = reindex e e (J α) * reindex e e A
        rw [← r_mul, ← r_mul, hAα α h1 (by omega)])
    rw [omegaK_eq_omega, ← r_mul, ← omega_iff_reindex] at h
    exact h
  · intro ι _ _ J k hJ hk J' hJ' t
    have hJk : J k * J k = -1 := (hJ.cs k hk le_rfl).2
    -- angles in `[0, π]`, for any `J'' ∈ Ω_{k+1}`
    have key : ∀ J'' ∈ Morse.Omega J (k + 1), ∀ s ∈ Set.Icc (0 : ℝ) 1,
        Real.cos (Real.pi * s) • J k + Real.sin (Real.pi * s) • J'' ∈ Morse.Omega J k := by
      intro J'' hJ'' s hs
      obtain ⟨hc, -, -, hgeo⟩ := B_transport hB hJ hk hJ''
      have := hgeo s hs
      rwa [Morse.exp_smul_of_mul_self_eq_neg_one hc.2, Matrix.mul_add, Matrix.mul_smul,
        Matrix.mul_smul, Matrix.mul_one, Matrix.mul_neg, ← Matrix.mul_assoc, hJk, Matrix.neg_mul,
        Matrix.one_mul, neg_neg] at this
    have hneg : -J' ∈ Morse.Omega J (k + 1) := by
      obtain ⟨hc, ha⟩ := hJ'
      exact ⟨hc.neg, fun α h1 h2 => by rw [Matrix.mul_neg, Matrix.neg_mul, ha α h1 h2]⟩
    -- reduce `t` modulo `2π` to `r ∈ [-π, π)`
    have hp : (0 : ℝ) < 2 * Real.pi := by positivity
    set r := toIcoMod hp (-Real.pi) t
    have hr := toIcoMod_mem_Ico hp (-Real.pi) t
    have ht : t = r + (toIcoDiv hp (-Real.pi) t : ℝ) * (2 * Real.pi) := by
      have := toIcoMod_add_toIcoDiv_zsmul hp (-Real.pi) t
      rw [zsmul_eq_mul] at this
      linarith
    rw [ht, Real.cos_add_int_mul_two_pi, Real.sin_add_int_mul_two_pi]
    have hpi := Real.pi_pos
    rcases le_or_gt 0 r with h0 | h0
    · have := key J' hJ' (r / Real.pi) ⟨div_nonneg h0 hpi.le,
        (div_le_one hpi).2 (by linarith [hr.2])⟩
      rwa [mul_div_cancel₀ _ hpi.ne'] at this
    · have := key (-J') hneg (-r / Real.pi) ⟨div_nonneg (by linarith) hpi.le,
        (div_le_one hpi).2 (by linarith [hr.1])⟩
      rwa [mul_div_cancel₀ _ hpi.ne', Real.cos_neg, Real.sin_neg, neg_smul_neg] at this
  · intro ι _ _ Jk J' hJk hA t
    rw [Morse.exp_smul_of_mul_self_eq_neg_one hA, Matrix.mul_add, Matrix.mul_smul,
      Matrix.mul_smul, Matrix.mul_one, Matrix.mul_neg, ← Matrix.mul_assoc, hJk, Matrix.neg_mul,
      Matrix.one_mul, neg_neg]
  · intro ι _ _ J J' h' hanti
    have h : Matrix.trace (J' * J) = -Matrix.trace (J' * J) := by
      conv_lhs => rw [hanti]
      rw [trace_neg, trace_mul_comm]
    rw [h'.transpose, Matrix.neg_mul, trace_neg]
    linarith

#rt_check RoundTrip.V15_7.A_to_B [Morse.omega_succ_decomp, Morse.mul_mem_omega_succ,
  Morse.semicircle_mem_omega, Morse.mul_exp_eq_semicircle, Morse.trace_transpose_mul_eq_zero]
#rt_check RoundTrip.V15_7.B_to_A [Morse.omega_succ_decomp, Morse.mul_mem_omega_succ,
  Morse.semicircle_mem_omega, Morse.mul_exp_eq_semicircle, Morse.trace_transpose_mul_eq_zero]
#rt_overlap RoundTrip.V15_7.B_to_A [Morse.omega_succ_decomp, Morse.mul_mem_omega_succ,
  Morse.semicircle_mem_omega, Morse.mul_exp_eq_semicircle, Morse.trace_transpose_mul_eq_zero]

end RoundTrip.V15_7
