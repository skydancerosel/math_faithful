import Morse
import RoundTrip.Check
import RoundTrip.Blind.V15_10

open Matrix

namespace RoundTrip.V15_10

/-- The project's statement (universes instantiated at `0`; `Morse.IsClifford` is vocabulary): an
anticommuting family of matrix complex structures satisfies the Clifford relations, and in an
arbitrary ring with `J_1, …, J_k` satisfying the Clifford relations: the commute/anticommute tables
of `θ₃ = J_1J_2J_3`, `θ₅ = J_1J_4J_5`, `θ₆ = J_2J_4J_6`, `θ₇ = J_1J_6J_7`, `J_3J_4`, `J_7J_8`, and
`ω₇ = J_1⋯J_7 = -θ₃θ₅θ₇` commutes with `J_1, …, J_7`. -/
def A : Prop :=
  type_of% @Morse.IsAnticommFamily.isClifford.{0} ∧ type_of% @Morse.θ₃_spec.{0} ∧
    type_of% @Morse.θ₃_anticommute.{0} ∧ type_of% @Morse.θ₅_spec.{0} ∧
    type_of% @Morse.θ₆_spec.{0} ∧ type_of% @Morse.θ₇_spec.{0} ∧ type_of% @Morse.J₃J₄_spec.{0} ∧
    type_of% @Morse.J₇J₈_spec.{0} ∧ type_of% @Morse.ω₇_spec.{0}

theorem A_holds : A :=
  ⟨@Morse.IsAnticommFamily.isClifford.{0}, @Morse.θ₃_spec.{0}, @Morse.θ₃_anticommute.{0},
    @Morse.θ₅_spec.{0}, @Morse.θ₆_spec.{0}, @Morse.θ₇_spec.{0}, @Morse.J₃J₄_spec.{0},
    @Morse.J₇J₈_spec.{0}, @Morse.ω₇_spec.{0}⟩

/-! Vocabulary: the blind notions are the project's. -/

theorem isACFam_iff {ι : Type} [Fintype ι] [DecidableEq ι] (Js : ℕ → Mat ι) (m : ℕ) :
    IsACFam Js m ↔ Morse.IsAnticommFamily Js m :=
  ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.cs, h.anti⟩⟩

theorem anti_symm' {ι : Type} [Fintype ι] [DecidableEq ι] {x y : Mat ι} (h : x * y = -(y * x)) :
    AntiComm y x := by
  unfold AntiComm; rw [h, neg_neg]

/-- A matrix killing every vector is `0`. -/
theorem eq_zero_of_mulVec {ι : Type} [Fintype ι] [DecidableEq ι] {M : Mat ι}
    (h : ∀ v, M *ᵥ v = 0) : M = 0 := by
  have : Matrix.toLin' M = 0 := LinearMap.ext fun v => by simpa using h v
  simpa using this

/-- A central involution of a minimal space is `±1` (the eigenspace argument). -/
theorem central_eq {ι : Type} [Fintype ι] [DecidableEq ι] {Js : ℕ → Mat ι} {m : ℕ} {ω : Mat ι}
    (hmin : IsMinimalSp Js m) (hω : ω * ω = 1) (hc : ∀ α, 1 ≤ α → α ≤ m → Commute ω (Js α)) :
    ω = 1 ∨ ω = -1 := by
  set W := LinearMap.ker (Matrix.mulVecLin (ω - 1)) with hW
  have hmem : ∀ v, v ∈ W ↔ (ω - 1) *ᵥ v = 0 := fun v => by
    rw [hW, LinearMap.mem_ker, Matrix.mulVecLin_apply]
  have hinv : ∀ α, 1 ≤ α → α ≤ m → ∀ v ∈ W, Js α *ᵥ v ∈ W := by
    intro α h1 h2 v hv
    rw [hmem] at hv ⊢
    have : (ω - 1) * Js α = Js α * (ω - 1) := by
      rw [Matrix.sub_mul, Matrix.mul_sub, (hc α h1 h2).eq, Matrix.one_mul, Matrix.mul_one]
    rw [mulVec_mulVec, this, ← mulVec_mulVec, hv, mulVec_zero]
  rcases hmin W hinv with hbot | htop
  · right
    have : ω + 1 = 0 := by
      refine eq_zero_of_mulVec fun v => ?_
      have hv : (ω + 1) *ᵥ v ∈ W := by
        rw [hmem, mulVec_mulVec]
        have : (ω - 1) * (ω + 1) = 0 := by
          simp only [Matrix.sub_mul, Matrix.mul_add, hω, Matrix.one_mul, Matrix.mul_one]
          abel
        rw [this, zero_mulVec]
      rw [hbot, Submodule.mem_bot] at hv
      exact hv
    exact eq_neg_of_add_eq_zero_left this
  · left
    have : ω - 1 = 0 := eq_zero_of_mulVec fun v => (hmem v).1 (htop ▸ Submodule.mem_top)
    exact sub_eq_zero.1 this

/-- A ⇒ B. Part 1 is A's tables, specialized to the matrix ring (through A's
`IsAnticommFamily.isClifford`). Part 2: A's `ω₇_spec` (`ω₇ = -θ₃θ₅θ₇` central), with `ω₇² = 1` from
A's `θ` tables, makes `ω₇ = ±1` on a minimal space (`central_eq`, the eigenspace argument), and then
`J_7 = ∓J_1⋯J_6`. -/
theorem A_to_B : A → B := by
  rintro ⟨hcl, h3, h3a, h5, h6, h7, h34, h78, hω⟩
  refine ⟨fun n Js hJ => ?_, fun n Js hJ hmin => ?_⟩
  · have hC := hcl ((isACFam_iff Js 8).1 hJ)
    obtain ⟨s3, c31, c32, -⟩ := h3 (hC.mono (by norm_num))
    obtain ⟨a34, -, -⟩ := h34 (hC.mono (by norm_num))
    obtain ⟨s5, c51, -, -, a52, -, c53⟩ := h5 (hC.mono (by norm_num))
    obtain ⟨s6, -, -, -, a61, -, -, c63, c65⟩ := h6 (hC.mono (by norm_num))
    obtain ⟨s7, -, -, -, -, -, -, -, c73, c75, c76⟩ := h7 (hC.mono (by norm_num))
    obtain ⟨c783, c785, c786, a787⟩ := h78 hC
    exact ⟨⟨s3, c31, c32, a34⟩, ⟨s5, c51, c53, anti_symm' a52⟩, ⟨s6, c63, c65, anti_symm' a61⟩,
      ⟨s7, c73, c75, c76, a787, c783, c785, c786⟩⟩
  · have hC := hcl ((isACFam_iff Js 7).1 hJ)
    obtain ⟨heq, hcomm⟩ := hω hC
    obtain ⟨s3, -⟩ := h3 (hC.mono (by norm_num))
    obtain ⟨s5, -, -, -, -, -, c53⟩ := h5 (hC.mono (by norm_num))
    obtain ⟨s7, -, -, -, -, -, -, -, c73, c75, -⟩ := h7 hC
    have hsq : Morse.ω₇ Js * Morse.ω₇ Js = 1 := by
      rw [heq, neg_mul_neg]
      set a := Morse.θ₃ Js
      set b := Morse.θ₅ Js
      set c := Morse.θ₇ Js
      calc a * b * c * (a * b * c) = a * b * (c * a) * b * c := by simp only [mul_assoc]
        _ = a * b * (a * c) * b * c := by rw [c73.eq]
        _ = a * (b * a) * (c * b) * c := by simp only [mul_assoc]
        _ = a * (a * b) * (b * c) * c := by rw [c53.eq, c75.eq]
        _ = (a * a) * (b * b) * (c * c) := by simp only [mul_assoc]
        _ = 1 := by rw [s3, s5, s7, one_mul, one_mul]
    have hJ7 : Js 7 * Js 7 = -1 := (hJ.1 7 (by norm_num) le_rfl).2
    have hω7 : Morse.ω₇ Js = Js 1 * Js 2 * Js 3 * Js 4 * Js 5 * Js 6 * Js 7 := rfl
    rcases central_eq hmin hsq hcomm with h1 | h1
    · right
      have := congrArg (· * Js 7) h1
      simp only [hω7, Matrix.mul_assoc, hJ7, Matrix.one_mul] at this
      rw [← this]
      simp only [Matrix.mul_assoc, Matrix.mul_neg, Matrix.mul_one]
    · left
      have := congrArg (· * Js 7) h1
      simp only [hω7, Matrix.mul_assoc, hJ7, Matrix.neg_mul, Matrix.one_mul] at this
      have h' := congrArg Neg.neg this
      rw [neg_neg] at h'
      rw [← h']
      simp only [Matrix.mul_assoc, Matrix.mul_neg, Matrix.mul_one, neg_neg]

/-- B ⇒ A, vacuously: A is re-proved outright (each item is a word computation with the project's
`clifford_simp`, the method of the project's own proofs). B cannot give A: A holds in an arbitrary
ring (B only for real matrices with orthogonal `J_α` on `ℝⁿ`), and A has more relations than B
(`θ₃` commutes with `J_3`, `θ_*` anticommutes with the higher `J_α`, `J_3J_4` commutes with
`J_1, J_2`, `ω₇` is central, …). -/
theorem B_to_A : B → A := by
  intro _
  refine ⟨fun {n} _ _ {J} {k} h => ⟨fun α h1 h2 => (h.cs α h1 h2).2, h.anti⟩, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_⟩
  · intro R _ J h
    unfold Morse.θ₃ Commute SemiconjBy; refine ⟨?_, ?_, ?_, ?_⟩ <;> clifford_simp h
  · intro R _ J k α h h4 hk
    unfold Morse.AntiCommute Morse.θ₃; clifford_simp h
  · intro R _ J h
    unfold Morse.θ₅ Morse.θ₃ Commute SemiconjBy Morse.AntiCommute
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> clifford_simp h
  · intro R _ J h
    unfold Morse.θ₆ Morse.θ₃ Morse.θ₅ Commute SemiconjBy Morse.AntiCommute
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> clifford_simp h
  · intro R _ J h
    unfold Morse.θ₇ Morse.θ₃ Morse.θ₅ Morse.θ₆ Commute SemiconjBy Morse.AntiCommute
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> clifford_simp h
  · intro R _ J h
    unfold Morse.θ₃ Commute SemiconjBy Morse.AntiCommute
    refine ⟨?_, ?_, ?_⟩ <;> clifford_simp h
  · intro R _ J h
    unfold Morse.θ₃ Morse.θ₅ Morse.θ₆ Morse.θ₇ Commute SemiconjBy Morse.AntiCommute
    refine ⟨?_, ?_, ?_, ?_⟩ <;> clifford_simp h
  · intro R _ J h
    unfold Morse.ω₇ Morse.θ₃ Morse.θ₅ Morse.θ₇ Commute SemiconjBy
    refine ⟨by clifford_simp h, fun α h1 h2 => ?_⟩
    interval_cases α <;> clifford_simp h

#rt_check RoundTrip.V15_10.A_to_B [Morse.IsAnticommFamily.isClifford, Morse.θ₃_spec,
  Morse.θ₃_anticommute, Morse.θ₅_spec, Morse.θ₆_spec, Morse.θ₇_spec, Morse.J₃J₄_spec,
  Morse.J₇J₈_spec, Morse.ω₇_spec]
#rt_check RoundTrip.V15_10.B_to_A [Morse.IsAnticommFamily.isClifford, Morse.θ₃_spec,
  Morse.θ₃_anticommute, Morse.θ₅_spec, Morse.θ₆_spec, Morse.θ₇_spec, Morse.J₃J₄_spec,
  Morse.J₇J₈_spec, Morse.ω₇_spec]
#rt_overlap RoundTrip.V15_10.B_to_A [Morse.IsAnticommFamily.isClifford, Morse.θ₃_spec,
  Morse.θ₃_anticommute, Morse.θ₅_spec, Morse.θ₆_spec, Morse.θ₇_spec, Morse.J₃J₄_spec,
  Morse.J₇J₈_spec, Morse.ω₇_spec]

end RoundTrip.V15_10
