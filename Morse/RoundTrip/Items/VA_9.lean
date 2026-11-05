import Morse
import RoundTrip.Check
import RoundTrip.Blind.VA_9

/-! # Round trip for VA_9 (Milnor, Appendix pp. 151–152: the maps `h₁` and their inverse `g`)

`A` is the conjunction of the types, universes at `0`, of `Morse.reparam_homotopic`
(reparametrizing the strips is homotopic to the identity) and `Morse.isHomotopyEquiv_of_milnorMap`
(a map `h₁` with Milnor's two properties is a homotopy equivalence). Both assume the `X_n` CLOSED.

`B` (faithful to Milnor) assumes only that `S` is increasing, and asks for a CONTINUOUS `g` given by
Milnor's formulas, with `h₁ g ≃ id ≃ g h₁`.

**`B` is false** (`not_B`): with `X = ℝ`, `X₀ = (0, ∞)` (not closed), `X_n = ℝ` for `n ≥ 1`, the map
`h₁(x, τ) = (x + E(x, τ), τ + dist(τ, ℤ))`, with
`E(x, τ) = clamp(2 - 2τ) · clamp((τ - ½)/x)`, is continuous on `X_Σ` and has Milnor's properties,
but Milnor's formula forces `g(x, 1 - x) = h₁(x, ½ + x) = (1 - x, 1)` for small `x > 0`, while
`g(0, 1) = (0, 1)`: `g` is discontinuous at `(0, 1)`. The point: `g` on the strip `X₀ × [½, 1]`
reads `h₁` near level `½`, and `(0, ½) ∉ X_Σ`, so nothing controls `h₁` there.
Hence `A ⇒ B` is false and `B ⇒ A` holds only ex falso.

**Corrected `B`** (`Bfix`: `B` with all `X_n` closed): `A ⇒ Bfix` is proved, using `A`'s first
clause (`reparam_homotopic`, for `R₄ ≃ id`) together with the project's DEFINITIONS `milnorInv`
(Milnor's `g`), `milnorH`, `milnorK` (his `H_u` and the analogous homotopy), transported along the
identity homeomorphism `tel S ≃ₜ telescope S`. Conversely `Bfix ⇒ A` (`Bfix_to_A`):
`isHomotopyEquiv_of_milnorMap` from `Bfix` (transport a project Milnor map to the blind telescope),
`reparam_homotopic` (not about `h₁`, so absent from `B`) re-proved outright. -/

namespace RoundTrip.VA_9

open Set Filter Topology
open scoped unitInterval

/-- `A`: the two listed theorems, universes at `0`. -/
def A : Prop :=
  (type_of% @Morse.reparam_homotopic.{0}) ∧ (type_of% @Morse.isHomotopyEquiv_of_milnorMap.{0})

theorem A_holds : A :=
  ⟨Morse.reparam_homotopic, Morse.isHomotopyEquiv_of_milnorMap⟩

/-! ### The counterexample -/

namespace Counter

/-- `X₀ = (0, ∞)`, `X_n = ℝ` for `n ≥ 1`. -/
def S : ℕ → Set ℝ := fun n => if n = 0 then Ioi 0 else univ

theorem S_succ (n : ℕ) : S (n + 1) = univ := by simp [S]

theorem mem_S_of_pos {x : ℝ} (hx : 0 < x) (n : ℕ) : x ∈ S n := by
  unfold S; split_ifs <;> simp [hx]

theorem S_mono : Monotone S := by
  intro m n h x hx
  by_cases hn : n = 0
  · subst hn
    obtain rfl : m = 0 := Nat.le_zero.1 h
    exact hx
  · simp [S, hn]

theorem mem_tel_iff {p : ℝ × ℝ} : p ∈ tel S ↔ (0 < p.1 ∧ 0 ≤ p.2) ∨ 1 ≤ p.2 := by
  constructor
  · rintro ⟨i, hi, h1, h2⟩
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · left
      simp only [S, if_true, mem_Ioi] at hi
      exact ⟨hi, by simpa using h1⟩
    · right
      have : (1 : ℝ) ≤ i := by exact_mod_cast hi0
      linarith
  · rintro (⟨hx, hτ⟩ | hτ)
    · exact ⟨⌊p.2⌋₊, mem_S_of_pos hx _, Nat.floor_le hτ, (Nat.lt_floor_add_one _).le⟩
    · have h0 : (0 : ℝ) ≤ p.2 := by linarith
      have hf : 1 ≤ ⌊p.2⌋₊ := Nat.le_floor (by simpa using hτ)
      refine ⟨⌊p.2⌋₊, ?_, Nat.floor_le h0, (Nat.lt_floor_add_one _).le⟩
      have : ⌊p.2⌋₊ ≠ 0 := by omega
      simp [S, this]

/-- `dist(τ, ℤ)`. -/
noncomputable def Dt (τ : ℝ) : ℝ := min (Int.fract τ) (1 - Int.fract τ)

/-- `clamp(2 - 2τ)`: `1` at `τ = ½`, `0` for `τ ≥ 1`. -/
def at' (τ : ℝ) : ℝ := max 0 (min 1 (2 - 2 * τ))

/-- `clamp((τ - ½)/x)`. -/
noncomputable def mt (x τ : ℝ) : ℝ := max 0 (min 1 ((τ - 1 / 2) / x))

noncomputable def Et (x τ : ℝ) : ℝ := at' τ * mt x τ

theorem continuous_Dt : Continuous Dt :=
  ContinuousOn.comp_fract'' (f := fun s : ℝ => min s (1 - s))
    (continuous_id.min (continuous_const.sub continuous_id)).continuousOn (by norm_num)

theorem Dt_nonneg (τ : ℝ) : 0 ≤ Dt τ :=
  le_min (Int.fract_nonneg _) (sub_nonneg.2 (Int.fract_lt_one _).le)

theorem Dt_natCast_add (n : ℕ) {t : ℝ} (h0 : 0 ≤ t) (h1 : t < 1) :
    Dt (n + t) = min t (1 - t) := by
  unfold Dt
  rw [Int.fract_natCast_add, Int.fract_eq_self.2 ⟨h0, h1⟩]

theorem Dt_natCast (n : ℕ) : Dt n = 0 := by
  unfold Dt
  rw [Int.fract_natCast]
  norm_num

theorem continuous_at' : Continuous at' :=
  continuous_const.max (continuous_const.min (continuous_const.sub
    (continuous_const.mul continuous_id)))

theorem at'_of_one_le {τ : ℝ} (h : 1 ≤ τ) : at' τ = 0 := by
  unfold at'
  rw [min_eq_right (by linarith), max_eq_left (by linarith)]

theorem mt_of_le {x τ : ℝ} (hx : 0 ≤ x) (h : τ ≤ 1 / 2) : mt x τ = 0 := by
  unfold mt
  have : (τ - 1 / 2) / x ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hx
  rw [min_eq_right (by linarith), max_eq_left this]

theorem Et_eq_zero {x τ : ℝ} (h : (τ ≤ 1 / 2 ∧ 0 ≤ x) ∨ 1 ≤ τ) : Et x τ = 0 := by
  rcases h with ⟨h, hx⟩ | h
  · simp [Et, mt_of_le hx h]
  · simp [Et, at'_of_one_le h]

theorem continuous_Et : Continuous fun z : ↥(tel S) => Et z.1.1 z.1.2 := by
  have hx : Continuous fun z : ↥(tel S) => z.1.1 := continuous_fst.comp continuous_subtype_val
  have hτ : Continuous fun z : ↥(tel S) => z.1.2 := continuous_snd.comp continuous_subtype_val
  rw [continuous_iff_continuousAt]
  intro z₀
  by_cases hx0 : 0 < z₀.1.1
  · have hm : ContinuousAt (fun z : ↥(tel S) => mt z.1.1 z.1.2) z₀ := by
      unfold mt
      exact continuousAt_const.max (continuousAt_const.min
        (((hτ.sub continuous_const).continuousAt).div hx.continuousAt hx0.ne'))
    exact ((continuous_at'.comp hτ).continuousAt).mul hm
  · have hτ0 : 1 ≤ z₀.1.2 := by
      rcases mem_tel_iff.1 z₀.2 with h | h
      · exact absurd h.1 hx0
      · exact h
    have hE0 : Et z₀.1.1 z₀.1.2 = 0 := Et_eq_zero (Or.inr hτ0)
    rw [ContinuousAt, hE0]
    refine squeeze_zero (g := fun z : ↥(tel S) => at' z.1.2) (fun z => ?_) (fun z => ?_) ?_
    · exact mul_nonneg (le_max_left _ _) (le_max_left _ _)
    · exact mul_le_of_le_one_right (le_max_left _ _) (max_le zero_le_one (min_le_left _ _))
    · have := (continuous_at'.comp hτ).tendsto z₀
      simp only [Function.comp_def] at this
      rwa [at'_of_one_le hτ0] at this

/-- The underlying function of the counterexample `h₁`. -/
noncomputable def h1fun (z : ↥(tel S)) : ℝ × ℝ := (z.1.1 + Et z.1.1 z.1.2, z.1.2 + Dt z.1.2)

theorem h1_mem (z : ↥(tel S)) : h1fun z ∈ tel S := by
  have hz := mem_tel_iff.1 z.2
  rw [mem_tel_iff]
  by_cases hτ : z.1.2 < 1 / 2
  · have hz' : 0 < z.1.1 ∧ 0 ≤ z.1.2 := by
      rcases hz with h | h
      · exact h
      · linarith
    left
    have hE : Et z.1.1 z.1.2 = 0 := Et_eq_zero (Or.inl ⟨hτ.le, hz'.1.le⟩)
    simp only [h1fun, hE, add_zero]
    exact ⟨hz'.1, add_nonneg hz'.2 (Dt_nonneg _)⟩
  · right
    simp only [h1fun]
    by_cases h1 : 1 ≤ z.1.2
    · linarith [Dt_nonneg z.1.2]
    · have h0 : 0 ≤ z.1.2 := by linarith
      have hD : Dt z.1.2 = 1 - z.1.2 := by
        have := Dt_natCast_add 0 h0 (by linarith)
        simp only [Nat.cast_zero, zero_add] at this
        rw [this, min_eq_right (by linarith)]
      linarith

/-- The counterexample `h₁ : X_Σ → X_Σ`. -/
noncomputable def h₁ : C(↥(tel S), ↥(tel S)) :=
  ⟨fun z => ⟨h1fun z, h1_mem z⟩,
    (((continuous_fst.comp continuous_subtype_val).add continuous_Et).prodMk
      ((continuous_snd.comp continuous_subtype_val).add
        (continuous_Dt.comp (continuous_snd.comp continuous_subtype_val)))).subtype_mk _⟩

theorem isH1 : IsH1 S h₁ := by
  constructor
  · intro z n t ht0 ht1 hzt
    change h1fun z = _
    have hD : Dt z.1.2 = t := by
      rw [hzt, Dt_natCast_add n ht0 (by linarith), min_eq_left (by linarith)]
    have hE : Et z.1.1 z.1.2 = 0 := by
      refine Et_eq_zero ?_
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · left
        refine ⟨by rw [hzt]; simpa using ht1, ?_⟩
        rcases mem_tel_iff.1 z.2 with h | h
        · exact h.1.le
        · rw [hzt] at h; simp at h; linarith
      · right
        have : (1 : ℝ) ≤ n := by exact_mod_cast hn
        rw [hzt]; linarith
    simp only [h1fun]
    rw [hE, hD, hzt]
    simp only [add_zero, Prod.mk.injEq, true_and]
    ring
  · intro z n t ht0 ht1 hzt
    refine ⟨by rw [S_succ]; trivial, ?_⟩
    change z.1.2 + Dt z.1.2 = n + 1
    rcases eq_or_lt_of_le ht1 with rfl | ht1'
    · have : z.1.2 = ((n + 1 : ℕ) : ℝ) := by rw [hzt]; push_cast; ring
      rw [this, Dt_natCast]
      push_cast; ring
    · rw [hzt, Dt_natCast_add n (by linarith) ht1', min_eq_right (by linarith)]
      ring

end Counter

open Counter in
/-- **`B` is false**: Milnor's `g` need not be continuous when the `X_n` are not closed. -/
theorem not_B : ¬ B := by
  intro hB
  obtain ⟨-, g, hglow, hghigh, -, -⟩ := hB ℝ S S_mono h₁ isH1
  -- the point `(0, 1)`
  have hz₀ : ((0 : ℝ), (1 : ℝ)) ∈ tel S := mem_tel_iff.2 (Or.inr le_rfl)
  let z₀ : ↥(tel S) := ⟨_, hz₀⟩
  have hg₀ : (g z₀).1.1 = 0 := by
    have := hglow z₀ 1 0 le_rfl (by norm_num) (by simp [z₀])
    rw [this]
  -- the points `(x_k, 1 - x_k)` and `(x_k, ½ + x_k)`
  let xk : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1) / 4
  have hxpos : ∀ k, 0 < xk k := fun k => by positivity
  have hxle : ∀ k, xk k ≤ 1 / 4 := fun k => by
    have : 1 / ((k : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
    simp only [xk]
    linarith
  have hzk : ∀ k, (xk k, 1 - xk k) ∈ tel S := fun k =>
    mem_tel_iff.2 (Or.inl ⟨hxpos k, by linarith [hxle k]⟩)
  have hwk : ∀ k, (xk k, 1 / 2 + xk k) ∈ tel S := fun k =>
    mem_tel_iff.2 (Or.inl ⟨hxpos k, by linarith [hxpos k]⟩)
  let zk : ℕ → ↥(tel S) := fun k => ⟨_, hzk k⟩
  have hgk : ∀ k, (g (zk k)).1.1 = 1 - xk k := by
    intro k
    have := hghigh (zk k) 0 (1 - xk k) (by linarith [hxle k]) (by linarith [hxpos k])
      (by simp [zk]) ⟨_, hwk k⟩ (by
        refine Prod.ext rfl ?_
        change 1 / 2 + xk k = ((0 : ℕ) : ℝ) + 3 / 2 - (1 - xk k)
        push_cast; ring)
    rw [this]
    change xk k + Et (xk k) (1 / 2 + xk k) = 1 - xk k
    have ha : at' (1 / 2 + xk k) = 1 - 2 * xk k := by
      unfold at'
      rw [min_eq_right (by linarith [hxpos k]), max_eq_right (by linarith [hxle k])]
      ring
    have hm : Counter.mt (xk k) (1 / 2 + xk k) = 1 := by
      unfold Counter.mt
      rw [show 1 / 2 + xk k - 1 / 2 = xk k by ring, div_self (hxpos k).ne', min_self,
        max_eq_right zero_le_one]
    rw [Et, ha, hm]
    ring
  -- `x_k → 0`
  have hx0 : Tendsto xk atTop (𝓝 0) := by
    have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).div_const 4
    simpa [xk] using this
  have hzt : Tendsto zk atTop (𝓝 z₀) := by
    rw [tendsto_subtype_rng]
    change Tendsto (fun k => (xk k, 1 - xk k)) atTop (𝓝 ((0 : ℝ), (1 : ℝ)))
    refine hx0.prodMk_nhds ?_
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub hx0
  have h1 : Tendsto (fun k => (g (zk k)).1.1) atTop (𝓝 ((g z₀).1.1)) :=
    ((continuous_fst.comp continuous_subtype_val).tendsto _).comp
      ((g.continuous.tendsto z₀).comp hzt)
  have h2 : Tendsto (fun k => (g (zk k)).1.1) atTop (𝓝 1) := by
    simp only [hgk]
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub hx0
  have := tendsto_nhds_unique h1 h2
  rw [hg₀] at this
  norm_num at this

/-- `B ⇒ A`, only ex falso. -/
theorem B_to_A : B → A := fun hB => absurd hB not_B

#rt_check RoundTrip.VA_9.not_B [Morse.reparam_homotopic, Morse.isHomotopyEquiv_of_milnorMap]
#rt_check RoundTrip.VA_9.B_to_A [Morse.reparam_homotopic, Morse.isHomotopyEquiv_of_milnorMap]
#rt_overlap RoundTrip.VA_9.B_to_A [Morse.reparam_homotopic, Morse.isHomotopyEquiv_of_milnorMap]

/-! ### The corrected statement: all `X_n` closed -/

/-- `B` with Milnor's missing hypothesis: all `X_n` closed. -/
def Bfix : Prop :=
  ∀ (X : Type) [TopologicalSpace X] (S : ℕ → Set X), Monotone S → (∀ n, IsClosed (S n)) →
    ∀ h₁ : C(↥(tel S), ↥(tel S)), IsH1 S h₁ →
    (∀ (z w : ↥(tel S)) (x : X) (n : ℕ), z.1 = (x, (n : ℝ) + 1 / 2) → w.1 = (x, (n : ℝ) + 1) →
      h₁ z = h₁ w ∧ (h₁ w).1 = (x, (n : ℝ) + 1)) ∧
    ∃ g : C(↥(tel S), ↥(tel S)),
      (∀ (z : ↥(tel S)) (n : ℕ) (t : ℝ), 0 ≤ t → t ≤ 1 / 2 → z.1.2 = n + t →
        (g z).1 = (z.1.1, (n : ℝ) + 2 * t)) ∧
      (∀ (z : ↥(tel S)) (n : ℕ) (t : ℝ), 1 / 2 ≤ t → t ≤ 1 → z.1.2 = n + t →
        ∀ w : ↥(tel S), w.1 = (z.1.1, (n : ℝ) + 3 / 2 - t) → (g z).1 = (h₁ w).1) ∧
      (h₁.comp g).Homotopic (ContinuousMap.id _) ∧ (g.comp h₁).Homotopic (ContinuousMap.id _)

theorem B_to_Bfix : B → Bfix := fun hB X _ S hS _ => hB X S hS

section Glue

variable {X : Type} [TopologicalSpace X]

omit [TopologicalSpace X] in
theorem tel_eq_telescope (S : ℕ → Set X) : tel S = Morse.telescope S := by
  ext z
  simp only [tel, Morse.telescope, mem_iUnion, mem_prod, mem_Icc]; rfl

/-- The identity homeomorphism `tel S ≃ₜ telescope S`. -/
noncomputable def telHomeo (S : ℕ → Set X) : ↥(tel S) ≃ₜ ↥(Morse.telescope S) :=
  Homeomorph.setCongr (tel_eq_telescope S)

@[simp] theorem coe_telHomeo (S : ℕ → Set X) (z : ↥(tel S)) :
    ((telHomeo S z : ↥(Morse.telescope S)) : X × ℝ) = z := rfl

@[simp] theorem coe_telHomeo_symm (S : ℕ → Set X) (z : ↥(Morse.telescope S)) :
    (((telHomeo S).symm z : ↥(tel S)) : X × ℝ) = z := rfl

/-- `h₁` transported to the project's telescope. -/
noncomputable def toPsi (S : ℕ → Set X) (h₁ : C(↥(tel S), ↥(tel S))) :
    C(↥(Morse.telescope S), ↥(Morse.telescope S)) :=
  (telHomeo S : C(↥(tel S), ↥(Morse.telescope S))).comp
    (h₁.comp ((telHomeo S).symm : C(↥(Morse.telescope S), ↥(tel S))))

theorem isMilnorMap_toPsi {S : ℕ → Set X} {h₁ : C(↥(tel S), ↥(tel S))} (hh : IsH1 S h₁) :
    Morse.IsMilnorMap (toPsi S h₁) where
  low n x t ht := by
    apply Subtype.ext
    change ((h₁ ((telHomeo S).symm (Morse.stripMap S n (x, t)))) : X × ℝ) =
      ((x : X), (n : ℝ) + (Morse.clampI (2 * t) : ℝ))
    rw [hh.1 _ n t t.2.1 ht rfl, Morse.clampI_two_mul ht]
    rfl
  high n x t ht := (hh.2 _ n t ht t.2.2 rfl).2

end Glue

/-- **`A ⇒ Bfix`.** `g` is the project's `milnorInv` (Milnor's formula), transported; `h₁ g ≃ R₄`
and `g h₁ ≃ R₄` are the project's homotopies `milnorH`, `milnorK` (definitions), and `R₄ ≃ id`
is `A`'s `reparam_homotopic`. -/
theorem A_to_Bfix : A → Bfix := by
  rintro ⟨hrep, -⟩ X _ S hS hSc h₁ hh
  have hψ := isMilnorMap_toPsi hh
  set e := telHomeo S
  set ψ := toPsi S h₁
  have hT := tel_eq_telescope S
  have hmemT : ∀ y : X × ℝ, y ∈ tel S → y ∈ Morse.telescope S := fun y hy => hT ▸ hy
  refine ⟨?_, ?_⟩
  · -- (a) well-definedness
    intro z w x n hz hw
    have h1 : (h₁ z).1 = (x, (n : ℝ) + 1) := by
      rw [hh.1 z n (1 / 2) (by norm_num) le_rfl (by rw [hz])]
      rw [hz]; simp only [Prod.mk.injEq, true_and]; ring
    have h2 : (h₁ w).1 = (x, (n : ℝ) + 1) := by
      rw [hh.1 w (n + 1) 0 le_rfl (by norm_num) (by rw [hw]; push_cast; ring)]
      rw [hw]; simp only [Prod.mk.injEq, true_and]; push_cast; ring
    exact ⟨Subtype.ext (h1.trans h2.symm), h2⟩
  let mI := Morse.milnorInv hS hSc ψ hψ
  let g : C(↥(tel S), ↥(tel S)) :=
    (e.symm : C(↥(Morse.telescope S), ↥(tel S))).comp (mI.comp (e : C(↥(tel S), ↥(Morse.telescope S))))
  have hR : (Morse.scaleMap hS hSc 4 (by norm_num)).Homotopic (ContinuousMap.id _) :=
    hrep hS hSc _ _ _
  refine ⟨g, ?_, ?_, ?_, ?_⟩
  · -- low formula
    intro z n t ht0 ht1 hzt
    have hx : z.1.1 ∈ S n := Morse.mem_of_mem_telescope hS (hmemT _ z.2) (by rw [hzt]; linarith)
    have hez : e z = Morse.stripMap S n (⟨z.1.1, hx⟩, ⟨t, ht0, by linarith⟩) :=
      Subtype.ext (Prod.ext rfl (by change (z : X × ℝ).2 = (n : ℝ) + t; exact hzt))
    change ((mI (e z) : ↥(Morse.telescope S)) : X × ℝ) = _
    rw [hez, Morse.milnorInv_low hS hSc ψ hψ n _ _ ht1]
    change ((z.1.1, (n : ℝ) + (Morse.clampI (2 * t) : ℝ)) : X × ℝ) = _
    rw [Morse.clampI_val (by linarith) (by linarith)]
  · -- high formula
    intro z n t ht0 ht1 hzt w hw
    have hx : z.1.1 ∈ S n := by
      rcases eq_or_lt_of_le ht0 with ht | ht
      · exact Morse.mem_of_mem_telescope hS (hmemT _ z.2) (by rw [hzt, ← ht]; linarith)
      · have := Morse.mem_of_mem_telescope hS (hmemT _ w.2) (n := n)
          (by rw [hw]; simp only; linarith)
        rwa [hw] at this
    have hez : e z = Morse.stripMap S n (⟨z.1.1, hx⟩, ⟨t, by linarith, ht1⟩) :=
      Subtype.ext (Prod.ext rfl (by change (z : X × ℝ).2 = (n : ℝ) + t; exact hzt))
    change ((mI (e z) : ↥(Morse.telescope S)) : X × ℝ) = _
    rw [hez]
    rcases eq_or_lt_of_le ht0 with ht | ht
    · subst ht
      rw [Morse.milnorInv_low hS hSc ψ hψ n _ _ (by norm_num)]
      have h2 : (h₁ w).1 = (z.1.1, (n : ℝ) + 1) := by
        rw [hh.1 w (n + 1) 0 le_rfl (by norm_num) (by rw [hw]; push_cast; ring)]
        rw [hw]; simp only [Prod.mk.injEq, true_and]; push_cast; ring
      rw [h2]
      change ((z.1.1, (n : ℝ) + (Morse.clampI (2 * (1 / 2 : ℝ)) : ℝ)) : X × ℝ) = _
      rw [Morse.clampI_val (by norm_num) (by norm_num)]
      norm_num
    · rw [Morse.milnorInv_high hS hSc ψ hψ n _ _ ht]
      change ((h₁ ((telHomeo S).symm (Morse.stripMap S n (⟨z.1.1, hx⟩,
        Morse.clampI (3 / 2 - t))))) : X × ℝ) = _
      congr 2
      apply Subtype.ext
      change ((z.1.1, (n : ℝ) + (Morse.clampI (3 / 2 - t) : ℝ)) : X × ℝ) = w.1
      rw [Morse.clampI_val (by linarith) (by linarith), hw]
      simp only [Prod.mk.injEq, true_and]; ring
  · -- `h₁ g ≃ id`
    have hH : (ψ.comp mI).Homotopic (ContinuousMap.id _) :=
      ContinuousMap.Homotopic.trans ⟨Morse.milnorH hS hSc ψ hψ⟩ hR
    have := (ContinuousMap.Homotopic.refl (e.symm : C(↥(Morse.telescope S), ↥(tel S)))).comp
      (hH.comp (ContinuousMap.Homotopic.refl (e : C(↥(tel S), ↥(Morse.telescope S)))))
    convert this using 1
    · exact ContinuousMap.ext fun z => rfl
    · exact ContinuousMap.ext fun z => rfl
  · -- `g h₁ ≃ id`
    have hK : (mI.comp ψ).Homotopic (ContinuousMap.id _) :=
      ContinuousMap.Homotopic.trans ⟨Morse.milnorK hS hSc ψ hψ⟩ hR
    have := (ContinuousMap.Homotopic.refl (e.symm : C(↥(Morse.telescope S), ↥(tel S)))).comp
      (hK.comp (ContinuousMap.Homotopic.refl (e : C(↥(tel S), ↥(Morse.telescope S)))))
    convert this using 1
    · exact ContinuousMap.ext fun z => rfl
    · exact ContinuousMap.ext fun z => rfl

#rt_check RoundTrip.VA_9.A_to_Bfix [Morse.reparam_homotopic, Morse.isHomotopyEquiv_of_milnorMap]
#rt_overlap RoundTrip.VA_9.A_to_Bfix [Morse.reparam_homotopic, Morse.isHomotopyEquiv_of_milnorMap]

/-! ### `Bfix ⇒ A` -/

section BfixToA

open Morse

variable {X : Type} [TopologicalSpace X] {S : ℕ → Set X}

/-- `reparam_homotopic`, re-proved outright (straight-line homotopy on each strip; not a statement
about Milnor's `h₁`, so not in `B`). -/
theorem reparam_homotopic' (hA : Monotone S) (hAc : ∀ n, IsClosed (S n)) (ρ : C(I, I))
    (h₀ : ρ 0 = 0) (h₁ : ρ 1 = 1) : (reparam hA hAc ρ h₀ h₁).Homotopic (ContinuousMap.id _) := by
  refine ⟨telescopeHomotopy hA hAc (fun n => ⟨fun q => stripMap S n
    (q.2.1, clampI ((1 - (q.1 : ℝ)) * ρ q.2.2 + q.1 * q.2.2)), ?_⟩) ?_ ?_ ?_⟩
  · refine (stripMap S n).continuous.comp ((continuous_fst.comp continuous_snd).prodMk
      (continuous_clampI.comp ?_))
    have hs : Continuous fun q : I × (S n × I) => ((q.1 : I) : ℝ) :=
      continuous_subtype_val.comp continuous_fst
    exact ((continuous_const.sub hs).mul (continuous_subtype_val.comp (ρ.continuous.comp
      (continuous_snd.comp continuous_snd)))).add (hs.mul continuous_param)
  · intro n s x
    change stripMap S (n + 1) (up hA n x, clampI ((1 - (s : ℝ)) * ρ 0 + s * ((0 : I) : ℝ))) =
      stripMap S n (x, clampI ((1 - (s : ℝ)) * ρ 1 + s * ((1 : I) : ℝ)))
    rw [h₀, h₁, clampI_eq (t := 0) (by simp), clampI_eq (t := 1) (by simp), stripMap_one hA]
  · intro n x t
    change stripMap S n (x, clampI ((1 - ((0 : I) : ℝ)) * ρ t + ((0 : I) : ℝ) * t)) =
      reparam hA hAc ρ h₀ h₁ (stripMap S n (x, t))
    rw [reparam_stripMap, clampI_eq (t := ρ t) (by simp)]
  · intro n x t
    change stripMap S n (x, clampI ((1 - ((1 : I) : ℝ)) * ρ t + ((1 : I) : ℝ) * t)) =
      stripMap S n (x, t)
    rw [clampI_eq (t := t) (by simp)]

/-- A Milnor map on the project's telescope, transported to the blind telescope. -/
noncomputable def fromPsi (S : ℕ → Set X) (ψ : C(↥(telescope S), ↥(telescope S))) :
    C(↥(tel S), ↥(tel S)) :=
  ((telHomeo S).symm : C(↥(telescope S), ↥(tel S))).comp
    (ψ.comp (telHomeo S : C(↥(tel S), ↥(telescope S))))

theorem isH1_fromPsi (hA : Monotone S) {ψ : C(↥(telescope S), ↥(telescope S))}
    (hψ : IsMilnorMap ψ) : IsH1 S (fromPsi S ψ) := by
  have hT := tel_eq_telescope S
  have hmemT : ∀ y : X × ℝ, y ∈ tel S → y ∈ telescope S := fun y hy => hT ▸ hy
  constructor
  · intro z n t ht0 ht1 hzt
    have hx : z.1.1 ∈ S n := mem_of_mem_telescope hA (hmemT _ z.2) (by rw [hzt]; linarith)
    have hez : telHomeo S z = stripMap S n (⟨z.1.1, hx⟩, ⟨t, ht0, by linarith⟩) :=
      Subtype.ext (Prod.ext rfl (by change (z : X × ℝ).2 = (n : ℝ) + t; exact hzt))
    change ((ψ (telHomeo S z) : ↥(telescope S)) : X × ℝ) = _
    rw [hez, hψ.low n _ _ ht1]
    change ((z.1.1, (n : ℝ) + (clampI (2 * t) : ℝ)) : X × ℝ) = _
    rw [clampI_val (by linarith) (by linarith)]
  · intro z n t ht0 ht1 hzt
    change ((ψ (telHomeo S z) : ↥(telescope S)) : X × ℝ).1 ∈ S (n + 1) ∧
      ((ψ (telHomeo S z) : ↥(telescope S)) : X × ℝ).2 = n + 1
    have hlev : ((ψ (telHomeo S z) : ↥(telescope S)) : X × ℝ).2 = n + 1 := by
      rcases eq_or_lt_of_le ht1 with rfl | ht1'
      · rw [hψ.fix hA (z := telHomeo S z) (m := n + 1) (by
          change (z : X × ℝ).2 = _; rw [hzt]; push_cast; ring)]
        change (z : X × ℝ).2 = _
        rw [hzt]
      · have hx : z.1.1 ∈ S n := mem_of_mem_telescope hA (hmemT _ z.2) (by rw [hzt]; linarith)
        have hez : telHomeo S z = stripMap S n (⟨z.1.1, hx⟩, ⟨t, by linarith, ht1⟩) :=
          Subtype.ext (Prod.ext rfl (by change (z : X × ℝ).2 = (n : ℝ) + t; exact hzt))
        rw [hez]
        exact hψ.high n _ _ ht0
    refine ⟨mem_of_mem_telescope hA (ψ (telHomeo S z)).2 (by rw [hlev]; push_cast; linarith),
      hlev⟩

theorem isHomotopyEquiv_conj {P Q : Type} [TopologicalSpace P] [TopologicalSpace Q] (e : P ≃ₜ Q)
    {ψ : C(Q, Q)} (h : Morse.IsHomotopyEquiv ((e.symm : C(Q, P)).comp (ψ.comp (e : C(P, Q))))) :
    Morse.IsHomotopyEquiv ψ := by
  have h' := ((Morse.IsHomotopyEquiv.of_homeomorph e.symm).comp h).comp
    (Morse.IsHomotopyEquiv.of_homeomorph e)
  have : ((e : C(P, Q)).comp (((e.symm : C(Q, P)).comp (ψ.comp (e : C(P, Q)))).comp
      (e.symm : C(Q, P)))) = ψ := by
    ext x; simp
  rwa [this] at h'

end BfixToA

/-- `Bfix ⇒ A`: `isHomotopyEquiv_of_milnorMap` from `Bfix` (a Milnor map `ψ` on the project's
telescope, transported, satisfies `IsH1`; `Bfix`'s `g` is a homotopy inverse); `reparam_homotopic`
outright. -/
theorem Bfix_to_A : Bfix → A := by
  intro hB
  refine ⟨fun hA hAc ρ h₀ h₁ => reparam_homotopic' hA hAc ρ h₀ h₁, ?_⟩
  intro X _ S hA hAc ψ hψ
  obtain ⟨-, g, -, -, hg1, hg2⟩ := hB X S hA hAc (fromPsi S ψ) (isH1_fromPsi hA hψ)
  exact isHomotopyEquiv_conj (telHomeo S) ⟨g, hg2, hg1⟩

#rt_check RoundTrip.VA_9.Bfix_to_A [Morse.reparam_homotopic, Morse.isHomotopyEquiv_of_milnorMap]
#rt_overlap RoundTrip.VA_9.Bfix_to_A [Morse.reparam_homotopic, Morse.isHomotopyEquiv_of_milnorMap]

end RoundTrip.VA_9
