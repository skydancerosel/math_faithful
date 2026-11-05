import Morse
import RoundTrip.Check
import RoundTrip.Blind.V15_45

open Matrix Topology

noncomputable section

namespace RoundTrip.V15_45

/-- The project's statement (no universe parameters): Theorem 24.7 in the stable range, for
`i ≥ 0`, `n ≥ i + 2`, `n' ≥ i + 10`: `π_i(O(n), I) ≃ π_{i+8}(O(n'), I)` — as SETS, at the base
point `I`. -/
def A : Prop := type_of% @Morse.theorem_24_7

theorem A_holds : A := @Morse.theorem_24_7

/-! ### Glue -/

section Glue

open Morse.Homotopy

/-- `O(m)` as the type of the blind file, with its base point `I`. -/
abbrev one' (m : ℕ) : ↥(Orth (Fin m)) := ⟨1, (Matrix.orthogonalGroup (Fin m) ℝ).one_mem⟩

/-- Left translation by `g` moves the base point `I` of `O(m)` to `g`. -/
def bc {m : ℕ} (g : ↥(Matrix.orthogonalGroup (Fin m) ℝ)) (n : ℕ) :
    π_ n ↥(Orth (Fin m)) (one' m) ≃ π_ n ↥(Orth (Fin m)) g :=
  piEquivOfHomeomorph (Homeomorph.mulLeft g) (mul_one g) n

theorem bcM {m : ℕ} (g : ↥(Matrix.orthogonalGroup (Fin m) ℝ)) (n : ℕ) :
    Nonempty (π_ (n + 1) ↥(Orth (Fin m)) (one' m) ≃* π_ (n + 1) ↥(Orth (Fin m)) g) :=
  nonempty_mulEquiv_of_homeomorph (Homeomorph.mulLeft g) (mul_one g) n

/-- The iterated loop space: `π_i(Ω^k(X, x)) ≃ π_{i+k}(X, x)` (the project's
`homotopyGroupPiLoopEquiv`, `π_i(ΩY) ≃ π_{i+1}Y`, applied `k` times). -/
theorem iterLoop_pi (X : TopCat.{0}) (x : X) :
    ∀ (k i : ℕ), Nonempty (π_ i (iterLoop k X x).1 (iterLoop k X x).2 ≃ π_ (i + k) X x)
  | 0, i => ⟨Equiv.refl _⟩
  | k + 1, i => by
    obtain ⟨e⟩ := iterLoop_pi X x k (i + 1)
    have e₁ := homotopyGroupPiLoopEquiv (X := (iterLoop k X x).1) (x := (iterLoop k X x).2) i
    exact ⟨e₁.trans (e.trans (Equiv.cast (by rw [Nat.add_right_comm, Nat.add_assoc])))⟩

/-- The same as groups. -/
theorem iterLoop_piM (X : TopCat.{0}) (x : X) :
    ∀ (k i j : ℕ), i + k = j →
      Nonempty (π_ (i + 1) (iterLoop k X x).1 (iterLoop k X x).2 ≃* π_ (j + 1) X x)
  | 0, i, j, h => by subst h; exact ⟨MulEquiv.refl _⟩
  | k + 1, i, j, h => by
    obtain ⟨e⟩ := iterLoop_piM X x k (i + 1) j (by omega)
    have e₁ := homotopyGroupPiLoopMulEquiv (X := (iterLoop k X x).1) (x := (iterLoop k X x).2) i
    exact ⟨e₁.trans e⟩

end Glue

/-- `B ⇒ A`: `B`'s first conjunct at the base points `I`. -/
theorem B_to_A : B → A := by
  rintro ⟨hB1, -, -, -⟩ i n n' hn hn'
  exact hB1 i n n' hn hn' (one' n) (one' n')

/-- The group-level periodicity `π_{i+1}O(m) ≃* π_{i+9}O(m')` in the stable range: `B`'s second
conjunct, which is NOT in `A` (the project states real periodicity only as a bijection of sets). -/
def G : Prop :=
  ∀ i m m' : ℕ, i + 3 ≤ m → i + 11 ≤ m' → ∀ (g : ↥(Orth (Fin m))) (g' : ↥(Orth (Fin m'))),
    Nonempty (π_ (i + 1) ↥(Orth (Fin m)) g ≃* π_ (i + 9) ↥(Orth (Fin m')) g')

open Morse.Homotopy in
/-- `A ⇒ B` up to the group structure: `A` gives `B`'s set-level conjuncts (1) (base points moved
by left translation) and (3) (`π_i Ω⁸O(m') ≃ π_{i+8}O(m')`, the project's loop-space lemma
applied eight times); `B`'s group-level conjuncts (2), (4) are exactly `G` (and its loop-space
form). So `G` is the only thing missing for `A ⇒ B`. -/
theorem A_to_B_of_groups : A → G → B := by
  intro hA hG
  have h1 : ∀ i m m' : ℕ, i + 2 ≤ m → i + 10 ≤ m' → ∀ (g : ↥(Orth (Fin m)))
      (g' : ↥(Orth (Fin m'))), Nonempty (π_ i ↥(Orth (Fin m)) g ≃ π_ (i + 8) ↥(Orth (Fin m')) g') := by
    intro i m m' hm hm' g g'
    obtain ⟨e⟩ := hA (i := i) (n := m) (n' := m') hm hm'
    exact ⟨(bc (m := m) g i).symm.trans (e.trans (bc (m := m') g' (i + 8)))⟩
  refine ⟨h1, hG, fun i m m' hm hm' g g' => ?_, fun i m m' hm hm' g g' => ?_⟩
  · obtain ⟨e⟩ := h1 i m m' hm hm' g g'
    obtain ⟨l⟩ := iterLoop_pi (TopCat.of ↥(Orth (Fin m'))) g' 8 i
    exact ⟨e.trans l.symm⟩
  · obtain ⟨e⟩ := hG i m m' hm hm' g g'
    obtain ⟨l⟩ := iterLoop_piM (TopCat.of ↥(Orth (Fin m'))) g' 8 i (i + 8) rfl
    exact ⟨e.trans l.symm⟩

/-! ### The group-level periodicity `G`, from the project's per-step lemmas (outside the item)

Every step of the project's chain is induced by a continuous map (`omegaPhi`, the inclusion of a
stratum, the stabilization `U(m) → U(m + k)`) whose induced map on `π_{j+1}` is bijective, or is
already a group isomorphism (`nonempty_mulEquiv_pathSp`, homeomorphisms); so it upgrades to a group
isomorphism by `MulEquiv.ofBijective (homotopyGroupHom …)`. This re-assembles the project's proof
of `theorem_24_7` in positive degrees, at the group level. -/

section Groups

open Morse Morse.Homotopy
open scoped Morse.MatrixInner

variable {ι : Type} [Fintype ι] [DecidableEq ι] {J : ℕ → Matrix ι ι ℝ} {k : ℕ}

/-- The stratum has the homotopy GROUPS of `Ω_k(n)` (it is open and closed). -/
theorem stratumM {p : Matrix ι ι ℝ} (hJ : IsAnticommFamily J k) {x : Matrix ι ι ℝ}
    (hx : x ∈ omegaStratum J k p) (j : ℕ) :
    Nonempty (π_ (j + 1) (omegaStratum J k p) ⟨x, hx⟩ ≃*
      π_ (j + 1) (Omega J k) ⟨x, omegaStratum_subset p hx⟩) := by
  obtain ⟨e₁⟩ := nonempty_mulEquiv_of_homeomorph (stratumInHomeomorph J k p).symm
    (x := ⟨x, hx⟩) (y := ⟨⟨x, omegaStratum_subset p hx⟩, hx⟩) rfl j
  have e₂ := MulEquiv.ofBijective (homotopyGroupHom (N := Fin (j + 1))
    (⟨Subtype.val, continuous_subtype_val⟩ : C(stratumIn J k p, Omega J k))
      ⟨⟨x, omegaStratum_subset p hx⟩, hx⟩)
    (bijective_homotopyGroupMap_clopen (N := Fin (j + 1)) (isClopen_stratumIn (p := p) hJ)
      (x := ⟨x, omegaStratum_subset p hx⟩) hx)
  exact ⟨e₁.trans e₂⟩

/-- Theorem 24.5 at a finite stage, `k ≢ 2 (mod 4)`, as GROUPS:
`π_{j+1}(Ω_{k+1}(n), J') ≅ π_{j+2}(Ω_k(n), J_k)`. -/
theorem linkM (hJ : IsAnticommFamily J (k + 1)) (hk8 : k + 1 ≤ 8) (hk3 : (k + 1) % 4 ≠ 3)
    {r₀ : ℕ} (hr₀ : r₀ = 1 ∨ (r₀ = 2 ∧ k = 0)) {j : ℕ}
    (hi : j + 1 + 2 ≤ r₀ * (Fintype.card ι / milnorM (k + 1) - 1)) (J' : Omega J (k + 1)) :
    Nonempty (π_ (j + 1) (Omega J (k + 1)) J' ≃* π_ (j + 2) (Omega J k) ⟨basePt J k, basePt_mem hJ⟩) := by
  have e₁ := MulEquiv.ofBijective (homotopyGroupHom (N := Fin (j + 1)) (omegaPhi hJ) J')
    (omegaPhi_bijective hJ hk8 hk3 hr₀ hi J')
  obtain ⟨e₂⟩ := nonempty_mulEquiv_pathSp
    (isSliceSubmanifold_omegaStratum (hJ.mono k.le_succ) (basePt J k))
    (self_mem_omegaStratum (basePt_mem hJ)) (neg_basePt_mem hJ) j (omegaPhi hJ J')
  obtain ⟨e₃⟩ := stratumM (hJ.mono k.le_succ) (self_mem_omegaStratum (basePt_mem hJ)) (j + 1)
  exact ⟨e₁.trans (e₂.trans e₃)⟩

/-- Theorem 24.5 at a finite stage, `k ≡ 2 (mod 4)`, as GROUPS. -/
theorem linkM_two (hJ : IsAnticommFamily J (k + 1)) (hk : k ≠ 0) (hk8 : k + 1 ≤ 8)
    (hk3 : k % 4 ≠ 3) (hii : IsCentralI J k (iWordM J k)) (c : ℤ) {j : ℕ}
    (hj : j + 3 ≤ (Fintype.card ι / milnorM (k + 1) - c.natAbs) / 4) (J' : Omega J (k + 1))
    (hJ' : (omegaPhi hJ J' : PathSp _ _ _) ∈
      omegaComp J k (iWordM J k) (Real.pi * milnorM (k + 1) * c / 2)) :
    Nonempty (π_ (j + 1) (Omega J (k + 1)) J' ≃* π_ (j + 2) (Omega J k) ⟨basePt J k, basePt_mem hJ⟩) := by
  have e₁ := MulEquiv.ofBijective (homotopyGroupHom (N := Fin (j + 1)) (omegaPhi hJ) J')
    (omegaPhi_bijective_two hJ hk hk8 hk3 hii c hj J' hJ')
  obtain ⟨e₂⟩ := nonempty_mulEquiv_pathSp
    (isSliceSubmanifold_omegaStratum (hJ.mono k.le_succ) (basePt J k))
    (self_mem_omegaStratum (basePt_mem hJ)) (neg_basePt_mem hJ) j (omegaPhi hJ J')
  obtain ⟨e₃⟩ := stratumM (hJ.mono k.le_succ) (self_mem_omegaStratum (basePt_mem hJ)) (j + 1)
  exact ⟨e₁.trans (e₂.trans e₃)⟩

/-- Bott's chain at `n = 16r` as GROUPS (the project's `bott_chain`, step by step with `linkM`,
`linkM_two`): `π_{j+1}(Ω_8(16r), J_8) ≅ π_{j+9}(O(16r), I)` for `2j + 12 ≤ r`. -/
theorem chainM (r j : ℕ) (hr : 2 * j + 12 ≤ r) :
    Nonempty (π_ (j + 1) (Omega (bottJ r) 8)
        ⟨basePt (bottJ r) 8, basePt_mem_omega (isAnticommFamily_bottJ r)⟩ ≃*
      π_ (j + 9) (Omega (bottJ r) 0) ⟨basePt (bottJ r) 0,
        basePt_mem (k := 0) ((isAnticommFamily_bottJ r).mono (by norm_num))⟩) := by
  have hJ := isAnticommFamily_bottJ r
  have hc := card_bottJ r
  have hd : ∀ m : ℕ, 0 < m → m ∣ 16 → Fintype.card (I16 × Fin r) / m = (16 / m) * r := by
    intro m hm hm16
    obtain ⟨q, hq⟩ := hm16
    rw [hc, hq, Nat.mul_div_cancel_left _ hm, mul_assoc, Nat.mul_div_cancel_left _ hm]
  have m8 : Fintype.card (I16 × Fin r) / milnorM (7 + 1) = r := by
    rw [show milnorM (7 + 1) = 16 from rfl, hd 16 (by norm_num) dvd_rfl]; simp
  have m7 : Fintype.card (I16 × Fin r) / milnorM (6 + 1) = 2 * r := by
    rw [show milnorM (6 + 1) = 8 from rfl, hd 8 (by norm_num) (by norm_num)]
  have m6 : Fintype.card (I16 × Fin r) / milnorM (5 + 1) = 2 * r := by
    rw [show milnorM (5 + 1) = 8 from rfl, hd 8 (by norm_num) (by norm_num)]
  have m5 : Fintype.card (I16 × Fin r) / milnorM (4 + 1) = 2 * r := by
    rw [show milnorM (4 + 1) = 8 from rfl, hd 8 (by norm_num) (by norm_num)]
  have m4 : Fintype.card (I16 × Fin r) / milnorM (3 + 1) = 2 * r := by
    rw [show milnorM (3 + 1) = 8 from rfl, hd 8 (by norm_num) (by norm_num)]
  have m3 : Fintype.card (I16 × Fin r) / milnorM (2 + 1) = 4 * r := by
    rw [show milnorM (2 + 1) = 4 from rfl, hd 4 (by norm_num) (by norm_num)]
  have m2 : Fintype.card (I16 × Fin r) / milnorM (1 + 1) = 4 * r := by
    rw [show milnorM (1 + 1) = 4 from rfl, hd 4 (by norm_num) (by norm_num)]
  have m1 : Fintype.card (I16 × Fin r) / milnorM (0 + 1) = 8 * r := by
    rw [show milnorM (0 + 1) = 2 from rfl, hd 2 (by norm_num) (by norm_num)]
  obtain ⟨e8⟩ := linkM (k := 7) hJ (by norm_num) (by norm_num) (r₀ := 1) (Or.inl rfl)
    (j := j) (by rw [m8]; omega) ⟨basePt (bottJ r) 8, basePt_mem_omega hJ⟩
  have hJ7 : IsAnticommFamily (bottJ r) (6 + 1) := hJ.mono (by norm_num)
  obtain ⟨e7⟩ := linkM_two (k := 6) hJ7 (by norm_num) (by norm_num) (by norm_num)
    (isCentralI_iWordM hJ7 (Or.inr rfl)) 0 (j := j + 1) (by rw [m7]; simp; omega)
    ⟨basePt (bottJ r) 7, basePt_mem_omega hJ7⟩
    (omegaPhi_bottJ_mem_omegaComp r (Or.inr rfl))
  obtain ⟨e6⟩ := linkM (k := 5) (hJ.mono (by norm_num)) (by norm_num) (by norm_num)
    (r₀ := 1) (Or.inl rfl) (j := j + 2) (by rw [m6]; omega)
    ⟨basePt (bottJ r) 6, basePt_mem_omega (hJ.mono (by norm_num))⟩
  obtain ⟨e5⟩ := linkM (k := 4) (hJ.mono (by norm_num)) (by norm_num) (by norm_num)
    (r₀ := 1) (Or.inl rfl) (j := j + 3) (by rw [m5]; omega)
    ⟨basePt (bottJ r) 5, basePt_mem_omega (hJ.mono (by norm_num))⟩
  obtain ⟨e4⟩ := linkM (k := 3) (hJ.mono (by norm_num)) (by norm_num) (by norm_num)
    (r₀ := 1) (Or.inl rfl) (j := j + 4) (by rw [m4]; omega)
    ⟨basePt (bottJ r) 4, basePt_mem_omega (hJ.mono (by norm_num))⟩
  have hJ3 : IsAnticommFamily (bottJ r) (2 + 1) := hJ.mono (by norm_num)
  obtain ⟨e3⟩ := linkM_two (k := 2) hJ3 (by norm_num) (by norm_num) (by norm_num)
    (isCentralI_iWordM hJ3 (Or.inl rfl)) 0 (j := j + 5) (by rw [m3]; simp; omega)
    ⟨basePt (bottJ r) 3, basePt_mem_omega hJ3⟩
    (omegaPhi_bottJ_mem_omegaComp r (Or.inl rfl))
  obtain ⟨e2⟩ := linkM (k := 1) (hJ.mono (by norm_num)) (by norm_num) (by norm_num)
    (r₀ := 1) (Or.inl rfl) (j := j + 6) (by rw [m2]; omega)
    ⟨basePt (bottJ r) 2, basePt_mem_omega (hJ.mono (by norm_num))⟩
  obtain ⟨e1⟩ := linkM (k := 0) (hJ.mono (by norm_num)) (by norm_num) (by norm_num)
    (r₀ := 2) (Or.inr ⟨rfl, rfl⟩) (j := j + 7) (by rw [m1]; omega)
    ⟨basePt (bottJ r) 1, basePt_mem_omega (hJ.mono (by norm_num))⟩
  exact ⟨e8.trans (e7.trans (e6.trans (e5.trans (e4.trans (e3.trans (e2.trans e1))))))⟩

/-- Stability of `O(m)` as groups (`O(m) = U(m)` over `ℝ`; the project's
`bijective_homotopyGroupMap_unitaryIncl` with `sphereConnected_real`). -/
theorem stab_leM {n a c : ℕ} (hi : n + 1 + 2 ≤ a) :
    Nonempty (π_ (n + 1) (unitaryGroup (Fin a) ℝ) 1 ≃* π_ (n + 1) (unitaryGroup (Fin (a + c)) ℝ) 1) := by
  have e₁ := MulEquiv.ofBijective (homotopyGroupHom (N := Fin (n + 1)) (unitaryInclC (𝕜 := ℝ) a c) 1)
    (bijective_homotopyGroupMap_unitaryIncl (k := c) sphereConnected_real (i := n + 1)
      (by omega) (1 : unitaryGroup (Fin a) ℝ))
  rw [show unitaryInclC (𝕜 := ℝ) a c 1 = 1 from map_one (unitaryIncl ℝ (Fin a) (Fin c))] at e₁
  obtain ⟨e₂⟩ := nonempty_mulEquiv_of_homeomorph (unitaryCongr (𝕜 := ℝ) (finSumFinEquiv (m := a) (n := c)))
    (unitaryCongr_one _) n
  exact ⟨e₁.trans e₂⟩

theorem stableM {n a b : ℕ} (ha : n + 1 + 2 ≤ a) (hb : n + 1 + 2 ≤ b) :
    Nonempty (π_ (n + 1) (unitaryGroup (Fin a) ℝ) 1 ≃* π_ (n + 1) (unitaryGroup (Fin b) ℝ) 1) := by
  rcases le_total a b with h | h
  · obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le h
    exact stab_leM ha
  · obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le h
    obtain ⟨e⟩ := stab_leM (c := c) hb
    exact ⟨e.symm⟩

end Groups

/-- **`G` holds**: Bott periodicity for `O` in the stable range as GROUP isomorphisms, assembled
from the project's per-step lemmas (none of them an item theorem). -/
theorem G_holds : G := by
  intro i m m' hm hm' g g'
  set r := 2 * i + 12
  obtain ⟨e₁⟩ := stableM (n := i) (a := m) (b := r) (by omega) (by omega)
  obtain ⟨e₂⟩ := Morse.Homotopy.nonempty_mulEquiv_of_homeomorph (Morse.omegaEightHomeomorph r)
    (Morse.omegaEightHomeomorph_basePt r) i
  obtain ⟨e₃⟩ := chainM r i le_rfl
  obtain ⟨e₄⟩ := Morse.Homotopy.nonempty_mulEquiv_of_homeomorph
    (Morse.Homotopy.unitaryCongr (𝕜 := ℝ) (Fintype.equivFinOfCardEq (Morse.card_bottJ r)))
    (Morse.Homotopy.unitaryCongr_one _) (i + 8)
  obtain ⟨e₅⟩ := stableM (n := i + 8) (a := 16 * r) (b := m') (by omega) (by omega)
  obtain ⟨b₁⟩ := bcM (m := m) g i
  obtain ⟨b₂⟩ := bcM (m := m') g' (i + 8)
  exact ⟨b₁.symm.trans (e₁.trans (e₂.symm.trans (e₃.trans (e₄.trans (e₅.trans b₂)))))⟩

/-- `A ⇒ B`: the set-level conjuncts from `A`, the group-level ones from `G_holds` (proved outright
from the project's per-step lemmas: `A` is a bijection of sets and cannot give them). -/
theorem A_to_B : A → B := fun hA => A_to_B_of_groups hA G_holds

#rt_check RoundTrip.V15_45.B_to_A [Morse.theorem_24_7]
#rt_check RoundTrip.V15_45.A_to_B_of_groups [Morse.theorem_24_7]
#rt_check RoundTrip.V15_45.A_to_B [Morse.theorem_24_7]
#rt_overlap RoundTrip.V15_45.B_to_A [Morse.theorem_24_7]
#rt_overlap RoundTrip.V15_45.A_to_B [Morse.theorem_24_7]

end RoundTrip.V15_45
