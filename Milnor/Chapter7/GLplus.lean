import Milnor.Chapter7.Cobordism

/-!
# Smooth paths in the positive general linear group

Every real matrix `A` with `det A > 0` is joined to the identity by a smooth path of matrices
of positive determinant (`exists_glPath`).  This is the ingredient of Milnor's Lemma 1 in §7
("the framed cobordism class does not depend on the positive basis"), and it replaces the
appeal to the connectedness of `GL⁺` in the book.

Route: Mathlib's normal form `A = L · diag d · L'` with `L, L'` products of transvections; a
transvection `1 + c Eᵢⱼ` is joined to `1` by `1 + t c Eᵢⱼ` (determinant `1`); the diagonal part
has an even number of negative entries, which are paired up and each pair flipped by a planar
rotation through angle `π` (determinant `1`, by the identity `det (1 + A B) = det (1 + B A)`),
while the absolute values are scaled to `1`.
-/

open Matrix Finset Function
open scoped ContDiff

noncomputable section

namespace Milnor

namespace GLp

variable {p : ℕ}

/-! ### Smooth matrix-valued functions -/

/-- Smoothness of the entries of a matrix-valued function of a real variable. -/
def SmoothEntries (A : ℝ → Matrix (Fin p) (Fin p) ℝ) : Prop :=
  ∀ a b, ContDiff ℝ ∞ (fun t => A t a b)

theorem SmoothEntries.mul {A B : ℝ → Matrix (Fin p) (Fin p) ℝ} (hA : SmoothEntries A)
    (hB : SmoothEntries B) : SmoothEntries (fun t => A t * B t) := by
  intro a b
  simp only [Matrix.mul_apply]
  exact ContDiff.sum fun k _ => (hA a k).mul (hB k b)

theorem SmoothEntries.const (M : Matrix (Fin p) (Fin p) ℝ) : SmoothEntries (fun _ => M) :=
  fun _ _ => contDiff_const

theorem SmoothEntries.listProd (L : List (ℝ → Matrix (Fin p) (Fin p) ℝ))
    (h : ∀ A ∈ L, SmoothEntries A) : SmoothEntries (fun t => (L.map (fun A => A t)).prod) := by
  induction L with
  | nil => simpa using SmoothEntries.const (1 : Matrix (Fin p) (Fin p) ℝ)
  | cons A L ih =>
    simp only [List.map_cons, List.prod_cons]
    exact (h A List.mem_cons_self).mul (ih fun B hB => h B (List.mem_cons_of_mem _ hB))

theorem SmoothEntries.diagonal {d : Fin p → ℝ → ℝ} (hd : ∀ i, ContDiff ℝ ∞ (d i)) :
    SmoothEntries (fun t => Matrix.diagonal (fun i => d i t)) := by
  intro a b
  by_cases h : a = b
  · subst h; simp only [diagonal_apply_eq]; exact hd a
  · simp only [diagonal_apply_ne _ h]; exact contDiff_const

theorem SmoothEntries.comp {A : ℝ → Matrix (Fin p) (Fin p) ℝ} (hA : SmoothEntries A) {ρ : ℝ → ℝ}
    (hρ : ContDiff ℝ ∞ ρ) : SmoothEntries (fun t => A (ρ t)) := fun a b => (hA a b).comp hρ

/-! ### Transvection paths -/

/-- The path `t ↦ 1 + t c Eᵢⱼ` from `1` to a transvection. -/
def transPath (T : TransvectionStruct (Fin p) ℝ) (t : ℝ) : Matrix (Fin p) (Fin p) ℝ :=
  transvection T.i T.j (t * T.c)

theorem transPath_zero (T : TransvectionStruct (Fin p) ℝ) : transPath T 0 = 1 := by
  simp [transPath]

theorem transPath_one (T : TransvectionStruct (Fin p) ℝ) : transPath T 1 = T.toMatrix := by
  simp [transPath, TransvectionStruct.toMatrix]

theorem det_transPath (T : TransvectionStruct (Fin p) ℝ) (t : ℝ) : det (transPath T t) = 1 :=
  det_transvection_of_ne _ _ T.hij _

theorem smooth_transPath (T : TransvectionStruct (Fin p) ℝ) : SmoothEntries (transPath T) := by
  intro a b
  simp only [transPath, transvection, Matrix.add_apply]
  by_cases h : T.i = a ∧ T.j = b
  · obtain ⟨rfl, rfl⟩ := h
    simp only [single_apply_same]
    exact contDiff_const.add (contDiff_id.mul contDiff_const)
  · simp only [single_apply_of_ne _ _ _ _ _ h]
    exact contDiff_const

/-- The product path of a list of transvections. -/
def listPath (L : List (TransvectionStruct (Fin p) ℝ)) (t : ℝ) : Matrix (Fin p) (Fin p) ℝ :=
  (L.map fun T => transPath T t).prod

theorem listPath_zero (L : List (TransvectionStruct (Fin p) ℝ)) : listPath L 0 = 1 := by
  simp [listPath, transPath_zero]

theorem listPath_one (L : List (TransvectionStruct (Fin p) ℝ)) :
    listPath L 1 = (L.map TransvectionStruct.toMatrix).prod := by
  simp [listPath, transPath_one]

theorem det_listPath (L : List (TransvectionStruct (Fin p) ℝ)) (t : ℝ) : det (listPath L t) = 1 := by
  induction L with
  | nil => simp [listPath]
  | cons T L ih =>
    simp only [listPath, List.map_cons, List.prod_cons, det_mul, det_transPath, one_mul]
    exact ih

theorem smooth_listPath (L : List (TransvectionStruct (Fin p) ℝ)) : SmoothEntries (listPath L) := by
  have := SmoothEntries.listProd (L.map transPath) (by
    intro A hA
    obtain ⟨T, -, rfl⟩ := List.mem_map.1 hA
    exact smooth_transPath T)
  have heq : (fun t => ((L.map transPath).map fun A => A t).prod) = listPath L := by
    funext t; simp [listPath, List.map_map, Function.comp_def]
  rwa [heq] at this

/-! ### Planar rotations -/

theorem ite_and_eq_mul (P Q : Prop) [Decidable P] [Decidable Q] :
    (if P ∧ Q then (1 : ℝ) else 0) = (if P then 1 else 0) * (if Q then 1 else 0) := by
  by_cases hP : P <;> by_cases hQ : Q <;> simp [hP, hQ]

/-- The rotation through angle `θ` in the `(i, j)`-plane. -/
def rot (i j : Fin p) (θ : ℝ) : Matrix (Fin p) (Fin p) ℝ :=
  1 + (Real.cos θ - 1) • (single i i (1 : ℝ) + single j j 1) +
    Real.sin θ • (single j i (1 : ℝ) - single i j 1)

theorem rot_apply (i j : Fin p) (θ : ℝ) (a b : Fin p) :
    rot i j θ a b = (if a = b then 1 else 0) +
      (Real.cos θ - 1) * ((if i = a ∧ i = b then 1 else 0) + (if j = a ∧ j = b then 1 else 0)) +
      Real.sin θ * ((if j = a ∧ i = b then 1 else 0) - (if i = a ∧ j = b then 1 else 0)) := by
  simp only [rot, Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, single, Matrix.of_apply,
    Matrix.one_apply, smul_eq_mul]
  all_goals (try (split_ifs <;> ring))

theorem rot_zero (i j : Fin p) : rot i j 0 = 1 := by
  ext a b; simp [rot_apply, Matrix.one_apply]

theorem rot_pi (i j : Fin p) (hij : i ≠ j) :
    rot i j Real.pi = Matrix.diagonal (fun a => if a = i ∨ a = j then (-1 : ℝ) else 1) := by
  ext a b
  rw [rot_apply, Real.cos_pi, Real.sin_pi, diagonal_apply]
  by_cases hab : a = b
  · subst hab
    by_cases hi : a = i
    · subst hi; simp [Ne.symm hij]
    · by_cases hj : a = j
      · subst hj; simp [hij, Ne.symm hi]
      · simp [hi, hj, Ne.symm hi, Ne.symm hj]
  · have h1 : ¬ (i = a ∧ i = b) := fun h => hab (h.1.symm.trans h.2)
    have h2 : ¬ (j = a ∧ j = b) := fun h => hab (h.1.symm.trans h.2)
    simp [hab, h1, h2]

theorem smooth_rot (i j : Fin p) : SmoothEntries (rot i j) := by
  intro a b
  simp only [rot_apply]
  refine (contDiff_const.add ((Real.contDiff_cos.sub contDiff_const).mul contDiff_const)).add
    (Real.contDiff_sin.mul contDiff_const)

/-- `det (rot i j θ) = 1` for `i ≠ j`. -/
theorem det_rot (i j : Fin p) (hij : i ≠ j) (θ : ℝ) : det (rot i j θ) = 1 := by
  -- `rot = 1 + A * (C * B)` with `A : p × 2`, `B : 2 × p`, `B * A = 1`
  set A : Matrix (Fin p) (Fin 2) ℝ := Matrix.of fun a r =>
    if r = 0 then (if i = a then 1 else 0) else (if j = a then 1 else 0) with hA
  set B : Matrix (Fin 2) (Fin p) ℝ := Aᵀ with hB
  set C : Matrix (Fin 2) (Fin 2) ℝ := !![Real.cos θ - 1, -Real.sin θ; Real.sin θ, Real.cos θ - 1]
    with hC
  have hrot : rot i j θ = 1 + A * (C * B) := by
    ext a b
    rw [rot_apply]
    simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_two, hA, hB, hC,
      Matrix.of_apply, Matrix.transpose_apply]
    simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      ↓reduceIte, one_ne_zero]
    simp only [ite_and_eq_mul]
    ring
  have hBA : B * A = 1 := by
    ext r s
    simp only [hB, hA, Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply]
    fin_cases r <;> fin_cases s <;>
      simp [hij, Ne.symm hij, Finset.sum_ite_eq, Finset.sum_ite_eq', ite_mul, mul_ite, Matrix.one_apply]
  rw [hrot, Matrix.det_one_add_mul_comm, Matrix.mul_assoc, hBA, Matrix.mul_one, Matrix.det_fin_two]
  simp [hC, Matrix.one_apply]
  linear_combination Real.cos_sq_add_sin_sq θ

/-! ### Pairing the negative entries -/

/-- A perfect matching of a finite set of even cardinality, as a list of pairs; every element
of the set lies in exactly one pair and elements outside the set lie in none. -/
theorem exists_matching (s : Finset (Fin p)) (hs : Even s.card) :
    ∃ P : List (Fin p × Fin p), (∀ q ∈ P, q.1 ≠ q.2) ∧
      ∀ a, (P.filter fun q => a = q.1 ∨ a = q.2).length = if a ∈ s then 1 else 0 := by
  induction' hn : s.card using Nat.strong_induction_on with n ih generalizing s
  rcases s.eq_empty_or_nonempty with rfl | ⟨x, hx⟩
  · exact ⟨[], by simp, fun a => by simp⟩
  · have hcard2 : 2 ≤ s.card := by
      obtain ⟨k, hk⟩ := hs
      rcases Nat.eq_zero_or_pos k with rfl | hk0
      · simp at hk; rw [hk] at hx; simp at hx
      · omega
    have hne : (s.erase x).Nonempty := by
      rw [← Finset.card_pos, Finset.card_erase_of_mem hx]; omega
    obtain ⟨y, hy⟩ := hne
    have hxy : x ≠ y := fun h => (Finset.mem_erase.1 hy).1 h.symm
    have hys : y ∈ s := (Finset.mem_erase.1 hy).2
    set s' := (s.erase x).erase y with hs'
    have hcard' : s'.card = s.card - 2 := by
      rw [hs', Finset.card_erase_of_mem hy, Finset.card_erase_of_mem hx]; omega
    have hs'even : Even s'.card := by
      rw [hcard']; obtain ⟨k, hk⟩ := hs; exact ⟨k - 1, by omega⟩
    obtain ⟨P', hP'1, hP'2⟩ := ih s'.card (by rw [hcard']; omega) s' hs'even rfl
    refine ⟨(x, y) :: P', ?_, ?_⟩
    · intro q hq
      rcases List.mem_cons.1 hq with rfl | hq
      · exact hxy
      · exact hP'1 q hq
    · intro a
      have hmem : a ∈ s' ↔ a ∈ s ∧ a ≠ x ∧ a ≠ y := by
        simp only [hs', Finset.mem_erase]; tauto
      by_cases ha : a = x ∨ a = y
      · have h1 : a ∉ s' := fun h => by
          rcases ha with rfl | rfl
          · exact (hmem.1 h).2.1 rfl
          · exact (hmem.1 h).2.2 rfl
        have h2 : a ∈ s := by rcases ha with rfl | rfl <;> assumption
        rw [List.filter_cons_of_pos (by simpa using ha), List.length_cons, hP'2 a, if_neg h1, if_pos h2]
      · have h3 : a ∈ s' ↔ a ∈ s := by
          rw [hmem]; push_neg at ha; tauto
        rw [List.filter_cons_of_neg (by simpa using ha), hP'2 a]
        simp only [h3]

/-- The product of the flips of a list of pairs is diagonal with entry `(-1)^(count)`. -/
theorem prod_rot_pi (P : List (Fin p × Fin p)) (hP : ∀ q ∈ P, q.1 ≠ q.2) :
    (P.map fun q => rot q.1 q.2 Real.pi).prod =
      Matrix.diagonal (fun a => (-1 : ℝ) ^ (P.filter fun q => a = q.1 ∨ a = q.2).length) := by
  induction P with
  | nil => ext a b; simp [Matrix.one_apply, diagonal_apply]
  | cons q P ih =>
    rw [List.map_cons, List.prod_cons, rot_pi q.1 q.2 (hP q List.mem_cons_self),
      ih (fun q' hq' => hP q' (List.mem_cons_of_mem _ hq')), diagonal_mul_diagonal]
    congr 1
    funext a
    by_cases h : a = q.1 ∨ a = q.2
    · rw [List.filter_cons_of_pos (by simpa using h), List.length_cons, if_pos h, pow_succ]; ring
    · rw [List.filter_cons_of_neg (by simpa using h), if_neg h, one_mul]

/-! ### The diagonal path -/

/-- The sign pattern of `d`. -/
def sgnv (d : Fin p → ℝ) (i : Fin p) : ℝ := if d i < 0 then -1 else 1

theorem even_card_neg {d : Fin p → ℝ} (hd : ∀ i, d i ≠ 0) (hpos : 0 < ∏ i, d i) :
    Even (Finset.univ.filter fun i => d i < 0).card := by
  have h1 : ∀ i, d i = sgnv d i * |d i| := by
    intro i; unfold sgnv
    split_ifs with h
    · rw [abs_of_neg h]; ring
    · push_neg at h; rw [abs_of_nonneg h]; ring
  have h2 : ∏ i, d i = (∏ i, sgnv d i) * ∏ i, |d i| := by
    rw [← Finset.prod_mul_distrib]; exact Finset.prod_congr rfl fun i _ => h1 i
  have h3 : ∏ i, sgnv d i = (-1 : ℝ) ^ (Finset.univ.filter fun i => d i < 0).card := by
    unfold sgnv
    rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const]
  have h4 : 0 < ∏ i, |d i| := Finset.prod_pos fun i _ => abs_pos.2 (hd i)
  rw [h2, h3] at hpos
  have h5 : (0 : ℝ) < (-1) ^ (Finset.univ.filter fun i => d i < 0).card := by
    by_contra h
    push_neg at h
    nlinarith
  rcases neg_one_pow_eq_or ℝ (Finset.univ.filter fun i => d i < 0).card with h6 | h6
  · exact (neg_one_pow_eq_one_iff_even (by norm_num : (-1 : ℝ) ≠ 1)).1 h6
  · rw [h6] at h5; norm_num at h5

/-- The converse: a nonvanishing tuple with an even number of negative entries has positive
product. -/
theorem prod_pos_of_even {d : Fin p → ℝ} (hd : ∀ i, d i ≠ 0)
    (hev : Even (Finset.univ.filter fun i => d i < 0).card) : 0 < ∏ i, d i := by
  have h1 : ∀ i, d i = sgnv d i * |d i| := by
    intro i; unfold sgnv
    split_ifs with h
    · rw [abs_of_neg h]; ring
    · push_neg at h; rw [abs_of_nonneg h]; ring
  have h2 : ∏ i, d i = (∏ i, sgnv d i) * ∏ i, |d i| := by
    rw [← Finset.prod_mul_distrib]; exact Finset.prod_congr rfl fun i _ => h1 i
  have h3 : ∏ i, sgnv d i = (-1 : ℝ) ^ (Finset.univ.filter fun i => d i < 0).card := by
    unfold sgnv
    rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const]
  have h4 : 0 < ∏ i, |d i| := Finset.prod_pos fun i _ => abs_pos.2 (hd i)
  rw [h2, h3, hev.neg_one_pow, one_mul]
  exact h4

/-- The scaled diagonal `e i t = (1 - t) d i + t sgn (d i)`. -/
def diagScale (d : Fin p → ℝ) (t : ℝ) (i : Fin p) : ℝ := (1 - t) * d i + t * sgnv d i

theorem diagScale_zero (d : Fin p → ℝ) : diagScale d 0 = d := by
  funext i; simp [diagScale]

theorem diagScale_one (d : Fin p → ℝ) : diagScale d 1 = sgnv d := by
  funext i; simp [diagScale]

theorem diagScale_neg_of_neg {d : Fin p → ℝ} {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) {i : Fin p}
    (h : d i < 0) : diagScale d t i < 0 := by
  unfold diagScale sgnv
  rw [if_pos h]
  have h1 : (1 - t) * d i ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by linarith) h.le
  rcases eq_or_lt_of_le ht0 with rfl | ht0'
  · simpa using h
  · linarith

theorem diagScale_pos_of_pos {d : Fin p → ℝ} {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) {i : Fin p}
    (h : 0 < d i) : 0 < diagScale d t i := by
  unfold diagScale sgnv
  rw [if_neg (not_lt.2 h.le)]
  have h1 : 0 ≤ (1 - t) * d i := mul_nonneg (by linarith) h.le
  rcases eq_or_lt_of_le ht0 with rfl | ht0'
  · simpa using h
  · linarith

theorem diagScale_neg_iff {d : Fin p → ℝ} (hd : ∀ i, d i ≠ 0) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (i : Fin p) : diagScale d t i < 0 ↔ d i < 0 := by
  rcases lt_or_gt_of_ne (hd i) with h | h
  · exact ⟨fun _ => h, fun _ => diagScale_neg_of_neg ht0 ht1 h⟩
  · exact ⟨fun h' => absurd (diagScale_pos_of_pos ht0 ht1 h) (not_lt.2 h'.le), fun h' => absurd h (not_lt.2 h'.le)⟩

theorem diagScale_ne_zero {d : Fin p → ℝ} (hd : ∀ i, d i ≠ 0) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (i : Fin p) : diagScale d t i ≠ 0 := by
  rcases lt_or_gt_of_ne (hd i) with h | h
  · exact (diagScale_neg_of_neg ht0 ht1 h).ne
  · exact (diagScale_pos_of_pos ht0 ht1 h).ne'

theorem prod_diagScale_pos {d : Fin p → ℝ} (hd : ∀ i, d i ≠ 0) (hpos : 0 < ∏ i, d i) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : 0 < ∏ i, diagScale d t i := by
  apply prod_pos_of_even (diagScale_ne_zero hd ht0 ht1)
  have : (Finset.univ.filter fun i => diagScale d t i < 0) = Finset.univ.filter fun i => d i < 0 := by
    ext i; simp [diagScale_neg_iff hd ht0 ht1]
  rw [this]
  exact even_card_neg hd hpos

theorem smooth_diagScale (d : Fin p → ℝ) (i : Fin p) : ContDiff ℝ ∞ (fun t => diagScale d t i) := by
  unfold diagScale
  exact ((contDiff_const.sub contDiff_id).mul contDiff_const).add (contDiff_id.mul contDiff_const)

/-- The diagonal path: simultaneous flips of the paired negative entries and scaling. -/
def diagPath (d : Fin p → ℝ) (P : List (Fin p × Fin p)) (t : ℝ) : Matrix (Fin p) (Fin p) ℝ :=
  (P.map fun q => rot q.1 q.2 (Real.pi * t)).prod * Matrix.diagonal (diagScale d t)

theorem diagPath_zero (d : Fin p → ℝ) (P : List (Fin p × Fin p)) :
    diagPath d P 0 = Matrix.diagonal d := by
  simp [diagPath, rot_zero, diagScale_zero]

theorem det_diagPath (d : Fin p → ℝ) {P : List (Fin p × Fin p)} (hP : ∀ q ∈ P, q.1 ≠ q.2) (t : ℝ) :
    det (diagPath d P t) = ∏ i, diagScale d t i := by
  unfold diagPath
  rw [det_mul, det_diagonal]
  have : det (P.map fun q => rot q.1 q.2 (Real.pi * t)).prod = 1 := by
    induction P with
    | nil => simp
    | cons q P ih =>
      rw [List.map_cons, List.prod_cons, det_mul, det_rot _ _ (hP q List.mem_cons_self),
        ih (fun q' hq' => hP q' (List.mem_cons_of_mem _ hq')), one_mul]
  rw [this, one_mul]

theorem diagPath_one {d : Fin p → ℝ} {P : List (Fin p × Fin p)} (hP : ∀ q ∈ P, q.1 ≠ q.2)
    (hP2 : ∀ a, (P.filter fun q => a = q.1 ∨ a = q.2).length =
      if a ∈ Finset.univ.filter (fun i => d i < 0) then 1 else 0) :
    diagPath d P 1 = 1 := by
  unfold diagPath
  rw [mul_one, prod_rot_pi P hP, diagScale_one, diagonal_mul_diagonal]
  rw [← Matrix.diagonal_one]
  congr 1
  funext a
  rw [hP2 a]
  unfold sgnv
  by_cases h : d a < 0
  · simp [h]
  · simp [h]

theorem smooth_diagPath (d : Fin p → ℝ) (P : List (Fin p × Fin p)) : SmoothEntries (diagPath d P) := by
  unfold diagPath
  refine SmoothEntries.mul ?_ (SmoothEntries.diagonal fun i => smooth_diagScale d i)
  have := SmoothEntries.listProd (P.map fun q => fun t => rot q.1 q.2 (Real.pi * t)) (by
    intro A hA
    obtain ⟨q, -, rfl⟩ := List.mem_map.1 hA
    exact (smooth_rot q.1 q.2).comp (contDiff_const.mul contDiff_id))
  have heq : (fun t => ((P.map fun q => fun t => rot q.1 q.2 (Real.pi * t)).map fun A => A t).prod) =
      fun t => (P.map fun q => rot q.1 q.2 (Real.pi * t)).prod := by
    funext t; simp [List.map_map, Function.comp_def]
  rwa [heq] at this

/-! ### The path from `A` to `1` -/

/-- **Smooth paths in `GL⁺`.**  A matrix of positive determinant is joined to the identity by a
smooth path of matrices of positive determinant (for `t ∈ [0,1]`). -/
theorem exists_glPath (A : Matrix (Fin p) (Fin p) ℝ) (hA : 0 < det A) :
    ∃ G : ℝ → Matrix (Fin p) (Fin p) ℝ, SmoothEntries G ∧ G 0 = A ∧ G 1 = 1 ∧
      ∀ t, 0 ≤ t → t ≤ 1 → 0 < det (G t) := by
  obtain ⟨L, L', D, hLDL⟩ := Matrix.Pivot.exists_list_transvec_mul_diagonal_mul_list_transvec A
  have hdet : det (Matrix.diagonal D) = det A := by
    rw [hLDL, det_mul, det_mul, TransvectionStruct.det_toMatrix_prod,
      TransvectionStruct.det_toMatrix_prod]; ring
  have hDpos : 0 < ∏ i, D i := by rw [← det_diagonal, hdet]; exact hA
  have hD : ∀ i, D i ≠ 0 := fun i h => by
    have := hDpos
    rw [Finset.prod_eq_zero (Finset.mem_univ i) h] at this
    exact lt_irrefl _ this
  obtain ⟨P, hP1, hP2⟩ := exists_matching _ (even_card_neg hD hDpos)
  refine ⟨fun t => listPath L (1 - t) * diagPath D P t * listPath L' (1 - t), ?_, ?_, ?_, ?_⟩
  · exact (((smooth_listPath L).comp (contDiff_const.sub contDiff_id)).mul (smooth_diagPath D P)).mul
      ((smooth_listPath L').comp (contDiff_const.sub contDiff_id))
  · simp only [sub_zero, listPath_one, diagPath_zero]; exact hLDL.symm
  · simp only [sub_self, listPath_zero, diagPath_one hP1 hP2, one_mul]
  · intro t ht0 ht1
    rw [det_mul, det_mul, det_listPath, det_listPath, det_diagPath D hP1, one_mul, mul_one]
    exact prod_diagScale_pos hD hDpos ht0 ht1

end GLp

end Milnor
