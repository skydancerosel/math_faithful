import Morse
import RoundTrip.Check
import RoundTrip.Blind.V15_32

open Matrix
open scoped Topology

namespace RoundTrip.V15_32

/-- The project's statement (universe instantiated at `0`, an arbitrary finite index type `ι`,
`J : ℕ → M_ι(ℝ)` with `J_1` a complex structure): for `i + 4 ≤ card ι` and every
`J' ∈ Ω_1 = Morse.Omega J 1` (all complex structures), Milnor's `φ_r = Morse.omegaPhi`,
`J' ↦ (t ↦ cos(πt)I + sin(πt)J')`, into the project's path space
`Morse.PathSp (Morse.omegaStratum J 0 I) I (−I)` (Milnor's metric `d` as a pseudo-emetric,
paths not normalized off `[0,1]`) is bijective on `π_i` (pointed sets), and
`π_i(Ω_1, J') ≃ π_{i+1}(O(ι), I)` as SETS (an `Equiv`, not a group isomorphism). -/
def A : Prop := type_of% @Morse.theorem_24_3.{0}

theorem A_holds : A := @Morse.theorem_24_3.{0}

/-- B's fourth conjunct (the set-level "hence `π_iΩ_1(n) ≅ π_{i+1}O(n)`", at every base point
`X ∈ O(n)`). -/
def B4 : Prop :=
  ∀ (n : ℕ) (J : ↥(CS (Fin n))) (i : ℕ), i + 4 ≤ n → ∀ X : ↥(Orth (Fin n)),
    Nonempty (π_ i ↥(CS (Fin n)) J ≃ π_ (i + 1) ↥(Orth (Fin n)) X)

theorem B_to_B4 : B → B4 := fun hB n J i hi X => by
  obtain ⟨j, -, h⟩ := hB n
  exact (h J).2.2.1 i hi X

/-- Left translation by `X` is a homeomorphism of `O(n)` (as a subspace of `M_n(ℝ)`). -/
def leftMul {n : ℕ} (X : ↥(Orth (Fin n))) : ↥(Orth (Fin n)) ≃ₜ ↥(Orth (Fin n)) where
  toFun Y := ⟨X.1 * Y.1, (orthogonalGroup (Fin n) ℝ).mul_mem X.2 Y.2⟩
  invFun Y := ⟨star X.1 * Y.1, (orthogonalGroup (Fin n) ℝ).mul_mem
    (Unitary.star_mem X.2) Y.2⟩
  left_inv Y := Subtype.ext (by
    simp only
    rw [← Matrix.mul_assoc, Unitary.star_mul_self_of_mem X.2, Matrix.one_mul])
  right_inv Y := Subtype.ext (by
    simp only
    rw [← Matrix.mul_assoc, Unitary.mul_star_self_of_mem X.2, Matrix.one_mul])
  continuous_toFun := (continuous_const.mul continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_const.mul continuous_subtype_val).subtype_mk _

/-- **A ⇒ B's fourth conjunct** (partial bridge): A's `π_iΩ_1 ≃ π_{i+1}O(n)` at the base point
`I` (with `J_1 := J`), transported by left translation to every base point `X`. -/
theorem A_to_B4 : A → B4 := by
  intro hA n J i hi X
  set Js : ℕ → Mat (Fin n) := fun _ => J.1
  have hJ : Morse.IsAnticommFamily Js 1 :=
    ⟨fun α _ _ => J.2, fun α β h1 h2 h3 h4 hne => absurd (by omega : α = β) hne⟩
  have hset : CS (Fin n) = Morse.Omega Js 1 := by
    ext K
    simp only [CS, Morse.Omega, Set.mem_ofPred_eq, IsCplxStr, Morse.IsComplexStructure]
    exact ⟨fun h => ⟨h, fun α h1 h2 => absurd h2 (by omega)⟩, fun h => h.1⟩
  have hn : i + 4 ≤ Fintype.card (Fin n) := by rw [Fintype.card_fin]; exact hi
  obtain ⟨-, ⟨e⟩⟩ := hA (J := Js) hJ hn ⟨J.1, hset ▸ J.2⟩
  have e₁ := Morse.Homotopy.piEquivOfHomeomorph (Homeomorph.setCongr hset)
    (x := J) (y := ⟨J.1, hset ▸ J.2⟩) rfl i
  have e₂ := Morse.Homotopy.piEquivOfHomeomorph (leftMul X)
    (x := ⟨1, (orthogonalGroup (Fin n) ℝ).one_mem⟩) (y := X)
    (Subtype.ext (by simp [leftMul])) (i + 1)
  exact ⟨e₁.trans (e.trans e₂)⟩

/-- B's fifth conjunct (the group-level "hence", at every base point `X ∈ O(n)`). -/
def B5 : Prop :=
  ∀ (n : ℕ) (J : ↥(CS (Fin n))) (i : ℕ), i + 1 + 4 ≤ n → ∀ X : ↥(Orth (Fin n)),
    Nonempty (π_ (i + 1) ↥(CS (Fin n)) J ≃* π_ (i + 2) ↥(Orth (Fin n)) X)

theorem B_to_B5 : B → B5 := fun hB n J i hi X => by
  obtain ⟨j, -, h⟩ := hB n
  exact (h J).2.2.2 i hi X

open scoped Morse.MatrixInner in
/-- **A ⇒ B's fifth conjunct** (partial bridge): A's bijectivity of `φ_*` on `π_{i+1}` makes it a
group isomorphism (`homotopyGroupHom`, a project lemma outside A), and the project's group version
of the loop-space isomorphism `π_{i+1}(Ω(N; p, q)) ≃* π_{i+2}(N, p)` (`nonempty_mulEquiv_pathSp`,
Theorem 17.1 + loop space, outside A) gives `π_{i+1}Ω_1(n) ≃* π_{i+2}O(n)`; then translate the
base point. So the group-level "hence" of B follows from A's first conjunct with the project's
other lemmas, without the blind path space. -/
theorem A_to_B5 : A → B5 := by
  intro hA n J i hi X
  set Js : ℕ → Mat (Fin n) := fun _ => J.1
  have hJ : Morse.IsAnticommFamily Js (0 + 1) :=
    ⟨fun α _ _ => J.2, fun α β h1 h2 h3 h4 hne => absurd (by omega : α = β) hne⟩
  have hset : CS (Fin n) = Morse.Omega Js 1 := by
    ext K
    simp only [CS, Morse.Omega, Set.mem_ofPred_eq, IsCplxStr, Morse.IsComplexStructure]
    exact ⟨fun h => ⟨h, fun α h1 h2 => absurd h2 (by omega)⟩, fun h => h.1⟩
  have hn : i + 1 + 4 ≤ Fintype.card (Fin n) := by rw [Fintype.card_fin]; exact hi
  set J' : ↥(Morse.Omega Js 1) := ⟨J.1, hset ▸ J.2⟩
  obtain ⟨hbij, -⟩ := hA (J := Js) hJ hn J'
  have f := MulEquiv.ofBijective
    (Morse.Homotopy.homotopyGroupHom (N := Fin (i + 1)) (Morse.omegaPhi (k := 0) hJ) J') hbij
  have hp := Morse.self_mem_omegaStratum (Morse.basePt_mem (k := 0) hJ)
  obtain ⟨g⟩ := Morse.nonempty_mulEquiv_pathSp
    (Morse.isSliceSubmanifold_omegaStratum (hJ.mono (Nat.le_succ 0)) (Morse.basePt Js 0)) hp
    (Morse.neg_basePt_mem hJ) i (Morse.omegaPhi (k := 0) hJ J')
  have hb : Morse.basePt Js 0 = 1 := by simp [Morse.basePt]
  have hstr : Morse.omegaStratum Js 0 (Morse.basePt Js 0) = Orth (Fin n) := by
    rw [Morse.omegaStratum_zero]; rfl
  obtain ⟨e₀⟩ := Morse.Homotopy.nonempty_mulEquiv_of_homeomorph (Homeomorph.setCongr hset)
    (x := J) (y := J') rfl i
  obtain ⟨e₁⟩ := Morse.Homotopy.nonempty_mulEquiv_of_homeomorph (Homeomorph.setCongr hstr)
    (x := ⟨Morse.basePt Js 0, hp⟩) (y := ⟨1, (orthogonalGroup (Fin n) ℝ).one_mem⟩)
    (Subtype.ext hb) (i + 1)
  obtain ⟨e₂⟩ := Morse.Homotopy.nonempty_mulEquiv_of_homeomorph (leftMul X)
    (x := ⟨1, (orthogonalGroup (Fin n) ℝ).one_mem⟩) (y := X)
    (Subtype.ext (by simp [leftMul])) (i + 1)
  exact ⟨e₀.trans (f.trans (g.trans (e₁.trans e₂)))⟩

/-! ### B ⇒ A's second conjunct (partial bridge) -/

/-- A's second conjunct: `π_i(Ω_1, J') ≃ π_{i+1}(O(ι), I)` (sets), for any finite `ι`. -/
def A2 : Prop :=
  ∀ {ι : Type} [Fintype ι] [DecidableEq ι] {J : ℕ → Matrix ι ι ℝ}, Morse.IsAnticommFamily J 1 →
    ∀ {i : ℕ}, i + 4 ≤ Fintype.card ι → ∀ J' : ↥(Morse.Omega J 1),
      Nonempty (π_ i ↥(Morse.Omega J 1) J' ≃
        π_ (i + 1) ↥(orthogonalGroup ι ℝ : Set (Matrix ι ι ℝ)) ⟨1, (orthogonalGroup ι ℝ).one_mem⟩)

theorem A_to_A2 : A → A2 := fun hA _ _ _ _ hJ _ hi J' => (hA hJ hi J').2

section Reindex
set_option linter.unusedSectionVars false
variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- `M ↦ (e × e)`-reindexed `M`, a homeomorphism `M_ι(ℝ) ≃ M_κ(ℝ)`. -/
def rH (e : ι ≃ κ) : Matrix ι ι ℝ ≃ₜ Matrix κ κ ℝ where
  toEquiv := Matrix.reindex e e
  continuous_toFun := by
    change Continuous fun M : Matrix ι ι ℝ => Matrix.reindex e e M
    simp only [Matrix.reindex_apply]
    exact continuous_id.matrix_submatrix _ _
  continuous_invFun := by
    change Continuous fun M : Matrix κ κ ℝ => (Matrix.reindex e e).symm M
    simp only [Matrix.reindex_symm, Matrix.reindex_apply]
    exact continuous_id.matrix_submatrix _ _

theorem rH_apply (e : ι ≃ κ) (M : Matrix ι ι ℝ) : rH e M = Matrix.reindex e e M := rfl

theorem r_mul (e : ι ≃ κ) (X Y : Matrix ι ι ℝ) :
    reindex e e (X * Y) = reindex e e X * reindex e e Y := by
  simpa only [coe_reindexAlgEquiv] using map_mul (reindexAlgEquiv ℝ ℝ e) X Y

theorem r_neg (e : ι ≃ κ) (X : Matrix ι ι ℝ) : reindex e e (-X) = -reindex e e X := by ext; simp

theorem r_one (e : ι ≃ κ) : reindex e e (1 : Matrix ι ι ℝ) = 1 := by ext i j; simp [one_apply]

theorem r_eq_iff (e : ι ≃ κ) (X Y : Matrix ι ι ℝ) : reindex e e X = reindex e e Y ↔ X = Y :=
  ⟨fun h => (reindex e e).injective h, congrArg _⟩

theorem r_orth_iff (e : ι ≃ κ) (X : Matrix ι ι ℝ) :
    reindex e e X ∈ orthogonalGroup κ ℝ ↔ X ∈ orthogonalGroup ι ℝ := by
  rw [mem_orthogonalGroup_iff', mem_orthogonalGroup_iff']
  rw [transpose_reindex, ← r_mul, ← r_one e, r_eq_iff]

theorem r_cs_iff (e : ι ≃ κ) (X : Matrix ι ι ℝ) :
    IsCplxStr (reindex e e X) ↔ Morse.IsComplexStructure X := by
  change (_ ∧ _) ↔ (_ ∧ _)
  rw [r_orth_iff, ← r_mul, ← r_one e, ← r_neg, r_eq_iff]

end Reindex

/-- **B ⇒ A's second conjunct** (partial bridge): B's set-level "hence" at `X = I`, transported
from `Fin (card ι)` to `ι` by reindexing. -/
theorem B4_to_A2 : B4 → A2 := by
  intro hB4 ι _ _ J hJ i hi J'
  set e := Fintype.equivFin ι
  have h1 : ∀ X : Matrix ι ι ℝ, X ∈ Morse.Omega J 1 ↔ rH e X ∈ CS (Fin (Fintype.card ι)) := by
    intro X
    change (Morse.IsComplexStructure X ∧ _) ↔ IsCplxStr (reindex e e X)
    rw [r_cs_iff]
    exact ⟨fun h => h.1, fun h => ⟨h, fun α h1 h2 => absurd (h1.trans h2) (by norm_num)⟩⟩
  have h2 : ∀ X : Matrix ι ι ℝ, X ∈ (orthogonalGroup ι ℝ : Set (Matrix ι ι ℝ)) ↔
      rH e X ∈ Orth (Fin (Fintype.card ι)) := fun X => (r_orth_iff e X).symm
  set H1 := (rH e).subtype h1
  set H2 := (rH e).subtype h2
  obtain ⟨E⟩ := hB4 (Fintype.card ι) (H1 J') i hi
    ⟨1, (orthogonalGroup (Fin (Fintype.card ι)) ℝ).one_mem⟩
  have e₁ := Morse.Homotopy.piEquivOfHomeomorph H1 (x := J') rfl i
  have e₂ := Morse.Homotopy.piEquivOfHomeomorph H2
    (x := ⟨1, (orthogonalGroup ι ℝ).one_mem⟩)
    (y := ⟨1, (orthogonalGroup (Fin (Fintype.card ι)) ℝ).one_mem⟩)
    (Subtype.ext (by simp [H2, rH_apply])) (i + 1)
  exact ⟨e₁.trans (E.trans e₂.symm)⟩

theorem B_to_A2 : B → A2 := fun hB => B4_to_A2 (B_to_B4 hB)

#rt_check RoundTrip.V15_32.A_to_B4 [Morse.theorem_24_3]
#rt_check RoundTrip.V15_32.B_to_A2 [Morse.theorem_24_3]
#rt_overlap RoundTrip.V15_32.B_to_A2 [Morse.theorem_24_3]

/-! ### What is left (neither full direction is proved; see `Items/V15_32.json`)

B's first two conjuncts (`j_* : π_i(Ω_1(n)) → π_i(Ω(O(n); I, −I))` bijective, a group isomorphism
for `i ≥ 1`) and A's first conjunct (`φ_*` bijective) are the same statement about two different
formalizations of Milnor's path space: the project's `PathSp (omegaStratum J 0 I) I (−I)`
(`IsPiecewiseSmooth`, `riemDist`, Milnor's `d` as a pseudo-emetric, paths not normalized off
`[0, 1]`) and the blind `OmIn (Orth (Fin n)) 1 (−1)` (`IsPWOn`, `rhoIn`, the topology generated by
the `dOmIn`-balls, paths normalized). `φ_r(J') = cos(πt)I + sin(πt)J' = exp(πtJ')` on `[0, 1]`, so
`j = normalize ∘ φ_r`; transferring bijectivity needs the homotopy equivalence
`PathSp ≃ OmIn` (`IsPWOn ↔ IsPiecewiseSmooth`, `rhoIn = riemDist`, entrywise- vs Frobenius-norm
derivatives, ball topology = emetric topology, the normalization homotopy) and, for B ⇒ A, its
compatibility with reindexing `ι ≃ Fin (card ι)`. This glue is believed true and was not built.
The group structure is not an obstacle: `homotopyGroupMap_mul` (project) makes a bijective `j_*`
a group isomorphism. The "hence" parts are proved above: A ⇒ B4, A ⇒ B5, B ⇒ A2. -/
#rt_check RoundTrip.V15_32.A_to_B5 [Morse.theorem_24_3]

end RoundTrip.V15_32
