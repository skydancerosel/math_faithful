import Morse
import RoundTrip.Check
import RoundTrip.Blind.V14_26

open Matrix Topology

namespace RoundTrip.V14_26

/-- The project's statement (universes instantiated at `0`). The listed definitions
`grassmannianEquiv`, `grassmannianEquiv_complex`, `grassmannianPiEquiv`, `minVelPiEquiv` (equivalences
of homotopy groups) are read as the `Nonempty` of their types; the two theorems are taken as they
are:
(1) for every `RCLike 𝕜` with `SphereConnected 𝕜 d`: `π_{j+1}(G_m(𝕜^{m'+m}), P₀) ≃ π_j(U(m), 1)` for
`j + 2 ≤ dm' + d − 1`;
(2) for `ℂ`, `m' = m`: `π_{j+1}(G_m(ℂ^{2m}), P₀) ≃ π_j(U(m), 1)` for `j + 1 ≤ 2m`;
(3) the same as groups for `j + 2 ≤ 2m`;
(4) for `Morse.grassmannian ι m` (`|ι| = 2m`) at every point `P`: `π_{j+1} ≃ π_j(U(m), 1)`;
(5) the same as groups;
(6) the same for the space `Morse.minVel ι` of velocities of minimal geodesics in `SU(2m)`. -/
def A : Prop :=
  (∀ {𝕜 : Type} [RCLike 𝕜] {m m' d : ℕ} (_hS : Morse.Homotopy.SphereConnected 𝕜 d) {j : ℕ}
      (_hj : j + 2 ≤ d * m' + d - 1),
      Nonempty (π_ (j + 1) ↥(Morse.Homotopy.Grassmannian 𝕜 (Fin m' ⊕ Fin m) m)
          (Morse.Homotopy.grassBase 𝕜 (Fin m') m) ≃
        π_ j ↥(Matrix.unitaryGroup (Fin m) 𝕜) 1)) ∧
  (∀ {m j : ℕ} (_hj : j + 1 ≤ 2 * m),
      Nonempty (π_ (j + 1) ↥(Morse.Homotopy.Grassmannian ℂ (Fin m ⊕ Fin m) m)
          (Morse.Homotopy.grassBase ℂ (Fin m) m) ≃
        π_ j ↥(Matrix.unitaryGroup (Fin m) ℂ) 1)) ∧
  type_of% @Morse.Homotopy.nonempty_mulEquiv_grassmannian_complex ∧
  (∀ {ι : Type} [Fintype ι] [DecidableEq ι] {m : ℕ} (_hcard : Fintype.card ι = 2 * m)
      (P : ↥(Morse.grassmannian ι m)) {j : ℕ} (_hj : j + 1 ≤ 2 * m),
      Nonempty (π_ (j + 1) ↥(Morse.grassmannian ι m) P ≃ π_ j ↥(Matrix.unitaryGroup (Fin m) ℂ) 1)) ∧
  type_of% @Morse.Homotopy.nonempty_mulEquiv_grassmannianPi.{0} ∧
  (∀ {ι : Type} [Fintype ι] [DecidableEq ι] {m : ℕ} (_hcard : Fintype.card ι = 2 * m)
      (A : ↥(Morse.minVel ι)) {j : ℕ} (_hj : j + 1 ≤ 2 * m),
      Nonempty (π_ (j + 1) ↥(Morse.minVel ι) A ≃ π_ j ↥(Matrix.unitaryGroup (Fin m) ℂ) 1))

theorem A_holds : A :=
  ⟨fun hS _ hj => ⟨Morse.Homotopy.grassmannianEquiv hS hj⟩,
    fun hj => ⟨Morse.Homotopy.grassmannianEquiv_complex hj⟩,
    @Morse.Homotopy.nonempty_mulEquiv_grassmannian_complex,
    fun hcard P _ hj => ⟨Morse.Homotopy.grassmannianPiEquiv hcard P hj⟩,
    @Morse.Homotopy.nonempty_mulEquiv_grassmannianPi.{0},
    fun hcard A _ hj => ⟨Morse.Homotopy.minVelPiEquiv hcard A hj⟩⟩

section Glue

/-- For an idempotent matrix, `rank = trace`. -/
theorem rank_eq_trace {k : ℕ} {P : Mat k} (hP : P * P = P) : ((P.rank : ℕ) : ℂ) = P.trace := by
  have he : IsIdempotentElem (Matrix.toLin' P) := by
    change Matrix.toLin' P * Matrix.toLin' P = Matrix.toLin' P
    rw [Module.End.mul_eq_comp, ← Matrix.toLin'_mul, hP]
  have h := (LinearMap.IsIdempotentElem.isProj_range _ he).trace
  rw [Matrix.trace_toLin'_eq] at h
  rw [h, Matrix.rank, Matrix.toLin'_apply']

/-- The blind Grassmannian (rank `m`) is the project's (trace `m`). -/
theorem grass_eq (k m : ℕ) : Grass k m = Morse.grassmannian (Fin k) m := by
  ext P
  simp only [Grass, Morse.grassmannian, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, h2, by rw [← rank_eq_trace h2, h3]⟩
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, h2, ?_⟩
    rw [← rank_eq_trace h2] at h3
    exact_mod_cast h3

end Glue

theorem A_to_B : A → B := by
  rintro ⟨-, -, -, hA4, hA5, -⟩ m
  have hcard : Fintype.card (Fin (2 * m)) = 2 * m := Fintype.card_fin _
  let hG : ↥(Grass (2 * m) m) ≃ₜ ↥(Morse.grassmannian (Fin (2 * m)) m) :=
    Homeomorph.setCongr (grass_eq (2 * m) m)
  refine ⟨fun k hk P g => ?_, fun k hk P g => ?_⟩
  · obtain ⟨e⟩ := hA4 hcard (hG P) hk
    exact ⟨(Morse.Homotopy.piEquivOfHomeomorph hG rfl (k + 1)).trans
      (e.trans (Morse.Homotopy.piEquivOfHomeomorph (Homeomorph.mulLeft g) (mul_one g) k))⟩
  · obtain ⟨e⟩ := hA5 hcard (hG P) hk
    obtain ⟨e₁⟩ := Morse.Homotopy.nonempty_mulEquiv_of_homeomorph hG (x := P) rfl (k + 1)
    obtain ⟨e₃⟩ := Morse.Homotopy.nonempty_mulEquiv_of_homeomorph (Homeomorph.mulLeft g)
      (mul_one g) k
    exact ⟨e₁.trans (e.trans e₃)⟩

/-- `A` without its first conjunct (the general statement for any `RCLike 𝕜` with
`SphereConnected 𝕜 d` and any codimension `m'`): the complex Grassmannian `G_m(ℂ^{2m})` parts. -/
def A_core : Prop :=
  (∀ {m j : ℕ} (_hj : j + 1 ≤ 2 * m),
      Nonempty (π_ (j + 1) ↥(Morse.Homotopy.Grassmannian ℂ (Fin m ⊕ Fin m) m)
          (Morse.Homotopy.grassBase ℂ (Fin m) m) ≃
        π_ j ↥(Matrix.unitaryGroup (Fin m) ℂ) 1)) ∧
  type_of% @Morse.Homotopy.nonempty_mulEquiv_grassmannian_complex ∧
  (∀ {ι : Type} [Fintype ι] [DecidableEq ι] {m : ℕ} (_hcard : Fintype.card ι = 2 * m)
      (P : ↥(Morse.grassmannian ι m)) {j : ℕ} (_hj : j + 1 ≤ 2 * m),
      Nonempty (π_ (j + 1) ↥(Morse.grassmannian ι m) P ≃ π_ j ↥(Matrix.unitaryGroup (Fin m) ℂ) 1)) ∧
  type_of% @Morse.Homotopy.nonempty_mulEquiv_grassmannianPi.{0} ∧
  (∀ {ι : Type} [Fintype ι] [DecidableEq ι] {m : ℕ} (_hcard : Fintype.card ι = 2 * m)
      (A : ↥(Morse.minVel ι)) {j : ℕ} (_hj : j + 1 ≤ 2 * m),
      Nonempty (π_ (j + 1) ↥(Morse.minVel ι) A ≃ π_ j ↥(Matrix.unitaryGroup (Fin m) ℂ) 1))

theorem A_core_of_A : A → A_core := fun h => h.2

/-- **B ⇒ A without its first conjunct**: reindexing (`Fin m ⊕ Fin m`, any `ι` with `|ι| = 2m`),
rank = trace, and Lemma 23.1's homeomorphism `minVel ι ≃ₜ G_m(ℂ^ι)` (`Morse.lemma_23_1`, outside
the item) for the last conjunct. -/
theorem B_to_A_core : B → A_core := by
  intro hB
  -- B, transported to any `ι` with `|ι| = 2m`, at any `P`, with `U(m)` at `1`
  have hι : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] {m : ℕ} (_hcard : Fintype.card ι = 2 * m)
      (P : ↥(Morse.Homotopy.Grassmannian ℂ ι m)),
      (∀ {j : ℕ}, j + 1 ≤ 2 * m →
        Nonempty (π_ (j + 1) ↥(Morse.Homotopy.Grassmannian ℂ ι m) P ≃
          π_ j ↥(Matrix.unitaryGroup (Fin m) ℂ) 1)) ∧
      (∀ {j : ℕ}, j + 2 ≤ 2 * m →
        Nonempty (π_ (j + 2) ↥(Morse.Homotopy.Grassmannian ℂ ι m) P ≃*
          π_ (j + 1) ↥(Matrix.unitaryGroup (Fin m) ℂ) 1)) := by
    intro ι _ _ m hcard P
    let e : ι ≃ Fin (2 * m) := Fintype.equivFinOfCardEq hcard
    let gH : ↥(Morse.Homotopy.Grassmannian ℂ ι m) ≃ₜ ↥(Grass (2 * m) m) :=
      (Morse.Homotopy.grassCongr e).trans (Homeomorph.setCongr (grass_eq (2 * m) m).symm)
    refine ⟨fun {j} hj => ?_, fun {j} hj => ?_⟩
    · obtain ⟨E⟩ := (hB m).1 j hj (gH P) 1
      exact ⟨(Morse.Homotopy.piEquivOfHomeomorph gH rfl (j + 1)).trans E⟩
    · obtain ⟨E⟩ := (hB m).2 j hj (gH P) 1
      obtain ⟨E₁⟩ := Morse.Homotopy.nonempty_mulEquiv_of_homeomorph gH (x := P) rfl (j + 1)
      exact ⟨E₁.trans E⟩
  have hcard2 : ∀ m : ℕ, Fintype.card (Fin m ⊕ Fin m) = 2 * m := fun m => by
    rw [Fintype.card_sum, Fintype.card_fin, two_mul]
  refine ⟨fun {m} {j} hj => (hι (hcard2 m) _).1 hj, fun {m} {j} hj => (hι (hcard2 m) _).2 hj,
    fun hcard P _ hj => (hι hcard P).1 hj, fun hcard P _ hj => (hι hcard P).2 hj,
    fun {ι} _ _ {m} hcard A {j} hj => ?_⟩
  have : Nonempty ι := Fintype.card_pos_iff.1 (by omega)
  obtain ⟨E⟩ := (hι hcard (Morse.lemma_23_1 hcard A)).1 hj
  exact ⟨(Morse.Homotopy.piEquivOfHomeomorph (Morse.lemma_23_1 hcard) rfl (j + 1)).trans E⟩

#rt_check RoundTrip.V14_26.B_to_A_core [Morse.Homotopy.grassmannianEquiv, Morse.Homotopy.grassmannianEquiv_complex, Morse.Homotopy.nonempty_mulEquiv_grassmannian_complex, Morse.Homotopy.grassmannianPiEquiv, Morse.Homotopy.nonempty_mulEquiv_grassmannianPi, Morse.Homotopy.minVelPiEquiv]
#rt_overlap RoundTrip.V14_26.B_to_A_core [Morse.Homotopy.grassmannianEquiv, Morse.Homotopy.grassmannianEquiv_complex, Morse.Homotopy.nonempty_mulEquiv_grassmannian_complex, Morse.Homotopy.grassmannianPiEquiv, Morse.Homotopy.nonempty_mulEquiv_grassmannianPi, Morse.Homotopy.minVelPiEquiv]
#rt_check RoundTrip.V14_26.A_to_B [Morse.Homotopy.grassmannianEquiv, Morse.Homotopy.grassmannianEquiv_complex, Morse.Homotopy.nonempty_mulEquiv_grassmannian_complex, Morse.Homotopy.grassmannianPiEquiv, Morse.Homotopy.nonempty_mulEquiv_grassmannianPi, Morse.Homotopy.minVelPiEquiv]
#rt_overlap RoundTrip.V14_26.A_to_B [Morse.Homotopy.grassmannianEquiv, Morse.Homotopy.grassmannianEquiv_complex, Morse.Homotopy.nonempty_mulEquiv_grassmannian_complex, Morse.Homotopy.grassmannianPiEquiv, Morse.Homotopy.nonempty_mulEquiv_grassmannianPi, Morse.Homotopy.minVelPiEquiv]

end RoundTrip.V14_26
