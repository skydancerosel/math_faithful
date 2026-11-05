import Morse
import RoundTrip.Check
import RoundTrip.Blind.VA_11

/-! # Round trip for VA_11 (Milnor, Appendix pp. 152–153: Theorem A, Case 2)

`A` is the conjunction of the types (universes at `0`) of the three listed theorems
`Morse.isHomotopyEquiv_of_truncation` (a self-map `F` of `X_Σ` preserving the truncations `X^m_Σ`,
with `F(x, m) = (e_m x, m)` and `e_m ≃ id`, is a homotopy equivalence), `Morse.homotopic_square`
(`i_n g_n ≃ g_{n+1} j_n`) and `Morse.theoremA_telescope` (`f_Σ` is a homotopy equivalence when the
`Y_n` are CLOSED); `Morse.case2Inv` (Milnor's `G`) is vocabulary.

`B`: for Case-2 data `D` (increasing `X_i`, `Y_i`, homotopy inverses `g_n`, homotopies
`h^n : i_n g_n ≃ g_{n+1} j_n`), (a) Milnor's formula `G` is a continuous map `Y_Σ → X_Σ`;
(b) `G f_Σ` restricts to a self-map of each `X^n_Σ` homotopic to the identity; (c) `G f_Σ` and
`f_Σ G` are homotopy equivalences; (d) `f_Σ` has left and right homotopy inverses and is a
homotopy equivalence. No closedness is assumed.

* **`B` is false** (`not_B`): Milnor's `G`, defined strip by strip, need not be continuous when
  the `Y_i` are not closed. Counterexample: `X = Y = ℝ`, `f = id`, `X_0 = Y_0 = (0, ∞)`,
  `X_n = Y_n = ℝ` (`n ≥ 1`), `g_n = id`, `h^0_s(y) = y + s(1 - s)/y` (a loop of maps, legitimate
  on `(0, ∞)`): `G(ε, 1 - ε/2) = (1, 1)` for all `ε ∈ (0, 1/2]`, but `G(0, 1) = (0, 1)`.
  So `A ⇒ B` is false and `B ⇒ A` holds vacuously.
* With the `Y_i` closed (`Bfix`, the project's hypothesis; Milnor's application has subcomplexes),
  `A ⇔ Bfix`, both directions proved:
  - `A ⇒ Bfix`: (a) is the project's `case2Inv` (whose values agree with Milnor's formula by
    unfolding: both use `n = ⌊τ⌋`); (b) is the chain `F ≃ F ι r = ι (g_m f_m) r ≃ ι r ≃ id`
    (re-proved here; `A` states only the homotopy-equivalence consequence); (c) is `A`'s
    `isHomotopyEquiv_of_truncation` for `G f_Σ` and `f_Σ G`; (d) follows from (c).
  - `Bfix ⇒ A`: `theoremA_telescope` is `Bfix`(d) (with `h^n` from the square lemma);
    `isHomotopyEquiv_of_truncation` is `Bfix`(d) applied to the space `X_Σ` with the closed
    sequence `{X^m_Σ}`, `f = F`, `g_m = id` (Case 1 is the special case `g_m = id` of Case 2),
    then `X_Σ = hdl{X^m_Σ}`; `homotopic_square` (not in `B`, where the `h^n` are data) is
    re-proved outright. -/

namespace RoundTrip.VA_11

open Set Filter Topology

/-- `A`: the three listed theorems, universes at `0`. -/
def A : Prop :=
  (type_of% @Morse.isHomotopyEquiv_of_truncation.{0}) ∧
    (type_of% @Morse.homotopic_square.{0, 0}) ∧ (type_of% @Morse.theoremA_telescope.{0, 0})

theorem A_holds : A :=
  ⟨@Morse.isHomotopyEquiv_of_truncation, @Morse.homotopic_square, @Morse.theoremA_telescope⟩

/-! ### `B` is false -/

namespace Counter

/-- `T_0 = (0, ∞)`, `T_n = ℝ` for `n ≥ 1`: `T_0` is not closed in `T_1`. -/
def T (n : ℕ) : Set ℝ := {x | 0 < x ∨ 1 ≤ n}

theorem hT : Monotone T := fun m n h x hx => by
  rcases hx with hx | hx
  · exact Or.inl hx
  · exact Or.inr (le_trans hx (by exact_mod_cast h))

theorem hf : ∀ i, ∀ x ∈ T i, (ContinuousMap.id ℝ) x ∈ T i := fun _ _ hx => hx

/-- `g_n = id`. -/
def g (n : ℕ) : C(↥(T n), ↥(T n)) := ContinuousMap.id _

/-- The correction term `s (1 - s) / y` on `T_0`, `0` on the other `T_n`. -/
noncomputable def c (n : ℕ) (y : ℝ) : ℝ := if n = 0 then y⁻¹ else 0

theorem continuous_c (n : ℕ) : Continuous fun y : ↥(T n) => c n y.1 := by
  unfold c
  split_ifs with hn
  · subst hn
    refine continuous_subtype_val.inv₀ fun y => ?_
    rcases y.2 with h | h
    · exact h.ne'
    · simp at h
  · exact continuous_const

/-- The homotopy `h^n_s(y) = y + s (1 - s) c_n(y)` from `i_n g_n = incl` to `g_{n+1} j_n = incl`;
for `n = 0` it is unbounded near `y = 0`, `s = 1`. -/
noncomputable def H (n : ℕ) : ContinuousMap.Homotopy ((inclC (hT (Nat.le_succ n))).comp (g n))
    ((g (n + 1)).comp (inclC (hT (Nat.le_succ n)))) where
  toFun q := ⟨q.2.1 + (q.1 : ℝ) * (1 - q.1) * c n q.2.1, Or.inr (by simp)⟩
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    have hs : Continuous fun q : unitInterval × ↥(T n) => ((q.1 : unitInterval) : ℝ) :=
      continuous_subtype_val.comp continuous_fst
    exact (continuous_subtype_val.comp continuous_snd).add
      ((hs.mul (continuous_const.sub hs)).mul ((continuous_c n).comp continuous_snd))
  map_zero_left y := by
    apply Subtype.ext
    simp [g, inclC]
  map_one_left y := by
    apply Subtype.ext
    simp [g, inclC]

noncomputable def D : Case2 (ContinuousMap.id ℝ) T T where
  hS := hT
  hT := hT
  hf := hf
  g := g
  hg₁ _ := ContinuousMap.Homotopic.refl _
  hg₂ _ := ContinuousMap.Homotopic.refl _
  H := H

theorem Gmap_eq (z : ↥(tel T)) : Gmap D z =
    if z.1.2 - ⌊z.1.2⌋₊ ≤ 1 / 2 then (z.1.1, (⌊z.1.2⌋₊ : ℝ) + 2 * (z.1.2 - ⌊z.1.2⌋₊))
    else (z.1.1 + ((Set.projIcc (0 : ℝ) 1 zero_le_one (2 * (z.1.2 - ⌊z.1.2⌋₊) - 1) : ℝ)) *
      (1 - (Set.projIcc (0 : ℝ) 1 zero_le_one (2 * (z.1.2 - ⌊z.1.2⌋₊) - 1) : ℝ)) *
        c ⌊z.1.2⌋₊ z.1.1, (⌊z.1.2⌋₊ : ℝ) + 1) := by
  unfold Gmap
  split_ifs <;> rfl

theorem Gmap_seq {ε : ℝ} (h0 : 0 < ε) (h1 : ε ≤ 1 / 2) (hz : ((ε, 1 - ε / 2) : ℝ × ℝ) ∈ tel T) :
    Gmap D ⟨(ε, 1 - ε / 2), hz⟩ = (1, 1) := by
  rw [Gmap_eq]
  have hfl : ⌊(1 - ε / 2 : ℝ)⌋₊ = 0 := Nat.floor_eq_zero.mpr (by linarith)
  simp only [hfl, Nat.cast_zero, sub_zero, zero_add]
  rw [if_neg (by linarith)]
  have hmem : (2 * (1 - ε / 2) - 1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
  rw [Set.projIcc_of_mem zero_le_one hmem]
  simp only [c, if_true]
  have hne : ε ≠ 0 := h0.ne'
  ext
  · simp only
    field_simp
    ring
  · simp

theorem Gmap_lim (hz : ((0, 1) : ℝ × ℝ) ∈ tel T) : Gmap D ⟨(0, 1), hz⟩ = (0, 1) := by
  rw [Gmap_eq]
  simp

end Counter

/-- **`B` is false**: Milnor's `G` need not be continuous when the `Y_i` are not closed. With
`X = Y = ℝ`, `f = id`, `X_i = Y_i = T_i` (`T_0 = (0, ∞)`, `T_n = ℝ` for `n ≥ 1`), `g_n = id` and
`h^0_s(y) = y + s(1 - s)/y`, the points `(ε, 1 - ε/2) ∈ Y_Σ` tend to `(0, 1)` as `ε → 0`, but
`G(ε, 1 - ε/2) = (h^0_{1-ε}(ε), 1) = (1, 1)` while `G(0, 1) = (g_1(0), 1) = (0, 1)`. -/
theorem not_B : ¬ B := by
  intro hB
  obtain ⟨Gc, hGc, -⟩ := hB ℝ ℝ (ContinuousMap.id ℝ) Counter.T Counter.T Counter.D
  have hcont : Continuous (Gmap Counter.D) := by
    have : Gmap Counter.D = fun z => ((Gc z : ↥(tel Counter.T)) : ℝ × ℝ) :=
      funext fun z => (hGc z).symm
    rw [this]
    exact continuous_subtype_val.comp Gc.continuous
  set ε : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1) / 2 with hεdef
  have hε0 : ∀ k, 0 < ε k := fun k => by positivity
  have hε1 : ∀ k, ε k ≤ 1 / 2 := fun k => by
    have : 1 / ((k : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
    simp only [hεdef]; linarith
  have hmem : ∀ k, ((ε k, 1 - ε k / 2) : ℝ × ℝ) ∈ tel Counter.T := fun k =>
    ⟨0, Or.inl (hε0 k), by simp; linarith [hε1 k], by simp; linarith [hε0 k]⟩
  have hmem0 : ((0, 1) : ℝ × ℝ) ∈ tel Counter.T := ⟨1, Or.inr le_rfl, by simp, by norm_num⟩
  let z : ℕ → ↥(tel Counter.T) := fun k => ⟨(ε k, 1 - ε k / 2), hmem k⟩
  have hε : Tendsto ε atTop (𝓝 0) := by
    have := tendsto_one_div_add_atTop_nhds_zero_nat.div_const (2 : ℝ)
    rw [zero_div] at this
    exact this
  have htend : Tendsto z atTop (𝓝 ⟨(0, 1), hmem0⟩) := by
    rw [tendsto_subtype_rng]
    refine hε.prodMk_nhds ?_
    have := (tendsto_const_nhds (x := (1 : ℝ))).sub (hε.div_const 2)
    simpa using this
  have h1 := (hcont.tendsto _).comp htend
  have hval : (Gmap Counter.D ∘ z) = fun _ => ((1 : ℝ), (1 : ℝ)) :=
    funext fun k => Counter.Gmap_seq (hε0 k) (hε1 k) (hmem k)
  rw [hval, Counter.Gmap_lim] at h1
  have := tendsto_nhds_unique tendsto_const_nhds h1
  simp at this

/-- `B ⇒ A`: vacuous. -/
theorem B_to_A : B → A := fun hB => absurd hB not_B

/-! ### The corrected claim: `Y_i` closed -/

/-- `B` with the `Y_i` closed. -/
def Bfix : Prop :=
  ∀ (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y)) (S : ℕ → Set X)
    (T : ℕ → Set Y) (D : Case2 f S T), (∀ n, IsClosed (T n)) →
    ∃ Gc : C(↥(tel T), ↥(tel S)), (∀ z, (Gc z).1 = Gmap D z) ∧
      (∀ n : ℕ, ∃ hn : C(↥(truncSub S n), ↥(truncSub S n)),
        (∀ z, ((hn z).1 : ↥(tel S)) = Gc (fSig f D.hf z.1)) ∧ hn.Homotopic (ContinuousMap.id _)) ∧
      IsHE (Gc.comp (fSig f D.hf)) ∧ IsHE ((fSig f D.hf).comp Gc) ∧
      (∃ L R : C(↥(tel T), ↥(tel S)), (L.comp (fSig f D.hf)).Homotopic (ContinuousMap.id _) ∧
        ((fSig f D.hf).comp R).Homotopic (ContinuousMap.id _)) ∧
      IsHE (fSig f D.hf)

theorem B_to_Bfix : B → Bfix := fun hB X Y _ _ f S T D _ => hB X Y f S T D

/-! ### Glue -/

section Glue

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

omit [TopologicalSpace X] in
theorem tel_eq_telescope (S : ℕ → Set X) : tel S = Morse.telescope S := by
  ext z
  simp only [tel, Morse.telescope, mem_iUnion, mem_prod, mem_Icc]; rfl

/-- The identity homeomorphism `tel S ≃ₜ telescope S`. -/
noncomputable def telHomeo (S : ℕ → Set X) : ↥(tel S) ≃ₜ ↥(Morse.telescope S) :=
  Homeomorph.setCongr (tel_eq_telescope S)

/-- The identity homeomorphism `X^n_Σ (blind) ≃ₜ X^n_Σ (project)`. -/
noncomputable def truncHomeo (S : ℕ → Set X) (n : ℕ) :
    ↥(truncSub S n) ≃ₜ ↥(Morse.truncation S n) :=
  (telHomeo S).subtype (p := fun z => z ∈ truncSub S n)
    (q := fun z => z ∈ Morse.truncation S n) fun _ => Iff.rfl

theorem isHE_iff {P Q : Type} [TopologicalSpace P] [TopologicalSpace Q] (f : C(P, Q)) :
    IsHE f ↔ Morse.IsHomotopyEquiv f :=
  ⟨fun ⟨g, h₁, h₂⟩ => ⟨g, h₂, h₁⟩, fun ⟨g, h₁, h₂⟩ => ⟨g, h₂, h₁⟩⟩

theorem isHomotopyEquiv_comp_homeo_iff {P P' Q : Type} [TopologicalSpace P] [TopologicalSpace P']
    [TopologicalSpace Q] (f : C(P, Q)) (e : P' ≃ₜ P) :
    Morse.IsHomotopyEquiv (f.comp (e : C(P', P))) ↔ Morse.IsHomotopyEquiv f := by
  constructor
  · intro h
    have h' := (Morse.IsHomotopyEquiv.of_homeomorph e.symm).comp h
    have : (f.comp (e : C(P', P))).comp (e.symm : C(P, P')) = f := by
      ext x; simp
    rwa [this] at h'
  · intro h
    exact (Morse.IsHomotopyEquiv.of_homeomorph e).comp h

theorem isHomotopyEquiv_homeo_comp_iff {P Q Q' : Type} [TopologicalSpace P] [TopologicalSpace Q']
    [TopologicalSpace Q] (f : C(P, Q)) (e : Q ≃ₜ Q') :
    Morse.IsHomotopyEquiv ((e : C(Q, Q')).comp f) ↔ Morse.IsHomotopyEquiv f := by
  constructor
  · intro h
    have h' := h.comp (Morse.IsHomotopyEquiv.of_homeomorph e.symm)
    have : (e.symm : C(Q', Q)).comp ((e : C(Q, Q')).comp f) = f := by
      ext x; simp
    rwa [this] at h'
  · intro h
    exact h.comp (Morse.IsHomotopyEquiv.of_homeomorph e)

/-- Conjugating by homeomorphisms preserves and reflects homotopy equivalences. -/
theorem isHE_conj_iff {P P' Q Q' : Type} [TopologicalSpace P] [TopologicalSpace P']
    [TopologicalSpace Q] [TopologicalSpace Q'] (f : C(P, Q)) (e : P' ≃ₜ P) (e' : Q ≃ₜ Q') :
    IsHE ((e' : C(Q, Q')).comp (f.comp (e : C(P', P)))) ↔ Morse.IsHomotopyEquiv f := by
  rw [isHE_iff, isHomotopyEquiv_homeo_comp_iff, isHomotopyEquiv_comp_homeo_iff]

theorem fSig_eq (f : C(X, Y)) {S : ℕ → Set X} {T : ℕ → Set Y} (h : ∀ i, ∀ x ∈ S i, f x ∈ T i) :
    fSig f h = ((telHomeo T).symm : C(↥(Morse.telescope T), ↥(tel T))).comp
      ((Morse.telescopeMap f (fun i _ hx => h i _ hx)).comp
        (telHomeo S : C(↥(tel S), ↥(Morse.telescope S)))) :=
  rfl

end Glue

/-! ### `A ⇒ Bfix` -/

section AtoB

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] {f : C(X, Y)} {S : ℕ → Set X}
  {T : ℕ → Set Y} (D : Case2 f S T) (hTc : ∀ n, IsClosed (T n))

include D in
theorem hf' : ∀ n, MapsTo f (S n) (T n) := fun n _ hx => D.hf n _ hx

/-- The homotopies `h^n` of `D`, with the project's inclusions `up` (definitionally `inclC`). -/
def Hk (n : ℕ) : ((Morse.up D.hS n).comp (D.g n)).Homotopy
    ((D.g (n + 1)).comp (Morse.up D.hT n)) := D.H n

/-- Milnor's `G`: the project's `case2Inv` (vocabulary of `A`). -/
noncomputable def G' : C(↥(Morse.telescope T), ↥(Morse.telescope S)) :=
  Morse.case2Inv D.hS D.hT hTc D.g (Hk D)

/-- `G` on the blind telescopes. -/
noncomputable def Gc : C(↥(tel T), ↥(tel S)) :=
  ((telHomeo S).symm : C(↥(Morse.telescope S), ↥(tel S))).comp
    ((G' D hTc).comp (telHomeo T : C(↥(tel T), ↥(Morse.telescope T))))

/-- (a) The project's `G` is Milnor's formula (both use the strip `n = ⌊τ⌋`). -/
theorem Gc_val (z : ↥(tel T)) : ((Gc D hTc z : ↥(tel S)) : X × ℝ) = Gmap D z := by
  change ((Morse.case2InvStrip D.hS D.hT D.g (Hk D) ⌊z.1.2⌋₊
    (⟨z.1.1, Morse.mem_floor D.hT (telHomeo T z)⟩,
      ⟨z.1.2 - ⌊z.1.2⌋₊, Morse.fract_mem (telHomeo T z)⟩) : ↥(Morse.telescope S)) : X × ℝ) =
    Gmap D z
  have hfl0 : (⌊z.1.2⌋₊ : ℝ) ≤ z.1.2 := Nat.floor_le (Morse.nonneg_of_mem_telescope (telHomeo T z).2)
  unfold Gmap Morse.case2InvStrip
  simp only [ContinuousMap.coe_mk]
  split_ifs with h
  · refine Prod.ext rfl ?_
    simp only [Morse.stripMap_apply_snd]
    rw [Morse.clampI_val (by linarith) (by linarith)]
  · refine Prod.ext rfl ?_
    simp

/-- `F = G f_Σ` on the project's telescope. -/
noncomputable def F : C(↥(Morse.telescope S), ↥(Morse.telescope S)) :=
  (G' D hTc).comp (Morse.telescopeMap f (hf' D))

theorem F_maps (m : ℕ) : MapsTo (F D hTc) (Morse.truncation S m) (Morse.truncation S m) := by
  intro z hz
  change ((F D hTc z : ↥(Morse.telescope S)) : X × ℝ).2 ≤ m
  refine Morse.level_le_of_stripMap D.hS (fun w : ↥(Morse.telescope S) => (w : X × ℝ).2)
    (F D hTc) (fun n x t => ?_) (fun n x => ?_) hz
  · rw [F, ContinuousMap.comp_apply, Morse.telescopeMap_stripMap]
    exact Morse.case2Inv_level D.hS D.hT hTc D.g (Hk D) n _ t
  · rw [F, ContinuousMap.comp_apply, Morse.telescopeMap_stripMap, G', Morse.case2Inv_zero]
    simp

theorem F_zero (m : ℕ) (x : ↥(S m)) : F D hTc (Morse.stripMap S m (x, 0)) =
    Morse.stripMap S m (((D.g m).comp (resC f (D.hf m))) x, 0) := by
  rw [F, ContinuousMap.comp_apply, Morse.telescopeMap_stripMap, G', Morse.case2Inv_zero]
  rfl

/-- (b) on the project's truncation: `F ≃ F ι r = ι (g_m f_m) r ≃ ι r ≃ id`. -/
theorem F_restrict_homotopic (m : ℕ) :
    (Morse.restrictTo (F D hTc) (F_maps D hTc m)).Homotopic (ContinuousMap.id _) := by
  set ι := Morse.truncIncl S m
  set r := Morse.truncProj D.hS m
  set Fm := Morse.restrictTo (F D hTc) (F_maps D hTc m)
  have hT2 := Morse.truncIncl_comp_truncProj D.hS m
  have hcomm : Fm.comp ι = ι.comp ((D.g m).comp (resC f (D.hf m))) :=
    ContinuousMap.ext fun x => Subtype.ext (F_zero D hTc m x)
  have h1 : Fm.Homotopic ((Fm.comp ι).comp r) := by
    have := (ContinuousMap.Homotopic.refl Fm).comp hT2.symm
    rwa [ContinuousMap.comp_id] at this
  have h2 : ((ι.comp ((D.g m).comp (resC f (D.hf m)))).comp r).Homotopic (ι.comp r) := by
    have := ((ContinuousMap.Homotopic.refl ι).comp (D.hg₁ m)).comp
      (ContinuousMap.Homotopic.refl r)
    rwa [ContinuousMap.comp_id] at this
  rw [hcomm] at h1
  exact (h1.trans h2).trans hT2

/-- `F' = f_Σ G` on the project's telescope. -/
noncomputable def F' : C(↥(Morse.telescope T), ↥(Morse.telescope T)) :=
  (Morse.telescopeMap f (hf' D)).comp (G' D hTc)

theorem F'_maps (m : ℕ) : MapsTo (F' D hTc) (Morse.truncation T m) (Morse.truncation T m) := by
  intro z hz
  change ((F' D hTc z : ↥(Morse.telescope T)) : Y × ℝ).2 ≤ m
  refine Morse.level_le_of_stripMap D.hT (fun w : ↥(Morse.telescope T) => (w : Y × ℝ).2)
    (F' D hTc) (fun n y t => ?_) (fun n y => ?_) hz
  · exact Morse.case2Inv_level D.hS D.hT hTc D.g (Hk D) n y t
  · change ((G' D hTc (Morse.stripMap T n (y, 0)) : ↥(Morse.telescope S)) : X × ℝ).2 ≤ n
    rw [G', Morse.case2Inv_zero]
    simp

theorem F'_zero (m : ℕ) (y : ↥(T m)) : F' D hTc (Morse.stripMap T m (y, 0)) =
    Morse.stripMap T m (((resC f (D.hf m)).comp (D.g m)) y, 0) := by
  rw [F', ContinuousMap.comp_apply, G', Morse.case2Inv_zero, Morse.telescopeMap_stripMap]
  rfl

theorem GcfSig_eq : (Gc D hTc).comp (fSig f D.hf) =
    ((telHomeo S).symm : C(↥(Morse.telescope S), ↥(tel S))).comp
      ((F D hTc).comp (telHomeo S : C(↥(tel S), ↥(Morse.telescope S)))) :=
  ContinuousMap.ext fun _ => rfl

theorem fSigGc_eq : (fSig f D.hf).comp (Gc D hTc) =
    ((telHomeo T).symm : C(↥(Morse.telescope T), ↥(tel T))).comp
      ((F' D hTc).comp (telHomeo T : C(↥(tel T), ↥(Morse.telescope T)))) :=
  ContinuousMap.ext fun _ => rfl

end AtoB

/-- `A ⇒ Bfix` (uses `A`'s `isHomotopyEquiv_of_truncation` for (c); (a), (b) are the
construction and the chain above, (d) follows from (c)). -/
theorem A_to_Bfix : A → Bfix := by
  rintro ⟨hTrunc, -, -⟩ X Y _ _ f S T D hTc
  have hc1 : IsHE ((Gc D hTc).comp (fSig f D.hf)) := by
    rw [GcfSig_eq, isHE_conj_iff]
    exact hTrunc D.hS (F D hTc) (F_maps D hTc) (fun m => (D.g m).comp (resC f (D.hf m))) D.hg₁
      (F_zero D hTc)
  have hc2 : IsHE ((fSig f D.hf).comp (Gc D hTc)) := by
    rw [fSigGc_eq, isHE_conj_iff]
    exact hTrunc D.hT (F' D hTc) (F'_maps D hTc) (fun m => (resC f (D.hf m)).comp (D.g m))
      D.hg₂ (F'_zero D hTc)
  have hLR : ∃ L R : C(↥(tel T), ↥(tel S)), (L.comp (fSig f D.hf)).Homotopic
      (ContinuousMap.id _) ∧ ((fSig f D.hf).comp R).Homotopic (ContinuousMap.id _) := by
    obtain ⟨k₁, -, hk₁⟩ := hc1
    obtain ⟨k₂, hk₂, -⟩ := hc2
    exact ⟨k₁.comp (Gc D hTc), (Gc D hTc).comp k₂, by simpa only [ContinuousMap.comp_assoc]
      using hk₁, by simpa only [ContinuousMap.comp_assoc] using hk₂⟩
  refine ⟨Gc D hTc, Gc_val D hTc, fun n => ?_, hc1, hc2, hLR, ?_⟩
  · refine ⟨((truncHomeo S n).symm : C(↥(Morse.truncation S n), ↥(truncSub S n))).comp ((Morse.restrictTo (F D hTc)
      (F_maps D hTc n)).comp (truncHomeo S n : C(↥(truncSub S n), ↥(Morse.truncation S n)))), fun z => rfl, ?_⟩
    have := (ContinuousMap.Homotopic.refl ((truncHomeo S n).symm : C(↥(Morse.truncation S n), ↥(truncSub S n)))).comp
      ((F_restrict_homotopic D hTc n).comp
        (ContinuousMap.Homotopic.refl (truncHomeo S n : C(↥(truncSub S n), ↥(Morse.truncation S n)))))
    convert this using 1
    exact ContinuousMap.ext fun z => rfl
  · obtain ⟨L, R, hL, hR⟩ := hLR
    exact (isHE_iff _).2 (Morse.IsHomotopyEquiv.of_leftInv_rightInv hL hR)

/-! ### `Bfix ⇒ A` -/

section BtoA

variable {X : Type} [TopologicalSpace X] {S : ℕ → Set X} {Y : Type} [TopologicalSpace Y]
  {T : ℕ → Set Y}

/-- `Morse.homotopic_square`, re-proved outright (`B` takes the homotopies `h^n` as data). -/
theorem square (hS : Monotone S) (hT : Monotone T) {f : C(X, Y)}
    {hf : ∀ n, MapsTo f (S n) (T n)} (g : ∀ n, C(T n, S n))
    (hgf : ∀ n, ((g n).comp (Morse.restrictTo f (hf n))).Homotopic (ContinuousMap.id _))
    (hfg : ∀ n, ((Morse.restrictTo f (hf n)).comp (g n)).Homotopic (ContinuousMap.id _))
    (n : ℕ) : ((Morse.up hS n).comp (g n)).Homotopic ((g (n + 1)).comp (Morse.up hT n)) := by
  have hc : (Morse.restrictTo f (hf (n + 1))).comp (Morse.up hS n) =
      (Morse.up hT n).comp (Morse.restrictTo f (hf n)) := rfl
  have h1 : ((Morse.up hS n).comp (g n)).Homotopic
      (((g (n + 1)).comp (Morse.restrictTo f (hf (n + 1)))).comp ((Morse.up hS n).comp (g n))) := by
    have := (hgf (n + 1)).symm.comp (ContinuousMap.Homotopic.refl ((Morse.up hS n).comp (g n)))
    rwa [ContinuousMap.id_comp] at this
  have h2 : (((g (n + 1)).comp (Morse.restrictTo f (hf (n + 1)))).comp
      ((Morse.up hS n).comp (g n))) =
      ((g (n + 1)).comp (Morse.up hT n)).comp ((Morse.restrictTo f (hf n)).comp (g n)) := by
    simp only [ContinuousMap.comp_assoc]
    rw [← ContinuousMap.comp_assoc (Morse.restrictTo f (hf (n + 1))), hc,
      ContinuousMap.comp_assoc]
  have h3 : (((g (n + 1)).comp (Morse.up hT n)).comp
      ((Morse.restrictTo f (hf n)).comp (g n))).Homotopic ((g (n + 1)).comp (Morse.up hT n)) := by
    have := (ContinuousMap.Homotopic.refl ((g (n + 1)).comp (Morse.up hT n))).comp (hfg n)
    rwa [ContinuousMap.comp_id] at this
  rw [h2] at h1
  exact h1.trans h3

/-- `theoremA_telescope` from `Bfix`(d). -/
theorem tel_of_Bfix (hB : Bfix) : type_of% @Morse.theoremA_telescope.{0, 0} := by
  intro X _ S Y _ T hS hT hTc f hf hfe
  choose g hgf hfg using hfe
  let D : Case2 f S T :=
    { hS := hS, hT := hT, hf := fun i _ hx => hf i hx, g := g, hg₁ := hgf, hg₂ := hfg,
      H := fun n => (square hS hT g hgf hfg n).some }
  obtain ⟨-, -, -, -, -, -, h⟩ := hB X Y f S T D hTc
  rw [fSig_eq, isHE_conj_iff] at h
  exact h

/-- `isHomotopyEquiv_of_truncation` from `Bfix`(d), applied to the space `X_Σ`, its closed
truncations, `f = F` and `g_m = id` (Case 1 as a special case of Case 2). -/
theorem trunc_of_Bfix (hB : Bfix) : type_of% @Morse.isHomotopyEquiv_of_truncation.{0} := by
  intro X _ S hS F hF e he hFe
  have hFm : ∀ m, (Morse.restrictTo F (hF m)).Homotopic (ContinuousMap.id _) := by
    intro m
    set ι := Morse.truncIncl S m
    set r := Morse.truncProj hS m
    set Fm := Morse.restrictTo F (hF m)
    have hT2 := Morse.truncIncl_comp_truncProj hS m
    have hcomm : Fm.comp ι = ι.comp (e m) :=
      ContinuousMap.ext fun x => Subtype.ext (hFe m x)
    have h1 : Fm.Homotopic ((Fm.comp ι).comp r) := by
      have := (ContinuousMap.Homotopic.refl Fm).comp hT2.symm
      rwa [ContinuousMap.comp_id] at this
    have h2 : ((ι.comp (e m)).comp r).Homotopic (ι.comp r) := by
      have := ((ContinuousMap.Homotopic.refl ι).comp (he m)).comp
        (ContinuousMap.Homotopic.refl r)
      rwa [ContinuousMap.comp_id] at this
    rw [hcomm] at h1
    exact (h1.trans h2).trans hT2
  let D : Case2 F (Morse.truncation S) (Morse.truncation S) :=
    { hS := Morse.monotone_truncation, hT := Morse.monotone_truncation,
      hf := fun i _ hx => hF i hx, g := fun m => ContinuousMap.id _,
      hg₁ := fun m => hFm m, hg₂ := fun m => hFm m,
      H := fun n => ContinuousMap.Homotopy.refl _ }
  obtain ⟨-, -, -, -, -, -, h⟩ := hB _ _ F _ _ D Morse.isClosed_truncation
  rw [fSig_eq, isHE_conj_iff] at h
  exact Morse.IsHomotopyEquiv.of_telescopeMap Morse.isHomotopyDirectLimit_truncation
    Morse.isHomotopyDirectLimit_truncation h

end BtoA

theorem Bfix_to_A : Bfix → A := fun hB => ⟨trunc_of_Bfix hB, @square, tel_of_Bfix hB⟩

/-- `A ⇒ B` is false (`A` holds, `B` does not). -/
theorem not_A_to_B : ¬ (A → B) := fun h => not_B (h A_holds)

#rt_check RoundTrip.VA_11.not_B [Morse.isHomotopyEquiv_of_truncation, Morse.homotopic_square, Morse.theoremA_telescope]
#rt_check RoundTrip.VA_11.B_to_A [Morse.isHomotopyEquiv_of_truncation, Morse.homotopic_square, Morse.theoremA_telescope]
#rt_check RoundTrip.VA_11.A_to_Bfix [Morse.isHomotopyEquiv_of_truncation, Morse.homotopic_square, Morse.theoremA_telescope]
#rt_check RoundTrip.VA_11.Bfix_to_A [Morse.isHomotopyEquiv_of_truncation, Morse.homotopic_square, Morse.theoremA_telescope]
#rt_overlap RoundTrip.VA_11.B_to_A [Morse.isHomotopyEquiv_of_truncation, Morse.homotopic_square, Morse.theoremA_telescope]
#rt_overlap RoundTrip.VA_11.A_to_Bfix [Morse.isHomotopyEquiv_of_truncation, Morse.homotopic_square, Morse.theoremA_telescope]
#rt_overlap RoundTrip.VA_11.Bfix_to_A [Morse.isHomotopyEquiv_of_truncation, Morse.homotopic_square, Morse.theoremA_telescope]

end RoundTrip.VA_11
