import Morse.Appendix.Telescope

/-!
Milnor, *Morse Theory*, Appendix, p. 153 (the Corollary) and §17 (p. 95, the alternative proof of
Theorem 17.3): the mapping telescope of a sequence of maps.

# The mapping telescope of `K₀ → K₁ → K₂ → ⋯`

Milnor's telescope `X_Σ ⊆ X × ℝ` is built from *subspaces* of one space. The complexes `K_i` of the
proof of Theorem 17.3, and the CW-complexes `K_i ≃ X_i` of the Corollary, are not subspaces of a
common space in the Lean model of this project: an iterated adjunction space
(`Morse.IsCellAttachment`) is a pushout in `TopCat`, and attaching a cell comes with a map
`K → K ∪_φ e^λ`, not an inclusion. The *mapping telescope* of a sequence of maps
`c_n : K_n → K_{n+1}` (a functor `ℕ ⥤ TopCat`) is the quotient of `⨆_n K_n × [0, 1]` by
`(k, 1)_n ∼ (c_n(k), 0)_{n+1}`, with the quotient topology (`Morse.MappingTelescope`); the point
`(k, t)_n` is at level `n + t` (`Morse.MappingTelescope.level`). For a sequence of inclusions of
closed subspaces it is homeomorphic to Milnor's `X_Σ` (`Morse.telescopeComparisonHomeomorph`), and
for any monotone sequence of subspaces homotopy equivalent to it
(`Morse.isHomotopyEquiv_telescopeComparison`). It is the standard model of the union of the `K_n`
up to homotopy; the comparison with the union with the weak topology is Example 2 of the Appendix
(Whitehead's theorem), not formalized.

## What is proved here

* Maps and homotopies out of the mapping telescope are given block by block
  (`Morse.MappingTelescope.desc`, `Morse.MappingTelescope.lift`,
  `Morse.MappingTelescope.homotopy`): `[0, 1]` is locally compact, so the product of the quotient
  map with `[0, 1]` is again a quotient map (J. H. C. Whitehead's lemma, via the exponential law).
* The truncations `T_n = {level ≤ n}` are closed, and the mapping telescope is the homotopy direct
  limit of them (`Morse.MappingTelescope.isHomotopyDirectLimit_trunc`), by Lemma 2.1 with
  `f = level + 1`.
* **(T2) for mapping telescopes**: `k ↦ (k, 0)_n` is a homotopy equivalence `K_n → T_n`
  (`Morse.MappingTelescope.isHomotopyEquiv_levelIncl`). The deformation pushes every point of `T_n`
  up to level `n` along the trajectories of the maps `c` (`Morse.MappingTelescope.traj`,
  `Morse.MappingTelescope.push`), crossing the blocks between; the inverse map `T_n → K_n` is
  continuous because `K_n → T_n` is an embedding (`Morse.MappingTelescope.isInducing_mk_zero`: a
  neighbourhood of level `n` is a saturated open set of the disjoint union) and injective
  (`Morse.MappingTelescope.atLevel`).
-/

open Set Filter Topology Function CategoryTheory
open scoped unitInterval

universe u

noncomputable section

namespace Morse

variable (F : ℕ ⥤ TopCat.{u})

/-- The maps of the sequence: `F(m ≤ n) : F_m → F_n`. -/
def tmap {m n : ℕ} (h : m ≤ n) : C(F.obj m, F.obj n) :=
  (F.map (homOfLE h)).hom

theorem tmap_refl (n : ℕ) (k : F.obj n) : tmap F (le_refl n) k = k := by
  have : homOfLE (le_refl n) = 𝟙 n := Subsingleton.elim _ _
  simp only [tmap]
  rw [this, F.map_id]
  rfl

theorem tmap_tmap {l m n : ℕ} (h₁ : l ≤ m) (h₂ : m ≤ n) (k : F.obj l) :
    tmap F h₂ (tmap F h₁ k) = tmap F (h₁.trans h₂) k := by
  have : homOfLE h₁ ≫ homOfLE h₂ = homOfLE (h₁.trans h₂) := Subsingleton.elim _ _
  simp only [tmap]
  rw [← this, F.map_comp]
  rfl

/-- The gluing relation of the mapping telescope: the top `(k, 1)` of the `n`-th block is the
bottom `(c_n(k), 0)` of the next one. -/
inductive MapTelRel : (Σ n : ℕ, F.obj n × I) → (Σ n : ℕ, F.obj n × I) → Prop
  | glue (n : ℕ) (k : F.obj n) :
      MapTelRel ⟨n, k, 1⟩ ⟨n + 1, tmap F (Nat.le_add_right n 1) k, 0⟩

/-- **The mapping telescope** of `F₀ → F₁ → F₂ → ⋯`: `⨆_n F_n × [0, 1]` with `(k, 1)_n` glued to
`(c_n(k), 0)_{n+1}`, with the quotient topology. -/
def MappingTelescope : Type u :=
  Quot (MapTelRel F)

instance : TopologicalSpace (MappingTelescope F) :=
  inferInstanceAs (TopologicalSpace (Quot (MapTelRel F)))

namespace MappingTelescope

/-- The point `(k, t)` of the `n`-th block, at level `n + t`. -/
def mk (n : ℕ) (k : F.obj n) (t : I) : MappingTelescope F :=
  Quot.mk _ ⟨n, k, t⟩

theorem mk_one (n : ℕ) (k : F.obj n) :
    mk F n k 1 = mk F (n + 1) (tmap F (Nat.le_add_right n 1) k) 0 :=
  Quot.sound (.glue n k)

theorem isQuotientMap_quotMk :
    @IsQuotientMap _ (MappingTelescope F) _ _ (Quot.mk (MapTelRel F)) :=
  isQuotientMap_quot_mk

theorem continuous_mk (n : ℕ) : Continuous fun q : F.obj n × I => mk F n q.1 q.2 :=
  (isQuotientMap_quotMk F).continuous.comp
    (continuous_sigmaMk.comp (continuous_fst.prodMk continuous_snd))

theorem exists_mk (z : MappingTelescope F) : ∃ n k t, mk F n k t = z := by
  induction z using Quot.ind with
  | mk q => exact ⟨q.1, q.2.1, q.2.2, rfl⟩

section Desc

variable {Z : Type*} [TopologicalSpace Z]

/-- **Maps out of the mapping telescope**, given block by block, compatibly at the gluing. -/
def desc (Φ : ∀ n, C(F.obj n × I, Z))
    (hΦ : ∀ n k, Φ (n + 1) (tmap F (Nat.le_add_right n 1) k, 0) = Φ n (k, 1)) :
    C(MappingTelescope F, Z) where
  toFun := Quot.lift (fun q => Φ q.1 q.2) (by
    rintro _ _ ⟨n, k⟩
    exact (hΦ n k).symm)
  continuous_toFun := continuous_quot_lift _ (continuous_sigma fun n => (Φ n).continuous)

@[simp]
theorem desc_mk (Φ : ∀ n, C(F.obj n × I, Z))
    (hΦ : ∀ n k, Φ (n + 1) (tmap F (Nat.le_add_right n 1) k, 0) = Φ n (k, 1)) (n : ℕ)
    (k : F.obj n) (t : I) : desc F Φ hΦ (mk F n k t) = Φ n (k, t) :=
  rfl

/-- **Maps out of `P × (mapping telescope)`**, for a locally compact `P`, given block by block. -/
def lift {P : Type*} [TopologicalSpace P] [LocallyCompactSpace P] (Φ : ∀ n, C(P × (F.obj n × I), Z))
    (hΦ : ∀ n p k, Φ (n + 1) (p, (tmap F (Nat.le_add_right n 1) k, 0)) = Φ n (p, (k, 1))) :
    C(P × MappingTelescope F, Z) :=
  (ContinuousMap.uncurry (desc F (fun n => ContinuousMap.curry ((Φ n).comp ContinuousMap.prodSwap))
    fun n k => ContinuousMap.ext fun p => hΦ n p k)).comp ContinuousMap.prodSwap

@[simp]
theorem lift_mk {P : Type*} [TopologicalSpace P] [LocallyCompactSpace P]
    (Φ : ∀ n, C(P × (F.obj n × I), Z))
    (hΦ : ∀ n p k, Φ (n + 1) (p, (tmap F (Nat.le_add_right n 1) k, 0)) = Φ n (p, (k, 1)))
    (n : ℕ) (p : P) (k : F.obj n) (t : I) : lift F Φ hΦ (p, mk F n k t) = Φ n (p, (k, t)) :=
  rfl

/-- **Homotopies of maps out of the mapping telescope**, given block by block. -/
def homotopy {f₀ f₁ : C(MappingTelescope F, Z)} (Φ : ∀ n, C(I × (F.obj n × I), Z))
    (hΦ : ∀ n s k, Φ (n + 1) (s, (tmap F (Nat.le_add_right n 1) k, 0)) = Φ n (s, (k, 1)))
    (h₀ : ∀ n k t, Φ n (0, (k, t)) = f₀ (mk F n k t))
    (h₁ : ∀ n k t, Φ n (1, (k, t)) = f₁ (mk F n k t)) : f₀.Homotopy f₁ where
  toContinuousMap := lift F Φ hΦ
  map_zero_left z := by
    obtain ⟨n, k, t, rfl⟩ := exists_mk F z
    exact h₀ n k t
  map_one_left z := by
    obtain ⟨n, k, t, rfl⟩ := exists_mk F z
    exact h₁ n k t

theorem ext {f g : C(MappingTelescope F, Z)} (h : ∀ n k t, f (mk F n k t) = g (mk F n k t)) :
    f = g :=
  ContinuousMap.ext fun z => by
    obtain ⟨n, k, t, rfl⟩ := exists_mk F z
    exact h n k t

end Desc

/-! ### Levels and truncations -/

/-- The level `n + t` of the point `(k, t)_n`. -/
def level : C(MappingTelescope F, ℝ) :=
  desc F (fun n => ⟨fun q => n + q.2, continuous_const.add
    (continuous_subtype_val.comp continuous_snd)⟩) fun n k => by
    change ((n + 1 : ℕ) : ℝ) + ((0 : I) : ℝ) = n + ((1 : I) : ℝ)
    push_cast
    ring

@[simp]
theorem level_mk (n : ℕ) (k : F.obj n) (t : I) : level F (mk F n k t) = n + t :=
  rfl

theorem level_nonneg (z : MappingTelescope F) : 0 ≤ level F z := by
  obtain ⟨n, k, t, rfl⟩ := exists_mk F z
  rw [level_mk]
  exact add_nonneg (Nat.cast_nonneg n) t.2.1

/-- The truncation `T_n = {level ≤ n}`: the blocks `0, …, n - 1` and the bottom of the `n`-th. -/
def trunc (n : ℕ) : Set (MappingTelescope F) :=
  {z | level F z ≤ n}

theorem isClosed_trunc (n : ℕ) : IsClosed (trunc F n) :=
  isClosed_le (level F).continuous continuous_const

theorem monotone_trunc : Monotone (trunc F) := fun m n h z hz => by
  change level F z ≤ n
  exact le_trans hz (by exact_mod_cast h)

/-- **The mapping telescope is the homotopy direct limit of its truncations** (Lemma 2.1 with
`f = level + 1`). -/
theorem isHomotopyDirectLimit_trunc : IsHomotopyDirectLimit (trunc F) :=
  isHomotopyDirectLimit_of_level (monotone_trunc F)
    ⟨fun z => level F z + 1, (level F).continuous.add continuous_const⟩
    (fun z => by
      have := level_nonneg F z
      simp only [ContinuousMap.coe_mk]
      linarith)
    (fun n z hz => by
      have hz' : (n : ℝ) < level F z := not_le.1 hz
      simp only [ContinuousMap.coe_mk]
      linarith)

/-! ### Trajectories -/

/-- The point at height `s ∈ [0, d + 1]` above the bottom of the `m`-th block along the trajectory
of `k ∈ F_m`: `(k, s)_m` for `s ≤ 1`, then `(c_m(k), s - 1)_{m+1}`, and so on. -/
def traj : ℕ → ∀ m : ℕ, F.obj m → ℝ → MappingTelescope F
  | 0, m, k, s => mk F m k (clampI s)
  | d + 1, m, k, s => if s ≤ 1 then mk F m k (clampI s)
      else traj d (m + 1) (tmap F (Nat.le_add_right m 1) k) (s - 1)

theorem traj_of_le_one (d m : ℕ) (k : F.obj m) {s : ℝ} (hs : s ≤ 1) :
    traj F d m k s = mk F m k (clampI s) := by
  cases d with
  | zero => rfl
  | succ d => exact if_pos hs

theorem traj_zero_right (d m : ℕ) (k : F.obj m) : traj F d m k 0 = mk F m k 0 := by
  rw [traj_of_le_one F d m k zero_le_one, clampI_zero]

theorem continuous_traj (d : ℕ) : ∀ m : ℕ,
    Continuous fun q : F.obj m × ℝ => traj F d m q.1 q.2 := by
  induction d with
  | zero =>
    intro m
    exact (continuous_mk F m).comp (continuous_fst.prodMk (continuous_clampI.comp continuous_snd))
  | succ d ih =>
    intro m
    refine Continuous.if_le ?_ ?_ continuous_snd continuous_const ?_
    · exact (continuous_mk F m).comp (continuous_fst.prodMk
        (continuous_clampI.comp continuous_snd))
    · exact (ih (m + 1)).comp (((tmap F (Nat.le_add_right m 1)).continuous.comp
        continuous_fst).prodMk (continuous_snd.sub continuous_const))
    · intro q hq
      rw [hq, clampI_one, mk_one, sub_self, traj_zero_right]

theorem level_traj (d : ℕ) : ∀ (m : ℕ) (k : F.obj m) {s : ℝ}, 0 ≤ s → s ≤ d + 1 →
    level F (traj F d m k s) = m + s := by
  induction d with
  | zero =>
    intro m k s h0 h1
    simp only [traj, level_mk]
    rw [clampI_val h0 (by simpa using h1)]
  | succ d ih =>
    intro m k s h0 h1
    simp only [traj]
    split_ifs with h
    · rw [level_mk, clampI_val h0 h]
    · rw [ih (m + 1) _ (by linarith) (by push_cast at h1 ⊢; linarith)]
      push_cast
      ring

/-! ### Pushing the truncation `T_n` up to level `n` -/

/-- On the `m`-th block: `(k, t)_m ↦` the point at height `t + s · max(0, n - m - t)` on the
trajectory of `k`. -/
def pushFun (n m : ℕ) (q : I × (F.obj m × I)) : MappingTelescope F :=
  traj F (n - m) m q.2.1 (q.2.2 + q.1 * max 0 ((n : ℝ) - m - q.2.2))

theorem continuous_pushFun (n m : ℕ) : Continuous (pushFun F n m) := by
  have ht : Continuous fun q : I × (F.obj m × I) => ((q.2.2 : I) : ℝ) :=
    continuous_subtype_val.comp (continuous_snd.comp continuous_snd)
  exact (continuous_traj F (n - m) m).comp ((continuous_fst.comp continuous_snd).prodMk
    (ht.add ((continuous_subtype_val.comp continuous_fst).mul
      (continuous_const.max ((continuous_const.sub continuous_const).sub ht)))))

theorem pushFun_compat (n m : ℕ) (s : I) (k : F.obj m) :
    pushFun F n (m + 1) (s, (tmap F (Nat.le_add_right m 1) k, 0)) = pushFun F n m (s, (k, 1)) := by
  unfold pushFun
  simp only [Set.Icc.coe_zero, Set.Icc.coe_one, zero_add, sub_zero]
  push_cast
  rcases lt_or_ge m n with hmn | hmn
  · have hM : (0 : ℝ) ≤ max 0 ((n : ℝ) - (m + 1)) := le_max_left _ _
    have hsM : (0 : ℝ) ≤ s * max 0 ((n : ℝ) - (m + 1)) := mul_nonneg s.2.1 hM
    rw [show n - m = (n - (m + 1)) + 1 by omega, show (n : ℝ) - m - 1 = n - (m + 1) by ring]
    simp only [traj]
    split_ifs with h
    · have h0 : s * max 0 ((n : ℝ) - (m + 1)) = 0 := by linarith
      rw [h0, traj_zero_right, add_zero, clampI_one, mk_one]
    · congr 1
      ring
  · have h1 : n - m = 0 := by omega
    have h2 : n - (m + 1) = 0 := by omega
    have hmax : max 0 ((n : ℝ) - (m + 1)) = 0 :=
      max_eq_left (by have : (n : ℝ) ≤ m := by exact_mod_cast hmn
                      linarith)
    have hmax' : max 0 ((n : ℝ) - m - 1) = 0 :=
      max_eq_left (by have : (n : ℝ) ≤ m := by exact_mod_cast hmn
                      linarith)
    rw [h1, h2, hmax, hmax']
    simp only [mul_zero, add_zero, traj]
    rw [clampI_one, clampI_zero, mk_one]

/-- **The deformation of `T_n` to level `n`**, defined on the whole mapping telescope (it fixes
the levels `≥ n`). -/
def push (n : ℕ) : C(I × MappingTelescope F, MappingTelescope F) :=
  lift F (fun m => ⟨pushFun F n m, continuous_pushFun F n m⟩) fun m s k => pushFun_compat F n m s k

theorem push_mk (n m : ℕ) (s : I) (k : F.obj m) (t : I) :
    push F n (s, mk F m k t) = pushFun F n m (s, (k, t)) :=
  rfl

theorem push_zero (n : ℕ) (z : MappingTelescope F) : push F n (0, z) = z := by
  obtain ⟨m, k, t, rfl⟩ := exists_mk F z
  rw [push_mk]
  unfold pushFun
  rw [Set.Icc.coe_zero, zero_mul, add_zero, traj_of_le_one F _ m k t.2.2, clampI_coe]

theorem push_bottom (n : ℕ) (s : I) (k : F.obj n) : push F n (s, mk F n k 0) = mk F n k 0 := by
  rw [push_mk]
  unfold pushFun
  rw [Set.Icc.coe_zero, sub_self, sub_zero, max_self, mul_zero, add_zero, Nat.sub_self,
    traj_zero_right]

theorem level_push {n : ℕ} {z : MappingTelescope F} (hz : level F z ≤ n) (s : I) :
    level F (push F n (s, z)) = level F z + s * (n - level F z) := by
  obtain ⟨m, k, t, rfl⟩ := exists_mk F z
  rw [level_mk] at hz ⊢
  have hmn : m ≤ n := by
    have : (m : ℝ) ≤ n := by linarith [t.2.1]
    exact_mod_cast this
  rw [push_mk]
  unfold pushFun
  rw [max_eq_right (by linarith), level_traj F (n - m) m k
    (add_nonneg t.2.1 (mul_nonneg s.2.1 (by linarith)))]
  · ring
  · push_cast [hmn]
    nlinarith [s.2.1, s.2.2]

theorem push_mem_trunc {n : ℕ} {z : MappingTelescope F} (hz : z ∈ trunc F n) (s : I) :
    push F n (s, z) ∈ trunc F n := by
  change level F (push F n (s, z)) ≤ n
  have hz' : level F z ≤ n := hz
  rw [level_push F hz' s]
  nlinarith [s.2.1, s.2.2]

theorem level_push_one {n : ℕ} {z : MappingTelescope F} (hz : z ∈ trunc F n) :
    level F (push F n (1, z)) = n := by
  rw [level_push F hz 1, Set.Icc.coe_one]
  ring

/-! ### The bottom of the `n`-th block -/

/-- The value at level `n`: `(k, t)_m ↦ c_{m,n}(k)` if `m + t = n`, `none` otherwise. It is
compatible with the gluing, so it is defined on the mapping telescope. -/
def atLevel (n : ℕ) : MappingTelescope F → Option (F.obj n) :=
  Quot.lift (fun q => if h : q.1 ≤ n ∧ (q.1 : ℝ) + q.2.2 = n then some (tmap F h.1 q.2.1)
    else none) (by
    rintro _ _ ⟨m, k⟩
    simp only [Set.Icc.coe_one, Set.Icc.coe_zero, add_zero]
    by_cases hmn : m + 1 = n
    · have h1 : m ≤ n ∧ (m : ℝ) + 1 = n := ⟨by omega, by rw [← hmn]; push_cast; ring⟩
      have h2 : m + 1 ≤ n ∧ ((m + 1 : ℕ) : ℝ) = n := ⟨by omega, by rw [hmn]⟩
      rw [dif_pos h1, dif_pos h2, tmap_tmap]
    · have h1 : ¬ (m ≤ n ∧ (m : ℝ) + 1 = n) := fun h => hmn (by exact_mod_cast h.2)
      have h2 : ¬ (m + 1 ≤ n ∧ ((m + 1 : ℕ) : ℝ) = n) := fun h => hmn (by exact_mod_cast h.2)
      rw [dif_neg h1, dif_neg h2])

theorem atLevel_mk_zero (n : ℕ) (k : F.obj n) : atLevel F n (mk F n k 0) = some k := by
  change (if h : n ≤ n ∧ (n : ℝ) + ((0 : I) : ℝ) = n then some (tmap F h.1 k) else none) = some k
  rw [dif_pos ⟨le_rfl, by simp⟩, tmap_refl]

theorem mk_zero_injective (n : ℕ) : Injective fun k : F.obj n => mk F n k 0 := by
  intro k k' h
  have := congrArg (atLevel F n) h
  simp only [atLevel_mk_zero, Option.some.injEq] at this
  exact this

theorem exists_mk_zero_of_level {n : ℕ} {z : MappingTelescope F} (hz : level F z = n) :
    ∃ k, mk F n k 0 = z := by
  obtain ⟨m, k, t, rfl⟩ := exists_mk F z
  rw [level_mk] at hz
  rcases eq_or_lt_of_le t.2.2 with ht | ht
  · have hmn : m + 1 = n := by
      have : (m : ℝ) + 1 = n := by rw [← ht]; exact hz
      exact_mod_cast this
    subst hmn
    refine ⟨tmap F (Nat.le_add_right m 1) k, ?_⟩
    rw [show t = 1 from Subtype.ext ht, mk_one]
  · have hmn : m = n := by
      have h1 : (m : ℝ) ≤ n := by linarith [t.2.1]
      have h2 : (n : ℝ) < m + 1 := by linarith
      have h1' : m ≤ n := by exact_mod_cast h1
      have h2' : n < m + 1 := by exact_mod_cast h2
      omega
    subst hmn
    have ht0 : t = 0 := Subtype.ext (by simp only [Set.Icc.coe_zero]; linarith)
    exact ⟨k, by rw [ht0]⟩

/-- **`k ↦ (k, 0)_n` is an embedding.** For an open `V ⊆ F_n`, the points within `1/2` of level
`n` whose image at level `n` lies in `V` form a saturated open subset of `⨆_m F_m × [0, 1]`. -/
theorem isInducing_mk_zero (n : ℕ) : IsInducing fun k : F.obj n => mk F n k 0 := by
  have hcont : Continuous fun k : F.obj n => mk F n k 0 :=
    (continuous_mk F n).comp (continuous_id.prodMk continuous_const)
  refine ⟨le_antisymm (continuous_iff_le_induced.1 hcont) ?_⟩
  rw [TopologicalSpace.le_def]
  intro V hV
  let S : Set (Σ m : ℕ, F.obj m × I) :=
    {q | ∃ h : q.1 ≤ n, |(q.1 : ℝ) + q.2.2 - n| < 1 / 2 ∧ tmap F h q.2.1 ∈ V}
  have hS : ∀ a b, MapTelRel F a b → (a ∈ S ↔ b ∈ S) := by
    rintro _ _ ⟨m, k⟩
    simp only [S, mem_ofPred_eq, Set.Icc.coe_one, Set.Icc.coe_zero, add_zero]
    constructor
    · rintro ⟨h, h1, h2⟩
      have hmn : m + 1 = n := by
        have : |((m + 1 : ℕ) : ℝ) - n| < 1 / 2 := by push_cast; exact h1
        have h3 : ((m + 1 : ℕ) : ℝ) - n < 1 / 2 := (abs_lt.1 this).2
        have h4 : -(1 / 2 : ℝ) < ((m + 1 : ℕ) : ℝ) - n := (abs_lt.1 this).1
        have h5 : ((m + 1 : ℕ) : ℝ) < n + 1 := by linarith
        have h6 : (n : ℝ) < (m + 1 : ℕ) + 1 := by linarith
        have h5' : m + 1 < n + 1 := by exact_mod_cast h5
        have h6' : n < m + 1 + 1 := by exact_mod_cast h6
        omega
      refine ⟨by omega, by push_cast; exact h1, ?_⟩
      rw [tmap_tmap]
      exact h2
    · rintro ⟨h, h1, h2⟩
      refine ⟨by omega, by push_cast at h1; exact h1, ?_⟩
      rw [tmap_tmap] at h2
      exact h2
  let P : MappingTelescope F → Prop := Quot.lift (· ∈ S) fun a b h => propext (hS a b h)
  have hW : IsOpen {z : MappingTelescope F | P z} := by
    rw [← (isQuotientMap_quotMk F).isCoinducing.isOpen_preimage]
    change IsOpen S
    rw [isOpen_sigma_iff]
    intro m
    by_cases hm : m ≤ n
    · have : Sigma.mk m ⁻¹' S = {p : F.obj m × I | |(m : ℝ) + p.2 - n| < 1 / 2} ∩
          (Prod.fst ⁻¹' (tmap F hm ⁻¹' V)) := by
        ext p
        simp only [S, mem_preimage, mem_ofPred_eq, mem_inter_iff]
        exact ⟨fun ⟨_, h1, h2⟩ => ⟨h1, h2⟩, fun ⟨h1, h2⟩ => ⟨hm, h1, h2⟩⟩
      rw [this]
      refine IsOpen.inter (isOpen_lt (continuous_abs.comp ((continuous_const.add
        (continuous_subtype_val.comp continuous_snd)).sub continuous_const))
          continuous_const) ?_
      exact (hV.preimage (tmap F hm).continuous).preimage continuous_fst
    · have : Sigma.mk m ⁻¹' S = ∅ := by
        ext p
        simp only [S, mem_preimage, mem_ofPred_eq, mem_empty_iff_false, iff_false]
        exact fun ⟨h, _⟩ => hm h
      rw [this]
      exact isOpen_empty
  refine isOpen_induced_iff.2 ⟨_, hW, ?_⟩
  ext k
  change (⟨n, k, 0⟩ : Σ m : ℕ, F.obj m × I) ∈ S ↔ k ∈ V
  simp only [S, mem_ofPred_eq, Set.Icc.coe_zero, add_zero, sub_self, abs_zero]
  constructor
  · rintro ⟨h, -, h2⟩
    rwa [tmap_refl] at h2
  · intro hk
    exact ⟨le_rfl, by norm_num, by rwa [tmap_refl]⟩

/-! ### (T2) for the mapping telescope -/

theorem mk_zero_mem_trunc (n : ℕ) (k : F.obj n) : mk F n k 0 ∈ trunc F n := by
  change level F (mk F n k 0) ≤ n
  simp

/-- `F_n → T_n`, `k ↦ (k, 0)_n`. -/
def levelIncl (n : ℕ) : C(F.obj n, trunc F n) where
  toFun k := ⟨mk F n k 0, mk_zero_mem_trunc F n k⟩
  continuous_toFun :=
    ((continuous_mk F n).comp (continuous_id.prodMk continuous_const)).subtype_mk _

theorem push_one_eq (n : ℕ) (z : trunc F n) : ∃ k, mk F n k 0 = push F n (1, z) :=
  exists_mk_zero_of_level F (level_push_one F z.2)

/-- `T_n → F_n`: push to level `n`, and read off the point of `F_n`. -/
def levelRetract (n : ℕ) : C(trunc F n, F.obj n) where
  toFun z := Classical.choose (push_one_eq F n z)
  continuous_toFun := by
    rw [(isInducing_mk_zero F n).continuous_iff]
    have : ((fun k : F.obj n => mk F n k 0) ∘ fun z : trunc F n =>
        Classical.choose (push_one_eq F n z)) =
          fun z : trunc F n => push F n (1, (z : MappingTelescope F)) :=
      funext fun z => Classical.choose_spec (push_one_eq F n z)
    rw [this]
    exact (push F n).continuous.comp (continuous_const.prodMk continuous_subtype_val)

theorem mk_levelRetract (n : ℕ) (z : trunc F n) :
    mk F n (levelRetract F n z) 0 = push F n (1, z) :=
  Classical.choose_spec (push_one_eq F n z)

theorem levelRetract_levelIncl (n : ℕ) (k : F.obj n) :
    levelRetract F n (levelIncl F n k) = k := by
  apply mk_zero_injective F n
  change mk F n (levelRetract F n (levelIncl F n k)) 0 = mk F n k 0
  rw [mk_levelRetract]
  exact push_bottom F n 1 k

theorem levelRetract_comp_levelIncl (n : ℕ) :
    (levelRetract F n).comp (levelIncl F n) = ContinuousMap.id _ :=
  ContinuousMap.ext fun k => levelRetract_levelIncl F n k

/-- Pushing `T_n` up to level `n` is a homotopy from the identity to `levelIncl ∘ levelRetract`. -/
theorem levelIncl_comp_levelRetract (n : ℕ) :
    ((levelIncl F n).comp (levelRetract F n)).Homotopic (ContinuousMap.id _) := by
  refine ContinuousMap.Homotopic.symm ⟨⟨⟨fun q => ⟨push F n (q.1, q.2),
    push_mem_trunc F q.2.2 _⟩, ?_⟩, ?_, ?_⟩⟩
  · exact ((push F n).continuous.comp (continuous_fst.prodMk
      (continuous_subtype_val.comp continuous_snd))).subtype_mk _
  · intro z
    exact Subtype.ext (push_zero F n z)
  · intro z
    exact Subtype.ext (mk_levelRetract F n z).symm

/-- **(T2) for mapping telescopes**: `k ↦ (k, 0)_n` is a homotopy equivalence `F_n → T_n`. -/
theorem isHomotopyEquiv_levelIncl (n : ℕ) : IsHomotopyEquiv (levelIncl F n) :=
  ⟨levelRetract F n, by rw [levelRetract_comp_levelIncl], levelIncl_comp_levelRetract F n⟩

theorem isHomotopyEquiv_levelRetract (n : ℕ) : IsHomotopyEquiv (levelRetract F n) :=
  IsHomotopyEquiv.of_inverse (by rw [levelRetract_comp_levelIncl]) (levelIncl_comp_levelRetract F n)

end MappingTelescope

end Morse
