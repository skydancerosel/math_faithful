import Morse
import RoundTrip.Check
import RoundTrip.Blind.V8_13
import RoundTrip.Bridge
import RoundTrip.EnergyC2

open Set Filter Topology Function
open scoped ContDiff Manifold
open Bundle

namespace RoundTrip.V8_13

/-- The project's statement (universes instantiated at 0), for a slice submanifold `N ⊆ V` with
the induced metric: **Theorem 13.1** — for every 2-parameter variation `α : ℝ × ℝ → ℝ → V`
(`IsVariation`, open `U ⊆ ℝ²`, any break set) of an unbroken geodesic `γ`, the iterated
derivative `∂/∂u₁ (∂E(α(u₁, u₂))/∂u₂ |_{u₂ = 0})` at `u₁ = 0` exists and equals
`2 secondVariation γ W₁ W₂` (Milnor's right side, `W₁ = ∂α/∂u₁`, `W₂ = ∂α/∂u₂`, jumps
`P(Δ_t W₁')`, `R = curvR`); and its consequence that this iterated derivative depends only on
`W₁, W₂` on `[0, 1]`. -/
def A : Prop :=
  type_of% @Morse.second_variation.{0,0,0} ∧ type_of% @Morse.second_variation_eq.{0,0,0}

theorem A_holds : A := ⟨@Morse.second_variation, @Morse.second_variation_eq⟩

/-! Neither `A → B` nor `B → A` is proved; see `V8_13.json`.

* Abstract setting: B quantifies over abstract connected Riemannian `ℝⁿ`-manifolds with any
  Levi-Civita connection; A is about slice submanifolds `N ⊆ V` with the induced metric.
* Even on embedded manifolds (`B_emb` below), the two statements use different notions of the
  second derivative, and neither side proves the analytic fact that would identify them:
  B's `mixedD F = ∂/∂u₂ (fderiv F u e₀)` at `0` is built from the Fréchet derivative of
  `F = E ∘ α : ℝ² → ℝ`, and B asserts that `u ↦ fderiv F u e₀` is Fréchet differentiable at `0`;
  A's quantity is the iterated *line* derivative `∂/∂u₁ (∂F/∂u₂ (u₁, 0))` along the axis `u₂ = 0`
  (in the other order). `fderiv F u` is a junk `0` wherever `F` is not Fréchet differentiable,
  so neither statement implies the other without knowing that `F` is `C¹` near `0` (for
  `B_emb → A`) resp. `C²` near `0` (for `A → B_emb`: Fréchet differentiability of
  `u ↦ ∂F/∂u₁ (u)`). `E ∘ α` is in fact `C^∞` (differentiation under the integral sign on the
  closed strips, in two parameters), but the project only differentiates `E` along 1-parameter
  lines (`Morse.IsVariation.hasDerivAt_energy`, Theorem 12.2). Given that lemma the order of
  the partial derivatives is handled by the symmetry of the second variation
  (`Morse.secondVariation_eq_hessForm`, `Morse.hessForm_comm`, not part of A), and the rest is
  dictionary glue (2-parameter variations, `varField`, covariant derivatives on the pieces, jumps
  of `DW₁/dt` vs `P(Δ_t W₁')`, sums of piece integrals, `IsCurvVal` vs `curvR`). -/

/-- B on embedded manifolds: `M = ↥N` with the induced metric and the induced Levi-Civita
connection (a special case of B, see `B_to_B_emb`). -/
def B_emb : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (W : Type) [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] (n : ℕ)
    (N : Set V) (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N)
    [ConnectedSpace (Bridge.Sub hN)],
    ∀ (U : Set (Rn 2)) (α : Rn 2 → ℝ → Bridge.Sub hN) (k : ℕ) (t : ℕ → ℝ),
      IsVarSub (n := n) U α k t →
    IsGeodesic (Bridge.conn (hN := hN)) (α 0) (Set.Icc 0 1) →
    ∀ (D1 D2 : ℕ → FA n (α 0)) (Rv : FA n (α 0)),
      (∀ i < k, HasCovDeriv (Bridge.conn (hN := hN)) (α 0) (Set.Icc (t i) (t (i + 1)))
          (varField (n := n) α 0) (D1 i) ∧
        HasCovDeriv (Bridge.conn (hN := hN)) (α 0) (Set.Icc (t i) (t (i + 1))) (D1 i) (D2 i)) →
      (∀ s ∈ Set.Icc (0 : ℝ) 1, IsCurvVal (Bridge.conn (hN := hN)) (α 0 s)
        (vel (n := n) (α 0) (Set.Icc 0 1) s)
        (varField (n := n) α 0 s) (vel (n := n) (α 0) (Set.Icc 0 1) s) (Rv s)) →
      DifferentiableAt ℝ (fun u : Rn 2 => fderiv ℝ (fun v : Rn 2 => Efun (n := n) (α v)) u
        (EuclideanSpace.single 0 (1 : ℝ))) 0 ∧
      (1 / 2 : ℝ) * mixedD (fun v : Rn 2 => Efun (n := n) (α v)) =
        - (∑ i ∈ Finset.Ico 1 k, inner ℝ (varField (n := n) α 1 (t i)) (D1 i (t i) - D1 (i - 1) (t i)))
        - ∑ i ∈ Finset.range k, ∫ s in (t i)..(t (i + 1)),
            inner ℝ (varField (n := n) α 1 s) (D2 i s + Rv s)

/-- `B_emb` is a special case of B (the induced connection is Levi-Civita, `Bridge.conn_isLC`). -/
theorem B_to_B_emb : B → B_emb := fun hB _ _ _ _ _ _ _ _ n _ hN _ =>
  hB n (Bridge.Sub hN) (Bridge.conn (hN := hN)) Bridge.conn_isLC

/-! ## Second attempt (with `RoundTrip.EnergyC2`): the variational `E_**` on embedded manifolds

Dictionary for 2-parameter variations on `↥N` (namespace `Emb`): a blind `IsVarSub U α k t`
(`U ⊆ ℝ²`) is a project `IsVariation` of the ambient family `amb α`; its fields are the line
derivatives along `r ↦ r eᵢ` (`D_varField`); by `EnergyC2`, `u ↦ E(α u)` is `C^∞`, so the
blind `DifferentiableAt` clause holds and `mixedD` is the project's iterated derivative
(`hess_data`); hence every blind `IsHess` value is `2 secondVariation` of the ambient fields
(`hess_eq`, from Theorem 13.1 taken as the hypothesis `SV hN`). Conversely every pair of blind
fields `W₁, W₂ ∈ TΩ_γ` has an `IsHess` value (`exists_isHess`): Lemma 11.A
(`Morse.exists_variation` with `P = ℝ²`) gives `α(u, t) = exp_{γ(t)}(u₀ W₁(t) + u₁ W₂(t))`, and
the same formula has the prescribed `∂α/∂uᵢ (0, t)` at every `t ∈ ℝ` (blind `IsHess` matches the
fields on all of `ℝ`), since `exp` is smooth near the zero section with `d(exp_q)₀ = id`. -/

namespace Emb

set_option linter.unusedSectionVars false

/-- `e₀, e₁ ∈ ℝ²`. -/
noncomputable abbrev e0 : Rn 2 := EuclideanSpace.single 0 (1 : ℝ)
noncomputable abbrev e1 : Rn 2 := EuclideanSpace.single 1 (1 : ℝ)

/-! ### Subdivisions (copied from `Items/V8_9.lean`, `Items/V8_10.lean`) -/

theorem exists_piece_of_mem {k : ℕ} {t : ℕ → ℝ} (h0 : t 0 = 0) (hk : t k = 1)
    (hlt : ∀ i < k, t i < t (i + 1)) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    ∃ i < k, s ∈ Icc (t i) (t (i + 1)) := by
  classical
  have hk0 : k ≠ 0 := by rintro rfl; rw [h0] at hk; exact zero_ne_one hk
  have hP : ∃ j, s ≤ t j ∧ j ≤ k := ⟨k, hk ▸ hs.2, le_rfl⟩
  have hm := Nat.find_spec hP
  by_cases hm0 : Nat.find hP = 0
  · refine ⟨0, Nat.pos_of_ne_zero hk0, ?_, ?_⟩
    · rw [h0]; exact hs.1
    · have : s ≤ t 0 := by rw [← hm0]; exact hm.1
      exact this.trans (hlt 0 (Nat.pos_of_ne_zero hk0)).le
  · refine ⟨Nat.find hP - 1, by omega, ?_, ?_⟩
    · by_contra hcon
      exact Nat.find_min hP (Nat.sub_lt (Nat.pos_of_ne_zero hm0) one_pos)
        ⟨(lt_of_not_ge hcon).le, by omega⟩
    · rw [Nat.sub_add_cancel (Nat.pos_of_ne_zero hm0)]; exact hm.1

theorem exists_piece_of_subdiv {t : ℕ → ℝ} {k : ℕ} (h0 : t 0 = 0) (hk : t k = 1)
    (hlt : ∀ i < k, t i < t (i + 1)) {s u : ℝ} (hs : 0 ≤ s) (hsu : s < u) (hub : u ≤ 1)
    (hB : ∀ x ∈ (Finset.range (k + 1)).image t, x ∉ Ioo s u) :
    ∃ i < k, t i ≤ s ∧ u ≤ t (i + 1) := by
  have hP : ∃ j, s < t j ∧ j ≤ k := ⟨k, by rw [hk]; linarith, le_rfl⟩
  classical
  set m := Nat.find hP
  have hm : s < t m ∧ m ≤ k := Nat.find_spec hP
  have hm0 : m ≠ 0 := by
    intro h; have := hm.1; rw [h, h0] at this; linarith
  have hi : t (m - 1) ≤ s := by
    by_contra hcon
    exact Nat.find_min hP (Nat.sub_lt (Nat.pos_of_ne_zero hm0) one_pos)
      ⟨lt_of_not_ge hcon, by omega⟩
  have hu : u ≤ t m := by
    by_contra hcon
    exact hB (t m) (Finset.mem_image.2 ⟨m, Finset.mem_range.2 (by omega), rfl⟩)
      ⟨hm.1, lt_of_not_ge hcon⟩
  have hm1 : m - 1 + 1 = m := Nat.sub_add_cancel (Nat.pos_of_ne_zero hm0)
  exact ⟨m - 1, by omega, hi, hm1.symm ▸ hu⟩

/-- A subdivision `0 = t₀ < ⋯ < t_k = 1` whose open pieces avoid a finite set `B`. -/
theorem exists_subdiv (B : Finset ℝ) : ∃ (k : ℕ) (t : ℕ → ℝ), t 0 = 0 ∧ t k = 1 ∧
    (∀ i < k, t i < t (i + 1)) ∧
    ∀ i < k, 0 ≤ t i ∧ t (i + 1) ≤ 1 ∧ ∀ x ∈ B, x ∉ Ioo (t i) (t (i + 1)) := by
  classical
  have hlt : (0 : ℝ) < 1 := zero_lt_one
  set a : ℝ := 0
  set b : ℝ := 1
  set S : Finset ℝ := insert a (insert b (B.filter (· ∈ Ioo a b)))
  have hS : ∀ x ∈ S, a ≤ x ∧ x ≤ b := by
    intro x hx
    simp only [S, Finset.mem_insert, Finset.mem_filter] at hx
    rcases hx with rfl | rfl | ⟨-, hx⟩
    · exact ⟨le_rfl, hlt.le⟩
    · exact ⟨hlt.le, le_rfl⟩
    · exact ⟨hx.1.le, hx.2.le⟩
  have haS : a ∈ S := Finset.mem_insert_self _ _
  have hbS : b ∈ S := Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  set m := S.card
  have hm : 1 < m := Finset.one_lt_card.2 ⟨a, haS, b, hbS, hlt.ne⟩
  set e := S.orderEmbOfFin rfl
  set t : ℕ → ℝ := fun j => if h : j < m then e ⟨j, h⟩ else b
  have ht : ∀ j (h : j < m), t j = e ⟨j, h⟩ := fun j h => dif_pos h
  refine ⟨m - 1, t, ?_, ?_, ?_, ?_⟩
  · rw [ht 0 (by omega), Finset.orderEmbOfFin_zero rfl (by omega)]
    exact le_antisymm (Finset.min'_le _ _ haS) ((hS _ (Finset.min'_mem _ _)).1)
  · rw [ht (m - 1) (by omega), Finset.orderEmbOfFin_last rfl (by omega)]
    exact le_antisymm ((hS _ (Finset.max'_mem _ _)).2) (Finset.le_max' _ _ hbS)
  · intro i hi
    rw [ht i (by omega), ht (i + 1) (by omega)]
    exact e.strictMono (Fin.mk_lt_mk.2 (Nat.lt_succ_self i))
  · intro i hi
    rw [ht i (by omega), ht (i + 1) (by omega)]
    refine ⟨(hS _ (Finset.orderEmbOfFin_mem _ _ _)).1, (hS _ (Finset.orderEmbOfFin_mem _ _ _)).2,
      fun x hx hxi => ?_⟩
    have hxS : x ∈ S := Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
      (Finset.mem_filter.2 ⟨hx, (hS _ (Finset.orderEmbOfFin_mem _ _ _)).1.trans_lt hxi.1,
        hxi.2.trans_le (hS _ (Finset.orderEmbOfFin_mem _ _ _)).2⟩))
    obtain ⟨j, rfl⟩ : x ∈ Set.range e := by
      rw [Finset.range_orderEmbOfFin]; exact hxS
    have h1 := e.lt_iff_lt.1 hxi.1
    have h2 := e.lt_iff_lt.1 hxi.2
    rw [Fin.lt_def] at h1 h2
    simp only at h1 h2
    omega

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] {n : ℕ} {N : Set V}
  {hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N}

/-! ### Maps into `↥N` (copied from `Items/V8_10.lean`, `Items/V8_12.lean`) -/

theorem contMDiffWithinAt_map_iff {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → Bridge.Sub hN} {s : Set E} {x : E} :
    ContMDiffWithinAt 𝓘(ℝ, E) 𝓘(ℝ, Rn n) ∞ f s x ↔
      ContDiffWithinAt ℝ ∞ (Bridge.incl hN ∘ f) s x := by
  constructor
  · intro h
    exact contMDiffWithinAt_iff_contDiffWithinAt.1
      ((Bridge.contMDiff_incl (f x)).comp_contMDiffWithinAt x h)
  · intro h
    have hcont : ContinuousWithinAt f s x :=
      (Topology.IsInducing.subtypeVal.continuousWithinAt_iff (f := f)).2 h.continuousWithinAt
    rw [contMDiffWithinAt_iff_target]
    refine ⟨hcont, ?_⟩
    set σ := Morse.sliceAt hN (f x)
    have hφ : ContDiffAt ℝ ∞ (fun y => (σ.φ y).1) (Bridge.incl hN (f x)) :=
      contDiff_fst.contDiffAt.comp _ ((Milnor.Problems.sliceChart_contDiffOn σ).contDiffAt
        (σ.φ.open_source.mem_nhds (Morse.mem_sliceAt_source hN (f x))))
    have e : (extChartAt 𝓘(ℝ, Rn n) (f x) ∘ f) =
        (fun y => (σ.φ y).1) ∘ (Bridge.incl hN ∘ f) := rfl
    rw [e]
    exact contMDiffWithinAt_iff_contDiffWithinAt.2 (hφ.comp_contDiffWithinAt x h)

theorem contMDiffOn_map_iff {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → Bridge.Sub hN} {s : Set E} :
    ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, Rn n) ∞ f s ↔ ContDiffOn ℝ ∞ (Bridge.incl hN ∘ f) s :=
  forall₂_congr fun _ _ => contMDiffWithinAt_map_iff

/-- The derivative of a map from a normed space into `N`, read in `V`. -/
theorem D_mfderiv_map {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → Bridge.Sub hN}
    {x : E} (hf : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, Rn n) f x) (v : E) :
    Bridge.D hN (f x) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, Rn n) f x v) = fderiv ℝ (Bridge.incl hN ∘ f) x v := by
  have h := HasMFDerivAt.comp x
    ((Bridge.contMDiff_incl (f x)).mdifferentiableAt (by simp)).hasMFDerivAt hf.hasMFDerivAt
  have h' : HasFDerivAt (Bridge.incl hN ∘ f)
      ((Bridge.D hN (f x)).comp (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, Rn n) f x : E →L[ℝ] Rn n)) x :=
    hasMFDerivAt_iff_hasFDerivAt.1 h
  have h'' : fderiv ℝ (Bridge.incl hN ∘ f) x =
      (Bridge.D hN (f x)).comp (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, Rn n) f x : E →L[ℝ] Rn n) :=
    HasFDerivAt.fderiv h'
  exact (DFunLike.congr_fun h'' v).symm

/-- A map into `N` that is `C^∞` at `x` when read in `V` has its derivative read in `V`. -/
theorem D_mfderiv_of_contDiffAt {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → Bridge.Sub hN} {x : E} (hf : ContDiffAt ℝ ∞ (Bridge.incl hN ∘ f) x) (v : E) :
    Bridge.D hN (f x) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, Rn n) f x v) = fderiv ℝ (Bridge.incl hN ∘ f) x v := by
  have : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, Rn n) ∞ f x := by
    rw [← contMDiffWithinAt_univ]
    exact contMDiffWithinAt_map_iff.2 (contDiffWithinAt_univ.2 hf)
  exact D_mfderiv_map (this.mdifferentiableAt (by simp)) v

/-! ### Paths, geodesics and `TΩ` -/

/-- A blind geodesic on `[0, 1]` (induced connection) is a project unbroken geodesic. -/
theorem isUnbrokenGeodesic_of_isGeodesic {pw : ℝ → Bridge.Sub hN}
    (h : IsGeodesic (Bridge.conn (hN := hN)) pw (Icc 0 1)) :
    Morse.IsUnbrokenGeodesic hN (Bridge.incl hN ∘ pw) := by
  have h' : RoundTrip.BridgePrelude.IsGeodesic (Bridge.conn (hN := hN)) pw (Icc 0 1) := h
  exact ⟨(Bridge.isGeodesic_iff.1 h').2.1, Bridge.isGeodesicOn_Ioo h'⟩

theorem mem_pathSpace_of_isGeodesic {pw : ℝ → Bridge.Sub hN}
    (h : IsGeodesic (Bridge.conn (hN := hN)) pw (Icc 0 1)) :
    Bridge.incl hN ∘ pw ∈ Morse.pathSpace N (Bridge.incl hN (pw 0)) (Bridge.incl hN (pw 1)) := by
  have hcd := (isUnbrokenGeodesic_of_isGeodesic h).1
  exact ⟨⟨zero_le_one, hcd.continuousOn, ∅, fun s u hs _ hu _ => hcd.mono (Icc_subset_Icc hs hu)⟩,
    fun t _ => (pw t).2, rfl, rfl⟩

/-- **Dictionary: `TΩ_γ`, blind ⇒ project.** The ambient field of a blind `W ∈ TΩ_γ` lies in
`Morse.pathTangent`. -/
theorem mem_pathTangent_of_inTOmega {γ : ℝ → Bridge.Sub hN} {X : FA n γ}
    (h : InTOmega (n := n) γ X) :
    Bridge.ambA γ X ∈ Morse.pathTangent hN (Bridge.incl hN ∘ γ) := by
  obtain ⟨⟨k, t, ht0, htk, hlt, -, hsm⟩, hX0, hX1⟩ := h
  have hsm' : ∀ i < k, ContDiffOn ℝ ∞ (Bridge.ambA γ X) (Icc (t i) (t (i + 1))) := fun i hi => by
    have h' : RoundTrip.BridgePrelude.IsSmoothAlong γ (Icc (t i) (t (i + 1))) X := hsm i hi
    exact (Bridge.isSmoothAlong_iff.1 h').2
  have hpiece : ∀ s u, 0 ≤ s → s < u → u ≤ 1 →
      (∀ x ∈ (Finset.range (k + 1)).image t, x ∉ Ioo s u) →
      ContDiffOn ℝ ∞ (Bridge.ambA γ X) (Icc s u) := by
    intro s u hs hsu hu hB
    obtain ⟨i, hi, hti, hui⟩ := exists_piece_of_subdiv ht0 htk hlt hs hsu hu hB
    exact (hsm' i hi).mono (Icc_subset_Icc hti hui)
  refine (Morse.mem_pathTangent hN).2 ⟨⟨zero_le_one, Morse.continuousOn_of_piecewise
    fun s u hs hsu hu hB => (hpiece s u hs hsu hu hB).continuousOn, _, hpiece⟩,
    fun τ _ => (Morse.prj_eq_self_iff hN (γ τ).2).2 (Bridge.D_mem (γ τ) (X τ)), ?_, ?_⟩
  · show Bridge.D hN (γ 0) (X 0) = 0
    rw [hX0]; exact map_zero _
  · show Bridge.D hN (γ 1) (X 1) = 0
    rw [hX1]; exact map_zero _

/-! ### 2-parameter variations -/

/-- The ambient family `(u, s) ↦ α(u, s) ∈ N ⊆ V`. -/
def amb {m : ℕ} (α : Rn m → ℝ → Bridge.Sub hN) : Rn m → ℝ → V := fun u s => Bridge.incl hN (α u s)

/-- **Dictionary: variations.** A blind `m`-parameter variation is a project `IsVariation`
(parameters in `U ⊆ ℝᵐ`, break points the subdivision points). -/
theorem isVariation_of_isVarSub {m : ℕ} {U : Set (Rn m)} {α : Rn m → ℝ → Bridge.Sub hN} {k : ℕ}
    {t : ℕ → ℝ} (h : IsVarSub (n := n) U α k t) :
    Morse.IsVariation N U (amb α) ((Finset.range (k + 1)).image t) := by
  obtain ⟨hU, h0U, ht0, htk, hlt, hend, hsm⟩ := h
  refine ⟨hU, h0U, fun _ _ _ _ => (α _ _).2, fun x hx => ?_, fun x hx => ?_,
    fun s u hs hsu hu hB => ?_⟩
  · show Bridge.incl hN (α x 0) = Bridge.incl hN (α 0 0)
    rw [(hend _ hx).2.1]
  · show Bridge.incl hN (α x 1) = Bridge.incl hN (α 0 1)
    rw [(hend _ hx).2.2]
  · obtain ⟨i, hi, hti, hui⟩ := exists_piece_of_subdiv ht0 htk hlt hs hsu hu hB
    exact (contMDiffOn_map_iff.1 (hsm i hi)).mono
      fun p hp => ⟨hp.1, hti.trans hp.2.1, hp.2.2.trans hui⟩

/-- **Dictionary: variation fields.** `Wᵢ = ∂α/∂uᵢ (0, τ)`, read in `V`, is the derivative along
the line `r ↦ r eᵢ`, for `τ ∈ [0, 1]`. -/
theorem D_varField {m : ℕ} {U : Set (Rn m)} {α : Rn m → ℝ → Bridge.Sub hN} {k : ℕ}
    {t : ℕ → ℝ} (hα : IsVarSub (n := n) U α k t) (i : Fin m) {τ : ℝ} (hτ : τ ∈ Icc (0 : ℝ) 1) :
    Bridge.D hN (α 0 τ) (varField (n := n) α i τ) =
      deriv (fun r : ℝ => amb α (r • EuclideanSpace.single i (1 : ℝ)) τ) 0 := by
  obtain ⟨hU, h0U, ht0, htk, hlt, -, hsm⟩ := hα
  obtain ⟨j, hj, hτj⟩ := exists_piece_of_mem ht0 htk hlt hτ
  have hG : ContDiffOn ℝ ∞ (Bridge.incl hN ∘ fun x : Rn m × ℝ => α x.1 x.2)
      (U ×ˢ Icc (t j) (t (j + 1))) := contMDiffOn_map_iff.1 (hsm j hj)
  have hcd : ContDiffAt ℝ ∞ (Bridge.incl hN ∘ fun u => α u τ) 0 :=
    (hG.comp (contDiff_id.prodMk contDiff_const).contDiffOn fun u hu => ⟨hu, hτj⟩).contDiffAt
      (hU.mem_nhds h0U)
  have h1 := D_mfderiv_of_contDiffAt hcd (EuclideanSpace.single i (1 : ℝ))
  have h2 := RoundTrip.EnergyC2.hasDerivAt_line (hcd.differentiableAt (by simp))
    (EuclideanSpace.single i (1 : ℝ))
  simp only [zero_add] at h2
  exact h1.trans h2.deriv.symm

/-- The blind energy of `α u` is the project energy of the ambient path. -/
theorem efun_eq {m : ℕ} (α : Rn m → ℝ → Bridge.Sub hN) :
    (fun v : Rn m => Efun (n := n) (α v)) = fun v => Morse.energy (amb α v) 0 1 :=
  funext fun v => Bridge.energy_eq (α v) 0 1

/-- **`E ∘ α` is `C²` (EnergyC2)**: the blind `DifferentiableAt` clause of `IsHess` holds for every
blind 2-parameter variation, and the blind `mixedD` is the project's iterated derivative
`∂/∂u₁ ∂/∂u₂ E(α(u₁ e₀ + u₂ e₁))` at `0`. -/
theorem hess_data {U : Set (Rn 2)} {α : Rn 2 → ℝ → Bridge.Sub hN} {k : ℕ} {t : ℕ → ℝ}
    (hα : IsVarSub (n := n) U α k t) :
    DifferentiableAt ℝ (fun u : Rn 2 => fderiv ℝ (fun v : Rn 2 => Efun (n := n) (α v)) u e0) 0 ∧
    mixedD (fun v : Rn 2 => Efun (n := n) (α v)) =
      deriv (fun s : ℝ => deriv (fun r : ℝ => Morse.energy (amb α (s • e0 + r • e1)) 0 1) 0) 0 := by
  have hvar := isVariation_of_isVarSub hα
  have hF : ContDiffOn ℝ 2 (fun v => Morse.energy (amb α v) 0 1) U :=
    hvar.contDiffOn_energy.of_le ENat.LEInfty.out
  rw [efun_eq]
  refine ⟨RoundTrip.EnergyC2.differentiableAt_fderiv_apply hvar.isOpen hF hvar.zero_mem e0, ?_⟩
  have h := RoundTrip.EnergyC2.fderiv_fderiv_apply_eq_deriv_deriv hvar.isOpen hF hvar.zero_mem
    e0 e1
  simp only [zero_add] at h
  exact h

/-- Theorem 13.1 for `N` (the statement of `Morse.second_variation`, or of
`Morse.hasDerivAt_energyHessian` unfolded), taken as a hypothesis. -/
def SV (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N) : Prop :=
  ∀ {γ : ℝ → V} {p q : V}, γ ∈ Morse.pathSpace N p q → Morse.IsUnbrokenGeodesic hN γ →
    ∀ {U : Set (ℝ × ℝ)} {α : ℝ × ℝ → ℝ → V} {B : Finset ℝ}, Morse.IsVariation N U α B →
    (∀ t ∈ Icc (0 : ℝ) 1, α 0 t = γ t) →
    HasDerivAt (fun u₁ => deriv (fun u₂ => Morse.energy (α (u₁, u₂)) 0 1) 0)
      (2 * Morse.secondVariation hN γ (fun t => deriv (fun u₁ => α (u₁, 0) t) 0)
        (fun t => deriv (fun u₂ => α (0, u₂) t) 0)) 0

/-- **Every blind `IsHess` value is `E_**` of the ambient fields** (Theorem 13.1 in Fréchet form
on `↥N`): `r = 2 secondVariation γ W₁ W₂`. -/
theorem hess_eq (hsv : SV hN) {γ : ℝ → Bridge.Sub hN}
    (hgeo : IsGeodesic (Bridge.conn (hN := hN)) γ (Icc 0 1)) {W₁ W₂ : FA n γ} {r : ℝ}
    (h : IsHess (n := n) γ W₁ W₂ r) :
    r = 2 * Morse.secondVariation hN (Bridge.incl hN ∘ γ) (Bridge.ambA γ W₁)
      (Bridge.ambA γ W₂) := by
  obtain ⟨U, α, ⟨k, t, hα⟩, rfl, hW₁, hW₂, -, hr⟩ := h
  have hvar := isVariation_of_isVarSub hα
  have hφ : ContDiff ℝ ∞ (fun p : ℝ × ℝ => p.1 • e0 + p.2 • e1) :=
    (contDiff_fst.smul contDiff_const).add (contDiff_snd.smul contDiff_const)
  have hφ0 : (fun p : ℝ × ℝ => p.1 • e0 + p.2 • e1) 0 ∈ U := by
    simpa using hvar.zero_mem
  have hvar2 := hvar.comp hφ hφ0
  have hαγ : ∀ τ ∈ Icc (0 : ℝ) 1,
      (fun p : ℝ × ℝ => amb α (p.1 • e0 + p.2 • e1)) 0 τ = (Bridge.incl hN ∘ α 0) τ := by
    intro τ _
    simp [amb]
  have hd := hsv (mem_pathSpace_of_isGeodesic hgeo) (isUnbrokenGeodesic_of_isGeodesic hgeo)
    hvar2 hαγ
  simp only [zero_smul, add_zero, zero_add] at hd
  rw [← hr, (hess_data hα).2, hd.deriv]
  congr 1
  refine Morse.secondVariation_congr hN (fun τ hτ => ?_) (fun τ hτ => ?_)
  · rw [Bridge.ambA, eq_of_heq (hW₁ τ), D_varField hα 0 hτ]
  · rw [Bridge.ambA, eq_of_heq (hW₂ τ), D_varField hα 1 hτ]

/-! ### Existence of `IsHess` values (Lemma 11.A on `↥N`, fields matched on all of `ℝ`) -/

/-- Near the zero section `exp` is smooth with `d(exp_q)₀ = id` (from `Morse.exists_isOpen_exp`
and `Morse.hasFDerivAt_exp_zero`), along any linear map into `T_qN`. -/
theorem exp_local {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] {q : V} (hq : q ∈ N)
    (Λ : P →L[ℝ] V) (hΛ : ∀ u, Morse.prj hN q (Λ u) = Λ u) :
    (∀ᶠ u in 𝓝 (0 : P), Morse.exp hN q (Λ u) ∈ N) ∧
    ContDiffAt ℝ ∞ (fun u => Morse.exp hN q (Λ u)) 0 ∧
    HasFDerivAt (fun u => Morse.exp hN q (Λ u)) Λ 0 := by
  obtain ⟨O, hO, hO0, hexp⟩ := Morse.exists_isOpen_exp (hN := hN)
  have hTN : ∀ u, (q, Λ u) ∈ Milnor.Problems.tangentBundleSet hN :=
    fun u => ⟨hq, (Morse.prj_eq_self_iff hN hq).1 (hΛ u)⟩
  have hc : Continuous (fun u : P => (q, Λ u)) := continuous_const.prodMk Λ.continuous
  have hq0 : (q, Λ 0) ∈ O := by rw [map_zero]; exact hO0 q hq
  have hev : ∀ᶠ u in 𝓝 (0 : P), (q, Λ u) ∈ O :=
    hc.continuousAt.preimage_mem_nhds (hO.mem_nhds hq0)
  refine ⟨?_, ?_, ?_⟩
  · filter_upwards [hev] with u hu
    exact Morse.exp_mem_of_mem_expDom (hexp _ hu (hTN u)).1
  · obtain ⟨-, F, O', hO', hzO', hF, hFeq⟩ := hexp _ hq0 (hTN 0)
    have h1 : ContDiffAt ℝ ∞ (fun u => F (q, Λ u)) 0 :=
      (hF.contDiffAt (hO'.mem_nhds hzO')).comp (0 : P)
        (contDiff_const.prodMk Λ.contDiff).contDiffAt
    refine h1.congr_of_eventuallyEq ?_
    filter_upwards [hc.continuousAt.preimage_mem_nhds (hO'.mem_nhds hzO')] with u hu
    exact hFeq _ hu (hTN u)
  · set qt : N := ⟨q, hq⟩
    let L : P →L[ℝ] Morse.tangentSubspace hN qt :=
      Λ.codRestrict (Morse.tangentSubspace hN qt) fun u =>
        (Morse.prj_eq_self_iff hN hq).1 (hΛ u)
    have h1 := Morse.hasFDerivAt_exp_zero (hN := hN) qt
    rw [← map_zero L] at h1
    have h2 := h1.comp (0 : P) L.hasFDerivAt
    have hL : ((Morse.tangentSubspace hN qt).subtypeL.comp L) = Λ :=
      ContinuousLinearMap.ext fun u => rfl
    rw [hL] at h2
    exact h2

open Classical in
/-- Milnor's `α(u, t) = exp_{γ(t)}(Λ(t) u)`, as a map into `↥N` (junk `γ t` where `exp` leaves
`N`, which does not happen near `u = 0`). -/
noncomputable def liftE (γ : ℝ → Bridge.Sub hN) (Λ : ℝ → Rn 2 →L[ℝ] V) (u : Rn 2) (t : ℝ) :
    Bridge.Sub hN :=
  if h : Morse.exp hN (Bridge.incl hN (γ t)) (Λ t u) ∈ N then (⟨_, h⟩ : N) else γ t

theorem liftE_of_mem {γ : ℝ → Bridge.Sub hN} {Λ : ℝ → Rn 2 →L[ℝ] V} {u : Rn 2} {t : ℝ}
    (h : Morse.exp hN (Bridge.incl hN (γ t)) (Λ t u) ∈ N) :
    liftE γ Λ u t = (⟨_, h⟩ : N) := by
  unfold liftE; exact dif_pos h

theorem incl_liftE {γ : ℝ → Bridge.Sub hN} {Λ : ℝ → Rn 2 →L[ℝ] V} {u : Rn 2} {t : ℝ}
    (h : Morse.exp hN (Bridge.incl hN (γ t)) (Λ t u) ∈ N) :
    Bridge.incl hN (liftE γ Λ u t) = Morse.exp hN (Bridge.incl hN (γ t)) (Λ t u) := by
  rw [liftE_of_mem h]; rfl

/-- **Existence of `E_**(W₁, W₂)` on `↥N`**: for a geodesic `γ` and blind `W₁, W₂ ∈ TΩ_γ` there is
a blind 2-parameter variation with fields `W₁, W₂` (at every `t ∈ ℝ`), hence an `IsHess` value. -/
theorem exists_isHess {γ : ℝ → Bridge.Sub hN}
    (hgeo : IsGeodesic (Bridge.conn (hN := hN)) γ (Icc 0 1)) {W₁ W₂ : FA n γ}
    (h₁ : InTOmega (n := n) γ W₁) (h₂ : InTOmega (n := n) γ W₂) :
    ∃ r, IsHess (n := n) γ W₁ W₂ r := by
  have hc := mem_pathSpace_of_isGeodesic hgeo
  obtain ⟨hXs₁, -, hX0₁, hX1₁⟩ := (Morse.mem_pathTangent hN).1 (mem_pathTangent_of_inTOmega h₁)
  obtain ⟨hXs₂, -, hX0₂, hX1₂⟩ := (Morse.mem_pathTangent hN).1 (mem_pathTangent_of_inTOmega h₂)
  set X₁ := Bridge.ambA γ W₁
  set X₂ := Bridge.ambA γ W₂
  set Λ : ℝ → Rn 2 →L[ℝ] V := fun t =>
    (EuclideanSpace.proj (0 : Fin 2) : Rn 2 →L[ℝ] ℝ).smulRight (X₁ t) +
      (EuclideanSpace.proj (1 : Fin 2) : Rn 2 →L[ℝ] ℝ).smulRight (X₂ t) with hΛdef
  have hΛapp : ∀ t u, Λ t u = u 0 • X₁ t + u 1 • X₂ t := fun t u => by
    simp [hΛdef]
  have hΛT : ∀ t u, Morse.prj hN (Bridge.incl hN (γ t)) (Λ t u) = Λ t u := fun t u =>
    (Morse.prj_eq_self_iff hN (γ t).2).2 (by
      rw [hΛapp]
      exact add_mem (Submodule.smul_mem _ _ (Bridge.D_mem (γ t) (W₁ t)))
        (Submodule.smul_mem _ _ (Bridge.D_mem (γ t) (W₂ t))))
  have hΛs : Morse.IsPiecewiseSmooth Λ 0 1 :=
    (hXs₁.smulRight (EuclideanSpace.proj (0 : Fin 2) : Rn 2 →L[ℝ] ℝ)).add
      (hXs₂.smulRight (EuclideanSpace.proj (1 : Fin 2) : Rn 2 →L[ℝ] ℝ))
  have hΛ0 : Λ 0 = 0 := ContinuousLinearMap.ext fun u => by
    rw [hΛapp]; simp [hX0₁, hX0₂]
  have hΛ1 : Λ 1 = 0 := ContinuousLinearMap.ext fun u => by
    rw [hΛapp]; simp [hX1₁, hX1₂]
  obtain ⟨ε, hε, B, hα, -, -⟩ := Morse.exists_variation hN hc (P := Rn 2) hΛs
    (fun t _ u => hΛT t u) hΛ0 hΛ1
  set α := liftE γ Λ
  have hinc : ∀ u ∈ Metric.ball (0 : Rn 2) ε, ∀ t ∈ Icc (0 : ℝ) 1,
      Bridge.incl hN (α u t) = Morse.exp hN (Bridge.incl hN (γ t)) (Λ t u) :=
    fun u hu t ht => incl_liftE (hα.mem u hu t ht)
  have hinj : Function.Injective (Bridge.incl hN) := Subtype.val_injective
  have hα0 : α 0 = γ := funext fun t => by
    have e : Morse.exp hN (Bridge.incl hN (γ t)) (Λ t 0) = Bridge.incl hN (γ t) := by
      rw [map_zero]; exact Morse.exp_zero (γ t).2
    exact hinj ((incl_liftE (γ := γ) (Λ := Λ) (u := 0) (t := t) (by rw [e]; exact (γ t).2)).trans e)
  -- the subdivision
  obtain ⟨k, tt, ht0, htk, hlt, hgood⟩ := exists_subdiv B
  have hstrip : ∀ i < k, ContMDiffOn 𝓘(ℝ, Rn 2 × ℝ) 𝓘(ℝ, Rn n) ∞
      (fun x : Rn 2 × ℝ => α x.1 x.2) (Metric.ball (0 : Rn 2) ε ×ˢ Icc (tt i) (tt (i + 1))) := by
    intro i hi
    obtain ⟨hi0, hi1, hiB⟩ := hgood i hi
    refine contMDiffOn_map_iff.2 ((hα.smooth _ _ hi0 (hlt i hi) hi1 hiB).congr fun p hp => ?_)
    exact hinc p.1 hp.1 p.2 ⟨hi0.trans hp.2.1, hp.2.2.trans hi1⟩
  have hvs : IsVarSub (n := n) (Metric.ball (0 : Rn 2) ε) α k tt := by
    refine ⟨Metric.isOpen_ball, Metric.mem_ball_self hε, ht0, htk, hlt, fun u hu => ⟨?_, ?_, ?_⟩,
      hstrip⟩
    · refine ⟨k, tt, ht0, htk, hlt, fun i hi => ?_⟩
      have hι : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, Rn 2 × ℝ) ∞ (fun s : ℝ => (u, s)) :=
        contMDiff_iff_contDiff.2 (contDiff_const.prodMk contDiff_id)
      exact (hstrip i hi).comp hι.contMDiffOn fun s hs => ⟨hu, hs⟩
    · refine hinj ?_
      rw [hinc u hu 0 ⟨le_rfl, zero_le_one⟩, hinc 0 (Metric.mem_ball_self hε) 0 ⟨le_rfl, zero_le_one⟩,
        hΛ0]
      rfl
    · refine hinj ?_
      rw [hinc u hu 1 ⟨zero_le_one, le_rfl⟩, hinc 0 (Metric.mem_ball_self hε) 1 ⟨zero_le_one, le_rfl⟩,
        hΛ1]
      rfl
  -- the variation fields, at every `t ∈ ℝ`
  have hfield : ∀ (i : Fin 2) (t : ℝ),
      Bridge.D hN (γ t) (varField (n := n) α i t) = Λ t (EuclideanSpace.single i (1 : ℝ)) := by
    intro i t
    obtain ⟨hmem, hcd, hfd⟩ := exp_local (hN := hN) (γ t).2 (Λ t) (hΛT t)
    have hev : (Bridge.incl hN ∘ fun u => α u t) =ᶠ[𝓝 0]
        fun u => Morse.exp hN (Bridge.incl hN (γ t)) (Λ t u) := by
      filter_upwards [hmem] with u hu
      exact incl_liftE hu
    have h1 := D_mfderiv_of_contDiffAt (hcd.congr_of_eventuallyEq hev)
      (EuclideanSpace.single i (1 : ℝ))
    have h2 := (hfd.congr_of_eventuallyEq hev).fderiv
    rw [h2] at h1
    calc Bridge.D hN (γ t) (varField (n := n) α i t)
        = Bridge.D hN (α 0 t) (varField (n := n) α i t) := by rw [congrFun hα0 t]
      _ = _ := h1
  have hW : ∀ (i : Fin 2) (Wi : FA n γ), (∀ t, Λ t (EuclideanSpace.single i (1 : ℝ)) =
      Bridge.D hN (γ t) (Wi t)) → ∀ t, HEq (Wi t) (varField (n := n) α i t) := by
    intro i Wi hWi t
    have := Bridge.D_injective (γ t) ((hfield i t).trans (hWi t))
    exact heq_of_eq this.symm
  refine ⟨_, Metric.ball (0 : Rn 2) ε, α, ⟨k, tt, hvs⟩, hα0,
    hW 0 W₁ fun t => by rw [hΛapp]; simp [X₁, Bridge.ambA],
    hW 1 W₂ fun t => by rw [hΛapp]; simp [X₂, Bridge.ambA], (hess_data hvs).1, rfl⟩

end Emb

/-! ### The second variation formula, blind ⇔ project (dictionary for Theorem 13.1's right side) -/

namespace Emb

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] {n : ℕ} {N : Set V}
  {hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N}

/-- **B's `mixedD` is the project's `2 secondVariation`** of the ambient fields, for every blind
2-parameter variation of a geodesic (`EnergyC2` plus Theorem 13.1 taken as the hypothesis
`SV hN`). -/
theorem mixedD_eq (hsv : SV hN) {U : Set (Rn 2)} {α : Rn 2 → ℝ → Bridge.Sub hN} {k : ℕ}
    {t : ℕ → ℝ} (hα : IsVarSub (n := n) U α k t)
    (hgeo : IsGeodesic (Bridge.conn (hN := hN)) (α 0) (Icc 0 1)) :
    mixedD (fun v : Rn 2 => Efun (n := n) (α v)) =
      2 * Morse.secondVariation hN (Bridge.incl hN ∘ α 0) (Bridge.ambA (α 0) (varField (n := n) α 0))
        (Bridge.ambA (α 0) (varField (n := n) α 1)) := by
  have hvar := isVariation_of_isVarSub hα
  have hφ : ContDiff ℝ ∞ (fun p : ℝ × ℝ => p.1 • e0 + p.2 • e1) :=
    (contDiff_fst.smul contDiff_const).add (contDiff_snd.smul contDiff_const)
  have hφ0 : (fun p : ℝ × ℝ => p.1 • e0 + p.2 • e1) 0 ∈ U := by
    simpa using hvar.zero_mem
  have hvar2 := hvar.comp hφ hφ0
  have hαγ : ∀ τ ∈ Icc (0 : ℝ) 1,
      (fun p : ℝ × ℝ => amb α (p.1 • e0 + p.2 • e1)) 0 τ = (Bridge.incl hN ∘ α 0) τ := by
    intro τ _
    simp [amb]
  have hd := hsv (mem_pathSpace_of_isGeodesic hgeo) (isUnbrokenGeodesic_of_isGeodesic hgeo)
    hvar2 hαγ
  simp only [zero_smul, add_zero, zero_add] at hd
  rw [(hess_data hα).2, hd.deriv]
  congr 1
  refine Morse.secondVariation_congr hN (fun τ hτ => ?_) (fun τ hτ => ?_)
  · rw [Bridge.ambA, D_varField hα 0 hτ]
  · rw [Bridge.ambA, D_varField hα 1 hτ]

theorem sum_filter_image {k : ℕ} {t : ℕ → ℝ} (h0 : t 0 = 0) (hk : t k = 1)
    (hlt : ∀ i < k, t i < t (i + 1)) (g : ℝ → ℝ) :
    ∑ x ∈ (Finset.range (k + 1)).image t with x ∈ Ioo (0 : ℝ) 1, g x =
      ∑ i ∈ Finset.Ico 1 k, g (t i) := by
  classical
  have hfilt : Finset.filter (fun x => x ∈ Ioo (0 : ℝ) 1) ((Finset.range (k + 1)).image t) =
      (Finset.Ico 1 k).image t := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_range, Finset.mem_Ico]
    constructor
    · rintro ⟨⟨j, hj, rfl⟩, hx⟩
      refine ⟨j, ⟨?_, ?_⟩, rfl⟩
      · by_contra h
        have : j = 0 := by omega
        subst this
        rw [h0] at hx
        exact lt_irrefl 0 hx.1
      · by_contra h
        have : j = k := by omega
        subst this
        rw [hk] at hx
        exact lt_irrefl 1 hx.2
    · rintro ⟨j, ⟨hj1, hjk⟩, rfl⟩
      refine ⟨⟨j, by omega, rfl⟩, ?_, ?_⟩
      · rw [← h0]; exact Bridge.lt_of_strictSeq hlt (by omega) hjk.le
      · rw [← hk]; exact Bridge.lt_of_strictSeq hlt hjk le_rfl
  rw [hfilt, Finset.sum_image]
  intro i hi j hj hij
  simp only [Finset.coe_Ico, mem_Ico] at hi hj
  rcases lt_trichotomy i j with h | h | h
  · exact absurd hij (Bridge.lt_of_strictSeq hlt h hj.2.le).ne
  · exact h
  · exact absurd hij.symm (Bridge.lt_of_strictSeq hlt h hi.2.le).ne

theorem integral_split' {f : ℝ → ℝ} {k : ℕ} {t : ℕ → ℝ} (h0 : t 0 = 0) (hk : t k = 1)
    (hlt : ∀ i < k, t i < t (i + 1)) (hf : IntervalIntegrable f MeasureTheory.volume 0 1) :
    ∫ x in (0 : ℝ)..1, f x = ∑ i ∈ Finset.range k, ∫ x in t i..t (i + 1), f x := by
  have hint : ∀ j < k, IntervalIntegrable f MeasureTheory.volume (t j) (t (j + 1)) := by
    intro j hj
    refine hf.mono_set ?_
    rw [uIcc_of_le (hlt j hj).le, uIcc_of_le zero_le_one]
    refine Icc_subset_Icc ?_ ?_
    · rw [← h0]; exact Bridge.le_of_strictSeq hlt (Nat.zero_le j) hj.le
    · rw [← hk]; exact Bridge.le_of_strictSeq hlt (Nat.succ_le_of_lt hj) le_rfl
  rw [intervalIntegral.sum_integral_adjacent_intervals hint, h0, hk]

/-- **Dictionary: Milnor's right side of Theorem 13.1.** For a geodesic `γ` of `↥N`, a subdivision
`t`, blind `D1 i = DW₁/dt`, `D2 i = D²W₁/dt²` on the closed pieces and `Rv = R(V, W₁)V`, the blind
right side (jumps `D1 i (tᵢ) − D1 (i−1) (tᵢ)` at the interior subdivision points, sum of piece
integrals) is the project's `secondVariation` of the ambient fields (jumps `P(Δ_t W₁')` over all
`t ∈ (0, 1)`, one integral, `covD`, `curvR`). -/
theorem sv_eq_rhs {γ : ℝ → Bridge.Sub hN}
    (hgeo : IsGeodesic (Bridge.conn (hN := hN)) γ (Icc 0 1)) {k : ℕ} {t : ℕ → ℝ}
    (ht0 : t 0 = 0) (htk : t k = 1) (hlt : ∀ i < k, t i < t (i + 1)) {W₁ W₂ : FA n γ}
    (hW₂ : ContinuousOn (Bridge.ambA γ W₂) (Icc 0 1)) (D1 D2 : ℕ → FA n γ) (Rv : FA n γ)
    (hD : ∀ i < k, HasCovDeriv (Bridge.conn (hN := hN)) γ (Icc (t i) (t (i + 1))) W₁ (D1 i) ∧
      HasCovDeriv (Bridge.conn (hN := hN)) γ (Icc (t i) (t (i + 1))) (D1 i) (D2 i))
    (hR : ∀ s ∈ Icc (0 : ℝ) 1, IsCurvVal (Bridge.conn (hN := hN)) (γ s)
      (vel (n := n) γ (Icc 0 1) s) (W₁ s) (vel (n := n) γ (Icc 0 1) s) (Rv s)) :
    Morse.secondVariation hN (Bridge.incl hN ∘ γ) (Bridge.ambA γ W₁) (Bridge.ambA γ W₂) =
      - (∑ i ∈ Finset.Ico 1 k, inner ℝ (W₂ (t i)) (D1 i (t i) - D1 (i - 1) (t i)))
      - ∑ i ∈ Finset.range k, ∫ s in (t i)..(t (i + 1)), inner ℝ (W₂ s) (D2 i s + Rv s) := by
  set c := Bridge.incl hN ∘ γ with hc
  set X₁ := Bridge.ambA γ W₁ with hX₁
  set X₂ := Bridge.ambA γ W₂ with hX₂
  have hcs : ContDiffOn ℝ ∞ c (Icc 0 1) := (isUnbrokenGeodesic_of_isGeodesic hgeo).1
  have hγs : IsSmoothCurve (n := n) γ (Icc 0 1) := hgeo.2.1
  have hti : ∀ i < k, 0 ≤ t i ∧ t (i + 1) ≤ 1 := fun i hi =>
    ⟨ht0 ▸ Bridge.le_of_strictSeq hlt (Nat.zero_le i) hi.le,
      htk ▸ Bridge.le_of_strictSeq hlt (Nat.succ_le_of_lt hi) le_rfl⟩
  have hsub : ∀ i < k, Icc (t i) (t (i + 1)) ⊆ Icc 0 1 := fun i hi =>
    Icc_subset_Icc (hti i hi).1 (hti i hi).2
  have hIntv : ∀ i < k, RoundTrip.BridgePrelude.IsIntv (Icc (t i) (t (i + 1))) := fun i hi =>
    ⟨ordConnected_Icc, uniqueDiffOn_Icc (hlt i hi)⟩
  have hpc : ∀ i < k, RoundTrip.BridgePrelude.IsSmoothCurve (n := n) γ (Icc (t i) (t (i + 1))) :=
    fun i hi => ContMDiffOn.mono hγs (hsub i hi)
  -- the blind covariant derivatives, read in `V`
  have hD1 : ∀ i < k, ContDiffOn ℝ ∞ X₁ (Icc (t i) (t (i + 1))) ∧
      ∀ τ ∈ Icc (t i) (t (i + 1)), Bridge.ambA γ (D1 i) τ =
        Bridge.P hN (γ τ) (derivWithin X₁ (Icc (t i) (t (i + 1))) τ) := fun i hi => by
    have h : RoundTrip.BridgePrelude.HasCovDeriv (Bridge.conn (hN := hN)) γ
        (Icc (t i) (t (i + 1))) W₁ (D1 i) := (hD i hi).1
    obtain ⟨hs, h2⟩ := (Bridge.hasCovDeriv_iff' (hIntv i hi) (hpc i hi)).1 h
    exact ⟨(Bridge.isSmoothAlong_iff.1 hs).2, h2⟩
  have hD2 : ∀ i < k, ContDiffOn ℝ ∞ (Bridge.ambA γ (D1 i)) (Icc (t i) (t (i + 1))) ∧
      ∀ τ ∈ Icc (t i) (t (i + 1)), Bridge.ambA γ (D2 i) τ =
        Bridge.P hN (γ τ) (derivWithin (Bridge.ambA γ (D1 i)) (Icc (t i) (t (i + 1))) τ) :=
    fun i hi => by
    have h : RoundTrip.BridgePrelude.HasCovDeriv (Bridge.conn (hN := hN)) γ
        (Icc (t i) (t (i + 1))) (D1 i) (D2 i) := (hD i hi).2
    obtain ⟨hs, h2⟩ := (Bridge.hasCovDeriv_iff' (hIntv i hi) (hpc i hi)).1 h
    exact ⟨(Bridge.isSmoothAlong_iff.1 hs).2, h2⟩
  have hPprj : ∀ τ, Bridge.P hN (γ τ) = Morse.prj hN (c τ) := fun τ => by
    show Bridge.P hN (γ τ) = Morse.prj hN (γ τ).1
    rw [Morse.prj_of_mem hN (γ τ).2]; rfl
  -- velocity
  have hvel : ∀ τ ∈ Icc (0 : ℝ) 1,
      Bridge.D hN (γ τ) (vel (n := n) γ (Icc 0 1) τ) = derivWithin c (Icc 0 1) τ := fun τ hτ =>
    Bridge.D_vel hγs (uniqueDiffOn_Icc zero_lt_one) hτ
  -- interior points of a piece: `D1 i` is `covD X₁`, `D2 i` is `covD (covD X₁)`
  have hcov1 : ∀ i < k, ∀ τ ∈ Ioo (t i) (t (i + 1)),
      Bridge.ambA γ (D1 i) τ = Morse.covD hN c X₁ τ := fun i hi τ hτ => by
    rw [(hD1 i hi).2 τ (Ioo_subset_Icc_self hτ), derivWithin_of_mem_nhds (Icc_mem_nhds hτ.1 hτ.2),
      hPprj, Morse.covD]
  have hcov2 : ∀ i < k, ∀ τ ∈ Ioo (t i) (t (i + 1)),
      Bridge.ambA γ (D2 i) τ = Morse.covD hN c (Morse.covD hN c X₁) τ := fun i hi τ hτ => by
    rw [(hD2 i hi).2 τ (Ioo_subset_Icc_self hτ), derivWithin_of_mem_nhds (Icc_mem_nhds hτ.1 hτ.2),
      hPprj, Morse.covD]
    congr 1
    refine Filter.EventuallyEq.deriv_eq ?_
    filter_upwards [Ioo_mem_nhds hτ.1 hτ.2] with σ hσ
    exact hcov1 i hi σ hσ
  -- the piece integrands
  set dc := derivWithin c (Icc 0 1)
  have hint : ∀ i < k, ∀ τ ∈ Ioo (t i) (t (i + 1)),
      inner ℝ (X₂ τ) (Morse.covD hN c (Morse.covD hN c X₁) τ +
          Morse.curvR hN (c τ) (deriv c τ) (X₁ τ) (deriv c τ)) =
        inner ℝ (W₂ τ) (D2 i τ + Rv τ) := fun i hi τ hτ => by
    have hτ01 : τ ∈ Icc (0 : ℝ) 1 := hsub i hi (Ioo_subset_Icc_self hτ)
    have hτ' : τ ∈ Ioo (0 : ℝ) 1 :=
      ⟨(hti i hi).1.trans_lt hτ.1, hτ.2.trans_le (hti i hi).2⟩
    have hdc : deriv c τ = dc τ :=
      (derivWithin_of_mem_nhds (Icc_mem_nhds hτ'.1 hτ'.2)).symm
    rw [Bridge.inner_eq, Bridge.D_tadd, (Bridge.isCurvVal_iff _ _ _ _ _).1 (hR τ hτ01),
      hvel τ hτ01, ← hdc]
    show _ = inner ℝ (X₂ τ) (Bridge.ambA γ (D2 i) τ + _)
    rw [hcov2 i hi τ hτ]
    rfl
  -- integrability
  have hfint : IntervalIntegrable (fun τ => inner ℝ (X₂ τ)
      (Morse.covD hN c (Morse.covD hN c X₁) τ +
        Morse.curvR hN (c τ) (deriv c τ) (X₁ τ) (deriv c τ))) MeasureTheory.volume 0 1 := by
    refine Morse.intervalIntegrable_of_piecewise (B := (Finset.range (k + 1)).image t) (lo := 0)
      (hi := 1) (fun s u hs hsu hu hB => ?_) le_rfl zero_le_one le_rfl
    obtain ⟨i, hi, hts, hut⟩ := exists_piece_of_subdiv ht0 htk hlt hs hsu hu hB
    have hsI : Icc s u ⊆ Icc (t i) (t (i + 1)) := Icc_subset_Icc hts hut
    have hsI01 : Icc s u ⊆ Icc 0 1 := hsI.trans (hsub i hi)
    refine ⟨fun τ => inner ℝ (X₂ τ)
      (Bridge.P hN (γ τ) (derivWithin (Bridge.ambA γ (D1 i)) (Icc (t i) (t (i + 1))) τ) +
        Morse.curvR hN (c τ) (dc τ) (X₁ τ) (dc τ)), ?_, fun τ hτ => ?_⟩
    · have hγc : ContinuousOn γ (Icc 0 1) := fun τ hτ =>
        (Topology.IsInducing.subtypeVal.continuousWithinAt_iff (f := γ)).2
          (hcs.continuousOn τ hτ)
      have hP : ContinuousOn (fun τ => Bridge.P hN (γ τ)) (Icc s u) :=
        (Bridge.contMDiff_P.continuous.comp_continuousOn hγc).mono hsI01
      have hdd : ContinuousOn (derivWithin (Bridge.ambA γ (D1 i)) (Icc (t i) (t (i + 1))))
          (Icc s u) :=
        (((hD2 i hi).1.derivWithin (uniqueDiffOn_Icc (hlt i hi)) (m := 0) (by simp)).continuousOn).mono
          hsI
      have hdc : ContinuousOn dc (Icc 0 1) :=
        (hcs.derivWithin (uniqueDiffOn_Icc zero_lt_one) (m := 0) (by simp)).continuousOn
      have hX₁c : ContinuousOn X₁ (Icc s u) := ((hD1 i hi).1.continuousOn).mono hsI
      have hdcT : ∀ τ ∈ Icc s u, Morse.prj hN (c τ) (dc τ) = dc τ := fun τ hτ => by
        rw [← hvel τ (hsI01 hτ)]
        exact (Morse.prj_eq_self_iff hN (γ τ).2).2 (Bridge.D_mem _ _)
      have hX₁T : ∀ τ ∈ Icc s u, Morse.prj hN (c τ) (X₁ τ) = X₁ τ := fun τ _ =>
        (Morse.prj_eq_self_iff hN (γ τ).2).2 (Bridge.D_mem _ _)
      have hR' : ContinuousOn (fun τ => Morse.curvR hN (c τ) (dc τ) (X₁ τ) (dc τ)) (Icc s u) :=
        fun τ hτ => Morse.continuousWithinAt_curvR hN hτ ((hcs.continuousOn τ (hsI01 hτ)).mono
          hsI01) (fun σ _ => (γ σ).2) ((hdc τ (hsI01 hτ)).mono hsI01) (hX₁c τ hτ)
          ((hdc τ (hsI01 hτ)).mono hsI01) hdcT hX₁T
      exact (hW₂.mono hsI01).inner ((hP.clm_apply hdd).add hR')
    · have hτ' : τ ∈ Ioo (t i) (t (i + 1)) := ⟨hts.trans_lt hτ.1, hτ.2.trans_le hut⟩
      have hτ'' : τ ∈ Ioo (0 : ℝ) 1 :=
        ⟨(hti i hi).1.trans_lt hτ'.1, hτ'.2.trans_le (hti i hi).2⟩
      have hdc' : deriv c τ = dc τ := (derivWithin_of_mem_nhds (Icc_mem_nhds hτ''.1 hτ''.2)).symm
      simp only
      rw [← hcov2 i hi τ hτ', (hD2 i hi).2 τ (Ioo_subset_Icc_self hτ'), hdc']
  -- the jumps
  have hjump : ∀ i ∈ Finset.Ico 1 k,
      inner ℝ (W₂ (t i)) (D1 i (t i) - D1 (i - 1) (t i)) =
        inner ℝ (X₂ (t i)) (Morse.prj hN (c (t i)) (Morse.jump X₁ (t i))) := by
    intro i hi
    rw [Finset.mem_Ico] at hi
    have hi1 : i - 1 + 1 = i := Nat.sub_add_cancel hi.1
    have hl := (hD1 i hi.2).2 (t i) (left_mem_Icc.2 (hlt i hi.2).le)
    have hlt' : t (i - 1) < t i := by have := hlt (i - 1) (by omega); rwa [hi1] at this
    have hD1' := hD1 (i - 1) (by omega)
    rw [hi1] at hD1'
    have hr := hD1'.2 (t i) (right_mem_Icc.2 hlt'.le)
    rw [Bridge.inner_eq, Bridge.D_tsub_aux]
    show inner ℝ (X₂ (t i)) (Bridge.ambA γ (D1 i) (t i) - Bridge.ambA γ (D1 (i - 1)) (t i)) = _
    rw [hl, hr, ← map_sub, hPprj, Morse.jump,
      Morse.derivWithin_Ici_eq_of_piece (hlt i hi.2) ((hD1 i hi.2).1.differentiableOn (by simp)),
      Morse.derivWithin_Iic_eq_of_piece hlt' (hD1'.1.differentiableOn (by simp))]
  have hS : ∑ᶠ τ ∈ Ioo (0 : ℝ) 1, inner ℝ (X₂ τ) (Morse.prj hN (c τ) (Morse.jump X₁ τ)) =
      ∑ i ∈ Finset.Ico 1 k, inner ℝ (X₂ (t i)) (Morse.prj hN (c (t i)) (Morse.jump X₁ (t i))) := by
    rw [Morse.finsum_mem_Ioo_eq_sum (B := (Finset.range (k + 1)).image t) fun x hx hxB => ?_,
      sum_filter_image ht0 htk hlt]
    obtain ⟨i, hi, hxi⟩ := exists_piece_of_mem ht0 htk hlt (Ioo_subset_Icc_self hx)
    have hne : ∀ j ≤ k, x ≠ t j := fun j hj h =>
      hxB (Finset.mem_image.2 ⟨j, Finset.mem_range.2 (by omega), h.symm⟩)
    have hxo : x ∈ Ioo (t i) (t (i + 1)) :=
      ⟨lt_of_le_of_ne hxi.1 (hne i hi.le).symm, lt_of_le_of_ne hxi.2 (hne (i + 1) hi)⟩
    have hd : DifferentiableAt ℝ X₁ x :=
      ((hD1 i hi).1.contDiffAt (Icc_mem_nhds hxo.1 hxo.2)).differentiableAt (by simp)
    rw [Morse.jump_eq_zero hd, map_zero, inner_zero_right]
  rw [Morse.secondVariation, hS, integral_split' ht0 htk hlt hfint, Finset.sum_congr rfl hjump]
  congr 1
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.mem_range] at hi
  exact intervalIntegral.integral_congr_Ioo_of_le (hlt i hi).le fun τ hτ => hint i hi τ hτ

end Emb

/-- **`A ⇒ B_emb`** (Theorem 13.1 on `↥N`): `E ∘ α` is `C²` (`EnergyC2`, giving B's
`DifferentiableAt` clause), B's `mixedD` is A's iterated derivative `= 2 secondVariation`
(`Emb.mixedD_eq`, A's `second_variation` as the hypothesis), and the project's `secondVariation` of
the ambient fields is B's right side (`Emb.sv_eq_rhs`). -/
theorem A_to_B_emb : A → B_emb := by
  intro hA V _ _ _ W _ _ _ n N hN _ U α k t hα hgeo D1 D2 Rv hD hR
  have hsv : Emb.SV hN := by
    intro _ _ _ _ hub _ _ _ hβ hβγ
    exact hA.1 hN hub hβ hβγ
  obtain ⟨hU, h0U, ht0, htk, hlt, -, -⟩ := id hα
  have hvar := Emb.isVariation_of_isVarSub hα
  -- the ambient field `W₂` is continuous on `[0, 1]`
  have hW₂ : ContinuousOn (Bridge.ambA (α 0) (varField (n := n) α 1)) (Icc 0 1) := by
    have hv1 := hvar.comp (φ := fun r : ℝ => r • (EuclideanSpace.single 1 (1 : ℝ) : Rn 2))
      (contDiff_id.smul contDiff_const) (by simpa using h0U)
    have hc := ((Morse.mem_pathTangent hN).1 (hv1.varField_mem hN)).1.2.1
    refine hc.congr fun τ hτ => ?_
    rw [Bridge.ambA, Emb.D_varField hα 1 hτ]
    rfl
  refine ⟨(Emb.hess_data hα).1, ?_⟩
  rw [Emb.mixedD_eq hsv hα hgeo, Emb.sv_eq_rhs hgeo ht0 htk hlt hW₂ D1 D2 Rv hD hR]
  ring

#rt_check RoundTrip.V8_13.A_to_B_emb [Morse.second_variation, Morse.second_variation_eq]
#rt_overlap RoundTrip.V8_13.A_to_B_emb [Morse.second_variation, Morse.second_variation_eq]


/-! ### `B_emb ⇒ A` on embedded manifolds (reverse dictionary: project variations are blind ones) -/

namespace Emb

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] {n : ℕ} {N : Set V}
  {hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N}

/-- A project unbroken geodesic is a blind geodesic on `[0, 1]` (copied from `Items/V8_10.lean`). -/
theorem isGeodesic_of_isUnbrokenGeodesic {pw : ℝ → Bridge.Sub hN}
    (h : Morse.IsUnbrokenGeodesic hN (Bridge.incl hN ∘ pw)) :
    IsGeodesic (Bridge.conn (hN := hN)) pw (Icc 0 1) := by
  show RoundTrip.BridgePrelude.IsGeodesic _ _ _
  refine Bridge.isGeodesic_iff.2 ⟨⟨ordConnected_Icc, uniqueDiffOn_Icc zero_lt_one⟩, h.1, ?_⟩
  set f := Bridge.incl hN ∘ pw
  set I := Icc (0 : ℝ) 1
  have uI : UniqueDiffOn ℝ I := uniqueDiffOn_Icc zero_lt_one
  have hg : ContinuousOn (derivWithin (derivWithin f I) I) I :=
    ((h.1.derivWithin uI (m := ∞) (by simp)).derivWithin uI (m := 0) (by simp)).continuousOn
  have hpw : ContinuousOn pw I := fun t ht =>
    (Topology.IsInducing.subtypeVal.continuousWithinAt_iff (f := pw)).2 (h.1.continuousOn t ht)
  have hP : ContinuousOn (fun t => Bridge.P hN (pw t)) I :=
    Bridge.contMDiff_P.continuous.comp_continuousOn hpw
  have hcont : ContinuousOn
      (fun t => Bridge.P hN (pw t) (derivWithin (derivWithin f I) I t)) I := hP.clm_apply hg
  have hzero : EqOn (fun t => Bridge.P hN (pw t) (derivWithin (derivWithin f I) I t)) 0
      (Ioo 0 1) := by
    intro t ht
    have h1 : deriv f =ᶠ[𝓝 t] derivWithin f I := by
      filter_upwards [isOpen_Ioo.mem_nhds ht] with τ hτ
      exact (derivWithin_of_mem_nhds (Icc_mem_nhds hτ.1 hτ.2)).symm
    have e : derivWithin (derivWithin f I) I t = deriv (deriv f) t := by
      rw [h1.deriv_eq, derivWithin_of_mem_nhds (Icc_mem_nhds ht.1 ht.2)]
    show Bridge.P hN (pw t) _ = 0
    rw [e]
    exact (Morse.tanProj_eq_zero_iff hN).2 (h.2.normal t ht)
  intro t ht
  exact hzero.of_subset_closure hcont continuousOn_const Ioo_subset_Icc_self
    (by rw [closure_Ioo zero_ne_one]) ht

theorem isUnbrokenGeodesic_congr {c c' : ℝ → V} (h : EqOn c c' (Icc 0 1))
    (hc : Morse.IsUnbrokenGeodesic hN c) : Morse.IsUnbrokenGeodesic hN c' :=
  ⟨hc.1.congr fun t ht => (h ht).symm, hc.2.congr fun t ht => h (Ioo_subset_Icc_self ht)⟩

/-- `secondVariation` only depends on the path on `[0, 1]`. -/
theorem sv_congr_path {c c' X₁ X₂ : ℝ → V} (h : ∀ t ∈ Icc (0 : ℝ) 1, c t = c' t) :
    Morse.secondVariation hN c X₁ X₂ = Morse.secondVariation hN c' X₁ X₂ := by
  have hev : ∀ t ∈ Ioo (0 : ℝ) 1, c =ᶠ[𝓝 t] c' := fun t ht => by
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with x hx
    exact h x (Ioo_subset_Icc_self hx)
  have hcov : ∀ t ∈ Ioo (0 : ℝ) 1, Morse.covD hN c X₁ =ᶠ[𝓝 t] Morse.covD hN c' X₁ :=
    fun t ht => by
      filter_upwards [Ioo_mem_nhds ht.1 ht.2] with x hx
      simp only [Morse.covD, h x (Ioo_subset_Icc_self hx)]
  rw [Morse.secondVariation, Morse.secondVariation]
  congr 1
  · congr 1
    exact finsum_mem_congr rfl fun t ht => by rw [h t (Ioo_subset_Icc_self ht)]
  · refine intervalIntegral.integral_congr_Ioo_of_le zero_le_one fun t ht => ?_
    simp only [Morse.covD, (hcov t ht).deriv_eq, h t (Ioo_subset_Icc_self ht), (hev t ht).deriv_eq]

/-- The variation field of a project 1-parameter variation is smooth on each strip. -/
theorem contDiffOn_varField {U : Set ℝ} {β : ℝ → ℝ → V} {B : Finset ℝ}
    (hβ : Morse.IsVariation N U β B) {s u : ℝ} (hs : 0 ≤ s) (hsu : s < u) (hu : u ≤ 1)
    (hB : ∀ x ∈ B, x ∉ Ioo s u) :
    ContDiffOn ℝ ∞ (fun τ => deriv (fun r => β r τ) 0) (Icc s u) := by
  have hF := hβ.smooth s u hs hsu hu hB
  have h1 : ContDiffOn ℝ ∞ (fun τ => Morse.pdU (U ×ˢ Icc s u) (fun p : ℝ × ℝ => β p.1 p.2) (0, τ))
      (Icc s u) :=
    (Morse.contDiffOn_pdU hβ.isOpen hsu hF).comp (contDiffOn_const.prodMk contDiffOn_id)
      fun τ hτ => mk_mem_prod hβ.zero_mem hτ
  refine h1.congr fun τ hτ => ?_
  exact Morse.deriv_eq_pdU hβ.isOpen (F := fun p : ℝ × ℝ => β p.1 p.2)
    (hF.differentiableOn (by simp)) hβ.zero_mem hτ

/-- **A project variation lifts to a blind variation** (generalizes `Items/V8_9.lean`'s
`isVarSub_liftVar` to `ℝᵐ`), along a subdivision avoiding its break points. -/
theorem isVarSub_lift {m : ℕ} {U : Set (Rn m)} {α' : Rn m → ℝ → V} {B : Finset ℝ}
    (hα : Morse.IsVariation N U α' B) (p₀ : Bridge.Sub hN) {k : ℕ} {t : ℕ → ℝ} (ht0 : t 0 = 0)
    (htk : t k = 1) (hlt : ∀ i < k, t i < t (i + 1))
    (hgood : ∀ i < k, 0 ≤ t i ∧ t (i + 1) ≤ 1 ∧ ∀ x ∈ B, x ∉ Ioo (t i) (t (i + 1))) :
    IsVarSub (n := n) U (fun u => Bridge.lift (α' u) p₀) k t := by
  have hinj : Function.Injective (Bridge.incl hN) := Subtype.val_injective
  have hinc : ∀ u ∈ U, ∀ s ∈ Icc (0 : ℝ) 1, Bridge.incl hN (Bridge.lift (α' u) p₀ s) = α' u s :=
    fun u hu s hs => Bridge.incl_lift p₀ (hα.mem _ hu s hs)
  refine ⟨hα.isOpen, hα.zero_mem, ht0, htk, hlt, fun u hu => ⟨?_, ?_, ?_⟩, fun i hi => ?_⟩
  · exact Bridge.isPW_lift (hα.isPiecewiseSmooth hu) (hα.mem _ hu) p₀
  · refine hinj ?_
    rw [hinc u hu 0 ⟨le_rfl, zero_le_one⟩, hinc 0 hα.zero_mem 0 ⟨le_rfl, zero_le_one⟩,
      hα.start _ hu]
  · refine hinj ?_
    rw [hinc u hu 1 ⟨zero_le_one, le_rfl⟩, hinc 0 hα.zero_mem 1 ⟨zero_le_one, le_rfl⟩,
      hα.finish _ hu]
  · obtain ⟨h0i, hi1, hBi⟩ := hgood i hi
    refine contMDiffOn_map_iff.2 ((hα.smooth _ _ h0i (hlt i hi) hi1 hBi).congr fun p hp => ?_)
    exact hinc p.1 hp.1 p.2 ⟨h0i.trans hp.2.1, hp.2.2.trans hi1⟩

end Emb

/-- A's two claims (Theorem 13.1 and its corollary `second_variation_eq`) for connected slice
submanifolds modelled on `ℝⁿ` (the setting of `B_emb`). -/
def A_emb : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (W : Type) [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] (n : ℕ)
    (N : Set V) (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N)
    [ConnectedSpace (Bridge.Sub hN)],
    (∀ {γ : ℝ → V}, Morse.IsUnbrokenGeodesic hN γ →
      ∀ {U : Set (ℝ × ℝ)} {α : ℝ × ℝ → ℝ → V} {B : Finset ℝ}, Morse.IsVariation N U α B →
      (∀ t ∈ Icc (0 : ℝ) 1, α 0 t = γ t) →
      HasDerivAt (fun u₁ => deriv (fun u₂ => Morse.energy (α (u₁, u₂)) 0 1) 0)
        (2 * Morse.secondVariation hN γ (fun t => deriv (fun u₁ => α (u₁, 0) t) 0)
          (fun t => deriv (fun u₂ => α (0, u₂) t) 0)) 0) ∧
    (∀ {γ : ℝ → V}, Morse.IsUnbrokenGeodesic hN γ →
      ∀ {U U' : Set (ℝ × ℝ)} {α α' : ℝ × ℝ → ℝ → V} {B B' : Finset ℝ},
      Morse.IsVariation N U α B → Morse.IsVariation N U' α' B' →
      (∀ t ∈ Icc (0 : ℝ) 1, α 0 t = γ t) → (∀ t ∈ Icc (0 : ℝ) 1, α' 0 t = γ t) →
      (∀ t ∈ Icc (0 : ℝ) 1,
        deriv (fun u₁ => α (u₁, 0) t) 0 = deriv (fun u₁ => α' (u₁, 0) t) 0) →
      (∀ t ∈ Icc (0 : ℝ) 1,
        deriv (fun u₂ => α (0, u₂) t) 0 = deriv (fun u₂ => α' (0, u₂) t) 0) →
      deriv (fun u₁ => deriv (fun u₂ => Morse.energy (α (u₁, u₂)) 0 1) 0) 0 =
        deriv (fun u₁ => deriv (fun u₂ => Morse.energy (α' (u₁, u₂)) 0 1) 0) 0)

/-- `A_emb` is A's special case. -/
theorem A_to_A_emb : A → A_emb := fun hA _ _ _ _ _ _ _ _ _ _ hN _ =>
  ⟨fun hgeo _ _ _ hα hαγ => hA.1 hN hgeo hα hαγ,
    fun hgeo _ _ _ _ _ _ hα hα' hαγ hα'γ h₁ h₂ => hA.2 hN hgeo hα hα' hαγ hα'γ h₁ h₂⟩

open Emb in
/-- **Theorem 13.1 on `↥N` from `B_emb`**: lift the project variation (reparametrized by
`ψ : ℝ² ≃ ℝ × ℝ`) to a blind one along a subdivision avoiding its break points, take for
`D1, D2, Rv` the induced covariant derivatives and the curvature, apply `B_emb`, and read its right
side back with `sv_eq_rhs`; `mixedD` is the project's iterated derivative by `EnergyC2`. -/
theorem sv_of_B_emb (h : B_emb) {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W]
    [FiniteDimensional ℝ W] {n : ℕ} {N : Set V} {hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N}
    [ConnectedSpace (Bridge.Sub hN)] {γ : ℝ → V} (hgeo : Morse.IsUnbrokenGeodesic hN γ)
    {U : Set (ℝ × ℝ)} {α : ℝ × ℝ → ℝ → V} {B : Finset ℝ} (hα : Morse.IsVariation N U α B)
    (hαγ : ∀ t ∈ Icc (0 : ℝ) 1, α 0 t = γ t) :
    HasDerivAt (fun u₁ => deriv (fun u₂ => Morse.energy (α (u₁, u₂)) 0 1) 0)
      (2 * Morse.secondVariation hN γ (fun t => deriv (fun u₁ => α (u₁, 0) t) 0)
        (fun t => deriv (fun u₂ => α (0, u₂) t) 0)) 0 := by
  -- the parameters: `ψ u = (u₀, u₁)`
  set ψ : Rn 2 →L[ℝ] ℝ × ℝ :=
    (EuclideanSpace.proj (0 : Fin 2) : Rn 2 →L[ℝ] ℝ).prod (EuclideanSpace.proj (1 : Fin 2))
  have hψ : ∀ s r : ℝ, ψ (s • e0 + r • e1) = (s, r) := fun s r => by
    simp [ψ]
  have hα2 : Morse.IsVariation N (ψ ⁻¹' U) (fun u => α (ψ u)) B :=
    hα.comp ψ.contDiff (by simpa using hα.zero_mem)
  -- the blind variation
  obtain ⟨k, t, ht0, htk, hlt, hgood⟩ := exists_subdiv B
  set p₀ : Bridge.Sub hN := ⟨α 0 0, hα.mem 0 hα.zero_mem 0 ⟨le_rfl, zero_le_one⟩⟩
  set αb : Rn 2 → ℝ → Bridge.Sub hN := fun u => Bridge.lift (α (ψ u)) p₀
  have hvs : IsVarSub (n := n) (ψ ⁻¹' U) αb k t := isVarSub_lift hα2 p₀ ht0 htk hlt hgood
  have h0 : (0 : Rn 2) ∈ ψ ⁻¹' U := hα2.zero_mem
  have hinc : ∀ u ∈ ψ ⁻¹' U, ∀ s ∈ Icc (0 : ℝ) 1, Bridge.incl hN (αb u s) = α (ψ u) s :=
    fun u hu s hs => Bridge.incl_lift p₀ (hα.mem _ hu s hs)
  have hpath : ∀ s ∈ Icc (0 : ℝ) 1, (Bridge.incl hN ∘ αb 0) s = γ s := fun s hs => by
    rw [Function.comp_apply, hinc 0 h0 s hs, map_zero, hαγ s hs]
  have hgeo' : IsGeodesic (Bridge.conn (hN := hN)) (αb 0) (Icc 0 1) :=
    isGeodesic_of_isUnbrokenGeodesic (isUnbrokenGeodesic_congr (fun s hs => (hpath s hs).symm) hgeo)
  -- the fields, read in `V`
  have hX : ∀ (i : Fin 2) (τ : ℝ), τ ∈ Icc (0 : ℝ) 1 →
      Bridge.ambA (αb 0) (varField (n := n) αb i) τ =
        deriv (fun r : ℝ => α (ψ (r • EuclideanSpace.single i (1 : ℝ))) τ) 0 := by
    intro i τ hτ
    rw [Bridge.ambA, D_varField hvs i hτ]
    refine Filter.EventuallyEq.deriv_eq ?_
    have hc : Continuous fun r : ℝ => r • (EuclideanSpace.single i (1 : ℝ) : Rn 2) :=
      continuous_id.smul continuous_const
    filter_upwards [(hvs.1.preimage hc).mem_nhds (by simpa using h0)] with r hr
    exact hinc _ hr τ hτ
  have hψ0 : ∀ r : ℝ, ψ (r • EuclideanSpace.single (0 : Fin 2) (1 : ℝ)) = (r, 0) := fun r => by
    simpa using hψ r 0
  have hψ1 : ∀ r : ℝ, ψ (r • EuclideanSpace.single (1 : Fin 2) (1 : ℝ)) = (0, r) := fun r => by
    simpa using hψ 0 r
  have hX₁ : ∀ τ ∈ Icc (0 : ℝ) 1, Bridge.ambA (αb 0) (varField (n := n) αb 0) τ =
      deriv (fun u₁ => α (u₁, 0) τ) 0 := fun τ hτ => by
    rw [hX 0 τ hτ]; simp only [hψ0]
  have hX₂ : ∀ τ ∈ Icc (0 : ℝ) 1, Bridge.ambA (αb 0) (varField (n := n) αb 1) τ =
      deriv (fun u₂ => α (0, u₂) τ) 0 := fun τ hτ => by
    rw [hX 1 τ hτ]; simp only [hψ1]
  have hσ₁ : Morse.IsVariation N {r : ℝ | (r, (0 : ℝ)) ∈ U} (fun r => α (r, 0)) B :=
    hα.comp (φ := fun r => (r, (0 : ℝ))) (contDiff_id.prodMk contDiff_const) hα.zero_mem
  have hσ₂ : Morse.IsVariation N {r : ℝ | ((0 : ℝ), r) ∈ U} (fun r => α (0, r)) B :=
    hα.comp (φ := fun r => ((0 : ℝ), r)) (contDiff_const.prodMk contDiff_id) hα.zero_mem
  have hW₂ : ContinuousOn (Bridge.ambA (αb 0) (varField (n := n) αb 1)) (Icc 0 1) :=
    ((Morse.mem_pathTangent hN).1 (hσ₂.varField_mem hN)).1.2.1.congr hX₂
  -- the blind data `D1, D2, Rv`
  have hpiece : ∀ i < k, Icc (t i) (t (i + 1)) ⊆ Icc 0 1 := fun i hi =>
    Icc_subset_Icc (hgood i hi).1 (hgood i hi).2.1
  have hIntv : ∀ i < k, RoundTrip.BridgePrelude.IsIntv (Icc (t i) (t (i + 1))) := fun i hi =>
    ⟨ordConnected_Icc, uniqueDiffOn_Icc (hlt i hi)⟩
  have hcurve : ∀ i < k,
      RoundTrip.BridgePrelude.IsSmoothCurve (n := n) (αb 0) (Icc (t i) (t (i + 1))) :=
    fun i hi => ContMDiffOn.mono hgeo'.2.1 (hpiece i hi)
  have hW₁s : ∀ i < k, ContDiffOn ℝ ∞ (Bridge.ambA (αb 0) (varField (n := n) αb 0))
      (Icc (t i) (t (i + 1))) := fun i hi =>
    (contDiffOn_varField hσ₁ (hgood i hi).1 (hlt i hi) (hgood i hi).2.1 (hgood i hi).2.2).congr
      fun τ hτ => hX₁ τ (hpiece i hi hτ)
  set D1 : ℕ → FA n (αb 0) := fun i =>
    Bridge.covA (αb 0) (Icc (t i) (t (i + 1))) (varField (n := n) αb 0)
  set D2 : ℕ → FA n (αb 0) := fun i => Bridge.covA (αb 0) (Icc (t i) (t (i + 1))) (D1 i)
  have hD1s : ∀ i < k, ContDiffOn ℝ ∞ (Bridge.ambA (αb 0) (D1 i)) (Icc (t i) (t (i + 1))) := by
    intro i hi
    have hP : ContDiffOn ℝ ∞ (fun τ => Bridge.P hN (αb 0 τ)) (Icc (t i) (t (i + 1))) :=
      contMDiffOn_iff_contDiffOn.1 (Bridge.contMDiff_P.comp_contMDiffOn (hcurve i hi))
    have hd : ContDiffOn ℝ ∞ (derivWithin (Bridge.ambA (αb 0) (varField (n := n) αb 0))
        (Icc (t i) (t (i + 1)))) (Icc (t i) (t (i + 1))) :=
      (hW₁s i hi).derivWithin (uniqueDiffOn_Icc (hlt i hi)) (m := ∞) (by simp)
    refine (hP.clm_apply hd).congr fun τ _ => ?_
    exact Bridge.D_covA _ _ _ _
  have hD : ∀ i < k,
      HasCovDeriv (Bridge.conn (hN := hN)) (αb 0) (Icc (t i) (t (i + 1)))
        (varField (n := n) αb 0) (D1 i) ∧
      HasCovDeriv (Bridge.conn (hN := hN)) (αb 0) (Icc (t i) (t (i + 1))) (D1 i) (D2 i) := by
    intro i hi
    exact ⟨(Bridge.hasCovDeriv_iff (hIntv i hi) (hcurve i hi)).2
        ⟨Bridge.isSmoothAlong_iff.2 ⟨hcurve i hi, hW₁s i hi⟩, fun _ _ => rfl⟩,
      (Bridge.hasCovDeriv_iff (hIntv i hi) (hcurve i hi)).2
        ⟨Bridge.isSmoothAlong_iff.2 ⟨hcurve i hi, hD1s i hi⟩, fun _ _ => rfl⟩⟩
  set Rv : FA n (αb 0) := fun s => Bridge.L hN (αb 0 s)
    (Morse.curvR hN (Bridge.incl hN (αb 0 s))
      (Bridge.D hN (αb 0 s) (vel (n := n) (αb 0) (Icc 0 1) s))
      (Bridge.D hN (αb 0 s) (varField (n := n) αb 0 s))
      (Bridge.D hN (αb 0 s) (vel (n := n) (αb 0) (Icc 0 1) s)))
  have hR : ∀ s ∈ Icc (0 : ℝ) 1, IsCurvVal (Bridge.conn (hN := hN)) (αb 0 s)
      (vel (n := n) (αb 0) (Icc 0 1) s) (varField (n := n) αb 0 s)
      (vel (n := n) (αb 0) (Icc 0 1) s) (Rv s) := by
    intro s _
    refine (Bridge.isCurvVal_iff _ _ _ _ _).2 (Bridge.D_L ?_)
    show Morse.curvR hN (αb 0 s).1 _ _ _ ∈ _
    rw [Morse.curvR_of_mem hN (αb 0 s).2]
    exact Morse.curvOp_mem hN (Bridge.D_mem _ _) (Bridge.D_mem _ _) (Bridge.D_mem _ _)
  -- apply `B_emb`
  obtain ⟨-, hval⟩ := h V W n N hN (ψ ⁻¹' U) αb k t hvs hgeo' D1 D2 Rv hD hR
  rw [← sv_eq_rhs hgeo' ht0 htk hlt hW₂ D1 D2 Rv hD hR, sv_congr_path hpath,
    Morse.secondVariation_congr hN hX₁ hX₂] at hval
  -- `mixedD` is the iterated derivative of `F = E ∘ α`
  set F : ℝ × ℝ → ℝ := fun p => Morse.energy (α p) 0 1
  have hF : ContDiffOn ℝ ∞ F U := hα.contDiffOn_energy
  have hFψ : ContDiffOn ℝ 2 (F ∘ ψ) (ψ ⁻¹' U) :=
    (hF.comp ψ.contDiff.contDiffOn fun _ hu => hu).of_le ENat.LEInfty.out
  have hev : (fun v : Rn 2 => Efun (n := n) (αb v)) =ᶠ[𝓝 0] F ∘ ψ := by
    filter_upwards [hvs.1.mem_nhds h0] with v hv
    show Efun (n := n) (αb v) = Morse.energy (α (ψ v)) 0 1
    rw [show Efun (n := n) (αb v) = Morse.energy (Bridge.incl hN ∘ αb v) 0 1 from
      Bridge.energy_eq _ 0 1]
    exact Morse.energy_congr fun s hs => hinc v hv s hs
  have hmix : mixedD (fun v : Rn 2 => Efun (n := n) (αb v)) =
      deriv (fun u₁ => deriv (fun u₂ => F (u₁, u₂)) 0) 0 := by
    have e1' : (fun u : Rn 2 => fderiv ℝ (fun v : Rn 2 => Efun (n := n) (αb v)) u e0) =ᶠ[𝓝 0]
        fun u => fderiv ℝ (F ∘ ψ) u e0 := by
      filter_upwards [hev.eventuallyEq_nhds] with u hu
      rw [hu.fderiv_eq]
    have e2 := RoundTrip.EnergyC2.fderiv_fderiv_apply_eq_deriv_deriv hvs.1 hFψ h0 e0 e1
    simp only [zero_add, Function.comp_apply, hψ] at e2
    show fderiv ℝ (fun u : Rn 2 => fderiv ℝ (fun v : Rn 2 => Efun (n := n) (αb v)) u e0) 0 e1 = _
    rw [e1'.fderiv_eq, e2]
  -- differentiability of `u₁ ↦ ∂F/∂u₂ (u₁, 0)`
  have hU0 : (0 : ℝ × ℝ) ∈ U := hα.zero_mem
  have hg : (fun u₁ => deriv (fun u₂ => F (u₁, u₂)) 0) =ᶠ[𝓝 0]
      fun u₁ => fderiv ℝ F (u₁, 0) (0, 1) := by
    have hc : Continuous fun u₁ : ℝ => (u₁, (0 : ℝ)) := continuous_id.prodMk continuous_const
    filter_upwards [(hα.isOpen.preimage hc).mem_nhds (show ((0 : ℝ), (0 : ℝ)) ∈ U from hU0)]
      with u₁ hu₁
    have hd : DifferentiableAt ℝ F (u₁, 0) :=
      (hF.differentiableOn (by simp)).differentiableAt (hα.isOpen.mem_nhds hu₁)
    have := RoundTrip.EnergyC2.hasDerivAt_line hd ((0 : ℝ), (1 : ℝ))
    simp only [Prod.smul_mk, smul_eq_mul, mul_zero, mul_one, Prod.mk_add_mk, add_zero,
      zero_add] at this
    exact this.deriv
  have hgd : DifferentiableAt ℝ (fun u₁ => fderiv ℝ F (u₁, 0) (0, 1)) 0 := by
    have hF2 : ContDiffOn ℝ 2 F U := hF.of_le ENat.LEInfty.out
    have h1 : DifferentiableAt ℝ (fderiv ℝ F) ((0 : ℝ), (0 : ℝ)) :=
      ((hF2.fderiv_of_isOpen hα.isOpen (by norm_num : (1 : ℕ∞ω) + 1 ≤ 2)).differentiableOn
        one_ne_zero).differentiableAt (hα.isOpen.mem_nhds hU0)
    have h2 : DifferentiableAt ℝ (fun u₁ : ℝ => (u₁, (0 : ℝ))) 0 :=
      differentiableAt_id.prodMk (differentiableAt_const _)
    exact (DifferentiableAt.comp (f := fun u₁ : ℝ => (u₁, (0 : ℝ))) (0 : ℝ) h1 h2).clm_apply
      (differentiableAt_const _)
  have hgd' := (hgd.congr_of_eventuallyEq hg).hasDerivAt
  rw [← hmix] at hgd'
  have e : mixedD (fun v : Rn 2 => Efun (n := n) (αb v)) =
      2 * Morse.secondVariation hN γ (fun t => deriv (fun u₁ => α (u₁, 0) t) 0)
        (fun t => deriv (fun u₂ => α (0, u₂) t) 0) := by
    linarith
  rw [e] at hgd'
  exact hgd'

/-- **`B_emb ⇒ A_emb`**: Theorem 13.1 on `↥N` from `B_emb` (`sv_of_B_emb`), and its corollary
by the project's argument (both iterated derivatives are `2 secondVariation`, which only depends
on the fields on `[0, 1]`). -/
theorem B_emb_to_A_emb : B_emb → A_emb := by
  intro h V _ _ _ W _ _ _ n N hN _
  refine ⟨fun hgeo _ _ _ hα hαγ => sv_of_B_emb h hgeo hα hαγ, ?_⟩
  intro γ hgeo U U' α α' B B' hα hα' hαγ hα'γ h₁ h₂
  rw [(sv_of_B_emb h hgeo hα hαγ).deriv, (sv_of_B_emb h hgeo hα' hα'γ).deriv]
  congr 1
  exact Morse.secondVariation_congr hN h₁ h₂

theorem B_to_A_emb : B → A_emb := fun hB => B_emb_to_A_emb (B_to_B_emb hB)

#rt_check RoundTrip.V8_13.B_to_A_emb [Morse.second_variation, Morse.second_variation_eq]
#rt_overlap RoundTrip.V8_13.B_to_A_emb [Morse.second_variation, Morse.second_variation_eq]

end RoundTrip.V8_13
