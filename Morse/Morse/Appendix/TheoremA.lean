import Morse.Appendix.Telescope

/-!
Milnor, *Morse Theory*, Appendix, pp. 150–153: Theorem A.

# Maps which are homotopy equivalences level by level

**Theorem A** (p. 150), paraphrased: let `X` and `Y` be the homotopy direct limits of `{X_i}` and
`{Y_i}`, and let `f : X → Y` carry each `X_i` into `Y_i` by a homotopy equivalence. Then `f` is a
homotopy equivalence (`Morse.theoremA`).

Milnor's proof reduces to the map of telescopes `f_Σ(x, τ) = (f(x), τ)`, "clearly sufficient"
(`Morse.IsHomotopyEquiv.of_telescopeMap`), and proves that `f_Σ` is a homotopy equivalence in two
cases.

*Case 1* (pp. 150–152): `X_i = Y_i` and each `f_i` is homotopic to the identity of `X_i`. With
homotopies `h^n_u : X_n → X_n` from `f_n` to the identity, he defines `h_u : X_Σ → X_Σ` strip by
strip (`Morse.case1Fun`); `h_0` is homotopic to `f_Σ`, and `h_1` belongs to a class of maps which
he shows to be homotopy equivalences, with an explicit homotopy inverse `g` and explicit homotopies
`H_u` from `h_1 g` to (a reparametrization of) the identity (`Morse.isHomotopyEquiv_of_milnorMap`).
*Case 2* (pp. 152–153): the general case. With homotopy inverses `g_n` of `f_n` and homotopies
`h^n_u : Y_n → X_{n+1}` from `i_n g_n` to `g_{n+1} j_n`, he defines `G : Y_Σ → X_Σ`
(`Morse.case2Inv`); `G f_Σ` and `f_Σ G` preserve the truncations `X^m_Σ`, `Y^m_Σ` and are homotopic
to the identity on each, so Case 1 applies to them; hence `f_Σ` has a left and a right homotopy
inverse (`Morse.theoremA_telescope`).

## What Milnor's text leaves implicit

* **Closedness.** Every map of Milnor's proof is defined strip by strip, and pasting needs (T3)
  of `Morse/Appendix/Telescope.lean`: the sets must be closed. Milnor does not say so. In Case 1,
  as he states it, the `X_i` must be closed: the exposition gives an example (`X = [0,1]`,
  `X_0 = (0,1]`) where his `g` is discontinuous (`Morse.theoremA_case1` assumes them closed).
  In Case 2, however, Case 1 is applied only to the truncations `X^m_Σ`, `Y^m_Σ`, which are always
  closed, and the only map defined strip by strip on a telescope of the original sets is
  `G : Y_Σ → X_Σ`. So **the proof of Theorem A needs only the `Y_i` closed**
  (`Morse.theoremA`). In his application the `Y_i` are subcomplexes, hence closed. Milnor's
  statement itself needs no closedness: `Morse.theoremA_general`
  (`Morse/Appendix/MonotoneUnion.lean`) runs the same proof on the mapping telescopes of the
  inclusions, whose truncations are closed.
* **A misprint** (p. 151): the third line of `h_u` reads `h^{n+1}_{(4-3t)u}`; at `t = 3/4` this
  would be `h^{n+1}_{7u/4}`. It must be `h^{n+1}_{(4t-3)u}`, which runs from
  `h^{n+1}_0 = f_{n+1}` at `t = 3/4` to `h^{n+1}_u` at `t = 1`; this is what `Morse.case1Fun` uses.
  The second line, `h^n_{(3-4t)u}`, is correct.
* **"`h_0` is clearly homotopic to `f_Σ`"**: `h_0 = f_Σ ∘ R₂`, where `R₂(x, n + t) =
  (x, n + min(2t, 1))` is homotopic to the identity by reparametrizing each strip
  (`Morse.reparam_homotopic`).
* **"Any such map `h_1`" is a homotopy equivalence**: the class is that of maps with
  `h_1(x, n + t) = (x, n + 2t)` for `t ≤ 1/2` and `h_1(x, n + t) ∈ X_{n+1} × [n+1]` for
  `t ≥ 1/2` (`Morse.isHomotopyEquiv_of_milnorMap`). Milnor's `g` is `Morse.milnorInv`. His
  computation of `h_1 g` uses that `h_1` fixes the points at integer levels (from the first
  property at `t = 0`).
* **Milnor's `H_u`** (p. 151, `0 ≤ u ≤ 1/2`) is, with `u` rescaled to `[0, 1]`, the single formula
  `(x, n + t) ↦ (x, n + 4t)` for `t ≤ 1/4` and `h_1(x, n + 1/2 + μ/2)` for `t ≥ 1/4`, with
  `μ = min(4t - 1, 1 - u, 2 - 2t)` (`Morse.loopFun`). Its end `H_1` is `R₄(x, n + t) =
  (x, n + min(4t, 1))`, "clearly homotopic to the identity" (`Morse.reparam_homotopic`).
* **`g h_1 ≃ id` "by a completely analogous argument"** (p. 152): the analogous homotopy is the
  same formula with `μ = max(2 - 4t, 2t - 1, u)`.
* **Case 2 needs Case 1 for the space `X_Σ` and its truncations**, and then returns from the
  telescope of `{X^m_Σ}` to `X_Σ`; this uses that `X_Σ` is the homotopy direct limit of its
  truncations (`Morse.isHomotopyDirectLimit_truncation`), which Milnor does not mention. The
  truncations are closed, as Case 1 requires. That `G f_Σ` restricted to `X^m_Σ` is homotopic to
  the identity is the chain `G f_Σ ≃ G f_Σ ι r = ι (g_m f_m) r ≃ ι r ≃ id`, with `r` the
  deformation of (T2) (`Morse.isHomotopyEquiv_of_truncation`).
* **The end of Case 2** ("compare page 22", p. 153): a map with a left and a right homotopy
  inverse is a homotopy equivalence (`Morse.IsHomotopyEquiv.of_leftInv_rightInv`).
* **The homotopy direct limit hypotheses are used only at the very end**: `f_Σ` is a homotopy
  equivalence as soon as the `Y_i` are closed (`Morse.theoremA_telescope`). Chapter 10 of the
  exposition uses Theorem A for telescopes of open sets and their (closed) truncations.

## Main results

* `Morse.reparam`, `Morse.reparam_homotopic`: reparametrizing the strips.
* `Morse.IsMilnorMap`, `Morse.milnorInv`, `Morse.isHomotopyEquiv_of_milnorMap`: Milnor's `h_1`,
  `g`, `H_u`.
* `Morse.case1Fun`, `Morse.theoremA_case1`: **Case 1**.
* `Morse.isHomotopyEquiv_of_truncation`, `Morse.case2Inv`, `Morse.theoremA_telescope`: **Case 2**.
* `Morse.theoremA`: **Theorem A**, with the `Y_i` closed.
-/

open Set Filter Topology Function
open scoped unitInterval

noncomputable section

namespace Morse

variable {X : Type*} [TopologicalSpace X] {A : ℕ → Set X}

theorem clampI_two_mul {t : I} (h : (t : ℝ) ≤ 1 / 2) : (clampI (2 * t) : ℝ) = 2 * t :=
  clampI_val (by linarith [t.2.1]) (by linarith)

theorem continuous_param {P : Type*} [TopologicalSpace P] {n : ℕ} :
    Continuous fun q : P × (A n × I) => ((q.2.2 : I) : ℝ) :=
  continuous_subtype_val.comp (continuous_snd.comp continuous_snd)

/-! ### Reparametrizing the strips -/

section Reparam

/-- `(x, n + t) ↦ (x, n + ρ(t))`, for `ρ : [0, 1] → [0, 1]` fixing `0` and `1`. -/
def reparam (hA : Monotone A) (hAc : ∀ n, IsClosed (A n)) (ρ : C(I, I)) (h₀ : ρ 0 = 0)
    (h₁ : ρ 1 = 1) : C(telescope A, telescope A) :=
  telescopeDesc hA hAc
    (fun n => (stripMap A n).comp (ContinuousMap.fst.prodMk (ρ.comp ContinuousMap.snd)))
    (fun n x => by
      change stripMap A (n + 1) (up hA n x, ρ 0) = stripMap A n (x, ρ 1)
      rw [h₀, h₁, stripMap_one hA])

@[simp]
theorem reparam_stripMap (hA : Monotone A) (hAc : ∀ n, IsClosed (A n)) (ρ : C(I, I))
    (h₀ : ρ 0 = 0) (h₁ : ρ 1 = 1) (n : ℕ) (x : A n) (t : I) :
    reparam hA hAc ρ h₀ h₁ (stripMap A n (x, t)) = stripMap A n (x, ρ t) :=
  telescopeDesc_stripMap hA hAc _ _ n x t

/-- **Reparametrizing the strips is homotopic to the identity**: the straight-line homotopy
`(x, n + t) ↦ (x, n + (1 - s) ρ(t) + s t)` stays in each strip. This is Milnor's "clearly
homotopic" for `h_0 ≃ f_Σ` (p. 151) and for `H_{1/2} ≃ id` (p. 152). -/
theorem reparam_homotopic (hA : Monotone A) (hAc : ∀ n, IsClosed (A n)) (ρ : C(I, I))
    (h₀ : ρ 0 = 0) (h₁ : ρ 1 = 1) : (reparam hA hAc ρ h₀ h₁).Homotopic (ContinuousMap.id _) := by
  refine ⟨telescopeHomotopy hA hAc (fun n => ⟨fun q => stripMap A n
    (q.2.1, clampI ((1 - (q.1 : ℝ)) * ρ q.2.2 + q.1 * q.2.2)), ?_⟩) ?_ ?_ ?_⟩
  · refine (stripMap A n).continuous.comp ((continuous_fst.comp continuous_snd).prodMk
      (continuous_clampI.comp ?_))
    have hs : Continuous fun q : I × (A n × I) => ((q.1 : I) : ℝ) :=
      continuous_subtype_val.comp continuous_fst
    exact ((continuous_const.sub hs).mul (continuous_subtype_val.comp (ρ.continuous.comp
      (continuous_snd.comp continuous_snd)))).add (hs.mul continuous_param)
  · intro n s x
    change stripMap A (n + 1) (up hA n x, clampI ((1 - (s : ℝ)) * ρ 0 + s * ((0 : I) : ℝ))) =
      stripMap A n (x, clampI ((1 - (s : ℝ)) * ρ 1 + s * ((1 : I) : ℝ)))
    rw [h₀, h₁, clampI_eq (t := 0) (by simp), clampI_eq (t := 1) (by simp), stripMap_one hA]
  · intro n x t
    change stripMap A n (x, clampI ((1 - ((0 : I) : ℝ)) * ρ t + ((0 : I) : ℝ) * t)) =
      reparam hA hAc ρ h₀ h₁ (stripMap A n (x, t))
    rw [reparam_stripMap, clampI_eq (t := ρ t) (by simp)]
  · intro n x t
    change stripMap A n (x, clampI ((1 - ((1 : I) : ℝ)) * ρ t + ((1 : I) : ℝ) * t)) =
      stripMap A n (x, t)
    rw [clampI_eq (t := t) (by simp)]

/-- `t ↦ min(c t, 1)` (for `c ≥ 0`). -/
def scaleI (c : ℝ) : C(I, I) :=
  ⟨fun t => clampI (c * t), continuous_clampI.comp (continuous_const.mul continuous_subtype_val)⟩

theorem scaleI_zero (c : ℝ) : scaleI c 0 = 0 := by
  change clampI (c * ((0 : I) : ℝ)) = 0
  rw [Set.Icc.coe_zero, mul_zero, clampI_zero]

theorem scaleI_one (c : ℝ) (hc : 1 ≤ c) : scaleI c 1 = 1 := by
  change clampI (c * ((1 : I) : ℝ)) = 1
  rw [Set.Icc.coe_one, mul_one, clampI_of_one_le hc]

/-- Milnor's `R_c(x, n + t) = (x, n + min(ct, 1))`, for `c ≥ 1`. -/
def scaleMap (hA : Monotone A) (hAc : ∀ n, IsClosed (A n)) (c : ℝ) (hc : 1 ≤ c) :
    C(telescope A, telescope A) :=
  reparam hA hAc (scaleI c) (scaleI_zero c) (scaleI_one c hc)

theorem scaleMap_stripMap (hA : Monotone A) (hAc : ∀ n, IsClosed (A n)) (c : ℝ) (hc : 1 ≤ c)
    (n : ℕ) (x : A n) (t : I) :
    scaleMap hA hAc c hc (stripMap A n (x, t)) = stripMap A n (x, clampI (c * t)) :=
  reparam_stripMap hA hAc _ _ _ n x t

theorem scaleMap_homotopic (hA : Monotone A) (hAc : ∀ n, IsClosed (A n)) (c : ℝ) (hc : 1 ≤ c) :
    (scaleMap hA hAc c hc).Homotopic (ContinuousMap.id _) :=
  reparam_homotopic hA hAc _ _ _

end Reparam

/-! ### Milnor's `h_1` and its homotopy inverse `g` (pp. 151–152) -/

section MilnorMap

/-- **The properties of Milnor's `h_1`** (p. 151): `h_1(x, n + t) = (x, n + 2t)` for `t ≤ 1/2`,
and `h_1(x, n + t) ∈ X_{n+1} × [n+1]` for `t ≥ 1/2`. -/
structure IsMilnorMap (ψ : telescope A → telescope A) : Prop where
  low : ∀ n (x : A n) (t : I), (t : ℝ) ≤ 1 / 2 →
    ψ (stripMap A n (x, t)) = stripMap A n (x, clampI (2 * t))
  high : ∀ n (x : A n) (t : I), 1 / 2 ≤ (t : ℝ) → (ψ (stripMap A n (x, t)) : X × ℝ).2 = n + 1

variable {ψ : telescope A → telescope A}

/-- Such a map fixes the points at integer levels. -/
theorem IsMilnorMap.fix (hA : Monotone A) (hψ : IsMilnorMap ψ) {z : telescope A} {m : ℕ}
    (hz : (z : X × ℝ).2 = m) : ψ z = z := by
  rw [eq_stripMap_of_level hA hz, hψ.low m _ 0 (by norm_num)]
  exact stripMap_congr rfl (by simp)

theorem IsMilnorMap.fix_high (hA : Monotone A) (hψ : IsMilnorMap ψ) (n : ℕ) (x : A n) (t : I)
    (ht : 1 / 2 ≤ (t : ℝ)) : ψ (ψ (stripMap A n (x, t))) = ψ (stripMap A n (x, t)) := by
  have := hψ.high n x t ht
  exact hψ.fix hA (m := n + 1) (by rw [this]; push_cast; ring)

theorem IsMilnorMap.apply_one (hA : Monotone A) (hψ : IsMilnorMap ψ) (n : ℕ) (x : A n) :
    ψ (stripMap A n (x, 1)) = stripMap A n (x, 1) :=
  hψ.fix hA (m := n + 1) (by simp)

/-- `ψ(x, n + 1/2 + μ/2) = (x, n + 1)` when `μ ∈ {0, 1}`. -/
theorem IsMilnorMap.apply_half_or_one (hA : Monotone A) (hψ : IsMilnorMap ψ) {μ : ℝ}
    (hμ : μ = 0 ∨ μ = 1) (n : ℕ) (x : A n) :
    ψ (stripMap A n (x, clampI (1 / 2 + μ / 2))) = stripMap A n (x, 1) := by
  rcases hμ with rfl | rfl
  · have h : ((clampI (1 / 2 + 0 / 2)) : ℝ) = 1 / 2 := by
      rw [clampI_val (by norm_num) (by norm_num)]; norm_num
    rw [hψ.low n x _ h.le, h]
    exact stripMap_congr rfl (by rw [clampI_eq (t := 1) (by norm_num)])
  · rw [clampI_eq (t := 1) (by norm_num)]
    exact hψ.apply_one hA n x

/-- The strip formula of Milnor's `g` (p. 151): `g(x, n + t) = (x, n + 2t)` for `t ≤ 1/2` and
`h_1(x, n + 3/2 - t)` for `t ≥ 1/2`. -/
def milnorInvStrip (hA : Monotone A) (ψ : C(telescope A, telescope A)) (hψ : IsMilnorMap ψ)
    (n : ℕ) :
    C(A n × I, telescope A) where
  toFun q := if (q.2 : ℝ) ≤ 1 / 2 then stripMap A n (q.1, clampI (2 * q.2))
    else ψ (stripMap A n (q.1, clampI (3 / 2 - q.2)))
  continuous_toFun := by
    have ht : Continuous fun q : A n × I => ((q.2 : I) : ℝ) :=
      continuous_subtype_val.comp continuous_snd
    refine Continuous.if_le ?_ ?_ ht continuous_const ?_
    · exact (stripMap A n).continuous.comp (continuous_fst.prodMk
        (continuous_clampI.comp (continuous_const.mul ht)))
    · exact ψ.continuous.comp ((stripMap A n).continuous.comp (continuous_fst.prodMk
        (continuous_clampI.comp (continuous_const.sub ht))))
    · intro q hq
      rw [hq, show (2 : ℝ) * (1 / 2) = 1 by norm_num, show (3 : ℝ) / 2 - 1 / 2 = 1 by norm_num,
        clampI_one, hψ.apply_one hA]

/-- **Milnor's homotopy inverse `g`** of `h_1` (p. 151). It is well defined since
`h_1(x, n + 1/2) = h_1(x, n + 1) = (x, n + 1)`. -/
def milnorInv (hA : Monotone A) (hAc : ∀ n, IsClosed (A n)) (ψ : C(telescope A, telescope A))
    (hψ : IsMilnorMap ψ) :
    C(telescope A, telescope A) :=
  telescopeDesc hA hAc (milnorInvStrip hA ψ hψ) fun n x => by
    change (if ((0 : I) : ℝ) ≤ 1 / 2 then stripMap A (n + 1) (up hA n x, clampI (2 * (0 : I)))
      else ψ (stripMap A (n + 1) (up hA n x, clampI (3 / 2 - (0 : I))))) =
      (if ((1 : I) : ℝ) ≤ 1 / 2 then stripMap A n (x, clampI (2 * (1 : I)))
      else ψ (stripMap A n (x, clampI (3 / 2 - (1 : I)))))
    rw [if_pos (by norm_num), if_neg (by norm_num)]
    have h : ((clampI (3 / 2 - ((1 : I) : ℝ))) : ℝ) = 1 / 2 := by
      rw [clampI_val (by norm_num) (by norm_num)]; norm_num
    rw [hψ.low n x _ h.le, h, show (2 : ℝ) * (1 / 2) = 1 by norm_num, clampI_one, stripMap_one hA]
    exact stripMap_congr rfl (by simp)

theorem milnorInv_low (hA : Monotone A) (hAc : ∀ n, IsClosed (A n))
    (ψ : C(telescope A, telescope A)) (hψ : IsMilnorMap ψ) (n : ℕ) (x : A n)
    (t : I) (ht : (t : ℝ) ≤ 1 / 2) :
    milnorInv hA hAc ψ hψ (stripMap A n (x, t)) = stripMap A n (x, clampI (2 * t)) := by
  rw [milnorInv, telescopeDesc_stripMap]
  exact if_pos ht

theorem milnorInv_high (hA : Monotone A) (hAc : ∀ n, IsClosed (A n))
    (ψ : C(telescope A, telescope A)) (hψ : IsMilnorMap ψ) (n : ℕ) (x : A n)
    (t : I) (ht : 1 / 2 < (t : ℝ)) :
    milnorInv hA hAc ψ hψ (stripMap A n (x, t)) = ψ (stripMap A n (x, clampI (3 / 2 - t))) := by
  rw [milnorInv, telescopeDesc_stripMap]
  exact if_neg (not_le.2 ht)

theorem milnorInv_isMilnorMap (hA : Monotone A) (hAc : ∀ n, IsClosed (A n))
    (ψ : C(telescope A, telescope A)) (hψ : IsMilnorMap ψ) :
    IsMilnorMap (milnorInv hA hAc ψ hψ) where
  low := milnorInv_low hA hAc ψ hψ
  high n x t ht := by
    rcases eq_or_lt_of_le ht with h | h
    · rw [milnorInv_low hA hAc ψ hψ n x t h.ge, stripMap_apply_snd, ← h]
      simp
    · rw [milnorInv_high hA hAc ψ hψ n x t h]
      exact hψ.high n x _ (by rw [clampI_val (by linarith [t.2.2]) (by linarith)]; linarith [t.2.2])

/-- **Milnor's homotopies `H_u` and `K_u`** (pp. 151–152) have, on the strip `n`, the form
`(x, n + t) ↦ (x, n + 4t)` for `t ≤ 1/4` and `ψ(x, n + 1/2 + μ(u, t)/2)` for `t ≥ 1/4`. -/
def loopFun (ψ : C(telescope A, telescope A)) (μ : ℝ → ℝ → ℝ) (n : ℕ) (q : I × (A n × I)) :
    telescope A :=
  if (q.2.2 : ℝ) ≤ 1 / 4 then stripMap A n (q.2.1, clampI (4 * q.2.2))
  else ψ (stripMap A n (q.2.1, clampI (1 / 2 + μ q.1 q.2.2 / 2)))

theorem continuous_loopFun (hA : Monotone A) (ψ : C(telescope A, telescope A)) (hψ : IsMilnorMap ψ)
    {μ : ℝ → ℝ → ℝ} (hμc : Continuous fun p : ℝ × ℝ => μ p.1 p.2)
    (hμ : ∀ u : I, μ u (1 / 4) = 0 ∨ μ u (1 / 4) = 1) (n : ℕ) :
    Continuous (loopFun ψ μ n) := by
  refine Continuous.if_le ?_ ?_ continuous_param continuous_const ?_
  · exact (stripMap A n).continuous.comp ((continuous_fst.comp continuous_snd).prodMk
      (continuous_clampI.comp (continuous_const.mul continuous_param)))
  · refine ψ.continuous.comp ((stripMap A n).continuous.comp ((continuous_fst.comp
      continuous_snd).prodMk (continuous_clampI.comp (continuous_const.add
        (Continuous.div_const ?_ _)))))
    exact hμc.comp ((continuous_subtype_val.comp continuous_fst).prodMk continuous_param)
  · intro q hq
    rw [hq, hψ.apply_half_or_one hA (hμ q.1)]
    exact stripMap_congr rfl (by rw [clampI_eq (t := 1) (by norm_num)])

/-- The loop homotopies, as homotopies of maps of the telescope. -/
def loopHomotopy (hA : Monotone A) (hAc : ∀ n, IsClosed (A n))
    (ψ : C(telescope A, telescope A)) (hψ : IsMilnorMap ψ) {μ : ℝ → ℝ → ℝ}
    (hμc : Continuous fun p : ℝ × ℝ => μ p.1 p.2)
    (hμ : ∀ u : I, μ u (1 / 4) = 0 ∨ μ u (1 / 4) = 1) (hμ₁ : ∀ u : I, μ u 1 = 0 ∨ μ u 1 = 1)
    {f₀ f₁ : C(telescope A, telescope A)}
    (h₀ : ∀ n x t, loopFun ψ μ n (0, (x, t)) = f₀ (stripMap A n (x, t)))
    (h₁ : ∀ n x t, loopFun ψ μ n (1, (x, t)) = f₁ (stripMap A n (x, t))) : f₀.Homotopy f₁ :=
  telescopeHomotopy hA hAc (fun n => ⟨loopFun ψ μ n, continuous_loopFun hA ψ hψ hμc hμ n⟩)
    (fun n u x => by
      change loopFun ψ μ (n + 1) (u, (up hA n x, 0)) = loopFun ψ μ n (u, (x, 1))
      unfold loopFun
      rw [if_pos (by norm_num), if_neg (by norm_num), Set.Icc.coe_one,
        hψ.apply_half_or_one hA (hμ₁ u), stripMap_one hA]
      exact stripMap_congr rfl (by simp))
    h₀ h₁

/-- Milnor's `μ` for `H_u`: `min(4t - 1, 1 - u, 2 - 2t)`. -/
def muH (u t : ℝ) : ℝ :=
  min (min (4 * t - 1) (1 - u)) (2 - 2 * t)

/-- The `μ` of the analogous homotopy `K_u`: `max(2 - 4t, 2t - 1, u)`. -/
def muK (u t : ℝ) : ℝ :=
  max (max (2 - 4 * t) (2 * t - 1)) u

theorem continuous_muH : Continuous fun p : ℝ × ℝ => muH p.1 p.2 :=
  ((continuous_const.mul continuous_snd).sub continuous_const |>.min
    (continuous_const.sub continuous_fst)).min (continuous_const.sub
      (continuous_const.mul continuous_snd))

theorem continuous_muK : Continuous fun p : ℝ × ℝ => muK p.1 p.2 :=
  ((continuous_const.sub (continuous_const.mul continuous_snd)).max
    ((continuous_const.mul continuous_snd).sub continuous_const)).max continuous_fst

theorem muH_zero_low {t : ℝ} (h : t ≤ 1 / 2) : muH 0 t = 4 * t - 1 := by
  unfold muH
  rw [min_eq_left (show 4 * t - 1 ≤ 1 - 0 by linarith),
    min_eq_left (show 4 * t - 1 ≤ 2 - 2 * t by linarith)]

theorem muH_zero_high {t : ℝ} (h : 1 / 2 ≤ t) : muH 0 t = 2 - 2 * t := by
  unfold muH
  rw [min_eq_right (show (1 : ℝ) - 0 ≤ 4 * t - 1 by linarith),
    min_eq_right (show 2 - 2 * t ≤ 1 - 0 by linarith)]

theorem muH_one {t : ℝ} (h₀ : 1 / 4 ≤ t) (h₁ : t ≤ 1) : muH 1 t = 0 := by
  unfold muH
  rw [min_eq_right (show (1 : ℝ) - 1 ≤ 4 * t - 1 by linarith),
    min_eq_left (show (1 : ℝ) - 1 ≤ 2 - 2 * t by linarith)]
  norm_num

theorem muH_quarter (u : I) : muH u (1 / 4) = 0 ∨ muH u (1 / 4) = 1 := by
  left
  have := u.2.2
  unfold muH
  rw [show (4 : ℝ) * (1 / 4) - 1 = 0 by norm_num, min_eq_left (show (0 : ℝ) ≤ 1 - u by linarith),
    min_eq_left (show (0 : ℝ) ≤ 2 - 2 * (1 / 4) by norm_num)]

theorem muH_end (u : I) : muH u 1 = 0 ∨ muH u 1 = 1 := by
  left
  have := u.2.2
  unfold muH
  rw [show (2 : ℝ) - 2 * 1 = 0 by norm_num,
    min_eq_right (show (0 : ℝ) ≤ min (4 * 1 - 1) (1 - (u : ℝ)) from
      le_min (by norm_num) (by linarith))]

theorem muK_zero_low {t : ℝ} (h : t ≤ 1 / 2) : muK 0 t = 2 - 4 * t := by
  unfold muK
  rw [max_eq_left (show 2 * t - 1 ≤ 2 - 4 * t by linarith),
    max_eq_left (show (0 : ℝ) ≤ 2 - 4 * t by linarith)]

theorem muK_zero_high {t : ℝ} (h : 1 / 2 ≤ t) : muK 0 t = 2 * t - 1 := by
  unfold muK
  rw [max_eq_right (show 2 - 4 * t ≤ 2 * t - 1 by linarith),
    max_eq_left (show (0 : ℝ) ≤ 2 * t - 1 by linarith)]

theorem muK_one {t : ℝ} (h₀ : 1 / 4 ≤ t) (h₁ : t ≤ 1) : muK 1 t = 1 :=
  max_eq_right (max_le (by linarith) (by linarith))

theorem muK_quarter (u : I) : muK u (1 / 4) = 0 ∨ muK u (1 / 4) = 1 := by
  right
  have := u.2.2
  unfold muK
  rw [show (2 : ℝ) - 4 * (1 / 4) = 1 by norm_num, max_eq_left (show 2 * (1 / 4) - 1 ≤ (1 : ℝ) by
    norm_num), max_eq_left this]

theorem muK_end (u : I) : muK u 1 = 0 ∨ muK u 1 = 1 := by
  right
  have := u.2.2
  unfold muK
  rw [show (2 : ℝ) * 1 - 1 = 1 by norm_num, max_eq_right (show 2 - 4 * 1 ≤ (1 : ℝ) by norm_num),
    max_eq_left this]

/-- At `u = 1` both loop homotopies are `R₄(x, n + t) = (x, n + min(4t, 1))`. -/
theorem loopFun_one (hA : Monotone A) (hAc : ∀ n, IsClosed (A n))
    (ψ : C(telescope A, telescope A)) (hψ : IsMilnorMap ψ) {μ : ℝ → ℝ → ℝ}
    (hμ : ∀ t : ℝ, 1 / 4 < t → t ≤ 1 → μ 1 t = 0 ∨ μ 1 t = 1) (n : ℕ) (x : A n) (t : I) :
    loopFun ψ μ n (1, (x, t)) = scaleMap hA hAc 4 (by norm_num) (stripMap A n (x, t)) := by
  rw [scaleMap_stripMap]
  simp only [loopFun, Set.Icc.coe_one]
  split_ifs with h
  · rfl
  · rw [hψ.apply_half_or_one hA (hμ t (not_le.1 h) t.2.2)]
    exact stripMap_congr rfl (by rw [clampI_of_one_le (by linarith [not_le.1 h])])

/-- **`h_1 g ≃ R₄`**: Milnor's homotopy `H_u` (p. 151), here with `u ∈ [0, 1]` standing for his
`2u`. -/
def milnorH (hA : Monotone A) (hAc : ∀ n, IsClosed (A n)) (ψ : C(telescope A, telescope A))
    (hψ : IsMilnorMap ψ) :
    (ψ.comp (milnorInv hA hAc ψ hψ)).Homotopy (scaleMap hA hAc 4 (by norm_num)) :=
  loopHomotopy hA hAc ψ hψ continuous_muH muH_quarter muH_end
    (fun n x t => by
      change loopFun ψ muH n (0, (x, t)) = ψ (milnorInv hA hAc ψ hψ (stripMap A n (x, t)))
      have ht0 := t.2.1
      have ht1 := t.2.2
      simp only [loopFun, Set.Icc.coe_zero]
      split_ifs with h
      · rw [milnorInv_low hA hAc ψ hψ n x t (by linarith), hψ.low n x _
          (by rw [clampI_two_mul (t := t) (by linarith)]; linarith)]
        exact stripMap_congr rfl (by
          rw [clampI_two_mul (t := t) (by linarith), show (2 : ℝ) * (2 * t) = 4 * t by ring])
      · rcases le_or_gt (t : ℝ) (1 / 2) with h' | h'
        · rw [milnorInv_low hA hAc ψ hψ n x t h', muH_zero_low h',
            show (1 : ℝ) / 2 + (4 * t - 1) / 2 = 2 * t by ring]
        · rw [milnorInv_high hA hAc ψ hψ n x t h', hψ.fix_high hA n x _
            (by rw [clampI_val (by linarith) (by linarith)]; linarith), muH_zero_high h'.le,
            show (1 : ℝ) / 2 + (2 - 2 * t) / 2 = 3 / 2 - t by ring])
    (fun n x t => loopFun_one hA hAc ψ hψ (fun _ h₁ h₂ => Or.inl (muH_one h₁.le h₂)) n x t)

/-- **`g h_1 ≃ R₄`**, "by a completely analogous argument" (Milnor, p. 152). -/
def milnorK (hA : Monotone A) (hAc : ∀ n, IsClosed (A n)) (ψ : C(telescope A, telescope A))
    (hψ : IsMilnorMap ψ) :
    ((milnorInv hA hAc ψ hψ).comp ψ).Homotopy (scaleMap hA hAc 4 (by norm_num)) :=
  loopHomotopy hA hAc ψ hψ continuous_muK muK_quarter muK_end
    (fun n x t => by
      change loopFun ψ muK n (0, (x, t)) = milnorInv hA hAc ψ hψ (ψ (stripMap A n (x, t)))
      have ht0 := t.2.1
      have ht1 := t.2.2
      simp only [loopFun, Set.Icc.coe_zero]
      split_ifs with h
      · rw [hψ.low n x t (by linarith), milnorInv_low hA hAc ψ hψ n x _
          (by rw [clampI_two_mul (t := t) (by linarith)]; linarith)]
        exact stripMap_congr rfl (by
          rw [clampI_two_mul (t := t) (by linarith), show (2 : ℝ) * (2 * t) = 4 * t by ring])
      · rcases le_or_gt (t : ℝ) (1 / 2) with h' | h'
        · rw [hψ.low n x t h', milnorInv_high hA hAc ψ hψ n x _
            (by rw [clampI_two_mul h']; linarith), muK_zero_low h', clampI_two_mul h',
            show (1 : ℝ) / 2 + (2 - 4 * t) / 2 = 3 / 2 - 2 * t by ring]
        · have hl := hψ.high n x t h'.le
          rw [(milnorInv_isMilnorMap hA hAc ψ hψ).fix hA (m := n + 1)
            (by rw [hl]; push_cast; ring), muK_zero_high h'.le,
            show (1 : ℝ) / 2 + (2 * t - 1) / 2 = t by ring, clampI_coe])
    (fun n x t => loopFun_one hA hAc ψ hψ (fun _ h₁ h₂ => Or.inr (muK_one h₁.le h₂)) n x t)

/-- **Milnor's maps `h_1` are homotopy equivalences** (pp. 151–152): a map of the
telescope with `h_1(x, n + t) = (x, n + 2t)` for `t ≤ 1/2` and `h_1(x, n + t) ∈ X_{n+1} × [n+1]`
for `t ≥ 1/2` is a homotopy equivalence, with homotopy inverse Milnor's `g`. -/
theorem isHomotopyEquiv_of_milnorMap (hA : Monotone A) (hAc : ∀ n, IsClosed (A n))
    (ψ : C(telescope A, telescope A)) (hψ : IsMilnorMap ψ) :
    IsHomotopyEquiv ψ := by
  have hR := scaleMap_homotopic hA hAc 4 (by norm_num)
  exact ⟨milnorInv hA hAc ψ hψ, ContinuousMap.Homotopic.trans ⟨milnorK hA hAc ψ hψ⟩ hR,
    ContinuousMap.Homotopic.trans ⟨milnorH hA hAc ψ hψ⟩ hR⟩

end MilnorMap

/-! ### Case 1 -/

section Case1

variable {φ : C(X, X)} {hφ : ∀ n, MapsTo φ (A n) (A n)}

/-- **Milnor's `h_u`** (p. 151), on the strip `n`, with the misprint corrected:
`h_u(x, n + t) = (h^n_u(x), n + 2t)` for `0 ≤ t ≤ 1/2`, `(h^n_{(3-4t)u}(x), n + 1)` for
`1/2 ≤ t ≤ 3/4`, and `(h^{n+1}_{(4t-3)u}(x), n + 1)` for `3/4 ≤ t ≤ 1`; here
`h^n : (restriction of φ to X_n) ≃ id`. -/
def case1Fun (hA : Monotone A)
    (H : ∀ n, (restrictTo φ (hφ n)).Homotopy (ContinuousMap.id (A n))) (n : ℕ)
    (q : I × (A n × I)) : telescope A :=
  if (q.2.2 : ℝ) ≤ 1 / 2 then stripMap A n (H n (q.1, q.2.1), clampI (2 * q.2.2))
  else if (q.2.2 : ℝ) ≤ 3 / 4 then
    stripMap A (n + 1) (up hA n (H n (clampI ((3 - 4 * q.2.2) * q.1), q.2.1)), 0)
  else stripMap A (n + 1) (H (n + 1) (clampI ((4 * q.2.2 - 3) * q.1), up hA n q.2.1), 0)

theorem continuous_case1Fun (hA : Monotone A)
    (H : ∀ n, (restrictTo φ (hφ n)).Homotopy (ContinuousMap.id (A n)))
    (n : ℕ) : Continuous (case1Fun hA H n) := by
  have hu : Continuous fun q : I × (A n × I) => ((q.1 : I) : ℝ) :=
    continuous_subtype_val.comp continuous_fst
  have hx : Continuous fun q : I × (A n × I) => q.2.1 := continuous_fst.comp continuous_snd
  refine Continuous.if_le ?_ (Continuous.if_le ?_ ?_ continuous_param continuous_const ?_)
    continuous_param continuous_const ?_
  · exact (stripMap A n).continuous.comp (((H n).continuous.comp (continuous_fst.prodMk hx)).prodMk
      (continuous_clampI.comp (continuous_const.mul continuous_param)))
  · exact (stripMap A (n + 1)).continuous.comp (((up hA n).continuous.comp ((H n).continuous.comp
      ((continuous_clampI.comp (((continuous_const.sub (continuous_const.mul continuous_param)).mul
        hu))).prodMk hx))).prodMk continuous_const)
  · exact (stripMap A (n + 1)).continuous.comp (((H (n + 1)).continuous.comp
      ((continuous_clampI.comp ((((continuous_const.mul continuous_param).sub
        continuous_const)).mul hu)).prodMk ((up hA n).continuous.comp hx))).prodMk
          continuous_const)
  · intro q hq
    rw [hq]
    congr 2
    apply Subtype.ext
    simp only [coe_up]
    rw [show (3 : ℝ) - 4 * (3 / 4) = 0 by norm_num, show (4 : ℝ) * (3 / 4) - 3 = 0 by norm_num,
      zero_mul, clampI_zero, (H n).apply_zero, (H (n + 1)).apply_zero]
    rfl
  · intro q hq
    rw [if_pos (by rw [hq]; norm_num), hq, show (2 : ℝ) * (1 / 2) = 1 by norm_num, clampI_one,
      stripMap_one hA]
    congr 3
    rw [show (3 : ℝ) - 4 * (1 / 2) = 1 by norm_num, one_mul, clampI_coe]

theorem case1Fun_compat (hA : Monotone A)
    (H : ∀ n, (restrictTo φ (hφ n)).Homotopy (ContinuousMap.id (A n))) (n : ℕ) (u : I) (x : A n) :
    case1Fun hA H (n + 1) (u, (up hA n x, 0)) = case1Fun hA H n (u, (x, 1)) := by
  unfold case1Fun
  rw [if_pos (by norm_num), if_neg (by norm_num), if_neg (by norm_num)]
  simp only [Set.Icc.coe_zero, Set.Icc.coe_one, mul_zero, clampI_zero]
  rw [show (4 : ℝ) * 1 - 3 = 1 by norm_num, one_mul, clampI_coe]

/-- Milnor's homotopy `u ↦ h_u` (p. 151), as a map `I × X_Σ → X_Σ`. -/
def case1Family (hA : Monotone A) (hAc : ∀ n, IsClosed (A n))
    (H : ∀ n, (restrictTo φ (hφ n)).Homotopy (ContinuousMap.id (A n))) :
    C(I × telescope A, telescope A) :=
  telescopeLift hA hAc (fun n => ⟨case1Fun hA H n, continuous_case1Fun hA H n⟩)
    (case1Fun_compat hA H)

/-- `h_u` at a fixed time `u`. -/
def case1Map (hA : Monotone A) (hAc : ∀ n, IsClosed (A n))
    (H : ∀ n, (restrictTo φ (hφ n)).Homotopy (ContinuousMap.id (A n))) (u : I) :
    C(telescope A, telescope A) :=
  (case1Family hA hAc H).comp ((ContinuousMap.const _ u).prodMk (ContinuousMap.id _))

theorem case1Map_stripMap (hA : Monotone A) (hAc : ∀ n, IsClosed (A n))
    (H : ∀ n, (restrictTo φ (hφ n)).Homotopy (ContinuousMap.id (A n)))
    (u : I) (n : ℕ) (x : A n) (t : I) :
    case1Map hA hAc H u (stripMap A n (x, t)) = case1Fun hA H n (u, (x, t)) :=
  telescopeLift_stripMap hA hAc (fun n => ⟨case1Fun hA H n, continuous_case1Fun hA H n⟩)
    (case1Fun_compat hA H) n u x t

/-- **`h_0` is homotopic to `f_Σ`** ("clearly", Milnor, p. 151): `h_0 = f_Σ ∘ R₂`. -/
theorem case1Map_zero (hA : Monotone A) (hAc : ∀ n, IsClosed (A n))
    (H : ∀ n, (restrictTo φ (hφ n)).Homotopy (ContinuousMap.id (A n))) :
    case1Map hA hAc H 0 = (telescopeMap φ hφ).comp (scaleMap hA hAc 2 (by norm_num)) := by
  refine telescope_ext' fun n x t => ?_
  rw [case1Map_stripMap, ContinuousMap.comp_apply, scaleMap_stripMap, telescopeMap_stripMap]
  unfold case1Fun
  split_ifs with h1 h2
  · rw [(H n).apply_zero]
  · rw [Set.Icc.coe_zero, mul_zero, clampI_zero, (H n).apply_zero, ← stripMap_one hA,
      clampI_of_one_le (by linarith)]
  · rw [Set.Icc.coe_zero, mul_zero, clampI_zero, (H (n + 1)).apply_zero,
      clampI_of_one_le (by linarith), stripMap_one hA]
    rfl

/-- **`h_1` is one of Milnor's maps**: `h_1(x, n + t) = (x, n + 2t)` for `t ≤ 1/2`, and it lands
at level `n + 1` for `t ≥ 1/2` (p. 151). -/
theorem case1Map_one (hA : Monotone A) (hAc : ∀ n, IsClosed (A n))
    (H : ∀ n, (restrictTo φ (hφ n)).Homotopy (ContinuousMap.id (A n))) :
    IsMilnorMap (case1Map hA hAc H 1) where
  low n x t ht := by
    rw [case1Map_stripMap]
    unfold case1Fun
    rw [if_pos ht, (H n).apply_one]
    rfl
  high n x t ht := by
    rw [case1Map_stripMap]
    unfold case1Fun
    split_ifs with h1 h2
    · rw [stripMap_apply_snd, show (t : ℝ) = 1 / 2 by linarith,
        show (2 : ℝ) * (1 / 2) = 1 by norm_num, clampI_one]
      simp
    · simp
    · simp

/-- **Case 1 of Theorem A** (Milnor, pp. 150–152). Let the `X_n` be closed, and let `φ : X → X`
carry each `X_n` into itself by a map homotopic (in `X_n`) to the identity of `X_n`. Then
`φ_Σ : X_Σ → X_Σ` is a homotopy equivalence: `φ_Σ ≃ h_0 ≃ h_1`, and `h_1` is a homotopy
equivalence. -/
theorem theoremA_case1 (hA : Monotone A) (hAc : ∀ n, IsClosed (A n))
    (hφe : ∀ n, (restrictTo φ (hφ n)).Homotopic (ContinuousMap.id (A n))) :
    IsHomotopyEquiv (telescopeMap φ hφ) := by
  let H : ∀ n, (restrictTo φ (hφ n)).Homotopy (ContinuousMap.id (A n)) := fun n => (hφe n).some
  have h01 : (case1Map hA hAc H 0).Homotopic (case1Map hA hAc H 1) :=
    ⟨⟨case1Family hA hAc H, fun _ => rfl, fun _ => rfl⟩⟩
  have hS0 : (telescopeMap φ hφ).Homotopic (case1Map hA hAc H 0) := by
    rw [case1Map_zero hA hAc H]
    have := (ContinuousMap.Homotopic.refl (telescopeMap φ hφ)).comp
      (scaleMap_homotopic hA hAc 2 (by norm_num)).symm
    rwa [ContinuousMap.comp_id] at this
  exact (isHomotopyEquiv_of_milnorMap hA hAc _ (case1Map_one hA hAc H)).of_homotopic
    (hS0.trans h01).symm

end Case1

/-! ### Case 2 and Theorem A -/

section Case2

/-- **A self-map of a telescope which preserves the truncations and is homotopic to the identity
on the integer levels is a homotopy equivalence** (Milnor, pp. 152–153, for `G f_Σ` and `f_Σ G`).
Its restriction to `X^m_Σ` is homotopic to the identity, by `F ≃ F ι r = ι e_m r ≃ ι r ≃ id`
((T2)), so Case 1 applies to the space `X_Σ` and its closed subsets `X^m_Σ`; and `X_Σ` is the
homotopy direct limit of `{X^m_Σ}` (`Morse.isHomotopyDirectLimit_truncation`). -/
theorem isHomotopyEquiv_of_truncation (hA : Monotone A) (F : C(telescope A, telescope A))
    (hF : ∀ m, MapsTo F (truncation A m) (truncation A m)) (e : ∀ m, C(A m, A m))
    (he : ∀ m, (e m).Homotopic (ContinuousMap.id _))
    (hFe : ∀ m (x : A m), F (stripMap A m (x, 0)) = stripMap A m (e m x, 0)) :
    IsHomotopyEquiv F := by
  refine IsHomotopyEquiv.of_telescopeMap (hf := hF) isHomotopyDirectLimit_truncation
    isHomotopyDirectLimit_truncation
      (theoremA_case1 (hφ := hF) monotone_truncation isClosed_truncation ?_)
  intro m
  set ι := truncIncl A m
  set r := truncProj hA m
  set Fm := restrictTo F (hF m)
  have hT2 := truncIncl_comp_truncProj hA m
  have hcomm : Fm.comp ι = ι.comp (e m) :=
    ContinuousMap.ext fun x => Subtype.ext (hFe m x)
  have h1 : Fm.Homotopic ((Fm.comp ι).comp r) := by
    have := (ContinuousMap.Homotopic.refl Fm).comp hT2.symm
    rwa [ContinuousMap.comp_id] at this
  have h2 : ((ι.comp (e m)).comp r).Homotopic (ι.comp r) := by
    have := ((ContinuousMap.Homotopic.refl ι).comp (he m)).comp (ContinuousMap.Homotopic.refl r)
    rwa [ContinuousMap.comp_id] at this
  rw [hcomm] at h1
  exact (h1.trans h2).trans hT2

variable {Y : Type*} [TopologicalSpace Y] {B : ℕ → Set Y}

/-- The strip formula of Milnor's `G : Y_Σ → X_Σ` (p. 152): `G(y, n + t) = (g_n(y), n + 2t)` for
`t ≤ 1/2` and `(h^n_{2t-1}(y), n + 1)` for `t ≥ 1/2`, where `h^n : i_n g_n ≃ g_{n+1} j_n`. -/
def case2InvStrip (hA : Monotone A) (hB : Monotone B) (g : ∀ n, C(B n, A n))
    (k : ∀ n, ((up hA n).comp (g n)).Homotopy ((g (n + 1)).comp (up hB n))) (n : ℕ) :
    C(B n × I, telescope A) where
  toFun q := if (q.2 : ℝ) ≤ 1 / 2 then stripMap A n (g n q.1, clampI (2 * q.2))
    else stripMap A (n + 1) (k n (clampI (2 * q.2 - 1), q.1), 0)
  continuous_toFun := by
    have ht : Continuous fun q : B n × I => ((q.2 : I) : ℝ) :=
      continuous_subtype_val.comp continuous_snd
    refine Continuous.if_le ?_ ?_ ht continuous_const ?_
    · exact (stripMap A n).continuous.comp (((g n).continuous.comp continuous_fst).prodMk
        (continuous_clampI.comp (continuous_const.mul ht)))
    · exact (stripMap A (n + 1)).continuous.comp (((k n).continuous.comp
        ((continuous_clampI.comp ((continuous_const.mul ht).sub continuous_const)).prodMk
          continuous_fst)).prodMk continuous_const)
    · intro q hq
      rw [hq, show (2 : ℝ) * (1 / 2) = 1 by norm_num, show (1 : ℝ) - 1 = 0 by norm_num,
        clampI_one, clampI_zero, (k n).apply_zero, stripMap_one hA]
      rfl

/-- **Milnor's map `G : Y_Σ → X_Σ`** (Case 2, p. 152). It is well defined since
`h^n_0 = i_n g_n` and `h^n_1 = g_{n+1} j_n`. -/
def case2Inv (hA : Monotone A) (hB : Monotone B) (hBc : ∀ n, IsClosed (B n)) (g : ∀ n, C(B n, A n))
    (k : ∀ n, ((up hA n).comp (g n)).Homotopy ((g (n + 1)).comp (up hB n))) :
    C(telescope B, telescope A) :=
  telescopeDesc hB hBc (case2InvStrip hA hB g k) fun n y => by
    change (if ((0 : I) : ℝ) ≤ 1 / 2 then stripMap A (n + 1) (g (n + 1) (up hB n y),
        clampI (2 * (0 : I))) else stripMap A (n + 1 + 1) (k (n + 1) (clampI (2 * (0 : I) - 1),
          up hB n y), 0)) =
      (if ((1 : I) : ℝ) ≤ 1 / 2 then stripMap A n (g n y, clampI (2 * (1 : I)))
      else stripMap A (n + 1) (k n (clampI (2 * (1 : I) - 1), y), 0))
    rw [if_pos (by norm_num), if_neg (by norm_num)]
    simp only [Set.Icc.coe_zero, Set.Icc.coe_one, mul_zero, clampI_zero]
    rw [show (2 : ℝ) * 1 - 1 = 1 by norm_num, clampI_one, (k n).apply_one]
    rfl

theorem case2Inv_stripMap (hA : Monotone A) (hB : Monotone B) (hBc : ∀ n, IsClosed (B n))
    (g : ∀ n, C(B n, A n))
    (k : ∀ n, ((up hA n).comp (g n)).Homotopy ((g (n + 1)).comp (up hB n))) (n : ℕ) (y : B n)
    (t : I) : case2Inv hA hB hBc g k (stripMap B n (y, t)) =
      if (t : ℝ) ≤ 1 / 2 then stripMap A n (g n y, clampI (2 * t))
      else stripMap A (n + 1) (k n (clampI (2 * t - 1), y), 0) :=
  telescopeDesc_stripMap hB hBc _ _ n y t

theorem case2Inv_zero (hA : Monotone A) (hB : Monotone B) (hBc : ∀ n, IsClosed (B n))
    (g : ∀ n, C(B n, A n))
    (k : ∀ n, ((up hA n).comp (g n)).Homotopy ((g (n + 1)).comp (up hB n))) (n : ℕ) (y : B n) :
    case2Inv hA hB hBc g k (stripMap B n (y, 0)) = stripMap A n (g n y, 0) := by
  rw [case2Inv_stripMap, if_pos (by norm_num)]
  exact stripMap_congr rfl (by simp)

theorem case2Inv_level (hA : Monotone A) (hB : Monotone B) (hBc : ∀ n, IsClosed (B n))
    (g : ∀ n, C(B n, A n))
    (k : ∀ n, ((up hA n).comp (g n)).Homotopy ((g (n + 1)).comp (up hB n))) (n : ℕ) (y : B n)
    (t : I) : (case2Inv hA hB hBc g k (stripMap B n (y, t)) : X × ℝ).2 ≤ n + 1 := by
  rw [case2Inv_stripMap]
  split_ifs
  · simp only [stripMap_apply_snd]
    linarith [(clampI (2 * t)).2.2]
  · simp

/-- **The squares commute up to homotopy** (Milnor, p. 152):
`i_n g_n ≃ g_{n+1} f_{n+1} i_n g_n = g_{n+1} j_n f_n g_n ≃ g_{n+1} j_n`. -/
theorem homotopic_square (hA : Monotone A) (hB : Monotone B) {f : C(X, Y)}
    {hf : ∀ n, MapsTo f (A n) (B n)} (g : ∀ n, C(B n, A n))
    (hgf : ∀ n, ((g n).comp (restrictTo f (hf n))).Homotopic (ContinuousMap.id _))
    (hfg : ∀ n, ((restrictTo f (hf n)).comp (g n)).Homotopic (ContinuousMap.id _)) (n : ℕ) :
    ((up hA n).comp (g n)).Homotopic ((g (n + 1)).comp (up hB n)) := by
  have hc : (restrictTo f (hf (n + 1))).comp (up hA n) = (up hB n).comp (restrictTo f (hf n)) :=
    rfl
  have h1 : ((up hA n).comp (g n)).Homotopic
      (((g (n + 1)).comp (restrictTo f (hf (n + 1)))).comp ((up hA n).comp (g n))) := by
    have := (hgf (n + 1)).symm.comp (ContinuousMap.Homotopic.refl ((up hA n).comp (g n)))
    rwa [ContinuousMap.id_comp] at this
  have h2 : (((g (n + 1)).comp (restrictTo f (hf (n + 1)))).comp ((up hA n).comp (g n))) =
      ((g (n + 1)).comp (up hB n)).comp ((restrictTo f (hf n)).comp (g n)) := by
    simp only [ContinuousMap.comp_assoc]
    rw [← ContinuousMap.comp_assoc (restrictTo f (hf (n + 1))), hc, ContinuousMap.comp_assoc]
  have h3 : (((g (n + 1)).comp (up hB n)).comp ((restrictTo f (hf n)).comp (g n))).Homotopic
      ((g (n + 1)).comp (up hB n)) := by
    have := (ContinuousMap.Homotopic.refl ((g (n + 1)).comp (up hB n))).comp (hfg n)
    rwa [ContinuousMap.comp_id] at this
  rw [h2] at h1
  exact h1.trans h3

/-- **`f_Σ` is a homotopy equivalence** (Case 2 of Theorem A, Milnor, pp. 152–153), when the `Y_n`
are closed and `f` carries each `X_n` into `Y_n` by a homotopy equivalence. No homotopy direct
limit hypothesis, and no closedness of the `X_n`, is needed for this part. -/
theorem theoremA_telescope (hA : Monotone A) (hB : Monotone B) (hBc : ∀ n, IsClosed (B n))
    (f : C(X, Y)) (hf : ∀ n, MapsTo f (A n) (B n))
    (hfe : ∀ n, IsHomotopyEquiv (restrictTo f (hf n))) : IsHomotopyEquiv (telescopeMap f hf) := by
  choose g hgf hfg using hfe
  let k : ∀ n, ((up hA n).comp (g n)).Homotopy ((g (n + 1)).comp (up hB n)) := fun n =>
    (homotopic_square hA hB g hgf hfg n).some
  -- Milnor's `G`, with the two properties used below
  obtain ⟨G, hGl, hG0⟩ : ∃ G : C(telescope B, telescope A),
      (∀ n y t, (G (stripMap B n (y, t)) : X × ℝ).2 ≤ n + 1) ∧
        ∀ n y, G (stripMap B n (y, 0)) = stripMap A n (g n y, 0) :=
    ⟨case2Inv hA hB hBc g k, case2Inv_level hA hB hBc g k, case2Inv_zero hA hB hBc g k⟩
  -- `G f_Σ` is a homotopy equivalence
  have hGf : IsHomotopyEquiv (G.comp (telescopeMap f hf)) := by
    refine isHomotopyEquiv_of_truncation hA _ (fun m z hz => ?_)
      (fun m => (g m).comp (restrictTo f (hf m))) hgf (fun m x => ?_)
    · change ((G.comp (telescopeMap f hf)) z : X × ℝ).2 ≤ m
      refine level_le_of_stripMap hA (fun w : telescope A => (w : X × ℝ).2)
        (G.comp (telescopeMap f hf)) (fun n x t => ?_) (fun n x => ?_) hz
      · rw [ContinuousMap.comp_apply, telescopeMap_stripMap]
        exact hGl n _ t
      · rw [ContinuousMap.comp_apply, telescopeMap_stripMap, hG0]
        simp
    · rw [ContinuousMap.comp_apply, telescopeMap_stripMap, hG0]
      rfl
  -- `f_Σ G` is a homotopy equivalence
  have hfG : IsHomotopyEquiv ((telescopeMap f hf).comp G) := by
    refine isHomotopyEquiv_of_truncation hB _ (fun m z hz => ?_)
      (fun m => (restrictTo f (hf m)).comp (g m)) hfg (fun m y => ?_)
    · change (((telescopeMap f hf).comp G) z : Y × ℝ).2 ≤ m
      refine level_le_of_stripMap hB (fun w : telescope B => (w : Y × ℝ).2)
        ((telescopeMap f hf).comp G) (fun n y t => ?_) (fun n y => ?_) hz
      · exact hGl n y t
      · change (G (stripMap B n (y, 0)) : X × ℝ).2 ≤ n
        rw [hG0]
        simp
    · rw [ContinuousMap.comp_apply, hG0, telescopeMap_stripMap]
      rfl
  obtain ⟨k₁, hk₁, -⟩ := hGf
  obtain ⟨k₂, -, hk₂⟩ := hfG
  exact IsHomotopyEquiv.of_leftInv_rightInv (L := k₁.comp G) (R := G.comp k₂) hk₁ hk₂

/-- **Theorem A** (Milnor, p. 150). Let `X` be the homotopy direct limit of `{X_i}` and `Y` that of
`{Y_i}`, and let `f : X → Y` carry each `X_i` into `Y_i` by a homotopy equivalence `f_i = f|X_i`.
Then `f` is a homotopy equivalence. Milnor's proof, formalized here, needs the `Y_i` closed (for
his map `G`); for the statement without any closedness hypothesis see `Morse.theoremA_general`. -/
theorem theoremA (hA : Monotone A) (hB : Monotone B) (hBc : ∀ n, IsClosed (B n))
    (hX : IsHomotopyDirectLimit A) (hY : IsHomotopyDirectLimit B) (f : C(X, Y))
    (hf : ∀ n, MapsTo f (A n) (B n)) (hfe : ∀ n, IsHomotopyEquiv (restrictTo f (hf n))) :
    IsHomotopyEquiv f :=
  IsHomotopyEquiv.of_telescopeMap hX hY (theoremA_telescope hA hB hBc f hf hfe)

end Case2

end Morse
