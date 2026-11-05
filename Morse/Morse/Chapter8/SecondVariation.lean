import Morse.Chapter8.Critical
import Morse.Chapter6.Surface

/-!
Milnor, *Morse Theory*, §13, pp. 74–76 (Theorem 13.1 and Remark 13.5), for a submanifold
`N ⊆ ℝᴷ` with the induced metric.

# The second variation formula

## Milnor's text, paraphrased

* (p. 74) For a critical point `p` of `f` on a manifold, `f_**(X₁, X₂) = ∂²f(α(u₁, u₂))/∂u₁∂u₂`
  at `(0, 0)` for any `α` with `∂α/∂uᵢ (0, 0) = Xᵢ`.  By analogy, for a geodesic `γ` and
  `W₁, W₂ ∈ TΩ_γ`, choose a 2-parameter variation `α(u₁, u₂, t)` of `γ` with
  `∂α/∂uᵢ (0, 0, t) = Wᵢ(t)` and set `E_**(W₁, W₂) = ∂²E(ᾱ(u₁, u₂))/∂u₁∂u₂ (0, 0)`; Theorem 13.1 is
  what shows that this is well defined.
* **Theorem 13.1** (pp. 74–76, second variation formula):
  `½ ∂²E/∂u₁∂u₂ (0, 0) = -Σ_t ⟨W₂(t), Δ_t DW₁/dt⟩ - ∫₀¹ ⟨W₂, D²W₁/dt² + R(V, W₁)V⟩ dt`, with
  `V = dγ/dt` and `Δ_t DW₁/dt = DW₁/dt(t⁺) - DW₁/dt(t⁻)`.  Proof: by 12.2,
  `½ ∂E/∂u₂ = -Σ ⟨∂α/∂u₂, Δ_t ∂α/∂t⟩ - ∫ ⟨∂α/∂u₂, D/∂t ∂α/∂t⟩`; differentiate with respect to
  `u₁`; at `(0, 0)` the terms containing `Δ_t V = 0` and `D/dt V = 0` vanish; rearranging the
  jump term gives (13.2); the curvature formula (Lemma 9.2) and Lemma 8.7 give (13.3)
  `D/∂u₁ D/∂t V = D²W₁/dt² + R(V, W₁)V`.
* **Remark 13.5** (p. 76): `E_**(W, W) = d²E(ᾱ(u))/du² (0)` for any 1-parameter variation with
  field `W`, using `β(u₁, u₂) = ᾱ(u₁ + u₂)`.

## In the embedded setting

* `Morse.curvR hN x a b c` is Milnor's `R(a, b)c` at `x ∈ N`, with Milnor's sign (Chapter 6's
  `Morse.curvOp`, for which Lemma 9.2 holds as stated and the unit sphere has curvature `+1`).
* `Morse.secondVariation hN γ W₁ W₂` is the right side of Theorem 13.1 (half of `E_**`), with
  `Δ_t DW₁/dt = P(Δ_t W₁')` (`DW₁/dt(t^±) = P W₁'(t^±)`).
* **Theorem 13.1**: `Morse.second_variation`.  The second derivative `∂²E/∂u₁∂u₂ (0, 0)` is
  formalized as the iterated partial derivative `∂/∂u₁ (∂E/∂u₂ (u₁, 0))` at `u₁ = 0`, which is
  exactly what Milnor's proof computes; its existence is part of the theorem.
  `Morse.second_variation_eq`: it depends only on `W₁, W₂` (Milnor's "well defined").
* **Remark 13.5**: `Morse.remark_13_5`.
* `Morse.curvature_identity` is (13.3) at an interior point of a strip (Lemmas 8.7 and 9.2 for a
  surface defined only near the point; Chapter 6 states them for surfaces defined on all of
  `ℝ²`); `Morse.IsVariation.hasDerivAt_jump` is the "rearranging of the second term".
  The bilinear form `E_**` on `TΩ_γ` and Corollary 13.4 are in `Morse/Chapter8/Hessian.lean`.

## What Milnor leaves implicit

* **(12.2′) at every `u`**: the proof differentiates the first variation formula, so it is
  needed at every `(u₁, 0)`, not only at `(0, 0)` (`Morse.IsVariation.hasDerivAt_energy` applied
  to the slices `u₂ ↦ α(u₁, u₂)`).
* **Differentiating the jump terms** ("rearranging the second term", p. 75): `Δ_t ∂α/∂t` is the
  difference of the one-sided velocities computed on the two adjacent closed strips; each is
  smooth in `u₁`, and `∂/∂u₁` of a one-sided `t`-derivative is the one-sided `t`-derivative of
  `∂α/∂u₁`, by the symmetry of second derivatives *on the edge of a closed strip*
  (`Morse.pdU_pdT`).
* **Differentiating the integral term** needs differentiation under the integral sign on each
  closed strip (`Morse.hasDerivAt_integral_of_piecewise`), with the integrand
  `⟨∂α/∂u₂, P(∂²α/∂t²)⟩` smooth on the closed strips.
* **The curvature formula** is applied to the surface `(u₁, t) ↦ α(u₁, 0, t)`, which is only
  defined on the strips, with `x = t`, `y = u₁`; and `D/∂t D/∂u₁ V` at `u₁ = 0` is `D²W₁/dt²`
  because `D/∂t` along `u₁ = 0` only involves values on that curve.
* Milnor's notation `∂²E/∂u₁∂u₂` suggests that `E ∘ ᾱ` is `C²`; this is neither proved in the book
  nor needed here.
-/

open Set Filter Topology Function MeasureTheory Metric
open scoped ContDiff Manifold RealInnerProductSpace Interval

noncomputable section

namespace Morse

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {N : Set V} (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N)

open Classical in
/-- **Milnor's curvature tensor at a point `x` of `V`** (`0` off `N`): `R(a, b)c` is
`Morse.curvOp hN x a b c = II(b, II(a, c)) − II(a, II(b, c))` of Chapter 6, i.e. Milnor's
`R(X, Y)Z = −∇_X∇_Y Z + ∇_Y∇_X Z + ∇_{[X,Y]} Z` (p. 51), the sign for which Lemma 9.2 reads
`D/∂y D/∂x V − D/∂x D/∂y V = R(∂s/∂x, ∂s/∂y)V` and the unit sphere has curvature `+1`. -/
def curvR (x a b c : V) : V := if h : x ∈ N then curvOp hN ⟨x, h⟩ a b c else 0

omit [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
theorem curvR_of_mem {x : V} (hx : x ∈ N) (a b c : V) :
    curvR hN x a b c = curvOp hN ⟨x, hx⟩ a b c := by
  rw [curvR, dif_pos hx]

/-! ### Partial derivatives near a point -/

section Partial

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem partialX_congr {F G : ℝ × ℝ → E} {p : ℝ × ℝ} (h : F =ᶠ[𝓝 p] G) :
    partialX F p = partialX G p := by
  rw [partialX, partialX, h.fderiv_eq]

theorem partialY_congr {F G : ℝ × ℝ → E} {p : ℝ × ℝ} (h : F =ᶠ[𝓝 p] G) :
    partialY F p = partialY G p := by
  rw [partialY, partialY, h.fderiv_eq]

/-- **Symmetry of the mixed partial derivatives** at a point near which `F` is smooth. -/
theorem partialX_partialY_of_contDiffOn {F : ℝ × ℝ → E} {O : Set (ℝ × ℝ)} (hO : IsOpen O)
    (hF : ContDiffOn ℝ ∞ F O) {p : ℝ × ℝ} (hp : p ∈ O) :
    partialX (partialY F) p = partialY (partialX F) p := by
  have hFp : ContDiffAt ℝ ∞ F p := hF.contDiffAt (hO.mem_nhds hp)
  have hd : DifferentiableAt ℝ (fderiv ℝ F) p :=
    ((hF.fderiv_of_isOpen hO (m := ∞) (by simp)).contDiffAt (hO.mem_nhds hp)).differentiableAt
      (by simp)
  have e1 : partialX (partialY F) p = fderiv ℝ (fderiv ℝ F) p (1, 0) (0, 1) := by
    change fderiv ℝ (fun q => fderiv ℝ F q ((fun _ => ((0 : ℝ), (1 : ℝ))) q)) p (1, 0) = _
    rw [fderiv_clm_apply hd (differentiableAt_const _)]
    simp
  have e2 : partialY (partialX F) p = fderiv ℝ (fderiv ℝ F) p (0, 1) (1, 0) := by
    change fderiv ℝ (fun q => fderiv ℝ F q ((fun _ => ((1 : ℝ), (0 : ℝ))) q)) p (0, 1) = _
    rw [fderiv_clm_apply hd (differentiableAt_const _)]
    simp
  rw [e1, e2]
  exact (hFp.isSymmSndFDerivAt (by
    simp only [minSmoothness_of_isRCLikeNormedField]; exact WithTop.coe_le_coe.2 le_top)) _ _

theorem contDiffOn_partialX {F : ℝ × ℝ → E} {O : Set (ℝ × ℝ)} (hO : IsOpen O)
    (hF : ContDiffOn ℝ ∞ F O) : ContDiffOn ℝ ∞ (partialX F) O :=
  (hF.fderiv_of_isOpen hO (m := ∞) (by simp)).clm_apply contDiffOn_const

theorem contDiffOn_partialY {F : ℝ × ℝ → E} {O : Set (ℝ × ℝ)} (hO : IsOpen O)
    (hF : ContDiffOn ℝ ∞ F O) : ContDiffOn ℝ ∞ (partialY F) O :=
  (hF.fderiv_of_isOpen hO (m := ∞) (by simp)).clm_apply contDiffOn_const

end Partial

/-! ### Lemmas 8.7 and 9.2 at an interior point: the curvature term -/

/-- **The curvature identity behind the second variation formula** (Milnor's (13.3), from
Lemmas 8.7 and 9.2): for a smooth parametrized surface `F(u, t)` in `N` near `p₀`,
`D/∂u D/∂t ∂F/∂t = D/∂t D/∂t ∂F/∂u + R(∂F/∂t, ∂F/∂u) ∂F/∂t` at `p₀`, with
`D/∂u X = P(∂X/∂u)`, `D/∂t X = P(∂X/∂t)` and `D/∂u ∂F/∂t = D/∂t ∂F/∂u` (Lemma 8.7) used on the
right.

Proof, in `V`: with `Q = P ∘ F`, `a = ∂F/∂t`, `b = ∂F/∂u`, `∂_u Q = D_b`, `∂_t Q = D_a` (`D_v` the
derivative of the projection, `D_v w = II(v, w)`): the difference of the two sides is
`P D_b ∂_t a - P D_a ∂_t b`; since `a = Qa` and `b = Qb`, the normal parts of `∂_t a`, `∂_t b` are
`D_a a` and `D_a b`, so it is `D_b D_a a - D_a D_a b = R(a, b)a`, using `II(a, b) = II(b, a)`. -/
theorem curvature_identity {F : ℝ × ℝ → V} {O : Set (ℝ × ℝ)} (hO : IsOpen O)
    (hF : ContDiffOn ℝ ∞ F O) (hFN : ∀ p ∈ O, F p ∈ N) {p₀ : ℝ × ℝ} (hp₀ : p₀ ∈ O) :
    prj hN (F p₀) (partialX (fun p => prj hN (F p) (partialY (partialY F) p)) p₀) =
      prj hN (F p₀) (partialY (fun p => prj hN (F p) (partialY (partialX F) p)) p₀) +
        curvR hN (F p₀) (partialY F p₀) (partialX F p₀) (partialY F p₀) := by
  set q : N := ⟨F p₀, hFN p₀ hp₀⟩
  set σ := sliceAt hN q
  have hq : F p₀ ∈ σ.φ.source := mem_sliceAt_source hN q
  set O' := O ∩ F ⁻¹' σ.φ.source
  have hO' : IsOpen O' := hF.continuousOn.isOpen_inter_preimage hO σ.φ.open_source
  have hp₀' : p₀ ∈ O' := ⟨hp₀, hq⟩
  have hO'n : O' ∈ 𝓝 p₀ := hO'.mem_nhds hp₀'
  have hF' : ContDiffOn ℝ ∞ F O' := hF.mono inter_subset_left
  set a := partialY F
  set b := partialX F
  have ha : ContDiffOn ℝ ∞ a O' := contDiffOn_partialY hO' hF'
  have hb : ContDiffOn ℝ ∞ b O' := contDiffOn_partialX hO' hF'
  have hA : ContDiffOn ℝ ∞ (partialY a) O' := contDiffOn_partialY hO' ha
  have hM : ContDiffOn ℝ ∞ (partialY b) O' := contDiffOn_partialY hO' hb
  have hFd : ∀ p ∈ O', DifferentiableAt ℝ F p := fun p hp =>
    (hF'.contDiffAt (hO'.mem_nhds hp)).differentiableAt (by simp)
  have had : DifferentiableAt ℝ a p₀ := (ha.contDiffAt hO'n).differentiableAt (by simp)
  have hAd : DifferentiableAt ℝ (partialY a) p₀ := (hA.contDiffAt hO'n).differentiableAt (by simp)
  have hbd : DifferentiableAt ℝ b p₀ := (hb.contDiffAt hO'n).differentiableAt (by simp)
  have hMd : DifferentiableAt ℝ (partialY b) p₀ := (hM.contDiffAt hO'n).differentiableAt (by simp)
  -- the projection along `F` is `Q = projRep σ ∘ F` near `p₀`
  set Q : ℝ × ℝ → V →L[ℝ] V := fun p => projRep σ (F p)
  have hQd : DifferentiableAt ℝ Q p₀ :=
    ((contDiffAt_projRep σ (q := q) hq).differentiableAt (by simp)).comp p₀ (hFd p₀ hp₀')
  have hQeq : ∀ p ∈ O', prj hN (F p) = Q p := fun p hp => by
    rw [prj_of_mem hN (hFN p hp.1)]
    exact (projRep_eq hN σ (x := ⟨F p, hFN p hp.1⟩) hp.2).symm
  have hPQ : prj hN (F p₀) = tanProj hN q := prj_of_mem hN _
  have hQ0 : Q p₀ = tanProj hN q := by rw [← hQeq p₀ hp₀', hPQ]
  -- tangency of the partial derivatives
  have htan : ∀ p (hp : p ∈ O'), ∀ w, fderiv ℝ F p w ∈ tangentSubspace hN ⟨F p, hFN p hp.1⟩ :=
    fun p hp w => hasFDerivWithinAt_mem_tangentSubspace hN
      ((hFd p hp).hasFDerivAt.hasFDerivWithinAt) (hO'.uniqueDiffWithinAt hp)
      (fun x hx => hFN x hx.1) hp w
  have hap : ∀ p ∈ O', Q p (a p) = a p := fun p hp => by
    rw [← hQeq p hp, prj_eq_self_iff hN (hFN p hp.1)]; exact htan p hp (0, 1)
  have hbp : ∀ p ∈ O', Q p (b p) = b p := fun p hp => by
    rw [← hQeq p hp, prj_eq_self_iff hN (hFN p hp.1)]; exact htan p hp (1, 0)
  have ha0 : a p₀ ∈ tangentSubspace hN q := htan p₀ hp₀' (0, 1)
  have hb0 : b p₀ ∈ tangentSubspace hN q := htan p₀ hp₀' (1, 0)
  -- the derivatives of `Q` are `D_v = II(v, ·)`
  set D := dN hN (tanProj hN) q
  have hQfd : ∀ w, fderiv ℝ Q p₀ w = D (fderiv ℝ F p₀ w) := fun w => by
    have h1 : fderiv ℝ Q p₀ = (fderiv ℝ (projRep σ) (F p₀)).comp (fderiv ℝ F p₀) :=
      fderiv_comp p₀ ((contDiffAt_projRep σ (q := q) hq).differentiableAt (by simp))
        (hFd p₀ hp₀')
    rw [h1, ContinuousLinearMap.comp_apply]
    exact (dN_tanProj_eq_fderiv hN σ hq (htan p₀ hp₀' w)).symm
  have hQx : partialX Q p₀ = D (b p₀) := hQfd (1, 0)
  have hQy : partialY Q p₀ = D (a p₀) := hQfd (0, 1)
  -- normal parts: `∂a/∂t = P ∂a/∂t + D_a a` and `∂b/∂t = P ∂b/∂t + D_a b`
  have hAdec : partialY a p₀ = tanProj hN q (partialY a p₀) + D (a p₀) (a p₀) := by
    have h1 : partialY a p₀ = partialY (fun p => Q p (a p)) p₀ :=
      partialY_congr (eventually_of_mem hO'n fun p hp => (hap p hp).symm)
    conv_lhs => rw [h1, partialY_clm_apply hQd had, hQy, hQ0]
    abel
  have hMdec : partialY b p₀ = tanProj hN q (partialY b p₀) + D (a p₀) (b p₀) := by
    have h1 : partialY b p₀ = partialY (fun p => Q p (b p)) p₀ :=
      partialY_congr (eventually_of_mem hO'n fun p hp => (hbp p hp).symm)
    conv_lhs => rw [h1, partialY_clm_apply hQd hbd, hQy, hQ0]
    abel
  -- `∂/∂u ∂a/∂t = ∂/∂t ∂b/∂t` (Lemma 8.7 and symmetry of second derivatives)
  have hsym : partialX (partialY a) p₀ = partialY (partialY b) p₀ := by
    rw [partialX_partialY_of_contDiffOn hO' ha hp₀']
    exact partialY_congr (eventually_of_mem hO'n fun p hp =>
      partialX_partialY_of_contDiffOn hO' hF' hp)
  -- the two sides
  have hL : partialX (fun p => prj hN (F p) (partialY a p)) p₀ =
      D (b p₀) (partialY a p₀) + tanProj hN q (partialX (partialY a) p₀) := by
    rw [partialX_congr (eventually_of_mem hO'n fun p hp => by rw [hQeq p hp]),
      partialX_clm_apply hQd hAd, hQx, hQ0]
  have hR : partialY (fun p => prj hN (F p) (partialY b p)) p₀ =
      D (a p₀) (partialY b p₀) + tanProj hN q (partialY (partialY b) p₀) := by
    rw [partialY_congr (eventually_of_mem hO'n fun p hp => by rw [hQeq p hp]),
      partialY_clm_apply hQd hMd, hQy, hQ0]
  have e1 : tanProj hN q (D (b p₀) (partialY a p₀)) = D (b p₀) (D (a p₀) (a p₀)) := by
    conv_lhs => rw [hAdec]
    rw [map_add, map_add, tanProj_dN_tanProj hN hb0, zero_add]
    exact tanProj_eq_self hN (dN_tanProj_mem_of_mem_orthogonal hN hb0
      (dN_tanProj_mem_orthogonal_of_mem hN ha0 ha0))
  have e2 : tanProj hN q (D (a p₀) (partialY b p₀)) = D (a p₀) (D (a p₀) (b p₀)) := by
    conv_lhs => rw [hMdec]
    rw [map_add, map_add, tanProj_dN_tanProj hN ha0, zero_add]
    exact tanProj_eq_self hN (dN_tanProj_mem_of_mem_orthogonal hN ha0
      (dN_tanProj_mem_orthogonal_of_mem hN ha0 hb0))
  have hII : D (b p₀) (a p₀) = D (a p₀) (b p₀) := secondFundForm_comm hN hb0 ha0
  rw [hPQ, hL, hR, map_add, map_add, tanProj_tanProj, tanProj_tanProj, hsym, e1, e2,
    curvR_of_mem hN (hFN p₀ hp₀), curvOp_apply]
  simp only [secondFundForm]
  rw [hII]
  abel

/-! ### Derivatives of the first variation along a second parameter -/

/-- **The second variation** (half of Milnor's `E_**`) at the path `γ`, Milnor's right side of
Theorem 13.1: `−Σ_t ⟨W₂(t), Δ_t DW₁/dt⟩ − ∫₀¹ ⟨W₂, D²W₁/dt² + R(V, W₁)V⟩ dt`, with
`D/dt = Morse.covD`, `V = dγ/dt`, `R = Morse.curvR`, and `Δ_t DW₁/dt = P_{γ(t)}(Δ_t W₁')` the jump
of the covariant derivative (`DW₁/dt(t^±) = P W₁'(t^±)`), the sum over the finitely many
`t ∈ (0, 1)` at which it is not zero. -/
def secondVariation (γ X₁ X₂ : ℝ → V) : ℝ :=
  -(∑ᶠ t ∈ Ioo (0 : ℝ) 1, ⟪X₂ t, prj hN (γ t) (jump X₁ t)⟫) -
    ∫ t in (0 : ℝ)..1,
      ⟪X₂ t, covD hN γ (covD hN γ X₁) t + curvR hN (γ t) (deriv γ t) (X₁ t) (deriv γ t)⟫

omit [FiniteDimensional ℝ V] in
/-- The jumps of the velocity of the paths of a variation depend differentiably on the parameter:
`d/du Δ_x(∂α/∂t) = Δ_x(∂/∂t ∂α/∂u)` (Milnor's "rearranging the second term", p. 75: `D/∂u`
commutes with the jump, and Lemma 8.7 on each strip). -/
theorem IsVariation.hasDerivAt_jump {U : Set ℝ} {α : ℝ → ℝ → V} {B : Finset ℝ}
    (hα : IsVariation N U α B) {u₀ : ℝ} (hu₀ : u₀ ∈ U) {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun u => jump (α u) x) (jump (fun t => deriv (fun v => α v t) u₀) x) u₀ := by
  have hU := hα.isOpen
  obtain ⟨s, hs, hsx, hBs⟩ := exists_piece_left B hx.1
  obtain ⟨s', hxs', hs', hBs'⟩ := exists_piece_right B hx.2
  have hL : ContDiffOn ℝ ∞ (unc α) (U ×ˢ Icc s x) := hα.smooth s x hs hsx hx.2.le hBs
  have hR : ContDiffOn ℝ ∞ (unc α) (U ×ˢ Icc x s') := hα.smooth x s' hx.1.le hxs' hs' hBs'
  -- the one-sided derivatives of the variation field at `x`, on each side
  have hdR : HasDerivAt (fun u => pdT (U ×ˢ Icc x s') (unc α) (u, x))
      (derivWithin (fun t => deriv (fun v => α v t) u₀) (Ici x) x) u₀ := by
    have h1 := hasDerivAt_pdU hU ((contDiffOn_pdT hU hxs' hR).differentiableOn (by simp)) hu₀
      (left_mem_Icc.2 hxs'.le)
    rw [pdU_pdT hU hxs' hR (mk_mem_prod hu₀ (left_mem_Icc.2 hxs'.le))] at h1
    convert h1 using 1
    rw [← derivWithin_Ici_eq_pdT hxs' ((contDiffOn_pdU hU hxs' hR).differentiableOn (by simp))
      hu₀]
    refine Filter.EventuallyEq.derivWithin_eq ?_ (piece_varDeriv hU hR hu₀ (left_mem_Icc.2
      hxs'.le))
    filter_upwards [Icc_mem_nhdsGE hxs'] with t ht
    exact piece_varDeriv hU hR hu₀ ht
  have hdL : HasDerivAt (fun u => pdT (U ×ˢ Icc s x) (unc α) (u, x))
      (derivWithin (fun t => deriv (fun v => α v t) u₀) (Iic x) x) u₀ := by
    have h1 := hasDerivAt_pdU hU ((contDiffOn_pdT hU hsx hL).differentiableOn (by simp)) hu₀
      (right_mem_Icc.2 hsx.le)
    rw [pdU_pdT hU hsx hL (mk_mem_prod hu₀ (right_mem_Icc.2 hsx.le))] at h1
    convert h1 using 1
    rw [← derivWithin_Iic_eq_pdT hsx ((contDiffOn_pdU hU hsx hL).differentiableOn (by simp))
      hu₀]
    refine Filter.EventuallyEq.derivWithin_eq ?_ (piece_varDeriv hU hL hu₀ (right_mem_Icc.2
      hsx.le))
    filter_upwards [Icc_mem_nhdsLE hsx] with t ht
    exact piece_varDeriv hU hL hu₀ ht
  refine (hdR.sub hdL).congr_of_eventuallyEq ?_
  filter_upwards [hU.mem_nhds hu₀] with u hu
  rw [jump, piece_derivWithin_Ici hxs' hR hu, piece_derivWithin_Iic hsx hL hu]
  rfl

omit [FiniteDimensional ℝ V] in
/-- For a 2-parameter variation, `∂α/∂u₂` on the slice `u₂ = 0` is, on each strip, the
restriction of a function of `(u₁, t)` smooth on the closed strip. -/
theorem IsVariation.exists_param₂ {U : Set (ℝ × ℝ)} {α : ℝ × ℝ → ℝ → V} {B : Finset ℝ}
    (hα : IsVariation N U α B) {s t : ℝ} (hs : 0 ≤ s) (hst : s < t) (ht : t ≤ 1)
    (hB : ∀ x ∈ B, x ∉ Ioo s t) :
    ∃ G : ℝ × ℝ → V, ContDiffOn ℝ ∞ G ({u₁ : ℝ | (u₁, (0 : ℝ)) ∈ U} ×ˢ Icc s t) ∧
      ∀ u₁ τ, (u₁, (0 : ℝ)) ∈ U → τ ∈ Icc s t → deriv (fun u₂ => α (u₁, u₂) τ) 0 = G (u₁, τ) := by
  set S := U ×ˢ Icc s t
  have hS : UniqueDiffOn ℝ S := hα.isOpen.uniqueDiffOn.prod (uniqueDiffOn_Icc hst)
  have hF := hα.smooth s t hs hst ht hB
  set G : ℝ × ℝ → V := fun p =>
    fderivWithin ℝ (fun p : (ℝ × ℝ) × ℝ => α p.1 p.2) S ((p.1, 0), p.2) ((0, 1), 0)
  have hmaps : MapsTo (fun p : ℝ × ℝ => ((p.1, (0 : ℝ)), p.2))
      ({u₁ : ℝ | (u₁, (0 : ℝ)) ∈ U} ×ˢ Icc s t) S := fun p hp => mk_mem_prod hp.1 hp.2
  refine ⟨G, ((hF.fderivWithin hS (m := ∞) (by simp)).comp
    ((contDiff_fst.prodMk contDiff_const).prodMk contDiff_snd).contDiffOn hmaps).clm_apply
      contDiffOn_const, fun u₁ τ hu hτ => ?_⟩
  have h1 : HasFDerivWithinAt (fun p : (ℝ × ℝ) × ℝ => α p.1 p.2)
      (fderivWithin ℝ (fun p : (ℝ × ℝ) × ℝ => α p.1 p.2) S ((u₁, 0), τ)) S ((u₁, 0), τ) :=
    ((hF _ (mk_mem_prod hu hτ)).differentiableWithinAt (by simp)).hasFDerivWithinAt
  have h2 : HasDerivAt (fun u₂ : ℝ => ((u₁, u₂), τ)) (((0 : ℝ), (1 : ℝ)), (0 : ℝ)) 0 :=
    ((hasDerivAt_const _ _).prodMk (hasDerivAt_id _)).prodMk (hasDerivAt_const _ _)
  have h3 : HasDerivWithinAt ((fun p : (ℝ × ℝ) × ℝ => α p.1 p.2) ∘ fun u₂ => ((u₁, u₂), τ))
      (G (u₁, τ)) {u₂ | (u₁, u₂) ∈ U} 0 :=
    HasFDerivWithinAt.comp_hasDerivWithinAt (0 : ℝ) h1 h2.hasDerivWithinAt
      fun v hv => mk_mem_prod hv hτ
  exact (h3.hasDerivAt ((hα.isOpen.preimage (by fun_prop)).mem_nhds hu)).deriv

/-! ### Theorem 13.1 -/

/-- **Theorem 13.1 (the second variation formula)** (Milnor p. 74): let `α(u₁, u₂, t)` be a
2-parameter variation of a geodesic `γ` (`C^∞` on `[0, 1]`, zero acceleration), with variation
fields `W₁ = ∂α/∂u₁ (0, 0, ·)`, `W₂ = ∂α/∂u₂ (0, 0, ·)`.  Then the second derivative
`∂²E/∂u₁∂u₂ (0, 0) = ∂/∂u₁ (∂E/∂u₂ (u₁, 0))` at `u₁ = 0` exists, and
`½ ∂²E/∂u₁∂u₂ (0, 0) = −Σ_t ⟨W₂(t), Δ_t DW₁/dt⟩ − ∫₀¹ ⟨W₂, D²W₁/dt² + R(V, W₁)V⟩ dt`
(`Morse.secondVariation`).

Proof (Milnor's): by the first variation formula at every `u₁` (`(12.2′)`,
`Morse.IsVariation.hasDerivAt_energy`), `½ ∂E/∂u₂ (u₁, 0)` is `−Σ ⟨∂α/∂u₂, Δ_t ∂α/∂t⟩ −
∫ ⟨∂α/∂u₂, D/∂t ∂α/∂t⟩`; differentiate in `u₁` at `0`: the terms containing `Δ_t V = 0` or
`D/dt V = 0` vanish, `d/du₁ Δ_t ∂α/∂t = Δ_t ∂/∂t ∂α/∂u₁` (`Morse.IsVariation.hasDerivAt_jump`), and
`D/∂u₁ D/∂t V = D²W₁/dt² + R(V, W₁)V` (`Morse.curvature_identity`, Lemmas 8.7 and 9.2). -/
theorem second_variation {γ : ℝ → V} (hgeo : IsUnbrokenGeodesic hN γ)
    {U : Set (ℝ × ℝ)} {α : ℝ × ℝ → ℝ → V} {B : Finset ℝ} (hα : IsVariation N U α B)
    (hαγ : ∀ t ∈ Icc (0 : ℝ) 1, α 0 t = γ t) :
    HasDerivAt (fun u₁ => deriv (fun u₂ => energy (α (u₁, u₂)) 0 1) 0)
      (2 * secondVariation hN γ (fun t => deriv (fun u₁ => α (u₁, 0) t) 0)
        (fun t => deriv (fun u₂ => α (0, u₂) t) 0)) 0 := by
  set U₁ : Set ℝ := {u₁ | (u₁, (0 : ℝ)) ∈ U}
  set σ : ℝ → ℝ → V := fun u₁ t => α (u₁, 0) t
  set Y : ℝ → ℝ → V := fun u₁ t => deriv (fun u₂ => α (u₁, u₂) t) 0
  set W₁ : ℝ → V := fun t => deriv (fun u₁ => α (u₁, 0) t) 0
  set W₂ : ℝ → V := fun t => deriv (fun u₂ => α (0, u₂) t) 0
  have h00 : ((0 : ℝ), (0 : ℝ)) ∈ U := hα.zero_mem
  have hσ : IsVariation N U₁ σ B :=
    hα.comp (φ := fun u₁ => (u₁, (0 : ℝ))) (contDiff_id.prodMk contDiff_const) h00
  have hβ₀ : IsVariation N {u₂ | ((0 : ℝ), u₂) ∈ U} (fun u₂ => α (0, u₂)) B :=
    hα.comp (φ := fun u₂ => ((0 : ℝ), u₂)) (contDiff_const.prodMk contDiff_id) h00
  have hU₁ : IsOpen U₁ := hσ.isOpen
  have h0U₁ : (0 : ℝ) ∈ U₁ := hσ.zero_mem
  have hσγ : ∀ t ∈ Icc (0 : ℝ) 1, σ 0 t = γ t := fun t ht => hαγ t ht
  have hγN : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ N := fun t ht => hσγ t ht ▸ hσ.mem 0 h0U₁ t ht
  have hσev : ∀ t ∈ Ioo (0 : ℝ) 1, σ 0 =ᶠ[𝓝 t] γ := fun t ht => by
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with x hx
    exact hσγ x (Ioo_subset_Icc_self hx)
  -- `W₂` is tangent along `γ`
  have hW₂T : ∀ t ∈ Icc (0 : ℝ) 1, prj hN (γ t) (W₂ t) = W₂ t := fun t ht => by
    have := (hβ₀.varField_mem hN).2.1 t ht
    rw [show α (0, 0) t = γ t from hαγ t ht] at this
    exact this
  -- Step 1: the first variation in `u₂`, at every `u₁`
  have h1 : ∀ u₁ ∈ U₁, deriv (fun u₂ => energy (α (u₁, u₂)) 0 1) 0 =
      2 * firstVariation hN (σ u₁) (Y u₁) := by
    intro u₁ hu₁
    have hβ : IsVariation N {u₂ | (u₁, u₂) ∈ U} (fun u₂ => α (u₁, u₂)) B :=
      hα.comp (φ := fun u₂ => (u₁, u₂)) (contDiff_const.prodMk contDiff_id) hu₁
    exact (hβ.hasDerivAt_energy hN (u₀ := 0) hu₁).deriv
  suffices h2 : HasDerivAt (fun u₁ => firstVariation hN (σ u₁) (Y u₁))
      (secondVariation hN γ W₁ W₂) 0 by
    refine (h2.const_mul 2).congr_of_eventuallyEq ?_
    filter_upwards [hU₁.mem_nhds h0U₁] with u₁ hu₁
    exact h1 u₁ hu₁
  -- Step 2: the jump terms
  have hfv : ∀ u₁ ∈ U₁, firstVariation hN (σ u₁) (Y u₁) =
      -(∑ x ∈ B with x ∈ Ioo (0 : ℝ) 1, ⟪Y u₁ x, jump (σ u₁) x⟫) -
        ∫ t in (0 : ℝ)..1, ⟪Y u₁ t, accel hN (σ u₁) t⟫ := fun u₁ hu₁ => by
    rw [firstVariation, finsum_jump_eq_sum (fun x hx hxB => hσ.differentiableAt hu₁ hx hxB)]
  have hS : HasDerivAt (fun u₁ => ∑ x ∈ B with x ∈ Ioo (0 : ℝ) 1, ⟪Y u₁ x, jump (σ u₁) x⟫)
      (∑ x ∈ B with x ∈ Ioo (0 : ℝ) 1, ⟪W₂ x, prj hN (γ x) (jump W₁ x)⟫) 0 := by
    refine HasDerivAt.fun_sum fun x hx => ?_
    have hx' : x ∈ Ioo (0 : ℝ) 1 := (Finset.mem_filter.1 hx).2
    obtain ⟨s', hxs', hs', hBs'⟩ := exists_piece_right B hx'.2
    obtain ⟨G, hG, hGY⟩ := hα.exists_param₂ hx'.1.le hxs' hs' hBs'
    have hYd : HasDerivAt (fun u₁ => Y u₁ x) (pdU (U₁ ×ˢ Icc x s') G (0, x)) 0 := by
      refine (hasDerivAt_pdU hU₁ (hG.differentiableOn (by simp)) h0U₁
        (left_mem_Icc.2 hxs'.le)).congr_of_eventuallyEq ?_
      filter_upwards [hU₁.mem_nhds h0U₁] with u hu
      exact hGY u x hu (left_mem_Icc.2 hxs'.le)
    have hJ := hσ.hasDerivAt_jump h0U₁ hx'
    have hJ0 : jump (σ 0) x = 0 := by
      rw [jump_congr (hσev x hx')]
      exact jump_eq_zero (hgeo.2.hasDerivAt hx').differentiableAt
    have h3 := hYd.inner ℝ hJ
    rw [hJ0, inner_zero_right, add_zero] at h3
    exact h3.congr_deriv (inner_prj_right_of_eq hN (hW₂T x (Ioo_subset_Icc_self hx')) _).symm
  -- Step 3: the integral term
  set g : ℝ → ℝ → ℝ := fun u₁ t => ⟪Y u₁ t, accel hN (σ u₁) t⟫
  have hI : HasDerivAt (fun u₁ => ∫ t in (0 : ℝ)..1, g u₁ t)
      (∫ t in (0 : ℝ)..1, deriv (fun u₁ => g u₁ t) 0) 0 := by
    refine hasDerivAt_integral_of_piecewise hU₁ (B := B) (lo := 0) (hi := 1)
      (fun s t hs hst ht hB => ?_) le_rfl zero_le_one le_rfl h0U₁
    obtain ⟨G, hG, hGY⟩ := hα.exists_param₂ hs hst ht hB
    have hF : ContDiffOn ℝ ∞ (unc σ) (U₁ ×ˢ Icc s t) := hσ.smooth s t hs hst ht hB
    have hFN : ∀ p ∈ U₁ ×ˢ Icc s t, unc σ p ∈ N := fun p hp =>
      hσ.mem p.1 hp.1 p.2 ⟨hs.trans hp.2.1, hp.2.2.trans ht⟩
    refine ⟨fun p => ⟪G p, prj hN (unc σ p) (pdT (U₁ ×ˢ Icc s t) (pdT (U₁ ×ˢ Icc s t)
      (unc σ)) p)⟫, (hG.inner ℝ ((ContDiffOn.prj_comp hN hF hFN).clm_apply
        (contDiffOn_pdT hU₁ hst (contDiffOn_pdT hU₁ hst hF)))).of_le (by simp),
      fun u hu τ hτ => ?_⟩
    simp only [g, accel, covD]
    rw [← hGY u τ hu (Ioo_subset_Icc_self hτ), piece_deriv_deriv hU₁ hst hF hu hτ]
    rfl
  -- Step 4: the integrand at `u₁ = 0`, off the break points: Lemmas 8.7 and 9.2
  have hpt : ∀ t ∈ Ioo (0 : ℝ) 1, t ∉ B → deriv (fun u₁ => g u₁ t) 0 =
      ⟪W₂ t, covD hN γ (covD hN γ W₁) t + curvR hN (γ t) (deriv γ t) (W₁ t) (deriv γ t)⟫ := by
    intro t ht htB
    obtain ⟨s, s', hs, hst, hts', hs', hBs⟩ := exists_piece_around B ht.1 ht.2 htB
    set O := U₁ ×ˢ Ioo s s'
    have hO : IsOpen O := hU₁.prod isOpen_Ioo
    have hF : ContDiffOn ℝ ∞ (unc σ) (U₁ ×ˢ Icc s s') :=
      hσ.smooth s s' hs (hst.trans hts') hs' hBs
    have hFO : ContDiffOn ℝ ∞ (unc σ) O := hF.mono (prod_mono le_rfl Ioo_subset_Icc_self)
    have hFN : ∀ p ∈ O, unc σ p ∈ N := fun p hp =>
      hσ.mem p.1 hp.1 p.2 ⟨hs.trans hp.2.1.le, hp.2.2.le.trans hs'⟩
    have hp₀ : ((0 : ℝ), t) ∈ O := ⟨h0U₁, hst, hts'⟩
    have hdiffO : ∀ {K : ℝ × ℝ → V}, ContDiffOn ℝ ∞ K O → ∀ p ∈ O, DifferentiableAt ℝ K p :=
      fun hK p hp => (hK.contDiffAt (hO.mem_nhds hp)).differentiableAt (by simp)
    have hd1 : ∀ p ∈ O, deriv (σ p.1) p.2 = partialY (unc σ) p := fun p hp =>
      (hasDerivAt_partialY (hdiffO hFO p hp)).deriv
    have hd2 : ∀ p ∈ O, deriv (deriv (σ p.1)) p.2 = partialY (partialY (unc σ)) p := by
      intro p hp
      have hev : deriv (σ p.1) =ᶠ[𝓝 p.2] fun y => partialY (unc σ) (p.1, y) := by
        filter_upwards [Ioo_mem_nhds hp.2.1 hp.2.2] with y hy
        exact hd1 (p.1, y) ⟨hp.1, hy⟩
      rw [hev.deriv_eq]
      exact (hasDerivAt_partialY (hdiffO (contDiffOn_partialY hO hFO) p hp)).deriv
    set Acc : ℝ × ℝ → V := fun p => prj hN (unc σ p) (partialY (partialY (unc σ)) p)
    have hAcc : ContDiffOn ℝ ∞ Acc O := (ContDiffOn.prj_comp hN hFO hFN).clm_apply
      (contDiffOn_partialY hO (contDiffOn_partialY hO hFO))
    obtain ⟨G, hG, hGY⟩ := hα.exists_param₂ hs (hst.trans hts') hs' hBs
    have hYd : HasDerivAt (fun u => Y u t) (pdU (U₁ ×ˢ Icc s s') G (0, t)) 0 := by
      refine (hasDerivAt_pdU hU₁ (hG.differentiableOn (by simp)) h0U₁
        ⟨hst.le, hts'.le⟩).congr_of_eventuallyEq ?_
      filter_upwards [hU₁.mem_nhds h0U₁] with u hu
      exact hGY u t hu ⟨hst.le, hts'.le⟩
    have hgev : (fun u => g u t) =ᶠ[𝓝 0] fun u => ⟪Y u t, Acc (u, t)⟫ := by
      filter_upwards [hU₁.mem_nhds h0U₁] with u hu
      simp only [g, accel, covD, Acc]
      rw [hd2 (u, t) ⟨hu, hst, hts'⟩]
      rfl
    have hAccd : HasDerivAt (fun u => Acc (u, t)) (partialX Acc (0, t)) 0 :=
      hasDerivAt_partialX (hdiffO hAcc _ hp₀)
    rw [hgev.deriv_eq, (hYd.inner ℝ hAccd).deriv]
    -- the acceleration of `γ` vanishes
    have hAcc0 : Acc (0, t) = 0 := by
      have e : Acc (0, t) = accel hN (σ 0) t := by
        simp only [Acc, accel, covD]
        rw [hd2 _ hp₀]
        rfl
      rw [e, accel, covD, (hσev t ht).self_of_nhds, (hσev t ht).deriv.deriv_eq,
        prj_of_mem hN (hgeo.2.mem t ht), hgeo.2.tanProj_deriv_deriv ht]
    rw [hAcc0, inner_zero_right, add_zero]
    have hγt : unc σ ((0 : ℝ), t) = γ t := hσγ t (Ioo_subset_Icc_self ht)
    rw [show Y 0 t = W₂ t from rfl, ← inner_prj_right_of_eq hN (hW₂T t (Ioo_subset_Icc_self ht))]
    have hci := curvature_identity hN hO hFO hFN hp₀
    rw [hγt] at hci
    rw [hci]
    -- identify the two terms
    have hW₁ : ∀ τ ∈ Ioo s s', W₁ τ = partialX (unc σ) (0, τ) := fun τ hτ =>
      (hasDerivAt_partialX (hdiffO hFO ((0 : ℝ), τ) ⟨h0U₁, hτ⟩)).deriv
    have hV : deriv γ t = partialY (unc σ) (0, t) := by
      rw [← (hσev t ht).deriv_eq]
      exact hd1 _ hp₀
    set K : ℝ × ℝ → V := fun p => prj hN (unc σ p) (partialY (partialX (unc σ)) p)
    have hK : ContDiffOn ℝ ∞ K O := (ContDiffOn.prj_comp hN hFO hFN).clm_apply
      (contDiffOn_partialY hO (contDiffOn_partialX hO hFO))
    have hDW : covD hN γ W₁ =ᶠ[𝓝 t] fun τ => K (0, τ) := by
      have hO' : Ioo s s' ∩ Ioo 0 1 ∈ 𝓝 t := inter_mem (Ioo_mem_nhds hst hts')
        (Ioo_mem_nhds ht.1 ht.2)
      filter_upwards [hO'] with τ hτ
      have hev : W₁ =ᶠ[𝓝 τ] fun y => partialX (unc σ) (0, y) := by
        filter_upwards [Ioo_mem_nhds hτ.1.1 hτ.1.2] with y hy
        exact hW₁ y hy
      simp only [covD, K]
      rw [hev.deriv_eq, (hasDerivAt_partialY (hdiffO (contDiffOn_partialX hO hFO) ((0 : ℝ), τ)
        ⟨h0U₁, hτ.1⟩)).deriv, ← hσγ τ (Ioo_subset_Icc_self hτ.2)]
      rfl
    have hDDW : covD hN γ (covD hN γ W₁) t = prj hN (γ t) (partialY K (0, t)) := by
      rw [covD, hDW.deriv_eq, (hasDerivAt_partialY (hdiffO hK ((0 : ℝ), t) hp₀)).deriv]
    rw [hDDW, hV, hW₁ t ⟨hst, hts'⟩]
  -- assemble
  have hsv : secondVariation hN γ W₁ W₂ =
      -(∑ x ∈ B with x ∈ Ioo (0 : ℝ) 1, ⟪W₂ x, prj hN (γ x) (jump W₁ x)⟫) -
        ∫ t in (0 : ℝ)..1, deriv (fun u₁ => g u₁ t) 0 := by
    have hsum : ∑ᶠ t ∈ Ioo (0 : ℝ) 1, ⟪W₂ t, prj hN (γ t) (jump W₁ t)⟫ =
        ∑ x ∈ B with x ∈ Ioo (0 : ℝ) 1, ⟪W₂ x, prj hN (γ x) (jump W₁ x)⟫ :=
      finsum_mem_Ioo_eq_sum fun x hx hxB => by
        rw [jump_eq_zero (hσ.differentiableAt_varDeriv h0U₁ hx hxB), map_zero, inner_zero_right]
    rw [secondVariation, hsum]
    congr 1
    refine intervalIntegral.integral_congr_ae ?_
    have hfin : ∀ᵐ τ ∂(volume : Measure ℝ), τ ∉ insert (1 : ℝ) (B : Set ℝ) :=
      (B.finite_toSet.insert 1).countable.ae_notMem _
    filter_upwards [hfin] with τ hτB hτ
    rw [uIoc_of_le zero_le_one] at hτ
    rw [mem_insert_iff, not_or] at hτB
    exact (hpt τ ⟨hτ.1, lt_of_le_of_ne hτ.2 hτB.1⟩ hτB.2).symm
  rw [hsv]
  refine (hS.neg.sub hI).congr_of_eventuallyEq ?_
  filter_upwards [hU₁.mem_nhds h0U₁] with u₁ hu₁
  exact hfv u₁ hu₁

/-- **Milnor's `E_**` is well defined** (p. 74, where Theorem 13.1 is introduced for this purpose):
two 2-parameter variations of a geodesic with the same variation fields have the same second
derivative `∂²E/∂u₁∂u₂ (0, 0)`. -/
theorem second_variation_eq {γ : ℝ → V} (hgeo : IsUnbrokenGeodesic hN γ)
    {U U' : Set (ℝ × ℝ)} {α α' : ℝ × ℝ → ℝ → V} {B B' : Finset ℝ} (hα : IsVariation N U α B)
    (hα' : IsVariation N U' α' B') (hαγ : ∀ t ∈ Icc (0 : ℝ) 1, α 0 t = γ t)
    (hα'γ : ∀ t ∈ Icc (0 : ℝ) 1, α' 0 t = γ t)
    (h₁ : ∀ t ∈ Icc (0 : ℝ) 1,
      deriv (fun u₁ => α (u₁, 0) t) 0 = deriv (fun u₁ => α' (u₁, 0) t) 0)
    (h₂ : ∀ t ∈ Icc (0 : ℝ) 1,
      deriv (fun u₂ => α (0, u₂) t) 0 = deriv (fun u₂ => α' (0, u₂) t) 0) :
    deriv (fun u₁ => deriv (fun u₂ => energy (α (u₁, u₂)) 0 1) 0) 0 =
      deriv (fun u₁ => deriv (fun u₂ => energy (α' (u₁, u₂)) 0 1) 0) 0 := by
  rw [(second_variation hN hgeo hα hαγ).deriv, (second_variation hN hgeo hα' hα'γ).deriv]
  congr 1
  rw [secondVariation, secondVariation]
  congr 1
  · congr 1
    refine finsum_mem_congr rfl fun t ht => ?_
    have hev : (fun t => deriv (fun u₁ => α (u₁, 0) t) 0) =ᶠ[𝓝 t]
        fun t => deriv (fun u₁ => α' (u₁, 0) t) 0 := by
      filter_upwards [Ioo_mem_nhds ht.1 ht.2] with x hx
      exact h₁ x (Ioo_subset_Icc_self hx)
    rw [h₂ t (Ioo_subset_Icc_self ht), jump_congr hev]
  · refine intervalIntegral.integral_congr_Ioo_of_le zero_le_one fun t ht => ?_
    have hev : (fun t => deriv (fun u₁ => α (u₁, 0) t) 0) =ᶠ[𝓝 t]
        fun t => deriv (fun u₁ => α' (u₁, 0) t) 0 := by
      filter_upwards [Ioo_mem_nhds ht.1 ht.2] with x hx
      exact h₁ x (Ioo_subset_Icc_self hx)
    have hev' : covD hN γ (fun t => deriv (fun u₁ => α (u₁, 0) t) 0) =ᶠ[𝓝 t]
        covD hN γ (fun t => deriv (fun u₁ => α' (u₁, 0) t) 0) := by
      filter_upwards [Ioo_mem_nhds ht.1 ht.2] with x hx
      have hevx : (fun t => deriv (fun u₁ => α (u₁, 0) t) 0) =ᶠ[𝓝 x]
          fun t => deriv (fun u₁ => α' (u₁, 0) t) 0 := by
        filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
        exact h₁ y (Ioo_subset_Icc_self hy)
      rw [covD, covD, hevx.deriv_eq]
    rw [h₂ t (Ioo_subset_Icc_self ht), covD, covD, hev'.deriv_eq, h₁ t (Ioo_subset_Icc_self ht)]

/-- **Remark 13.5** (Milnor p. 76): the diagonal values of `E_**` are second derivatives along
1-parameter variations: for a variation `ᾱ` of a geodesic with variation field `W`,
`d²E(ᾱ(u))/du² (0) = E_**(W, W) = 2 · secondVariation W W`.  (Proof: `β(u₁, u₂) = ᾱ(u₁ + u₂)` is
a 2-parameter variation with both variation fields equal to `W`.) -/
theorem remark_13_5 {γ : ℝ → V} (hgeo : IsUnbrokenGeodesic hN γ) {U : Set ℝ}
    {α : ℝ → ℝ → V} {B : Finset ℝ} (hα : IsVariation N U α B)
    (hαγ : ∀ t ∈ Icc (0 : ℝ) 1, α 0 t = γ t) :
    HasDerivAt (deriv fun u => energy (α u) 0 1)
      (2 * secondVariation hN γ (varField α) (varField α)) 0 := by
  have hβ : IsVariation N ((fun p : ℝ × ℝ => p.1 + p.2) ⁻¹' U) (fun p => α (p.1 + p.2)) B :=
    hα.comp (φ := fun p : ℝ × ℝ => p.1 + p.2) (contDiff_fst.add contDiff_snd)
      (by simpa using hα.zero_mem)
  have h := second_variation hN hgeo hβ (by simpa using hαγ)
  simp only [add_zero, zero_add] at h
  refine h.congr_of_eventuallyEq (Eventually.of_forall fun u₁ => ?_)
  have := deriv_comp_const_add (fun u => energy (α u) 0 1) u₁ 0
  simp only [add_zero] at this
  exact this.symm

end Morse
