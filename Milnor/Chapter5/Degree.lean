import Milnor.Chapter5.HomotopyInv
import Milnor.Chapter4.Degree

/-!
# The Brouwer degree (Milnor, chapter 5)

* orientation preservation along an isotopy: if `h` is the end of a smooth isotopy from the
  identity (every stage a diffeomorphism), then `sign dh = 1` everywhere;
* `signAt` is multiplicative under composition;
* **Theorem B** (Milnor p. 28): for `f : M → N`, `M` compact, `N` connected, the signed count
  `degAt f y` is the same at every regular value `y`;
* the **degree** `deg f`, and Theorem A for it: smoothly homotopic maps have the same degree;
* a map of nonzero degree is surjective; the identity has degree `1`.
-/

open Set Module Filter Topology Function
open scoped ContDiff Manifold

noncomputable section

namespace Milnor

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G} [J.Boundaryless]
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N] {n : ℕ}

/-- The sign of the identity is `1`. -/
theorem signAt_id (oN : Orient J N n) (z : N) : signAt oN oN id z = 1 := by
  unfold signAt
  rw [HasMFDerivAt.mfd_eq (hasMFDerivAt_id (I := J) z)]
  exact orSign_id _

/-- **Chain rule for signs.** -/
theorem signAt_comp {P : Type*} [TopologicalSpace P] [ChartedSpace G P] [IsManifold J ∞ P]
    (hE : finrank ℝ E = n) (hF : finrank ℝ F = n) (oM : Orient I M n) (oN : Orient J N n)
    (oP : Orient J P n) {f : M → N} (hf : ContMDiff I J ∞ f) {h : N → P}
    (hh : ContMDiff J J ∞ h) (x : M) :
    signAt oM oP (fun x => h (f x)) x = signAt oN oP h (f x) * signAt oM oN f x := by
  unfold signAt
  have hc := HasMFDerivAt.mfd_eq ((hasMFDerivAt_mfd (I := J) (J := J)
    (hh.mdifferentiableAt (x := f x) (by simp))).comp x
    (hasMFDerivAt_mfd (I := I) (J := J) (hf.mdifferentiableAt (by simp))))
  show orSign (oM.or x) (oP.or ((h ∘ f) x)) (mfd I J (h ∘ f) x) = _
  rw [hc]
  exact orSign_comp hE hF _ _ _ _ _

/-- **Orientation preservation along an isotopy.** If `y` and `z` are isotopic, the
diffeomorphism at the end of the isotopy preserves orientation. -/
theorem exists_isotopy_signAt_eq_one [T2Space N] (hF : finrank ℝ F = n) (oN : Orient J N n)
    {y z : N} (hiso : Isotopic J y z) :
    ∃ (h : N ≃ₘ⟮J, J⟯ N) (Hm : N × ℝ → N), ContMDiff (J.prod 𝓘(ℝ, ℝ)) J ∞ Hm ∧
      (∀ x, Hm (x, 0) = x) ∧ (∀ x, Hm (x, 1) = h x) ∧ h y = z ∧ ∀ x, signAt oN oN h x = 1 := by
  obtain ⟨h, Hm, hH, h0, h1, hyz, hslice⟩ := hiso
  refine ⟨h, Hm, hH, h0, h1, hyz, fun x => ?_⟩
  -- the map `G (z, t) = (H (z, t), t)` of `N × ℝ`
  set Gm : N × ℝ → N × ℝ := pairMap Hm Prod.snd with hGm
  have hG : ContMDiff (J.prod 𝓘(ℝ, ℝ)) (J.prod 𝓘(ℝ, ℝ)) ∞ Gm := hH.prodMk contMDiff_snd
  have hF' : finrank ℝ (F × ℝ) = n + 1 := finrank_prod_real hF
  -- its sign at `(z, t)` is the sign of `H (·, t)` at `z`
  have hsG : ∀ (z : N) (t : ℝ), signAt (oN.prodReal hF) (oN.prodReal hF) Gm (z, t) =
      signAt oN oN (fun z => Hm (z, t)) z := by
    intro z t
    rw [signAt_prodReal hF hF oN oN (A := mfd J J (fun z => Hm (z, t)) z)
      (w := mfd (J.prod 𝓘(ℝ, ℝ)) J Hm (z, t) (0, 1)) (c := 1) ?_]
    · rw [sgn_one, mul_one]; rfl
    · intro v s
      rw [hGm, mfd_pairMap (hH.mdifferentiableAt (by simp))
        ((contMDiff_snd (I := J) (J := 𝓘(ℝ, ℝ)) (n := ∞)).mdifferentiableAt (by simp))]
      show (mfd (J.prod 𝓘(ℝ, ℝ)) J Hm (z, t) (v, s),
        mfd (J.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) Prod.snd (z, t) (v, s)) = _
      rw [mfd_prod_apply hH, HasMFDerivAt.mfd_eq (hasMFDerivAt_snd (I := J) (I' := 𝓘(ℝ, ℝ)) (z, t))]
      exact Prod.ext rfl (by show s = 1 * s; ring)
  -- every stage is a diffeomorphism, so the sign is nonzero everywhere
  have hreg : ∀ (z : N) (t : ℝ), signAt oN oN (fun z => Hm (z, t)) z ≠ 0 := by
    intro z t
    obtain ⟨ht, hht⟩ := hslice t
    have : (fun z => Hm (z, t)) = ht := funext hht
    rw [this]
    have hsurj : Function.Surjective (mfd J J ht z) := surjective_mfderiv_diffeomorph ht z
    exact IsRegularPoint.signAt_ne_zero hF hF oN oN hsurj
  -- `t ↦ signAt (H (·, t)) x` is locally constant
  let φ : ℝ → ℤ := fun t => signAt oN oN (fun z => Hm (z, t)) x
  have hloc : IsLocallyConstant φ := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro t
    have hne : signAt (oN.prodReal hF) (oN.prodReal hF) Gm (x, t) ≠ 0 := by
      rw [hsG]; exact hreg x t
    have hregG : IsRegularPoint (J.prod 𝓘(ℝ, ℝ)) (J.prod 𝓘(ℝ, ℝ)) Gm (x, t) :=
      ((signAt_ne_zero_iff hF' hF' _ _ _ _).1 hne).2
    have hev := eventually_signAt_eq hF' hF' (oN.prodReal hF) (oN.prodReal hF) hG hregG
    have hcont : Tendsto (fun t' : ℝ => ((x, t') : N × ℝ)) (𝓝 t) (𝓝 (x, t)) :=
      (continuous_const.prodMk continuous_id).tendsto t
    filter_upwards [hcont.eventually hev] with t' ht'
    show signAt oN oN (fun z => Hm (z, t')) x = signAt oN oN (fun z => Hm (z, t)) x
    rw [← hsG, ← hsG]
    exact ht'
  have hconst := hloc.apply_eq_of_isPreconnected isPreconnected_univ (mem_univ (1 : ℝ))
    (mem_univ (0 : ℝ))
  have h1' : (fun z => Hm (z, 1)) = h := funext h1
  have h0' : (fun z => Hm (z, 0)) = id := funext h0
  show signAt oN oN h x = 1
  have := hconst
  simp only [φ] at this
  rw [h1', h0', signAt_id] at this
  exact this

/-- **Theorem B** (Milnor p. 28): the signed count is the same at all regular values. -/
theorem degAt_eq_of_isRegularValue [CompactSpace M] [T2Space M] [SecondCountableTopology M]
    [T2Space N] [PreconnectedSpace N] (hE : finrank ℝ E = n) (hF : finrank ℝ F = n)
    (oM : Orient I M n) (oN : Orient J N n) {f : M → N} (hf : ContMDiff I J ∞ f) {y z : N}
    (hy : IsRegularValue I J f y) (hz : IsRegularValue I J f z) :
    degAt oM oN f y = degAt oM oN f z := by
  obtain ⟨h, Hm, hH, h0, h1, hyz, hsign⟩ :=
    exists_isotopy_signAt_eq_one hF oN (isotopic_of_preconnected (J := J) y z)
  -- `degAt (h ∘ f) (h y) = degAt f y` since `h` preserves orientation
  have hcomp : degAt oM oN (fun x => h (f x)) (h y) = degAt oM oN f y := by
    unfold degAt
    rw [preimage_diffeomorph_comp h rfl]
    refine finsum_mem_congr rfl fun x _ => ?_
    rw [signAt_comp hE hF oM oN oN hf h.contMDiff x, hsign, one_mul]
  -- the homotopy `(x, t) ↦ H (f x, t)` from `f` to `h ∘ f`
  let F' : M × ℝ → N := fun q => Hm (f q.1, q.2)
  have hF' : ContMDiff (I.prod 𝓘(ℝ, ℝ)) J ∞ F' :=
    hH.comp ((hf.comp contMDiff_fst).prodMk contMDiff_snd)
  have hF0 : (fun x => F' (x, 0)) = f := funext fun x => h0 (f x)
  have hF1 : (fun x => F' (x, 1)) = fun x => h (f x) := funext fun x => h1 (f x)
  have hz1 : IsRegularValue I J (fun x => F' (x, 1)) z := by
    rw [hF1]
    have := hy.diffeomorph_comp hf h
    rwa [hyz] at this
  have hz0 : IsRegularValue I J (fun x => F' (x, 0)) z := by rw [hF0]; exact hz
  have hA := degAt_eq_of_homotopy hE hF oM oN hF' hz0 hz1
  rw [hF0, hF1] at hA
  rw [hyz] at hcomp
  rw [← hcomp, hA]

open Classical in
/-- The **Brouwer degree** of `f : M → N` (`M` compact, `N` connected, both oriented of the same
dimension): the signed count of preimages of any regular value (by Theorem B they all agree;
regular values exist by Brown's theorem when `N` is nonempty).  `0` if there is no regular
value. -/
def deg (oM : Orient I M n) (oN : Orient J N n) (f : M → N) : ℤ :=
  if h : ∃ y, IsRegularValue I J f y then degAt oM oN f (Classical.choose h) else 0

/-- The degree is computed at any regular value. -/
theorem deg_eq [CompactSpace M] [T2Space M] [SecondCountableTopology M] [T2Space N]
    [PreconnectedSpace N] (hE : finrank ℝ E = n) (hF : finrank ℝ F = n) (oM : Orient I M n)
    (oN : Orient J N n) {f : M → N} (hf : ContMDiff I J ∞ f) {y : N}
    (hy : IsRegularValue I J f y) : deg oM oN f = degAt oM oN f y := by
  have hex : ∃ y, IsRegularValue I J f y := ⟨y, hy⟩
  rw [deg, dif_pos hex]
  exact degAt_eq_of_isRegularValue hE hF oM oN hf (Classical.choose_spec hex) hy

/-- **Theorem A** for the degree: smoothly homotopic maps have the same degree. -/
theorem deg_eq_of_homotopy [CompactSpace M] [T2Space M] [SecondCountableTopology M] [T2Space N]
    [PreconnectedSpace N] (hE : finrank ℝ E = n) (hF : finrank ℝ F = n) (oM : Orient I M n)
    (oN : Orient J N n) {F' : M × ℝ → N} (hF' : ContMDiff (I.prod 𝓘(ℝ, ℝ)) J ∞ F') :
    deg oM oN (fun x => F' (x, 0)) = deg oM oN (fun x => F' (x, 1)) := by
  by_cases hN : Nonempty N
  · have hf₀ : ContMDiff I J ∞ (fun x => F' (x, 0)) := hF'.comp (contMDiff_inl 0)
    have hf₁ : ContMDiff I J ∞ (fun x => F' (x, 1)) := hF'.comp (contMDiff_inl 1)
    obtain ⟨y, hy0, hy1⟩ := exists_common_isRegularValue (hE.trans hF.symm) hf₀ hf₁
    rw [deg_eq hE hF oM oN hf₀ hy0, deg_eq hE hF oM oN hf₁ hy1]
    exact degAt_eq_of_homotopy hE hF oM oN hF' hy0 hy1
  · have h : ∀ f : M → N, ¬ ∃ y, IsRegularValue I J f y := fun f ⟨y, _⟩ => hN ⟨y⟩
    simp only [deg, dif_neg (h _)]

/-- A point outside the range gives degree `0`. -/
theorem deg_eq_zero_of_notMem_range [CompactSpace M] [T2Space M] [SecondCountableTopology M]
    [T2Space N] [PreconnectedSpace N] (hE : finrank ℝ E = n) (hF : finrank ℝ F = n)
    (oM : Orient I M n) (oN : Orient J N n) {f : M → N} (hf : ContMDiff I J ∞ f) {y : N}
    (hy : y ∉ range f) : deg oM oN f = 0 := by
  have hreg : IsRegularValue I J f y := fun x hx => (hy ⟨x, hx⟩).elim
  rw [deg_eq hE hF oM oN hf hreg]
  exact degAt_of_notMem_range oM oN hy

/-- **A map of nonzero degree is surjective** (Milnor p. 28). -/
theorem surjective_of_deg_ne_zero [CompactSpace M] [T2Space M] [SecondCountableTopology M]
    [T2Space N] [PreconnectedSpace N] (hE : finrank ℝ E = n) (hF : finrank ℝ F = n)
    (oM : Orient I M n) (oN : Orient J N n) {f : M → N} (hf : ContMDiff I J ∞ f)
    (hdeg : deg oM oN f ≠ 0) : Surjective f := by
  intro y
  by_contra hy
  exact hdeg (deg_eq_zero_of_notMem_range hE hF oM oN hf hy)

/-- The identity has degree `1`. -/
theorem deg_id [CompactSpace N] [T2Space N] [SecondCountableTopology N] [PreconnectedSpace N]
    [Nonempty N] (hF : finrank ℝ F = n) (oN : Orient J N n) : deg oN oN (id : N → N) = 1 := by
  obtain ⟨y⟩ := ‹Nonempty N›
  have hy : IsRegularValue J J (id : N → N) y := fun x _ => by
    show Function.Surjective (mfd J J id x)
    rw [HasMFDerivAt.mfd_eq (hasMFDerivAt_id (I := J) x)]
    exact fun v => ⟨v, rfl⟩
  rw [deg_eq hF hF oN oN contMDiff_id hy]
  unfold degAt
  have : (id : N → N) ⁻¹' {y} = {y} := by ext; simp
  rw [this, finsum_mem_singleton, signAt_id]

end Milnor
