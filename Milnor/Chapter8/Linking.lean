import Milnor.Chapter8.OrientProd
import Milnor.Chapter8.OrientFrame

/-!
# Problem 13: the linking number

Milnor, *Topology from the Differentiable Viewpoint*, §8, Problem 13 (first two parts):

> Given disjoint manifolds `M, N ⊂ ℝᵏ⁺¹`, the linking map `λ : M × N → Sᵏ` is defined by
> `λ(x, y) = (x − y)/‖x − y‖`. If `M` and `N` are compact, oriented, and boundaryless, with total
> dimension `m + n = k`, then the degree of `λ` is called the linking number `l(M, N)`. Prove that
> `l(N, M) = (−1)^((m+1)(n+1)) l(M, N)`. If `M` bounds an oriented manifold `X` disjoint from `N`,
> prove that `l(M, N) = 0`.

We work with abstract compact oriented boundaryless manifolds `A` (dimension `a`) and `B`
(dimension `b`) and smooth maps `α : A → ℝᵏ⁺¹`, `β : B → ℝᵏ⁺¹` with disjoint images (Milnor's
`M, N` are the case of inclusions).

* `linkMap α β (x, y) = (α x − β y)/‖α x − β y‖` and `linkingNumber = deg linkMap`, for the product
  orientation of `A × B` and the orientation `sphOrStd k` of `Sᵏ` as the boundary of the disk.
* `linkingNumber_symm`: `l(β, α) = (−1)^((a+1)(b+1)) l(α, β)`, since
  `λ_{β,α} = antip ∘ λ_{α,β} ∘ swap` (the swap has sign `(−1)^(ab)`, the antipodal map
  `(−1)^(k+1)`).
* `linkingNumber_eq_zero_of_bounds`: if `A = ∂X` for `X = {g ≥ 0}` compact in an oriented
  `(a+1)`-manifold `W` (with the boundary orientation) and `ᾱ : W → ℝᵏ⁺¹` maps `X` into the
  complement of `β(B)`, then `l(ᾱ|A, β) = 0`.  Proof: the map `(w, y) ↦ (ᾱ w − β y)/‖ᾱ w − β y‖`
  is smooth near `X × B`, a compact region with boundary `A × B = {G = 0}` in `W × B`
  (`G (w, y) = g w`), so by Milnor's Lemma 1 of §5 (`degAt_level_eq_zero_of_opens`) its restriction
  to the boundary has degree `0`; the boundary orientation of `A × B` in `W × B` is the product of
  the boundary orientation of `A` and the orientation of `B` (`orSign_contractOr_prod`).
-/

open Set Filter Topology Function Module TopologicalSpace
open scoped ContDiff Manifold

noncomputable section

namespace Milnor

namespace Problems

open Sphere

local notation "𝔼" n:max => EuclideanSpace ℝ (Fin n)

/-! ### The linking map -/

section linkMap

variable {k : ℕ} {A B : Type*}

/-- **The linking map** `λ(x, y) = (α x − β y)/‖α x − β y‖`. -/
def linkMap (α : A → 𝔼 (k + 1)) (β : B → 𝔼 (k + 1)) (q : A × B) : Sph k :=
  nv0 (α q.1 - β q.2)

theorem linkMap_val {α : A → 𝔼 (k + 1)} {β : B → 𝔼 (k + 1)} {q : A × B} (h : α q.1 ≠ β q.2) :
    (linkMap α β q).1 = Sphere.normalize (α q.1 - β q.2) :=
  nv0_val (sub_ne_zero.2 h)

/-- `λ_{β,α} = antip ∘ λ_{α,β} ∘ swap`. -/
theorem linkMap_swap {α : A → 𝔼 (k + 1)} {β : B → 𝔼 (k + 1)} (hdisj : ∀ x y, α x ≠ β y)
    (p : B × A) : linkMap β α p = antip (linkMap α β p.swap) := by
  apply Subtype.ext
  show (linkMap β α p).1 = -(linkMap α β p.swap).1
  rw [linkMap_val (fun h => hdisj p.2 p.1 h.symm), linkMap_val (hdisj p.2 p.1)]
  simp only [Prod.fst_swap, Prod.snd_swap, Sphere.normalize]
  rw [← neg_sub (α p.2) (β p.1), norm_neg, smul_neg]

end linkMap

variable {a b k : ℕ}
  {A : Type*} [TopologicalSpace A] [ChartedSpace (𝔼 a) A] [IsManifold 𝓘(ℝ, 𝔼 a) ∞ A]
  {B : Type*} [TopologicalSpace B] [ChartedSpace (𝔼 b) B] [IsManifold 𝓘(ℝ, 𝔼 b) ∞ B]

theorem contMDiff_linkMap {α : A → 𝔼 (k + 1)} {β : B → 𝔼 (k + 1)}
    (hα : ContMDiff 𝓘(ℝ, 𝔼 a) 𝓘(ℝ, 𝔼 (k + 1)) ∞ α) (hβ : ContMDiff 𝓘(ℝ, 𝔼 b) 𝓘(ℝ, 𝔼 (k + 1)) ∞ β)
    (hdisj : ∀ x y, α x ≠ β y) :
    ContMDiff (𝓘(ℝ, 𝔼 a).prod 𝓘(ℝ, 𝔼 b)) 𝓘(ℝ, 𝔼 k) ∞ (linkMap α β) :=
  contMDiff_nv0_comp ((hα.comp contMDiff_fst).sub (hβ.comp contMDiff_snd))
    (fun q => sub_ne_zero.2 (hdisj q.1 q.2))

/-! ### The linking number -/

/-- **The linking number** `l(α, β) = deg λ`, with `A × B` oriented as a product and `Sᵏ` as
the boundary of the disk. -/
def linkingNumber (hk : a + b = k) (oA : Orient 𝓘(ℝ, 𝔼 a) A a) (oB : Orient 𝓘(ℝ, 𝔼 b) B b)
    (α : A → 𝔼 (k + 1)) (β : B → 𝔼 (k + 1)) : ℤ :=
  deg ((oA.prod finrank_euclideanSpace_fin finrank_euclideanSpace_fin oB).cast hk) (sphOrStd k)
    (linkMap α β)

/-! ### Symmetry -/

section cast

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

theorem orient_cast_cast {k k' k'' : ℕ} (h : k = k') (h' : k' = k'') (o : Orient I M k) :
    (o.cast h).cast h' = o.cast (h.trans h') := by
  subst h h'
  exact Orient.ext' fun x => by simp [finCongr_refl]

theorem orient_cast_self {k : ℕ} (h : k = k) (o : Orient I M k) : o.cast h = o :=
  Orient.ext' fun x => by simp [finCongr_refl]

end cast

/-- The swap `B × A → A × B` has sign `(-1)^(a b)` for the (transported) product orientations. -/
theorem signAt_swap_cast (hk : a + b = k) (hk' : b + a = k) (oA : Orient 𝓘(ℝ, 𝔼 a) A a)
    (oB : Orient 𝓘(ℝ, 𝔼 b) B b) (p : B × A) :
    signAt ((oB.prod finrank_euclideanSpace_fin finrank_euclideanSpace_fin oA).cast hk')
      ((oA.prod finrank_euclideanSpace_fin finrank_euclideanSpace_fin oB).cast hk) Prod.swap p =
      (-1) ^ (a * b) := by
  have h : (oA.prod finrank_euclideanSpace_fin finrank_euclideanSpace_fin oB).cast hk =
      ((oA.prod finrank_euclideanSpace_fin finrank_euclideanSpace_fin oB).cast
        (Nat.add_comm a b)).cast hk' := by
    rw [orient_cast_cast]
  rw [h, signAt_cast, signAt_swap, mul_comm]

/-- The antipodal map has sign `(-1)^(k+1)` for the standard orientation of the sphere. -/
theorem signAt_antip_std (hk0 : 0 < k) (q : Sph k) :
    signAt (sphOrStd k) (sphOrStd k) antip q = (-1) ^ (k + 1) := by
  rcases sphOrStd_eq_or_neg hk0 with h | h
  · rw [h, signAt_antip]
  · rw [h, signAt_neg_left hZ, signAt_neg_right hZ hZ, neg_neg, signAt_antip]

theorem bijective_antip : Bijective (antip (n := k)) :=
  Function.Involutive.bijective antip_antip

/-- **Symmetry of the degree of the linking map**, for any orientations of `A × B` and
`B × A` related by a swap of sign `(-1)^(a b)`. -/
theorem deg_linkMap_swap [CompactSpace A] [T2Space A] [SecondCountableTopology A]
    [CompactSpace B] [T2Space B] [SecondCountableTopology B] (hk : a + b = k) (hk0 : 0 < k)
    (oAB : Orient (𝓘(ℝ, 𝔼 a).prod 𝓘(ℝ, 𝔼 b)) (A × B) k)
    (oBA : Orient (𝓘(ℝ, 𝔼 b).prod 𝓘(ℝ, 𝔼 a)) (B × A) k)
    (hswap : ∀ p, signAt oBA oAB Prod.swap p = (-1) ^ (a * b)) {α : A → 𝔼 (k + 1)}
    {β : B → 𝔼 (k + 1)} (hα : ContMDiff 𝓘(ℝ, 𝔼 a) 𝓘(ℝ, 𝔼 (k + 1)) ∞ α)
    (hβ : ContMDiff 𝓘(ℝ, 𝔼 b) 𝓘(ℝ, 𝔼 (k + 1)) ∞ β) (hdisj : ∀ x y, α x ≠ β y) :
    deg oBA (sphOrStd k) (linkMap β α) =
      (-1) ^ ((a + 1) * (b + 1)) * deg oAB (sphOrStd k) (linkMap α β) := by
  have := preconnectedSpace hk0
  have hfin : finrank ℝ (𝔼 a × 𝔼 b) = k := by
    rw [Module.finrank_prod, finrank_euclideanSpace_fin, finrank_euclideanSpace_fin, hk]
  have hfin' : finrank ℝ (𝔼 b × 𝔼 a) = k := by
    rw [Module.finrank_prod, finrank_euclideanSpace_fin, finrank_euclideanSpace_fin, ← hk,
      Nat.add_comm]
  have hf := contMDiff_linkMap hα hβ hdisj
  have hf' := contMDiff_linkMap hβ hα (fun y x h => hdisj x y h.symm)
  have hfd : ∀ q, MDifferentiableAt (𝓘(ℝ, 𝔼 a).prod 𝓘(ℝ, 𝔼 b)) 𝓘(ℝ, 𝔼 k) (linkMap α β) q :=
    fun q => hf.mdifferentiableAt (by simp)
  have hantd : ∀ q : Sph k, MDifferentiableAt 𝓘(ℝ, 𝔼 k) 𝓘(ℝ, 𝔼 k) antip q :=
    fun q => contMDiff_antip.mdifferentiableAt (by simp)
  have hswapd : ∀ p : B × A, MDifferentiableAt (𝓘(ℝ, 𝔼 b).prod 𝓘(ℝ, 𝔼 a))
      (𝓘(ℝ, 𝔼 a).prod 𝓘(ℝ, 𝔼 b)) Prod.swap p :=
    fun p => ((hasMFDerivAt_snd p).prodMk (hasMFDerivAt_fst p)).mdifferentiableAt
  have hcd : ∀ q, MDifferentiableAt (𝓘(ℝ, 𝔼 a).prod 𝓘(ℝ, 𝔼 b)) 𝓘(ℝ, 𝔼 k)
      (fun q => antip (linkMap α β q)) q :=
    fun q => (contMDiff_antip.comp hf).mdifferentiableAt (by simp)
  have heq : linkMap β α = fun p => antip (linkMap α β p.swap) :=
    funext (linkMap_swap hdisj)
  -- a regular value `z` of `λ_{α,β}`; then `antip z` is a regular value of `λ_{β,α}`
  obtain ⟨z, hz⟩ := (dense_regularValues hf).nonempty
  have hz' : IsRegularValue (𝓘(ℝ, 𝔼 b).prod 𝓘(ℝ, 𝔼 a)) 𝓘(ℝ, 𝔼 k) (linkMap β α) (antip z) := by
    intro p hp
    have hpz : linkMap α β p.swap = z := by
      have h1 : antip (linkMap α β p.swap) = antip z := by rw [← linkMap_swap hdisj]; exact hp
      rw [← antip_antip (linkMap α β p.swap), h1, antip_antip]
    rw [← signAt_ne_zero_iff_isRegularPoint hfin' finrank_euclideanSpace_fin oBA (sphOrStd k), heq,
      signAt_comp' hfin' hfin oBA oAB (sphOrStd k) (hswapd p) (hcd _),
      signAt_comp' hfin finrank_euclideanSpace_fin oAB (sphOrStd k) (sphOrStd k) (hfd _) (hantd _),
      hswap, signAt_antip_std hk0]
    refine mul_ne_zero (mul_ne_zero (pow_ne_zero _ (by norm_num)) ?_) (pow_ne_zero _ (by norm_num))
    exact IsRegularPoint.signAt_ne_zero hfin finrank_euclideanSpace_fin oAB (sphOrStd k) (hz _ hpz)
  rw [deg_eq hfin' finrank_euclideanSpace_fin oBA (sphOrStd k) hf' hz',
    deg_eq hfin finrank_euclideanSpace_fin oAB (sphOrStd k) hf hz, heq,
    degAt_comp_bij' hfin' hfin oBA oAB (sphOrStd k) hcd Prod.swap_bijective hswapd
      (neg_one_pow_eq_or ℤ _) hswap,
    degAt_comp_bij_left hfin finrank_euclideanSpace_fin oAB (sphOrStd k) (sphOrStd k)
      bijective_antip hantd
      (neg_one_pow_eq_or ℤ _) (signAt_antip_std hk0) hfd rfl, ← mul_assoc, ← pow_add]
  have hexp : a * b + (k + 1) = (a + 1) * (b + 1) := by subst hk; ring
  rw [hexp]

/-- **Problem 13, symmetry**: `l(β, α) = (-1)^((a+1)(b+1)) l(α, β)`. -/
theorem linkingNumber_symm [CompactSpace A] [T2Space A] [SecondCountableTopology A]
    [CompactSpace B] [T2Space B] [SecondCountableTopology B] (hk : a + b = k) (hk' : b + a = k)
    (hk0 : 0 < k) {oA : Orient 𝓘(ℝ, 𝔼 a) A a} {oB : Orient 𝓘(ℝ, 𝔼 b) B b} {α : A → 𝔼 (k + 1)}
    {β : B → 𝔼 (k + 1)} (hα : ContMDiff 𝓘(ℝ, 𝔼 a) 𝓘(ℝ, 𝔼 (k + 1)) ∞ α)
    (hβ : ContMDiff 𝓘(ℝ, 𝔼 b) 𝓘(ℝ, 𝔼 (k + 1)) ∞ β) (hdisj : ∀ x y, α x ≠ β y) :
    linkingNumber hk' oB oA β α = (-1) ^ ((a + 1) * (b + 1)) * linkingNumber hk oA oB α β :=
  deg_linkMap_swap hk hk0 _ _ (signAt_swap_cast hk hk' oA oB) hα hβ hdisj

/-! ### Bounding -/

section linear

section sign

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {d : ℕ}

omit [FiniteDimensional ℝ E] in
theorem orEpsB_mul_self (e : Basis (Fin d) ℝ E) (o : Orientation ℝ E (Fin d)) :
    orEpsB e o * orEpsB e o = 1 := by
  unfold orEpsB; split_ifs <;> norm_num

/-- A representative `vol` of an orientation `o` has the sign `orEpsB e o` on every basis `e`. -/
theorem mul_orEpsB_pos {vol : E [⋀^Fin d]→ₗ[ℝ] ℝ} (hvol : vol ≠ 0) {o : Orientation ℝ E (Fin d)}
    (ho : rayOfNeZero ℝ vol hvol = o) (e : Basis (Fin d) ℝ E) : 0 < vol e * orEpsB e o := by
  have h1 : SameRay ℝ (orEpsB e o • e.det) vol :=
    (ray_eq_iff (orEpsB_smul_det_ne_zero e o) hvol).1 (by rw [rayOfNeZero_orEpsB_det, ho])
  obtain ⟨r, hr, hrv⟩ := h1.exists_pos_left (orEpsB_smul_det_ne_zero e o) hvol
  rw [← hrv]
  simp only [AlternatingMap.smul_apply, smul_eq_mul, Basis.det_self, mul_one]
  rw [mul_assoc, orEpsB_mul_self, mul_one]
  exact hr

end sign

variable {E₁ : Type*} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [FiniteDimensional ℝ E₁]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {Z₁ : Type*} [NormedAddCommGroup Z₁] [NormedSpace ℝ Z₁] [FiniteDimensional ℝ Z₁]
  {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z] {m n : ℕ}

/-- **The boundary orientation of a product.**  Let `T : Z₁ → E₁` be injective with range in the
hyperplane `l = 0`, `l ν < 0`, and let `S : Z → E₁ × F` have range `{v | l v.1 = 0}`, with
`l νP.1 < 0`.  If `S ∘ D = T × id`, then `D` carries the product of the contracted orientation
`contractOr oE ν T` and `oF` to the contraction of the product orientation `oE × oF` by `νP`. -/
theorem orSign_contractOr_prod (hE₁ : finrank ℝ E₁ = m + 1) (hF : finrank ℝ F = n)
    (hZ₁ : finrank ℝ Z₁ = m) (hZ : finrank ℝ Z = m + n) (h1 : m + 1 + n = m + n + 1)
    (oE : Orientation ℝ E₁ (Fin (m + 1))) (oF : Orientation ℝ F (Fin n))
    {ν : E₁} {T : Z₁ →L[ℝ] E₁} {l : E₁ →L[ℝ] ℝ} (hTinj : Injective T) (hlT : ∀ z, l (T z) = 0)
    (hlν : l ν < 0) {νP : E₁ × F} {S : Z →L[ℝ] E₁ × F}
    (hS : ∀ v, (∃ z, S z = v) ↔ l v.1 = 0) (hlνP : l νP.1 < 0) {D : Z₁ × F →L[ℝ] Z}
    (hSD : S.comp D = T.prodMap (ContinuousLinearMap.id ℝ F)) :
    orSign (orProdGen hZ₁ hF (contractOr hZ₁ oE ν T) oF)
      (contractOr hZ (Orientation.reindex ℝ (E₁ × F) (finCongr h1) (orProdGen hE₁ hF oE oF)) νP S)
      D = 1 := by
  set e₁ := finBasisOfFinrankEq ℝ E₁ hE₁ with he₁
  set u := finBasisOfFinrankEq ℝ Z₁ hZ₁ with hu
  set f := finBasisOfFinrankEq ℝ F hF with hf
  -- the contracted orientation of `Z₁`
  have hωE : orEpsB e₁ oE • e₁.det ≠ 0 := orEpsB_smul_det_ne_zero e₁ oE
  have hκ : contractForm (orEpsB e₁ oE • e₁.det) ν T u ≠ 0 :=
    contractForm_basis_ne_zero hE₁ hZ₁ hωE hTinj hlT hlν.ne u
  have hρ : contractForm (orEpsB e₁ oE • e₁.det) ν T ≠ 0 := fun h => hκ (by rw [h]; rfl)
  have hρray := rayOfNeZero_contractForm hZ₁ hωE (rayOfNeZero_orEpsB_det e₁ oE) ν T hρ
  -- the representative of the source orientation
  have hω := orProdForm_ne_zero u f (contractOr hZ₁ oE ν T) oF
  have hωray := rayOfNeZero_prodBasis hZ₁ hF (contractOr hZ₁ oE ν T) oF u f
  -- the representative of the product orientation of `E₁ × F`
  have hΩ' : ((orEpsB e₁ oE * orEpsB f oF) • (prodBasis e₁ f).det).domDomCongr (finCongr h1) ≠ 0 :=
    mt ((AlternatingMap.domDomCongr_eq_zero_iff _ _).1) (orProdForm_ne_zero e₁ f oE oF)
  have hΩray : rayOfNeZero ℝ _ hΩ' =
      Orientation.reindex ℝ (E₁ × F) (finCongr h1) (orProdGen hE₁ hF oE oF) := by
    rw [← rayOfNeZero_prodBasis hE₁ hF oE oF e₁ f, Orientation.reindex_apply]
  -- `νP = c • (ν, 0) + S t` with `c > 0`
  obtain ⟨t, ht⟩ := (hS (νP - (l νP.1 / l ν) • (ν, (0 : F)))).2 (by
    simp [div_mul_cancel₀ _ hlν.ne])
  have hdecomp : νP = (l νP.1 / l ν) • (ν, (0 : F)) + S t := by rw [ht]; abel
  have hc : 0 < l νP.1 / l ν := div_pos_of_neg_of_neg hlνP hlν
  -- the value of the pulled back target form on the product basis
  have hval : (contractForm (((orEpsB e₁ oE * orEpsB f oF) • (prodBasis e₁ f).det).domDomCongr
      (finCongr h1)) νP S).compLinearMap D.toLinearMap (prodBasis u f) =
      (l νP.1 / l ν) * (orEpsB f oF * contractForm (orEpsB e₁ oE • e₁.det) ν T u) := by
    rw [contractForm_eq_smul hZ _ hdecomp, smul_compLinearMap, contractForm_comp, hSD]
    simp only [AlternatingMap.smul_apply, smul_eq_mul, contractForm_apply,
      AlternatingMap.domDomCongr_apply]
    congr 1
    rw [prodBasis_det_apply e₁ f _ (Matrix.vecCons ν fun i => T (u i)) f 0 ?_ ?_, Basis.det_self]
    · ring
    · intro j
      refine Fin.cases ?_ (fun j => ?_) j
      · have h0 : finCongr h1 (Fin.castAdd n (0 : Fin (m + 1))) = 0 := Fin.ext (by simp)
        simp [h0]
      · have hs : finCongr h1 (Fin.castAdd n j.succ) = (Fin.castAdd n j).succ := Fin.ext (by simp)
        simp [hs, prodBasis_castAdd]
    · intro j
      have hs : finCongr h1 (Fin.natAdd (m + 1) j) = (Fin.natAdd m j).succ :=
        Fin.ext (by simp; omega)
      simp [hs, prodBasis_natAdd]
  have hne : (contractForm (((orEpsB e₁ oE * orEpsB f oF) • (prodBasis e₁ f).det).domDomCongr
      (finCongr h1)) νP S).compLinearMap D.toLinearMap (prodBasis u f) ≠ 0 := by
    rw [hval]; exact mul_ne_zero hc.ne' (mul_ne_zero (orEpsB_ne_zero f oF) hκ)
  have hη : contractForm (((orEpsB e₁ oE * orEpsB f oF) • (prodBasis e₁ f).det).domDomCongr
      (finCongr h1)) νP S ≠ 0 := fun h => hne (by rw [h]; rfl)
  have hηray := rayOfNeZero_contractForm hZ hΩ' hΩray νP S hη
  have hv : ((orEpsB u (contractOr hZ₁ oE ν T) * orEpsB f oF) • (prodBasis u f).det)
      (prodBasis u f) ≠ 0 := by
    rw [smul_det_apply_self]
    exact mul_ne_zero (orEpsB_ne_zero _ _) (orEpsB_ne_zero f oF)
  rw [orSign_eq_sgn_mul (finrank_prod_eq hZ₁ hF) hω hη hωray hηray D hv, hval, smul_det_apply_self]
  apply sgn_pos
  have hpos := mul_orEpsB_pos hρ hρray u
  have : l νP.1 / l ν * (orEpsB f oF * contractForm (orEpsB e₁ oE • e₁.det) ν T u) *
      (orEpsB u (contractOr hZ₁ oE ν T) * orEpsB f oF) = (l νP.1 / l ν) *
      (orEpsB f oF * orEpsB f oF) *
      (contractForm (orEpsB e₁ oE • e₁.det) ν T u * orEpsB u (contractOr hZ₁ oE ν T)) := by ring
  rw [this, orEpsB_mul_self, mul_one]
  exact mul_pos hc hpos

end linear

section ofEqModel

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {n : ℕ}

/-- An orientation for a model `I` is one for any equal model `I'` (e.g. `𝓘(ℝ, E).prod 𝓘(ℝ, F)`
and `𝓘(ℝ, E × F)`). -/
def Orient.ofEqModel {I I' : ModelWithCorners ℝ E H} (h : I = I') (o : Orient I M n) :
    Orient I' M n where
  or := o.or
  cont := by subst h; exact o.cont

theorem Orient.ofEqModel_or {I I' : ModelWithCorners ℝ E H} (h : I = I') (o : Orient I M n)
    (x : M) : (Orient.ofEqModel h o).or x = o.or x := rfl

end ofEqModel

/-- **Problem 13, bounding** (ambient form of "`M` bounds an oriented manifold `X` disjoint from
`N`"): `W` is an oriented `(a+1)`-manifold without boundary, `X = {g ≥ 0}` is compact with
boundary `A = g⁻¹(0)` carrying the boundary orientation `levelOrientM`, and `ᾱ : W → ℝᵏ⁺¹` maps
`X` into the complement of `β(B)`.  Then `l(ᾱ|A, β) = 0`. -/
theorem linkingNumber_eq_zero_of_bounds [CompactSpace B] [T2Space B] [SecondCountableTopology B]
    {W : Type*} [TopologicalSpace W] [ChartedSpace (𝔼 (a + 1)) W]
    [IsManifold 𝓘(ℝ, 𝔼 (a + 1)) ∞ W] [T2Space W] [SecondCountableTopology W]
    (oW : Orient 𝓘(ℝ, 𝔼 (a + 1)) W (a + 1)) {g : W → ℝ}
    (hg : ContMDiff 𝓘(ℝ, 𝔼 (a + 1)) 𝓘(ℝ, ℝ) ∞ g)
    (h0 : IsRegularValue 𝓘(ℝ, 𝔼 (a + 1)) 𝓘(ℝ, ℝ) g 0) (hX : IsCompact {w | 0 ≤ g w})
    {ᾱ : W → 𝔼 (k + 1)} (hᾱ : ContMDiff 𝓘(ℝ, 𝔼 (a + 1)) 𝓘(ℝ, 𝔼 (k + 1)) ∞ ᾱ)
    {oB : Orient 𝓘(ℝ, 𝔼 b) B b} {β : B → 𝔼 (k + 1)}
    (hβ : ContMDiff 𝓘(ℝ, 𝔼 b) 𝓘(ℝ, 𝔼 (k + 1)) ∞ β) (hdisj : ∀ w, 0 ≤ g w → ∀ y, ᾱ w ≠ β y)
    (hk : a + b = k) (hk0 : 0 < k) :
    letI := (isSliceSubmanifold_preimage (Z := 𝔼 a)
      (finrank_Z_add finrank_euclideanSpace_fin finrank_euclideanSpace_fin) hg h0).chartedSpace
    haveI := (isSliceSubmanifold_preimage (Z := 𝔼 a)
      (finrank_Z_add finrank_euclideanSpace_fin finrank_euclideanSpace_fin) hg h0).isManifold
    linkingNumber hk (levelOrientM finrank_euclideanSpace_fin finrank_euclideanSpace_fin oW hg h0)
      oB (fun q : g ⁻¹' {0} => ᾱ q.1) β = 0 := by
  subst hk
  -- the boundary `A = g⁻¹(0)`
  have hSA := isSliceSubmanifold_preimage (Z := 𝔼 a)
    (finrank_Z_add finrank_euclideanSpace_fin finrank_euclideanSpace_fin) hg h0
  let := hSA.chartedSpace
  have := hSA.isManifold
  have hEa : finrank ℝ (𝔼 (a + 1)) = a + 1 := finrank_euclideanSpace_fin
  have hZa : finrank ℝ (𝔼 a) = a := finrank_euclideanSpace_fin
  have hFb : finrank ℝ (𝔼 b) = b := finrank_euclideanSpace_fin
  have hEP : finrank ℝ (𝔼 (a + 1) × 𝔼 b) = a + b + 1 := by
    rw [Module.finrank_prod, hEa, hFb]; ring
  have hZP : finrank ℝ (𝔼 a × 𝔼 b) = a + b := finrank_prod_eq hZa hFb
  have hSk : finrank ℝ (𝔼 (a + b)) = a + b := finrank_euclideanSpace_fin
  have h1 : a + 1 + b = a + b + 1 := by ring
  have : CompactSpace (g ⁻¹' {0}) := isCompact_iff_compactSpace.1
    (hX.of_isClosed_subset (isClosed_singleton.preimage hg.continuous)
      (fun x hx => le_of_eq (mem_singleton_iff.1 hx).symm))
  have := preconnectedSpace hk0
  -- the product `P = W × B`, modelled on the vector space `ℝᵃ⁺¹ × ℝᵇ`
  let : ChartedSpace (𝔼 (a + 1) × 𝔼 b) (W × B) := prodChartedSpace _ _ _ _
  have : IsManifold 𝓘(ℝ, 𝔼 (a + 1) × 𝔼 b) ∞ (W × B) := by
    rw [modelWithCornersSelf_prod]; exact IsManifold.prod W B
  obtain ⟨oP, hoP⟩ : ∃ oP : Orient 𝓘(ℝ, 𝔼 (a + 1) × 𝔼 b) (W × B) (a + b + 1), ∀ p : W × B,
      oP.or p = Orientation.reindex ℝ (𝔼 (a + 1) × 𝔼 b) (finCongr h1)
        (orProdGen hEa hFb (oW.or p.1) (oB.or p.2)) :=
    ⟨Orient.ofEqModel modelWithCornersSelf_prod.symm ((oW.prod hEa hFb oB).cast h1),
      fun p => rfl⟩
  -- the boundary function `G = g ∘ fst` of `X × B`
  have hGs : ContMDiff 𝓘(ℝ, 𝔼 (a + 1) × 𝔼 b) 𝓘(ℝ, ℝ) ∞ (g ∘ Prod.fst : W × B → ℝ) := by
    rw [modelWithCornersSelf_prod]; exact hg.comp contMDiff_fst
  have hGd : ∀ p : W × B, mfd 𝓘(ℝ, 𝔼 (a + 1) × 𝔼 b) 𝓘(ℝ, ℝ) (g ∘ Prod.fst) p =
      (mfd 𝓘(ℝ, 𝔼 (a + 1)) 𝓘(ℝ, ℝ) g p.1).comp
        (ContinuousLinearMap.fst ℝ (𝔼 (a + 1)) (𝔼 b)) := by
    intro p
    apply HasMFDerivAt.mfd_eq
    have h := (hasMFDerivAt_mfd (hg.mdifferentiableAt (by simp) :
      MDifferentiableAt 𝓘(ℝ, 𝔼 (a + 1)) 𝓘(ℝ, ℝ) g p.1)).comp p
      (hasMFDerivAt_fst (I := 𝓘(ℝ, 𝔼 (a + 1))) (I' := 𝓘(ℝ, 𝔼 b)) p)
    rw [modelWithCornersSelf_prod]
    exact h
  have hGd' : ∀ (p : W × B) (v : 𝔼 (a + 1) × 𝔼 b),
      mfd 𝓘(ℝ, 𝔼 (a + 1) × 𝔼 b) 𝓘(ℝ, ℝ) (g ∘ Prod.fst) p v =
        mfd 𝓘(ℝ, 𝔼 (a + 1)) 𝓘(ℝ, ℝ) g p.1 v.1 :=
    fun p v => DFunLike.congr_fun (hGd p) v
  have hGr : IsRegularValue 𝓘(ℝ, 𝔼 (a + 1) × 𝔼 b) 𝓘(ℝ, ℝ) (g ∘ Prod.fst : W × B → ℝ) 0 := by
    intro p hp
    have hs : Surjective (mfd 𝓘(ℝ, 𝔼 (a + 1)) 𝓘(ℝ, ℝ) g p.1) := h0 p.1 hp
    show Surjective (mfd 𝓘(ℝ, 𝔼 (a + 1) × 𝔼 b) 𝓘(ℝ, ℝ) (g ∘ Prod.fst) p)
    intro t
    obtain ⟨v, hv⟩ := hs t
    exact ⟨(v, 0), (hGd' p (v, 0)).trans hv⟩
  -- the boundary `A × B = G⁻¹(0)` of `X × B`
  have hSL := isSliceSubmanifold_preimage (Z := 𝔼 a × 𝔼 b) (finrank_Z_add hEP hZP) hGs hGr
  let := hSL.chartedSpace
  have := hSL.isManifold
  obtain ⟨φ, hφ⟩ : ∃ φ : g ⁻¹' {0} × B → (g ∘ Prod.fst : W × B → ℝ) ⁻¹' {0},
      ∀ p, (φ p).1 = (p.1.1, p.2) := ⟨fun p => ⟨(p.1.1, p.2), p.1.2⟩, fun p => rfl⟩
  have hφ1 : ∀ p, (φ p).1.1 = p.1.1 := fun p => by rw [hφ]
  have hφ2 : ∀ p, (φ p).1.2 = p.2 := fun p => by rw [hφ]
  have hφs : ContMDiff (𝓘(ℝ, 𝔼 a).prod 𝓘(ℝ, 𝔼 b)) 𝓘(ℝ, 𝔼 a × 𝔼 b) ∞ φ := by
    have hφeq : φ = fun p => ⟨(p.1.1, p.2), p.1.2⟩ := funext fun p => Subtype.ext (hφ p)
    rw [hφeq]
    refine hSL.contMDiff_codRestrict (F := fun p : g ⁻¹' {0} × B => ((p.1 : W), p.2)) ?_
      (fun p => p.1.2)
    rw [modelWithCornersSelf_prod]
    exact (hSA.contMDiff_val.comp contMDiff_fst).prodMk contMDiff_snd
  have hφb : Bijective φ := by
    constructor
    · intro p p' h
      have h' := congrArg Subtype.val h
      rw [hφ, hφ] at h'
      obtain ⟨hp1, hp2⟩ := Prod.mk.inj h'
      exact Prod.ext (Subtype.ext hp1) hp2
    · intro q
      exact ⟨(⟨q.1.1, q.2⟩, q.1.2), Subtype.ext (hφ _)⟩
  -- the chain rule `dι_{A×B} ∘ dφ = dι_A × id`
  have hφD : ∀ p : g ⁻¹' {0} × B,
      (mfd 𝓘(ℝ, 𝔼 a × 𝔼 b) 𝓘(ℝ, 𝔼 (a + 1) × 𝔼 b)
        (Subtype.val : (g ∘ Prod.fst : W × B → ℝ) ⁻¹' {0} → W × B) (φ p)).comp
        (mfd (𝓘(ℝ, 𝔼 a).prod 𝓘(ℝ, 𝔼 b)) 𝓘(ℝ, 𝔼 a × 𝔼 b) φ p) =
      (mfd 𝓘(ℝ, 𝔼 a) 𝓘(ℝ, 𝔼 (a + 1)) (Subtype.val : g ⁻¹' {0} → W) p.1).prodMap
        (ContinuousLinearMap.id ℝ (𝔼 b)) := by
    intro p
    have h1 := (hasMFDerivAt_mfd (hSL.contMDiff_val.mdifferentiableAt (by simp) :
      MDifferentiableAt 𝓘(ℝ, 𝔼 a × 𝔼 b) 𝓘(ℝ, 𝔼 (a + 1) × 𝔼 b)
        (Subtype.val : (g ∘ Prod.fst : W × B → ℝ) ⁻¹' {0} → W × B) (φ p))).comp p
      (hasMFDerivAt_mfd (hφs.mdifferentiableAt (by simp)))
    have h2 : HasMFDerivAt (𝓘(ℝ, 𝔼 a).prod 𝓘(ℝ, 𝔼 b)) 𝓘(ℝ, 𝔼 (a + 1) × 𝔼 b)
        (Prod.map (Subtype.val : g ⁻¹' {0} → W) (id : B → B)) p
        ((mfd 𝓘(ℝ, 𝔼 a) 𝓘(ℝ, 𝔼 (a + 1)) (Subtype.val : g ⁻¹' {0} → W) p.1).prodMap
          (ContinuousLinearMap.id ℝ (𝔼 b))) := by
      have h := (hasMFDerivAt_mfd (hSA.contMDiff_val.mdifferentiableAt (by simp) :
        MDifferentiableAt 𝓘(ℝ, 𝔼 a) 𝓘(ℝ, 𝔼 (a + 1)) (Subtype.val : g ⁻¹' {0} → W) p.1)).prodMap
        (hasMFDerivAt_id (I := 𝓘(ℝ, 𝔼 b)) p.2)
      rw [mfderiv_id] at h
      rw [modelWithCornersSelf_prod]
      exact h
    have h3 : (Subtype.val ∘ φ) = Prod.map (Subtype.val : g ⁻¹' {0} → W) (id : B → B) :=
      funext fun p => hφ p
    rw [h3] at h1
    exact hasMFDerivAt_unique h1 h2
  -- `φ` preserves orientation: the boundary orientation of `A × B` is the product one
  have hφsign : ∀ p, signAt ((levelOrientM hEa hZa oW hg h0).prod hZa hFb oB)
      (levelOrientM hEP hZP oP hGs hGr) φ p = 1 := by
    intro p
    have hS' : ∀ v : 𝔼 (a + 1) × 𝔼 b, (∃ z, mfd 𝓘(ℝ, 𝔼 a × 𝔼 b) 𝓘(ℝ, 𝔼 (a + 1) × 𝔼 b)
        (Subtype.val : (g ∘ Prod.fst : W × B → ℝ) ⁻¹' {0} → W × B) (φ p) z = v) ↔
        mfd 𝓘(ℝ, 𝔼 (a + 1)) 𝓘(ℝ, ℝ) g p.1.1 v.1 = 0 := fun v => by
      have h := mem_range_mfderiv_val_iff (finrank_Z_add hEP hZP) hGs hGr (φ p) v
      have h' : mfderiv 𝓘(ℝ, 𝔼 (a + 1) × 𝔼 b) 𝓘(ℝ, ℝ) (g ∘ Prod.fst) (φ p).1 v =
          mfd 𝓘(ℝ, 𝔼 (a + 1)) 𝓘(ℝ, ℝ) g p.1.1 v.1 := by
        rw [← hφ1 p]; exact hGd' _ v
      rw [h'] at h
      exact h
    have hlνP : mfd 𝓘(ℝ, 𝔼 (a + 1)) 𝓘(ℝ, ℝ) g p.1.1
        (outwardM hEP (g ∘ Prod.fst) (φ p).1).1 < 0 := by
      have h := mfd_outwardM_neg hEP (mfd_ne_zero_of_level hEP hZP hGs hGr (φ p))
      rw [hGd', hφ1] at h
      exact h
    have key : orSign (orProdGen hZa hFb (contractOr hZa (oW.or p.1.1) (outwardM hEa g p.1.1)
        (mfd 𝓘(ℝ, 𝔼 a) 𝓘(ℝ, 𝔼 (a + 1)) (Subtype.val : g ⁻¹' {0} → W) p.1)) (oB.or p.2))
        (contractOr hZP (oP.or (φ p).1) (outwardM hEP (g ∘ Prod.fst) (φ p).1)
          (mfd 𝓘(ℝ, 𝔼 a × 𝔼 b) 𝓘(ℝ, 𝔼 (a + 1) × 𝔼 b)
            (Subtype.val : (g ∘ Prod.fst : W × B → ℝ) ⁻¹' {0} → W × B) (φ p)))
        (mfd (𝓘(ℝ, 𝔼 a).prod 𝓘(ℝ, 𝔼 b)) 𝓘(ℝ, 𝔼 a × 𝔼 b) φ p) = 1 := by
      rw [hoP, hφ1, hφ2]
      exact orSign_contractOr_prod hEa hFb hZa hZP h1 (oW.or p.1.1) (oB.or p.2)
        (injective_mfderiv_val hSA p.1) (mfd_level_comp_val hEa hZa hg h0 p.1)
        (mfd_outwardM_neg hEa (mfd_ne_zero_of_level hEa hZa hg h0 p.1)) hS' hlνP (hφD p)
    exact key
  -- the map `λ(w, y) = (ᾱ w - β y)/‖ᾱ w - β y‖`, smooth on the open set `U = {ᾱ w ≠ β y}`
  obtain ⟨U, hU⟩ : ∃ U : Opens (W × B), (U : Set (W × B)) = {p | ᾱ p.1 ≠ β p.2} :=
    ⟨⟨_, isOpen_ne_fun (hᾱ.continuous.comp continuous_fst) (hβ.continuous.comp continuous_snd)⟩,
      rfl⟩
  have hmemU : ∀ p : W × B, p ∈ U ↔ ᾱ p.1 ≠ β p.2 := fun p => by
    rw [← SetLike.mem_coe, hU]; rfl
  have hwsm : ContMDiff 𝓘(ℝ, 𝔼 (a + 1) × 𝔼 b) 𝓘(ℝ, 𝔼 (a + b + 1)) ∞
      (fun p : W × B => ᾱ p.1 - β p.2) := by
    rw [modelWithCornersSelf_prod]; exact (hᾱ.comp contMDiff_fst).sub (hβ.comp contMDiff_snd)
  have hfU' : ContMDiff 𝓘(ℝ, 𝔼 (a + 1) × 𝔼 b) 𝓘(ℝ, 𝔼 (a + b)) ∞
      (fun x : U => linkMap ᾱ β x.1) :=
    contMDiff_nv0_comp (hwsm.comp contMDiff_subtype_val) (fun x => sub_ne_zero.2 ((hmemU _).1 x.2))
  have hfOn : ContMDiffOn 𝓘(ℝ, 𝔼 (a + 1) × 𝔼 b) 𝓘(ℝ, 𝔼 (a + b)) ∞ (linkMap ᾱ β) U :=
    fun x hx => ((contMDiffAt_subtype_iff (I := 𝓘(ℝ, 𝔼 (a + 1) × 𝔼 b))
      (I' := 𝓘(ℝ, 𝔼 (a + b))) (n := ∞) (U := U) (f := linkMap ᾱ β) (x := ⟨x, hx⟩)).1
        (hfU' ⟨x, hx⟩)).contMDiffWithinAt
  have hgU : ∀ x : W × B, (g ∘ Prod.fst) x = 0 → x ∈ U := fun x hx =>
    (hmemU x).2 (hdisj x.1 (le_of_eq hx.symm) x.2)
  have hfL : ContMDiff 𝓘(ℝ, 𝔼 a × 𝔼 b) 𝓘(ℝ, 𝔼 (a + b)) ∞
      (linkMap ᾱ β ∘ (Subtype.val : (g ∘ Prod.fst : W × B → ℝ) ⁻¹' {0} → W × B)) :=
    contMDiff_nv0_comp (hwsm.comp hSL.contMDiff_val) (fun q => sub_ne_zero.2
      (hdisj q.1.1 (ge_of_eq (show g q.1.1 = 0 from q.2)) q.1.2))
  -- the linking map of `A × B`
  have hlink : ContMDiff (𝓘(ℝ, 𝔼 a).prod 𝓘(ℝ, 𝔼 b)) 𝓘(ℝ, 𝔼 (a + b)) ∞
      (linkMap (fun q : g ⁻¹' {0} => ᾱ q.1) β) :=
    contMDiff_linkMap (hᾱ.comp hSA.contMDiff_val) hβ
      (fun q y => hdisj q.1 (ge_of_eq (show g q.1 = 0 from q.2)) y)
  have hlinkeq : linkMap (fun q : g ⁻¹' {0} => ᾱ q.1) β =
      fun x => (linkMap ᾱ β ∘ Subtype.val) (φ x) := by
    funext x
    show nv0 _ = nv0 _
    rw [hφ1, hφ2]
  -- a common regular value `e` of `λ|U` and of `λ|A×B`
  have hAB := dense_isOpen_regularValues hZP hSk ((levelOrientM hEa hZa oW hg h0).prod hZa hFb oB)
    (sphOrStd (a + b)) hlink
  obtain ⟨e, heU, het⟩ := exists_mem_of_dense_of_isOpen (dense_regularValues hfU')
    (t := fun _ : Unit => regularValues (𝓘(ℝ, 𝔼 a).prod 𝓘(ℝ, 𝔼 b)) 𝓘(ℝ, 𝔼 (a + b))
      (linkMap (fun q : g ⁻¹' {0} => ᾱ q.1) β)) (fun _ => hAB.1) (fun _ => hAB.2)
  have he1 : IsRegularValue 𝓘(ℝ, 𝔼 (a + 1) × 𝔼 b) 𝓘(ℝ, 𝔼 (a + b))
      (linkMap ᾱ β ∘ (Subtype.val : U → W × B)) e := heU
  have he2 : IsRegularValue (𝓘(ℝ, 𝔼 a).prod 𝓘(ℝ, 𝔼 b)) 𝓘(ℝ, 𝔼 (a + b))
      (linkMap (fun q : g ⁻¹' {0} => ᾱ q.1) β) e := het ()
  -- transversality of `λ⁻¹(e)` to the boundary
  have hreg : ∀ x : W × B, linkMap ᾱ β x = e → (g ∘ Prod.fst) x = 0 →
      ∃ w, mfd 𝓘(ℝ, 𝔼 (a + 1) × 𝔼 b) 𝓘(ℝ, 𝔼 (a + b)) (linkMap ᾱ β) x w = 0 ∧
        mfd 𝓘(ℝ, 𝔼 (a + 1) × 𝔼 b) 𝓘(ℝ, ℝ) (g ∘ Prod.fst) x w ≠ 0 := by
    intro x hfx hGx
    have hxU : x ∈ U := hgU x hGx
    have hd : MDifferentiableAt 𝓘(ℝ, 𝔼 (a + 1) × 𝔼 b) 𝓘(ℝ, 𝔼 (a + b)) (linkMap ᾱ β) x :=
      (hfOn.contMDiffAt (U.isOpen.mem_nhds hxU)).mdifferentiableAt (by simp)
    have hreg1 : IsRegularPoint 𝓘(ℝ, 𝔼 (a + 1) × 𝔼 b) 𝓘(ℝ, 𝔼 (a + b)) (linkMap ᾱ β) x := by
      have h1' := he1 ⟨x, hxU⟩ hfx
      show Surjective (mfd 𝓘(ℝ, 𝔼 (a + 1) × 𝔼 b) 𝓘(ℝ, 𝔼 (a + b)) (linkMap ᾱ β) x)
      rw [← mfd_comp_subtype_val U (y := ⟨x, hxU⟩) hd]
      exact h1'
    have hq : IsRegularPoint 𝓘(ℝ, 𝔼 a × 𝔼 b) 𝓘(ℝ, 𝔼 (a + b)) (linkMap ᾱ β ∘ Subtype.val)
        (⟨x, hGx⟩ : (g ∘ Prod.fst : W × B → ℝ) ⁻¹' {0}) := by
      obtain ⟨p, hp⟩ := hφb.2 ⟨x, hGx⟩
      have hpe : linkMap (fun q : g ⁻¹' {0} => ᾱ q.1) β p = e := by
        rw [hlinkeq]
        show linkMap ᾱ β (φ p).1 = e
        rw [hp]
        exact hfx
      have hsurj : Surjective (mfd (𝓘(ℝ, 𝔼 a).prod 𝓘(ℝ, 𝔼 b)) 𝓘(ℝ, 𝔼 (a + b))
          (linkMap (fun q : g ⁻¹' {0} => ᾱ q.1) β) p) := he2 p hpe
      have hchain := HasMFDerivAt.mfd_eq ((hasMFDerivAt_mfd (hfL.mdifferentiableAt (by simp) :
        MDifferentiableAt 𝓘(ℝ, 𝔼 a × 𝔼 b) 𝓘(ℝ, 𝔼 (a + b)) (linkMap ᾱ β ∘ Subtype.val)
          (φ p))).comp p (hasMFDerivAt_mfd (hφs.mdifferentiableAt (by simp))))
      have hcomp : (linkMap ᾱ β ∘ Subtype.val) ∘ φ = linkMap (fun q : g ⁻¹' {0} => ᾱ q.1) β :=
        hlinkeq.symm
      rw [hcomp] at hchain
      rw [hchain] at hsurj
      rw [← hp]
      show Surjective (mfd 𝓘(ℝ, 𝔼 a × 𝔼 b) 𝓘(ℝ, 𝔼 (a + b)) (linkMap ᾱ β ∘ Subtype.val) (φ p))
      intro v
      obtain ⟨w, hw⟩ := hsurj v
      exact ⟨_, hw⟩
    exact exists_mfd_eq_zero_of_isRegularPoint_level hEP hZP hSk hGs hGr ⟨x, hGx⟩ hd hreg1 hq
  -- compactness of `λ⁻¹(e) ∩ (X × B)` inside `U`
  have hXc : IsCompact {x : U | linkMap ᾱ β x.1 = e ∧ 0 ≤ (g ∘ Prod.fst) x.1} := by
    rw [Subtype.isCompact_iff]
    have hKc : IsCompact ({w | 0 ≤ g w} ×ˢ (univ : Set B)) := hX.prod isCompact_univ
    have hKU : {w | 0 ≤ g w} ×ˢ (univ : Set B) ⊆ U := fun p hp => (hmemU p).2 (hdisj p.1 hp.1 p.2)
    have himg : Subtype.val '' {x : U | linkMap ᾱ β x.1 = e ∧ 0 ≤ (g ∘ Prod.fst) x.1} =
        ({w | 0 ≤ g w} ×ˢ (univ : Set B)) ∩ linkMap ᾱ β ⁻¹' {e} := by
      ext p
      constructor
      · rintro ⟨⟨p, hpU⟩, ⟨hp1, hp2⟩, rfl⟩
        exact ⟨⟨hp2, mem_univ _⟩, hp1⟩
      · rintro ⟨⟨hp1, -⟩, hp2⟩
        exact ⟨⟨p, hKU ⟨hp1, mem_univ _⟩⟩, ⟨hp2, hp1⟩, rfl⟩
    rw [himg]
    exact hKc.of_isClosed_subset (ContinuousOn.preimage_isClosed_of_isClosed
      (hfOn.continuousOn.mono hKU) hKc.isClosed isClosed_singleton) inter_subset_left
  -- Lemma 1: the degree of `λ` on the boundary `G⁻¹(0)` vanishes
  obtain ⟨-, hdeg0⟩ := degAt_level_eq_zero_of_opens hEP hZP hSk hGs hGr oP (sphOrStd (a + b))
    hfOn hgU he1 hreg hXc
  -- transfer to `A × B` along `φ`
  have htrans := degAt_comp_bij hZP hZP ((levelOrientM hEa hZa oW hg h0).prod hZa hFb oB)
    (levelOrientM hEP hZP oP hGs hGr) (sphOrStd (a + b))
    (fun q => hfL.mdifferentiableAt (by simp)) hφb (fun p => hφs.mdifferentiableAt (by simp))
    hφsign e
  rw [linkingNumber, orient_cast_self, deg_eq hZP hSk _ (sphOrStd (a + b)) hlink he2, hlinkeq,
    htrans]
  exact hdeg0

end Problems

end Milnor
