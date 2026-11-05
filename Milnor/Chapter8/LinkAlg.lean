import Milnor.Chapter8.OrientProd
import Milnor.Chapter8.OrientFrame

/-!
# Linear algebra behind "linking numbers of preimages are local degrees"

Milnor, *Topology from the Differentiable Viewpoint*, §8, Problem 14 (linear-algebra part).

Setting: `D : V → F` is a linear map with `dim V = d + p`, `dim F = p`, and `ι : Z → V` is an
injective linear map from a `d`-dimensional space with `range ι = ker D` (the tangent space of a
preimage).  Let `u : Fin p → V` be vectors whose images `D u₀, …, D u_{p-1}` form a positive basis
of `F` (hypotheses `hu`, `huo`).  The preimage is oriented by the frame `u`:
`frameOr hZ oV u ι` (frame vectors first).

* `frameOr_basis_iff`: `(u, ι z)` is a positive basis of `V` iff `z` is positive for
  `frameOr hZ oV u ι`.
* `orSign_single_preimage`: the sign of `(x, w) ↦ (D x, L (x, w))` on `V × W` equals the sign of
  `L ∘ (ι × id)` on `Z × W`.
* `orSign_single_preimage_right`: the sign of `(w, x) ↦ (D x, L (w, x))` is `(-1)^(b p)` times the
  sign of `L ∘ (id × ι)` (`b = dim W`).
* `orSign_pair_preimage`: the sign of `(x, x') ↦ ((D x, D' x'), L (x, x'))` on `V × V` is
  `(-1)^(d p)` times the sign of `L ∘ (ι × ι')` on `Z × Z'`.

The single case is a block-triangular determinant computation in the bases
`(u, ι z, w)` of `V × W` and `(D u, g)` of `F × G`.  The mirror case follows by composing with
two swaps (`orSign_swap`), and the pair case from the single case (with `W = V`), the mirror case
(with `W = Z`) and the associativity of product orientations (`LinkAlg.orSign_prodAssoc`).

Auxiliary lemmas live in the namespace `Milnor.Problems.LinkAlg`.  To produce the hypothesis
`huo` from a positive basis `f` of `F` with `D (u i) = f i`, use
`LinkAlg.orientation_basisOfLinearIndependent'`.
-/

open Set Function Module

noncomputable section

namespace Milnor

namespace Problems

namespace LinkAlg

/-! ### Index bookkeeping -/

section tuple

variable {α : Type*} {d : ℕ}

/-- The first `k` entries of `frameTuple ν w` are the frame vectors. -/
theorem frameTuple_apply_left : ∀ {k : ℕ} (ν : Fin k → α) (w : Fin d → α) {i : Fin (d + k)}
    {j : Fin k}, (i : ℕ) = j → frameTuple ν w i = ν j
  | 0, _, _, _, j, _ => j.elim0
  | k + 1, ν, w, ⟨0, hi⟩, j, h => by
    obtain rfl : j = 0 := Fin.ext h.symm
    rfl
  | k + 1, ν, w, ⟨i + 1, hi⟩, j, h => by
    obtain ⟨j, rfl⟩ : ∃ j' : Fin k, j = j'.succ :=
      ⟨⟨(j : ℕ) - 1, by simp at h; omega⟩, Fin.ext (by simp at h ⊢; omega)⟩
    show Matrix.vecCons (ν 0) (frameTuple (Fin.tail ν) w) (Fin.succ ⟨i, by omega⟩) = ν j.succ
    rw [Matrix.cons_val_succ]
    exact frameTuple_apply_left (Fin.tail ν) w (by simp at h ⊢; omega)

/-- The entries of `frameTuple ν w` after the `k` frame vectors are the vectors `w`. -/
theorem frameTuple_apply_right : ∀ {k : ℕ} (ν : Fin k → α) (w : Fin d → α) {i : Fin (d + k)}
    {j : Fin d}, (i : ℕ) = k + j → frameTuple ν w i = w j
  | 0, ν, w, i, j, h => by
    rw [frameTuple_zero]
    exact congrArg w (Fin.ext (by simpa using h))
  | k + 1, _, _, ⟨0, hi⟩, j, h => by simp at h; omega
  | k + 1, ν, w, ⟨i + 1, hi⟩, j, h => by
    show Matrix.vecCons (ν 0) (frameTuple (Fin.tail ν) w) (Fin.succ ⟨i, by omega⟩) = w j
    rw [Matrix.cons_val_succ]
    exact frameTuple_apply_right (Fin.tail ν) w (by simp at h ⊢; omega)

end tuple

/-! ### Signs in arbitrary bases -/

section linear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {m n : ℕ}

theorem prodBasis_apply_left (e : Basis (Fin m) ℝ E) (f : Basis (Fin n) ℝ F) {i : Fin (m + n)}
    {j : Fin m} (h : (i : ℕ) = j) : prodBasis e f i = (e j, 0) := by
  obtain rfl : i = Fin.castAdd n j := Fin.ext h
  exact prodBasis_castAdd e f j

theorem prodBasis_apply_right (e : Basis (Fin m) ℝ E) (f : Basis (Fin n) ℝ F) {i : Fin (m + n)}
    {j : Fin n} (h : (i : ℕ) = m + j) : prodBasis e f i = (0, f j) := by
  obtain rfl : i = Fin.natAdd m j := Fin.ext h
  exact prodBasis_natAdd e f j

theorem orEpsB_eq_one_or (e : Basis (Fin m) ℝ E) (a : Orientation ℝ E (Fin m)) :
    orEpsB e a = 1 ∨ orEpsB e a = -1 := by
  unfold orEpsB; split_ifs <;> simp

theorem orEpsB_eq_neg_one' {e : Basis (Fin m) ℝ E} {a : Orientation ℝ E (Fin m)}
    (h : e.orientation ≠ a) : orEpsB e a = -1 := by
  unfold orEpsB; rw [if_neg h]

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

/-- The sign of a map computed in arbitrary bases `e` of the source and `f` of the target. -/
theorem orSign_eq_sgn_det (hE : finrank ℝ E = n) (a : Orientation ℝ E (Fin n))
    (b : Orientation ℝ F (Fin n)) (e : Basis (Fin n) ℝ E) (f : Basis (Fin n) ℝ F)
    (T : E →L[ℝ] F) :
    orSign a b T = sgn (orEpsB e a * orEpsB f b * f.det (fun i => T (e i))) := by
  have hv : (orEpsB e a • e.det) ⇑e ≠ 0 := by
    rw [orEpsB_apply_self]; exact orEpsB_ne_zero e a
  rw [orSign_eq_sgn_mul hE _ _ (rayOfNeZero_orEpsB_det e a) (rayOfNeZero_orEpsB_det f b) T hv,
    orEpsB_apply_self]
  simp only [AlternatingMap.compLinearMap_apply, AlternatingMap.smul_apply, smul_eq_mul,
    ContinuousLinearMap.coe_coe]
  congr 1
  ring

omit [FiniteDimensional ℝ F] in
theorem orEpsB_rayOfNeZero_smul_det (e : Basis (Fin m) ℝ E) {c : ℝ} (hc : c = 1 ∨ c = -1)
    (h : c • e.det ≠ 0) : orEpsB e (rayOfNeZero ℝ (c • e.det) h) = c := by
  rcases hc with rfl | rfl
  · apply orEpsB_eq_one
    rw [Basis.orientation, ray_eq_iff, one_smul]
    exact SameRay.rfl
  · apply orEpsB_eq_neg_one
    have h1 : (-1 : ℝ) • e.det = -e.det := by ext; simp
    rw [Basis.orientation, neg_rayOfNeZero, ray_eq_iff, h1]
    exact SameRay.rfl

/-- The sign of the concatenated basis relative to the product orientation. -/
theorem orEpsB_prodBasis (hE : finrank ℝ E = m) (hF : finrank ℝ F = n)
    (a : Orientation ℝ E (Fin m)) (b : Orientation ℝ F (Fin n)) (e : Basis (Fin m) ℝ E)
    (f : Basis (Fin n) ℝ F) :
    orEpsB (prodBasis e f) (orProdGen hE hF a b) = orEpsB e a * orEpsB f b := by
  rw [← rayOfNeZero_prodBasis hE hF a b e f]
  apply orEpsB_rayOfNeZero_smul_det
  rcases orEpsB_eq_one_or e a with h1 | h1 <;> rcases orEpsB_eq_one_or f b with h2 | h2 <;>
    simp [h1, h2]

theorem orEpsB_congr {e : Basis (Fin m) ℝ E} {a : Orientation ℝ E (Fin m)}
    {e' : Basis (Fin n) ℝ F} {a' : Orientation ℝ F (Fin n)}
    (h : e.orientation = a ↔ e'.orientation = a') : orEpsB e a = orEpsB e' a' := by
  by_cases h1 : e.orientation = a
  · rw [orEpsB_eq_one h1, orEpsB_eq_one (h.1 h1)]
  · rw [orEpsB_eq_neg_one' h1, orEpsB_eq_neg_one' (fun h2 => h1 (h.2 h2))]

omit [FiniteDimensional ℝ F] in
theorem orEpsB_reindex (e : Basis (Fin m) ℝ E) (a : Orientation ℝ E (Fin m))
    (σ : Fin m ≃ Fin n) :
    orEpsB (e.reindex σ) (Orientation.reindex ℝ E σ a) = orEpsB e a :=
  orEpsB_congr (by rw [Basis.orientation_reindex, Equiv.apply_eq_iff_eq])

omit [FiniteDimensional ℝ F] in
/-- A basis is positive for the orientation of a form iff the form is positive on it. -/
theorem orientation_eq_rayOfNeZero_iff (e : Basis (Fin n) ℝ E) {ω : E [⋀^Fin n]→ₗ[ℝ] ℝ}
    (hω : ω ≠ 0) : e.orientation = rayOfNeZero ℝ ω hω ↔ 0 < ω e := by
  have h1 := ω.eq_smul_basis_det e
  have h2 : ω e ≠ 0 := ne_zero_of_basis hω e
  rw [Basis.orientation, ray_eq_iff]
  conv_lhs => rw [h1]
  exact sameRay_smul_right_iff_of_ne e.det_ne_zero h2

omit [FiniteDimensional ℝ F] in
/-- The basis made from a family equal to a basis `f` has the orientation of `f` (this produces
the hypothesis `huo` of the main results from a positive basis `f` with `D (u i) = f i`). -/
theorem orientation_basisOfLinearIndependent' (f : Basis (Fin n) ℝ E) {v : Fin n → E}
    (hv : ∀ i, v i = f i) (hli : LinearIndependent ℝ v)
    (h : Fintype.card (Fin n) = finrank ℝ E) :
    (basisOfLinearIndependentOfCardEqFinrank' v hli h).orientation = f.orientation := by
  congr 1
  exact Basis.eq_of_apply_eq fun i => by simp [hv]

end linear

/-! ### Reindexing and associativity -/

section glue

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G] {m n q : ℕ}

omit [FiniteDimensional ℝ F] in
/-- Transporting along equalities of dimension indices does not change the sign. -/
theorem orSign_reindex_reindex {N : ℕ} (h₁ : m = N) (h₂ : n = N) (h₃ : n = m)
    (A : Orientation ℝ E (Fin m)) (B : Orientation ℝ F (Fin n)) (T : E →L[ℝ] F) :
    orSign (Orientation.reindex ℝ E (finCongr h₁) A) (Orientation.reindex ℝ F (finCongr h₂) B) T =
      orSign A (Orientation.reindex ℝ F (finCongr h₃) B) T := by
  subst h₁ h₃
  simp [finCongr_refl]

omit [FiniteDimensional ℝ F] in
/-- Transporting along equalities of dimension indices does not change the sign. -/
theorem orSign_reindex_reindex' {N : ℕ} (h₁ : m = N) (h₂ : n = N) (h₃ : m = n)
    (A : Orientation ℝ E (Fin m)) (B : Orientation ℝ F (Fin n)) (T : E →L[ℝ] F) :
    orSign (Orientation.reindex ℝ E (finCongr h₁) A) (Orientation.reindex ℝ F (finCongr h₂) B) T =
      orSign (Orientation.reindex ℝ E (finCongr h₃) A) B T := by
  subst h₂ h₃
  simp [finCongr_refl]

/-- **Associativity of the product orientation**: the associator `(E × F) × G → E × (F × G)`
has sign `1`. -/
theorem orSign_prodAssoc (hE : finrank ℝ E = m) (hF : finrank ℝ F = n) (hG : finrank ℝ G = q)
    (a : Orientation ℝ E (Fin m)) (b : Orientation ℝ F (Fin n)) (c : Orientation ℝ G (Fin q)) :
    orSign (orProdGen (finrank_prod_eq hE hF) hG (orProdGen hE hF a b) c)
      (Orientation.reindex ℝ (E × F × G) (finCongr (Nat.add_assoc m n q).symm)
        (orProdGen hE (finrank_prod_eq hF hG) a (orProdGen hF hG b c)))
      (((ContinuousLinearMap.fst ℝ E F).comp (ContinuousLinearMap.fst ℝ (E × F) G)).prod
        (((ContinuousLinearMap.snd ℝ E F).comp (ContinuousLinearMap.fst ℝ (E × F) G)).prod
          (ContinuousLinearMap.snd ℝ (E × F) G))) = 1 := by
  set e := finBasisOfFinrankEq ℝ E hE
  set f := finBasisOfFinrankEq ℝ F hF
  set g := finBasisOfFinrankEq ℝ G hG
  rw [orSign_eq_sgn_det (finrank_prod_eq (finrank_prod_eq hE hF) hG) _ _
      (prodBasis (prodBasis e f) g)
      ((prodBasis e (prodBasis f g)).reindex (finCongr (Nat.add_assoc m n q).symm)),
    orEpsB_reindex, orEpsB_prodBasis, orEpsB_prodBasis, orEpsB_prodBasis, orEpsB_prodBasis,
    Basis.det_reindex]
  have hv : (fun i => (((ContinuousLinearMap.fst ℝ E F).comp
      (ContinuousLinearMap.fst ℝ (E × F) G)).prod
        (((ContinuousLinearMap.snd ℝ E F).comp (ContinuousLinearMap.fst ℝ (E × F) G)).prod
          (ContinuousLinearMap.snd ℝ (E × F) G))) (prodBasis (prodBasis e f) g i)) ∘
      finCongr (Nat.add_assoc m n q).symm = prodBasis e (prodBasis f g) := by
    funext i
    induction i using Fin.addCases with
    | left i =>
      rw [Function.comp_apply, prodBasis_apply_left _ g (j := Fin.castAdd n i) (by simp),
        prodBasis_castAdd, prodBasis_castAdd]
      simp
    | right j =>
      induction j using Fin.addCases with
      | left j =>
        rw [Function.comp_apply, prodBasis_apply_left _ g (j := Fin.natAdd m j) (by simp),
          prodBasis_natAdd, prodBasis_natAdd, prodBasis_castAdd]
        simp
      | right j =>
        rw [Function.comp_apply, prodBasis_apply_right _ g (j := j) (by simp; omega),
          prodBasis_natAdd, prodBasis_natAdd]
        simp
  rw [hv, Basis.det_self, mul_one]
  have hne : orEpsB e a * orEpsB f b * orEpsB g c ≠ 0 :=
    mul_ne_zero (mul_ne_zero (orEpsB_ne_zero e a) (orEpsB_ne_zero f b)) (orEpsB_ne_zero g c)
  rw [show orEpsB e a * orEpsB f b * orEpsB g c * (orEpsB e a * (orEpsB f b * orEpsB g c)) =
    (orEpsB e a * orEpsB f b * orEpsB g c) * (orEpsB e a * orEpsB f b * orEpsB g c) by ring,
    sgn_mul_self hne]

end glue

/-! ### The frame followed by a basis of the kernel -/

section frame

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] {d p : ℕ}

/-- `(u₀, …, u_{p-1}, ι z₀, …, ι z_{d-1})` is linearly independent if `D ∘ u` is, `ι` is
injective and `range ι = ker D`. -/
theorem linearIndependent_frameTuple {ι : Z →L[ℝ] V} {D : V →L[ℝ] F} (hι : Injective ι)
    (hker : LinearMap.range (ι : Z →ₗ[ℝ] V) = LinearMap.ker (D : V →ₗ[ℝ] F)) {u : Fin p → V}
    (hu : LinearIndependent ℝ (fun i => D (u i))) (z : Basis (Fin d) ℝ Z) :
    LinearIndependent ℝ (frameTuple u (fun i => ι (z i))) := by
  have h1 : LinearIndependent ℝ u := LinearIndependent.of_comp (D : V →ₗ[ℝ] F) hu
  have h2 : LinearIndependent ℝ (fun i => ι (z i)) :=
    z.linearIndependent.map' (ι : Z →ₗ[ℝ] V) (LinearMap.ker_eq_bot_of_injective hι)
  have h3 : Disjoint (Submodule.span ℝ (range u))
      (Submodule.span ℝ (range fun i => ι (z i))) := by
    refine (Submodule.range_ker_disjoint (f := (D : V →ₗ[ℝ] F)) hu).mono_right ?_
    rw [Submodule.span_le, ← hker]
    rintro _ ⟨i, rfl⟩
    exact ⟨z i, rfl⟩
  refine (linearIndependent_equiv' (finSumFinEquiv.trans (finCongr (Nat.add_comm p d))) ?_).1
    (h1.sum_type h2 h3)
  funext x
  rcases x with i | j
  · exact frameTuple_apply_left _ _ (by simp)
  · exact frameTuple_apply_right _ _ (by simp; omega)

end frame

end LinkAlg

open LinkAlg

/-! ### Positive bases for the frame orientation -/

section frameOr

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z] {d p : ℕ}

/-- `(u, ι ∘ z)` is a positive basis of `V` exactly when `z` is positive for
`frameOr hZ oV u ι`. -/
theorem frameOr_basis_iff (hZ : finrank ℝ Z = d) (oV : Orientation ℝ V (Fin (d + p)))
    (u : Fin p → V) (ι : Z →L[ℝ] V) (z : Basis (Fin d) ℝ Z) (e : Basis (Fin (d + p)) ℝ V)
    (he : ⇑e = frameTuple u (fun i => ι (z i))) :
    e.orientation = oV ↔ z.orientation = frameOr hZ oV u ι := by
  have hΩ := oV.someVector_ne_zero
  have hval : frameForm oV.someVector u ι z = oV.someVector e := by rw [frameForm_apply, he]
  have hne : frameForm oV.someVector u ι ≠ 0 := by
    intro h0
    have h1 := ne_zero_of_basis hΩ e
    rw [← hval, h0] at h1
    exact h1 rfl
  rw [frameOr_eq_someVector hZ oV hne, orientation_eq_rayOfNeZero_iff z hne, hval]
  conv_lhs => rw [← Module.Ray.someVector_ray oV]
  exact orientation_eq_rayOfNeZero_iff e hΩ

end frameOr

/-! ### Signs of maps whose first component is `D` -/

section main

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
  {Z' : Type*} [NormedAddCommGroup Z'] [NormedSpace ℝ Z'] [FiniteDimensional ℝ Z']
  {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] {d p k b : ℕ}

/-- One preimage and a fixed oriented space `W` (`k = d + b`): no sign. -/
theorem orSign_single_preimage (hk : d + b = k) (hdim : (d + p) + b = p + k)
    (hV : finrank ℝ V = d + p) (hF : finrank ℝ F = p) (hZ : finrank ℝ Z = d)
    (hG : finrank ℝ G = k) (hW : finrank ℝ W = b)
    (oV : Orientation ℝ V (Fin (d + p))) (oF : Orientation ℝ F (Fin p))
    (oG : Orientation ℝ G (Fin k)) (oW : Orientation ℝ W (Fin b))
    (ι : Z →L[ℝ] V) (D : V →L[ℝ] F) (hι : Function.Injective ι)
    (hker : LinearMap.range (ι : Z →ₗ[ℝ] V) = LinearMap.ker (D : V →ₗ[ℝ] F))
    (u : Fin p → V) (hu : LinearIndependent ℝ (fun i => D (u i)))
    (huo : (basisOfLinearIndependentOfCardEqFinrank' _ hu (by simp [hF])).orientation = oF)
    (L : V × W →L[ℝ] G) :
    orSign (Orientation.reindex ℝ (V × W) (finCongr hdim) (orProdGen hV hW oV oW))
        (orProdGen hF hG oF oG) ((D.comp (ContinuousLinearMap.fst ℝ V W)).prod L) =
      orSign (Orientation.reindex ℝ (Z × W) (finCongr hk)
          (orProdGen hZ hW (frameOr hZ oV u ι) oW))
        oG (L.comp (ι.prodMap (ContinuousLinearMap.id ℝ W))) := by
  -- bases: `z` of `Z`, `w` of `W`, `g` of `G`, `eV = (u, ι z)` of `V`, `f = D u` of `F`
  obtain ⟨z, -⟩ : ∃ z : Basis (Fin d) ℝ Z, True := ⟨finBasisOfFinrankEq ℝ Z hZ, trivial⟩
  obtain ⟨w, -⟩ : ∃ w : Basis (Fin b) ℝ W, True := ⟨finBasisOfFinrankEq ℝ W hW, trivial⟩
  obtain ⟨g, -⟩ : ∃ g : Basis (Fin k) ℝ G, True := ⟨finBasisOfFinrankEq ℝ G hG, trivial⟩
  obtain ⟨eV, heV⟩ : ∃ eV : Basis (Fin (d + p)) ℝ V, ⇑eV = frameTuple u (fun i => ι (z i)) :=
    ⟨basisOfLinearIndependentOfCardEqFinrank' _ (linearIndependent_frameTuple hι hker hu z)
      (by simp [hV]), by simp⟩
  obtain ⟨f, hf, hfo⟩ : ∃ f : Basis (Fin p) ℝ F, ⇑f = (fun i => D (u i)) ∧ f.orientation = oF :=
    ⟨_, by simp, huo⟩
  have hDι : ∀ x, D (ι x) = 0 := fun x => by
    have hx : ι x ∈ LinearMap.range (ι : Z →ₗ[ℝ] V) := ⟨x, rfl⟩
    rw [hker] at hx
    exact hx
  have hεz : orEpsB z (frameOr hZ oV u ι) = orEpsB eV oV :=
    orEpsB_congr (frameOr_basis_iff hZ oV u ι z eV heV).symm
  -- the matrix of the map is block lower triangular
  have h₁ : ∀ j, ((D.comp (ContinuousLinearMap.fst ℝ V W)).prod L)
      (((prodBasis eV w).reindex (finCongr hdim)) (Fin.castAdd k j)) = (f j, L (u j, 0)) := by
    intro j
    rw [Basis.reindex_apply,
      prodBasis_apply_left eV w (j := ⟨j, by have := j.isLt; omega⟩) (by simp), heV,
      frameTuple_apply_left u _ (j := j) rfl, hf]
    simp
  have h₂ : ∀ j, ((D.comp (ContinuousLinearMap.fst ℝ V W)).prod L)
      (((prodBasis eV w).reindex (finCongr hdim)) (Fin.natAdd p j)) =
        (0, (L.comp (ι.prodMap (ContinuousLinearMap.id ℝ W)))
          (((prodBasis z w).reindex (finCongr hk)) j)) := by
    intro j
    obtain ⟨j, rfl⟩ := (finCongr hk).surjective j
    rw [Basis.reindex_apply, Basis.reindex_apply, Equiv.symm_apply_apply]
    induction j using Fin.addCases with
    | left i =>
      rw [prodBasis_castAdd,
        prodBasis_apply_left eV w (j := ⟨p + i, by have := i.isLt; omega⟩) (by simp), heV,
        frameTuple_apply_right u _ (j := i) rfl]
      simp [hDι]
    | right i =>
      rw [prodBasis_natAdd, prodBasis_apply_right eV w (j := i) (by simp; omega)]
      simp
  have hdet := prodBasis_det_apply f g
    (fun i => ((D.comp (ContinuousLinearMap.fst ℝ V W)).prod L)
      (((prodBasis eV w).reindex (finCongr hdim)) i)) f
    (fun i => (L.comp (ι.prodMap (ContinuousLinearMap.id ℝ W)))
      (((prodBasis z w).reindex (finCongr hk)) i))
    (fun j => L (u j, 0)) h₁ h₂
  rw [Basis.det_self, one_mul] at hdet
  rw [orSign_eq_sgn_det ((finrank_prod_eq hV hW).trans hdim) _ _
      ((prodBasis eV w).reindex (finCongr hdim)) (prodBasis f g),
    orSign_eq_sgn_det ((finrank_prod_eq hZ hW).trans hk) _ _
      ((prodBasis z w).reindex (finCongr hk)) g,
    orEpsB_reindex, orEpsB_reindex, orEpsB_prodBasis, orEpsB_prodBasis, orEpsB_prodBasis,
    orEpsB_eq_one hfo, hεz, hdet]
  congr 1
  ring

/-- The mirror statement of `orSign_single_preimage`, with the preimage in the second factor:
the map `(w, x) ↦ (D x, L (w, x))` has sign `(-1)^(b p)` times the sign of `L ∘ (id × ι)`. -/
theorem orSign_single_preimage_right (hk : b + d = k) (hdim : b + (d + p) = p + k)
    (hV : finrank ℝ V = d + p) (hF : finrank ℝ F = p) (hZ : finrank ℝ Z = d)
    (hG : finrank ℝ G = k) (hW : finrank ℝ W = b)
    (oV : Orientation ℝ V (Fin (d + p))) (oF : Orientation ℝ F (Fin p))
    (oG : Orientation ℝ G (Fin k)) (oW : Orientation ℝ W (Fin b))
    (ι : Z →L[ℝ] V) (D : V →L[ℝ] F) (hι : Function.Injective ι)
    (hker : LinearMap.range (ι : Z →ₗ[ℝ] V) = LinearMap.ker (D : V →ₗ[ℝ] F))
    (u : Fin p → V) (hu : LinearIndependent ℝ (fun i => D (u i)))
    (huo : (basisOfLinearIndependentOfCardEqFinrank' _ hu (by simp [hF])).orientation = oF)
    (L : W × V →L[ℝ] G) :
    orSign (Orientation.reindex ℝ (W × V) (finCongr hdim) (orProdGen hW hV oW oV))
        (orProdGen hF hG oF oG) ((D.comp (ContinuousLinearMap.snd ℝ W V)).prod L) =
      (-1) ^ (b * p) *
        orSign (Orientation.reindex ℝ (W × Z) (finCongr hk)
            (orProdGen hW hZ oW (frameOr hZ oV u ι)))
          oG (L.comp ((ContinuousLinearMap.id ℝ W).prodMap ι)) := by
  have hdim' : (d + p) + b = p + k := by omega
  have hk' : d + b = k := by omega
  -- precompose with the swap `W × V → V × W`
  have hS : (D.comp (ContinuousLinearMap.snd ℝ W V)).prod L =
      ((D.comp (ContinuousLinearMap.fst ℝ V W)).prod
        (L.comp ((ContinuousLinearMap.snd ℝ V W).prod (ContinuousLinearMap.fst ℝ V W)))).comp
        ((ContinuousLinearMap.snd ℝ W V).prod (ContinuousLinearMap.fst ℝ W V)) := by
    refine ContinuousLinearMap.ext fun x => ?_
    simp
  rw [hS, orSign_comp ((finrank_prod_eq hW hV).trans hdim) ((finrank_prod_eq hV hW).trans hdim') _
      (Orientation.reindex ℝ (V × W) (finCongr hdim') (orProdGen hV hW oV oW)),
    orSign_single_preimage hk' hdim' hV hF hZ hG hW oV oF oG oW ι D hι hker u hu huo,
    orSign_reindex_reindex hdim hdim' (Nat.add_comm (d + p) b), orSign_swap hW hV oW oV]
  -- and swap back `Z × W → W × Z`
  have hM : (L.comp ((ContinuousLinearMap.snd ℝ V W).prod (ContinuousLinearMap.fst ℝ V W))).comp
      (ι.prodMap (ContinuousLinearMap.id ℝ W)) =
      (L.comp ((ContinuousLinearMap.id ℝ W).prodMap ι)).comp
        ((ContinuousLinearMap.snd ℝ Z W).prod (ContinuousLinearMap.fst ℝ Z W)) := by
    refine ContinuousLinearMap.ext fun x => ?_
    simp
  rw [hM, orSign_comp ((finrank_prod_eq hZ hW).trans hk') ((finrank_prod_eq hW hZ).trans hk) _
      (Orientation.reindex ℝ (W × Z) (finCongr hk) (orProdGen hW hZ oW (frameOr hZ oV u ι))),
    orSign_reindex_reindex hk' hk (Nat.add_comm b d), orSign_swap hZ hW]
  have hsign : ((-1 : ℤ) ^ (d * b) * (-1) ^ (b * (d + p))) = (-1) ^ (b * p) := by
    rw [← pow_add, show d * b + b * (d + p) = b * p + 2 * (b * d) by ring, pow_add, pow_mul]
    norm_num
  rw [mul_assoc, hsign, mul_comm]

/-- Two preimages (`k = d + d`): the sign of `(x, x') ↦ ((D x, D' x'), L (x, x'))` equals
`(-1)^(d p)` times the sign of `L ∘ (ι × ι')` for the product of the frame orientations. -/
theorem orSign_pair_preimage (hk : d + d = k) (hdim : (d + p) + (d + p) = (p + p) + k)
    (hV : finrank ℝ V = d + p) (hF : finrank ℝ F = p) (hZ : finrank ℝ Z = d)
    (hZ' : finrank ℝ Z' = d) (hG : finrank ℝ G = k)
    (oV : Orientation ℝ V (Fin (d + p))) (oF : Orientation ℝ F (Fin p))
    (oG : Orientation ℝ G (Fin k))
    (ι : Z →L[ℝ] V) (D : V →L[ℝ] F) (hι : Function.Injective ι)
    (hker : LinearMap.range (ι : Z →ₗ[ℝ] V) = LinearMap.ker (D : V →ₗ[ℝ] F))
    (u : Fin p → V) (hu : LinearIndependent ℝ (fun i => D (u i)))
    (huo : (basisOfLinearIndependentOfCardEqFinrank' _ hu (by simp [hF])).orientation = oF)
    (ι' : Z' →L[ℝ] V) (D' : V →L[ℝ] F) (hι' : Function.Injective ι')
    (hker' : LinearMap.range (ι' : Z' →ₗ[ℝ] V) = LinearMap.ker (D' : V →ₗ[ℝ] F))
    (u' : Fin p → V) (hu' : LinearIndependent ℝ (fun i => D' (u' i)))
    (huo' : (basisOfLinearIndependentOfCardEqFinrank' _ hu' (by simp [hF])).orientation = oF)
    (L : V × V →L[ℝ] G) :
    orSign (Orientation.reindex ℝ (V × V) (finCongr hdim) (orProdGen hV hV oV oV))
        (orProdGen (finrank_prod_eq hF hF) hG (orProdGen hF hF oF oF) oG)
        ((D.prodMap D').prod L) =
      (-1) ^ (d * p) *
        orSign (Orientation.reindex ℝ (Z × Z') (finCongr hk)
            (orProdGen hZ hZ' (frameOr hZ oV u ι) (frameOr hZ' oV u' ι')))
          oG (L.comp (ι.prodMap ι')) := by
  have hdim₁ : (d + p) + (d + p) = p + (p + k) := by omega
  have hk₁ : d + (d + p) = p + k := by omega
  -- compose with the associator `(F × F) × G → F × (F × G)`
  have h1 := orSign_comp ((finrank_prod_eq hV hV).trans hdim)
    (finrank_prod_eq (finrank_prod_eq hF hF) hG)
    (Orientation.reindex ℝ (V × V) (finCongr hdim) (orProdGen hV hV oV oV))
    (orProdGen (finrank_prod_eq hF hF) hG (orProdGen hF hF oF oF) oG)
    (Orientation.reindex ℝ (F × F × G) (finCongr (Nat.add_assoc p p k).symm)
      (orProdGen hF (finrank_prod_eq hF hG) oF (orProdGen hF hG oF oG)))
    ((D.prodMap D').prod L)
    (((ContinuousLinearMap.fst ℝ F F).comp (ContinuousLinearMap.fst ℝ (F × F) G)).prod
        (((ContinuousLinearMap.snd ℝ F F).comp (ContinuousLinearMap.fst ℝ (F × F) G)).prod
          (ContinuousLinearMap.snd ℝ (F × F) G)))
  have hT : (((ContinuousLinearMap.fst ℝ F F).comp (ContinuousLinearMap.fst ℝ (F × F) G)).prod
        (((ContinuousLinearMap.snd ℝ F F).comp (ContinuousLinearMap.fst ℝ (F × F) G)).prod
          (ContinuousLinearMap.snd ℝ (F × F) G))).comp ((D.prodMap D').prod L) =
      (D.comp (ContinuousLinearMap.fst ℝ V V)).prod
        ((D'.comp (ContinuousLinearMap.snd ℝ V V)).prod L) := by
    refine ContinuousLinearMap.ext fun x => ?_
    simp
  rw [hT, orSign_prodAssoc, one_mul,
    orSign_reindex_reindex' hdim (Nat.add_assoc p p k).symm hdim₁] at h1
  -- the first preimage, with `W = V`
  rw [← h1, orSign_single_preimage hk₁ hdim₁ hV hF hZ (finrank_prod_eq hF hG) hV oV oF
    (orProdGen hF hG oF oG) oV ι D hι hker u hu huo]
  have hL : ((D'.comp (ContinuousLinearMap.snd ℝ V V)).prod L).comp
      (ι.prodMap (ContinuousLinearMap.id ℝ V)) =
      (D'.comp (ContinuousLinearMap.snd ℝ Z V)).prod
        (L.comp (ι.prodMap (ContinuousLinearMap.id ℝ V))) := by
    refine ContinuousLinearMap.ext fun x => ?_
    simp
  -- the second preimage, with `W = Z`
  rw [hL, orSign_single_preimage_right hk hk₁ hV hF hZ' hG hZ oV oF oG (frameOr hZ oV u ι)
    ι' D' hι' hker' u' hu' huo']
  have hL' : (L.comp (ι.prodMap (ContinuousLinearMap.id ℝ V))).comp
      ((ContinuousLinearMap.id ℝ Z).prodMap ι') = L.comp (ι.prodMap ι') := by
    refine ContinuousLinearMap.ext fun x => ?_
    rcases x with ⟨x₁, x₂⟩
    simp
  rw [hL']

end main

end Problems

end Milnor
