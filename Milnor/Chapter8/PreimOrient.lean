import Milnor.Chapter8.OrientFrame
import Milnor.Chapter7.Hopf0
import Milnor.Chapter7.BasisPath
import Milnor.Chapter7.Stereo
import Milnor.Chapter6.Invariance

/-!
# Orienting the preimage of a regular value of a map between spheres (Milnor §5; §8, Problem 14)

Let `f : S^{d+p} → Sᵖ` be smooth with regular value `y`, and let `e` be a positive basis of
`T_y Sᵖ` (read in the chart at `y`).  Spheres carry Milnor's orientation `sphOrStd` as boundaries
of disks.  As in the proof of Lemma 1 of §5, `N = f⁻¹(y)` is oriented by declaring a basis `w` of
`T_xN` positive iff `(u₁, …, u_p, w₁, …, w_d)` is a positive basis of `T_x S^{d+p}` whenever
`df_x(uᵢ) = eᵢ`.  Milnor lists the tangent vectors of `N` first; moving the `p` vectors `uᵢ` past
the `d` vectors `wⱼ` changes the sign by `(-1)^{dp}`, which is `+1` in the Hopf setting
`p = d + 1`.  We put the frame first, as in `Orient.ofFrame`.

* `preimOr`: the orientation, defined by the ambient frame `(x, v₁(x), …, v_p(x))` of
  `ℝ^{d+p+1}` against its standard orientation, where `vᵢ = A^*(AA^*)⁻¹ eᵢ` and `A = dF̃_x` for
  the extension `F̃(z) = c_y(f(z/|z|))` of the chart expression of `f` (`c_y` the chart at `y`);
* `preimOr_or_eq`: the chart-level description above, for any lifts `u` of `e`;
* `preimOr_eq_of_orientation_eq`: independence of the positive basis `e` (by a path of bases).

The Pontryagin framing `pontV` of Chapter 7 is not used: it needs the source to be a slice
submanifold with normal model `ℝʷ` (Euclidean space), while `Sph` is modelled with normal model
`ℝ` (`sphS`).  The explicit extension `F̃` replaces the tubular retraction.
-/

open Set Filter Topology Function Module
open scoped ContDiff Manifold RealInnerProductSpace

noncomputable section

namespace Milnor

namespace Problems

open Sphere Framed

/-! ### Linear algebra of frame tuples -/

section tuple

variable {α β : Type*} {d : ℕ}

theorem frameTuple_map (g : α → β) : ∀ {k : ℕ} (ν : Fin k → α) (w : Fin d → α),
    (fun j => g (frameTuple ν w j)) = frameTuple (fun i => g (ν i)) (fun j => g (w j))
  | 0, _, _ => rfl
  | k + 1, ν, w => by
    funext j
    refine Fin.cases rfl (fun j => ?_) j
    exact congrFun (frameTuple_map g (Fin.tail ν) w) j

theorem frameTuple_mem : ∀ {k : ℕ} (ν : Fin k → α) (w : Fin d → α) (j : Fin (d + k)),
    (∃ i, frameTuple ν w j = ν i) ∨ ∃ i, frameTuple ν w j = w i
  | 0, _, _, j => Or.inr ⟨j, rfl⟩
  | k + 1, ν, w, j => by
    refine Fin.cases (Or.inl ⟨0, rfl⟩) (fun j => ?_) j
    rcases frameTuple_mem (Fin.tail ν) w j with ⟨i, hi⟩ | ⟨i, hi⟩
    · exact Or.inl ⟨i.succ, hi⟩
    · exact Or.inr ⟨i, hi⟩

theorem exists_frameTuple_eq : ∀ {k : ℕ} (ν : Fin k → α) (w : Fin d → α) (i : Fin d),
    ∃ j, frameTuple ν w j = w i
  | 0, _, _, i => ⟨i, rfl⟩
  | k + 1, ν, w, i => by
    obtain ⟨j, hj⟩ := exists_frameTuple_eq (Fin.tail ν) w i
    exact ⟨(j.succ : Fin (d + k + 1)), hj⟩

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]

theorem linearIndependent_of_frameTuple : ∀ {k : ℕ} {ν : Fin k → E} {w : Fin d → E},
    LinearIndependent ℝ (frameTuple ν w) → LinearIndependent ℝ w
  | 0, _, _, h => h
  | k + 1, ν, w, h => by
    have h' : LinearIndependent ℝ
        (Fin.cons (ν 0) (frameTuple (Fin.tail ν) w) : Fin (d + k + 1) → E) := h
    exact linearIndependent_of_frameTuple (linearIndependent_finCons.1 h').1

/-- **Independence of a frame tuple**: `(ν, w)` is independent if `L ∘ ν` is independent, `w` is
independent and `L` kills `w`. -/
theorem linearIndependent_frameTuple (L : E →ₗ[ℝ] F) :
    ∀ {k : ℕ} {ν : Fin k → E} {w : Fin d → E}, LinearIndependent ℝ (fun i => L (ν i)) →
      LinearIndependent ℝ w → (∀ j, L (w j) = 0) → LinearIndependent ℝ (frameTuple ν w)
  | 0, _, _, _, hw, _ => hw
  | k + 1, ν, w, hν, hw, hLw => by
    have ih : LinearIndependent ℝ (frameTuple (Fin.tail ν) w) :=
      linearIndependent_frameTuple L (hν.comp Fin.succ (Fin.succ_injective _)) hw hLw
    have hν' : LinearIndependent ℝ
        (Fin.cons (L (ν 0)) (fun i => L (Fin.tail ν i)) : Fin (k + 1) → F) := by
      have h := Fin.cons_self_tail (fun i => L (ν i))
      rw [← h] at hν
      exact hν
    show LinearIndependent ℝ (Fin.cons (ν 0) (frameTuple (Fin.tail ν) w) : Fin (d + k + 1) → E)
    refine linearIndependent_finCons.2 ⟨ih, fun hmem => (linearIndependent_finCons.1 hν').2 ?_⟩
    have h1 := Submodule.mem_map_of_mem (f := L) hmem
    rw [Submodule.map_span] at h1
    refine Submodule.span_le.2 ?_ h1
    rintro _ ⟨_, ⟨j, rfl⟩, rfl⟩
    rcases frameTuple_mem (Fin.tail ν) w j with ⟨i, hi⟩ | ⟨i, hi⟩
    · rw [SetLike.mem_coe, hi]
      exact Submodule.subset_span ⟨i, rfl⟩
    · rw [SetLike.mem_coe, hi, hLw]
      exact zero_mem _

end tuple

theorem rayOfNeZero_congr {M : Type*} [AddCommGroup M] [Module ℝ M] {v w : M} (h : v = w)
    (hv : v ≠ 0) (hw : w ≠ 0) : rayOfNeZero ℝ v hv = rayOfNeZero ℝ w hw := by
  subst h; rfl

/-! ### Frame forms -/

section forms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z] {d : ℕ}

omit [FiniteDimensional ℝ E] in
/-- A form vanishes on `(T r, μ, T z₁, …, T z_d)`: these contain `d + 1` vectors of the at most
`d`-dimensional space `range T`. -/
theorem apply_vecCons_frameTuple_eq_zero (hZ : finrank ℝ Z = d) {k : ℕ}
    (Ω : E [⋀^Fin (d + k + 1)]→ₗ[ℝ] ℝ) (μ : Fin k → E) (T : Z →L[ℝ] E) (r : Z) (z : Fin d → Z) :
    Ω (Matrix.vecCons (T r) (frameTuple μ fun j => T (z j))) = 0 := by
  by_contra hne
  have hli : LinearIndependent ℝ (Matrix.vecCons (T r) (frameTuple μ fun j => T (z j))) := by
    by_contra h
    exact hne (Ω.map_linearDependent _ h)
  rw [Matrix.vecCons, linearIndependent_finCons] at hli
  obtain ⟨hli1, hnot⟩ := hli
  have hw : LinearIndependent ℝ (fun j => T (z j)) := linearIndependent_of_frameTuple hli1
  have hle : Submodule.span ℝ (range fun j => T (z j)) ≤ LinearMap.range (T : Z →ₗ[ℝ] E) := by
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    exact ⟨z j, rfl⟩
  have heq : Submodule.span ℝ (range fun j => T (z j)) = LinearMap.range (T : Z →ₗ[ℝ] E) := by
    refine Submodule.eq_of_le_of_finrank_le hle ?_
    rw [finrank_span_eq_card hw, Fintype.card_fin, ← hZ]
    exact LinearMap.finrank_range_le _
  apply hnot
  have h1 : T r ∈ Submodule.span ℝ (range fun j => T (z j)) := by
    rw [heq]; exact ⟨r, rfl⟩
  refine Submodule.span_mono ?_ h1
  rintro _ ⟨j, rfl⟩
  exact exists_frameTuple_eq μ _ j

omit [FiniteDimensional ℝ E] in
/-- **The frame form only depends on the frame modulo `range T`.** -/
theorem frameForm_congr_frame (hZ : finrank ℝ Z = d) :
    ∀ {k : ℕ} (Ω : E [⋀^Fin (d + k)]→ₗ[ℝ] ℝ) {ν ν' : Fin k → E} (T : Z →L[ℝ] E),
      (∀ i, ∃ r, ν i = ν' i + T r) → frameForm Ω ν T = frameForm Ω ν' T
  | 0, Ω, ν, ν', T, _ => by rw [Subsingleton.elim ν ν']
  | k + 1, Ω, ν, ν', T, h => by
    have ih := frameForm_congr_frame hZ ((Ω : E [⋀^Fin (d + k + 1)]→ₗ[ℝ] ℝ).curryLeft (ν 0)) T
      (ν := Fin.tail ν) (ν' := Fin.tail ν') fun i => h i.succ
    obtain ⟨r, hr⟩ := h 0
    show frameForm ((Ω : E [⋀^Fin (d + k + 1)]→ₗ[ℝ] ℝ).curryLeft (ν 0)) (Fin.tail ν) T =
      frameForm ((Ω : E [⋀^Fin (d + k + 1)]→ₗ[ℝ] ℝ).curryLeft (ν' 0)) (Fin.tail ν') T
    rw [ih]
    ext z
    have h0 : (Ω : E [⋀^Fin (d + k + 1)]→ₗ[ℝ] ℝ).curryLeft (T r)
        (frameTuple (Fin.tail ν') fun j => T (z j)) = 0 := by
      rw [AlternatingMap.curryLeft_apply_apply]
      exact apply_vecCons_frameTuple_eq_zero hZ Ω _ T r z
    rw [frameForm_apply, frameForm_apply, hr, map_add, AlternatingMap.add_apply, h0, add_zero]

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ Z] in
/-- Pulling a frame of vectors of the form `L cᵢ` in front of a form along `L`. -/
theorem frameForm_vecCons_comp {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] {k : ℕ}
    (Ω : E [⋀^Fin (d + k + 1)]→ₗ[ℝ] ℝ) (v : E) (L : E' →L[ℝ] E) (c : Fin k → E')
    (T : Z →L[ℝ] E') :
    frameForm (d := d) (k := k + 1) Ω (Matrix.vecCons v fun i => L (c i)) (L.comp T) =
      frameForm (frameForm (k := 1) Ω ![v] L) c T := by
  ext z
  rw [frameForm_apply, frameForm_apply, frameForm_apply]
  exact congrArg (fun t => Ω (Matrix.vecCons v t)) (frameTuple_map L c fun j => T (z j)).symm

/-- **Positive changes of basis.**  Let `L : E → ℝᵖ` have a right inverse `S`, and let `T : Z → E`
be injective with `L ∘ T = 0`.  For two bases `e, e'` of `ℝᵖ` with the same orientation, the frame
forms of the lifts `S e'` and `S e` are positive multiples of each other. -/
theorem exists_pos_frameForm_lift {p : ℕ} (hZ : finrank ℝ Z = d) (hE : finrank ℝ E = d + p)
    {Ω : E [⋀^Fin (d + p)]→ₗ[ℝ] ℝ} (hΩ : Ω ≠ 0) {L : E →L[ℝ] EuclideanSpace ℝ (Fin p)}
    {S : EuclideanSpace ℝ (Fin p) →L[ℝ] E} (hLS : ∀ c, L (S c) = c) {T : Z →L[ℝ] E}
    (hT : Injective T) (hLT : ∀ r, L (T r) = 0)
    (e e' : Basis (Fin p) ℝ (EuclideanSpace ℝ (Fin p))) (hee' : e.orientation = e'.orientation) :
    ∃ c : ℝ, 0 < c ∧
      frameForm Ω (fun i => S (e' i)) T = c • frameForm Ω (fun i => S (e i)) T := by
  obtain ⟨z, -⟩ : ∃ z : Basis (Fin d) ℝ Z, z = finBasisOfFinrankEq ℝ Z hZ := ⟨_, rfl⟩
  have hnd : ∀ b : Fin p → EuclideanSpace ℝ (Fin p), LinearIndependent ℝ b →
      frameForm Ω (fun i => S (b i)) T z ≠ 0 := by
    intro b hb
    refine frameForm_apply_ne_zero_of_linearIndependent hE hΩ ?_
    refine linearIndependent_frameTuple (L : E →ₗ[ℝ] EuclideanSpace ℝ (Fin p)) ?_
      (z.linearIndependent.map' (T : Z →ₗ[ℝ] E) (LinearMap.ker_eq_bot_of_injective hT))
      fun j => hLT (z j)
    convert hb using 1
    funext i
    exact hLS (b i)
  obtain ⟨A, hA, hAe⟩ := GLp.exists_det_pos_of_orientation_eq e e' hee'
  obtain ⟨B, hBs, hB0, hB1, hBli⟩ := GLp.exists_basisPath e.linearIndependent hA
    (ε := 1 / 4) (by norm_num) (by norm_num)
  obtain ⟨g, hg⟩ : ∃ g : ℝ → ℝ, ∀ t, g t = frameForm Ω (fun i => S (B t i)) T z :=
    ⟨_, fun _ => rfl⟩
  have hgc : Continuous g := by
    have h1 : g = fun t => Ω (frameTuple (fun i => S (B t i)) fun j => T (z j)) :=
      funext fun t => by rw [hg, frameForm_apply]
    rw [h1]
    exact (continuous_alternatingMap_of_finrank hE Ω).comp (continuous_frameTuple.comp
      ((continuous_pi fun i => S.continuous.comp ((continuous_apply i).comp hBs.continuous)).prodMk
        continuous_const))
  have hg0 : ∀ t, g t ≠ 0 := fun t => by rw [hg]; exact hnd _ (hBli t)
  have hsign : 0 < g 0 * g 1 := by
    rcases lt_or_gt_of_ne (hg0 0) with h0 | h0 <;> rcases lt_or_gt_of_ne (hg0 1) with h1 | h1
    · exact mul_pos_of_neg_of_neg h0 h1
    · obtain ⟨t, ht⟩ := intermediate_value_univ 0 1 hgc
        (show (0 : ℝ) ∈ Icc (g 0) (g 1) from ⟨h0.le, h1.le⟩)
      exact absurd ht (hg0 t)
    · obtain ⟨t, ht⟩ := intermediate_value_univ 1 0 hgc
        (show (0 : ℝ) ∈ Icc (g 1) (g 0) from ⟨h1.le, h0.le⟩)
      exact absurd ht (hg0 t)
    · exact mul_pos h0 h1
  have hge' : g 0 = frameForm Ω (fun i => S (e' i)) T z := by
    rw [hg, hB0 0 (by norm_num), hAe]
  have hge : g 1 = frameForm Ω (fun i => S (e i)) T z := by
    rw [hg, hB1 1 (by norm_num)]
  have hne : frameForm Ω (fun i => S (e i)) T ≠ 0 := fun h =>
    hnd _ e.linearIndependent (by rw [h]; rfl)
  obtain ⟨c, hc⟩ := exists_eq_smul_of_finrank hZ hne (frameForm Ω (fun i => S (e' i)) T)
  refine ⟨c, ?_, hc⟩
  have h2 : g 0 = c * g 1 := by rw [hge', hge, hc, AlternatingMap.smul_apply, smul_eq_mul]
  rw [h2, mul_assoc] at hsign
  exact (pos_iff_pos_of_mul_pos hsign).2 (mul_self_pos.2 (hg0 1))

end forms

/-! ### The extension of the chart expression of a map between spheres -/

section ext

variable {n p : ℕ}

theorem sph_val_ne_zero (x : Sph n) : x.1 ≠ 0 := fun h => by
  have h1 := mem_iff_norm.1 x.2
  rw [h, norm_zero] at h1
  exact zero_ne_one h1

/-- The tangent space of the sphere at `x` is `x^⊥`. -/
theorem exists_mfd_val_eq {x : Sph n} {v : EuclideanSpace ℝ (Fin (n + 1))} (hv : ⟪x.1, v⟫ = 0) :
    ∃ c, mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))
      (Subtype.val : Sph n → EuclideanSpace ℝ (Fin (n + 1))) x c = v := by
  refine (mem_range_mfderiv_val_iff (finrank_Z_add hE hZ) contMDiff_sphG isRegularValue_sphG
    x v).2 ?_
  have h : fderiv ℝ sphG x.1 v = 0 := by rw [fderiv_sphG, hv, mul_zero]
  rw [mfderiv_eq_fderiv]
  exact h

/-- The extension `F̃(z) = c_y(f(z/|z|))` of the chart expression of `f : Sⁿ → Sᵖ` at `y`. -/
def sphExt (f : Sph n → Sph p) (y : Sph p) (z : EuclideanSpace ℝ (Fin (n + 1))) :
    EuclideanSpace ℝ (Fin p) :=
  extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) y (f (nv0 z))

/-- Its derivative `A(z) = dF̃_z`. -/
def sphExtDer (f : Sph n → Sph p) (y : Sph p) (z : EuclideanSpace ℝ (Fin (n + 1))) :
    EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] EuclideanSpace ℝ (Fin p) :=
  fderiv ℝ (sphExt f y) z

theorem sphExt_val (f : Sph n → Sph p) (y : Sph p) (x : Sph n) :
    sphExt f y x.1 = extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) y (f x) := by
  unfold sphExt; rw [nv0_of_mem]

variable {f : Sph n → Sph p}
  (hf : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) ∞ f) {y : Sph p}

include hf in
theorem contDiffAt_sphExt {x : Sph n}
    (hsrc : f x ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) y).source) :
    ContDiffAt ℝ ∞ (sphExt f y) x.1 := by
  have h1 : ContMDiffAt 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞
      (fun z => nv0 z) x.1 :=
    contMDiffAt_nv0_comp (w := fun z => z) ⟨{z | z ≠ 0}, isOpen_ne⟩
      (fun _ _ => contMDiffAt_id) (fun _ hz => hz) (sph_val_ne_zero x)
  have h2 : ContMDiffAt 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) ∞
      (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) y) (f (nv0 x.1)) := by
    rw [nv0_of_mem]
    exact contMDiffAt_extChartAt' (by rwa [← extChartAt_source 𝓘(ℝ, EuclideanSpace ℝ (Fin p))])
  exact contMDiffAt_iff_contDiffAt.1 (h2.comp x.1 ((hf (nv0 x.1)).comp x.1 h1))

include hf in
theorem hasFDerivAt_sphExt {x : Sph n}
    (hsrc : f x ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) y).source) :
    HasFDerivAt (sphExt f y) (sphExtDer f y x.1) x.1 :=
  ((contDiffAt_sphExt hf hsrc).differentiableAt (by simp)).hasFDerivAt

include hf in
/-- The chain rule along the sphere: `A(x) ∘ d(val)_x = df_x` at points of `f⁻¹(y)`. -/
theorem sphExtDer_comp_mfd_val {x : Sph n} (hx : f x = y) :
    (sphExtDer f y x.1).comp (mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) (Subtype.val : Sph n → EuclideanSpace ℝ (Fin (n + 1))) x) =
      mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) f x := by
  have hsrc : f x ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) y).source := by
    rw [hx]; exact mem_extChartAt_source y
  have h1 : sphExt f y ∘ (Subtype.val : Sph n → EuclideanSpace ℝ (Fin (n + 1))) =
      fun q => extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) y (f q) :=
    funext fun q => sphExt_val f y q
  have hd := (hasFDerivAt_sphExt hf hsrc).hasMFDerivAt
  have h2 := hd.comp x (hasMFDerivAt_mfd (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
    (J := 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))))
    (Sphere.contMDiff_val.mdifferentiableAt (by simp)))
  rw [h1] at h2
  have h3 := (hasMFDerivAt_mfd (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin p)))
    (J := 𝓘(ℝ, EuclideanSpace ℝ (Fin p)))
    (mdifferentiableAt_extChartAt
      (by rwa [← extChartAt_source 𝓘(ℝ, EuclideanSpace ℝ (Fin p))]))).comp
    x (hasMFDerivAt_mfd (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      (J := 𝓘(ℝ, EuclideanSpace ℝ (Fin p))) (hf.mdifferentiableAt (by simp)))
  have h4 : (sphExtDer f y x.1).comp (mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) (Subtype.val : Sph n → EuclideanSpace ℝ (Fin (n + 1))) x) =
      (mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p))
        (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) y) (f x)).comp
        (mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) f x) :=
    hasMFDerivAt_unique h2 h3
  rw [hx, mfd_extChartAt_self, ContinuousLinearMap.id_comp] at h4
  exact h4

include hf in
theorem sphExtDer_mfd_val {x : Sph n} (hx : f x = y) (u : EuclideanSpace ℝ (Fin n)) :
    sphExtDer f y x.1 (mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))
      (Subtype.val : Sph n → EuclideanSpace ℝ (Fin (n + 1))) x u) =
      mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) f x u :=
  congrArg (fun T : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin p) => T u)
    (sphExtDer_comp_mfd_val hf hx)

include hf in
/-- The radial direction lies in the kernel: `A(x) x = 0`. -/
theorem sphExtDer_self {x : Sph n}
    (hsrc : f x ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) y).source) :
    sphExtDer f y x.1 x.1 = 0 := by
  have h1 : HasDerivAt (fun s : ℝ => (1 + s) • x.1) x.1 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).const_add 1).smul_const x.1
  have h2 : HasFDerivAt (sphExt f y) (sphExtDer f y x.1) ((1 + (0 : ℝ)) • x.1) := by
    rw [add_zero, one_smul]; exact hasFDerivAt_sphExt hf hsrc
  have hd := h2.comp_hasDerivAt (0 : ℝ) h1
  have hconst : (sphExt f y ∘ fun s : ℝ => (1 + s) • x.1) =ᶠ[𝓝 (0 : ℝ)]
      fun _ => sphExt f y x.1 := by
    filter_upwards [Ioi_mem_nhds (show (-1 : ℝ) < 0 by norm_num)] with s hs
    have hs' : 0 < 1 + s := by
      have : -1 < s := hs
      linarith
    show sphExt f y ((1 + s) • x.1) = sphExt f y x.1
    unfold sphExt
    rw [nv0_smul hs']
  exact hd.unique ((hasDerivAt_const (0 : ℝ) _).congr_of_eventuallyEq hconst)

variable (hy : IsRegularValue 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) f y)

include hf hy in
theorem surjective_sphExtDer {x : Sph n} (hx : f x = y) : Surjective (sphExtDer f y x.1) := by
  have hs : Surjective (mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) f x) :=
    hy x hx
  rw [← sphExtDer_comp_mfd_val hf hx] at hs
  exact Surjective.of_comp hs

/-- The pulled-back frame `vᵢ = A^*(AA^*)⁻¹ bᵢ` along `f⁻¹(y)`. -/
def sphPullFrame (f : Sph n → Sph p) (y : Sph p) (b : Fin p → EuclideanSpace ℝ (Fin p))
    (i : Fin p) (q : f ⁻¹' {y}) : EuclideanSpace ℝ (Fin (n + 1)) :=
  pinv (sphExtDer f y q.1.1) (b i)

include hf hy in
theorem sphExtDer_sphPullFrame (b : Fin p → EuclideanSpace ℝ (Fin p)) (i : Fin p)
    (q : f ⁻¹' {y}) : sphExtDer f y q.1.1 (sphPullFrame f y b i q) = b i := by
  have hq : f q.1 = y := q.2
  exact comp_pinv (surjective_sphExtDer hf hy hq) (b i)

include hf in
theorem inner_sphPullFrame (b : Fin p → EuclideanSpace ℝ (Fin p)) (i : Fin p) (q : f ⁻¹' {y}) :
    ⟪q.1.1, sphPullFrame f y b i q⟫ = 0 := by
  have hq : f q.1 = y := q.2
  rw [real_inner_comm]
  exact inner_pinv_eq_zero _ _ (sphExtDer_self hf (by rw [hq]; exact mem_extChartAt_source y))

include hf hy in
theorem continuous_sphPullFrame (b : Fin p → EuclideanSpace ℝ (Fin p)) (i : Fin p) :
    Continuous (sphPullFrame f y b i) := by
  rw [continuous_iff_continuousAt]
  intro q
  have hq : f q.1 = y := q.2
  have hsrc : f q.1 ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) y).source := by
    rw [hq]; exact mem_extChartAt_source y
  have hA : ContDiffAt ℝ ∞ (sphExtDer f y) q.1.1 :=
    (contDiffAt_sphExt hf hsrc).fderiv_right le_rfl
  have hAd : ContDiffAt ℝ ∞ (fun z => ContinuousLinearMap.adjoint (sphExtDer f y z)) q.1.1 :=
    ((Tub.adjointCLM (k := p) (n := n + 1)).contDiff.contDiffAt).comp q.1.1 hA
  have hAA : ContDiffAt ℝ ∞ (fun z => (sphExtDer f y z).comp
      (ContinuousLinearMap.adjoint (sphExtDer f y z))) q.1.1 := hA.clm_comp hAd
  obtain ⟨u, hu⟩ := isUnit_comp_adjoint (surjective_sphExtDer hf hy hq)
  have hinv : ContDiffAt ℝ ∞ (fun z => Ring.inverse ((sphExtDer f y z).comp
      (ContinuousLinearMap.adjoint (sphExtDer f y z)))) q.1.1 := by
    have := contDiffAt_ringInverse ℝ (n := ∞) u
    rw [hu] at this
    exact this.comp q.1.1 hAA
  have hpinv : ContDiffAt ℝ ∞ (fun z => pinv (sphExtDer f y z) (b i)) q.1.1 := by
    unfold pinv
    exact (hAd.clm_comp hinv).clm_apply contDiffAt_const
  exact ContinuousAt.comp (g := fun z => pinv (sphExtDer f y z) (b i)) hpinv.continuousAt
    (continuous_subtype_val.comp continuous_subtype_val).continuousAt

end ext

/-! ### The orientation of the preimage -/

section preim

variable {d p : ℕ}

theorem preimDim : finrank ℝ (EuclideanSpace ℝ (Fin d)) + finrank ℝ (EuclideanSpace ℝ (Fin p)) =
    finrank ℝ (EuclideanSpace ℝ (Fin (d + p))) := levelDim rfl

/-- A positive basis of `T_y Sᵖ` for the orientation `sphOrStd`. -/
theorem exists_basis_orientation_sphOrStd (hp : 1 ≤ p) (y : Sph p) :
    ∃ e : Basis (Fin p) ℝ (EuclideanSpace ℝ (Fin p)), e.orientation = (sphOrStd p).or y :=
  haveI : Nonempty (Fin p) := ⟨⟨0, hp⟩⟩
  ⟨((sphOrStd p).or y).someBasis (by simp), Orientation.someBasis_orientation _ _⟩

variable {f : Sph (d + p) → Sph p}
  (hf : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin (d + p))) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) ∞ f)
  {y : Sph p}
  (hy : IsRegularValue 𝓘(ℝ, EuclideanSpace ℝ (Fin (d + p))) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) f y)

include hf hy in
/-- `f⁻¹(y)` is a submanifold of `S^{d+p}` of dimension `d` (Chapter 2, Lemma 1). -/
theorem isSliceSubmanifold_preim :
    IsSliceSubmanifold 𝓘(ℝ, EuclideanSpace ℝ (Fin (d + p))) (EuclideanSpace ℝ (Fin d))
      (EuclideanSpace ℝ (Fin p)) (f ⁻¹' {y}) :=
  isSliceSubmanifold_preimage preimDim hf hy

include hy in
theorem surjective_mfd_preim (q : f ⁻¹' {y}) :
    Surjective (mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin (d + p))) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) f q.1) :=
  hy q.1 q.2

include hf hy in
theorem contMDiff_preimEmb :
    letI := (isSliceSubmanifold_preim hf hy).chartedSpace
    ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) 𝓘(ℝ, EuclideanSpace ℝ (Fin (d + p + 1))) ∞
      (fun q : f ⁻¹' {y} => q.1.1) := by
  let _ := (isSliceSubmanifold_preim hf hy).chartedSpace
  have _ := (isSliceSubmanifold_preim hf hy).isManifold
  exact Sphere.contMDiff_val.comp (isSliceSubmanifold_preim hf hy).contMDiff_val

include hf hy in
theorem mfd_preimEmb (q : f ⁻¹' {y}) :
    letI := (isSliceSubmanifold_preim hf hy).chartedSpace
    mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) 𝓘(ℝ, EuclideanSpace ℝ (Fin (d + p + 1)))
        (fun q : f ⁻¹' {y} => q.1.1) q =
      (mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin (d + p))) 𝓘(ℝ, EuclideanSpace ℝ (Fin (d + p + 1)))
        (Subtype.val : Sph (d + p) → EuclideanSpace ℝ (Fin (d + p + 1))) q.1).comp
      (mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) 𝓘(ℝ, EuclideanSpace ℝ (Fin (d + p)))
        (Subtype.val : f ⁻¹' {y} → Sph (d + p)) q) := by
  let _ := (isSliceSubmanifold_preim hf hy).chartedSpace
  have _ := (isSliceSubmanifold_preim hf hy).isManifold
  have h1 := hasMFDerivAt_mfd (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin (d + p))))
    (J := 𝓘(ℝ, EuclideanSpace ℝ (Fin (d + p + 1))))
    (Sphere.contMDiff_val.mdifferentiableAt (by simp) :
      MDifferentiableAt _ _ (Subtype.val : Sph (d + p) → EuclideanSpace ℝ (Fin (d + p + 1))) q.1)
  have h2 := hasMFDerivAt_mfd (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin d)))
    (J := 𝓘(ℝ, EuclideanSpace ℝ (Fin (d + p))))
    ((isSliceSubmanifold_preim hf hy).contMDiff_val.mdifferentiableAt (by simp) :
      MDifferentiableAt _ _ (Subtype.val : f ⁻¹' {y} → Sph (d + p)) q)
  exact HasMFDerivAt.mfd_eq (h1.comp q h2)

/-- The ambient frame `(x, v₁(x), …, v_p(x))` along `f⁻¹(y)`. -/
def preimFrame (f : Sph (d + p) → Sph p) (y : Sph p) (b : Fin p → EuclideanSpace ℝ (Fin p))
    (q : f ⁻¹' {y}) : Fin (p + 1) → EuclideanSpace ℝ (Fin (d + p + 1)) :=
  Matrix.vecCons q.1.1 fun i => sphPullFrame f y b i q

include hf hy in
theorem continuous_preimFrame (b : Fin p → EuclideanSpace ℝ (Fin p)) :
    Continuous (preimFrame f y b) :=
  (continuous_subtype_val.comp continuous_subtype_val).matrixVecCons
    (continuous_pi fun i => continuous_sphPullFrame hf hy b i)

include hf hy in
/-- **Nondegeneracy**: for lifts `u` of an independent family, `(x, u, dι z)` is a basis. -/
theorem frameForm_lift_ne_zero {b : Fin p → EuclideanSpace ℝ (Fin p)} (hb : LinearIndependent ℝ b)
    (q : f ⁻¹' {y}) (u : Fin p → EuclideanSpace ℝ (Fin (d + p)))
    (hu : ∀ i,
      mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin (d + p))) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) f q.1 (u i) = b i) :
    letI := (isSliceSubmanifold_preim hf hy).chartedSpace
    frameForm (frameForm (stdOrE (d + p)).someVector ![q.1.1]
        (mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin (d + p))) 𝓘(ℝ, EuclideanSpace ℝ (Fin (d + p + 1)))
          (Subtype.val : Sph (d + p) → EuclideanSpace ℝ (Fin (d + p + 1))) q.1)) u
      (mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) 𝓘(ℝ, EuclideanSpace ℝ (Fin (d + p)))
        (Subtype.val : f ⁻¹' {y} → Sph (d + p)) q) ≠ 0 := by
  let _ := (isSliceSubmanifold_preim hf hy).chartedSpace
  have _ := (isSliceSubmanifold_preim hf hy).isManifold
  obtain ⟨z, -⟩ : ∃ z : Basis (Fin d) ℝ (EuclideanSpace ℝ (Fin d)),
      z = finBasisOfFinrankEq ℝ _ (hZ (n := d)) := ⟨_, rfl⟩
  intro h0
  refine frameForm_apply_ne_zero_of_linearIndependent (z := z) (hZ (n := d + p))
    (sph_frameForm_ne_zero q.1) ?_ (by rw [h0]; rfl)
  refine linearIndependent_frameTuple
    (mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin (d + p))) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) f q.1 :
      EuclideanSpace ℝ (Fin (d + p)) →ₗ[ℝ] EuclideanSpace ℝ (Fin p)) ?_
    (z.linearIndependent.map'
      (mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) 𝓘(ℝ, EuclideanSpace ℝ (Fin (d + p)))
        (Subtype.val : f ⁻¹' {y} → Sph (d + p)) q :
          EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin (d + p)))
      (LinearMap.ker_eq_bot_of_injective
        (injective_mfderiv_val (isSliceSubmanifold_preim hf hy) q)))
    fun j => (mem_range_mfderiv_val_iff preimDim hf hy q _).1 ⟨z j, rfl⟩
  have hfun : (fun i => (mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin (d + p))) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) f
      q.1 : EuclideanSpace ℝ (Fin (d + p)) →ₗ[ℝ] EuclideanSpace ℝ (Fin p)) (u i)) = b := funext hu
  rw [hfun]
  exact hb

include hf hy in
/-- **Reduction to the tangent space of the sphere**: the ambient frame form equals the frame form
of `sphOrStd`'s volume form with the chart-level lifts `u` of `b`. -/
theorem frameForm_preimFrame (b : Fin p → EuclideanSpace ℝ (Fin p)) (q : f ⁻¹' {y})
    (u : Fin p → EuclideanSpace ℝ (Fin (d + p)))
    (hu : ∀ i,
      mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin (d + p))) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) f q.1 (u i) = b i) :
    letI := (isSliceSubmanifold_preim hf hy).chartedSpace
    frameForm (d := d) (k := p + 1) (stdOrE (d + p)).someVector (preimFrame f y b q)
        (mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) 𝓘(ℝ, EuclideanSpace ℝ (Fin (d + p + 1)))
          (fun q : f ⁻¹' {y} => q.1.1) q) =
      frameForm (frameForm (stdOrE (d + p)).someVector ![q.1.1]
          (mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin (d + p))) 𝓘(ℝ, EuclideanSpace ℝ (Fin (d + p + 1)))
            (Subtype.val : Sph (d + p) → EuclideanSpace ℝ (Fin (d + p + 1))) q.1)) u
        (mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) 𝓘(ℝ, EuclideanSpace ℝ (Fin (d + p)))
          (Subtype.val : f ⁻¹' {y} → Sph (d + p)) q) := by
  let _ := (isSliceSubmanifold_preim hf hy).chartedSpace
  have _ := (isSliceSubmanifold_preim hf hy).isManifold
  have hq : f q.1 = y := q.2
  have hc : ∀ i, ∃ c, mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin (d + p)))
      𝓘(ℝ, EuclideanSpace ℝ (Fin (d + p + 1)))
      (Subtype.val : Sph (d + p) → EuclideanSpace ℝ (Fin (d + p + 1))) q.1 c =
        sphPullFrame f y b i q :=
    fun i => exists_mfd_val_eq (inner_sphPullFrame hf b i q)
  choose c hc using hc
  have hframe : preimFrame f y b q = Matrix.vecCons q.1.1 fun i =>
      mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin (d + p))) 𝓘(ℝ, EuclideanSpace ℝ (Fin (d + p + 1)))
        (Subtype.val : Sph (d + p) → EuclideanSpace ℝ (Fin (d + p + 1))) q.1 (c i) := by
    unfold preimFrame
    simp only [hc]
  rw [hframe, mfd_preimEmb hf hy q, frameForm_vecCons_comp]
  refine frameForm_congr_frame (hZ (n := d)) _ _ fun i => ?_
  have h1 : mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin (d + p))) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) f q.1
      (c i - u i) = 0 := by
    rw [map_sub, hu, ← sphExtDer_mfd_val hf hq, hc, sphExtDer_sphPullFrame hf hy, sub_self]
  obtain ⟨r, hr⟩ := (mem_range_mfderiv_val_iff preimDim hf hy q (c i - u i)).2 h1
  refine ⟨r, ?_⟩
  have hr' : mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) 𝓘(ℝ, EuclideanSpace ℝ (Fin (d + p)))
      (Subtype.val : f ⁻¹' {y} → Sph (d + p)) q r = c i - u i := hr
  rw [hr']
  abel

/-- **The preimage orientation** of `f⁻¹(y)`, for a positive basis `e` of `T_y Sᵖ`: the frame
`(x, v₁, …, v_p)` (`vᵢ` the pulled-back frame, `df_x vᵢ = eᵢ`) followed by the tangent vectors is
positive for the standard orientation of `ℝ^{d+p+1}`. -/
def preimOr (e : Basis (Fin p) ℝ (EuclideanSpace ℝ (Fin p)))
    (_he : e.orientation = (sphOrStd p).or y) :
    letI := (isSliceSubmanifold_preim hf hy).chartedSpace
    Orient 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) (f ⁻¹' {y}) d :=
  letI := (isSliceSubmanifold_preim hf hy).chartedSpace
  haveI := (isSliceSubmanifold_preim hf hy).isManifold
  Orient.ofFrame (E := EuclideanSpace ℝ (Fin (d + p + 1))) (d := d) (k := p + 1) (hZ (n := d))
    (finrank_euclideanSpace_fin : finrank ℝ (EuclideanSpace ℝ (Fin (d + p + 1))) = d + (p + 1))
    (stdOrE (d + p)) (contMDiff_preimEmb hf hy) (continuous_preimFrame hf hy e) fun q => by
      have hs := surjective_mfd_preim hy q
      rw [frameForm_preimFrame hf hy e q _ fun i => comp_pinv hs (e i)]
      exact frameForm_lift_ne_zero hf hy e.linearIndependent q _ fun i => comp_pinv hs (e i)

/-- **Chart-level description of the preimage orientation.**  In chart coordinates of the source
sphere at `x = q.1`, with `ι = d(val)_q : ℝᵈ → ℝ^{d+p}` and any lifts `u` of `e`
(`df_x(uᵢ) = eᵢ`), a basis `z` of `ℝᵈ` is positive iff `(u, ι z)` is positive for
`(sphOrStd (d + p)).or x`. -/
theorem preimOr_or_eq (e : Basis (Fin p) ℝ (EuclideanSpace ℝ (Fin p)))
    (he : e.orientation = (sphOrStd p).or y) (q : f ⁻¹' {y})
    (u : Fin p → EuclideanSpace ℝ (Fin (d + p)))
    (hu : ∀ i,
      mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin (d + p))) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) f q.1 (u i) = e i) :
    letI := (isSliceSubmanifold_preim hf hy).chartedSpace
    (preimOr hf hy e he).or q = frameOr hZ ((sphOrStd (d + p)).or q.1) u
      (mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) 𝓘(ℝ, EuclideanSpace ℝ (Fin (d + p)))
        (Subtype.val : f ⁻¹' {y} → Sph (d + p)) q) := by
  let _ := (isSliceSubmanifold_preim hf hy).chartedSpace
  have _ := (isSliceSubmanifold_preim hf hy).isManifold
  have hΩS := sph_frameForm_ne_zero q.1
  have hnd := frameForm_lift_ne_zero hf hy e.linearIndependent q u hu
  have hkey := frameForm_preimFrame hf hy e q u hu
  have hnd' : frameForm (d := d) (k := p + 1) (stdOrE (d + p)).someVector (preimFrame f y e q)
      (mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) 𝓘(ℝ, EuclideanSpace ℝ (Fin (d + p + 1)))
        (fun q : f ⁻¹' {y} => q.1.1) q) ≠ 0 := by
    rw [hkey]; exact hnd
  have hS : rayOfNeZero ℝ _ hΩS = (sphOrStd (d + p)).or q.1 :=
    (frameOr_eq_someVector hZ (stdOrE (d + p)) hΩS).symm
  rw [frameOr_eq hZ hΩS hS hnd]
  show frameOr (d := d) (k := p + 1) (hZ (n := d)) (stdOrE (d + p)) (preimFrame f y e q)
    (mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) 𝓘(ℝ, EuclideanSpace ℝ (Fin (d + p + 1)))
      (fun q : f ⁻¹' {y} => q.1.1) q) = _
  rw [frameOr_eq_someVector (d := d) (k := p + 1) (hZ (n := d)) (stdOrE (d + p)) hnd']
  exact rayOfNeZero_congr hkey _ _

/-- **Independence of the positive basis.** -/
theorem preimOr_eq_of_orientation_eq (e e' : Basis (Fin p) ℝ (EuclideanSpace ℝ (Fin p)))
    (he : e.orientation = (sphOrStd p).or y) (he' : e'.orientation = (sphOrStd p).or y) :
    letI := (isSliceSubmanifold_preim hf hy).chartedSpace
    preimOr hf hy e he = preimOr hf hy e' he' := by
  let _ := (isSliceSubmanifold_preim hf hy).chartedSpace
  have _ := (isSliceSubmanifold_preim hf hy).isManifold
  refine Orient.ext' fun q => ?_
  have hs := surjective_mfd_preim hy q
  have hlift : ∀ b : Fin p → EuclideanSpace ℝ (Fin p), ∀ i,
      mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin (d + p))) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) f q.1
        (pinv (mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin (d + p))) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) f q.1)
          (b i)) = b i :=
    fun b i => comp_pinv hs (b i)
  rw [preimOr_or_eq hf hy e he q _ (hlift e), preimOr_or_eq hf hy e' he' q _ (hlift e')]
  have hΩS := sph_frameForm_ne_zero q.1
  have hS : rayOfNeZero ℝ _ hΩS = (sphOrStd (d + p)).or q.1 :=
    (frameOr_eq_someVector hZ (stdOrE (d + p)) hΩS).symm
  rw [frameOr_eq hZ hΩS hS (frameForm_lift_ne_zero hf hy e.linearIndependent q _ (hlift e)),
    frameOr_eq hZ hΩS hS (frameForm_lift_ne_zero hf hy e'.linearIndependent q _ (hlift e')),
    ray_eq_iff]
  obtain ⟨c, hc, hce⟩ := exists_pos_frameForm_lift (hZ (n := d)) (hZ (n := d + p)) hΩS
    (L := mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin (d + p))) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) f q.1)
    (S := pinv (mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin (d + p))) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) f q.1))
    (comp_pinv hs)
    (T := mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) 𝓘(ℝ, EuclideanSpace ℝ (Fin (d + p)))
      (Subtype.val : f ⁻¹' {y} → Sph (d + p)) q)
    (injective_mfderiv_val (isSliceSubmanifold_preim hf hy) q)
    (fun r => (mem_range_mfderiv_val_iff preimDim hf hy q _).1 ⟨r, rfl⟩) e e' (he.trans he'.symm)
  rw [hce]
  exact (SameRay.sameRay_pos_smul_left _ hc).symm

end preim

end Problems

end Milnor
