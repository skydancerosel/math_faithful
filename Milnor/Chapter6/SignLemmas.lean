import Milnor.Chapter6.Opens
import Milnor.Chapter6.LevelSign

/-!
# Sign lemmas for Chapter 6

* the chain rule for signs, with three independent models;
* the signed count is invariant under precomposition with an orientation-preserving
  diffeomorphism;
* the sign of the pair map `(f, c·G)` at a zero of `G` is `sgn c` times that of `(f, G)`;
* the contracted form does not depend on the choice of outward vector;
* the sign of a map restricted between two level sets, for the level-set orientations, is the
  sign of the ambient Jacobian determinant.
-/

open Set Module Filter Topology Function
open scoped ContDiff Manifold

noncomputable section

namespace Milnor

universe u

section chain

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N]
  {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℝ F'] [FiniteDimensional ℝ F']
  {G'' : Type*} [TopologicalSpace G''] {K : ModelWithCorners ℝ F' G''}
  {P : Type*} [TopologicalSpace P] [ChartedSpace G'' P] [IsManifold K ∞ P] {n : ℕ}

/-- **Chain rule for signs**, three models. -/
theorem signAt_comp' (hE : finrank ℝ E = n) (hF : finrank ℝ F = n) (oM : Orient I M n)
    (oN : Orient J N n) (oP : Orient K P n) {f : M → N} {h : N → P} {x : M}
    (hf : MDifferentiableAt I J f x) (hh : MDifferentiableAt J K h (f x)) :
    signAt oM oP (fun x => h (f x)) x = signAt oN oP h (f x) * signAt oM oN f x := by
  unfold signAt
  have hc := HasMFDerivAt.mfd_eq ((hasMFDerivAt_mfd (I := J) (J := K) hh).comp x
    (hasMFDerivAt_mfd (I := I) (J := J) hf))
  show orSign (oM.or x) (oP.or ((h ∘ f) x)) (mfd I K (h ∘ f) x) = _
  rw [hc]
  exact orSign_comp hE hF _ _ _ _ _

/-- **Precomposition with an orientation-preserving diffeomorphism** preserves the signed
count. -/
theorem degAt_comp_diffeo (hE : finrank ℝ E = n) (hF : finrank ℝ F = n) (hF' : finrank ℝ F' = n)
    (oM : Orient I M n) (oN : Orient J N n) (oP : Orient K P n) {f : N → P}
    (hf : ∀ y, MDifferentiableAt J K f y) (φ : M ≃ₘ⟮I, J⟯ N)
    (hφ : ∀ x, signAt oM oN φ x = 1) (z : P) :
    degAt oM oP (fun x => f (φ x)) z = degAt oN oP f z := by
  unfold degAt
  refine finsum_mem_eq_of_bijOn φ ⟨fun x hx => hx, fun x _ x' _ h => φ.injective h, fun y hy =>
    ⟨φ.symm y, by show f (φ (φ.symm y)) = z; rw [φ.apply_symm_apply]; exact hy,
      φ.apply_symm_apply y⟩⟩ fun x _ => ?_
  rw [signAt_comp' hE hF oM oN oP (φ.contMDiff.mdifferentiableAt (by simp)) (hf _), hφ, mul_one]

end chain

section pair

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G} [J.Boundaryless] [I.Boundaryless]
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N] {n : ℕ}

/-- **Rescaling the boundary function.** At a zero of `G`, `sign (f, c·G) = sgn c · sign (f, G)`. -/
theorem signAt_pairMap_mul (hE : finrank ℝ E = n + 1) (hF : finrank ℝ F = n) (oM : Orient I M (n + 1))
    (oN : Orient J N n) {f : M → N} {c G : M → ℝ} {x : M} (hf : MDifferentiableAt I J f x)
    (hc : MDifferentiableAt I 𝓘(ℝ, ℝ) c x) (hG : MDifferentiableAt I 𝓘(ℝ, ℝ) G x) (hG0 : G x = 0) :
    signAt oM (oN.prodReal hF) (pairMap f (fun x => c x * G x)) x =
      sgn (c x) * signAt oM (oN.prodReal hF) (pairMap f G) x := by
  have hcG : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun x => c x * G x) x := hc.mul hG
  have hd : mfd I 𝓘(ℝ, ℝ) (fun x => c x * G x) x = c x • mfd I 𝓘(ℝ, ℝ) G x := by
    have := HasMFDerivAt.mfd_eq ((hasMFDerivAt_mfd (I := I) (J := 𝓘(ℝ, ℝ)) hc).mul
      (hasMFDerivAt_mfd (I := I) (J := 𝓘(ℝ, ℝ)) hG))
    rw [show (fun x => c x * G x) = c * G from rfl, this]
    change (c x • mfd I 𝓘(ℝ, ℝ) G x + G x • mfd I 𝓘(ℝ, ℝ) c x : E →L[ℝ] ℝ) = _
    rw [hG0, zero_smul, add_zero]
  -- the scaling map of `F × ℝ`
  set S : F × ℝ →L[ℝ] F × ℝ :=
    (ContinuousLinearMap.fst ℝ F ℝ).prod (c x • ContinuousLinearMap.snd ℝ F ℝ) with hS
  have hcomp : mfd I (J.prod 𝓘(ℝ, ℝ)) (pairMap f (fun x => c x * G x)) x =
      S.comp (mfd I (J.prod 𝓘(ℝ, ℝ)) (pairMap f G) x) := by
    rw [mfd_pairMap hf hcG, mfd_pairMap hf hG, hd]
    ext v <;> simp [S]
  unfold signAt
  rw [hcomp, orSign_comp hE (finrank_prod_real hF)]
  have hSsign : orSign ((oN.prodReal hF).or (pairMap f G x)) ((oN.prodReal hF).or
      (pairMap f (fun x => c x * G x) x)) S = sgn (c x) := by
    show orSign (orProd hF (oN.or (f x))) (orProd hF (oN.or (f x))) S = sgn (c x)
    rw [orSign_orProd hF hF _ _ S (ContinuousLinearMap.id ℝ F) 0 (c x) (fun v t => by
      simp [S])]
    rw [orSign_id, one_mul]
  rw [hSsign]

end pair

section level

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z] {n : ℕ}

/-- **Independence of the outward vector.** If `w = a • w' + t` with `t` in the range of the
injective `T : Z → E` (`dim Z = n`), then the contracted forms are proportional by `a`. -/
theorem contractForm_eq_smul (hZ : finrank ℝ Z = n) (om : E [⋀^Fin (n + 1)]→ₗ[ℝ] ℝ)
    {w w' : E} {T : Z →L[ℝ] E} {a : ℝ} {t : Z} (h : w = a • w' + T t) :
    contractForm om w T = a • contractForm om w' T := by
  ext u
  simp only [contractForm_apply, AlternatingMap.smul_apply, smul_eq_mul, h]
  -- `om (a • w' + T t, T u₁, …)` = `a • om (w', T u) + om (T t, T u)`, the last vanishing
  have hcons : Matrix.vecCons (a • w' + T t) (fun i => T (u i)) =
      Function.update (Matrix.vecCons w' fun i => T (u i)) 0 (a • w' + T t) := by
    funext i; refine Fin.cases ?_ (fun i => ?_) i <;> simp
  rw [hcons, AlternatingMap.map_update_add, AlternatingMap.map_update_smul]
  have h0 : Function.update (Matrix.vecCons w' fun i => T (u i)) 0 w' =
      Matrix.vecCons w' fun i => T (u i) := by
    funext i; refine Fin.cases ?_ (fun i => ?_) i <;> simp
  have hdep : om (Function.update (Matrix.vecCons w' fun i => T (u i)) 0 (T t)) = 0 := by
    apply AlternatingMap.map_linearDependent
    intro hli
    -- `n + 1` vectors in the range of `T`, which has dimension `≤ n`
    have hsub : Set.range (Function.update (Matrix.vecCons w' fun i => T (u i)) 0 (T t)) ⊆
        LinearMap.range (T : Z →ₗ[ℝ] E) := by
      rintro _ ⟨i, rfl⟩
      refine Fin.cases ?_ (fun i => ?_) i
      · simp
      · simp
    have h1 := finrank_span_eq_card (R := ℝ) hli
    have h2 := Submodule.finrank_mono (Submodule.span_le.2 hsub)
    have h3 := LinearMap.finrank_range_le (T : Z →ₗ[ℝ] E)
    rw [Fintype.card_fin] at h1
    rw [hZ] at h3
    omega
  rw [h0, hdep, add_zero]
  rfl

end level

end Milnor
