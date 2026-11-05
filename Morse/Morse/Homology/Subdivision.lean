import Morse.Homology.AffineSimplex
import Morse.Homology.ModuleComplex

/-!
# Barycentric subdivision of singular chains

This file carries out steps (2)–(4) of Hatcher's proof of Prop. 2.21 (*Algebraic Topology*,
pp. 119–123): barycentric subdivision of singular chains, as a natural chain map
`S : C(X) → C(X)` with a natural chain homotopy `T` from the identity, `∂T + T∂ = 1 - S`.

## Natural operators from models

A singular `n`-simplex `σ : Δⁿ → X` is the image of the identity simplex `ιₙ = id_{Δⁿ}` under
`σ_♯`.  So an operator `Φ` on singular chains which is natural in `X` is determined by the
chain `Φ(ιₙ) ∈ C(Δⁿ)`, its *model*: `Φ(σ) = σ_♯ Φ(ιₙ)`.  Conversely every family of models
`m ∈ C_k(Δⁿ)` defines a natural operator `Morse.Homology.modelOp m`, `σ ↦ σ_♯ m`.  Composites
and boundaries of such operators are again of this form (`Morse.Homology.modelOp_modelOp`,
`Morse.Homology.sbd_modelOp`, `Morse.Homology.modelOp_sbd`), so identities between natural
operators reduce to identities between their models in the chains of the standard simplices.
Every simplex in `modelOp m σ` is of the form `σ ∘ τ`, so these operators preserve chains made
of simplices with a prescribed property that is stable under precomposition, such as lying in a
given subset (`Morse.Homology.modelOp_mem_supported`).

## Subdivision

The models of `S` and `T` are the barycentric subdivision `S ιₙ` and the homotopy `T ιₙ` of the
standard simplex, as linear chains realized as singular chains
(`Morse.Homology.sdModel`, `Morse.Homology.sdHModel`).  The singular operators are
`Morse.Homology.ssd X n` and `Morse.Homology.ssdH X n`.  The identities of linear chains
(`Morse.Homology.lbd_sd`, `Morse.Homology.lbd_sdH`), their naturality for affine maps, and the
fact that each face `δⁱ : Δⁿ → Δⁿ⁺¹` is affine give the model identities, whence:

* `Morse.Homology.sbd_ssd`: `∂S = S∂`;
* `Morse.Homology.sbd_ssdH`: `∂T + T∂ = 1 - S` (in degree `0`, `S = 1` and `T = 0`);
* `Morse.Homology.push_ssd`, `Morse.Homology.push_ssdH`: naturality;
* `Morse.Homology.ssd_pow_single`: `Sᵐ σ = σ_♯ (realization of the m-th barycentric subdivision
  of Δⁿ)`, the input for the diameter estimate.

As morphisms of chain complexes: `Morse.Homology.subdivisionHom R X : C(X) ⟶ C(X)`, natural in
`X` (`Morse.Homology.subdivision R`, an endomorphism of the singular chain functor
`Morse.Homology.singChainsFunctor R`), and
`Morse.Homology.subdivisionHomotopy R X : Homotopy (𝟙 _) (subdivisionHom R X)`.
-/

open CategoryTheory Opposite

noncomputable section

namespace Morse.Homology

universe u v w

variable {R : Type u} [Ring R]

/-! ### Natural operators given by model chains -/

section ModelOp

variable {X : Type v} {Y : Type w} [TopologicalSpace X] [TopologicalSpace Y]

/-- The natural operator `Cₙ(X) → C_k(X)`, `σ ↦ σ_♯ m`, determined by a model chain
`m ∈ C_k(Δⁿ)`. -/
def modelOp {n k : ℕ} (m : Chains R (Simplex n) k) : Chains R X n →ₗ[R] Chains R X k :=
  Finsupp.linearCombination R (fun σ ↦ push σ k m)

@[simp]
lemma modelOp_single {n k : ℕ} (m : Chains R (Simplex n) k) (σ : C(Simplex n, X)) (r : R) :
    modelOp m (Finsupp.single σ r) = r • push σ k m := by
  simp [modelOp]

/-- Natural operators given by models are natural. -/
lemma push_modelOp {n k : ℕ} (m : Chains R (Simplex n) k) (f : C(X, Y)) (c : Chains R X n) :
    push f k (modelOp m c) = modelOp m (push f n c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add, hc, hd]
  | single σ r => simp [push_comp]

/-- The identity singular simplex `ιₙ = id : Δⁿ → Δⁿ`, as a chain. -/
abbrev idSimplex (R : Type u) [Ring R] (n : ℕ) : Chains R (Simplex n) n :=
  Finsupp.single (ContinuousMap.id _) 1

lemma push_idSimplex {n : ℕ} (σ : C(Simplex n, X)) (r : R) :
    push σ n (r • idSimplex R n) = Finsupp.single σ r := by
  rw [Finsupp.smul_single_one, push_single, ContinuousMap.comp_id]

@[simp]
lemma modelOp_idSimplex {n : ℕ} (c : Chains R X n) : modelOp (idSimplex R n) c = c := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add, hc, hd]
  | single σ r => rw [modelOp_single, ← map_smul, push_idSimplex]

lemma modelOp_add_model {n k : ℕ} (m m' : Chains R (Simplex n) k) (c : Chains R X n) :
    modelOp (m + m') c = modelOp m c + modelOp m' c := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add, hc, hd]; abel
  | single σ r => simp [smul_add]

lemma modelOp_sub_model {n k : ℕ} (m m' : Chains R (Simplex n) k) (c : Chains R X n) :
    modelOp (m - m') c = modelOp m c - modelOp m' c := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add, hc, hd]; abel
  | single σ r => simp [smul_sub]

@[simp]
lemma modelOp_zero_model {n k : ℕ} (c : Chains R X n) :
    modelOp (0 : Chains R (Simplex n) k) c = 0 := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add, hc, hd, add_zero]
  | single σ r => simp

/-- Composites of natural operators given by models. -/
lemma modelOp_modelOp {n k l : ℕ} (m : Chains R (Simplex n) k) (m' : Chains R (Simplex k) l)
    (c : Chains R X n) : modelOp m' (modelOp m c) = modelOp (modelOp m' m) c := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add, hc, hd]
  | single σ r => rw [modelOp_single, map_smul, ← push_modelOp, modelOp_single]

/-- The boundary of a natural operator given by a model is given by the boundary of the model. -/
lemma sbd_modelOp {n k : ℕ} (m : Chains R (Simplex n) (k + 1)) (c : Chains R X n) :
    sbd X k (modelOp m c) = modelOp (sbd (Simplex n) k m) c := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add, hc, hd]
  | single σ r => rw [modelOp_single, map_smul, ← push_sbd, modelOp_single]

/-- A natural operator given by a model, precomposed with the boundary, is given by a model. -/
lemma modelOp_sbd {n k : ℕ} (m : Chains R (Simplex n) k) (c : Chains R X (n + 1)) :
    modelOp m (sbd X n c) =
      modelOp (modelOp m (sbd (Simplex (n + 1)) n (idSimplex R (n + 1)))) c := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add, hc, hd]
  | single σ r =>
    rw [← push_idSimplex σ r, ← push_sbd, ← push_modelOp, push_idSimplex, modelOp_single,
      map_smul, map_smul, map_smul]

/-- A family of sets of singular simplices of `X`, one in each degree, closed under
precomposition with maps between standard simplices (for instance: the simplices lying in a given
subset). -/
def IsPrecompClosed (P : ∀ n, Set C(Simplex n, X)) : Prop :=
  ∀ ⦃n k : ℕ⦄ (σ : C(Simplex n, X)) (τ : C(Simplex k, Simplex n)), σ ∈ P n → σ.comp τ ∈ P k

/-- Natural operators given by models preserve chains made of simplices in a family closed
under precomposition. -/
lemma modelOp_mem_supported {P : ∀ n, Set C(Simplex n, X)} (hP : IsPrecompClosed P) {n k : ℕ}
    (m : Chains R (Simplex n) k) {c : Chains R X n} (hc : c ∈ Finsupp.supported R R (P n)) :
    modelOp m c ∈ Finsupp.supported R R (P k) := by
  refine map_mem_supported (fun σ hσ ↦ ?_) hc
  rw [modelOp_single, one_smul]
  refine Finsupp.supported_mono ?_ (mapDomain_mem_supported (f := (σ.comp ·))
    (Finsupp.mem_supported R m |>.2 (Set.subset_univ _)))
  rintro _ ⟨τ, -, rfl⟩
  exact hP σ τ hσ

end ModelOp

/-! ### The models of subdivision -/

section Models

variable (R) in
/-- The model of barycentric subdivision: the barycentric subdivision of the standard simplex
`Δⁿ`, as a singular chain on `Δⁿ`. -/
def sdModel (n : ℕ) : Chains R (Simplex n) n :=
  lreal (convex_simplex n) R n (bsd (convex_simplex n) n (Finsupp.single (verts n) 1))

variable (R) in
/-- The model of the subdivision homotopy: the homotopy `T` applied to the standard simplex
`Δⁿ`, as a singular chain on `Δⁿ`. -/
def sdHModel (n : ℕ) : Chains R (Simplex n) (n + 1) :=
  lreal (convex_simplex n) R (n + 1) (bsdH (convex_simplex n) n (Finsupp.single (verts n) 1))

variable {E : Type v} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul ℝ E] {s : Set E} (hs : Convex ℝ s)

lemma aff_comp_verts {n : ℕ} (u : Fin (n + 1) → s) : aff hs u ∘ verts n = u := by
  ext i : 1
  simp

/-- Pushing the model of subdivision forward along an affine simplex `[u]` gives the
subdivision of `[u]`. -/
lemma push_aff_sdModel {n : ℕ} (u : Fin (n + 1) → s) :
    push (aff hs u) n (sdModel R n) = lreal hs R n (bsd hs n (Finsupp.single u 1)) := by
  rw [sdModel, push_aff_lreal, lmap_aff_bsd, lmap_single, aff_comp_verts]

/-- Pushing the model of the subdivision homotopy forward along an affine simplex `[u]` gives the
homotopy applied to `[u]`. -/
lemma push_aff_sdHModel {n : ℕ} (u : Fin (n + 1) → s) :
    push (aff hs u) (n + 1) (sdHModel R n) =
      lreal hs R (n + 1) (bsdH hs n (Finsupp.single u 1)) := by
  rw [sdHModel, push_aff_lreal, lmap_aff_bsdH, lmap_single, aff_comp_verts]

lemma lreal_verts (n : ℕ) :
    lreal (convex_simplex n) R n (Finsupp.single (verts n) 1) = idSimplex R n := by
  rw [lreal_single, aff_verts]

/-- The boundary of the identity simplex is the alternating sum of the faces, which are affine. -/
lemma sbd_idSimplex (n : ℕ) :
    sbd (Simplex (n + 1)) n (idSimplex R (n + 1)) = ∑ i : Fin (n + 2), ((-1 : ℤ) ^ (i : ℕ)) •
      Finsupp.single (aff (convex_simplex (n + 1)) (verts (n + 1) ∘ Fin.succAbove i)) 1 := by
  rw [sbd_single]
  simp_rw [ContinuousMap.id_comp, faceMap, simplexMap_eq_aff]

/-- The model identity behind `∂S = S∂`. -/
lemma sbd_sdModel (n : ℕ) :
    sbd (Simplex (n + 1)) n (sdModel R (n + 1)) =
      modelOp (sdModel R n) (sbd (Simplex (n + 1)) n (idSimplex R (n + 1))) := by
  rw [sdModel, sbd_lreal, lbd_sd, lbd_single, sbd_idSimplex]
  simp only [map_sum, map_zsmul, modelOp_single, one_smul, push_aff_sdModel]

/-- The model identity behind `∂T + T∂ = 1 - S`. -/
lemma sbd_sdHModel (n : ℕ) :
    sbd (Simplex (n + 1)) (n + 1) (sdHModel R (n + 1)) +
        modelOp (sdHModel R n) (sbd (Simplex (n + 1)) n (idSimplex R (n + 1))) =
      idSimplex R (n + 1) - sdModel R (n + 1) := by
  have h := lbd_sdH (R := R) (fun _ ↦ bary (convex_simplex (n + 1))) n
    (Finsupp.single (verts (n + 1)) 1)
  rw [sdHModel, sbd_lreal, sbd_idSimplex, sdModel, ← lreal_verts, ← map_sub, ← h, map_add,
    lbd_single]
  simp only [map_sum, map_zsmul, modelOp_single, one_smul, push_aff_sdHModel]

lemma sdModel_zero : sdModel R 0 = idSimplex R 0 := by
  rw [sdModel, sd_zero_apply, lreal_verts]

lemma sdHModel_zero : sdHModel R 0 = 0 := by
  simp [sdHModel, bsdH]

end Models

/-! ### Subdivision of singular chains -/

section Subdivision

variable {X : Type v} {Y : Type w} [TopologicalSpace X] [TopologicalSpace Y]

variable (R X) in
/-- **Barycentric subdivision** of singular chains, `S σ = σ_♯ (S Δⁿ)`. -/
def ssd (n : ℕ) : Chains R X n →ₗ[R] Chains R X n := modelOp (sdModel R n)

variable (R X) in
/-- The **subdivision homotopy** of singular chains, `T σ = σ_♯ (T Δⁿ)`. -/
def ssdH (n : ℕ) : Chains R X n →ₗ[R] Chains R X (n + 1) := modelOp (sdHModel R n)

/-- Subdivision is a chain map: `∂S = S∂`. -/
theorem sbd_ssd (n : ℕ) (c : Chains R X (n + 1)) :
    sbd X n (ssd R X (n + 1) c) = ssd R X n (sbd X n c) := by
  rw [ssd, ssd, sbd_modelOp, modelOp_sbd, sbd_sdModel]

/-- **The subdivision homotopy**: `∂T + T∂ = 1 - S`. -/
theorem sbd_ssdH (n : ℕ) (c : Chains R X (n + 1)) :
    sbd X (n + 1) (ssdH R X (n + 1) c) + ssdH R X n (sbd X n c) = c - ssd R X (n + 1) c := by
  rw [ssdH, ssdH, sbd_modelOp, modelOp_sbd, ← modelOp_add_model, sbd_sdHModel,
    modelOp_sub_model, modelOp_idSimplex, ssd]

/-- Subdivision is the identity in degree `0`. -/
@[simp]
lemma ssd_zero (c : Chains R X 0) : ssd R X 0 c = c := by
  rw [ssd, sdModel_zero, modelOp_idSimplex]

/-- The subdivision homotopy vanishes in degree `0`. -/
@[simp]
lemma ssdH_zero (c : Chains R X 0) : ssdH R X 0 c = 0 := by
  rw [ssdH, sdHModel_zero, modelOp_zero_model]

/-- Subdivision is natural. -/
lemma push_ssd (f : C(X, Y)) (n : ℕ) (c : Chains R X n) :
    push f n (ssd R X n c) = ssd R Y n (push f n c) :=
  push_modelOp _ f c

/-- The subdivision homotopy is natural. -/
lemma push_ssdH (f : C(X, Y)) (n : ℕ) (c : Chains R X n) :
    push f (n + 1) (ssdH R X n c) = ssdH R Y n (push f n c) :=
  push_modelOp _ f c

lemma push_ssd_pow (f : C(X, Y)) (n m : ℕ) (c : Chains R X n) :
    push f n ((ssd R X n ^ m) c) = (ssd R Y n ^ m) (push f n c) := by
  induction m with
  | zero => rfl
  | succ m ih => rw [pow_succ', Module.End.mul_apply, push_ssd, ih, pow_succ', Module.End.mul_apply]

/-- Subdivision preserves chains made of simplices in a family closed under precomposition (for
instance, chains in a subspace). -/
lemma ssd_mem_supported {P : ∀ n, Set C(Simplex n, X)} (hP : IsPrecompClosed P) {n : ℕ}
    {c : Chains R X n} (hc : c ∈ Finsupp.supported R R (P n)) :
    ssd R X n c ∈ Finsupp.supported R R (P n) :=
  modelOp_mem_supported hP _ hc

/-- The subdivision homotopy preserves chains made of simplices in a family closed under
precomposition. -/
lemma ssdH_mem_supported {P : ∀ n, Set C(Simplex n, X)} (hP : IsPrecompClosed P) {n : ℕ}
    {c : Chains R X n} (hc : c ∈ Finsupp.supported R R (P n)) :
    ssdH R X n c ∈ Finsupp.supported R R (P (n + 1)) :=
  modelOp_mem_supported hP _ hc

lemma ssd_pow_mem_supported {P : ∀ n, Set C(Simplex n, X)} (hP : IsPrecompClosed P) {n : ℕ}
    (m : ℕ) {c : Chains R X n} (hc : c ∈ Finsupp.supported R R (P n)) :
    (ssd R X n ^ m) c ∈ Finsupp.supported R R (P n) := by
  induction m with
  | zero => exact hc
  | succ m ih => rw [pow_succ', Module.End.mul_apply]; exact ssd_mem_supported hP ih

variable {E : Type w} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul ℝ E] {s : Set E} (hs : Convex ℝ s)

/-- On linear chains, singular subdivision is the subdivision of linear chains. -/
lemma ssd_lreal (n : ℕ) (c : LinChain R s n) :
    ssd R s n (lreal hs R n c) = lreal hs R n (bsd hs n c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add, hc, hd]
  | single w r =>
    rw [lreal_single, ssd, modelOp_single, push_aff_sdModel, ← map_smul, ← map_smul,
      Finsupp.smul_single_one]

lemma ssd_pow_lreal (n m : ℕ) (c : LinChain R s n) :
    (ssd R s n ^ m) (lreal hs R n c) = lreal hs R n ((bsd hs n ^ m) c) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [pow_succ', Module.End.mul_apply, ih, ssd_lreal, pow_succ', Module.End.mul_apply]

/-- **Iterated subdivision of a singular simplex**: `Sᵐ σ` is the image under `σ` of the `m`-th
barycentric subdivision of the standard simplex. -/
theorem ssd_pow_single {n : ℕ} (σ : C(Simplex n, X)) (m : ℕ) :
    (ssd R X n ^ m) (Finsupp.single σ 1) = push σ n
      (lreal (convex_simplex n) R n ((bsd (convex_simplex n) n ^ m)
        (Finsupp.single (verts n) 1))) := by
  rw [← ssd_pow_lreal, lreal_verts, push_ssd_pow, push_single, ContinuousMap.comp_id]

end Subdivision

/-! ### Subdivision as a natural chain map, and the subdivision homotopy -/

section Complexes

variable (R)

/-- **Barycentric subdivision** as a chain map `C(X) → C(X)`. -/
def subdivisionHom (X : Type v) [TopologicalSpace X] : singChains R X ⟶ singChains R X :=
  natHomMk (fun n ↦ ModuleCat.ofHom (ssd R X n)) (fun n ↦ by
    rw [singChains_d]
    exact ModuleCat.hom_ext (LinearMap.ext fun c ↦ sbd_ssd n c))

lemma subdivisionHom_f (X : Type v) [TopologicalSpace X] (n : ℕ) :
    (subdivisionHom R X).f n = ModuleCat.ofHom (ssd R X n) := rfl

/-- **Barycentric subdivision** as a natural chain map `C(X) → C(X)`. -/
def subdivision : singChainsFunctor.{u, v} R ⟶ singChainsFunctor R where
  app X := subdivisionHom R X
  naturality X Y f := by
    ext n : 1
    exact ModuleCat.hom_ext (LinearMap.ext fun (c : Chains R X n) ↦ (push_ssd f.hom n c).symm)

/-- **The subdivision homotopy**: barycentric subdivision is chain homotopic to the identity,
by the natural homotopy `T` with `∂T + T∂ = 1 - S`. -/
def subdivisionHomotopy (X : Type v) [TopologicalSpace X] :
    Homotopy (𝟙 (singChains R X)) (subdivisionHom R X) :=
  natHomotopyMk (fun n ↦ ModuleCat.ofHom (ssdH R X n))
    (by
      rw [singChains_d]
      refine ModuleCat.hom_ext (LinearMap.ext fun (c : Chains R X 0) ↦ ?_)
      change c = sbd X 0 (ssdH R X 0 c) + ssd R X 0 c
      simp)
    (fun n ↦ by
      rw [singChains_d, singChains_d]
      refine ModuleCat.hom_ext (LinearMap.ext fun (c : Chains R X (n + 1)) ↦ ?_)
      change c = ssdH R X n (sbd X n c) + sbd X (n + 1) (ssdH R X (n + 1) c) + ssd R X (n + 1) c
      rw [add_comm (ssdH R X n _), sbd_ssdH, sub_add_cancel])

end Complexes

end Morse.Homology
