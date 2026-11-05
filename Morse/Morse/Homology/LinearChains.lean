import Morse.Homology.Simplex

/-!
# Linear chains, the cone operator and barycentric subdivision (combinatorics)

Hatcher's proof of excision (*Algebraic Topology*, Prop. 2.21) subdivides singular chains by
first subdividing *linear* chains.  A linear `k`-simplex `[w₀, …, w_k]` in a convex set is
determined by its ordered tuple of vertices, and the operations on linear chains used by the
subdivision are purely combinatorial operations on tuples, together with one geometric input,
the barycentre `b(w)` of a tuple.  This file isolates the combinatorics; the geometry (affine
simplices in a convex set, barycentres, diameters) is in `Morse/Homology/AffineSimplex.lean`.

## Linear chains

For a type `V` of "vertices", `Morse.Homology.tuples V` is the simplicial set whose `k`-simplices
are the tuples `w : Fin (k + 1) → V`, simplicial operators acting by precomposition, and the
*linear chains* `LinChain R V k = (Fin (k + 1) → V) →₀ R` are its free chains
(`Morse.Homology.freeChains`).  So the boundary `∂[w₀, …, w_{k+1}] = ∑ᵢ (-1)ⁱ [w₀, …, ŵᵢ, …]`
(`Morse.Homology.lbd`) satisfies `∂∂ = 0` without further work, and a map of vertex sets
`f : V → V'` acts by a chain map (`Morse.Homology.lmap`).

## The cone operator (Hatcher's `b ·`)

For `b : V`, `Morse.Homology.cone b : LinChain R V k → LinChain R V (k + 1)` is
`[w₀, …, w_k] ↦ [b, w₀, …, w_k]`.  It satisfies `∂(b · α) = α - b · ∂α` in positive degrees
(`Morse.Homology.lbd_cone_succ`) and `∂(b · α) = α - ε(α) [b]` in degree `0`, where `ε` is the
augmentation (`Morse.Homology.lbd_cone_zero`).  Hatcher packages both as one formula with the
augmented complex; we keep the two cases apart and never need the degree `-1`.

## Subdivision and the subdivision homotopy

Given a barycentre function `β : (Fin (k + 1) → V) → V` in each degree, the subdivision operator
`S = Morse.Homology.sd β` and the homotopy `T = Morse.Homology.sdH β` are defined by recursion on
the degree, as in Hatcher:
* `S = id` in degree `0`, and `S[w] = β(w) · S(∂[w])` in degree `k + 1`;
* `T = 0` in degree `0`, and `T[w] = β(w) · ([w] - T(∂[w]))` in degree `k + 1`.

(Hatcher's `T` is `[w₀] ↦ [w₀, w₀]` in degree `0`; with `T = 0` the formulas below still hold,
because `S = id` in degree `0`.)  Then, purely formally:
* `∂S = S∂` (`Morse.Homology.lbd_sd`): `S` is a chain map;
* `∂T + T∂ = 1 - S` (`Morse.Homology.lbd_sdH`, and `lbd_sdH_zero` in degree `0`);
* `S` and `T` are natural for maps of vertex sets compatible with the barycentres
  (`Morse.Homology.lmap_sd`, `Morse.Homology.lmap_sdH`).

All identities are proved on the generators `[w]` by induction on the degree.
-/

open CategoryTheory Opposite

noncomputable section

namespace Morse.Homology

universe u v w

/-! ### The simplicial set of tuples -/

section Tuples

variable (V : Type v)

/-- The simplicial set of tuples in `V`: its `k`-simplices are the tuples `w : Fin (k + 1) → V`
(the vertices of a "linear simplex"), and a simplicial operator `f : ⦋m⦌ ⟶ ⦋k⦌` acts by
precomposition `w ↦ w ∘ f`. -/
def tuples : SSet.{v} where
  obj n := Fin (n.unop.len + 1) → V
  map f := ↾fun w ↦ w ∘ f.unop.toOrderHom

variable {V}

@[simp]
lemma tuples_δ {k : ℕ} (i : Fin (k + 2)) (w : Fin (k + 2) → V) :
    (tuples V).δ i w = w ∘ Fin.succAbove i := rfl

/-- A map of vertex sets induces a map of simplicial sets of tuples. -/
@[simps]
def tuplesMap {V' : Type v} (f : V → V') : tuples V ⟶ tuples V' where
  app _ := ↾fun w ↦ f ∘ w

end Tuples

/-! ### Linear chains -/

section LinChain

variable (R : Type u) [Ring R] (V : Type v)

/-- Linear `k`-chains with vertices in `V`: finite formal combinations of `(k + 1)`-tuples. -/
abbrev LinChain (k : ℕ) : Type (max u v) := (Fin (k + 1) → V) →₀ R

variable {R V}

/-- The boundary of linear chains, `∂[w₀, …, w_{k+1}] = ∑ᵢ (-1)ⁱ [w₀, …, ŵᵢ, …, w_{k+1}]`. -/
abbrev lbd (k : ℕ) : LinChain R V (k + 1) →ₗ[R] LinChain R V k := bd R (tuples V) k

lemma lbd_single {k : ℕ} (w : Fin (k + 2) → V) (r : R) :
    lbd k (Finsupp.single w r) =
      ∑ i : Fin (k + 2), ((-1 : ℤ) ^ (i : ℕ)) • Finsupp.single (w ∘ Fin.succAbove i) r :=
  bd_single R (tuples V) k w r

@[simp]
lemma lbd_lbd {k : ℕ} (c : LinChain R V (k + 2)) : lbd k (lbd (k + 1) c) = 0 :=
  bd_bd R (tuples V) k c

/-- The map of linear chains induced by a map of vertex sets. -/
def lmap {V' : Type w} (f : V → V') (k : ℕ) : LinChain R V k →ₗ[R] LinChain R V' k :=
  Finsupp.lmapDomain R R (f ∘ ·)

@[simp]
lemma lmap_single {V' : Type w} (f : V → V') {k : ℕ} (w : Fin (k + 1) → V) (r : R) :
    lmap f k (Finsupp.single w r) = Finsupp.single (f ∘ w) r :=
  Finsupp.mapDomain_single

lemma lmap_lbd {V' : Type w} (f : V → V') (k : ℕ) (c : LinChain R V (k + 1)) :
    lmap f k (lbd k c) = lbd k (lmap f (k + 1) c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add, hc, hd]
  | single w r =>
    rw [lbd_single, lmap_single, lbd_single, map_sum]
    simp only [map_zsmul, lmap_single]
    rfl

/-- The cone operator `b · [w₀, …, w_k] = [b, w₀, …, w_k]`. -/
def cone (b : V) (k : ℕ) : LinChain R V k →ₗ[R] LinChain R V (k + 1) :=
  Finsupp.lmapDomain R R (fun w : Fin (k + 1) → V ↦ (Fin.cons b w : Fin (k + 2) → V))

@[simp]
lemma cone_single (b : V) {k : ℕ} (w : Fin (k + 1) → V) (r : R) :
    cone b k (Finsupp.single w r) = Finsupp.single (Fin.cons b w) r :=
  Finsupp.mapDomain_single

/-- The augmentation `ε : LinChain R V 0 → R`, the sum of the coefficients. -/
def aug : LinChain R V 0 →ₗ[R] R := Finsupp.linearCombination R (fun _ ↦ 1)

@[simp]
lemma aug_single (w : Fin 1 → V) (r : R) : aug (Finsupp.single w r) = r := by
  simp [aug]

lemma aug_lbd (c : LinChain R V 1) : aug (lbd 0 c) = 0 := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => rw [map_add, map_add, hc, hd, add_zero]
  | single w r =>
    rw [lbd_single, map_sum]
    simp [Fin.sum_univ_two]

lemma cons_comp_succAbove_succ {k : ℕ} (b : V) (w : Fin (k + 2) → V) (j : Fin (k + 2)) :
    (Fin.cons b w : Fin (k + 3) → V) ∘ Fin.succAbove j.succ = Fin.cons b (w ∘ Fin.succAbove j) := by
  ext i
  refine Fin.cases ?_ (fun i ↦ ?_) i
  · simp
  · simp [Fin.succ_succAbove_succ]

/-- `∂(b · α) = α - ε(α) [b]` for `α` of degree `0`. -/
lemma lbd_cone_zero (b : V) (c : LinChain R V 0) :
    lbd 0 (cone b 0 c) = c - Finsupp.single (fun _ ↦ b) (aug c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => rw [map_add, map_add, hc, hd, map_add, Finsupp.single_add]; abel
  | single w r =>
    rw [cone_single, lbd_single, Fin.sum_univ_two, aug_single]
    have h₁ : (Fin.cons b w : Fin 2 → V) ∘ Fin.succAbove 1 = fun _ ↦ b := by
      ext i
      fin_cases i
      rfl
    simp [h₁, sub_eq_add_neg]

/-- `∂(b · α) = α - b · ∂α` for `α` of positive degree. -/
lemma lbd_cone_succ (b : V) {k : ℕ} (c : LinChain R V (k + 1)) :
    lbd (k + 1) (cone b (k + 1) c) = c - cone b k (lbd k c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => rw [map_add, map_add, hc, hd, map_add, map_add]; abel
  | single w r =>
    rw [cone_single, lbd_single, Fin.sum_univ_succ, lbd_single, map_sum]
    simp only [Fin.val_zero, pow_zero, one_smul, Fin.succAbove_zero, Fin.val_succ,
      cons_comp_succAbove_succ, cone_single, map_zsmul]
    have h₀ : (Fin.cons b w : Fin (k + 3) → V) ∘ Fin.succ = w := by ext i; simp
    rw [h₀, sub_eq_add_neg, ← Finset.sum_neg_distrib]
    congr 1
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [pow_succ, mul_neg_one, neg_smul]

lemma lmap_cone {V' : Type w} (f : V → V') (b : V) (k : ℕ) (c : LinChain R V k) :
    lmap f (k + 1) (cone b k c) = cone (f b) k (lmap f k c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => rw [map_add, map_add, hc, hd, map_add, map_add]
  | single w r =>
    simp only [cone_single, lmap_single]
    congr 1
    ext i
    refine Fin.cases ?_ (fun i ↦ ?_) i <;> simp

end LinChain

/-! ### Subdivision and the subdivision homotopy -/

section Subdivision

variable {R : Type u} [Ring R] {V : Type v} (β : ∀ k : ℕ, (Fin (k + 1) → V) → V)

/-- The barycentric subdivision operator on linear chains, relative to a barycentre function
`β`: the identity in degree `0`, and `S[w] = β(w) · S(∂[w])` in degree `k + 1`. -/
def sd : ∀ k : ℕ, (LinChain R V k →ₗ[R] LinChain R V k)
  | 0 => LinearMap.id
  | k + 1 => Finsupp.linearCombination R
      (fun w ↦ cone (β (k + 1) w) k (sd k (lbd k (Finsupp.single w 1))))

/-- The subdivision homotopy on linear chains: `0` in degree `0`, and
`T[w] = β(w) · ([w] - T(∂[w]))` in degree `k + 1`. -/
def sdH : ∀ k : ℕ, (LinChain R V k →ₗ[R] LinChain R V (k + 1))
  | 0 => 0
  | k + 1 => Finsupp.linearCombination R
      (fun w ↦ cone (β (k + 1) w) (k + 1) (Finsupp.single w 1 - sdH k (lbd k (Finsupp.single w 1))))

@[simp]
lemma sd_zero : sd (R := R) β 0 = LinearMap.id := rfl

@[simp]
lemma sdH_zero : sdH (R := R) β 0 = 0 := rfl

@[simp]
lemma sd_zero_apply (c : LinChain R V 0) : sd β 0 c = c := rfl

lemma sd_succ_single {k : ℕ} (w : Fin (k + 2) → V) (r : R) :
    sd β (k + 1) (Finsupp.single w r) =
      r • cone (β (k + 1) w) k (sd β k (lbd k (Finsupp.single w 1))) := by
  simp [sd]

lemma sdH_succ_single {k : ℕ} (w : Fin (k + 2) → V) (r : R) :
    sdH β (k + 1) (Finsupp.single w r) =
      r • cone (β (k + 1) w) (k + 1)
        (Finsupp.single w 1 - sdH β k (lbd k (Finsupp.single w 1))) := by
  simp [sdH]

/-- Subdivision is a chain map: `∂S = S∂`. -/
lemma lbd_sd (k : ℕ) (c : LinChain R V (k + 1)) : lbd k (sd β (k + 1) c) = sd β k (lbd k c) := by
  induction k with
  | zero =>
    induction c using Finsupp.induction_linear with
    | zero => simp
    | add c d hc hd => simp only [map_add, hc, hd]
    | single w r =>
      rw [sd_succ_single, map_smul, lbd_cone_zero, sd_zero_apply, sd_zero_apply, aug_lbd,
        Finsupp.single_zero, sub_zero, ← map_smul, Finsupp.smul_single_one]
  | succ k ih =>
    induction c using Finsupp.induction_linear with
    | zero => simp
    | add c d hc hd => simp only [map_add, hc, hd]
    | single w r =>
      rw [sd_succ_single, map_smul, lbd_cone_succ, ih, lbd_lbd, map_zero, map_zero, sub_zero,
        ← map_smul, ← map_smul, Finsupp.smul_single_one]

/-- The subdivision homotopy in degree `0`: `∂T = 1 - S` (both sides vanish). -/
lemma lbd_sdH_zero (c : LinChain R V 0) : sdH β 0 c = 0 := rfl

/-- One step of the proof of `∂T + T∂ = 1 - S`, assuming that `∂([w] - T∂[w]) = S∂[w]`
for the generators `[w]` of degree `k + 1`. -/
lemma lbd_sdH_of_key (k : ℕ) (key : ∀ w : Fin (k + 2) → V, lbd k (Finsupp.single w (1 : R) -
      sdH β k (lbd k (Finsupp.single w 1))) = sd β k (lbd k (Finsupp.single w 1)))
    (c : LinChain R V (k + 1)) :
    lbd (k + 1) (sdH β (k + 1) c) + sdH β k (lbd k c) = c - sd β (k + 1) c := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd =>
    simp only [map_add]
    calc _ = (lbd (k + 1) (sdH β (k + 1) c) + sdH β k (lbd k c)) +
          (lbd (k + 1) (sdH β (k + 1) d) + sdH β k (lbd k d)) := by abel
      _ = _ := by rw [hc, hd]; abel
  | single w r =>
    rw [sdH_succ_single, map_smul, lbd_cone_succ, key, sd_succ_single,
      ← Finsupp.smul_single_one w r, map_smul, map_smul]
    simp only [smul_sub]
    abel

/-- **The subdivision homotopy**: `∂T + T∂ = 1 - S` in degree `k + 1`. -/
lemma lbd_sdH (k : ℕ) (c : LinChain R V (k + 1)) :
    lbd (k + 1) (sdH β (k + 1) c) + sdH β k (lbd k c) = c - sd β (k + 1) c := by
  induction k with
  | zero => exact lbd_sdH_of_key β 0 (fun w ↦ by simp) c
  | succ j ih =>
    refine lbd_sdH_of_key β (j + 1) (fun w ↦ ?_) c
    have h := ih (lbd (j + 1) (Finsupp.single w 1))
    rw [lbd_lbd, map_zero, add_zero] at h
    rw [map_sub, h]
    abel

/-- Naturality of subdivision for maps of vertex sets compatible with the barycentres. -/
lemma lmap_sd {V' : Type w} (β' : ∀ k : ℕ, (Fin (k + 1) → V') → V') (f : V → V')
    (hf : ∀ k (w : Fin (k + 1) → V), f (β k w) = β' k (f ∘ w)) (k : ℕ) (c : LinChain R V k) :
    lmap f k (sd β k c) = sd β' k (lmap f k c) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    induction c using Finsupp.induction_linear with
    | zero => simp
    | add c d hc hd => simp only [map_add, hc, hd]
    | single w r =>
      rw [sd_succ_single, lmap_single, sd_succ_single, map_smul, lmap_cone, ih, lmap_lbd,
        lmap_single, hf]

/-- Naturality of the subdivision homotopy for maps of vertex sets compatible with the
barycentres. -/
lemma lmap_sdH {V' : Type w} (β' : ∀ k : ℕ, (Fin (k + 1) → V') → V') (f : V → V')
    (hf : ∀ k (w : Fin (k + 1) → V), f (β k w) = β' k (f ∘ w)) (k : ℕ) (c : LinChain R V k) :
    lmap f (k + 1) (sdH β k c) = sdH β' k (lmap f k c) := by
  induction k with
  | zero => simp
  | succ k ih =>
    induction c using Finsupp.induction_linear with
    | zero => simp
    | add c d hc hd => simp only [map_add, hc, hd]
    | single w r =>
      rw [sdH_succ_single, lmap_single, sdH_succ_single, map_smul, lmap_cone, map_sub, ih,
        lmap_lbd, lmap_single, hf]

end Subdivision

end Morse.Homology
