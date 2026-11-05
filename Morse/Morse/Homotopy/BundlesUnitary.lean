import Mathlib
import Morse.Homotopy.BundleHomotopy
import Morse.Homotopy.Spheres
import Morse.Chapter12.SUMinimal

/-!
# The bundles of Bott periodicity for the unitary group

Milnor, *Morse Theory*, §23, pp. 128–129 (Lemma 23.4).

## Milnor's text, paraphrased

* (p. 128) "`U(m+1)` acts transitively on the unit sphere `S^{2m+1} ⊂ ℂ^{m+1}`, with isotropy
  group `U(m)`; so `U(m+1)/U(m) ≅ S^{2m+1}`, and from the exact homotopy sequence of the
  fibration `U(m) → U(m+1) → S^{2m+1}` together with `πᵢ S^{2m+1} = 0` for `i ≤ 2m`, the inclusion
  `U(m) → U(m+1)` induces isomorphisms `πᵢ U(m) ≅ πᵢ U(m+1)` for `i < 2m`."
* **Lemma 23.4** (p. 128). "`πᵢ G_m(ℂ^{2m}) ≅ πᵢ₋₁ U(m)` for `1 ≤ i ≤ 2m`. Furthermore
  `πᵢ₋₁ U(m) ≅ πᵢ₋₁ U(m+1) ≅ πᵢ₋₁ U(m+2) ≅ ⋯` for `i ≤ 2m`, and `πⱼ U(m) ≅ πⱼ SU(m)` for
  `j ≠ 1`." *Proof*: `πᵢ U(m) → πᵢ U(2m)` is onto for `i ≤ 2m` and one-to-one for `i < 2m`, so the
  exact sequence of `U(m) → U(2m) → U(2m)/U(m)` gives `πᵢ(U(2m)/U(m)) = 0` for `i ≤ 2m`; the
  exact sequence of `U(m) → U(2m)/U(m) → G_m(ℂ^{2m}) = U(2m)/(U(m) × U(m))` then gives the
  first assertion.

## What is formalized

The generic results of `Morse/Homotopy/BundleHomotopy.lean` are parametrized by the connectivity
of the unit spheres `V₁(𝕜ⁿ)`, `Morse.Homotopy.SphereConnected 𝕜 d`. Here:

* `Morse.Homotopy.stiefelSphere`: **`V₁(𝕜^ι)` is the unit sphere of `𝕜^ι`**, `F ↦` its column.
* `Morse.Homotopy.sphereConnected_complex`: **`SphereConnected ℂ 2`**, i.e.
  `πᵢ(S^{2n-1}) = 0` for `i < 2n − 1`, transported from `Morse/Homotopy/Spheres.lean`.
* `Morse.Homotopy.isLocallyTrivial_sphereOrbit`: **`U(m) → U(m+1) → S^{2m+1}`** is locally
  trivial, with the honest unit sphere of `𝕜^{m+1}` as base (for every `RCLike 𝕜`).
* Lemma 23.4, concretely for `ℂ`:
  `Morse.Homotopy.bijective_homotopyGroupMap_unitaryIncl_complex` (**`πᵢ U(m) → πᵢ U(m+k)`
  bijective for `i < 2m`**), `Morse.Homotopy.surjective_homotopyGroupMap_unitaryIncl_complex`
  (onto for `i ≤ 2m`), `Morse.Homotopy.subsingleton_pi_stiefel_complex` (**`V_k(ℂⁿ)` is
  `2(n − k)`-connected**; for `V_m(ℂ^{2m}) = U(2m)/U(m)` this is Milnor's `πᵢ = 0`, `i ≤ 2m`),
  and `Morse.Homotopy.grassmannianEquiv_complex`,
  `Morse.Homotopy.nonempty_mulEquiv_grassmannian_complex`
  (**`π_{j+1} G_m(ℂ^{2m}) ≅ π_j U(m)` for `j + 1 ≤ 2m`**, as a bijection, and as a group
  isomorphism for `j ≥ 1`).
* **The bridge to Lemma 23.1 and Theorem 22.1.** Milnor's `G_m(ℂ^{2m})` of Lemma 23.1 is
  `Morse.grassmannian ι m` (Hermitian projections of trace `m` on `ℂ^ι`, `|ι| = 2m`), which is
  the same set as `Morse.Homotopy.Grassmannian ℂ ι m`. Reindexing `ι ≃ Fin m ⊕ Fin m`
  (`Morse.Homotopy.grassCongr`) and moving the base point by the transitive action of the unitary
  group (`Morse.Homotopy.grassMove`) give `Morse.Homotopy.grassmannianPiEquiv` and
  `Morse.Homotopy.nonempty_mulEquiv_grassmannianPi`: **`π_{j+1}(Morse.grassmannian ι m, P) ≅
  π_j U(m)` for every `P` and `j + 1 ≤ 2m`**, and through Lemma 23.1 (`Morse.lemma_23_1`)
  `Morse.Homotopy.minVelPiEquiv`, `Morse.Homotopy.nonempty_mulEquiv_minVelPi`: the same for the
  space `Morse.minVel ι` of initial velocities of minimal geodesics, the space Theorem 22.1 is
  about.

## What Milnor leaves implicit

* That the coset spaces are the concrete spaces: Milnor identifies `U(m+1)/U(m)` with
  `S^{2m+1}` and `U(2m)/U(m) × U(m)` with `G_m(ℂ^{2m})` by "(compare Steenrod §7)". Here the
  bundles are built on the concrete spaces directly (orbit maps with explicit local sections), so
  no coset space appears.
* The base points. Milnor's isomorphisms are base-point free; here the Grassmannian is
  homogeneous (`Morse.Homotopy.exists_unitary_smul_grassBase`), so every base point is moved to
  `P₀` by a homeomorphism, and `U(m)` is taken at `1`.
* `i = 1`: `π₁ G_m ≅ π₀ U(m)` is a bijection of pointed sets (both are trivial); the group
  isomorphism is for `i ≥ 2`.

## Also proved here

* `Morse.Homotopy.bijective_homotopyGroupMap_suInclC`: **`πⱼ SU(n) ≅ πⱼ U(n)` for `j ≥ 2`** (the
  last clause of Lemma 23.4), from the trivial bundle `SU(n) → U(n) → S¹`
  (`Morse.Homotopy.unitaryProd`: `U(n) ≅ S¹ × SU(n)`, `g ↦ (det g, g D(det g)⁻¹)`,
  `D(z) = diag(z, 1, …, 1)`) and **`πᵢ(S¹) = 0` for `i ≥ 2`**
  (`Morse.Homotopy.subsingleton_pi_circle`), the exact sequence of the covering
  `ℤ → ℝ → S¹`, `t ↦ e^{it}` (`Morse.Homotopy.isLocallyTrivial_circleExp`, from Mathlib's
  `Circle.isCoveringMap_exp`). Milnor's `j = 0` (both groups connected) is not formalized.
* `Morse.Homotopy.bijective_homotopyGroupMap_clopen`: the inclusion of a clopen set containing the
  base point is bijective on `π_N`, `N ≠ ∅` (so discrete spaces have trivial higher homotopy
  groups, `Morse.Homotopy.subsingleton_homotopyGroup_discrete`).
* `Morse.Homotopy.IsLocallyTrivial.homeomorph_comp`,
  `Morse.Homotopy.isLocallyTrivial_of_homeomorph`,
  `Morse.Homotopy.IsCoveringMap.isLocallyTrivial`: local triviality under a homeomorphism of the
  base, for globally trivial maps, and for covering maps with homeomorphic fibres.
-/

open Matrix Set Function Topology Metric
open scoped unitInterval Topology.Homotopy

noncomputable section

namespace Morse.Homotopy

/-! ### Transport of homotopy groups -/

section Transport

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- A homeomorphism carrying `x` to `y` identifies `πₙ(X, x)` with `πₙ(Y, y)`. -/
def piEquivOfHomeomorph (h : X ≃ₜ Y) {x : X} {y : Y} (hxy : h x = y) (n : ℕ) :
    π_ n X x ≃ π_ n Y y :=
  (homotopyGroupEquivOfHomotopyEquiv h.toHomotopyEquiv x).trans
    (Equiv.cast (congrArg (fun u => π_ n Y u) hxy))

/-- The same as groups. -/
theorem nonempty_mulEquiv_of_homeomorph (h : X ≃ₜ Y) {x : X} {y : Y} (hxy : h x = y) (n : ℕ) :
    Nonempty (π_ (n + 1) X x ≃* π_ (n + 1) Y y) := by
  subst hxy
  exact ⟨MulEquiv.ofBijective (homotopyGroupHom (N := Fin (n + 1)) (h : C(X, Y)) x)
    (bijective_homotopyGroupMap_homeomorph (N := Fin (n + 1)) h x)⟩

end Transport

/-- **Local triviality is invariant under homeomorphisms of the base.** -/
theorem IsLocallyTrivial.homeomorph_comp {E B B' F : Type*} [TopologicalSpace E]
    [TopologicalSpace B] [TopologicalSpace B'] [TopologicalSpace F] {p : E → B}
    (hp : IsLocallyTrivial p F) (h : B ≃ₜ B') : IsLocallyTrivial (h ∘ p) F := by
  intro b'
  obtain ⟨U, hU, hb, φ, hφ⟩ := hp (h.symm b')
  have hpre : (h ∘ p) ⁻¹' (h '' U) = p ⁻¹' U := by
    rw [Set.preimage_comp, h.preimage_image]
  refine ⟨h '' U, h.isOpenMap U hU, ⟨h.symm b', hb, h.apply_symm_apply b'⟩,
    ((Homeomorph.setCongr hpre).trans φ).trans ((h.image U).prodCongr (Homeomorph.refl F)),
    fun x => ?_⟩
  change h ((φ ⟨x, _⟩).1 : B) = h (p x)
  rw [hφ]

variable {𝕜 : Type*} [RCLike 𝕜]

/-! ### `V₁(𝕜ⁿ)` is the unit sphere -/

section Sphere

variable {ι : Type*} [Fintype ι]

theorem mem_stiefel_fin_one {F : Matrix ι (Fin 1) 𝕜} :
    F ∈ Stiefel 𝕜 ι (Fin 1) ↔ ∑ i, star (F i 0) * F i 0 = 1 := by
  rw [mem_stiefel]
  constructor
  · intro h
    simpa [Matrix.mul_apply] using congrFun (congrFun h 0) 0
  · intro h
    ext a b
    rw [Subsingleton.elim a 0, Subsingleton.elim b 0]
    simpa [Matrix.mul_apply] using h

theorem sum_star_mul_self_euclidean (x : EuclideanSpace 𝕜 ι) :
    ∑ i, star (x i) * x i = ((‖x‖ ^ 2 : ℝ) : 𝕜) := by
  rw [EuclideanSpace.norm_sq_eq, RCLike.ofReal_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [RCLike.star_def, RCLike.conj_mul]
  push_cast
  rfl

theorem norm_eq_one_iff_sum_star_mul_self (x : EuclideanSpace 𝕜 ι) :
    ‖x‖ = 1 ↔ ∑ i, star (x i) * x i = 1 := by
  rw [sum_star_mul_self_euclidean]
  constructor
  · intro h
    rw [h]
    simp
  · intro h
    have h' : ‖x‖ ^ 2 = 1 := by exact_mod_cast h
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg x) two_ne_zero).1 h'

theorem stiefel_col_mem_sphere (F : Stiefel 𝕜 ι (Fin 1)) :
    (WithLp.toLp 2 fun i => F.1 i 0 : EuclideanSpace 𝕜 ι) ∈ sphere (0 : EuclideanSpace 𝕜 ι) 1 :=
  mem_sphere_zero_iff_norm.2 ((norm_eq_one_iff_sum_star_mul_self _).2
    (mem_stiefel_fin_one.1 F.2))

theorem sphere_mem_stiefel (x : sphere (0 : EuclideanSpace 𝕜 ι) 1) :
    (Matrix.of fun i (_ : Fin 1) => (x : EuclideanSpace 𝕜 ι) i) ∈ Stiefel 𝕜 ι (Fin 1) :=
  mem_stiefel_fin_one.2 ((norm_eq_one_iff_sum_star_mul_self _).1
    (mem_sphere_zero_iff_norm.1 x.2))

variable (𝕜 ι) in
/-- **`V₁(𝕜^ι)` is the unit sphere of `𝕜^ι`**: a one-frame is a unit vector. -/
def stiefelSphere : Stiefel 𝕜 ι (Fin 1) ≃ₜ sphere (0 : EuclideanSpace 𝕜 ι) 1 where
  toFun F := ⟨WithLp.toLp 2 fun i => F.1 i 0, stiefel_col_mem_sphere F⟩
  invFun x := ⟨Matrix.of fun i _ => (x : EuclideanSpace 𝕜 ι) i, sphere_mem_stiefel x⟩
  left_inv F := Subtype.ext (by
    ext i a
    rw [Subsingleton.elim a 0]
    rfl)
  right_inv x := Subtype.ext rfl
  continuous_toFun := Continuous.subtype_mk ((PiLp.continuous_toLp 2 _).comp
    (continuous_pi fun i => continuous_subtype_val.matrix_elem i 0)) _
  continuous_invFun := Continuous.subtype_mk (continuous_matrix fun i _ =>
    (PiLp.continuous_apply 2 _ i).comp continuous_subtype_val) _

/-- **`SphereConnected ℂ 2`**: `πᵢ(V₁(ℂⁿ)) = πᵢ(S^{2n-1}) = 0` for `i < 2n − 1`. -/
theorem sphereConnected_complex : SphereConnected ℂ 2 := fun n i hi x =>
  subsingleton_homotopyGroup_of_homeomorph (stiefelSphere ℂ (Fin n)) x
    (subsingleton_pi_sphere_complex (by omega) _)

end Sphere

/-! ### The bundle `U(m) → U(m+1) → S^{2m+1}` -/

section SphereBundle

variable (𝕜) in
/-- The orbit map `U(m + 1) → S^{d(m+1)-1}`, `g ↦ g e_{m+1}` (the last column of `g`), with the
unit sphere of `𝕜^{m+1}` as target. -/
def sphereOrbit (m : ℕ) :
    C(unitaryGroup (Fin m ⊕ Fin 1) 𝕜, sphere (0 : EuclideanSpace 𝕜 (Fin m ⊕ Fin 1)) 1) :=
  (stiefelSphere 𝕜 (Fin m ⊕ Fin 1) : C(_, _)).comp (unitaryOrbitC m 1)

/-- **`U(m) → U(m + 1) → S^{d(m+1)-1}` is locally trivial** (Milnor p. 128:
`U(m+1)/U(m) ≅ S^{2m+1}`), with fibre `U(m)`. -/
theorem isLocallyTrivial_sphereOrbit (m : ℕ) :
    IsLocallyTrivial (sphereOrbit 𝕜 m) (unitaryGroup (Fin m) 𝕜) :=
  (isLocallyTrivial_unitaryOrbit (𝕜 := 𝕜) (ι₁ := Fin m) (κ₂ := Fin 1)).homeomorph_comp
    (stiefelSphere 𝕜 (Fin m ⊕ Fin 1))

end SphereBundle

/-! ### Lemma 23.4 for `ℂ` -/

section Unitary

variable {m k : ℕ}

/-- **Stability** (Milnor, Lemma 23.4): the inclusion `U(m) → U(m + k)`, `S ↦ diag(S, I_k)`,
induces bijections `πᵢ U(m) → πᵢ U(m + k)` for `i < 2m`. -/
theorem bijective_homotopyGroupMap_unitaryIncl_complex {i : ℕ} (hi : i < 2 * m)
    (S : unitaryGroup (Fin m) ℂ) :
    Bijective (homotopyGroupMap (N := Fin i) (unitaryInclC (𝕜 := ℂ) m k) S) :=
  bijective_homotopyGroupMap_unitaryIncl sphereConnected_complex (by omega) S

/-- **Stability, the top degree** (Milnor p. 129): `π_{2m} U(m) → π_{2m} U(m + k)` is onto (and
so is `πᵢ` for every `i ≤ 2m`). -/
theorem surjective_homotopyGroupMap_unitaryIncl_complex {i : ℕ} (hi : i ≤ 2 * m)
    (S : unitaryGroup (Fin m) ℂ) :
    Surjective (homotopyGroupMap (N := Fin i) (unitaryInclC (𝕜 := ℂ) m k) S) :=
  surjective_homotopyGroupMap_unitaryIncl sphereConnected_complex (by omega) S

/-- **`V_k(ℂⁿ)` is `2(n − k)`-connected**: `πᵢ V_k(ℂⁿ) = 0` for `i ≤ 2(n − k)`. For
`V_m(ℂ^{2m}) = U(2m)/U(m)` this is Milnor's `πᵢ(U(2m)/U(m)) = 0` for `i ≤ 2m` (p. 129). -/
theorem subsingleton_pi_stiefel_complex {n i : ℕ} (hkn : k ≤ n) (hi : i ≤ 2 * (n - k))
    (x : Stiefel ℂ (Fin n) (Fin k)) : Subsingleton (π_ i (Stiefel ℂ (Fin n) (Fin k)) x) :=
  subsingleton_pi_stiefel sphereConnected_complex k n hkn i (by omega) x

/-- **Lemma 23.4** (Milnor p. 128): **`πᵢ G_m(ℂ^{2m}) ≅ πᵢ₋₁ U(m)` for `1 ≤ i ≤ 2m`**, written
with `i = j + 1`; `G_m(ℂ^{2m})` at the base point `P₀ = F₀F₀ᴴ`, `U(m)` at `1`. -/
def grassmannianEquiv_complex {j : ℕ} (hj : j + 1 ≤ 2 * m) :
    π_ (j + 1) (Grassmannian ℂ (Fin m ⊕ Fin m) m) (grassBase ℂ (Fin m) m) ≃
      π_ j (unitaryGroup (Fin m) ℂ) 1 :=
  grassmannianEquiv (m' := m) sphereConnected_complex (by omega)

/-- **Lemma 23.4 as a group isomorphism**: `π_{j+2} G_m(ℂ^{2m}) ≅ π_{j+1} U(m)` for
`j + 2 ≤ 2m`. -/
theorem nonempty_mulEquiv_grassmannian_complex {j : ℕ} (hj : j + 2 ≤ 2 * m) :
    Nonempty (π_ (j + 2) (Grassmannian ℂ (Fin m ⊕ Fin m) m) (grassBase ℂ (Fin m) m) ≃*
      π_ (j + 1) (unitaryGroup (Fin m) ℂ) 1) :=
  nonempty_mulEquiv_grassmannian (m' := m) sphereConnected_complex (by omega)

end Unitary

/-! ### Reindexing and homogeneity of the Grassmannian -/

section GrassCongr

variable {ι ι' : Type*} [Fintype ι] [Fintype ι'] [DecidableEq ι] [DecidableEq ι'] {k : ℕ}

omit [DecidableEq ι] [DecidableEq ι'] in
theorem reindex_mem_grassmannian (e : ι ≃ ι') {P : Matrix ι ι 𝕜}
    (hP : P ∈ Grassmannian 𝕜 ι k) : reindex e e P ∈ Grassmannian 𝕜 ι' k := by
  obtain ⟨h1, h2, h3⟩ := hP
  refine ⟨by rw [conjTranspose_reindex, h1], ?_, ?_⟩
  · rw [reindex_apply, submatrix_mul_equiv _ _ _ e.symm, h2]
  · rw [← h3, reindex_apply, trace, trace]
    exact Equiv.sum_comp e.symm fun i => P i i

/-- **Reindexing the coordinates** is a homeomorphism of Grassmannians. -/
def grassCongr (e : ι ≃ ι') : Grassmannian 𝕜 ι k ≃ₜ Grassmannian 𝕜 ι' k where
  toFun P := ⟨reindex e e P.1, reindex_mem_grassmannian e P.2⟩
  invFun P := ⟨reindex e.symm e.symm P.1, reindex_mem_grassmannian e.symm P.2⟩
  left_inv P := Subtype.ext (by simp)
  right_inv P := Subtype.ext (by simp)
  continuous_toFun := Continuous.subtype_mk
    (continuous_subtype_val.matrix_submatrix _ _) _
  continuous_invFun := Continuous.subtype_mk
    (continuous_subtype_val.matrix_submatrix _ _) _

end GrassCongr

section Homogeneous

variable {ι₁ : Type*} [Fintype ι₁] [DecidableEq ι₁] {m : ℕ}

/-- **The Grassmannian is homogeneous**: a homeomorphism (the action of a unitary matrix) moving
a given `P` to the base point `P₀`. -/
def grassMove (P : Grassmannian 𝕜 (ι₁ ⊕ Fin m) m) :
    Grassmannian 𝕜 (ι₁ ⊕ Fin m) m ≃ₜ Grassmannian 𝕜 (ι₁ ⊕ Fin m) m :=
  Homeomorph.smul (exists_unitary_smul_grassBase P).choose⁻¹

theorem grassMove_self (P : Grassmannian 𝕜 (ι₁ ⊕ Fin m) m) :
    grassMove P P = grassBase 𝕜 ι₁ m := by
  exact inv_smul_eq_iff.2 (exists_unitary_smul_grassBase P).choose_spec.symm

end Homogeneous

/-! ### The bridge to Milnor's `G_m(ℂ^{2m})` of Lemma 23.1 -/

section Bridge

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ}

/-- Milnor's Grassmannian of Lemma 23.1 is the Grassmannian of the bundle. -/
theorem grassmannian_eq_Grassmannian : Morse.grassmannian ι m = Grassmannian ℂ ι m := rfl

omit [DecidableEq ι] in
theorem card_eq_of_card_eq_two_mul (hcard : Fintype.card ι = 2 * m) :
    Fintype.card ι = Fintype.card (Fin m ⊕ Fin m) := by
  rw [hcard, Fintype.card_sum, Fintype.card_fin]
  ring

/-- **Milnor's `G_m(ℂ^{2m})` (`Morse.grassmannian ι m`, `|ι| = 2m`) at any point `P`, moved to the
base point `P₀` of `G_m(ℂ^{Fin m ⊕ Fin m})`**: reindexing followed by a unitary motion. -/
def grassmannianToBase (hcard : Fintype.card ι = 2 * m) (P : Morse.grassmannian ι m) :
    Morse.grassmannian ι m ≃ₜ Grassmannian ℂ (Fin m ⊕ Fin m) m :=
  let e : Grassmannian ℂ ι m ≃ₜ Grassmannian ℂ (Fin m ⊕ Fin m) m :=
    grassCongr (Fintype.equivOfCardEq (card_eq_of_card_eq_two_mul hcard))
  e.trans (grassMove (e P))

theorem grassmannianToBase_self (hcard : Fintype.card ι = 2 * m) (P : Morse.grassmannian ι m) :
    grassmannianToBase hcard P P = grassBase ℂ (Fin m) m :=
  grassMove_self _

/-- **Lemma 23.4 for Milnor's `G_m(ℂ^{2m})`** (`Morse.grassmannian ι m`, `|ι| = 2m`), at any
base point `P`: `π_{j+1}(G_m(ℂ^{2m}), P) ≅ π_j(U(m), 1)` for `j + 1 ≤ 2m`, i.e.
`πᵢ G_m(ℂ^{2m}) ≅ πᵢ₋₁ U(m)` for `1 ≤ i ≤ 2m`. -/
def grassmannianPiEquiv (hcard : Fintype.card ι = 2 * m) (P : Morse.grassmannian ι m) {j : ℕ}
    (hj : j + 1 ≤ 2 * m) :
    π_ (j + 1) (Morse.grassmannian ι m) P ≃ π_ j (unitaryGroup (Fin m) ℂ) 1 :=
  (piEquivOfHomeomorph (grassmannianToBase hcard P) (grassmannianToBase_self hcard P) _).trans
    (grassmannianEquiv_complex hj)

/-- **Lemma 23.4 for Milnor's `G_m(ℂ^{2m})`, as groups**: `π_{j+2}(G_m(ℂ^{2m}), P) ≅
π_{j+1}(U(m), 1)` for `j + 2 ≤ 2m`. -/
theorem nonempty_mulEquiv_grassmannianPi (hcard : Fintype.card ι = 2 * m)
    (P : Morse.grassmannian ι m) {j : ℕ} (hj : j + 2 ≤ 2 * m) :
    Nonempty (π_ (j + 2) (Morse.grassmannian ι m) P ≃* π_ (j + 1) (unitaryGroup (Fin m) ℂ) 1) := by
  obtain ⟨e₁⟩ := nonempty_mulEquiv_of_homeomorph (grassmannianToBase hcard P)
    (grassmannianToBase_self hcard P) (j + 1)
  obtain ⟨e₂⟩ := nonempty_mulEquiv_grassmannian_complex hj
  exact ⟨e₁.trans e₂⟩

/-- **The space of minimal geodesics from `I` to `−I` in `SU(2m)`** (as initial velocities,
`Morse.minVel ι`, the space of Theorem 22.1 and Lemma 23.1): `π_{j+1}(minVel, A) ≅ π_j(U(m))`
for `j + 1 ≤ 2m`, through Lemma 23.1 (`Morse.lemma_23_1`) and Lemma 23.4. -/
def minVelPiEquiv (hcard : Fintype.card ι = 2 * m) (A : Morse.minVel ι) {j : ℕ}
    (hj : j + 1 ≤ 2 * m) : π_ (j + 1) (Morse.minVel ι) A ≃ π_ j (unitaryGroup (Fin m) ℂ) 1 :=
  (piEquivOfHomeomorph (Morse.lemma_23_1 hcard) rfl _).trans
    (grassmannianPiEquiv hcard _ hj)

/-- The same as groups, for `j + 2 ≤ 2m`. -/
theorem nonempty_mulEquiv_minVelPi (hcard : Fintype.card ι = 2 * m) (A : Morse.minVel ι)
    {j : ℕ} (hj : j + 2 ≤ 2 * m) :
    Nonempty (π_ (j + 2) (Morse.minVel ι) A ≃* π_ (j + 1) (unitaryGroup (Fin m) ℂ) 1) := by
  obtain ⟨e₁⟩ := nonempty_mulEquiv_of_homeomorph (Morse.lemma_23_1 hcard) rfl (j + 1)
  obtain ⟨e₂⟩ := nonempty_mulEquiv_grassmannianPi hcard (Morse.lemma_23_1 hcard A) hj
  exact ⟨e₁.trans e₂⟩

end Bridge

/-! ### Clopen sets, discrete spaces and the circle -/

section Clopen

variable {X : Type*} [TopologicalSpace X] {s : Set X} {x : X}

theorem range_subset_of_isClopen (hs : IsClopen s) {A : Type*} [TopologicalSpace A]
    [PreconnectedSpace A] (f : C(A, X)) (a : A) (ha : f a ∈ s) : range f ⊆ s :=
  (isPreconnected_range f.continuous).subset_isClopen hs ⟨f a, mem_range_self a, ha⟩

variable {N : Type*} [Nonempty N]

theorem zero_mem_cube_boundary : (fun _ => 0 : I^N) ∈ Cube.boundary N :=
  ⟨Classical.arbitrary N, Or.inl rfl⟩

theorem genLoop_mem_of_isClopen (hs : IsClopen s) (hx : x ∈ s) (γ : Ω^ N X x) (y : I^N) :
    γ y ∈ s :=
  range_subset_of_isClopen hs γ.1 _ (by
    change γ (fun _ => 0) ∈ s
    rw [GenLoop.boundary γ _ zero_mem_cube_boundary]
    exact hx) (mem_range_self y)

/-- A generalized loop at `x ∈ s`, `s` clopen, lies in `s`. -/
def genLoopRestrict (hs : IsClopen s) (hx : x ∈ s) (γ : Ω^ N X x) : Ω^ N s ⟨x, hx⟩ :=
  ⟨⟨fun y => ⟨γ y, genLoop_mem_of_isClopen hs hx γ y⟩, γ.1.continuous.subtype_mk _⟩,
    fun y hy => Subtype.ext (γ.2 y hy)⟩

/-- **The path component of a base point carries all higher homotopy groups**: the inclusion of
a clopen set `s ∋ x` induces bijections `π_N(s, x) → π_N(X, x)` for `N` nonempty. -/
theorem bijective_homotopyGroupMap_clopen (hs : IsClopen s) (hx : x ∈ s) :
    Bijective (homotopyGroupMap (N := N) (⟨Subtype.val, continuous_subtype_val⟩ : C(s, X))
      ⟨x, hx⟩) := by
  refine ⟨fun a b hab => ?_, fun c => ?_⟩
  · induction a using Quotient.inductionOn with
    | h a =>
    induction b using Quotient.inductionOn with
    | h b =>
    obtain ⟨H⟩ := Quotient.exact hab
    have hmem : ∀ q, H q ∈ s := fun q => range_subset_of_isClopen hs H.toContinuousMap
      (0, fun _ => 0) (by
        change H (0, fun _ => 0) ∈ s
        rw [H.apply_zero]
        exact (a _).2) (mem_range_self q)
    refine Quotient.sound ⟨?_⟩
    exact
      { toFun := fun q => ⟨H q, hmem q⟩
        continuous_toFun := H.continuous.subtype_mk _
        map_zero_left := fun y => Subtype.ext (H.apply_zero y)
        map_one_left := fun y => Subtype.ext (H.apply_one y)
        prop' := fun t y hy => Subtype.ext (H.prop' t y hy) }
  · induction c using Quotient.inductionOn with
    | h c =>
    exact ⟨⟦genLoopRestrict hs hx c⟧, congrArg _ (GenLoop.ext _ _ fun _ => rfl)⟩

end Clopen

/-- **A covering map whose fibres are all homeomorphic to `F` is locally trivial** with fibre
`F`. -/
theorem IsCoveringMap.isLocallyTrivial {E B F : Type*} [TopologicalSpace E] [TopologicalSpace B]
    [TopologicalSpace F] {f : E → B} (hf : IsCoveringMap f)
    (hF : ∀ b, Nonempty (f ⁻¹' {b} ≃ₜ F)) : IsLocallyTrivial f F := fun b => by
  obtain ⟨-, U, hb, hU, -, H, hH⟩ := hf b
  obtain ⟨h⟩ := hF b
  exact ⟨U, hU, hb, H.trans ((Homeomorph.refl U).prodCongr h), fun x => hH x⟩

/-- The fibre of `t ↦ e^{it}` over `e^{iθ}` is `θ + 2πℤ`. -/
def circleFibreEquiv (θ : ℝ) : ℤ ≃ Circle.exp ⁻¹' {Circle.exp θ} where
  toFun k := ⟨θ + k * (2 * Real.pi), Circle.exp_eq_exp.2 ⟨k, rfl⟩⟩
  invFun t := (Circle.exp_eq_exp.1 t.2).choose
  left_inv k := by
    have h := (Circle.exp_eq_exp.1 (Circle.exp_eq_exp.2 ⟨k, rfl⟩ :
      Circle.exp (θ + k * (2 * Real.pi)) = Circle.exp θ)).choose_spec
    have hπ : (2 * Real.pi) ≠ 0 := by positivity
    have : (k : ℝ) = (Circle.exp_eq_exp.1 (Circle.exp_eq_exp.2 ⟨k, rfl⟩ :
      Circle.exp (θ + k * (2 * Real.pi)) = Circle.exp θ)).choose := by
      have := mul_right_cancel₀ hπ (add_left_cancel h)
      exact this
    exact_mod_cast this.symm
  right_inv t := Subtype.ext (Circle.exp_eq_exp.1 t.2).choose_spec.symm

/-- **`ℝ → S¹`, `t ↦ e^{it}`, is locally trivial with fibre `ℤ`.** -/
theorem isLocallyTrivial_circleExp : IsLocallyTrivial Circle.exp ℤ :=
  IsCoveringMap.isLocallyTrivial Circle.isCoveringMap_exp fun b => by
    obtain ⟨θ, rfl⟩ := Circle.exp_surjective b
    have : DiscreteTopology (Circle.exp ⁻¹' {Circle.exp θ}) :=
      (Circle.isCoveringMap_exp (Circle.exp θ)).1
    exact ⟨(circleFibreEquiv θ).symm.toHomeomorphOfDiscrete⟩

/-- A discrete space has trivial higher homotopy groups. -/
theorem subsingleton_homotopyGroup_discrete {X : Type*} [TopologicalSpace X] [DiscreteTopology X]
    {N : Type*} [Finite N] [Nonempty N] (x : X) : Subsingleton (HomotopyGroup N X x) := by
  have : Subsingleton (HomotopyGroup N ({x} : Set X) ⟨x, rfl⟩) :=
    subsingleton_homotopyGroup_of_subsingleton _
  exact (bijective_homotopyGroupMap_clopen (isClopen_discrete {x}) rfl).surjective.subsingleton

/-- **`πᵢ(S¹) = 0` for `i ≥ 2`**: the exact sequence of `ℤ → ℝ → S¹`. -/
theorem subsingleton_pi_circle {j : ℕ} (z : Circle) : Subsingleton (π_ (j + 2) Circle z) := by
  obtain ⟨t, rfl⟩ := Circle.exp_surjective z
  have hp := isLocallyTrivial_circleExp.isSerreFibration (p := Circle.exp)
  obtain ⟨h⟩ := isLocallyTrivial_circleExp.nonempty_homeomorph_fiber (Circle.exp t)
  have hF : Subsingleton (π_ (j + 1) (fiber Circle.exp t) (fiberPt Circle.exp t)) := by
    have : DiscreteTopology (Circle.exp ⁻¹' {Circle.exp t}) := h.isEmbedding.discreteTopology
    exact subsingleton_homotopyGroup_discrete _
  exact subsingleton_pi_base hp t (subsingleton_homotopyGroup_of_contractible _) hF

/-- **A globally trivial map is locally trivial.** -/
theorem isLocallyTrivial_of_homeomorph {E B F : Type*} [TopologicalSpace E] [TopologicalSpace B]
    [TopologicalSpace F] {p : E → B} (Φ : E ≃ₜ B × F) (hΦ : ∀ x, (Φ x).1 = p x) :
    IsLocallyTrivial p F := fun b =>
  ⟨univ, isOpen_univ, mem_univ b, ((Homeomorph.setCongr (preimage_univ (f := p))).trans
    (Homeomorph.Set.univ E)).trans (Φ.trans ((Homeomorph.Set.univ B).symm.prodCongr
      (Homeomorph.refl F))), fun x => hΦ x⟩

section SpecialUnitary

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem det_mem_circle (g : unitaryGroup ι ℂ) :
    (g : Matrix ι ι ℂ).det ∈ Submonoid.unitSphere ℂ := by
  exact mem_sphere_zero_iff_norm.2 (CStarRing.norm_of_mem_unitary (det_of_mem_unitary g.2))

variable (ι) in
/-- `det : U(n) → S¹`. -/
def detCircle : C(unitaryGroup ι ℂ, Circle) :=
  ⟨fun g => ⟨(g : Matrix ι ι ℂ).det, det_mem_circle g⟩,
    continuous_subtype_val.matrix_det.subtype_mk _⟩

@[simp]
theorem coe_detCircle (g : unitaryGroup ι ℂ) :
    (detCircle ι g : ℂ) = (g : Matrix ι ι ℂ).det :=
  rfl

variable (i₀ : ι)

theorem diagonal_update_mem (z : Circle) :
    diagonal (Function.update (1 : ι → ℂ) i₀ (z : ℂ)) ∈ unitaryGroup ι ℂ := by
  rw [mem_unitaryGroup_iff', star_eq_conjTranspose, diagonal_conjTranspose, diagonal_mul_diagonal,
    ← diagonal_one]
  congr 1
  funext i
  by_cases h : i = i₀
  · subst h
    simp [← Circle.coe_inv_eq_conj]
  · simp [h]

/-- `D(z) = diag(z, 1, …, 1)`, a section of `det : U(n) → S¹`. -/
def diagCircle (z : Circle) : unitaryGroup ι ℂ :=
  ⟨diagonal (Function.update (1 : ι → ℂ) i₀ (z : ℂ)), diagonal_update_mem i₀ z⟩

theorem det_diagCircle (z : Circle) : ((diagCircle i₀ z : unitaryGroup ι ℂ) :
    Matrix ι ι ℂ).det = z := by
  simp [diagCircle, det_diagonal, Finset.prod_update_of_mem (Finset.mem_univ i₀)]

theorem continuous_diagCircle : Continuous (diagCircle (ι := ι) i₀) :=
  Continuous.subtype_mk (Continuous.matrix_diagonal
    (continuous_const.update i₀ continuous_subtype_val)) _

theorem det_mul_inv_diagCircle (g : unitaryGroup ι ℂ) :
    ((g * (diagCircle i₀ (detCircle ι g))⁻¹ : unitaryGroup ι ℂ) : Matrix ι ι ℂ).det = 1 := by
  rw [Submonoid.coe_mul, det_mul, UnitaryGroup.inv_val, star_eq_conjTranspose, det_conjTranspose,
    det_diagCircle, ← coe_detCircle, Complex.star_def, ← Circle.coe_inv_eq_conj, ← Circle.coe_mul,
    mul_inv_cancel, Circle.coe_one]

/-- **`U(n) ≅ S¹ × SU(n)`**, `g ↦ (det g, g D(det g)⁻¹)`. -/
def unitaryProd : unitaryGroup ι ℂ ≃ₜ Circle × specialUnitaryGroup ι ℂ where
  toFun g := (detCircle ι g, ⟨(g * (diagCircle i₀ (detCircle ι g))⁻¹ : unitaryGroup ι ℂ),
    mem_specialUnitaryGroup_iff.2 ⟨Subtype.coe_prop _, det_mul_inv_diagCircle i₀ g⟩⟩)
  invFun q := ⟨q.2.1, (mem_specialUnitaryGroup_iff.1 q.2.2).1⟩ * diagCircle i₀ q.1
  left_inv g := by
    change (g * (diagCircle i₀ (detCircle ι g))⁻¹) * diagCircle i₀ (detCircle ι g) = g
    exact inv_mul_cancel_right _ _
  right_inv q := by
    obtain ⟨z, s⟩ := q
    have hz : detCircle ι (⟨s.1, (mem_specialUnitaryGroup_iff.1 s.2).1⟩ * diagCircle i₀ z) = z := by
      ext
      rw [coe_detCircle, Submonoid.coe_mul, det_mul, det_diagCircle,
        (mem_specialUnitaryGroup_iff.1 s.2).2, one_mul]
    refine Prod.ext hz (Subtype.ext ?_)
    change ((⟨s.1, _⟩ * diagCircle i₀ z * (diagCircle i₀ (detCircle ι
      (⟨s.1, (mem_specialUnitaryGroup_iff.1 s.2).1⟩ * diagCircle i₀ z)))⁻¹ :
        unitaryGroup ι ℂ) : Matrix ι ι ℂ) = s.1
    rw [hz, mul_inv_cancel_right]
  continuous_toFun := by
    refine (detCircle ι).continuous.prodMk (Continuous.subtype_mk ?_ _)
    exact continuous_subtype_val.comp (continuous_id.mul
      ((continuous_diagCircle i₀).comp (detCircle ι).continuous).inv)
  continuous_invFun := by
    refine Continuous.mul ?_ ((continuous_diagCircle i₀).comp continuous_fst)
    exact (continuous_subtype_val.comp continuous_snd).subtype_mk _

/-- **`SU(n) → U(n) → S¹` is a (trivial) bundle**, `det` with fibre `SU(n)`. -/
theorem isLocallyTrivial_detCircle [Nonempty ι] :
    IsLocallyTrivial (detCircle ι) (specialUnitaryGroup ι ℂ) :=
  isLocallyTrivial_of_homeomorph (unitaryProd (Classical.arbitrary ι)) fun _ => rfl

variable (ι) in
/-- The inclusion `SU(n) → U(n)`. -/
def suInclC : C(specialUnitaryGroup ι ℂ, unitaryGroup ι ℂ) :=
  ⟨fun A => ⟨A, (mem_specialUnitaryGroup_iff.1 A.2).1⟩, continuous_subtype_val.subtype_mk _⟩

/-- `SU(n)` is the fibre of `det` through any of its points. -/
def suFibre (A : specialUnitaryGroup ι ℂ) :
    specialUnitaryGroup ι ℂ ≃ₜ fiber (detCircle ι) (suInclC ι A) where
  toFun B := ⟨suInclC ι B, Circle.ext (by
    change (B : Matrix ι ι ℂ).det = (A : Matrix ι ι ℂ).det
    rw [(mem_specialUnitaryGroup_iff.1 B.2).2, (mem_specialUnitaryGroup_iff.1 A.2).2])⟩
  invFun g := ⟨g.1.1, mem_specialUnitaryGroup_iff.2 ⟨g.1.2, by
    have := congrArg Subtype.val g.2
    change (g.1 : Matrix ι ι ℂ).det = (A : Matrix ι ι ℂ).det at this
    rw [this, (mem_specialUnitaryGroup_iff.1 A.2).2]⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.subtype_mk _).subtype_mk _
  continuous_invFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _

end SpecialUnitary

/-- **`πⱼ SU(n) ≅ πⱼ U(n)` for `j ≥ 2`** (Milnor, Lemma 23.4, last clause): the inclusion induces
bijections, by the exact sequence of `SU(n) → U(n) → S¹` and `πᵢ(S¹) = 0` for `i ≥ 2`. -/
theorem bijective_homotopyGroupMap_suInclC {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {j : ℕ} (A : specialUnitaryGroup ι ℂ) :
    Bijective (homotopyGroupMap (N := Fin (j + 2)) (suInclC ι) A) := by
  have hp := (isLocallyTrivial_detCircle (ι := ι)).isSerreFibration
  exact bijective_homotopyGroupMap_of_fiber (suFibre A) (suInclC ι) (fun _ => rfl) A rfl
    (bijective_homotopyGroupMap_fiberIncl hp _
      (subsingleton_homotopyGroup_option (subsingleton_pi_circle (j := j + 1) _))
      (subsingleton_pi_circle _))


end Morse.Homotopy
