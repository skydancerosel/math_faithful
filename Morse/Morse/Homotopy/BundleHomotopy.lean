import Mathlib
import Morse.Homotopy.Grassmannian
import Morse.Homotopy.HomotopyLifting
import Morse.Homotopy.ExactSequenceIso
import Morse.Homotopy.CellAttach

/-!
# Homotopy groups of Stiefel manifolds, unitary groups and Grassmannians

The homotopy-theoretic input of Milnor's §§23–24, for `𝕜 = ℂ` and `𝕜 = ℝ` at once. The bundles
of `Morse/Homotopy/Stiefel.lean` and `Morse/Homotopy/Grassmannian.lean` are locally trivial in
the sense of `Morse.Homotopy.IsLocallyTrivial`, hence Serre fibrations
(`Morse/Homotopy/HomotopyLifting.lean`), and their exact homotopy sequences
(`Morse/Homotopy/ExactSequenceIso.lean`) give everything else from one input: the connectivity
of the unit spheres `V₁(𝕜ⁿ) = S^{dn-1}`, `d = dim_ℝ 𝕜` (`Morse.Homotopy.SphereConnected`; it
holds for `ℂ` with `d = 2` and `ℝ` with `d = 1` by `Morse/Homotopy/Spheres.lean`:
`Morse.Homotopy.sphereConnected_complex` in `Morse/Homotopy/BundlesUnitary.lean` and
`Morse.Homotopy.sphereConnected_real` in `Morse/Homotopy/BundlesOrthogonal.lean`, where the
results below are restated concretely).

## Main results (with `c(n, k) = d(n − k) + d − 1`)

* `Morse.Homotopy.subsingleton_pi_stiefel`: **`πᵢ(V_k(𝕜ⁿ)) = 0` for `i + 1 ≤ c(n, k)`**, i.e.
  `V_k(ℂⁿ)` is `2(n − k)`-connected and `V_k(ℝⁿ)` is `(n − k − 1)`-connected. By induction on `k`
  through the bundles `V_{k-1}(𝕜^{n-1}) → V_k(𝕜ⁿ) → S^{dn-1}` (restriction to the last vector):
  in the exact sequence `πᵢ(V_{k-1}) → πᵢ(V_k) → πᵢ(S^{dn-1})` the outer groups vanish. Milnor
  (p. 129) gets the case `V_m(ℂ^{2m})`, `i ≤ 2m`, from the stability of `πᵢ U(m)` instead; the
  induction avoids the full exact sequence and gives all `n, k`.
* `Morse.Homotopy.bijective_homotopyGroupMap_unitaryIncl`: **stability**, the inclusion
  `S ↦ diag(S, I_k)` of `U(m)` in `U(m + k)` induces bijections on `πᵢ` for `i + 2 ≤ c(m + k, k)`
  and surjections for `i + 1 ≤ c(m + k, k)`: the base `V_k(𝕜^{m+k})` of the bundle
  `U(m) → U(m + k) → V_k(𝕜^{m+k})` is `c`-connected. For `ℂ`: `i < 2m` and `i ≤ 2m` (Milnor's
  Lemma 23.4); for `ℝ`: `i < m − 1` and `i ≤ m − 1`.
* `Morse.Homotopy.grassmannianEquiv` (as groups for `j ≥ 1`:
  `Morse.Homotopy.nonempty_mulEquiv_grassmannian`): **`π_{j+1}(G_m(𝕜^{m'+m})) ≅ π_j(U(m))`** for
  `j + 2 ≤ c(m' + m, m)`, through the boundary map of `U(m) → V_m(𝕜^{m'+m}) → G_m(𝕜^{m'+m})`,
  whose total space is `c`-connected. For `ℂ` and `m' = m`: `1 ≤ j + 1 ≤ 2m` (Milnor's
  Lemma 23.4).

## General facts proved here

* `Morse.Homotopy.IsLocallyTrivial.nonempty_homeomorph_fiber`: every fibre of a locally trivial
  map is homeomorphic to the model fibre.
* `Morse.Homotopy.stiefelCongr`, `Morse.Homotopy.unitaryCongr`: reindexing the coordinates is a
  homeomorphism.
-/

open Matrix Set Function Topology
open scoped unitInterval Topology.Homotopy

noncomputable section

namespace Morse.Homotopy

/-! ### General facts -/

section General

variable {E B F : Type*} [TopologicalSpace E] [TopologicalSpace B] [TopologicalSpace F]

/-- A subsingleton space has trivial homotopy groups. -/
theorem subsingleton_homotopyGroup_of_subsingleton {N : Type*} [Subsingleton E] (x : E) :
    Subsingleton (HomotopyGroup N E x) := by
  refine ⟨fun a b => ?_⟩
  induction a using Quotient.inductionOn with
  | h γ =>
  induction b using Quotient.inductionOn with
  | h γ' =>
  have : γ = γ' := by
    ext y
    exact Subsingleton.elim _ _
  rw [this]

/-- Homotopy groups are transported by homeomorphisms. -/
theorem subsingleton_homotopyGroup_of_homeomorph {N : Type*} [Finite N] (h : E ≃ₜ F) (x : E)
    (hF : Subsingleton (HomotopyGroup N F (h x))) : Subsingleton (HomotopyGroup N E x) :=
  (bijective_homotopyGroupMap_homeomorph (N := N) h x).injective.subsingleton

/-- **Every fibre of a locally trivial map is homeomorphic to the model fibre.** -/
theorem IsLocallyTrivial.nonempty_homeomorph_fiber {p : E → B} (hp : IsLocallyTrivial p F)
    (b : B) : Nonempty (p ⁻¹' {b} ≃ₜ F) := by
  obtain ⟨U, -, hb, φ, hφ⟩ := hp b
  have hmem : ∀ x : p ⁻¹' {b}, (x : E) ∈ p ⁻¹' U := fun x => by
    change p x ∈ U
    rw [show p x = b from x.2]
    exact hb
  have hsymm : ∀ y : F, φ.symm (⟨b, hb⟩, y) ∈ (Subtype.val ⁻¹' (p ⁻¹' {b}) : Set (p ⁻¹' U)) :=
    fun y => by
      change p (φ.symm (⟨b, hb⟩, y) : E) = b
      rw [← hφ, Homeomorph.apply_symm_apply]
  refine ⟨
    { toFun := fun x => (φ ⟨x, hmem x⟩).2
      invFun := fun y => ⟨φ.symm (⟨b, hb⟩, y), hsymm y⟩
      left_inv := fun x => ?_
      right_inv := fun y => by simp
      continuous_toFun := continuous_snd.comp (φ.continuous.comp
        (continuous_subtype_val.subtype_mk _))
      continuous_invFun := (continuous_subtype_val.comp (φ.symm.continuous.comp
        (continuous_const.prodMk continuous_id))).subtype_mk _ }⟩
  apply Subtype.ext
  have h1 : (φ ⟨x, hmem x⟩).1 = ⟨b, hb⟩ := Subtype.ext ((hφ _).trans x.2)
  change ((φ.symm (⟨b, hb⟩, (φ ⟨x, hmem x⟩).2)) : E) = x
  rw [← h1, Prod.mk.eta, Homeomorph.symm_apply_apply]

/-- If the inclusion `fiberIncl` of the fibre is bijective on `π_N`, so is any map identified
with it by a homeomorphism onto the fibre. -/
theorem bijective_homotopyGroupMap_of_fiber {N : Type*} [Finite N] {p : C(E, B)} {e₀ : E}
    (h : F ≃ₜ fiber p e₀) (j : C(F, E)) (hj : ∀ y, j y = h y) (y₀ : F) (hy₀ : j y₀ = e₀)
    (hb : Bijective (homotopyGroupMap (N := N) (fiberIncl p e₀) (fiberPt p e₀))) :
    Bijective (homotopyGroupMap (N := N) j y₀) := by
  have hjc : j = (fiberIncl p e₀).comp (h : C(F, fiber p e₀)) := ContinuousMap.ext hj
  have hpt : h y₀ = fiberPt p e₀ := Subtype.ext ((hj y₀).symm.trans hy₀)
  rw [hjc, homotopyGroupMap_comp]
  refine Bijective.comp ?_ (bijective_homotopyGroupMap_homeomorph (N := N) h y₀)
  change Bijective (homotopyGroupMap (N := N) (fiberIncl p e₀) (h y₀))
  rw [hpt]
  exact hb

/-- The same for surjectivity. -/
theorem surjective_homotopyGroupMap_of_fiber {N : Type*} [Finite N] {p : C(E, B)} {e₀ : E}
    (h : F ≃ₜ fiber p e₀) (j : C(F, E)) (hj : ∀ y, j y = h y) (y₀ : F) (hy₀ : j y₀ = e₀)
    (hb : Surjective (homotopyGroupMap (N := N) (fiberIncl p e₀) (fiberPt p e₀))) :
    Surjective (homotopyGroupMap (N := N) j y₀) := by
  have hjc : j = (fiberIncl p e₀).comp (h : C(F, fiber p e₀)) := ContinuousMap.ext hj
  have hpt : h y₀ = fiberPt p e₀ := Subtype.ext ((hj y₀).symm.trans hy₀)
  rw [hjc, homotopyGroupMap_comp]
  refine Surjective.comp ?_ (bijective_homotopyGroupMap_homeomorph (N := N) h y₀).surjective
  change Surjective (homotopyGroupMap (N := N) (fiberIncl p e₀) (h y₀))
  rw [hpt]
  exact hb

/-- **Connectivity of the total space from the fibre and the base**: if `πᵢ` of every fibre of a
Serre fibration and `πᵢ'` of the base vanish (`i' ≤ i`), then `πᵢ(E) = 0`. -/
theorem subsingleton_pi_total {p : C(E, B)} (hp : IsSerreFibration p) (e₀ : E) {i : ℕ}
    (hB : ∀ i' ≤ i, Subsingleton (π_ i' B (p e₀)))
    (hF : Subsingleton (π_ i (fiber p e₀) (fiberPt p e₀))) : Subsingleton (π_ i E e₀) :=
  (surjective_homotopyGroupMap_fiberIncl_of_le hp e₀ hB le_rfl).subsingleton

end General

variable {𝕜 : Type*} [RCLike 𝕜]

/-! ### Reindexing -/

section Reindex

variable {ι ι' κ κ' : Type*} [Fintype ι] [Fintype ι'] [DecidableEq κ] [DecidableEq κ']

theorem reindex_mem_stiefel (e : ι ≃ ι') (f : κ ≃ κ') {F : Matrix ι κ 𝕜}
    (hF : F ∈ Stiefel 𝕜 ι κ) : reindex e f F ∈ Stiefel 𝕜 ι' κ' := by
  rw [mem_stiefel, conjTranspose_reindex, reindex_apply, reindex_apply,
    submatrix_mul_equiv _ _ _ e.symm, mem_stiefel.1 hF, submatrix_one_equiv]

/-- **Reindexing the coordinates** is a homeomorphism of Stiefel manifolds. -/
def stiefelCongr (e : ι ≃ ι') (f : κ ≃ κ') : Stiefel 𝕜 ι κ ≃ₜ Stiefel 𝕜 ι' κ' where
  toFun F := ⟨reindex e f F.1, reindex_mem_stiefel e f F.2⟩
  invFun F := ⟨reindex e.symm f.symm F.1, reindex_mem_stiefel e.symm f.symm F.2⟩
  left_inv F := Subtype.ext (by simp)
  right_inv F := Subtype.ext (by simp)
  continuous_toFun := Continuous.subtype_mk
    (continuous_subtype_val.matrix_submatrix _ _) _
  continuous_invFun := Continuous.subtype_mk
    (continuous_subtype_val.matrix_submatrix _ _) _

/-- Stiefel manifolds of empty frames are points. -/
instance [IsEmpty κ] : Subsingleton (Stiefel 𝕜 ι κ) :=
  ⟨fun F G => Subtype.ext (by ext i k; exact isEmptyElim k)⟩

end Reindex

section ReindexUnitary

variable {ι ι' : Type*} [Fintype ι] [Fintype ι'] [DecidableEq ι] [DecidableEq ι']

theorem reindex_mem_unitaryGroup (e : ι ≃ ι') {g : Matrix ι ι 𝕜}
    (hg : g ∈ unitaryGroup ι 𝕜) : reindex e e g ∈ unitaryGroup ι' 𝕜 := by
  rw [← SetLike.mem_coe, coe_unitaryGroup_eq_stiefel] at hg ⊢
  exact reindex_mem_stiefel e e hg

/-- Reindexing the coordinates is a homeomorphism of unitary groups. -/
def unitaryCongr (e : ι ≃ ι') : unitaryGroup ι 𝕜 ≃ₜ unitaryGroup ι' 𝕜 where
  toFun g := ⟨reindex e e g.1, reindex_mem_unitaryGroup e g.2⟩
  invFun g := ⟨reindex e.symm e.symm g.1, reindex_mem_unitaryGroup e.symm g.2⟩
  left_inv g := Subtype.ext (by simp)
  right_inv g := Subtype.ext (by simp)
  continuous_toFun := Continuous.subtype_mk
    (continuous_subtype_val.matrix_submatrix _ _) _
  continuous_invFun := Continuous.subtype_mk
    (continuous_subtype_val.matrix_submatrix _ _) _

@[simp]
theorem coe_unitaryCongr (e : ι ≃ ι') (g : unitaryGroup ι 𝕜) :
    (unitaryCongr e g : Matrix ι' ι' 𝕜) = reindex e e (g : Matrix ι ι 𝕜) :=
  rfl

end ReindexUnitary

/-! ### The bundles are locally trivial, hence Serre fibrations -/

section LocallyTrivial

variable {ι₁ κ₁ κ₂ : Type*} [Fintype ι₁] [Fintype κ₁] [Fintype κ₂] [DecidableEq ι₁]
  [DecidableEq κ₁] [DecidableEq κ₂]

omit [Fintype κ₁] [DecidableEq ι₁] in
/-- **`V_{k}(𝕜ⁿ) → V_j(𝕜ⁿ)` is locally trivial** with fibre `V_{k-j}(𝕜^{n-j})`. -/
theorem isLocallyTrivial_stiefelRestrict :
    IsLocallyTrivial (stiefelRestrict 𝕜 ι₁ κ₁ κ₂) (Stiefel 𝕜 ι₁ κ₁) := fun b => by
  obtain ⟨U, hU, hb, φ, hφ⟩ := stiefelRestrict_locallyTrivial (κ₁ := κ₁) b
  exact ⟨U, hU, hb, φ, fun x => congrArg Subtype.val (hφ x)⟩

/-- **`U(ι₁ ⊕ κ₂) → V_{κ₂}`, `g ↦ g F₀`, is locally trivial** with fibre `U(ι₁)`. -/
theorem isLocallyTrivial_unitaryOrbit :
    IsLocallyTrivial (unitaryOrbit 𝕜 ι₁ κ₂) (unitaryGroup ι₁ 𝕜) := fun b => by
  obtain ⟨U, hU, hb, φ, hφ⟩ := unitaryOrbit_locallyTrivial b
  exact ⟨U, hU, hb, φ, fun x => congrArg Subtype.val (hφ x)⟩

omit [DecidableEq ι₁] in
/-- **`V_m(𝕜^{ι₁ ⊕ Fin m}) → G_m(𝕜^{ι₁ ⊕ Fin m})` is locally trivial** with fibre `U(m)`. -/
theorem isLocallyTrivial_frameSpan {m : ℕ} :
    IsLocallyTrivial (frameSpan 𝕜 (ι₁ ⊕ Fin m) m) (unitaryGroup (Fin m) 𝕜) := fun b => by
  obtain ⟨U, hU, hb, φ, hφ⟩ := frameSpan_locallyTrivial b
  exact ⟨U, hU, hb, φ, fun x => congrArg Subtype.val (hφ x)⟩

end LocallyTrivial

/-! ### Connectivity of Stiefel manifolds -/

section Connectivity

variable (𝕜) in
/-- **The connectivity of spheres**: `πᵢ(V₁(𝕜ⁿ)) = 0` for `i + 2 ≤ dn`, i.e. `πᵢ(S^{dn-1}) = 0`
for `i < dn − 1` (`d = 2` for `ℂ`, `d = 1` for `ℝ`). -/
def SphereConnected (d : ℕ) : Prop :=
  ∀ (n i : ℕ), i + 2 ≤ d * n → ∀ x : Stiefel 𝕜 (Fin n) (Fin 1),
    Subsingleton (π_ i (Stiefel 𝕜 (Fin n) (Fin 1)) x)

/-- **`πᵢ(V_k(𝕜ⁿ)) = 0` for `i + 1 ≤ d(n − k) + d − 1`**: `V_k(ℂⁿ)` is `2(n − k)`-connected,
`V_k(ℝⁿ)` is `(n − k − 1)`-connected. Induction on `k` through `V_{k-1}(𝕜^{n-1}) → V_k(𝕜ⁿ) →
S^{dn-1}`. -/
theorem subsingleton_pi_stiefel {d : ℕ} (hS : SphereConnected 𝕜 d) :
    ∀ (k n : ℕ), k ≤ n → ∀ i, i + 1 ≤ d * (n - k) + d - 1 →
      ∀ x : Stiefel 𝕜 (Fin n) (Fin k), Subsingleton (π_ i (Stiefel 𝕜 (Fin n) (Fin k)) x) := by
  intro k
  induction k with
  | zero =>
    intro n _ i _ x
    exact subsingleton_homotopyGroup_of_subsingleton x
  | succ k ih =>
    intro n hkn i hi x
    obtain ⟨n, rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    have hnk : n + 1 - (k + 1) = n - k := by omega
    rw [hnk] at hi
    have h1 : d * (n - k) ≤ d * n := Nat.mul_le_mul_left d (Nat.sub_le n k)
    have h2 : d * (n + 1) = d * n + d := by ring
    -- the total space `E' = V_{k+1}(𝕜^{n ⊕ 1})` and the restriction to the last vector
    let e : Stiefel 𝕜 (Fin n ⊕ Fin 1) (Fin k ⊕ Fin 1) ≃ₜ Stiefel 𝕜 (Fin (n + 1)) (Fin (k + 1)) :=
      stiefelCongr finSumFinEquiv finSumFinEquiv
    refine subsingleton_homotopyGroup_of_homeomorph e.symm x ?_
    let p : C(Stiefel 𝕜 (Fin n ⊕ Fin 1) (Fin k ⊕ Fin 1), Stiefel 𝕜 (Fin n ⊕ Fin 1) (Fin 1)) :=
      ⟨stiefelRestrict 𝕜 (Fin n) (Fin k) (Fin 1), continuous_stiefelRestrict⟩
    have hloc : IsLocallyTrivial p (Stiefel 𝕜 (Fin n) (Fin k)) := isLocallyTrivial_stiefelRestrict
    refine subsingleton_pi_total hloc.isSerreFibration (e.symm x) (fun i' hi' => ?_) ?_
    · -- the base is the sphere `S^{d(n+1)-1}`
      let eB : Stiefel 𝕜 (Fin n ⊕ Fin 1) (Fin 1) ≃ₜ Stiefel 𝕜 (Fin (n + 1)) (Fin 1) :=
        stiefelCongr finSumFinEquiv (Equiv.refl _)
      exact subsingleton_homotopyGroup_of_homeomorph eB _ (hS (n + 1) i' (by omega) _)
    · -- the fibre is `V_k(𝕜ⁿ)`
      obtain ⟨h⟩ := hloc.nonempty_homeomorph_fiber (p (e.symm x))
      exact subsingleton_homotopyGroup_of_homeomorph h _ (ih n (by omega) i hi _)

end Connectivity

/-! ### Stability of the homotopy groups of `U(m)` -/

section Stability

variable {m k : ℕ}

theorem unitaryOrbit_unitaryIncl {ι₁ κ₂ : Type*} [Fintype ι₁] [Fintype κ₂] [DecidableEq ι₁]
    [DecidableEq κ₂] (S : unitaryGroup ι₁ 𝕜) :
    unitaryOrbit 𝕜 ι₁ κ₂ (unitaryIncl 𝕜 ι₁ κ₂ S) = stiefelBase :=
  ((unitaryFibreHomeomorph 𝕜 ι₁ κ₂).symm S).2

/-- The orbit map `U(m + k) → V_k(𝕜^{m+k})` as a continuous map. -/
def unitaryOrbitC (m k : ℕ) :
    C(unitaryGroup (Fin m ⊕ Fin k) 𝕜, Stiefel 𝕜 (Fin m ⊕ Fin k) (Fin k)) :=
  ⟨unitaryOrbit 𝕜 (Fin m) (Fin k), continuous_unitaryOrbit⟩

/-- Milnor's embedding `U(m) → U(m + k)`, `S ↦ diag(S, I)`, as a continuous map. -/
def unitaryInclC (m k : ℕ) : C(unitaryGroup (Fin m) 𝕜, unitaryGroup (Fin m ⊕ Fin k) 𝕜) :=
  ⟨unitaryIncl 𝕜 (Fin m) (Fin k), continuous_unitaryIncl⟩

/-- The fibre of the orbit map through `diag(S, I)` is `U(m)`, included by Milnor's embedding. -/
def unitaryFibreAt (S : unitaryGroup (Fin m) 𝕜) :
    unitaryGroup (Fin m) 𝕜 ≃ₜ fiber (unitaryOrbitC (𝕜 := 𝕜) m k) (unitaryIncl 𝕜 (Fin m) (Fin k) S) :=
  (unitaryFibreHomeomorph 𝕜 (Fin m) (Fin k)).symm.trans (Homeomorph.setCongr (by
    change unitaryOrbit 𝕜 (Fin m) (Fin k) ⁻¹' {stiefelBase} =
      unitaryOrbit 𝕜 (Fin m) (Fin k) ⁻¹' {unitaryOrbit 𝕜 (Fin m) (Fin k) (unitaryIncl 𝕜 _ _ S)}
    rw [unitaryOrbit_unitaryIncl]))

theorem subsingleton_pi_unitaryOrbit_base {d : ℕ} (hS : SphereConnected 𝕜 d) {i : ℕ}
    (hi : i + 1 ≤ d * m + d - 1) (b : Stiefel 𝕜 (Fin m ⊕ Fin k) (Fin k)) :
    Subsingleton (π_ i (Stiefel 𝕜 (Fin m ⊕ Fin k) (Fin k)) b) := by
  let eB : Stiefel 𝕜 (Fin m ⊕ Fin k) (Fin k) ≃ₜ Stiefel 𝕜 (Fin (m + k)) (Fin k) :=
    stiefelCongr finSumFinEquiv (Equiv.refl _)
  refine subsingleton_homotopyGroup_of_homeomorph eB _ (subsingleton_pi_stiefel hS k (m + k)
    (by omega) i ?_ _)
  rwa [Nat.add_sub_cancel]

/-- **Stability** (Milnor, Lemma 23.4, p. 128): the inclusion `U(m) → U(m + k)`,
`S ↦ diag(S, I_k)`, induces bijections `πᵢ(U(m)) → πᵢ(U(m + k))` for `i + 2 ≤ dm + d − 1`
(`i < 2m` for `ℂ`, `i < m − 1` for `ℝ`), at every base point. -/
theorem bijective_homotopyGroupMap_unitaryIncl {d : ℕ} (hS : SphereConnected 𝕜 d) {i : ℕ}
    (hi : i + 2 ≤ d * m + d - 1) (S : unitaryGroup (Fin m) 𝕜) :
    Bijective (homotopyGroupMap (N := Fin i) (unitaryInclC (𝕜 := 𝕜) m k) S) := by
  have hloc : IsLocallyTrivial (unitaryOrbitC (𝕜 := 𝕜) m k) (unitaryGroup (Fin m) 𝕜) :=
    isLocallyTrivial_unitaryOrbit
  exact bijective_homotopyGroupMap_of_fiber (unitaryFibreAt S) (unitaryInclC m k) (fun _ => rfl) S
    rfl (bijective_homotopyGroupMap_fiberIncl_of_le hloc.isSerreFibration _
      (k := i + 1) (fun i' hi' => subsingleton_pi_unitaryOrbit_base hS (by omega) _) le_rfl)

/-- **Stability, the top degree**: `πᵢ(U(m)) → πᵢ(U(m + k))` is onto for `i + 1 ≤ dm + d − 1`
(`i ≤ 2m` for `ℂ`, `i ≤ m − 1` for `ℝ`; Milnor p. 129). -/
theorem surjective_homotopyGroupMap_unitaryIncl {d : ℕ} (hS : SphereConnected 𝕜 d) {i : ℕ}
    (hi : i + 1 ≤ d * m + d - 1) (S : unitaryGroup (Fin m) 𝕜) :
    Surjective (homotopyGroupMap (N := Fin i) (unitaryInclC (𝕜 := 𝕜) m k) S) := by
  have hloc : IsLocallyTrivial (unitaryOrbitC (𝕜 := 𝕜) m k) (unitaryGroup (Fin m) 𝕜) :=
    isLocallyTrivial_unitaryOrbit
  exact surjective_homotopyGroupMap_of_fiber (unitaryFibreAt S) (unitaryInclC m k) (fun _ => rfl)
    S rfl (surjective_homotopyGroupMap_fiberIncl_of_le hloc.isSerreFibration _
      (k := i) (fun i' hi' => subsingleton_pi_unitaryOrbit_base hS (by omega) _) le_rfl)

end Stability

/-! ### The Grassmannian: `π_{j+1}(G_m) ≅ π_j(U(m))` -/

section Grassmannian

variable {m m' : ℕ}

/-- The frame-to-span map `V_m(𝕜^{m'+m}) → G_m(𝕜^{m'+m})` as a continuous map. -/
def frameSpanC (m' m : ℕ) :
    C(Stiefel 𝕜 (Fin m' ⊕ Fin m) (Fin m), Grassmannian 𝕜 (Fin m' ⊕ Fin m) m) :=
  ⟨frameSpan 𝕜 _ m, continuous_frameSpan⟩

theorem isSerreFibration_frameSpanC : IsSerreFibration (frameSpanC (𝕜 := 𝕜) m' m) :=
  isLocallyTrivial_frameSpan.isSerreFibration

/-- `V_m(𝕜^{m'+m})` is `(dm' + d − 2)`-connected. -/
theorem subsingleton_pi_stiefel_sum {d : ℕ} (hS : SphereConnected 𝕜 d) {i : ℕ}
    (hi : i + 1 ≤ d * m' + d - 1) (x : Stiefel 𝕜 (Fin m' ⊕ Fin m) (Fin m)) :
    Subsingleton (π_ i (Stiefel 𝕜 (Fin m' ⊕ Fin m) (Fin m)) x) := by
  let e : Stiefel 𝕜 (Fin m' ⊕ Fin m) (Fin m) ≃ₜ Stiefel 𝕜 (Fin (m' + m)) (Fin m) :=
    stiefelCongr finSumFinEquiv (Equiv.refl _)
  refine subsingleton_homotopyGroup_of_homeomorph e _ (subsingleton_pi_stiefel hS m (m' + m)
    (by omega) i ?_ _)
  rwa [Nat.add_sub_cancel]

/-- The identification of the fibre over `P₀` with `U(m)`, `F₀S ↦ S`. -/
def grassFibre (m' m : ℕ) :
    fiber (frameSpanC (𝕜 := 𝕜) m' m) stiefelBase ≃ₜ unitaryGroup (Fin m) 𝕜 :=
  frameSpanFibreHomeomorph 𝕜 (Fin m') m

theorem grassFibre_fiberPt :
    grassFibre (𝕜 := 𝕜) m' m (fiberPt (frameSpanC m' m) stiefelBase) = 1 :=
  Subtype.ext (toRows₂_fromRows _ _)

/-- **`π_{j+1}(G_m(𝕜^{m'+m})) ≅ π_j(U(m))`** (Milnor, Lemma 23.4, p. 128), for
`j + 2 ≤ dm' + d − 1`: the boundary map of `U(m) → V_m(𝕜^{m'+m}) → G_m(𝕜^{m'+m})`, whose total
space is `(dm' + d − 2)`-connected, followed by the identification of the fibre with `U(m)`. -/
def grassmannianEquiv {d : ℕ} (hS : SphereConnected 𝕜 d) {j : ℕ} (hj : j + 2 ≤ d * m' + d - 1) :
    π_ (j + 1) (Grassmannian 𝕜 (Fin m' ⊕ Fin m) m) (grassBase 𝕜 (Fin m') m) ≃
      π_ j (unitaryGroup (Fin m) 𝕜) 1 :=
  (boundaryEquivPi isSerreFibration_frameSpanC stiefelBase (k := j + 1)
    (fun i hi => subsingleton_pi_stiefel_sum hS (by omega) _) le_rfl).trans
    ((homotopyGroupEquivOfHomotopyEquiv (grassFibre (𝕜 := 𝕜) m' m).toHomotopyEquiv
      (fiberPt (frameSpanC m' m) stiefelBase)).trans
      (Equiv.cast (congrArg (fun u => π_ j (unitaryGroup (Fin m) 𝕜) u) grassFibre_fiberPt)))

/-- **`π_{j+2}(G_m(𝕜^{m'+m})) ≅ π_{j+1}(U(m))` as groups**, for `j + 3 ≤ dm' + d − 1`: the
boundary map is a homomorphism (`Morse.Homotopy.boundaryHom`). -/
theorem nonempty_mulEquiv_grassmannian {d : ℕ} (hS : SphereConnected 𝕜 d) {j : ℕ}
    (hj : j + 3 ≤ d * m' + d - 1) :
    Nonempty (π_ (j + 2) (Grassmannian 𝕜 (Fin m' ⊕ Fin m) m) (grassBase 𝕜 (Fin m') m) ≃*
      π_ (j + 1) (unitaryGroup (Fin m) 𝕜) 1) := by
  have hq := isSerreFibration_frameSpanC (𝕜 := 𝕜) (m' := m') (m := m)
  have hE₁ : Subsingleton (HomotopyGroup (Option (Fin (j + 1)))
      (Stiefel 𝕜 (Fin m' ⊕ Fin m) (Fin m)) stiefelBase) :=
    subsingleton_homotopyGroup_option (subsingleton_pi_stiefel_sum hS (by omega) _)
  have hE₀ : Subsingleton (HomotopyGroup (Fin (j + 1)) (Stiefel 𝕜 (Fin m' ⊕ Fin m) (Fin m))
      stiefelBase) := subsingleton_pi_stiefel_sum hS (by omega) _
  let φ : C(fiber (frameSpanC (𝕜 := 𝕜) m' m) stiefelBase, unitaryGroup (Fin m) 𝕜) :=
    (grassFibre (𝕜 := 𝕜) m' m : C(fiber (frameSpanC (𝕜 := 𝕜) m' m) stiefelBase,
      unitaryGroup (Fin m) 𝕜))
  let f := (homotopyGroupHom (N := Fin (j + 1)) φ (fiberPt (frameSpanC m' m) stiefelBase)).comp
    (boundaryHom hq stiefelBase (N := Fin (j + 1)))
  have hf : Bijective f := (bijective_homotopyGroupMap_homeomorph (N := Fin (j + 1))
    (grassFibre (𝕜 := 𝕜) m' m) _).comp (bijective_boundaryMap hq stiefelBase hE₁ hE₀)
  have key : ∀ u : unitaryGroup (Fin m) 𝕜, φ (fiberPt (frameSpanC m' m) stiefelBase) = u →
      Nonempty (π_ (j + 2) (Grassmannian 𝕜 (Fin m' ⊕ Fin m) m) (grassBase 𝕜 (Fin m') m) ≃*
        π_ (j + 1) (unitaryGroup (Fin m) 𝕜) u) := by
    rintro u rfl
    exact ⟨(homotopyGroupCongrMulEquiv (finSuccEquiv (j + 1))).trans (MulEquiv.ofBijective f hf)⟩
  exact key 1 (grassFibre_fiberPt (𝕜 := 𝕜))

end Grassmannian

end Morse.Homotopy
