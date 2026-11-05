import Mathlib

/-!
Milnor, *Morse Theory*, §4, p. 25: the last sentence of the proof of Theorem 4.1 (Reeb).

# Two closed balls glued along their boundary spheres form a sphere

## Milnor's text, paraphrased

At the end of the proof of Reeb's theorem (p. 25) Milnor has written the compact manifold `M` as
the union of two closed `n`-cells, `M^{1-ε}` and `f⁻¹[1 - ε, 1]`, "matched along their common
boundary", and he concludes that a homeomorphism between `M` and `Sⁿ` is now easy to construct.
No construction is given.

## What is proved here

The purely topological statement behind this sentence, in a reusable form
(`Morse.nonempty_homeomorph_sphere_of_union_closedBall`): *if a Hausdorff space `X` is the union of
two embedded closed `n`-balls `D₁ = h₁(Dⁿ)` and `D₂ = h₂(Dⁿ)` which meet exactly in their common
boundary sphere, `D₁ ∩ D₂ = h₁(Sⁿ⁻¹) = h₂(Sⁿ⁻¹)`, then `X` is homeomorphic to the unit sphere
`Sⁿ ⊆ ℝⁿ⁺¹`.*  Here `Dⁿ` and `Sⁿ⁻¹` are the closed unit ball and the unit sphere of
`EuclideanSpace ℝ (Fin n)`, and `h₁, h₂` are only required to be continuous and injective on `Dⁿ`.
The compactness of `X` is automatic (`X = D₁ ∪ D₂`).

## The construction, and what Milnor's "easy" hides

1. **The boundary identification.**  `g = h₂⁻¹ ∘ h₁ : Sⁿ⁻¹ → Sⁿ⁻¹` is a well-defined bijection
   because `h₁(Sⁿ⁻¹) = h₂(Sⁿ⁻¹)` and `h₂` is injective; it is continuous because `h₂` restricted to
   the compact sphere is a closed embedding into the Hausdorff space `X`
   (`Continuous.isClosedEmbedding`), and so is its inverse.
2. **Alexander's trick** (`Morse.alexanderConeHomeomorph`).  The two balls are glued by `g`, which
   in general is not the identity, so one ball must be reparametrized so that the gluing becomes
   the identity of the sphere.  The cone `G(x) = ‖x‖ g(x / ‖x‖)`, `G(0) = 0`, is a homeomorphism of
   `ℝⁿ` (with inverse the cone of `g⁻¹`) which preserves norms and extends `g`.  It is continuous
   at `0` only because `‖G(x)‖ = ‖x‖`; it is in general not differentiable there.  This is where
   smoothness is lost (compare Milnor's Remark 2, p. 25: `M` need not be diffeomorphic to `Sⁿ`).
3. **The map `H : Sⁿ → X`.**  Write `z ∈ Sⁿ ⊆ ℝⁿ × ℝ` as `(x, s)` (`Morse.hemiProj`,
   `Morse.hemiHeight`).  Put `H(x, s) = h₁(x)` for `s ≥ 0` and `H(x, s) = h₂(G(x))` for `s < 0`.  On
   the equator `|x| = 1`, so `h₂(G(x)) = h₂(g(x)) = h₁(x)`, and `H` is continuous by the pasting
   lemma (`Continuous.if_le`).
4. **`H` is bijective.**  Points of the open hemispheres have different images because the two
   balls meet only in the boundary sphere and `‖G(x)‖ = ‖x‖`; on each closed hemisphere the
   projection `(x, s) ↦ x` is injective.  `H` is onto because `D₁ ∪ D₂ = X` and `G` is onto.
5. **`H` is a homeomorphism**, being a continuous bijection from the compact space `Sⁿ` to the
   Hausdorff space `X` (`Continuous.homeoOfEquivCompactToT2`).

The argument works for every `n ≥ 0` (for `n = 0` the balls are points and `S⁻¹ = ∅`).

## Main definitions and results

* `Morse.alexanderCone g`: the cone `x ↦ ‖x‖ g(x / ‖x‖)` of a self-map `g` of the unit sphere of
  a real normed space; `Morse.norm_alexanderCone`, `Morse.alexanderCone_of_mem_sphere`,
  `Morse.continuous_alexanderCone`.
* `Morse.alexanderConeHomeomorph g`: **Alexander's trick**, the cone of a homeomorphism of the unit
  sphere, a homeomorphism of the whole space.
* `Morse.hemiProj`, `Morse.hemiHeight`, `Morse.hemiLift`: the coordinates `ℝⁿ⁺¹ = ℝⁿ × ℝ`.
* `Morse.nonempty_homeomorph_sphere_of_union_closedBall`: **two closed `n`-balls glued along their
  boundary spheres form `Sⁿ`**.
-/

open Set Metric Filter Topology Function

noncomputable section

namespace Morse

/-! ### Alexander's trick -/

section Cone

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem inv_norm_smul_mem_sphere {x : E} (hx : x ≠ 0) : ‖x‖⁻¹ • x ∈ sphere (0 : E) 1 := by
  rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm,
    inv_mul_cancel₀ (norm_ne_zero_iff.2 hx)]

open Classical in
/-- **Alexander's cone** of a map `g` of the unit sphere to itself: `x ↦ ‖x‖ g(x / ‖x‖)` for
`x ≠ 0`, and `0 ↦ 0`. -/
def alexanderCone (g : sphere (0 : E) 1 → sphere (0 : E) 1) (x : E) : E :=
  if hx : x = 0 then 0 else ‖x‖ • (g ⟨‖x‖⁻¹ • x, inv_norm_smul_mem_sphere hx⟩ : E)

variable (g g' : sphere (0 : E) 1 → sphere (0 : E) 1)

@[simp] theorem alexanderCone_zero : alexanderCone g (0 : E) = 0 := by
  simp [alexanderCone]

theorem alexanderCone_of_ne_zero {x : E} (hx : x ≠ 0) :
    alexanderCone g x = ‖x‖ • (g ⟨‖x‖⁻¹ • x, inv_norm_smul_mem_sphere hx⟩ : E) := by
  simp [alexanderCone, hx]

/-- The cone preserves norms. -/
@[simp] theorem norm_alexanderCone (x : E) : ‖alexanderCone g x‖ = ‖x‖ := by
  by_cases hx : x = 0
  · simp [hx]
  · rw [alexanderCone_of_ne_zero g hx, norm_smul, norm_norm,
      mem_sphere_zero_iff_norm.1 (g _).2, mul_one]

/-- The cone extends `g`. -/
theorem alexanderCone_of_mem_sphere {x : E} (hx : x ∈ sphere (0 : E) 1) :
    alexanderCone g x = g ⟨x, hx⟩ := by
  have h1 : ‖x‖ = 1 := mem_sphere_zero_iff_norm.1 hx
  have hx0 : x ≠ 0 := ne_zero_of_mem_unit_sphere ⟨x, hx⟩
  have hs : (⟨‖x‖⁻¹ • x, inv_norm_smul_mem_sphere hx0⟩ : sphere (0 : E) 1) = ⟨x, hx⟩ :=
    Subtype.ext (by simp [h1])
  rw [alexanderCone_of_ne_zero g hx0, hs, h1, one_smul]

/-- The cone of a composite is the composite of the cones. -/
theorem alexanderCone_alexanderCone (x : E) :
    alexanderCone g (alexanderCone g' x) = alexanderCone (g ∘ g') x := by
  by_cases hx : x = 0
  · simp [hx]
  · have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.2 hx
    have hy : alexanderCone g' x ≠ 0 := by
      rw [← norm_ne_zero_iff, norm_alexanderCone]
      exact hn
    have hs : (⟨‖alexanderCone g' x‖⁻¹ • alexanderCone g' x, inv_norm_smul_mem_sphere hy⟩ :
        sphere (0 : E) 1) = g' ⟨‖x‖⁻¹ • x, inv_norm_smul_mem_sphere hx⟩ := by
      apply Subtype.ext
      change ‖alexanderCone g' x‖⁻¹ • alexanderCone g' x = _
      rw [norm_alexanderCone, alexanderCone_of_ne_zero g' hx, smul_smul, inv_mul_cancel₀ hn,
        one_smul]
    rw [alexanderCone_of_ne_zero g hy, hs, norm_alexanderCone, alexanderCone_of_ne_zero _ hx,
      comp_apply]

theorem alexanderCone_id (x : E) : alexanderCone id x = x := by
  by_cases hx : x = 0
  · simp [hx]
  · rw [alexanderCone_of_ne_zero _ hx, id, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.2 hx),
      one_smul]

/-- The cone of a continuous map is continuous: away from `0` it is a composite of continuous
maps, and at `0` it is continuous because it preserves norms. -/
theorem continuous_alexanderCone {g : sphere (0 : E) 1 → sphere (0 : E) 1} (hg : Continuous g) :
    Continuous (alexanderCone g) := by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : x = 0
  · subst hx
    rw [ContinuousAt, alexanderCone_zero, tendsto_zero_iff_norm_tendsto_zero]
    simp_rw [norm_alexanderCone]
    exact tendsto_norm_zero
  · have hOn : ContinuousOn (alexanderCone g) {0}ᶜ := by
      rw [continuousOn_iff_continuous_domRestrict]
      have hne : ∀ y : ({0}ᶜ : Set E), (y : E) ≠ 0 := fun y => y.2
      have : ({0}ᶜ : Set E).domRestrict (alexanderCone g) = fun y : ({0}ᶜ : Set E) =>
          ‖(y : E)‖ • (g ⟨‖(y : E)‖⁻¹ • (y : E), inv_norm_smul_mem_sphere (hne y)⟩ : E) := by
        funext y
        exact alexanderCone_of_ne_zero g (hne y)
      rw [this]
      refine continuous_subtype_val.norm.smul (continuous_subtype_val.comp (hg.comp ?_))
      exact ((continuous_subtype_val.norm.inv₀ fun y => norm_ne_zero_iff.2 (hne y)).smul
        continuous_subtype_val).subtype_mk _
    exact hOn.continuousAt (isOpen_compl_singleton.mem_nhds hx)

/-- **Alexander's trick**: a homeomorphism `g` of the unit sphere extends, by the cone
construction, to a homeomorphism of the whole space which preserves norms (so it maps the closed
unit ball onto itself, and the unit sphere onto itself by `g`). -/
def alexanderConeHomeomorph (g : sphere (0 : E) 1 ≃ₜ sphere (0 : E) 1) : E ≃ₜ E where
  toFun := alexanderCone g
  invFun := alexanderCone g.symm
  left_inv x := by
    rw [alexanderCone_alexanderCone, g.symm_comp_self, alexanderCone_id]
  right_inv x := by
    rw [alexanderCone_alexanderCone, g.self_comp_symm, alexanderCone_id]
  continuous_toFun := continuous_alexanderCone g.continuous
  continuous_invFun := continuous_alexanderCone g.symm.continuous

@[simp] theorem alexanderConeHomeomorph_apply (g : sphere (0 : E) 1 ≃ₜ sphere (0 : E) 1)
    (x : E) : alexanderConeHomeomorph g x = alexanderCone g x := rfl

end Cone

/-! ### The sphere `Sⁿ ⊆ ℝⁿ⁺¹` over the closed ball `Dⁿ` -/

section Hemisphere

variable {n : ℕ}

/-- The first `n` coordinates of a point of `ℝⁿ⁺¹`: the vertical projection of `Sⁿ` onto the
equatorial disk `Dⁿ`. -/
def hemiProj (z : EuclideanSpace ℝ (Fin (n + 1))) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (fun i => z (Fin.castSucc i))

/-- The last coordinate of a point of `ℝⁿ⁺¹` (the height). -/
def hemiHeight (z : EuclideanSpace ℝ (Fin (n + 1))) : ℝ :=
  z (Fin.last n)

/-- The point `(v, s) ∈ ℝⁿ × ℝ = ℝⁿ⁺¹`. -/
def hemiLift (v : EuclideanSpace ℝ (Fin n)) (s : ℝ) : EuclideanSpace ℝ (Fin (n + 1)) :=
  WithLp.toLp 2 (Fin.snoc (α := fun _ => ℝ) (fun i => v i) s)

@[simp] theorem hemiProj_hemiLift (v : EuclideanSpace ℝ (Fin n)) (s : ℝ) :
    hemiProj (hemiLift v s) = v := by
  apply PiLp.ext
  intro i
  simp [hemiProj, hemiLift]

@[simp] theorem hemiHeight_hemiLift (v : EuclideanSpace ℝ (Fin n)) (s : ℝ) :
    hemiHeight (hemiLift v s) = s := by
  simp [hemiHeight, hemiLift]

theorem norm_sq_eq_hemiProj_hemiHeight (z : EuclideanSpace ℝ (Fin (n + 1))) :
    ‖z‖ ^ 2 = ‖hemiProj z‖ ^ 2 + hemiHeight z ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_castSucc]
  simp [hemiProj, hemiHeight]

theorem eq_of_hemiProj_eq {z z' : EuclideanSpace ℝ (Fin (n + 1))}
    (h1 : hemiProj z = hemiProj z') (h2 : hemiHeight z = hemiHeight z') : z = z' := by
  apply PiLp.ext
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · exact h2
  · have := congrArg (fun v : EuclideanSpace ℝ (Fin n) => v j) h1
    simpa [hemiProj] using this

theorem continuous_hemiProj : Continuous (hemiProj (n := n)) := by
  unfold hemiProj
  fun_prop

theorem continuous_hemiHeight : Continuous (hemiHeight (n := n)) := by
  unfold hemiHeight
  fun_prop

theorem norm_hemiProj_le {z : EuclideanSpace ℝ (Fin (n + 1))} (hz : z ∈ sphere (0 : _) 1) :
    ‖hemiProj z‖ ≤ 1 := by
  have h := norm_sq_eq_hemiProj_hemiHeight z
  rw [mem_sphere_zero_iff_norm.1 hz] at h
  have : ‖hemiProj z‖ ^ 2 ≤ 1 ^ 2 := by nlinarith [sq_nonneg (hemiHeight z)]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) zero_le_one two_ne_zero).1 this

theorem hemiHeight_sq {z : EuclideanSpace ℝ (Fin (n + 1))} (hz : z ∈ sphere (0 : _) 1) :
    hemiHeight z ^ 2 = 1 - ‖hemiProj z‖ ^ 2 := by
  have h := norm_sq_eq_hemiProj_hemiHeight z
  rw [mem_sphere_zero_iff_norm.1 hz] at h
  linarith

theorem hemiLift_mem_sphere {v : EuclideanSpace ℝ (Fin n)} {s : ℝ}
    (hs : s ^ 2 = 1 - ‖v‖ ^ 2) : hemiLift v s ∈ sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 := by
  rw [mem_sphere_zero_iff_norm]
  have h := norm_sq_eq_hemiProj_hemiHeight (hemiLift v s)
  rw [hemiProj_hemiLift, hemiHeight_hemiLift, hs] at h
  have h1 : ‖hemiLift v s‖ ^ 2 = 1 ^ 2 := by linarith
  exact (pow_left_inj₀ (norm_nonneg _) zero_le_one two_ne_zero).1 h1

theorem sq_sqrt_one_sub_norm_sq {v : EuclideanSpace ℝ (Fin n)} (hv : ‖v‖ ≤ 1) :
    √(1 - ‖v‖ ^ 2) ^ 2 = 1 - ‖v‖ ^ 2 := by
  refine Real.sq_sqrt ?_
  nlinarith [norm_nonneg v]

/-- Two points of `Sⁿ` with the same projection and heights of the same sign coincide. -/
theorem eq_of_hemiProj_eq_of_sameSign {z z' : EuclideanSpace ℝ (Fin (n + 1))}
    (hz : z ∈ sphere (0 : _) 1) (hz' : z' ∈ sphere (0 : _) 1) (h1 : hemiProj z = hemiProj z')
    (h2 : (0 ≤ hemiHeight z ∧ 0 ≤ hemiHeight z') ∨ (hemiHeight z ≤ 0 ∧ hemiHeight z' ≤ 0)) :
    z = z' := by
  refine eq_of_hemiProj_eq h1 ?_
  have hsq : hemiHeight z ^ 2 = hemiHeight z' ^ 2 := by
    rw [hemiHeight_sq hz, hemiHeight_sq hz', h1]
  rcases h2 with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · exact (pow_left_inj₀ ha hb two_ne_zero).1 hsq
  · have := (pow_left_inj₀ (neg_nonneg.2 ha) (neg_nonneg.2 hb) two_ne_zero).1
      (by simpa using hsq)
    simpa using this

end Hemisphere

/-! ### Two closed balls glued along their boundary spheres -/

section Gluing

variable {X : Type*} [TopologicalSpace X] [T2Space X] {n : ℕ}

/-- **Two closed `n`-balls glued along their boundary spheres form `Sⁿ`.**  Let `h₁, h₂` be
continuous maps of the closed unit ball `Dⁿ ⊆ ℝⁿ` into a Hausdorff space `X`, injective on `Dⁿ`,
whose images `D₁ = h₁(Dⁿ)` and `D₂ = h₂(Dⁿ)` cover `X` and meet exactly in the common boundary
sphere `h₁(Sⁿ⁻¹) = h₂(Sⁿ⁻¹)`.  Then `X` is homeomorphic to the unit sphere `Sⁿ ⊆ ℝⁿ⁺¹`.

The homeomorphism `Sⁿ → X` maps the upper hemisphere onto `D₁` by `h₁ ∘ (vertical projection)`,
and the lower one onto `D₂` by `h₂ ∘ G ∘ (vertical projection)`, `G` the Alexander cone of the
boundary identification `h₂⁻¹ ∘ h₁ : Sⁿ⁻¹ → Sⁿ⁻¹` (`Morse.alexanderConeHomeomorph`); it is a
continuous bijection from a compact space to a Hausdorff space. -/
theorem nonempty_homeomorph_sphere_of_union_closedBall
    {h₁ h₂ : EuclideanSpace ℝ (Fin n) → X}
    (hc₁ : ContinuousOn h₁ (closedBall 0 1)) (hc₂ : ContinuousOn h₂ (closedBall 0 1))
    (hi₁ : InjOn h₁ (closedBall 0 1)) (hi₂ : InjOn h₂ (closedBall 0 1))
    (hcover : h₁ '' closedBall 0 1 ∪ h₂ '' closedBall 0 1 = univ)
    (hinter : h₁ '' closedBall 0 1 ∩ h₂ '' closedBall 0 1 = h₁ '' sphere 0 1)
    (hbdry : h₂ '' sphere 0 1 = h₁ '' sphere 0 1) :
    Nonempty (X ≃ₜ sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) := by
  set B := closedBall (0 : EuclideanSpace ℝ (Fin n)) 1 with hB
  set S := sphere (0 : EuclideanSpace ℝ (Fin n)) 1 with hS
  have hSB : S ⊆ B := sphere_subset_closedBall
  -- a point of `D₂` which lies in `D₁` comes from the boundary sphere
  have hbd : ∀ x ∈ B, h₂ x ∈ h₁ '' B → x ∈ S := by
    intro x hx hx1
    have h1 : h₂ x ∈ h₂ '' S := by
      rw [hbdry, ← hinter]
      exact ⟨hx1, mem_image_of_mem _ hx⟩
    obtain ⟨w, hw, hwx⟩ := h1
    rwa [hi₂ hx (hSB hw) hwx.symm]
  -- the boundary identification `g = h₂⁻¹ ∘ h₁` and its inverse `g'`
  have hex₁ : ∀ v : S, ∃ w : S, h₂ w = h₁ v := by
    intro v
    obtain ⟨w, hw, hw'⟩ : h₁ v ∈ h₂ '' S := by
      rw [hbdry]
      exact mem_image_of_mem _ v.2
    exact ⟨⟨w, hw⟩, hw'⟩
  have hex₂ : ∀ w : S, ∃ v : S, h₁ v = h₂ w := by
    intro w
    obtain ⟨v, hv, hv'⟩ : h₂ w ∈ h₁ '' S := by
      rw [← hbdry]
      exact mem_image_of_mem _ w.2
    exact ⟨⟨v, hv⟩, hv'⟩
  choose g hg using hex₁
  choose g' hg' using hex₂
  have hgg' : ∀ w, g (g' w) = w := fun w =>
    Subtype.ext (hi₂ (hSB (g (g' w)).2) (hSB w.2) (by rw [hg, hg']))
  have hg'g : ∀ v, g' (g v) = v := fun v =>
    Subtype.ext (hi₁ (hSB (g' (g v)).2) (hSB v.2) (by rw [hg', hg]))
  -- `g` and `g'` are continuous: `h₁` and `h₂` are closed embeddings of the compact sphere
  have hk₁ : Continuous fun v : S => h₁ v :=
    hc₁.comp_continuous continuous_subtype_val fun v => hSB v.2
  have hk₂ : Continuous fun v : S => h₂ v :=
    hc₂.comp_continuous continuous_subtype_val fun v => hSB v.2
  have he₁ : IsEmbedding fun v : S => h₁ v :=
    (hk₁.isClosedEmbedding fun v w h => Subtype.ext (hi₁ (hSB v.2) (hSB w.2) h)).isEmbedding
  have he₂ : IsEmbedding fun v : S => h₂ v :=
    (hk₂.isClosedEmbedding fun v w h => Subtype.ext (hi₂ (hSB v.2) (hSB w.2) h)).isEmbedding
  have hgc : Continuous g := by
    rw [he₂.continuous_iff]
    have : ((fun v : S => h₂ v) ∘ g) = fun v : S => h₁ v := funext fun v => hg v
    rw [this]
    exact hk₁
  have hg'c : Continuous g' := by
    rw [he₁.continuous_iff]
    have : ((fun v : S => h₁ v) ∘ g') = fun v : S => h₂ v := funext fun v => hg' v
    rw [this]
    exact hk₂
  let gS : S ≃ₜ S :=
    { toFun := g
      invFun := g'
      left_inv := hg'g
      right_inv := hgg'
      continuous_toFun := hgc
      continuous_invFun := hg'c }
  -- Alexander's trick: the cone `G` of `g`
  let G := alexanderConeHomeomorph gS
  have hGn : ∀ x, ‖G x‖ = ‖x‖ := norm_alexanderCone _
  have hGB : ∀ x ∈ B, G x ∈ B := fun x hx => by
    rw [hB, mem_closedBall_zero_iff, hGn]
    exact mem_closedBall_zero_iff.1 hx
  have hGS : ∀ x (hx : x ∈ S), h₂ (G x) = h₁ x := by
    intro x hx
    rw [alexanderConeHomeomorph_apply, alexanderCone_of_mem_sphere _ hx]
    exact hg ⟨x, hx⟩
  -- the map `H : Sⁿ → X`, continuous by the pasting lemma
  set T := sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 with hT
  have hPB : ∀ z : T, hemiProj (z : EuclideanSpace ℝ (Fin (n + 1))) ∈ B := fun z =>
    mem_closedBall_zero_iff.2 (norm_hemiProj_le z.2)
  let H : T → X := fun z => if 0 ≤ hemiHeight (z : EuclideanSpace ℝ (Fin (n + 1)))
    then h₁ (hemiProj z) else h₂ (G (hemiProj z))
  have hHc : Continuous H := by
    refine Continuous.if_le
      (hc₁.comp_continuous (continuous_hemiProj.comp continuous_subtype_val) hPB)
      (hc₂.comp_continuous (G.continuous.comp (continuous_hemiProj.comp continuous_subtype_val))
        fun z => hGB _ (hPB z))
      continuous_const (continuous_hemiHeight.comp continuous_subtype_val) ?_
    intro z hz
    have hzS : hemiProj (z : EuclideanSpace ℝ (Fin (n + 1))) ∈ S := by
      have h := hemiHeight_sq z.2
      rw [← hz] at h
      have h1 : ‖hemiProj (z : EuclideanSpace ℝ (Fin (n + 1)))‖ ^ 2 = 1 ^ 2 := by linarith
      rw [hS, mem_sphere_zero_iff_norm]
      exact (pow_left_inj₀ (norm_nonneg _) zero_le_one two_ne_zero).1 h1
    exact (hGS _ hzS).symm
  -- `H` is injective
  have hlow : ∀ z : T, h₂ (G (hemiProj (z : EuclideanSpace ℝ (Fin (n + 1))))) ∈ h₁ '' B →
      hemiHeight (z : EuclideanSpace ℝ (Fin (n + 1))) = 0 := by
    intro z hz
    have hS' := hbd _ (hGB _ (hPB z)) hz
    rw [hS, mem_sphere_zero_iff_norm, hGn] at hS'
    have h := hemiHeight_sq z.2
    rw [hS', one_pow, sub_self] at h
    exact pow_eq_zero_iff two_ne_zero |>.1 h
  have hHi : Injective H := by
    intro z z' hzz'
    by_cases h1 : 0 ≤ hemiHeight (z : EuclideanSpace ℝ (Fin (n + 1))) <;>
      by_cases h2 : 0 ≤ hemiHeight (z' : EuclideanSpace ℝ (Fin (n + 1)))
    · simp only [H, if_pos h1, if_pos h2] at hzz'
      exact Subtype.ext (eq_of_hemiProj_eq_of_sameSign z.2 z'.2 (hi₁ (hPB z) (hPB z') hzz')
        (Or.inl ⟨h1, h2⟩))
    · simp only [H, if_pos h1, if_neg h2] at hzz'
      exact absurd (hlow z' ⟨_, hPB z, hzz'⟩).ge h2
    · simp only [H, if_neg h1, if_pos h2] at hzz'
      exact absurd (hlow z ⟨_, hPB z', hzz'.symm⟩).ge h1
    · simp only [H, if_neg h1, if_neg h2] at hzz'
      have hp := G.injective (hi₂ (hGB _ (hPB z)) (hGB _ (hPB z')) hzz')
      exact Subtype.ext (eq_of_hemiProj_eq_of_sameSign z.2 z'.2 hp
        (Or.inr ⟨(not_le.1 h1).le, (not_le.1 h2).le⟩))
  -- `H` is surjective
  have hup : ∀ v ∈ B, ∃ z : T, H z = h₁ v := by
    intro v hv
    have hv' : ‖v‖ ≤ 1 := mem_closedBall_zero_iff.1 hv
    refine ⟨⟨hemiLift v (√(1 - ‖v‖ ^ 2)), hemiLift_mem_sphere (sq_sqrt_one_sub_norm_sq hv')⟩,
      ?_⟩
    simp only [H, hemiHeight_hemiLift, hemiProj_hemiLift, if_pos (Real.sqrt_nonneg _)]
  have hHs : Surjective H := by
    intro x
    have hx : x ∈ h₁ '' B ∪ h₂ '' B := by
      rw [hcover]
      exact mem_univ x
    rcases hx with ⟨v, hv, rfl⟩ | ⟨w, hw, rfl⟩
    · exact hup v hv
    · by_cases hwS : w ∈ S
      · obtain ⟨v, hv, hvw⟩ : h₂ w ∈ h₁ '' S := by
          rw [← hbdry]
          exact mem_image_of_mem _ hwS
        rw [← hvw]
        exact hup v (hSB hv)
      · set v := G.symm w with hv_def
        have hGv : G v = w := G.apply_symm_apply w
        have hvn : ‖v‖ < 1 := by
          have h1 : ‖v‖ = ‖w‖ := by rw [← hGn v, hGv]
          rw [h1]
          refine lt_of_le_of_ne (mem_closedBall_zero_iff.1 hw) fun h => hwS ?_
          rw [hS, mem_sphere_zero_iff_norm]
          exact h
        have hpos : 0 < √(1 - ‖v‖ ^ 2) := Real.sqrt_pos.2 (by nlinarith [norm_nonneg v])
        refine ⟨⟨hemiLift v (-√(1 - ‖v‖ ^ 2)), hemiLift_mem_sphere (by
          rw [neg_sq]; exact sq_sqrt_one_sub_norm_sq hvn.le)⟩, ?_⟩
        simp only [H, hemiHeight_hemiLift, hemiProj_hemiLift,
          if_neg (not_le.2 (neg_neg_iff_pos.2 hpos)), hGv]
  -- a continuous bijection from a compact space to a Hausdorff space is a homeomorphism
  exact ⟨(Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective H ⟨hHi, hHs⟩) hHc).symm⟩

end Gluing

end Morse
