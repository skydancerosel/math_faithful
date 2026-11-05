import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-!
Milnor, *Morse Theory*, §24, p. 144 ("`ℝⁿ` splits as a direct sum of minimal subspaces");
Exposition/Chapter15.md, Lemma 5.1 and Lemma 6.1.

# Orthogonal splitting into minimal invariant subspaces

## Milnor's text, paraphrased

(p. 144) `ℝⁿ` is the orthogonal direct sum `M_1 ⊕ ⋯ ⊕ M_s` of subspaces which are invariant and
minimal under `J_1, …, J_{k−1}, J, A`; the eigenvalues of `A²` on `M_h` are all equal.

## What is formalized

For a finite-dimensional real inner product space and a family `𝒢` of operators, each
self-adjoint or skew-adjoint (`Morse.IsStarSigned`):

* `Morse.IsInvar.orthogonal`: complements of invariant subspaces are invariant;
  `Morse.IsInvar.starProjection_comm`: the orthogonal projection onto an invariant subspace
  commutes with `𝒢`.
* `Morse.exists_minInvar_le`, `Morse.exists_minInvar_decomp`: **every invariant subspace is the
  orthogonal sum of minimal invariant subspaces** (a list, pairwise orthogonal, dimensions adding
  up, spanning).
* `Morse.IsMinInvar.exists_scalar`: **a self-adjoint operator commuting with `𝒢` is scalar on a
  minimal invariant subspace** (its eigenspaces are invariant).

## What Milnor leaves implicit

* The splitting uses that orthogonal complements of invariant subspaces are invariant, which
  needs every member of the family to be skew (or symmetric); "all equal, except for sign" is the
  scalar lemma applied to `−A²`.
-/

open Set Module

noncomputable section

namespace Morse

section Invar

open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- `W` is invariant under the family `𝒢`. -/
def IsInvar (𝒢 : Set (E →L[ℝ] E)) (W : Submodule ℝ E) : Prop := ∀ g ∈ 𝒢, ∀ w ∈ W, g w ∈ W

/-- `W` is a minimal non-zero invariant subspace (Milnor's "minimal", p. 143). -/
def IsMinInvar (𝒢 : Set (E →L[ℝ] E)) (W : Submodule ℝ E) : Prop :=
  W ≠ ⊥ ∧ IsInvar 𝒢 W ∧ ∀ W' : Submodule ℝ E, W' ≤ W → IsInvar 𝒢 W' → W' = ⊥ ∨ W' = W

/-- Every member of `𝒢` is self-adjoint or skew-adjoint. -/
def IsStarSigned (𝒢 : Set (E →L[ℝ] E)) : Prop :=
  ∀ g ∈ 𝒢, ContinuousLinearMap.adjoint g = g ∨ ContinuousLinearMap.adjoint g = -g

variable {𝒢 : Set (E →L[ℝ] E)}

/-- **Complements of invariant subspaces are invariant** (Milnor p. 144: the splitting into
minimal summands). -/
theorem IsInvar.orthogonal (h𝒢 : IsStarSigned 𝒢) {W : Submodule ℝ E} (hW : IsInvar 𝒢 W) :
    IsInvar 𝒢 Wᗮ := by
  intro g hg w hw
  rw [Submodule.mem_orthogonal]
  intro v hv
  rw [← ContinuousLinearMap.adjoint_inner_left]
  rcases h𝒢 g hg with h | h
  · rw [h]; exact (Submodule.mem_orthogonal _ _).1 hw _ (hW g hg v hv)
  · rw [h, neg_apply, inner_neg_left,
      (Submodule.mem_orthogonal _ _).1 hw _ (hW g hg v hv), neg_zero]

omit [FiniteDimensional ℝ E] in
theorem IsInvar.inf {W W' : Submodule ℝ E} (hW : IsInvar 𝒢 W) (hW' : IsInvar 𝒢 W') :
    IsInvar 𝒢 (W ⊓ W') := fun g hg w hw => ⟨hW g hg w hw.1, hW' g hg w hw.2⟩

omit [FiniteDimensional ℝ E] in
theorem isInvar_top : IsInvar 𝒢 (⊤ : Submodule ℝ E) := fun _ _ _ _ => Submodule.mem_top

/-- Every non-zero invariant subspace contains a minimal one (of least dimension). -/
theorem exists_minInvar_le {U : Submodule ℝ E} (hU : IsInvar 𝒢 U) (hne : U ≠ ⊥) :
    ∃ M ≤ U, IsMinInvar 𝒢 M := by
  classical
  have hex : ∃ d, ∃ M : Submodule ℝ E, M ≤ U ∧ IsInvar 𝒢 M ∧ M ≠ ⊥ ∧ finrank ℝ M = d :=
    ⟨_, U, le_rfl, hU, hne, rfl⟩
  obtain ⟨M, hMU, hM, hMne, hMd⟩ := Nat.find_spec hex
  refine ⟨M, hMU, hMne, hM, fun W hWM hW => ?_⟩
  by_cases hW0 : W = ⊥
  · exact Or.inl hW0
  · right
    have hle : Nat.find hex ≤ finrank ℝ W :=
      Nat.find_min' hex ⟨W, hWM.trans hMU, hW, hW0, rfl⟩
    exact Submodule.eq_of_le_of_finrank_le hWM (hMd ▸ hle)

/-- **Every invariant subspace splits orthogonally into minimal invariant subspaces** (Milnor
p. 144; the exposition's Lemma 5.1). -/
theorem exists_minInvar_decomp (h𝒢 : IsStarSigned 𝒢) :
    ∀ U : Submodule ℝ E, IsInvar 𝒢 U → ∃ L : List (Submodule ℝ E),
      (∀ M ∈ L, IsMinInvar 𝒢 M ∧ M ≤ U) ∧ L.Pairwise (fun M M' => M ⟂ M') ∧
      (L.map fun M : Submodule ℝ E => finrank ℝ M).sum = finrank ℝ U ∧
      U ≤ L.foldr (· ⊔ ·) ⊥ := by
  intro U
  induction h : finrank ℝ U using Nat.strong_induction_on generalizing U with
  | _ d ih =>
  intro hU
  by_cases hU0 : U = ⊥
  · subst hU0
    exact ⟨[], by simp, by simp, by simp [← h], bot_le⟩
  obtain ⟨M, hMU, hM⟩ := exists_minInvar_le hU hU0
  have hU'inv : IsInvar 𝒢 (Mᗮ ⊓ U) := (hM.2.1.orthogonal h𝒢).inf hU
  have hdim : finrank ℝ M + finrank ℝ (Mᗮ ⊓ U : Submodule ℝ E) = finrank ℝ U :=
    Submodule.finrank_add_inf_finrank_orthogonal hMU
  have hMpos : 0 < finrank ℝ M :=
    Nat.pos_of_ne_zero fun h0 => hM.1 (Submodule.finrank_eq_zero.1 h0)
  obtain ⟨L, hL1, hL2, hL3, hL4⟩ := ih (finrank ℝ (Mᗮ ⊓ U : Submodule ℝ E)) (by omega) (Mᗮ ⊓ U)
    rfl hU'inv
  refine ⟨M :: L, ?_, ?_, ?_, ?_⟩
  · intro M' hM'
    rcases List.mem_cons.1 hM' with rfl | hM'
    · exact ⟨hM, hMU⟩
    · exact ⟨(hL1 M' hM').1, (hL1 M' hM').2.trans inf_le_right⟩
  · refine List.pairwise_cons.2 ⟨fun M' hM' => ?_, hL2⟩
    exact (Submodule.isOrtho_orthogonal_right M).mono_right ((hL1 M' hM').2.trans inf_le_left)
  · simp only [List.map_cons, List.sum_cons, hL3]
    omega
  · rw [List.foldr_cons, ← Submodule.sup_orthogonal_inf_of_hasOrthogonalProjection hMU]
    exact sup_le_sup_left hL4 M

/-- **A self-adjoint operator commuting with `𝒢` is scalar on a minimal invariant subspace**
(Milnor p. 144: "the eigenvalues are all equal, except for sign"): its eigenspaces in `M` are
invariant. -/
theorem IsMinInvar.exists_scalar {M : Submodule ℝ E} (hM : IsMinInvar 𝒢 M) {S : E →L[ℝ] E}
    (hS : ContinuousLinearMap.adjoint S = S) (hSM : ∀ v ∈ M, S v ∈ M)
    (hcomm : ∀ g ∈ 𝒢, ∀ v, S (g v) = g (S v)) : ∃ c : ℝ, ∀ v ∈ M, S v = c • v := by
  set Sm : M →ₗ[ℝ] M := (S : E →ₗ[ℝ] E).restrict hSM with hSmdef
  have hsym : Sm.IsSymmetric := fun x y => by
    simp only [hSmdef, Submodule.coe_inner, LinearMap.coe_restrict_apply,
      ContinuousLinearMap.coe_coe]
    rw [← ContinuousLinearMap.adjoint_inner_right, hS]
  have : Nontrivial M := Submodule.nontrivial_iff_ne_bot.2 hM.1
  obtain ⟨v, hv⟩ := (hsym.hasEigenvalue_iSup_of_finiteDimensional).exists_hasEigenvector
  set c := ⨆ x : { x : M // x ≠ 0 }, RCLike.re ⟪Sm x, x⟫ / ‖(x : M)‖ ^ 2 with hc
  refine ⟨c, ?_⟩
  let W : Submodule ℝ E :=
    { carrier := {w | w ∈ M ∧ S w = c • w}
      add_mem' := fun ha hb => ⟨M.add_mem ha.1 hb.1, by rw [map_add, ha.2, hb.2, smul_add]⟩
      zero_mem' := ⟨M.zero_mem, by simp⟩
      smul_mem' := fun r w hw => ⟨M.smul_mem r hw.1, by rw [map_smul, hw.2, smul_comm]⟩ }
  have hWinv : IsInvar 𝒢 W := fun g hg w hw =>
    ⟨hM.2.1 g hg w hw.1, by rw [hcomm g hg, hw.2, map_smul]⟩
  have hvW : (v : E) ∈ W := by
    refine ⟨v.2, ?_⟩
    have h2 := congrArg Subtype.val hv.apply_eq_smul
    simpa [hSmdef] using h2
  have hWne : W ≠ ⊥ := fun h0 => by
    have hv0 : (v : E) = 0 := by
      have : (v : E) ∈ (⊥ : Submodule ℝ E) := h0 ▸ hvW
      exact (Submodule.mem_bot ℝ).1 this
    exact hv.2 (Subtype.ext hv0)
  rcases hM.2.2 W (fun w hw => hw.1) hWinv with h0 | hWM
  · exact absurd h0 hWne
  · intro w hw
    rw [← hWM] at hw
    exact hw.2

/-- The orthogonal projection onto an invariant subspace commutes with `𝒢`. -/
theorem IsInvar.starProjection_comm (h𝒢 : IsStarSigned 𝒢) {W : Submodule ℝ E}
    (hW : IsInvar 𝒢 W) {g : E →L[ℝ] E} (hg : g ∈ 𝒢) (v : E) :
    W.starProjection (g v) = g (W.starProjection v) := by
  have h1 : v = W.starProjection v + (v - W.starProjection v) := by abel
  have h2 : v - W.starProjection v ∈ Wᗮ := W.sub_starProjection_mem_orthogonal v
  conv_lhs => rw [h1]
  rw [map_add, map_add, Submodule.starProjection_eq_self_iff.2
    (hW g hg _ (W.starProjection_apply_mem v)),
    (Submodule.starProjection_apply_eq_zero_iff W).2 ((hW.orthogonal h𝒢) g hg _ h2), add_zero]

end Invar

end Morse
