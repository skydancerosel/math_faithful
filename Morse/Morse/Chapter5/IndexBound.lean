import Morse.Chapter1.Nondegenerate
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars

/-!
Milnor, *Morse Theory*, §7 (The Lefschetz theorem on hyperplane sections), pp. 39–41.

# The linear algebra behind the Lefschetz theorem: complex manifolds have index `≤ k`

## Milnor's text (pp. 39–41), paraphrased

* **Theorem 7.1** (p. 39).  A non-singular affine algebraic variety `M ⊂ ℂⁿ` of real dimension
  `2k` has `H_i(M; ℤ) = 0` for `i > k`.  It follows from
* **Theorem 7.2** (p. 39).  A complex analytic manifold of complex dimension `k`,
  bianalytically embedded as a closed subset of `ℂⁿ`, has the homotopy type of a
  `k`-dimensional CW-complex.
* **The quadratic form `Q'`** (p. 39).  A complex quadratic form `Q(z) = Σ b_{hj} zʰ zʲ`
  (`b_{hj} = b_{jh}`) in `k` variables becomes, after substituting `zʰ = xʰ + i yʰ` and taking
  real parts, a real quadratic form `Q'` in `2k` variables.
* **Assertion 1** (p. 39).  If `e` is an eigenvalue of `Q'` of multiplicity `μ`, then so is
  `-e`.  Milnor's proof: `Q(iz) = -Q(z)`, so an orthogonal change of variables carries `Q'` to
  `-Q'`; "Assertion 1 clearly follows".
* **Assertion 2** (p. 40).  If `M` is a complex manifold bianalytically embedded in `ℂⁿ` and
  `q ∈ M`, the focal points of `(M, q)` along any normal line occur in pairs symmetric about
  `q`, with equal multiplicities.  Proof: in holomorphic coordinates centred at `q` the
  Hermitian product `Σ w_α(z) v̄_α` of the inclusion `w` with a unit normal `v` is
  `const + Q(z) + ⋯` (no linear terms "since `v` is orthogonal to `M`"); its real part, the
  real inner product `w · v`, is `const + Q'(x, y) + ⋯`; "clearly" `Q'` determines the second
  fundamental form in the direction `v`, whose eigenvalues come in opposite pairs by Assertion 1;
  "hence" so do the focal points.
* **Proof of 7.2** (pp. 40–41).  For `p` with `L_p = ‖· − p‖²` non-degenerate on `M`
  (Theorem 6.6) every `L_p⁻¹[0, a]` is compact.  By Lemma 6.9 the index of `L_p` at a critical
  point `q` is the number of focal points on the segment from `q` to `p`.  There are at most
  `2k` focal points on the whole normal line, symmetric about `q`, so at most `k` lie between
  `q` and `p`: every index is `≤ k`, and Theorem 3.5 gives the CW-complex.

## What is formalized here

The algebraic core of pp. 39–41, in a form that plugs into §2 (`Morse.index` is Mathlib's
`sigNeg`, `Morse.nullity` the dimension of the null space).  A complex structure on a real
vector space `E` is a real-linear `J` with `J² = -1`; on a complex vector space it is
multiplication by `i`.

* **Assertion 1** (`Morse.nullity_reBilin_sub_smul_reInner_eq`,
  `Morse.finrank_eigenspace_neg_eq`).  The "eigenvalues of `Q'`" are those of the matrix `A` of
  `Q'` in the real coordinates `(x, y)`, i.e. the self-adjoint operator with
  `⟨A u, w⟩ = Re B(u, w)` for the real inner product `Re⟨u, w⟩` of `ℂᵏ`; the eigenspace of `e`
  is the null space of `Re B − e⟨·,·⟩`.  Both forms are proved: `Re B − e⟨·,·⟩` and
  `Re B + e⟨·,·⟩` have the same nullity, and `A` has eigenspaces of equal dimension for `e` and
  `-e`.  The proof is Milnor's: `J = i·` is orthogonal and turns `Re B` into `-Re B`
  (`Morse.reBilin_I_smul`).
* **Assertion 2, algebraic content** (`Morse.nullity_sub_smul_eq_nullity_add_smul`).  If `G` is
  `J`-invariant and `L` is `J`-anti-invariant, `G − tL` and `G + tL` have the same nullity, for
  every real `t`.  With `G = (g_ij)` (the first fundamental form) and `L = (v · ℓ_ij)` (the second
  fundamental form in the direction `v`) these nullities are the multiplicities of `q + tv` and
  `q − tv` as focal points (Milnor's Assertion 6.4).  In holomorphic coordinates
  (`Morse.nullity_hessian_normSq_sub_add_eq_sub`): the Hessians of `‖w(·) − p‖²` at `q` for
  `p = w(q) ± t n` have the same nullity.
* **The index bound** (`Morse.two_mul_index_le_finrank`, `Morse.index_le_finrank_complex`).  If
  `H(v, v) + H(Jv, Jv) ≥ 0` for every `v`, then `2 · index H ≤ dim_ℝ E`; on a complex space,
  `index H ≤ dim_ℂ V`.  A negative definite subspace `W` meets `JW` only in `0`.
* **The Andreotti–Frankel identity** (`Morse.apply_J_apply_J_eq`,
  `Morse.apply_I_smul_apply_I_smul_eq`, `Morse.apply_I_smul_apply_I_smul_eq_two_mul_norm_sq_sub`).
  If `H(v, v) = G(v, v) − L(v, v)` with `G` `J`-invariant and `L` `J`-anti-invariant, then
  `H(Jv, Jv) = 2G(v, v) − H(v, v)`.  For `Q(v) = ‖v‖² − Re B(v, v)`, `B` complex bilinear and
  `‖·‖` a Hermitian norm, this is `Q(iv) = 2‖v‖² − Q(v)`.
* **Milnor's consequence, for a form of the right shape** (`Morse.index_le_finrank_of_eq_sub_re`,
  `Morse.index_le_finrank_of_hermitian`, `Morse.index_hessian_le_finrank_complex`).  A real
  quadratic form on `ℂᵏ` of the shape `G(v, v) − Re B(v, v)`, with `G ≥ 0` invariant under
  `v ↦ iv` and `B` complex bilinear, has index `≤ k`.  In particular, if the Hessian of
  `f : ℂᵏ → ℝ` at `q` has that shape, its index is `≤ k`.
* **Milnor's consequence in holomorphic coordinates**
  (`Morse.hessian_normSq_sub_holomorphic`, `Morse.index_hessian_normSq_sub_holomorphic_le`).
  For `w : ℂᵏ → ℂⁿ` holomorphic near `q` (the inclusion of `M` read in a holomorphic chart) and
  `p ∈ ℂⁿ`, the real Hessian of `z ↦ ‖w(z) − p‖²` at `q` is
  `2 Re⟨dw ξ, dw ξ'⟩ + 2 Re⟨w(q) − p, d²w(ξ, ξ')⟩`, which has the above shape; so its index is
  `≤ k`.  This is the index of `L_p` at the critical point `w(q)` of `L_p|M`, computed in the
  real coordinates `(x, y)` as Milnor's §2 prescribes.
* **No local maxima** (`Morse.exists_pos_apply_of_eq_sub_re`).  If moreover `G` is positive
  definite and `V ≠ 0`, then `H(v, v) > 0` for some `v`: `L_p` has no local maximum on a complex
  submanifold of positive dimension.
* **Real orthogonality to a complex subspace** (`Morse.inner_eq_zero_of_re_inner_eq_zero`).  If
  `Re⟨a, v⟩ = 0` for all `a` in a complex subspace `T`, then `⟨a, v⟩ = 0` for all `a ∈ T`.  This
  is what Milnor's "the linear terms vanish since `v` is orthogonal to `M`" uses.

## What Milnor leaves implicit, and how it is handled

* **Assertion 1 "clearly follows"** (p. 39).  The orthogonal map `J` with `Q'(Ju) = -Q'(u)`
  anticommutes with the matrix `A` of `Q'`, so it maps the `e`-eigenspace of `A` injectively into
  the `(-e)`-eigenspace and vice versa.  Here: `Morse.finrank_eigenspace_neg_eq`.
* **Eigenvalues in which inner product** (p. 40).  Assertion 1 concerns eigenvalues relative to
  the coordinate inner product of `ℝ^{2k}`; focal points are governed by the eigenvalues of
  `(v · ℓ_ij)` relative to `(g_ij)` (Lemma 6.3 even assumes `g_ij(q) = δ_ij`).  The two agree only
  if the real coordinates are orthonormal at `q`.  What is needed, and true, is the version
  relative to a `J`-invariant `G` (`Morse.nullity_sub_smul_eq_nullity_add_smul`); the
  `J`-invariance of `(g_ij)` is the Cauchy–Riemann equations.
* **"Clearly the quadratic terms `Q'` determine the second fundamental form"** (p. 40).  Not
  needed in this form: `Morse.hessian_normSq_sub_holomorphic` computes the Hessian of `L_p` in
  holomorphic coordinates directly, and its second-order term `Re⟨w(q) − p, d²w(ξ, ξ)⟩` is
  visibly the real part of a complex quadratic form (with `p = q + tv`, `v` a unit normal, it
  is `−2t Q'(ξ)`).
* **"The linear terms vanish since `v` is orthogonal to `M`"** (p. 40).  Orthogonality is meant
  in the real sense, while the linear terms are Hermitian products; the gap is closed by
  `Morse.inner_eq_zero_of_re_inner_eq_zero`, since `TM_q` is a complex subspace.
* **Counting focal points** (p. 41).  "At most `2k` focal points on the line, symmetric about
  `q`, hence at most `k` between `p` and `q`" also needs that `q` and `p` are not focal (`p` is
  not, by Lemma 6.5, since `q` is non-degenerate) and the case `p = q`.  The route taken here
  avoids focal points altogether (Andreotti and Frankel's own argument): the bound
  `index ≤ k` holds at *every* critical point, degenerate or not, and uses neither Lemma 6.3
  nor Lemma 6.9.
* **"A `k`-dimensional CW-complex"** (p. 39).  The proof gives dimension *at most* `k`
  (`ℂ` is contractible).

## What is not covered

Theorems 7.1 and 7.2 themselves (they need Theorem 3.5 and Theorem 6.6), complex submanifolds of
`ℂⁿ` as manifolds (so the index bound is stated in a holomorphic chart, not for `L_p : M → ℝ`;
the passage from one to the other is the chart-independence of the index, §2), focal points and
Milnor's own route through Lemmas 6.3 and 6.9, Corollary 7.3 and Theorem 7.4.
-/

open Complex Module Filter Topology

noncomputable section

namespace Morse

/-! ### A real vector space with a complex structure -/

section ComplexStructure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The nullity is invariant under a linear change of variables (local copy, so that this file
does not depend on the manifold files). -/
private theorem nullity_bilinearComp_equiv (H : E →L[ℝ] E →L[ℝ] ℝ) (L : E ≃L[ℝ] E) :
    nullity (H.bilinearComp (L : E →L[ℝ] E) (L : E →L[ℝ] E)) = nullity H := by
  have hnull : nullSpace (H.bilinearComp (L : E →L[ℝ] E) (L : E →L[ℝ] E)) =
      (nullSpace H).comap (L : E →ₗ[ℝ] E) := by
    ext v
    simp only [mem_nullSpace, Submodule.mem_comap, ContinuousLinearMap.bilinearComp_apply,
      ContinuousLinearEquiv.coe_coe, LinearEquiv.coe_coe, ContinuousLinearEquiv.coe_toLinearEquiv]
    constructor
    · intro h w
      simpa using h (L.symm w)
    · intro h w
      exact h (L w)
  rw [nullity, hnull, nullity,
    Submodule.comap_equiv_eq_map_symm (L.toLinearEquiv : E ≃ₗ[ℝ] E)]
  exact LinearEquiv.finrank_map_eq _ _

/-- The nullity of `-H` is that of `H`. -/
private theorem nullity_neg (H : E →L[ℝ] E →L[ℝ] ℝ) : nullity (-H) = nullity H := by
  have : nullSpace (-H) = nullSpace H := by
    ext v
    simp [mem_nullSpace]
  rw [nullity, this, nullity]

/-- A real-linear `J` with `J² = -1`, as a linear equivalence (its inverse is `-J`). -/
def complexStructureEquiv (J : E →L[ℝ] E) (hJ : ∀ v, J (J v) = -v) : E ≃L[ℝ] E :=
  ContinuousLinearEquiv.equivOfInverse J (-J) (fun v => by simp [hJ]) (fun v => by simp [hJ])

@[simp] theorem complexStructureEquiv_apply (J : E →L[ℝ] E) (hJ : ∀ v, J (J v) = -v) (v : E) :
    complexStructureEquiv J hJ v = J v :=
  rfl

/-- **Assertion 2 of Milnor, algebraic content** (p. 40; Assertion 1a of the exposition).  Let
`J` be a complex structure, `G` a `J`-invariant and `L` a `J`-anti-invariant bilinear form.  Then
`G − tL` and `G + tL` have the same nullity, for every real `t`.  For `G = (g_ij)` and
`L = (v · ℓ_ij)` these are the multiplicities of `q + tv` and `q − tv` as focal points. -/
theorem nullity_sub_smul_eq_nullity_add_smul (G L : E →L[ℝ] E →L[ℝ] ℝ) (J : E →L[ℝ] E)
    (hJ : ∀ v, J (J v) = -v) (hG : ∀ v w, G (J v) (J w) = G v w)
    (hL : ∀ v w, L (J v) (J w) = -L v w) (t : ℝ) :
    nullity (G - t • L) = nullity (G + t • L) := by
  have h : (G - t • L).bilinearComp ((complexStructureEquiv J hJ : E ≃L[ℝ] E) : E →L[ℝ] E)
      ((complexStructureEquiv J hJ : E ≃L[ℝ] E) : E →L[ℝ] E) = G + t • L := by
    ext v w
    simp [hG, hL]
  rw [← h, nullity_bilinearComp_equiv]

/-- **Assertion 1 of Milnor, relative form** (p. 39).  With `G` `J`-invariant and `L`
`J`-anti-invariant, the multiplicity of `e` as an eigenvalue of `L` relative to `G`, the nullity
of `L − eG`, equals that of `-e`. -/
theorem nullity_sub_smul_eq_nullity_add_smul' (G L : E →L[ℝ] E →L[ℝ] ℝ) (J : E →L[ℝ] E)
    (hJ : ∀ v, J (J v) = -v) (hG : ∀ v w, G (J v) (J w) = G v w)
    (hL : ∀ v w, L (J v) (J w) = -L v w) (e : ℝ) :
    nullity (L - e • G) = nullity (L + e • G) := by
  have h : (L - e • G).bilinearComp ((complexStructureEquiv J hJ : E ≃L[ℝ] E) : E →L[ℝ] E)
      ((complexStructureEquiv J hJ : E ≃L[ℝ] E) : E →L[ℝ] E) = -(L + e • G) := by
    ext v w
    simp [hG, hL]
    ring
  rw [← nullity_neg (L + e • G), ← h, nullity_bilinearComp_equiv]

/-- **The Andreotti–Frankel identity.**  If `H(v, v) = G(v, v) − L(v, v)` with `G` `J`-invariant
and `L` `J`-anti-invariant (on the diagonal), then `H(Jv, Jv) = 2G(v, v) − H(v, v)`. -/
theorem apply_J_apply_J_eq (H G L : E →L[ℝ] E →L[ℝ] ℝ) (J : E → E)
    (hH : ∀ v, H v v = G v v - L v v) (hG : ∀ v, G (J v) (J v) = G v v)
    (hL : ∀ v, L (J v) (J v) = -L v v) (v : E) :
    H (J v) (J v) = 2 * G v v - H v v := by
  rw [hH, hH, hG, hL]
  ring

/-- **The index bound.**  Let `J` be injective and linear (e.g. a complex structure) and `H` a
bilinear form with `H(v, v) + H(Jv, Jv) ≥ 0` for all `v`.  Then `2 · index H ≤ dim E`: a subspace
`W` on which `H` is negative definite meets `JW` only in `0`. -/
theorem two_mul_index_le_finrank [FiniteDimensional ℝ E] (H : E →L[ℝ] E →L[ℝ] ℝ)
    (J : E →ₗ[ℝ] E) (hJ : Function.Injective J) (hH : ∀ v, 0 ≤ H v v + H (J v) (J v)) :
    2 * index H ≤ finrank ℝ E := by
  obtain ⟨W, hWdim, hWneg⟩ := exists_negDef_finrank_eq_index H
  have hJW : finrank ℝ (W.map J) = finrank ℝ W :=
    (Submodule.equivMapOfInjective J hJ W).finrank_eq.symm
  have hinf : W ⊓ W.map J = ⊥ := by
    rw [Submodule.eq_bot_iff]
    rintro v ⟨hvW, hvJW⟩
    obtain ⟨w, hwW, rfl⟩ := Submodule.mem_map.1 hvJW
    by_contra hne
    have hw0 : w ≠ 0 := by
      rintro rfl
      exact hne (map_zero J)
    have h1 := hWneg w hwW hw0
    have h2 := hWneg (J w) hvW hne
    have h3 := hH w
    linarith
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq W (W.map J)
  rw [hinf, finrank_bot, add_zero, hJW] at hsum
  have hle := Submodule.finrank_le (W ⊔ W.map J)
  omega

end ComplexStructure

/-! ### Complex vector spaces: `J` is multiplication by `i` -/

section Complex

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

/-- Multiplication by `i`, as a real-linear map. -/
def realMulI : V →L[ℝ] V :=
  Complex.I • ContinuousLinearMap.id ℝ V

@[simp] theorem realMulI_apply (v : V) : (realMulI : V →L[ℝ] V) v = I • v := by
  simp [realMulI]

theorem realMulI_realMulI (v : V) : (realMulI : V →L[ℝ] V) (realMulI v) = -v := by
  simp [smul_smul]

theorem realMulI_injective : Function.Injective (realMulI : V →L[ℝ] V) := by
  intro v w h
  simpa [I_ne_zero] using h

/-- **The index bound on a complex vector space.**  If `H(v, v) + H(iv, iv) ≥ 0` for all `v`,
then `index H ≤ dim_ℂ V`. -/
theorem index_le_finrank_complex [FiniteDimensional ℂ V] (H : V →L[ℝ] V →L[ℝ] ℝ)
    (hH : ∀ v, 0 ≤ H v v + H (I • v) (I • v)) : index H ≤ finrank ℂ V := by
  have h := two_mul_index_le_finrank H (realMulI : V →L[ℝ] V) realMulI_injective (by simpa using hH)
  rw [finrank_real_of_complex] at h
  omega

/-- The real part of a complex bilinear form, as a real bilinear form: Milnor's `Q'` is the
quadratic form of `reBilin B` when `Q(z) = B(z, z)`. -/
def reBilin (B : V →L[ℂ] V →L[ℂ] ℂ) : V →L[ℝ] V →L[ℝ] ℝ :=
  (ContinuousLinearMap.compL ℝ V ℂ ℝ reCLM).comp
    ((ContinuousLinearMap.restrictScalarsL ℂ V ℂ ℝ ℝ).comp (B.restrictScalars ℝ))

@[simp] theorem reBilin_apply (B : V →L[ℂ] V →L[ℂ] ℂ) (v w : V) :
    reBilin B v w = (B v w).re := by
  simp [reBilin]

/-- Milnor's identity `Q(iz) = -Q(z)` (p. 39), polarized: `Re B(iv, iw) = -Re B(v, w)` for a
complex bilinear `B`. -/
theorem reBilin_I_smul (B : V →L[ℂ] V →L[ℂ] ℂ) (v w : V) :
    reBilin B (I • v) (I • w) = -reBilin B v w := by
  simp [← mul_assoc]

/-- **The index bound for the shape `G − Re B`.**  Let `G` be a real bilinear form on a complex
vector space `V` with `G(v, v) ≥ 0` and `G(iv, iv) = G(v, v)`, and `B` complex bilinear.  If
`H(v, v) = G(v, v) − Re B(v, v)` for all `v`, then `index H ≤ dim_ℂ V`. -/
theorem index_le_finrank_of_eq_sub_re [FiniteDimensional ℂ V] (H G : V →L[ℝ] V →L[ℝ] ℝ)
    (B : V →L[ℂ] V →L[ℂ] ℂ) (hG : ∀ v, 0 ≤ G v v) (hGI : ∀ v, G (I • v) (I • v) = G v v)
    (hH : ∀ v, H v v = G v v - (B v v).re) : index H ≤ finrank ℂ V := by
  refine index_le_finrank_complex H fun v => ?_
  have h := apply_J_apply_J_eq H G (reBilin B) (I • ·) (by simpa using hH) hGI
    (fun v => reBilin_I_smul B v v) v
  linarith [hG v]

/-- **The Andreotti–Frankel identity on a complex vector space.**  If
`H(v, v) = G(v, v) − Re B(v, v)` with `G(iv, iv) = G(v, v)` and `B` complex bilinear, then
`H(iv, iv) = 2G(v, v) − H(v, v)`. -/
theorem apply_I_smul_apply_I_smul_eq (H G : V →L[ℝ] V →L[ℝ] ℝ) (B : V →L[ℂ] V →L[ℂ] ℂ)
    (hGI : ∀ v, G (I • v) (I • v) = G v v) (hH : ∀ v, H v v = G v v - (B v v).re) (v : V) :
    H (I • v) (I • v) = 2 * G v v - H v v :=
  apply_J_apply_J_eq H G (reBilin B) (I • ·) (by simpa using hH) hGI
    (fun v => reBilin_I_smul B v v) v

/-- **No negative semidefinite directions**, hence no local maxima (exposition, §4 and §6).  If
`G` is positive definite and `V ≠ 0`, a form `H(v, v) = G(v, v) − Re B(v, v)` takes a positive
value. -/
theorem exists_pos_apply_of_eq_sub_re [Nontrivial V] (H G : V →L[ℝ] V →L[ℝ] ℝ)
    (B : V →L[ℂ] V →L[ℂ] ℂ) (hG : ∀ v, v ≠ 0 → 0 < G v v)
    (hGI : ∀ v, G (I • v) (I • v) = G v v) (hH : ∀ v, H v v = G v v - (B v v).re) :
    ∃ v, 0 < H v v := by
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  have h := apply_I_smul_apply_I_smul_eq H G B hGI hH v
  have hGv := hG v hv
  by_cases h0 : 0 < H v v
  · exact ⟨v, h0⟩
  · exact ⟨I • v, by linarith⟩

end Complex

/-! ### Complex inner product spaces: Milnor's setting -/

section Hermitian

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

/-- The real inner product `Re⟨v, w⟩` of a complex inner product space, as a real bilinear form.
This is Milnor's `w · v` ("real part of `Σ w_α v̄_α`", p. 40), the Euclidean inner product of
`ℝ^{2k}` when `V = ℂᵏ`.  (Mathlib's Hermitian product is conjugate-linear in the first slot,
Milnor's in the second; their real parts agree.) -/
def reInner : V →L[ℝ] V →L[ℝ] ℝ :=
  letI : InnerProductSpace ℝ V := InnerProductSpace.complexToReal
  innerSL ℝ

theorem reInner_apply (v w : V) : reInner v w = (inner ℂ v w).re :=
  rfl

theorem reInner_self (v : V) : reInner v v = ‖v‖ ^ 2 := by
  rw [reInner_apply, inner_self_eq_norm_sq_to_K]
  norm_cast

/-- `Re⟨e u, w⟩ = e Re⟨u, w⟩` for real `e`. -/
theorem re_inner_real_smul_left (e : ℝ) (u w : V) :
    (inner ℂ (e • u) w).re = e * (inner ℂ u w).re := by
  rw [← Complex.coe_smul, inner_smul_left, conj_ofReal, re_ofReal_mul]

/-- The real inner product `Re⟨v, w⟩` is invariant under multiplication by `i`: the matrix `J` of
Milnor's change of variables is orthogonal. -/
theorem reInner_I_smul (v w : V) : reInner (I • v) (I • w) = reInner v w := by
  rw [reInner_apply, reInner_apply, inner_smul_left, inner_smul_right, ← mul_assoc, conj_I,
    neg_mul, I_mul_I, neg_neg, one_mul]

/-- **Real orthogonality to a complex subspace is Hermitian orthogonality** (exposition,
Lemma 3.1).  If `Re⟨a, v⟩ = 0` for every `a` in a complex subspace `T`, then `⟨a, v⟩ = 0` for
every `a ∈ T`.  This is what Milnor's "the linear terms vanish since `v` is orthogonal to `M`"
(p. 40) uses, with `T = TM_q`. -/
theorem inner_eq_zero_of_re_inner_eq_zero (T : Submodule ℂ V) (v : V)
    (h : ∀ a ∈ T, (inner ℂ a v).re = 0) (a : V) (ha : a ∈ T) : inner ℂ a v = 0 := by
  have h1 := h a ha
  have h2 := h (I • a) (T.smul_mem I ha)
  rw [inner_smul_left, conj_I] at h2
  apply Complex.ext
  · simpa using h1
  · simpa using h2

/-- **Assertion 1 of Milnor** (p. 39), with eigenvalues relative to the real inner product
`Re⟨·,·⟩` of `V` (the coordinate inner product of `ℝ^{2k}` when `V = ℂᵏ`): the null spaces of
`Re B − e⟨·,·⟩` and `Re B + e⟨·,·⟩` have the same dimension. -/
theorem nullity_reBilin_sub_smul_reInner_eq (B : V →L[ℂ] V →L[ℂ] ℂ) (e : ℝ) :
    nullity (reBilin B - e • reInner) = nullity (reBilin B + e • reInner) :=
  nullity_sub_smul_eq_nullity_add_smul' _ _ (realMulI : V →L[ℝ] V) realMulI_realMulI
    (fun v w => by simpa using reInner_I_smul v w)
    (fun v w => by simp) e

/-- The eigenspace of an operator `A` with `Re⟨A u, w⟩ = L(u, w)` is the null space of
`L − e Re⟨·,·⟩`. -/
theorem eigenspace_eq_nullSpace_sub_smul_reInner (A : V →ₗ[ℝ] V) (L : V →L[ℝ] V →L[ℝ] ℝ)
    (hA : ∀ u w, (inner ℂ (A u) w).re = L u w) (e : ℝ) :
    End.eigenspace A e = nullSpace (L - e • reInner) := by
  ext u
  rw [End.mem_eigenspace_iff, mem_nullSpace]
  simp only [sub_apply, smul_apply, smul_eq_mul,
    reInner_apply, ← hA]
  constructor
  · intro h w
    rw [h, re_inner_real_smul_left, sub_self]
  · intro h
    have hw := h (A u - e • u)
    rw [← re_inner_real_smul_left, ← Complex.sub_re, ← inner_sub_left, ← reInner_apply,
      reInner_self, sq_eq_zero_iff, norm_eq_zero, sub_eq_zero] at hw
    exact hw

/-- **Assertion 1 of Milnor, in matrix form** (p. 39).  Let `B` be complex bilinear on `V` and
`A` the matrix of `Q' = Re B` for the real inner product, `Re⟨A u, w⟩ = Re B(u, w)`.  If `e` is
an eigenvalue of `A` with multiplicity `μ`, then so is `-e`: the eigenspaces have equal
dimension. -/
theorem finrank_eigenspace_neg_eq (B : V →L[ℂ] V →L[ℂ] ℂ) (A : V →ₗ[ℝ] V)
    (hA : ∀ u w, (inner ℂ (A u) w).re = (B u w).re) (e : ℝ) :
    finrank ℝ (End.eigenspace A e) = finrank ℝ (End.eigenspace A (-e)) := by
  have hA' : ∀ u w, (inner ℂ (A u) w).re = reBilin B u w := by simpa using hA
  rw [eigenspace_eq_nullSpace_sub_smul_reInner A (reBilin B) hA',
    eigenspace_eq_nullSpace_sub_smul_reInner A (reBilin B) hA']
  have := nullity_reBilin_sub_smul_reInner_eq B e
  rw [nullity, nullity] at this
  have h : reBilin B - (-e) • reInner = reBilin B + e • (reInner : V →L[ℝ] V →L[ℝ] ℝ) := by
    ext v w
    simp
  rw [this, h]

/-- **The Andreotti–Frankel identity** for Milnor's quadratic forms: if
`Q(v) = H(v, v) = ‖v‖² − Re B(v, v)` with `B` complex bilinear, then `Q(iv) = 2‖v‖² − Q(v)`. -/
theorem apply_I_smul_apply_I_smul_eq_two_mul_norm_sq_sub (H : V →L[ℝ] V →L[ℝ] ℝ)
    (B : V →L[ℂ] V →L[ℂ] ℂ) (hH : ∀ v, H v v = ‖v‖ ^ 2 - (B v v).re) (v : V) :
    H (I • v) (I • v) = 2 * ‖v‖ ^ 2 - H v v := by
  have h := apply_I_smul_apply_I_smul_eq H reInner B (fun v => reInner_I_smul v v)
    (fun v => by rw [hH, reInner_self]) v
  rwa [reInner_self] at h

/-- **The index bound for `‖v‖² − Re B(v, v)`** (Milnor's Theorem 7.2, algebraic core): the real
quadratic form `‖v‖² − Re B(v, v)` on a complex inner product space of dimension `k`, with `B`
complex bilinear, has index `≤ k`. -/
theorem index_le_finrank_of_hermitian [FiniteDimensional ℂ V] (H : V →L[ℝ] V →L[ℝ] ℝ)
    (B : V →L[ℂ] V →L[ℂ] ℂ) (hH : ∀ v, H v v = ‖v‖ ^ 2 - (B v v).re) :
    index H ≤ finrank ℂ V :=
  index_le_finrank_of_eq_sub_re H reInner B (fun v => by rw [reInner_self]; positivity)
    (fun v => reInner_I_smul v v) (fun v => by rw [hH, reInner_self])

end Hermitian

/-! ### Milnor's consequence: critical points of index `≤ k` -/

section Hessian

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]

/-- **Critical points on a complex manifold have index `≤ k`** (Milnor, p. 41, as a statement
about the shape of the Hessian).  Let `f : V → ℝ` be a function on a complex vector space of
dimension `k` (a holomorphic chart).  If the Hessian of `f` at `q` has the form
`d²f_q(v, v) = G(v, v) − Re B(v, v)`, with `G ≥ 0` invariant under `v ↦ iv` and `B` complex
bilinear, then its index is at most `k`.  This is the case for `f = L_p` in holomorphic
coordinates (Milnor, pp. 36 and 40: `G` is twice the first fundamental form, `Re B` twice the
second fundamental form in the direction `p − q`).  Non-degeneracy of `q` is not needed. -/
theorem index_hessian_le_finrank_complex (f : V → ℝ) (q : V) (G : V →L[ℝ] V →L[ℝ] ℝ)
    (B : V →L[ℂ] V →L[ℂ] ℂ) (hG : ∀ v, 0 ≤ G v v) (hGI : ∀ v, G (I • v) (I • v) = G v v)
    (hf : ∀ v, hessian f q v v = G v v - (B v v).re) :
    index (hessian f q) ≤ finrank ℂ V :=
  index_le_finrank_of_eq_sub_re _ G B hG hGI hf

end Hessian

/-! ### The Hessian of `L_p` in holomorphic coordinates -/

section Holomorphic

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

theorem reInner_comm (a b : F) : reInner a b = reInner b a := by
  rw [reInner_apply, reInner_apply, ← inner_conj_symm, conj_re]

/-- **The Hessian of `L_p` in holomorphic coordinates** (Milnor, p. 40).  Let `w : V → F` be
holomorphic near `q` (the inclusion `M → ℂⁿ` read in a holomorphic chart, Milnor's
`w_α(z¹, …, zᵏ)`) and `p ∈ F`.  The real Hessian of `z ↦ L_p(w(z)) = ‖w(z) − p‖²` at `q` is
`2(Re⟨dw v, dw v'⟩ + Re⟨w(q) − p, d²w(v, v')⟩)`, where `dw` and `d²w` are the complex
derivatives.  The first term is the first fundamental form, `J`-invariant; the second is the real
part of a complex bilinear form, `J`-anti-invariant.  This replaces Milnor's "clearly the
quadratic terms `Q'` determine the second fundamental form". -/
theorem hessian_normSq_sub_holomorphic {w : V → F} {q : V} (hw : ContDiffAt ℂ 2 w q) (p : F)
    (v v' : V) :
    hessian (fun z => ‖w z - p‖ ^ 2) q v v' =
      2 * (reInner (fderiv ℂ w q v) (fderiv ℂ w q v') +
        reInner (w q - p) (fderiv ℂ (fderiv ℂ w) q v v')) := by
  have hf : (fun z => ‖w z - p‖ ^ 2) = fun z => reInner (w z - p) (w z - p) := by
    funext z
    rw [reInner_self]
  rw [hf]
  have hdiff : ∀ᶠ z in 𝓝 q, DifferentiableAt ℂ w z :=
    (hw.eventually (by simp)).mono fun z hz => hz.differentiableAt (by simp)
  have h1 : ∀ᶠ z in 𝓝 q, HasFDerivAt (fun z => reInner (w z - p) (w z - p))
      ((2 : ℝ) • (reInner (w z - p)).comp ((fderiv ℂ w z).restrictScalars ℝ)) z := by
    filter_upwards [hdiff] with z hz
    have hu : HasFDerivAt (fun z => w z - p) ((fderiv ℂ w z).restrictScalars ℝ) z :=
      (hz.hasFDerivAt.restrictScalars ℝ).sub_const p
    refine ((reInner : F →L[ℝ] F →L[ℝ] ℝ).hasFDerivAt_of_bilinear hu hu).congr_fderiv ?_
    ext v
    simp [reInner_comm (fderiv ℂ w z v)]
    ring
  have h2 : fderiv ℝ (fun z => reInner (w z - p) (w z - p)) =ᶠ[𝓝 q]
      fun z => (2 : ℝ) • (reInner (w z - p)).comp ((fderiv ℂ w z).restrictScalars ℝ) :=
    h1.mono fun z hz => hz.fderiv
  have hwq : HasFDerivAt (fun z => w z - p) ((fderiv ℂ w q).restrictScalars ℝ) q :=
    ((hw.differentiableAt (by simp)).hasFDerivAt.restrictScalars ℝ).sub_const p
  have hc : HasFDerivAt (fun z => reInner (w z - p))
      ((reInner : F →L[ℝ] F →L[ℝ] ℝ).comp ((fderiv ℂ w q).restrictScalars ℝ)) q :=
    (reInner : F →L[ℝ] F →L[ℝ] ℝ).hasFDerivAt.comp q hwq
  have hD : HasFDerivAt (fderiv ℂ w) (fderiv ℂ (fderiv ℂ w) q) q :=
    ((hw.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
  have hd : HasFDerivAt (fun z => (fderiv ℂ w z).restrictScalars ℝ)
      ((ContinuousLinearMap.restrictScalarsL ℂ V F ℝ ℝ).comp
        ((fderiv ℂ (fderiv ℂ w) q).restrictScalars ℝ)) q :=
    (ContinuousLinearMap.restrictScalarsL ℂ V F ℝ ℝ).hasFDerivAt.comp q (hD.restrictScalars ℝ)
  have h3 : HasFDerivAt (fun z => (2 : ℝ) • (reInner (w z - p)).comp
      ((fderiv ℂ w z).restrictScalars ℝ)) _ q := (hc.clm_comp hd).const_smul (2 : ℝ)
  rw [hessian, h2.fderiv_eq, h3.fderiv]
  simp
  ring

/-- **Milnor's index bound in holomorphic coordinates** (p. 41: "the index of `L_p` at `q` is
`≤ k`").  Let `w : V → F` be holomorphic near `q`, `V` of complex dimension `k`, and `p ∈ F`.
Then the Hessian of `z ↦ ‖w(z) − p‖²` at `q` has index at most `k`.  When `w` is a holomorphic
parametrization of a complex submanifold `M ⊂ ℂⁿ` and `w(q)` a critical point of `L_p|M`, this
Hessian is Milnor's `L_p**` in the coordinates `(x, y)` (§2), so the index of `L_p` there is
`≤ k`.  Neither non-degeneracy nor criticality of `q`, nor injectivity of `dw`, is needed. -/
theorem index_hessian_normSq_sub_holomorphic_le [FiniteDimensional ℂ V] {w : V → F} {q : V}
    (hw : ContDiffAt ℂ 2 w q) (p : F) :
    index (hessian (fun z => ‖w z - p‖ ^ 2) q) ≤ finrank ℂ V := by
  refine index_le_finrank_complex _ fun v => ?_
  rw [hessian_normSq_sub_holomorphic hw, hessian_normSq_sub_holomorphic hw]
  have h1 : reInner (fderiv ℂ w q (I • v)) (fderiv ℂ w q (I • v)) =
      reInner (fderiv ℂ w q v) (fderiv ℂ w q v) := by
    rw [map_smul, reInner_I_smul]
  have h2 : reInner (w q - p) (fderiv ℂ (fderiv ℂ w) q (I • v) (I • v)) =
      -reInner (w q - p) (fderiv ℂ (fderiv ℂ w) q v v) := by
    simp only [map_smul, smul_apply, smul_smul, I_mul_I, neg_one_smul, map_neg]
  rw [h1, h2, reInner_self]
  nlinarith [sq_nonneg ‖fderiv ℂ w q v‖]

/-- **Assertion 2 of Milnor in holomorphic coordinates** (p. 40).  Let `w : V → F` be holomorphic
near `q`, `n ∈ F` and `t ∈ ℝ`.  The Hessians at `q` of `‖w(·) − p‖²` for `p = w(q) + t n` and
`p = w(q) − t n` have the same nullity.  For a unit normal `n` at the point `w(q)` of a complex
submanifold, these nullities are the multiplicities of `w(q) ± t n` as focal points (Milnor's
Assertion 6.4 and Lemma 6.5, not formalized here): focal points come in symmetric pairs. -/
theorem nullity_hessian_normSq_sub_add_eq_sub {w : V → F} {q : V} (hw : ContDiffAt ℂ 2 w q)
    (n : F) (t : ℝ) :
    nullity (hessian (fun z => ‖w z - (w q + t • n)‖ ^ 2) q) =
      nullity (hessian (fun z => ‖w z - (w q - t • n)‖ ^ 2) q) := by
  have h : (hessian (fun z => ‖w z - (w q + t • n)‖ ^ 2) q).bilinearComp
      ((complexStructureEquiv (realMulI : V →L[ℝ] V) realMulI_realMulI : V ≃L[ℝ] V) : V →L[ℝ] V)
      ((complexStructureEquiv (realMulI : V →L[ℝ] V) realMulI_realMulI : V ≃L[ℝ] V) :
        V →L[ℝ] V) = hessian (fun z => ‖w z - (w q - t • n)‖ ^ 2) q := by
    ext v v'
    simp only [ContinuousLinearMap.bilinearComp_apply, ContinuousLinearEquiv.coe_coe,
      complexStructureEquiv_apply, realMulI_apply]
    rw [hessian_normSq_sub_holomorphic hw, hessian_normSq_sub_holomorphic hw]
    simp only [map_smul, smul_apply, smul_smul, I_mul_I, neg_one_smul, map_neg, reInner_I_smul,
      sub_add_cancel_left, sub_sub_cancel, neg_apply, neg_neg]
  rw [← h, nullity_bilinearComp_equiv]

end Holomorphic

end Morse
