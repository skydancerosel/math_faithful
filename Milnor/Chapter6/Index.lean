import Milnor.Chapter5.HairyBall

/-!
# The index of a vector field at an isolated zero (Milnor pp. 32–33)

For a smooth vector field `v` on `ℝⁿ⁺¹` (`n ≥ 1`) with an isolated zero at `z`, the **index** of
`v` at `z` is the degree of the map `u ↦ v(z + εu)/|v(z + εu)|` of the unit sphere `Sⁿ` to
itself, for any `ε > 0` such that `v` has no other zero in the closed `ε`-ball.  It does not
depend on `ε` (homotopy invariance), and it is invariant under homotopies of `v` that keep the
sphere free of zeros.
-/

open Set Module Filter Topology Function
open scoped ContDiff Manifold RealInnerProductSpace

noncomputable section

namespace Milnor

namespace Sphere

variable {n : ℕ}

/-- `y / |y|`. -/
def normalize (y : EuclideanSpace ℝ (Fin (n + 1))) : EuclideanSpace ℝ (Fin (n + 1)) := ‖y‖⁻¹ • y

theorem normalize_mem {y : EuclideanSpace ℝ (Fin (n + 1))} (hy : y ≠ 0) : normalize y ∈ Sph n := by
  rw [mem_iff_norm, normalize, norm_smul, norm_inv, norm_norm]
  exact inv_mul_cancel₀ (norm_ne_zero_iff.2 hy)

theorem contDiffAt_normalize {y : EuclideanSpace ℝ (Fin (n + 1))} (hy : y ≠ 0) :
    ContDiffAt ℝ ∞ (normalize (n := n)) y :=
  ((contDiffAt_norm ℝ hy).inv (norm_ne_zero_iff.2 hy)).smul contDiffAt_id

/-- The map `u ↦ v(z + εu)/|v(z + εu)|` of the sphere (identity where `v` vanishes). -/
def sphMap (v : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)))
    (z : EuclideanSpace ℝ (Fin (n + 1))) (ε : ℝ) (u : Sph n) : Sph n :=
  open Classical in
  if h : v (z + ε • u.1) ≠ 0 then ⟨normalize (v (z + ε • u.1)), normalize_mem h⟩ else u

theorem sphMap_val {v : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))}
    {z : EuclideanSpace ℝ (Fin (n + 1))} {ε : ℝ} {u : Sph n} (h : v (z + ε • u.1) ≠ 0) :
    (sphMap v z ε u).1 = normalize (v (z + ε • u.1)) := by
  unfold sphMap; rw [dif_pos h]

/-- Smoothness of a family of sphere maps `(u, t) ↦ sphMap v z (ρ t) u`. -/
theorem contMDiff_sphMap_family {v : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))}
    (hv : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) ∞ v)
    (z : EuclideanSpace ℝ (Fin (n + 1))) {ρ : ℝ → ℝ} (hρ : ContDiff ℝ ∞ ρ)
    (hne : ∀ (t : ℝ) (u : Sph n), v (z + ρ t • u.1) ≠ 0) :
    ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞
      (fun p : Sph n × ℝ => sphMap v z (ρ p.2) p.1) := by
  set F : Sph n × ℝ → EuclideanSpace ℝ (Fin (n + 1)) :=
    fun p => normalize (v (z + ρ p.2 • p.1.1)) with hF
  have hFS : ∀ p, F p ∈ Sph n := fun p => normalize_mem (hne p.2 p.1)
  have hg : ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, ℝ))
      𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) ∞ (fun p : Sph n × ℝ => z + ρ p.2 • p.1.1) :=
    contMDiff_const.add ((hρ.contMDiff.comp contMDiff_snd).smul (contMDiff_val.comp contMDiff_fst))
  have hFsmooth : ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, ℝ))
      𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) ∞ F := by
    intro p
    show ContMDiffAt _ _ ∞ (normalize ∘ v ∘ (fun p : Sph n × ℝ => z + ρ p.2 • p.1.1)) p
    exact (contDiffAt_normalize (hne p.2 p.1)).contMDiffAt.comp p
      (hv.contMDiffAt.comp p hg.contMDiffAt)
  have heq : (fun p : Sph n × ℝ => sphMap v z (ρ p.2) p.1) = fun p => ⟨F p, hFS p⟩ := by
    funext p; exact Subtype.ext (sphMap_val (hne p.2 p.1))
  rw [heq]
  exact (sphS n).contMDiff_codRestrict hFsmooth hFS

theorem contMDiff_sphMap {v : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))}
    (hv : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) ∞ v)
    (z : EuclideanSpace ℝ (Fin (n + 1))) {ε : ℝ} (hne : ∀ u : Sph n, v (z + ε • u.1) ≠ 0) :
    ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ (sphMap v z ε) := by
  have := contMDiff_sphMap_family hv z (ρ := fun _ => ε) contDiff_const (fun _ u => hne u)
  have h2 : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      (𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, ℝ)) ∞ (fun u : Sph n => (u, (0 : ℝ))) :=
    contMDiff_id.prodMk contMDiff_const
  exact this.comp h2

/-- The degree of the sphere map at radius `ε`. -/
def indexAt (v : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)))
    (z : EuclideanSpace ℝ (Fin (n + 1))) (ε : ℝ) : ℤ :=
  deg (sphOr n) (sphOr n) (sphMap v z ε)

/-- `v` has an isolated zero at `z`, with no other zero in the closed `r`-ball. -/
def IsolatedZero (v : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)))
    (z : EuclideanSpace ℝ (Fin (n + 1))) (r : ℝ) : Prop :=
  v z = 0 ∧ ∀ x, dist x z ≤ r → x ≠ z → v x ≠ 0

theorem IsolatedZero.ne_zero_sph {v : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))}
    {z : EuclideanSpace ℝ (Fin (n + 1))} {r : ℝ} (h : IsolatedZero v z r) {ε : ℝ} (hε : 0 < ε)
    (hεr : ε ≤ r) (u : Sph n) : v (z + ε • u.1) ≠ 0 := by
  have hu : ‖u.1‖ = 1 := mem_iff_norm.1 u.2
  refine h.2 _ ?_ ?_
  · rw [dist_eq_norm, add_sub_cancel_left, norm_smul, hu, mul_one, Real.norm_eq_abs,
      abs_of_pos hε]
    exact hεr
  · intro heq
    have : ε • u.1 = 0 := by simpa using congrArg (· - z) heq
    rw [smul_eq_zero] at this
    rcases this with h1 | h1
    · exact hε.ne' h1
    · rw [h1, norm_zero] at hu; exact zero_ne_one hu

/-- **Homotopy invariance of the sphere-map degree** along a smooth family of radii. -/
theorem indexAt_eq_of_radii (hn : 0 < n)
    {v : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))}
    (hv : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) ∞ v)
    {z : EuclideanSpace ℝ (Fin (n + 1))} {r : ℝ} (h : IsolatedZero v z r) {ε₁ ε₂ : ℝ}
    (hε₁ : 0 < ε₁) (hε₁r : ε₁ ≤ r) (hε₂ : 0 < ε₂) (hε₂r : ε₂ ≤ r) :
    indexAt v z ε₁ = indexAt v z ε₂ := by
  haveI := preconnectedSpace hn
  set ρ : ℝ → ℝ := fun t => ε₁ + Real.smoothTransition t * (ε₂ - ε₁) with hρ
  have hρs : ContDiff ℝ ∞ ρ :=
    contDiff_const.add ((Real.smoothTransition.contDiff (n := ⊤)).mul contDiff_const)
  have hρpos : ∀ t, 0 < ρ t := fun t => by
    have h0 := Real.smoothTransition.nonneg t
    have h1 := Real.smoothTransition.le_one t
    simp only [ρ]
    calc (0 : ℝ) < min ε₁ ε₂ := lt_min hε₁ hε₂
      _ = (1 - Real.smoothTransition t) * min ε₁ ε₂ + Real.smoothTransition t * min ε₁ ε₂ := by ring
      _ ≤ (1 - Real.smoothTransition t) * ε₁ + Real.smoothTransition t * ε₂ := by
        gcongr
        · exact min_le_left _ _
        · exact min_le_right _ _
      _ = ε₁ + Real.smoothTransition t * (ε₂ - ε₁) := by ring
  have hρle : ∀ t, ρ t ≤ r := fun t => by
    have h0 := Real.smoothTransition.nonneg t
    have h1 := Real.smoothTransition.le_one t
    simp only [ρ]
    calc ε₁ + Real.smoothTransition t * (ε₂ - ε₁)
        = (1 - Real.smoothTransition t) * ε₁ + Real.smoothTransition t * ε₂ := by ring
      _ ≤ (1 - Real.smoothTransition t) * r + Real.smoothTransition t * r := by gcongr
      _ = r := by ring
  have hne : ∀ (t : ℝ) (u : Sph n), v (z + ρ t • u.1) ≠ 0 := fun t u =>
    h.ne_zero_sph (hρpos t) (hρle t) u
  have hH := contMDiff_sphMap_family hv z hρs hne
  have := deg_eq_of_homotopy hZ hZ (sphOr n) (sphOr n) hH
  simp only [ρ, Real.smoothTransition.zero, Real.smoothTransition.one, zero_mul, add_zero,
    one_mul, add_sub_cancel] at this
  exact this

/-- The **index** of `v` at `z`: the degree of the sphere map for a small radius (`0` if `z` is
not an isolated zero). -/
def index (v : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)))
    (z : EuclideanSpace ℝ (Fin (n + 1))) : ℤ :=
  open Classical in
  if h : ∃ r > 0, IsolatedZero v z r then indexAt v z (Classical.choose h) else 0

/-- The index is computed at any admissible radius. -/
theorem index_eq (hn : 0 < n)
    {v : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))}
    (hv : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) ∞ v)
    {z : EuclideanSpace ℝ (Fin (n + 1))} {r : ℝ} (hr : 0 < r) (h : IsolatedZero v z r) {ε : ℝ}
    (hε : 0 < ε) (hεr : ε ≤ r) : index v z = indexAt v z ε := by
  have hex : ∃ r > 0, IsolatedZero v z r := ⟨r, hr, h⟩
  rw [index, dif_pos hex]
  obtain ⟨hr', h'⟩ := Classical.choose_spec hex
  have h1 := indexAt_eq_of_radii hn hv h' hr' le_rfl (lt_min hr' hr) (min_le_left _ _)
  have h2 := indexAt_eq_of_radii hn hv h hε hεr (lt_min hr' hr) (min_le_right _ _)
  rw [h1, h2]

/-- **Homotopy invariance of the index**: if `V(·, t)` has no zero on the `ε`-sphere around `z`
for all `t`, the sphere-map degrees at `t = 0` and `t = 1` agree. -/
theorem indexAt_eq_of_homotopy (hn : 0 < n)
    {V : EuclideanSpace ℝ (Fin (n + 1)) × ℝ → EuclideanSpace ℝ (Fin (n + 1))}
    (hV : ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))).prod 𝓘(ℝ, ℝ))
      𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) ∞ V)
    {z : EuclideanSpace ℝ (Fin (n + 1))} {ε : ℝ}
    (hne : ∀ (t : ℝ) (u : Sph n), V (z + ε • u.1, t) ≠ 0) :
    indexAt (fun x => V (x, 0)) z ε = indexAt (fun x => V (x, 1)) z ε := by
  haveI := preconnectedSpace hn
  set F : Sph n × ℝ → EuclideanSpace ℝ (Fin (n + 1)) :=
    fun p => normalize (V (z + ε • p.1.1, p.2)) with hF
  have hFS : ∀ p, F p ∈ Sph n := fun p => normalize_mem (hne p.2 p.1)
  have hs : ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun _ : Sph n × ℝ => ε) := contMDiff_const
  have hv1 : ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, ℝ))
      𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) ∞ (fun p : Sph n × ℝ => p.1.1) :=
    contMDiff_val.comp contMDiff_fst
  have hzc : ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, ℝ))
      𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) ∞ (fun _ : Sph n × ℝ => z) := contMDiff_const
  have hg1 : ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, ℝ))
      𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) ∞ (fun p : Sph n × ℝ => z + ε • p.1.1) :=
    hzc.add (hs.smul hv1)
  have hg : ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, ℝ))
      (𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))).prod 𝓘(ℝ, ℝ)) ∞
      (fun p : Sph n × ℝ => (z + ε • p.1.1, p.2)) := hg1.prodMk contMDiff_snd
  have hFsmooth : ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, ℝ))
      𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) ∞ F := by
    intro p
    show ContMDiffAt _ _ ∞ (normalize ∘ V ∘ (fun p : Sph n × ℝ => (z + ε • p.1.1, p.2))) p
    exact (contDiffAt_normalize (hne p.2 p.1)).contMDiffAt.comp p
      (hV.contMDiffAt.comp p hg.contMDiffAt)
  set Hm : Sph n × ℝ → Sph n := fun p => ⟨F p, hFS p⟩ with hHm
  have hH : ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, ℝ))
      𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ Hm := (sphS n).contMDiff_codRestrict hFsmooth hFS
  have h0 : (fun u => Hm (u, 0)) = sphMap (fun x => V (x, 0)) z ε := by
    funext u; exact (Subtype.ext (sphMap_val (hne 0 u))).symm
  have h1 : (fun u => Hm (u, 1)) = sphMap (fun x => V (x, 1)) z ε := by
    funext u; exact (Subtype.ext (sphMap_val (hne 1 u))).symm
  have := deg_eq_of_homotopy hZ hZ (sphOr n) (sphOr n) hH
  rw [h0, h1] at this
  exact this

end Sphere

end Milnor
