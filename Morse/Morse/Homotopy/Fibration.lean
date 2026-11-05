import Mathlib
import Morse.Homotopy.ChangeOfBase

/-!
# Locally trivial maps and Serre fibrations

Milnor (§§23–24) computes the low homotopy groups of the Grassmannians from those of the unitary
groups by quoting the exact homotopy sequence of a fibre bundle (Steenrod, *The Topology of Fibre
Bundles*, §17). This file sets up the two notions that sequence rests on; the lifting theorem is in
`Morse/Homotopy/HomotopyLifting.lean` and the exact sequence in
`Morse/Homotopy/ExactSequence.lean`.

## Locally trivial maps

`Morse.Homotopy.IsLocallyTrivial p F`: every point of `B` has an open neighbourhood `U` and a
homeomorphism `p⁻¹(U) ≃ₜ U × F` over `U` (its first component is `p`). Unlike Mathlib's
`FiberBundle`, which is a structure on the sigma type `Bundle.TotalSpace F E`, this is a property
of an arbitrary map `p : E → B`, so that it applies directly to maps between concrete spaces (a
unitary group onto a sphere, a Stiefel manifold onto a Grassmannian). Mathlib's fibre bundles
satisfy it (`Morse.Homotopy.isLocallyTrivial_proj`), as does any map covered by
`Bundle.Trivialization`s (`Morse.Homotopy.isLocallyTrivial_of_trivializations`), and the
property is invariant under homeomorphisms of the total space and of the fibre. The fibres
`p⁻¹(b)` are homeomorphic to `F` (`Morse.Homotopy.IsLocallyTrivial.fiberHomeomorph`). Continuity
of `p` is not part of the definition: the lifting argument only uses the homeomorphisms over the
sets `U`.

## Serre fibrations

The **open box** `Jᴺ = Iᴺ × {0} ∪ ∂Iᴺ × I` of the cylinder `Iᴺ × I` (Hatcher's notation;
`Morse.Homotopy.openBox`) is the boundary of the cube `Iᴺ⁺¹` with the top face `Iᴺ × {1}`
removed. A map `p : E → B` is a **Serre fibration** (`Morse.Homotopy.IsSerreFibration p`) if it
has the homotopy lifting property for cubes, relative to the boundary: for every `n`, every map
`H : Iⁿ × I → B` and every lift of `H` given (continuously) on `Jⁿ`, there is a lift of `H` on
all of `Iⁿ × I` extending it. This relative form is what the exact sequence uses: the boundary
map lifts an `(n+1)`-cube relative to the part of its boundary which goes to the base point.

* `Morse.Homotopy.IsSerreFibration.exists_lift`: the lifting property for cubes `I^N` indexed by
  any finite type `N` (the definition quantifies over `Fin n` only, to stay in one universe).
* `Morse.Homotopy.IsSerreFibration.exists_lift_of_bot`: the **absolute** homotopy lifting
  property for cubes: a homotopy `H : Iᴺ × I → B` lifts, given a lift of `H(·, 0)` only. The
  proof transports the problem by a map of pairs `(Iᴺ × I, Jᴺ) → (Iᴺ × I, Iᴺ × {0})` with a
  section: `φ(x, t) = (s(x), t · c(x))`, where `s` stretches the cube of radius `1/4` about the
  centre onto `Iᴺ` (the frames of `Morse/Homotopy/ChangeOfBase.lean`) and `c(x) = 0` on `∂Iᴺ`,
  with section `ψ(x, t) = (x/2 + 1/4, t)`.
-/

open Set Function Topology
open scoped unitInterval Topology.Homotopy

noncomputable section

namespace Morse.Homotopy

variable {E B F : Type*} [TopologicalSpace E] [TopologicalSpace B] [TopologicalSpace F]

/-! ### Locally trivial maps -/

/-- **Local triviality** of `p : E → B` with fibre `F`: every point of `B` has an open
neighbourhood `U` with a homeomorphism `p⁻¹(U) ≃ₜ U × F` over `U`. -/
def IsLocallyTrivial (p : E → B) (F : Type*) [TopologicalSpace F] : Prop :=
  ∀ b : B, ∃ U : Set B, IsOpen U ∧ b ∈ U ∧
    ∃ φ : p ⁻¹' U ≃ₜ U × F, ∀ x, ((φ x).1 : B) = p x

/-- A map covered by Mathlib's local trivializations is locally trivial. -/
theorem isLocallyTrivial_of_trivializations {p : E → B}
    (h : ∀ b, ∃ e : Bundle.Trivialization F p, b ∈ e.baseSet) : IsLocallyTrivial p F := by
  intro b
  obtain ⟨e, hb⟩ := h b
  exact ⟨e.baseSet, e.open_baseSet, hb, e.preimageHomeomorph subset_rfl, fun x => by simp⟩

/-- **Mathlib's fibre bundles are locally trivial**: the projection of the total space of a
`FiberBundle F Z` is locally trivial with fibre `F`. -/
theorem isLocallyTrivial_proj {Z : B → Type*} [TopologicalSpace (Bundle.TotalSpace F Z)]
    [∀ b, TopologicalSpace (Z b)] [FiberBundle F Z] :
    IsLocallyTrivial (Bundle.TotalSpace.proj : Bundle.TotalSpace F Z → B) F :=
  isLocallyTrivial_of_trivializations fun b =>
    ⟨trivializationAt F Z b, FiberBundle.mem_baseSet_trivializationAt' b⟩

/-- The projection of a product is locally trivial. -/
theorem isLocallyTrivial_fst : IsLocallyTrivial (Prod.fst : B × F → B) F :=
  fun b => ⟨univ, isOpen_univ, mem_univ b,
    { toFun := fun x => (⟨x.1.1, mem_univ _⟩, x.1.2)
      invFun := fun y => ⟨(y.1, y.2), mem_univ _⟩
      left_inv := fun x => rfl
      right_inv := fun y => rfl
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }, fun x => rfl⟩

/-- Local triviality is invariant under homeomorphisms of the total space. -/
theorem IsLocallyTrivial.comp_homeomorph {E' : Type*} [TopologicalSpace E'] {p : E → B}
    (hp : IsLocallyTrivial p F) (h : E' ≃ₜ E) : IsLocallyTrivial (p ∘ h) F := by
  intro b
  obtain ⟨U, hU, hb, φ, hφ⟩ := hp b
  let e : (p ∘ h) ⁻¹' U ≃ₜ p ⁻¹' U :=
    { toFun := fun x => ⟨h x, x.2⟩
      invFun := fun y => ⟨h.symm y, by
        change p (h (h.symm y)) ∈ U
        rw [h.apply_symm_apply]
        exact y.2⟩
      left_inv := fun x => Subtype.ext (h.symm_apply_apply x)
      right_inv := fun y => Subtype.ext (h.apply_symm_apply y)
      continuous_toFun := by fun_prop
      continuous_invFun := Continuous.subtype_mk (h.symm.continuous.comp continuous_subtype_val)
        fun y => by
          change p (h (h.symm y)) ∈ U
          rw [h.apply_symm_apply]
          exact y.2 }
  exact ⟨U, hU, hb, e.trans φ, fun x => hφ (e x)⟩

/-- Local triviality is invariant under homeomorphisms of the fibre. -/
theorem IsLocallyTrivial.congr_fiber {F' : Type*} [TopologicalSpace F'] {p : E → B}
    (hp : IsLocallyTrivial p F) (h : F ≃ₜ F') : IsLocallyTrivial p F' := by
  intro b
  obtain ⟨U, hU, hb, φ, hφ⟩ := hp b
  exact ⟨U, hU, hb, φ.trans ((Homeomorph.refl U).prodCongr h), fun x => hφ x⟩

omit [TopologicalSpace E] [TopologicalSpace B] in
theorem mem_preimage_of_mem_fiber {p : E → B} {U : Set B} {b : B} (hb : b ∈ U)
    (x : p ⁻¹' {b}) : (x : E) ∈ p ⁻¹' U := by
  change p x ∈ U
  rw [show p x = b from x.2]
  exact hb

/-- The fibre `p⁻¹(b)` of a map with a trivialization `φ : p⁻¹(U) ≃ₜ U × F` over `U ∋ b` is
homeomorphic to `F`. -/
def fiberHomeomorphOfTriv {p : E → B} {U : Set B} (φ : p ⁻¹' U ≃ₜ U × F)
    (hφ : ∀ x, ((φ x).1 : B) = p x) {b : B} (hb : b ∈ U) : p ⁻¹' {b} ≃ₜ F where
  toFun x := (φ ⟨x, mem_preimage_of_mem_fiber hb x⟩).2
  invFun f := ⟨φ.symm (⟨b, hb⟩, f), show p (φ.symm (⟨b, hb⟩, f) : E) = b by
    rw [← hφ, Homeomorph.apply_symm_apply]⟩
  left_inv x := by
    apply Subtype.ext
    have hx : (⟨b, hb⟩, (φ ⟨x, mem_preimage_of_mem_fiber hb x⟩).2) =
        φ ⟨x, mem_preimage_of_mem_fiber hb x⟩ :=
      Prod.ext (Subtype.ext ((show p x = b from x.2).symm.trans
        (hφ ⟨x, mem_preimage_of_mem_fiber hb x⟩).symm)) rfl
    change ((φ.symm (⟨b, hb⟩, (φ ⟨x, mem_preimage_of_mem_fiber hb x⟩).2) : p ⁻¹' U) : E) = x
    rw [hx, Homeomorph.symm_apply_apply]
  right_inv f := by
    change (φ ⟨(φ.symm (⟨b, hb⟩, f) : E), _⟩).2 = f
    rw [Subtype.coe_eta, Homeomorph.apply_symm_apply]
  continuous_toFun := continuous_snd.comp (φ.continuous.comp
    (continuous_subtype_val.subtype_mk _))
  continuous_invFun := (continuous_subtype_val.comp (φ.symm.continuous.comp
    (continuous_const.prodMk continuous_id))).subtype_mk _

/-- **The fibres of a locally trivial map with fibre `F` are homeomorphic to `F`.** -/
theorem IsLocallyTrivial.nonempty_fiberHomeomorph {p : E → B} (hp : IsLocallyTrivial p F)
    (b : B) : Nonempty (p ⁻¹' {b} ≃ₜ F) := by
  obtain ⟨U, -, hb, φ, hφ⟩ := hp b
  exact ⟨fiberHomeomorphOfTriv φ hφ hb⟩

/-- A homeomorphism of the fibre `p⁻¹(b)` of a locally trivial map with `F` (chosen). -/
def IsLocallyTrivial.fiberHomeomorph {p : E → B} (hp : IsLocallyTrivial p F) (b : B) :
    p ⁻¹' {b} ≃ₜ F :=
  (hp.nonempty_fiberHomeomorph b).some

/-! ### Serre fibrations -/

/-- The **open box** `Jᴺ = Iᴺ × {0} ∪ ∂Iᴺ × I`: the boundary of the cylinder `Iᴺ × I` without
its top face `Iᴺ × {1}`. -/
def openBox (N : Type*) : Set ((N → I) × I) :=
  {z | z.2 = 0 ∨ z.1 ∈ Cube.boundary N}

theorem mem_openBox {N : Type*} {z : (N → I) × I} :
    z ∈ openBox N ↔ z.2 = 0 ∨ z.1 ∈ Cube.boundary N :=
  Iff.rfl

theorem mk_zero_mem_openBox {N : Type*} (x : N → I) : (x, (0 : I)) ∈ openBox N :=
  Or.inl rfl

theorem mk_mem_openBox_of_mem_boundary {N : Type*} {x : N → I} (hx : x ∈ Cube.boundary N)
    (t : I) : (x, t) ∈ openBox N :=
  Or.inr hx

/-- **Serre fibrations**: `p` has the homotopy lifting property for the cubes `Iⁿ`, relative to
the boundary: every map `H : Iⁿ × I → B` with a lift `g` given and continuous on the open box
`Jⁿ = Iⁿ × {0} ∪ ∂Iⁿ × I` has a lift `G : Iⁿ × I → E` extending `g`. -/
def IsSerreFibration (p : E → B) : Prop :=
  ∀ (n : ℕ) (H : C((Fin n → I) × I, B)) (g : (Fin n → I) × I → E),
    ContinuousOn g (openBox (Fin n)) → (∀ z ∈ openBox (Fin n), p (g z) = H z) →
      ∃ G : C((Fin n → I) × I, E), (∀ z, p (G z) = H z) ∧ ∀ z ∈ openBox (Fin n), G z = g z

/-- Reindexing a cube along a bijection of the index types. -/
def cubeCongr {N M : Type*} (e : N ≃ M) : (N → I) ≃ₜ (M → I) where
  toFun w j := w (e.symm j)
  invFun v i := v (e i)
  left_inv w := funext fun i => by simp
  right_inv v := funext fun j => by simp
  continuous_toFun := continuous_pi fun _ => continuous_apply _
  continuous_invFun := continuous_pi fun _ => continuous_apply _

theorem cubeCongr_apply {N M : Type*} (e : N ≃ M) (w : N → I) (j : M) :
    cubeCongr e w j = w (e.symm j) :=
  rfl

theorem cubeCongr_mem_boundary_iff {N M : Type*} (e : N ≃ M) {w : N → I} :
    cubeCongr e w ∈ Cube.boundary M ↔ w ∈ Cube.boundary N := by
  constructor
  · rintro ⟨j, hj⟩
    exact ⟨e.symm j, hj⟩
  · rintro ⟨i, hi⟩
    refine ⟨e i, ?_⟩
    rw [cubeCongr_apply, e.symm_apply_apply]
    exact hi

/-- **The lifting property of a Serre fibration for cubes indexed by any finite type.** -/
theorem IsSerreFibration.exists_lift {p : E → B} (hp : IsSerreFibration p) {N : Type*} [Finite N]
    (H : C((N → I) × I, B)) (g : (N → I) × I → E) (hg : ContinuousOn g (openBox N))
    (hpg : ∀ z ∈ openBox N, p (g z) = H z) :
    ∃ G : C((N → I) × I, E), (∀ z, p (G z) = H z) ∧ ∀ z ∈ openBox N, G z = g z := by
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin N
  let Φ : (N → I) × I ≃ₜ (Fin n → I) × I := (cubeCongr e).prodCongr (Homeomorph.refl I)
  have hΦ : ∀ z, Φ.symm z ∈ openBox N ↔ z ∈ openBox (Fin n) := by
    rintro ⟨w, t⟩
    change (t = 0 ∨ (cubeCongr e).symm w ∈ Cube.boundary N) ↔ (t = 0 ∨ w ∈ Cube.boundary (Fin n))
    rw [← cubeCongr_mem_boundary_iff e, Homeomorph.apply_symm_apply]
  obtain ⟨G, hG, hGg⟩ := hp n (H.comp (Φ.symm : C((Fin n → I) × I, (N → I) × I))) (g ∘ Φ.symm)
    (hg.comp Φ.symm.continuous.continuousOn fun z hz => (hΦ z).2 hz)
    (fun z hz => hpg _ ((hΦ z).2 hz))
  refine ⟨G.comp (Φ : C((N → I) × I, (Fin n → I) × I)), fun z => ?_, fun z hz => ?_⟩
  · simpa using hG (Φ z)
  · have := hGg (Φ z) ((hΦ (Φ z)).1 (by simpa using hz))
    simpa using this

/-! ### The absolute lifting property -/

section Absolute

variable {N : Type*} [Fintype N]

/-- Shrinking the cube by the factor `1/2` about its centre. -/
def cubeShrink (x : N → I) : N → I :=
  fun j => ⟨(x j : ℝ) / 2 + 1 / 4, by constructor <;> linarith [(x j).2.1, (x j).2.2]⟩

omit [Fintype N] in
theorem continuous_cubeShrink : Continuous (cubeShrink (N := N)) :=
  continuous_pi fun j => ((continuous_subtype_val.comp (continuous_apply j)).div_const _
    |>.add continuous_const).subtype_mk _

theorem cubeDist_cubeShrink (x : N → I) : cubeDist (cubeShrink x) = cubeDist x / 2 := by
  have : (fun j => (cubeShrink x j : ℝ) - 1 / 2) = (2 : ℝ)⁻¹ • fun j => (x j : ℝ) - 1 / 2 := by
    funext j
    simp only [cubeShrink, Pi.smul_apply, smul_eq_mul]
    ring
  rw [cubeDist, this, norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num), cubeDist]
  ring

omit [Fintype N] in
theorem cubeScale_cubeShrink [Finite N] (x : N → I) : cubeScale (1 / 4) (cubeShrink x) = x := by
  have := Fintype.ofFinite N
  have hd : cubeDist (cubeShrink x) ≤ 1 / 4 := by
    rw [cubeDist_cubeShrink]
    linarith [cubeDist_le_half x]
  funext j
  apply Subtype.ext
  rw [coe_cubeScale (by norm_num) hd]
  simp only [cubeShrink]
  ring

/-- The map of pairs `(Iᴺ × I, Jᴺ) → (Iᴺ × I, Iᴺ × {0})`: stretch the cube of radius `1/4` onto
`Iᴺ`, and scale the time by a factor vanishing on `∂Iᴺ`. -/
def boxFold (z : (N → I) × I) : (N → I) × I :=
  (cubeScale (1 / 4) z.1, z.2 * Set.projIcc 0 1 zero_le_one (2 - 4 * cubeDist z.1))

theorem continuous_boxFold : Continuous (boxFold (N := N)) :=
  (((continuous_cubeScale (P := Unit) (r := fun _ => (1 / 4 : ℝ)) continuous_const
      (fun _ => by norm_num)).comp (Continuous.prodMk (continuous_const (y := ()))
        continuous_id)).comp continuous_fst).prodMk
    (continuous_snd.mul (continuous_projIcc.comp (continuous_const.sub
      (continuous_const.mul (continuous_cubeDist.comp continuous_fst)))))

theorem boxFold_snd_of_mem_openBox {z : (N → I) × I} (hz : z ∈ openBox N) : (boxFold z).2 = 0 := by
  rcases hz with h | h
  · simp [boxFold, h]
  · simp only [boxFold, cubeDist_of_mem_boundary h]
    norm_num

theorem boxFold_shrink (z : (N → I) × I) : boxFold (cubeShrink z.1, z.2) = z := by
  have h1 : (1 : ℝ) ≤ 2 - 4 * cubeDist (cubeShrink z.1) := by
    rw [cubeDist_cubeShrink]
    linarith [cubeDist_le_half z.1]
  have h2 : Set.projIcc (0 : ℝ) 1 zero_le_one (2 - 4 * cubeDist (cubeShrink z.1)) = 1 :=
    Set.projIcc_of_right_le _ h1
  simp only [boxFold, cubeScale_cubeShrink, h2, mul_one]

end Absolute

/-- **The absolute homotopy lifting property for cubes**: for a Serre fibration `p`, every
homotopy `H : Iᴺ × I → B` lifts to `E`, given a lift `g₀` of `H(·, 0)`. -/
theorem IsSerreFibration.exists_lift_of_bot {p : E → B} (hp : IsSerreFibration p) {N : Type*}
    [Finite N] (H : C((N → I) × I, B)) (g₀ : C(N → I, E)) (hg₀ : ∀ x, p (g₀ x) = H (x, 0)) :
    ∃ G : C((N → I) × I, E), (∀ z, p (G z) = H z) ∧ ∀ x, G (x, 0) = g₀ x := by
  have := Fintype.ofFinite N
  let φ : C((N → I) × I, (N → I) × I) := ⟨boxFold, continuous_boxFold⟩
  obtain ⟨G, hG, hGg⟩ := hp.exists_lift (H.comp φ) (fun z => g₀ (boxFold z).1)
    (g₀.continuous.comp (continuous_fst.comp continuous_boxFold)).continuousOn
    (fun z hz => by
      change p (g₀ (boxFold z).1) = H (boxFold z)
      rw [hg₀]
      congr 1
      exact Prod.ext rfl (boxFold_snd_of_mem_openBox hz).symm)
  let ψ : C((N → I) × I, (N → I) × I) :=
    ⟨fun z => (cubeShrink z.1, z.2), (continuous_cubeShrink.comp continuous_fst).prodMk
      continuous_snd⟩
  refine ⟨G.comp ψ, fun z => ?_, fun x => ?_⟩
  · change p (G (cubeShrink z.1, z.2)) = H z
    rw [hG]
    change H (boxFold (cubeShrink z.1, z.2)) = H z
    rw [boxFold_shrink]
  · change G (cubeShrink x, 0) = g₀ x
    rw [hGg _ (mk_zero_mem_openBox _)]
    have h := boxFold_shrink (x, (0 : I))
    change g₀ (boxFold (cubeShrink x, 0)).1 = g₀ x
    rw [h]

end Morse.Homotopy
