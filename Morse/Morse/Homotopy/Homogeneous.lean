import Mathlib

/-!
# Local trivializations from local sections of an orbit map

The fibre bundles Milnor uses in §§23–24 (`U(m) → U(m+1) → S^{2m+1}`, `U(m) → U(2m) → U(2m)/U(m)`,
`U(m) → V → G_m(ℂ^{2m})`, `O(m) → O(m+1) → Sᵐ`, …) are all of one kind: a topological group `G`
acts on a space `E` and on a space `B`, and `p : E → B` is equivariant. Steenrod (*The Topology of
Fibre Bundles*, §7), whom Milnor cites on p. 128, proves that a coset map `G → G/H` is a bundle
when it has local cross-sections; this file isolates that argument.

If `s : U → G` is continuous with `s b • b₀ = b` (a *local section of the orbit map*
`g ↦ g • b₀` over `U`), then
`p⁻¹(U) ≅ U × p⁻¹(b₀)`, `x ↦ (p x, s(p x)⁻¹ • x)`, with inverse `(b, y) ↦ s b • y`
(`Morse.Homotopy.orbitTriv`). If moreover `G` acts transitively on `B`, a section near `b₀` is
moved by translations to a section near every point (`s'(b) = g · s(g⁻¹ • b)`), so `p` is
locally trivial with fibre `p⁻¹(b₀)` (`Morse.Homotopy.exists_triv_of_orbitSection`; the
conclusion is the definition of `Morse.Homotopy.IsLocallyTrivial` in
`Morse/Homotopy/Fibration.lean`, restated in `Morse/Homotopy/BundleHomotopy.lean`).

The construction of the sections themselves (explicit formulas, Gram–Schmidt) is in
`Morse/Homotopy/Stiefel.lean` and `Morse/Homotopy/Grassmannian.lean`.
-/

open Set Function Topology

noncomputable section

namespace Morse.Homotopy

variable {E B F : Type*} [TopologicalSpace E] [TopologicalSpace B] [TopologicalSpace F]

/-- **A homeomorphism `p⁻¹(U) ≃ U × F` over `U`** from continuous maps `φ : p⁻¹(U) → F` and
`ψ : U × F → E` that are mutually inverse in the evident sense. -/
def trivOfInverse (p : E → B) (hp : Continuous p) (U : Set B) (φ : p ⁻¹' U → F)
    (ψ : U × F → E) (hφ : Continuous φ) (hψ : Continuous ψ) (hpψ : ∀ q, p (ψ q) = q.1)
    (hφψ : ∀ q, φ ⟨ψ q, show p (ψ q) ∈ U from (hpψ q).symm ▸ q.1.2⟩ = q.2)
    (hψφ : ∀ x : p ⁻¹' U, ψ (⟨p x, x.2⟩, φ x) = x) : p ⁻¹' U ≃ₜ U × F where
  toFun x := (⟨p x, x.2⟩, φ x)
  invFun q := ⟨ψ q, show p (ψ q) ∈ U from (hpψ q).symm ▸ q.1.2⟩
  left_inv x := Subtype.ext (hψφ x)
  right_inv q := by
    refine Prod.ext (Subtype.ext (hpψ q)) (hφψ q)
  continuous_toFun :=
    ((hp.comp continuous_subtype_val).subtype_mk _).prodMk hφ
  continuous_invFun := hψ.subtype_mk _

@[simp]
theorem trivOfInverse_apply_fst (p : E → B) (hp : Continuous p) (U : Set B) (φ : p ⁻¹' U → F)
    (ψ : U × F → E) (hφ : Continuous φ) (hψ : Continuous ψ) (hpψ : ∀ q, p (ψ q) = q.1) (hφψ)
    (hψφ) (x : p ⁻¹' U) :
    (trivOfInverse p hp U φ ψ hφ hψ hpψ hφψ hψφ x).1 = ⟨p x, x.2⟩ :=
  rfl

section Orbit

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MulAction G E] [MulAction G B] [ContinuousSMul G E] [ContinuousSMul G B]

omit [TopologicalSpace E] [TopologicalSpace B] [TopologicalSpace G] [IsTopologicalGroup G]
  [ContinuousSMul G E] [ContinuousSMul G B] in
/-- The points of the fibre over `b₀` reached from `x` by the section. -/
theorem smul_mem_fiber {p : E → B} (hequiv : ∀ (g : G) x, p (g • x) = g • p x) {b₀ : B}
    {U : Set B} {s : U → G} (hs : ∀ b, s b • b₀ = b) (x : p ⁻¹' U) :
    (s ⟨p x, x.2⟩)⁻¹ • (x : E) ∈ p ⁻¹' {b₀} := by
  change p _ = b₀
  rw [hequiv]
  calc (s ⟨p x, x.2⟩)⁻¹ • p (x : E) = (s ⟨p x, x.2⟩)⁻¹ • (s ⟨p x, x.2⟩ • b₀) := by rw [hs]
    _ = b₀ := inv_smul_smul _ _

/-- **The local trivialization defined by a local section of the orbit map**:
`p⁻¹(U) ≃ U × p⁻¹(b₀)`, `x ↦ (p x, s(p x)⁻¹ • x)`. -/
def orbitTriv (p : E → B) (hp : Continuous p) (hequiv : ∀ (g : G) x, p (g • x) = g • p x)
    (b₀ : B) (U : Set B) (s : U → G) (hsc : Continuous s) (hs : ∀ b, s b • b₀ = b) :
    p ⁻¹' U ≃ₜ U × p ⁻¹' {b₀} :=
  trivOfInverse p hp U (fun x => ⟨(s ⟨p x, x.2⟩)⁻¹ • (x : E), smul_mem_fiber hequiv hs x⟩)
    (fun q => s q.1 • (q.2 : E))
    (by
      refine Continuous.subtype_mk (Continuous.smul ?_ continuous_subtype_val) _
      exact (hsc.comp ((hp.comp continuous_subtype_val).subtype_mk _)).inv)
    ((hsc.comp continuous_fst).smul (continuous_subtype_val.comp continuous_snd))
    (fun q => by
      rw [hequiv, show p (q.2 : E) = b₀ from q.2.2, hs])
    (fun q => by
      have h1 : p (s q.1 • (q.2 : E)) = q.1 := by
        rw [hequiv, show p (q.2 : E) = b₀ from q.2.2, hs]
      apply Subtype.ext
      change (s ⟨p (s q.1 • (q.2 : E)), _⟩)⁻¹ • (s q.1 • (q.2 : E)) = q.2
      rw [show ∀ h, s ⟨p (s q.1 • (q.2 : E)), h⟩ = s q.1 from
        fun h => congrArg s (Subtype.ext h1), inv_smul_smul])
    (fun x => by simp)

omit [ContinuousSMul G B] in
@[simp]
theorem orbitTriv_apply_fst (p : E → B) (hp : Continuous p)
    (hequiv : ∀ (g : G) x, p (g • x) = g • p x) (b₀ : B) (U : Set B) (s : U → G)
    (hsc : Continuous s) (hs : ∀ b, s b • b₀ = b) (x : p ⁻¹' U) :
    (orbitTriv p hp hequiv b₀ U s hsc hs x).1 = ⟨p x, x.2⟩ :=
  rfl

/-- **Local triviality of an equivariant map over a homogeneous space**: if `G` acts transitively
on `B` and the orbit map `g ↦ g • b₀` has a continuous section over a neighbourhood of `b₀`, then
every point of `B` has an open neighbourhood `U` with `p⁻¹(U) ≅ U × p⁻¹(b₀)` over `U`. -/
theorem exists_triv_of_orbitSection (p : E → B) (hp : Continuous p)
    (hequiv : ∀ (g : G) x, p (g • x) = g • p x) (b₀ : B) (htrans : ∀ b, ∃ g : G, g • b₀ = b)
    {U₀ : Set B} (hU₀ : IsOpen U₀) (hb₀ : b₀ ∈ U₀) (s₀ : U₀ → G) (hs₀c : Continuous s₀)
    (hs₀ : ∀ b, s₀ b • b₀ = b) (b : B) :
    ∃ U : Set B, IsOpen U ∧ b ∈ U ∧
      ∃ φ : p ⁻¹' U ≃ₜ U × p ⁻¹' {b₀}, ∀ x, (φ x).1 = ⟨p x, x.2⟩ := by
  obtain ⟨g, rfl⟩ := htrans b
  let U : Set B := (fun b' => g⁻¹ • b') ⁻¹' U₀
  have hU : IsOpen U := hU₀.preimage (continuous_const_smul _)
  have hmem : ∀ b' : U, g⁻¹ • (b' : B) ∈ U₀ := fun b' => b'.2
  let s : U → G := fun b' => g * s₀ ⟨g⁻¹ • (b' : B), hmem b'⟩
  have hsc : Continuous s :=
    continuous_const.mul (hs₀c.comp
      (((continuous_const_smul _).comp continuous_subtype_val).subtype_mk _))
  have hs : ∀ b', s b' • b₀ = b' := by
    intro b'
    simp only [s, mul_smul, hs₀, smul_inv_smul]
  refine ⟨U, hU, ?_, orbitTriv p hp hequiv b₀ U s hsc hs, fun x => rfl⟩
  change g⁻¹ • g • b₀ ∈ U₀
  rwa [inv_smul_smul]

/-- The same with the fibre `p⁻¹(b₀)` replaced by any space homeomorphic to it. -/
theorem exists_triv_of_orbitSection' (p : E → B) (hp : Continuous p)
    (hequiv : ∀ (g : G) x, p (g • x) = g • p x) (b₀ : B) (htrans : ∀ b, ∃ g : G, g • b₀ = b)
    {U₀ : Set B} (hU₀ : IsOpen U₀) (hb₀ : b₀ ∈ U₀) (s₀ : U₀ → G) (hs₀c : Continuous s₀)
    (hs₀ : ∀ b, s₀ b • b₀ = b) (e : p ⁻¹' {b₀} ≃ₜ F) (b : B) :
    ∃ U : Set B, IsOpen U ∧ b ∈ U ∧ ∃ φ : p ⁻¹' U ≃ₜ U × F, ∀ x, (φ x).1 = ⟨p x, x.2⟩ := by
  obtain ⟨U, hU, hb, φ, hφ⟩ :=
    exists_triv_of_orbitSection p hp hequiv b₀ htrans hU₀ hb₀ s₀ hs₀c hs₀ b
  exact ⟨U, hU, hb, φ.trans ((Homeomorph.refl U).prodCongr e), fun x => hφ x⟩

end Orbit

end Morse.Homotopy
