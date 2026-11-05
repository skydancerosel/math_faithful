import Morse
import RoundTrip.Check
import RoundTrip.Blind.V6_3
import RoundTrip.Bridge

open Bundle Manifold
open scoped ContDiff Manifold

namespace RoundTrip.V6_3

/-- The project's statement: the three listed rules, universes instantiated at 0. -/
def A : Prop :=
  type_of% @Morse.cov_smul_left.{0,0,0} ∧ type_of% @Morse.cov_add_right.{0,0,0} ∧
    type_of% @Morse.cov_smul_right.{0,0,0}

theorem A_holds : A := ⟨@Morse.cov_smul_left, @Morse.cov_add_right, @Morse.cov_smul_right⟩

/-- Parts (i) and (ii) of B (everything except the converse (iii)) follow from A. -/
theorem A_to_B_rules (hA : A) (n : ℕ) (M : Type) [TopologicalSpace M] [ChartedSpace (Rn n) M]
    [IsManifold 𝓘(ℝ, Rn n) ∞ M]
    (cov : CovariantDerivative 𝓘(ℝ, Rn n) (Rn n) (TangentSpace 𝓘(ℝ, Rn n) : M → Type))
    (hcov : IsGlobalConn cov) :
    (∀ (p : M) (Xp : TangentSpace 𝓘(ℝ, Rn n) p) (Y Y' : (q : M) → TangentSpace 𝓘(ℝ, Rn n) q) (f : M → ℝ),
        IsSmoothVF Y → IsSmoothVF Y' → ContMDiff 𝓘(ℝ, Rn n) 𝓘(ℝ) ∞ f →
        cov (fun q => Y q + Y' q) p Xp = cov Y p Xp + cov Y' p Xp ∧
        cov (fun q => f q • Y q) p Xp = dirDeriv (fun _ => Xp) f p • Y p + f p • cov Y p Xp) ∧
      IsMilnorRules (nab cov) := by
  obtain ⟨hsl, har, hsr⟩ := hA
  have mdY : ∀ {Y : (q : M) → TangentSpace 𝓘(ℝ, Rn n) q}, IsSmoothVF Y → ∀ p : M,
      MDifferentiableAt 𝓘(ℝ, Rn n) (𝓘(ℝ, Rn n)).tangent
        (fun q => (⟨q, Y q⟩ : TangentBundle 𝓘(ℝ, Rn n) M)) p :=
    fun hY p => (hY p).mdifferentiableAt (by simp)
  have mdf : ∀ {f : M → ℝ}, ContMDiff 𝓘(ℝ, Rn n) 𝓘(ℝ) ∞ f → ∀ p : M,
      MDifferentiableAt 𝓘(ℝ, Rn n) 𝓘(ℝ) f p := fun hf p => (hf p).mdifferentiableAt (by simp)
  have hadd : ∀ (p : M) (Xp : TangentSpace 𝓘(ℝ, Rn n) p) (Y Y' : (q : M) → TangentSpace 𝓘(ℝ, Rn n) q),
      IsSmoothVF Y → IsSmoothVF Y' →
      cov (fun q => Y q + Y' q) p Xp = cov Y p Xp + cov Y' p Xp := by
    intro p Xp Y Y' hY hY'
    have := har cov (mdY hY p) (mdY hY' p) (fun _ => Xp)
    exact this
  have hlei : ∀ (p : M) (Xp : TangentSpace 𝓘(ℝ, Rn n) p) (Y : (q : M) → TangentSpace 𝓘(ℝ, Rn n) q)
      (f : M → ℝ), IsSmoothVF Y → ContMDiff 𝓘(ℝ, Rn n) 𝓘(ℝ) ∞ f →
      cov (fun q => f q • Y q) p Xp = dirDeriv (fun _ => Xp) f p • Y p + f p • cov Y p Xp := by
    intro p Xp Y f hY hf
    have := hsr cov (mdf hf p) (mdY hY p) (fun _ => Xp)
    exact this
  have hsm : ∀ X Y, IsSmoothVF X → IsSmoothVF Y → IsSmoothVF (nab cov X Y) := by
    intro X Y hX hY
    have h1 := hcov.contMDiff (σ := Y) (by
      rw [contMDiffOn_univ]; exact hY.of_le (by simp))
    rw [contMDiffOn_univ] at h1
    exact ContMDiff.clm_bundle_apply (b := id) h1 hX
  refine ⟨fun p Xp Y Y' f hY hY' hf => ⟨hadd p Xp Y Y' hY hY', hlei p Xp Y f hY hf⟩,
    hsm, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro X X' Y _ _ _; funext p; exact map_add _ _ _
  · intro a X Y _ _; funext p; exact map_smul _ _ _
  · intro X Y Y' _ hY hY'; funext p; exact hadd p (X p) Y Y' hY hY'
  · intro a X Y _ hY; funext p
    have := hlei p (X p) Y (fun _ => a) hY contMDiff_const
    simp only [dirDeriv, mfderiv_const] at this
    rw [nab, nab, this]
    show (0 : ℝ) • Y p + _ = _
    rw [zero_smul, zero_add]
  · intro f X Y _ _ _; funext p; exact hsl cov f X Y p
  · intro f X Y hf _ hY; funext p; exact hlei p (X p) Y f hY hf

/-- B ⇒ A holds only because A is provable outright (Mathlib's `CovariantDerivative` axioms):
`A` is about arbitrary models `I`, while `B` covers only manifolds modelled on `ℝⁿ`. -/
theorem B_to_A : B → A := by
  intro _
  refine ⟨?_, ?_, ?_⟩
  · intro E _ _ H _ I M _ _ _ cov f X Y x
    exact map_smul (cov Y x) (f x) (X x)
  · intro E _ _ H _ I M _ _ _ cov Y Y' x hY hY' X
    rw [cov.isCovariantDerivativeOnUniv.add hY hY']; rfl
  · intro E _ _ H _ I M _ _ _ cov f Y x hf hY X
    rw [cov.isCovariantDerivativeOnUniv.leibniz hY hf]; simp [add_comm]

#rt_check RoundTrip.V6_3.A_to_B_rules [Morse.cov_smul_left, Morse.cov_add_right, Morse.cov_smul_right]
#rt_check RoundTrip.V6_3.B_to_A [Morse.cov_smul_left, Morse.cov_add_right, Morse.cov_smul_right]
#rt_overlap RoundTrip.V6_3.B_to_A [Morse.cov_smul_left, Morse.cov_add_right, Morse.cov_smul_right]

/-! ## The embedded special case

B is specialized to `M = ↥N` (`RoundTrip.Bridge.Sub hN`) for a slice submanifold `N ⊆ V` with
model `ℝⁿ`: parts (i)+(ii) at the induced connection `Bridge.conn` (`B_emb_rules`), part (iii)
(every operation obeying rules (1)–(4) is `⊢` of a smooth Mathlib connection) on `↥N`. Unlike the
other §8 items, A is not an embedded statement: it is about arbitrary Mathlib connections on
arbitrary manifolds, so the embedded case only re-locates the known gap. A ⇒ `B_emb_rules` holds
(by `A_to_B_rules`); part (iii) on `↥N` is not in A. On `↥N` it could be proved outright (the
difference `D − ∇^{conn}` is tensorial by rules (2)–(4); expanding smooth fields in the global
frame `Eᵢ = P eᵢ` (`Bridge.frame`) makes it pointwise, and `conn` plus that tensor is a smooth
Mathlib connection), but that construction is in neither the project nor the Bridge and would not
use A; it was not attempted. No converse is meaningful: `B_emb` is about one manifold, A about
all manifolds and all models. -/

/-- B on embedded manifolds: (i)+(ii) for the induced connection of `↥N`, and (iii) on `↥N`. -/
def B_emb : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (W : Type) [NormedAddCommGroup W] [NormedSpace ℝ W] (n : ℕ)
    (N : Set V) (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N),
    ((∀ (p : Bridge.Sub hN) (Xp : TangentSpace 𝓘(ℝ, Rn n) p)
        (Y Y' : (q : Bridge.Sub hN) → TangentSpace 𝓘(ℝ, Rn n) q) (f : Bridge.Sub hN → ℝ),
        IsSmoothVF Y → IsSmoothVF Y' → ContMDiff 𝓘(ℝ, Rn n) 𝓘(ℝ) ∞ f →
        Bridge.conn (fun q => Y q + Y' q) p Xp = Bridge.conn Y p Xp + Bridge.conn Y' p Xp ∧
        Bridge.conn (fun q => f q • Y q) p Xp =
          dirDeriv (fun _ => Xp) f p • Y p + f p • Bridge.conn Y p Xp) ∧
      IsMilnorRules (nab (Bridge.conn (hN := hN)))) ∧
    (∀ D : ((p : Bridge.Sub hN) → TangentSpace 𝓘(ℝ, Rn n) p) →
        ((p : Bridge.Sub hN) → TangentSpace 𝓘(ℝ, Rn n) p) →
        ((p : Bridge.Sub hN) → TangentSpace 𝓘(ℝ, Rn n) p), IsMilnorRules D →
      ∃ cov : CovariantDerivative 𝓘(ℝ, Rn n) (Rn n)
          (TangentSpace 𝓘(ℝ, Rn n) : Bridge.Sub hN → Type), IsGlobalConn cov ∧
        ∀ X Y, IsSmoothVF X → IsSmoothVF Y → nab cov X Y = D X Y)

/-- Parts (i)+(ii) of `B_emb`: the pointwise and global rules for the induced connection. -/
def B_emb_rules : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (W : Type) [NormedAddCommGroup W] [NormedSpace ℝ W] (n : ℕ)
    (N : Set V) (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N),
    (∀ (p : Bridge.Sub hN) (Xp : TangentSpace 𝓘(ℝ, Rn n) p)
        (Y Y' : (q : Bridge.Sub hN) → TangentSpace 𝓘(ℝ, Rn n) q) (f : Bridge.Sub hN → ℝ),
        IsSmoothVF Y → IsSmoothVF Y' → ContMDiff 𝓘(ℝ, Rn n) 𝓘(ℝ) ∞ f →
        Bridge.conn (fun q => Y q + Y' q) p Xp = Bridge.conn Y p Xp + Bridge.conn Y' p Xp ∧
        Bridge.conn (fun q => f q • Y q) p Xp =
          dirDeriv (fun _ => Xp) f p • Y p + f p • Bridge.conn Y p Xp) ∧
      IsMilnorRules (nab (Bridge.conn (hN := hN)))

/-- `B_emb` is a special case of B (the induced connection is smooth, `Bridge.conn_contMDiff`). -/
theorem B_to_B_emb : B → B_emb := fun hB _ _ _ _ _ _ _ n _ hN =>
  ⟨(hB n (Bridge.Sub hN)).1 Bridge.conn Bridge.conn_contMDiff, (hB n (Bridge.Sub hN)).2⟩

theorem B_emb_to_rules : B_emb → B_emb_rules := fun h V _ _ _ W _ _ n N hN => (h V W n N hN).1

/-- **A implies parts (i)+(ii) of B on embedded manifolds** (`A_to_B_rules` at `Bridge.conn`).
Part (iii) of `B_emb` is not in A. -/
theorem A_to_B_emb_rules : A → B_emb_rules := fun hA _ _ _ _ _ _ _ n _ hN =>
  A_to_B_rules hA n (Bridge.Sub hN) Bridge.conn Bridge.conn_contMDiff

#rt_check RoundTrip.V6_3.A_to_B_emb_rules [Morse.cov_smul_left, Morse.cov_add_right, Morse.cov_smul_right]

end RoundTrip.V6_3
