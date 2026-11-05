import Mathlib.Algebra.Homology.Homotopy
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Category.ModuleCat.Abelian

/-!
# Chain maps and homotopies of `ℕ`-indexed chain complexes, degree by degree

Small constructors for morphisms and homotopies of chain complexes indexed by `ℕ` (homological
grading, `ComplexShape.down ℕ`), from their components in each degree:

* `Morse.Homology.natHomMk`: a chain map from components `fₙ` with `fₙ₊₁ ≫ d = d ≫ fₙ`;
* `Morse.Homology.natHomotopyMk`: a homotopy `f ≃ g` from components `hₙ : Cₙ ⟶ Dₙ₊₁` with
  `f₀ = h₀ ≫ d + g₀` and `fₙ₊₁ = d ≫ hₙ + hₙ₊₁ ≫ d + gₙ₊₁`.

(Mathlib's `Homotopy.mkInductive` builds a homotopy by induction on the degree; here all the
components are given at once.)

## Subcomplexes and quotient complexes of complexes of modules

For a chain complex `K` of `R`-modules and submodules `Lₙ ⊆ Kₙ` with `d(Lₙ₊₁) ⊆ Lₙ`:

* `Morse.Homology.subcomplex K L hL` with inclusion `Morse.Homology.subcomplexι`, and
  `Morse.Homology.quotient K L hL` with projection `Morse.Homology.quotientπ` (degreewise the
  quotient modules `Kₙ / Lₙ`);
* maps and homotopies preserving the submodules descend to the quotients
  (`Morse.Homology.quotientMap`, `Morse.Homology.quotientHomotopy`) and restrict to the
  subcomplexes (`Morse.Homology.subcomplexMap`);
* if `f : K' ⟶ K` is degreewise injective with image `L`, the quotient is a cokernel of `f`
  (`Morse.Homology.isColimitQuotient`): this identifies the concrete quotient with the cokernels
  used to define relative chains.
-/

open CategoryTheory Limits

namespace Morse.Homology

variable {V : Type*} [Category* V] [Preadditive V]

/-- A morphism of `ℕ`-indexed chain complexes from its components. -/
@[simps]
def natHomMk {C D : ChainComplex V ℕ} (f : ∀ n, C.X n ⟶ D.X n)
    (comm : ∀ n, f (n + 1) ≫ D.d (n + 1) n = C.d (n + 1) n ≫ f n) : C ⟶ D where
  f := f
  comm' := by
    rintro i j (rfl : j + 1 = i)
    exact comm j

/-- A homotopy between morphisms of `ℕ`-indexed chain complexes from its components
`hₙ : Cₙ ⟶ Dₙ₊₁`. -/
def natHomotopyMk {C D : ChainComplex V ℕ} {f g : C ⟶ D} (h : ∀ n, C.X n ⟶ D.X (n + 1))
    (h₀ : f.f 0 = h 0 ≫ D.d 1 0 + g.f 0)
    (hsucc : ∀ n, f.f (n + 1) = C.d (n + 1) n ≫ h n + h (n + 1) ≫ D.d (n + 2) (n + 1) +
      g.f (n + 1)) :
    Homotopy f g where
  hom i j := if hij : i + 1 = j then h i ≫ eqToHom (congrArg D.X hij) else 0
  zero i j hij := dif_neg hij
  comm i := by
    cases i with
    | zero =>
      rw [Homotopy.dNext_zero_chainComplex, Homotopy.prevD_chainComplex, zero_add, dif_pos rfl,
        eqToHom_refl, Category.comp_id]
      exact h₀
    | succ n =>
      rw [Homotopy.dNext_succ_chainComplex, Homotopy.prevD_chainComplex, dif_pos rfl,
        dif_pos rfl, eqToHom_refl, eqToHom_refl, Category.comp_id, Category.comp_id]
      exact hsucc n

@[simp]
lemma natHomotopyMk_hom {C D : ChainComplex V ℕ} {f g : C ⟶ D} (h : ∀ n, C.X n ⟶ D.X (n + 1))
    (h₀ : f.f 0 = h 0 ≫ D.d 1 0 + g.f 0)
    (hsucc : ∀ n, f.f (n + 1) = C.d (n + 1) n ≫ h n + h (n + 1) ≫ D.d (n + 2) (n + 1) +
      g.f (n + 1)) (n : ℕ) :
    (natHomotopyMk h h₀ hsucc).hom n (n + 1) = h n := by
  simp [natHomotopyMk]

/-! ### Subcomplexes and quotient complexes -/

section Sub

universe u v

variable {R : Type u} [Ring R] (K : ChainComplex (ModuleCat.{v} R) ℕ) (L : ∀ n, Submodule R (K.X n))
  (hL : ∀ n, ∀ x ∈ L (n + 1), K.d (n + 1) n x ∈ L n)

/-- The subcomplex of `K` with `n`-chains the submodule `Lₙ`. -/
noncomputable abbrev subcomplex : ChainComplex (ModuleCat.{v} R) ℕ :=
  ChainComplex.of (fun n ↦ ModuleCat.of R (L n))
    (fun n ↦ ModuleCat.ofHom ((K.d (n + 1) n).hom.restrict (hL n)))
    (fun n ↦ by
      refine ModuleCat.hom_ext (LinearMap.ext fun (x : L (n + 2)) ↦ Subtype.ext ?_)
      change K.d (n + 1) n (K.d (n + 2) (n + 1) x.1) = 0
      rw [← ModuleCat.comp_apply, K.d_comp_d]
      rfl)

lemma subcomplex_X (n : ℕ) : (subcomplex K L hL).X n = ModuleCat.of R (L n) := rfl

lemma subcomplex_d (n : ℕ) : (subcomplex K L hL).d (n + 1) n =
    ModuleCat.ofHom ((K.d (n + 1) n).hom.restrict (hL n)) := by
  simp [subcomplex]

lemma subcomplex_d_apply (n : ℕ) (x : L (n + 1)) :
    (((subcomplex K L hL).d (n + 1) n x : L n) : K.X n) = K.d (n + 1) n x := by
  rw [subcomplex_d]
  rfl

/-- The inclusion of a subcomplex. -/
noncomputable def subcomplexι : subcomplex K L hL ⟶ K :=
  natHomMk (fun n ↦ ModuleCat.ofHom (L n).subtype) (fun n ↦
    ModuleCat.hom_ext (LinearMap.ext fun (x : L (n + 1)) ↦ (subcomplex_d_apply K L hL n x).symm))

@[simp]
lemma subcomplexι_f_apply (n : ℕ) (x : L n) : (subcomplexι K L hL).f n x = x := rfl

instance : Mono (subcomplexι K L hL) :=
  HomologicalComplex.mono_of_mono_f _ fun _ ↦ (ModuleCat.mono_iff_injective _).2
    Subtype.val_injective

/-- The quotient complex `K / L`, with `n`-chains `Kₙ / Lₙ`. -/
noncomputable abbrev quotient : ChainComplex (ModuleCat.{v} R) ℕ :=
  ChainComplex.of (fun n ↦ ModuleCat.of R (K.X n ⧸ L n))
    (fun n ↦ ModuleCat.ofHom ((L (n + 1)).mapQ (L n) (K.d (n + 1) n).hom (hL n)))
    (fun n ↦ by
      refine ModuleCat.hom_ext (Submodule.linearMap_qext _ (LinearMap.ext fun x ↦ ?_))
      change (L n).mkQ (K.d (n + 1) n (K.d (n + 2) (n + 1) x)) = 0
      rw [← ModuleCat.comp_apply, K.d_comp_d]
      exact (L n).mkQ.map_zero)

lemma quotient_X (n : ℕ) : (quotient K L hL).X n = ModuleCat.of R (K.X n ⧸ L n) := rfl

lemma quotient_d (n : ℕ) : (quotient K L hL).d (n + 1) n =
    ModuleCat.ofHom ((L (n + 1)).mapQ (L n) (K.d (n + 1) n).hom (hL n)) := by
  simp [quotient]

/-- The projection onto a quotient complex. -/
noncomputable def quotientπ : K ⟶ quotient K L hL :=
  natHomMk (fun n ↦ ModuleCat.ofHom (L n).mkQ) (fun n ↦ by
    rw [quotient_d]
    rfl)

@[simp]
lemma quotientπ_f_apply (n : ℕ) (x : K.X n) :
    (quotientπ K L hL).f n x = (show K.X n ⧸ L n from Submodule.Quotient.mk x) := rfl

instance : Epi (quotientπ K L hL) :=
  HomologicalComplex.epi_of_epi_f _ fun n ↦ (ModuleCat.epi_iff_surjective _).2
    (Submodule.mkQ_surjective (L n))

lemma quotientπ_comp_eq_zero {K' : ChainComplex (ModuleCat.{v} R) ℕ} (f : K' ⟶ K)
    (hfL : ∀ n, ∀ x, f.f n x ∈ L n) : f ≫ quotientπ K L hL = 0 := by
  ext n x : 3
  exact (Submodule.Quotient.mk_eq_zero _).2 (hfL n x)

/-- If `f : K' ⟶ K` is degreewise injective with image `L`, then `K' ⟶ K ⟶ K / L` is a short
exact sequence of complexes. -/
lemma shortExact_quotient {K' : ChainComplex (ModuleCat.{v} R) ℕ} (f : K' ⟶ K)
    (hf : ∀ n, Function.Injective (f.f n)) (hfL : ∀ n, LinearMap.range (f.f n).hom = L n)
    (w : f ≫ quotientπ K L hL = 0) : (ShortComplex.mk f (quotientπ K L hL) w).ShortExact := by
  refine HomologicalComplex.shortExact_of_degreewise_shortExact _ fun n ↦ ?_
  refine ShortComplex.ShortExact.mk' ?_ ((ModuleCat.mono_iff_injective _).2 (hf n))
    ((ModuleCat.epi_iff_surjective _).2 (Submodule.mkQ_surjective (L n)))
  rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
  change LinearMap.range (f.f n).hom = LinearMap.ker (L n).mkQ
  rw [Submodule.ker_mkQ, hfL]

/-- If `f : K' ⟶ K` is degreewise injective with image `L`, then the quotient `K / L` is a
cokernel of `f`. -/
noncomputable def isColimitQuotient {K' : ChainComplex (ModuleCat.{v} R) ℕ} (f : K' ⟶ K)
    (hf : ∀ n, Function.Injective (f.f n)) (hfL : ∀ n, LinearMap.range (f.f n).hom = L n)
    (w : f ≫ quotientπ K L hL = 0) :
    IsColimit (CokernelCofork.ofπ (quotientπ K L hL) w) :=
  (shortExact_quotient K L hL f hf hfL w).exact.gIsCokernel

variable {K L hL} {K' : ChainComplex (ModuleCat.{v} R) ℕ} {L' : ∀ n, Submodule R (K'.X n)}
  {hL' : ∀ n, ∀ x ∈ L' (n + 1), K'.d (n + 1) n x ∈ L' n}

/-- A chain map preserving the subcomplexes restricts to the subcomplexes. -/
noncomputable def subcomplexMap (f : K ⟶ K') (hf : ∀ n, ∀ x ∈ L n, f.f n x ∈ L' n) :
    subcomplex K L hL ⟶ subcomplex K' L' hL' :=
  natHomMk (fun n ↦ ModuleCat.ofHom ((f.f n).hom.restrict (hf n))) (fun n ↦ by
    rw [subcomplex_d, subcomplex_d]
    refine ModuleCat.hom_ext (LinearMap.ext fun (x : L (n + 1)) ↦ Subtype.ext ?_)
    change K'.d (n + 1) n (f.f (n + 1) x.1) = f.f n (K.d (n + 1) n x.1)
    rw [← ModuleCat.comp_apply, ← ModuleCat.comp_apply, f.comm])

@[simp]
lemma subcomplexMap_f_apply (f : K ⟶ K') (hf : ∀ n, ∀ x ∈ L n, f.f n x ∈ L' n) (n : ℕ)
    (x : L n) :
    ((show L' n from (subcomplexMap (hL := hL) (hL' := hL') f hf).f n x) : K'.X n) =
      f.f n x := rfl

@[reassoc (attr := simp)]
lemma subcomplexMap_ι (f : K ⟶ K') (hf : ∀ n, ∀ x ∈ L n, f.f n x ∈ L' n) :
    subcomplexMap f hf ≫ subcomplexι K' L' hL' = subcomplexι K L hL ≫ f := rfl

/-- A chain map preserving the subcomplexes induces a map of quotient complexes. -/
noncomputable def quotientMap (f : K ⟶ K') (hf : ∀ n, ∀ x ∈ L n, f.f n x ∈ L' n) :
    quotient K L hL ⟶ quotient K' L' hL' :=
  natHomMk (fun n ↦ ModuleCat.ofHom ((L n).mapQ (L' n) (f.f n).hom (hf n))) (fun n ↦ by
    rw [quotient_d, quotient_d]
    refine ModuleCat.hom_ext (Submodule.linearMap_qext _ (LinearMap.ext fun x ↦ ?_))
    change (L' n).mkQ (K'.d (n + 1) n (f.f (n + 1) x)) = (L' n).mkQ (f.f n (K.d (n + 1) n x))
    rw [← ModuleCat.comp_apply, ← ModuleCat.comp_apply, f.comm])

@[simp]
lemma quotientMap_f_mk (f : K ⟶ K') (hf : ∀ n, ∀ x ∈ L n, f.f n x ∈ L' n) (n : ℕ) (x : K.X n) :
    (quotientMap (hL := hL) (hL' := hL') f hf).f n
        (show K.X n ⧸ L n from Submodule.Quotient.mk x) =
      (show K'.X n ⧸ L' n from Submodule.Quotient.mk (f.f n x)) := rfl

@[reassoc (attr := simp)]
lemma quotientπ_quotientMap (f : K ⟶ K') (hf : ∀ n, ∀ x ∈ L n, f.f n x ∈ L' n) :
    quotientπ K L hL ≫ quotientMap f hf = f ≫ quotientπ K' L' hL' := rfl

lemma quotientMap_id : quotientMap (𝟙 K) (fun _ _ hx ↦ hx) = 𝟙 (quotient K L hL) := by
  ext n : 1
  exact ModuleCat.hom_ext (Submodule.linearMap_qext _ rfl)

lemma quotientMap_comp {K'' : ChainComplex (ModuleCat.{v} R) ℕ} {L'' : ∀ n, Submodule R (K''.X n)}
    {hL'' : ∀ n, ∀ x ∈ L'' (n + 1), K''.d (n + 1) n x ∈ L'' n} (f : K ⟶ K') (g : K' ⟶ K'')
    (hf : ∀ n, ∀ x ∈ L n, f.f n x ∈ L' n) (hg : ∀ n, ∀ x ∈ L' n, g.f n x ∈ L'' n) :
    quotientMap (L := L) (hL := hL) (L' := L'') (hL' := hL'') (f ≫ g)
        (fun n x hx ↦ hg n _ (hf n x hx)) =
      quotientMap (hL' := hL') f hf ≫ quotientMap g hg := by
  ext n : 1
  exact ModuleCat.hom_ext (Submodule.linearMap_qext _ rfl)

/-- A homotopy whose components preserve the subcomplexes descends to the quotient complexes. -/
noncomputable def quotientHomotopy {f g : K ⟶ K'} (h : Homotopy f g)
    (hf : ∀ n, ∀ x ∈ L n, f.f n x ∈ L' n) (hg : ∀ n, ∀ x ∈ L n, g.f n x ∈ L' n)
    (hh : ∀ n, ∀ x ∈ L n, h.hom n (n + 1) x ∈ L' (n + 1)) :
    Homotopy (quotientMap (hL := hL) (hL' := hL') f hf) (quotientMap g hg) :=
  natHomotopyMk (fun n ↦ ModuleCat.ofHom ((L n).mapQ (L' (n + 1)) (h.hom n (n + 1)).hom (hh n)))
    (by
      rw [quotient_d]
      refine ModuleCat.hom_ext (Submodule.linearMap_qext _ (LinearMap.ext fun x ↦ ?_))
      have := h.comm 0
      rw [Homotopy.dNext_zero_chainComplex, Homotopy.prevD_chainComplex, zero_add] at this
      change (L' 0).mkQ (f.f 0 x) = (L' 0).mkQ (K'.d 1 0 (h.hom 0 1 x)) + (L' 0).mkQ (g.f 0 x)
      rw [this, ← map_add]
      rfl)
    (fun n ↦ by
      rw [quotient_d, quotient_d]
      refine ModuleCat.hom_ext (Submodule.linearMap_qext _ (LinearMap.ext fun x ↦ ?_))
      have := h.comm (n + 1)
      rw [Homotopy.dNext_succ_chainComplex, Homotopy.prevD_chainComplex] at this
      change (L' (n + 1)).mkQ (f.f (n + 1) x) =
        (L' (n + 1)).mkQ (h.hom n (n + 1) (K.d (n + 1) n x)) +
        (L' (n + 1)).mkQ (K'.d (n + 2) (n + 1) (h.hom (n + 1) (n + 2) x)) +
        (L' (n + 1)).mkQ (g.f (n + 1) x)
      rw [this, ← map_add, ← map_add]
      rfl)

end Sub

end Morse.Homology
