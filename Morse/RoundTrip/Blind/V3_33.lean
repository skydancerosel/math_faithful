import Morse
/-! Blind formalization of V3_33 (Milnor §5, pp. 28-29: Betti numbers and the homology of a slab). Choices:
- Setting of §5: `M` compact smooth Hausdorff manifold modelled on finite-dimensional `E`, `f` smooth with only non-degenerate critical points
  (project's `Morse.IsCriticalPointM`, `Morse.IsNondegenerateCriticalPointM`, `Morse.indexM`), `F` an arbitrary field, homology = project's `relHomology` on `subsetPair`.
- Filtration: `MorseFilt` = Milnor's `a_1 < ... < a_k` with exactly `i` critical points in `M^{a_i}` and `M^{a_k} = M`, plus `M^{a_0} = ∅` (convention of the chain `∅ ⊂ M^{a_1} ⊂ ...`);
  the critical points are `p : Fin k → M` injective listed in order (so the hypothesis forces distinct critical values). B is stated for every such choice of `a`, `p` (existence of the choice is not claimed).
- (i) `R_λ(X,Y) = rank H_λ(X,Y;F)`: B asserts that `R` (a `finrank`) equals `Module.rank` whenever `H_λ(X,Y;F)` is finite-dimensional.
- (ii) Cell attachment hand-built (`Attach g`, `Y ∪_g e^λ`; `g` existentially quantified, any continuous map `S^{λ-1} → Y`): for each `i` there is `g : S^{λ_i-1} → M^{a_{i-1}}`
  with `H_n(M^{a_i}, M^{a_{i-1}}; F) ≃ₗ H_n(M^{a_{i-1}} ∪_g e^{λ_i}, M^{a_{i-1}}; F)` for all `n`, `λ_i = index p_i` (the replacement of the pair by Thms 3.1/3.2; only existence of a linear isomorphism is stated, not its naturality). -/
namespace RoundTrip.V3_33
open CategoryTheory Morse.Homology
open scoped ContDiff Manifold unitInterval

/-- `H_n(X, Y; F)` for `Y ⊆ X` subsets of a space (project's relative singular homology). -/
noncomputable def Hom (F : Type) [Field F] {E : Type} [TopologicalSpace E] {A B : Set E} (h : A ⊆ B) (n : ℕ) :
    ModuleCat F := (relHomology (ModuleCat.of F F) n).obj (subsetPair h)

/-- `R_i(X, Y) = rank H_i(X, Y; F)`. -/
noncomputable def R (F : Type) [Field F] {E : Type} [TopologicalSpace E] {A B : Set E} (h : A ⊆ B) (i : ℕ) : ℕ :=
  Module.finrank F (Hom F h i)

/-- `R_i(X) = R_i(X, ∅)`. -/
noncomputable def Rabs (F : Type) [Field F] (E : Type) [TopologicalSpace E] (i : ℕ) : ℕ :=
  R F (Set.empty_subset (Set.univ : Set E)) i

/-- `a_λ - a_{λ-1} + ... ± a_0`. -/
def alt (a : ℕ → ℤ) (l : ℕ) : ℤ := ∑ i ∈ Finset.range (l + 1), (-1 : ℤ) ^ (l - i) * a i

/-- `C_λ`: number of critical points of index `λ`. -/
noncomputable def Cnum (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] {M : Type} [TopologicalSpace M]
    [ChartedSpace E M] (f : M → ℝ) (l : ℕ) : ℕ :=
  {p : M | Morse.IsCriticalPointM E f p ∧ Morse.indexM E f p = l}.ncard

/-- The closed unit ball `e^k` in ℝ^k. -/
abbrev Cell (k : ℕ) : Type := Metric.closedBall (0 : EuclideanSpace ℝ (Fin k)) 1
/-- Its boundary sphere `ė^k = S^{k-1}`. -/
abbrev Bdry (k : ℕ) : Type := Metric.sphere (0 : EuclideanSpace ℝ (Fin k)) 1
/-- The inclusion of the boundary sphere into the cell. -/
def bdryToCell {k : ℕ} (x : Bdry k) : Cell k := ⟨x.1, Metric.sphere_subset_closedBall x.2⟩

section
variable {Y : Type} [TopologicalSpace Y]

/-- Identification relation on the topological sum: `x ∈ S^{k-1}` is glued to `g x`. -/
def Rel {k : ℕ} (g : C(Bdry k, Y)) : (Y ⊕ Cell k) → (Y ⊕ Cell k) → Prop :=
  fun a b => ∃ x : Bdry k, a = Sum.inr (bdryToCell x) ∧ b = Sum.inl (g x)

/-- `Y ∪_g e^k`: quotient of the topological sum `Y ⊕ e^k` by the identifications. -/
def Attach {k : ℕ} (g : C(Bdry k, Y)) : Type := Quot (Rel g)

instance {k : ℕ} (g : C(Bdry k, Y)) : TopologicalSpace (Attach g) :=
  inferInstanceAs (TopologicalSpace (Quot (Rel g)))

/-- Inclusion of `Y`. -/
def inl {k : ℕ} (g : C(Bdry k, Y)) : C(Y, Attach g) :=
  ⟨fun y => Quot.mk _ (Sum.inl y), continuous_quot_mk.comp continuous_inl⟩

/-- Characteristic map of the cell. -/
def inr {k : ℕ} (g : C(Bdry k, Y)) : C(Cell k, Attach g) :=
  ⟨fun c => Quot.mk _ (Sum.inr c), continuous_quot_mk.comp continuous_inr⟩

/-- The characteristic map sends `ė^k` into `Y` (well-definedness of the map of pairs). -/
theorem inr_maps {k : ℕ} (g : C(Bdry k, Y)) :
    Set.MapsTo (inr g) (Set.range (bdryToCell (k := k))) (Set.range (inl g)) := by
  rintro _ ⟨x, rfl⟩
  exact ⟨g x, (Quot.sound ⟨x, rfl, rfl⟩).symm⟩
end

/-- `M^a`. -/
def sub {M : Type} (f : M → ℝ) (a : ℝ) : Set M := {x | f x ≤ a}

/-- Milnor's choice `a_0 < a_1 < ... < a_k`, `p_1, ..., p_k` the critical points: `M^{a_0} = ∅`, `M^{a_i}` contains exactly
the critical points `p_1..p_i`, `M^{a_k} = M`. (Here `a : Fin (k+1) → ℝ` and `p : Fin k → M`; `p i` is Milnor's `p_{i+1}`.) -/
def MorseFilt (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] {M : Type} [TopologicalSpace M] [ChartedSpace E M]
    (f : M → ℝ) (k : ℕ) (p : Fin k → M) (a : Fin (k + 1) → ℝ) : Prop :=
  StrictMono a ∧ Function.Injective p ∧ sub f (a 0) = ∅ ∧ sub f (a (Fin.last k)) = Set.univ ∧
  ∀ i : Fin (k + 1), {x | Morse.IsCriticalPointM E f x ∧ f x ≤ a i} = p '' {j | j.val < i.val}

/-- Milnor's claim. -/
def B : Prop :=
  (∀ (F : Type) [Field F] (E : Type) [TopologicalSpace E] (A B : Set E) (h : A ⊆ B) (i : ℕ),
      Module.Finite F (Hom F h i) → ((R F h i : ℕ) : Cardinal) = Module.rank F (Hom F h i)) ∧
  ∀ (F : Type) [Field F] (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (M : Type) [TopologicalSpace M] [T2Space M] [CompactSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    (f : M → ℝ), ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ f →
    (∀ p, Morse.IsCriticalPointM E f p → Morse.IsNondegenerateCriticalPointM E f p) →
    ∀ (k : ℕ) (p : Fin k → M) (a : Fin (k + 1) → ℝ), MorseFilt E f k p a →
    ∀ (i : Fin k) (h : sub f (a i.castSucc) ⊆ sub f (a i.succ)),
    ∃ g : C(Bdry (Morse.indexM E f (p i)), ↥(sub f (a i.castSucc))),
      ∀ n, Nonempty (↥(Hom F h n) ≃ₗ[F] ↥(Hom F (Set.subset_univ (Set.range (inl g))) n))
end RoundTrip.V3_33
