import Morse
import RoundTrip.Check
import RoundTrip.Glue
import RoundTrip.Blind.V4_22

open Module Set
open scoped ContDiff Manifold

namespace RoundTrip.V4_22

/-- The project's statement: the two listed theorems, universes instantiated at `0`. -/
def A : Prop :=
  type_of% @Morse.ae_isMorseFunction_add_inner_comp.{0, 0} ∧
  type_of% @Morse.exists_isMorseFunction_approx_of_compactSpace.{0, 0, 0, 0}

theorem A_holds : A :=
  ⟨@Morse.ae_isMorseFunction_add_inner_comp.{0, 0},
    @Morse.exists_isMorseFunction_approx_of_compactSpace.{0, 0, 0, 0}⟩

/-- **A ⇒ B**: A's approximation clause with `E = E' = ℝⁿ`, `ι = Fin r`, `y_j = φ_j` (maximal-atlas
charts are smooth coordinate systems) and `K_j = φ_j(C_j)`; B's bound on the difference of the
derivatives is A's bound on the derivatives of the difference (`Glue.iteratedFDeriv_sub_comp_symm`). -/
theorem A_to_B : A → B := by
  intro hA n M _ _ _ _ _ _ f hf _ ε hε k r φ hφ C hC
  have hy : ∀ j, Morse.IsSmoothCoord (Rn n) (φ j) := fun j ↦
    Morse.isSmoothCoord_of_mem_maximalAtlas (hφ j)
  obtain ⟨g, hg, hgf, hder⟩ := hA.2 hf (ι := Fin r) φ hy (fun j ↦ φ j '' C j)
    (fun j ↦ (hC j).1.image_of_continuousOn ((φ j).continuousOn.mono (hC j).2))
    (fun j ↦ (image_mono (hC j).2).trans (φ j).image_source_subset) k hε
  refine ⟨g, hg.contMDiff, fun q hq ↦ hg.isNondegenerateCriticalPointM hq, hgf, ?_⟩
  intro j i hi u hu
  have hut : u ∈ (φ j).target := (image_mono (hC j).2).trans (φ j).image_source_subset hu
  rw [← Glue.iteratedFDeriv_sub_comp_symm (hy j) hf hg.contMDiff hut]
  exact hder j i hi u hu

/-! `B_to_A` is not proved, and is genuinely weaker. A's first clause
`ae_isMorseFunction_add_inner_comp` is the engine of Milnor's proof, for ANY (not necessarily
compact) manifold with ANY embedding `e : M → ℝⁿ` (smooth, topological embedding, injective
differential): for almost every `a ∈ ℝⁿ`, `f + ⟪a, e⟫` is a Morse function. B, an existence
statement for compact `M`, gives no information about almost every `a`. (A's second clause is B
for an arbitrary model `E` and arbitrary smooth coordinate systems into any `E'`; deriving it
from B would be transport along Whitney's diffeomorphism and a linear change of target, i.e.
glue, but the conjunction fails because of the first clause.) -/

#rt_check RoundTrip.V4_22.A_to_B [Morse.ae_isMorseFunction_add_inner_comp,
  Morse.exists_isMorseFunction_approx_of_compactSpace]

end RoundTrip.V4_22
