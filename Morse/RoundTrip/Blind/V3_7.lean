import Morse
/-! Blind formalization of V3_7 (Milnor §5, Definition: subadditive and additive functions). Choices:
- "Spaces" = subsets of an ambient type `α`; "pairs of spaces" `(X, Y)`, `Y ⊆ X`; an integer-valued function `S` defined on "certain
  pairs" is modelled as `S : Set α → Set α → ℤ` together with a domain predicate `dom X Y` (S's value off `dom` is irrelevant).
- `Subadditive dom S`: for all `X ⊇ Y ⊇ Z` with the three pairs `(X,Z),(X,Y),(Y,Z)` in `dom`, `S X Z ≤ S X Y + S Y Z`;
  `Additive` with equality. (Milnor presupposes all three pairs are defined.)
- Definitions-only item: `B` asserts the obvious basic relation: additive ⇒ subadditive. -/
namespace RoundTrip.V3_7

/-- subadditive. -/
def Subadditive {α : Type} (dom : Set α → Set α → Prop) (S : Set α → Set α → ℤ) : Prop :=
  ∀ X Y Z : Set α, Z ⊆ Y → Y ⊆ X → dom X Z → dom X Y → dom Y Z → S X Z ≤ S X Y + S Y Z

/-- additive. -/
def Additive {α : Type} (dom : Set α → Set α → Prop) (S : Set α → Set α → ℤ) : Prop :=
  ∀ X Y Z : Set α, Z ⊆ Y → Y ⊆ X → dom X Z → dom X Y → dom Y Z → S X Z = S X Y + S Y Z

/-- Milnor's claim. -/
def B : Prop :=
  ∀ (α : Type) (dom : Set α → Set α → Prop) (S : Set α → Set α → ℤ), Additive dom S → Subadditive dom S

end RoundTrip.V3_7
