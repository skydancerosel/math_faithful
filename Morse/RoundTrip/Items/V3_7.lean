import Morse
import RoundTrip.Check
import RoundTrip.Blind.V3_7

namespace RoundTrip.V3_7

/-- The declarations of this item (`Morse.IsSubadditive`, `Morse.IsAdditive`) are both
definitions: there is no listed theorem, so the project's formal statement is the empty
conjunction. -/
def A : Prop := True

theorem A_holds : A := trivial

/-- `B` (additive ⇒ subadditive) holds outright. -/
theorem B_holds : B := fun _ _ _ h X Y Z hZY hYX h1 h2 h3 => (h X Y Z hZY hYX h1 h2 h3).le

theorem A_to_B : A → B := fun _ => B_holds

theorem B_to_A : B → A := fun _ => trivial

/-! ### Vocabulary check (not part of `A`)

The project's `IsSubadditive S` is stated on a preorder `ι` with `S a c` (`a ≤ c`) standing for
Milnor's `S(X_c, X_a)`, and with `S` defined on all pairs. B's `Subadditive dom S` is stated on
subsets `X ⊇ Y ⊇ Z` of an ambient type with `S X Z`, restricted to a domain `dom` of defined
pairs. With `ι = Set α` (ordered by `⊆`), the argument order swapped, and `dom` everything, the two
notions coincide. -/

theorem subadditive_iff {α : Type} (S : Set α → Set α → ℤ) :
    Subadditive (fun _ _ => True) S ↔ Morse.IsSubadditive (fun a c : Set α => S c a) :=
  ⟨fun h a b c hab hbc => (h c b a hab hbc trivial trivial trivial).trans_eq (add_comm _ _),
   fun h _ _ _ hZY hYX _ _ _ => (h hZY hYX).trans_eq (add_comm _ _)⟩

theorem additive_iff {α : Type} (S : Set α → Set α → ℤ) :
    Additive (fun _ _ => True) S ↔ Morse.IsAdditive (fun a c : Set α => S c a) :=
  ⟨fun h a b c hab hbc => (h c b a hab hbc trivial trivial trivial).trans (add_comm _ _),
   fun h _ _ _ hZY hYX _ _ _ => (h hZY hYX).trans (add_comm _ _)⟩

#rt_check RoundTrip.V3_7.A_to_B [Morse.IsSubadditive, Morse.IsAdditive]
#rt_check RoundTrip.V3_7.B_to_A [Morse.IsSubadditive, Morse.IsAdditive]
#rt_overlap RoundTrip.V3_7.B_to_A [Morse.IsSubadditive, Morse.IsAdditive]

end RoundTrip.V3_7
