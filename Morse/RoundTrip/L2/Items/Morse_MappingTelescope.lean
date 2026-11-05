import Morse
import RoundTrip.L2.Blind.Morse_MappingTelescope

/-! Layer-2 check of `Morse.MappingTelescope F` against the blind textbook mapping telescope: both
are the quotient `Quot` of `Σ n, Fₙ × [0,1]` by `(n, k, 1) ∼ (n+1, cₙ k, 0)` with the quotient
topology; the project's gluing relation is an inductive predicate, the blind one an existential.
The relations are equal, hence so are the carriers, and the identity on representatives is a
homeomorphism. -/

namespace RoundTrip.L2.Morse_MappingTelescope

open CategoryTheory
open scoped unitInterval

theorem rel_eq (F : ℕ ⥤ TopCat.{0}) : Morse.MapTelRel F = Rel F := by
  funext a b
  apply propext
  constructor
  · rintro ⟨n, k⟩
    exact ⟨n, k, rfl, rfl⟩
  · rintro ⟨n, k, rfl, rfl⟩
    exact .glue n k

/-- The carriers are the same type. -/
theorem carrier_eq (F : ℕ ⥤ TopCat.{0}) : Morse.MappingTelescope F = T F := by
  change Quot (Morse.MapTelRel F) = Quot (Rel F)
  rw [rel_eq]

/-- **Agreement**: the identity on representatives is a homeomorphism. -/
noncomputable def agree (F : ℕ ⥤ TopCat.{0}) : Morse.MappingTelescope F ≃ₜ T F where
  toFun := Quot.lift (Quot.mk (Rel F)) (fun a b h => Quot.sound (rel_eq F ▸ h))
  invFun := Quot.lift (Quot.mk (Morse.MapTelRel F)) (fun a b h => Quot.sound ((rel_eq F).symm ▸ h))
  left_inv z := by induction z using Quot.ind; rfl
  right_inv z := by induction z using Quot.ind; rfl
  continuous_toFun := continuous_quot_lift _ continuous_quot_mk
  continuous_invFun := continuous_quot_lift _ continuous_quot_mk

theorem agree_mk (F : ℕ ⥤ TopCat.{0}) (n : ℕ) (k : F.obj n) (t : I) :
    agree F (Morse.MappingTelescope.mk F n k t) = Quot.mk (Rel F) ⟨n, (k, t)⟩ :=
  rfl

end RoundTrip.L2.Morse_MappingTelescope
