import Morse
import RoundTrip.Check
import RoundTrip.Blind.V3_3

open scoped ContDiff Manifold

namespace RoundTrip.V3_3

/-- The project's statement (Step 1 of Reeb's theorem), universes instantiated at `0`. -/
def A : Prop := type_of% @Morse.exists_min_max_of_ncard_eq_two.{0, 0}

theorem A_holds : A := @Morse.exists_min_max_of_ncard_eq_two.{0, 0}

theorem A_to_B : A → B := by
  intro hA E _ _ _ M _ _ _ _ _ f p q hf hpq hp hq honly
  by_cases hdim : Module.finrank ℝ E = 0
  · -- dimension `0`: every point is critical, so `M = {p, q}`
    have hsub : Subsingleton E := Module.finrank_zero_iff.1 hdim
    have hall : ∀ x, x = p ∨ x = q := fun x => honly x (by
      change mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) f x = 0
      ext v
      have : v = 0 := Subsingleton.elim (α := E) v 0
      rw [this, map_zero]
      rfl)
    rcases le_total (f p) (f q) with h | h
    · refine ⟨p, q, Or.inl ⟨rfl, rfl⟩, fun x => ?_⟩
      rcases hall x with rfl | rfl <;> exact ⟨by linarith, by linarith⟩
    · refine ⟨q, p, Or.inr ⟨rfl, rfl⟩, fun x => ?_⟩
      rcases hall x with rfl | rfl <;> exact ⟨by linarith, by linarith⟩
  · have hset : {x : M | Morse.IsCriticalPointM E f x} = {p, q} := by
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
      exact ⟨honly x, by rintro (rfl | rfl); exacts [hp.1, hq.1]⟩
    have htwo : {x : M | Morse.IsCriticalPointM E f x}.ncard = 2 := by
      rw [hset, Set.ncard_pair hpq]
    have hnd : ∀ x, Morse.IsCriticalPointM E f x → Morse.IsNondegenerate (Morse.hessianM E f x) := by
      intro x hx
      rcases honly x hx with rfl | rfl
      exacts [hp.2, hq.2]
    obtain ⟨a, b, hab, hiff, ha, hb, -, -⟩ := hA (Nat.pos_of_ne_zero hdim) hf htwo hnd
    refine ⟨a, b, ?_, fun x => ⟨?_, ?_⟩⟩
    · have hne : a ≠ b := fun h => (lt_irrefl (f a)) (h ▸ hab)
      have ha' := honly a ((hiff a).2 (Or.inl rfl))
      have hb' := honly b ((hiff b).2 (Or.inr rfl))
      rcases ha' with rfl | rfl <;> rcases hb' with rfl | rfl
      · exact absurd rfl hne
      · exact Or.inl ⟨rfl, rfl⟩
      · exact Or.inr ⟨rfl, rfl⟩
      · exact absurd rfl hne
    · by_cases hx : x = a
      · rw [hx]
      · exact (ha x hx).le
    · by_cases hx : x = b
      · rw [hx]
      · exact (hb x hx).le

#rt_check RoundTrip.V3_3.A_to_B [Morse.exists_min_max_of_ncard_eq_two]

end RoundTrip.V3_3
