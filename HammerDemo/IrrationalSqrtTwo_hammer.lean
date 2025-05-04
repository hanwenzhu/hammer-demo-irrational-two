import HammerDemo.Setup
import Mathlib

set_premise_selector Lean.PremiseSelection.Cloud.premiseSelector
set_option premiseSelection.apiBaseUrl "http://leanpremise.net"
register_hammer_extension linarith

namespace Lemma

theorem two_dvd_of_two_dvd_sq {m : ℕ} (h : 2 ∣ m ^ 2) : 2 ∣ m := by
  hammer

end Lemma

namespace IrrationalSqrtTwo

/-- Theorem taken from Mathematics in Lean -/
theorem irrational_sqrt_two {m n : ℕ} (coprime_mn : m.Coprime n) :
    m ^ 2 ≠ 2 * n ^ 2 := by
  intro sqr_eq
  have : 2 ∣ m := by
    hammer
  obtain ⟨k, meq⟩ := dvd_iff_exists_eq_mul_left.mp this
  have : 2 * (2 * k ^ 2) = 2 * n ^ 2 := by
    hammer
  have : 2 * k ^ 2 = n ^ 2 := by
    hammer
  have : 2 ∣ n := by
    hammer
  have : 2 ∣ m.gcd n := by
    clear coprime_mn
    hammer
  have : 2 ∣ 1 := by
    hammer
  hammer

end IrrationalSqrtTwo
