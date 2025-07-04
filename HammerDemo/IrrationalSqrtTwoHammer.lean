import HammerDemo.Setup
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.Linarith

set_premise_selector Lean.PremiseSelection.Cloud.premiseSelector

namespace Nat

theorem two_dvd_of_two_dvd_sq {m : ℕ} (h : 2 ∣ m ^ 2) : 2 ∣ m := by
  hammer

end Nat

namespace IrrationalSqrtTwo

/-- Theorem taken from Mathematics in Lean -/
theorem irrational_sqrt_two {m n : ℕ} (coprime_mn : m.Coprime n) :
    m ^ 2 ≠ 2 * n ^ 2 := by
  intro sqr_eq
  have : 2 ∣ m := by
    hammer
  obtain ⟨k, meq⟩ := dvd_iff_exists_eq_mul_left.mp this
  have : 2 * n ^ 2 = 2 * (2 * k ^ 2) := by
    -- currently this is not solved by `hammer`
    subst meq
    linarith
  have : n ^ 2 = 2 * k ^ 2 := by
    hammer
  have : 2 ∣ n := by
    hammer
  have : 2 ∣ m.gcd n := by
    -- aesop/simp_all eagerly reduces goal to `False` using `m.Coprime n = (m.gcd n = 1)`; we disable them here
    hammer [Nat.dvd_gcd_iff] {disableAesop := true, preprocessing := no_preprocessing}
  have : 2 ∣ 1 := by
    hammer
  hammer

end IrrationalSqrtTwo
