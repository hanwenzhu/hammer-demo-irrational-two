import HammerDemo.Setup
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.NormNum.Basic

namespace Nat

theorem two_dvd_of_two_dvd_sq {m : ℕ} (h : 2 ∣ m ^ 2) : 2 ∣ m := by
  -- `hammer`able
  rw [pow_two, Nat.prime_two.dvd_mul] at h
  cases h <;> assumption

end Nat

namespace IrrationalSqrtTwo

/-- Theorem taken from Mathematics in Lean -/
theorem irrational_sqrt_two {m n : ℕ} (coprime_mn : m.Coprime n) :
    m ^ 2 ≠ 2 * n ^ 2 := by
  intro sqr_eq
  have : 2 ∣ m := by
    -- `hammer`able
    apply Nat.two_dvd_of_two_dvd_sq
    use n ^ 2
  obtain ⟨k, meq⟩ := dvd_iff_exists_eq_mul_left.mp this
  have : 2 * n ^ 2 = 2 * (2 * k ^ 2) := by
    rw [← sqr_eq, meq, mul_pow]
    omega
  have : n ^ 2 = 2 * k ^ 2 := by
    -- `hammer`able
    exact mul_left_cancel₀ two_ne_zero this
  have : 2 ∣ n := by
    -- `hammer`able
    apply Nat.two_dvd_of_two_dvd_sq
    use k ^ 2
  have : 2 ∣ m.gcd n := by
    -- `hammer`able after `clear coprime_mn` or disabling preprocessing
    rw [Nat.dvd_gcd_iff]
    constructor <;> assumption
  have : 2 ∣ 1 := by
    -- `hammer`able
    rwa [coprime_mn.gcd_eq_one] at this
  -- `hammer`able
  norm_num at this

end IrrationalSqrtTwo
