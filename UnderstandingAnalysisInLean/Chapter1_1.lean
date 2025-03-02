import Mathlib.Tactic

/-
Exercise 1.1.1
-/
def sqrt2_irrational_for_coprimes : ∀ (p q : ℕ), Nat.Coprime p q → (p^2) ≠ 2 * (q^2) := by
    intro p q hcoprime
    by_contra hcontra

    have : 2 ∣ p^2 := by
        use q^2
    have even_p : 2 ∣ p := Nat.Prime.dvd_of_dvd_pow Nat.prime_two this

    have : 2 ∣ q^2 := by
        have : ∃ (r : ℕ), p = 2 * r := even_p
        obtain ⟨r, hr⟩ := this
        rw [hr] at hcontra
        ring_nf at hcontra
        have : 4 = 2 * 2 := by trivial
        rw [this, ←mul_assoc] at hcontra
        simp at hcontra
        exact Dvd.intro_left (r ^ 2) hcontra
    have even_q : 2 ∣ q := Nat.Prime.dvd_of_dvd_pow Nat.prime_two this

    have hnot_coprime : ¬ p.Coprime q := Nat.not_coprime_of_dvd_of_dvd one_lt_two even_p even_q
    contradiction

def sqrt3_irrational_for_coprimes : ∀ (p q : ℕ), Nat.Coprime p q → (p^2) ≠ 3 * (q^2) := by
    intro p q hcoprime
    by_contra hcontra

    have : 3 ∣ p^2 := by
        use q^2
    have three_divides_p : 3 ∣ p := Nat.Prime.dvd_of_dvd_pow Nat.prime_three this

    have : 3 ∣ q^2 := by
        have : ∃ (r : ℕ), p = 3 * r := three_divides_p
        obtain ⟨r, hr⟩ := this
        rw [hr] at hcontra
        ring_nf at hcontra
        have : 9 = 3 * 3 := by trivial
        rw [this, ←mul_assoc] at hcontra
        simp at hcontra
        exact Dvd.intro_left (r ^ 2) hcontra
    have three_divides_q : 3 ∣ q := Nat.Prime.dvd_of_dvd_pow Nat.prime_three this

    have hnot_coprime : ¬ p.Coprime q := Nat.not_coprime_of_dvd_of_dvd (by trivial) three_divides_p three_divides_q
    contradiction
