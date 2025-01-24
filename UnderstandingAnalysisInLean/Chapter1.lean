import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

/-
Exercise 1.2.1
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

    have one_le_three : 1 < 3 := by trivial
    have hnot_coprime : ¬ p.Coprime q := Nat.not_coprime_of_dvd_of_dvd one_le_three three_divides_p three_divides_q
    contradiction

/-
**Example 1.2.2.** Let
    A₁ = N = {1, 2, 3, ... },
    A₂ = {2, 3, 4, ... },
    A₃ = {3, 4, 5, ... },
and, in general, for each n ∈ N, define the set
Aₙ = {n, n + 1, n + 2, ... }.
The result is a nested chain of sets
A₁ ⊇ A₂ ⊇ A₃ ⊇ A₄ ⊇ · · ·
-/
def S (n : Nat) : Set Nat := {(x : Nat) | x ≥ n}

example : ∀ (n : Nat), S (n+1) ⊆ S n := by
    unfold S
    simp
    intro n x h
    linarith

/-
Because of the nested property of
this particular collection of sets, it is not too hard to see that
# Math: \bigcup_{n=1}^\infty A_n = A_1
-/
example : ⋃ (n : Nat) (h : n > 0), S n = S 1 := by
    unfold S
    apply Set.eq_of_forall_subset_iff
    intro K
    constructor
    simp
    case h.mp =>
        intro h y hy
        have h₀ : {x | 1 ≤ x} ⊆ K := (h 1) (zero_lt_one)
        exact h₀ hy
    case h.mpr =>
        simp
        intro h z hz y hy
        have h₀ : {x | z ≤ x} ⊆ {x | 1 ≤ x} := by
            apply Set.setOf_subset_setOf.mpr
            intro a hz_le_a
            linarith
        exact h (h₀ hy)

/-
The notion of intersection has the same kind of natural extension to infinite
collections of sets. For this example, we have
# Math: \bigcap_{n=1}^\infty A_n = \emptyset.
Let’s be sure we understand why this is the case. Suppose we had some natural
number m that we thought might actually satisfy
# Math: m \in \bigcap_{n=1}^\infty A_n
What this would mean is that m ∈ An for every An in our collection of sets.
Because m is not an element of Am+1, no such m exists and the intersection is empty.
-/
example : ⋂ (n : Nat) (h : n > 0), S n = ∅ := by
    unfold S
    simp
    ext y
    constructor
    case h.mp =>
        intro hy
        simp at hy
        apply False.elim
        have h_inf : ∀ n > 0, n ≤ y := hy
        specialize h_inf (y+1) (Nat.succ_pos y)
        have h₁ : (y+1) ∉ S y := by linarith
        have h₂ : (y+1) ∈ S y := by linarith
        contradiction
    case h.mpr =>
        intro hy
        simp at hy


/-
Example 1.2.5
-/
--Our custom definition of the absolute value on `ℝ`. -/
noncomputable def av (a : ℝ) : ℝ := if 0 ≤ a then a else -a

/- Setting the notation `|·|` to refer to our definition. -/
@[inherit_doc av]
macro:max (priority := 1001) atomic("|" noWs) a:term noWs "|" : term => `(av $a)

lemma av_of_nonneg (h : 0 ≤ a) : |a| = a := if_pos h
lemma av_of_neg (h : a < 0) : |a| = -a := if_neg (lt_iff_not_le.mp h)

example (a b : ℝ) : |a * b| = |a| * |b| := by
    /- Just shows all 4 cases:
    1) a is neg, b is pos, 2) a is pos, b is neg 3) both are pos, 4) both are neg-/
    have av_of_nonpos : ∀ x : ℝ, x ≤ 0 → |x| = -x := by
        intro x
        by_cases x = 0
        case pos xeq0 =>
            intro xle0 -- linarith doesn't work if this isn't in context
            have zero_le_x : 0 ≤ x := by linarith
            rw [av, if_pos zero_le_x]
            linarith
        case neg xnoteq0 =>
            intro xle0
            have x_lt_0 : x < 0 := lt_of_le_of_ne xle0 xnoteq0
            rw [av, if_neg (not_le_of_lt x_lt_0)]

    by_cases a ≤ 0
    case pos =>
        by_cases b ≤ 0
        case pos nonpos_a nonpos_b =>
            have ab_nonneg : a * b ≥ 0 := mul_nonneg_of_nonpos_of_nonpos nonpos_a nonpos_b
            rw [av_of_nonneg ab_nonneg, av_of_nonpos a, av_of_nonpos b]
            linarith
            exact nonpos_b
            exact nonpos_a
        case neg nonpos_a not_nonpos_b =>
            have nonneg_b : 0 ≤ b := by exact le_of_not_ge not_nonpos_b
            have ab_nonpos : a * b ≤ 0 := mul_nonpos_of_nonpos_of_nonneg nonpos_a nonneg_b
            rw [av_of_nonpos (a * b), av_of_nonneg nonneg_b, av_of_nonpos a]
            linarith
            exact nonpos_a
            exact ab_nonpos
    case neg =>
        by_cases b ≤ 0
        case pos not_nonpos_a nonpos_b =>
            have nonneg_a : 0 ≤ a := le_of_not_ge not_nonpos_a
            have ab_nonpos : a * b ≤ 0 := mul_nonpos_of_nonneg_of_nonpos nonneg_a nonpos_b
            rw [av_of_nonpos (a * b), av_of_nonneg nonneg_a, av_of_nonpos b]
            linarith
            exact nonpos_b
            exact ab_nonpos
        case neg not_nonpos_a not_nonpos_b =>
            have nonneg_a : 0 ≤ a := le_of_not_ge not_nonpos_a
            have nonneg_b : 0 ≤ b := le_of_not_ge not_nonpos_b
            have nonneg_ab : 0 ≤ a * b := Left.mul_nonneg nonneg_a nonneg_b
            rw [av_of_nonneg nonneg_ab, av_of_nonneg nonneg_a, av_of_nonneg nonneg_b]

/-
Example 1.2.5
-/
lemma av_triangle_inequality {a b c : ℝ} : |a - b| ≤ |a - c| + |c - b| := by
    rw [av, av, av]
    split
    case isTrue =>
        split
        case isTrue =>
            split
            case isTrue =>
                linarith
            case isFalse =>
                linarith
        case isFalse =>
            split
            case isTrue =>
                linarith
            case isFalse =>
                linarith
    case isFalse =>
        split
        case isTrue =>
            split
            case isTrue =>
                linarith
            case isFalse =>
                linarith
        case isFalse =>
            split
            case isTrue =>
                linarith
            case isFalse =>
                linarith
/-
Example 1.2.6
-/
lemma eq_iff_sub_lt_forall {a b : ℝ} : a = b ↔ ∀ ε > 0, |a - b| < ε := by
    simp
    constructor
    case mp =>
        intro h₁ h₂ h₃
        rw [av]
        split
        linarith
        linarith
    case mpr =>
        intro h₄
        rw [av] at h₄
        split at h₄
        case isTrue h₅ =>
            have h₇ : a - b ≤ 0 := forall_lt_iff_le'.mp h₄
            linarith
        case isFalse h₉ =>
            simp at h₄
            have h₁₀ : b - a ≤ 0 := forall_lt_iff_le'.mp h₄
            linarith

/-
Example 1.2.7
-/
def f : Nat → ℝ
| 0   => 1
| n+1 =>  0.5 * (f n) + 1

example : f n ≤ f (n+1) := by
    induction n with
    | zero =>
        simp
        rw [f, f, f]
        norm_num
    | succ k hk =>
        rw [f, f]
        norm_num
        exact hk

/-
Exercise 1.2.2
-/
theorem example_1_2_2_c : ¬ ∀ (A B C : Set ℕ), A ∩ (B ∪ C) = (A ∩ B) ∪ C := by
    by_contra hcontra
    specialize hcontra {1} {1} {2}
    simp at hcontra

theorem example_1_2_2_d : ∀ (A B C : Set ℕ), A ∩ (B ∩ C) = (A ∩ B) ∩ C := by
    intro A B C
    have my_lemma: ∀ (x : ℕ), x ∈ A ∩ (B ∩ C) ↔ x ∈ (A ∩ B) ∩ C := by
        intro x
        constructor
        case mp =>
            intro h
            have h₀ : x ∈ A ∧ x ∈ (B ∩ C) := h
            apply (Set.mem_inter_iff x (A ∩ B) C).mpr ?_
            let right := h₀.right
            have h₁ : x ∈ B ∧ x ∈ C := right
            have h₂ : x ∈ A ∧ x ∈ B := ⟨h₀.left, h₁.left⟩
            have h₃ : x ∈ A ∩ B := h₂
            exact ⟨h₃, h₁.right⟩
        case mpr =>
            intro h
            have h₀ : x ∈ A ∧ (x ∈ B ∧ x ∈ C) := and_assoc.mp h
            exact ⟨h₀.left, h₀.right⟩
    ext x
    exact my_lemma x

theorem example_1_2_2_e : ∀ (A B C : Set ℕ), A ∩ (B ∪ C) = ( A ∩ B) ∪ (A ∩ C) := by
    intro A B C
    ext x
    constructor
    · intro h
      have h₀ : x ∈ A ∧ x ∈ (B ∪ C) := h
      refine (Set.mem_union x (A ∩ B) (A ∩ C)).mpr ?_
      let right := h₀.right
      have h₁ : x ∈ B ∨ x ∈ C := right
      cases h₁
      case inl hb => exact Or.inl ⟨h₀.left, hb⟩
      case inr hc => exact Or.inr ⟨h₀.left, hc⟩
    intro h
    have h₀ : (x ∈ A ∧ x ∈ B) ∨ (x ∈ A ∧  x ∈ C) := h
    cases h₀
    case inl hab =>
        have ha : x ∈ A := hab.left
        have hb : x ∈ B := hab.right
        exact ⟨ha, Or.inl hb⟩
    case inr hac =>
        have ha : x ∈ A := hac.left
        have hc : x ∈ C := hac.right
        exact ⟨ ha, Or.inr hc⟩

/-
End of chapter exercises
-/


theorem exercise_1_2_5_a : |a - b| ≤ |a| + |b| := by
    rw [av, av, av]
    split
    split
    split
    linarith
    linarith
    split
    linarith
    linarith
    split
    split
    linarith
    linarith
    split
    linarith
    linarith


/-
Chapter 1.3
-/
@[simp]
def is_bounded_above (A : Set ℝ) := ∃ (b : ℝ), ∀ a ∈ A, a ≤ b
def is_bounded_below (A : Set ℝ) := ∃ (b : ℝ), ∀ a ∈ A, a ≥ b
@[simp]
def is_bounded_above_N (A : Set ℕ) := ∃ (b : ℕ), ∀ a ∈ A, a ≤ b

@[simp]
def is_an_upper_bound_of (s : ℝ) (A : Set ℝ) := ∀ a ∈ A, a ≤ s
infixl:50 " is_an_upper_bound_of " => is_an_upper_bound_of
@[simp]
def is_an_upper_bound_of_N (s : ℕ) (A : Set ℕ) := ∀ a ∈ A, a ≤ s
infixl:50 " is_an_upper_bound_of_N " => is_an_upper_bound_of_N
def is_a_lower_bound_of (s : ℝ) (A : Set ℝ) := ∀ a ∈ A, a ≥ s
infixl:50 " is_a_lower_bound_of " => is_a_lower_bound_of

lemma if_is_bounded_above_then_has_upper_bound (A : Set ℝ) (h : is_bounded_above A) : ∃ s, s is_an_upper_bound_of A := by
    simp at h
    obtain ⟨h, hb⟩ := h
    use h
    exact hb

lemma if_is_bounded_above_then_has_upper_bound_N (A : Set ℕ) (h : is_bounded_above_N A) : ∃ s, s is_an_upper_bound_of_N A := by
    simp at h
    obtain ⟨h, hb⟩ := h
    use h
    exact hb

def is_the_supremum_of (s : ℝ) (A : Set ℝ) := s is_an_upper_bound_of A ∧ ∀ x ∈ {x | x is_an_upper_bound_of A}, s ≤ x
infixl:50 " is_the_supremum_of " => is_the_supremum_of
def is_the_infimum_of (s : ℝ) (A : Set ℝ) := s is_a_lower_bound_of A ∧ ∀ x ∈ {x | x is_a_lower_bound_of A}, s ≥ x
infixl:50 " is_the_infimum_of " => is_the_infimum_of

def is_max_of (s : ℝ) (A : Set ℝ) := ∀ a ∈ A, s ≥ a
def is_min_of (s : ℝ) (A : Set ℝ) := ∀ a ∈ A, s ≤ a

/-
Chapter 1.4
-/
-- Theorem 1.4.2
def all_natural_numbers : (Set ℕ) := { x | true }
theorem archimedean_property_1 : ¬ is_bounded_above_N all_natural_numbers := by
    by_contra hcontra
    let a := if_is_bounded_above_then_has_upper_bound_N all_natural_numbers
    obtain ⟨b, hb⟩ := hcontra
    let counter_example := hb (b+1)
    have : (b+1) ∈ all_natural_numbers := by rfl
    let contra := counter_example this
    linarith

theorem archimedean_property_2 : ∀ (y : ℝ), ∃ n, 1 / n < y := by
    intro y
    by_cases 1 < y
    case pos hpos =>
        use 2 / y
        norm_num
        linarith
    case neg hpos =>  sorry
