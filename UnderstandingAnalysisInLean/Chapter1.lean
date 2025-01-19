import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

@[simp]
def divides (n m : ℕ) := ∃ (d : ℕ), m = n * d
infixl:50 " divides " => divides

example : 2 divides 4 := by
    simp
    use 2

@[simp]
def coprime' (n m : ℕ) := ¬ ∃ (d : ℕ), d divides n ∧ d divides m ∧ d ≠ 1

lemma even_is_even_squared : ∀ (n : ℕ), 2 divides n → 2 divides n ^ 2 := by
    intro n
    simp
    intro x hxn
    use (2 * x * x)
    rw [hxn]
    ring_nf

lemma even_squared_is_even : ∀ (n : ℕ), 2 divides n^2 → 2 divides n := by sorry


def sqrt2_irrational_for_coprimes : ∀ (p q : ℕ), coprime' p q → (p^2) ≠ 2 * (q^2) := by
    intro p q hcoprime
    by_contra hcontra

    have: 2 divides (p^2) := by
        simp
        use (q^2)
    have two_divides_p': 2 divides p := by
        exact even_squared_is_even p this
    obtain ⟨r, hm⟩ := two_divides_p'

    rw [hm] at hcontra
    ring_nf at hcontra

    have : 4 = 2 * 2 := by ring_nf
    rw [this, ←Nat.mul_assoc] at hcontra
    have two_gt_zero : 0 < 2 := by trivial
    have : r ^ 2 * 2 = q ^ 2 := Nat.mul_right_cancel two_gt_zero hcontra

    have : 2 divides q^2 := by
        simp
        use (r^2)
        rw [Nat.mul_comm]
        exact (Eq.symm this)

    have two_divides_q' : 2 divides q := by
        exact even_squared_is_even q this

    have h_not_coprime: ¬ coprime' p q := by
        simp
        use 2
        have h_two_ne_1 : 2 ≠ 1 := by trivial
        exact ⟨⟨r, hm⟩, two_divides_q', h_two_ne_1⟩

    contradiction
    -- exact h_not_coprime hcoprime

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
End of chapter exercises
-/

theorem div3_of_div3_sqr {m : ℕ} (h : 3 ∣ m ^ 2) : 3 ∣ m := by sorry


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
