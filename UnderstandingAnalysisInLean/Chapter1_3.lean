import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

/-
Chapter 1.3
-/

-- Definition of bounded above
@[simp]
def is_bounded_above (A : Set ℝ) := ∃ (b : ℝ), ∀ a ∈ A, a ≤ b
@[simp]
def is_bounded_above_N (A : Set ℕ) := ∃ (b : ℕ), ∀ a ∈ A, a ≤ b
@[simp]
def is_bounded_above_Q (A : Set ℚ) := ∃ (b : ℚ), ∀ a ∈ A, a ≤ b

-- Definition of bounded below
@[simp]
def is_bounded_below (A : Set ℝ) := ∃ (b : ℝ), ∀ a ∈ A, a ≥ b

-- Definition of upper bound
@[simp]
def is_an_upper_bound_of (s : ℝ) (A : Set ℝ) := ∀ a ∈ A, a ≤ s
infixl:50 " is_an_upper_bound_of " => is_an_upper_bound_of
@[simp]
def is_an_upper_bound_of_N (s : ℕ) (A : Set ℕ) := ∀ a ∈ A, a ≤ s
infixl:50 " is_an_upper_bound_of_N " => is_an_upper_bound_of_N
@[simp]
def is_an_upper_bound_of_Q (s : ℚ) (A : Set ℚ) := ∀ a ∈ A, a ≤ s
infixl:50 " is_an_upper_bound_of_Q " => is_an_upper_bound_of_Q

-- Definition of lower bound
@[simp]
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

-- Supremum and infimum
@[simp]
def is_the_supremum_of (s : ℝ) (A : Set ℝ) := s is_an_upper_bound_of A ∧ ∀ x ∈ {x | x is_an_upper_bound_of A}, s ≤ x
infixl:50 " is_the_supremum_of " => is_the_supremum_of

@[simp]
def is_the_infimum_of (s : ℝ) (A : Set ℝ) := s is_a_lower_bound_of A ∧ ∀ x ∈ {x | x is_a_lower_bound_of A}, s ≥ x
infixl:50 " is_the_infimum_of " => is_the_infimum_of

@[simp]
def is_max_of (s : ℝ) (A : Set ℝ):= ∃ s ∈ A, ∀ a ∈ A, s ≥ a
infixl:50 " is_max_of " => is_max_of
def is_min_of (s : ℝ) (A : Set ℝ) := ∃ s ∈ A, ∀ a ∈ A, s ≤ a

/-
Axiom of completeness
Every nonempty set of real numbers that is bounded
above has a least upper bound.
-/
axiom completeness : ∀ (A : Set ℝ) , A.Nonempty ∧ is_bounded_above A → ∃ s : ℝ , s is_the_supremum_of A


/-
Example 1.3.3
Let A = { 1/n : n ∈ N} = {1, 1/2, 1/3, ...}
supA = 1
-/

def A : Set ℝ := {x | ∃ n : ℕ, n > 0 ∧ x = 1 / n}

example : 1 is_the_supremum_of A := by
  simp
  constructor
  · intro a ha
    rcases ha with ⟨n, hn, rfl⟩
    apply div_le_one_of_le₀
    · norm_num
      linarith
    norm_num

  · intro b hb
    have h1 : 1 ∈ A := by
      use 1
      simp
    exact hb 1 h1

/-
Example 1.3.5

(0, 2) = {x ∈ R : 0 < x < 2}
[0, 2] = {x ∈ R : 0 ≤ x ≤ 2}
Both sets are bounded above and have the same supremum.
(0, 2) doesn't have a maximum while [0, 2] does.
When a maximum exists then it is the supremum
-/

def openi : Set ℝ := {x | 0 < x ∧ x < 2}
def closedi : Set ℝ := {x | 0 ≤ x ∧ x ≤ 2}

lemma open_closed_bounded_above : is_bounded_above openi ∧ is_bounded_above closedi := by
  constructor
  · simp
    use 2
    intro a ha
    simp [openi] at ha
    linarith
  · simp
    use 2
    intro a ha
    simp [closedi] at ha
    linarith

lemma open_closed_bounded_below : is_bounded_below openi ∧ is_bounded_below closedi := by
  constructor
  · simp
    use 0
    intro a ha
    simp [openi] at ha
    linarith
  · simp
    use 0
    intro a ha
    simp [closedi] at ha
    linarith

lemma sup_open_closed_is_2 : 2 is_the_supremum_of openi ∧ 2 is_the_supremum_of closedi := by
  constructor
  · constructor
    · simp[openi]
      intro a ha0 ha2
      linarith
    intro x
    simp[openi]
    contrapose!
    intro h1
    sorry
  constructor
  · simp [closedi]
  intro b hb
  have h1 : 2 ∈ closedi := by simp [closedi]
  exact hb 2 h1

lemma inf_open_closed_is_0 : 0 is_the_infimum_of openi ∧ 0 is_the_infimum_of closedi := by
  constructor
  · constructor
    · simp[openi]
      intro a ha0 ha
      linarith
    intro x
    simp[openi]
    contrapose!
    intro h
    sorry
  constructor
  · simp[closedi]
    intro a ha0 ha
    linarith
  intro x ha
  have h1 : 0 ∈ closedi := by simp [closedi]
  exact ha 0 h1

lemma closed_has_max : ∃ x ∈ closedi, ∀ y ∈ closedi, y ≤ x := by
  use 2
  constructor
  · simp [closedi]
  · intro y hy
    simp [closedi] at hy
    linarith

lemma open_no_max : ¬∃ x ∈ openi, ∀ y ∈ openi, y ≤ x := by
  simp[openi]
  intro x hx h2
  use (x + 2) / 2
  constructor
  · linarith

  constructor
  · linarith
  linarith

lemma max_is_supremum :∃ s, s is_max_of closedi ∧ s is_the_supremum_of closedi := by
  use 2
  constructor
  · simp[closedi]
    use 2
    norm_num
  apply sup_open_closed_is_2.2

/-
Example 1.3.6

S = {r ∈ Q : r^2 < 2}
-/

def S : Set ℚ := {r | r^2 < 2}

example : is_bounded_above_Q S := by
  simp
  use 2
  intro q hq
  have hq2 : q^2 < 2 := by exact hq
  by_contra h
  push_neg at h
  have hq_sq : q^2 > 4 := by
    calc
      q^2 > 2^2 := by gcongr
      _ = 4     := by norm_num
  linarith

/-
Lemma 1.3.7

Assume s ∈ R is an upper bound for a set A ⊆ R. Then, s = supA if and only if, for every choice of ε > 0, there exists an element a ∈ A
satisfying s − ε < a
-/

lemma supremum (A : Set ℝ ) (s : ℝ) (h1 : s is_an_upper_bound_of A): s is_the_supremum_of A ↔ ∀ ε : ℝ, ε > 0 → ∃ a ∈ A, s - ε < a := by
  constructor
  · intro h ε hε
    simp at h h1
    rcases h with ⟨h2, h3⟩
    by_contra! hc
    have h4 : (s - ε) is_an_upper_bound_of A := by
      intro a ha
      exact hc a ha
    have h5 : s ≤ s - ε := by
      exact h3 (s - ε) h4
    linarith

  intro h
  constructor
  · exact h1
  intro b hb
  by_contra! hc
  specialize h (s - b)
  specialize h (by linarith)
  rcases h with ⟨a, ha, h₀⟩
  simp at hb
  linarith [hb a ha]

/-
Exercise 1.3.2.b

Assume i ∈ R is a lower bound for a set A ⊆ R. Then, i = inf A if and only if, for every choice of ε > 0, there exists an element a ∈ A satisfying
i + ε > a.
-/

lemma infimum (A : Set ℝ ) (i : ℝ) (h1 : i is_a_lower_bound_of A): i is_the_infimum_of A ↔ ∀ ε : ℝ, ε > 0 → ∃ a ∈ A, i + ε > a := by
constructor
· intro h ε hε
  simp at h h1
  rcases h with ⟨h2, h3⟩
  by_contra! hc
  have h4 : (i + ε) is_a_lower_bound_of A := by
    intro a ha
    exact hc a ha
  have h5 : i ≥ i + ε := by
    exact h3 (i + ε) h4
  linarith

intro h
constructor
· exact h1
intro b hb
by_contra! hc
specialize h (b - i)
specialize h (by linarith)
rcases h with ⟨a, ha, h₀⟩
simp at hb
linarith [hb a ha]

/-
Exercise 1.3.3.a

Let A be bounded below, and define B = {b ∈ R : b is a lower bound for A}. Show that sup B = inf A.
-/

def B (A : Set ℝ) := {b | b is_a_lower_bound_of A}

example (A : Set ℝ)(hA : is_bounded_below A):∀ a ∈ A,∀ b ∈ B A, ∃ s, s is_the_supremum_of (B A) ∧ s is_the_infimum_of A := by
  intro a ha b hb
  obtain ⟨ab, ha'⟩ := hA

  have h1 : (B A).Nonempty := by
    use ab
    exact ha'

  have hBboundabove : ∀ a ∈ A, ∀ b ∈ B A, b ≤ a → is_bounded_above (B A) := by
    intro a ha b hb h
    simp
    use a
    intro b' hb'
    exact hb' a ha

  have h2 : is_bounded_above (B A) := by
    apply hBboundabove a ha b hb
    exact hb a ha

  obtain ⟨s, hs⟩ := completeness (B A) ⟨h1, h2⟩
  use s
  constructor
  · exact hs
  obtain ⟨hs1, hs2⟩ := hs
  constructor
  · intro a ha
    exact hs2 a fun a_1 a_2 ↦ a_2 a ha
  intro x hx
  exact hs1 x hx


/-
Exercise 1.3.7

Prove that if a is an upper bound for A, and if a is also an element of A, then it must be that a = supA
-/

example (A : Set ℝ) (a : ℝ) : a is_an_upper_bound_of A ∧ a ∈ A → a is_the_supremum_of A := by
intro h
rcases h with ⟨h1, h2⟩
constructor
· exact h1
simp
intro x ha
exact ha a h2
