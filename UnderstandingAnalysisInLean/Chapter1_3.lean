import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

/-
Chapter 1.3
-/
@[simp]
def is_bounded_above (A : Set ℝ) := ∃ (b : ℝ), ∀ a ∈ A, a ≤ b
@[simp]
def is_bounded_above_N (A : Set ℕ) := ∃ (b : ℕ), ∀ a ∈ A, a ≤ b
@[simp]
def is_bounded_above_Q (A : Set ℚ) := ∃ (b : ℚ), ∀ a ∈ A, a ≤ b

@[simp]
def is_bounded_below (A : Set ℝ) := ∃ (b : ℝ), ∀ a ∈ A, a ≥ b

@[simp]
def is_an_upper_bound_of (s : ℝ) (A : Set ℝ) := ∀ a ∈ A, a ≤ s
infixl:50 " is_an_upper_bound_of " => is_an_upper_bound_of
@[simp]
def is_an_upper_bound_of_N (s : ℕ) (A : Set ℕ) := ∀ a ∈ A, a ≤ s
infixl:50 " is_an_upper_bound_of_N " => is_an_upper_bound_of_N
@[simp]
def is_an_upper_bound_of_Q (s : ℚ) (A : Set ℚ) := ∀ a ∈ A, a ≤ s
infixl:50 " is_an_upper_bound_of_Q " => is_an_upper_bound_of_Q

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

@[simp]
def is_the_supremum_of (s : ℝ) (A : Set ℝ) := s is_an_upper_bound_of A ∧ ∀ x ∈ {x | x is_an_upper_bound_of A}, s ≤ x
infixl:50 " is_the_supremum_of " => is_the_supremum_of

@[simp]
def is_the_infimum_of (s : ℝ) (A : Set ℝ) := s is_a_lower_bound_of A ∧ ∀ x ∈ {x | x is_a_lower_bound_of A}, s ≥ x
infixl:50 " is_the_infimum_of " => is_the_infimum_of

def is_max_of (s : ℝ) (A : Set ℝ) := ∀ a ∈ A, s ≥ a
def is_min_of (s : ℝ) (A : Set ℝ) := ∀ a ∈ A, s ≤ a

axiom completeness : ∀ (A : Set ℝ) , A.Nonempty ∧ is_bounded_above A → ∃ s : ℝ , s is_the_supremum_of A


/-
Example 1.3.3
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
  intro b hb
  have h1 : 1 ∈ A := by
    use 1
    simp
  exact hb 1 h1

/-
Example 1.3.5
-/

def openi : Set ℝ := {x | 0 < x ∧ x < 2}
def closedi : Set ℝ := {x | 0 ≤ x ∧ x ≤ 2}

lemma open_closed_b_above : is_bounded_above openi ∧ is_bounded_above closedi := by
  constructor
  · simp
    use 2
    intro a ha
    simp [openi] at ha
    linarith
  simp
  use 2
  intro a ha
  simp [closedi] at ha
  linarith

lemma open_closed_b_below : is_bounded_below openi ∧ is_bounded_below closedi := by
  constructor
  · simp
    use 0
    intro a ha
    simp [openi] at ha
    linarith
  simp
  use 0
  intro a ha
  simp [closedi] at ha
  linarith

lemma sup_closed_is_2 : 2 is_the_supremum_of closedi := by
  constructor
  · simp [closedi]
  intro b hb
  have h1 : 2 ∈ closedi := by simp [closedi]
  exact hb 2 h1

lemma inf_closed_0 : 0 is_the_infimum_of closedi := by
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

/-
Example 1.3.6
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
-/

lemma sup (A : Set ℝ ) (s : ℝ) (h1 : s is_an_upper_bound_of A): s is_the_supremum_of A ↔ ∀ ε : ℝ, ε > 0 → ∃ a ∈ A, s - ε < a := by
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
  specialize h (s-b) (by linarith)
  rcases h with ⟨a, ha, h₀⟩
  simp at hb
  linarith [hb a ha]
