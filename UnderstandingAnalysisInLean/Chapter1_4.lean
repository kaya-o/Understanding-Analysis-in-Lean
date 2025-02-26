import Mathlib.Data.Finset.Basic
import Mathlib.Tactic
import UnderstandingAnalysisInLean.Chapter1
import Std.Data.List.Sort
import Mathlib.Data.Rat.Basic

/-
Chapter 1.4
-/

/-Theorem 1.4.1
For each n ∈ ℕ, assume closed Interval I(n) = [an,bn]. Assume each I(n) contains I(n+1),
then sequence of intervals has nonemtpy intersection ∩ I(n) ≠ ∅-/
def interval (a b : ℝ) : Set ℝ := {x:ℝ | a ≤ x ∧ x ≤ b}

/-
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
-/

/-Theorem 1.4.3-/
theorem density_Q_in_R: ∀ (a b:ℝ), a < b → ∃ (r: ℚ), a<r ∧ r<b:=by
    intro a b h
    sorry


/-Corollar 1.4.4
Given any real numbers a < b, there exists a irrational number t satisfying a < t < b
Idea: predefine irrational number as a number x ∈ ℝ \ ℚ -/


/-Theorem 1.4.5-/
theorem square_root_existence: ∃ (α : ℝ), α^2 = 2:=by
sorry

--Definition 1.4.6
def one_to_one (f : A → B):= ∀ (a1 a2 : A), a1 ≠ a2 → f a1 ≠ f a2

def onto (f : A → B):= ∀ (b : B), ∃ (a : A), f a = b

--Definition 1.4.7
@[simp]
def cardinality (A B):= ∃ (f : A → B), (one_to_one f) ∧ (onto f)
infixl:50 "~" => cardinality

--Definition 1.4.10
def countable (A) := ℕ ~ A
def uncountable (A) := ¬ (ℕ ~ A)

--Theorem 1.4.11
def neg_embedding : ℚ ↪ ℚ := ⟨(λ x ↦ -x), neg_injective⟩
def A₁ (n : ℕ) : Finset ℚ :=
    match n with
    | 0 => ∅
    | 1 =>
        {0}
    | (n+1) =>
        let A'' := (Finset.image (λ (p : Fin (n+1)) ↦ (p.val : ℚ) / (((n+1) - p.val) : ℚ)) Finset.univ).filter (λ x ↦ x ≠ 0)
        A'' ∪ A''.map neg_embedding

def A (n : ℕ) : Finset ℚ :=
    match n with
    | 0 => ∅
    | 1 =>
        {0}
    | (n+1) =>
        let A'' := (Finset.image (λ (p : Fin (n+1)) ↦ (p.val : ℚ) / (((n+1) - p.val) : ℚ)) Finset.univ).filter (λ x ↦ x ≠ 0)
        let A' := A'' ∪ A''.map neg_embedding
        A' \ (Finset.range n).biUnion A₁

theorem Q_is_countable: countable ℚ:= by
    rw [countable]
    simp
    let f : ℕ → ℕ → ℕ := λ p q ↦
        let n := p + q
        let sum₀ := (Finset.image (λ (n₀ : Fin (n-1)) ↦ A n₀) Finset.univ).sum (λ x ↦ x.card)
        let A₀ := (A n).sort (fun a b ↦ a < b)




theorem R_is_uncountable: uncountable ℝ := by
    intro h
    sorry

/-Theorem 1.4.12
If A⊆B and B is countable, then A is either countable, finite or empty-/

/-Theorem 1.4.13
(i)If A1...Am each countable sets, then A1∪...∪Am is countable
(ii)If An countable for each n ∈ ℕ, then ∪ An is countable-/
