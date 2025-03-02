import Mathlib.Data.Finset.Basic
import Mathlib.Tactic
import Mathlib.Data.List.Sort
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Floor.Div
import UnderstandingAnalysisInLean.Chapter1_4

/-
Simplifying assumption: Every real number can be represented by a unique
decimal expansion.

A function of the `decimal_expansion` type returns the n'th digit in the
decimal expansion of the real number it represents.

The whole part isn't represented because the version of Cantor's proof in
Understanding Analysis is constrained to the interval (0,1).
-/
def decimal_expansion : Type := ℕ → Fin 10

def is_eventually_periodic (r : decimal_expansion) : Prop :=
  ∃ (p n : ℕ), p > 0 ∧ ∀ k, r (n + k) = r (n + k + p)

def aperiodic (r : decimal_expansion) := ¬ is_eventually_periodic r

@[simp]
def r_eq (r₁ r₂ : decimal_expansion) : Prop :=
  ∀ (n : ℕ), r₁ n = r₂ n

@[simp]
def r_ne (r₁ r₂ : decimal_expansion) : Prop := ¬ r_eq r₁ r₂

-- Exercise 1.5.1
theorem reals_is_uncountable : ∀ (f : ℕ → decimal_expansion), (∀ (a1 a2 : ℕ), a1 ≠ a2 → r_ne (f a1) (f a2)) → ¬∀ (b : decimal_expansion), ∃ a, r_eq (f a) b := by
  intro f one_to_one
  by_contra onto

  let g : decimal_expansion :=
    fun (n : ℕ) => if f n n = 2 then 3 else 2

  have : ∀ (n : ℕ), r_ne (f n) g := by
    intro n
    simp
    use n
    by_contra hcontra
    by_cases f n n = (2 : Fin 10)
    case pos hfnn2 =>
      unfold g at hcontra
      simp [hfnn2] at hcontra
    case neg nhfnn2 =>
      unfold g at hcontra
      simp [nhfnn2] at hcontra

  let onto_g := onto g
  obtain ⟨a, h⟩ := onto_g
  let contrad := this a
  rw [r_ne] at contrad
  exact contrad h

-- Exercise 1.5.3.b
def r₁ : decimal_expansion := -- r₁ = 0,499...
  fun (n : ℕ) => if n = 1 then 4 else 9

def r₂ : decimal_expansion := -- r₂ = 0,500...
  fun (n : ℕ) => if n = 1 then 5 else 0

/- We are able to prove the false statement that 0,49... != 0,50
A limitation of our design choice
-/
lemma r₁_ne_r₂ : r_ne r₁ r₂ := by
  simp
  use 0
  unfold r₁ r₂
  simp
