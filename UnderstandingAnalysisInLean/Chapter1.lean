import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

/-
Example 1.2.2. Let
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
