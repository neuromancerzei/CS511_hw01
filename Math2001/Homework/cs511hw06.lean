import Mathlib.Data.Real.Basic
import Mathlib.Tactic.IntervalCases
import Library.Theory.Comparison
import Library.Theory.Parity
import Library.Theory.Prime
import Library.Tactic.ModCases
import Library.Tactic.Extra
import Library.Tactic.Numbers
import Library.Tactic.Addarith
import Library.Tactic.Cancel
import Library.Tactic.Use

def Tribalanced (x : ℝ) : Prop := ∀ n : ℕ, (1 + x / n) ^ n < 3

def Superpowered (k : ℕ) : Prop := ∀ n : ℕ, Prime (k ^ k ^ n + 1)

/- MoP Section 5.1.7 Exercise 11-14 -/
example {P Q : α → Prop} (h : ∀ x, P x ↔ Q x) : (∃ x, P x) ↔ (∃ x, Q x) := by
  constructor
  · rintro ⟨x, hx⟩
    use x
    exact (h x).mp hx
  · rintro ⟨x, hx⟩
    use x
    exact (h x).mpr hx

example (P : α → β → Prop) : (∃ x y, P x y) ↔ ∃ y x, P x y := by
  constructor
  · rintro ⟨x, y, hp⟩
    exact ⟨y, x, hp⟩
  · rintro ⟨y, x, hp⟩
    exact ⟨x, y, hp⟩

example (P : α → β → Prop) : (∀ x y, P x y) ↔ ∀ y x, P x y := by
  constructor
  · intros h y x
    exact h x y
  · intros h x y
    exact h y x

example (P : α → Prop) (Q : Prop) : ((∃ x, P x) ∧ Q) ↔ ∃ x, (P x ∧ Q) := by
  constructor
  · rintro ⟨⟨x, hp⟩, hq⟩
    exact ⟨x, hp, hq⟩
  · rintro ⟨x, hp, hq⟩
    exact ⟨⟨x, hp⟩, hq⟩

/- MoP Section 5.2.7 Exercise 1-/
example : ∃ x : ℝ, Tribalanced x ∧ ¬ Tribalanced (x + 1) := by
  by_cases h0: Tribalanced 1
  . use 1
    dsimp[Tribalanced] at *
    constructor
    . apply h0
    . simp
      use 1
      numbers
  . use 0
    constructor
    . intro n
      conv => ring_nf
      numbers
    . conv => ring_nf
      apply h0

/- MoP Section 5.2.7 Exercise 3 -/
theorem superpowered_one : Superpowered 1 := by
  intro n
  conv => ring_nf
  exact prime_two

theorem not_superpowered_three : ¬ Superpowered 3 := by
  intro h
  dsimp [Superpowered] at h
  have four_prime : Prime (3 ^ 3 ^ 0 + 1) := h 0
  conv at four_prime => numbers -- simplifies that statement to `Prime 4`
  have four_not_prime : ¬ Prime 4
  · apply not_prime 2 2
    · numbers -- show `2 ≠ 1` 
    · numbers -- show `2 ≠ 4` 
    · numbers -- show `4 = 2 * 2`
  contradiction

example : ∃ k : ℕ, Superpowered k ∧ ¬ Superpowered (k + 1) := by
  by_cases Superpowered 2
  · use 2
    exact ⟨h, not_superpowered_three⟩
  · use 1 
    exact ⟨superpowered_one, h⟩
