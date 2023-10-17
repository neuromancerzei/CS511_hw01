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

/- Section 5.1.7 Exercise 11-14 -/
example {P Q : α → Prop} (h : ∀ x, P x ↔ Q x) : (∃ x, P x) ↔ (∃ x, Q x) := by
  constructor
  · rintro ⟨x, hx⟩
    use x
    obtain ⟨h, _ ⟩ := h x
    exact h hx
  · rintro ⟨x, hx⟩
    use x
    obtain ⟨_, h ⟩ := h x
    exact h hx

example (P : α → β → Prop) : (∃ x y, P x y) ↔ ∃ y x, P x y := by
  constructor
  repeat{rintro ⟨x, ⟨y, _⟩⟩; use y, x; assumption}

example (P : α → β → Prop) : (∀ x y, P x y) ↔ ∀ y x, P x y := by
  constructor
  repeat{exact fun (h y x) => h x y}

example (P : α → Prop) (Q : Prop) : ((∃ x, P x) ∧ Q) ↔ ∃ x, (P x ∧ Q) := by
  constructor
  · rintro ⟨⟨x, _⟩, _⟩
    use x
    exact ⟨by assumption, by assumption⟩
  · rintro ⟨x, ⟨_, _⟩⟩
    exact ⟨by use x; assumption, by assumption⟩

/- Section 5.2.7 Exercise 1-/

example : ∃ x : ℝ, Tribalanced x ∧ ¬ Tribalanced (x + 1) := by
  have h_lemma1 : Tribalanced 0 := by 
    intro n
    ring_nf
    numbers
  have h_lemma2 : ¬Tribalanced 2 := by
    intro h
    specialize h 2
    numbers at h
  by_cases Tribalanced 1
  · use 1
    ring_nf
    constructor <;> assumption
  · use 0
    ring_nf
    constructor <;> assumption

/- Section 5.2.7 Exercise 3-/

example : ∃ k : ℕ, Superpowered k ∧ ¬ Superpowered (k + 1) := by
  sorry