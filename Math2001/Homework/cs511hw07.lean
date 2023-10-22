import Mathlib.Data.Real.Basic
import Mathlib.Tactic.IntervalCases
import Library.Theory.Comparison
import Library.Theory.Parity
import Library.Theory.Prime
import Library.Tactic.Rel
import Library.Tactic.ModCases
import Library.Tactic.Extra
import Library.Tactic.Numbers
import Library.Tactic.Addarith
import Library.Tactic.Cancel
import Library.Tactic.Use

/-5.3.5-/
example : ¬ (∃ n : ℕ, n ^ 2 = 2) := by
  push_neg
  intro n
  have hn := le_or_succ_le n 1
  obtain hn | hn := hn
  · apply ne_of_lt
    calc
      n ^ 2 ≤ 1 ^ 2 := by rel [hn]
      _ < 2 := by numbers
  · apply ne_of_gt
    calc
      n^2 ≥ 2^2 := by rel[hn]
      _ > 2 := by numbers 
/-5.3.6 Exercise 2-/
example (P Q : Prop) : ¬ (P → Q) ↔ (P ∧ ¬ Q) := by
  constructor <;> intro h
  · constructor
    · push_neg at h
      exact And.left h
    · intro hq
      exact h (fun _ ↦ hq)
  · rcases h with ⟨hp, hq⟩ 
    intro h 
    apply hq
    apply h hp 


/-5.3.6 Exercise 9-/

/-5.3.6 Exercise 10-/
