import Mathlib.Data.Real.Basic
import Library.Tactic.Extra
import Library.Tactic.Numbers
import Library.Tactic.Addarith
import Library.Tactic.Cancel

attribute [-instance] Int.instDivInt_1 Int.instDivInt Nat.instDivNat

theorem demorgan2 {p q:Prop}(h: ¬p ∧ ¬q): ¬ (p ∨ q):=by
  have h_not_p: ¬p := And.left h
  have h_not_q: ¬q := And.right h
  intro h_pq
  cases h_pq with
    | inl h_p => contradiction
    | inr h_q => contradiction

theorem demorgan3 {p q:Prop}(h: ¬p ∨ ¬q): ¬ (p ∧ q):=by
  intro h_pq
  have h_p: p := And.left h_pq
  have h_q: q := And.right h_pq
  cases h with
    | inl h_not_p => contradiction
    | inr h_not_q => contradiction


-- MCB 1.4.11 Exercise 1,2,3
example {x y : ℤ} (h1 : x + 3 ≥ 2 * y) (h2 : 1 ≤ y) : x ≥ -1 :=
  calc
    x = x+3-3 := by ring
    _ ≥ 2 * y -3 := by rel[h1]
    _ ≥ 2*1-3 := by rel[h2]
    _ = -1 := by ring


example {a b : ℚ} (h1 : 3 ≤ a) (h2 : a + 2 * b ≥ 4) : a + b ≥ 3 :=
  calc
    a + b = a + (a+2*b-a)/2 := by ring
    _ ≥ a + (4-a)/2 := by rel[h2]
    _ = 2 + a/2 := by ring
    _ ≥ 2 + 3/2 := by rel[h1]
    _ = 3.5 := by ring
    _ ≥ 3 := by numbers

example {x : ℤ} (hx : x ≥ 9) : x ^ 3 - 8 * x ^ 2 + 2 * x ≥ 3 :=
  calc
    x ^ 3 - 8 * x ^ 2 + 2 * x = x*(x^2-8*x+2) := by ring
    _ =x * ((x-4)^2-14) := by ring
    _ ≥ 9 * ((9-4)^2-14) := by rel[hx]
    _ = 99 := by ring
    _ ≥ 3 := by numbers



