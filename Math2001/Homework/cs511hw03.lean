import Mathlib.Data.Real.Basic
import Library.Theory.Comparison
import Library.Theory.Parity
import Library.Tactic.Extra
import Library.Tactic.Numbers
import Library.Tactic.Addarith
import Library.Tactic.Cancel
import Library.Tactic.Use

attribute [-instance] Int.instDivInt_1 Int.instDivInt Nat.instDivNat

/-Example 2.5.2-/
example {t : ℝ} (h : ∃ a : ℝ, a * t < 0) : t ≠ 0 := by
  obtain ⟨x, hxt⟩ := h
  have H := le_or_gt x 0
  obtain hx | hx := H
  · have hxt' : 0 < (-x) * t := by addarith [hxt]
    have hx' : 0 ≤ -x := by addarith [hx]
    cancel -x at hxt'
    apply ne_of_gt
    apply hxt'
  · have := calc 
      0 < -x * t := by addarith[hxt]
      _ = x*(-t) := by ring
    cancel x at this
    have : 0 > t := by exact Iff.mp neg_pos this
    exact ne_of_lt this

/-Example 2.5.6-/
example (a : ℤ) : ∃ m n : ℤ, m ^ 2 - n ^ 2 = 2 * a + 1 := by
  use a+1, a
  ring

/-Example 2.5.7-/
example {p q : ℝ} (h : p < q) : ∃ x, p < x ∧ x < q := by
  use (p+q)/2
  constructor
  · calc 
    p = (p+p)/2 := by ring
    _ < (p+q)/2 := by rel[h]
  · calc 
    (p+q)/2 < (q+q)/2 := by rel[h]
    _ = q := by ring

/-Mop 2.5.9 Exercise 5-/
example (x : ℚ) : ∃ y : ℚ, y ^ 2 > x := by
  have h := le_or_gt 0 x
  obtain h | h := h
  · use x+1
    calc 
      (x+1)^2 = x^2 + 1 + 2*x := by ring
      _ > 2*x := by extra
      _ = x + x := by ring
      _ ≥ 0+x := by rel[h]
      _ = x := by ring
  · use x-1
    have : 0 < -x := Iff.mpr neg_pos h
    calc 
      (x-1)^2 = x^2 + 1 + -2*x := by ring
      _ > -2*x := by extra
      _ = -x + -x := by ring
      _ > 0 + 0 := by rel[this, this]
      _ = 0 := by ring
      _ > x := by rel[h]

/-Mop 2.5.9 Exercise 6-/
example {t : ℝ} (h : ∃ a : ℝ, a * t + 1 < a + t) : t ≠ 1 := by
  intro ht
  rcases h with ⟨a, h⟩ 
  rw[ht] at h
  apply Iff.mp (lt_self_iff_false (a+1))
  simp at h 

/-Mop 2.5.9 Exercise 7-/
example {m : ℤ} (h : ∃ a, 2 * a = m) : m ≠ 5 := by
  obtain ⟨a, h⟩ := h
  intro hm
  rw[hm] at h
  simp at h
  obtain h1 | h1 :=  le_or_gt a 2 
  · have := calc
      5 = 2*a := by rw[h]
      _ ≤ 2 * 2 := by rel[h1] 
    simp at this
  · have h1 : a ≥ 3 := by exact h1
    have := calc
      5 = 2 * a := by rw[h]
      _ ≥ 2 * 3 := by rel[h1]
      _ = 6 := by numbers
    simp at this
  