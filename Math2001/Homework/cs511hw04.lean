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

/-MOP Sec 3.1.4-/
example {n : ℤ} (hn : Odd n) : Odd (7 * n - 4) := by
  rcases hn with ⟨k, hk⟩
  rw[hk]
  use 7*k+1
  ring

/-MOP Sec 3.1.6-/
example {x y : ℤ} (hx : Odd x) (hy : Odd y) : Odd (x * y + 2 * y) := by
  obtain ⟨a, ha⟩ := hx
  obtain ⟨b, hb⟩ := hy
  rw[ha, hb]
  use 2*a*b+3*b+a+1
  ring

/-MOP Sec 3.1.8-/
example {n : ℤ} (hn : Even n) : Odd (n ^ 2 + 2 * n - 5) := by
  obtain ⟨k, hn⟩ := hn
  rw[hn]
  use 2*k^2+2*k-3
  ring

/-MOP Sec 3.1.10 Exercise 14-/
example (a b c : ℤ) : Even (a - b) ∨ Even (a + c) ∨ Even (b - c) := by
  obtain (ha | ha) := Int.even_or_odd a
  obtain (hb | hb) := Int.even_or_odd b
  obtain (hc | hc) := Int.even_or_odd c
  · --even, even, even
    left
    obtain ⟨x, hx⟩ := ha
    obtain ⟨y, hy⟩ := hb
    use x-y
    rw[hx,hy]
    ring
  · -- even, even, odd
    left
    obtain ⟨x, hx⟩ := ha
    obtain ⟨y, hy⟩ := hb
    use x-y
    rw[hx,hy]
    ring
  obtain (hc | hc) := Int.even_or_odd c
  · -- even, odd, even
    right; left
    obtain ⟨x, hx⟩ := ha
    obtain ⟨y, hy⟩ := hc
    use x+y
    rw[hx,hy]
    ring
  · -- even, odd, odd
    right; right
    obtain ⟨x, hx⟩ := hb
    obtain ⟨y, hy⟩ := hc
    use x-y
    rw[hx,hy]
    ring

  obtain (hb | hb) := Int.even_or_odd b
  obtain (hc | hc) := Int.even_or_odd c
  · --odd, even, even
    right; right
    obtain ⟨x, hx⟩ := hb
    obtain ⟨y, hy⟩ := hc
    use x-y
    rw[hx,hy]
    ring
  · -- odd, even, odd
    right; left
    obtain ⟨x, hx⟩ := ha
    obtain ⟨y, hy⟩ := hc
    use x+y+1
    rw[hx,hy]
    ring
  obtain (hc | hc) := Int.even_or_odd c
  · -- odd, odd, even
    left;
    obtain ⟨x, hx⟩ := ha
    obtain ⟨y, hy⟩ := hb
    use x-y
    rw[hx,hy]
    ring
  · -- odd, odd, odd
    right; right
    obtain ⟨x, hx⟩ := hb
    obtain ⟨y, hy⟩ := hc
    use x-y
    rw[hx,hy]
    ring


/-MOP Sec 4.1.3-/
example {a b : ℝ} (h : ∀ x, x ≥ a ∨ x ≤ b) : a ≤ b := by
  obtain h|h := h ((a+b)/2)
  · calc 
      b = 2 * ((a+b)/2) - a := by ring
      _ ≥ 2 * a - a := by rel[h]
      _ = a := by ring
  · calc 
      a = 2 * ((a+b)/2) - b := by ring
      _ ≤ 2 * b - b := by rel[h]
      _ = b := by ring

/-MOP Sec 4.1.6-/
example : ∃ c : ℝ, ∀ x y, x ^ 2 + y ^ 2 ≤ 4 → x + y ≥ c := by
  use -3
  intro x y hc 
  have := calc
    (x+y)^2 ≤ (x+y)^2 + (x-y)^2 := by extra
    _ = 2*(x^2+y^2) := by ring
    _ ≤ 2*4 := by rel[hc]
    _ ≤ 3^2 := by numbers 
  have that : (0:ℝ) ≤ 3 := by extra
  exact And.left (abs_le_of_sq_le_sq' this that)

/-MOP Sec 4.1.10 Exercise 2-/
example {n : ℤ} (hn : ∀ m, 1 ≤ m → m ≤ 5 → m ∣ n) : 15 ∣ n := by
  obtain ⟨x, hx⟩ := hn 3 (by numbers) (by numbers)
  obtain ⟨y, hy⟩ := hn 5 (by numbers) (by numbers)
  use 2*x - 3*y
  calc
    n = 10*n - 9*n := by ring
    _ = 10*(3*x) - 9*(5*y) :=  by nth_rw 1 [hx]; rw[hy]
    _ = 15*(2*x - 3*y) := by ring

/-MOP Sec 4.1.10 Exercise 4-/
notation3 (prettyPrint := false) "forall_sufficiently_large "(...)", "r:(scoped P => ∃ C, ∀ x ≥ C, P x) => r
example : forall_sufficiently_large x : ℝ, x ^ 3 + 3 * x ≥ 7 * x ^ 2 + 12 := by
  use 10
  intro x hx
  calc 
    x ^ 3 + 3 * x = x * x^2 + 3*x := by ring
    _ ≥ 10*x^2 + 3*10 := by rel[hx]
    _ = 7*x^2 + 12 + (18 + 3*x^2) := by ring
    _ ≥ 7*x^2 + 12 := by extra

/-MOP Sec 4.2.5-/
example {x : ℝ} : x ^ 2 + x - 6 = 0 ↔ x = -3 ∨ x = 2 := by
  constructor
  · intro hx
    have := calc
      (x+3)*(x-2) =  x ^ 2 + x - 6 := by ring
      _ = 0 := by rw[hx]
    rw [mul_eq_zero] at this
    obtain hx|hx := this
    left; addarith[hx]
    right; addarith[hx]
  · rintro (hx|hx)
    repeat {rw[hx]; numbers}

/-MOP Sec 4.2.6-/
example {a : ℤ} : a ^ 2 - 5 * a + 5 ≤ -1 ↔ a = 2 ∨ a = 3 := by
  constructor
  · intro h
    have := calc
      (2*a-5)^2 = 4*(a ^ 2 - 5 * a + 5) + 5 := by ring
      _ ≤ 4 *-1 + 5 := by rel[h]
      _ = 1^2 := by ring
    obtain ⟨h1, h2⟩ := abs_le_of_sq_le_sq' this (by numbers)
    have h1 : 2*2 ≤ 2*a := by addarith[h1]
    cancel 2 at h1
    have h2 : 2*a ≤ 2*3 := by addarith[h2]
    cancel 2 at h2
    interval_cases a
    · left; rfl
    · right; rfl
  · rintro (h|h) 
    repeat {rw[h]; numbers}