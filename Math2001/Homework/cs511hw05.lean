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

attribute [-instance] Int.instDivInt_1 Int.instDivInt EuclideanDomain.instDiv Nat.instDivNat
namespace Int
attribute [-simp] Nat.not_two_dvd_bit1 two_dvd_bit0

/-4.2.10 Exercise 2-/
example {n : ℤ} : 63 ∣ n ↔ 7 ∣ n ∧ 9 ∣ n := by
  constructor
  · rintro ⟨x, h⟩
    constructor
    rw[h]
    use 9*x
    ring
    rw[h]
    use 7*x
    ring
  
  · rintro ⟨⟨x, hx⟩, ⟨y,hy⟩⟩
    use 4*y - 3*x
    calc
      n = 28*n - 27*n := by ring
      _ = 28*(9*y) - 27*(7*x) := by nth_rw 1 [hy]; rw[hx]
      _ = 63*(4*y - 3*x) := by ring

/-4.2.10 Exercise 5-/
example {k : ℕ} : k ^ 2 ≤ 6 ↔ k = 0 ∨ k = 1 ∨ k = 2 := by
  constructor
  · intro h1
    have h2:= calc 
      k*k = k^2 := by ring 
      _ ≤ 6 := h1
      _ ≤ 3*3:= by numbers
    rw [← Nat.mul_self_le_mul_self_iff] at h2
    obtain h|h := eq_or_lt_of_le h2
    rw[h] at h1
    simp at h1
    interval_cases k
    left; rfl
    right; left; rfl
    right; right; rfl
  · rintro (h|h|h)
    repeat{rw[h]; numbers}


/-4.3.2-/
example : ∃! x : ℚ, ∀ a, a ≥ 1 → a ≤ 3 → (a - x) ^ 2 ≤ 1 := by
  use 2
  dsimp
  constructor
  · intro a h1 h2 
    have h1 : -1 ≤ a-2 := by addarith[h1]
    have h2 : 1 ≥ a-2 := by addarith[h2]
    have : (1:ℚ) = 1^2 := by exact Eq.symm (one_pow 2)
    rw[this]
    apply sq_le_sq' h1 h2
  · intro y h
    have h1 := h 1 (by numbers) (by numbers)
    have h3 := h 3 (by numbers) (by numbers)
    rw [← sub_eq_zero]
    rw [← sq_eq_zero_iff]
    apply le_antisymm
    · calc
      (y-2)^2 = ((1-y)^2 + (3-y)^2 -2)/2 := by ring
      _ ≤ ((1:ℚ) + 1 -2)/2 := by rel[h1, h3]
      _ = 0 := by numbers
    · extra

/-4.3.5 Exercise 1-/
example : ∃! x : ℚ, 4 * x - 3 = 9 := by
  use 3
  constructor
  numbers
  intro y h 
  have h : 4*y = 4 *3 := by addarith[h]
  cancel 4 at h

/-4.3.5 Exercise 2-/
example : ∃! n : ℕ, ∀ a, n ≤ a := by
  use 0
  dsimp
  constructor
  exact fun a ↦ Nat.zero_le a
  intro y h 
  cases y -- ℕ is an inductive type constructed by either 0 or as the successor of some nat
  · rfl
  · specialize h 0
    simp at h


/-4.4.4-/
example {p : ℕ} (hp : 2 ≤ p) (H : ∀ m : ℕ, 1 < m → m < p → ¬m ∣ p) : Prime p := by
  constructor
  · apply hp -- show that `2 ≤ p`
  intro m hmp
  have hp' : 0 < p := by extra
  have h1m : 1 ≤ m := Nat.pos_of_dvd_of_pos hmp hp'
  obtain hm | hm_left : 1 = m ∨ 1 < m := eq_or_lt_of_le h1m
  · -- the case `m = 1`
    left
    addarith [hm]
  · -- the case `1 < m`
    have hmlep : m ≤ p := Nat.le_of_dvd hp' hmp
    obtain hm| hm_right : m=p ∨ m < p := eq_or_lt_of_le hmlep
    · -- the case `m=p`
      right
      exact hm
    · -- the case `m<p`
      specialize H m hm_left hm_right
      contradiction

/-4.4.5-/
example {a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h_pyth : a ^ 2 + b ^ 2 = c ^ 2) : 3 ≤ a := by
    obtain ha_left | ha_right : a ≤ 2 ∨ a ≥ 3 := by apply le_or_gt
    obtain hb_left | hb_right : b ≤ 1 ∨ b ≥ 2 := by apply le_or_gt
    · have := calc --Case 1
        c^2 = a^2+b^2 := by rw [h_pyth]
        _   ≤ 2^2 + 1^2 := by rel [ha_left, hb_left]
        _   < 3^2 := by numbers
      have :=  lt_of_pow_lt_pow' 2 this
      interval_cases a <;> interval_cases b <;> interval_cases c
      all_goals numbers at h_pyth
    · have := calc --Case 2
        b^2 < a^2 + b^2 := by extra
        _   = c^2 := h_pyth
      
      have :=  lt_of_pow_lt_pow' 2 this
      have that := calc
        c^2 = a^2 + b^2 := by rw[h_pyth]
        _   ≤ 2^2 + b^2 := by rel[ha_left]
        _   = b^2 + 2*2 := by ring
        _   ≤ b^2 + 2*b := by rel[hb_right]
        _   < b^2+2*b+1 := by extra
        _   = (b+1)^2   := by ring
      have := calc
        b+1 ≤ c   := this
        _   < b+1 := lt_of_pow_lt_pow' 2 that
      have : 1<1 := by addarith[this]
      numbers at this
    · apply ha_right

/-4.4.6 Exercise 1-/
example {x y : ℝ} (n : ℕ) (hx : 0 ≤ x) (hn : 0 < n) (h : y ^ n ≤ x ^ n) :
    y ≤ x := by
    apply le_of_pow_le_pow n <;> assumption


/-4.4.6 Exercise 5-/
namespace Nat

example (p : ℕ) (h : Prime p) : p = 2 ∨ Odd p := by
  obtain ⟨hp, hdiv⟩ := h
  rw [le_iff_lt_or_eq] at hp
  rcases hp  with hp | hp
  · right
    rw [odd_iff_not_even]
    rintro ⟨k, hk⟩
    obtain this|this := hdiv 2 (by use k; rw[hk]) 
    numbers at this
    rw[← this] at hp
    numbers at hp
  · left
    rw[hp]


