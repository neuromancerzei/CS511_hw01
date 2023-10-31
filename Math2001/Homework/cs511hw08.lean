import Mathlib.Data.Real.Basic
import Library.Theory.Parity
import Library.Tactic.Induction
import Library.Tactic.ModCases
import Library.Tactic.Extra
import Library.Tactic.Numbers
import Library.Tactic.Addarith
import Library.Tactic.Use

/-6.1.3-/
example {a b d : ℤ} (h : a ≡ b [ZMOD d]) (n : ℕ) : a ^ n ≡ b ^ n [ZMOD d] := by
  simple_induction n with n ih
  · calc a^0 = b^0 := by ring
    _ ≡ b^0 [ZMOD d] := by exact Int.ModEq.refl (b ^ 0)
  · calc
    a ^ (n + 1) = a ^ n * a := rfl
    _ ≡ b^n *b [ZMOD d] := by rel[ih, h]
    _ = b^(n+1) := rfl

/-6.1.6-/
notation3 (prettyPrint := false) "forall_sufficiently_large "(...)", "r:(scoped P => ∃ C, ∀ x ≥ C, P x) => r
example : forall_sufficiently_large n : ℕ, 2 ^ n ≥ n ^ 2 := by
  dsimp
  use 4
  intro n hn
  induction_from_starting_point n, hn with k hk IH
  · -- base case
    numbers
  · -- inductive step
    calc  2^(k+1) = 2^k*2 := rfl
      _ ≥ k^2*2 := by rel[IH]
      _ = k^2 + k*k := by ring
      _ ≥ k^2 + 4*k := by rel[hk]
      _ = k^2 + 2*k+2*k := by ring
      _ ≥ k^2 + 2*k + 2*4 := by rel[hk]
      _ = (k+1)^2 + 7 := by ring
      _ ≥ (k+1)^2 := by extra

/-6.1.7Exercise 2, 6-/
example {a : ℝ} (ha : -1 ≤ a) (n : ℕ) : (1 + a) ^ n ≥ 1 + n * a := by
  simple_induction n with k ik
  . -- base case
    ring; numbers
  . -- inductive step
    have ha' : 0 ≤ 1 + a := by addarith[ha]
    calc
      (1 + a)^(k+1) = (1 + a) * (1 + a)^k := by ring
      _ ≥ (1 + a) * (1 + k * a) := by rel[ik]
      _ = 1 + (k + 1)*a + k*a^2 := by ring
      _ ≥ 1 + (k + 1)*a := by extra

example : forall_sufficiently_large n : ℕ, (3:ℤ) ^ n ≥ 2 ^ n + 100 := by
  dsimp
  use 5
  intro n
  simple_induction n with n ih
  intro a0
  numbers at a0
  intro hn
  have hn : 4≤n := by addarith[hn]
  rw[le_iff_eq_or_lt] at hn
  rcases hn with hn|hn
  · rw[← hn]
    numbers
  · have hn : n≥5 := by addarith [hn]
    exact calc
      (3:ℤ) ^ (n + 1) = 3 ^ n * 2 + 3^n  := by ring
      _ ≥ 3^n*2 := by extra
      _ ≥ (2 ^ n + 100)*2 := by rel[ih hn]
      _ = 2^(n+1) + 100 + 100 := by ring
      _ ≥ 2^(n+1) + 100 := by extra

/-Problem5(b)-/
def sum_of_odds : ℕ → ℕ
  | 0       => 0
  | (m + 1) => (2 * m + 1) + sum_of_odds m

theorem sum_of_odds_is_square (p: ℕ) : ∃q: ℕ, sum_of_odds p = q ^ 2 := by
  use p
  simple_induction p with n Hn
  . -- base case
    simp [sum_of_odds]
  . -- inductive step
    simp [sum_of_odds]
    rw [Hn]
    ring
