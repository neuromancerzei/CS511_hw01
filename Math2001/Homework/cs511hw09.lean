import Mathlib.Data.Real.Basic
import Library.Theory.Parity
import Library.Theory.Comparison
import Library.Theory.Prime
import Library.Tactic.Induction
import Library.Tactic.ModCases
import Library.Tactic.Extra
import Library.Tactic.Numbers
import Library.Tactic.Addarith
import Library.Tactic.Use
import Mathlib.Tactic.GCongr
import Library.Tactic.Cancel

notation3 (prettyPrint := false) "forall_sufficiently_large "(...)", "r:(scoped P => ∃ C, ∀ x ≥ C, P x) => r

def B : ℕ → ℚ
  | 0 => 0
  | n + 1 => B n + (n + 1 : ℚ) ^ 2

/- 2 points -/
theorem problem4a (n : ℕ) : B n = n * (n + 1) * (2 * n + 1) / 6 := by
  simple_induction n with k hk
  . simp [B]
  . simp [B]
    rw [hk]
    ring

def S : ℕ → ℚ
  | 0 => 1
  | n + 1 => S n + 1 / 2 ^ (n + 1)

/- 3 points -/
theorem problem4b (n : ℕ) : S n = 2 - 1 / 2 ^ n := by
  simple_induction n with k hk
  . simp [S]
    numbers
  . simp [S, hk]
    ring

/- 3 points -/
theorem problem4c (n : ℕ) : S n ≤ 2 := by
  induction n with
  | zero => simp [S]
  | succ k hk =>
    have h_4b : S k.succ = 2 - 1 / 2 ^ k.succ := problem4b k.succ
    simp [h_4b]

def factorial : ℕ → ℕ
  | 0 => 1
  | n + 1 => (n + 1) * factorial n

notation:10000 n "!" => factorial n

/- 3 points -/
theorem problem4d (n : ℕ) : (n + 1) ! ≤ (n + 1) ^ n := by
  simple_induction n with k hk
  . simp [factorial]

  . have l : ℕ := (k)
    have h : (k+1)^l ≤  (k+1+1)^l := by
      simple_induction l with i hi
      . simp
      . calc
        (k + 1) ^ (i + 1) = (k+1)^i * (k+1) := by ring
        _ ≤ (k+1)^i * (k+1+1) := by simp
        _ ≤ (k+2)^i * (k+2) := by rel[hi]
        _ = (k+2)^(i+1) := by ring
    have hk_plus_1: k ≤ k+1 := by extra
    calc
      (k+1+1)! = (k+2)*(k+1)! := by rw[factorial]
      _ ≤ (k+2)*(k+1)^k := by rel[hk]
      _ ≤ (k+2)*(k+1+1)^k := by rel[h, hk_plus_1]
      _ = (k+2)^(k+1) := by ring

def q : ℕ → ℤ
  | 0 => 1
  | 1 => 2
  | n + 2 => 2 * q (n + 1) - q n + 6 * n + 6

/- 3 points -/
theorem problem5a (n : ℕ) : q n = (n:ℤ) ^ 3 + 1 := by
  two_step_induction n with k IH1 IH2
  . simp
  . simp
  calc
    q (k+1+1) = 2*q (k+1) - q k + 6*k + 6 := by rw [q]
    _ = 2*q (k+1) - (↑k ^ 3 + 1) + 6*k + 6 := by rw [IH1]
    _ = 2*((↑k + 1) ^ 3 + 1) - (↑k ^ 3 + 1) + 6*k + 6 := by rw [IH2]
    _ = (↑k + 2) ^ 3 + 1 := by ring

def r : ℕ → ℤ
  | 0 => 2
  | 1 => 0
  | n + 2 => 2 * r (n + 1) + r n

/- 3 points -/
theorem problem5b : forall_sufficiently_large n : ℕ, r n ≥ 2 ^ n := by
  simp [r]
  use 7
  intro n hn
  two_step_induction_from_starting_point n, hn with k hk IH1 IH2
  . simp [r]
  . simp [r]
  . calc
    r (k+1+1) = 2 * r (k + 1) + r k := by rw [r]
    _ ≥ 2 * (2 ^ (k + 1)) + 2 ^ k := by rel [IH1, IH2]
    _ = 2 ^ (k+2) + 2^k := by ring
    _ ≥  2 ^ (k+2) := by extra

/- 3 points -/
theorem problem5c (n : ℕ) (hn : 0 < n) : ∃ a x, Odd x ∧ n = 2 ^ a * x := by
  obtain hn | hn := Nat.even_or_odd n
  . obtain ⟨c,hc⟩ := hn
    rw [hc] at hn
    cancel 2 at hn
    have IH : ∃ a x, Odd x ∧ c = 2 ^ a * x := problem5c c hn-- inductive hypothesis
    obtain ⟨a', x', hx', h2ax⟩ := IH
    use a'+1, x'
    use hx'
    calc
      n = 2*c := by rw [hc]
      _ = 2 * (2^a'*x') := by rw [h2ax]
      _ = 2^(a'+1)*x' := by ring
  . use 0, n
    simp
    apply hn
