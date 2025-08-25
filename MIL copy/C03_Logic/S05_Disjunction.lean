import MIL.Common
import Mathlib.Data.Real.Basic

namespace C03S05

section

variable {x y : ℝ}

example (h : y > x ^ 2) : y > 0 ∨ y < -1 := by
  left
  linarith [pow_two_nonneg x]

example (h : -y > x ^ 2 + 1) : y > 0 ∨ y < -1 := by
  right
  linarith [pow_two_nonneg x]

example (h : y > 0) : y > 0 ∨ y < -1 :=
  Or.inl h

example (h : y < -1) : y > 0 ∨ y < -1 :=
  Or.inr h

example : x < |y| → x < y ∨ x < -y := by
  rcases le_or_gt 0 y with h | h
  -- P ∨ Q → R requires a proof of
  -- P → R `and` a proof of Q → R
  -- P → R:
  · rw [abs_of_nonneg h]
    intro h; left; exact h
  -- Q → R:
  · rw [abs_of_neg h]
    intro h; right; exact h

example : x < |y| → x < y ∨ x < -y := by
  cases le_or_gt 0 y
  case inl h =>
    rw [abs_of_nonneg h]
    intro h; left; exact h
  case inr h =>
    rw [abs_of_neg h]
    intro h; right; exact h

example : x < |y| → x < y ∨ x < -y := by
  cases le_or_gt 0 y
  next h =>
    rw [abs_of_nonneg h]
    intro h; left; exact h
  next h =>
    rw [abs_of_neg h]
    intro h; right; exact h

example : x < |y| → x < y ∨ x < -y := by
  match le_or_gt 0 y with
    | Or.inl h =>
      rw [abs_of_nonneg h]
      intro h; left; exact h
    | Or.inr h =>
      rw [abs_of_neg h]
      intro h; right; exact h

namespace MyAbs

theorem le_abs_self (x : ℝ) : x ≤ |x| := by
  rcases le_or_gt 0 x with h | h
  rw [abs_of_nonneg h]
  rw [abs_of_neg h]
  linarith

theorem neg_le_abs_self (x : ℝ) : -x ≤ |x| := by
  rcases le_or_gt 0 x with h | h
  rw [abs_of_nonneg h]
  linarith
  rw [abs_of_neg h]

theorem abs_add (x y : ℝ) : |x + y| ≤ |x| + |y| := by
  rcases le_or_gt 0 (x + y) with h | h
  rw [abs_of_nonneg h]
  apply add_le_add (le_abs_self x) (le_abs_self y)
  rw [abs_of_neg h]
  simp only [neg_add]
  apply add_le_add (neg_le_abs_self x) (neg_le_abs_self y)

theorem lt_abs : x < |y| ↔ x < y ∨ x < -y := by
  constructor
  · rcases le_or_gt 0 y with h | h
    rw [abs_of_nonneg h]
    intro x_le_y
    exact Or.inl x_le_y
    rw [abs_of_neg h]
    intro x_le_my
    exact Or.inr x_le_my
  · rcases le_or_gt 0 y with h | h
    · rw [abs_of_nonneg h]
      intro bau
      rcases bau with a | b
      exact a
      have : -y ≤ y := by
        apply (le_trans (neg_nonpos_of_nonneg h) h)
      apply lt_of_lt_of_le b this
    · rw [abs_of_neg h]
      intro miao
      rcases miao with a | b
      have : x < -y := by
        apply (lt_trans a (lt_trans h (neg_pos_of_neg h)))
      exact this
      exact b


theorem abs_lt : |x| < y ↔ -y < x ∧ x < y := by
  constructor
  · intro bau
    rcases le_or_gt 0 x with h | h
    · rw [abs_of_nonneg h] at bau
      constructor
      · have fst : -y < -x := by apply neg_lt_neg bau
        have snd : -x ≤ x := by apply le_trans (neg_nonpos_of_nonneg h) h
        exact lt_of_lt_of_le fst snd
      · exact bau
    · rw [abs_of_neg h] at bau
      constructor
      · apply neg_lt_of_neg_lt bau
      · have : x < -x := by apply lt_trans h (neg_pos_of_neg h)
        apply lt_trans this bau
  · rintro ⟨pio,pao⟩
    rcases le_or_gt 0 x with h | h
    rw [abs_of_nonneg]
    exact pao
    exact h
    rw [abs_of_neg]
    exact neg_lt_of_neg_lt pio
    exact h


end MyAbs

end

example {x : ℝ} (h : x ≠ 0) : x < 0 ∨ x > 0 := by
  rcases lt_trichotomy x 0 with xlt | xeq | xgt
  · left
    exact xlt
  · contradiction
  · right; exact xgt

example {m n k : ℕ} (h : m ∣ n ∨ m ∣ k) : m ∣ n * k := by
  rcases h with ⟨a, rfl⟩ | ⟨b, rfl⟩
  · rw [mul_assoc]
    apply dvd_mul_right
  · rw [mul_comm, mul_assoc]
    apply dvd_mul_right

example {z : ℝ} (h : ∃ x y, z = x ^ 2 + y ^ 2 ∨ z = x ^ 2 + y ^ 2 + 1) : z ≥ 0 := by
  rcases h with ⟨a , t , q⟩
  rcases q with pio | pao
  · rw [pio]
    apply add_nonneg
    apply pow_two_nonneg
    apply pow_two_nonneg
  · rw [pao]
    apply add_nonneg
    apply add_nonneg
    apply pow_two_nonneg
    apply pow_two_nonneg
    norm_num

example {x : ℝ} (h : x ^ 2 = 1) : x = 1 ∨ x = -1 := by
  have h₁ : x ^ 2 - 1 = 0 := by rw [h,sub_self]
  have h₂ : (x + 1) * (x - 1) = 0 := by
    rw [← h₁]
    ring
  rcases eq_zero_or_eq_zero_of_mul_eq_zero h₂ with l | r
  right; linarith
  left; linarith

example {x y : ℝ} (h : x ^ 2 = y ^ 2) : x = y ∨ x = -y := by
  have h₁ : x ^ 2 - y ^ 2 = 0 := by rw [h,sub_self]
  have h₂ : (x + y) * (x - y) = 0 := by
    rw [← h₁]
    ring
  rcases eq_zero_or_eq_zero_of_mul_eq_zero h₂ with l | r
  right; linarith
  left; linarith

section
variable {R : Type*} [CommRing R] [IsDomain R]
variable (x y : R)

example (h : x ^ 2 = 1) : x = 1 ∨ x = -1 := by
  have h₁ : x ^ 2 - 1 = 0 := by rw [h,sub_self]
  have h₂ : (x + 1) * (x - 1) = 0 := by
    rw [← h₁]
    ring
  rcases eq_zero_or_eq_zero_of_mul_eq_zero h₂ with l | r
  right; apply add_eq_zero_iff_eq_neg.1; exact l
  left; apply sub_eq_zero.1; exact r


example (h : x ^ 2 = y ^ 2) : x = y ∨ x = -y := by
  have h₁ : x ^ 2 - y ^ 2 = 0 := by rw [h,sub_self]
  have h₂ : (x + y) * (x - y) = 0 := by
    rw [← h₁]
    ring
  rcases eq_zero_or_eq_zero_of_mul_eq_zero h₂ with l | r
  right; apply add_eq_zero_iff_eq_neg.1; exact l
  left; apply sub_eq_zero.1; exact r

end

example (P : Prop) : ¬¬P → P := by
  intro h
  cases em P
  · assumption
  · contradiction

example (P : Prop) : ¬¬P → P := by
  intro h
  by_cases h' : P
  · assumption
  contradiction

example (P Q : Prop) : P → Q ↔ ¬P ∨ Q := by
  constructor
  · intro h
    by_cases p : P
    · right; exact h p
    · left; exact p
  · intro h
    rcases h with l | r
    intro p
    contradiction
    intro p
    exact r
