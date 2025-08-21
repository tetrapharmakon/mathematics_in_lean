import MIL.Common
import Mathlib.Data.Real.Basic

namespace C03S03

section
variable (a b : ℝ)

example (h : a < b) : ¬b < a := by
  intro h'
  have : a < a := lt_trans h h'
  apply lt_irrefl a this

def FnUb (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, f x ≤ a

def FnLb (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, a ≤ f x

def FnHasUb (f : ℝ → ℝ) :=
  ∃ a, FnUb f a

def FnHasLb (f : ℝ → ℝ) :=
  ∃ a, FnLb f a

variable (f : ℝ → ℝ)

theorem noLB_crit (h : ∀ a, ∃ x, f x > a) : ¬FnHasUb f := by
  intro fnub
  rcases fnub with ⟨a, fnuba⟩
  rcases h a with ⟨x, hx⟩
  have : f x ≤ a := fnuba x
  linarith

example (h : ∀ a, ∃ x, f x < a) : ¬FnHasLb f := by
  intro fnlb
  rcases fnlb with ⟨a , fnlba⟩
  rcases h a with ⟨x , hx⟩
  have : f x ≥ a := fnlba x
  linarith -- linarith konws how to combine [hx : f x < a] and [this : f x ≥ a] to get False


example : ¬FnHasUb fun x ↦ x := by
  rintro ⟨a , ha⟩
  have : a + 1 ≤ a := ha (a + 1)
  linarith


#check (not_le_of_gt : a > b → ¬a ≤ b)
#check (not_lt_of_ge : a ≥ b → ¬a < b)
#check (lt_of_not_ge : ¬a ≥ b → a < b)
#check (le_of_not_gt : ¬a > b → a ≤ b)

example (h : Monotone f) (h' : f a < f b) : a < b := by
  apply lt_of_not_ge
  intro b_le_a
  have : f b ≤ f a := by apply h b_le_a
  linarith


example (h : a ≤ b) (h' : f b < f a) : ¬Monotone f := by
  intro mon_f
  have : f a ≤ f b := by apply mon_f h
  linarith -- linarith konws how to combine [foo < bar] and [foo ≥ bar] to imply bottom

example : ¬∀ {f : ℝ → ℝ}, Monotone f → ∀ {a b}, f a ≤ f b → a ≤ b := by
  intro h
  let f := fun x : ℝ ↦ (0 : ℝ)
  have monof : Monotone f := by
    intro u v u_le_v
    apply le_refl
  have h' : f 1 ≤ f 0 := le_refl _
  have : (1 : ℝ) ≤ 0 := h monof h'
  linarith

example (x : ℝ) (h : ∀ ε > 0, x < ε) : x ≤ 0 := by
  apply le_of_not_gt
  intro z_le_x
  have : x < x := by apply h x z_le_x
  linarith

end

section
variable {α : Type*} (P : α → Prop) (Q : Prop)

theorem all_not_of_not_ex (h : ¬∃ x, P x) : ∀ x, ¬P x := by
  intro x px
  apply h
  exact ⟨x , px⟩

theorem not_ex_of_all_not (h : ∀ x, ¬P x) : ¬∃ x, P x := by
  intro ⟨x , px⟩
  exact h x px

theorem ex_not_of_not_all (h : ¬∀ x, P x) : ∃ x, ¬P x := by
  by_contra h'
  apply h
  intro x
  by_contra h''
  exact h' ⟨x , h''⟩

theorem not_all_of_ex_not (h : ∃ x, ¬P x) : ¬∀ x, P x := by
  intro sgno
  rcases h with ⟨x , not_px⟩
  apply not_px
  exact sgno x

theorem of_notnot (h : ¬¬Q) : Q := by
  by_contra h'
  exact h h'

theorem notnot_of (h : Q) : ¬¬Q := by
  by_contra h'
  exact h' h

end

section
variable (f : ℝ → ℝ)

example (h : ¬FnHasUb f) : ∀ a, ∃ x, f x > a := by
  intro a
  by_contra h'
  push_neg at h'
  -- would be nice to use `dsimp` to simplify FnHasUb f into ∃ a, FnUb f a
  -- it's the line below
  exact h ⟨a , h'⟩



example (h : ¬∀ a, ∃ x, f x > a) : FnHasUb f := by
  push_neg at h
  exact h

example (h : ¬FnHasUb f) : ∀ a, ∃ x, f x > a := by
  dsimp only [FnHasUb, FnUb] at h
  push_neg at h
  exact h

example (h : ¬Monotone f) : ∃ x y, x ≤ y ∧ f y < f x := by
  dsimp only [Monotone] at h
  push_neg at h
  exact h

example (h : ¬FnHasUb f) : ∀ a, ∃ x, f x > a := by
  contrapose! h
  exact h

example (x : ℝ) (h : ∀ ε > 0, x ≤ ε) : x ≤ 0 := by
  contrapose! h
  use x / 2
  constructor <;> linarith

end

section
variable (a : ℕ)

example (h : 0 < 0) : a > 37 := by
  exfalso
  apply lt_irrefl 0 h

example (h : 0 < 0) : a > 37 :=
  absurd h (lt_irrefl 0)

example (h : 0 < 0) : a > 37 := by
  have h' : ¬0 < 0 := lt_irrefl 0
  contradiction --explosion principle

end
