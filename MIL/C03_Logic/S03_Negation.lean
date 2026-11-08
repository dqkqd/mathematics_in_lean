module
public import MIL.Common
public import Mathlib.Basic.Real.Basic

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

example (h : ∀ a, ∃ x, f x > a) : ¬FnHasUb f := by
  intro fnub
  rcases fnub with ⟨a, fnuba⟩
  rcases h a with ⟨x, hx⟩
  have : f x ≤ a := fnuba x
  linarith

example (h : ∀ a, ∃ x, f x < a) : ¬FnHasLb f := by
  intro fnlb
  rcases fnlb with ⟨a, fnlba⟩
  rcases h a with ⟨x, hx⟩
  have : f x ≥ a := fnlba x
  linarith

example : ¬FnHasUb fun x ↦ x := by
  intro fnub
  rcases fnub with ⟨a, fnuba⟩
  have: a + 1 ≤ a := fnuba (a + 1)
  linarith

#check (not_le_of_gt : a > b → ¬a ≤ b)
#check (not_lt_of_ge : a ≥ b → ¬a < b)
#check (lt_of_not_ge : ¬a ≥ b → a < b)
#check (le_of_not_gt : ¬a > b → a ≤ b)

example (h : Monotone f) (h' : f a < f b) : a < b := by
  have : ¬a ≥ b := by
    intro ageb
    linarith [h ageb]
  apply lt_of_not_ge this

example (h : a ≤ b) (h' : f b < f a) : ¬Monotone f := by
  intro monof
  have: f a ≤ f b := monof h
  linarith

example : ¬∀ {f : ℝ → ℝ}, Monotone f → ∀ {a b}, f a ≤ f b → a ≤ b := by
  intro h
  let f := fun x : ℝ ↦ (0 : ℝ)
  have monof : Monotone f := by
      intro a b aleb
      linarith
  have h' : f 1 ≤ f 0 := le_refl (f 1)
  have : (1 : ℝ) ≤ (0 : ℝ) := h monof h'
  linarith

example (x : ℝ) (h : ∀ ε > 0, x < ε) : x ≤ 0 := by
  apply le_of_not_gt
  intro (h1: x > 0)
  have : x < x := h x h1
  linarith

end

section
variable {α : Type*} (P : α → Prop) (Q : Prop)

example (h : ¬∃ x, P x) : ∀ x, ¬P x := by
  intro x p
  have h1: ∃ x, P x := by
    use x
  apply h h1

example (h : ∀ x, ¬P x) : ¬∃ x, P x := by
  rintro ⟨x, p⟩
  have h' := h x
  apply h' p

example (h : ¬∀ x, P x) : ∃ x, ¬P x := by
  by_contra h'
  apply h
  intro x
  show P x
  by_contra h''
  exact h' ⟨x, h''⟩

example (h : ∃ x, ¬P x) : ¬∀ x, P x := by
  intro h'
  rcases h with ⟨x, np⟩
  apply np (h' x)

example (h : ¬∀ x, P x) : ∃ x, ¬P x := by
  by_contra h'
  apply h
  intro x
  show P x
  by_contra h''
  exact h' ⟨x, h''⟩

example (h : ¬¬Q) : Q := by
  by_contra hnq
  exact h hnq

example (h : Q) : ¬¬Q := by
  intro hq
  exact hq h

end

section
variable (f : ℝ → ℝ)

example (h : ¬FnHasUb f) : ∀ a, ∃ x, f x > a := by
  -- take an arbitrary `a`
  intro a
  -- suppose that there is no `x` such that f x > a
  by_contra h1
  -- we prove that `h` fails, which means `FnHasUb f` true.
  -- in other word, there exist upperbound for `f`
  apply h
  -- we prove that the upperbound is `a`
  use a
  show ∀ x, f x ≤ a
  -- take a random x
  intro x
  -- we prove that f x ≤ a by contradiction.
  -- Suppose we don't have f x ≤ a
  by_contra h2
  -- then f x > a
  have h3: f x > a := by linarith
  -- but this contradict with h1 because there is no `x` such that `f x > a`
  exact h1 ⟨x, h3⟩

example (h : ¬∀ a, ∃ x, f x > a) : FnHasUb f := by
  push Not at h
  exact h

example (h : ¬FnHasUb f) : ∀ a, ∃ x, f x > a := by
  dsimp only [FnHasUb, FnUb] at h
  push Not at h
  exact h

example (h : ¬Monotone f) : ∃ x y, x ≤ y ∧ f y < f x := by
  dsimp only [Monotone] at h
  push Not at h
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
  contradiction

end
