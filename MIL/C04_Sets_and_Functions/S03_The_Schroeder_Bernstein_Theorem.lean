module
public import Mathlib.Data.Set.Function
public import MIL.Common

open Set
open Function

noncomputable section
open Classical
variable {α β : Type*} [Nonempty β]

section
variable (f : α → β) (g : β → α)

def sbAux : ℕ → Set α
  | 0 => univ \ g '' univ
  | n + 1 => g '' (f '' sbAux n)

def sbSet :=
  ⋃ n, sbAux f g n

def sbFun (x : α) : β :=
  if x ∈ sbSet f g then f x else invFun g x

theorem sb_right_inv {x : α} (hx : x ∉ sbSet f g) : g (invFun g x) = x := by
  have : x ∈ g '' univ := by
    contrapose! hx
    rw [sbSet, mem_iUnion]
    use 0
    rw [sbAux, mem_sdiff]
    use trivial
  have : ∃ y, g y = x := exists_mem_univ.mp this
  exact (invFun_eq  this)

-- my full proof
example (hf : Injective f) : Injective (sbFun f g) := by
  -- we prove and aux that if x is in A, then the `g f` should also be in A
  have hx: ∀ x ∈ sbSet f g, g (f x) ∈ sbSet f g := by
    -- let x be in A
    rintro x xinA
    rw [sbSet, mem_iUnion] at *
    -- there exists i such that x ∈ Aᵢ
    rcases xinA with ⟨i, xAi⟩
    -- because sbAux is defined as `S(n + 1) => g '' (f '' Sn)`,
    -- so (g f x) is in S(i + 1)
    use i + 1
    simp [sbAux]
    use x

  rintro x1 x2
  rw [sbFun, sbFun]
  rintro eq

  by_cases h1: x1 ∈ sbSet f g
  . by_cases h2: x2 ∈ sbSet f g
    . simp [h1, h2] at eq
      exact hf eq
    . simp [h1, h2] at eq
      have h := hx x1 h1
      rw [eq, sb_right_inv f g h2] at h
      exact absurd h h2
  by_cases h2: x2 ∈ sbSet f g
  . simp [h1, h2] at eq
    have h := hx x2 h2
    rw [← eq, sb_right_inv f g h1] at h
    exact absurd h h1
  simp [h1, h2] at eq
  rw [← sb_right_inv f g h1, ← sb_right_inv f g h2]
  rw [eq]

theorem sb_injective (hf : Injective f) : Injective (sbFun f g) := by
  set A := sbSet f g with A_def
  set h := sbFun f g with h_def

  rintro x1 x2 (eq: h x1 = h x2)
  simp [h_def, sbFun] at eq
  by_cases xA: x1 ∈ A ∨ x2 ∈ A
  . wlog x1A: x1 ∈ A generalizing x1 x2 eq xA
    . symm
      apply this eq.symm xA.symm (xA.resolve_left x1A)
    simp [A_def] at x1A
    simp [x1A] at eq
    have x2A: x2 ∈ A := by
      by_contra x2a
      simp [A_def] at x2a
      simp [x2a] at eq
      rw [← sb_right_inv f g x2a, ← eq] at x2a
      apply x2a
      rw [sbSet, mem_iUnion] at *
      rcases x1A with ⟨i, xAi⟩
      use i + 1
      simp [sbAux]
      use x1
    simp [A_def] at x2A
    simp [x2A] at eq
    exact hf eq
  push Not at xA
  simp [A_def] at xA
  simp [xA] at eq
  rw [← sb_right_inv f g xA.left, ← sb_right_inv f g xA.right]
  rw [eq]

theorem sb_surjective (hg : Injective g) : Surjective (sbFun f g) := by
  intro y
  simp [sbFun]
  let gy := g y
  by_cases gyA: gy ∈ sbSet f g
  .
    -- we prove that there exists x such that g f x = gy
    have : ∃ x ∈ sbSet f g, g (f x) = gy := by
      simp [sbSet] at gyA
      -- because gy ∈ A, there exists i such that g ∈ Aᵢ
      rcases gyA with ⟨i, gAi⟩
      -- there are two cases for i, zero and non zero
      cases i with
      | zero =>
        -- if i is zero, then gy ∉ A, this is the contradiction
        simp [sbAux] at gAi
        have := gAi y
        contradiction
      | succ n =>
        -- if i is not zero, there exists n such that i = n + 1
        simp [sbAux] at gAi
        -- there exists x in Sₙ such that (g f x) = gy
        rcases gAi with ⟨x, ⟨xAi, _⟩⟩
        have : x ∈ sbSet f g := by
          rw [sbSet, mem_iUnion]
          use n
        use x
    rcases this with ⟨x, ⟨xA, gfx⟩⟩
    use x
    simp [xA]
    -- because g is injective, we have f x = y
    exact hg gfx
  use gy
  simp [gyA]
  apply hg
  rw [sb_right_inv f g gyA]

end

theorem schroeder_bernstein {f : α → β} {g : β → α} (hf : Injective f) (hg : Injective g) :
    ∃ h : α → β, Bijective h :=
  ⟨sbFun f g, sb_injective f g hf, sb_surjective f g hg⟩

-- Auxiliary information
section
variable (g : β → α) (x : α)

#check (invFun g : α → β)
#check (leftInverse_invFun : Injective g → LeftInverse (invFun g) g)
#check (leftInverse_invFun : Injective g → ∀ y, invFun g (g y) = y)
#check (invFun_eq : (∃ y, g y = x) → g (invFun g x) = x)

end
