module
public import MIL.Common
public import Mathlib.Data.Set.Function
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

section

variable {α β : Type*}
variable (f : α → β)
variable (s t : Set α)
variable (u v : Set β)

open Function
open Set

example : f ⁻¹' (u ∩ v) = f ⁻¹' u ∩ f ⁻¹' v := by
  ext
  rfl

example : f '' (s ∪ t) = f '' s ∪ f '' t := by
  ext y; constructor
  · rintro ⟨x, xs | xt, rfl⟩
    · left
      use x, xs
    right
    use x, xt
  rintro (⟨x, xs, rfl⟩ | ⟨x, xt, rfl⟩)
  · use x, Or.inl xs
  use x, Or.inr xt

example : s ⊆ f ⁻¹' (f '' s) := by
  intro x xs
  show f x ∈ f '' s
  use x, xs

example : f '' s ⊆ v ↔ s ⊆ f ⁻¹' v := by
  constructor
  . simp only [subset_def]
    intro (yinv: ∀ y ∈ f '' s, y ∈ v) x xs
    let y := f x
    let hy: y ∈ f '' s := ⟨x, xs, rfl⟩
    show y ∈ v
    exact yinv y hy
  simp only [subset_def]
  intro (h: ∀ x ∈ s, f x ∈ v)
  rintro y ⟨x, xs, rfl⟩
  show f x ∈ v
  exact h x xs

example (h : Injective f) : f ⁻¹' (f '' s) ⊆ s := by
  intro x (v : f x ∈ (f '' s))
  -- ∃ a ∈ s, such that f a = f x
  rcases v with ⟨a, ha, hfa⟩
  -- because f is injective, we have a = x
  have xeqa : a = x := h hfa
  rw [← xeqa]
  exact ha

-- image of the preimage of u is a subset of u
-- in other words:
--   take all x that map into u
--   the image of that set is a subset of u
example : f '' (f ⁻¹' u) ⊆ u := by
  rintro y ⟨x, (yu : f x ∈ u), yeqfx⟩
  rw [← yeqfx]
  exact yu

-- Take the preimage of u, then take its image
-- The result is is a superset of u
example (h : Surjective f) : u ⊆ f '' (f ⁻¹' u) := by
  intro y yu -- with y ∈ u
  rcases h y with ⟨x, yeqfx⟩ -- we can find x such that f x = y
  have fxu : f x ∈ u := by
    rw [yeqfx]; exact yu
  exact ⟨x, fxu, yeqfx⟩

-- if s is a subset of t, then the image of s is a subset of the image of t
example (h : s ⊆ t) : f '' s ⊆ f '' t := by
  rintro y ⟨x, xs, xeq⟩
  use x, (h xs)

-- if u is a subset of v, then the preimage of u is also a subset of the preimage of v
example (h : u ⊆ v) : f ⁻¹' u ⊆ f ⁻¹' v := by
  rintro x (fxu : f x ∈ u)
  use h fxu

-- preimage of union of two set is a union of preimage of each set
example : f ⁻¹' (u ∪ v) = f ⁻¹' u ∪ f ⁻¹' v := by
  apply Subset.antisymm
  . rintro x (xuv: f x ∈ (u ∪ v))
    exact xuv
  rintro x (fxu | fxv)
  . left; exact fxu
  . right; exact fxv

-- image of intersection of two set, is an intersection of two image
example : f '' (s ∩ t) ⊆ f '' s ∩ f '' t := by
  rintro y ⟨x, ⟨xs, xt⟩, xeq⟩
  constructor
  . use x, xs
  use x,  xt

-- if f is injective, then the intersection of two image
-- is a subset of the image of of the intersection
example (h : Injective f) : f '' s ∩ f '' t ⊆ f '' (s ∩ t) := by
  rintro y ⟨⟨x, xs, xeq⟩, ⟨x', x't, x2eq⟩⟩
  have eq : x = x' := h (Eq.trans xeq x2eq.symm)
  have xt : x ∈ t := by
      rw [eq]; apply x't
  use x, ⟨xs, xt⟩

-- the differences of the images is contained in the image of the difference
example : f '' s \ f '' t ⊆ f '' (s \ t) := by
  rintro y ⟨⟨x, xs, xeq⟩, fnt⟩
  use x
  constructor
  . constructor
    . exact xs
    intro xt
    exact fnt ⟨x, xt, xeq⟩
  exact xeq

-- the differences of the preimages is contained in the preimage of the difference
example : f ⁻¹' u \ f ⁻¹' v ⊆ f ⁻¹' (u \ v) := by
  rintro x ⟨fu, fnv⟩
  use fu, fnv

-- the intersection of the image of s with v equals
-- the image of s intersected with the preimage of v
example : f '' s ∩ v = f '' (s ∩ f ⁻¹' v) := by
  apply Subset.antisymm
  . rintro y ⟨⟨x, xs, xeq⟩, yv⟩
    use x
    constructor
    . use xs
      rw [← xeq] at yv
      exact yv
    exact xeq
  rintro y ⟨x, ⟨xs, fv⟩, xeq⟩
  constructor
  . use x
  rw [← xeq]
  exact fv

-- the image of s intersected with the preimage of u
-- is contained in the intersection of the image of s with u
example : f '' (s ∩ f ⁻¹' u) ⊆ f '' s ∩ u := by
  rintro y ⟨x, ⟨xs, fv⟩, xeq⟩
  constructor
  . use x
  rw [← xeq]
  exact fv

-- the intersection of s and the preimage is contained
-- in the preimage of the image of s intersected with u
example : s ∩ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∩ u) := by
  rintro x ⟨xs, fxu⟩
  constructor
  . use x, xs
  exact fxu

-- the union of s and preimage of u is contained in
-- the preimage of the image of s union with u
example : s ∪ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∪ u) := by
  rintro x (xs | fxu)
  . left; use x
  right; exact fxu

variable {I : Type*} (A : I → Set α) (B : I → Set β)

-- image of union equals union of image
example : (f '' ⋃ i, A i) = ⋃ i, f '' A i := by
  ext y; constructor
  . -- suppose y is in the image of the union
    -- we can find x in the union such that f x = y
    rintro ⟨x, xAi, xeq⟩
    -- there exists i such that x ∈ Aᵢ, we prove y is in the image of Aᵢ
    simp only [mem_iUnion] at *
    rcases xAi with ⟨i, xAi⟩
    use i, x
  simp only [mem_iUnion]
  -- suppose there is i such that y is the image of Aᵢ
  -- this means there exists x ∈ Aᵢsuch that f x = y
  rintro ⟨i, ⟨x, xAi, xeq⟩⟩
  use x
  -- we need to prove that y is in the image of the union,
  -- this is true since y is in the image of Aᵢ
  simp only [mem_iUnion]
  use ⟨i, xAi⟩


-- image of intersection is contained in the intersection of images
example : (f '' ⋂ i, A i) ⊆ ⋂ i, f '' A i := by
  -- suppose y is in the image of union,
  -- there exists x such that x is in the intersection and f x = y
  rintro y ⟨x, xAi, xeq⟩
  -- we prove that y exists in all Aᵢ
  simp only [mem_iInter] at *
  rintro i
  use x, (xAi i)

-- given an injective function f.
-- the intersection of images is contained in the image of the intersection
example (i : I) (injf : Injective f) : (⋂ i, f '' A i) ⊆ f '' ⋂ i, A i := by
  -- suppose y is in the intersection of all the images
  -- we prove that y is in the image of the intersection
  -- which means there is `x` in the intersection such that
  -- f x = y
  intro y
  simp only [mem_iInter]
  intro h
  -- let's take x ∈ Aᵢ such that f x = y
  rcases h i with ⟨x, xAi, xeq⟩
  -- we prove that x is in the intersection
  have h1: x ∈ ⋂ j, A j := by
    simp only [mem_iInter]
    -- given a arbitrary index j
    intro j
    -- because y in the intersection of all images, y must be
    -- in the image of Aⱼ, so there exists x' such that f x' = y
    rcases h j with ⟨x', x'Aj, x'eq⟩
    -- because y is injective, x must be equal x'
    have eq : x' = x := injf (Eq.trans x'eq xeq.symm)
    -- therefore, x ∈ Aⱼ
    rw [eq] at x'Aj
    exact x'Aj
  use x

-- preimage of union equals union of all preimages
example : (f ⁻¹' ⋃ i, B i) = ⋃ i, f ⁻¹' B i := by
  ext x; simp

example : (f ⁻¹' ⋂ i, B i) = ⋂ i, f ⁻¹' B i := by
  ext x; simp

example : InjOn f s ↔ ∀ x₁ ∈ s, ∀ x₂ ∈ s, f x₁ = f x₂ → x₁ = x₂ :=
  Iff.refl _

end

section

open Set Real

example : InjOn log { x | x > 0 } := by
  intro x xpos y ypos e
  calc
    x = exp (log x) := by rw [exp_log xpos]
    _ = exp (log y) := by rw [e]
    _ = y := by apply exp_log ypos


example : range exp = { y | y > 0 } := by
  ext y; constructor
  . rintro ⟨x, req⟩
    simp
    rw [← req]
    apply exp_pos
  intro ypos
  simp at *
  exact ypos

example : InjOn sqrt { x | x ≥ 0 } := by
  intro x xpos y ypos e
  calc
    x = (√x) ^ 2 := by rw [sq_sqrt xpos]
    _ = (√y) ^ 2 := by rw [e]
    _ = y := by apply sq_sqrt ypos

example : InjOn (fun x ↦ x ^ 2) { x : ℝ | x ≥ 0 } := by
  intro x xpos y ypos e
  calc
    x = √(x ^ 2) := by rw [sqrt_sq xpos]
    _ = √(y ^ 2) := by congr
    _ = y := by apply sqrt_sq ypos

example : sqrt '' { x | x ≥ 0 } = { y | y ≥ 0 } := by
  ext y; constructor
  . rintro ⟨_, _, xeq⟩
    simp
    rw [← xeq]
    apply sqrt_nonneg
  simp
  intro ynonneg
  use y^2
  constructor
  . apply pow_nonneg ynonneg
  exact sqrt_sq ynonneg

example : (range fun x ↦ x ^ 2) = { y : ℝ | y ≥ 0 } := by
  ext y; constructor
  . simp
    intro x xsq
    rw [← xsq]
    apply pow_two_nonneg x
  simp
  intro ynonneg
  use sqrt y
  exact sq_sqrt ynonneg

end

section
variable {α β : Type*} [Inhabited α]

#check (default : α)

variable (P : α → Prop) (h : ∃ x, P x)

#check Classical.choose h

example : P (Classical.choose h) :=
  Classical.choose_spec h

noncomputable section

open Classical

def inverse (f : α → β) : β → α := fun y : β ↦
  if h : ∃ x, f x = y then Classical.choose h else default

theorem inverse_spec {f : α → β} (y : β) (h : ∃ x, f x = y) : f (inverse f y) = y := by
  rw [inverse, dite_eq_left h]
  exact Classical.choose_spec h

variable (f : α → β)

open Function

example : Injective f ↔ LeftInverse (inverse f) f := by
  constructor
  . intro injf x
    have h := inverse_spec (f x) (⟨x, rfl⟩)
    exact injf h
  intro linv a b feq
  calc
    a = inverse f (f a) := Eq.symm (linv a)
    _ = inverse f (f b) := by rw [feq]
    _ = b := linv b

example : Surjective f ↔ RightInverse (inverse f) f := by
  constructor
  . intro surj y
    exact inverse_spec y (surj y)
  intro rinv b
  have h := rinv b
  use (inverse f b)

end

section
variable {α : Type*}
open Function

-- There is no surjective function from a set to its power set.
theorem Cantor : ∀ f : α → Set α, ¬Surjective f := by
  -- Suppose f is a surjective function
  intro f surj
  -- Let S be a set of all elements such that each of them doesn't belong
  -- to the set created by function f.
  let S := {j | j ∉ f j}
  -- because f is surjective, there is an element s such that S = f s
  rcases surj S with ⟨s, h⟩
  -- we prove that s ∉ f s by contradiction
  have h1: s ∉ f s := by
    -- Suppose s ∈ f s
    intro h'
    have : s ∉ f s := by
      -- because S = f s, we also have s ∈ S
      rw [h] at h'
      -- because S contain elements that doesn't belong to their own images,
      -- we should have s ∉ f s
      simp [S] at h'
      exact h'
    -- we have both s ∈ f s and s ∉ f s, this is a constradiction
    contradiction

  -- because s ∉ f s, and S = f s, so s ∉ S
  have h2: s ∉ S := by rwa [h] at h1

  -- also because s ∉ f s, and by definition of S, we have s ∈ S
  have h3: s ∈ S := h1

  -- h2 and h3 both contradict
  contradiction

-- COMMENTS: TODO: improve this
end
