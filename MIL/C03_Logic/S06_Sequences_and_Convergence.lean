module
public import MIL.Common
public import Mathlib.Basic.Real.Basic

namespace C03S06

def ConvergesTo (s : ℕ → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |s n - a| < ε

example : (fun x y : ℝ ↦ (x + y) ^ 2) = fun x y : ℝ ↦ x ^ 2 + 2 * x * y + y ^ 2 := by
  ext
  ring

example (a b : ℝ) : |a| = |a - b + b| := by
  congr
  ring

example {a : ℝ} (h : 1 < a) : a < a * a := by
  convert! (mul_lt_mul_iff_left₀ _).2 h
  · rw [one_mul]
  exact lt_trans zero_lt_one h

theorem convergesTo_const (a : ℝ) : ConvergesTo (fun _x : ℕ ↦ a) a := by
  intro ε εpos
  use 0
  intro n nneg
  dsimp
  rw [sub_self, abs_zero]
  apply εpos

theorem convergesTo_add {s t : ℕ → ℝ} {a b : ℝ}
      (cs : ConvergesTo s a) (ct : ConvergesTo t b) :
    ConvergesTo (fun n ↦ s n + t n) (a + b) := by
  intro ε εpos
  -- there is n₁ such that ∀ n ≥ n₁, |s n₁ - a| ≤ ε
  rcases cs (ε/2) (half_pos εpos) with ⟨n₁, sn⟩
  rcases ct (ε/2) (half_pos εpos) with ⟨n₂, tn⟩
  use max n₁ n₂
  intro n nmax
  have h₁: n ≥ n₁ := le_of_max_le_left nmax
  have h₂: n ≥ n₂ := le_of_max_le_right nmax
  dsimp
  calc
    |s n + t n - (a + b)| = |(s n - a) + (t n - b)| := by ring_nf
    _ ≤ |s n - a| + |t n - b| := by apply abs_add_le
    _ < ε/2 + ε/2 := by
      apply add_lt_add
      apply sn n h₁
      apply tn n h₂
    _ = ε := by ring

theorem convergesTo_mul_const {s : ℕ → ℝ} {a : ℝ} (c : ℝ) (cs : ConvergesTo s a) :
    ConvergesTo (fun n ↦ c * s n) (c * a) := by
  by_cases h : c = 0
  · convert convergesTo_const 0
    · rw [h]
      ring
    rw [h]
    ring
  have acpos : 0 < |c| := abs_pos.mpr h
  intro ε εpos
  dsimp
  rcases cs (ε/|c|) (div_pos εpos acpos) with ⟨m, cn⟩
  use m
  intro n ngem
  calc
    |c * s n - c * a| = |c * (s n - a)| := by ring_nf
    _ = |c| * |s n - a| := by apply abs_mul
    _ < |c| * (ε / |c|) := by
      apply mul_lt_mul_of_pos_left
      linarith [cn n ngem]
      apply acpos
    _ = ε := by
      apply mul_div_cancel₀
      apply abs_ne_zero.mpr h

theorem exists_abs_le_of_convergesTo {s : ℕ → ℝ} {a : ℝ} (cs : ConvergesTo s a) :
    ∃ N b, ∀ n, N ≤ n → |s n| < b := by
  have epos: (1 : ℝ) > 0 := by norm_num
  rcases cs (1 : ℝ) epos with ⟨m, cn⟩
  use m, |a| + 1
  intro n ngem
  have h: 1 > |s n| - |a| :=
    calc
      1 > |s n - a| := cn n ngem
      _ ≥ |s n| - |a| := by apply abs_sub_abs_le_abs_sub
  linarith


theorem aux {s t : ℕ → ℝ} {a : ℝ} (cs : ConvergesTo s a) (ct : ConvergesTo t 0) :
    ConvergesTo (fun n ↦ s n * t n) 0 := by
  intro ε εpos
  dsimp
  rcases exists_abs_le_of_convergesTo cs with ⟨n₁,b,snltb⟩
  have bpos: 0 < b := by
    apply lt_of_le_of_lt
    apply abs_nonneg (s n₁)
    apply snltb n₁ (le_refl n₁)

  have εbpos: ε/b > 0 := div_pos εpos bpos
  rcases ct (ε/b) εbpos with ⟨n₂, tn⟩
  use max n₁ n₂
  intro n nmax
  have h₁: n ≥ n₁ := le_of_max_le_left nmax
  have h₂: n ≥ n₂ := le_of_max_le_right nmax
  have h₃: |t n| < ε / b := by
    apply lt_of_eq_of_lt _ (tn n h₂)
    ring_nf
  calc
    |s n * t n - 0| = |s n * t n| := by ring_nf
    _ = |s n| * |t n| := by apply abs_mul
    _ < b * (ε / b) := by
      apply mul_lt_mul'
      apply le_of_lt (snltb n h₁)
      apply h₃
      apply abs_nonneg
      apply bpos
    _ = ε := by
      apply mul_div_cancel₀ ε
      linarith

theorem convergesTo_mul {s t : ℕ → ℝ} {a b : ℝ}
      (cs : ConvergesTo s a) (ct : ConvergesTo t b) :
    ConvergesTo (fun n ↦ s n * t n) (a * b) := by

  have h1: ConvergesTo (fun n ↦ s n - a) 0 := by
    convert convergesTo_add cs (convergesTo_const (-a))
    ring

  have h2: ConvergesTo (fun n ↦ t n - b) 0 := by
    convert convergesTo_add ct (convergesTo_const (-b))
    ring

  have h3: ConvergesTo (fun n ↦ s n * t n - a * b) 0 := by
    have h := aux cs h2
    have h' := aux (convergesTo_const b) h1
    convert convergesTo_add h h'
    ring
    simp

  convert convergesTo_add h3 (convergesTo_const (a * b))
  ring
  simp



theorem convergesTo_unique {s : ℕ → ℝ} {a b : ℝ}
      (sa : ConvergesTo s a) (sb : ConvergesTo s b) :
    a = b := by
  by_contra aneb
  have epos: |a - b| > 0 := abs_sub_pos.mpr aneb

  have h1: ConvergesTo (fun n ↦ - (s n)) (-b) := by
    convert convergesTo_mul_const (-1) sb
    simp
    ring
  have h2: ConvergesTo (fun n ↦ 0) (a - b) := by
    convert convergesTo_add sa h1
    simp

  rcases h2 |a - b| epos with ⟨n, hn⟩
  dsimp at hn

  have : |a - b| < |a - b| := by
    have h': |0 - (a - b)| < |a - b|:= hn n (le_refl _)
    simp at h'
    linarith [abs_sub_comm a b]

  apply lt_irrefl |a - b| this

section
variable {α : Type*} [LinearOrder α]

def ConvergesTo' (s : α → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |s n - a| < ε

end
