import MIL.Common
import Mathlib.Data.Real.Basic

namespace C02S04

section
variable (a b c d : ℝ)

#check (min_le_left a b : min a b ≤ a)
#check (min_le_right a b : min a b ≤ b)
#check (le_min : c ≤ a → c ≤ b → c ≤ min a b)

example : min a b = min b a := by
  apply le_antisymm
  · show min a b ≤ min b a
    apply le_min
    · apply min_le_right
    apply min_le_left
  · show min b a ≤ min a b
    apply le_min
    · apply min_le_right
    apply min_le_left

example : min a b = min b a := by
  have h : ∀ x y : ℝ, min x y ≤ min y x := by
    intro x y
    apply le_min
    apply min_le_right
    apply min_le_left
  apply le_antisymm
  apply h
  apply h

example : min a b = min b a := by
  apply le_antisymm
  repeat
    apply le_min
    apply min_le_right
    apply min_le_left

example : max a b = max b a := by
  have h : ∀ x y : ℝ, max x y ≤ max y x := by
    intro x y
    apply max_le
    apply le_max_right
    apply le_max_left
  apply le_antisymm
  apply h
  apply h
example : min (min a b) c = min a (min b c) := by
  apply le_antisymm
  · have h1 : min (min a b) c ≤ a := le_trans (min_le_left _ _) (min_le_left _ _)
    have h2 : min (min a b) c ≤ b := le_trans (min_le_left _ _) (min_le_right _ _)
    have h3 : min (min a b) c ≤ c := min_le_right _ _
    exact le_min h1 (le_min h2 h3)
  · have h1 : min a (min b c) ≤ a := min_le_left _ _
    have h2 : min a (min b c) ≤ b := le_trans (min_le_right _ _) (min_le_left _ _)
    have h3 : min a (min b c) ≤ c := le_trans (min_le_right _ _) (min_le_right _ _)
    exact le_min (le_min h1 h2) h3
theorem aux : min a b + c ≤ min (a + c) (b + c) := by
  apply le_min
  · have h : min a b ≤ a := min_le_left a b
    exact add_le_add_right h c
  · have h : min a b ≤ b := min_le_right a b
    exact add_le_add_right h c
example : min a b + c = min (a + c) (b + c) := by
  apply le_antisymm
  · exact aux a b c
  · have h : min (a + c) (b + c) + -c ≤ min ((a + c) + -c) ((b + c) + -c) :=
      aux (a + c) (b + c) (-c)
    rw [add_neg_cancel_right, add_neg_cancel_right] at h
    linarith
#check (abs_add : ∀ a b : ℝ, |a + b| ≤ |a| + |b|)

example : |a| - |b| ≤ |a - b| := by
  have h : |a - b + b| ≤ |a - b| + |b| := abs_add (a - b) b
  rw [sub_add_cancel] at h
  linarith
end

section
variable (w x y z : ℕ)

example (h₀ : x ∣ y) (h₁ : y ∣ z) : x ∣ z :=
  dvd_trans h₀ h₁

#check dvd_mul_of_dvd_left

example : x ∣ y * x * z := by
  apply dvd_mul_of_dvd_left
  apply dvd_mul_left

example : x ∣ x ^ 2 := by
  apply dvd_mul_left

example (h : x ∣ w) : x ∣ y * (x * z) + x ^ 2 + w ^ 2 := by
  have h1 : x ∣ y * (x * z) := by
    apply dvd_mul_of_dvd_right
    apply dvd_mul_right
  have h2 : x ∣ x ^ 2 := by apply dvd_mul_left
  have h3 : x ∣ w ^ 2 := by
    rw [sq]
    exact dvd_mul_of_dvd_left h w
  exact dvd_add (dvd_add h1 h2) h3
end

section
variable (m n : ℕ)

#check (Nat.gcd_zero_right n : Nat.gcd n 0 = n)
#check (Nat.gcd_zero_left n : Nat.gcd 0 n = n)
#check (Nat.lcm_zero_right n : Nat.lcm n 0 = 0)
#check (Nat.lcm_zero_left n : Nat.lcm 0 n = 0)

example : Nat.gcd m n = Nat.gcd n m := by
  have h : ∀ x y : ℕ, Nat.gcd x y ∣ Nat.gcd y x := by
    intro x y
    apply Nat.dvd_gcd
    apply Nat.gcd_dvd_right
    apply Nat.gcd_dvd_left
  apply Nat.dvd_antisymm
  apply h
  apply h
end
