import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Real.Basic
import MIL.Common

section
variable (R : Type*) [Ring R]

#check (add_assoc : ∀ a b c : R, a + b + c = a + (b + c))
#check (add_comm : ∀ a b : R, a + b = b + a)
#check (zero_add : ∀ a : R, 0 + a = a)
#check (neg_add_cancel : ∀ a : R, -a + a = 0)
#check (mul_assoc : ∀ a b c : R, a * b * c = a * (b * c))
#check (mul_one : ∀ a : R, a * 1 = a)
#check (one_mul : ∀ a : R, 1 * a = a)
#check (mul_add : ∀ a b c : R, a * (b + c) = a * b + a * c)
#check (add_mul : ∀ a b c : R, (a + b) * c = a * c + b * c)

end

section
variable (R : Type*) [CommRing R]
variable (a b c d : R)

example : c * b * a = b * (a * c) := by ring

example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b := by ring

example : (a + b) * (a - b) = a ^ 2 - b ^ 2 := by ring

example (hyp : c = d * a + b) (hyp' : b = a * d) : c = 2 * a * d := by
  rw [hyp, hyp']
  ring

end

namespace MyRing
variable {R : Type*} [Ring R]

theorem add_zero (a : R) : a + 0 = a := by rw [add_comm, zero_add]

theorem add_neg_cancel (a : R) : a + -a = 0 := by rw [add_comm, neg_add_cancel]

#check MyRing.add_zero
#check add_zero

end MyRing

namespace MyRing
variable {R : Type*} [Ring R]

theorem neg_add_cancel_left (a b : R) : -a + (a + b) = b := by
  rw [← add_assoc, neg_add_cancel, zero_add]

-- Prove these:
theorem add_neg_cancel_right (a b : R) : a + b + -b = a := by
  rw [add_assoc]
  rw [add_neg_cancel]
  rw [add_zero]

theorem add_left_cancel {a b c : R} (h : a + b = a + c) : b = c := by
  have hyp : -a + a + b = -a + a + c := by
    rw [add_assoc, h, ← add_assoc]
  rw [add_assoc] at hyp
  rw [add_assoc] at hyp
  rw [neg_add_cancel_left] at hyp
  rw [neg_add_cancel_left] at hyp
  exact hyp

theorem add_right_cancel {a b c : R} (h : a + b = c + b) : a = c := by
  have hyp : a + b + -b = c + b + -b := by rw [h]
  rw [add_neg_cancel_right] at hyp
  rw [add_neg_cancel_right] at hyp
  exact hyp

theorem mul_zero (a : R) : a * 0 = 0 := by
  have h : a * 0 + a * 0 = a * 0 + 0 := by
    rw [← mul_add, add_zero, add_zero]
  rw [add_left_cancel h]

theorem zero_mul (a : R) : 0 * a = 0 := by
  have h : 0 * a + 0 * a = 0 * a + 0 := by
    rw [← add_mul, add_zero, add_zero]
  rw [add_left_cancel h]

theorem neg_eq_of_add_eq_zero {a b : R} (h : a + b = 0) : -a = b := by
  have hyp : -a + a + b = -a := by rw [add_assoc, h, add_zero]
  rw [add_assoc, neg_add_cancel_left] at hyp
  rw [hyp]

theorem eq_neg_of_add_eq_zero {a b : R} (h : a + b = 0) : a = -b := by
  rw [add_comm] at h
  have hyp : -b = a := by exact neg_eq_of_add_eq_zero h
  rw [hyp]

theorem neg_zero : (-0 : R) = 0 := by
  apply neg_eq_of_add_eq_zero
  rw [add_zero]

theorem neg_neg (a : R) : - -a = a := by
  have h : a + -a = 0 := add_neg_cancel a
  have hyp : a = - -a := eq_neg_of_add_eq_zero h
  exact hyp.symm


end MyRing

-- Examples.
section
variable {R : Type*} [Ring R]

example (a b : R) : a - b = a + -b :=
  sub_eq_add_neg a b

end

example (a b : ℝ) : a - b = a + -b :=
  rfl

example (a b : ℝ) : a - b = a + -b := by
  rfl

namespace MyRing
variable {R : Type*} [Ring R]

theorem self_sub (a : R) : a - a = 0 := by
  rw [sub_eq_add_neg a]
  rw [add_neg_cancel]

theorem one_add_one_eq_two : 1 + 1 = (2 : R) := by
  norm_num

theorem two_mul (a : R) : 2 * a = a + a := by
  rw [← one_add_one_eq_two]
  rw [add_mul]
  rw [one_mul]

end MyRing

section
variable (A : Type*) [AddGroup A]

#check (add_assoc : ∀ a b c : A, a + b + c = a + (b + c))
#check (zero_add : ∀ a : A, 0 + a = a)
#check (neg_add_cancel : ∀ a : A, -a + a = 0)

end

#print Group

section
variable {G : Type*} [Group G]

#check (mul_assoc : ∀ a b c : G, a * b * c = a * (b * c))
#check (one_mul : ∀ a : G, 1 * a = a)
#check (inv_mul_cancel : ∀ a : G, a⁻¹ * a = 1)

namespace MyGroup

theorem mul_inv_cancel (a : G) : a * a⁻¹ = 1 := by
  -- (*) 初始事实
  have h1 : a⁻¹⁻¹ * a⁻¹ = 1 := inv_mul_cancel a⁻¹
  -- 两边同时右乘 a
  have h2 : a⁻¹⁻¹ * a⁻¹ * a = 1 * a := by rw [h1]
  -- 化简 h2：左端用结合律 + inv_mul_cancel，右端用 one_mul
  rw [mul_assoc, inv_mul_cancel, one_mul] at h2
  -- 此时 h2 : a⁻¹⁻¹ * 1 = a
  -- 两边再同时右乘 a⁻¹
  have h3 : a⁻¹⁻¹ * 1 * a⁻¹ = a * a⁻¹ := by rw [h2]
  -- 化简 h3 的左端：结合律 → one_mul → inv_mul_cancel
  rw [mul_assoc, one_mul, inv_mul_cancel] at h3
  -- 此时 h3 : 1 = a * a⁻¹
  exact h3.symm

theorem mul_one (a : G) : a * 1 = a := by
  -- 把 1 换成 a⁻¹ * a
  rw [← inv_mul_cancel a]
  -- 目标: a * (a⁻¹ * a) = a
  -- 左边两个重新结合
  rw [← mul_assoc]
  -- 目标: a * a⁻¹ * a = a
  -- 用刚证的 mul_inv_cancel 把 a * a⁻¹ 变 1
  rw [mul_inv_cancel]
  -- 目标: 1 * a = a
  rw [one_mul]

-- 右逆唯一性：若 x * y = 1，则 y = x⁻¹
theorem inv_unique {x y : G} (h : x * y = 1) : y = x⁻¹ := by
  calc y = 1 * y             := by rw [one_mul]
    _ = x⁻¹ * x * y          := by rw [← inv_mul_cancel x]
    _ = x⁻¹ * (x * y)        := by rw [mul_assoc]
    _ = x⁻¹ * 1              := by rw [h]
    _ = x⁻¹                  := by rw [mul_one]

theorem mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹ := by
  -- 先算出 (a*b) * (b⁻¹*a⁻¹) = 1
  have h : (a * b) * (b⁻¹ * a⁻¹) = 1 := by
    rw [mul_assoc, ← mul_assoc b b⁻¹ a⁻¹, mul_inv_cancel, one_mul, mul_inv_cancel]
  -- 套用唯一性: b⁻¹*a⁻¹ 就是 (a*b) 的逆
  exact (inv_unique h).symm

end MyGroup

end
