/-
Copyright  2026  Pieter Collins
Released under the GNU GPLv3 as described in the file LICENSE.
Authors: Pieter Collins
-/

import Init.Data.Int
import Init.Data.Rat
import Init.Data.Int.Order


def Int.abs (z : Int) : Int := Int.natAbs z

theorem Int.nat_abs_of_nat : forall n : Nat, Int.natAbs (Int.ofNat n) = n := by
  grind

theorem Int.abs_of_nonneg : forall z : Int, 0 ≤ z → abs z = z := by
  intro z Hz; cases z
  . case ofNat n => rfl
  . case negSucc m => contradiction

theorem Int.abs_of_nonpos : forall z : Int, z ≤ 0 → abs z = Int.neg z := by
  intro z Hz; cases z
  . case ofNat n => simp at Hz; rw [Hz]; rfl
  . case negSucc m => rfl

theorem Int.natAbs_of_nonpos : forall {a}, a ≤ 0 → Int.abs a = Int.neg a := by
  intro n Hnle0; unfold Int.neg Int.abs; cases n
  . case ofNat n => simp at Hnle0; rw [Hnle0]; unfold negOfNat; rfl
  . case negSucc m => rfl

theorem Int.abs_pos : forall n : Int, 0 ≤ abs n := by
  intro n; unfold abs; grind

theorem Int.abs_odd : forall n : Int, n % 2 = 1 → n.abs % 2 = 1 := by
  intro n Hn;
  cases n
  . case ofNat n => unfold abs; simp; exact Hn
  . case negSucc m => unfold abs; simp; grind


def Int.dist (z1 z2 : Int) := (z1-z2).natAbs

private theorem Int.sub_add_assoc : forall z1 z2 z3 : Int, (z1-z2)+z3 = z1-(z2-z3) := by
  intro z1 z2 z3
  rw [← @Int.add_neg_eq_sub z1 z2]
  rw [Int.add_assoc z1 (-z2) z3]
  rw [←Int.sub_neg z1 (-z2+z3)]
  rw [@Int.neg_add (-z2) z3]
  rw [Int.neg_neg z2]
  rw [@Int.add_neg_eq_sub z2 z3]

private theorem Int.sub_add_sub_cancel : forall z1 z2 z3 : Int, (z1-z2) + (z2-z3) = (z1-z3) := by
  intro z1 z2 z3
  rw [Int.sub_add_assoc z1 z2 (z2-z3)]
  rw [← Int.sub_add_assoc z2 z2 z3]
  rw [Int.sub_self z2]
  rw [Int.zero_add z3]


theorem Int.dist.eq : forall z1 z2, dist z1 z2 = 0 → z1 = z2 := by
  unfold dist; intros z1 z2 Hz
  suffices z1subz2 : z1-z2 = 0 by
    exact Int.eq_of_sub_eq_zero z1subz2
  exact (@Int.natAbs_eq_zero (z1-z2)).mp Hz

theorem Int.dist.refl : forall z, dist z z = 0 := by
  intros z; unfold dist
  rw [Int.sub_self z]
  rfl

theorem Int.dist.symm : forall z1 z2, dist z1 z2 = dist z2 z1 := by
  intros z1 z2; unfold dist
  rw [← @Int.neg_sub z1 z2]
  rw [natAbs_neg (z1-z2)]

theorem Int.dist.trans : forall z1 z2 z3, dist z1 z3 ≤ dist z1 z2 + dist z2 z3 := by
  intros z1 z2 z3; unfold dist
  suffices sum : z1 - z3 = (z1 - z2) + (z2 - z3) by
    rw [sum]
    exact natAbs_add_le (z1-z2) (z2-z3)
  apply Eq.symm
  exact Int.sub_add_sub_cancel z1 z2 z3
