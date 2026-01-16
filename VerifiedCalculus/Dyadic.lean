/-
Copyright  2026  Pieter Collins 
Released under the GNU GPLv3 as described in the file LICENSE.
Authors: Pieter Collins
-/

import Init.Data.Int
import Init.Data.Rat
import Init.Data.Int.Order
import Init.Data.Dyadic

def Int.abs (z : Int) : Int := Int.natAbs z

theorem Int.nat_abs_of_nat : forall n : Nat, Int.natAbs (Int.ofNat n) = n := by
  grind

theorem Int.abs_ge_zero : forall z : Int, 0 ≤ z → abs z = z := by
  intro z Hz; cases z
  . case ofNat n => rfl
  . case negSucc m => contradiction

theorem Int.abs_le_zero : forall z : Int, z ≤ 0 → abs z = Int.neg z := by
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



#check Int.natAbs_of_nonneg
#check Int.natAbs_of_nonpos
#check Int.natAbs_neg
#check Int.natAbs_add_le
#check Int.abs_pos
#check Int.abs_odd

def Int.dist (z1 z2 : Int) := (z1-z2).natAbs

#check Int.add_neg_eq_sub

theorem Int.sub_add_assoc : forall z1 z2 z3 : Int, (z1-z2)+z3 = z1-(z2-z3) := by
  intro z1 z2 z3
  rw [← @Int.add_neg_eq_sub z1 z2]
  rw [Int.add_assoc z1 (-z2) z3]
  rw [←Int.sub_neg z1 (-z2+z3)]
  rw [@Int.neg_add (-z2) z3]
  rw [Int.neg_neg z2]
  rw [@Int.add_neg_eq_sub z2 z3]

theorem Int.sub_add_sub_cancel : forall z1 z2 z3 : Int, (z1-z2) + (z2-z3) = (z1-z3) := by
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


#print Dyadic

def Dyadic.two_exp (e : Int) : Dyadic := Dyadic.shiftLeft (1 : Dyadic) e

/-
Dyadic.ofOdd : (n : Int) → Int → n % 2 = 1 → Dyadic
-/


def Dyadic.abs (w : Dyadic) : Dyadic :=
  match w with
  | zero => zero
  | Dyadic.ofOdd m e p =>
      have q : m.abs % 2 = 1 := by unfold Int.abs; grind
      Dyadic.ofOdd m.abs e q

private theorem Dyadic.neg_op (w : Dyadic) : -w = Dyadic.neg w := by rfl
private theorem Dyadic.add_op (w1 w2 : Dyadic) : w1+w2 = Dyadic.add w1 w2 := by rfl
private theorem Dyadic.le_op (w1 w2 : Dyadic) : (w1 ≤ w2) = (Dyadic.ble w1 w2 = true) := by rfl

private theorem Dyadic.pos_int {n : Int} {k} {ho} : zero ≤ ofOdd n k ho ↔ 0 ≤ n := by
  rw [@Dyadic.le_op zero (ofOdd n k ho)]; unfold ble; simp

private theorem Dyadic.neg_int {n : Int} {k} {ho} : ofOdd n k ho ≤ zero ↔ n ≤ 0 := by
  rw [@Dyadic.le_op (ofOdd n k ho) zero]; unfold ble; simp


theorem Dyadic.abs_pos : forall w, 0 ≤ abs w := by
  intro w;
  unfold abs
  cases w
  . case zero => rfl
  . case ofOdd n k ho =>
    simp
    have hao : (Int.abs n) % 2 = 1 := by exact Int.abs_odd n ho
    have np := (@Dyadic.pos_int (Int.abs n) k hao).mpr
    apply np
    exact Int.abs_pos n

theorem Dyadic.abs_nonneg : forall w : Dyadic, 0 ≤ w → w.abs = w := by
  intro w H0lew
  cases w
  . case zero => unfold abs; simp
  . case ofOdd n e ho =>
    have H0len : 0 ≤ n := by exact Dyadic.pos_int.mp H0lew
    unfold Dyadic.abs; simp
    unfold Int.abs; exact Int.natAbs_of_nonneg H0len

theorem Dyadic.abs_nonpos : forall w : Dyadic, w ≤ 0 → w.abs = w.neg := by
  intro w Hwle0
  cases w
  . case zero => unfold Dyadic.abs; unfold Dyadic.neg; simp
  . case ofOdd n e ho =>
    have Hnle0 : n ≤ 0 := by exact Dyadic.neg_int.mp Hwle0
    unfold Dyadic.abs; unfold Dyadic.neg; simp
    exact Int.natAbs_of_nonpos Hnle0

theorem Dyadic.abs_sgn : forall w : Dyadic, if 0 ≤ w then w.abs = w else w.abs = w.neg := by
  intro w
  unfold ite
  let d := instDecidableLE 0 w
  have eqd : d = instDecidableLE 0 w := by trivial
  cases h : d
  . case isFalse pf =>
    rw [← eqd]; rw [h]; simp
    apply Dyadic.abs_nonpos
    exact Std.le_of_not_ge pf
  . case isTrue pt =>
    rw [← eqd]; rw [h]; simp
    apply Dyadic.abs_nonneg
    exact pt

theorem Dyadic.neg_add : forall w1 w2 : Dyadic,
  - (w1 + w2) = -w1 + -w2 := by grind
theorem Dyadic.add_le_add_left : forall w1 w2 w3 : Dyadic,
  w1 + w2 ≤ w1 + w3 ↔ w2 ≤ w3 := by grind
theorem Dyadic.add_le_add_right : forall w1 w2 w3 : Dyadic,
  w1 + w3 ≤ w2 + w3 ↔ w1 ≤ w2 := by grind
theorem Dyadic.pos_neg_le : forall {w : Dyadic},
  0 ≤ w → -w ≤ w := by grind
theorem Dyadic.neg_le_neg : forall {w : Dyadic},
  w ≤ 0 → w ≤ -w := by grind

theorem Dyadic.neg_add' : forall w1 w2 : Dyadic, (w1 + w2).neg = w1.neg + w2.neg := by
  intro w1 w2; repeat rw [←neg_op]; exact neg_add w1 w2
theorem Dyadic.pos_neg_le' : forall {w : Dyadic}, 0 ≤ w → w.neg ≤ w := by
  intro w; rw [←neg_op]; exact @pos_neg_le w
theorem Dyadic.neg_le_neg' : forall {w : Dyadic}, w ≤ 0 → w ≤ w.neg := by
  intro w; rw [←neg_op]; exact @neg_le_neg w


theorem Dyadic.le_abs : forall w : Dyadic, w ≤ Dyadic.abs w := by
  intro w
  let d := instDecidableLE 0 w
  have eqd : d = instDecidableLE 0 w := by trivial
  cases h : d
  . case isFalse q =>
    have p : w ≤ 0 := by exact Std.le_of_not_ge q
    rw [abs_nonpos _ p]
    rw [← neg_op]
    grind
  . case isTrue p =>
    rw [abs_nonneg _ p]
    exact Dyadic.le_refl w

theorem Dyadic.neg_le_abs : forall w : Dyadic, Dyadic.neg w ≤ Dyadic.abs w := by
  intro w
  let d := instDecidableLE 0 w
  have eqd : d = instDecidableLE 0 w := by trivial
  cases h : d
  . case isFalse q =>
    have p : w ≤ 0 := by exact Std.le_of_not_ge q
    rw [abs_nonpos _ p]
    exact Dyadic.le_refl w.neg
  . case isTrue p =>
    rw [abs_nonneg _ p]
    rw [← neg_op]
    grind


theorem Dyadic.abs_add : forall w1 w2, abs (w1 + w2) ≤ abs w1 + abs w2 := by
  intro w1 w2;
  let d12 := instDecidableLE 0 (w1+w2)
  have eqd12 : d12 = instDecidableLE 0 (w1+w2) := by trivial
  cases h12 : d12
  . case isFalse q12 =>
    have p12 : w1 + w2 ≤ 0 := by exact Std.le_of_not_ge q12
    rw [abs_nonpos _ p12]; rw [Dyadic.neg_add' w1 w2]
    refine @Dyadic.le_trans _ (w1.neg + w2.abs) _ ?_ ?_
    exact (add_le_add_left w1.neg w2.neg w2.abs).mpr (neg_le_abs w2)
    exact (add_le_add_right w1.neg w1.abs w2.abs).mpr (neg_le_abs w1)
  . case isTrue p12 =>
    rw [abs_nonneg _ p12]
    refine @Dyadic.le_trans _ (w1 + w2.abs) _ ?_ ?_
    exact (add_le_add_left w1 w2 w2.abs).mpr (le_abs w2)
    exact (add_le_add_right w1 w1.abs w2.abs).mpr (le_abs w1)


def Dyadic.dist (w1 w2 : Dyadic) : Dyadic := abs (w1-w2)

def two_exp_neg_three : Dyadic := Dyadic.two_exp (-3 : Int)
def two_exp_neg_three_rat : Rat := two_exp_neg_three.toRat
#eval two_exp_neg_three_rat

#eval (two_exp_neg_three ≤ two_exp_neg_three)
