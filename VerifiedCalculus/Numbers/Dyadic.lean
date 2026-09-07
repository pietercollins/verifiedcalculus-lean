/-
Copyright  2026  Pieter Collins
Released under the GNU GPLv3 as described in the file LICENSE.
Authors: Pieter Collins
-/

import Mathlib.Tactic.Linter.Style

import VerifiedCalculus.Numbers.Integer

import Init.Data.Dyadic
import Init.Data.Rat
import Init.Data.Dyadic.Instances

import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Field.Rat
import Mathlib.Algebra.Order.Group.Abs

set_option linter.style.header false


namespace Dyadic

def mk (m : Int) (e : Int) : Dyadic := Dyadic.shiftLeft (ofInt m) e
def two_exp (e : Int) : Dyadic := Dyadic.shiftLeft (1 : Dyadic) e

end Dyadic

private def Dyadic.inv (w : Dyadic) := w.toRat.inv
private def Dyadic.div (w1 w2 : Dyadic) := w1.toRat / w2.toRat

instance Dyadic.instHDiv : HDiv Dyadic Dyadic Rat where hDiv := Dyadic.div
instance Dyadic.instMax : Max Dyadic := maxOfLe
instance Dyadic.instMin : Min Dyadic := minOfLe


protected def Dyadic.max (w1 w2 : Dyadic) : Dyadic :=
  if w1 ≤ w2 then w2 else w1

protected def Dyadic.min (w1 w2 : Dyadic) : Dyadic :=
  if w1 ≤ w2 then w1 else w2

protected def Dyadic.abs (a : Dyadic) : Dyadic :=
  if 0 ≤ a then a else -a

protected def Dyadic.abs' (w : Dyadic) : Dyadic :=
  match w with
  | zero => zero
  | Dyadic.ofOdd m e p =>
      have q : m.abs % 2 = 1 := by unfold Int.abs; grind
      Dyadic.ofOdd m.abs e q


private theorem Dyadic.sup_le' : forall {w1 w2 w3 : Dyadic},
    w1 ≤ w3 → w2 ≤ w3 → (Dyadic.max w1 w2) ≤ w3 := by
  intros w1 w2 w3 Hw13 Hw23; unfold Dyadic.max
  rcases Dyadic.instDecidableLE w1 w2 with Hf | Ht
  · rw [if_neg Hf]; exact Hw13
  · rw [if_pos Ht]; exact Hw23

private theorem Dyadic.le_sup_left' : forall w1 w2 : Dyadic, w1 ≤ Dyadic.max w1 w2 := by
  intros w1 w2; unfold Dyadic.max
  rcases Dyadic.instDecidableLE w1 w2 with Hf | Ht
  · rw [if_neg Hf]; exact Dyadic.le_refl w1
  · rw [if_pos Ht]; exact le_of_eq_of_le rfl Ht

private theorem Dyadic.le_sup_right' : forall w1 w2 : Dyadic, w2 ≤ Dyadic.max w1 w2 := by
  intros w1 w2; unfold Dyadic.max
  rcases Dyadic.instDecidableLE w1 w2 with Hf | Ht
  · rw [if_neg Hf]; exact Std.le_of_not_ge Hf
  · rw [if_pos Ht]; exact Dyadic.le_refl w2


theorem Dyadic.sup_le : ∀ {a b c : Dyadic}, a ≤ c → b ≤ c → a ⊔ b ≤ c := by
  intros a b c Hac Hbc
  unfold Max.max instMax maxOfLe; simp_all only
  split
  · assumption
  · assumption

theorem Dyadic.le_sup_left : ∀ (a b : Dyadic), a ≤ a ⊔ b := by
  intros a b
  unfold Max.max instMax maxOfLe; simp_all only
  split
  · assumption
  · exact Dyadic.le_refl a

theorem Dyadic.le_sup_right : ∀ (a b : Dyadic), b ≤ a ⊔ b := by
  intros a b
  unfold Max.max instMax maxOfLe; simp_all only
  split
  · exact Dyadic.le_refl b
  · apply Std.le_of_not_ge; assumption

theorem Dyadic.le_inf : ∀ {a b c : Dyadic}, a ≤ b → a ≤ c → a ≤ b ⊓ c := by
  intros a b c Hab Hac
  unfold Min.min instMin minOfLe; simp_all only
  split
  · assumption
  · assumption

instance : Lattice Dyadic where
  le_refl := @Dyadic.le_refl
  le_trans := @Dyadic.le_trans
  le_antisymm := @Dyadic.le_antisymm
  lt_iff_le_not_ge := Std.LawfulOrderLT.lt_iff
  sup := fun a b => a ⊔ b
  sup_le := @Dyadic.sup_le
  le_sup_left := Dyadic.le_sup_left
  le_sup_right := Dyadic.le_sup_right
  inf := fun a b => a ⊓ b
  inf_le_left := fun _ _ ↦ Std.min_le_left
  inf_le_right := fun _ _ ↦ Std.min_le_right
  le_inf := @Dyadic.le_inf


private theorem Dyadic.neg_op (w : Dyadic) : -w = Dyadic.neg w := by rfl
private theorem Dyadic.add_op (w1 w2 : Dyadic) : w1+w2 = Dyadic.add w1 w2 := by rfl
private theorem Dyadic.sub_op (w1 w2 : Dyadic) : w1-w2 = Dyadic.sub w1 w2 := by rfl
private theorem Dyadic.mul_op (w1 w2 : Dyadic) : w1*w2 = Dyadic.mul w1 w2 := by rfl
private theorem Dyadic.le_op (w1 w2 : Dyadic) : (w1 ≤ w2) = (Dyadic.ble w1 w2 = true) := by rfl
private theorem Dyadic.lt_op (w1 w2 : Dyadic) : (w1 < w2) = (Dyadic.blt w1 w2 = true) := by rfl


private theorem Dyadic.pos_int {n : Int} {k} {ho} : zero ≤ ofOdd n k ho ↔ 0 ≤ n := by
  rw [@Dyadic.le_op zero (ofOdd n k ho)]; unfold ble; simp

private theorem Dyadic.neg_int {n : Int} {k} {ho} : ofOdd n k ho ≤ zero ↔ n ≤ 0 := by
  rw [@Dyadic.le_op (ofOdd n k ho) zero]; unfold ble; simp

theorem Dyadic.add_le_add_left : forall w1 w2 w3 : Dyadic,
  w3 + w1 ≤ w3 + w2 ↔ w1 ≤ w2 := by grind

theorem Dyadic.add_le_add_left' : forall w1 w2 w3 : Dyadic,
  w3 + w1 ≤ w3 + w2 ↔ w1 ≤ w2 := by
  intro w1 w2 w3
  apply Iff.intro
  · intro Hw123
    have H : (w3+w1).toRat ≤ (w3+w2).toRat := toRat_le_toRat_iff.mpr Hw123
    have H' : w3.toRat+w1.toRat ≤ w3.toRat+w2.toRat := by
      rw [←Dyadic.toRat_add]; rw [←Dyadic.toRat_add]
      exact H
    have H'' : w1.toRat ≤ w2.toRat := Rat.add_le_add_left.mp H'
    exact Dyadic.toRat_le_toRat_iff.mp H''
  · intro Hw12
    have H := Dyadic.toRat_le_toRat_iff.mpr Hw12
    have H' : w3.toRat+w1.toRat ≤ w3.toRat+w2.toRat := Rat.add_le_add_left.mpr H
    rw [←Dyadic.toRat_add] at H'
    rw [←Dyadic.toRat_add] at H'
    exact Dyadic.toRat_le_toRat_iff.mp H'

theorem Dyadic.add_le_add_right : forall w1 w2 w3 : Dyadic,
  w1 + w3 ≤ w2 + w3 ↔ w1 ≤ w2 := by grind

theorem Dyadic.neg_neg : forall w : Dyadic,
  - (-w) = w := by grind
theorem Dyadic.neg_add : forall w1 w2 : Dyadic,
  - (w1 + w2) = -w1 + -w2 := by grind
theorem Dyadic.neg_nonpos_iff : forall {w : Dyadic},
  -w ≤ 0 ↔ 0 ≤ w := by grind
theorem Dyadic.neg_nonneg : forall {w : Dyadic},
  0 ≤ -w ↔ w ≤ 0 := by grind
theorem Dyadic.pos_neg_le : forall {w : Dyadic},
  0 ≤ w ↔ -w ≤ w := by grind
theorem Dyadic.neg_le_neg : forall {w : Dyadic},
  w ≤ 0 ↔ w ≤ -w := by grind


theorem Dyadic.zero_le_toRat_iff : forall {w : Dyadic}, 0 ≤ w ↔ 0 ≤ w.toRat := by
  intros w
  rewrite [← toRat_zero]
  exact Iff.symm toRat_le_toRat_iff


theorem Dyadic.mul_neg (x y : Dyadic) : x * -y = -(x * y) := by
  rw [mul_comm, neg_mul, mul_comm y x]

theorem Dyadic.neg_mul_neg (x y : Dyadic) : -x * -y = x * y := by
  rw [mul_neg, neg_mul, neg_neg]

theorem Dyadic.mul_nonneg : forall {w1 w2 : Dyadic}, 0 ≤ w1 → 0 ≤ w2 → 0 ≤ w1 * w2 := by
  intros w1 w2 Hw1 Hw2
  let q1 := w1.toRat
  let q2 := w2.toRat
  have Hq1 : 0 ≤ q1 := by exact zero_le_toRat_iff.mp Hw1
  have Hq2 : 0 ≤ q2 := by exact zero_le_toRat_iff.mp Hw2
  have Hq12 : 0 ≤ q1 * q2 := by exact Rat.mul_nonneg Hq1 Hq2
  have Hwq : (w1 * w2).toRat = q1 * q2 := by exact toRat_mul w1 w2
  rw [← Hwq] at Hq12
  exact zero_le_toRat_iff.mpr Hq12

theorem Dyadic.mul_nonneg_nonpos : forall {w1 w2 : Dyadic}, 0 ≤ w1 → w2 ≤ 0 → w1 * w2 ≤ 0 := by
  intros w1 w2 Hw1 Hw2
  have Hw1n2 : 0 ≤ w1 * -w2 := mul_nonneg Hw1 (neg_nonneg.mpr Hw2)
  rw [mul_neg w1 w2] at Hw1n2
  exact neg_nonneg.mp Hw1n2

theorem Dyadic.mul_nonpos_nonneg : forall {w1 w2 : Dyadic}, w1 ≤ 0 → 0 ≤ w2 → w1 * w2 ≤ 0 := by
  intros w1 w2 Hw1 Hw2
  have Hnw12 : 0 ≤ -w1 * w2 := mul_nonneg (neg_nonneg.mpr Hw1) Hw2
  rw [neg_mul w1 w2] at Hnw12
  exact neg_nonneg.mp Hnw12

theorem Dyadic.mul_nonpos : forall {w1 w2 : Dyadic}, w1 ≤ 0 → w2 ≤ 0 → 0 ≤ w1 * w2 := by
  intros w1 w2 Hw1 Hw2
  have Hw12 : 0 ≤ -w1 * -w2 := mul_nonneg (neg_nonneg.mpr Hw1) (neg_nonneg.mpr Hw2)
  rw [neg_mul_neg w1 w2] at Hw12
  exact Hw12

def Dyadic.nsmul (n : ℕ) (w : Dyadic) : Dyadic :=
  match n with | Nat.zero => Dyadic.zero | Nat.succ m => Dyadic.nsmul m w + w
def Dyadic.zsmul (n : ℤ) (w : Dyadic) : Dyadic :=
  match n with | Int.ofNat m => nsmul m w | Int.negSucc m => - (nsmul (m.succ) w)

instance : AddGroup Dyadic where
  add_assoc := Dyadic.add_assoc
  zero_add := Dyadic.zero_add
  add_zero := Dyadic.add_zero
  nsmul := Dyadic.nsmul
  zsmul := Dyadic.zsmul
  neg_add_cancel := Dyadic.neg_add_cancel


theorem Dyadic.max_op (w1 w2 : Dyadic) : Dyadic.max w1 w2 = w1 ⊔ w2 := by
  unfold Dyadic.max
  rcases Dyadic.instDecidableLE w1 w2 with Hnw1lew2 | Hw1lew2
  · have Hw2lew1 : w2 ≤ w1 := by exact Std.le_of_not_ge Hnw1lew2
    rw [if_neg Hnw1lew2]
    exact left_eq_sup.mpr Hw2lew1
  · rw [if_pos Hw1lew2]
    exact right_eq_sup.mpr Hw1lew2

theorem Dyadic.min_op (w1 w2 : Dyadic) : Dyadic.min w1 w2 = w1 ⊓ w2 := by
  unfold Dyadic.min
  rcases Dyadic.instDecidableLE w1 w2 with Hnw1lew2 | Hw1lew2
  · have Hw2lew1 : w2 ≤ w1 := by exact Std.le_of_not_ge Hnw1lew2
    rw [if_neg Hnw1lew2]
    exact right_eq_inf.mpr Hw2lew1
  · rw [if_pos Hw1lew2]
    exact left_eq_inf.mpr Hw1lew2

theorem Dyadic.abs_of_nonneg : forall {w : Dyadic}, 0 ≤ w → |w| = w := by
  intros w H0lew
  unfold abs
  refine sup_eq_left.mpr ?_
  transitivity 0
  · exact neg_nonpos_iff.mpr H0lew
  · exact le_of_eq_of_le rfl H0lew

theorem Dyadic.abs_of_nonpos : forall {w : Dyadic}, w ≤ 0 → |w| = -w := by
  intros w Hwle0
  unfold abs
  refine sup_eq_right.mpr ?_
  transitivity 0
  · exact Dyadic.le_trans Hwle0 rfl
  · exact neg_nonneg.mpr Hwle0


theorem Dyadic.abs_op (w : Dyadic) : Dyadic.abs w = abs w := by
  unfold Dyadic.abs
  rcases Dyadic.instDecidableLE 0 w with Hn0lew | H0lew
  · have Hwle0 : w ≤ 0 := by exact Std.le_of_not_ge Hn0lew
    rw [if_neg Hn0lew]
    rw [abs_of_nonpos Hwle0]
  · rw [if_pos H0lew]
    rw [abs_of_nonneg H0lew]



theorem Dyadic.abs_sgn : forall w : Dyadic, if 0 ≤ w then |w| = w else |w| = -w := by
  intro w
  rcases Dyadic.instDecidableLE 0 w with Hn0lew | H0lew
  · have Hwle0 : w ≤ 0 := by exact Std.le_of_not_ge Hn0lew
    rw [if_neg Hn0lew]
    exact abs_of_nonpos Hwle0
  · rw [if_pos H0lew]
    exact abs_of_nonneg H0lew

theorem Dyadic.le_abs : forall w : Dyadic, w ≤ |w| := by
  intro w
  rcases Dyadic.instDecidableLE 0 w with Hn0lew | H0lew
  · have Hwle0 : w ≤ 0 := by exact Std.le_of_not_ge Hn0lew
    rw [abs_of_nonpos Hwle0]
    exact neg_le_neg.mp Hwle0
  · rw [abs_of_nonneg H0lew]

theorem Dyadic.neg_le_abs : forall w : Dyadic, -w ≤ |w| := by
  intro w
  rcases Dyadic.instDecidableLE 0 w with Hn0lew | H0lew
  · have Hwle0 : w ≤ 0 := by exact Std.le_of_not_ge Hn0lew
    rw [abs_of_nonpos Hwle0]
  · rw [abs_of_nonneg H0lew];
    exact pos_neg_le.mp H0lew

theorem Dyadic.abs_eq_zero : forall w : Dyadic, |w| = 0 → w = 0 := by
  intro w
  rcases Dyadic.instDecidableLE 0 w with Hn0lew | H0lew
  · have Hwle0 : w ≤ 0 := by exact Std.le_of_not_ge Hn0lew
    rw [abs_of_nonpos Hwle0]
    intro Hnegweq0
    exact neg_eq_zero.mp Hnegweq0
  · rw [abs_of_nonneg H0lew]; intro; trivial

theorem Dyadic.abs_zero : |(0:Dyadic)| = 0 := by
  apply abs_of_nonneg; exact neg_nonpos_iff.mp rfl

theorem Dyadic.abs_pos : forall w : Dyadic, 0 ≤ |w| := by
  intro w
  rcases Dyadic.instDecidableLE 0 w with Hn0lew | H0lew
  · have Hwle0 : w ≤ 0 := by exact Std.le_of_not_ge Hn0lew
    rw [abs_of_nonpos Hwle0]
    exact neg_nonneg.mpr Hwle0
  · rw [abs_of_nonneg H0lew]; trivial


theorem Dyadic.abs_add : forall (w1 w2 : Dyadic), |w1 + w2| ≤ |w1| + |w2| := by
  intro w1 w2;
  rcases Dyadic.instDecidableLE 0 (w1+w2) with q12 | p12
  · have p12 : w1 + w2 ≤ 0 := by exact Std.le_of_not_ge q12
    rw [Dyadic.abs_of_nonpos p12]
    rw [Dyadic.neg_add w1 w2]
    refine @Dyadic.le_trans _ (-w1 + |w2|) _ ?_ ?_
    · exact (add_le_add_left (-w2) |w2| (-w1)).mpr (neg_le_abs w2)
    · exact (add_le_add_right (-w1) |w1| |w2|).mpr (neg_le_abs w1)
  · rw [Dyadic.abs_of_nonneg p12]
    refine @Dyadic.le_trans _ (w1 + |w2|) _ ?_ ?_
    · exact (add_le_add_left w2 |w2| w1).mpr (le_abs w2)
    · exact (add_le_add_right w1 |w1| |w2|).mpr (le_abs w1)


theorem Dyadic.abs_mul : forall (w1 w2 : Dyadic), |w1 * w2| = |w1| * |w2| := by
  intro w1 w2;
  rcases Dyadic.instDecidableLE 0 w1 with q1 | p1
  · have p1 : w1 ≤ 0 := by exact Std.le_of_not_ge q1
    rw [Dyadic.abs_of_nonpos p1]
    rcases Dyadic.instDecidableLE 0 w2 with q2 | p2
    · have p2 : w2 ≤ 0 := by exact Std.le_of_not_ge q2
      rw [Dyadic.abs_of_nonpos p2]
      have p12 : 0 ≤ w1 * w2 := by exact mul_nonpos p1 p2
      rw [Dyadic.abs_of_nonneg p12]
      rw [Dyadic.neg_mul]
      rw [Dyadic.mul_neg]
      rw [Dyadic.neg_neg]
    · rw [Dyadic.abs_of_nonneg p2]
      have p12 : w1 * w2 ≤ 0 := by exact mul_nonpos_nonneg p1 p2
      rw [Dyadic.abs_of_nonpos p12]
      rw [Dyadic.neg_mul]
  · rw [Dyadic.abs_of_nonneg p1]
    rcases Dyadic.instDecidableLE 0 w2 with q2 | p2
    · have p2 : w2 ≤ 0 := by exact Std.le_of_not_ge q2
      rw [Dyadic.abs_of_nonpos p2]
      have p12 : w1 * w2 ≤ 0 := by exact mul_nonneg_nonpos p1 p2
      rw [Dyadic.abs_of_nonpos p12]
      rw [Dyadic.mul_neg]
    · rw [Dyadic.abs_of_nonneg p2]
      have p12 : 0 ≤ w1 * w2 := by exact mul_nonneg p1 p2
      rw [Dyadic.abs_of_nonneg p12]




theorem Dyadic.sub_eq_add_neg : forall {a b : Dyadic}, a - b = a + (-b) := by
  intro a b; rfl

theorem Dyadic.left_distrib : forall {a b c : Dyadic},
  a * (b + c) = a * b + a * c :=
by
  intros a b c
  exact mul_add a b c

theorem Dyadic.right_distrib : forall {a b c : Dyadic},
  (a + b) * c = a * c + b * c :=
by
  intros a b c
  exact add_mul a b c

/-
 instance inst_Ring_Dyadic' : Ring Dyadic where
  add_assoc := Dyadic.add_assoc
  zero_add := Dyadic.zero_add
  add_zero := Dyadic.add_zero
  nsmul := Dyadic.nsmul
  add_comm := Dyadic.add_comm
  left_distrib := Dyadic.left_distrib
  right_distrib := Dyadic.right_distrib
  zero_mul := Dyadic.zero_mul
  mul_zero := Dyadic.mul_zero
  mul_assoc := Dyadic.mul_assoc
  one_mul  := Dyadic.one_mul
  mul_one := Dyadic.mul_one
  zsmul := Dyadic.zsmul
  neg_add_cancel := Dyadic.neg_add_cancel
-/

theorem Dyadic.toRat_ofInt_eq_Rat_ofInt {n : Int} :
    (ofInt n).toRat = Rat.ofInt n := by
  unfold ofInt
  unfold Rat.ofInt
  rw [Dyadic.toRat_ofIntWithPrec_eq_mkRat]
  simp only [neg_zero, Int.toNat_zero, Int.shiftLeft_zero, Nat.shiftLeft_zero, Rat.mk_den_one]
  exact Rat.mkRat_one n

theorem Rat.ofInt_add : forall z1 z2 : ℤ, ofInt z1 + ofInt z2 = ofInt (z1 + z2) := by
  intro z1 z2
  rw [Rat.add_def]
  unfold ofInt
  unfold normalize
  simp

theorem Rat.ofInt_neg : forall z : ℤ, - (ofInt z) = ofInt (-z) := by
  intro z
  unfold ofInt
  simp

theorem Dyadic.ofInt_add : forall z1 z2 : ℤ, ofInt z1 + ofInt z2 = ofInt (z1 + z2) := by
  intro z1 z2
  apply Dyadic.toRat_inj.mp
  rw [Dyadic.toRat_add]
  repeat rw [Dyadic.toRat_ofInt_eq_Rat_ofInt]
  apply Rat.ofInt_add

theorem Dyadic.ofInt_neg : forall z : ℤ, - (ofInt z) = ofInt (-z) := by
  intro z
  apply Dyadic.toRat_inj.mp
  rw [Dyadic.toRat_neg]
  repeat rw [Dyadic.toRat_ofInt_eq_Rat_ofInt]
  apply Rat.ofInt_neg


private theorem Dyadic.natCast_succ : ∀ (n : ℕ),
    (@NatCast.natCast Dyadic Dyadic.instNatCast (n + 1) : Dyadic)
      = (@HAdd.hAdd Dyadic Dyadic Dyadic instHAdd (↑n) 1 : Dyadic) := by
    intro n
    unfold NatCast.natCast
    unfold Dyadic.instNatCast
    simp only [Nat.cast_add, Nat.cast_one]
    rw [← Dyadic.ofInt_add]
    rfl


instance inst_Semiring_Dyadic : Semiring Dyadic where
  add_assoc := Dyadic.add_assoc
  zero_add := Dyadic.zero_add
  add_zero := Dyadic.add_zero
  nsmul := Dyadic.nsmul
  add_comm := Dyadic.add_comm
  left_distrib := Dyadic.mul_add
  right_distrib := Dyadic.add_mul
  zero_mul := Dyadic.zero_mul
  mul_zero := Dyadic.mul_zero
  mul_assoc := Dyadic.mul_assoc
  one_mul  := Dyadic.one_mul
  mul_one := Dyadic.mul_one
  natCast_succ := Dyadic.natCast_succ
  npow_zero := Dyadic.pow_zero
  npow_succ := fun n w => Dyadic.pow_succ w n


private theorem Int.negSucc_eq_neg_add_one : forall n, Int.negSucc n = - ((Int.ofNat n) + 1) := by
  intro n; rfl

/-
set_option pp.all true
set_option pp.all false
-/

private theorem Dyadic.max_left : forall w1 w2, w1 ≤ w2 → Dyadic.max w1 w2 = w2 := by
  intros w1 w2 Hw12; unfold Dyadic.max; exact if_pos Hw12

private theorem Dyadic.max_right' : forall w1 w2, ¬ w1 ≤ w2 → Dyadic.max w1 w2 = w1 := by
  intros w1 w2 Hw21; unfold Dyadic.max; exact if_neg Hw21

private theorem Dyadic.max_right : forall w1 w2, w2 ≤ w1 → Dyadic.max w1 w2 = w1 := by
  intros w1 w2 Hw21; unfold Dyadic.max
  rcases Dyadic.instDecidableLE w1 w2 with Hf | Ht
  · exact if_neg Hf
  · rw [if_pos Ht]; exact Dyadic.le_antisymm Hw21 Ht

private theorem Dyadic.inf_le_left : forall w1 w2 : Dyadic, Dyadic.min w1 w2 ≤ w1 := by
  intros w1 w2; unfold Dyadic.min
  rcases Dyadic.instDecidableLE w1 w2 with Hf | Ht
  · rw [if_neg Hf]; exact Std.le_of_not_ge Hf
  · rw [if_pos Ht]

private theorem Dyadic.inf_le_right : forall w1 w2 : Dyadic, Dyadic.min w1 w2 ≤ w2 := by
  intros w1 w2; unfold Dyadic.min
  rcases Dyadic.instDecidableLE w1 w2 with Hf | Ht
  · rw [if_neg Hf]
  · rw [if_pos Ht]; exact le_of_eq_of_le rfl Ht

private theorem Dyadic.le_inf' : forall w1 w2 w3 : Dyadic,
    w1 ≤ w2 → w1 ≤ w3 → w1 ≤ (Dyadic.min w2 w3) := by
  intros w1 w2 w3 Hw12 Hw13; unfold Dyadic.min
  rcases Dyadic.instDecidableLE w2 w3 with Hf | Ht
  · rw [if_neg Hf]; exact Hw13
  · rw [if_pos Ht]; exact Hw12


private theorem Dyadic.zsmul_succ' : ∀ (n : ℕ) (a : Dyadic),
     Dyadic.zsmul (↑n.succ) a = Dyadic.zsmul (↑n) a + a := by
  unfold Dyadic.zsmul
  intro n w
  simp only [Nat.succ_eq_add_one]
  exact toRat_inj.mp rfl

private theorem Dyadic.zsmul_neg' : ∀ (n : ℕ) (a : Dyadic),
    Dyadic.zsmul (Int.negSucc n) a = - Dyadic.zsmul (↑n.succ) a := by
  unfold Dyadic.zsmul
  intro n w
  simp only [Nat.succ_eq_add_one]

private theorem Dyadic.intCast_negSucc : ∀ (n : ℕ),
     (@IntCast.intCast Dyadic Dyadic.instIntCast (Int.negSucc n) : Dyadic)
      = (@Neg.neg Dyadic Dyadic.instNeg ↑(n + 1) : Dyadic) := by
  intro n
  unfold IntCast.intCast
  unfold Dyadic.instIntCast
  simp only [Nat.cast_add, Nat.cast_one]
  rw [Int.negSucc_eq_neg_add_one]
  rw [← Dyadic.ofInt_neg]
  unfold Dyadic.instNeg
  simp only [Int.ofNat_eq_natCast]
  rw [← Dyadic.ofInt_add]
  unfold instHAdd
  simp
  congr


instance instRingDyadic' : Ring Dyadic where
  zsmul := Dyadic.zsmul
  neg_add_cancel := Dyadic.neg_add_cancel
  zsmul_succ' := Dyadic.zsmul_succ'
  zsmul_neg' := Dyadic.zsmul_neg'
  intCast_negSucc := Dyadic.intCast_negSucc




instance instPreorderDyadic : Preorder Dyadic where
  le_refl := Dyadic.le_refl
  le_trans := @Dyadic.le_trans
  lt_iff_le_not_ge := fun w1 w2 ↦ Std.LawfulOrderLT.lt_iff w1 w2

instance inst_PartialOrder_Dyadic : PartialOrder Dyadic where
  le_antisymm := @Dyadic.le_antisymm


instance instLatticeDyadic : Lattice Dyadic where
  sup := Dyadic.max
  le_sup_left := Dyadic.le_sup_left
  le_sup_right := Dyadic.le_sup_right
  sup_le := @Dyadic.sup_le
  inf := Dyadic.min
  inf_le_left := Dyadic.inf_le_left
  inf_le_right := Dyadic.inf_le_right
  le_inf := @Dyadic.le_inf

/-
instance instAbsDyadic : AbsoluteValue Dyadic Dyadic where
  toFun := Dyadic.abs
  map_mul' := Dyadic.abs_mul
  nonneg' := Dyadic.abs_pos
  eq_zero' := Dyadic.abs_eq_zero
  add_le' := Dyadic.abs_add
-/

def Dyadic.dist (w1 w2 : Dyadic) : Dyadic := abs (w1-w2)


namespace Dyadic

theorem toRat_add' (x y : Dyadic) : toRat (x + y) = toRat x + toRat y := by
  match x, y with
  | .zero, _ => simp [toRat]
  | _, .zero => simp [toRat]
  | .ofOdd n₁ k₁ hn₁, .ofOdd n₂ k₂ hn₂ =>
    change (Dyadic.add _ _).toRat = _
    rw [Dyadic.add, toRat_ofOdd_eq_mkRat, toRat_ofOdd_eq_mkRat]
    rw [Rat.mkRat_add_mkRat _ _ (NeZero.ne _) (NeZero.ne _)]
    split
    · rename_i h
      cases Int.sub_eq_zero.mp h
      rw [toRat_ofIntWithPrec_eq_mkRat, Rat.mkRat_eq_iff (NeZero.ne _) (NeZero.ne _)]
      simp [Int.shiftLeft_mul_shiftLeft, Int.add_shiftLeft, Int.add_mul, Nat.add_assoc]
    · rename_i h
      cases Int.sub_eq_iff_eq_add.mp h
      rw [toRat_ofOdd_eq_mkRat, Rat.mkRat_eq_iff (NeZero.ne _) (NeZero.ne _)]
      simp only [Nat.succ_eq_add_one, Int.ofNat_eq_natCast, Int.add_shiftLeft, ← Int.shiftLeft_add,
        Int.natCast_mul, Int.natCast_shiftLeft, Int.shiftLeft_mul_shiftLeft, Int.add_mul]
      congr 2 <;> omega
    · rename_i h
      cases Int.sub_eq_iff_eq_add.mp h
      rw [toRat_ofOdd_eq_mkRat, Rat.mkRat_eq_iff (NeZero.ne _) (NeZero.ne _)]
      simp only [Int.add_shiftLeft, ← Int.shiftLeft_add, Int.natCast_mul, Int.natCast_shiftLeft,
        Int.cast_ofNat_Int, Int.shiftLeft_mul_shiftLeft, Int.mul_one, Int.add_mul]
      congr 2 <;> omega

theorem toRat_add'' (x y : Dyadic) : toRat (x + y) = toRat x + toRat y := by
  match x, y with
  | .zero, _ => simp [toRat]
  | _, .zero => simp [toRat]
  | .ofOdd n₁ k₁ hn₁, .ofOdd n₂ k₂ hn₂ =>
    change (Dyadic.add _ _).toRat = _
    rw [Dyadic.add]
    rw [toRat_ofOdd_eq_mkRat, toRat_ofOdd_eq_mkRat]
    rw [Rat.mkRat_add_mkRat _ _ (NeZero.ne _) (NeZero.ne _)]
    split
    · rename_i h
      cases Int.sub_eq_zero.mp h
      rw [toRat_ofIntWithPrec_eq_mkRat]
      rw [Rat.mkRat_eq_iff (NeZero.ne _) (NeZero.ne _)]
      simp [Int.shiftLeft_mul_shiftLeft]
      simp [Int.add_shiftLeft]
      simp [Int.add_mul]
      simp [Int.shiftLeft_mul_shiftLeft]
      simp [Nat.add_assoc]
    · rename_i h
      cases Int.sub_eq_iff_eq_add.mp h
      rw [toRat_ofOdd_eq_mkRat, Rat.mkRat_eq_iff (NeZero.ne _) (NeZero.ne _)]
      simp only [Nat.succ_eq_add_one, Int.ofNat_eq_natCast, Int.add_shiftLeft, ← Int.shiftLeft_add,
        Int.natCast_mul, Int.natCast_shiftLeft, Int.shiftLeft_mul_shiftLeft, Int.add_mul]
      congr 2 <;> omega
    · rename_i h
      cases Int.sub_eq_iff_eq_add.mp h
      rw [toRat_ofOdd_eq_mkRat, Rat.mkRat_eq_iff (NeZero.ne _) (NeZero.ne _)]
      simp only [Int.add_shiftLeft, ← Int.shiftLeft_add, Int.natCast_mul, Int.natCast_shiftLeft,
        Int.cast_ofNat_Int, Int.shiftLeft_mul_shiftLeft, Int.mul_one, Int.add_mul]
      congr 2 <;> omega

theorem ble_iff_toRat' : ble x y ↔ x.toRat ≤ y.toRat := by
  rw [← blt_eq_false_iff, Bool.eq_false_iff]
  simp only [ne_eq, blt_iff_toRat, Rat.not_lt]

theorem toRat_le_toRat_iff' {x y : Dyadic} : x.toRat ≤ y.toRat ↔ x ≤ y := ble_iff_toRat.symm


def w1 := Dyadic.mk 3 (-2)
def w2 := Dyadic.mk 7 (-3)

#eval w1.toRat
#eval w2.toRat
#eval (Dyadic.min w1 w2).toRat
#eval  (w1 ⊓ w2).toRat

end Dyadic
