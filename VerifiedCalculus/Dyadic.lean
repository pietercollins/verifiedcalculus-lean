/-
Copyright  2026  Pieter Collins
Released under the GNU GPLv3 as described in the file LICENSE.
Authors: Pieter Collins
-/

import VerifiedCalculus.Integer
import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.Algebra.Ring.Defs
import Init.Data.Dyadic

import Mathlib.Algebra.Order.Group.Unbundled.Abs

#print AbsoluteValue
#print Dyadic

namespace Dyadic

def mk (m : Int) (e : Int) : Dyadic := Dyadic.shiftLeft (ofInt m) e
def two_exp (e : Int) : Dyadic := Dyadic.shiftLeft (1 : Dyadic) e

end Dyadic

#print Dyadic
#print Dyadic.mk

private def negative_seven_fourths := Dyadic.mk (-14) (-3)
#eval negative_seven_fourths
/- #eval |negative_seven_fourths| -/


#print Dyadic.instMul
#print instHMul
#check @instHMul Dyadic Dyadic.instMul


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

theorem Dyadic.add_le_add_left : forall {w1 w2 w3 : Dyadic},
  w3 + w1 ≤ w3 + w2 ↔ w1 ≤ w2 := by grind

private theorem Dyadic.add_le_add_left' : forall {w1 w2 w3 : Dyadic},
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

theorem Dyadic.add_le_add_right : forall {w1 w2 w3 : Dyadic},
  w1 + w3 ≤ w2 + w3 ↔ w1 ≤ w2 := by grind

theorem Dyadic.neg_le : forall {w1 w2 : Dyadic},
    w1 ≤ w2 ↔ -w2 ≤ -w1 := by grind

theorem Dyadic.neg_le_zero : forall {w : Dyadic},
    0 ≤ w ↔ -w ≤ 0 := by grind
theorem Dyadic.zero_le_neg : forall {w : Dyadic},
    w ≤ 0 ↔ 0 ≤ -w := by grind

theorem Dyadic.mul_neg (x y : Dyadic) : x * -y = -(x * y) := by
  rw [mul_comm, neg_mul, mul_comm y x]

theorem Dyadic.mul_nonneg : forall {w1 w2 : Dyadic},
    0 ≤ w1 → 0 ≤ w2 → 0 ≤ w1 * w2 := by
  intro w1 w2 Hw1 Hw2
  let w0 := (0 : Dyadic)
  have H0 : (w0.toRat) = (0 : Rat) := Dyadic.toRat_zero
  have H1 : (w0.toRat) ≤ (w1).toRat := toRat_le_toRat_iff.mpr Hw1
  have H2 : (w0.toRat) ≤ (w2).toRat := toRat_le_toRat_iff.mpr Hw2
  rw [H0] at H1 H2
  have H12 : 0 ≤ w1.toRat * w2.toRat := Rat.mul_nonneg H1 H2
  rw [←H0] at H12
  rw [←Dyadic.toRat_mul w1 w2] at H12
  exact Dyadic.toRat_le_toRat_iff.mp H12


theorem Dyadic.neg_neg : forall w : Dyadic,
  - (-w) = w := by grind
theorem Dyadic.neg_add : forall w1 w2 : Dyadic,
  - (w1 + w2) = -w1 + -w2 := by grind
theorem Dyadic.pos_neg_le : forall {w : Dyadic},
  0 ≤ w → -w ≤ w := by grind
theorem Dyadic.neg_le_neg : forall {w : Dyadic},
  w ≤ 0 → w ≤ -w := by grind

theorem Dyadic.neg_le' : forall w1 w2 : Dyadic, w1 ≤ w2 ↔ w2.neg ≤ w1.neg := by
  intro w1 w2; repeat rw [←neg_op]; exact @neg_le w1 w2
theorem Dyadic.neg_add' : forall w1 w2 : Dyadic, (w1 + w2).neg = w1.neg + w2.neg := by
  intro w1 w2; repeat rw [←neg_op]; exact @neg_add w1 w2
theorem Dyadic.pos_neg_le' : forall {w : Dyadic}, 0 ≤ w → w.neg ≤ w := by
  intro w; rw [←neg_op]; exact @pos_neg_le w
theorem Dyadic.neg_le_neg' : forall {w : Dyadic}, w ≤ 0 → w ≤ w.neg := by
  intro w; rw [←neg_op]; exact @neg_le_neg w

def Dyadic.max (w1 w2 : Dyadic) : Dyadic :=
  if w1 ≤ w2 then w2 else w1
def Dyadic.min (w1 w2 : Dyadic) : Dyadic :=
  if w1 ≤ w2 then w1 else w2

def Dyadic.hlf (w : Dyadic) : Dyadic :=
  Dyadic.shiftRight w 1

def Dyadic.abs (w : Dyadic) : Dyadic :=
  match w with
  | zero => zero
  | Dyadic.ofOdd m e p =>
      have q : m.abs % 2 = 1 := by unfold Int.abs; grind
      Dyadic.ofOdd m.abs e q

theorem Dyadic.abs_nonneg : forall w : Dyadic, 0 ≤ w → w.abs = w := by
  intro w H0lew
  cases w
  · case zero => unfold abs; simp
  · case ofOdd n e ho =>
    have H0len : 0 ≤ n := by exact Dyadic.pos_int.mp H0lew
    unfold Dyadic.abs; simp only [ofOdd.injEq, and_true]
    unfold Int.abs; exact Int.natAbs_of_nonneg H0len

theorem Dyadic.abs_nonpos' : forall w : Dyadic, w ≤ 0 → w.abs = w.neg := by
  intro w Hwle0
  cases w
  · case zero => unfold Dyadic.abs; unfold Dyadic.neg; simp
  · case ofOdd n e ho =>
    have Hnle0 : n ≤ 0 := by exact Dyadic.neg_int.mp Hwle0
    unfold Dyadic.abs; unfold Dyadic.neg; simp only [ofOdd.injEq, and_true]
    exact Int.natAbs_of_nonpos Hnle0

theorem Dyadic.abs_nonpos : forall w : Dyadic, w ≤ 0 → w.abs = -w := by
  intros w Hw
  suffices w.abs = w.neg by rw [this]; rfl
  exact Dyadic.abs_nonpos' w Hw

theorem Dyadic.le_abs : forall w : Dyadic, w ≤ Dyadic.abs w := by
  intro w
  let d := instDecidableLE 0 w
  have eqd : d = instDecidableLE 0 w := by trivial
  cases h : d
  · case isFalse q =>
    have p : w ≤ 0 := by exact Std.le_of_not_ge q
    rw [abs_nonpos _ p]
    grind
  · case isTrue p =>
    rw [abs_nonneg _ p]
    exact Dyadic.le_refl w

theorem Dyadic.neg_le_abs' : forall w : Dyadic, Dyadic.neg w ≤ Dyadic.abs w := by
  intro w
  let d := instDecidableLE 0 w
  have eqd : d = instDecidableLE 0 w := by trivial
  cases h : d
  · case isFalse q =>
    have p : w ≤ 0 := by exact Std.le_of_not_ge q
    rw [abs_nonpos _ p]
    exact Dyadic.le_refl w.neg
  · case isTrue p =>
    rw [abs_nonneg _ p]
    rw [← neg_op]
    grind

theorem Dyadic.neg_le_abs : forall w : Dyadic, -w ≤ Dyadic.abs w := by
  intros w; rw [neg_op w]; exact neg_le_abs' w

theorem Dyadic.abs_eq_zero : forall w, abs w = (0 : Dyadic) ↔ w = 0 := by
  intro w
  unfold abs
  cases w
  · case zero => simp
  · case ofOdd n k ho => simp

theorem Dyadic.abs_pos : forall w, 0 ≤ Dyadic.abs w := by
  intro w;
  unfold abs
  cases w
  · case zero => rfl
  · case ofOdd n k ho =>
    simp only
    have hao : (Int.abs n) % 2 = 1 := by exact Int.abs_odd n ho
    have np := (@Dyadic.pos_int (Int.abs n) k hao).mpr
    apply np
    exact Int.abs_pos n

theorem Dyadic.abs_add : forall w1 w2, abs (w1 + w2) ≤ abs w1 + abs w2 := by
  intro w1 w2;
  let d12 := instDecidableLE 0 (w1+w2)
  have eqd12 : d12 = instDecidableLE 0 (w1+w2) := by trivial
  cases h12 : d12
  · case isFalse q12 =>
    have p12 : w1 + w2 ≤ 0 := by exact Std.le_of_not_ge q12
    rw [Dyadic.abs_nonpos _ p12]
    rw [Dyadic.neg_add w1 w2]
    refine @Dyadic.le_trans _ (w1.neg + w2.abs) _ ?_ ?_
    · exact (@add_le_add_left w2.neg w2.abs w1.neg).mpr (neg_le_abs w2)
    · exact (@add_le_add_right w1.neg w1.abs w2.abs).mpr (neg_le_abs w1)
  · case isTrue p12 =>
    rw [Dyadic.abs_nonneg _ p12]
    refine @Dyadic.le_trans _ (w1 + w2.abs) _ ?_ ?_
    · exact (@add_le_add_left w2 w2.abs w1).mpr (le_abs w2)
    · exact (@add_le_add_right w1 w1.abs w2.abs).mpr (le_abs w1)

theorem Dyadic.abs_sgn' : forall w : Dyadic, if 0 ≤ w then w.abs = w else w.abs = w.neg := by
  intro w
  unfold ite
  let d := instDecidableLE 0 w
  have eqd : d = instDecidableLE 0 w := by trivial
  cases h : d
  · case isFalse pf =>
    rw [← eqd]; rw [h]; simp only
    apply Dyadic.abs_nonpos
    exact Std.le_of_not_ge pf
  · case isTrue pt =>
    rw [← eqd]; rw [h]; simp only
    apply Dyadic.abs_nonneg
    exact pt

theorem Dyadic.abs_sgn : forall w : Dyadic, if 0 ≤ w then w.abs = w else w.abs = -w := by
  intros w; rw [Dyadic.neg_op w]; exact Dyadic.abs_sgn' w

theorem Dyadic.abs_neg : forall w : Dyadic, abs (-w) = abs w := by
  intro w
  let d := instDecidableLE 0 w
  have eqd : d = instDecidableLE 0 w := by trivial
  have z : -0 = (0 : Dyadic) := by exact Dyadic.neg_zero
  cases h : d
  · case isFalse q =>
    have p : w ≤ 0 := by exact Std.le_of_not_ge q
    have r : -0 ≤ -w := by exact neg_le.mp p
    rw [←z] at r
    rw [Dyadic.abs_nonneg (-w) r,Dyadic.abs_nonpos (w) p]
  · case isTrue p
    have r : -w ≤ -0 := by exact neg_le.mp p
    rw [z] at r
    rw [Dyadic.abs_nonpos (-w) r, Dyadic.abs_nonneg w p]
    exact Dyadic.neg_neg w

theorem Dyadic.abs_mul : forall w1 w2 : Dyadic, abs (w1 * w2) = abs w1 * abs w2 := by
  intros w1 w2
  let d1 := instDecidableLE 0 w1
  have eqd : d1 = instDecidableLE 0 w1 := by trivial
  let d2 := instDecidableLE 0 w2
  have eqd : d2 = instDecidableLE 0 w2 := by trivial
  cases h1 : d1
  · case isFalse q1 =>
    have p1 : w1 ≤ 0 := by exact Std.le_of_not_ge q1
    have r1 : 0 ≤ -w1 := by exact zero_le_neg.mp p1
    rw [abs_nonpos w1 p1]
    cases h2 : d2
    · case isFalse q2 =>
      have p2 : w2 ≤ 0 := by exact Std.le_of_not_ge q2
      have r2 : 0 ≤ -w2 := by exact zero_le_neg.mp p2
      have p12 : 0 ≤ w1*w2 := by
        rw [←Dyadic.neg_neg (w1*w2)]
        rw [←Dyadic.mul_neg w1 w2]
        rw [←Dyadic.neg_mul w1 (-w2)]
        exact Dyadic.mul_nonneg r1 r2
      rw [abs_nonpos w2 p2]
      rw [abs_nonneg (w1*w2) p12]
      rw [Dyadic.neg_mul w1 (-w2)]
      rw [Dyadic.mul_neg w1 w2]
      exact Eq.symm (Dyadic.neg_neg (w1 * w2))
    · case isTrue p2 =>
      have p12 : w1*w2 ≤ 0 := by
        apply Dyadic.zero_le_neg.mpr
        rw [←Dyadic.neg_mul w1 w2]
        exact Dyadic.mul_nonneg r1 p2
      rw [abs_nonneg w2 p2]
      rw [abs_nonpos (w1*w2) p12]
      exact Eq.symm (Dyadic.neg_mul w1 w2)
  · case isTrue p1 =>
    rw [abs_nonneg w1 p1]
    cases h2 : d2
    · case isFalse q2 =>
      have p2 : w2 ≤ 0 := by exact Std.le_of_not_ge q2
      have r2 : 0 ≤ -w2 := by exact zero_le_neg.mp p2
      have p12 : w1*w2 ≤ 0 := by
        apply Dyadic.zero_le_neg.mpr
        rw [←Dyadic.mul_neg w1 w2]
        exact Dyadic.mul_nonneg p1 r2
      rw [abs_nonpos w2 p2]
      rw [abs_nonpos (w1*w2) p12]
      exact Eq.symm (Dyadic.mul_neg w1 w2)
    · case isTrue p2 =>
      have p12 : 0 ≤ w1*w2 := by exact Dyadic.mul_nonneg p1 p2
      rw [abs_nonneg w2 p2]
      rw [abs_nonneg (w1*w2) p12]



/-
set_option trace.Meta.synthInstance true
-/
#print Semiring
#print Ring
#print AbsoluteValue

#print NonUnitalNonAssocSemiring.mk
#print NonUnitalSemiring.mk
#print Semiring.mk
#print Ring.mk


theorem Dyadic.sub_eq_add_neg (w1 w2 : Dyadic) : w1 - w2 = w1 + (-w2) := by rfl

def negative_seven_halves := negative_seven_fourths + negative_seven_fourths
#print negative_seven_halves

/-
instance inst_Ring_Rat : Ring Rat := by
  exact Rat.commRing.toRing
-/

def Dyadic.nsmul : ℕ → Dyadic → Dyadic :=
  fun n w => match n with | Nat.zero => Dyadic.zero | Nat.succ m => Dyadic.nsmul m w + w
/- def Dyadic.nsmul : ℕ → Dyadic → Dyadic := fun n1 w2 => (Dyadic.ofInt (Int.ofNat n1)) * w2 -/

def Dyadic.zsmul : ℤ → Dyadic → Dyadic := fun z1 w2 => (Dyadic.ofInt z1) * w2

def Dyadic.left_distrib : forall a b c : Dyadic, a * (b + c) = a * b + a * c := by
  intro a b c
  exact mul_add a b c

def Dyadic.right_distrib : forall a b c : Dyadic, (a + b) * c = a * c + b * c := by
  intros a b c
  exact add_mul a b c

#check Dyadic.left_distrib

#check Dyadic.zsmul

#check Eq.trans

#print OfNat
#check OfNat Dyadic

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



private theorem Int.negSucc_eq_neg_add_one : forall n, Int.negSucc n = - ((Int.ofNat n) + 1) := by
  intro n; rfl

set_option pp.all true
set_option pp.all false


#print Dyadic.instDecidableLE

private theorem Dyadic.max_left : forall w1 w2, w1 ≤ w2 → Dyadic.max w1 w2 = w2 := by
  intros w1 w2 Hw12; unfold Dyadic.max; exact if_pos Hw12

private theorem Dyadic.max_right' : forall w1 w2, ¬ w1 ≤ w2 → Dyadic.max w1 w2 = w1 := by
  intros w1 w2 Hw21; unfold Dyadic.max; exact if_neg Hw21

private theorem Dyadic.max_right : forall w1 w2, w2 ≤ w1 → Dyadic.max w1 w2 = w1 := by
  intros w1 w2 Hw21; unfold Dyadic.max
  rcases Dyadic.instDecidableLE w1 w2 with Hf | Ht
  · exact if_neg Hf
  · rw [if_pos Ht]; exact Dyadic.le_antisymm Hw21 Ht


private theorem Dyadic.le_sup_left : forall w1 w2 : Dyadic, w1 ≤ Dyadic.max w1 w2 := by
  intros w1 w2; unfold Dyadic.max
  rcases Dyadic.instDecidableLE w1 w2 with Hf | Ht
  · rw [if_neg Hf]; exact Dyadic.le_refl w1
  · rw [if_pos Ht]; exact le_of_eq_of_le rfl Ht

private theorem Dyadic.le_sup_right : forall w1 w2 : Dyadic, w2 ≤ Dyadic.max w1 w2 := by
  intros w1 w2; unfold Dyadic.max
  rcases Dyadic.instDecidableLE w1 w2 with Hf | Ht
  · rw [if_neg Hf]; exact Std.le_of_not_ge Hf
  · rw [if_pos Ht]; exact Dyadic.le_refl w2

private theorem Dyadic.sup_le : forall w1 w2 w3 : Dyadic,
    w1 ≤ w3 → w2 ≤ w3 → (Dyadic.max w1 w2) ≤ w3 := by
  intros w1 w2 w3 Hw13 Hw23; unfold Dyadic.max
  rcases Dyadic.instDecidableLE w1 w2 with Hf | Ht
  · rw [if_neg Hf]; exact Hw13
  · rw [if_pos Ht]; exact Hw23

private theorem Dyadic.inf_le_left : forall w1 w2 : Dyadic, Dyadic.min w1 w2 ≤ w1 := by
  intros w1 w2; unfold Dyadic.min
  rcases Dyadic.instDecidableLE w1 w2 with Hf | Ht
  · rw [if_neg Hf]; exact Std.le_of_not_ge Hf
  · rw [if_pos Ht]; exact Dyadic.le_refl w1

private theorem Dyadic.inf_le_right : forall w1 w2 : Dyadic, Dyadic.min w1 w2 ≤ w2 := by
  intros w1 w2; unfold Dyadic.min
  rcases Dyadic.instDecidableLE w1 w2 with Hf | Ht
  · rw [if_neg Hf]; exact Dyadic.le_refl w2
  · rw [if_pos Ht]; exact le_of_eq_of_le rfl Ht

private theorem Dyadic.le_inf : forall w1 w2 w3 : Dyadic,
    w1 ≤ w2 → w1 ≤ w3 → w1 ≤ (Dyadic.min w2 w3) := by
  intros w1 w2 w3 Hw12 Hw13; unfold Dyadic.min
  rcases Dyadic.instDecidableLE w2 w3 with Hf | Ht
  · rw [if_neg Hf]; exact Hw13
  · rw [if_pos Ht]; exact Hw12


private theorem Dyadic.zsmul_succ' : ∀ (n : ℕ) (a : Dyadic),
     Dyadic.zsmul (↑n.succ) a = Dyadic.zsmul (↑n) a + a := by
  unfold Dyadic.zsmul
  intro n w
  have Hzs : ↑n.succ = (↑n) + (1 : ℤ) := by exact Int.natCast_succ n
  rw [Hzs]
  rw [← Dyadic.ofInt_add]
  rw [Dyadic.right_distrib]
  have Hone : ofInt 1 = (1 : Dyadic) := by rfl
  rw [Hone]
  rw [Dyadic.one_mul]

private theorem Dyadic.zsmul_neg' : ∀ (n : ℕ) (a : Dyadic),
    Dyadic.zsmul (Int.negSucc n) a = - Dyadic.zsmul (↑n.succ) a := by
  unfold Dyadic.zsmul
  intro n w
  rw [Int.negSucc_eq_neg_add_one]
  rw [← ofInt_neg]
  rw [Dyadic.neg_mul]
  congr


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


instance inst_Ring_Dyadic' : Ring Dyadic where
  zsmul := Dyadic.zsmul
  neg_add_cancel := Dyadic.neg_add_cancel
  zsmul_succ' := Dyadic.zsmul_succ'
  zsmul_neg' := Dyadic.zsmul_neg'
  intCast_negSucc := Dyadic.intCast_negSucc




instance inst_Preorder_Dyadic : Preorder Dyadic where
  le_refl := Dyadic.le_refl
  le_trans := @Dyadic.le_trans
  lt_iff_le_not_ge := fun w1 w2 ↦ Std.LawfulOrderLT.lt_iff w1 w2

instance inst_PartialOrder_Dyadic : PartialOrder Dyadic where
  le_antisymm := @Dyadic.le_antisymm


instance instLatticeDyadic : Lattice Dyadic where
  sup := Dyadic.max
  le_sup_left := Dyadic.le_sup_left
  le_sup_right := Dyadic.le_sup_right
  sup_le := Dyadic.sup_le
  inf := Dyadic.min
  inf_le_left := Dyadic.inf_le_left
  inf_le_right := Dyadic.inf_le_right
  le_inf := Dyadic.le_inf

instance instAbsDyadic : AbsoluteValue Dyadic Dyadic where
  toFun := Dyadic.abs
  map_mul' := Dyadic.abs_mul
  nonneg' := Dyadic.abs_pos
  eq_zero' := Dyadic.abs_eq_zero
  add_le' := Dyadic.abs_add


#check |negative_seven_fourths|





def Dyadic.dist (w1 w2 : Dyadic) : Dyadic := abs (w1-w2)

def two_exp_neg_three : Dyadic := Dyadic.two_exp (-3 : Int)
def two_exp_neg_three_rat : Rat := two_exp_neg_three.toRat
#eval two_exp_neg_three_rat

#eval (two_exp_neg_three ≤ two_exp_neg_three)



namespace Dyadic

theorem toRat_add' (x y : Dyadic) : toRat (x + y) = toRat x + toRat y := by
  match x, y with
  | .zero, _ => simp [toRat, Rat.zero_add]
  | _, .zero => simp [toRat, Rat.add_zero]
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
  | .zero, _ => simp [toRat, Rat.zero_add]
  | _, .zero => simp [toRat, Rat.add_zero]
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

end Dyadic
