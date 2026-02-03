/-
Copyright  2026  Pieter Collins
Released under the GNU GPLv3 as described in the file LICENSE.
Authors: Pieter Collins
-/

import Mathlib.Tactic.Linter.Style

import VerifiedCalculus.Numbers.Integer
import VerifiedCalculus.Numbers.Dyadic

import Init.Data.Dyadic

set_option linter.style.header false



theorem Int.abs_neg (z : Int) : |-z| = |z| := by grind

theorem Int.abs_add (z1 z2 : Int) : |z1 + z2| ≤ |z1| + |z2| := by grind

theorem Int.neg_odd (z : Int) : z % 2 = 1 → -z % 2 = 1 := by grind





def Dyadic.is_increasing (xs : Nat -> Dyadic) : Prop :=
  forall n1 n2, n1 <= n2 -> xs n1 <= xs n2

def Dyadic.is_decreasing (xs : Nat -> Dyadic) : Prop :=
  forall n1 n2, n1 <= n2 -> xs n2 <= xs n1

def Dyadic.is_fast_cauchy_sequence (xs : Int → Dyadic) : Prop :=
  forall n1 n2, abs (xs n1 - xs n2) <= two_exp n1 + two_exp n2

def Dyadic.fast_equivalent_cauchy_sequences (xs1 xs2 : Int → Dyadic) : Prop :=
  forall n : Int, ( abs (xs1 n - xs2 n) ≤  Dyadic.two_exp (n+1 : Int) )

def Dyadic.equivalent_cauchy_sequences (xs1 xs2 : Int → Dyadic) : Prop :=
  forall n : Int, exists m : Int, forall l, l ≤ m →
    ( abs (xs1 l - xs2 l) ≤  Dyadic.two_exp (n : Int) )


theorem Dyadic.equivalent_cauchy_sequences_refl :
    forall (xs : Int → Dyadic), Dyadic.equivalent_cauchy_sequences xs xs := by
  unfold equivalent_cauchy_sequences
  intro xs n
  exists 0
  intro l l_le_zero
  have diff_zero : xs l - xs l = 0 := by exact sub_self (xs l)
  rw [diff_zero]
  rw [abs_zero]
  unfold two_exp
  unfold Dyadic.shiftLeft
  exact le_of_eq_of_le rfl rfl

theorem Dyadic.equivalent_cauchy_sequences_symm :
  forall (xs ys : Int → Dyadic),
    equivalent_cauchy_sequences xs ys → equivalent_cauchy_sequences ys xs := by
  unfold equivalent_cauchy_sequences
  intros xs ys H n
  cases H n
  · case intro m Hm =>
    exists m
    intro l Hlm
    have Hl := Hm l Hlm
    have abs_eq : abs (xs l - ys l) = abs (ys l - xs l) := by
      exact Dyadic.abs_sub_eq (xs l) (ys l)
    rw [←abs_eq]
    exact Hl

theorem Dyadic.equivalent_cauchy_sequences_trans :
  forall (xs ys zs : Int → Dyadic),
    equivalent_cauchy_sequences xs ys → equivalent_cauchy_sequences ys zs →
      equivalent_cauchy_sequences xs zs := by
  unfold equivalent_cauchy_sequences
  intros xs ys zs Hxy Hyz n
  cases Hxy (n-1)
  ·  case intro m1 Hm1 =>
    cases Hyz (n-1)
    · case intro m2 Hm2 =>
      let m := min m1 m2
      exists m
      intro l Hlm
      have Hlm1 : l ≤ m1 := by exact le_of_le_min_left Hlm
      have Hlm2 : l ≤ m2 := by exact le_of_le_min_right Hlm
      have  Hlxy := Hm1 l Hlm1
      have  Hlyz := Hm2 l Hlm2
      trans |xs l - ys l| + |ys l - zs l|
      · exact abs_triangle
      · trans two_exp (n - 1) + two_exp (n - 1)
        · exact add_le_add (Hm1 l Hlm1) (Hm2 l Hlm2)
        · apply le_of_eq;
          exact twice_two_exp


def MetricSequenceReal :=
  { xs : Nat -> Dyadic | forall n1 n2, Dyadic.dist (xs n1) (xs n2)
                            <= (Dyadic.hlf 1) ^ ( (n1 + n2)) }



def neg_three : Dyadic := Dyadic.ofInt (-3 : Int)
def hlf_neg_three : Dyadic := Dyadic.hlf neg_three * Dyadic.two_exp 3
def abs_hlf_neg_three : Dyadic := Dyadic.abs hlf_neg_three

def rat_abs_hlf_neg_three : Rat := Dyadic.toRat abs_hlf_neg_three

#eval rat_abs_hlf_neg_three
