/-
Copyright  2026  Pieter Collins
Released under the GNU GPLv3 as described in the file LICENSE.
Authors: Pieter Collins
-/

import Mathlib.Data.Real.Basic

import VerifiedCalculus.Numbers.Floats

set_option linter.style.header false

namespace RoundedBounds

open Floats.Rounded

inductive MyNat where | MO : MyNat | MS : MyNat -> MyNat
def zr := MyNat.MO
def tw := MyNat.MS (zr.MS)

class MyAdd (α : Type) where
  my_add : α → α → α
#check @MyAdd.my_add

instance : MyAdd Nat
  where my_add := Nat.add

structure Bounds (𝔽 : Type) [@RoundedFloatOperations 𝔽] [@RoundedFloatTheory 𝔽 _] where
  lower : 𝔽
  upper : 𝔽

#check Bounds.mk
#check Bounds.lower

def x : Bounds Float64 := Bounds.mk 3.125 3.1875
def y := @Bounds.mk Float64 _ _ 2.6875 2.75
def xl := x.lower
def xlq := xl.toRat
def xlr := xl.toReal

#check x
#check xl
#eval Bounds.lower x




def toReal {𝔽 : Type} [Flt : RoundedFloatOperations 𝔽] (x : 𝔽) : ℝ := Flt.toRat x

def Bounds.models {𝔽}
     [Flt : RoundedFloatOperations 𝔽] [@RoundedFloatTheory 𝔽 _] (x : Bounds 𝔽) (y : ℝ) : Prop :=
  (toReal x.lower ≤ y) ∧ (y ≤ toReal x.upper)


def Float64Bounds := Bounds Float64

#check Float64Bounds
#print Float64Bounds

theorem Real.ratCast_eq {q1 q2 : ℚ} : q1 = q2 ↔ (q1 : ℝ) = (q2 : ℝ) := by
  apply Iff.intro
  · exact fun a ↦ Real.ext_cauchy (congrArg Real.cauchy (congrArg Rat.cast a))
  · have Heqv := @CauSeq.const_equiv _ _ _ _ _ _ abs _ q1 q2
    rw [← Real.mk_const, ← Real.mk_const]
    intro H
    apply Heqv.mp
    apply Real.mk_eq.mp
    exact H

theorem Real.ratCast_le {x y : ℚ} : x ≤ y ↔ (x : ℝ) ≤ (y : ℝ) := by
  have Hlt := @Real.ratCast_lt x y
  rw [Rat.le_iff_lt_or_eq]
  rw [Std.le_iff_lt_or_eq]
  apply Iff.intro
  · intro Hlteq
    cases Hlteq with
    | inl Hlt => left; exact Real.ratCast_lt.mpr Hlt
    | inr Heq => right; exact ratCast_eq.mp Heq
  · intro Hlteq
    cases Hlteq with
    | inl Hlt => left; exact Real.ratCast_lt.mp Hlt
    | inr Heq => right; exact ratCast_eq.mpr Heq

theorem Real.ratCast_add {q1 q2 : ℚ} : ((q1 + q2 : ℚ) : ℝ) = (q1 : ℝ) + (q2 : ℝ) :=
by
  rw [← Real.mk_const, ← Real.mk_const, ← Real.mk_const]
  rw [← Real.mk_add]
  exact Real.ext_cauchy rfl



open Rounding

theorem toReal_cast {𝔽 : Type} [Flt : RoundedFloatOperations 𝔽] :
  forall x : 𝔽, toReal x = ((Flt.toRat x) : ℝ) :=
by
  intro x; rfl

theorem le_real_correct {𝔽 : Type}
    [Flt : RoundedFloatOperations 𝔽] [FltT : @RoundedFloatTheory 𝔽 _] {x1 x2 : 𝔽} :
  Flt.le x1 x2 → toReal x1 ≤ toReal x2 :=
by
  intro Hxle
  rw [toReal_cast, toReal_cast]
  apply Real.ratCast_le.mp
  have H := (FltT.le_correct x1 x2).mp
  apply H
  exact Hxle



def Bounds.add {𝔽 : Type} [Flt : RoundedFloatOperations 𝔽] [@RoundedFloatTheory 𝔽 _]
    (x y : Bounds 𝔽) : Bounds 𝔽 :=
  Bounds.mk (Flt.add down x.lower y.lower) (Flt.add up x.upper y.upper)



theorem Bounds.add_correct {𝔽 : Type}
    [Flt : RoundedFloatOperations 𝔽] [FltT : @RoundedFloatTheory 𝔽 _] :
  forall x1 x2 : Bounds 𝔽, forall y1 y2 : ℝ, x1.models y1 → x2.models y2 →
    (Bounds.add x1 x2).models (y1+y2) :=
by
  unfold Bounds.models
  unfold Bounds.add
  simp only [and_imp]
  intros x1 x2 y1 y2 H1l H1u H2l H2u
  apply And.intro
  · transitivity toReal (x1.lower) + toReal (x2.lower)
    · rw [toReal_cast, toReal_cast, toReal_cast]
      rw [← Real.ratCast_add]
      apply Real.ratCast_le.mp
      exact (FltT.add_correct x1.lower x2.lower).down
    · exact add_le_add H1l H2l
  · have Hu := (FltT.add_correct x1.upper x2.upper).up
    transitivity toReal (x1.upper) + toReal (x2.upper)
    · exact add_le_add H1u H2u
    · rw [toReal_cast, toReal_cast, toReal_cast]
      rw [← Real.ratCast_add]
      apply Real.ratCast_le.mp
      exact (FltT.add_correct x1.upper x2.upper).up

end RoundedBounds
