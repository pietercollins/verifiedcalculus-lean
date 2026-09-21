/-
Copyright  2026  Pieter Collins
Released under the GNU GPLv3 as described in the file LICENSE.
Authors: Pieter Collins
-/

import Mathlib.Data.Real.Basic

import VerifiedCalculus.Logic.Kleeneans
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

theorem Real.ratCast_neg {q : ℚ} : ((-q : ℚ) : ℝ) = - (q : ℝ) :=
by
  rw [← Real.mk_const, ← Real.mk_const]
  rw [← Real.mk_neg]
  exact Real.ext_cauchy rfl

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
  Flt.le x1 x2 ↔ toReal x1 ≤ toReal x2 :=
by
  rw [toReal_cast, toReal_cast]
  apply Iff.intro
  · intro Hxle
    apply Real.ratCast_le.mp
    have H := (FltT.le_correct x1 x2).mp
    apply H
    exact Hxle
  · intro Hyle
    apply Real.ratCast_le.mpr at Hyle
    have H := (FltT.le_correct x1 x2).mpr
    apply H
    exact le_of_eq_of_le rfl Hyle

def Bounds.le {𝔽 : Type} [Flt : RoundedFloatOperations 𝔽] [@RoundedFloatTheory 𝔽 _]
    (x1 x2 : Bounds 𝔽) : Tribool :=
  if Flt.le x1.upper x2.lower then Tribool.true else
    if Flt.le x1.lower x2.upper then Tribool.indeterminate else
      Tribool.false

def Bounds.neg {𝔽 : Type} [Flt : RoundedFloatOperations 𝔽] [@RoundedFloatTheory 𝔽 _]
    (x : Bounds 𝔽) : Bounds 𝔽 :=
  Bounds.mk (Flt.neg x.upper) (Flt.neg x.lower)

def Bounds.add {𝔽 : Type} [Flt : RoundedFloatOperations 𝔽] [@RoundedFloatTheory 𝔽 _]
    (x1 x2 : Bounds 𝔽) : Bounds 𝔽 :=
  Bounds.mk (Flt.add down x1.lower x2.lower) (Flt.add up x1.upper x2.upper)


theorem Bounds.le_is_true {𝔽 : Type} [Flt : RoundedFloatOperations 𝔽] [@RoundedFloatTheory 𝔽 _] :
  forall {x1 x2 : Bounds 𝔽}, (Bounds.le x1 x2 = Tribool.true → Flt.le x1.upper x2.lower = true) :=
by
  intros x1 x2
  unfold Bounds.le
  cases Flt.le x1.upper x2.lower
  · simp only [Bool.false_eq_true, ↓reduceIte]
    cases RoundedFloatOperations.le x1.lower x2.upper
    · simp only [Bool.false_eq_true, ↓reduceIte, reduceCtorEq, imp_self]
    · simp only [↓reduceIte, reduceCtorEq, imp_self]
  · intro _; rfl

theorem Bounds.le_is_false {𝔽 : Type} [Flt : RoundedFloatOperations 𝔽] [@RoundedFloatTheory 𝔽 _] :
  forall {x1 x2 : Bounds 𝔽}, (Bounds.le x1 x2 = Tribool.false → Flt.le x1.lower x2.upper = false) :=
by
  intros x1 x2
  unfold Bounds.le
  cases Flt.le x1.lower x2.upper
  · intro _; rfl
  · simp only [↓reduceIte]
    cases Flt.le x1.upper x2.lower
    · simp only [Bool.false_eq_true, ↓reduceIte, reduceCtorEq, Bool.true_eq_false, imp_self]
    · simp only [↓reduceIte, reduceCtorEq, Bool.true_eq_false, imp_self]

theorem Bounds.le_correct {𝔽 : Type}
    [Flt : RoundedFloatOperations 𝔽] [FltT : @RoundedFloatTheory 𝔽 _] :
  forall x1 x2 : Bounds 𝔽, forall y1 y2 : ℝ, x1.models y1 → x2.models y2 →
    (Bounds.le x1 x2 = Tribool.true → y1 ≤ y2) ∧ (Bounds.le x1 x2 = Tribool.false → ¬(y1 ≤ y2)) :=
by
  unfold Bounds.models
  simp_all only [and_imp]
  intros x1 x2 y1 y2 Hl1 Hu1 Hl2 Hu2
  apply And.intro
  · intro Hx1lex2
    have Hx1ulex2l : Flt.le x1.upper x2.lower := by exact le_is_true Hx1lex2
    have Hy1uley2l := (le_real_correct.mp Hx1ulex2l)
    transitivity (toReal x2.lower)
    · transitivity (toReal x1.upper)
      · exact le_of_eq_of_le rfl Hu1
      · exact le_real_correct.mp Hx1ulex2l
    · exact le_of_eq_of_le rfl Hl2
  · intro Hx1nlex2
    have Hx1lnlex2u : ¬ (Flt.le x1.lower x2.upper) := by
      apply ne_true_of_eq_false
      exact le_is_false Hx1nlex2
    intro Hy1ley2
    apply Hx1lnlex2u
    have Hx1llex2u : (toReal x1.lower) ≤ (toReal x2.upper) := by
      transitivity (y2)
      · transitivity (y1)
        · exact le_of_eq_of_le rfl Hl1
        · exact le_of_eq_of_le rfl Hy1ley2
      · exact le_of_eq_of_le rfl Hu2
    exact le_real_correct.mpr Hx1llex2u

theorem Bounds.neg_correct {𝔽 : Type}
    [Flt : RoundedFloatOperations 𝔽] [FltT : @RoundedFloatTheory 𝔽 _] :
  forall x : Bounds 𝔽, forall y : ℝ, x.models y →
    (Bounds.neg x).models (-y) :=
by
  unfold Bounds.models
  unfold Bounds.neg
  simp_all only [and_imp]
  intros x y Hl Hu
  apply And.intro
  · transitivity - toReal (x.upper)
    · rw [toReal_cast, toReal_cast]
      rw [← Real.ratCast_neg]
      apply Real.ratCast_le.mp
      rw [FltT.neg_correct x.upper]
      rfl
    · exact neg_le_neg_iff.mpr Hu
  · transitivity - toReal (x.lower)
    · exact neg_le_neg_iff.mpr Hl
    · rw [toReal_cast, toReal_cast]
      rw [← Real.ratCast_neg]
      apply Real.ratCast_le.mp
      rw [FltT.neg_correct x.lower]
      rfl

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
