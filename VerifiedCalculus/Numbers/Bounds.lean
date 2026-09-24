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

theorem Real.ratCast_mul {q1 q2 : ℚ} : ((q1 * q2 : ℚ) : ℝ) = (q1 : ℝ) * (q2 : ℝ) :=
by
  rw [← Real.mk_const, ← Real.mk_const, ← Real.mk_const]
  rw [← Real.mk_mul]
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

def Bounds.mul {𝔽 : Type} [Flt : RoundedFloatOperations 𝔽] [@RoundedFloatTheory 𝔽 _]
    (x y : Bounds 𝔽) : Bounds 𝔽 :=
  if Flt.zero ≤ x.lower then
    if Flt.zero ≤ y.lower then
      Bounds.mk (Flt.mul down x.lower y.lower) (Flt.mul up x.upper y.upper)
    else if y.upper ≤ Flt.zero then
      Bounds.mk (Flt.mul down x.upper y.lower) (Flt.mul up x.lower y.upper)
    else
      Bounds.mk (Flt.mul down x.upper y.lower) (Flt.mul up x.upper y.upper)
  else if x.upper ≤ Flt.zero then
    if Flt.zero ≤ y.lower then
      Bounds.mk (Flt.mul down x.lower y.upper) (Flt.mul up x.upper y.lower)
    else if y.upper ≤ Flt.zero then
      Bounds.mk (Flt.mul down x.upper y.upper) (Flt.mul up x.lower y.lower)
    else
      Bounds.mk (Flt.mul down x.upper y.upper) (Flt.mul up x.upper y.lower)
  else
    if Flt.zero ≤ y.lower then
      Bounds.mk (Flt.mul down x.lower y.upper) (Flt.mul up x.upper y.upper)
    else if y.upper ≤ Flt.zero then
      Bounds.mk (Flt.mul down x.upper y.lower) (Flt.mul up x.lower y.lower)
    else
      Bounds.mk
        (Flt.min (Flt.mul down x.lower y.upper) (Flt.mul down x.upper y.lower))
        (Flt.max (Flt.mul up x.lower y.lower) (Flt.mul up x.upper y.upper))

def Bounds.abs {𝔽 : Type} [Flt : RoundedFloatOperations 𝔽] [@RoundedFloatTheory 𝔽 _]
    (x : Bounds 𝔽) : Bounds 𝔽 :=
  if Flt.zero ≤ x.lower then
    Bounds.mk x.lower x.upper
  else if x.upper ≤ Flt.zero then
    Bounds.mk (Flt.neg x.upper) (Flt.neg x.lower)
  else
    Bounds.mk Flt.zero (Flt.max (Flt.neg x.lower) x.upper)


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


theorem zero_le_correct {𝔽 : Type}
    [Flt : RoundedFloatOperations 𝔽] [FltT : @RoundedFloatTheory 𝔽 _] :
  forall x : 𝔽, Flt.zero ≤ x ↔ 0 ≤ toReal x :=
by
  intro x
  unfold toReal
  rw [←Rat.cast_zero]
  apply Iff.intro
  · intro H
    apply Real.ratCast_le.mp
    rw [←FltT.zero_correct]
    apply (FltT.le_correct Flt.zero x).mp
    exact Bool.eq_false_imp_eq_true.mp fun a ↦ H
  · intro H
    apply Real.ratCast_le.mpr at H
    rw [←FltT.zero_correct] at H
    apply (FltT.le_correct Flt.zero x).mpr at H
    exact H



theorem Bounds.mul_correct {𝔽 : Type}
    [Flt : RoundedFloatOperations 𝔽] [FltT : @RoundedFloatTheory 𝔽 _] :
  forall x1 x2 : Bounds 𝔽, forall y1 y2 : ℝ, x1.models y1 → x2.models y2 →
    (Bounds.mul x1 x2).models (y1*y2) :=
by
  unfold Bounds.mul
  intros x1 x2 y1 y2
  have Hx : exists (x1l x1u x2l x2u : 𝔽),
      x1l = x1.lower ∧ x1u=x1.upper ∧ x2l = x2.lower ∧ x2u=x2.upper := by
    exists x1.lower; exists x1.upper; exists x2.lower; exists x2.upper
  cases Hx with | intro x1l Hx =>
  cases Hx with | intro x1u Hx =>
  cases Hx with | intro x2l Hx =>
  cases Hx with | intro x2u Hx =>
  cases Hx with | intro Ex1l Hx =>
  cases Hx with | intro Ex1u Hx =>
  cases Hx with | intro Ex2l Ex2u =>
  unfold Bounds.models
  simp only [and_imp]
  rw [←Ex1l,←Ex1u,←Ex2l,←Ex2u]
  intros H1l H1u H2l H2u
  clear Ex1l Ex1u Ex2l Ex2u
  let Fmul := Flt.mul
  have tmp : Fmul = RoundedFloatOperations.mul := by rfl
  rw [←tmp]; clear tmp
  have Hp1l : exists p, p = Flt.le Flt.zero x1l := by exists (Flt.le Flt.zero x1l)
  have Hp2l : exists p, p = Flt.le Flt.zero x2l := by exists (Flt.le Flt.zero x2l)
  cases Hp1l with | intro p1l Ep1l =>
  cases Hp2l with | intro p2l Ep2l =>
  cases p1l with
  | true =>
      have H0lex1l : 0 ≤ toReal x1l := by exact (zero_le_correct x1l).mp Ep1l
      cases p2l with
      | true =>
          have H0lex2l : 0 ≤ toReal x2l := by exact (zero_le_correct x2l).mp Ep2l
          unfold roundedFloatLE
          simp_all only [↓reduceIte]
          apply And.intro
          · transitivity (toReal x1l) * (toReal x2l)
            · have t := (FltT.mul_correct x1l x2l).down
              unfold toReal
              apply Real.ratCast_mul
              sorry
       | false => sorry
  | false => sorry


theorem Bounds.abs_correct {𝔽 : Type}
    [Flt : RoundedFloatOperations 𝔽] [FltT : @RoundedFloatTheory 𝔽 _] :
  forall x : Bounds 𝔽, forall y : ℝ, x.models y →
    (Bounds.abs x).models |y| :=
by
  let Fneg := Flt.neg; have Eneg : Fneg = Flt.neg := by rfl
  let Fmax := Flt.max; have Emax : Fmax = Flt.max := by rfl
  let Fle := Flt.le; have Ele : Fle = Flt.le := by rfl
  have Qneg : forall q : ℚ, (q.neg : ℚ) = (-q : ℚ) := by
    exact fun q ↦ (fun {q1 q2} ↦ Real.ratCast_eq.mpr) rfl
  unfold Bounds.models
  unfold Bounds.abs
  simp only [and_imp]
  intros x y Hl Hu
  rw [←Eneg,←Emax];
  have Hp : exists p, p = Flt.le Flt.zero x.lower := by exists (Flt.le Flt.zero x.lower)
  cases Hp with | intro p Ep =>
  cases p with
  | true =>
      unfold roundedFloatLE
      simp_all only [↓reduceIte]
      have H0ley : (0 ≤ y) := by
        transitivity (toReal x.lower)
        · rw [←Rat.cast_zero]
          unfold toReal
          apply Real.ratCast_le.mp
          rw [←FltT.zero_correct]
          apply (FltT.le_correct Flt.zero x.lower).mp
          exact (Eq.symm Ep)
        · exact Hl
      have Hay : |y|=y := by exact abs_of_nonneg H0ley
      rw [Hay]
      exact ⟨Hl, Hu1⟩
  | false =>
      unfold roundedFloatLE
      simp_all only [Bool.false_eq, Bool.true_eq_false, ↓reduceIte]
      have Hq : exists q, q = Flt.le x.upper Flt.zero := by exists (Flt.le x.upper Flt.zero)
      cases Hq with | intro q Eq =>
      cases q with
      | true =>
          simp_all only [Bool.true_eq, ↓reduceIte]
          have Hyle0 : (y ≤ 0) := by
            transitivity (toReal x.upper)
            · exact Hu
            · rw [←Rat.cast_zero]
              unfold toReal
              apply Real.ratCast_le.mp
              rw [←FltT.zero_correct]
              apply (FltT.le_correct x.upper Flt.zero).mp
              exact Eq
          have Hay : |y|=-y := by exact abs_of_nonpos Hyle0
          rw [Hay]
          apply And.intro
          · unfold toReal
            rw [FltT.neg_correct]
            rw [Qneg]
            rw [Real.ratCast_neg]
            exact neg_le_neg_iff.mpr Hu
          · unfold toReal
            rw [FltT.neg_correct]
            rw [Qneg]
            rw [Real.ratCast_neg]
            exact neg_le_neg_iff.mpr Hl
      | false =>
          simp_all only [Bool.false_eq, Bool.true_eq_false, ↓reduceIte]
          apply And.intro
          · have H : (toReal Flt.zero = (0:ℝ)) := by sorry
            rw [H]
            exact abs_nonneg y
          · have Hy0 : 0 ≤ y ∨ y ≤ 0 := by exact Std.IsLinearPreorder.le_total 0 y
            cases Hy0 with
            | inl H0ley =>
                rw [abs_of_nonneg]
                unfold toReal
                rw [FltT.max_correct]
                simp
                transitivity ( (Flt.toRat x.upper) : ℝ)
                · exact Hu
                · apply Real.ratCast_le.mp
                  exact Std.right_le_max
                exact H0ley
            | inr Hyle0 =>
                rw [abs_of_nonpos]
                unfold toReal
                rw [FltT.max_correct]
                simp
                transitivity ( (Flt.toRat (Flt.neg x.lower)) : ℝ)
                rw [FltT.neg_correct]
                rw [Qneg]
                rw [Real.ratCast_neg]
                apply neg_le_neg_iff.mpr
                exact Hl


end RoundedBounds
