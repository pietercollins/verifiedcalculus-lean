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

theorem Real.ratCast_sub {q1 q2 : ℚ} : ((q1 - q2 : ℚ) : ℝ) = (q1 : ℝ) - (q2 : ℝ) :=
by
  have HR {r1 r2 : ℝ} : r1 - r2 = r1 + (-r2) := sub_eq_add_neg r1 r2
  have HQ : q1 - q2 = q1 + (-q2) := Rat.sub_eq_add_neg q1 q2
  rw [HR,HQ]
  rw [←Real.ratCast_neg]
  rw [←Real.ratCast_add]

theorem Real.ratCast_mul {q1 q2 : ℚ} : ((q1 * q2 : ℚ) : ℝ) = (q1 : ℝ) * (q2 : ℝ) :=
by
  rw [← Real.mk_const, ← Real.mk_const, ← Real.mk_const]
  rw [← Real.mk_mul]
  exact Real.ext_cauchy rfl

theorem Real.ratCast_min {q1 q2 : ℚ} : ((min q1 q2 : ℚ) : ℝ) = min (q1 : ℝ) (q2 : ℝ) :=
by
  have HQ : min q1 q2 = if q1 ≤ q2 then q1 else q2 := by exact ratCast_eq.mpr rfl
  rw [HQ]; clear HQ
  split
  · case isTrue Ht =>
      rw[←left_eq_inf.mpr]
      exact ratCast_le.mp Ht
  · case isFalse Hf =>
      apply le_of_not_ge at Hf
      rw[←right_eq_inf.mpr]
      exact ratCast_le.mp Hf

theorem Real.ratCast_max {q1 q2 : ℚ} : ((max q1 q2 : ℚ) : ℝ) = max (q1 : ℝ) (q2 : ℝ) :=
by
  have HQ : max q1 q2 = if q1 ≤ q2 then q2 else q1 := by exact ratCast_eq.mpr rfl
  rw [HQ]; clear HQ
  split
  · case isTrue Ht =>
      rw[←right_eq_sup.mpr]
      exact ratCast_le.mp Ht
  · case isFalse Hf =>
      apply le_of_not_ge at Hf
      rw[←left_eq_sup.mpr]
      exact ratCast_le.mp Hf

open Rounding

section WithFloat


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

theorem nle_impl {𝔽 : Type}
    [Flt : RoundedFloatOperations 𝔽] [FltT : @RoundedFloatTheory 𝔽 _] {x1 x2 : 𝔽} :
  Flt.le x1 x2 = false → Flt.le x2 x1 = true :=
by
  intro H
  apply le_real_correct.mpr
  apply le_of_not_ge
  intro Hrl
  apply (@le_real_correct 𝔽 _ _ x1 x2).mpr at Hrl
  rw [Hrl] at H
  exact (Bool.eq_not_self true).mp H

theorem zero_eq {𝔽 : Type}
    [Flt : RoundedFloatOperations 𝔽] [FltT : @RoundedFloatTheory 𝔽 _] :
  toReal Flt.zero = 0 :=
by
  unfold toReal
  rw [←Rat.cast_zero]
  rw [←FltT.zero_correct]

theorem neg_real_correct {𝔽 : Type}
    [Flt : RoundedFloatOperations 𝔽] [FltT : @RoundedFloatTheory 𝔽 _] {x : 𝔽} :
  toReal (Flt.neg x) = - (toReal x) :=
by
  unfold toReal; rw [FltT.neg_correct x]; exact Real.ratCast_neg

theorem min_real_correct {𝔽 : Type}
    [Flt : RoundedFloatOperations 𝔽] [FltT : @RoundedFloatTheory 𝔽 _] {x1 x2 : 𝔽} :
  toReal (Flt.min x1 x2) = min (toReal x1) (toReal x2) :=
by
  unfold toReal; rw [FltT.min_correct x1 x2]; exact Real.ratCast_min

theorem max_real_correct {𝔽 : Type}
    [Flt : RoundedFloatOperations 𝔽] [FltT : @RoundedFloatTheory 𝔽 _] {x1 x2 : 𝔽} :
  toReal (Flt.max x1 x2) = max (toReal x1) (toReal x2) :=
by
  unfold toReal; rw [FltT.max_correct x1 x2]; exact Real.ratCast_max

private theorem mul_down_real_correct {𝔽 : Type}
    [Flt : RoundedFloatOperations 𝔽] [FltT : @RoundedFloatTheory 𝔽 _] :
  forall {x1 x2}, toReal (Flt.mul down x1 x2) ≤ toReal x1 * toReal x2 :=
by
  intros x1 x2
  unfold toReal
  rw [←Real.ratCast_mul];
  apply Real.ratCast_le.mp;
  exact (FltT.mul_correct x1 x2).down

private theorem mul_up_real_correct {𝔽 : Type}
    [Flt : RoundedFloatOperations 𝔽] [FltT : @RoundedFloatTheory 𝔽 _] :
  forall {x1 x2}, toReal x1 * toReal x2 ≤ toReal (Flt.mul up x1 x2):=
by
  intros x1 x2
  unfold toReal
  rw [←Real.ratCast_mul];
  apply Real.ratCast_le.mp;
  exact (FltT.mul_correct x1 x2).up

private theorem mul_down_real_trans {𝔽 : Type}
    [Flt : RoundedFloatOperations 𝔽] [FltT : @RoundedFloatTheory 𝔽 _] :
  forall {x1 x2 y1 y2}, toReal x1 * toReal x2 ≤ y1 * y2 →
    toReal (Flt.mul down x1 x2) ≤ y1 * y2 :=
by
  intros x1 x2 y1 y2 H
  trans toReal x1 * toReal x2
  · exact mul_down_real_correct
  · exact H

private theorem mul_up_real_trans {𝔽 : Type}
    [Flt : RoundedFloatOperations 𝔽] [FltT : @RoundedFloatTheory 𝔽 _] :
  forall {x1 x2 y1 y2}, y1 * y2 ≤ toReal x1 * toReal x2 →
    y1 * y2 ≤ toReal (Flt.mul up x1 x2) :=
by
  intros x1 x2 y1 y2 H
  trans toReal x1 * toReal x2
  · exact H
  · exact mul_up_real_correct

/-
theorem zero_le_correct {𝔽 : Type}
    [Flt : RoundedFloatOperations 𝔽] [FltT : @RoundedFloatTheory 𝔽 _] {x : 𝔽} :
  Flt.zero ≤ x ↔ 0 ≤ toReal x :=
by
  rw [←@zero_eq 𝔽]
  exact le_real_correct
-/

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

def Bounds.sub {𝔽 : Type} [Flt : RoundedFloatOperations 𝔽] [@RoundedFloatTheory 𝔽 _]
    (x1 x2 : Bounds 𝔽) : Bounds 𝔽 :=
  Bounds.mk (Flt.sub down x1.lower x2.upper) (Flt.sub up x1.upper x2.lower)

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
      Bounds.mk (Flt.mul down x.lower y.upper) (Flt.mul up x.lower y.lower)
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
      · exact Hu1
      · exact le_real_correct.mp Hx1ulex2l
    · exact Hl2
  · intro Hx1nlex2
    have Hx1lnlex2u : ¬ (Flt.le x1.lower x2.upper) := by
      apply ne_true_of_eq_false
      exact le_is_false Hx1nlex2
    intro Hy1ley2
    apply Hx1lnlex2u
    have Hx1llex2u : (toReal x1.lower) ≤ (toReal x2.upper) := by
      transitivity (y2)
      · transitivity (y1)
        · exact Hl1
        · exact Hy1ley2
      · exact Hu2
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
  · transitivity toReal (x1.upper) + toReal (x2.upper)
    · exact add_le_add H1u H2u
    · rw [toReal_cast, toReal_cast, toReal_cast]
      rw [← Real.ratCast_add]
      apply Real.ratCast_le.mp
      exact (FltT.add_correct x1.upper x2.upper).up


theorem Bounds.sub_correct {𝔽 : Type}
    [Flt : RoundedFloatOperations 𝔽] [FltT : @RoundedFloatTheory 𝔽 _] :
  forall x1 x2 : Bounds 𝔽, forall y1 y2 : ℝ, x1.models y1 → x2.models y2 →
    (Bounds.sub x1 x2).models (y1-y2) :=
by
  unfold Bounds.models
  unfold Bounds.sub
  simp only [and_imp]
  intros x1 x2 y1 y2 H1l H1u H2l H2u
  apply And.intro
  · transitivity toReal x1.lower - toReal x2.upper
    · rw [toReal_cast, toReal_cast, toReal_cast]
      rw [← Real.ratCast_sub]
      apply Real.ratCast_le.mp
      exact (FltT.sub_correct x1.lower x2.upper).down
    · exact sub_le_sub H1l H2u
  · transitivity toReal x1.upper - toReal x2.lower
    · exact sub_le_sub H1u H2l
    · rw [toReal_cast, toReal_cast, toReal_cast]
      rw [← Real.ratCast_sub]
      apply Real.ratCast_le.mp
      exact (FltT.sub_correct x1.upper x2.lower).up



theorem Bounds.mul_correct' {𝔽 : Type}
    [Flt : RoundedFloatOperations 𝔽] [FltT : @RoundedFloatTheory 𝔽 _] :
  forall x1l x1u x2l x2u : 𝔽, forall y1 y2 : ℝ,
    toReal x1l ≤ y1 → y1 ≤ toReal x1u → toReal x2l ≤ y2 → y2 ≤ toReal x2u →
    (Bounds.mul (Bounds.mk x1l x1u) (Bounds.mk x2l x2u)).models (y1*y2) :=
by
  let Fmul := Flt.mul
  let z := Flt.zero
  intros x1l x1u x2l x2u y1 y2 H1l H1u H2l H2u
  unfold Bounds.mul
  simp only
  have tmp : Fmul = Flt.mul := by rfl
  rw [←tmp]; clear tmp
  have tmp : z = Flt.zero := by rfl
  rw [←tmp]; clear tmp
  unfold roundedFloatLE
  cases Hp1l : Flt.le z x1l with
  | true =>
      have H0ley1l : 0 ≤ toReal x1l := by
        rw [←@zero_eq 𝔽]; exact le_real_correct.mp Hp1l
      cases Hp2l : Flt.le z x2l with
      | true =>
          have H0ley2l : 0 ≤ toReal x2l := by
            rw [←@zero_eq 𝔽]; exact le_real_correct.mp Hp2l
          simp_all only [↓reduceIte]
          apply And.intro <;> simp only
          · apply mul_down_real_trans; apply mul_le_mul <;> grind
          · apply mul_up_real_trans; apply mul_le_mul <;> grind
      | false =>
          have Hp2lr := nle_impl Hp2l
          have Hy2lle : toReal x2l ≤ 0 := by
            rw [←@zero_eq 𝔽]; exact le_real_correct.mp Hp2lr
          cases Hp2u : Flt.le x2u z with
          | true =>
              have Hy2ule0 : toReal x2u ≤ 0 := by
                rw [←@zero_eq 𝔽]; exact le_real_correct.mp Hp2u
              simp_all only [↓reduceIte, Bool.false_eq_true]
              apply And.intro <;> simp only
              · apply mul_down_real_trans
                have Ht := @mul_le_mul _ _ _ _ y1 (toReal x1u) (-y2) (-toReal x2l)
                simp_all only [neg_le_neg_iff, Left.nonneg_neg_iff, mul_neg, forall_const,
                  ge_iff_le]
                apply Ht <;> grind
              · apply mul_up_real_trans
                have Ht := @mul_le_mul _ _ _ _ (toReal x1l) y1 (-toReal x2u) (-y2)
                simp_all only [neg_le_neg_iff, Left.nonneg_neg_iff, mul_neg, forall_const,
                  ge_iff_le]
                apply Ht; grind
          | false =>
              have H0ley2u : 0 ≤ toReal x2u := by
                apply le_of_not_ge; rw [←@zero_eq 𝔽]; intro Hy2ule0
                apply le_real_correct.mpr at Hy2ule0; grind
              simp_all only [↓reduceIte, Bool.false_eq_true]
              apply And.intro <;> simp only
              · apply mul_down_real_trans
                rw [mul_comm, mul_comm y1 y2]
                have Ht := @mul_le_mul _ _ _ _ (-y2) (-toReal x2l) y1 (toReal x1u)
                simp_all only [neg_le_neg_iff, Left.nonneg_neg_iff, neg_mul, forall_const,
                  ge_iff_le]
                apply Ht; grind
              · apply mul_up_real_trans
                rw [mul_comm (toReal x1u) (toReal x2u), mul_comm y1 y2]
                have Ht := @mul_le_mul _ _ _ _ y2 (toReal x2u) y1 (toReal x1u)
                simp_all only [forall_const, ge_iff_le]
                apply Ht; grind
  | false =>
      have Hy1lle0 : toReal x1l ≤ 0 := by
        rw [←@zero_eq 𝔽]; exact le_real_correct.mp (nle_impl Hp1l)
      cases Hp1u : Flt.le x1u z with
      | true =>
          have Hy1ule0 : toReal x1u ≤ 0 := by
            rw [←@zero_eq 𝔽]; exact le_real_correct.mp Hp1u
          cases Hp2l : Flt.le z x2l with
          | true =>
              have H0ley2l : 0 ≤ toReal x2l := by
                rw [←@zero_eq 𝔽]; exact le_real_correct.mp Hp2l
              simp_all only [↓reduceIte]
              simp only [Bool.false_eq_true, ↓reduceIte]
              apply And.intro <;> simp only
              · apply mul_down_real_trans
                have Ht := @mul_le_mul _ _ _ _ (-y1) (-toReal x1l) (y2) (toReal x2u)
                simp_all only [neg_le_neg_iff, Left.nonneg_neg_iff, neg_mul, forall_const,
                  ge_iff_le]
                apply Ht; grind
              · apply mul_up_real_trans
                have Ht := @mul_le_mul _ _ _ _ (-toReal x1u) (-y1) (toReal x2l) (y2)
                simp_all only [neg_le_neg_iff, Left.nonneg_neg_iff, neg_mul, forall_const,
                  ge_iff_le]
                apply Ht; grind
          | false =>
              have Hy2lle : toReal x2l ≤ 0 := by
                rw [←@zero_eq 𝔽]; exact le_real_correct.mp (nle_impl Hp2l)
              cases Hp2u : Flt.le x2u z with
              | true =>
                  have Hy2ule0 : toReal x2u ≤ 0 := by
                    rw [←@zero_eq 𝔽]; exact le_real_correct.mp Hp2u
                  simp_all only [↓reduceIte, Bool.false_eq_true]
                  apply And.intro <;> simp only
                  · apply mul_down_real_trans
                    have Ht := @mul_le_mul _ _ _ _ (-toReal x1u) (-y1) (-toReal x2u) (-y2)
                    simp_all only [neg_le_neg_iff, Left.nonneg_neg_iff, mul_neg, neg_mul, neg_neg,
                      forall_const, ge_iff_le]
                    apply Ht; grind
                  · apply mul_up_real_trans
                    have Ht := @mul_le_mul _ _ _ _ (-y1) (-toReal x1l) (-y2) (-toReal x2l)
                    simp_all only [neg_le_neg_iff, Left.nonneg_neg_iff, mul_neg, neg_mul, neg_neg,
                      forall_const, ge_iff_le]
                    apply Ht; grind
              | false =>
                  have H0ley2u : 0 ≤ toReal x2u := by
                    rw [←@zero_eq 𝔽]; exact le_real_correct.mp (nle_impl Hp2u)
                  simp_all only [↓reduceIte, Bool.false_eq_true]
                  apply And.intro <;> simp only
                  · apply mul_down_real_trans
                    rw [mul_comm (toReal x1l) (toReal x2u), mul_comm y1 y2]
                    have Ht := @mul_le_mul _ _ _ _ (y2) (toReal x2u) (-y1) (-toReal x1l)
                    simp_all only [neg_le_neg_iff, Left.nonneg_neg_iff, mul_neg, forall_const,
                      ge_iff_le]
                    apply Ht; grind
                  · apply mul_up_real_trans
                    rw [mul_comm (toReal x1l) (toReal x2l), mul_comm y1 y2]
                    have Ht := @mul_le_mul _ _ _ _ (-y2) (-toReal x2l) (-y1) (-toReal x1l)
                    simp_all only [neg_le_neg_iff, Left.nonneg_neg_iff, mul_neg, neg_mul, neg_neg,
                      forall_const, ge_iff_le]
                    apply Ht; grind
      | false =>
          have H0ley1u : 0 ≤ toReal x1u := by
            rw [←@zero_eq 𝔽]; exact le_real_correct.mp (nle_impl Hp1u)
          cases Hp2l : Flt.le z x2l with
          | true =>
              have H0ley2l : 0 ≤ toReal x2l := by
                rw [←@zero_eq 𝔽]; exact le_real_correct.mp Hp2l
              simp_all only [↓reduceIte]
              simp only [Bool.false_eq_true, ↓reduceIte]
              apply And.intro <;> simp only
              · apply mul_down_real_trans
                have Ht := @mul_le_mul _ _ _ _ (-y1) (-toReal x1l) (y2) (toReal x2u)
                simp_all only [neg_le_neg_iff, Left.nonneg_neg_iff, neg_mul, forall_const,
                  ge_iff_le]
                apply Ht; grind
              · apply mul_up_real_trans
                have Ht := @mul_le_mul _ _ _ _ (y1) (toReal x1u) (y2) (toReal x2u)
                simp_all only [forall_const, ge_iff_le]
                apply Ht; grind
          | false =>
              have Hy2lle : toReal x2l ≤ 0 := by
                rw [←@zero_eq 𝔽]; exact le_real_correct.mp (nle_impl Hp2l)
              cases Hp2u : Flt.le x2u z with
              | true =>
                  have Hy2ule0 : toReal x2u ≤ 0 := by
                    rw [←@zero_eq 𝔽]; exact le_real_correct.mp Hp2u
                  simp_all only [↓reduceIte, Bool.false_eq_true]
                  apply And.intro <;> simp only
                  · apply mul_down_real_trans
                    have Ht := @mul_le_mul _ _ _ _  (y1) (toReal x1u) (-y2) (-toReal x2l)
                    simp_all only [neg_le_neg_iff, Left.nonneg_neg_iff, mul_neg, forall_const,
                      ge_iff_le]
                    apply Ht; grind
                  · apply mul_up_real_trans
                    have Ht := @mul_le_mul _ _ _ _ (-y1) (-toReal x1l) (-y2) (-toReal x2l)
                    simp_all only [neg_le_neg_iff, Left.nonneg_neg_iff, mul_neg, neg_mul, neg_neg,
                      forall_const, ge_iff_le]
                    apply Ht; grind
              | false =>
                  have H0ley2u : 0 ≤ toReal x2u := by
                    rw [←@zero_eq 𝔽]; exact le_real_correct.mp (nle_impl Hp2u)
                  simp_all only [Bool.false_eq_true, ↓reduceIte]
                  apply And.intro <;> simp only
                  · trans (min (toReal x1l * toReal x2u) (toReal x1u * toReal x2l))
                    · rw [min_real_correct]
                      apply inf_le_inf
                      · exact mul_down_real_correct
                      · exact mul_down_real_correct
                    · have Hs : 0≤y1 ∨ y1≤0 := Std.IsLinearPreorder.le_total 0 y1
                      cases Hs with
                      | inl Hp =>
                          apply inf_le_of_right_le
                          rw [mul_comm (toReal x1u) (toReal x2l), mul_comm y1 y2]
                          have Ht := @mul_le_mul _ _ _ _ (-y2) (-toReal x2l) (y1) (toReal x1u)
                          simp_all only [neg_le_neg_iff, Left.nonneg_neg_iff, neg_mul, forall_const]
                      | inr Hn =>
                          apply inf_le_of_left_le
                          rw [mul_comm (toReal x1l) (toReal x2u), mul_comm y1 y2]
                          have Ht := @mul_le_mul _ _ _ _ (y2) (toReal x2u) (-y1) (-toReal x1l)
                          simp_all only [neg_le_neg_iff, Left.nonneg_neg_iff, mul_neg, forall_const]
                  · trans (max (toReal x1l * toReal x2l) (toReal x1u * toReal x2u))
                    · have Hs : 0≤y1 ∨ y1≤0 := Std.IsLinearPreorder.le_total 0 y1
                      cases Hs with
                      | inl Hp =>
                          apply le_sup_of_le_right
                          rw [mul_comm (toReal x1u) (toReal x2u), mul_comm y1 y2]
                          have Ht := @mul_le_mul _ _ _ _ (y2) (toReal x2u) (y1) (toReal x1u)
                          simp_all only [forall_const]
                      | inr Hn =>
                          apply le_sup_of_le_left
                          rw [mul_comm (toReal x1l) (toReal x2l), mul_comm y1 y2]
                          have Ht := @mul_le_mul _ _ _ _ (-y2) (-toReal x2l) (-y1) (-toReal x1l)
                          simp_all only [neg_le_neg_iff, Left.nonneg_neg_iff, mul_neg, neg_mul,
                            neg_neg, forall_const]
                    · rw [max_real_correct]
                      apply sup_le_sup
                      · exact mul_up_real_correct
                      · exact mul_up_real_correct


theorem Bounds.mul_correct {𝔽 : Type}
    [Flt : RoundedFloatOperations 𝔽] [FltT : @RoundedFloatTheory 𝔽 _] :
  forall x1 x2 : Bounds 𝔽, forall y1 y2 : ℝ, x1.models y1 → x2.models y2 →
    (Bounds.mul x1 x2).models (y1*y2) :=
by
  intros x1 x2 y1 y2
  cases x1 with | mk x1l x1u =>
  cases x2 with | mk x2l x2u =>
    intros H1 H2
    unfold models at H1 H2
    simp_all only
    cases H1 with | intro H1l H1u =>
    cases H2 with | intro H2l H2u =>
      exact mul_correct' x1l x1u x2l x2u y1 y2 H1l H1u H2l H2u

theorem Bounds.abs_correct {𝔽 : Type}
    [Flt : RoundedFloatOperations 𝔽] [FltT : @RoundedFloatTheory 𝔽 _] :
  forall x : Bounds 𝔽, forall y : ℝ, x.models y →
    (Bounds.abs x).models |y| :=
by
  let Fneg := Flt.neg; have Eneg : Fneg = Flt.neg := by rfl
  let Fmax := Flt.max; have Emax : Fmax = Flt.max := by rfl
  let Fle := Flt.le; have Ele : Fle = Flt.le := by rfl
  unfold Bounds.models
  unfold Bounds.abs
  simp only [and_imp]
  intros x y Hl Hu
  rw [←Eneg,←Emax];
  cases Exl : Flt.le Flt.zero x.lower with
  | true =>
      unfold roundedFloatLE
      simp_all only [↓reduceIte]
      have H0ley : (0 ≤ y) := by
        transitivity (toReal x.lower)
        · rw [←@zero_eq 𝔽]
          apply le_real_correct.mp
          exact Exl
        · exact Hl
      rw [abs_of_nonneg H0ley]
      exact ⟨Hl, Hu⟩
  | false =>
      unfold roundedFloatLE
      simp_all only [Bool.false_eq, Bool.true_eq_false, ↓reduceIte]
      cases Exu : Flt.le x.upper Flt.zero with
      | true =>
          simp_all only [↓reduceIte]
          have Hyle0 : (y ≤ 0) := by
            transitivity (toReal x.upper)
            · exact Hu
            · rw [←@zero_eq 𝔽]
              apply le_real_correct.mp
              exact Exu
          rw [abs_of_nonpos Hyle0]
          apply And.intro
          · rw [neg_real_correct]
            exact neg_le_neg_iff.mpr Hu
          · rw [neg_real_correct]
            exact neg_le_neg_iff.mpr Hl
      | false =>
          simp_all only [Bool.false_eq, Bool.true_eq_false, ↓reduceIte]
          apply And.intro
          · rw [zero_eq]
            exact abs_nonneg y
          · have Hy0 : 0 ≤ y ∨ y ≤ 0 := Std.IsLinearPreorder.le_total 0 y
            cases Hy0 with
            | inl H0ley =>
                rw [abs_of_nonneg H0ley]
                rw [max_real_correct]
                transitivity (toReal x.upper)
                · exact Hu
                · exact Std.right_le_max
            | inr Hyle0 =>
                rw [abs_of_nonpos Hyle0]
                rw [max_real_correct]
                rw [neg_real_correct]
                transitivity (-toReal x.lower)
                · exact neg_le_neg_iff.mpr Hl
                · exact Std.left_le_max

end WithFloat

end RoundedBounds
