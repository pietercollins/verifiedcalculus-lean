/-
Copyright  2026  Pieter Collins
Released under the GNU GPLv3 as described in the file LICENSE.
Authors: Pieter Collins
-/

import Init.Data.Nat
import Init.Data.Int
import Init.Data.Dyadic
import Init.Data.Rat
import Init.Data.Float
import Mathlib.Data.Real.Basic

def Float.eps : Float := Float.scaleB (1.0) (-52)
#eval Float.eps * 2^52

def Float.toRat (x : Float) : Rat :=
  let me := Float.frExp x
  let p64 := Float.toInt64 (Float.scaleB me.fst 52)
  let p := p64.toInt
  let e := me.snd - 52
  let q := (2:ℚ)^e
  p * q

def Float.toReal : Float → Real := fun x => (x.toRat : ℝ)


namespace Floats.Rounded

inductive Rounding where | down | near | up

structure is_correctly_rounded {𝔽 : Type} (toRat : 𝔽 → ℚ) (x : Rounding → 𝔽) (q : ℚ) : Prop where
  down : toRat (x .down) ≤ q
  near : ∀ w : 𝔽, |toRat (x .near) - q| ≤ |toRat w - q|
  up   : toRat (x .up) ≥ q

def is_correct_unary {𝔽 : Type} (toRat : 𝔽 → ℚ)
    (fop : 𝔽 → 𝔽) (qop : ℚ → ℚ) : Prop :=
  ∀ x : 𝔽, toRat (fop x) = qop (toRat x)

def is_correct_binary_predicate {𝔽 : Type} (toRat : 𝔽 → ℚ)
    (fpr : 𝔽 → 𝔽 → Prop) (qpr : ℚ → ℚ → Prop) : Prop :=
  ∀ x1 x2 : 𝔽, fpr x1 x2 ↔ qpr (toRat x1) (toRat x2)

def is_correctly_rounded_unary {𝔽 : Type} (toRat : 𝔽 → ℚ)
    (fop : Rounding → 𝔽 → 𝔽) (qop : ℚ → ℚ) : Prop :=
  ∀ x : 𝔽, is_correctly_rounded toRat (fun r ↦ fop r x) (qop (toRat x))

def is_correctly_rounded_binary {𝔽 : Type} (toRat : 𝔽 → ℚ)
    (fop : Rounding → 𝔽 → 𝔽 → 𝔽) (qop : ℚ → ℚ → ℚ) : Prop :=
  ∀ x1 x2 : 𝔽, is_correctly_rounded toRat (fun r ↦ fop r x1 x2) (qop (toRat x1) (toRat x2))

def is_correctly_rounded_binary_nonzero {𝔽 : Type} (ofNat : ℕ → 𝔽) (toRat : 𝔽 → ℚ)
    (fop : Rounding → 𝔽 → 𝔽 → 𝔽) (qop : ℚ → ℚ → ℚ) : Prop :=
  ∀ x1 x2 : 𝔽, x2 ≠ ofNat 0 →
    is_correctly_rounded toRat (fun r ↦ fop r x1 x2) (qop (toRat x1) (toRat x2))

class RoundedFloatOperations (𝔽 : Type) : Type where
  ofNat : ℕ → 𝔽
  toRat : 𝔽 → ℚ
  neg : 𝔽 → 𝔽
  abs : 𝔽 → 𝔽
  le : 𝔽 → 𝔽 → Prop
  add : Rounding → 𝔽 → 𝔽 → 𝔽
  sub : Rounding → 𝔽 → 𝔽 → 𝔽
  mul : Rounding → 𝔽 → 𝔽 → 𝔽
  div : Rounding → 𝔽 → 𝔽 → 𝔽

structure RoundedFloatTheory {𝔽 : Type} [Flt : RoundedFloatOperations 𝔽] : Prop where
  ofNat_correct : ∀ n, Flt.toRat (Flt.ofNat n) = (n : ℚ)
  neg_correct : is_correct_unary Flt.toRat Flt.neg Rat.neg
  abs_correct : is_correct_unary Flt.toRat Flt.abs (fun q : ℚ ↦ |q|)
  le_correct :  is_correct_binary_predicate Flt.toRat Flt.le (fun q1 q2 : ℚ ↦ q1 ≤ q2)
  add_correct : is_correctly_rounded_binary Flt.toRat Flt.add Rat.add
  sub_correct : is_correctly_rounded_binary Flt.toRat Flt.sub Rat.sub
  mul_correct : is_correctly_rounded_binary Flt.toRat Flt.mul Rat.mul
  div_correct : is_correctly_rounded_binary_nonzero Flt.ofNat Flt.toRat Flt.div Rat.div
  add_down_correct : ∀ x1 x2, Flt.toRat (Flt.add .down x1 x2) <= Flt.toRat x1 + Flt.toRat x2 :=
    fun x1 x2 => (add_correct x1 x2).down

def next_down (x : Float) : Float := x - x.abs * Float.eps
def next_up (x : Float) : Float := x + x.abs * Float.eps

def Float.add_near (x1 x2 : Float) : Float := x1 + x2
def Float.add_up (x1 x2 : Float) : Float := next_up (x1 + x2)
def Float.add_down (x1 x2 : Float) : Float := next_down (x1 + x2)
def Float.sub_near (x1 x2 : Float) : Float := x1 - x2
def Float.sub_up (x1 x2 : Float) : Float := next_up (x1 - x2)
def Float.sub_down (x1 x2 : Float) : Float := next_down (x1 - x2)
def Float.mul_near (x1 x2 : Float) : Float := x1 * x2
def Float.mul_up (x1 x2 : Float) : Float := next_up (x1 * x2)
def Float.mul_down (x1 x2 : Float) : Float := next_down (x1 * x2)
def Float.div_near (x1 x2 : Float) : Float := x1 / x2
def Float.div_up (x1 x2 : Float) : Float := next_up (x1 / x2)
def Float.div_down (x1 x2 : Float) : Float := next_down (x1 / x2)

def Float.add (rnd : Rounding) :=
  match rnd with | .down => add_down | .near => add_near | .up => add_up
def Float.sub (rnd : Rounding) :=
  match rnd with | .down => sub_down | .near => sub_near | .up => sub_up
def Float.mul (rnd : Rounding) :=
  match rnd with | .down => mul_down | .near => mul_near | .up => mul_up
def Float.div (rnd : Rounding) :=
  match rnd with | .down => div_down | .near => div_near | .up => div_up


def Rat.dist (x1 x2 : Rat) : Rat := |x1-x2|


instance roundedFloat64Operations : RoundedFloatOperations Float where
  ofNat := Float.ofNat
  toRat := Float.toRat
  neg := Float.neg
  abs := Float.abs
  le := Float.le
  add := Float.add
  sub := Float.sub
  mul := Float.mul
  div := Float.div

axiom roundedFloat64Correct : @RoundedFloatTheory Float roundedFloat64Operations

#check roundedFloat64Correct

theorem Float.correctly_rounded_near (x : Rounding → Float) (q : Rat) :
  is_correctly_rounded Float.toRat x q
    → |(x .near).toRat - q| ≤ ( (x .up).toRat - (x .down).toRat ) / 2
:= by
  intros H
  have Hu := H.up; have Hd := H.down; have Hn := H.near; clear H;
  set xd := x .down; set xn := x .near; set xu := x .up
  simp_all only [ge_iff_le]
  /- grind -/
  suffices |xn.toRat - q| + |xn.toRat - q| ≤ xu.toRat - xd.toRat by grind
  transitivity |xu.toRat - q| + |xd.toRat - q|
  · have Hnu : |xn.toRat - q| ≤ |xu.toRat - q| := Hn xu
    have Hnd : |xn.toRat - q| ≤ |xd.toRat - q| := Hn xd
    exact add_le_add Hnu Hnd
  · have Hua : |xu.toRat - q| = (xu.toRat - q) := by grind
    have Hda : |xd.toRat - q| = (q - xd.toRat) := by grind
    rewrite [Hua,Hda]; grind


theorem Float.ofNat_correct : ∀ (n : ℕ), (Float.ofNat n).toRat = (n:ℚ) :=
  roundedFloat64Correct.ofNat_correct
theorem Float.neg_correct : ∀ (x : Float), x.neg.toRat = -(x.toRat) :=
  roundedFloat64Correct.neg_correct
theorem Float.abs_correct : ∀ (x : Float), x.abs.toRat = |x.toRat| :=
  roundedFloat64Correct.abs_correct
theorem Float.le_correct : ∀ (x1 x2 : Float), x1 ≤ x2 ↔ x1.toRat ≤ x2.toRat :=
  roundedFloat64Correct.le_correct

theorem Float.add_correct : is_correctly_rounded_binary Float.toRat Float.add Rat.add :=
  roundedFloat64Correct.add_correct
theorem Float.sub_correct : is_correctly_rounded_binary Float.toRat Float.sub Rat.sub :=
  roundedFloat64Correct.sub_correct
theorem Float.mul_correct : is_correctly_rounded_binary Float.toRat Float.mul Rat.mul :=
  roundedFloat64Correct.mul_correct
theorem Float.div_correct : is_correctly_rounded_binary_nonzero Float.ofNat Float.toRat
                                                                  Float.div Rat.div :=
  roundedFloat64Correct.div_correct




theorem Float.add_down_correct : ∀ x1 x2, (Float.add_down x1 x2).toRat <= x1.toRat + x2.toRat :=
  fun x1 x2 => (add_correct x1 x2).down
theorem Float.sub_down_correct : ∀ x1 x2, (Float.sub_down x1 x2).toRat <= x1.toRat - x2.toRat :=
  fun x1 x2 => (sub_correct x1 x2).down
theorem Float.mul_down_correct : ∀ x1 x2, (Float.mul_down x1 x2).toRat <= x1.toRat * x2.toRat :=
  fun x1 x2 => (mul_correct x1 x2).down
theorem Float.div_down_correct : ∀ x1 x2, x2 ≠ Float.ofNat 0 →
    (Float.div_down x1 x2).toRat <= x1.toRat / x2.toRat :=
  fun x1 x2 Hx2 => (div_correct x1 x2 Hx2).down

theorem Float.add_near_correct : ∀ x1 x2, let q := x1.toRat + x2.toRat
  ∀ w : Float, |(Float.add_near x1 x2).toRat - q| ≤ |w.toRat - q| :=
    fun x1 x2 => (add_correct x1 x2).near
theorem Float.sub_near_correct : ∀ x1 x2, ∀ w : Float,
   |(Float.sub_near x1 x2).toRat - (x1.toRat - x2.toRat)| ≤ |w.toRat - (x1.toRat - x2.toRat)| :=
  fun x1 x2 => (sub_correct x1 x2).near


theorem Float.zero_le_correct : ∀ (x : Float), 0 <= x → 0 ≤ x.toRat := by
  have Hz : (0 : ℚ) = (Float.ofNat (0:ℕ)).toRat := by
    rewrite [ofNat_correct 0]; simp only [Nat.cast_zero]
  rewrite [Hz]; exact fun x ↦ (le_correct (Float.ofNat 0) x).mp

theorem Float.ofNat_toRat : ∀ n1 n2 : ℕ, Float.ofNat n1 = Float.ofNat n2 → (n1 : ℚ) = (n2 : ℚ) := by
  intros n1 n2 Hx
  rewrite [←ofNat_correct n1,←ofNat_correct n2]
  rw [Hx]

theorem Float.ofNat_inj : ∀ {n1 n2 : ℕ}, Float.ofNat n1 = Float.ofNat n2 → n1 = n2 := by
  intros n1 n2 Hx
  have  Hr : (n1 : ℚ) = (n2 : ℚ) := ofNat_toRat n1 n2 Hx
  exact Rat.natCast_inj.mp Hr


theorem Float.add_down_le : ∀ {x1 x2 r1 r2},
  x1.toRat ≤ r1 → x2.toRat ≤ r2 → (Float.add_down x1 x2).toRat ≤ r1 + r2
:= by
  intros x1 x2 r1 r2 H1 H2
  trans (x1.toRat + x2.toRat)
  · exact Float.add_down_correct x1 x2
  · exact add_le_add H1 H2

theorem Float.add_down_le_l : ∀ {x1 x2 r1},
  x1.toRat ≤ r1 → (add_down x1 x2).toRat ≤ r1 + x2.toRat
:= by
  intros x1 x2 r1 H1; apply Float.add_down_le H1 _; exact Rat.le_refl

theorem Float.add_down_le_r : ∀ {x1 x2 r2},
  x2.toRat ≤ r2 → (add_down x1 x2).toRat ≤ x1.toRat + r2
:= by
  intros x1 x2 r2 H2; apply Float.add_down_le _ H2; exact Rat.le_refl

theorem Float.sub_down_le : ∀ {x1 x2 r1 r2},
  x1.toRat ≤ r1 → r2 ≤ x2.toRat → (sub_down x1 x2).toRat ≤ r1 - r2
:= by
  intros x1 x2 r1 r2 H1 H2
  trans (x1.toRat - x2.toRat)
  · exact sub_down_correct x1 x2
  · exact tsub_le_tsub H1 H2

theorem Float.mul_down_le : ∀ {x1 x2 r1 r2},
  0 ≤ x1 → 0 ≤ x2 → x1.toRat ≤ r1 → x2.toRat ≤ r2 → (mul_down x1 x2).toRat ≤ r1 * r2
:= by
  intros x1 x2 r1 r2 H01 H02 H1 H2
  have H01r : 0 ≤ x1.toRat := by exact zero_le_correct x1 H01
  have H02r : 0 ≤ x2.toRat := by exact zero_le_correct x2 H02
  have H0r1 : 0 ≤ r1 := by exact Rat.le_trans H01r H1
  trans (x1.toRat * x2.toRat)
  · exact mul_down_correct x1 x2
  · trans (r1 * x2.toRat)
    · exact Rat.mul_le_mul_of_nonneg_right H1 H02r
    · exact Rat.mul_le_mul_of_nonneg_left H2 H0r1

theorem Float.mul_down_le_l : ∀ {x1 r2 x3},
  0 ≤ x3 → x1.toRat ≤ r2 → (mul_down x1 x3).toRat ≤ r2 * x3.toRat
:= by
  intros x1 r2 x3 H03 H12
  have H03r : 0 ≤ x3.toRat := by exact zero_le_correct x3 H03
  trans (x1.toRat * x3.toRat)
  · exact mul_down_correct x1 x3
  · exact Rat.mul_le_mul_of_nonneg_right H12 H03r

theorem Float.mul_down_le_r : ∀ {x1 x2 r3},
  0 ≤ x1 → x2.toRat ≤ r3 → (mul_down x1 x2).toRat ≤ x1.toRat * r3
:= by
  intros x1 x2 r3 H01 H23
  have H01r : 0 ≤ x1.toRat := by exact zero_le_correct x1 H01
  trans (x1.toRat * x2.toRat)
  · exact mul_down_correct x1 x2
  · exact PosMulMono.mul_le_mul_of_nonneg_left H01r H23


theorem Float.exp_approx_down' :
  ∀ x : Float, 0 <= x →
    Float.toRat (add_down 1 (Float.mul_down x (add_down 1 (div_down x 2))))
      <= 1 + x.toRat * (1 + x.toRat / 2)
:= by
  intro x Hx
  set r := x.toRat
  have Hr : 0 <= r := by exact zero_le_correct x Hx
  set one : Float := 1
  set two : Float := 2
  have Hone : one.toRat = 1 := by unfold one; exact ofNat_correct 1
  have Htwo : two.toRat = 2 := by unfold two; exact ofNat_correct 2
  have Htwo_ne_0 : two ≠ 0 := by intro Htwo; apply Float.ofNat_inj at Htwo; contradiction
  /- (div_down x 2).toRat <= r / 2 -/
  have p1 := Float.div_down_correct x two Htwo_ne_0
  /- (add_down one (div_down x two)).toRat <= 1 + r / 2 -/
  have p2 := @add_down_le_r one _ _ p1
  /- (mul_down x (add_down one (div_down x two))).toRat <= r * (1 + r / 2) -/
  have p3 := mul_down_le_r Hx p2
  /- (add_down one (mul_down x (add_down one (div_down x two)))).toRat <= 1 + r * (1 + r / 2) -/
  have p4 := @add_down_le_r one _ _ p3
  rewrite [Hone,Htwo] at p4
  exact p4

theorem Float.exp_approx_down :
  ∀ x : Float, 0 <= x →
    (add_down 1 (mul_down x (add_down 1 (div_down x 2)))).toRat
      <= 1 + x.toRat * (1 + x.toRat / 2)
:= by
  intro x Hx
  set r := x.toRat; have Hr : 0 <= r := zero_le_correct x Hx
  have QtoFloat (n:ℕ) : (@OfNat.ofNat ℚ n Rat.instOfNat) = (Float.ofNat n).toRat := by
    rw [ofNat_correct]; rfl
  have H2ne0 : (2:Float) ≠ 0 := by intro Htwo; apply Float.ofNat_inj at Htwo; contradiction
  rewrite [QtoFloat 1, QtoFloat 2]
  apply add_down_le_r
  apply mul_down_le_r Hx
  apply add_down_le_r
  apply div_down_correct _ _ H2ne0

end Floats.Rounded
