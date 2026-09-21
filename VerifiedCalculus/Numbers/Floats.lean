/-
Copyright  2026  Pieter Collins
Released under the GNU GPLv3 as described in the file LICENSE.
Authors: Pieter Collins
-/

import Mathlib.Tactic.Linter.Style

import Init.Data.Nat
import Init.Data.Int
import Init.Data.Dyadic
import Init.Data.Rat
import Init.Data.Float.Float
import Init.Data.Float.Float32
import Mathlib.Data.Real.Basic

import Init.Data.Float.Model.Format.Valid
import Init.Data.Float.Model.Unpacked.Pack.Basic
import Init.Data.Float.Model.Unpacked.Pack.Lemmas

set_option linter.style.header false

notation "𝔹" => Bool

abbrev Float64 := Float
abbrev Float64.ofNat : Nat → Float64 := Float.ofNat
abbrev Float64.toInt64 : Float64 → Int64 := Float.toInt64
abbrev Float64.frExp : Float64 → Float64 × Int := Float.frExp
abbrev Float64.scaleB : Float64 → Int → Float64 := Float.scaleB
abbrev Float64.neg : Float64 → Float64 := Float.neg
abbrev Float64.abs : Float64 → Float64 := Float.abs
abbrev Float64.le : Float64 → Float64 → Bool := Float.le


def Float32.eps : Float32 := Float32.scaleB (1.0) (-23)
def Float64.eps : Float64 := Float64.scaleB (1.0) (-52)


def Float32.toDyadic (x : Float32) : Dyadic :=
  let me := Float32.frExp x
  let p32 := Float32.toInt32 (Float32.scaleB me.fst 23)
  let p := p32.toInt
  let e := me.snd - 23
  Dyadic.shiftLeft (Dyadic.ofInt p) e

def Float32.toRat (x : Float32) : Rat := x.toDyadic.toRat

def Float32.toReal (x : Float32) : Real := (x.toRat : ℝ)

def Float64.toDyadic (x : Float64) : Dyadic :=
  let me := Float64.frExp x
  let p64 := Float64.toInt64 (Float64.scaleB me.fst 52)
  let p := p64.toInt
  let e := me.snd - 52
  Dyadic.shiftLeft (Dyadic.ofInt p) e

def Float64.toRat (x : Float64) : Rat := x.toDyadic.toRat

def Float64.toReal (x : Float64) : Real := (x.toRat : ℝ)


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
    (fpr : 𝔽 → 𝔽 → 𝔹) (qpr : ℚ → ℚ → Prop) : Prop :=
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
  le : 𝔽 → 𝔽 → 𝔹
  add : Rounding → 𝔽 → 𝔽 → 𝔽
  sub : Rounding → 𝔽 → 𝔽 → 𝔽
  mul : Rounding → 𝔽 → 𝔽 → 𝔽
  div : Rounding → 𝔽 → 𝔽 → 𝔽
  min : 𝔽 → 𝔽 → 𝔽 := fun x1 x2 => if le x1 x2 then x1 else x2
  max : 𝔽 → 𝔽 → 𝔽 := fun x1 x2 => if le x1 x2 then x2 else x1
  zero := ofNat 0

class RoundedFloatTheory {𝔽 : Type} [Flt : RoundedFloatOperations 𝔽] : Prop where
  ofNat_correct : ∀ n, Flt.toRat (Flt.ofNat n) = (n : ℚ)
  neg_correct : is_correct_unary Flt.toRat Flt.neg Rat.neg
  abs_correct : is_correct_unary Flt.toRat Flt.abs (fun q : ℚ ↦ |q|)
  le_correct :  is_correct_binary_predicate Flt.toRat Flt.le (fun q1 q2 : Rat ↦ q1 ≤ q2)
  add_correct : is_correctly_rounded_binary Flt.toRat Flt.add Rat.add
  sub_correct : is_correctly_rounded_binary Flt.toRat Flt.sub Rat.sub
  mul_correct : is_correctly_rounded_binary Flt.toRat Flt.mul Rat.mul
  div_correct : is_correctly_rounded_binary_nonzero Flt.ofNat Flt.toRat Flt.div Rat.div
  add_down_correct : ∀ x1 x2, Flt.toRat (Flt.add .down x1 x2) <= Flt.toRat x1 + Flt.toRat x2 :=
    fun x1 x2 => (add_correct x1 x2).down

instance roundedFloatLE
    {𝔽 : Type} [Flt : RoundedFloatOperations 𝔽] [@RoundedFloatTheory 𝔽 Flt] : LE 𝔽 where
  le := fun x1 x2 ↦ Flt.le x1 x2 = true

instance roundedFloatLEDecidable
      {𝔽 : Type} [Flt : RoundedFloatOperations 𝔽] [@RoundedFloatTheory 𝔽 Flt] (x1 x2 : 𝔽)
  : Decidable (x1 ≤ x2) := (RoundedFloatOperations.le x1 x2).decEq true

instance roundedFloatNeg
    {𝔽 : Type} [Flt : RoundedFloatOperations 𝔽] [@RoundedFloatTheory 𝔽 Flt] : Neg 𝔽 where
  neg := Flt.neg


def next_down (x : Float64) : Float64 := x - x.abs * Float64.eps
def next_up (x : Float64) : Float64 := x + x.abs * Float64.eps

def Float64.add_near (x1 x2 : Float64) : Float64 := x1 + x2
def Float64.add_up (x1 x2 : Float64) : Float64 := next_up (x1 + x2)
def Float64.add_down (x1 x2 : Float64) : Float64 := next_down (x1 + x2)
def Float64.sub_near (x1 x2 : Float64) : Float64 := x1 - x2
def Float64.sub_up (x1 x2 : Float64) : Float64 := next_up (x1 - x2)
def Float64.sub_down (x1 x2 : Float64) : Float64 := next_down (x1 - x2)
def Float64.mul_near (x1 x2 : Float64) : Float64 := x1 * x2
def Float64.mul_up (x1 x2 : Float64) : Float64 := next_up (x1 * x2)
def Float64.mul_down (x1 x2 : Float64) : Float64 := next_down (x1 * x2)
def Float64.div_near (x1 x2 : Float64) : Float64 := x1 / x2
def Float64.div_up (x1 x2 : Float64) : Float64 := next_up (x1 / x2)
def Float64.div_down (x1 x2 : Float64) : Float64 := next_down (x1 / x2)

def Float64.add (rnd : Rounding) :=
  match rnd with | .down => add_down | .near => add_near | .up => add_up
def Float64.sub (rnd : Rounding) :=
  match rnd with | .down => sub_down | .near => sub_near | .up => sub_up
def Float64.mul (rnd : Rounding) :=
  match rnd with | .down => mul_down | .near => mul_near | .up => mul_up
def Float64.div (rnd : Rounding) :=
  match rnd with | .down => div_down | .near => div_near | .up => div_up



instance roundedFloat64Operations : RoundedFloatOperations Float64 where
  ofNat := Float64.ofNat
  toRat := Float64.toRat
  neg := Float64.neg
  abs := Float64.abs
  le := Float64.le
  add := Float64.add
  sub := Float64.sub
  mul := Float64.mul
  div := Float64.div

axiom roundedFloat64Correct : @RoundedFloatTheory Float64 roundedFloat64Operations

instance roundedFloat64Theory : @RoundedFloatTheory Float64 roundedFloat64Operations :=
  roundedFloat64Correct

#check roundedFloat64Operations
#check roundedFloat64Correct
#check roundedFloat64Theory

theorem Float64.correctly_rounded_near (x : Rounding → Float64) (q : Rat) :
  is_correctly_rounded Float64.toRat x q
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


theorem Float64.ofNat_correct : ∀ (n : ℕ), (Float64.ofNat n).toRat = (n:ℚ) :=
  roundedFloat64Correct.ofNat_correct
theorem Float64.neg_correct : ∀ (x : Float64), x.neg.toRat = -(x.toRat) :=
  roundedFloat64Correct.neg_correct
theorem Float64.abs_correct : ∀ (x : Float64), x.abs.toRat = |x.toRat| :=
  roundedFloat64Correct.abs_correct
theorem Float64.le_correct : ∀ (x1 x2 : Float64), (Float64.le x1 x2) ↔ (x1.toRat ≤ x2.toRat) :=
  roundedFloat64Correct.le_correct
theorem Float64.le_prop_correct : ∀ (x1 x2 : Float64), x1 ≤ x2 ↔ (x1.toRat ≤ x2.toRat) :=
  roundedFloat64Correct.le_correct

theorem Float64.add_correct : is_correctly_rounded_binary Float64.toRat Float64.add Rat.add :=
  roundedFloat64Correct.add_correct
theorem Float64.sub_correct : is_correctly_rounded_binary Float64.toRat Float64.sub Rat.sub :=
  roundedFloat64Correct.sub_correct
theorem Float64.mul_correct : is_correctly_rounded_binary Float64.toRat Float64.mul Rat.mul :=
  roundedFloat64Correct.mul_correct
theorem Float64.div_correct : is_correctly_rounded_binary_nonzero Float64.ofNat Float64.toRat
                                                                  Float64.div Rat.div :=
  roundedFloat64Correct.div_correct




theorem Float64.add_down_correct : ∀ x1 x2, (Float64.add_down x1 x2).toRat <= x1.toRat + x2.toRat :=
  fun x1 x2 => (add_correct x1 x2).down
theorem Float64.sub_down_correct : ∀ x1 x2, (Float64.sub_down x1 x2).toRat <= x1.toRat - x2.toRat :=
  fun x1 x2 => (sub_correct x1 x2).down
theorem Float64.mul_down_correct : ∀ x1 x2, (Float64.mul_down x1 x2).toRat <= x1.toRat * x2.toRat :=
  fun x1 x2 => (mul_correct x1 x2).down
theorem Float64.div_down_correct : ∀ x1 x2, x2 ≠ Float64.ofNat 0 →
    (Float64.div_down x1 x2).toRat <= x1.toRat / x2.toRat :=
  fun x1 x2 Hx2 => (div_correct x1 x2 Hx2).down

theorem Float64.add_near_correct : ∀ x1 x2, let q := x1.toRat + x2.toRat
  ∀ w : Float64, |(Float64.add_near x1 x2).toRat - q| ≤ |w.toRat - q| :=
    fun x1 x2 => (add_correct x1 x2).near
theorem Float64.sub_near_correct : ∀ x1 x2, ∀ w : Float64,
   |(Float64.sub_near x1 x2).toRat - (x1.toRat - x2.toRat)| ≤ |w.toRat - (x1.toRat - x2.toRat)| :=
  fun x1 x2 => (sub_correct x1 x2).near


theorem Float64.zero_le_correct : ∀ (x : Float64), 0 ≤ x → 0 ≤ x.toRat := by
  have Hz : (0 : ℚ) = (Float64.ofNat (0:ℕ)).toRat := by
    rewrite [ofNat_correct 0]; simp only [Nat.cast_zero]
  rewrite [Hz]; exact fun x ↦ (le_correct (Float64.ofNat 0) x).mp

theorem Float64.ofNat_toRat : ∀ n1 n2 : ℕ,
    Float64.ofNat n1 = Float64.ofNat n2 → (n1 : ℚ) = (n2 : ℚ) := by
  intros n1 n2 Hx
  rewrite [←ofNat_correct n1,←ofNat_correct n2]
  rw [Hx]

theorem Float64.ofNat_inj : ∀ {n1 n2 : ℕ}, Float64.ofNat n1 = Float64.ofNat n2 → n1 = n2 := by
  intros n1 n2 Hx
  have  Hr : (n1 : ℚ) = (n2 : ℚ) := ofNat_toRat n1 n2 Hx
  exact Rat.natCast_inj.mp Hr


theorem Float64.add_down_le : ∀ {x1 x2 r1 r2},
  x1.toRat ≤ r1 → x2.toRat ≤ r2 → (Float64.add_down x1 x2).toRat ≤ r1 + r2
:= by
  intros x1 x2 r1 r2 H1 H2
  trans (x1.toRat + x2.toRat)
  · exact Float64.add_down_correct x1 x2
  · exact add_le_add H1 H2

theorem Float64.add_down_le_l : ∀ {x1 x2 r1},
  x1.toRat ≤ r1 → (add_down x1 x2).toRat ≤ r1 + x2.toRat
:= by
  intros x1 x2 r1 H1; apply Float64.add_down_le H1 _; exact Rat.le_refl

theorem Float64.add_down_le_r : ∀ {x1 x2 r2},
  x2.toRat ≤ r2 → (add_down x1 x2).toRat ≤ x1.toRat + r2
:= by
  intros x1 x2 r2 H2; apply Float64.add_down_le _ H2; exact Rat.le_refl

theorem Float64.sub_down_le : ∀ {x1 x2 r1 r2},
  x1.toRat ≤ r1 → r2 ≤ x2.toRat → (sub_down x1 x2).toRat ≤ r1 - r2
:= by
  intros x1 x2 r1 r2 H1 H2
  trans (x1.toRat - x2.toRat)
  · exact sub_down_correct x1 x2
  · exact tsub_le_tsub H1 H2

theorem Float64.mul_down_le : ∀ {x1 x2 r1 r2},
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

theorem Float64.mul_down_le_l : ∀ {x1 r2 x3},
  0 ≤ x3 → x1.toRat ≤ r2 → (mul_down x1 x3).toRat ≤ r2 * x3.toRat
:= by
  intros x1 r2 x3 H03 H12
  have H03r : 0 ≤ x3.toRat := by exact zero_le_correct x3 H03
  trans (x1.toRat * x3.toRat)
  · exact mul_down_correct x1 x3
  · exact Rat.mul_le_mul_of_nonneg_right H12 H03r

theorem Float64.mul_down_le_r : ∀ {x1 x2 r3},
  0 ≤ x1 → x2.toRat ≤ r3 → (mul_down x1 x2).toRat ≤ x1.toRat * r3
:= by
  intros x1 x2 r3 H01 H23
  have H01r : 0 ≤ x1.toRat := by exact zero_le_correct x1 H01
  trans (x1.toRat * x2.toRat)
  · exact mul_down_correct x1 x2
  · exact PosMulMono.mul_le_mul_of_nonneg_left H01r H23


theorem Float64.exp_approx_down' :
  ∀ x : Float64, 0 <= x →
    Float64.toRat (add_down 1 (Float64.mul_down x (add_down 1 (div_down x 2))))
      <= 1 + x.toRat * (1 + x.toRat / 2)
:= by
  intro x Hx
  set r := x.toRat
  have Hr : 0 <= r := by exact zero_le_correct x Hx
  set one : Float64 := 1
  set two : Float64 := 2
  have Hone : one.toRat = 1 := by unfold one; exact ofNat_correct 1
  have Htwo : two.toRat = 2 := by unfold two; exact ofNat_correct 2
  have Htwo_ne_0 : two ≠ 0 := by intro Htwo; apply Float64.ofNat_inj at Htwo; contradiction
  /- (div_down x 2).toRat <= r / 2 -/
  have p1 := Float64.div_down_correct x two Htwo_ne_0
  /- (add_down one (div_down x two)).toRat <= 1 + r / 2 -/
  have p2 := @add_down_le_r one _ _ p1
  /- (mul_down x (add_down one (div_down x two))).toRat <= r * (1 + r / 2) -/
  have p3 := mul_down_le_r Hx p2
  /- (add_down one (mul_down x (add_down one (div_down x two)))).toRat <= 1 + r * (1 + r / 2) -/
  have p4 := @add_down_le_r one _ _ p3
  rewrite [Hone,Htwo] at p4
  exact p4

theorem Float64.exp_approx_down :
  ∀ x : Float64, 0 <= x →
    (add_down 1 (mul_down x (add_down 1 (div_down x 2)))).toRat
      <= 1 + x.toRat * (1 + x.toRat / 2)
:= by
  intro x Hx
  set r := x.toRat; have Hr : 0 <= r := zero_le_correct x Hx
  have QtoFloat (n:ℕ) : (@OfNat.ofNat ℚ n Rat.instOfNat) = (Float64.ofNat n).toRat := by
    rw [ofNat_correct]; rfl
  have H2ne0 : (2:Float64) ≠ 0 := by intro Htwo; apply Float64.ofNat_inj at Htwo; contradiction
  rewrite [QtoFloat 1, QtoFloat 2]
  apply add_down_le_r
  apply mul_down_le_r Hx
  apply add_down_le_r
  apply div_down_correct _ _ H2ne0

end Floats.Rounded


namespace Floats.Specification

#print Float.Model.Format
#print Float.Model.Format.exponentBits
#print Float.Model.Format.mantissaBitsWithoutImplicit
#print Float.Model.Format.mantissaBits
#print Float.Model.Format.Valid
#print Float.Model.Format.numBits

#check Float.Model.UnpackedFloat.unpackMantissa_packComponents

open Float.Model
open Float.Model.UnpackedFloat

#print Fin
#print BitVec
#check unpackMantissa_packComponents
#check unpackExponent_packComponents
#check valid_pack

def x : Float32 := 1.0625
#eval x
#eval x.toModel
#eval Float32.ofModel (x.toModel)
def ux := x.toModel.unpack
def y : Float32 := 1048576.75
#eval y
def uy := y.toModel.unpack
#eval ux

#eval Format.binary32
#eval Format.binary64

#eval x.toDyadic

#eval (x+y)
def uz := UnpackedFloat.add Format.binary32 ux uy
#eval uz
#eval UnpackedFloat.pack Format.binary32 uz
#eval Float32.Model.pack uz
#eval Float32.ofModel (Float32.Model.pack uz)
#eval Float32.ofModel (x.toModel + y.toModel)

#eval (x+y).toDyadic
#eval x.toDyadic + y.toDyadic

#print Float32

#eval x

theorem float32_add_correct : forall x y : Float32,
  x.add y = Float32.ofModel (x.toModel + y.toModel) :=
by
  intros x y
  unfold Float32.add
  rfl

def Float.Model.UnpackedFloat.is_finite : UnpackedFloat → Prop
  | .finite _ _ _ _ => True
  | _ => False

def Float.Model.UnpackedFloat.toDyadic (ux : UnpackedFloat)
    (p : Float.Model.UnpackedFloat.is_finite ux) : Dyadic :=
  match ux with
  | .finite _s m e _ => Dyadic.shiftLeft (Dyadic.ofInt m) e
  | _ => Dyadic.ofInt 0


#eval ux

theorem ux_finite : Float.Model.UnpackedFloat.is_finite ux := by
  unfold Float.Model.UnpackedFloat.is_finite
  unfold ux x
  unfold Float32.toModel
  unfold Float32.Model.unpack
  sorry


#eval! Float.Model.UnpackedFloat.toDyadic ux ux_finite
#eval x.toDyadic

theorem float32_to_dyadic_correct : forall x y : Float32,
  1 ≤ x → x < 2 → 1 ≤ y → y < 2 → y < x →
    (x-y).toDyadic = x.toDyadic - y.toDyadic :=
by
  sorry


theorem float32_sub_unit_exact : forall x y : Float32,
  1 ≤ x → x < 2 → 1 ≤ y → y < 2 → y < x →
    (x-y).toDyadic = x.toDyadic - y.toDyadic :=
by
  sorry

end Floats.Specification
