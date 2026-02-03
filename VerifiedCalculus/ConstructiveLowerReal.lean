import Init.Data.Dyadic

import VerifiedCalculus.Dyadic

#print Dyadic

private theorem Dyadic.abs_sub (x y : Dyadic) : abs (x-y) = abs (y-x) := by
  rw [←Dyadic.abs_neg]; congr; exact neg_sub x y

theorem Dyadic.comp_shiftLeft : forall (w : Dyadic) (n1 n2 : Int) ,
  Dyadic.shiftLeft ( Dyadic.shiftLeft w n1) n2 = Dyadic.shiftLeft w (n1+n2) := by
  unfold Dyadic.shiftLeft
  intro w n1 n2
  cases w
  · case zero => simp only [Dyadic.zero_eq]
  · case ofOdd z k Hz => grind only


namespace ConstructiveLowerReals

open Dyadic

def is_increasing (xs : Nat -> Dyadic) : Prop :=
  forall n1 n2, n1 <= n2 -> xs n1 <= xs n2

def equivalent_sequences (xs1 xs2 : Nat → Dyadic) : Prop :=
  forall w : Dyadic, zero < w →
    exists m : Nat, forall l, l ≥ m → Dyadic.abs (xs1 l - xs2 l) ≤ w

theorem equivalent_sequences_refl :
    forall (xs : Nat → Dyadic), equivalent_sequences xs xs := by
  unfold equivalent_sequences
  intro xs w Hw
  exists 0
  intro l l_le_zero
  have diff_zero : xs l - xs l = zero := by exact sub_self (xs l)
  rw [diff_zero]
  unfold Dyadic.abs
  simp only [Dyadic.zero_eq, ge_iff_le]
  exact le_of_lt Hw

theorem equivalent_sequences_symm :
  forall {xs ys : Nat → Dyadic},
    equivalent_sequences xs ys → equivalent_sequences ys xs := by
  unfold equivalent_sequences
  intro xs ys H w Hw
  have Hm := H w Hw
  cases Hm
  · case intro m Hm =>
    exists m
    intros l Hlm
    have Hl := Hm l Hlm
    have abs_eq : Dyadic.abs (xs l - ys l) = Dyadic.abs (ys l - xs l) := by
      rw [←Dyadic.abs_neg]; congr; exact neg_sub (xs l) (ys l)
    rw [←abs_eq]
    exact Hl

open Dyadic

theorem equivalent_sequences_trans :
  forall {xs ys zs : Nat → Dyadic},
    equivalent_sequences xs ys → equivalent_sequences ys zs →
      equivalent_sequences xs zs := by
  let two_exp := Dyadic.two_exp /- Should not be needed -/
  unfold equivalent_sequences
  intro xs ys zs Hxy Hyz
  intro w Hw
  let hw := w.shiftRight 1
  have Hhw : zero < hw := by sorry
  have Hthw : hw + hw = w := by sorry
  replace Hxy := Hxy hw Hhw
  replace Hyz := Hyz hw Hhw
  cases Hxy
  · case intro m1 Hm1 =>
    cases Hyz
    · case intro m2 Hm2 =>
      let m := Max.max m1 m2
      exists m
      intro l Hml
      have Hlm1 : l ≥ m1 := by exact le_of_max_le_left Hml
      have Hlm2 : l ≥ m2 := by exact le_of_max_le_right Hml
      have abs_tri : (xs l - zs l).abs ≤  (xs l - ys l).abs + (ys l - zs l).abs := by
        have sum_diff : (xs l - zs l) = (xs l - ys l) + (ys l - zs l) := by sorry
        rw [sum_diff]
        exact Dyadic.abs_add (xs l - ys l) (ys l - zs l)
      have abs_sum' : (xs l - ys l).abs + (ys l - zs l).abs ≤ (xs l - ys l).abs + hw := by
        exact add_le_add_left.mpr (Hm2 l Hlm2)
      have abs_sum'' : (xs l - ys l).abs + hw ≤ hw + hw := by
        exact Dyadic.add_le_add_right.mpr (Hm1 l Hlm1)
      have abs_sum : (xs l - ys l).abs + (ys l - zs l).abs ≤ hw + hw := by
        exact Dyadic.le_trans abs_sum' abs_sum''
      trans (xs l - ys l).abs + (ys l - zs l).abs
      · exact abs_tri
      · trans hw+hw
        · exact?
        · rw [Hthw]

def IncreasingSequenceLowerReal :=
  { seq : Nat -> Dyadic // is_increasing seq }

#print IncreasingSequenceLowerReal


#print Setoid

instance seq_eq_equivalence : Equivalence equivalent_sequences where
  refl := equivalent_sequences_refl
  symm := equivalent_sequences_symm
  trans := equivalent_sequences_trans

instance seq_le_setoid : Setoid (Nat -> Dyadic) where
  r := equivalent_sequences
  iseqv := seq_eq_equivalence


def ConstructiveLowerReal := Quot (@equivalent_sequences)

#print ConstructiveLowerReal

axiom x : IncreasingSequenceLowerReal
#check x
#check x.val
#check x.property








#print IncreasingSequenceLowerReal
#print Set

def seq_le (x1 x2 : IncreasingSequenceLowerReal) : Prop :=
  forall w : Dyadic, ( (forall n : Nat, x2.val n ≤ w) →
                           (forall n : Nat, x1.val n ≤ w) )

def hlf (w : Dyadic) := w.shiftRight 1

private theorem seq_le_proper' : forall xs1 xs2 : Nat → Dyadic, forall w : Dyadic,
    is_increasing xs1 → is_increasing xs2 → equivalent_sequences xs1 xs2 →
      (forall n : Nat, xs1 n ≤ w) → (forall n : Nat, xs2 n ≤ w) := by
  intros xs1 xs2 w p1 p2 e12 H1 n
  unfold equivalent_sequences at e12
  suffices forall e, zero < e -> xs2 n ≤ w + e by sorry /- Archimidean -/
  intro e He
  replace e12 := e12 e He
  cases e12
  · case intro m Hml =>
    let l := Max.max m n
    replace H1 := H1 l
    have Hlm : l ≥ m := by exact Nat.le_max_left m n
    have Hln : l ≥ n := by exact Nat.le_max_right m n
    replace Hl := Hml l Hlm
    have H2l : xs2 l ≤ xs1 l + e := by sorry
    trans xs2 l
    · exact p2 n l Hln
    · trans xs1 l + e
      · exact H2l
      · exact Dyadic.add_le_add_right.mpr H1


private theorem seq_le_proper : forall {x1 x2 : IncreasingSequenceLowerReal} {w : Dyadic},
    equivalent_sequences x1.val x2.val ->  (forall n : Nat, x2.val n ≤ w) → (forall n : Int, x1.val n ≤ w) := by
  intros x1 x2 w
  let xs1 := x1.val
  let xs2 := x2.val
  have p1 : is_increasing xs1 := x1.property
  have p2 : is_increasing xs2 := x2.property
  unfold equivalent_sequences






end ConstructiveLowerReals
