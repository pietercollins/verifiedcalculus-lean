import VerifiedCalculus.Integer
import VerifiedCalculus.Dyadic

import Init.Data.Dyadic

/-
-/
#print Dyadic

theorem Int.abs_neg (z : Int) : abs (Int.neg z) = abs z := by
  unfold Int.neg
  unfold Int.abs
  cases z
  · case ofNat n =>
    cases n
    · case zero => rfl
    · case succ m => rfl
  · case negSucc m => rfl

theorem Int.abs_add (z1 z2 : Int) : abs (Int.add z1 z2) ≤ abs z1 + abs z2 := by
  apply?

theorem Int.neg_odd (z : Int) : z % 2 = 1 → -z % 2 = 1 := by grind

theorem Dyadic.abs_neg_eq (x : Dyadic) : abs x = abs (Dyadic.neg x) := by
  unfold Dyadic.abs; unfold Dyadic.neg
  cases x
  · case zero => rfl
  · case ofOdd n k H => simp only [ofOdd.injEq, and_true]; rw [←Int.abs_neg n]; rfl

#check sub_self

theorem Dyadic.abs_sub_eq (x y : Dyadic) : abs (x-y) = abs (y-x) := by
  have ns : y-x = - (x-y) := by
    rw [Eq.symm (neg_sub x y)]
  rw [ns]
  exact Dyadic.abs_neg_eq (x-y)

def Dyadic.is_increasing (xs : Nat -> Dyadic) : Prop :=
  forall n1 n2, n1 <= n2 -> xs n1 <= xs n2

def Dyadic.is_decreasing (xs : Nat -> Dyadic) : Prop :=
  forall n1 n2, n1 <= n2 -> xs n2 <= xs n1

def Dyadic.is_fast_cauchy_sequence (xs : Int → Dyadic) : Prop :=
  forall n1 n2, Dyadic.abs (xs n1 - xs n2) <= two_exp n1 + two_exp n2

def Dyadic.fast_equivalent_cauchy_sequences (xs1 xs2 : Int → Dyadic) : Prop :=
  forall n : Int, ( Dyadic.abs (xs1 n - xs2 n) ≤  Dyadic.two_exp (n+1 : Int) )

def Dyadic.equivalent_cauchy_sequences (xs1 xs2 : Int → Dyadic) : Prop :=
  forall n : Int, exists m : Int, forall l, l ≤ m →
    ( Dyadic.abs (xs1 l - xs2 l) ≤  Dyadic.two_exp (n : Int) )

theorem Dyadic.comp_shiftLeft : forall (w : Dyadic) (n1 n2 : Int) ,
  Dyadic.shiftLeft ( Dyadic.shiftLeft w n1) n2 = Dyadic.shiftLeft w (n1+n2) := by
  unfold Dyadic.shiftLeft
  intro w n1 n2
  cases w
  · case zero =>simp
  · case ofOdd z k Hz => grind

theorem Dyadic.equivalent_cauchy_sequences_refl :
    forall (xs : Int → Dyadic), Dyadic.equivalent_cauchy_sequences xs xs := by
  unfold equivalent_cauchy_sequences
  intro xs n
  exists 0
  intro l l_le_zero
  have diff_zero : xs l - xs l = 0 := by exact sub_self (xs l)
  rw [diff_zero]
  unfold abs
  simp only [Dyadic.zero_eq, ge_iff_le]
  unfold two_exp
  unfold Dyadic.shiftLeft
  exact le_of_eq_of_le rfl rfl

theorem Dyadic.equivalent_cauchy_sequences_symm :
  forall (xs ys : Int → Dyadic),
    equivalent_cauchy_sequences xs ys → equivalent_cauchy_sequences ys xs := by
  unfold equivalent_cauchy_sequences
  intros xs ys H
  intro n
  cases H n
  · case intro m Hm =>
    exists m
    intro l Hlm
    have Hl := Hm l Hlm
    have abs_eq : abs (xs l - ys l) = abs (ys l - xs l) := by
      exact Dyadic.abs_sub_eq (xs l) (ys l)
    rw [←abs_eq]
    exact Hl

def minInt (z1 z2 : ℤ) : ℤ := min z1 z2

theorem Dyadic.equivalent_cauchy_sequences_trans :
  forall (xs ys zs : Int → Dyadic),
    equivalent_cauchy_sequences xs ys → equivalent_cauchy_sequences ys zs →
      equivalent_cauchy_sequences xs zs := by
  unfold equivalent_cauchy_sequences
  intro xs ys zs Hxy Hyz
  intro n
  cases Hxy (n-1)
  . case intro m1 Hm1 =>
    cases Hyz (n-1)
    . case intro m2 Hm2 =>
      let m := minInt m1 m2
      exists m
      intro l Hlm
      have Hlm1 : l ≤ m1 := by grind
      have Hlm2 : l ≤ m2 := by grind
      have  Hlxy := Hm1 l Hlm1
      have  Hlyz := Hm2 l Hlm2
      have abs_tri : (xs l - zs l).abs ≤  (xs l - ys l).abs + (ys l - zs l).abs := by
        have sum_diff : (xs l - zs l) = (xs l - ys l) + (ys l - zs l) := by grind
        rw [sum_diff]
        exact Dyadic.abs_add (xs l - ys l) (ys l - zs l)
      have abs_sum : (xs l - ys l).abs + (ys l - zs l).abs ≤ two_exp (n-1) + two_exp (n-1) := by
        grind
      have exp_sum : two_exp (n-1) + two_exp (n-1) = two_exp n := by
        have sum_twice : two_exp (n-1) + two_exp (n-1) = (2 : Dyadic) * two_exp (n-1) := by grind
        rw [sum_twice]
        sorry
      grind


def MetricSequenceReal :=
  { xs : Nat -> Dyadic | forall n1 n2, Dyadic.dist (xs n1) (xs n2)
                            <= (Dyadic.hlf 1) ^ ( (n1 + n2)) }



def neg_three : Dyadic := Dyadic.ofInt (-3 : Int)
def hlf_neg_three : Dyadic := Dyadic.hlf neg_three * Dyadic.two_exp 3
def abs_hlf_neg_three : Dyadic := Dyadic.abs hlf_neg_three

def rat_abs_hlf_neg_three : Rat := Dyadic.toRat abs_hlf_neg_three

#eval rat_abs_hlf_neg_three
