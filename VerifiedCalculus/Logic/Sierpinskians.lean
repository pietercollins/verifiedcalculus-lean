/-
Copyright  2025-26  Pieter Collins
Released under the GNU GPLv3 as described in the file LICENSE.
Authors: Pieter Collins
-/

import VerifiedCalculus.Logic.Omniscience


inductive BasicSierpinskian : Type where | true | indeterminate

instance : DecidableEq BasicSierpinskian := by
  intros bs1 bs2; cases bs1; all_goals cases bs2; all_goals
    first | right; rfl | left; intro; contradiction

def BasicSierpinskian.definitely (bs : BasicSierpinskian) : Bool :=
  match bs with | true => Bool.true | _ => Bool.false

theorem BasicSierpinskian.not_indeterminate : forall (bs : BasicSierpinskian),
     (bs ≠ .indeterminate) → bs = true := by
  intros bs H; cases bs with | true => rfl | indeterminate => contradiction


def BasicSierpinskian.and (bs1 bs2 : BasicSierpinskian) : BasicSierpinskian :=
 match bs1, bs2 with
  | true, true => true
  | _, _ => indeterminate

theorem BasicSierpinskian.and_true : forall (bs1 bs2 : BasicSierpinskian),
    and bs1 bs2 = true ↔ bs1 = true ∧ bs2 = true := by
  unfold and; intros bs1 bs2; cases bs1; all_goals cases bs2; all_goals simp_all

def BasicSierpinskian.or (bs1 bs2 : BasicSierpinskian) : BasicSierpinskian :=
 match bs1, bs2 with
  | indeterminate, indeterminate => indeterminate
  | _, _ => true

theorem BasicSierpinskian.or_true : forall (bs1 bs2 : BasicSierpinskian),
    or bs1 bs2 = true ↔ bs1 = true ∨ bs2 = true := by
  unfold or; intros bs1 bs2; cases bs1; all_goals cases bs2; all_goals simp_all

def BasicSierpinskian.refines (bs1 bs2 : BasicSierpinskian) : Prop :=
  match bs2 with | indeterminate => True | _ => bs1 = bs2

theorem BasicSierpinskian.refines_true : forall bs, refines bs true -> bs = true := by
  unfold refines; intros bs H; cases bs; all_goals simp_all

def Sierpinskian.is_monotone (seq : Nat -> BasicSierpinskian) : Prop :=
  forall (m n : Nat), m <= n -> BasicSierpinskian.refines (seq n) (seq m)

structure Sierpinskian where
  mk ::
    seq : Nat -> BasicSierpinskian
    mono : Sierpinskian.is_monotone seq


def Sierpinskian.cnst (c : BasicSierpinskian) := fun (_ : Nat) => c

theorem Sierpinskian.cnst_is_monotone : forall (c : BasicSierpinskian), Sierpinskian.is_monotone (cnst c) := by
  with_unfolding_all
  unfold cnst is_monotone BasicSierpinskian.refines
  intros c m n H
  cases c
  all_goals simp_all

def Sierpinskian.true := Sierpinskian.mk (cnst .true) (cnst_is_monotone .true)
def Sierpinskian.indeterminate := Sierpinskian.mk (cnst .indeterminate) (cnst_is_monotone .indeterminate)

theorem Sierpinskian.monotone_true : forall (seq : Nat -> BasicSierpinskian), is_monotone seq →
    forall m, (seq m = .true) -> (forall n, m <= n -> seq n = .true) := by
  unfold is_monotone; intros seq Hmono m Hm n Hle
  apply BasicSierpinskian.refines_true; rewrite [← Hm]; exact Hmono m n Hle


def Sierpinskian.equivalent (s1 s2 : Sierpinskian) : Prop :=
  exists m, forall n, m <= n -> s1.seq n = s2.seq n

local infix:90 (name := eqvOp) " ≡ " => Sierpinskian.equivalent
local infix:90 " ≈ " => Sierpinskian.equivalent

theorem Sierpinskian.equivalent_refl : forall s : Sierpinskian, s ≡ s := by
  intros s; exists 0; intros n Hle; exact Eq.refl (s.seq n)
theorem Sierpinskian.equivalent_symm : forall { s1 s2 : Sierpinskian }, s1 ≡ s2 → s2 ≡ s1 := by
  unfold Sierpinskian.equivalent; simp
  intros s1 s2 m H12; exists m; intros n Hle
  exact Eq.symm (H12 n Hle)
theorem Sierpinskian.equivalent_trans : forall {s1 s2 s3 : Sierpinskian}, s1 ≡ s2 → s2 ≡ s3 → s1 ≡ s3 := by
  unfold Sierpinskian.equivalent
  intros s1 s2 s3 H12 H23
  cases H12 with | intro m12 H12 =>
  cases H23 with | intro m23 H23 =>
  let m13 := max m12 m23; exists m13
  intros n Hm13le
  have Hm12le : m12 <= n := Nat.le_trans (Nat.le_max_left m12 m23) Hm13le
  have Hm23le : m23 <= n := Nat.le_trans (Nat.le_max_right m12 m23) Hm13le
  exact Eq.trans (H12 n Hm12le) (H23 n Hm23le)

theorem Sierpinskian.equivalence : Equivalence Sierpinskian.equivalent :=
  Equivalence.mk Sierpinskian.equivalent_refl Sierpinskian.equivalent_symm Sierpinskian.equivalent_trans

/-
def Keqv' : Equivalence Sierpinskian.equivalent := by
  refine { refl := ?_, symm := ?_, trans := ?_ }
  exact Sierpinskian.equivalent_refl
  exact Sierpinskian.equivalent_symm
  exact Sierpinskian.equivalent_trans
-/

@[instance_reducible]
def Sierpinskian.has_equiv : HasEquiv Sierpinskian :=
  HasEquiv.mk Sierpinskian.equivalent

def Sierpinskian.setoid : Setoid Sierpinskian :=
  Setoid.mk Sierpinskian.equivalent Sierpinskian.equivalence

def QuotientSierpinskian := Quotient Sierpinskian.setoid
def QuotientSierpinskian.mk := Quotient.mk Sierpinskian.setoid


/-
def Sierpinskian.setoid : Setoid Sierpinskian := by
  refine { r := ?_, iseqv := ?_ }
  exact Sierpinskian.equivalent
  exact Sierpinskian.equivalence
-/

theorem Sierpinskian.is_true : forall (s : Sierpinskian),
    (exists (m : Nat), s.seq m = .true) → s ≡ true := by
  unfold Sierpinskian.equivalent Sierpinskian.true Sierpinskian.cnst
  intros s Em
  cases Em with | intro m Hm =>
  exists m; exact monotone_true s.seq s.mono m Hm

theorem Sierpinskian.is_indeterminate : forall (s : Sierpinskian),
    (forall n, s.seq n = BasicSierpinskian.indeterminate) → s ≡ Sierpinskian.indeterminate := by
  unfold Sierpinskian.equivalent Sierpinskian.indeterminate cnst
  intros s Hm; exists 0; simp; assumption




def Sierpinskian.LPO : Type :=
  forall (p : forall _ : Nat, Prop),
    forall (_ : forall n : Nat, SumBool (p n) (Not (p n))),
      SumBool (exists n, p n) (forall n, Not (p n))



theorem Sierpinskian.cases : LPO -> forall (s : Sierpinskian),
    s ≡ true ∨ s ≡ indeterminate := by
  intro lpo
  intro s
  let P (bs : BasicSierpinskian) := bs ≠ BasicSierpinskian.indeterminate
  let PDec (bs : BasicSierpinskian) : SumBool (P bs) (¬ (P bs)) := by
    exact SumBool.ofDecidable (instDecidableNot)
  let p := fun n : Nat => P (s.seq n)
  have pdec := fun n => PDec (s.seq n)
  have q := lpo p pdec
  clear lpo pdec PDec
  unfold p at q
  cases q
  · case case1 Epm =>
    left
    apply Sierpinskian.is_true
    cases Epm with | intro n Hn =>
    exists n
    exact BasicSierpinskian.not_indeterminate (s.seq n) Hn
  · case case2 Apn =>
    right
    apply Sierpinskian.is_indeterminate
    intro n
    apply Decidable.of_not_not
    exact Apn n

def QuotientSierpinskian.true := QuotientSierpinskian.mk Sierpinskian.true
def QuotientSierpinskian.indeterminate := QuotientSierpinskian.mk Sierpinskian.indeterminate


theorem QuotientSierpinskian.cases : LPO -> forall (qs : QuotientSierpinskian),
    qs = QuotientSierpinskian.true ∨ qs = QuotientSierpinskian.indeterminate := by
  intro lpo
  apply Quotient.ind
  intro s
  have Kc := Sierpinskian.cases lpo s
  cases Kc
  . case inl Ht =>
      left
      unfold QuotientSierpinskian.true
      apply Quotient.sound
      exact Ht
  . case inr Hif =>
      right
      unfold QuotientSierpinskian.indeterminate
      apply Quotient.sound
      exact Hif
