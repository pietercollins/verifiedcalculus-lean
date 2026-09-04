/-
Copyright  2025-26  Pieter Collins
Released under the GNU GPLv3 as described in the file LICENSE.
Authors: Pieter Collins
-/

import VerifiedCalculus.Omniscience

inductive BasicSierpinskian : Type where | true | indeterminate

def BasicSierpinskian.definitely (s : BasicSierpinskian) : Bool :=
  match s with | true => Bool.true | _ => Bool.false

theorem BasicSierpinskian.eq_dne : forall (s1 s2 : BasicSierpinskian), ¬ (s1 ≠ s2) → s1 = s2 := by
  intros s1 s2 H
  cases s1; all_goals cases s2; all_goals simp_all

#print BasicSierpinskian

def BasicSierpinskian.not_indeterminate_decidable :
    forall (s : BasicSierpinskian), SumBool (s ≠ indeterminate) (¬ (s ≠ indeterminate)) := by
  intro s; cases s
  . apply SumBool.case1; simp
  . apply SumBool.case2; simp

theorem BasicSierpinskian.not_indeterminate : forall (s : BasicSierpinskian),
     (s ≠ .indeterminate) → s = true := by
  intros s H
  cases s with
  | true => rfl
  | indeterminate => contradiction


def BasicSierpinskian.and (s1 s2 : BasicSierpinskian) : BasicSierpinskian :=
 match s1, s2 with
  | true, true => true
  | _, _ => indeterminate

theorem BasicSierpinskian.and_true : forall (s1 s2 : BasicSierpinskian),
    and s1 s2 = true ↔ s1 = true ∧ s2 = true := by
  unfold and; intros s1 s2; cases s1; all_goals cases s2; all_goals simp_all

def BasicSierpinskian.or (s1 s2 : BasicSierpinskian) : BasicSierpinskian :=
 match s1, s2 with
  | indeterminate, indeterminate => indeterminate
  | _, _ => true

theorem BasicSierpinskian.or_true : forall (s1 s2 : BasicSierpinskian),
    or s1 s2 = true ↔ s1 = true ∨ s2 = true := by
  unfold or; intros s1 s2; cases s1; all_goals cases s2; all_goals simp_all

def BasicSierpinskian.refines (s1 s2 : BasicSierpinskian) : Prop :=
  match s2 with | indeterminate => True | _ => s1 = s2

theorem BasicSierpinskian.refines_true : forall s, refines s true -> s = true := by
  unfold refines; intros s H; cases s; all_goals simp_all

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

def Sierpinskian.monotone_true : forall (seq : Nat -> BasicSierpinskian), is_monotone seq →
    forall m, (seq m = .true) -> (forall n, m <= n -> seq n = .true) := by
  unfold is_monotone; intros seq Hmono m Hm n Hle
  apply BasicSierpinskian.refines_true; rewrite [← Hm]; exact Hmono m n Hle


def Sierpinskian.equivalent (k1 k2 : Sierpinskian) : Prop :=
  exists m, forall n, m <= n -> k1.seq n = k2.seq n

local infix:90 (name := eqvOp) " ≡ " => Sierpinskian.equivalent
local infix:90 " ≈ " => Sierpinskian.equivalent

theorem Sierpinskian.equivalent_refl : forall k : Sierpinskian, k ≡ k := by
  intros k; exists 0; intros n Hle; exact Eq.refl (k.seq n)
theorem Sierpinskian.equivalent_symm : forall { k1 k2 : Sierpinskian }, k1 ≡ k2 → k2 ≡ k1 := by
  unfold Sierpinskian.equivalent; simp
  intros k1 k2 m H12; exists m; intros n Hle
  exact Eq.symm (H12 n Hle)
theorem Sierpinskian.equivalent_trans : forall {k1 k2 k3 : Sierpinskian}, k1 ≡ k2 → k2 ≡ k3 → k1 ≡ k3 := by
  unfold Sierpinskian.equivalent
  intros k1 k2 k3 H12 H23
  cases H12 with | intro m12 H12 =>
  cases H23 with | intro m23 H23 =>
  let m13 := max m12 m23; exists m13
  intros n Hm13le
  have Hm12le : m12 <= n := Nat.le_trans (Nat.le_max_left m12 m23) Hm13le
  have Hm23le : m23 <= n := Nat.le_trans (Nat.le_max_right m12 m23) Hm13le
  exact Eq.trans (H12 n Hm12le) (H23 n Hm23le)

def Sierpinskian.equivalence : Equivalence Sierpinskian.equivalent :=
  Equivalence.mk Sierpinskian.equivalent_refl Sierpinskian.equivalent_symm Sierpinskian.equivalent_trans

/-
def Keqv' : Equivalence Sierpinskian.equivalent := by
  refine { refl := ?_, symm := ?_, trans := ?_ }
  exact Sierpinskian.equivalent_refl
  exact Sierpinskian.equivalent_symm
  exact Sierpinskian.equivalent_trans
-/

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

theorem Sierpinskian.is_true : forall (k : Sierpinskian),
    (exists (m : Nat), k.seq m = .true) → k ≡ true := by
  unfold Sierpinskian.equivalent Sierpinskian.true Sierpinskian.cnst
  intros k Em
  cases Em with | intro m Hm =>
  exists m; exact monotone_true k.seq k.mono m Hm

theorem Sierpinskian.is_indeterminate : forall (k : Sierpinskian),
    (forall n, k.seq n = BasicSierpinskian.indeterminate) → k ≡ Sierpinskian.indeterminate := by
  unfold Sierpinskian.equivalent Sierpinskian.indeterminate cnst
  intros k Hm; exists 0; simp; assumption




def Sierpinskian.LPO : Type :=
  forall (p : forall _ : Nat, Prop),
    forall (_ : forall n : Nat, SumBool (p n) (Not (p n))),
      SumBool (exists n, p n) (forall n, Not (p n))


theorem Sierpinskian.cases' : LPO -> forall (k : Sierpinskian),
    k ≡ true ∨ k ≡ indeterminate := by
  intro lpo
  intro k
  let p := fun n : Nat => k.seq n ≠ .indeterminate
  have pdec := fun n => BasicSierpinskian.not_indeterminate_decidable (k.seq n)
  have q := lpo p pdec
  clear lpo pdec
  cases q
  . case case1 expn =>
      cases expn
      . case _ m pm =>
        unfold p at pm
        cases Hkm : k.seq m with
        | indeterminate => contradiction
        | true =>
          left
          unfold Sierpinskian.equivalent
          exists m
          unfold true cnst; simp
          apply Sierpinskian.monotone_true
          exact k.mono
          exact Hkm
  . case case2 allpn =>
    right
    unfold Sierpinskian.equivalent
    exists 0
    intros n _
    apply BasicSierpinskian.eq_dne
    apply allpn


#check Sierpinskian.is_true

theorem Sierpinskian.cases : LPO -> forall (k : Sierpinskian),
    k ≡ true ∨ k ≡ indeterminate := by
  intro lpo
  intro k
  let p := fun n : Nat => k.seq n ≠ .indeterminate
  have pdec := fun n => BasicSierpinskian.not_indeterminate_decidable (k.seq n)
  have q := lpo p pdec
  clear lpo pdec
  unfold p at q
  cases q
  · case case1 Epm =>
    have Etn : ∃ n, k.seq n = .true := by
      cases Epm
      · case intro n Hn => exists n; exact BasicSierpinskian.not_indeterminate (k.seq n) Hn
    have Htf := Sierpinskian.is_true k Etn
    left; assumption
  · case case2 Apn =>
    right
    apply Sierpinskian.is_indeterminate
    intro n; apply BasicSierpinskian.eq_dne; exact Apn n

def QuotientSierpinskian.true := QuotientSierpinskian.mk Sierpinskian.true
def QuotientSierpinskian.indeterminate := QuotientSierpinskian.mk Sierpinskian.indeterminate


theorem QuotientSierpinskian.cases : LPO -> forall (qk : QuotientSierpinskian),
    qk = QuotientSierpinskian.true ∨ qk = QuotientSierpinskian.indeterminate := by
  intro lpo
  apply Quotient.ind
  intro k
  have Kc := Sierpinskian.cases lpo k
  cases Kc
  . case a.inl Ht =>
      left
      unfold QuotientSierpinskian.true
      apply Quotient.sound
      exact Ht
  . case a.inr Hif =>
      right
      unfold QuotientSierpinskian.indeterminate
      apply Quotient.sound
      exact Hif
