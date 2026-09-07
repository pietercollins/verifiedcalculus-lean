/-
Copyright  2025-26  Pieter Collins
Released under the GNU GPLv3 as described in the file LICENSE.
Authors: Pieter Collins
-/

import VerifiedCalculus.Logic.Omniscience


inductive Tribool : Type where | true | indeterminate | false
def known : Bool -> Tribool :=
  fun b => match b with | Bool.true => Tribool.true | Bool.false => Tribool.false
def unknown : Tribool :=
  Tribool.indeterminate

theorem Tribool.eq_dne : forall (tb1 tb2 : Tribool), ¬ (tb1 ≠ tb2) → tb1 = tb2 := by
  intros tb1 tb2 H
  cases tb1; all_goals cases tb2; all_goals simp_all

def Tribool.not_indeterminate_decidable :
    forall (tb : Tribool), SumBool (tb ≠ indeterminate) (¬ (tb ≠ indeterminate)) := by
  intro tb; cases tb
  . apply SumBool.case1; simp
  . apply SumBool.case2; simp
  . apply SumBool.case1; simp

theorem Tribool.not_indeterminate : forall (tb : Tribool),
     (tb ≠ .indeterminate) → tb = true ∨ tb = false := by
  intros tb H
  cases tb with
  | true => left; rfl
  | indeterminate => contradiction
  | false => right; rfl

#print Tribool

def Tribool.implies' (tb1 tb2 : Tribool) : Tribool :=
  match tb1 with
  | indeterminate =>
      match tb2 with
      | true => true
      | indeterminate => indeterminate
      | false => indeterminate
  | false => true
  | true => tb2

def Tribool.implies (tb1 tb2 : Tribool) : Tribool :=
  match tb1, tb2 with
  | false, _ => true
  | _, true => true
  | indeterminate, _ => indeterminate
  | _, indeterminate => indeterminate
  | _, _ => false

#check Tribool.implies

def Tribool.not' (tb : Tribool) : Tribool :=
  match tb with
  | false => true
  | indeterminate => indeterminate
  | true => false

def Tribool.not (tb : Tribool) : Tribool :=
  Tribool.implies tb Tribool.false

theorem Tribool.not_not_id : forall (tb : Tribool), not (not tb) = tb := by
  unfold not implies; intros tb; cases tb; all_goals simp_all

theorem Tribool.not_true : forall (tb : Tribool), not tb = true <-> tb = false := by
  unfold not implies;intros tb; cases tb; all_goals simp_all

theorem Tribool.not_false : forall (tb : Tribool), not tb = false <-> tb = true := by
  unfold not implies; intros tb; cases tb; all_goals simp_all


theorem Tribool.implies_true : forall (tb1 tb2 : Tribool),
    implies tb1 tb2 = true ↔ tb1 = false ∨ tb2 = true := by
  unfold implies
  intros tb1 tb2; cases tb1; all_goals cases tb2; all_goals simp_all

theorem Tribool.implies_false : forall (tb1 tb2 : Tribool),
    implies tb1 tb2 = false ↔ tb1 = true ∧ tb2 = false := by
  unfold implies
  intros tb1 tb2; cases tb1; all_goals cases tb2; all_goals simp_all


def Tribool.and (tb1 tb2 : Tribool) : Tribool :=
  not (implies tb1 (not tb2))

theorem Tribool.and_true : forall (tb1 tb2 : Tribool),
    and tb1 tb2 = true ↔ tb1 = true ∧ tb2 = true := by
  unfold and not implies
  intros tb1 tb2; cases tb1; all_goals cases tb2; all_goals simp_all

theorem Tribool.and_false : forall (tb1 tb2 : Tribool),
    and tb1 tb2 = false ↔ tb1 = false ∨ tb2 = false := by
  unfold and not implies
  intros tb1 tb2; cases tb1; all_goals cases tb2; all_goals simp_all


def Tribool.or (tb1 tb2 : Tribool) : Tribool :=
  implies (not tb1) tb2

theorem Tribool.or_true : forall (tb1 tb2 : Tribool),
    or tb1 tb2 = true ↔ tb1 = true ∨ tb2 = true := by
  unfold or not implies
  intros tb1 tb2; cases tb1; all_goals cases tb2; all_goals simp_all

theorem Tribool.or_false : forall (tb1 tb2 : Tribool),
    or tb1 tb2 = false ↔ tb1 = false ∧ tb2 = false := by
  unfold or not implies
  intros tb1 tb2; cases tb1; all_goals cases tb2; all_goals simp_all


def Tribool.iff (tb1 tb2 : Tribool) : Tribool :=
  and (implies tb1 tb2) (implies tb2 tb1)

theorem Tribool.iff_true : forall (tb1 tb2 : Tribool),
    iff tb1 tb2 = true ↔ (tb1 = true ∧ tb2 = true) ∨ (tb1 = false ∧ tb2 = false) := by
  unfold iff and not implies
  intros tb1 tb2; cases tb1; all_goals cases tb2; all_goals simp_all

theorem Tribool.iff_false : forall (tb1 tb2 : Tribool),
    iff tb1 tb2 = false ↔ (tb1 = false ∧ tb2 = true) ∨ (tb1 = true ∧ tb2 = false) := by
  unfold iff and not implies
  intros tb1 tb2; cases tb1; all_goals cases tb2; all_goals simp_all


def Tribool.refines (tb1 tb2 : Tribool) : Prop :=
  match tb2 with | indeterminate => True | _ => tb1 = tb2

theorem Tribool.refines_true : forall tb, refines tb true -> tb = true := by
  unfold refines; intros tb H; cases tb; all_goals simp_all
theorem Tribool.refines_false : forall tb, refines tb false -> tb = false := by
  unfold refines; intros tb H; cases tb; all_goals simp_all
theorem Tribool.refines_true_false : forall tb1 tb2,
    (tb1 = true ∨ tb1 = false) → refines tb2 tb1 → tb2 = tb1 := by
  unfold refines; intros tb1 tb2 Htf Hr; cases tb1; all_goals cases tb2; all_goals simp_all

def is_monotone (seq : Nat -> Tribool) : Prop :=
  forall (m n : Nat), m <= n -> Tribool.refines (seq n) (seq m)

structure Kleenean where
  mk ::
    seq : Nat -> Tribool
    mono : is_monotone seq


def Kleenean.cnst (c : Tribool) := fun (_ : Nat) => c

theorem Kleenean.cnst_is_monotone : forall (c : Tribool), is_monotone (cnst c) := by
  with_unfolding_all
  unfold cnst is_monotone Tribool.refines
  intros c m n H
  cases c
  all_goals simp_all

def Kleenean.true := Kleenean.mk (cnst .true) (cnst_is_monotone .true)
def Kleenean.indeterminate := Kleenean.mk (cnst .indeterminate) (cnst_is_monotone .indeterminate)
def Kleenean.false := Kleenean.mk (cnst .false) (cnst_is_monotone .false)

theorem Kleenean.monotone_true : forall (seq : Nat -> Tribool), is_monotone seq →
    forall m, (seq m = .true) -> (forall n, m <= n -> seq n = .true) := by
  unfold is_monotone; intros seq Hmono m Hm n Hle
  apply Tribool.refines_true; rewrite [← Hm]; exact Hmono m n Hle

theorem Kleenean.monotone_false : forall (seq : Nat -> Tribool), is_monotone seq →
    forall m, (seq m = .false) -> (forall n, m <= n -> seq n = .false) := by
  unfold is_monotone; intros seq Hmono m Hm n Hle
  apply Tribool.refines_false; rewrite [← Hm]; exact Hmono m n Hle

theorem Kleenean.monotone_true_false : forall (seq : Nat -> Tribool), is_monotone seq →
    forall m, (seq m ≠ Tribool.indeterminate) -> (forall n, m <= n -> seq n = seq m) := by
/-
  unfold is_monotone; intros seq Hmono m Hm n Hle
  apply Tribool.refines_true_false
  . apply Tribool.not_indeterminate; exact Hm
  . exact Hmono m n Hle
-/
  intros seq Hmono m Hm
  cases Tribool.not_indeterminate _ Hm
  . case inl Ht =>
    intros n Hle; rewrite [Ht]
    exact monotone_true seq Hmono m Ht n Hle
  . case inr Hf =>
    intros n Hle; rewrite [Hf]
    exact monotone_false seq Hmono m Hf n Hle

def Kleenean.equivalent (k1 k2 : Kleenean) : Prop :=
  exists m, forall n, m <= n -> k1.seq n = k2.seq n

local infix:90 (name := eqvOp) " ≡ " => Kleenean.equivalent
local infix:90 " ≈ " => Kleenean.equivalent

theorem Kleenean.equivalent_refl : forall k : Kleenean, k ≡ k := by
  intros k; exists 0; intros n Hle; exact Eq.refl (k.seq n)
theorem Kleenean.equivalent_symm : forall { k1 k2 : Kleenean }, k1 ≡ k2 → k2 ≡ k1 := by
  unfold Kleenean.equivalent; simp
  intros k1 k2 m H12; exists m; intros n Hle
  exact Eq.symm (H12 n Hle)
theorem Kleenean.equivalent_trans : forall {k1 k2 k3 : Kleenean}, k1 ≡ k2 → k2 ≡ k3 → k1 ≡ k3 := by
  unfold Kleenean.equivalent
  intros k1 k2 k3 H12 H23
  cases H12 with | intro m12 H12 =>
  cases H23 with | intro m23 H23 =>
  let m13 := max m12 m23; exists m13
  intros n Hm13le
  have Hm12le : m12 <= n := Nat.le_trans (Nat.le_max_left m12 m23) Hm13le
  have Hm23le : m23 <= n := Nat.le_trans (Nat.le_max_right m12 m23) Hm13le
  exact Eq.trans (H12 n Hm12le) (H23 n Hm23le)

theorem Kleenean.equivalence : Equivalence Kleenean.equivalent :=
  Equivalence.mk Kleenean.equivalent_refl Kleenean.equivalent_symm Kleenean.equivalent_trans

/-
def Keqv' : Equivalence Kleenean.equivalent := by
  refine { refl := ?_, symm := ?_, trans := ?_ }
  exact Kleenean.equivalent_refl
  exact Kleenean.equivalent_symm
  exact Kleenean.equivalent_trans
-/

@[instance_reducible]
def Kleenean.has_equiv : HasEquiv Kleenean :=
  HasEquiv.mk Kleenean.equivalent

def Kleenean.setoid : Setoid Kleenean :=
  Setoid.mk Kleenean.equivalent Kleenean.equivalence

def QuotientKleenean := Quotient Kleenean.setoid
def QuotientKleenean.mk := Quotient.mk Kleenean.setoid


/-
def Kleenean.setoid : Setoid Kleenean := by
  refine { r := ?_, iseqv := ?_ }
  exact Kleenean.equivalent
  exact Kleenean.equivalence
-/

theorem Kleenean.is_true : forall (k : Kleenean),
    (exists (m : Nat), k.seq m = .true) → k ≡ true := by
  unfold Kleenean.equivalent Kleenean.true Kleenean.cnst
  intros k Em
  cases Em with | intro m Hm =>
  exists m; exact monotone_true k.seq k.mono m Hm

theorem Kleenean.is_false : forall (k : Kleenean),
    (exists (m : Nat), k.seq m = .false) → k ≡ false := by
  unfold Kleenean.equivalent Kleenean.false Kleenean.cnst; simp
  intros k m Hm
  exists m; exact monotone_false k.seq k.mono m Hm

theorem Kleenean.is_true_or_false : forall (k : Kleenean),
    (exists (m : Nat), k.seq m ≠ .indeterminate) → k ≡ true ∨ k ≡ false := by
  unfold Kleenean.equivalent
  intros k Em
  cases Em with | intro m Hm =>
  have Hm' := Tribool.not_indeterminate _ Hm
  have Htf := monotone_true_false k.seq k.mono m Hm
  cases Hm' with
  | inl Hmt => left; exists m; rw [Hmt] at Htf; unfold true cnst; exact Htf
  | inr Hmf => right; exists m; rw [Hmf] at Htf; unfold false cnst; exact Htf

theorem Kleenean.is_indeterminate : forall (k : Kleenean),
    (forall n, k.seq n = Tribool.indeterminate) → k ≡ Kleenean.indeterminate := by
  unfold Kleenean.equivalent Kleenean.indeterminate cnst
  intros k Hm; exists 0; simp; assumption




def Kleenean.LPO : Type :=
  forall (p : forall _ : Nat, Prop),
    forall (_ : forall n : Nat, SumBool (p n) (Not (p n))),
      SumBool (exists n, p n) (forall n, Not (p n))


theorem Kleenean.cases' : LPO -> forall (k : Kleenean),
    k ≡ true ∨ k ≡ indeterminate ∨ k ≡ false := by
  intro lpo
  intro k
  let p := fun n : Nat => k.seq n ≠ .indeterminate
  have pdec := fun n => Tribool.not_indeterminate_decidable (k.seq n)
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
          unfold Kleenean.equivalent
          exists m
          unfold true cnst; simp
          rw [← Hkm]
          apply monotone_true_false
          exact k.mono
          exact pm
        | false =>
          right; right
          unfold Kleenean.equivalent
          exists m
          unfold false cnst; simp
          rw [← Hkm]
          apply monotone_true_false
          exact k.mono
          exact pm
  . case case2 allpn =>
    right; left
    unfold Kleenean.equivalent
    exists 0
    intros n _
    apply Tribool.eq_dne
    apply allpn


theorem Kleenean.cases : LPO -> forall (k : Kleenean),
    k ≡ true ∨ k ≡ indeterminate ∨ k ≡ false := by
  intro lpo
  intro k
  let p := fun n : Nat => k.seq n ≠ .indeterminate
  have pdec := fun n => Tribool.not_indeterminate_decidable (k.seq n)
  have q := lpo p pdec
  clear lpo pdec
  unfold p at q
  cases q
  . case case1 Epm =>
    have Htf := Kleenean.is_true_or_false k Epm
    cases Htf
    . left; assumption
    . right; right; assumption
  . case case2 Apn =>
    right; left
    apply Kleenean.is_indeterminate
    intro n; apply Tribool.eq_dne; exact Apn n

def QuotientKleenean.true := QuotientKleenean.mk Kleenean.true
def QuotientKleenean.false := QuotientKleenean.mk Kleenean.false
def QuotientKleenean.indeterminate := QuotientKleenean.mk Kleenean.indeterminate


theorem QuotientKleenean.cases : LPO -> forall (qk : QuotientKleenean),
    qk = QuotientKleenean.true ∨ qk = QuotientKleenean.indeterminate ∨ qk = QuotientKleenean.false := by
  intro lpo
  apply Quotient.ind
  intro k
  have Kc := Kleenean.cases lpo k
  cases Kc
  . case inl Ht =>
      left
      unfold QuotientKleenean.true
      apply Quotient.sound
      exact Ht
  . case inr Hif =>
      right
      cases Hif
      . case inl Hi =>
        left
        unfold QuotientKleenean.indeterminate
        apply Quotient.sound
        exact Hi
      . case inr Hf =>
        right
        unfold QuotientKleenean.false
        apply Quotient.sound
        exact Hf




#print Classical.choose
#print PSigma
#print Sigma
