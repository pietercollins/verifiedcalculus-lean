/-
Copyright  2025-26  Pieter Collins
Released under the GNU GPLv3 as described in the file LICENSE.
Authors: Pieter Collins
-/

import VerifiedCalculus.Logic.Omniscience


inductive BasicKleenean : Type where | true | indeterminate | false

instance : DecidableEq BasicKleenean := by
  intros bk1 bk2; cases bk1 <;> cases bk2 <;> first
    | right; rfl | left; intro; contradiction

def known (b : Bool) : BasicKleenean :=
  match b with | .true => BasicKleenean.true | .false => BasicKleenean.false

def unknown : BasicKleenean :=
  BasicKleenean.indeterminate

def BasicKleenean.definitely (bk : BasicKleenean) : Bool :=
  match bk with | true => Bool.true | _ => Bool.false

def BasicKleenean.possibly (bk : BasicKleenean) : Bool :=
  match bk with | false => Bool.false | _ => Bool.true

theorem BasicKleenean.not_indeterminate : forall (bk : BasicKleenean),
     (bk ≠ .indeterminate) → bk = true ∨ bk = false := by
  intros bk H
  cases bk with
  | true => left; rfl
  | indeterminate => contradiction
  | false => right; rfl


def BasicKleenean.implies' (bk1 bk2 : BasicKleenean) : BasicKleenean :=
  match bk1 with
  | indeterminate =>
      match bk2 with
      | true => true
      | indeterminate => indeterminate
      | false => indeterminate
  | false => true
  | true => bk2

def BasicKleenean.implies (bk1 bk2 : BasicKleenean) : BasicKleenean :=
  match bk1, bk2 with
  | false, _ => true
  | _, true => true
  | indeterminate, _ => indeterminate
  | _, indeterminate => indeterminate
  | _, _ => false


def BasicKleenean.not' (bk : BasicKleenean) : BasicKleenean :=
  match bk with
  | false => true
  | indeterminate => indeterminate
  | true => false

def BasicKleenean.not (bk : BasicKleenean) : BasicKleenean :=
  BasicKleenean.implies bk BasicKleenean.false

theorem BasicKleenean.not_not_id : forall (bk : BasicKleenean), not (not bk) = bk := by
  unfold not implies; intros bk; cases bk; all_goals simp_all

theorem BasicKleenean.not_true : forall (bk : BasicKleenean), not bk = true <-> bk = false := by
  unfold not implies;intros bk; cases bk; all_goals simp_all

theorem BasicKleenean.not_false : forall (bk : BasicKleenean), not bk = false <-> bk = true := by
  unfold not implies; intros bk; cases bk; all_goals simp_all


theorem BasicKleenean.implies_true : forall (bk1 bk2 : BasicKleenean),
    implies bk1 bk2 = true ↔ bk1 = false ∨ bk2 = true := by
  unfold implies
  intros bk1 bk2; cases bk1; all_goals cases bk2; all_goals simp_all

theorem BasicKleenean.implies_false : forall (bk1 bk2 : BasicKleenean),
    implies bk1 bk2 = false ↔ bk1 = true ∧ bk2 = false := by
  unfold implies
  intros bk1 bk2; cases bk1; all_goals cases bk2; all_goals simp_all


def BasicKleenean.and (bk1 bk2 : BasicKleenean) : BasicKleenean :=
  not (implies bk1 (not bk2))

theorem BasicKleenean.and_true : forall (bk1 bk2 : BasicKleenean),
    and bk1 bk2 = true ↔ bk1 = true ∧ bk2 = true := by
  unfold and not implies
  intros bk1 bk2; cases bk1; all_goals cases bk2; all_goals simp_all

theorem BasicKleenean.and_false : forall (bk1 bk2 : BasicKleenean),
    and bk1 bk2 = false ↔ bk1 = false ∨ bk2 = false := by
  unfold and not implies
  intros bk1 bk2; cases bk1; all_goals cases bk2; all_goals simp_all


def BasicKleenean.or (bk1 bk2 : BasicKleenean) : BasicKleenean :=
  implies (not bk1) bk2

theorem BasicKleenean.or_true : forall (bk1 bk2 : BasicKleenean),
    or bk1 bk2 = true ↔ bk1 = true ∨ bk2 = true := by
  unfold or not implies
  intros bk1 bk2; cases bk1; all_goals cases bk2; all_goals simp_all

theorem BasicKleenean.or_false : forall (bk1 bk2 : BasicKleenean),
    or bk1 bk2 = false ↔ bk1 = false ∧ bk2 = false := by
  unfold or not implies
  intros bk1 bk2; cases bk1; all_goals cases bk2; all_goals simp_all


def BasicKleenean.iff (bk1 bk2 : BasicKleenean) : BasicKleenean :=
  and (implies bk1 bk2) (implies bk2 bk1)

theorem BasicKleenean.iff_true : forall (bk1 bk2 : BasicKleenean),
    iff bk1 bk2 = true ↔ (bk1 = true ∧ bk2 = true) ∨ (bk1 = false ∧ bk2 = false) := by
  unfold iff and not implies
  intros bk1 bk2; cases bk1; all_goals cases bk2; all_goals simp_all

theorem BasicKleenean.iff_false : forall (bk1 bk2 : BasicKleenean),
    iff bk1 bk2 = false ↔ (bk1 = false ∧ bk2 = true) ∨ (bk1 = true ∧ bk2 = false) := by
  unfold iff and not implies
  intros bk1 bk2; cases bk1; all_goals cases bk2; all_goals simp_all


def BasicKleenean.refines (bk1 bk2 : BasicKleenean) : Prop :=
  match bk2 with | indeterminate => True | _ => bk1 = bk2

theorem BasicKleenean.refines_true : forall bk, refines bk true -> bk = true := by
  unfold refines; intros bk H; cases bk; all_goals simp_all
theorem BasicKleenean.refines_false : forall bk, refines bk false -> bk = false := by
  unfold refines; intros bk H; cases bk; all_goals simp_all
theorem BasicKleenean.refines_true_false : forall bk1 bk2,
    (bk1 = true ∨ bk1 = false) → refines bk2 bk1 → bk2 = bk1 := by
  unfold refines; intros bk1 bk2 Htf Hr; cases bk1; all_goals cases bk2; all_goals simp_all

def is_monotone (seq : Nat -> BasicKleenean) : Prop :=
  forall (m n : Nat), m <= n -> BasicKleenean.refines (seq n) (seq m)

structure Kleenean where
  mk ::
    seq : Nat -> BasicKleenean
    mono : is_monotone seq


def Kleenean.cnst (c : BasicKleenean) := fun (_ : Nat) => c

theorem Kleenean.cnst_is_monotone : forall (c : BasicKleenean), is_monotone (cnst c) := by
  with_unfolding_all
  unfold cnst is_monotone BasicKleenean.refines
  intros c m n H
  cases c
  all_goals simp_all

def Kleenean.true := Kleenean.mk (cnst .true) (cnst_is_monotone .true)
def Kleenean.indeterminate := Kleenean.mk (cnst .indeterminate) (cnst_is_monotone .indeterminate)
def Kleenean.false := Kleenean.mk (cnst .false) (cnst_is_monotone .false)

theorem Kleenean.monotone_true : forall (seq : Nat -> BasicKleenean), is_monotone seq →
    forall m, (seq m = .true) -> (forall n, m <= n -> seq n = .true) := by
  unfold is_monotone; intros seq Hmono m Hm n Hle
  apply BasicKleenean.refines_true; rewrite [← Hm]; exact Hmono m n Hle

theorem Kleenean.monotone_false : forall (seq : Nat -> BasicKleenean), is_monotone seq →
    forall m, (seq m = .false) -> (forall n, m <= n -> seq n = .false) := by
  unfold is_monotone; intros seq Hmono m Hm n Hle
  apply BasicKleenean.refines_false; rewrite [← Hm]; exact Hmono m n Hle

theorem Kleenean.monotone_true_false : forall (seq : Nat -> BasicKleenean), is_monotone seq →
    forall m, (seq m ≠ BasicKleenean.indeterminate) -> (forall n, m <= n -> seq n = seq m) := by
/-
  unfold is_monotone; intros seq Hmono m Hm n Hle
  apply BasicKleenean.refines_true_false
  . apply BasicKleenean.not_indeterminate; exact Hm
  . exact Hmono m n Hle
-/
  intros seq Hmono m Hm
  cases BasicKleenean.not_indeterminate _ Hm
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
  have Hm' := BasicKleenean.not_indeterminate _ Hm
  have Htf := monotone_true_false k.seq k.mono m Hm
  cases Hm' with
  | inl Hmt => left; exists m; rw [Hmt] at Htf; unfold true cnst; exact Htf
  | inr Hmf => right; exists m; rw [Hmf] at Htf; unfold false cnst; exact Htf

theorem Kleenean.is_indeterminate : forall (k : Kleenean),
    (forall n, k.seq n = BasicKleenean.indeterminate) → k ≡ Kleenean.indeterminate := by
  unfold Kleenean.equivalent Kleenean.indeterminate cnst
  intros k Hm; exists 0; simp; assumption




def Kleenean.LPO : Type :=
  forall (p : forall _ : Nat, Prop),
    forall (_ : forall n : Nat, SumBool (p n) (Not (p n))),
      SumBool (exists n, p n) (forall n, Not (p n))

theorem Kleenean.cases : LPO -> forall (k : Kleenean),
    k ≡ true ∨ k ≡ indeterminate ∨ k ≡ false := by
  intro lpo
  intro k
  let P (bk : BasicKleenean) := bk ≠ BasicKleenean.indeterminate
  let PDec (bk : BasicKleenean) : SumBool (P bk) (¬ (P bk)) := by
    exact SumBool.ofDecidable (instDecidableNot)
  let p := fun n : Nat => P (k.seq n)
  have pdec := fun n => PDec (k.seq n)
  have q := lpo p pdec
  clear lpo pdec PDec
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
    intro n
    apply Decidable.of_not_not
    exact Apn n

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
