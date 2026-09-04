/-
Copyright  2026  Pieter Collins
Released under the GNU GPLv3 as described in the file LICENSE.
Authors: Pieter Collins
-/


inductive SumBool (P1 P2 : Prop) : Type where
  | case1 : forall _ : P1, SumBool P1 P2
  | case2 : forall _ : P2, SumBool P1 P2

theorem SumBool.forget : forall (P1 P2 : Prop), SumBool P1 P2 -> P1 ∨ P2 := by
  intros P1 P2 H
  cases H with
  | case1 p1 => left; exact p1
  | case2 p2 => right; exact p2


def LPO : Type :=
  forall (p : forall _ : Nat, Prop),
    forall (_ : forall n : Nat, SumBool (p n) (Not (p n))),
      SumBool (exists n, p n) (forall n, Not (p n))
