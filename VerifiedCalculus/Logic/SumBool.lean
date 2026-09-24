/-
Copyright  2026  Pieter Collins
Released under the GNU GPLv3 as described in the file LICENSE.
Authors: Pieter Collins
-/


inductive SumBool (P1 P2 : Prop) : Type where
  | case1 : forall _ : P1, SumBool P1 P2
  | case2 : forall _ : P2, SumBool P1 P2

def SumBool.ofDecidable {P : Prop} (decp : Decidable P) : SumBool P ¬P :=
  match decp with | isFalse np => case2 np | isTrue p => case1 p

def SumBool.toBool {P1 P2} (b : SumBool P1 P2) : Bool :=
  match b with
  | case1 _ => Bool.true
  | case2 _ => Bool.false

theorem SumBool.forget : forall (P1 P2 : Prop), SumBool P1 P2 -> P1 ∨ P2 := by
  intros P1 P2 H
  cases H with
  | case1 p1 => left; exact p1
  | case2 p2 => right; exact p2
