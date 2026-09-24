/-
Copyright  2026  Pieter Collins
Released under the GNU GPLv3 as described in the file LICENSE.
Authors: Pieter Collins
-/

import VerifiedCalculus.Logic.SumBool


def LPO : Type :=
  forall (p : forall _ : Nat, Prop),
    forall (_ : forall n : Nat, SumBool (p n) (Not (p n))),
      SumBool (exists n, p n) (forall n, Not (p n))
