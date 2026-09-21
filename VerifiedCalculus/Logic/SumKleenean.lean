/-
Copyright  2025-26  Pieter Collins
Released under the GNU GPLv3 as described in the file LICENSE.
Authors: Pieter Collins
-/

import VerifiedCalculus.Logic.Kleeneans

#print SumBool


inductive SumKleenean (PT PF : Prop) where
  | mk {QT QF : Nat → Prop}
       (exclusive : ¬ (PT ∧ PF))
       (why_true : PT ↔ (exists n, QT n))
       (why_false : PF ↔ (exists n, QF n))
       (proved_true : forall n, SumBool (QT n) (¬(QT n)))
       (proved_false : forall n, SumBool (QF n) (¬(QF n)))

#print SumKleenean

def SumKleenean.toKleenean {PT PF : Prop} (s : SumKleenean PT PF) : Kleenean :=
  sorry
