/-
Copyright  2025-26  Pieter Collins
Released under the GNU GPLv3 as described in the file LICENSE.
Authors: Pieter Collins
-/

import VerifiedCalculus.Logic.Kleeneans


inductive QuasiDecidable (PT PF : Prop) where
  | mk {QT QF : Nat → Prop}
       (exclusive : ¬ (PT ∧ PF))
       (why_true : PT ↔ (exists n, QT n))
       (why_false : PF ↔ (exists n, QF n))
       (proved_true : forall n, Decidable (QT n))
       (proved_false : forall n, Decidable (QF n))


def QuasiDecidable.toKleenean {PT PF : Prop} (k : QuasiDecidable PT PF) : Kleenean :=
  match k with
  | .mk _ _ _ proved_true proved_false =>
      let seq (n : Nat) : BasicKleenean :=
        if (proved_true n).decide then BasicKleenean.true
        else if (proved_false n).decide then BasicKleenean.false
        else BasicKleenean.indeterminate
      Kleenean.known_from seq


def QuasiDecidable.not {PT PF} (qd : QuasiDecidable PT PF) : QuasiDecidable PF PT :=
  match qd with
  |.mk exclusive why_true why_false proved_true proved_false =>
    have exclusive' : ¬(PF∧PT) := by exact Not.imp exclusive And.symm
    QuasiDecidable.mk exclusive' why_false why_true proved_false proved_true
