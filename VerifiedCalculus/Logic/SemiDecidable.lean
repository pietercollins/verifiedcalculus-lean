/-
Copyright  2025-26  Pieter Collins
Released under the GNU GPLv3 as described in the file LICENSE.
Authors: Pieter Collins
-/

import VerifiedCalculus.Logic.Induction
import VerifiedCalculus.Logic.Sierpinskians


inductive SemiDecidable {P : Prop} {Q : Nat → Prop} (whyQnP : P ↔ (∃n, Q n)) : Type where
  | mk (proved : forall n, Decidable (Q n))

def SemiDecidable.proved {P} {Q : Nat → Prop} {whyQnP : P ↔ (∃n, Q n)} (sd : SemiDecidable whyQnP)
    : forall n, Decidable (Q n) :=
  match sd with | .mk proved => proved

def SemiDecidable.is_true {P} {Q : Nat → Prop} {whyQnP : P ↔ (∃n, Q n)} (sd : SemiDecidable whyQnP) : Prop :=
  exists n, (SemiDecidable.proved sd n).decide = true


inductive StrongSemiDecidable {P : Prop} {Q : Nat → Prop} (whyQnP : P ↔ (∃n, Q n))
  | mk (proved : forall n, Decidable (Q n)) (proved_mono : forall n, Q n → Q (n.succ))


private def BasicSierpinskian.ofBool (b : Bool) : BasicSierpinskian :=
  match b with | .true => true | .false => indeterminate

private theorem BasicSierpinskian.implies_refines : forall (q1 q2 : Bool),
    (q1 → q2) → BasicSierpinskian.refines (ofBool q2) (ofBool q1) := by
  intros q1 q2 HQ
  unfold ofBool; unfold refines
  cases q1; all_goals cases q2; all_goals simp_all only [imp_self]
  contradiction


def SemiDecidable.toSierpinskian {P : Prop} {Q : Nat → Prop}
    (WhyQnP : P ↔ exists n, Q n)
      (s : SemiDecidable WhyQnP) : Sierpinskian :=
  match s with
  | .mk proved =>
      Sierpinskian.true_from (fun n => BasicSierpinskian.ofBool (proved n).decide)

def StrongSemiDecidable.toSierpinskian {P : Prop} {Q : Nat → Prop}
    (whyQnP : P ↔ ∃ n, Q n)
    (s : StrongSemiDecidable whyQnP) : Sierpinskian :=
  match s with
  | .mk proved proved_mono => by
      let seq := fun n => BasicSierpinskian.ofBool (proved n).decide
      have seq_mono : Sierpinskian.is_monotone seq := by
        unfold Sierpinskian.is_monotone
        apply (TopologicalBasis.weak_monotone_iff_strong_monotone seq).mp
        intro m; specialize (proved_mono m)
        apply BasicSierpinskian.implies_refines
        simp only [decide_eq_true_eq]
        exact proved_mono
      exact Sierpinskian.mk seq seq_mono
