/-
Copyright  2026  Pieter Collins
Released under the GNU GPLv3 as described in the file LICENSE.
Authors: Pieter Collins
-/

import VerifiedCalculus.Logic.Induction

namespace TopologicalBasis

class Basis (B : Type) : Type where
  refines : B → B → Prop
  refines_refl : forall b, refines b b
  refines_trans : forall {b1 b3} (b2), refines b1 b2 → refines b2 b3 → refines b1 b3

class ConsistencyBasis (B : Type) : Type extends Basis B where
  inconsistent : B → B → Prop
  refines_consistent : forall b1 b2 b3,
    refines b1 b2 → refines b1 b3 → ¬ inconsistent b2 b3
  inconsistent_refines : forall b1 b2 b3,
    refines b1 b2 → inconsistent b2 b3 → inconsistent b1 b3

class RefinableBasis (B : Type) : Type extends ConsistencyBasis B where
  refinement : B → B → B
  refinement_symm : forall b1 b2, refinement b1 b2 = refinement b2 b1
  refinement_refines_first : forall b1 b2, refines (refinement b1 b2) b1
  refinement_refines_second : forall b1 b2, refines (refinement b1 b2) b2


theorem weak_monotone_iff_strong_monotone {B} [Base : Basis B] (seq : Nat -> B) :
  (forall (m : Nat), Base.refines (seq (m.succ)) (seq m)) ↔
    (forall (m n : Nat), m <= n -> Base.refines (seq n) (seq m)) :=
by
  apply Iff.intro
  · intros H m n
    apply Induction.weak_implies_strong_induction
    intro k; apply Base.refines_trans (seq k)
    · exact H k
    · exact Base.refines_refl (seq m)
  · intros H m
    exact H m m.succ (Nat.le_succ m)

def is_monotone {B} [Base : Basis B] (seq : Nat -> B) : Prop :=
  forall (m n : Nat), m <= n -> Base.refines (seq n) (seq m)

def is_eventually_monotone {B} [Base : Basis B] (seq : Nat -> B) : Prop :=
  forall (n : Nat), exists m, forall l, m <= l -> Base.refines (seq l) (seq n)

def is_convergent {B} [Base : ConsistencyBasis B] (seq : Nat -> B) : Prop :=
  forall b : B, exists n, Base.refines (seq n) b ∨ exists n, Base.inconsistent (seq n) b

end TopologicalBasis
