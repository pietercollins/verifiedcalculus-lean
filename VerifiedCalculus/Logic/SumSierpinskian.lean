/-
Copyright  2025-26  Pieter Collins
Released under the GNU GPLv3 as described in the file LICENSE.
Authors: Pieter Collins
-/

import VerifiedCalculus.Logic.Sierpinskians

#print Sigma

#print Decidable

#print SumBool


structure SumSierpinskian' {P : Prop} {Q : Nat → Prop}
  (whyQnP : P ↔ (exists n, Q n))
  (decQ : forall n : Nat, Decidable (Q n))
  (proved : forall n, SumBool (Q n) (¬(Q n)))

inductive SumSierpinskian {P : Prop} {Q : Nat → Prop}
    (whyQnP : P ↔ (exists n, Q n)) (decQ : forall n : Nat, Decidable (Q n)) : Type where
  | mk (proved : forall n, SumBool (Q n) (¬(Q n)))

inductive StrongSumSierpinskian {P : Prop} {Q : Nat → Prop}
    (whyQnP : P ↔ (exists n, Q n))
    (decQ : forall n : Nat, Decidable (Q n))
    (monoQ : forall n, Q n → Q (n.succ)) : Type where
  | mk (proved : forall n, SumBool (Q n) (¬(Q n))) (proved_mono : forall n, Q n → Q (n.succ))

#print SumSierpinskian




theorem BasicSierpinskian.refines_refl : forall bs : BasicSierpinskian,
    refines bs bs := by
  unfold refines; grind

theorem BasicSierpinskian.refines_trans : forall {bs1 bs3} (bs2 : BasicSierpinskian),
    refines bs1 bs2 →  refines bs2 bs3 → refines bs1 bs3 := by
  unfold refines; grind

theorem BasicSierpinskian.or_refines (bs1 bs2 : BasicSierpinskian) : (bs1.or bs2).refines bs1 := by
  cases bs1; cases bs2; repeat trivial


theorem all_plus_implies_all_le {p : Nat → Prop} (m : Nat) :
  (forall k, p (m + k)) → (forall n, m ≤ n → p n) :=
by
  intro Hk n Hmlen ; let k := n - m; specialize Hk k
  have Hn : m+k=n := by exact Nat.add_sub_of_le Hmlen
  rw [←Hn]; exact Hk

theorem weak_implies_strong_induction {p : Nat → Prop} :
  (forall k, p k → p k.succ) → (forall m, p m → ∀ n, m ≤ n → p n) :=
by
  intros H m Hpm
  apply all_plus_implies_all_le
  intro k; induction k
  · case zero => exact Hpm
  · case succ k IHk => exact (H (m+k) IHk)

theorem Sierpinskian.weak_monotone_implies_monotone (s : Nat → BasicSierpinskian) :
  (forall m, BasicSierpinskian.refines (s (m.succ)) (s m)) → Sierpinskian.is_monotone s :=
by
  unfold Sierpinskian.is_monotone
  intros H m n
  apply weak_implies_strong_induction
  intro k; apply BasicSierpinskian.refines_trans (s k)
  · exact H k
  · exact BasicSierpinskian.refines_refl (s m)


def Sierpinskian.true_from_seq (s : Nat → BasicSierpinskian) : Nat → BasicSierpinskian :=
  fun n ↦ match n with | Nat.zero => s n | Nat.succ m => BasicSierpinskian.or (true_from_seq s m) (s n)

theorem Sierpinskian.true_from_seq_succ s : forall m,
  true_from_seq s (m.succ) = BasicSierpinskian.or (true_from_seq s m) (s (m.succ)) :=
by
  intro m; rfl

theorem Sierpinskian.true_from_seq_monotone (s : Nat → BasicSierpinskian)
  : Sierpinskian.is_monotone (true_from_seq s) :=
by
  apply weak_monotone_implies_monotone
  intro m
  apply BasicSierpinskian.or_refines

def Sierpinskian.true_from (s : Nat → BasicSierpinskian) : Sierpinskian :=
  Sierpinskian.mk (true_from_seq s) (true_from_seq_monotone s)


def BasicSierpinskian.ofSumBool {P Q} (b : SumBool P Q) : BasicSierpinskian :=
  match b with
  | SumBool.case1 _ => BasicSierpinskian.true
  | SumBool.case2 _ => BasicSierpinskian.indeterminate

theorem BasicSierpinskian.implies_refines : forall {Q1 Q2} (q1 : SumBool Q1 ¬Q1) (q2 : SumBool Q2 ¬Q2),
    (Q1 → Q2) → BasicSierpinskian.refines (ofSumBool q2) (ofSumBool q1) := by
  intros Q1 Q2 q1 q2 HQ
  unfold ofSumBool; unfold refines
  cases q1; all_goals cases q2; all_goals simp_all only [imp_self]
  contradiction


def SumSierpinskian.toSierpinskian {P : Prop} {Q : Nat → Prop}
    (WhyQnP : P ↔ exists n, Q n) (DecQ : forall n, Decidable (Q n))
      (s : SumSierpinskian WhyQnP DecQ) : Sierpinskian :=
  match s with
  | .mk proved =>
      Sierpinskian.true_from (fun n => BasicSierpinskian.ofSumBool (proved n))

def StrongSumSierpinskian.toSierpinskian {P : Prop} {Q : Nat → Prop}
    (whyQnP : P ↔ ∃ n, Q n) (decQ) (monoQ)
    (s : StrongSumSierpinskian whyQnP decQ monoQ) : Sierpinskian :=
  match s with
  | .mk proved proved_mono => by
      let sq := fun n => BasicSierpinskian.ofSumBool (proved n)
      have sq_mono : Sierpinskian.is_monotone sq := by
        apply Sierpinskian.weak_monotone_implies_monotone
        intro m; specialize (proved_mono m)
        apply BasicSierpinskian.implies_refines
        exact proved_mono
      exact Sierpinskian.mk sq sq_mono
