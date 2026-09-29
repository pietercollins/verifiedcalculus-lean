/-
Copyright  2025-26  Pieter Collins
Released under the GNU GPLv3 as described in the file LICENSE.
Authors: Pieter Collins
-/

namespace Induction

private theorem all_plus_implies_all_le {p : Nat → Prop} (m : Nat) :
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

end Induction
