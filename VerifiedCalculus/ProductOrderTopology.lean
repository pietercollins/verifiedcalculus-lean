/-
Copyright  2026  Pieter Collins
Released under the GNU GPLv3 as described in the file LICENSE.
Authors: Pieter Collins
-/

import Mathlib.Data.Real.Basic
import Mathlib.Topology.Order.Basic

namespace RTwo

#print OrderTopology


def zero : ℝ := (0 : ℝ)
def one : ℝ := (1 : ℝ)
def one_one : ℝ × ℝ := (one,one)
#check one_one ≤ one_one


def singleton {α : Type} (a : α) : Set α := fun x ↦ x = a

theorem generator_open {α : Type} :
  forall (g : Set (Set α)) (U : Set α), g U →
    (TopologicalSpace.generateFrom g).IsOpen U := by
  intros g U HgU
  unfold TopologicalSpace.IsOpen TopologicalSpace.generateFrom
  exact TopologicalSpace.GenerateOpen.basic U HgU

theorem order_topology_upper_open {α : Type} [Preorder α] :
    forall a : α, (Preorder.topology α).IsOpen (Set.Ioi a) := by
  intro a; apply generator_open; exists a; left; rfl

theorem order_topology_lower_open {α : Type} [Preorder α] :
    forall a : α, (Preorder.topology α).IsOpen (Set.Iio a) := by
  intro a; apply generator_open; exists a; right; rfl

theorem order_topology_interval_open {α : Type} [Preorder α] :
    forall a b : α, (Preorder.topology α).IsOpen (Set.Ioo a b) := by
  intros a b; rw [Eq.symm Set.Ioi_inter_Iio]
  apply @TopologicalSpace.isOpen_inter α (Preorder.topology α)
  · exact order_topology_upper_open a
  · exact order_topology_lower_open b

theorem interval_open_eq {α : Type} [Preorder α] :
    forall a b : α, (Set.Ioo a b) = {x:α | a<x ∧ x<b} := by
  intros a b; rfl

theorem order_topology_open_interval {α : Type} [Preorder α] :
    forall a b : α, (Preorder.topology α).IsOpen ({x:α|a<x∧x<b}) := by
  intros a b; rw [←interval_open_eq a b]; exact order_topology_interval_open a b




#check add_lt_add_iff_right


theorem zero_lt_one : zero < one  := by exact Real.zero_lt_one
theorem sub_one_lt : forall a : ℝ, a - 1 < a := by
    intro a;
    have Ha10 : a-1 < a-0 := by exact sub_lt_sub_left zero_lt_one a
    have Ha0 : a-0 = a := by exact sub_zero a
    exact lt_of_lt_of_eq Ha10 Ha0

theorem lt_add_one : forall a : ℝ, a < a + 1:= by
    intro a;
    have Ha01 : a+0 < a+1 := by exact add_lt_add_right zero_lt_one a
    have Ha0 : a = a+0 := by exact Eq.symm (add_zero a)
    exact lt_of_eq_of_lt Ha0 Ha01

private theorem pair_pair_le : forall {a b c d : ℝ},
  (a,b) ≤ (c,d) ↔ a ≤ c ∧ b ≤ d := by intros ab cd; rfl
private theorem prod_prod_le : forall {ab cd : ℝ×ℝ},
  ab ≤ cd ↔ ab.fst ≤ cd.fst ∧ ab.snd ≤ cd.snd := by intros ab cd; rfl
private theorem prod_pair_le : forall {ab : ℝ×ℝ} {c d : ℝ},
  ab ≤ (c,d) ↔ ab.fst ≤ c ∧ ab.snd ≤ d := by intros ab c d; rfl
private theorem pair_prod_le : forall {a b : ℝ} {cd : ℝ×ℝ},
  (a,b) ≤ cd ↔ a ≤ cd.fst ∧ b ≤ cd.snd := by intros a b cd; rfl

private theorem vertical_intersection : forall a b c : ℝ, { (x,y) | (a=x) ∧ (b<y∧y<c) } =
      { (x,y) | (a,b)≤(x,y)∧¬((x,y)≤(a,b)) } ∩ { (x,y) | (x,y)≤(a,c)∧¬((a,c)≤(x,y)) } := by
    intros a b c
    simp only [Prod.mk.eta]
    refine Set.ext ?_
    intro xy
    apply Iff.intro
    · intro H
      simp only [Set.mem_setOf_eq] at H
      refine Set.mem_inter ?_ ?_
      · apply And.intro
        · apply pair_prod_le.mpr
          apply And.intro
          · exact le_of_eq H.left
          · exact Std.le_of_lt H.right.left
        · intro Hf
          replace Hf := (prod_pair_le.mp Hf).right
          replace H := H.right.left
          apply lt_irrefl b
          exact Std.lt_of_lt_of_le H Hf
      · simp only [Set.mem_setOf_eq]
        apply And.intro
        · apply prod_pair_le.mpr
          apply And.intro
          · exact le_of_eq (Eq.symm H.left)
          · exact Std.le_of_lt H.right.right
        · intro Hf
          replace Hf := (prod_pair_le.mp Hf).right; simp only at Hf
          replace H := H.right.right
          apply lt_irrefl c
          exact Std.lt_of_le_of_lt Hf H
    · simp only [Set.mem_inter_iff, Set.mem_setOf_eq, and_imp]
      intros Hlab Hnuab Huac Hnlac
      have Hla := (prod_pair_le.mp Hlab).left; simp only at Hla
      have Hua := (prod_pair_le.mp Huac).left; simp only at Hua
      have Ha : a = xy.fst := by apply le_antisymm Hla Hua
      apply And.intro
      · exact Ha
      · apply And.intro
        · have Hlb := (prod_pair_le.mp Hlab).right; simp only at Hlb
          apply lt_of_le_not_ge
          · exact Hlb
          · intro Hbf
            apply Hnuab
            refine Prod.le_def.mpr ?_
            apply And.intro
            · exact Hua
            · exact Hbf
        · have Huc := (prod_pair_le.mp Huac).right; simp only at Huc
          apply lt_of_le_not_ge
          · exact Huc
          · intro Hcf
            apply Hnlac
            refine Prod.le_def.mpr ?_
            apply And.intro
            · exact Hla
            · exact Hcf

def switch (ab : ℝ × ℝ) := (ab.snd,ab.fst)

private theorem switch_switch_eq_id : forall {ab : ℝ×ℝ}, switch (switch ab) = ab := by
  intro ab; unfold switch; simp only [Prod.mk.eta]

private theorem switch_le : forall {ab xy : ℝ×ℝ}, ab ≤ xy ↔ (switch ab) ≤ (switch xy) := by
  intros ab xy
  apply Iff.intro
  · unfold switch
    intro Hab
    apply pair_pair_le.mp at Hab
    apply pair_pair_le.mpr
    simp_all
  · unfold switch
    intro Hab
    apply pair_pair_le.mp at Hab
    apply pair_pair_le.mpr
    simp_all

private theorem switch_le_eq : forall {ab xy : ℝ×ℝ}, (ab ≤ xy) = ( (switch ab) ≤ (switch xy) ) := by
  intro ab xy; exact propext (@switch_le ab xy)

def switch_set (S : Set (ℝ × ℝ)) := { yx : ℝ × ℝ | S (switch yx) }

private theorem switch_switch_set_eq_id : ∀ {S : Set (ℝ×ℝ)}, switch_set (switch_set S) = S := by
  intro S; unfold switch_set; refine Set.ext ?_; intro xy
  apply Iff.intro
  · intro H; congr
  · intro H; rw [←@switch_switch_eq_id xy]; congr


theorem switch_set_eq : ∀ {S1 S2 : Set (ℝ × ℝ)},
    S1 = S2 ↔ (switch_set S1) = (switch_set S2) := by
  intros S1 S2
  apply Iff.intro
  · intro H; rw [H]
  · intro H
    rw [←@switch_switch_set_eq_id S1]
    rw [←@switch_switch_set_eq_id S2]
    rw [H]

private theorem horizontal_intersection : forall a b c : ℝ, { (x,y) | (a<x∧x<b) ∧ (y=c) } =
      { (x,y) | (a,c)≤(x,y)∧¬((x,y)≤(a,c)) } ∩ { (x,y) | (x,y)≤(b,c)∧¬((b,c)≤(x,y)) } := by
    intros a b c
    simp only [Prod.mk.eta]
    refine Set.ext ?_
    intro xy
    apply Iff.intro
    · intro H
      simp only [Set.mem_setOf_eq] at H
      refine Set.mem_inter ?_ ?_
      · apply And.intro
        · apply pair_prod_le.mpr
          apply And.intro
          · exact Std.le_of_lt H.left.left
          · exact le_of_eq (Eq.symm H.right)
        · intro Hf
          replace Hf := (prod_pair_le.mp Hf).left
          replace H := H.left.left
          apply lt_irrefl a
          exact Std.lt_of_lt_of_le H Hf
      · simp only [Set.mem_setOf_eq]
        apply And.intro
        · apply prod_pair_le.mpr
          apply And.intro
          · exact Std.le_of_lt H.left.right
          · exact le_of_eq H.right
        · intro Hf
          replace Hf := (prod_pair_le.mp Hf).left; simp only at Hf
          replace H := H.left.right
          apply lt_irrefl b
          exact Std.lt_of_le_of_lt Hf H
    · simp only [Set.mem_inter_iff, Set.mem_setOf_eq, and_imp]
      intros Hlac Hnuac Hubc Hnlbc
      have Hlc := (prod_pair_le.mp Hlac).right; simp only at Hlc
      have Huc := (prod_pair_le.mp Hubc).right; simp only at Huc
      have Hc : c = xy.snd := by apply le_antisymm Hlc Huc
      apply And.intro
      · apply And.intro
        · have Hla := (prod_pair_le.mp Hlac).left; simp only at Hla
          apply lt_of_le_not_ge
          · exact Hla
          · intro Haf
            apply Hnuac
            refine Prod.le_def.mpr ?_
            apply And.intro
            · exact Haf
            · exact Huc
        · have Hub := (prod_pair_le.mp Hubc).left; simp only at Hub
          apply lt_of_le_not_ge
          · exact Hub
          · intro Hbf
            apply Hnlbc
            refine Prod.le_def.mpr ?_
            apply And.intro
            · exact Hbf
            · exact Hlc
      · exact Eq.symm Hc

private theorem horizontal_vertical_intersection : forall a b : ℝ, { (x,y) | (a=x) ∧ (b=y) } =
    { (x,y) | (a=x) ∧ (b-one<y∧y<b+one) } ∩ { (x,y) | (a-one<x ∧ x<a+one) ∧ (y=b) } := by
  intros a b
  refine Set.ext ?_
  intro xy
  apply Iff.intro
  · simp only [Set.mem_setOf_eq, Set.mem_inter_iff, and_imp]
    intro Ha Hb
    apply And.intro;
    · apply And.intro
      · exact Ha
      · apply And.intro
        · rw [←Hb]; exact sub_one_lt b
        · rw [←Hb]; exact lt_add_one b
    · apply And.intro
      · apply And.intro
        · rw [←Ha]; exact sub_one_lt a
        · rw [←Ha]; exact lt_add_one a
      · exact Eq.symm Hb
  · simp only [Set.mem_inter_iff, Set.mem_setOf_eq, and_imp]
    intro Ha _ _ _ _ Hb
    apply And.intro
    · exact Ha
    · exact Eq.symm Hb


def PreorderTopology_RTwo := Preorder.topology (ℝ×ℝ)

#print PreorderTopology_RTwo

theorem PreorderTopology_RTwo_is_discrete :
  forall ab : ℝ × ℝ , PreorderTopology_RTwo.IsOpen (singleton ab) :=
by
  let is_open := PreorderTopology_RTwo.IsOpen
  have Hu : forall a b : ℝ, is_open { (x,y) | (a,b)≤(x,y)∧¬((x,y)≤(a,b)) } := by
    intros a b; exact order_topology_upper_open (a,b)
  have Hl : forall a b : ℝ, is_open { (c,d) | (c,d)≤(a,b)∧¬((a,b)≤(c,d)) } := by
    intros a b; exact order_topology_lower_open (a,b)
  have Hv : forall a b c : ℝ, is_open { (x,y) | (a=x) ∧ (b<y∧y<c) } := by
    intros a b c
    rw [vertical_intersection a b c]
    apply @TopologicalSpace.isOpen_inter (ℝ×ℝ) (Preorder.topology (ℝ×ℝ))
    · apply Hu
    · apply Hl
  have Hh : forall a b c : ℝ, is_open { (x,y) | (a<x ∧ x<b) ∧ (y=c) } := by
    intros a b c
    rw [horizontal_intersection a b c]
    apply @TopologicalSpace.isOpen_inter (ℝ×ℝ) (Preorder.topology (ℝ×ℝ))
    · apply Hu
    · apply Hl
  have Ho : forall a b : ℝ, is_open { (x,y) | (a=x) ∧ (b=y) } := by
    intros a b
    rw [horizontal_vertical_intersection a b]
    apply @TopologicalSpace.isOpen_inter (ℝ×ℝ) (Preorder.topology (ℝ×ℝ))
    · apply Hv a (b-one) (b+one)
    · apply Hh (a-one) (a+one) b
  have His : forall ab : ℝ×ℝ, (singleton ab) = { (x,y) | (ab.fst=x) ∧ (ab.snd=y) } := by
    intros ab
    unfold singleton
    refine Set.ext ?_
    intro xy
    simp only [Set.mem_setOf_eq]
    unfold Membership.mem; unfold Set.instMembership; unfold Set.Mem
    simp only
    apply @Iff.trans _ (ab=xy) _
    · exact eq_comm
    · exact Prod.ext_iff
  have Hs : forall ab : ℝ×ℝ, is_open (singleton ab) := by
    intros ab
    rw [His]
    exact Ho ab.fst ab.snd
  intro ab; exact Hs ab
