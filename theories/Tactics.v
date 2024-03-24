From Coq Require Import Lia Nat Arith.Compare_dec Arith.Arith.
Ltac comp_cases :=
  repeat match goal with
  | |- _ => progress lia
  | |- _ => progress simplify_eq
  | |- _ => progress reflexivity
  | |- context [Nat.eq_dec ?lhs ?rhs] => destruct (Nat.eq_dec lhs rhs)
  | |- context [?lhs =? ?rhs] => destruct (lhs =? rhs) eqn:?
  | |- context [?lhs <? ?rhs] => destruct (lhs <? rhs) eqn:?
  | |- context [?lhs <=? ?rhs] => destruct (lhs <=? rhs) eqn:?
  | |- context [?lhs ?= ?rhs] => destruct (lhs ?= rhs) eqn:?
  | H : (_ =? _) = true |- _ => apply Nat.eqb_eq in H
  | H : (_ =? _) = false |- _ => apply Nat.eqb_neq in H
  | H : (_ <? _) = true |- _ => apply Nat.ltb_lt in H
  | H : (_ <? _) = false |- _ => apply Nat.ltb_nlt in H
  | H : (_ <=? _) = true |- _ => apply Nat.leb_le in H
  | H : (_ <=? _) = false |- _ => apply Nat.leb_nle in H
  | H : (_ ?= _) = Eq |- _ => apply nat_compare_eq in H
  | H : (_ ?= _) = Lt |- _ => apply nat_compare_Lt_lt in H
  | H : (_ ?= _) = Gt |- _ => apply nat_compare_Gt_gt in H
  end.
