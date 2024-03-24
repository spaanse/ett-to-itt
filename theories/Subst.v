From Coq Require Import Nat Lia List Arith.PeanoNat Logic.FunctionalExtensionality.
Require Import Ast Tactics.

Section Subst.

Definition id : nat -> nat :=
  fun i => i.

Definition jump (n : nat) : nat -> nat :=
  fun i => i+n.

Definition unjump (n : nat) : nat -> nat :=
  fun i => i-n.

Definition skip (f : nat -> nat) (n : nat) : nat -> nat :=
  fun i => if ltb i n then i else f (i-n) + n.

Fixpoint update_rel (f : nat -> nat) (t : term) : term :=
match t with
| tRel i => 
    tRel (f i)
| tLambda t => tLambda (update_rel (skip f 1) t)
| tApp u v => tApp (update_rel f u) (update_rel f v)
| tProd A B => tProd (update_rel f A) (update_rel (skip f 1) B)
| tSum A B => tSum (update_rel f A) (update_rel (skip f 1) B)
| tPair u v => tPair (update_rel f u) (update_rel f v)
| tPi1 p => tPi1 (update_rel f p)
| tPi2 p => tPi2 (update_rel f p)
| tSort s => tSort s
end.

Definition lift0 n t := (update_rel (jump n) t).
Definition lift n k t := (update_rel (skip (jump n) k) t).
Definition unlift0 n t := (update_rel (unjump n) t).
Definition unlift n k t := (update_rel (skip (unjump n) k) t).

Lemma skip_0 (f : nat -> nat)
: skip f 0 = f.
Proof.
  unfold skip.
  apply functional_extensionality. intro i.
  comp_cases.
  rewrite Nat.add_0_r. f_equal. lia.
Qed.

Lemma skip_skip (f : nat -> nat) (n m : nat)
: skip (skip f n) m = skip f (n+m).
Proof.
  unfold skip.
  apply functional_extensionality. intro i.
  comp_cases.
  rewrite Nat.add_assoc. f_equal. f_equal. f_equal. lia.
Qed.

Lemma skip_id (k : nat)
: skip id k = id.
Proof.
  unfold skip.
  apply functional_extensionality. intro i.
  comp_cases.
  unfold id. lia.
Qed.

Lemma jump_0
: jump 0 = id.
Proof.
  unfold jump.
  apply functional_extensionality. intro i.
  unfold id. lia.
Qed.

Lemma jump_jump (n m : nat)
: (fun i => jump n (jump m i)) = jump (n+m).
Proof.
  unfold jump.
  apply functional_extensionality. intro i.
  lia.
Qed.

Lemma unjump_jump (n : nat)
: (fun i => unjump n (jump n i)) = id.
Proof.
  unfold unjump, jump, id.
  apply functional_extensionality. intro i.
  lia.
Qed.

Lemma update_rel_id (t : term)
: update_rel id t = t.
Proof.
  assert (k : nat). { exact 0. }
  rewrite <- (skip_id k).
  revert k. induction t; intro k; simpl; f_equal; eauto.
  - rewrite skip_id. reflexivity.
  - rewrite skip_skip. apply IHt2.
  - rewrite skip_skip. apply IHt.
  - rewrite skip_skip. apply IHt2.
Qed.

Lemma update_rel_comp' (f g : nat -> nat) (k : nat) (t : term)
: update_rel (skip g k) (update_rel (skip f k) t) = update_rel (skip (fun i => g (f i)) k) t.
Proof.
  revert k; induction t; intro k; simpl; f_equal; eauto.
  - unfold skip; comp_cases; f_equal; f_equal; lia.
  - repeat rewrite skip_skip.
    apply IHt2.
  - repeat rewrite skip_skip.
    apply IHt.
  - repeat rewrite skip_skip.
    apply IHt2.
Qed.

Lemma update_rel_comp (f g : nat -> nat) (t : term)
: update_rel g (update_rel f t) = update_rel (fun i => g (f i)) t.
Proof.
  rewrite <- (skip_0 g), <- (skip_0 f).
  rewrite update_rel_comp'.
  repeat rewrite skip_0.
  reflexivity.
Qed.

Fixpoint liftc (n k : nat) (l : list term) : list term :=
match l with
  | nil => nil
  | x :: xs => (lift n (k + length xs) x) :: (liftc n k xs)
end.

Fixpoint subst (t : term) (k : nat) (u : term) :=
match u with
  | tRel n =>
      match n ?= k with
      | Eq => lift0 k t
      | Lt => tRel n
      | Gt => tRel (pred n)
      end
  | tLambda M => tLambda (subst t (S k) M)
  | tApp u v => tApp (subst t k u) (subst t k v)
  | tProd A B => tProd (subst t k A) (subst t (S k) B)
  | tSum A B => tSum (subst t k A) (subst t (S k) B)
  | tPair u v => tPair (subst t k u) (subst t k v)
  | tPi1 p => tPi1 (subst t k p)
  | tPi2 p => tPi2 (subst t k p)
  | tSort s => tSort s
end.

Definition subst0 t u := (subst t 0 u).

Lemma unlift_lift (n k : nat) (t : term) : unlift n k (lift n k t) = t.
Proof.
  unfold unlift, lift.
  rewrite update_rel_comp'.
  rewrite unjump_jump, skip_id.
  apply update_rel_id.
Qed.

Lemma unlift0_lift0 (n : nat) (t : term) : unlift0 n (lift0 n t) = t.
Proof.
  unfold unlift0, lift0.
  rewrite update_rel_comp.
  rewrite unjump_jump.
  apply update_rel_id.
Qed.

Lemma lift0_lift (k : nat)
: lift0 k = lift k 0.
Proof.
  unfold lift0, lift.
  rewrite skip_0.
  reflexivity.
Qed.

Lemma lift0k (u : term) (k : nat)
: lift 0 k u = u.
Proof.
  unfold lift.
  rewrite jump_0, skip_id.
  apply update_rel_id.
Qed.

Lemma liftc0k (l : list term) (k : nat)
: liftc 0 k l = l.
Proof.
  revert k. induction l; intro k; simpl.
  - reflexivity.
  - rewrite lift0k. rewrite IHl. reflexivity.
Qed.

Lemma lift_add (u : term) (n m k : nat)
: lift n k (lift m k u) = lift (n+m) k u.
Proof.
  unfold lift.
  rewrite update_rel_comp', jump_jump.
  reflexivity.
Qed.

Lemma liftc_length (l : list term) (n k : nat)
: length (liftc n k l) = length l.
Proof.
  revert k. induction l; intro k; simpl.
  - reflexivity.
  - rewrite IHl. reflexivity.
Qed.

Lemma liftc_add (l : list term) (n m k : nat)
: liftc n k (liftc m k l) = liftc (n+m) k l.
Proof.
  induction l; simpl. { reflexivity. }
  rewrite liftc_length. f_equal.
  - apply lift_add.
  - apply IHl.
Qed.

Lemma lift0_add (u : term) (n m : nat)
: lift0 n (lift0 m u) = lift0 (n+m) u.
Proof.
  unfold lift0.
  rewrite update_rel_comp, jump_jump.
  reflexivity.
Qed.

Lemma subst_lift (u v : term) (n k i : nat) (k_lt_i : k <= i) (i_le_nk : i <= n + k)
: subst u i (lift (S n) k v) = lift n k v.
Proof.
  revert k i k_lt_i i_le_nk. induction v; intros k i k_lt_i i_le_nk;
  unfold lift, update_rel; fold update_rel; simpl; f_equal; eauto with arith.
  - unfold skip, jump; comp_cases. f_equal. lia.
  - repeat rewrite skip_skip. apply IHv2; lia.
  - repeat rewrite skip_skip. apply IHv; lia.
  - repeat rewrite skip_skip. apply IHv2; lia.
Qed.

Lemma subst_lift0 (u v : term) (n : nat)
: subst u n (lift0 (S n) v) = lift0 n v.
Proof.
  repeat rewrite lift0_lift.
  apply subst_lift; lia.
Qed.

Lemma lift_lift (u : term) (n m k i : nat) (k_le_m : k <= m)
: lift n (i+k) (lift m i u) = lift n i (lift m i u).
Proof.
  unfold lift.
  repeat rewrite update_rel_comp. f_equal.
  apply functional_extensionality. intro x.
  unfold skip, jump. comp_cases.
Qed.
End Subst.

Ltac subst_helper :=
repeat match goal with
| _ => progress fold update_rel
| |- context [ skip (skip ?f ?n) ?m ] => rewrite (skip_skip f n m)
| |- context [ update_rel (skip (jump ?n) ?k) ] => replace (update_rel (skip (jump n) k)) with (lift n k) by reflexivity
end.