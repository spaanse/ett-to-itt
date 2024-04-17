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
| tEq u v => tEq (update_rel f u) (update_rel f v)
| tRefl u => tRefl (update_rel f u)
| tJ t p => tJ (update_rel (skip f 1) t) (update_rel f p)
end.

Definition lift n k t := (update_rel (skip (jump n) k) t).
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

Lemma jump_jump' (n m i : nat)
: jump n (jump m i) = jump (n+m) i.
Proof.
  unfold jump. lia.
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
  - rewrite skip_skip. apply IHt1.
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
  - repeat rewrite skip_skip.
    apply IHt1.
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
      | Eq => lift k 0 t
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
  | tEq u v => tEq (subst t k u) (subst t k v)
  | tRefl u => tRefl (subst t k u)
  | tJ u p => tJ (subst t (S k) u) (subst t k p)
end.

Lemma unlift_lift (n k : nat) (t : term) : unlift n k (lift n k t) = t.
Proof.
  unfold unlift, lift.
  rewrite update_rel_comp'.
  rewrite unjump_jump, skip_id.
  apply update_rel_id.
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

Lemma subst_lift (u v : term) (n k i : nat) (k_lt_i : k <= i) (i_le_nk : i <= n + k)
: subst u i (lift (S n) k v) = lift n k v.
Proof.
  revert k i k_lt_i i_le_nk. induction v; intros k i k_lt_i i_le_nk;
  unfold lift, update_rel; fold update_rel; simpl; f_equal; eauto with arith.
  - unfold skip, jump; comp_cases. f_equal. lia.
  - repeat rewrite skip_skip. apply IHv2; lia.
  - repeat rewrite skip_skip. apply IHv; lia.
  - repeat rewrite skip_skip. apply IHv2; lia.
  - repeat rewrite skip_skip. apply IHv1; lia.
Qed.

Lemma lift_lift (u : term) (n m k i : nat) (k_le_m : k <= m)
: lift n (i+k) (lift m i u) = lift n i (lift m i u).
Proof.
  unfold lift.
  repeat rewrite update_rel_comp. f_equal.
  apply functional_extensionality. intro x.
  unfold skip, jump. comp_cases.
Qed.

Lemma lift_lift' (u : term) (n k : nat)
: lift 1 0 (lift n k u) = lift n (k + 1) (lift 1 0 u).
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
| |- context [ jump ?n (jump ?m ?i) ] => rewrite (jump_jump' n m)
| |- context [ skip (skip ?f ?n) ?m ] => rewrite (skip_skip f n m)
| |- context [ update_rel (skip (jump ?n) ?k) ] => replace (update_rel (skip (jump n) k)) with (lift n k) by reflexivity
| H : context [ jump ?n (jump ?m ?i) ] |- _ => rewrite (jump_jump' n m) in H
| H : context [ skip (skip ?f ?n) ?m ] |- _ => rewrite (skip_skip f n m) in H
| H : context [ update_rel (skip (jump ?n) ?k) ] |- _ => replace (update_rel (skip (jump n) k)) with (lift n k) in H by reflexivity
end.

Inductive closed_above : nat -> term -> Prop :=
| ca_rel k n : n < k -> closed_above k (tRel n)
| ca_sort k s : closed_above k (tSort s)
| ca_prod k A B : closed_above k A -> closed_above (S k) B -> closed_above k (tProd A B)
| ca_lambda k t : closed_above (S k) t -> closed_above k (tLambda t)
| ca_app k u v : closed_above k u -> closed_above k v-> closed_above k (tApp u v)
| ca_sum k A B : closed_above k A -> closed_above (S k) B -> closed_above k (tSum A B)
| ca_pair k u v : closed_above k u -> closed_above (S k) v -> closed_above k (tPair u v)
| ca_pi1 k u : closed_above k u -> closed_above k (tPi1 u)
| ca_pi2 k u : closed_above k u -> closed_above k (tPi2 u)
.

Lemma closed_above_lt (n k : nat) (t : term) (n_le_k : n <= k)
: closed_above n t -> closed_above k t.
Proof.
  intro closed_t.
  revert k n_le_k. induction closed_t; intros k' n_le_k; cbn.
  - apply ca_rel. lia.
  - apply ca_sort.
  - apply ca_prod; eauto with arith.
  - apply ca_lambda; eauto with arith.
  - apply ca_app; eauto with arith.
  - apply ca_sum; eauto with arith.
  - apply ca_pair; eauto with arith.
  - apply ca_pi1; eauto with arith.
  - apply ca_pi2; eauto with arith.
Qed.

Lemma lift_subst (u v : term) (n k i : nat)
: lift n (k + i) (subst u i v) = subst (lift n k u) i (lift n (S k + i) v).
Proof.
  revert n k i; induction v; intros m k i;
  unfold lift, subst; simpl; subst_helper; fold subst.
  - unfold skip, jump; comp_cases.
    + unfold lift.
      rewrite update_rel_comp, update_rel_comp.
      f_equal. apply functional_extensionality. intro x.
      unfold skip, jump. comp_cases.
    + unfold lift. simpl. f_equal.
      unfold skip, jump. comp_cases.
    + unfold lift. simpl. f_equal.
      unfold skip, jump. comp_cases.
    + unfold lift. simpl. f_equal.
      unfold skip, jump. comp_cases.
  - reflexivity.
  - f_equal.
    + apply IHv1.
    + replace (S (k + i) + 1) with (S k + S i) by lia.
      replace (k + i + 1) with (k + S i) by lia.
      apply IHv2.
  - f_equal.
    replace (S (k + i) + 1) with (S k + S i) by lia.
    replace (k + i + 1) with (k + S i) by lia.
    apply IHv.
  - f_equal.
    + apply IHv1.
    + replace (S (k + i) + 1) with (S k + S i) by lia.
      replace (k + i + 1) with (k + S i) by lia.
      apply IHv2.
  - f_equal.
    + apply IHv1.
    + replace (S (k + i) + 1) with (S k + S i) by lia.
      replace (k + i + 1) with (k + S i) by lia.
      apply IHv2.
  - f_equal.
    + apply IHv1.
    + apply IHv2.
  - f_equal.
    apply IHv.
  - f_equal.
    apply IHv.
  - f_equal.
    + apply IHv1.
    + replace (S (k + i) + 1) with (S k + S i) by lia.
      replace (k + i + 1) with (k + S i) by lia.
      apply IHv2.
  - f_equal.
    apply IHv.
  - f_equal.
    + replace (S (k + i) + 1) with (S k + S i) by lia.
      replace (k + i + 1) with (k + S i) by lia.
      apply IHv1.
    + apply IHv2.
Qed.

Lemma lift_subst' (u v : term) (n k i : nat)
: lift k i (subst u (n + i) v) = subst u (n + k + i) (lift k i v).
Proof.
  revert n k i. induction v; intros m k i; simpl;
  unfold lift; simpl; subst_helper; [| |f_equal ..]; eauto.
  - unfold skip, jump. comp_cases.
    + unfold lift. simpl. f_equal.
      unfold skip, jump. comp_cases.
    + unfold lift. rewrite update_rel_comp. f_equal.
      unfold skip, jump. apply functional_extensionality. intro x.
      comp_cases.
    + unfold lift. simpl. f_equal. unfold skip, jump. comp_cases.
    + unfold lift. simpl. f_equal. unfold skip, jump. comp_cases.
  - replace (i + 1) with (S i) by lia.
    replace (S (m + i)) with (m + S i) by lia.
    rewrite IHv2. f_equal. lia.
  - replace (i + 1) with (S i) by lia.
    replace (S (m + i)) with (m + S i) by lia.
    rewrite IHv. f_equal. lia.
  - replace (i + 1) with (S i) by lia.
    replace (S (m + i)) with (m + S i) by lia.
    rewrite IHv2. f_equal. lia.
  - replace (i + 1) with (S i) by lia.
    replace (S (m + i)) with (m + S i) by lia.
    rewrite IHv1. f_equal. lia.
Qed.

Lemma subst_subst (u v t : term) (m k : nat)
: subst (subst u m v) k (subst u (S m + k) t) = subst u (m + k) (subst v k t).
Proof.
  revert u m k; induction t; intros u m k;
  simpl; [comp_cases; simpl; comp_cases|f_equal ..]; eauto.
  - rewrite subst_lift by lia.
    reflexivity.
  - replace m with (m + 0) by lia.
    rewrite lift_subst'.
    f_equal. lia.
  - replace (S (S (m + k))) with (S m + S k) by lia.
    rewrite IHt2. f_equal. lia.
  - replace (S (S (m + k))) with (S m + S k) by lia.
    rewrite IHt. f_equal. lia.
  - replace (S (S (m + k))) with (S m + S k) by lia.
    rewrite IHt2. f_equal. lia.
  - replace (S (S (m + k))) with (S m + S k) by lia.
    rewrite IHt1. f_equal. lia.
Qed.

Lemma lift_injective (u v : term) (n k : nat)
: lift n k u = lift n k v -> u = v.
Proof.
  revert v n k; induction u; intros v m k ulvl;
  destruct v; try discriminate ulvl;
  unfold lift in ulvl; simpl in ulvl; subst_helper;
  try (injection ulvl; intros; f_equal; eauto).
  - injection ulvl as ulvl. unfold skip, jump in *.
    f_equal. revert ulvl. comp_cases.
Qed.