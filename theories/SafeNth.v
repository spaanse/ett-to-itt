From Coq Require Import List Lia.
Require Import Tactics.

Program Fixpoint safe_nth {A} (n : nat) (l : list A) (isdecl : n < length l) : A :=
  match l with
  | nil => _
  | hd :: tl =>
    match n with
    | 0 => hd
    | S n => safe_nth n tl _
    end
  end.
Next Obligation.
  exfalso. simpl in isdecl. inversion isdecl.
Defined.
Next Obligation.
  simpl in isdecl. auto with arith.
Defined.

Lemma safe_nth_proof_irrelevant {A} (n : nat) (l : list A) (isdecl isdecl' : n < length l)
: safe_nth n l isdecl = safe_nth n l isdecl'.
Proof.
  revert l isdecl isdecl'. induction n; intros l isdecl isdecl'.
  - destruct l.
    + simpl in *. lia.
    + reflexivity.
  - destruct l.
    + simpl in *. lia.
    + simpl. apply IHn.
Qed.

Program Lemma safe_nth_rewrite {A} (n m : nat) (l : list A) (isdecl : n < length l) (eq : n = m)
: safe_nth n l isdecl = safe_nth m l _.
Proof.
  subst. apply safe_nth_proof_irrelevant.
Qed.

Lemma safe_nth_concat {A} (n : nat) (l1 l2 : list A) (isdecl : n < length (l1++l2)) (isdecl' : n < length l1)
: safe_nth n (l1 ++ l2) isdecl = safe_nth n l1 isdecl'.
Proof.
  revert n isdecl isdecl'. induction l1; intros n isdecl isdecl'; simpl in *. { lia. }
  destruct n; simpl in *. { reflexivity. }
  apply IHl1.
Qed.

Lemma safe_nth_concat' {A} (n : nat) (l1 l2 : list A) (isdecl : n + length l1 < length (l1++l2)) (isdecl' : n < length l2)
: safe_nth (n + length l1) (l1 ++ l2) isdecl = safe_nth n l2 isdecl'.
Proof.
  revert n isdecl isdecl'. induction l1; intros n isdecl isdecl'; simpl in *.
  - erewrite safe_nth_rewrite, safe_nth_proof_irrelevant. f_equal.
  - assert (eq : n + S (length l1) = S (n + length l1)) by lia.
    rewrite safe_nth_rewrite with _ _ _ _ eq. erewrite safe_nth_proof_irrelevant.
    erewrite <- IHl1.
    reflexivity.
    Unshelve.
    { lia. }
    { simpl. lia. }
Qed.