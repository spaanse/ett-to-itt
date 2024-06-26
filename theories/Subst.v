From Coq Require Import Nat Lia List Arith.PeanoNat Logic.FunctionalExtensionality.
Require Import Ast Tactics.
Open Scope t_scope.
Reserved Notation "t [ u ]" (at level 7, left associativity).
Reserved Notation "t [ u1 , u2 , .. , un ]" (at level 7, left associativity).
Reserved Notation "t [ n ← u ]" (at level 7, left associativity).

Section Subst.
Declare Scope subst_scope.
Open Scope subst_scope.

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
| ^i => ^(f i)
| λ, t => λ, update_rel (skip f 1) t
| u @ v => (update_rel f u) @ (update_rel f v)
| ∏A, B => ∏update_rel f A, update_rel (skip f 1) B
| ∑A, B => ∑update_rel f A, update_rel (skip f 1) B
| ⟨u, v⟩ => ⟨update_rel f u, update_rel f v⟩
| π₁ p => π₁ (update_rel f p)
| π₂ p => π₂ (update_rel f p)
| *s => *s
| u == v => (update_rel f u) == (update_rel f v)
| Refl(u) => Refl(update_rel f u)
| J(t, p) => J(update_rel (skip f 1) t, update_rel f p)

| tTransport p t => tTransport (update_rel f p) (update_rel f t)
end.

Notation lift n k t := (update_rel (skip (jump n) k) t).
Notation unlift n k t := (update_rel (skip (unjump n) k) t).

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
  unfold skip, id.
  apply functional_extensionality. intro i.
  comp_cases.
Qed.

Lemma jump_0
: jump 0 = id.
Proof.
  unfold jump, id.
  apply functional_extensionality. intro i.
  lia.
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
  | ^n =>
      match n ?= k with
      | Eq => lift k 0 t
      | Lt => ^n
      | Gt => ^(pred n)
      end
  | *s => *s
  | λ, M => λ, M[S k ← t]
  | u @ v => u[k ← t] @ v[k ← t]
  | ∏A, B => ∏A[k ← t], B[S k ← t]
  | ∑A, B => ∑A[k ← t], B[S k ← t]
  | ⟨u, v⟩ => ⟨u[k ← t], v[k ← t]⟩
  | π₁ p => π₁ p[k ← t]
  | π₂ p => π₂ p[k ← t]
  | u == v => u[k ← t] == v[k ← t]
  | Refl(u) => Refl(u[k← t])
  | J(u, p) => J(u[S k ← t], p[k ← t])

  | tTransport p u => tTransport p[k ← t] u[k ← t]
end
where "t [ n ← u ]" := (subst u n t) : subst_scope.
Notation "t [ n ← u ]" := (subst u n t) : subst_scope.
Notation "t [ u ]" := (subst u 0 t) : subst_scope.
Notation "t [ u1 , u2 , .. , un ]" := (subst u1 0 (subst u2 0 .. (subst un 0 t) .. )) : subst_scope.


Lemma unlift_lift (n k : nat) (t : term) : unlift n k (lift n k t) = t.
Proof.
  rewrite update_rel_comp'.
  rewrite unjump_jump, skip_id.
  apply update_rel_id.
Qed.

Lemma lift0k (u : term) (k : nat)
: lift 0 k u = u.
Proof.
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
: (lift (S n) k v)[i ← u] = lift n k v.
Proof.
  revert k i k_lt_i i_le_nk. induction v; intros k i k_lt_i i_le_nk;
  simpl; f_equal; eauto with arith.
  - unfold skip, jump; comp_cases. f_equal. lia.
  - repeat rewrite skip_skip. apply IHv2; lia.
  - repeat rewrite skip_skip. apply IHv; lia.
  - repeat rewrite skip_skip. apply IHv2; lia.
  - repeat rewrite skip_skip. apply IHv1; lia.
Qed.

Lemma lift_lift (u : term) (n m k i : nat) (k_le_m : k <= m)
: lift n (i+k) (lift m i u) = lift n i (lift m i u).
Proof.
  repeat rewrite update_rel_comp. f_equal.
  apply functional_extensionality. intro x.
  unfold skip, jump. comp_cases.
Qed.

Lemma lift_lift' (u : term) (n k : nat)
: lift 1 0 (lift n k u) = lift n (k + 1) (lift 1 0 u).
Proof.
  repeat rewrite update_rel_comp. f_equal.
  apply functional_extensionality. intro x.
  unfold skip, jump. comp_cases.
Qed.
End Subst.

Declare Scope subst_scope.
Open Scope subst_scope.
Notation "t [ n ← u ]" := (subst u n t) : subst_scope.
Notation "t [ u ]" := (subst u 0 t) : subst_scope.
Notation "t [ u1 , u2 , .. , un ]" := (subst u1 0 (subst u2 0 .. (subst un 0 t) .. )) : subst_scope.
Notation lift n k t := (update_rel (skip (jump n) k) t).
Notation unlift n k t := (update_rel (skip (unjump n) k) t).

Ltac subst_helper :=
repeat match goal with
| _ => progress fold update_rel
| |- context [ jump ?n (jump ?m ?i) ] => rewrite (jump_jump' n m)
| |- context [ skip (skip ?f ?n) ?m ] => rewrite (skip_skip f n m)
(* | |- context [ update_rel (skip (jump ?n) ?k) ] => replace (update_rel (skip (jump n) k)) with (lift n k) by reflexivity *)
| H : context [ jump ?n (jump ?m ?i) ] |- _ => rewrite (jump_jump' n m) in H
| H : context [ skip (skip ?f ?n) ?m ] |- _ => rewrite (skip_skip f n m) in H
(* | H : context [ update_rel (skip (jump ?n) ?k) ] |- _ => replace (update_rel (skip (jump n) k)) with (lift n k) in H by reflexivity *)
end.

Lemma lift_subst (u v : term) (n k i : nat)
: lift n (k + i) (v[i ← u]) = (lift n (S k + i) v)[i ← lift n k u].
Proof.
  revert n k i; induction v; intros m k i;
  unfold subst; simpl; subst_helper; fold subst;
  [ | (f_equal; eauto) .. ];
  try replace (S (k + i) + 1) with (S k + S i) by lia;
  try replace (k + i + 1) with (k + S i) by lia; eauto.
  unfold skip, jump; comp_cases;
  [ repeat rewrite update_rel_comp | .. ];
  simpl; f_equal; comp_cases.
  apply functional_extensionality. intro x.
  comp_cases.
Qed.

Lemma lift_subst' (u v : term) (n k i : nat)
: lift k i v[n + i ← u] = (lift k i v)[n + k + i ← u].
Proof.
  revert n k i. induction v; intros m k i; simpl;
  simpl; subst_helper; [| |f_equal ..]; eauto.
  { unfold skip, jump. comp_cases.
    + simpl. f_equal. comp_cases.
    + rewrite update_rel_comp. f_equal.
      apply functional_extensionality. intro x.
      comp_cases.
    + simpl. f_equal. comp_cases.
    + simpl. f_equal. comp_cases.
  }
  all: replace (i + 1) with (S i) by lia.
  all: replace (S (m + i)) with (m + S i) by lia.
  - rewrite IHv2. f_equal. lia.
  - rewrite IHv. f_equal. lia.
  - rewrite IHv2. f_equal. lia.
  - rewrite IHv1. f_equal. lia.
Qed.

Lemma subst_subst (u v t : term) (m k : nat)
: t[S m + k ← u][k ← v[m ← u]] = t[k ← v][m + k ← u].
Proof.
  revert u m k; induction t; intros u m k;
  simpl; [comp_cases; simpl; comp_cases|f_equal ..]; eauto.
  { rewrite subst_lift by lia.
    reflexivity. }
  { replace m with (m + 0) by lia.
    rewrite lift_subst'.
    f_equal. lia. }
  all: replace (S (S (m + k))) with (S m + S k) by lia.
  - rewrite IHt2. f_equal. lia.
  - rewrite IHt. f_equal. lia.
  - rewrite IHt2. f_equal. lia.
  - rewrite IHt1. f_equal. lia.
Qed.

Lemma lift_subst_rel (v : term) (i : nat)
: (lift 1 (S i) v) [i ← ^0] = v.
Proof.
  revert i. induction v; intros i; simpl; subst_helper;
  replace (S i + 1) with (S (S i)) by lia;
  try f_equal; eauto.
  unfold skip, jump. comp_cases; f_equal; lia.
Qed.

Lemma lift_subst_rel0 (v : term) (k : nat)
: (lift 1 1 v)[0 ← ^0] = v.
Proof.
  replace k with (k + 0) by lia.
  replace ^(k+0) with ^k by (f_equal; lia).
  apply lift_subst_rel.
Qed.

Lemma lift_injective (u v : term) (n k : nat)
: lift n k u = lift n k v -> u = v.
Proof.
  revert v n k; induction u; intros v m k ulvl;
  destruct v; try discriminate ulvl;
  simpl in ulvl; subst_helper;
  try (injection ulvl; intros; f_equal; eauto).
  - injection ulvl as ulvl. unfold skip, jump in *.
    f_equal. revert ulvl. comp_cases.
Qed.
