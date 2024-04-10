From Coq Require Import List Lia.
Require Import Ast Subst.

Reserved Notation "Γ ,, d" (at level 20, d at next level, left associativity, format "'[' Γ ',,' d ']'").
Reserved Notation "Γ ;; Δ" (at level 20, Δ at next level, left associativity, format "'[' Γ ';;' Δ ']'").
Reserved Notation "Γ ⊢ₓ t : T" (at level 50, t, T at next level, format "'[' Γ '//' '⊢ₓ'  t '//' ':'  T ']'").
Reserved Notation "Γ ⊢ₓ t ≡ u : T" (at level 50, t, u, T at next level, format "'[' Γ '//' '⊢ₓ'  t  '≡'  u '//' ':'  T ']'").

Open Scope t_scope.
Section ETT.
Declare Scope x_scope.
Definition context := list term.
Notation "Γ ,, d" := (d :: Γ) : x_scope.
Notation "Γ ;; Δ" := (Δ ++ Γ) : x_scope.

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

Program Lemma safe_nth_concat {A} (n : nat) (l1 l2 : list A) (isdecl : n < length (l1++l2)) (isdecl' : n < length l1)
: safe_nth n (l1 ++ l2) isdecl = safe_nth n l1 isdecl'.
Proof.
  revert n isdecl isdecl'. induction l1; intros n isdecl isdecl'; simpl in *. { lia. }
  destruct n; simpl in *. { reflexivity. }
  apply IHl1.
Qed.

Inductive typed: context -> term -> term -> Prop :=
| tySort (Γ : context) (s : sort)
: Γ ⊢ₓ *s : *(sSucc s)

| tyProd (Γ : context) (s1 : sort) (s2 : sort) (A B : term)
: Γ ⊢ₓ A : *s1 ->
  Γ ,, A ⊢ₓ B : *s2 ->
  Γ ⊢ₓ ∏A, B : *(sPi s1 s2)

| tySum (Γ : context) (s1 : sort) (s2 : sort) (A B : term)
: Γ ⊢ₓ A : *s1 ->
  Γ ,, A ⊢ₓ B : *s2 ->
  Γ ⊢ₓ ∑A, B : *(sSig s1 s2)

| tyRel (Γ : context) (n : nat) (isdef : n < List.length Γ)
: Γ ⊢ₓ ^n : lift (S n) 0 (safe_nth n Γ isdef)

| tyLam (Γ : context) (s1 s2 : sort) (A B t : term)
: Γ ⊢ₓ A : *s1 ->
  Γ ,, A ⊢ₓ B : *s2 ->
  Γ ,, A ⊢ₓ t : B ->
  Γ ⊢ₓ λ, t : ∏A, B

| tyApp {Γ : context} {s1 s2 : sort} (A B t u : term)
: Γ ⊢ₓ A : *s1 ->
  Γ ,, A ⊢ₓ B : *s2 ->
  Γ ⊢ₓ t : ∏A, B ->
  Γ ⊢ₓ u : A ->
  Γ ⊢ₓ t @ u : (subst u 0 B)

| tyPair (Γ : context) (s1 s2 : sort) (A B u v : term)
: Γ ⊢ₓ u : A ->
  Γ ⊢ₓ A : *s1 ->
  Γ ,, A ⊢ₓ B : *s2 ->
  Γ ⊢ₓ v : (subst u 0 B) ->
  Γ ⊢ₓ ⟨u, v⟩ : ∑A, B

| tyPi1 (Γ : context) (A B p : term)
: Γ ⊢ₓ p : ∑A, B ->
  Γ ⊢ₓ π₁ p : A

| tyPi2 (Γ : context) (A B p : term)
: Γ ⊢ₓ p : ∑A, B ->
  Γ ⊢ₓ π₂ p : (subst (π₁ p) 0 B)

| tyConv (Γ : context) (s : sort) (A B u : term)
: Γ ⊢ₓ u : A ->
  Γ ⊢ₓ A ≡ B : *s ->
  Γ ⊢ₓ u : B
where "Γ '⊢ₓ' t : T" := (typed Γ t T) : x_scope

with eq_typed : context -> term -> term -> term -> Prop :=
| eqRefl (Γ : context) (u A : term)
: Γ ⊢ₓ u : A ->
  Γ ⊢ₓ u ≡ u : A

| eqSym (Γ : context) (u v A : term)
: Γ ⊢ₓ u : A ->
  Γ ⊢ₓ v : A ->
  Γ ⊢ₓ u ≡ v : A ->
  Γ ⊢ₓ v ≡ u : A

| eqTrans (Γ : context) (u v w A : term)
: Γ ⊢ₓ u ≡ v : A ->
  Γ ⊢ₓ v ≡ w : A ->
  Γ ⊢ₓ u ≡ w : A

| eqConv (Γ : context) (s : sort) (t1 t2 T1 T2 : term)
: Γ ⊢ₓ t1 ≡ t2 : T1 ->
  Γ ⊢ₓ T1 ≡ T2 : *s ->
  Γ ⊢ₓ t1 ≡ t2 : T2

| eqAppComp (Γ : context) (s1 s2 : sort) (u t A B : term)
: Γ ⊢ₓ A : *s1 ->
  Γ ,, A ⊢ₓ B : *s2 ->
  Γ ,, A ⊢ₓ t : B ->
  Γ ⊢ₓ u : A ->
  Γ ⊢ₓ (λ, t) @ u ≡ (subst u 0 t) : (subst u 0 B) 

| eqPi1Comp (Γ : context) (s1 s2 : sort) (u v A B : term)
: Γ ⊢ₓ A : *s1 ->
  Γ ⊢ₓ u : A ->
  Γ ,, A ⊢ₓ B : *s2 ->
  Γ ⊢ₓ v : (subst u 0 B) ->
  Γ ⊢ₓ π₁ ⟨u, v⟩ ≡ u : A

| eqPi2Comp (Γ : context) (s1 s2 : sort) (u v A B : term)
: Γ ⊢ₓ A : *s1 ->
  Γ ⊢ₓ u : A ->
  Γ ,, A ⊢ₓ B : *s2 ->
  Γ ⊢ₓ v : (subst u 0 B) ->
  Γ ⊢ₓ π₂ ⟨u, v⟩ ≡ v : (subst u 0 B)

| eqLambdaEta (Γ : context) (s1 s2 : sort) (f A B : term)
: Γ ⊢ₓ A : *s1 ->
  Γ ,, A ⊢ₓ B : *s2 ->
  Γ ⊢ₓ f : ∏A, B ->
  Γ ⊢ₓ λ, f @ ^0 ≡ f : (tProd A B)

| eqPairEta (Γ : context) (s1 s2 : sort)  (A B p : term)
: Γ ⊢ₓ A : *s1 ->
  Γ ,, A ⊢ₓ B : *s2 ->
  Γ ⊢ₓ p : tSum A B ->
  Γ ⊢ₓ ⟨π₁ p, π₂ p⟩ ≡ p : (tSum A B)

| eqProdCong (Γ : context) (s1 s2 : sort) (A1 A2 B1 B2 : term)
: Γ ⊢ₓ A1 ≡ A2 : *s1 ->
  Γ ,, A1 ⊢ₓ B1 ≡ B2 : *s2 ->
  Γ ⊢ₓ ∏A1, B1 ≡ ∏A2, B2 : *(sPi s1 s2)

| eqLamCong (Γ : context) (A B t1 t2 : term)
: Γ ,, A ⊢ₓ t1 ≡ t2 : B ->
  Γ ⊢ₓ λ, t1 ≡ λ, t2 : ∏A, B

| eqAppCong (Γ : context) (A B t1 t2 u1 u2 : term)
: Γ ⊢ₓ u1 ≡ u2 : A ->
  Γ ⊢ₓ t1 ≡ t2 : ∏A, B ->
  Γ ⊢ₓ t1 @ u1 ≡ t2 @ u2 : (subst u1 0 B)

| eqSumCong (Γ : context) (s1 s2 : sort) (A1 A2 B1 B2 : term)
: Γ ⊢ₓ A1 ≡ A2 : *s1 ->
  Γ ,, A1 ⊢ₓ B1 ≡ B2 : *s2 ->
  Γ ⊢ₓ ∑A1, B1 ≡ ∑A2, B2 : *(sSig s1 s2)

| eqPairCong (Γ : context) (A B u1 u2 v1 v2 : term)
: Γ ⊢ₓ u1 ≡ u2 : A -> 
  Γ ,, A ⊢ₓ v1 ≡ v2 : B ->
  Γ ⊢ₓ ⟨u1, v1⟩ ≡ ⟨u2,v2⟩ : ∑A, B

| eqPi1Cong (Γ : context) (A B p1 p2 : term)
: Γ ⊢ₓ p1 ≡ p2 : ∑A, B ->
  Γ ⊢ₓ π₁ p2 ≡ π₁ p2 : A

| eqPi2Cong (Γ : context) (A B p1 p2 : term)
: Γ ⊢ₓ p1 ≡ p2 : ∑A, B ->
  Γ ⊢ₓ π₂ p1 ≡ π₂ p2 : subst (tPi1 p1) 0 B

where " Γ '⊢ₓ' t ≡ u : T " := (eq_typed Γ t u T) : x_scope.


End ETT.

Declare Scope x_scope.

Notation "Γ ,, d" := (d :: Γ) : x_scope.
Notation "Γ ;; Δ" := (Δ ++ Γ) : x_scope.
Notation "Γ ⊢ₓ t : T" := (typed Γ t T) : x_scope.
Notation "Γ ⊢ₓ t ≡ u : T" := (eq_typed Γ t u T) : x_scope.

Ltac getRel Γ n :=
  let isdef := fresh "isdef" in
  assert (isdef : n < length Γ); [simpl; lia|apply (tyRel Γ n isdef)].

Ltac typer :=
repeat match goal with
| |- _ => progress simpl
| |- typed _ (tSort _) _ => eapply tySort
| |- typed _ (tProd _ _) _ => eapply tyProd
| |- typed _ (tSum _ _) _ => eapply tySum
| |- typed _ (tLambda _) _ => eapply tyLam
| |- typed _ (tPair _ _) _ => eapply tyPair
| |- typed _ (tPi1 _) _ => eapply tyPi1
| |- typed _ (tPi2 _) _ => eapply tyPi2
| |- typed ?Γ (tRel ?n) _ => getRel Γ n
| |- typed _ (tApp _ _) (tSort _) => eapply (tyApp _ (tSort _))
| |- eq_typed _ ?x ?x _ => eapply (eqRefl _ x _)
| |- eq_typed _ _ _ _ => progress apply eqProdCong
| |- eq_typed _ _ _ _ => progress apply eqLamCong
| |- eq_typed _ _ _ _ => progress apply eqSumCong
| |- eq_typed _ _ _ _ => progress apply eqPairCong
end.