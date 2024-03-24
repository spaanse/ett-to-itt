From Coq Require Import List Lia.
Require Import Ast Subst.

Reserved Notation "Γ ,, d" (at level 20, d at next level, left associativity, format "'[' Γ ',,' d ']'").
Reserved Notation "Γ ;; Δ" (at level 20, Δ at next level, left associativity, format "'[' Γ ';;' Δ ']'").
Reserved Notation "Γ ⊢ t : T" (at level 50, t, T at next level, format "'[' Γ '//' '⊢'  t '//' ':'  T ']'").
Reserved Notation "Γ ⊢ t ≡ u : T" (at level 50, t, u, T at next level, format "'[' Γ '//' '⊢'  t  '≡'  u '//' ':'  T ']'").

Section Typing.
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

Inductive typed: context -> term -> term -> Prop :=
| tySort (Γ : context) (s : sort)
: Γ ⊢ (tSort s) : (tSort (sSucc s))

| tyProd (Γ : context) (s1 : sort) (s2 : sort) (A B : term)
: Γ ⊢ A : (tSort s1) ->
  Γ ,, A ⊢ B : (tSort s2) ->
  Γ ⊢ (tProd A B) : (tSort (sPi s1 s2))

| tySum (Γ : context) (s1 : sort) (s2 : sort) (A B : term)
: Γ ⊢ A : (tSort s1) ->
  Γ ,, A ⊢ B : (tSort s2) ->
  Γ ⊢ (tSum A B) : (tSort (sSig s1 s2))

| tyRel (Γ : context) (n : nat) (isdef : n < List.length Γ)
: Γ ⊢ (tRel n) : lift0 (S n) (safe_nth n Γ isdef)

| tyLam (Γ : context) (s1 s2 : sort) (A B t : term)
: Γ ⊢ A : (tSort s1) ->
  Γ ,, A ⊢ B : (tSort s2) ->
  Γ ,, A ⊢ t : B ->
  Γ ⊢ (tLambda t) : (tProd A B)

| tyApp {Γ : context} {s1 s2 : sort} (A B t u : term)
: Γ ⊢ A : (tSort s1) ->
  Γ ,, A ⊢ B : (tSort s2) ->
  Γ ⊢ t : (tProd A B) ->
  Γ ⊢ u : A ->
  Γ ⊢ (tApp t u) : (subst0 u B)

| tyPair (Γ : context) (s1 s2 : sort) (A B u v : term)
: Γ ⊢ u : A ->
  Γ ⊢ A : (tSort s1) ->
  Γ ,, A ⊢ B : (tSort s2) ->
  Γ ⊢ v : (subst0 u B) ->
  Γ ⊢ (tPair u v) : (tSum A B)

| tyPi1 (Γ : context) (A B p : term)
: Γ ⊢ p : (tSum A B) ->
  Γ ⊢ (tPi1 p) : A

| tyPi2 (Γ : context) (A B p : term)
: Γ ⊢ p : (tSum A B) ->
  Γ ⊢ (tPi2 p) : (subst0 (tPi1 p) B)

| tyConv (Γ : context) (s : sort) (A B u : term)
: Γ ⊢ u : A ->
  Γ ⊢ A ≡ B : (tSort s) ->
  Γ ⊢ u : B
where "Γ '⊢' t : T" := (typed Γ t T) : x_scope

with eq_typed : context -> term -> term -> term -> Prop :=
| eqRefl (Γ : context) (u A : term)
: Γ ⊢ u : A ->
  Γ ⊢ u ≡ u : A

| eqSym (Γ : context) (u v A : term)
: Γ ⊢ u : A ->
  Γ ⊢ v : A ->
  Γ ⊢ u ≡ v : A ->
  Γ ⊢ v ≡ u : A

| eqTrans (Γ : context) (u v w A : term)
: Γ ⊢ u ≡ v : A ->
  Γ ⊢ v ≡ w : A ->
  Γ ⊢ u ≡ w : A

| eqConv (Γ : context) (s : sort) (t1 t2 T1 T2 : term)
: Γ ⊢ t1 ≡ t2 : T1 ->
  Γ ⊢ T1 ≡ T2 : tSort s ->
  Γ ⊢ t1 ≡ t2 : T2

| eqAppComp (Γ : context) (s1 s2 : sort) (u t A B : term)
: Γ ⊢ A : (tSort s1) ->
  Γ ,, A ⊢ B : (tSort s2) ->
  Γ ,, A ⊢ t : B ->
  Γ ⊢ u : A ->
  Γ ⊢ (tApp (tLambda t) u) ≡ (subst0 u t) : (subst0 u B) 

| eqPi1Comp (Γ : context) (s1 s2 : sort) (u v A B : term)
: Γ ⊢ A : (tSort s1) ->
  Γ ⊢ u : A ->
  Γ ,, A ⊢ B : (tSort s2) ->
  Γ ⊢ v : (subst0 u B) ->
  Γ ⊢ (tPi1 (tPair u v)) ≡ u : A

| eqPi2Comp (Γ : context) (s1 s2 : sort) (u v A B : term)
: Γ ⊢ A : (tSort s1) ->
  Γ ⊢ u : A ->
  Γ ,, A ⊢ B : (tSort s2) ->
  Γ ⊢ v : (subst0 u B) ->
  Γ ⊢ (tPi2 (tPair u v)) ≡ v : (subst0 u B)

| eqLambdaEta (Γ : context) (s1 s2 : sort) (f A B : term)
: Γ ⊢ A : (tSort s1) ->
  Γ ,, A ⊢ B : (tSort s2) ->
  Γ ⊢ f : tProd A B ->
  Γ ⊢ (tLambda (tApp f (tRel 0))) ≡ f : (tProd A B)

| eqPairEta (Γ : context) (s1 s2 : sort)  (A B p : term)
: Γ ⊢ A : (tSort s1) ->
  Γ ,, A ⊢ B : (tSort s2) ->
  Γ ⊢ p : tSum A B ->
  Γ ⊢ (tPair (tPi1 p) (tPi2 p)) ≡ p : (tSum A B)

| eqProdCong (Γ : context) (s1 s2 : sort) (A1 A2 B1 B2 : term)
: Γ ⊢ A1 ≡ A2 : tSort s1 ->
  Γ ,, A1 ⊢ B1 ≡ B2 : tSort s2 ->
  Γ ⊢ (tProd A1 B1) ≡ (tProd A2 B2) : tSort (sPi s1 s2)

| eqLamCong (Γ : context) (A B t1 t2 : term)
: Γ ,, A ⊢ t1 ≡ t2 : B ->
  Γ ⊢ (tLambda t1) ≡ (tLambda t2) : (tProd A B)

| eqAppCong (Γ : context) (A B t1 t2 u1 u2 : term)
: Γ ⊢ u1 ≡ u2 : A ->
  Γ ⊢ t1 ≡ t2 : (tProd A B) ->
  Γ ⊢ (tApp t1 u1) ≡ (tApp t2 u2) : (subst0 u1 B)

| eqSumCong (Γ : context) (s1 s2 : sort) (A1 A2 B1 B2 : term)
: Γ ⊢ A1 ≡ A2 : tSort s1 ->
  Γ ,, A1 ⊢ B1 ≡ B2 : tSort s2 ->
  Γ ⊢ (tSum A1 B1) ≡ (tSum A2 B2) : tSort (sSig s1 s2)

| eqPairCong (Γ : context) (A B u1 u2 v1 v2 : term)
: Γ ⊢ u1 ≡ u2 : A -> 
  Γ ,, A ⊢ v1 ≡ v2 : B ->
  Γ ⊢ (tPair u1 v1) ≡ (tPair u2 v2) : (tSum A B)

| eqPi1Cong (Γ : context) (A B p1 p2 : term)
: Γ ⊢ p1 ≡ p2 : (tSum A B) ->
  Γ ⊢ (tPi1 p1) ≡ (tPi1 p2) : A

| eqPi2Cong (Γ : context) (A B p1 p2 : term)
: Γ ⊢ p1 ≡ p2 : (tSum A B) ->
  Γ ⊢ (tPi2 p1) ≡ (tPi2 p2) : subst0 (tPi1 p1) B

where " Γ '⊢' t ≡ u : T " := (eq_typed Γ t u T) : x_scope.


Delimit Scope x_scope with x.
End Typing.

Declare Scope x_scope.

Notation "Γ ,, d" := (d :: Γ) : x_scope.
Notation "Γ ;; Δ" := (Δ ++ Γ) : x_scope.
Notation "Γ ⊢ t : T" := (typed Γ t T) : x_scope.
Notation "Γ ⊢ t ≡ u : T" := (eq_typed Γ t u T) : x_scope.

Ltac getRel Γ n :=
  let isdef := fresh "isdef" in
  assert (isdef : n < length Γ); [simpl; lia|apply (tyRel Γ n isdef)].

Ltac typer :=
repeat match goal with
| |- _ => progress unfold subst0
| |- _ => progress unfold unlift0
| |- _ => progress unfold lift0
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