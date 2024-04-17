From Coq Require Import List Lia.
Require Import Ast Subst Conversion SafeNth.

Reserved Notation "Γ ,, d" (at level 20, d at next level, left associativity, format "'[' Γ ',,' d ']'").
Reserved Notation "Γ ;; Δ" (at level 20, Δ at next level, left associativity, format "'[' Γ ';;' Δ ']'").
Reserved Notation "Γ ⊢ᵢ t : T" (at level 50, t, T at next level, format "'[' Γ '//' '⊢ᵢ'  t '//' ':'  T ']'").

Open Scope t_scope.
Section ITT.
Declare Scope i_scope.
Definition context := list term.
Notation "Γ ,, d" := (d :: Γ) : i_scope.
Notation "Γ ;; Δ" := (Δ ++ Γ) : i_scope.

Inductive typed: context -> term -> term -> Prop :=
| tySort (Γ : context) (s : sort)
: Γ ⊢ᵢ *s : *(sSucc s)

| tyProd (Γ : context) (s1 : sort) (s2 : sort) (A B : term)
: Γ ⊢ᵢ A : *s1 ->
  Γ ,, A ⊢ᵢ B : *s2 ->
  Γ ⊢ᵢ ∏A, B : *(sPi s1 s2)

| tySum (Γ : context) (s1 : sort) (s2 : sort) (A B : term)
: Γ ⊢ᵢ A : *s1 ->
  Γ ,, A ⊢ᵢ B : *s2 ->
  Γ ⊢ᵢ ∑A, B : *(sSig s1 s2)

| tyRel (Γ : context) (n : nat) (isdef : n < List.length Γ)
: Γ ⊢ᵢ ^n : lift (S n) 0 (safe_nth n Γ isdef)

| tyLam (Γ : context) (s1 s2 : sort) (A B t : term)
: Γ ⊢ᵢ A : *s1 ->
  Γ ,, A ⊢ᵢ B : *s2 ->
  Γ ,, A ⊢ᵢ t : B ->
  Γ ⊢ᵢ λ, t : ∏A, B

| tyApp {Γ : context} {s1 s2 : sort} (A B t u : term)
: Γ ⊢ᵢ A : *s1 ->
  Γ ,, A ⊢ᵢ B : *s2 ->
  Γ ⊢ᵢ t : ∏A, B ->
  Γ ⊢ᵢ u : A ->
  Γ ⊢ᵢ t @ u : (subst u 0 B)

| tyPair (Γ : context) (s1 s2 : sort) (A B u v : term)
: Γ ⊢ᵢ u : A ->
  Γ ⊢ᵢ A : *s1 ->
  Γ ,, A ⊢ᵢ B : *s2 ->
  Γ ⊢ᵢ v : (subst u 0 B) ->
  Γ ⊢ᵢ ⟨u, v⟩ : ∑A, B

| tyPi1 (Γ : context) (A B p : term)
: Γ ⊢ᵢ p : ∑A, B ->
  Γ ⊢ᵢ π₁ p : A

| tyPi2 (Γ : context) (A B p : term)
: Γ ⊢ᵢ p : ∑A, B ->
  Γ ⊢ᵢ π₂ p : (subst (π₁ p) 0 B)

| tyEq (Γ : context) (s : sort) (A u v : term)
: Γ ⊢ᵢ A : *s ->
  Γ ⊢ᵢ u : A ->
  Γ ⊢ᵢ v : A ->
  Γ ⊢ᵢ u == v : *(sEq s)

| tyRefl (Γ : context) (s : sort) (A u : term)
: Γ ⊢ᵢ u : A ->
  Γ ⊢ᵢ A : *s ->
  Γ ⊢ᵢ Refl(u) : u == u

| tyJ (Γ : context) (s : sort) (A C t p x y : term)
: Γ ,, A ,, A ,, (^1 == ^0) ⊢ᵢ C : *s ->
  Γ ,, A ⊢ᵢ t : (subst Refl(^0) 0 (subst ^0 0 (subst ^0 0 C))) ->
  Γ ⊢ᵢ x : A ->
  Γ ⊢ᵢ y : A ->
  Γ ⊢ᵢ p : x == y ->
  Γ ⊢ᵢ J(t,p) : (subst p 0 (subst y 0 (subst x 0 C)))
  
| tyConv (Γ : context) (A B t : term) (s : sort)
: Γ ⊢ᵢ t : A ->
  A ≡ B ->
  Γ ⊢ᵢ B : *s ->
  Γ ⊢ᵢ t : B
where "Γ '⊢ᵢ' t : T" := (typed Γ t T) : i_scope.

End ITT.

Declare Scope i_scope.

Notation "Γ ,, d" := (d :: Γ) : i_scope.
Notation "Γ ;; Δ" := (Δ ++ Γ) : i_scope.
Notation "Γ ⊢ᵢ t : T" := (typed Γ t T) : i_scope.

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
end.