From Coq Require Import List Lia.
Require Import Ast Subst Conversion SafeNth.

Reserved Notation "Γ ⊢ᵢ t : T" (at level 50, t, T at next level, format "'[' Γ '//' '⊢ᵢ'  t '//' ':'  T ']'").

Open Scope t_scope.
Section ITT.
Declare Scope i_scope.

Inductive ityped: context -> term -> term -> Prop :=
| itySort (Γ : context) (s : sort)
: Γ ⊢ᵢ *s : *(sSucc s)

| ityProd (Γ : context) (s1 s2 : sort) (A B : term)
: Γ ⊢ᵢ A : *s1 ->
  Γ ,, A ⊢ᵢ B : *s2 ->
  Γ ⊢ᵢ ∏A, B : *(sPi s1 s2)

| itySum (Γ : context) (s1 s2 : sort) (A B : term)
: Γ ⊢ᵢ A : *s1 ->
  Γ ,, A ⊢ᵢ B : *s2 ->
  Γ ⊢ᵢ ∑A, B : *(sSig s1 s2)

| ityRel (Γ : context) (n : nat) (isdef : n < List.length Γ)
: Γ ⊢ᵢ ^n : lift (S n) 0 (safe_nth n Γ isdef)

| ityLam (Γ : context) (s1 s2 : sort) (A B t : term)
: Γ ⊢ᵢ A : *s1 ->
  Γ ,, A ⊢ᵢ B : *s2 ->
  Γ ,, A ⊢ᵢ t : B ->
  Γ ⊢ᵢ λ, t : ∏A, B

| ityApp {Γ : context} {s1 s2 : sort} (A B t u : term)
: Γ ⊢ᵢ A : *s1 ->
  Γ ,, A ⊢ᵢ B : *s2 ->
  Γ ⊢ᵢ t : ∏A, B ->
  Γ ⊢ᵢ u : A ->
  Γ ⊢ᵢ t @ u : (subst u 0 B)

| ityPair (Γ : context) (s1 s2 : sort) (A B u v : term)
: Γ ⊢ᵢ u : A ->
  Γ ⊢ᵢ A : *s1 ->
  Γ ,, A ⊢ᵢ B : *s2 ->
  Γ ⊢ᵢ v : (subst u 0 B) ->
  Γ ⊢ᵢ ⟨u, v⟩ : ∑A, B

| ityPi1 (Γ : context) (A B p : term)
: Γ ⊢ᵢ p : ∑A, B ->
  Γ ⊢ᵢ π₁ p : A

| ityPi2 (Γ : context) (A B p : term)
: Γ ⊢ᵢ p : ∑A, B ->
  Γ ⊢ᵢ π₂ p : (subst (π₁ p) 0 B)

| ityEq (Γ : context) (s : sort) (A u v : term)
: Γ ⊢ᵢ A : *s ->
  Γ ⊢ᵢ u : A ->
  Γ ⊢ᵢ v : A ->
  Γ ⊢ᵢ u == v : *(sEq s)

| ityRefl (Γ : context) (s : sort) (A u : term)
: Γ ⊢ᵢ u : A ->
  Γ ⊢ᵢ A : *s ->
  Γ ⊢ᵢ Refl(u) : u == u

| ityJ (Γ : context) (s : sort) (A C t p x y : term)
: Γ ,, A ,, (lift 1 0 A) ,, (^1 == ^0) ⊢ᵢ C : *s ->
  Γ ,, A ⊢ᵢ t : C[^0, Refl(^1)] ->
  Γ ⊢ᵢ x : A ->
  Γ ⊢ᵢ y : A ->
  Γ ⊢ᵢ p : x == y ->
  Γ ⊢ᵢ J(t,p) : C[x, lift 1 0 y, lift 2 0 p]

| ityTransport (Γ : context) (A B p t : term)
: Γ ⊢ᵢ p : A == B ->
  Γ ⊢ᵢ t : A ->
  Γ ⊢ᵢ tTransport p t : B
  
| ityConv (Γ : context) (A B t : term) (s : sort)
: Γ ⊢ᵢ t : A ->
  A ≡ B ->
  Γ ⊢ᵢ B : *s ->
  Γ ⊢ᵢ t : B
where "Γ '⊢ᵢ' t : T" := (ityped Γ t T) : i_scope.

End ITT.

Declare Scope i_scope.

Notation "Γ ⊢ᵢ t : T" := (ityped Γ t T) : i_scope.

Ltac getRel Γ n :=
  let isdef := fresh "isdef" in
  assert (isdef : n < length Γ); [simpl; lia|apply (ityRel Γ n isdef)].

Ltac ityper :=
repeat match goal with
| |- _ => progress simpl
| |- ityped _ (tSort _) _ => eapply itySort
| |- ityped _ (tProd _ _) _ => eapply ityProd
| |- ityped _ (tSum _ _) _ => eapply itySum
| |- ityped _ (tLambda _) _ => eapply ityLam
| |- ityped _ (tPair _ _) _ => eapply ityPair
| |- ityped _ (tPi1 _) _ => eapply ityPi1
| |- ityped _ (tPi2 _) _ => eapply ityPi2
| |- ityped ?Γ (tRel ?n) _ => getRel Γ n
| |- ityped _ (tApp _ _) (tSort _) => eapply (ityApp _ (tSort _))
end.