From Coq Require Import List Lia.
Require Import Ast Subst SafeNth.

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

Inductive typed: context -> term -> term -> Prop :=
| tySort (Γ : context) (s : sort)
: Γ ⊢ₓ *s : *(sSucc s)

| tyProd (Γ : context) (s1 s2 : sort) (A B : term)
: Γ ⊢ₓ A : *s1 ->
  Γ ,, A ⊢ₓ B : *s2 ->
  Γ ⊢ₓ ∏A, B : *(sPi s1 s2)

| tySum (Γ : context) (s1 s2 : sort) (A B : term)
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
  Γ ⊢ₓ t @ u : B[u]

| tyPair (Γ : context) (s1 s2 : sort) (A B u v : term)
: Γ ⊢ₓ u : A ->
  Γ ⊢ₓ A : *s1 ->
  Γ ,, A ⊢ₓ B : *s2 ->
  Γ ⊢ₓ v : B[u] ->
  Γ ⊢ₓ ⟨u, v⟩ : ∑A, B

| tyPi1 (Γ : context) (A B p : term)
: Γ ⊢ₓ p : ∑A, B ->
  Γ ⊢ₓ π₁ p : A

| tyPi2 (Γ : context) (A B p : term)
: Γ ⊢ₓ p : ∑A, B ->
  Γ ⊢ₓ π₂ p : B[π₁ p]

| tyEq (Γ : context) (s : sort) (A u v : term)
: Γ ⊢ₓ A : *s ->
  Γ ⊢ₓ u : A ->
  Γ ⊢ₓ v : A ->
  Γ ⊢ₓ u == v : *(sEq s)

| tyRefl (Γ : context) (s : sort) (A u : term)
: Γ ⊢ₓ u : A ->
  Γ ⊢ₓ A : *s ->
  Γ ⊢ₓ Refl(u) : u == u

| tyJ (Γ : context) (s : sort) (A C t p x y : term)
: Γ ,, A ,, (lift 1 0 A) ,, (^1 == ^0) ⊢ᵢ C : *s ->
  Γ ,, A ⊢ᵢ t : C[^0, Refl(^1)] ->
  Γ ⊢× x : A ->
  Γ ⊢× y : A ->
  Γ ⊢× p : x == y ->
  Γ ⊢× J(t,p) : C[x, lift 1 0 y, lift 2 0 p]

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

| eqReflection (Γ : context) (u v p A : term)
: Γ ⊢ₓ u : A ->
  Γ ⊢ₓ v : A ->
  Γ ⊢ₓ p : u == v ->
  Γ ⊢ₓ u ≡ v : A

| eqAppComp (Γ : context) (s1 s2 : sort) (u t A B : term)
: Γ ⊢ₓ A : *s1 ->
  Γ ,, A ⊢ₓ B : *s2 ->
  Γ ,, A ⊢ₓ t : B ->
  Γ ⊢ₓ u : A ->
  Γ ⊢ₓ (λ, t) @ u ≡ t[u] : B[u] 

| eqPi1Comp (Γ : context) (s1 s2 : sort) (u v A B : term)
: Γ ⊢ₓ A : *s1 ->
  Γ ⊢ₓ u : A ->
  Γ ,, A ⊢ₓ B : *s2 ->
  Γ ⊢ₓ v : B[u] ->
  Γ ⊢ₓ π₁ ⟨u, v⟩ ≡ u : A

| eqPi2Comp (Γ : context) (s1 s2 : sort) (u v A B : term)
: Γ ⊢ₓ A : *s1 ->
  Γ ⊢ₓ u : A ->
  Γ ,, A ⊢ₓ B : *s2 ->
  Γ ⊢ₓ v : B[u] ->
  Γ ⊢ₓ π₂ ⟨u, v⟩ ≡ v : B[u]

| eqJComp (Γ : context) (s : sort) (t x A C : term)
: Γ ,, A ,, A ,, (^1 == ^0) ⊢ₓ C : *s ->
  Γ ,, A ⊢ₓ t : C[^0, ^0, Refl(^0)] ->
  Γ ⊢ₓ x : A ->
  Γ ⊢ₓ J(t, Refl(x)) ≡ t[x] : C[x, x, Refl(x)]

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
  Γ ⊢ₓ t1 @ u1 ≡ t2 @ u2 : B[u1]

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
  Γ ⊢ₓ π₂ p1 ≡ π₂ p2 : B[π₁ p1]

| eqEqCong (Γ : context) (s : sort) (A u u' v v' : term)
: Γ ⊢ₓ u ≡ u' : A ->
  Γ ⊢ₓ v ≡ v' : A ->
  Γ ⊢ₓ A : *s ->
  Γ ⊢ₓ (u == v) ≡ (u' == v') : *(sEq s)

| eqReflCong (Γ : context) (A u u' : term)
: Γ ⊢ₓ u ≡ u' : A ->
  Γ ⊢ₓ Refl(u) ≡ Refl(u') : u == u

| eqJCong (Γ : context) (A C x y t t' p p' : term)
: Γ ,, A ⊢ₓ t ≡ t' : C[^0, ^0, Refl(^0)] ->
  Γ ⊢ₓ p ≡ p' : x == y ->
  Γ ⊢ₓ J(t,p) ≡ J(t',p') : C[x, y, p]

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