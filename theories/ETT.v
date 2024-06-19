From Coq Require Import List Lia.
Require Import Ast Subst SafeNth.

Reserved Notation "Γ ⊢ₓ t : T" (at level 50, t, T at next level, format "'[' Γ '//' '⊢ₓ'  t '//' ':'  T ']'").
Reserved Notation "Γ ⊢ₓ t ≡ u : T" (at level 50, t, u, T at next level, format "'[' Γ '//' '⊢ₓ'  t  '≡'  u '//' ':'  T ']'").

Open Scope t_scope.
Section ETT.
Declare Scope x_scope.

Inductive xtyped: context -> term -> term -> Prop :=
| xtySort (Γ : context) (s : sort)
: Γ ⊢ₓ *s : *(sSucc s)

| xtyProd (Γ : context) (s1 s2 : sort) (A B : term)
: Γ ⊢ₓ A : *s1 ->
  Γ ,, A ⊢ₓ B : *s2 ->
  Γ ⊢ₓ ∏A, B : *(sPi s1 s2)

| xtySum (Γ : context) (s1 s2 : sort) (A B : term)
: Γ ⊢ₓ A : *s1 ->
  Γ ,, A ⊢ₓ B : *s2 ->
  Γ ⊢ₓ ∑A, B : *(sSig s1 s2)

| xtyRel (Γ : context) (n : nat) (isdef : n < List.length Γ)
: Γ ⊢ₓ ^n : lift (S n) 0 (safe_nth n Γ isdef)

| xtyLam (Γ : context) (s1 s2 : sort) (A B t : term)
: Γ ⊢ₓ A : *s1 ->
  Γ ,, A ⊢ₓ B : *s2 ->
  Γ ,, A ⊢ₓ t : B ->
  Γ ⊢ₓ λ, t : ∏A, B

| xtyApp {Γ : context} {s1 s2 : sort} (A B t u : term)
: Γ ⊢ₓ A : *s1 ->
  Γ ,, A ⊢ₓ B : *s2 ->
  Γ ⊢ₓ t : ∏A, B ->
  Γ ⊢ₓ u : A ->
  Γ ⊢ₓ t @ u : B[u]

| xtyPair (Γ : context) (s1 s2 : sort) (A B u v : term)
: Γ ⊢ₓ u : A ->
  Γ ⊢ₓ A : *s1 ->
  Γ ,, A ⊢ₓ B : *s2 ->
  Γ ⊢ₓ v : B[u] ->
  Γ ⊢ₓ ⟨u, v⟩ : ∑A, B

| xtyPi1 (Γ : context) (A B p : term)
: Γ ⊢ₓ p : ∑A, B ->
  Γ ⊢ₓ π₁ p : A

| xtyPi2 (Γ : context) (A B p : term)
: Γ ⊢ₓ p : ∑A, B ->
  Γ ⊢ₓ π₂ p : B[π₁ p]

| xtyEq (Γ : context) (s : sort) (A u v : term)
: Γ ⊢ₓ A : *s ->
  Γ ⊢ₓ u : A ->
  Γ ⊢ₓ v : A ->
  Γ ⊢ₓ u == v : *(sEq s)

| xtyRefl (Γ : context) (s : sort) (A u : term)
: Γ ⊢ₓ u : A ->
  Γ ⊢ₓ A : *s ->
  Γ ⊢ₓ Refl(u) : u == u

| xtyJ (Γ : context) (s : sort) (A C t p x y : term)
: Γ ,, A ,, (lift 1 0 A) ,, (^1 == ^0) ⊢ₓ C : *s ->
  Γ ,, A ⊢ₓ t : C[^0, Refl(^1)] ->
  Γ ⊢ₓ x : A ->
  Γ ⊢ₓ y : A ->
  Γ ⊢ₓ p : x == y ->
  Γ ⊢ₓ J(t,p) : C[x, lift 1 0 y, lift 2 0 p]

| xtyConv (Γ : context) (s : sort) (A B u : term)
: Γ ⊢ₓ u : A ->
  Γ ⊢ₓ A ≡ B : *s ->
  Γ ⊢ₓ u : B
where "Γ '⊢ₓ' t : T" := (xtyped Γ t T) : x_scope

with eq_xtyped : context -> term -> term -> term -> Prop :=
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
  Γ ⊢ₓ λ, (lift 1 0 f) @ ^0 ≡ f : (tProd A B)

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

where " Γ '⊢ₓ' t ≡ u : T " := (eq_xtyped Γ t u T) : x_scope.


End ETT.

Declare Scope x_scope.

Notation "Γ ⊢ₓ t : T" := (xtyped Γ t T) : x_scope.
Notation "Γ ⊢ₓ t ≡ u : T" := (eq_xtyped Γ t u T) : x_scope.

Ltac getRel Γ n :=
  let isdef := fresh "isdef" in
  assert (isdef : n < length Γ); [simpl; lia|apply (xtyRel Γ n isdef)].

Ltac xtyper :=
repeat match goal with
| |- _ => progress simpl
| |- xtyped _ (tSort _) _ => eapply xtySort
| |- xtyped _ (tProd _ _) _ => eapply xtyProd
| |- xtyped _ (tSum _ _) _ => eapply xtySum
| |- xtyped _ (tLambda _) _ => eapply xtyLam
| |- xtyped _ (tPair _ _) _ => eapply xtyPair
| |- xtyped _ (tPi1 _) _ => eapply xtyPi1
| |- xtyped _ (tPi2 _) _ => eapply xtyPi2
| |- xtyped ?Γ (tRel ?n) _ => getRel Γ n
| |- xtyped _ (tApp _ _) (tSort _) => eapply (xtyApp _ (tSort _))
| |- eq_xtyped _ ?x ?x _ => eapply (eqRefl _ x _)
| |- eq_xtyped _ _ _ _ => progress apply eqProdCong
| |- eq_xtyped _ _ _ _ => progress apply eqLamCong
| |- eq_xtyped _ _ _ _ => progress apply eqSumCong
| |- eq_xtyped _ _ _ _ => progress apply eqPairCong
end.