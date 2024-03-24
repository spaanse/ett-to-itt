From Coq Require Import Lia.
Require Import Ast Subst Typing.
Open Scope t_scope.
Open Scope x_scope.

Section SigmaAssoc.

Lemma sum_assoc_ltr
  (A : Type)
  (B : forall x : A, Type)
  (C : forall (x : {y : A & B y}), Type)
: forall x : {y : {z : A & B z} & C y}, {a : A & {b : B a & C (existT _ a b)}}.
Proof.
  intros x.
  (* exact (existT _ (projT1 (projT1 x)) (existT _ (projT2 (projT1 x)) (projT2 x))). *)
  exists (projT1 (projT1 x)).
  exists (projT2 (projT1 x)).
  rewrite <- sigT_eta.
  exact (projT2 x).
Qed.

Lemma sum_assoc_rtl
  (A : Type)
  (B : forall x : A, Type)
  (C : forall (x : {y : A & B y}), Type)
: forall x : {a : A & {b : B a & C (existT _ a b)}}, {y : {z : A & B z} & C y}.
Proof.
  intros x.
  exact (existT _ (existT _ (projT1 x) (projT1 (projT2 x))) (projT2 (projT2 x))).
Qed.

Definition ltr : term := λ, (⟨π₁ (π₁ ^0), ⟨π₂ (π₁ ^0), π₂ ^0⟩⟩).

Lemma context_1 (s1 s2 s3 : sort) : exists T, nil ,, *s1 ⊢ ∏^0, *s2 : T.
Proof.
  eexists. typer.
Qed.

Lemma context_2 (s1 s2 s3 : sort) : exists T, nil ,, *s1 ,, ∏^0, *s2 ⊢ ∏(∑^1, ^1 @ ^0), *s3 : T.
Proof.
  eexists. typer; typer.
Qed.

Lemma ltr_typed (s1 s2 s3 : sort) : exists ctx T, ctx ⊢ ltr : T.
Proof.
    unfold ltr.
    exists (nil ,, 
           *s1 ,,
           ∏^0, *s2 ,,
           ∏(∑^1, (^1 @ ^0)), *s3).
    exists (∏(∑(∑^2, (^2 @ ^0)), (^1 @ ^0)), (∑^3, (∑(^3 @ ^0), (^3 @ (⟨^1, ^0⟩))))).
    repeat typer.
    - eapply (tyPi2 _ _ (^3 @ ^0)); typer.
    - eapply (tyPi2 _ (∑^3, ^3 @ ^0) (^2 @ ⟨π₁ ^0, π₂ ^0⟩)); typer.
      apply tyConv with (sSig (sSig s1 s2) s3) (∑(∑^3, ^3 @ ^0), ^2 @ ^0); typer.
      { simpl. typer. }
      apply (eqAppCong _ (∑^4, ^4 @ ^0) *s3 _ _ ^0 _); typer.
      apply eqSym.
      (* Need computation rule ^0 ≡ ⟨π₁ ^0, π₂ ^0⟩ *)
      apply eqPairEta; typer.
Qed.

Definition rtl : term := λ, (⟨⟨π₁ ^0, π₁ (π₂ ^0)⟩, π₂ (π₂ ^0)⟩).

Lemma rtl_typed (s1 s2 s3 : sort) : exists ctx T, ctx ⊢ rtl : T.
Proof.
    unfold rtl.
    exists (nil ,, 
           *s1 ,,
           ∏^0, *s2 ,,
           ∏(∑^1, (^1 @ ^0)), *s3).
    
    exists (∏(∑^2, (∑(^2 @ ^0), (^2 @ (⟨^1, ^0⟩)))), (∑(∑^3, (^3 @ ^0)), (^2 @ ^0))).
    repeat typer.
    - eapply (tyPi2 _ _ (∑ (^3 @ ^0), ^3 @ ⟨^1, ^0⟩)).
      typer.
    - eapply (tyPi2 _ _ (^2 @ ⟨π₁ ^1, ^0⟩)).
      eapply (tyPi2 _ _ (∑(^3 @ ^0), ^3 @ ⟨^1, ^0⟩)).
      typer.
Qed.
End SigmaAssoc.