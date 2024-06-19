Require Import Ast.
Open Scope t_scope.

Reserved Notation "a '⊏' b" (at level 50, format "'[' a  '/' '⊏' '/'  b ']'").
Reserved Notation "a '≃' b" (at level 50, format "'[' a  '/' '≃' '/'  b ']'").

Inductive decorates : term -> term -> Prop :=
| dec_transport p t1 t2          : t1 ⊏ t2 -> t1 ⊏ (tTransport p t2)
| dec_identity x                 : x ⊏ x
| dec_prod A1 A2 B1 B2           : A1 ⊏ A2 -> B1 ⊏ B2 -> ∏A1, B1 ⊏ ∏A2, B2
| dec_sum A1 A2 B1 B2            : A1 ⊏ A2 -> B1 ⊏ B2 -> ∑A1, B1 ⊏ ∑A2, B2
| dec_eq u1 u2 v1 v2             : u1 ⊏ u2 -> v1 ⊏ v2 -> u1 == v1 ⊏ u2 == v2
| dec_sort s                     : *s ⊏ *s
| dec_lambda t1 t2               : t1 ⊏ t2 -> λ, t1 ⊏ λ, t2
| dec_app t1 t2 u1 u2            : t1 ⊏ t2 -> u1 ⊏ u2 -> t1 @ u1 ⊏ t2 @ u2
| dec_pair u1 u2 v1 v2           : u1 ⊏ u2 -> v1 ⊏ v2 -> ⟨u1, v1⟩ ⊏ ⟨u2, v2⟩
| dec_pi1 p1 p2                  : p1 ⊏ p2 -> π₁ p1 ⊏ π₁ p2
| dec_pi2 p1 p2                  : p1 ⊏ p2 -> π₂ p1 ⊏ π₂ p2
| dec_J t1 t2 p1 p2              : t1 ⊏ t2 -> p1 ⊏ p2 -> J(t1,p1) ⊏ J(t2, p2)
| dec_refl u1 u2                 : u1 ⊏ u2 -> Refl(u1) ⊏ Refl(u2)
where "x ⊏ y" := (decorates x y).
Notation "x ⊏ y" := (decorates x y).

Inductive decsim : term -> term -> Prop :=
| ds_transport_l p t1 t2        : t1 ≃ t2 -> (tTransport p t1) ≃ t2
| ds_transport_r p t1 t2        : t1 ≃ t2 -> t1 ≃ (tTransport p t2)
| ds_identity x                 : x ≃ x
| ds_prod A1 A2 B1 B2           : A1 ≃ A2 -> B1 ≃ B2 -> ∏A1, B1 ≃ ∏A2, B2
| ds_sum A1 A2 B1 B2            : A1 ≃ A2 -> B1 ≃ B2 -> ∑A1, B1 ≃ ∑A2, B2
| ds_eq u1 u2 v1 v2             : u1 ≃ u2 -> v1 ≃ v2 -> u1 == v1 ≃ u2 == v2
| ds_sort s                     : *s ≃ *s
| ds_lambda t1 t2               : t1 ≃ t2 -> λ, t1 ≃ λ, t2
| ds_app t1 t2 u1 u2            : t1 ≃ t2 -> u1 ≃ u2 -> t1 @ u1 ≃ t2 @ u2
| ds_pair u1 u2 v1 v2           : u1 ≃ u2 -> v1 ≃ v2 -> ⟨u1, v1⟩ ≃ ⟨u2, v2⟩
| ds_pi1 p1 p2                  : p1 ≃ p2 -> π₁ p1 ≃ π₁ p2
| ds_pi2 p1 p2                  : p1 ≃ p2 -> π₂ p1 ≃ π₂ p2
| ds_J t1 t2 p1 p2              : t1 ≃ t2 -> p1 ≃ p2 -> J(t1,p1) ≃ J(t2, p2)
| ds_refl u1 u2                 : u1 ≃ u2 -> Refl(u1) ≃ Refl(u2)
where "x ≃ y" := (decsim x y).
Notation "x ≃ y" := (decsim x y).

Fixpoint erase_transport t : term :=
match t with
| tTransport p t => erase_transport t
| tRel n => tRel n
| tSort s => tSort s
| tProd A B => tProd (erase_transport A) (erase_transport B)
| tLambda t => tLambda (erase_transport t)
| tApp u v => tApp (erase_transport u) (erase_transport v)
| tSum A B => tSum (erase_transport A) (erase_transport B)
| tPair u v => tPair (erase_transport u) (erase_transport v)
| tPi1 p => tPi1 (erase_transport p)
| tPi2 p => tPi2 (erase_transport p)
| tEq u v => tEq (erase_transport u) (erase_transport v)
| tRefl u => tRefl (erase_transport u)
| tJ t p => tJ (erase_transport t) (erase_transport p)
end.

Lemma decsim_erase a
: a ≃ (erase_transport a).
Proof.
  induction a; simpl; eauto using decsim.
Qed.

Lemma decsim_sym a b
: a ≃ b -> b ≃ a.
Proof.
  intros ab. induction ab; eauto using decsim.
Qed.

Lemma decsim_same_erase a b
: a ≃ b <-> (erase_transport a) = (erase_transport b).
Proof.
  split.
  - intro ab. induction ab; simpl; congruence.
  - revert b; induction a; intros b ab;
    induction b; simpl in *;
    try discriminate;
    try injection ab as ab;
    repeat match goal with
    | IH : forall b, erase_transport ?a = erase_transport b -> a ≃ b,
      H : erase_transport ?a = erase_transport ?b |- _ =>
      specialize (IH _ H)
    end; eauto using decsim.
    + rewrite ab. eauto using decsim.
    + rewrite ab. eauto using decsim.
Qed.


Lemma decsim_trans a b c
: a ≃ b -> b ≃ c -> a ≃ c.
Proof.
    intros ab bc.
    apply decsim_same_erase in ab.
    apply decsim_same_erase in bc.
    apply decsim_same_erase.
    congruence.
Qed.

Lemma decsim_dec a b
: a ⊏ b -> a ≃ b.
Proof.
  intros ab.
  induction ab; eauto using decsim.
Qed.