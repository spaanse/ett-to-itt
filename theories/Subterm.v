Require Import Ast.
Open Scope t_scope.

Inductive subterm : term -> term -> Prop :=
| sub_prod_l A A' B : subterm_eq A A' -> subterm A (∏A', B)
| sub_prod_r A B B' : subterm_eq B B' -> subterm B (∏A, B')
| sub_lambda t t' : subterm_eq t t' -> subterm t (λ, t')
| sub_app_l u u' v : subterm_eq u u' -> subterm u (u' @ v)
| sub_app_r u v v' : subterm_eq v v' -> subterm v (u @ v')
| sub_sum_l A A' B : subterm_eq A A' -> subterm A (∑A', B)
| sub_sum_r A B B' : subterm_eq B B' -> subterm B (∑A, B')
| sub_pair_l u u' v : subterm_eq u u' -> subterm u ⟨u', v⟩
| sub_pair_r u v v' : subterm_eq v v' -> subterm v ⟨u, v'⟩
| sub_pi1 p p' : subterm_eq p p' -> subterm p (π₁ p')
| sub_pi2 p p' : subterm_eq p p' -> subterm p (π₂ p')
with subterm_eq : term -> term -> Prop :=
| sub_refl t : subterm_eq t t
| sub_sub u v : subterm u v -> subterm_eq u v
.

Lemma subterm_trans {u v w : term}
: subterm u v -> subterm v w -> subterm u w
with subterm_trans' {u v w : term}
: subterm u v -> subterm_eq v w -> subterm u w.
Proof.
  - intros uv vw.
    destruct vw.
    + eapply sub_prod_l, sub_sub, subterm_trans'; eassumption.
    + eapply sub_prod_r, sub_sub, subterm_trans'; eassumption.
    + eapply sub_lambda, sub_sub, subterm_trans'; eassumption.
    + eapply sub_app_l, sub_sub, subterm_trans'; eassumption.
    + eapply sub_app_r, sub_sub, subterm_trans'; eassumption.
    + eapply sub_sum_l, sub_sub, subterm_trans'; eassumption.
    + eapply sub_sum_r, sub_sub, subterm_trans'; eassumption.
    + eapply sub_pair_l, sub_sub, subterm_trans'; eassumption.
    + eapply sub_pair_r, sub_sub, subterm_trans'; eassumption.
    + eapply sub_pi1, sub_sub, subterm_trans'; eassumption.
    + eapply sub_pi2, sub_sub, subterm_trans'; eassumption.
  - intros uv vw.
    destruct vw.
    + assumption.
    + eapply subterm_trans; eassumption.
Qed.

Lemma term_strong_ind (P : term -> Prop) :
  (forall t, (forall u, subterm u t -> P u) -> P t) ->
  (forall t, P t).
Proof.
  intros H t.
  enough (H0 : forall u, subterm_eq u t -> P u).
  { apply H0, sub_refl. }
  induction t; intros u ut.
  - inversion ut; subst.
    + apply H. intros v vt. inversion vt.
    + inversion H0.
  - inversion ut; subst.
    + apply H. intros v vt. inversion vt.
    + inversion H0.
  - apply H. intros v vu. inversion ut; subst.
    + inversion vu; subst; eauto.
    + inversion H0; subst; [apply IHt1|apply IHt2].
      * eapply sub_sub, subterm_trans'; eassumption.
      * eapply sub_sub, subterm_trans'; eassumption.
  - apply H. intros v vu. inversion ut; subst.
    + inversion vu; subst; eauto.
    + inversion H0; subst; apply IHt.
      eapply sub_sub, subterm_trans'; eassumption.
  - apply H. intros v vu. inversion ut; subst.
    + inversion vu; subst; eauto.
    + inversion H0; subst; [apply IHt1|apply IHt2].
      * eapply sub_sub, subterm_trans'; eassumption.
      * eapply sub_sub, subterm_trans'; eassumption.
  - apply H. intros v vu. inversion ut; subst.
    + inversion vu; subst; eauto.
    + inversion H0; subst; [apply IHt1|apply IHt2].
      * eapply sub_sub, subterm_trans'; eassumption.
      * eapply sub_sub, subterm_trans'; eassumption.
  - apply H. intros v vu. inversion ut; subst.
    + inversion vu; subst; eauto.
    + inversion H0; subst; [apply IHt1|apply IHt2].
      * eapply sub_sub, subterm_trans'; eassumption.
      * eapply sub_sub, subterm_trans'; eassumption.
  - apply H. intros v vu. inversion ut; subst.
    + inversion vu; subst; eauto.
    + inversion H0; subst; apply IHt.
      eapply sub_sub, subterm_trans'; eassumption.
  - apply H. intros v vu. inversion ut; subst.
    + inversion vu; subst; eauto.
    + inversion H0; subst; apply IHt.
      eapply sub_sub, subterm_trans'; eassumption.
Qed.