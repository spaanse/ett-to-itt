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
| sub_eq_l u u' v : subterm_eq u u' -> subterm u (u' == v)
| sub_eq_r u v v' : subterm_eq v v' -> subterm v (u == v')
| sub_refl u u' : subterm_eq u u' -> subterm u (Refl(u'))
| sub_J_l t t' p : subterm_eq t t' -> subterm t (J(t', p))
| sub_J_r t p p' : subterm_eq p p' -> subterm p (J(t, p'))
| sub_tp_l p p' t : subterm_eq p p' -> subterm p (tTransport p' t)
| sub_tp_r p t t' : subterm_eq t t' -> subterm t (tTransport p t')
with subterm_eq : term -> term -> Prop :=
| subeq_refl t : subterm_eq t t
| subeq_sub u v : subterm u v -> subterm_eq u v
.

Lemma subterm_trans {u v w : term}
: subterm u v -> subterm v w -> subterm u w
with subterm_trans' {u v w : term}
: subterm u v -> subterm_eq v w -> subterm u w.
Proof.
  - intros uv vw.
    destruct vw.
    + eapply sub_prod_l, subeq_sub, subterm_trans'; eassumption.
    + eapply sub_prod_r, subeq_sub, subterm_trans'; eassumption.
    + eapply sub_lambda, subeq_sub, subterm_trans'; eassumption.
    + eapply sub_app_l, subeq_sub, subterm_trans'; eassumption.
    + eapply sub_app_r, subeq_sub, subterm_trans'; eassumption.
    + eapply sub_sum_l, subeq_sub, subterm_trans'; eassumption.
    + eapply sub_sum_r, subeq_sub, subterm_trans'; eassumption.
    + eapply sub_pair_l, subeq_sub, subterm_trans'; eassumption.
    + eapply sub_pair_r, subeq_sub, subterm_trans'; eassumption.
    + eapply sub_pi1, subeq_sub, subterm_trans'; eassumption.
    + eapply sub_pi2, subeq_sub, subterm_trans'; eassumption.
    + eapply sub_eq_l, subeq_sub, subterm_trans'; eassumption.
    + eapply sub_eq_r, subeq_sub, subterm_trans'; eassumption.
    + eapply sub_refl, subeq_sub, subterm_trans'; eassumption.
    + eapply sub_J_l, subeq_sub, subterm_trans'; eassumption.
    + eapply sub_J_r, subeq_sub, subterm_trans'; eassumption.
    + eapply sub_tp_l, subeq_sub, subterm_trans'; eassumption.
    + eapply sub_tp_r, subeq_sub, subterm_trans'; eassumption.
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
  { apply H0, subeq_refl. }
  induction t; intros u ut.
  { inversion ut; subst.
    - apply H. intros v vt. inversion vt.
    - inversion H0.
  }{inversion ut; subst.
    - apply H. intros v vt. inversion vt.
    - inversion H0.
  }
  all: apply H; intros v vu.
  all: inversion ut; subst; [inversion vu | inversion H0].
  all: subst; eauto.
  all: eauto using subeq_sub, subterm_trans'.
Qed.

Ltac subterm_solve := eauto using subterm, subterm_eq.