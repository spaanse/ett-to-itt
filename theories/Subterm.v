Require Import Lia.
Require Import Ast Subst Tactics.
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


Fixpoint clear_rel (t : term) : term :=
match t with
| ^i => ^0
| *s => *s
| λ, t => λ, clear_rel t
| u @ v => (clear_rel u) @ (clear_rel v)
| ∏A, B => ∏clear_rel A, clear_rel B
| ∑A, B => ∑clear_rel A, clear_rel B
| ⟨u, v⟩ => ⟨clear_rel u, clear_rel v⟩
| π₁ p => π₁ (clear_rel p)
| π₂ p => π₂ (clear_rel p)
| u == v => (clear_rel u) == (clear_rel v)
| Refl(u) => Refl(clear_rel u)
| J(t, p) => J(clear_rel t, clear_rel p)

| tTransport p t => tTransport (clear_rel p) (clear_rel t)
end.

Lemma clear_rel_lift (n k : nat) (t : term)
: clear_rel (lift n k t) = clear_rel t.
Proof.
  revert n k. induction t; intros m k;
  simpl; f_equal; subst_helper; eauto.
Qed.

Lemma term_strong_ind' (P : term -> Prop) :
  (forall t, (forall u, subterm (clear_rel u) (clear_rel t) -> P u) -> P t) ->
  (forall t, P t).
Proof.
  intros H t.
  enough (H0 : forall u, subterm_eq (clear_rel u) (clear_rel t) -> P u).
  { apply H0. apply subeq_refl. }
  induction t; intros u ut.
  { inversion ut; subst.
    - destruct u; try discriminate.
      apply H. intros v vt. inversion vt.
    - inversion H0.
  }{inversion ut; subst.
    - destruct u; try discriminate.
      apply H. intros v vt. inversion vt.
    - inversion H0.
  }
  all: apply H; intros v vu; simpl in *.
  all: inversion ut; subst; simpl in *; [inversion vu | inversion H0].
  all: subst; eauto using subeq_sub, subterm_trans'.
  all: destruct u; try discriminate; simpl in *.
  all: injection H0 as H0; simplify_eqs.
  all: try rewrite H0 in *.
  all: try rewrite H2 in *.
  all: eauto using subeq_sub, subterm_trans'.
Qed.

Lemma subterm_IH (P : term -> Prop) u v :
  (forall w, subterm w u -> P w) ->
  (subterm v u) ->
  (forall w, subterm w v -> P w).
Proof.
  intros H vu w wv.
  apply H. eapply subterm_trans; eassumption.
Qed.

Ltac subterm_solve := eauto using subterm, subterm_eq.
Ltac subterm_IH_specialize u v IH := 
  assert (st : subterm u v) by subterm_solve;
  let new1 := fresh "IH" in pose proof (new1 := IH _ st);
  let new2 := fresh "IH" in pose proof (new2 := subterm_IH _ _ _ IH st);
  clear st.
Ltac subterm_IH_split :=
repeat match goal with
| IH : forall x, subterm x ^?n -> _ |- _ => clear IH
| IH : forall x, subterm x *?s -> _ |- _ => clear IH
| IH : forall x, subterm x (∏?A, ?B) -> _ |- _ =>
    subterm_IH_specialize A (∏A, B) IH;
    subterm_IH_specialize B (∏A, B) IH;
    clear IH
| IH : forall x, subterm x (λ, ?t) -> _ |- _ =>
    subterm_IH_specialize t (λ, t) IH;
    clear IH
| IH : forall x, subterm x (?u @ ?v) -> _ |- _ =>
    subterm_IH_specialize u (u @ v) IH;
    subterm_IH_specialize v (u @ v) IH;
    clear IH
| IH : forall x, subterm x (∑?A, ?B) -> _ |- _ =>
    subterm_IH_specialize A (∑A, B) IH;
    subterm_IH_specialize B (∑A, B) IH;
    clear IH
| IH : forall x, subterm x (⟨?u, ?v⟩) -> _ |- _ =>
    subterm_IH_specialize u (⟨u, v⟩) IH;
    subterm_IH_specialize v (⟨u, v⟩) IH;
    clear IH
| IH : forall x, subterm x (π₁ ?p) -> _ |- _ =>
    subterm_IH_specialize p (π₁ p) IH;
    clear IH
| IH : forall x, subterm x (π₂ ?p) -> _ |- _ =>
    subterm_IH_specialize p (π₂ p) IH;
    clear IH
| IH : forall x, subterm x (?u == ?v) -> _ |- _ =>
    subterm_IH_specialize u (u == v) IH;
    subterm_IH_specialize v (u == v) IH;
    clear IH
| IH : forall x, subterm x (Refl(?u)) -> _ |- _ =>
    subterm_IH_specialize u (Refl(u)) IH;
    clear IH
| IH : forall x, subterm x (J(?t, ?p)) -> _ |- _ =>
    subterm_IH_specialize t (J(t, p)) IH;
    subterm_IH_specialize p (J(t, p)) IH;
    clear IH
| IH : forall x, subterm x (tTransport ?t ?p) -> _ |- _ =>
    subterm_IH_specialize t (tTransport t p) IH;
    subterm_IH_specialize p (tTransport t p) IH;
    clear IH
end.