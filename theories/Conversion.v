From Coq Require Import Program.Equality Lia.
Require Import Ast Subst Tactics Subterm.

Reserved Notation "a '▷' b" (at level 50, format "'[' a '/' '▷' '/'  b ']'").
Reserved Notation "a '▸' b" (at level 50, format "'[' a '/' '▸' '/'  b ']'").
Reserved Notation "a '≡' b" (at level 50, format "'[' a '/' '≡' '/'  b ']'").
Reserved Notation "a '⇒' b" (at level 50, format "'[' a '/' '⇒' '/'  b ']'").

Open Scope t_scope.
Open Scope subst_scope.
Section Conversion.
Declare Scope r_scope.

Inductive red1 : term -> term -> Prop :=
| red1_beta_app u t       : (λ,t) @ u ▷ t[u]
| red1_beta_pi1 u v       : π₁ ⟨u, v⟩ ▷ u
| red1_beta_pi2 u v       : π₂ ⟨u, v⟩ ▷ v
| red1_beta_J t x         : J(t, Refl(x)) ▷ t[x]
| red1_eta_lambda f       : λ,(lift 1 0 f) @ ^0 ▷ f
| red1_eta_pair p         : ⟨π₁ p,π₂ p⟩ ▷ p
| red1_prod_cong_l A A' B : A ▷ A' -> ∏ A, B ▷ ∏ A', B
| red1_prod_cong_r A B B' : B ▷ B' -> ∏ A, B ▷ ∏ A, B'
| red1_lambda_cong t t'   : t ▷ t' -> λ, t ▷ λ, t'
| red1_app_cong_l u u' v  : u ▷ u' -> u @ v ▷ u' @ v
| red1_app_cong_r u v v'  : v ▷ v' -> u @ v ▷ u @ v'
| red1_sum_cong_l A A' B  : A ▷ A' -> ∑ A, B ▷ ∑ A', B
| red1_sum_cong_r A B B'  : B ▷ B' -> ∑ A, B ▷ ∑ A, B'
| red1_pair_cong_l u u' v : u ▷ u' -> ⟨u, v⟩ ▷ ⟨u', v⟩
| red1_pair_cong_r u v v' : v ▷ v' -> ⟨u, v⟩ ▷ ⟨u, v'⟩
| red1_pi1_cong p p'      : p ▷ p' -> π₁ p ▷ π₁ p'
| red1_pi2_cong p p'      : p ▷ p' -> π₂ p ▷ π₂ p'
| red1_eq_cong_l u u' v   : u ▷ u' -> u == v ▷ u' == v
| red1_eq_cong_r u v v'   : v ▷ v' -> u == v ▷ u == v'
| red1_refl_cong u u'     : u ▷ u' -> Refl(u) ▷ Refl(u')
| red1_J_cong_l t t' p    : t ▷ t' -> J(t,p) ▷ J(t',p)
| red1_J_cong_r t p p'    : p ▷ p' -> J(t,p) ▷ J(t,p')
| red1_tp_cong_l p p' t   : p ▷ p' -> tTransport p t ▷ tTransport p' t 
| red1_tp_cong_r p t t'   : t ▷ t' -> tTransport p t ▷ tTransport p t' 
where "a '▷' b" := (red1 a b) : r_scope.

Inductive red : term -> term -> Prop :=
| red_refl u     : u ▸ u
| red_red1 u v w : u ▷ v -> v ▸ w -> u ▸ w
where "a '▸' b" := (red a b) : r_scope.

Inductive conv : term -> term -> Prop :=
| conv_refl u      : u ≡ u
| conv_red_l u v w : u ▷ v -> v ≡ w -> u ≡ w
| conv_red_r u v w : w ▷ v -> u ≡ v -> u ≡ w
where "a '≡' b" := (conv a b) : r_scope.

Inductive parred : term -> term -> Prop :=
| parred_rel n              : ^n ⇒ ^n
| parred_sort s             : *s ⇒ *s
| parred_beta_app t t' u u' : t ⇒ t' -> u ⇒ u' -> (λ,t) @ u ⇒ t'[u']
| parred_beta_pi1 u u' v v' : u ⇒ u' -> v ⇒ v' -> π₁ ⟨u, v⟩ ⇒ u'
| parred_beta_pi2 u u' v v' : u ⇒ u' -> v ⇒ v' -> π₂ ⟨u, v⟩ ⇒ v'
| parred_beta_J t t' x x'   : t ⇒ t' -> x ⇒ x' -> J(t, Refl(x)) ⇒ t'[x']
(* | parred_eta_lambda f f'    : f ⇒ f' -> (λ, (lift 1 0 f) @ ^0) ⇒ f' *)
| parred_eta_pair p p'      : p ⇒ p' -> ⟨π₁ p,π₂ p⟩ ⇒ p'
| parred_prod A A' B B'     : A ⇒ A' -> B ⇒ B' -> ∏ A, B ⇒ ∏ A', B'
| parred_lambda t t'        : t ⇒ t' -> λ, t ⇒ λ, t'
| parred_app u u' v v'      : u ⇒ u' -> v ⇒ v' -> u @ v ⇒ u' @ v'
| parred_sum A A' B B'      : A ⇒ A' -> B ⇒ B' -> ∑ A, B ⇒ ∑ A', B'
| parred_pair u u' v v'     : u ⇒ u' -> v ⇒ v' -> ⟨u, v⟩ ⇒ ⟨u', v'⟩
| parred_pi1 p p'           : p ⇒ p' -> π₁ p ⇒ π₁ p'
| parred_pi2 p p'           : p ⇒ p' -> π₂ p ⇒ π₂ p'
| parred_eq u u' v v'       : u ⇒ u' -> v ⇒ v' -> (u == v) ⇒ (u' == v')
| parred_refl u u'          : u ⇒ u' -> Refl(u) ⇒ Refl(u')
| parred_J t t' p p'        : t ⇒ t' -> p ⇒ p' -> J(t,p) ⇒ J(t',p')
| parred_tp p p' t t'        : p ⇒ p' -> t ⇒ t' -> tTransport p t ⇒ tTransport p' t'
where "a '⇒' b" := (parred a b) : r_scope.

Fixpoint parred_nf (t : term) : term :=
match t with
| ^n            => ^n
| *s            => *s
| ∏A, B         => ∏ parred_nf A, parred_nf B
(* | λ, f @ ^0     => parred_nf f *)
| λ, t          => λ, parred_nf t
| (λ, f) @ v    => (parred_nf f)[parred_nf v]
| u @ v         => parred_nf u @ parred_nf v
| ∑ A, B        => ∑ parred_nf A, parred_nf B
| ⟨u, v⟩ =>
  match u, v with
  | π₁ p, π₂ q =>
    match (term_eq_dec p q) with
    | left _      => parred_nf p
    | right _     => ⟨parred_nf u, parred_nf v⟩
    end
  | _, _ => ⟨parred_nf u, parred_nf v⟩
  end
| π₁ ⟨u,v⟩      => parred_nf u
| π₁ p          => π₁ (parred_nf p)
| π₂ ⟨u,v⟩      => parred_nf v
| π₂ p          => π₂ (parred_nf p)
| u == v        => (parred_nf u) == (parred_nf v)
| Refl(u)       => Refl(parred_nf u)
| J(t, Refl(x)) => (parred_nf t)[parred_nf x]
| J(t, p)       => J(parred_nf t, parred_nf p)
| tTransport p t => tTransport (parred_nf p) (parred_nf t)
end.

End Conversion.

Declare Scope r_scope.

Notation "a '▷' b" := (red1 a b) : r_scope.
Notation "a '▸' b" := (red a b) : r_scope.
Notation "a '≡' b" := (conv a b) : r_scope.
Notation "a '⇒' b" := (parred a b) : r_scope.

Open Scope r_scope.

Lemma lift_red1 (u v : term) (uv : u ▷ v) (n k : nat)
: lift n k u ▷ lift n k v.
Proof.
  revert n k. induction uv; intros m k;
  unfold lift; simpl; subst_helper; eauto using red1.
  - replace (lift m k t[u]) with (lift m (k+1) t)[lift m k u].
    apply red1_beta_app.
    replace k with (k + 0) by lia.
    rewrite lift_subst. f_equal; f_equal; lia.
  - replace (lift m k t[x]) with (lift m (k+1) t)[lift m k x].
    apply red1_beta_J.
    replace k with (k + 0) by lia.
    rewrite lift_subst. f_equal; f_equal; lia.
  - replace (skip (jump m) (k + 1) 0) with 0.
    replace (lift m (k + 1) (lift 1 0 f)) with (lift 1 0 (lift m k f)).
    apply red1_eta_lambda.
    + apply lift_lift'.
    + unfold skip, jump. comp_cases.
Qed.

Lemma red_prod_cong A A' B B' (AA' : A ▸ A') (BB' : B ▸ B')
: ∏ A, B ▸ ∏ A', B'.
Proof.
  induction AA'; eauto using red, red1.
  induction BB'; eauto using red, red1.
Qed.

Lemma red_lambda_cong t t' (tt' : t ▸ t')
: λ, t ▸ λ, t'.
Proof.
  induction tt'; eauto using red, red1.
Qed.

Lemma red_app_cong u u' v v' (uu' : u ▸ u') (vv' : v ▸ v')
: u @ v ▸ u' @ v'.
Proof.
  induction uu'; eauto using red, red1.
  induction vv'; eauto using red, red1.
Qed.

Lemma red_sum_cong A A' B B' (AA' : A ▸ A') (BB' : B ▸ B')
: ∑ A, B ▸ ∑ A', B'.
Proof.
  induction AA'; eauto using red, red1.
  induction BB'; eauto using red, red1.
Qed.

Lemma red_pair_cong u u' v v' (uu' : u ▸ u') (vv' : v ▸ v')
: ⟨u, v⟩ ▸ ⟨u', v'⟩.
Proof.
  induction uu'; eauto using red, red1.
  induction vv'; eauto using red, red1.
Qed.

Lemma red_pi1_cong p p' (pp' : p ▸ p')
: π₁ p ▸ π₁ p'.
Proof.
  induction pp'; eauto using red, red1.
Qed.

Lemma red_pi2_cong p p' (pp' : p ▸ p')
: π₂ p ▸ π₂ p'.
Proof.
  induction pp'; eauto using red, red1.
Qed.

Lemma red_eq_cong u u' v v' (uu' : u ▸ u') (vv' : v ▸ v')
: (u == v) ▸ (u' == v').
Proof.
  induction uu'; eauto using red, red1.
  induction vv'; eauto using red, red1.
Qed.

Lemma red_refl_cong u u' (uu' : u ▸ u')
: Refl(u) ▸ Refl(u').
Proof.
  induction uu'; eauto using red, red1.
Qed.

Lemma red_J_cong t t' p p' (tt' : t ▸ t') (pp' : p ▸ p')
: J(t,p) ▸ J(t',p').
Proof.
  induction tt'; eauto using red, red1.
  induction pp'; eauto using red, red1.
Qed.

Lemma red_tp_cong p p' t t' (pp' : p ▸ p') (tt' : t ▸ t')
: tTransport p t ▸ tTransport p' t'.
Proof.
  induction pp'; eauto using red, red1.
  induction tt'; eauto using red, red1.
Qed.

Create HintDb red_cong.
#[export] Hint Resolve red_prod_cong : red_cong.
#[export] Hint Resolve red_lambda_cong : red_cong.
#[export] Hint Resolve red_app_cong : red_cong.
#[export] Hint Resolve red_sum_cong : red_cong.
#[export] Hint Resolve red_pair_cong : red_cong.
#[export] Hint Resolve red_pi1_cong : red_cong.
#[export] Hint Resolve red_pi2_cong : red_cong.
#[export] Hint Resolve red_eq_cong : red_cong.
#[export] Hint Resolve red_refl_cong : red_cong.
#[export] Hint Resolve red_J_cong : red_cong.
#[export] Hint Resolve red_tp_cong : red_cong.


Lemma red_trans {u v w : term} (uv : u ▸ v) (vw : v ▸ w)
: u ▸ w.
Proof.
  induction uv; eauto using red.
Qed.

Lemma lift_red (u v : term) (uv : u ▸ v) (n k : nat)
: lift n k u ▸ lift n k v.
Proof.
  induction uv; eauto using red.
  eapply red_red1. apply lift_red1. eassumption.
  assumption.
Qed.

Lemma subst_red (u u' v v' : term) (uu' : u ▸ u') (vv' : v ▸ v') (n : nat)
: v[n ← u] ▸ v'[n ← u'].
Proof.
  revert n u u' uu'. induction vv'; intros n x x' xx'.
  - revert n x x' xx'. induction u; intros m x x' xx'; simpl in *;
    eauto using red with red_cong.
    comp_cases; eauto using red.
    apply lift_red. assumption.
  - eapply red_trans; [|apply IHvv'; eassumption].
    clear IHvv' x' xx' vv'.
    revert n. induction H; intros n; simpl in *;
    eauto using red, red1 with red_cong.
    + eapply red_red1. apply red1_beta_app.
      replace (S n) with (S n + 0) by lia.
      replace n with (n + 0) by lia.
      rewrite subst_subst.
      replace (n + 0 + 0) with (n + 0) by lia.
      apply red_refl.
    + eapply red_red1. apply red1_beta_J.
      replace (S n) with (S n + 0) by lia.
      replace n with (n + 0) by lia.
      rewrite subst_subst.
      replace (n + 0 + 0) with (n + 0) by lia.
      apply red_refl.
    + replace (lift 1 0 f)[S n ← x] with (lift 1 0 f[n ← x]).
      eapply red_red1. apply red1_eta_lambda. apply red_refl.
      replace n with (n + 0) by lia.
      rewrite lift_subst'.
      f_equal. lia.
Qed.

Lemma lift_parred (u v : term) (n k : nat)
: u ⇒ v -> lift n k u ⇒ lift n k v.
Proof.
  intros uv.
  revert n k. induction uv; intros m k;
  unfold lift; simpl; subst_helper; eauto using parred.
  - replace (lift m k t'[u']) with (lift m (k+1) t')[lift m k u'].
    { apply parred_beta_app; eauto. }
    replace k with (k + 0) by lia.
    rewrite lift_subst. f_equal; f_equal; lia.
  (* - replace (lift m (k + 1) (lift 1 0 f)) with (lift 1 0 (lift m k f)) by apply lift_lift'.
    replace (skip (jump m) (k + 1) 0) with 0 by (unfold skip, jump; comp_cases).
    apply parred_eta_lambda. apply IHuv. *)
  - replace (lift m k t'[x']) with (lift m (k+1) t')[lift m k x'].
    { apply parred_beta_J; eauto. }
    replace k with (k + 0) by lia.
    rewrite lift_subst. f_equal; f_equal; lia.
Qed.

Lemma subst_parred (u u' v v' : term) (n : nat)
: u ⇒ u' -> v ⇒ v' -> v[n ← u] ⇒ v'[n ← u'].
Proof.
  intros uu' vv'.
  revert n. induction vv'; intros m; simpl in *; eauto using parred.
  - comp_cases; eauto using parred.
    apply lift_parred. assumption.
  - replace t'[u'0][m ← u'] with t'[S m ← u'][u'0[m ← u']].
    apply parred_beta_app; [apply IHvv'1 | apply IHvv'2].
    replace (S m) with (S m + 0) by lia.
    rewrite subst_subst.
    f_equal. lia.
  - replace t'[x'][m ← u'] with t'[S m ← u'][x'[m ← u']].
    apply parred_beta_J; eauto.
    replace (S m) with (S m + 0) by lia.
    rewrite subst_subst.
    f_equal. lia.
  (* - replace (subst u (S m) (lift 1 0 f)) with (lift 1 0 (subst u m f)).
    { apply parred_eta_lambda. apply IHvv'. }
    replace m with (m + 0) by lia.
    rewrite lift_subst'. f_equal. lia. *)
Qed.

(* Lemma parred_diamond {u v w : term} (uv : u ⇒ v) (uw : u ⇒ w)
: exists t, v ⇒ t /\ w ⇒ t.
Proof.
  revert w uw. induction uv; intros w uw; inversion uw; subst.
  - exists ^n. split; eauto using parred.
  -  exists *s. split; eauto using parred.
  - destruct (IHuv1 _ H1) as [x [t'x t'0x]].
    destruct (IHuv2 _ H3) as [y [u'y u'0y]].
    exists (subst y 0 x).
    split; apply subst_parred; assumption.
  - inversion H1. subst.
    + assert (fw : lift 1 0 f @ ^0 ⇒ lift 1 0 u'0 @ ^0).
      { apply parred_app. apply lift_parred. assumption. apply parred_rel. }
      destruct (IHuv1 _ fw) as [x [? ?]].
      destruct (IHuv2 _ H3) as [y [? ?]].
      exists (subst y 0 x). split.
      * apply subst_parred; assumption.
      * admit.
        
    + destruct (IHuv1 _ H0) as [x [? ?]].
      destruct (IHuv2 _ H3) as [y [? ?]].
      exists (subst y 0 x). split; [apply subst_parred|apply parred_beta_app]; assumption.
  - destruct (IHuv1 _ H1) as [x [u'x wx]].
    exists x. split; assumption.
  - admit.
  - destruct (IHuv2 _ H3) as [x [u'x wx]].
    exists x. split; assumption.
  - admit.
  - assert (eq : f0 = f). { eapply lift_injective. eassumption. }
    rewrite eq in *.
    apply IHuv. assumption.
  - admit.
  - apply IHuv. assumption.
  - admit.
  - destruct (IHuv1 _ H1) as [x [A'x wx]].
    destruct (IHuv2 _ H3) as [y [B'y wy]].
    exists (∏x, y). split; apply parred_prod; assumption.
  - admit.
  - destruct (IHuv _ H0) as [x [t'x wx]].
    exists (λ, x). split; apply parred_lambda; assumption.
  - admit.
  - destruct (IHuv1 _ H1) as [x [u'x wx]].
    destruct (IHuv2 _ H3) as [y [v'y wy]].
    exists (x @ y). split; apply parred_app; assumption.
  - destruct (IHuv1 _ H1) as [x [A'x wx]].
    destruct (IHuv2 _ H3) as [y [B'y wy]].
    exists (∑x, y). split; apply parred_sum; assumption.
  - admit.
  - destruct (IHuv1 _ H1) as [x [u'x wx]].
    destruct (IHuv2 _ H3) as [y [v'y wy]].
    exists (⟨x, y⟩). split; apply parred_pair; assumption.
  - admit.
  - destruct (IHuv _ H0) as [x [p'x wx]].
    exists (π₁ x). split; apply parred_pi1; assumption.
  - admit.
  - destruct (IHuv _ H0) as [x [p'x wx]].
    exists (π₂ x). split; apply parred_pi2; assumption.
Admitted. *)

Lemma sumboolT T P (b : {P} + {~ P}) x y : P -> (if b then x else y) = x :> T.
Proof.
intros; destruct b; tauto.
Qed.

Lemma sumboolF T P (b : {P} + {~ P}) x y : ~ P -> (if b then x else y) = y :> T.
Proof.
intros; destruct b; tauto.
Qed.
    
(* ⟨π₁ ⟨π₁ p,π₂ p⟩, π₂ ⟨π₁ p, π₂ p⟩⟩ *)

Lemma red_wcr (u v w : term)
: u ▷ v -> u ▷ w -> exists x : term, v ▸ x /\ w ▸ x.
Proof.
  revert v w.
  induction u using term_strong_ind.
  intros v w uv uw.
  destruct u; inversion uv; inversion uw; subst;
  repeat match goal with
  | H : ?x = _ |- _ => subst x
  | H : _ = ?x |- _ => subst x
  | H : _ = _ |- _ => discriminate H
  | H : ?x = ?x |- _ => clear H
  | H : ?f _ = ?f _ |- _ => progress injection H as H
  | H : ?f _ _ = ?f _ _ |- _ => progress injection H as H
  | H : ?f _ _ _ = ?f _ _ _ |- _ => progress injection H as H
  | H : lift ?n ?k ?v = lift ?n ?k ?w |- _ => apply lift_injective in H
  | |- exists x, ?u ▸ x /\ ?u ▸ x => ( exists u; split; apply red_refl )
  end.
  
  - assert (s_u1 : subterm u1 (∏u1, u2)) by subterm_solve.
    destruct (H _ s_u1 _ _ H3 H7) as [u [A'u  A'0u]].
    exists (∏u, u2).
    split; apply red_prod_cong; eauto using red.
  - exists (∏A', B'). split; apply red_prod_cong; eauto using red.
  - exists (∏A', B'). split; apply red_prod_cong; eauto using red.
  - assert (s_u2 : subterm u2 (∏u1, u2)) by subterm_solve.
    destruct (H _ s_u2 _ _ H3 H7) as [u [B'u  B'0u]].
    exists (∏u1, u).
    split; apply red_prod_cong; eauto using red.
  - inversion H3; subst.
    + unfold lift in H1. destruct v; simpl in H1; try discriminate H1.
      injection H1 as H1. subst. subst_helper. replace (0 + 1) with 1 in * by lia.
      replace ((lift 1 1 v) [^0]) with v.
      exists (λ, v); eauto using red.
      rewrite lift_subst_rel0. reflexivity. exact 0.
    + admit.
    + inversion H4.
  - inversion H1; subst.
    + unfold lift in H2. destruct w; try discriminate; simpl in H2.
      injection H2 as H2. subst. subst_helper. replace (0 + 1) with 1 in * by lia.
      replace ((lift 1 1 w) [^0]) with w.
      exists (λ, w); eauto using red.
      rewrite lift_subst_rel0. reflexivity. exact 0.
    + admit.
    + inversion H4.
  - assert (s_u : subterm u (λ, u)) by subterm_solve.
    destruct (H u s_u _ _ H1 H4) as [x [t'x t'0x]].
    exists (λ, x). split; apply red_lambda_cong; assumption.
  - inversion H6; subst.
    + simpl. rewrite lift0k.
      replace (lift 1 0 u') [u2] with u'.
      exists (u' @ u2). eauto using red, red1.
      rewrite subst_lift by lia. rewrite lift0k. reflexivity.
    + exists t'[u2]. split.
      * apply subst_red; eauto using red.
      * eauto using red, red1.
  - exists t [v']. split.
    + apply subst_red; eauto using red.
    + eapply red_red1. apply red1_beta_app. apply red_refl.
  - inversion H3; subst.
    + admit.
    + exists t' [u2]; split; eauto using red, red1.
      apply subst_red; eauto using red.
  - assert (s_u1 : subterm u1 (u1 @ u2)) by subterm_solve.
    destruct (H u1 s_u1 _ _ H3 H7) as [u [u'u u'0u]].
    exists (u @ u2); split; apply red_app_cong; eauto using red.
  - exists (u' @ v'); split; apply red_app_cong; eauto using red.
  - exists (t[v']). split; eauto using red, red1, subst_red.
  - exists (u' @ v'); split; apply red_app_cong; eauto using red.
  - assert (s_u2 : subterm u2 (u1 @ u2)) by subterm_solve.
    destruct (H u2 s_u2 _ _ H3 H7) as [u [u'u u'0u]].
    exists (u1 @ u); split; apply red_app_cong; eauto using red.
  - assert (s_u1 : subterm u1 (∑u1, u2)) by subterm_solve.
    destruct (H u1 s_u1 _ _ H3 H7) as [u [u'u u'0u]].
    exists (∑u, u2); split; apply red_sum_cong; eauto using red.
  - exists (∑A', B'). split; apply red_sum_cong; eauto using red.
  - exists (∑A', B'). split; apply red_sum_cong; eauto using red.
  - assert (s_u2 : subterm u2 (∑u1, u2)) by subterm_solve.
    destruct (H u2 s_u2 _ _ H3 H7) as [u [u'u u'0u]].
    exists (∑u1, u); split; apply red_sum_cong; eauto using red.
  - inversion H6; subst.
    + exists (⟨u', v0⟩). eauto using red, red1.
    + exists p'. eauto 10 using red, red1.
  - inversion H6; subst.
    + exists (⟨u, v'⟩). eauto using red, red1.
    + exists p'. eauto 10 using red, red1.
  - inversion H3; subst.
    + exists (⟨u', v⟩). eauto using red, red1.
    + exists p'. eauto 10 using red, red1.
  - assert (s_u1 : subterm u1 ⟨u1, u2⟩) by subterm_solve.
    destruct (H u1 s_u1 _ _ H3 H7) as [u [u'u u'0u]].
    exists (⟨u, u2⟩). split; apply red_pair_cong; eauto using red.
  - exists (⟨u', v'⟩). eauto 10 using red, red1.
  - inversion H3; subst.
    + exists (⟨u, v'⟩). eauto using red, red1.
    + exists p'. eauto 10 using red, red1.
  - exists (⟨u', v'⟩). eauto 10 using red, red1.
  - assert (s_u2 : subterm u2 ⟨u1, u2⟩) by subterm_solve.
    destruct (H u2 s_u2 _ _ H3 H7) as [v [v'v v'0v]].
    exists (⟨u1, v⟩). split; apply red_pair_cong; eauto using red.
  - inversion H3; subst.
    + exists (π₁ p'). eauto using red.
    + exists u'. eauto using red, red1.
    + exists v. eauto using red, red1.
  - inversion H1; subst.
    + exists (π₁ p'). eauto using red.
    + exists u'. eauto using red, red1.
    + exists w. eauto using red, red1.
  - assert (s_u : subterm u (π₁ u)) by subterm_solve.
    destruct (H u s_u _ _ H1 H4) as [x [p'x p'0x]].
    exists (π₁ x). split; apply red_pi1_cong; assumption.
  - inversion H3; subst.
    + exists (π₂ p'). eauto using red.
    + exists v. eauto using red, red1.
    + exists v'. eauto using red, red1.
  - inversion H1; subst.
    + exists (π₂ p'). eauto using red.
    + exists w. eauto using red, red1.
    + exists v'. eauto using red, red1.
  - assert (s_u : subterm u (π₂ u)) by subterm_solve.
    destruct (H u s_u _ _ H1 H4) as [x [p'x p'0x]].
    exists (π₂ x). split; apply red_pi2_cong; assumption.
  - assert (s_u1 : subterm u1 (u1 == u2)) by subterm_solve.
    destruct (H u1 s_u1 _ _ H3 H7) as [x [u'x u'0x]].
    exists (x == u2). split; apply red_eq_cong; eauto using red.
  - exists (u' == v'). split; apply red_eq_cong; eauto using red.
  - exists (u' == v'). split; apply red_eq_cong; eauto using red.
  - assert (s_u2 : subterm u2 (u1 == u2)) by subterm_solve.
    destruct (H u2 s_u2 _ _ H3 H7) as [x [v'x v'0x]].
    exists (u1 == x). split; apply red_eq_cong; eauto using red.
  - assert (s_u : subterm u Refl(u)) by subterm_solve.
    destruct (H _ s_u _ _ H1 H4) as [x [u'x u'0x]].
    exists (Refl(x)). split; apply red_refl_cong; assumption.
  - exists (t'[x]). eauto using red, red1, subst_red.
  - inversion H6. subst.
    exists (u1 [u']). eauto using red, red1, subst_red.
  - exists (t'[x]). eauto using red, red1, subst_red.
  - assert (s_u1 : subterm u1 J(u1, u2)) by subterm_solve.
    destruct (H _ s_u1 _ _ H3 H7) as [x [t'x t'0x]].
    exists (J(x, u2)). eauto using red, red1, red_J_cong.
  - exists (J(t', p')). split; apply red_J_cong; eauto using red.
  - inversion H3. subst.
    exists (u1 [u']). eauto using red, red1, subst_red.
  - exists (J(t', p')). split; apply red_J_cong; eauto using red.
  - assert (s_u2 : subterm u2 J(u1, u2)) by subterm_solve.
    destruct (H _ s_u2 _ _ H3 H7) as [x [p'x p'0x]].
    exists (J(u1, x)). eauto using red, red1, red_J_cong.
  - assert (s_u1 : subterm u1 (tTransport u1 u2)) by subterm_solve.
    destruct (H _ s_u1 _ _ H3 H7) as [x [p'x p'0x]].
    exists (tTransport x u2). eauto using red, red1, red_tp_cong.
  - exists (tTransport p' t'). split; apply red_tp_cong; eauto using red.
  - exists (tTransport p' t'). split; apply red_tp_cong; eauto using red.
  - assert (s_u2 : subterm u2 (tTransport u1 u2)) by subterm_solve.
    destruct (H _ s_u2 _ _ H3 H7) as [x [t'x t'0x]].
    exists (tTransport u1 x). eauto using red, red1, red_tp_cong.
Admitted.

(* Lemma red_nf_wcr (u : term)
: forall v : term, u ⇒ v -> v ▸ (parred_nf u).
Proof.
  induction u using term_strong_ind; intros v uv.
  inversion uv; simpl; subst; eauto using red, red1.
  - apply subst_red.
    + apply H. subterm_solve. assumption.
    + apply H. subterm_solve. assumption.
  - apply H. subterm_solve. assumption.
  - apply H. subterm_solve. assumption.
  - apply subst_red.
    + apply H. subterm_solve. assumption.
    + apply H. subterm_solve. assumption.
  - rewrite sumboolT by reflexivity.
    apply H. subterm_solve. assumption.
  - apply red_prod_cong.
    + apply H. subterm_solve. assumption.
    + apply H. subterm_solve. assumption.
  - apply red_lambda_cong.
    apply H. subterm_solve. assumption.
  - apply H in H0. 2: { subterm_solve. }
    apply H in H1. 2: { subterm_solve. }
    destruct u0; try (apply red_app_cong; assumption).
    apply (@red_trans _ ((parred_nf (λ, u0)) @ (parred_nf v0))).
    + apply red_app_cong; assumption.
    + simpl. eapply red_red1. { apply red1_beta_app. }
      apply red_refl.
  - apply red_sum_cong.
    + apply H. subterm_solve. assumption.
    + apply H. subterm_solve. assumption.
  - assert (Hu : u' ▸ parred_nf u0). { apply H. subterm_solve. assumption. }
    assert (Hv : v' ▸ parred_nf v0). { apply H. subterm_solve. assumption. }
    destruct u0; try ( apply red_pair_cong; assumption ).
    destruct v0; try ( apply red_pair_cong; assumption ).
    destruct (term_eq_dec u0 v0) as [<-|neq].
    + apply (@red_trans _ ⟨π₁ (parred_nf u0), π₂ (parred_nf u0)⟩).
      2: { eauto using red, red1. }
      destruct u0; simpl in *;
      try ( apply red_pair_cong; assumption ).
      
    + apply red_pair_cong; assumption.

  


Qed. *)

Lemma parred_strong_diamond (u : term)
: forall v : term, u ⇒ v -> v ⇒ (parred_nf u).
Proof.
    intros v uv.
    induction uv; eauto using parred.
    - simpl. apply subst_parred; assumption.
    - simpl. apply subst_parred; assumption.
    - simpl. rewrite sumboolT by reflexivity. assumption.
    - destruct uv1; eauto using parred.
      simpl in *. inversion IHuv1.
      apply parred_beta_app; assumption.
    - destruct u; eauto using parred.
      destruct v; eauto using parred.
      simpl. destruct (term_eq_dec u v) as [<-|neq].
      + simpl in *.
    - destruct uv; eauto using parred.
      simpl in *. inversion IHuv.
      eapply parred_beta_pi1; eassumption.
    - destruct uv; eauto using parred.
      simpl in *. inversion IHuv.
      eapply parred_beta_pi2; eassumption.
    - destruct uv2; eauto using parred.
      simpl in *. inversion IHuv2.
      eapply parred_beta_J; eassumption.
Qed.

Lemma parred_diamond {u v w : term} (uv : u ⇒ v) (uw : u ⇒ w)
: exists t, v ⇒ t /\ w ⇒ t.
Proof.
  exists (parred_nf u).
  split; apply parred_strong_diamond; assumption.
Qed.

Lemma parred_identity u
: u ⇒ u.
Proof.
  induction u; eauto using parred.
Qed.

Lemma red1_parred u v
: u ▷ v -> u ⇒ v.
Proof.
  intro uv.
  induction uv; eauto using parred, parred_refl.
Admitted.

Lemma parred_red u v
: u ⇒ v -> u ▸ v.
Proof.
  intro uv.
  induction uv; eauto using red, red1 with red_cong.
  - eapply red_red1. apply red1_beta_app.
    apply subst_red; assumption.
  - eapply red_red1. apply red1_beta_J.
    apply subst_red; assumption.
Qed.

Lemma red1_wcr { u v w : term} (uv : u ▷ v) (uw : u ▷ w)
: exists x, v ▸ x /\ w ▸ x.
Proof.
  apply red1_parred in uv.
  apply red1_parred in uw.
  destruct (parred_diamond uv uw) as [x [vx wx]].
  exists x. split; apply parred_red; assumption.
Qed.

Lemma red_cr { u v w : term } (uv : u ▸ v) (uw : u ▸ w)
: exists x, v ▸ x /\ w ▸ x.
Admitted.

Lemma conv_sym u v
: u ≡ v -> v ≡ u.
Proof.
    intro uv.
    induction uv.
    - apply conv_refl.
    - apply conv_red_r with v; assumption.
    - apply conv_red_l with v; assumption.
Qed.

Lemma conv_red {u v : term} (uv : u ≡ v)
: exists w, u ▸ w /\ v ▸ w.
Proof.
  induction uv.
  - exists u. split; apply red_refl.
  - destruct IHuv as [x [vx wx]]; eauto using red.
  - destruct IHuv as [x [ux vx]]; eauto using red.
Qed.

Lemma red_conv {u v w : term} (uw : u ▸ w) (vw : v ▸ w)
: u ≡ v.
Proof.
  induction uw.
  - induction vw; eauto using conv.
  - eapply conv_red_l. eassumption. apply IHuw. assumption.
Qed.

Lemma conv_trans u v w
: u ≡ v -> v ≡ w -> u ≡ w.
Proof.
    intros uv vw.
    destruct (conv_red uv) as [x [ux vx]].
    destruct (conv_red vw) as [y [vy wy]].
    destruct (red_cr vx vy) as [z [xz yz]].
    eapply red_conv; eapply red_trans; eassumption.
Qed.

Lemma parred_example_1 p
: ⟨π₁ ⟨π₁ p,π₂ p⟩, π₂ ⟨π₁ p,π₂ p⟩⟩ ⇒ p.
Proof.
  apply parred_eta_pair.
  apply parred_eta_pair.
  apply parred_identity.
Qed.

Lemma parred_example_2 p
: ⟨π₁ ⟨π₁ p,π₂ p⟩, π₂ ⟨π₁ p,π₂ p⟩⟩ ⇒ ⟨π₁ p, π₂ p⟩.
Proof.
  apply parred_eta_pair.
  apply parred_identity.
Qed.

