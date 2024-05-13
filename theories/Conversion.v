From Coq Require Import Program.Equality Lia Nat.
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
| parred_eta_lambda f f'    : f ⇒ f' -> (λ, lift 1 0 f @ ^0) ⇒ f'
| parred_eta_pair u v p     : u ⇒ p -> v ⇒ p -> ⟨π₁ u, π₂ v⟩ ⇒ p
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
  - admit.
Admitted.

Lemma parred_identity u
: u ⇒ u.
Proof.
  induction u; eauto using parred.
Qed.

Lemma subst_parred (u u' v v' : term) (n : nat)
: u ⇒ u' -> v ⇒ v' -> v[n ← u] ⇒ v'[n ← u'].
Proof.
  intros uu' vv'.
  revert n u u' uu'. induction vv'; intros m y y' yy'; simpl in *; eauto using parred.
  - comp_cases; eauto using parred.
    apply lift_parred. assumption.
  - replace t'[u'][m ← y'] with t'[S m ← y'][u'[m ← y']].
    apply parred_beta_app; [apply IHvv'1 | apply IHvv'2]; try assumption.
    replace (S m) with (S m + 0) by lia.
    rewrite subst_subst.
    f_equal. lia.
  - replace t'[x'][m ← y'] with t'[S m ← y'][x'[m ← y']].
    apply parred_beta_J; eauto.
    replace (S m) with (S m + 0) by lia.
    rewrite subst_subst.
    f_equal. lia.
  - replace ((lift 1 0 f)[S m ← y]) with (lift 1 0 f[m ← y]).
    { apply parred_eta_lambda, IHvv'. assumption. }
    replace m with (m + 0) by lia.
    rewrite lift_subst'. f_equal. lia.
Qed.

(* Lemma parred_diamond {u v w : term} (uv : u ⇒ v) (uw : u ⇒ w)
: exists t, v ⇒ t /\ w ⇒ t.
Proof.
  revert w uw. induction uv; intros w uw; inversion uw; subst.
  - exists ^n. eauto using parred.
  -  exists *s. eauto using parred.
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
    
Lemma lift_red' (v w : term)  (n k : nat)
: (lift n k v ▷ lift n k w) -> v ▷ w.
Proof.
  revert n k w.
  induction v using term_strong_ind.
  intros n k w vw.
  inversion vw.
  - destruct v; try discriminate.
    destruct v1; try discriminate.
    unfold lift in H1. simpl in H1. subst_helper.
    injection H1 as H1. subst.
Admitted.

Lemma lift_red1' (v w : term) (n k : nat)
: (lift n k v ▷ w) -> exists w', v ▷ w'.
Proof.
  revert w n k.
  induction v using term_strong_ind;
  intros w n k vw.
  destruct v; unfold lift in vw; simpl in vw; subst_helper;
  inversion vw; subst.
  - assert (s_v1 : subterm v1 (∏v1, v2)) by subterm_solve.
    destruct (H _ s_v1 _ _ _ H3) as [x v1x].
    exists (∏x, v2). eauto using red1.
  - assert (s_v2 : subterm v2 (∏v1, v2)) by subterm_solve.
    destruct (H _ s_v2 _ _ _ H3) as [x v2x].
    exists (∏v1, x). eauto using red1.
  - destruct v; unfold lift in H1; simpl in H1; try discriminate H1; subst_helper.
    injection H1 as H1.
    destruct v2; unfold lift in H0; simpl in H0; try discriminate H0; subst_helper.
    injection H0 as H0.
    unfold skip, jump in H0.
    destruct (Nat.ltb n0 (k + 1)); comp_cases. subst.
    unfold lift in vw. simpl in vw. subst_helper. unfold skip, jump in vw.
    replace (Nat.ltb 0 (k+1)) with true in vw.
    2: { replace (k+1) with (S k) by lia. unfold Nat.ltb, Nat.leb. reflexivity. }

    
Admitted.

Lemma lift_eq (v w : term) (k i : nat)
: lift 1 i v = lift 1 (k + i + 1) w -> v = lift 1 (k + i) (unlift 1 (k + i) v).
Proof.
  revert k i w; induction v; intros k i w vw;
  unfold lift, unlift; simpl; subst_helper; f_equal;
  destruct w; try discriminate; injection vw as vw; eauto.
  - unfold skip, jump, unjump in *.
    destruct (n <? i) eqn: eq1;
    destruct (n0 <? k + i + 1) eqn: eq;
    comp_cases.
  - repeat rewrite skip_skip in H. subst_helper.
    replace (k + i + 1) with (k + (i + 1)) in *.
    eauto. lia.
  - repeat rewrite skip_skip in H. subst_helper.
    replace (k + i + 1) with (k + (i + 1)) in *.
    eauto. lia.
  - repeat rewrite skip_skip in H. subst_helper.
    replace (k + i + 1) with (k + (i + 1)) in *.
    eauto. lia.
  - repeat rewrite skip_skip in H. subst_helper.
    replace (k + i + 1) with (k + (i + 1)) in *.
    eauto. lia.
Qed.

Lemma lift_eq' (v w : term) (k : nat)
: lift 1 0 v = lift 1 (k + 1) w -> v = lift 1 k (unlift 1 k v).
Proof.
  intro vw. replace k with (k + 0) by lia. eapply lift_eq.
  replace (k+0) with k by lia. eassumption.
Qed.

Lemma lift_red1_lift (v w : term) (k : nat)
: (lift 1 k v) ▷ w -> exists w', w = lift 1 k w'.
Proof.
  revert k w. induction v;
  unfold lift; simpl; intros k w vw; inversion vw; subst_helper; subst.
  - destruct (IHv1 _ _ H2) as [x ->].
    exists (∏x, v2). unfold lift. simpl. subst_helper. reflexivity.
  - destruct (IHv2 _ _ H2) as [x ->].
    exists (∏v1, x). unfold lift. simpl. subst_helper. reflexivity.
  - destruct v; unfold lift in *; simpl in *; try discriminate; subst_helper.
    injection H0 as H0 H1.
    destruct v2; try discriminate.
    unfold lift, skip, jump in H1. simpl in H1. injection H1 as H1.
    destruct (Nat.ltb n (k+1)); try lia. subst; simpl in *.
    exists (unlift 1 k w).
    eapply lift_eq'. eassumption.
  - destruct (IHv _ _ H0) as [x ->].
    exists (λ, x). unfold lift. simpl. subst_helper. reflexivity.
  - destruct v1; try discriminate.
    unfold lift in *; simpl in *; subst_helper.
    injection H0 as H0. subst.
    replace (k + 1) with (S k + 0) by lia.
    rewrite <- lift_subst.
    replace (k+0) with k by lia. eauto.
  - destruct (IHv1 _ _ H2) as [x ->]. exists (x @ v2). eauto.
  - destruct (IHv2 _ _ H2) as [x ->]. exists (v1 @ x). eauto.
  - destruct (IHv1 _ _ H2) as [x ->].
    exists (∑x, v2). unfold lift. simpl. subst_helper. reflexivity.
  - destruct (IHv2 _ _ H2) as [x ->].
    exists (∑v1, x). unfold lift. simpl. subst_helper. reflexivity.
  - destruct v1; try discriminate.
    destruct v2; try discriminate.
    unfold lift in *; simpl in *; subst_helper.
    injection H0 as H0. injection H1 as H1. subst.
    exists v2. reflexivity.
  - destruct (IHv1 _ _ H2) as [x ->]. exists (⟨x, v2⟩). eauto.
  - destruct (IHv2 _ _ H2) as [x ->]. exists (⟨v1, x⟩). eauto.
  - destruct v; try discriminate.
    unfold lift in *; simpl in *; subst_helper.
    injection H0 as H0. subst. eauto.
  - destruct (IHv _ _ H0) as [x ->]. exists (π₁ x). eauto.
  - destruct v; try discriminate.
    unfold lift in *; simpl in *; subst_helper.
    injection H0 as H0. subst. eauto.
  - destruct (IHv _ _ H0) as [x ->]. exists (π₂ x). eauto.
  - destruct (IHv1 _ _ H2) as [x ->]. exists (x == v2). eauto.
  - destruct (IHv2 _ _ H2) as [x ->]. exists (v1 == x). eauto.
  - destruct (IHv _ _ H0) as [x ->]. exists (Refl(x)). eauto.
  - destruct v2; try discriminate.
    unfold lift in *; simpl in *; subst_helper.
    injection H1 as H1. subst.
    replace (k + 1) with (S k + 0) by lia.
    rewrite <- lift_subst.
    replace (k+0) with k by lia. eauto.
  - destruct (IHv1 _ _ H2) as [x ->]. exists (J(x,v2)).
    unfold lift. simpl. subst_helper. reflexivity.
  - destruct (IHv2 _ _ H2) as [x ->]. exists (J(v1,x)).
    unfold lift. simpl. subst_helper. reflexivity.
  - destruct (IHv1 _ _ H2) as [x ->]. exists (tTransport x v2). eauto.
  - destruct (IHv2 _ _ H2) as [x ->]. exists (tTransport v1 x). eauto.
Qed.

Lemma red_wcr (u v w : term)
: u ▷ v -> u ▷ w -> exists x : term, v ▸ x /\ w ▸ x.
Proof.
  revert v w.
  induction u using term_strong_ind.
  intros v w uv uw.
  destruct u; inversion uv; inversion uw; subst; subterm_IH_split;
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
  | H : exists x, _ /\ _ |- _ => destruct H as [? [? ?]]
  | IH : forall v w, ?u ▷ v -> ?u ▷ w -> _,
    H1 : ?u ▷ ?v', H2 : ?u ▷ ?w' |- _
    => specialize (IH v' w' H1 H2)
  end;
  eauto 10 using red, red1, subst_red with red_cong; simpl in *.
  - inversion H3; subst.
    + unfold lift in H0. destruct v; simpl in H0; try discriminate H0.
      injection H0 as H0. subst. subst_helper. replace (0 + 1) with 1 in * by lia.
      replace ((lift 1 1 v) [^0]) with v.
      exists (λ, v); eauto using red.
      rewrite lift_subst_rel0. reflexivity. exact 0.
    + destruct (lift_red1_lift _ _ _ H2) as [x ->].
      exists x. split; eauto using red, red1.
      eauto using lift_red', red.
    + inversion H2.
  - inversion H1; subst.
    + unfold lift in H0. destruct w; try discriminate; simpl in H0.
      injection H0 as H0. subst. subst_helper. replace (0 + 1) with 1 in * by lia.
      replace ((lift 1 1 w) [^0]) with w.
      exists (λ, w); eauto using red.
      rewrite lift_subst_rel0. reflexivity. exact 0.
    + destruct (lift_red1_lift _ _ _ H3) as [x ->].
      exists x. split; eauto using red, red1.
      eauto using lift_red', red.
    + inversion H3.
  - inversion H6; subst.
    + simpl. rewrite lift0k.
      replace (lift 1 0 u') [u2] with u'.
      eauto using red, red1.
      rewrite subst_lift by lia. rewrite lift0k. reflexivity.
    + eauto 10 using red, red1, subst_red.
  - inversion H3; subst.
    + simpl. rewrite lift0k.
      replace (lift 1 0 u') [u2] with u'.
      eauto using red, red1.
      rewrite subst_lift by lia. rewrite lift0k. reflexivity.
    + eauto 10 using red, red1, subst_red.
  - inversion H6; subst; eauto 10 using red, red1.
  - inversion H6; subst; eauto 10 using red, red1.
  - inversion H3; subst; eauto 10 using red, red1.
  - inversion H3; subst; eauto 10 using red, red1.
  - inversion H3; subst; eauto 10 using red, red1.
  - inversion H1; subst; eauto 10 using red, red1.
  - inversion H3; subst; eauto 10 using red, red1.
  - inversion H1; subst; eauto 10 using red, red1.
  - inversion H6. subst. eauto 10 using red, red1, subst_red.
  - inversion H3. subst. eauto 10 using red, red1, subst_red.
Qed.

(* Lemma red1_parred u v
: u ▷ v -> u ⇒ v.
Proof.
  intro uv.
  induction uv; eauto using parred, parred_refl, parred_identity.
Qed.

Lemma parred_red u v
: u ⇒ v -> u ▸ v.
Proof.
  intro uv.
  induction uv; eauto using red, red1 with red_cong.
  - eapply red_red1. apply red1_beta_app.
    apply subst_red; assumption.
  - eapply red_red1. apply red1_beta_J.
    apply subst_red; assumption.
  - eapply red_trans. 2: { eapply red_red1. apply red1_eta_pair. apply red_refl. }
    eauto with red_cong.
Qed.

Lemma lift_parred_lift (v w : term) (n k : nat)
: (lift n k v) ⇒ w -> exists w', w = lift n k w'.
Proof.
  revert n k w. induction v; intros m k w vw;
  unfold lift in *; simpl in *; inversion vw; subst; subst_helper;
  repeat match goal with
  | H1 : forall n k w, update_rel (skip (jump n) k) ?v ⇒ w -> _,
    H2 : lift _ _ ?v ⇒ ?w |- _ => apply H1 in H2
  | H : exists _, _ |- _ => destruct H
  end; subst; subst_helper.
  - unfold skip, jump. comp_cases; exists ^n;
    unfold lift, skip, jump; simpl; comp_cases.
  - exists *s. unfold lift. simpl. reflexivity.
  - exists (∏x0, x); unfold lift; simpl; rewrite skip_skip; subst_helper; f_equal.
  - unfold lift in *. destruct v; try discriminate.
    simpl in *; injection H as H H1; subst.
    destruct v2; try discriminate.
    unfold skip, jump in H1. simpl in H1. injection H1 as H1.
    destruct (n <? k + 1) eqn: eq; comp_cases. subst. subst_helper.
Admitted.

Lemma lift_parred' (v w : term) (n k : nat)
: lift n k v ⇒ lift n k w -> v ⇒ w.
Proof.
  revert n k w. induction v; intros m k w vw;
  unfold lift in *; simpl in *; inversion vw; subst.
  - admit.
  - admit.
  -
  (* destruct w; simpl in *; try discriminate;
  eauto using parred.
  - injection H as H.
    unfold skip, jump in *;
    destruct (n <? k) eqn: eq1;
    destruct (n1 <? k) eqn: eq2;
    comp_cases; replace n1 with n by lia; eauto using parred.
  *)
Admitted.

Lemma red_cr (u v w : term)
: u ▷ v -> u ⇒ w -> exists x : term, v ⇒ x /\ w ⇒ x.
Proof.
  revert v w.
  induction u using term_strong_ind.
  intros v w uv uw.
  destruct u; inversion uv; inversion uw; subst; subterm_IH_split;
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
  | H : exists x, _ /\ _ |- _ => destruct H as [? [? ?]]
  | IH : forall v w, ?u ▷ v -> ?u ⇒ w -> _,
    H1 : ?u ▷ ?v', H2 : ?u ⇒ ?w' |- _
    => specialize (IH v' w' H1 H2)
  (* | H : ?u ▷ ?v |- _ => apply red1_parred in H *)
  end;
  eauto 10 using parred, parred_identity; simpl in *.
  - inversion H3; inversion H4; subst.
    + unfold lift in H. destruct v; simpl in H; try discriminate H.
      injection H as H. subst. subst_helper. replace (0 + 1) with 1 in * by lia.
      destruct (lift_parred_lift _ _ _ _ H1) as [x ->].
      exists (λ, x); split.
      * apply lift_parred' in H1. eauto using parred.
      * apply parred_lambda.
        replace ((lift 1 1 x)[^0]) with x. { apply parred_identity. }
        rewrite lift_subst_rel0; eauto. exact 0.
    + destruct (lift_parred_lift _ _ _ _ H1) as [x ->].
      exists x. split.
      * apply lift_parred' in H1. assumption.
      * apply parred_eta_lambda, parred_identity.
  - inversion H1; subst.
    + unfold lift in H0. destruct f; try discriminate; simpl in H0.
      injection H0 as H0. subst. subst_helper. replace (0 + 1) with 1 in * by lia.
      replace ((lift 1 1 f)[^0]) with f. { eauto using parred, parred_identity. }
      rewrite lift_subst_rel0; eauto. exact 0.
    + admit.
    + inversion H3.
  - exists (t'[u']); split; apply subst_parred; eauto using parred_identity.
  - inversion H5; subst.
    + exists (u' @ v'). split.
      * simpl. rewrite subst_lift by lia. rewrite lift0k. rewrite lift0k.
        eauto using parred.
      * apply parred_identity.
    + exists (t'[v']). split; eauto using parred, subst_parred, parred_identity.
  - inversion H3; subst.
    + inversion H6; subst.
      inversion H4; subst.
      unfold lift in H. destruct u'; try discriminate; simpl in H;
      injection H as H; subst; subst_helper; replace (0 + 1) with 1 in * by lia.
      admit.
      admit.
    + admit.
  - admit.
  - inversion H5; inversion H7; subst.
    + injection H3 as -> ->.
      exists (⟨u', v'⟩). eauto using parred, parred_identity.
    + inversion H4; subst.
      * admit.
      * exists (⟨u', v'⟩). eauto using parred, parred_identity.
    + inversion H0; subst.
      * admit.
      * exists (⟨u', v'⟩). eauto using parred, parred_identity.
    + admit.




  (* - inversion H6; subst.
    + simpl. rewrite lift0k.
      replace (lift 1 0 u') [u2] with u'.
      eauto using red, red1.
      rewrite subst_lift by lia. rewrite lift0k. reflexivity.
    + eauto 10 using red, red1, subst_red.
  - inversion H3; subst.
    + simpl. rewrite lift0k.
      replace (lift 1 0 u') [u2] with u'.
      eauto using red, red1.
      rewrite subst_lift by lia. rewrite lift0k. reflexivity.
    + eauto 10 using red, red1, subst_red.
  - inversion H6; subst; eauto 10 using red, red1.
  - inversion H6; subst; eauto 10 using red, red1.
  - inversion H3; subst; eauto 10 using red, red1.
  - inversion H3; subst; eauto 10 using red, red1.
  - inversion H3; subst; eauto 10 using red, red1.
  - inversion H1; subst; eauto 10 using red, red1.
  - inversion H3; subst; eauto 10 using red, red1.
  - inversion H1; subst; eauto 10 using red, red1.
  - inversion H6. subst. eauto 10 using red, red1, subst_red.
  - inversion H3. subst. eauto 10 using red, red1, subst_red. *)
Admitted.

(* 
u ⇒ π₁ p
v ⇒ π₂ p
p ⇒ p'
u ⇒ u'
v ⇒ v'
Find z: p' ⇒ z and ⟨u', v'⟩ ⇒ z

exists: π₁ p ⇒ x ⇐ u'
exists: π₂ p ⇒ y ⇐ v'
assume² x = π₁ px with p ⇒ px
assume² y = π₂ py with p ⇒ py
exists¹: px ⇒ p'' ⇐ py
assume³ u' ⇒ π₁ p''
assume³ v' ⇒ π₂ p''
assume³ p ⇒ p''
exists¹: p' ⇒ z ⇐ p''
Then ⟨u', v'⟩ ⇒ z ⇐ p'

1 - may not be available as IH
2 - if p = ⟨a,b⟩ we may have x=a' or y=b'
3 - assumes a ⇒ b and b ⇒ c imply a ⇒ c which (by design) is not true
*)

(* 
u ⇒ π₁ p
v ⇒ π₂ p
u ⇒ u'
v ⇒ v'
Find z: p ⇒ z and ⟨u', v'⟩ ⇒ z

exists: π₁ p ⇒ x ⇐ u'
exists: π₂ p ⇒ y ⇐ v'
assume² x = π₁ px with p ⇒ px
assume² y = π₂ py with p ⇒ py
exists¹: px ⇒ p'' ⇐ py
assume³ u' ⇒ π₁ p''
assume³ v' ⇒ π₂ p''
assume³ p ⇒ p''
Then ⟨u', v'⟩ ⇒ p'' ⇐ p

1 - may not be available as IH
2 - if p = ⟨a,b⟩ we may have x=a' or y=b'
3 - assumes a ⇒ b and b ⇒ c imply a ⇒ c which (by design) is not true
*)

(* Lemma parred_unique_nf u
: exists w, forall v, u ⇒ v -> v ⇒ w.
Proof.
  induction u using term_strong_ind.
  destruct u; subterm_IH_split;
  repeat match goal with
  | H : exists w, _ |- _ => destruct H
  end;
  eexists; intros v uv;
  inversion uv; subst;
  repeat match goal with
  | H1 : forall v, ?u ⇒ v -> _,
    H2 : ?u ⇒ ?v |- _ => apply H1 in H2
  end.
  - eauto.
  - eauto.
  - eauto using parred.
  - admit.
  - admit.
  - admit.
  - admit.
  - eauto using parred.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - eauto using parred.
  - eauto using parred.
  - admit.
  - admit.
  - eauto using parred.



  repeat match goal with
  | H : ?a ⇒ ?b |- _ => inversion H; clear H; subst
  end; simpl in *; unfold lift, skip, jump in *; simpl in *;
  repeat match goal with
  | H : ?a = ?b |- _ => injection H as H; subst
  end.
  - apply parred_identity.
  - eauto using parred.
  - apply parred_eta_pair.
    + replace (π₁ ^2) with ((π₁ ^0) [^2] ).
      eauto using parred. reflexivity.
    + eauto using parred.
  - eauto using parred.
  - eauto using parred.
Qed. *)

Lemma parred_dp (u v w : term)
: u ⇒ v -> u ⇒ w -> exists x, v ⇒ x /\ w ⇒ x.
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
  end;
  repeat match goal with
  | IH : forall u, subterm u ?y -> forall v w, u ⇒ v -> u ⇒ w -> _,
    H1 : ?x ⇒ ?w1,
    H2 : ?x ⇒ ?w2 |- _ =>
      lazymatch goal with
      | H : exists z, w1 ⇒ z /\ w2 ⇒ z |- _ => fail
      | H : exists z, w2 ⇒ z /\ w1 ⇒ z |- _ => fail
      | |- _ =>
        assert (st : subterm x y) by subterm_solve;
        assert (exists z, w1 ⇒ z /\ w2 ⇒ z) by eauto;
        clear st
      end
  end;
  repeat match goal with
  | H : exists z, _ /\ _ |- _ => destruct H as [? [? ?]]
  end;
  eauto 10 using parred, subst_parred.
  - admit.
  - admit.
  - admit.
  - inversion H7; subst.
    + admit.
    + assert (IHt : exists z, t' ⇒ z /\ t'0 ⇒ z). { eapply H; try eassumption; subterm_solve. }
      destruct IHt as [? [? ?]].
      exists (x0 [x]). eauto using parred, subst_parred.
  - inversion H2; subst.
    + admit.
    + assert (IHt : exists z, t' ⇒ z /\ t'0 ⇒ z). { eapply H; try eassumption; subterm_solve. }
      destruct IHt as [? [? ?]].
      eauto using parred, subst_parred.
  - assert (pi_uv : π₁ u ⇒ π₁ v). eauto using parred.
    assert (pi_v0v : π₂ v0 ⇒ π₂ v). eauto using parred.
    assert (IHu : exists y, u' ⇒ y /\ π₁ v ⇒ y). { eapply H; try eassumption; subterm_solve. }
    assert (IHv : exists y, v' ⇒ y /\ π₂ v ⇒ y). { eapply H; try eassumption; subterm_solve. }
    destruct IHu as [y [? ?]]. destruct IHv as [z [? ?]].
    
    exists (⟨y, z⟩). split; eauto using parred.
    admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - inversion H9; subst.
    assert (IHx : exists z, x' ⇒ z /\ u' ⇒ z). { eapply H; try eassumption; subterm_solve. }
    destruct IHx as [? [? ?]].
    eauto using parred, subst_parred.
  - inversion H4; subst.
    assert (IHx : exists z, x' ⇒ z /\ u' ⇒ z). { eapply H; try eassumption; subterm_solve. }
    destruct IHx as [? [? ?]].
    eauto using parred, subst_parred.
Admitted.

Lemma parred_pair_pi2 u v p
: ⟨u, v⟩ ⇒ p -> v ⇒ π₂ p.
Proof.
  intros uvp.
  inversion uvp; subst; eauto using parred.
Admitted.

Lemma parred_strong_diamond (u : term)
: forall v : term, u ⇒ v -> v ⇒ (parred_nf u).
Proof.
  induction u using term_strong_ind.
  intros v uv. inversion uv; subst;
  repeat match goal with
  | IH : forall u, subterm u ?y -> forall v, u ⇒ v -> _,
    H1 : ?u ⇒ ?v |- _ =>
      lazymatch goal with
      | H : v ⇒ parred_nf u |- _ => fail
      | |- _ =>
        assert (st : subterm u y) by subterm_solve;
        assert (v ⇒ parred_nf u) by eauto;
        clear st
      end
  end;
  eauto using parred, subst_parred.
  - admit.
  - simpl in *.
    destruct (term_eq_dec (parred_nf u0) (parred_nf v0)) as [eq|neq].
    { assumption. }
    assert (u0v : π₁ u0 ⇒ π₁ v). { eauto using parred. }
    assert (v0v : π₂ v0 ⇒ π₂ v). { eauto using parred. }
    apply H in u0v. 2: { subterm_solve. }
    apply H in v0v. 2: { subterm_solve. }
    replace (match u0 with
    | ⟨u, _⟩ => parred_nf u
    | _ => π₁ (parred_nf u0)
    end) with (parred_nf (π₁ u0)) by reflexivity.
    replace (match v0 with
    | ⟨_, v1⟩ => parred_nf v1
    | _ => π₂ (parred_nf v0)
    end) with (parred_nf (π₂ v0)) by reflexivity.
    inversion u0v; inversion v0v; subst.
    + injection H8 as H8; subst.
      eauto using parred.
    + apply parred_pair; eauto.
      

      

  - admit.
  - simpl.
    destruct (term_eq_dec (parred_nf u) (parred_nf v)) as [eq | neq].
    { assumption. }
    
    

  - simpl. rewrite sumboolT by reflexivity. assumption.
  - destruct uv1; eauto using parred.
    simpl in *. inversion IHuv1.
    apply parred_beta_app; assumption.
  - destruct u; eauto using parred.
    destruct v; eauto using parred.
    simpl. destruct (term_eq_dec u v) as [<-|neq].
    + simpl in *. admit.
    + admit.
  (* - destruct uv; eauto using parred.
    simpl in *. inversion IHuv.
    eapply parred_beta_pi1; eassumption.
  - destruct uv; eauto using parred.
    simpl in *. inversion IHuv.
    eapply parred_beta_pi2; eassumption.
  - destruct uv2; eauto using parred.
    simpl in *. inversion IHuv2.
    eapply parred_beta_J; eassumption. *)
Admitted.

Lemma parred_diamond {u v w : term} (uv : u ⇒ v) (uw : u ⇒ w)
: exists t, v ⇒ t /\ w ⇒ t.
Proof.
  exists (parred_nf u).
  split; apply parred_strong_diamond; assumption.
Qed.



(* Lemma red1_wcr { u v w : term} (uv : u ▷ v) (uw : u ▷ w)
: exists x, v ▸ x /\ w ▸ x.
Proof.
  apply red1_parred in uv.
  apply red1_parred in uw.
  destruct (parred_diamond uv uw) as [x [vx wx]].
  exists x. split; apply parred_red; assumption.
Qed. *)

Lemma red1_wcr { u v w : term } (uv : u ▸ v) (uw : u ▸ w)
: exists x, v ▸ x /\ w ▸ x.
Proof.
  revert w uw. induction uv; intros w' uw. { exists w'. eauto using red. }
  induction uw. { exists w. eauto using red. }
  

  

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
    admit.
    (* destruct (red_cr vx vy) as [z [xz yz]].
    eapply red_conv; eapply red_trans; eassumption. *)
Admitted.

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
 *)
