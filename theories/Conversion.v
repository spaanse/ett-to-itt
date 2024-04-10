Require Import Ast Subst Tactics Lia.

Reserved Notation "a '▷' b" (at level 50, format "'[' a '/' '▷' '/'  b ']'").
Reserved Notation "a '▸' b" (at level 50, format "'[' a '/' '▸' '/'  b ']'").
Reserved Notation "a '≡' b" (at level 50, format "'[' a '/' '≡' '/'  b ']'").
Reserved Notation "a '⇒' b" (at level 50, format "'[' a '/' '⇒' '/'  b ']'").

Open Scope t_scope.
Section Conversion.
Declare Scope r_scope.


Inductive red1 : term -> term -> Prop :=
| red1_beta_app u t
: (λ,t) @ u ▷ (subst u 0 t)

| red1_beta_pi1 u v
: π₁ ⟨u, v⟩ ▷ u

| red1_beta_pi2 u v
: π₂ ⟨u, v⟩ ▷ v

| red1_eta_lambda f
: λ,(lift 1 0 f) @ ^0 ▷ f

| red1_eta_pair p
: ⟨π₁ p,π₂ p⟩ ▷ p

| red1_prod_cong1 A A' B
: A ▷ A' ->
  ∏ A, B ▷ ∏ A', B

| red1_prod_cong2 A B B'
: B ▷ B' ->
  ∏ A, B ▷ ∏ A, B'

| red1_lambda_cong t t'
: t ▷ t' ->
  λ, t ▷ λ, t'

| red1_app_cong1 u u' v
: u ▷ u' ->
  u @ v ▷ u' @ v

| red1_app_cong2 u v v'
: v ▷ v' ->
  u @ v ▷ u @ v'

| red1_sum_cong1 A A' B
: A ▷ A' ->
  ∑ A, B ▷ ∑ A', B

| red1_sum_cong2 A B B'
: B ▷ B' ->
  ∑ A, B ▷ ∑ A, B'

| red1_pair_cong1 u u' v
: u ▷ u' ->
  ⟨u, v⟩ ▷ ⟨u', v⟩

| red1_pair_cong2 u v v'
: v ▷ v' ->
  ⟨u, v⟩ ▷ ⟨u, v'⟩

| red1_pi1_cong p p'
: p ▷ p' ->
  π₁ p ▷ π₁ p'

| red1_pi2_cong p p'
: p ▷ p' ->
  π₂ p ▷ π₂ p'

where "a '▷' b" := (red1 a b) : r_scope.

Inductive red : term -> term -> Prop :=
| red_refl u
: u ▸ u
| red_red1 u v w
: u ▷ v ->
  v ▸ w ->
  u ▸ w
where "a '▸' b" := (red a b) : r_scope.

Inductive conv : term -> term -> Prop :=
| conv_refl u      : u ≡ u
| conv_red_l u v w : u ▷ v -> v ≡ w -> u ≡ w
| conv_red_r u v w : w ▷ v -> u ≡ v -> u ≡ w
where "a '≡' b" := (conv a b) : r_scope.

Inductive parred : term -> term -> Prop :=
| parred_rel n
: ^n ⇒ ^n
| parred_sort s
: *s ⇒ *s
| parred_beta_app t t' u u'
: t ⇒ t' -> u ⇒ u' -> (λ,t) @ u ⇒ (subst u' 0 t')
| parred_beta_pi1 u u' v v'
: u ⇒ u' -> v ⇒ v' -> π₁ ⟨u, v⟩ ⇒ u'
| parred_beta_pi2 u u' v v'
: u ⇒ u' -> v ⇒ v' -> π₂ ⟨u, v⟩ ⇒ v'
(* | parred_eta_lambda f f'
: f ⇒ f' -> (λ, (lift 1 0 f) @ ^0) ⇒ f'
| parred_eta_pair p p'
: p ⇒ p' -> ⟨π₁ p,π₂ p⟩ ⇒ p' *)
| parred_prod A A' B B'
: A ⇒ A' -> B ⇒ B' -> ∏ A, B ⇒ ∏ A', B'
| parred_lambda t t'
: t ⇒ t' -> λ, t ⇒ λ, t'
| parred_app u u' v v'
: u ⇒ u' -> v ⇒ v' -> u @ v ⇒ u' @ v'
| parred_sum A A' B B'
: A ⇒ A' -> B ⇒ B' -> ∑ A, B ⇒ ∑ A', B'
| parred_pair u u' v v'
: u ⇒ u' -> v ⇒ v' -> ⟨u, v⟩ ⇒ ⟨u', v'⟩
| parred_pi1 p p'
: p ⇒ p' -> π₁ p ⇒ π₁ p'
| parred_pi2 p p'
: p ⇒ p' -> π₂ p ⇒ π₂ p'
where "a '⇒' b" := (parred a b) : r_scope.

Fixpoint parred_nf (t : term) : term :=
match t with
| ^n => ^n
| *s => *s
| ∏A, B => ∏ parred_nf A, parred_nf B
(* | λ, f @ ^0 => parred_nf f *)
| λ, t => λ, parred_nf t
| (λ, f) @ v => subst (parred_nf v) 0 (parred_nf f)
| u @ v => parred_nf u @ parred_nf v
| ∑ A, B => ∑ parred_nf A, parred_nf B
(* TODO: missing pattern for pair_eta *)
| ⟨u, v⟩ => (tPair (parred_nf u) (parred_nf v))
| π₁ ⟨u,v⟩ => parred_nf u
| π₁ p => π₁ (parred_nf p)
| π₂ ⟨u,v⟩ => parred_nf v
| π₂ p => π₂ (parred_nf p)
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
  - replace (lift m k (subst u 0 t)) with (subst (lift m k u) 0 (lift m (k+1) t)).
    apply red1_beta_app.
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
: subst u n v ▸ subst u' n v'.
Proof.
  revert n u u' uu'. induction vv'; intros n x x' xx'.
  - revert n x x' xx'. induction u; intros m x x' xx'; simpl in *.
    + comp_cases; eauto using red.
      apply lift_red. assumption.
    + apply red_refl.
    + apply red_prod_cong; eauto.
    + apply red_lambda_cong; eauto.
    + apply red_app_cong; eauto.
    + apply red_sum_cong; eauto.
    + apply red_pair_cong; eauto.
    + apply red_pi1_cong; eauto.
    + apply red_pi2_cong; eauto.
  - eapply red_trans; [|apply IHvv'; eassumption].
    clear IHvv' x' xx' vv'.
    revert n. induction H; intros n; simpl in *.
    + eapply red_red1. apply red1_beta_app.
      replace (S n) with (S n + 0) by lia.
      replace n with (n + 0) by lia.
      rewrite subst_subst.
      replace (n + 0 + 0) with (n + 0) by lia.
      apply red_refl.
    + eapply red_red1. apply red1_beta_pi1.
      apply red_refl.
    + eapply red_red1. apply red1_beta_pi2.
      apply red_refl.
    + replace (subst x (S n) (lift 1 0 f)) with (lift 1 0 (subst x n f)).
      eapply red_red1. apply red1_eta_lambda. apply red_refl.
      replace n with (n + 0) by lia.
      rewrite lift_subst'.
      f_equal. lia.
    + eapply red_red1. apply red1_eta_pair. apply red_refl.
    + apply red_prod_cong; eauto using red.
    + apply red_prod_cong; eauto using red.
    + apply red_lambda_cong; eauto using red.
    + apply red_app_cong; eauto using red.
    + apply red_app_cong; eauto using red.
    + apply red_sum_cong; eauto using red.
    + apply red_sum_cong; eauto using red.
    + apply red_pair_cong; eauto using red.
    + apply red_pair_cong; eauto using red.
    + apply red_pi1_cong; eauto using red.
    + apply red_pi2_cong; eauto using red.
Qed.

Lemma lift_parred (u v : term) (n k : nat)
: u ⇒ v -> lift n k u ⇒ lift n k v.
Proof.
  intros uv.
  revert n k. induction uv; intros m k;
  unfold lift; simpl; subst_helper; eauto using parred.
  replace (lift m k (subst u' 0 t')) with (subst (lift m k u') 0 (lift m (k+1) t')).
  apply parred_beta_app; [apply IHuv1 | apply IHuv2].
  replace k with (k + 0) by lia.
  rewrite lift_subst. f_equal; f_equal; lia.
Qed.

Lemma subst_parred (u u' v v' : term) (n : nat)
: u ⇒ u' -> v ⇒ v' -> subst u n v ⇒ subst u' n v'.
Proof.
  intros uu' vv'.
  revert n. induction vv'; intros m; simpl in *; eauto using parred.
  - comp_cases; eauto using parred.
    apply lift_parred. assumption.
  - replace (subst u' m (subst u'0 0 t')) with (subst (subst u' m u'0) 0 (subst u' (S m) t')).
    apply parred_beta_app; [apply IHvv'1 | apply IHvv'2].
    (* subst (subst u m v) k (subst u (S m + k) t) = subst u (m + k) (subst v k t). *)
    replace (S m) with (S m + 0) by lia.
    rewrite subst_subst.
    f_equal. lia.
Qed.

Lemma parred_strong_diamond (u : term)
: forall v : term, u ⇒ v -> v ⇒ (parred_nf u).
Proof.
    intros v uv.
    induction uv; eauto using parred.
    - simpl. apply subst_parred; assumption.
    - destruct uv1; eauto using parred.
      simpl in *. inversion IHuv1.
      apply parred_beta_app; assumption.
    - destruct uv; eauto using parred.
      simpl in *. inversion IHuv.
      eapply parred_beta_pi1; eassumption.
    - destruct uv; eauto using parred.
      simpl in *. inversion IHuv.
      eapply parred_beta_pi2; eassumption.
Qed.

Lemma parred_diamond {u v w : term} (uv : u ⇒ v) (uw : u ⇒ w)
: exists t, v ⇒ t /\ w ⇒ t.
Proof.
  exists (parred_nf u).
  split; apply parred_strong_diamond; assumption.
Qed.

Lemma parred_refl u
: u ⇒ u.
Proof.
  induction u; eauto using parred.
Qed.

Lemma red1_parred u v
: u ▷ v -> u ⇒ v.
Proof.
  intro uv.
  induction uv; eauto using parred, parred_refl.
  - admit.
  - admit.
Admitted.

Lemma parred_red u v
: u ⇒ v -> u ▸ v.
Proof.
  intro uv.
  induction uv; eauto using red, red1.
  - eapply red_red1. apply red1_beta_app.
    apply subst_red; assumption.
  - apply red_prod_cong; assumption.
  - apply red_lambda_cong; assumption.
  - apply red_app_cong; assumption.
  - apply red_sum_cong; assumption.
  - apply red_pair_cong; assumption.
  - apply red_pi1_cong; assumption.
  - apply red_pi2_cong; assumption.
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