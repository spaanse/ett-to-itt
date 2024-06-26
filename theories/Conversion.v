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
| parred_beta_app t t' u u' : t ⇒ (λ, t') -> u ⇒ u' -> t @ u ⇒ t'[u']
| parred_beta_pi1 p u v     : p ⇒ ⟨u, v⟩ -> π₁ p ⇒ u
| parred_beta_pi2 p u v     : p ⇒ ⟨u, v⟩ -> π₂ p ⇒ v
| parred_beta_J t t' x x'   : t ⇒ t' -> x ⇒ Refl(x') -> J(t, x) ⇒ t'[x']
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

Lemma lift_red1 {u v : term} {n k : nat}
: u ▷ v -> lift n k u ▷ lift n k v.
Proof.
  intros uv. revert n k. induction uv; intros m k;
  simpl; subst_helper; eauto using red1.
  - replace (lift m k t[u]) with (lift m (k+1) t)[lift m k u].
    apply red1_beta_app.
    replace k with (k + 0) by lia.
    rewrite lift_subst. f_equal; f_equal; f_equal; lia.
  - replace (lift m k t[x]) with (lift m (k+1) t)[lift m k x].
    apply red1_beta_J.
    replace k with (k + 0) by lia.
    rewrite lift_subst. f_equal; f_equal; f_equal; lia.
  - replace (skip (jump m) (k + 1) 0) with 0.
    replace (lift m (k + 1) (lift 1 0 f)) with (lift 1 0 (lift m k f)).
    apply red1_eta_lambda.
    + apply lift_lift'.
    + unfold skip, jump. comp_cases.
Qed.

Lemma red_prod_cong {A A' B B' : term} (AA' : A ▸ A') (BB' : B ▸ B')
: A ▸ A' -> B ▸ B' -> ∏ A, B ▸ ∏ A', B'.
Proof.
  induction AA'; eauto using red, red1.
  induction BB'; eauto using red, red1.
Qed.

Lemma red_lambda_cong {t t' : term} (tt' : t ▸ t')
: λ, t ▸ λ, t'.
Proof.
  induction tt'; eauto using red, red1.
Qed.

Lemma red_app_cong {u u' v v' : term} (uu' : u ▸ u') (vv' : v ▸ v')
: u @ v ▸ u' @ v'.
Proof.
  induction uu'; eauto using red, red1.
  induction vv'; eauto using red, red1.
Qed.

Lemma red_sum_cong {A A' B B' : term} (AA' : A ▸ A') (BB' : B ▸ B')
: ∑ A, B ▸ ∑ A', B'.
Proof.
  induction AA'; eauto using red, red1.
  induction BB'; eauto using red, red1.
Qed.

Lemma red_pair_cong {u u' v v' : term} (uu' : u ▸ u') (vv' : v ▸ v')
: ⟨u, v⟩ ▸ ⟨u', v'⟩.
Proof.
  induction uu'; eauto using red, red1.
  induction vv'; eauto using red, red1.
Qed.

Lemma red_pi1_cong {p p' : term} (pp' : p ▸ p')
: π₁ p ▸ π₁ p'.
Proof.
  induction pp'; eauto using red, red1.
Qed.

Lemma red_pi2_cong {p p' : term} (pp' : p ▸ p')
: π₂ p ▸ π₂ p'.
Proof.
  induction pp'; eauto using red, red1.
Qed.

Lemma red_eq_cong {u u' v v' : term} (uu' : u ▸ u') (vv' : v ▸ v')
: (u == v) ▸ (u' == v').
Proof.
  induction uu'; eauto using red, red1.
  induction vv'; eauto using red, red1.
Qed.

Lemma red_refl_cong {u u' : term} (uu' : u ▸ u')
: Refl(u) ▸ Refl(u').
Proof.
  induction uu'; eauto using red, red1.
Qed.

Lemma red_J_cong {t t' p p' : term} (tt' : t ▸ t') (pp' : p ▸ p')
: J(t,p) ▸ J(t',p').
Proof.
  induction tt'; eauto using red, red1.
  induction pp'; eauto using red, red1.
Qed.

Lemma red_tp_cong {p p' t t' : term} (pp' : p ▸ p') (tt' : t ▸ t')
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

Lemma lift_red {u v : term} {n k : nat} (uv : u ▸ v)
: lift n k u ▸ lift n k v.
Proof.
  induction uv; eauto using red.
  eauto using red_red1, lift_red1.
Qed.

Lemma subst_red {u u' v v' : term} {n : nat} (uu' : u ▸ u') (vv' : v ▸ v')
: v[n ← u] ▸ v'[n ← u'].
Proof.
  revert n u u' uu'. induction vv'; intros n x x' xx'.
  - revert n x x' xx'. induction u; intros m x x' xx'; simpl in *;
    eauto 10 using red with red_cong.
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

Lemma lift_parred {u v : term} {n k : nat}
: u ⇒ v -> lift n k u ⇒ lift n k v.
Proof.
  intros uv.
  revert n k. induction uv; intros m k;
  simpl; subst_helper; eauto using parred.
  - replace (lift m k t'[u']) with (lift m (k+1) t')[lift m k u'].
    { apply parred_beta_app; eauto.
      replace (λ, lift m (k + 1) t') with (lift m k (λ, t')). eauto.
      simpl. subst_helper. reflexivity. }
    replace k with (k + 0) by lia.
    rewrite lift_subst. f_equal; f_equal; f_equal; lia.
  - replace (lift m k t'[x']) with (lift m (k+1) t')[lift m k x'].
    { apply parred_beta_J; eauto. }
    replace k with (k + 0) by lia.
    rewrite lift_subst. f_equal; f_equal; f_equal; lia.
  - rewrite <- lift_lift'.
    replace (^(skip (jump m) (k + 1) 0)) with ^0.
    2: { unfold skip, jump. comp_cases. }
    apply parred_eta_lambda, IHuv.
Qed.

Lemma parred_identity {u : term}
: u ⇒ u.
Proof.
  induction u; eauto using parred.
Qed.

Lemma subst_parred {u u' v v' : term} {n : nat}
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
    
Lemma lift_red' {v w : term}  {n k : nat}
: (lift n k v ▷ lift n k w) -> v ▷ w.
Proof.
  revert n k w.
  induction v using term_strong_ind.
  intros n k w vw. inversion vw.
  - destruct v; try discriminate.
    destruct v1; try discriminate.
    simpl in H1. subst_helper.
    injection H1 as H1. subst.
    replace (k + 1) with (S k + 0) in * by lia.
    rewrite <- lift_subst in H2.
    replace (k + 0) with k in * by lia.
    apply lift_injective in H2. subst.
    eauto using red1.
  - destruct v; try discriminate.
    destruct v; try discriminate.
    simpl in H1.
    injection H1 as H1. subst.
    apply lift_injective in H0. subst.
    eauto using red1.
  - destruct v; try discriminate.
    destruct v; try discriminate.
    simpl in H1.
    injection H1 as H1. subst.
    apply lift_injective in H0. subst.
    eauto using red1.
  - destruct v; try discriminate.
    destruct v2; try discriminate.
    injection H1 as H1; subst; subst_helper.
    replace (k + 1) with (S k + 0) in * by lia.
    rewrite <- lift_subst in H2.
    replace (k + 0) with k in * by lia.
    apply lift_injective in H2. subst.
    eauto using red1.
  - destruct v; try discriminate.
    destruct v; try discriminate.
    destruct v2; try discriminate.
    destruct n0; try discriminate.
    2: { injection H1 as H1. revert H2. unfold skip, jump. comp_cases. }
    injection H1 as H1. subst_helper.
    subst.
    rewrite lift_lift' in H1.
    apply lift_injective in H1. subst.
    eauto using red1.
  - destruct v; try discriminate.
    destruct v1; try discriminate.
    destruct v2; try discriminate.
    injection H1 as H1; subst.
    apply lift_injective in H0.
    apply lift_injective in H2.
    subst.
    eauto using red1.
  - destruct v; try discriminate.
    destruct w; try discriminate.
    injection H0 as H0. subst_helper.
    injection H1 as H1; subst; subst_helper.
    apply lift_injective in H4; subst.
    apply H in H2. eauto using red1.
    subterm_solve.
  - destruct v, w; try discriminate.
    injection H0 as H0. injection H1 as H1. subst; subst_helper.
    apply lift_injective in H1; subst.
    apply H in H2. eauto using red1.
    subterm_solve.
  - destruct v, w; try discriminate.
    injection H0 as H0. injection H1 as H1. subst; subst_helper.
    apply H in H2. eauto using red1.
    subterm_solve.
  - destruct v, w; try discriminate.
    injection H0 as H0. injection H1 as H1. subst; subst_helper.
    apply lift_injective in H4. subst.
    apply H in H2. eauto using red1.
    subterm_solve.
  - destruct v, w; try discriminate.
    injection H0 as H0. injection H1 as H1. subst; subst_helper.
    apply lift_injective in H1. subst.
    apply H in H2. eauto using red1.
    subterm_solve.
  - destruct v, w; try discriminate.
    injection H0 as H0. injection H1 as H1. subst; subst_helper.
    apply lift_injective in H4. subst.
    apply H in H2. eauto using red1.
    subterm_solve.
  - destruct v, w; try discriminate.
    injection H0 as H0. injection H1 as H1. subst; subst_helper.
    apply lift_injective in H1. subst.
    apply H in H2. eauto using red1.
    subterm_solve.
  - destruct v, w; try discriminate.
    injection H0 as H0. injection H1 as H1. subst; subst_helper.
    apply lift_injective in H4. subst.
    apply H in H2. eauto using red1.
    subterm_solve.
  - destruct v, w; try discriminate.
    injection H0 as H0. injection H1 as H1. subst; subst_helper.
    apply lift_injective in H1. subst.
    apply H in H2. eauto using red1.
    subterm_solve.
  - destruct v, w; try discriminate.
    injection H0 as H0. injection H1 as H1. subst; subst_helper.
    apply H in H2. eauto using red1.
    subterm_solve.
  - destruct v, w; try discriminate.
    injection H0 as H0. injection H1 as H1. subst; subst_helper.
    apply H in H2. eauto using red1.
    subterm_solve.
  - destruct v, w; try discriminate.
    injection H0 as H0. injection H1 as H1. subst; subst_helper.
    apply lift_injective in H4. subst.
    apply H in H2. eauto using red1.
    subterm_solve.
  - destruct v, w; try discriminate.
    injection H0 as H0. injection H1 as H1. subst; subst_helper.
    apply lift_injective in H1. subst.
    apply H in H2. eauto using red1.
    subterm_solve.
  - destruct v, w; try discriminate.
    injection H0 as H0. injection H1 as H1. subst; subst_helper.
    apply H in H2. eauto using red1.
    subterm_solve.
  - destruct v, w; try discriminate.
    injection H0 as H0. injection H1 as H1. subst; subst_helper.
    apply lift_injective in H4. subst.
    apply H in H2. eauto using red1.
    subterm_solve.
  - destruct v, w; try discriminate.
    injection H0 as H0. injection H1 as H1. subst; subst_helper.
    apply lift_injective in H1. subst.
    apply H in H2. eauto using red1.
    subterm_solve.
  - destruct v,w; try discriminate.
    injection H0 as H0. injection H1 as H1. subst; subst_helper.
    apply lift_injective in H4. subst.
    apply H in H2. eauto using red1.
    subterm_solve.
  - destruct v, w; try discriminate.
    injection H0 as H0. injection H1 as H1. subst; subst_helper.
    apply lift_injective in H1. subst.
    apply H in H2. eauto using red1.
    subterm_solve.
Qed.

Lemma lift_unlift {u t : term} {n m k : nat}
: lift 1 k u = lift n (m + k + 1) t -> 
  lift 1 k (unlift 1 k t) = t.
Proof.
  revert u k. induction t; intros u k H;
  simpl; subst_helper; f_equal;
  destruct u; try discriminate;
  injection H as H; subst_helper; eauto;
  replace (m + k + 1 + 1) with (m + (k + 1) + 1) in * by lia;
  replace (m + (k + 1) + 1) with (m + k + 1 + 1) by lia; eauto.
  unfold skip, jump, unjump. comp_cases.
  revert H. unfold skip, jump. comp_cases.
Qed.

Lemma lift_eq {v w : term} {k i : nat}
: lift 1 i v = lift 1 (k + i + 1) w ->  lift 1 (k + i) (unlift 1 (k + i) v) = v.
Proof.
  revert k i w; induction v; intros k i w vw;
  simpl; subst_helper; f_equal;
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

Lemma lift_red1_lift {v w : term} {k : nat}
: (lift 1 k v) ▷ w -> exists w', w = lift 1 k w'.
Proof.
  revert k w. induction v;
  simpl; intros k w vw; inversion vw; subst_helper; subst.
  - destruct (IHv1 _ _ H2) as [x ->].
    exists (∏x, v2). simpl. subst_helper. reflexivity.
  - destruct (IHv2 _ _ H2) as [x ->].
    exists (∏v1, x). simpl. subst_helper. reflexivity.
  - destruct v; simpl in *; try discriminate; subst_helper.
    injection H0 as H0 H1.
    destruct v2; try discriminate.
    unfold skip, jump in H1. simpl in H1. injection H1 as H1.
    destruct (Nat.ltb n (k+1)); try lia. subst; simpl in *.
    exists (unlift 1 k w).
    symmetry. replace k with (k + 0) by lia. eapply lift_eq.
  replace (k+0) with k by lia. eassumption.
  - destruct (IHv _ _ H0) as [x ->].
    exists (λ, x). simpl. subst_helper. reflexivity.
  - destruct v1; try discriminate.
    simpl in *; subst_helper.
    injection H0 as H0. subst.
    replace (k + 1) with (S k + 0) by lia.
    rewrite <- lift_subst.
    replace (k+0) with k by lia. eauto.
  - destruct (IHv1 _ _ H2) as [x ->]. exists (x @ v2). eauto.
  - destruct (IHv2 _ _ H2) as [x ->]. exists (v1 @ x). eauto.
  - destruct (IHv1 _ _ H2) as [x ->].
    exists (∑x, v2). simpl. subst_helper. reflexivity.
  - destruct (IHv2 _ _ H2) as [x ->].
    exists (∑v1, x). simpl. subst_helper. reflexivity.
  - destruct v1; try discriminate.
    destruct v2; try discriminate.
    simpl in *; subst_helper.
    injection H0 as H0. injection H1 as H1. subst.
    exists v2. reflexivity.
  - destruct (IHv1 _ _ H2) as [x ->]. exists (⟨x, v2⟩). eauto.
  - destruct (IHv2 _ _ H2) as [x ->]. exists (⟨v1, x⟩). eauto.
  - destruct v; try discriminate.
    simpl in *; subst_helper.
    injection H0 as H0. subst. eauto.
  - destruct (IHv _ _ H0) as [x ->]. exists (π₁ x). eauto.
  - destruct v; try discriminate.
    simpl in *; subst_helper.
    injection H0 as H0. subst. eauto.
  - destruct (IHv _ _ H0) as [x ->]. exists (π₂ x). eauto.
  - destruct (IHv1 _ _ H2) as [x ->]. exists (x == v2). eauto.
  - destruct (IHv2 _ _ H2) as [x ->]. exists (v1 == x). eauto.
  - destruct (IHv _ _ H0) as [x ->]. exists (Refl(x)). eauto.
  - destruct v2; try discriminate.
    simpl in *; subst_helper.
    injection H1 as H1. subst.
    replace (k + 1) with (S k + 0) by lia.
    rewrite <- lift_subst.
    replace (k+0) with k by lia. eauto.
  - destruct (IHv1 _ _ H2) as [x ->]. exists (J(x,v2)).
    simpl. subst_helper. reflexivity.
  - destruct (IHv2 _ _ H2) as [x ->]. exists (J(v1,x)).
    simpl. subst_helper. reflexivity.
  - destruct (IHv1 _ _ H2) as [x ->]. exists (tTransport x v2). eauto.
  - destruct (IHv2 _ _ H2) as [x ->]. exists (tTransport v1 x). eauto.
Qed.

Lemma red_wcr {u v w : term}
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
    + destruct v; simpl in H0; try discriminate H0.
      injection H0 as H0. subst. subst_helper. replace (0 + 1) with 1 in * by lia.
      replace ((lift 1 1 v) [^0]) with v.
      exists (λ, v); eauto using red.
      rewrite lift_subst_rel0. reflexivity. exact 0.
    + destruct (lift_red1_lift H2) as [x ->].
      exists x. split; eauto using red, red1.
      eauto using lift_red', red.
    + inversion H2.
  - inversion H1; subst.
    + destruct w; try discriminate; simpl in H0.
      injection H0 as H0. subst. subst_helper. replace (0 + 1) with 1 in * by lia.
      replace ((lift 1 1 w) [^0]) with w.
      exists (λ, w); eauto using red.
      rewrite lift_subst_rel0. reflexivity. exact 0.
    + destruct (lift_red1_lift H3) as [x ->].
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

Lemma red1_parred {u v : term}
: u ▷ v -> u ⇒ v.
Proof.
  intro uv.
  induction uv; eauto using parred, parred_refl, parred_identity.
Qed.

Lemma parred_red {u v : term}
: u ⇒ v -> u ▸ v.
Proof.
  intro uv.
  induction uv; eauto 10 using red, red1, red_trans with red_cong.
Qed.

Lemma lift1_liftm {t u : term} {m k i : nat}
: lift 1 i t = lift m (k + 1 + i) u -> exists u', t = lift m (k+i) u'.
Proof.
  revert m k i u. induction t; intros m k i u tu;
  destruct u; try discriminate; simpl in *.
  - unfold skip, jump in *. simpl in *. injection tu as tu.
    destruct (n <? i) eqn: eq1;
    destruct (n0 <? k+1+i) eqn: eq2; comp_cases.
    + subst. exists (^n0). simpl. comp_cases.
    + exists ^n. simpl. comp_cases.
    + assert (n + 1 = n0 + m) by lia.
      exists ^(pred n0). simpl. comp_cases.
      f_equal. lia.
  - exists *s. simpl. reflexivity.
  - injection tu as tu1 tu2. subst_helper.
    apply IHt1 in tu1.
    replace (k + 1 + i + 1) with (k + 1 + (i + 1)) in * by lia. apply IHt2 in tu2.
    destruct tu1, tu2. subst. 
    exists (∏x, x0). simpl. subst_helper. f_equal. f_equal. f_equal. lia.
  - injection tu as tu. subst_helper.
    replace (k + 1 + i + 1) with (k + 1 + (i + 1)) in * by lia. apply IHt in tu.
    destruct tu. subst.
    exists (λ, x). simpl. subst_helper.
    f_equal. f_equal. f_equal. lia.
  - simpl in tu. injection tu as tu. subst_helper.
    apply IHt1 in tu. apply IHt2 in H. destruct tu, H. subst.
    exists (x @ x0). reflexivity.
  - simpl in tu. injection tu as tu. subst_helper.
    apply IHt1 in tu.
    replace (k + 1 + i + 1) with (k + 1 + (i + 1)) in * by lia. apply IHt2 in H.
    destruct tu, H. subst.
    exists (∑x, x0). simpl. subst_helper.
    f_equal. f_equal. f_equal. lia.
  - simpl in tu. injection tu as tu. subst_helper.
    apply IHt1 in tu. apply IHt2 in H. destruct tu, H. subst.
    exists (⟨x, x0⟩). reflexivity.
  - simpl in tu. injection tu as tu. subst_helper.
    apply IHt in tu. destruct tu. subst.
    exists (π₁ x). reflexivity.
  - simpl in tu. injection tu as tu. subst_helper.
    apply IHt in tu. destruct tu. subst.
    exists (π₂ x). reflexivity.
  - simpl in tu. injection tu as tu. subst_helper.
    apply IHt1 in tu. apply IHt2 in H. destruct tu, H. subst.
    exists (x == x0). reflexivity.
  - injection tu as tu.
    apply IHt in tu. destruct tu. subst.
    exists (Refl(x)). simpl. reflexivity.
  - simpl in tu. injection tu as tu. subst_helper.
    replace (k + 1 + i + 1) with (k + 1 + (i + 1)) in * by lia.
    apply IHt1 in tu. apply IHt2 in H. destruct tu, H. subst.
    exists (J(x, x0)). simpl. subst_helper.
    f_equal. f_equal. f_equal. lia.
  - simpl in tu. injection tu as tu. subst_helper.
    apply IHt1 in tu. apply IHt2 in H. destruct tu, H. subst.
    exists (tTransport x x0). reflexivity.
Qed.

Lemma lift_parred_lift {v w : term} {n k : nat}
: (lift n k v) ⇒ w -> exists w', w = lift n k w'.
Proof.
  revert n k w. induction v using term_strong_ind'. intros m k w vw.
  inversion vw; destruct  v; try discriminate; subst; eauto;
  simpl in *; simplify_eqs;
  repeat match goal with
  | |- subterm _ _ => progress subterm_solve
  | |- _ => progress subst
  | |- _ => progress subst_helper
  | |- _ => progress replace (k + 1) with (S k + 0) by lia
  | |- _ => progress rewrite <- lift_subst
  | |- _ => progress replace (k + 0) with k by lia
  | H : lift _ _ _ ⇒ _,
    IH : forall u, _ -> forall n k w, lift n k u ⇒ w -> _ |- _
    => apply IH in H
  | H : exists x, _ |- _ => destruct H
  | H : _ = lift _ _ ?x |- _ => destruct x; try discriminate; injection H as H
  end; eauto.
  - unfold skip, jump in H2. revert H2. comp_cases. intros <-.
    replace (k + 1) with (k + 1 + 0) in H0 by lia.
    destruct (lift1_liftm H0) as [x ->].
    rewrite lift_lift' in H0.
    replace (k + 0 + 1) with (k + 1 + 0) in H0 by lia.
    apply lift_injective in H0. subst.
    replace (k + 0) with k in H1 by lia.
    eapply H; try eassumption.
    simpl. rewrite clear_rel_lift. subterm_solve.
  - exists (∏x0, x). simpl. subst_helper. repeat f_equal. lia.
  - exists (λ,x). simpl. subst_helper. repeat f_equal. lia.
  - exists (x0 @ x). reflexivity.
  - exists (∑x0, x). simpl. subst_helper. repeat f_equal. lia.
  - exists (⟨x0, x⟩). reflexivity.
  - exists (π₁ x). reflexivity.
  - exists (π₂ x). reflexivity.
  - exists (x0 == x). reflexivity.
  - exists (Refl(x)). reflexivity.
  - exists (J(x0, x)). simpl. subst_helper. repeat f_equal. lia.
  - exists (tTransport x0 x). reflexivity.
Qed.

Lemma lift_parred' {v w : term} {n k : nat}
: lift n k v ⇒ lift n k w -> v ⇒ w.
Proof.
  revert n k w. induction v using term_strong_ind'; intros m k w vw;
  simpl in *; inversion vw; subst.
  - destruct v, w; try discriminate.
    unfold skip, jump in *. simpl in *.
    destruct (n0 <? k) eqn: eq1, (n1 <? k) eqn: eq2; comp_cases.
    + injection H1 as H1. injection H2 as H2. subst.
      apply parred_rel.
    + injection H1 as H1. injection H2 as H2. lia.
    + injection H1 as H1. injection H2 as H2. lia.
    + injection H1 as H1. injection H2 as H2. subst.
      assert (n0 = n1) by lia. subst. apply parred_rel.
  - destruct v, w; try discriminate.
    simpl in *. assumption.
  - destruct v; try discriminate.
    injection H0 as H0; subst. subst_helper.
    destruct (lift_parred_lift H2) as [x xw].
    destruct (lift_parred_lift H3) as [y ->].
    destruct x; try discriminate. injection xw as xw.
    subst. subst_helper.
    replace (λ, lift m (k + 1) x) with (lift m k (λ,x)) in H2.
    2: { simpl. subst_helper. reflexivity. }
    apply H in H2. 2: { subterm_solve. }
    apply H in H3. 2: { subterm_solve. }
    replace (k + 1) with (S k + 0) in H1 by lia.
    rewrite <- lift_subst in H1.
    replace (k + 0) with k in H1 by lia.
    apply lift_injective in H1. subst.
    eauto using parred.
  - destruct v; try discriminate.
    injection H0 as H0. subst.
    destruct (lift_parred_lift H1) as [x px].
    destruct x; try discriminate. injection px as px. subst.
    replace (⟨lift m k w, lift m k x2⟩) with (lift m k ⟨w, x2⟩) in H1 by reflexivity.
    apply H in H1. 2: { subterm_solve. }
    eauto using parred, parred_identity.
  - destruct v; try discriminate.
    injection H0 as H0. subst.
    destruct (lift_parred_lift H1) as [x px].
    destruct x; try discriminate. injection px as px. subst.
    replace (⟨lift m k x1, lift m k w⟩) with (lift m k ⟨x1, w⟩) in H1 by reflexivity.
    apply H in H1. 2: { subterm_solve. }
    eauto using parred, parred_identity.
  - destruct v; try discriminate.
    injection H0 as H0. subst. subst_helper.    
    destruct (lift_parred_lift H2) as [x ->].
    destruct (lift_parred_lift H3) as [y x'y].
    destruct y; try discriminate. injection x'y as x'y. subst.
    replace (Refl(lift m k y)) with (lift m k Refl(y)) in H3 by reflexivity.
    apply H in H2. 2: { subterm_solve. }
    apply H in H3. 2: { subterm_solve. }
    replace (k + 1) with (S k + 0) in H1 by lia.
    rewrite <- lift_subst in H1.
    replace (k + 0) with k in H1 by lia.
    apply lift_injective in H1. subst.
    eauto using parred.
  - destruct v; try discriminate.
    destruct v; try discriminate.
    destruct v2; try discriminate.
    injection H0 as H0. subst. subst_helper.
    revert H2. unfold skip, jump. comp_cases. intros <-.
    replace (k + 1) with (k + 1 + 0) in H0 by lia.
    destruct (lift1_liftm H0) as [? ->].
    replace (k + 0) with k in * by lia.
    replace (k + 1 + 0) with (k + 1) in * by lia.
    rewrite lift_lift' in H0.
    apply lift_injective in H0. subst.
    apply H in H1. 2: { simpl. rewrite clear_rel_lift. subterm_solve. }
    eauto using parred.
  - destruct v; try discriminate.
    destruct v1; try discriminate.
    destruct v2; try discriminate.
    injection H0 as H0. subst.
    apply H in H1. 2: { subterm_solve. }
    apply H in H2. 2: { subterm_solve. }
    eauto using parred.
  - destruct v, w; try discriminate.
    injection H0 as H0. injection H1 as H1. subst. subst_helper.
    apply H in H2. 2: { subterm_solve. }
    apply H in H3. 2: { subterm_solve. }
    eauto using parred.
  - destruct v, w; try discriminate.
    injection H0 as H0. injection H1 as H1. subst. subst_helper.
    apply H in H2. 2: { subterm_solve. }
    eauto using parred.
  - destruct v, w; try discriminate.
    injection H0 as H0. injection H1 as H1. subst. subst_helper.
    apply H in H2. 2: { subterm_solve. }
    apply H in H3. 2: { subterm_solve. }
    eauto using parred.
  - destruct v, w; try discriminate.
    injection H0 as H0. injection H1 as H1. subst. subst_helper.
    apply H in H2. 2: { subterm_solve. }
    apply H in H3. 2: { subterm_solve. }
    eauto using parred.
  - destruct v, w; try discriminate.
    injection H0 as H0. injection H1 as H1. subst. subst_helper.
    apply H in H2. 2: { subterm_solve. }
    apply H in H3. 2: { subterm_solve. }
    eauto using parred.
  - destruct v, w; try discriminate.
    injection H0 as H0. injection H1 as H1. subst. subst_helper.
    apply H in H2. 2: { subterm_solve. }
    eauto using parred.
  - destruct v, w; try discriminate.
    injection H0 as H0. injection H1 as H1. subst. subst_helper.
    apply H in H2. 2: { subterm_solve. }
    eauto using parred.
  - destruct v, w; try discriminate.
    injection H0 as H0. injection H1 as H1. subst. subst_helper.
    apply H in H2. 2: { subterm_solve. }
    apply H in H3. 2: { subterm_solve. }
    eauto using parred.
  - destruct v, w; try discriminate.
    injection H0 as H0. injection H1 as H1. subst. subst_helper.
    apply H in H2. 2: { subterm_solve. }
    eauto using parred.
  - destruct v, w; try discriminate.
    injection H0 as H0. injection H1 as H1. subst. subst_helper.
    apply H in H2. 2: { subterm_solve. }
    apply H in H3. 2: { subterm_solve. }
    eauto using parred.
  - destruct v, w; try discriminate.
    injection H0 as H0. injection H1 as H1. subst. subst_helper.
    apply H in H2. 2: { subterm_solve. }
    apply H in H3. 2: { subterm_solve. }
    eauto using parred.
Qed.

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

Lemma parred_dp_pair {u v w u' v' : term}
: (forall y : term,
    subterm (clear_rel y) ⟨π₁ (clear_rel u), π₂ (clear_rel v)⟩ ->
    forall u v : term, y ⇒ u -> y ⇒ v -> exists x : term, u⇒ x /\ v⇒ x)
  -> u ⇒ w -> v ⇒ w -> π₁ u ⇒ u' -> π₂ v ⇒ v'
  -> exists x, w ⇒ x /\ ⟨u', v'⟩ ⇒ x.
Admitted.

Lemma parred_dp {u v w : term}
: u ⇒ v -> u ⇒ w -> exists x, v ⇒ x /\ w ⇒ x.
Proof.
  revert v w.
  induction u using term_strong_ind'.
  intros v w uv uw.
  destruct u; inversion uv; inversion uw; subst;
  simplify_eqs;
  repeat match goal with
  | H : lift ?n ?k ?v = lift ?n ?k ?w |- _ => apply lift_injective in H
  | |- exists x, ?u ▸ x /\ ?u ▸ x => ( exists u; split; apply red_refl )
  end; simpl in *;
  repeat match goal with
  | IH : forall u, subterm (clear_rel u) ?y -> forall v w, u ⇒ v -> u ⇒ w -> _,
    H1 : ?x ⇒ ?w1,
    H2 : ?x ⇒ ?w2 |- _ =>
      lazymatch goal with
      | H : exists z, w1 ⇒ z /\ w2 ⇒ z |- _ => fail
      | H : exists z, w2 ⇒ z /\ w1 ⇒ z |- _ => fail
      | |- _ =>
        assert (st : subterm (clear_rel x) y) by subterm_solve;
        assert (exists z, w1 ⇒ z /\ w2 ⇒ z) by eauto;
        clear st
      end
  end;
  repeat match goal with
  | H : exists z, _ /\ _ |- _ => destruct H as [? [? ?]]
  end;
  eauto 10 using parred, subst_parred.
  - subst. eapply H; try eassumption.
    rewrite clear_rel_lift. subterm_solve.
  - inversion H4; clear H4; subst.
    + inversion H6. clear H6. subst.
      destruct (lift_parred_lift H3) as [x t'x].
      destruct x; try discriminate. injection t'x as t'x. subst. subst_helper.
      simpl. rewrite lift_subst_rel.
      replace (λ, lift 1 (0 + 1) x) with (lift 1 0 (λ, x)) in H3.
      2: { simpl. subst_helper. f_equal. }
      apply lift_parred' in H3.
      eapply H; try eassumption.
      rewrite clear_rel_lift. subterm_solve.
    + inversion H6. clear H6. subst.
      destruct (lift_parred_lift H3) as [x ->].
      apply lift_parred' in H3.
      rewrite clear_rel_lift in H.
      assert (st : subterm (clear_rel f) (λ, clear_rel f @ ^0)) by subterm_solve.
      destruct (H _ st _ _ H1 H3) as [y [vy xy]].
      eauto using parred.
  - inversion H1; subst.
    + inversion H6. clear H6. subst.
      destruct (lift_parred_lift H3) as [x t'x].
      destruct x; try discriminate. injection t'x as t'x. subst. subst_helper.
      simpl. rewrite lift_subst_rel.
      replace (λ, lift 1 (0 + 1) x) with (lift 1 0 (λ, x)) in H3.
      2: { simpl. subst_helper. f_equal. }
      apply lift_parred' in H3.
      eapply H; try eassumption.
      rewrite clear_rel_lift. subterm_solve.
    + inversion H6. subst.
      destruct (lift_parred_lift H3) as [x ->].
      apply lift_parred' in H3.
      rewrite clear_rel_lift in H.
      assert (st : subterm (clear_rel f) (λ, clear_rel f @ ^0)) by subterm_solve.
      destruct (H _ st _ _ H4 H3) as [y [vy xy]].
      eauto using parred.
  - clear H4 H9.
    inversion H1; inversion H3; subst.
    + simpl. repeat rewrite subst_lift by lia. repeat rewrite lift0k.
      eauto using parred.
    + simpl. repeat rewrite subst_lift by lia. repeat rewrite lift0k.
      eauto using parred, subst_parred.
    + simpl. repeat rewrite subst_lift by lia. repeat rewrite lift0k.
      eauto using parred, subst_parred.
    + injection H11 as ->. eauto using parred, subst_parred.
  - inversion H1; subst.
    + simpl. repeat rewrite subst_lift by lia. repeat rewrite lift0k.
      eauto using parred.
    + eauto using parred, subst_parred.
  - inversion H3; subst.
    + simpl. repeat rewrite subst_lift by lia. repeat rewrite lift0k.
    eauto using parred.
    + eauto using parred, subst_parred.
  - eapply parred_dp_pair; eassumption.
  - enough (flipped : exists x, w ⇒ x /\ ⟨u', v'⟩ ⇒ x).
    { destruct flipped as [x [wx px]]. eauto. }
    eapply parred_dp_pair; eassumption.
  - inversion H0; inversion H2; subst; eauto using parred.
    inversion H12. subst. eauto using parred.
  - inversion H0; subst; eauto using parred.
  - inversion H2; inversion H2; subst; eauto using parred.
  - inversion H0; inversion H2; subst; eauto using parred.
    inversion H12. subst. eauto using parred.
  - inversion H0; subst; eauto using parred.
  - inversion H2; inversion H2; subst; eauto using parred.
  - inversion H0; inversion H5; subst.
    inversion H13. subst. eauto using parred, subst_parred.
  - inversion H0; subst.
    eauto using parred, subst_parred.
  - inversion H5; subst.
    eauto using parred, subst_parred.
Qed.

Lemma red_parred_diamond { u v w : term } (uv : u ▸ v) (uw : u ⇒ w)
: exists x, v ▸ x /\ w ▸ x.
Proof.
  revert w uw. induction uv; eauto using red, parred_red.
  intros w' uw.
  apply red1_parred in H.
  destruct (parred_dp  H uw) as [x [vx w'x]].
  destruct (IHuv _ vx) as [y [wy w'y]].
  apply parred_red in w'x.
  exists y. split; eauto using red, red_trans.
Qed.

Lemma red_cr { u v w : term } (uv : u ▸ v) (uw : u ▸ w)
: exists x, v ▸ x /\ w ▸ x.
Proof.
  revert w uw. induction uv; eauto using red.
  intros w' uw.
  apply red1_parred in H.
  destruct (red_parred_diamond uw H) as [x [w'x vx]].
  destruct (IHuv _ vx) as [y [wy w'y]].
  eauto using red_trans.
Qed.

Lemma conv_sym {u v : term}
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

Lemma conv_trans {u v w : term}
: u ≡ v -> v ≡ w -> u ≡ w.
Proof.
    intros uv vw.
    destruct (conv_red uv) as [x [ux vx]].
    destruct (conv_red vw) as [y [vy wy]].
    destruct (red_cr vx vy) as [z [xz yz]].
    eauto using red_conv, red_trans.
Qed.