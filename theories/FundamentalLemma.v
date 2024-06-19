From Coq Require Import Lia Nat List Arith.PeanoNat Logic.FunctionalExtensionality.
Require Import Ast Subst Conversion SafeNth ITT Decorates Tactics.
Open Scope t_scope.
Open Scope subst_scope.
Open Scope i_scope.

(* Notation "x '[' T '≅' U ']' y" := (∑ (T == U), tTransport ^0 (lift 1 0 x) == (lift 1 0 y)) (at level 12, only parsing) : t_scope. *)
Definition Heq T U x y := ∑ (T == U), tTransport ^0 (lift 1 0 x) == (lift 1 0 y).
Definition Pack A B := ∑ A, ∑ (lift 1 0 B), Heq (lift 2 0 A) (lift 2 0 B) ^1 ^0.
Definition Proj₁ p := π₁ p.
Definition Proj₂ p := π₁ π₂ p.
Definition Projₑ p := π₂ π₂ p.

Fixpoint Proj1N (n k : nat) (t : term) : term :=
match t with
  | ^i =>
      match (i <? k) with
      | true => ^i
      | false => match (i <? n+k) with
        | true => Proj₁ ^i
        | false => ^i
        end
      end
  | *s => *s
  | λ, M => λ, Proj1N n (S k) M
  | u @ v => (Proj1N n k u) @ (Proj1N n k v)
  | ∏A, B => ∏(Proj1N n k A), (Proj1N n (S k) B)
  | ∑A, B => ∑(Proj1N n k A), (Proj1N n (S k) B)
  | ⟨u, v⟩ => ⟨(Proj1N n k u), (Proj1N n k v)⟩
  | π₁ p => π₁ (Proj1N n k p)
  | π₂ p => π₂ (Proj1N n k p)
  | u == v => (Proj1N n k u) == (Proj1N n k v)
  | Refl(u) => Refl(Proj1N n k u)
  | J(u, p) => J(Proj1N n (S k) u, Proj1N n k p)

  | tTransport p u => tTransport (Proj1N n k p) (Proj1N n k u)
end.

Lemma proj1N_0k k t
: Proj1N 0 k t = t.
Proof.
  revert k; induction t; intros k; simpl; f_equal; eauto.
  comp_cases.
Qed.

Lemma proj1N_Sn n k t
: Proj1N (S n) k t = Proj1N n k ((lift 1 (S (n + k)) t)[n+k ← Proj₁ ^0]).
Proof.
  revert k; induction t; intros k; simpl; f_equal; eauto.
  - unfold lift, skip, jump; simpl. comp_cases.
    + induction n; simpl; comp_cases.
    + unfold lift, skip, jump; simpl; comp_cases.
      unfold Proj₁. f_equal. f_equal. lia.
    + induction n; simpl; comp_cases.
    + replace (pred (n0 - S (n + k) + 1 + S (n + k))) with n0 by lia.
      induction n; simpl; comp_cases.
  - rewrite IHt2. unfold lift, skip, jump.
    f_equal. f_equal; f_equal; try lia.
    apply functional_extensionality. intro i;
    comp_cases.
  - rewrite IHt. unfold lift, skip, jump.
    f_equal. f_equal; f_equal; try lia.
    apply functional_extensionality. intro i;
    comp_cases.
  - rewrite IHt2. unfold lift, skip, jump.
    f_equal. f_equal; f_equal; try lia.
    apply functional_extensionality. intro i;
    comp_cases.
  - rewrite IHt1. unfold lift, skip, jump.
    f_equal. f_equal; f_equal; try lia.
    apply functional_extensionality. intro i;
    comp_cases.
Qed.

Fixpoint Proj2N (n k : nat) (t : term) : term :=
match t with
  | ^i =>
      match (i <? k) with
      | true => ^i
      | false => match (i <? n+k) with
        | true => Proj₂ ^i
        | false => ^i
        end
      end
  | *s => *s
  | λ, M => λ, Proj2N n (S k) M
  | u @ v => (Proj2N n k u) @ (Proj2N n k v)
  | ∏A, B => ∏(Proj2N n k A), (Proj2N n (S k) B)
  | ∑A, B => ∑(Proj2N n k A), (Proj2N n (S k) B)
  | ⟨u, v⟩ => ⟨(Proj2N n k u), (Proj2N n k v)⟩
  | π₁ p => π₁ (Proj2N n k p)
  | π₂ p => π₂ (Proj2N n k p)
  | u == v => (Proj2N n k u) == (Proj2N n k v)
  | Refl(u) => Refl(Proj2N n k u)
  | J(u, p) => J(Proj2N n (S k) u, Proj2N n k p)

  | tTransport p u => tTransport (Proj2N n k p) (Proj2N n k u)
end.

Lemma proj2N_0k k t
: Proj2N 0 k t = t.
Proof.
  revert k; induction t; intros k; simpl; f_equal; eauto.
  comp_cases.
Qed.

Lemma proj2N_Sn n k t
: Proj2N (S n) k t = Proj2N n k ((lift 1 (S (n + k)) t)[n+k ← Proj₂ ^0]).
Proof.
  revert k; induction t; intros k; simpl; f_equal; eauto.
  - unfold lift, skip, jump; simpl. comp_cases.
    + induction n; simpl; comp_cases.
    + unfold lift, skip, jump; simpl; comp_cases.
      unfold Proj₂. f_equal. f_equal. f_equal. lia.
    + induction n; simpl; comp_cases.
    + replace (pred (n0 - S (n + k) + 1 + S (n + k))) with n0 by lia.
      induction n; simpl; comp_cases.
  - rewrite IHt2. unfold lift, skip, jump.
    f_equal. f_equal; f_equal; try lia.
    apply functional_extensionality. intro i;
    comp_cases.
  - rewrite IHt. unfold lift, skip, jump.
    f_equal. f_equal; f_equal; try lia.
    apply functional_extensionality. intro i;
    comp_cases.
  - rewrite IHt2. unfold lift, skip, jump.
    f_equal. f_equal; f_equal; try lia.
    apply functional_extensionality. intro i;
    comp_cases.
  - rewrite IHt1. unfold lift, skip, jump.
    f_equal. f_equal; f_equal; try lia.
    apply functional_extensionality. intro i;
    comp_cases.
Qed.

Program Fixpoint PackContext (n : nat) (Γ Δ : context) (eqΓ : length Γ = n) (eqΔ : length Δ = n) : context :=
match n, Γ, Δ with
| S n', (Γ',,A), (Δ',,B) => (PackContext n' Γ' Δ' _ _) ,, Pack (Proj1N n' 0 A) (Proj2N n' 0 B)
| O   , nil    , nil     => nil
| _   , _      , _       => _
end.
Obligation Tactic := split; intros; intros (? & ? & ?); try discriminate.
Solve All Obligations.

Lemma PackContext_proof_irrelevant (n : nat) (Γ Δ : context) (eqΓ1 eqΓ2 : length Γ = n) (eqΔ1 eqΔ2 : length Δ = n)
: PackContext n Γ Δ eqΓ1 eqΔ1 = PackContext n Γ Δ eqΓ2 eqΔ2.
Proof.
  revert Γ Δ eqΓ1 eqΓ2 eqΔ1 eqΔ2.
  induction n;
  intros Γ Δ eqΓ1 eqΓ2 eqΔ1 eqΔ2;
  destruct Γ, Δ; try discriminate.
  - reflexivity.
  - simpl. f_equal. apply IHn.
Qed.

Lemma PackContext_length (n : nat) (Γ Δ : context) (eqΓ : length Γ = n) (eqΔ : length Δ = n)
: length (PackContext n Γ Δ eqΓ eqΔ) = n.
Proof.
  revert Γ Δ eqΓ eqΔ. induction n; intros Γ Δ eqΓ eqΔ;
  destruct Γ, Δ; try discriminate.
  - reflexivity.
  - simpl. erewrite PackContext_proof_irrelevant.
    f_equal. apply IHn.
    Unshelve.
    simpl in eqΓ. lia.
    simpl in eqΔ. lia.
Qed.

Fixpoint Proj1Nc (n k : nat) (l : list term) : list term :=
match l with
  | nil => nil
  | x :: xs => (Proj1N n (k + length xs) x) :: (Proj1Nc n k xs)
end.

Lemma Proj1Nc_0k (k : nat) (l : list term)
: Proj1Nc 0 k l = l.
Proof.
  induction l; simpl. { reflexivity. }
  rewrite IHl, proj1N_0k. reflexivity.
Qed.

Lemma Proj1Nc_length (n k : nat) (l : list term)
: length (Proj1Nc n k l) = length l.
Proof.
  induction l; simpl; lia.
Qed.

Lemma Proj1Nc_nth (n m k : nat) (l : list term) (len : n < length (Proj1Nc m k l)) (len2 : n < length l)
: safe_nth n (Proj1Nc m k l) len = Proj1N m (k + length l - n - 1) (safe_nth n l len2).
Proof.
  revert n m k len len2.
  induction l; intros n m k len len2;
  simpl in *; try lia.
  destruct n; simpl in *. { f_equal. lia. }
  erewrite IHl. f_equal. lia.
Qed.

Fixpoint Proj2Nc (n k : nat) (l : list term) : list term :=
match l with
  | nil => nil
  | x :: xs => (Proj2N n (k + length xs) x) :: (Proj2Nc n k xs)
end.

Lemma Proj2Nc_0k (k : nat) (l : list term)
: Proj2Nc 0 k l = l.
Proof.
  induction l; simpl. { reflexivity. }
  rewrite IHl, proj2N_0k. reflexivity.
Qed.

Lemma Proj2Nc_length (n k : nat) (l : list term)
: length (Proj2Nc n k l) = length l.
Proof.
  induction l; simpl; lia.
Qed.

Lemma Proj2Nc_nth (n m k : nat) (l : list term) (len : n < length (Proj2Nc m k l)) (len2 : n < length l)
: safe_nth n (Proj2Nc m k l) len = Proj2N m (k + length l - n - 1) (safe_nth n l len2).
Proof.
  revert n m k len len2.
  induction l; intros n m k len len2;
  simpl in *; try lia.
  destruct n; simpl in *. { f_equal. lia. }
  erewrite IHl. f_equal. lia.
Qed.

Definition PC_length1 {m n Γ Δ} (eqΓ : length Γ = m) (eqΔ : length Δ = m) (isdef : n < length (PackContext m Γ Δ eqΓ eqΔ))
: n < length Γ.
Proof.
  rewrite PackContext_length in isdef. lia.
Defined.

Definition PC_length2 {m n Γ Δ} (eqΓ : length Γ = m) (eqΔ : length Δ = m) (isdef : n < length (PackContext m Γ Δ eqΓ eqΔ))
: n < length Δ.
Proof.
  rewrite PackContext_length in isdef. lia.
Defined.

Lemma PackContext_nth (m n : nat) (Γ Δ : context) (eqΓ : length Γ = m) (eqΔ : length Δ = m)
  (isdef : n < length (PackContext m Γ Δ eqΓ eqΔ)) (isdefΓ : n < length Γ) (isdefΔ : n < length Δ)
: safe_nth n (PackContext m Γ Δ eqΓ eqΔ) isdef = Pack (Proj1N (m - n - 1) 0 (safe_nth n Γ isdefΓ)) (Proj2N (m - n - 1) 0 (safe_nth n Δ isdefΔ)).
Proof.
  revert n Γ Δ eqΓ eqΔ isdef isdefΓ isdefΔ; induction m; intros n Γ Δ eqΓ eqΔ isdef isdefΓ isdefΔ;
  destruct Γ; destruct Δ; try discriminate.
  - simpl in isdefΓ. lia.
  - destruct n; simpl. { f_equal; f_equal; lia. }
    apply IHm.
Qed.

Lemma PackContext_nth' (m n : nat) (Γ Δ : context) (eqΓ : length Γ = m) (eqΔ : length Δ = m)
  (isdef : n < length (PackContext m Γ Δ eqΓ eqΔ)) (isdefΓ : n < length Γ) (isdefΔ : n < length Δ)
: safe_nth n (PackContext m Γ Δ eqΓ eqΔ) isdef = Pack (Proj1N (m - n - 1) 0 (safe_nth n Γ (PC_length1 eqΓ eqΔ isdef))) (Proj2N (m - n - 1) 0 (safe_nth n Δ (PC_length2 eqΓ eqΔ isdef))).
Proof.
  apply PackContext_nth.
Qed.

Lemma lift_proj1 (n m k i : nat) (t : term) (i_lt_k : i < S k)
: lift n i (Proj1N m k t) = Proj1N m (n + k) (lift n i t).
Proof.
  revert m k i i_lt_k. induction t; intros m k i i_lt_k; unfold lift;
  simpl in *; f_equal; eauto.
  - unfold skip, jump. comp_cases.
  - subst_helper. replace (S (n + k)) with (n + S k) by lia. apply IHt2. lia.
  - subst_helper. replace (S (n + k)) with (n + S k) by lia. apply IHt. lia.
  - subst_helper. replace (S (n + k)) with (n + S k) by lia. apply IHt2. lia.
  - subst_helper. replace (S (n + k)) with (n + S k) by lia. apply IHt1. lia.
Qed.

Lemma Proj1N_lift (n m k1 k2 i : nat) (t : term) (k1m : k1 <= m) (k2m : k2 <= m)
: Proj1N (n-k1) (i + k1) (lift m i t) = Proj1N (n-k2) (i + k2) (lift m i t).
Proof.
  revert i; induction t; intros i;
  unfold lift; simpl; f_equal; subst_helper; 
  try replace (S (i + k1)) with ((i + 1) + k1) by lia;
  try replace (S (i + k2)) with ((i + 1) + k2) by lia;
  eauto.
  unfold skip, jump. comp_cases.
Qed.

Lemma Proj1N_lift' (m n k i : nat) (t : term) (nmk : m + k < n)
: Proj1N m (k + i) (lift n i t) = lift n i t.
Proof.
  revert i k nmk; induction t; intros i k nmk;
  unfold lift; simpl; subst_helper; f_equal;
  try replace (S (k + i)) with (k + (i + 1)) by lia;
  eauto.
  unfold skip, jump. comp_cases.
Qed.

Lemma Proj1N_subst (m k i : nat) (t u : term)
: Proj1N m (k + i) t[i ← u] = (Proj1N m (S k + i) t)[i ← Proj1N m k u].
Proof.
  revert m k i u. induction t; intros m k i u;
  simpl in *; f_equal; eauto;
  try replace (S (k + i)) with (k + S i) by lia;
  try replace (S (k + S i)) with (S k + S i) by lia; eauto.
  comp_cases; simpl; comp_cases.
  rewrite lift_proj1 by lia.
  f_equal. lia.
Qed.

Lemma Proj1N_red1 (n k : nat) (u v : term)
: u ▷ v -> Proj1N n k u ▷ Proj1N n k v.
Proof.
  intro uv.
  revert k; induction uv; intro k; simpl; eauto using red1.
  - replace k with (k + 0) by lia.
    rewrite Proj1N_subst.
    replace (k + 0) with k by lia.
    replace (S k + 0) with (S k) by lia.
    apply red1_beta_app.
  - replace k with (k + 0) by lia.
    rewrite Proj1N_subst.
    replace (k + 0) with k by lia.
    replace (S k + 0) with (S k) by lia.
    apply red1_beta_J.
  - replace (S k) with (1 + k) by lia.
    rewrite <- lift_proj1 by lia.
    apply red1_eta_lambda.
Qed.

Lemma Proj1N_conv (n k : nat) (u v : term)
: u ≡ v -> Proj1N n k u ≡ Proj1N n k v.
Proof.
  intro uv. induction uv.
  - apply conv_refl.
  - eapply conv_red_l. 2: { eassumption. }
    apply Proj1N_red1. assumption.
  - eapply conv_red_r. 2: { eassumption. }
    apply Proj1N_red1. assumption.
Qed.

Lemma Pack1 {n k} (Γ Δ Ξ Ψ : context) (eqΓ : length Γ = n) (eqΔ : length Δ = n) (eqΞ : length Ξ = k) (t A : term)
: Ψ ;; Γ ;; Ξ ⊢ᵢ t : A ->
  Ψ ;; (PackContext n Γ Δ eqΓ eqΔ) ;; (Proj1Nc n 0 Ξ) ⊢ᵢ Proj1N n k t : Proj1N n k A.
Proof.
  remember (Ψ;;Γ;;Ξ) as ΓΞ.
  intro tA.
  revert n k Γ Δ Ξ HeqΓΞ eqΓ eqΔ eqΞ. induction tA; intros m k Γ' Δ Ξ HeqΓ'Ξ eqΓ eqΔ eqΞ;
  subst Γ; simpl Proj1N; simpl in *; eauto using ityped.
  - apply ityProd. eauto.
    replace k with (0 + length Ξ) by lia.
    replace (Ψ;;PackContext m Γ' Δ eqΓ eqΔ;;Proj1Nc m 0 Ξ,,Proj1N m (0 + length Ξ) A) with (Ψ;;PackContext m Γ' Δ eqΓ eqΔ;;(Proj1Nc m 0 Ξ,,Proj1N m (0 + length Ξ) A)) by reflexivity.
    replace (Proj1Nc m 0 Ξ,,Proj1N m (0 + length Ξ) A) with (Proj1Nc m 0 (Ξ,,A)) by reflexivity.
    apply IHtA2; simpl; eauto.
  - apply itySum. eauto.
    replace k with (0 + length Ξ) by lia.
    replace (Ψ;;PackContext m Γ' Δ eqΓ eqΔ;;Proj1Nc m 0 Ξ,,Proj1N m (0 + length Ξ) A) with (Ψ;;PackContext m Γ' Δ eqΓ eqΔ;;(Proj1Nc m 0 Ξ,,Proj1N m (0 + length Ξ) A)) by reflexivity.
    replace (Proj1Nc m 0 Ξ,,Proj1N m (0 + length Ξ) A) with (Proj1Nc m 0 (Ξ,,A)) by reflexivity.
    apply IHtA2; simpl; eauto.
  - comp_cases.
    + eassert (Proj1N m k (lift (S n) 0 (safe_nth n (Ψ;;Γ';;Ξ) isdef)) = _).
      2: { rewrite H. apply ityRel. }
      erewrite safe_nth_concat, safe_nth_concat.
      erewrite Proj1Nc_nth.
      rewrite lift_proj1 by lia.
      f_equal. lia.
      Unshelve.
      rewrite app_length, app_length, Proj1Nc_length, PackContext_length. lia.
      lia.
      rewrite Proj1Nc_length. lia.
    + eapply ityPi1.
      eassert (∑Proj1N m k (lift (S n) 0 (safe_nth n (Ψ;;Γ';;Ξ) isdef)), _ = _).
      2: { rewrite H. eapply ityRel. }
      assert (eq1 : n = n - k + length Ξ) by lia.
      assert (eq2 : n = n - k + length (Proj1Nc m 0 Ξ)).
      { rewrite Proj1Nc_length. assumption. }
      rewrite safe_nth_rewrite with _ _ _ _ eq1.
      rewrite safe_nth_rewrite with _ _ _ _ eq2.
      erewrite safe_nth_concat', safe_nth_concat'.
      erewrite safe_nth_concat, safe_nth_concat.
      erewrite PackContext_nth.
      unfold Pack, lift. simpl. subst_helper. f_equal.
      erewrite lift_proj1 by lia.
      replace (m - (n - k) - 1) with ((m + k) - S n) by lia.
      replace (S n + 0) with (0 + S n) by lia.
      rewrite (Proj1N_lift _ _ _ k) by lia.
      f_equal. lia.
      Unshelve.
      rewrite app_length, app_length, Proj1Nc_length, PackContext_length. lia.
      rewrite app_length. lia.
      rewrite app_length, PackContext_length. lia.
      rewrite PackContext_length. lia.
      lia. lia.
    + eassert (Proj1N m k (lift (S n) 0 (safe_nth n (Ψ;;Γ';;Ξ) isdef)) = _).
      2: { rewrite H. apply ityRel. }
      assert (isdef' : n < length (Ψ ;; Γ' ;; Ξ)) by assumption.
      rewrite app_length, app_length in isdef'.
      assert (eq1 : n = n - k - m + length Γ' + length Ξ) by lia.
      assert (eq2 : n = n - k - m + length (PackContext m Γ' Δ eqΓ eqΔ) + length (Proj1Nc m 0 Ξ)).
      { rewrite Proj1Nc_length. rewrite PackContext_length. lia. }
      rewrite safe_nth_rewrite with _ _ _ _ eq1.
      rewrite safe_nth_rewrite with _ _ _ _ eq2.
      erewrite safe_nth_concat', safe_nth_concat'.
      erewrite safe_nth_concat', safe_nth_concat'.
      replace (Proj1N m k) with (Proj1N m (k + 0)) by (f_equal; lia).
      apply Proj1N_lift'. lia.
      Unshelve.
      repeat rewrite app_length in *. rewrite Proj1Nc_length, PackContext_length. lia.
      repeat rewrite app_length in *. lia.
      lia.
      rewrite PackContext_length, app_length, PackContext_length. lia.
  - apply ityLam with s1 s2; eauto.
    + replace k with (0 + length Ξ) by lia.
      replace (Ψ;;PackContext m Γ' Δ eqΓ eqΔ;;Proj1Nc m 0 Ξ,,Proj1N m (0 + length Ξ) A) with (Ψ;;PackContext m Γ' Δ eqΓ eqΔ;;(Proj1Nc m 0 Ξ,,Proj1N m (0 + length Ξ) A)) by reflexivity.
      replace (Proj1Nc m 0 Ξ,,Proj1N m (0 + length Ξ) A) with (Proj1Nc m 0 (Ξ,,A)) by reflexivity.
      eauto.
    + replace k with (0 + length Ξ) by lia.
      replace (Ψ;;PackContext m Γ' Δ eqΓ eqΔ;;Proj1Nc m 0 Ξ,,Proj1N m (0 + length Ξ) A) with (Ψ;;PackContext m Γ' Δ eqΓ eqΔ;;(Proj1Nc m 0 Ξ,,Proj1N m (0 + length Ξ) A)) by reflexivity.
      replace (Proj1Nc m 0 Ξ,,Proj1N m (0 + length Ξ) A) with (Proj1Nc m 0 (Ξ,,A)) by reflexivity.
      eauto.
  - replace k with (k + 0) by lia. rewrite Proj1N_subst.
    replace (k + 0) with k by lia.
    replace (S k + 0) with (S k) by lia.
    eapply ityApp; eauto.

    replace k with (0 + length Ξ) by lia.
      replace (Ψ;;PackContext m Γ' Δ eqΓ eqΔ;;Proj1Nc m 0 Ξ,,Proj1N m (0 + length Ξ) A) with (Ψ;;PackContext m Γ' Δ eqΓ eqΔ;;(Proj1Nc m 0 Ξ,,Proj1N m (0 + length Ξ) A)) by reflexivity.
      replace (Proj1Nc m 0 Ξ,,Proj1N m (0 + length Ξ) A) with (Proj1Nc m 0 (Ξ,,A)) by reflexivity.
      eauto.
  - eapply ityPair; eauto.
    + replace k with (0 + length Ξ) by lia.
      replace (Ψ;;PackContext m Γ' Δ eqΓ eqΔ;;Proj1Nc m 0 Ξ,,Proj1N m (0 + length Ξ) A) with (Ψ;;PackContext m Γ' Δ eqΓ eqΔ;;(Proj1Nc m 0 Ξ,,Proj1N m (0 + length Ξ) A)) by reflexivity.
      replace (Proj1Nc m 0 Ξ,,Proj1N m (0 + length Ξ) A) with (Proj1Nc m 0 (Ξ,,A)) by reflexivity.
      eauto.
    + replace (S k) with (S k + 0) by lia.
      rewrite <- Proj1N_subst.
      replace (k + 0) with k by lia.
      eauto.
  - replace k with (k + 0) by lia. rewrite Proj1N_subst.
    replace (k + 0) with k by lia.
    replace (S k + 0) with (S k) by lia.
    eapply ityPi2. eauto.
  - replace k with (k + 0) by lia.
    repeat rewrite Proj1N_subst.
    replace (S k) with (1 + k) by lia. rewrite <-lift_proj1 by lia.
    replace (S (1 + k)) with (2 + k) by lia. rewrite <- lift_proj1 by lia.
    replace (k + 0) with k by lia.
    replace (2 + k) with (S (S k)) by lia.
    eapply ityJ.
    + specialize (IHtA1 m (S (S (S k))) Γ' Δ (Ξ,,A,,lift 1 0 A,,^1 == ^0)).
      simpl Proj1Nc in IHtA1.
      replace (S (length Ξ)) with (1 + length Ξ) in IHtA1 by lia.
      rewrite <- lift_proj1 in IHtA1.
      replace (S (S (S k)) + 0) with (S (S (S k))) by lia.
      apply IHtA1; simpl; eauto.
      lia.
    + replace (Refl(^1)) with (Proj1N m (S (S k)) Refl(^1)) by reflexivity.
      replace ^0 with (Proj1N m (S k) ^0) by reflexivity.
      repeat rewrite <- Proj1N_subst.
      replace (S k + 0) with (S k) by lia.
      specialize (IHtA2 m (S k) Γ' Δ (Ξ,,A)).
      simpl Proj1Nc in IHtA2. apply IHtA2; simpl; eauto.
    + rewrite eqΞ. eauto.
    + rewrite eqΞ. eauto.
    + eauto.
  - eapply ityConv; eauto.
    apply Proj1N_conv. assumption.
Qed.

Lemma lift_proj2 (n m k i : nat) (t : term) (i_lt_k : i < S k)
: lift n i (Proj2N m k t) = Proj2N m (n + k) (lift n i t).
Proof.
  revert m k i i_lt_k. induction t; intros m k i i_lt_k; unfold lift;
  simpl in *; f_equal; eauto.
  - unfold skip, jump. comp_cases.
  - subst_helper. replace (S (n + k)) with (n + S k) by lia. apply IHt2. lia.
  - subst_helper. replace (S (n + k)) with (n + S k) by lia. apply IHt. lia.
  - subst_helper. replace (S (n + k)) with (n + S k) by lia. apply IHt2. lia.
  - subst_helper. replace (S (n + k)) with (n + S k) by lia. apply IHt1. lia.
Qed.

Lemma Proj2N_lift (n m k1 k2 i : nat) (t : term) (k1m : k1 <= m) (k2m : k2 <= m)
: Proj2N (n-k1) (i + k1) (lift m i t) = Proj2N (n-k2) (i + k2) (lift m i t).
Proof.
  revert i; induction t; intros i;
  unfold lift; simpl; f_equal; subst_helper; 
  try replace (S (i + k1)) with ((i + 1) + k1) by lia;
  try replace (S (i + k2)) with ((i + 1) + k2) by lia;
  eauto.
  unfold skip, jump. comp_cases.
Qed.

Lemma Proj2N_lift' (m n k i : nat) (t : term) (nmk : m + k < n)
: Proj2N m (k + i) (lift n i t) = lift n i t.
Proof.
  revert i k nmk; induction t; intros i k nmk;
  unfold lift; simpl; subst_helper; f_equal;
  try replace (S (k + i)) with (k + (i + 1)) by lia;
  eauto.
  unfold skip, jump. comp_cases.
Qed.

Lemma Proj2N_subst (m k i : nat) (t u : term)
: Proj2N m (k + i) t[i ← u] = (Proj2N m (S k + i) t)[i ← Proj2N m k u].
Proof.
  revert m k i u. induction t; intros m k i u;
  simpl in *; f_equal; eauto;
  try replace (S (k + i)) with (k + S i) by lia;
  try replace (S (k + S i)) with (S k + S i) by lia; eauto.
  comp_cases; simpl; comp_cases.
  rewrite lift_proj2 by lia.
  f_equal. lia.
Qed.

Lemma Proj2N_red1 (n k : nat) (u v : term)
: u ▷ v -> Proj2N n k u ▷ Proj2N n k v.
Proof.
  intro uv.
  revert k; induction uv; intro k; simpl; eauto using red1.
  - replace k with (k + 0) by lia.
    rewrite Proj2N_subst.
    replace (k + 0) with k by lia.
    replace (S k + 0) with (S k) by lia.
    apply red1_beta_app.
  - replace k with (k + 0) by lia.
    rewrite Proj2N_subst.
    replace (k + 0) with k by lia.
    replace (S k + 0) with (S k) by lia.
    apply red1_beta_J.
  - replace (S k) with (1 + k) by lia.
    rewrite <- lift_proj2 by lia.
    apply red1_eta_lambda.
Qed.

Lemma Proj2N_conv (n k : nat) (u v : term)
: u ≡ v -> Proj2N n k u ≡ Proj2N n k v.
Proof.
  intro uv. induction uv.
  - apply conv_refl.
  - eapply conv_red_l. 2: { eassumption. }
    apply Proj2N_red1. assumption.
  - eapply conv_red_r. 2: { eassumption. }
    apply Proj2N_red1. assumption.
Qed.

Lemma Pack2 {n k} (Γ Δ Ξ Ψ : context) (eqΓ : length Γ = n) (eqΔ : length Δ = n) (eqΞ : length Ξ = k) (t A : term)
: Ψ ;; Δ ;; Ξ ⊢ᵢ t : A ->
  Ψ ;; (PackContext n Γ Δ eqΓ eqΔ) ;; (Proj2Nc n 0 Ξ) ⊢ᵢ Proj2N n k t : Proj2N n k A.
Proof.
  remember (Ψ;;Δ;;Ξ) as ΔΞ.
  intro tA.
  revert n k Γ Δ Ξ HeqΔΞ eqΓ eqΔ eqΞ. induction tA; intros m k Γ' Δ Ξ HeqΓ'Ξ eqΓ eqΔ eqΞ;
  subst Γ; simpl Proj2N; simpl in *; eauto using ityped.
  - apply ityProd. eauto.
    replace k with (0 + length Ξ) by lia.
    replace (Ψ;;PackContext m Γ' Δ eqΓ eqΔ;;Proj2Nc m 0 Ξ,,Proj2N m (0 + length Ξ) A) with (Ψ;;PackContext m Γ' Δ eqΓ eqΔ;;(Proj2Nc m 0 Ξ,,Proj2N m (0 + length Ξ) A)) by reflexivity.
    replace (Proj2Nc m 0 Ξ,,Proj2N m (0 + length Ξ) A) with (Proj2Nc m 0 (Ξ,,A)) by reflexivity.
    apply IHtA2; simpl; eauto.
  - apply itySum. eauto.
    replace k with (0 + length Ξ) by lia.
    replace (Ψ;;PackContext m Γ' Δ eqΓ eqΔ;;Proj2Nc m 0 Ξ,,Proj2N m (0 + length Ξ) A) with (Ψ;;PackContext m Γ' Δ eqΓ eqΔ;;(Proj2Nc m 0 Ξ,,Proj2N m (0 + length Ξ) A)) by reflexivity.
    replace (Proj2Nc m 0 Ξ,,Proj2N m (0 + length Ξ) A) with (Proj2Nc m 0 (Ξ,,A)) by reflexivity.
    apply IHtA2; simpl; eauto.
  - comp_cases.
    + eassert (Proj2N m k (lift (S n) 0 (safe_nth n (Ψ;;Δ;;Ξ) isdef)) = _).
      2: { rewrite H. apply ityRel. }
      erewrite safe_nth_concat, safe_nth_concat.
      erewrite Proj2Nc_nth.
      rewrite lift_proj2 by lia.
      f_equal. lia.
      Unshelve.
      rewrite app_length, app_length, Proj2Nc_length, PackContext_length. lia.
      lia.
      rewrite Proj2Nc_length. lia.
    + assert (isdef' : n-k < length (PackContext m Γ' Δ eqΓ eqΔ)). { rewrite PackContext_length. lia. }
      assert (isdef'' : n-k < length (PackContext m Γ' Δ eqΓ eqΔ)). { rewrite PackContext_length. lia. }
      set (x := (Proj1N (m + k - n - 1) 0 (safe_nth (n - k) Γ' (PC_length1 eqΓ eqΔ isdef')))).
      set (y := (Proj2N (m + k - n - 1) 0 (safe_nth (n - k) Δ (PC_length2 eqΓ eqΔ isdef')))).
      eapply (ityPi1 _ _ (∑(lift (n + 2) 0 x)==(lift (n + 2) 0 y),tTransport ^0 (π₁ ^(n+2))==^1)).
      eassert (H1 : ∑Proj2N m k (lift (S n) 0 (safe_nth n (Ψ;;Δ;;Ξ) isdef)), _ = _).
      2: {
        rewrite H1. eapply ityPi2.
        eassert (H2 : ∑_, _ = _).
        2: { rewrite H2. eapply ityRel. }
        assert (eq : n = n - k + length (Proj2Nc m 0 Ξ)). { rewrite Proj2Nc_length. lia. }
        rewrite eq.
        erewrite safe_nth_concat', safe_nth_concat.
        rewrite <- eq.
        erewrite PackContext_nth' by lia.
        replace (m - (n - k) - 1) with (m + k - (n + 1)) by lia.
        unfold Pack. simpl. subst_helper. simpl "+". f_equal.
      }
      replace 1 with (0 + 1) by lia. repeat rewrite lift_lift by lia. replace (0 + 1) with 1 by lia.
      replace 2 with (0 + 2) by lia. repeat rewrite lift_lift by lia. replace (0 + 2) with 2 by lia.
      repeat rewrite lift_add.
      simpl.
      repeat rewrite subst_lift by lia.
      f_equal.
      * rewrite lift_proj2 by lia.
        replace (n + 1 + 0) with (0 + (n + 1)) by lia.
        rewrite (Proj2N_lift _ _ _ k) by lia.
        f_equal. lia.
        f_equal. f_equal. f_equal. lia.
        assert (eq : n = n-k+length Ξ) by lia.
        rewrite (safe_nth_rewrite _ _ _ _ eq).
        erewrite safe_nth_concat'.
        erewrite safe_nth_concat.
        apply safe_nth_proof_irrelevant.
      * subst x y; f_equal; f_equal; f_equal; f_equal; try lia.
        f_equal. unfold skip, jump. comp_cases.

      Unshelve.
      repeat rewrite app_length. rewrite PackContext_length, Proj2Nc_length. lia.
      repeat rewrite app_length. rewrite PackContext_length. lia.
      rewrite app_length. lia.
      lia.
    + eassert (Proj2N m k (lift (S n) 0 (safe_nth n (Ψ;;Δ;;Ξ) isdef)) = _).
      2: { rewrite H. apply ityRel. }
      assert (isdef' : n < length (Ψ ;; Δ ;; Ξ)) by assumption.
      rewrite app_length, app_length in isdef'.
      assert (eq1 : n = n - k - m + length Δ + length Ξ) by lia.
      assert (eq2 : n = n - k - m + length (PackContext m Γ' Δ eqΓ eqΔ) + length (Proj2Nc m 0 Ξ)).
      { rewrite Proj2Nc_length. rewrite PackContext_length. lia. }
      rewrite safe_nth_rewrite with _ _ _ _ eq1.
      rewrite safe_nth_rewrite with _ _ _ _ eq2.
      erewrite safe_nth_concat', safe_nth_concat'.
      erewrite safe_nth_concat', safe_nth_concat'.
      replace (Proj2N m k) with (Proj2N m (k + 0)) by (f_equal; lia).
      apply Proj2N_lift'. lia.
      Unshelve.
      repeat rewrite app_length in *. rewrite Proj2Nc_length. rewrite PackContext_length. lia.
      repeat rewrite app_length in *. lia.
      repeat rewrite app_length in *. lia.
      rewrite PackContext_length, app_length, PackContext_length. lia.
  - apply ityLam with s1 s2; eauto.
    + replace k with (0 + length Ξ) by lia.
      replace (Ψ;;PackContext m Γ' Δ eqΓ eqΔ;;Proj2Nc m 0 Ξ,,Proj2N m (0 + length Ξ) A) with (Ψ;;PackContext m Γ' Δ eqΓ eqΔ;;(Proj2Nc m 0 Ξ,,Proj2N m (0 + length Ξ) A)) by reflexivity.
      replace (Proj2Nc m 0 Ξ,,Proj2N m (0 + length Ξ) A) with (Proj2Nc m 0 (Ξ,,A)) by reflexivity.
      eauto.
    + replace k with (0 + length Ξ) by lia.
      replace (Ψ;;PackContext m Γ' Δ eqΓ eqΔ;;Proj2Nc m 0 Ξ,,Proj2N m (0 + length Ξ) A) with (Ψ;;PackContext m Γ' Δ eqΓ eqΔ;;(Proj2Nc m 0 Ξ,,Proj2N m (0 + length Ξ) A)) by reflexivity.
      replace (Proj2Nc m 0 Ξ,,Proj2N m (0 + length Ξ) A) with (Proj2Nc m 0 (Ξ,,A)) by reflexivity.
      eauto.
  - replace k with (k + 0) by lia. rewrite Proj2N_subst.
    replace (k + 0) with k by lia.
    replace (S k + 0) with (S k) by lia.
    eapply ityApp; eauto.

    replace k with (0 + length Ξ) by lia.
      replace (Ψ;;PackContext m Γ' Δ eqΓ eqΔ;;Proj2Nc m 0 Ξ,,Proj2N m (0 + length Ξ) A) with (Ψ;;PackContext m Γ' Δ eqΓ eqΔ;;(Proj2Nc m 0 Ξ,,Proj2N m (0 + length Ξ) A)) by reflexivity.
      replace (Proj2Nc m 0 Ξ,,Proj2N m (0 + length Ξ) A) with (Proj2Nc m 0 (Ξ,,A)) by reflexivity.
      eauto.
  - eapply ityPair; eauto.
    + replace k with (0 + length Ξ) by lia.
      replace (Ψ;;PackContext m Γ' Δ eqΓ eqΔ;;Proj2Nc m 0 Ξ,,Proj2N m (0 + length Ξ) A) with (Ψ;;PackContext m Γ' Δ eqΓ eqΔ;;(Proj2Nc m 0 Ξ,,Proj2N m (0 + length Ξ) A)) by reflexivity.
      replace (Proj2Nc m 0 Ξ,,Proj2N m (0 + length Ξ) A) with (Proj2Nc m 0 (Ξ,,A)) by reflexivity.
      eauto.
    + replace (S k) with (S k + 0) by lia.
      rewrite <- Proj2N_subst.
      replace (k + 0) with k by lia.
      eauto.
  - replace k with (k + 0) by lia. rewrite Proj2N_subst.
    replace (k + 0) with k by lia.
    replace (S k + 0) with (S k) by lia.
    eapply ityPi2. eauto.
  - replace k with (k + 0) by lia.
    repeat rewrite Proj2N_subst.
    replace (S k) with (1 + k) by lia. rewrite <-lift_proj2 by lia.
    replace (S (1 + k)) with (2 + k) by lia. rewrite <- lift_proj2 by lia.
    replace (k + 0) with k by lia.
    replace (2 + k) with (S (S k)) by lia.
    eapply ityJ.
    + specialize (IHtA1 m (S (S (S k))) Γ' Δ (Ξ,,A,,lift 1 0 A,,^1 == ^0)).
      simpl Proj2Nc in IHtA1.
      replace (S (length Ξ)) with (1 + length Ξ) in IHtA1 by lia.
      rewrite <- lift_proj2 in IHtA1.
      replace (S (S (S k)) + 0) with (S (S (S k))) by lia.
      apply IHtA1; simpl; eauto.
      lia.
    + replace (Refl(^1)) with (Proj2N m (S (S k)) Refl(^1)) by reflexivity.
      replace ^0 with (Proj2N m (S k) ^0) by reflexivity.
      repeat rewrite <- Proj2N_subst.
      replace (S k + 0) with (S k) by lia.
      specialize (IHtA2 m (S k) Γ' Δ (Ξ,,A)).
      simpl Proj2Nc in IHtA2. apply IHtA2; simpl; eauto.
    + rewrite eqΞ. eauto.
    + rewrite eqΞ. eauto.
    + eauto.
  - eapply ityConv; eauto.
    apply Proj2N_conv. assumption.
Admitted. (* doesn't get through final checks *)

Lemma fundamental_lemma {Γ Γ₁ Γ₂} {t₁ t₂ T₁ T₂ : term} {n : nat} (isdef1 : length Γ₁ = n) (isdef2 : length Γ₂ = n)
: t₁ ≃ t₂ -> 
  Γ;;Γ₁ ⊢ᵢ t₁ : T₁ -> 
  Γ;;Γ₂ ⊢ᵢ t₂ : T₂ ->
  exists p, Γ ;; (PackContext n Γ₁ Γ₂ isdef1 isdef2) ⊢ᵢ p : Heq (Proj1N n 0 T₁) (Proj2N n 0 T₂) (Proj1N n 0 t₁) (Proj2N n 0 t₂).
Admitted.