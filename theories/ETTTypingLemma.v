From Coq Require Import List Lia Nat Arith.Compare_dec Arith.Arith Logic.FunctionalExtensionality.
From Coq Require Import Program.Equality.
Require Import Ast Subst ETT Tactics.
Open Scope t_scope.
Open Scope x_scope.

Lemma safe_nth_length (Γ Δ : context) (A : term) (isdef : length Δ < length (Γ ,, A ;; Δ))
: safe_nth (length Δ) (Γ ,, A ;; Δ) isdef = A.
Proof.
  induction Δ; simpl in *. { reflexivity. }
  apply IHΔ.
Qed.

Lemma type_lift {Γ Δ Ξ t A} (h : Γ ;; Ξ ⊢ₓ t : A)
: Γ ;; Δ ;; (liftc (length Δ) 0 Ξ) ⊢ₓ lift (length Δ) (length Ξ) t : lift (length Δ) (length Ξ) A
with cong_lift {Γ Δ Ξ t1 t2 A} (h : Γ ;; Ξ ⊢ₓ t1 ≡ t2 : A)
: Γ ;; Δ ;; (liftc (length Δ) 0 Ξ) ⊢ₓ lift (length Δ) (length Ξ) t1 ≡ lift (length Δ) (length Ξ) t1 : lift (length Δ) (length Ξ) A.
Proof.
  - dependent destruction h; cbn; subst_helper.
    + apply tySort.
    + apply tyProd.
      * apply (type_lift Γ Δ Ξ A *s1). assumption.
      * assert (H : Γ;;Δ;;liftc (length Δ) 0 (Ξ ,, A)
            ⊢ₓ lift (length Δ) (length (Ξ ,, A)) B
            : lift (length Δ) (length (Ξ ,, A)) *s2).
        { apply type_lift. assumption. }
        simpl in H.
        rewrite Nat.add_1_r.
        assumption.
    + apply tySum.
      * apply (type_lift Γ Δ Ξ A *s1). assumption.
      * assert (H : Γ;;Δ;;liftc (length Δ) 0 (Ξ ,, A)
            ⊢ₓ lift (length Δ) (length (Ξ ,, A)) B
            : lift (length Δ) (length (Ξ ,, A)) *s2).
        { apply type_lift. assumption. }
        simpl in H.
        rewrite Nat.add_1_r.
        assumption.
    + unfold jump, skip. comp_cases.
      * rewrite (safe_nth_concat _ _ _ _ Heqb).
        assert (isdef' : n < length (liftc (length Δ) 0 Ξ)).
        { rewrite liftc_length. assumption. }
        replace (lift (length Δ) (length Ξ) (lift0 (S n) (safe_nth n Ξ Heqb))) with (lift0 (S n) (safe_nth n (liftc (length Δ) 0 Ξ) isdef')).
        admit.
        admit.
      * admit.
    + apply tyLam with s1 s2.
      * apply (type_lift Γ Δ Ξ A *s1). assumption.
      * assert (H : Γ;;Δ;;liftc (length Δ) 0 (Ξ ,, A)
            ⊢ₓ lift (length Δ) (length (Ξ ,, A)) B
            : lift (length Δ) (length (Ξ ,, A)) *s2).
        { apply type_lift. assumption. }
        simpl in H.
        rewrite Nat.add_1_r.
        assumption.
      * assert (H : Γ;;Δ;;liftc (length Δ) 0 (Ξ ,, A)
            ⊢ₓ lift (length Δ) (length (Ξ ,, A)) t
            : lift (length Δ) (length (Ξ ,, A)) B).
        { apply type_lift. assumption. }
        simpl in H.
        rewrite Nat.add_1_r.
        assumption.
    + admit.
    + admit.
    + admit.
    + admit.
    + admit.
  - admit.   
Admitted.


Lemma context_consistent (Γ Δ Ξ : context) (u A : term) (uA : Γ ;; Ξ ⊢ₓ u : A)
: Γ ;; Δ ;; (liftc (length Δ) 0 Ξ) ⊢ₓ lift (length Δ) (length Ξ) u : lift (length Δ) (length Ξ) A.
Proof.
  induction Γ; simpl in *.
  - repeat rewrite <- (app_nil_end _) in *.
    induction uA; simpl.
    + apply tySort.
    + apply tyProd. { exact IHuA1. }
      subst_helper.
      replace (liftc (length Δ) 0 Γ ,, lift (length Δ) (length Γ) A) with (liftc (length Δ) 0 (Γ ,, A)).
      rewrite Nat.add_1_r.
      assumption. reflexivity.
    + apply tySum. { exact IHuA1. }
      subst_helper.
      simpl in IHuA2.
      rewrite Nat.add_1_r.
      assumption.
    + replace (lift (length Δ) (length Γ) ^n) with ^n.
      2: { unfold lift, update_rel, skip. comp_cases. }
      assert (isdef' : n < length (Δ ;; liftc (length Δ) 0 Γ)).
      { rewrite app_length, liftc_length. lia. }
      replace (lift (length Δ) (length Γ) (lift0 (S n) (safe_nth n Γ isdef))) with (lift0 (S n) (safe_nth n (Δ;;liftc (length Δ) 0 Γ) isdef')).
      { apply tyRel. }
      assert (isdef'' : n < length (liftc (length Δ) 0 Γ)).
      { rewrite liftc_length. assumption. }
      replace (safe_nth n (Δ ;; liftc (length Δ) 0 Γ) isdef') with (safe_nth n (liftc (length Δ) 0 Γ) isdef'').
      2: { revert n isdef isdef' isdef''; induction Γ; intros n isdef isdef' isdef''; simpl in *. { lia. }
           destruct n; simpl in *. { reflexivity. }
           apply IHΓ. lia. }
      revert n isdef isdef' isdef''; destruct Γ; intros n isdef isdef' isdef''; simpl in *. { lia. }
      destruct n; simpl in *.
      { unfold lift0, lift. rewrite update_rel_comp, update_rel_comp. f_equal.
        apply functional_extensionality. intro i.
        unfold skip, jump; comp_cases.
      }
      replace (safe_nth n (liftc (length Δ) 0 Γ) _) with (lift (length Δ) (length Γ - n - 1) (safe_nth n Γ (gt_le_S n (length Γ) (gt_S_le (S n) (length Γ) isdef)))).
      { unfold lift0, lift. rewrite update_rel_comp, update_rel_comp. f_equal.
        apply functional_extensionality. intro i.
        unfold jump, skip. comp_cases.
      }
      revert n isdef isdef' isdef''; induction Γ; intros n isdef isdef' isdef''; simpl in *. { lia. }
      destruct n; simpl in *.
      { replace (length Γ - 0) with (length Γ) by lia. reflexivity. }
      apply IHΓ.
      rewrite app_length, liftc_length. lia.
    + eapply (tyLam _ s1 s2); subst_helper;
      unfold liftc in *; fold liftc in *; simpl in *; try rewrite Nat.add_1_r; assumption.
    + unfold lift, update_rel in *; fold update_rel in *; subst_helper.
      simpl in *. rewrite Nat.add_1_r in *.
Admitted.

Lemma context_swap (Γ : context) (u A B C : term)
: Γ ,, A ⊢ₓ u : C ->
  Γ ,, B ,, lift 1 0 A ⊢ₓ lift 1 1 u : lift 1 1 C.
Proof.
  intro uC.
  induction u; inversion uC.
  - unfold lift. comp_cases; fold lift.
    + replace (lift 1 1) with (lift 1 (0+1)) by f_equal.
      unfold lift0.
      rewrite lift_lift by lia.
      rewrite lift_add. simpl.
      assert (isdef' : S n < length (Γ ,, B ,, lift 1 0 A)).
      { simpl in *. lia. }
      replace (safe_nth n (Γ ,, A) isdef) with (safe_nth (S n) (Γ ,, B ,, lift 1 0 A) isdef').
      apply tyRel.
      destruct n; simpl. { lia. }
      apply safe_nth_proof_irrelevant.
    + assert (nzero : n = 0). { lia. }
      rewrite nzero in *.
      generalize isdef. rewrite nzero. intro zero_lt_length.
      simpl. unfold lift0.
      replace (lift 1 1 (lift 1 0 A)) with (lift 1 0 (lift 1 0 A)).
      { getRel (Γ ,, B ,, lift 1 0 A) 0. }
      replace (lift 1 1) with (lift 1 (0+1)) by f_equal.
      rewrite lift_lift. reflexivity. lia.
  - unfold lift. comp_cases; fold lift.
    + 
      
  

Qed.

Lemma context_add_consistent' (Γ : context) (u A B : term) (uA : Γ ⊢ₓ u : A)
: Γ ,, B ⊢ₓ (lift 1 0 u) : (lift 1 0 A).
Proof.
  induction uA; simpl.
  - apply tySort.
  - apply tyProd.
    + assumption.
    + 
Qed.

Lemma context_add_consistent (Γ Ξ : context) (u A B : term) (uA : Γ ;; Ξ ⊢ₓ u : A)
: Γ ,, B ;; (liftc 1 0 Ξ) ⊢ₓ lift 1 (length Ξ) u : lift 1 (length Ξ) A.
Proof.
  induction Ξ; simpl in *.
  - induction uA; simpl.
    + apply tySort.
    + apply tyProd.
      * assumption.
      * 
Admitted.


Lemma context_consistent (Γ Δ Ξ : context) (u A : term) (uA : Γ ;; Ξ ⊢ₓ u : A)
: Γ ;; Δ ;; (liftc (length Δ) 0 Ξ) ⊢ₓ lift (length Δ) (length Ξ) u : lift (length Δ) (length Ξ) A.
Proof.
  induction uA; simpl in *.
  - apply tySort.
  - apply tyProd; try assumption.

    

  induction Δ; simpl.
  - unfold lift0. rewrite lift0k, lift0k. rewrite liftc0k. assumption.
  - rewrite <- Nat.add_1_l.
    rewrite <-lift_add.
    rewrite <-lift_add.
    rewrite <- liftc_add.
    apply (context_add_consistent _ _ _ _ a) in IHΔ.
    rewrite liftc_length in IHΔ.
    assumption.
Qed.

Lemma subst_consistent (Γ Δ : context) (u t A B : term) 
: Γ ⊢ₓ u : A ->
  Γ ,, A ;; Δ ⊢ₓ t : B ->
  Γ ;; Δ ⊢ₓ subst u (length Δ) t : subst u (length Δ) B.
Proof.
  intros uA tB.
  remember (Γ ,, A ;; Δ) as s. revert Heqs.
  induction tB; intros ->; simpl.
  - typer.
  - apply tyProd.
    + apply IHtB1. reflexivity.
    + admit.
  - apply tySum.
    + apply IHtB1. reflexivity.
    + admit. 
  - comp_cases.
    + generalize isdef.
      rewrite Heqc.
      intro isdef'.
      rewrite subst_lift0.
      rewrite safe_nth_length.
      
  - apply tyLam with s1 s2.
    
  - 
    
    
    
Qed.

Lemma typing_consistent_l (Γ : context) (u v A : term)
: Γ ⊢ₓ u ≡ v : A ->
  Γ ⊢ₓ u : A
with typing_consistent_r (Γ : context) (u v A : term)
: Γ ⊢ₓ u ≡ v : A ->
  Γ ⊢ₓ v : A.
Proof.
  intros eq.
  destruct eq.
  - assumption.
  - assumption.
  - exact (typing_consistent_l _ _ _ _ eq1).
  - eapply tyConv.
    { exact (typing_consistent_l _ _ _ _ eq1). }
    exact eq2.
  - eapply tyApp; [exact H|exact H0| |exact H2].
    eapply tyLam; [exact H|exact H0|exact H1].
  - eapply tyPi1.
    eapply tyPair; [exact H0|exact H|exact H1|exact H2].
  - eapply tyConv.
    + eapply tyPi2.
      eapply tyPair; [exact H0|exact H|exact H1|exact H2].
    + admit.
  - eapply tyLam; [exact H|exact H0|].
    eapply tyConv.
    + eapply tyApp; admit.
    + inversion H; admit.
  - admit.
  - admit.

Admitted.

Fixpoint valid_context (Γ : context) : Prop :=
match Γ with
| nil => True
| cons A Γ => (exists U, Γ ⊢ₓ A : U) /\ valid_context Γ
end.

Lemma typing_validity (Γ : context) (u A : term)
: Γ ⊢ₓ u : A ->
  exists (U : term), Γ ⊢ₓ A : U
with eq_validity (Γ : context) (u v A : term)
: Γ ⊢ₓ u ≡ v : A ->
  exists (U : term), Γ ⊢ₓ A : U.
Proof.
  intros judgement.
  destruct judgement.
  - exists (tSort (sSucc (sSucc s))).
    apply tySort.
  - exists (tSort (sSucc (sPi s1 s2))).
    apply tySort.
  - exists (tSort (sSucc (sSig s1 s2))).
    apply tySort.
  - admit.
    (* Need: validity of context *)
  - eexists.
    apply tyProd.
    + exact judgement1.
    + exact judgement2.
  - admit.
    (* Need: validity over subst *)
  - eexists.
    apply tySum.
    + exact judgement2.
    + exact judgement3.
  - destruct (typing_validity _ _ _ judgement) as [U j].
    inversion j.
    + exists *s1. assumption.
    + admit.
  - admit. 
    (* Need: validity over subst *)
  - eapply eq_validity.
    

  
    admit.
    (* Need: validity for equality judgement *)
  
Admitted.

