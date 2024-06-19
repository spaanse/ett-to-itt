From Coq Require Import Lia Nat List Arith.PeanoNat Logic.FunctionalExtensionality.
Require Import Ast Subst Conversion SafeNth ITT ETT Decorates Tactics FundamentalLemma.
Open Scope t_scope.
Open Scope subst_scope.
Open Scope i_scope.
Open Scope x_scope.

Inductive decoratesC : context -> context -> Prop :=
| decC_nil : decoratesC nil nil
| decC_app {Γ Γ' : context} {A A' : term}
: decoratesC Γ Γ' -> A ⊏ A' -> decoratesC (Γ ,, A) (Γ' ,, A')
.

Definition is_translation {t t' A A' : term} {Γ Γ' : context} (tAi : (Γ' ⊢ᵢ t' : A')) (tAx : (Γ ⊢ₓ t : A)) : Prop
:= decoratesC Γ Γ' /\ t ⊏ t' /\ A ⊏ A'.

Lemma same_head_sort {s : sort} {t A : term} {Γ : context}
: *s ⊏ A -> Γ ⊢ᵢ t : A-> exists e s'', Γ ⊢ᵢ t : tTransport e *s''.
Proof.
  intros sA tA.
  inversion tA; subst; try discriminate; eauto.
  - 

Qed.

Axiom Heq_to_Eq : forall {A u v p : term} {Γ : context}, Γ ⊢ᵢ p : Heq A A u v -> exists p', Γ ⊢ᵢ p' : u == v.

Lemma lem14_1_2 {Γ Γ' : context} {t t' A A' A'' : term} {s s' : sort}
    (tAi : (Γ' ⊢ᵢ t' : A')) (tAx : (Γ ⊢ₓ t : A))
    (Asi : (Γ' ⊢ᵢ A'' : *s')) (Asx : (Γ ⊢ₓ A : *s))
: is_translation tAi tAx ->
  is_translation Asi Asx ->
  exists t'', exists (tA'' : Γ' ⊢ᵢ t'' : A''), is_translation tA'' tAx.
Proof.
    intros [decΓ [tt' AA']] [_ [AA'' ss']].
    assert (sim : A' ≃ A'').
    { eauto using decsim_dec, decsim_trans, decsim_sym. }
    eapply (@fundamental_lemma _ nil nil _ _ _ _ 0 _ _) in sim; simpl in *; try eassumption.
    repeat rewrite proj1N_0k in sim. repeat rewrite proj2N_0k in sim.
    destruct sim as [p pHeq].
    apply Heq_to_Eq in pHeq.
    destruct pHeq as [p' p'eq].
    exists (tTransport p' t').
    assert (H : Γ' ⊢ᵢ tTransport p' t' : A'').
    { eapply ityTransport; eassumption. }
    exists H. split. assumption. split. apply dec_transport. assumption. assumption.
    admit. (* I don't know how Winterhalter arrived at this *)
Admitted.

Lemma translate_term {Γ Γ' : context} {t A : term} (tA : (Γ ⊢ₓ t : A)) (decΓ : decoratesC Γ Γ')
: exists t' A', (Γ' ⊢ᵢ t' : A') /\ t ⊏ t' /\ A ⊏ A'
with tranlate_eq {Γ Γ' : context} {u v A : term} (tA : (Γ ⊢ₓ u ≡ v : A)) (decΓ : decoratesC Γ' Γ)
: exists A' A'' u' v' e, A ⊏ A' /\ A ⊏ A'' /\ u ⊏ u' /\ v ⊏ v' /\ Γ ⊢ᵢ e : Heq A' A'' u' v'.
Proof.
- revert Γ' decΓ. induction tA; intros Γ' decΓ.
  + exists *s, *(sSucc s).
    split. apply itySort.
    split; apply dec_identity.
  + destruct (IHtA1 Γ' decΓ) as (A' & s1' & ? & ? & ?).
    assert (decΓA : decoratesC (Γ,,A) (Γ',,A')). { apply decC_app; assumption. }
    destruct (IHtA2 (Γ',,A') decΓA) as (B' & s2' & ? & ? & ?).
    exists (∏A', B').
    admit.
  + destruct (IHtA1 Γ' decΓ) as (A' & s1' & ? & ? & ?).
    assert (decΓA : decoratesC (Γ,,A) (Γ',,A')). { apply decC_app; assumption. }
    destruct (IHtA2 (Γ',,A') decΓA) as (B' & s2' & ? & ? & ?).
    exists (∑A', B'), *(sSig s1 s2).
    split. apply itySum.
    admit.
Admitted.