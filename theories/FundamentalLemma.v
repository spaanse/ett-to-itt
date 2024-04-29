From Coq Require Import Lia.
Require Import Ast Subst Conversion ITT Decorates.
Open Scope t_scope.
Open Scope subst_scope.
Open Scope i_scope.

Fixpoint Proj1N (n : nat) (t : term) : term :=
match n with
| S n' => Proj1N n' ((lift 1 (S n) t)[n ← Proj₁ ^n])
| O    => t
end.

Fixpoint Proj2N (n : nat) (t : term) : term :=
match n with
| S n' => Proj2N n' ((lift 1 (S n) t)[n ← Proj₂ ^n])
| O    => t
end.

Search (S ?n = S ?m -> ?n = ?m).

Program Fixpoint PackContext (n : nat) (Γ Δ : context) (eqΓ : length Γ = n) (eqΔ : length Δ = n) : context :=
match n, Γ, Δ with
| S n', (Γ',,A), (Δ',,B) => (PackContext n' Γ' Δ' _ _) ,, Pack (Proj1N (length Γ) A) (Proj2N (length Δ) B)
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

Lemma Pack1 {n} (Γ Δ Ξ : context) (eqΔ : length Δ = n) (eqΞ : length Ξ = n) (t A : term)
: Γ ;; Δ ⊢ᵢ t : A ->
  Γ ;; (PackContext n Δ Ξ eqΔ eqΞ) ⊢ᵢ Proj1N n t : Proj1N n A.
Proof.
  intros tA. revert n Ξ eqΔ eqΞ.
  induction tA; intros m Ξ eqΔ eqΞ.
  - revert Δ Ξ eqΔ eqΞ. induction m. { eauto using typed. }
    intros Δ Ξ eqΔ eqΞ.
    destruct Δ, Ξ; try discriminate.
    simpl in eqΔ, eqΞ.
    simpl . replace (PackContext m Δ Ξ _ _) with (PackContext m Δ Ξ (eq_add_S _ _ eqΔ) (eq_add_S _ _ eqΞ)) by apply PackContext_proof_irrelevant.
    


  
  revert Γ Δ Ξ eqΔ eqΞ.
  induction n; intros Γ Δ Ξ eqΔ eqΞ tA;
  destruct Δ; destruct Ξ; try discriminate. { assumption. }
  
  simpl in eqΔ, eqΞ.
  
  simpl; eauto using typed;
  try assert (eq' : length Δ = length Ξ) by (simpl in eq; lia);
  try replace (PackContext Δ Ξ _) with (PackContext Δ Ξ eq') by apply PackContext_proof_irrelevant;
  try replace (length Ξ) with (length Δ).
  - generalize (length Δ). intro n.
    induction n; simpl; eauto using typed.
  - 


Qed.
