From iris.base_logic.lib Require Export fancy_updates.
From iris_simp_lang Require Import implang_expr.
From iris_simp_lang Require Export state_interp.

Section wp_expr.

Context `{!gen_heapGS loc val Σ} `{!envGS val Σ} `{!invGS_gen HasNoLc Σ}.

Implicit Types (ρ : @env_state val) (σ : gmap loc val).

Definition stack_level (n : nat) : assert := monPred_in(I := stack_index) n.

Lemma stack_level_intro : ⊢ ∃ n, stack_level n.
Proof.
  by iDestruct (monPred_in_intro emp%I with "[]") as (?) "($ & _)".
Qed.

Lemma stack_level_elim : forall (P : assert) n, ⊢ stack_level n -∗ ⎡P n⎤ -∗ P.
Proof.
  intros; iIntros "#? H".
  iApply bi.impl_elim_r; iSplit; first iApply "H".
  by iApply monPred_in_elim.
Qed.

Lemma stack_level_embed : forall n (P : assert), ⊢ stack_level n -∗ P -∗ ⎡P n⎤.
Proof.
  split => ?; rewrite /stack_level; monPred.unseal.
  iIntros "_" (? [=] [=] ? [=]); subst; auto.
Qed.

Lemma stack_level_eq : forall a b, ⊢ stack_level a -∗ stack_level b -∗ ⌜a = b⌝.
Proof.
  split => n; rewrite /stack_level; monPred.unseal; simpl.
  iIntros; iPureIntro; congruence.
Qed.

Definition env_match ρ r := assert_of (λ n, ⌜ρ !! n = Some r⌝)%I.

Definition wp_expr E e Q : assert :=
  (∀ σ ρ, ⎡state_interp σ ρ⎤ ={E}=∗
     ∃ v, (∀ r, env_match ρ r -∗ ⌜eval_expr e r σ v⌝) ∗
          ⎡state_interp σ ρ⎤ ∗ Q v)%I.

Fixpoint wp_exprs E es Q : assert :=
  match es with
  | [] => Q []
  | e :: rest => wp_expr E e (λ v, wp_exprs E rest (λ vs, Q (v :: vs)))
  end.
  
End wp_expr.
