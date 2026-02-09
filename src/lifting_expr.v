From iris.base_logic.lib Require Export fancy_updates.
From iris_simp_lang Require Import implang_expr.
From iris_simp_lang Require Export state_interp.

Section wp_expr.

Context `{!gen_heapGS loc val Σ} `{!envGS val Σ} `{!invGS_gen hlc Σ}.

Implicit Types (ρ : @env_state val) (σ : gmap loc val).

(* to stack_ra *)
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

Lemma stack_level_up : forall n, stack_level n ⊢ up1 (stack_level (S n)).
Proof.
  split => ?; rewrite /stack_level; monPred.unseal.
  by apply bi.pure_mono; intros ->.
Qed.

Lemma stack_level_down : forall n, stack_level (S n) ⊢ down1 (stack_level n).
Proof.
  split => ?; rewrite /stack_level; monPred.unseal.
  by apply bi.pure_mono; intros <-.
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
  
Lemma wp_val E Q n :  Q (NumV n) ⊢ wp_expr E (Num n) Q.
Proof.
    rewrite /wp_expr.
    iIntros "?" (σ ρ) "?".
    iFrame.
    iModIntro. iIntros.
    iStopProof. split => l.
    monPred.unseal.
    iPureIntro => ?.
    constructor.
Qed.

Lemma wp_var E Q x v :
    x ↦v v ∗ (x ↦v v -∗ Q v) ⊢ wp_expr E (Var x) Q.
Proof.
    split => n; rewrite /wp_expr /state_interp; monPred.unseal; rewrite /sqsubseteq.
    iIntros "[Hx HQ]" (σ ρ l) "-> [? env_auth]".
    iExists v. iModIntro.
    iSplit.
    - iIntros (??->) "%Hj".
      iPoseProof (var_e with "[$]") as "%Hρ".
      rewrite /env_to_environ Hj in Hρ.
      iPureIntro; by constructor.
    - iFrame. by iApply "HQ".
Qed.

Lemma wp_binop E Q op e1 e2:
    wp_expr E e1 (λ v1,
      wp_expr E e2 (λ v2,
        match bin_op_eval op v1 v2 with
        | Some v => Q v
        | None => False
        end)) 
    ⊢ wp_expr E (BinOp op e1 e2) Q.
Proof.
    intros. rewrite /wp_expr.
    apply bi.forall_mono => σ.
    apply bi.forall_mono => ρ.
    apply bi.wand_mono; try done.
    iIntros ">(%v1 & He1 & interp & He2)".
    iMod ("He2" $! _ _ with "[interp]") as "(%v2 & He2 & $ & HQ)"; first done.
    iModIntro.
    destruct (bin_op_eval op v1 v2) eqn:?; last done.
    iFrame.
    iIntros (r) "env".
    iPoseProof ("He1" with "env") as "%He1".
    iPoseProof ("He2" with "env") as "%He2".
    iPureIntro; econstructor; eauto.
Qed.

Lemma wp_load E (Q: val -> assert) op e:
    wp_expr E e (λ v0, ∃ l v, ⌜v0 = LocV l⌝ ∧ l ↦ v ∗ (l ↦ v -∗ Q v))
    ⊢ wp_expr E (UnOp op e) Q.
Proof.
    rewrite /wp_expr.
    apply bi.forall_mono => σ.
    apply bi.forall_mono => ρ.
    apply bi.wand_mono; try done.
    iIntros ">(%v0 & He & interp & %l & %v & -> & Hl & HQ)".
    iPoseProof (state_interp_load with "interp Hl") as "%σl".
    iModIntro.
    iFrame.
    iExists _. iSplitL "He".
    - iStopProof.
      apply bi.forall_mono => r.
      apply bi.wand_mono, bi.pure_mono; try done.
      intros. destruct op. econstructor; eauto.
    - by iApply "HQ".
Qed.

End wp_expr.
