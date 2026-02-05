From iris_simp_lang Require Import imp_notation stack_ra implang_expr lifting_expr.
From iris Require Import gen_heap.

Section wp_expr.

Context `{!envGS val Σ} `{!gen_heapGS loc val Σ} `{!invGS_gen HasNoLc Σ}.

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
    wp_expr E e (λ v0, ∃ l v, ⌜v0 = LocV l⌝ ∧ l ↦ v⎤∗ (l ↦ v -∗ Q v))
    ⊢ wp_expr E (UnOp op e) Q.
Proof.

End wp_expr.
