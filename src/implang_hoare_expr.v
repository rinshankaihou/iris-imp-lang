From iris_simp_lang Require Import imp_notation stack_ra implang_expr lifting_expr.

Section wp_expr.

Context `{!envGS val Σ} `{!gen_heap.gen_heapGS loc val Σ} `{!invGS_gen HasNoLc Σ}.

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

Lemma wp_binop E Q op e1 e2 v1 v2 v:
    bin_op_eval op v1 v2 = Some v →
    wp_expr E e1 (λ v1,
      wp_expr E e2 (λ v2,
        Q v)) 
    ⊢ wp_expr E (BinOp op e1 e2) Q.
Proof.

End wp_expr.
