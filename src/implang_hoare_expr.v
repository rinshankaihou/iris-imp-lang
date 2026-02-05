From iris_simp_lang Require Import imp_notation stack_ra implang_expr lifting_expr.

Section wp_expr.

Context `{!envGS val Σ} `{!gen_heap.gen_heapGS loc val Σ} `{!invGS_gen HasNoLc Σ}.

Lemma wp_val E Q n :  Q (NumV n) ⊢ wp_expr E (Num n) Q.
    rewrite /wp_expr.
    iIntros "?" (σ ρ) "?".
    iFrame.
    iModIntro. iIntros.
    iStopProof. split => l.
    monPred.unseal.
    iPureIntro => ?.
    constructor.
Qed.

End wp_expr.
