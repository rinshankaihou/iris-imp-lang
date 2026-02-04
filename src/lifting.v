(* wp for implang *)
From iris.base_logic Require Import gen_heap.
From iris_simp_lang Require Import stack_ra implang imp_notation lifting_expr.

Section wp.

Context `{!gen_heapGS loc val Σ} `{!envGS val Σ} `{!invGS_gen HasNoLc Σ}.

Implicit Types (ρ : @env_state val) (σ : gmap loc val).

Definition wp_pre (wp : func_env -d> coPset -d> stmt -d> assert -d> assert) :
    func_env -d> coPset -d> stmt -d> assert -d> assert := λ F E s Q,
 (∀ σ ρ, state_interp σ ρ ={E,∅}=∗ ∀ r, env_match ρ r -∗ ∃ s' r' σ' stk stk',
        ⌜step F s (Build_state r σ stk) s' (Build_state r' σ' stk')⌝ ∗
        ▷ |={∅,E}=> ∃ ρ', state_interp σ' ρ' ∗ env_match ρ' r' ∗ wp F E s' Q)%I.

Local Instance wp_contractive : Contractive (wp_pre).
Proof.
  rewrite /wp_pre /= => n wp wp' Hwp F E s Q.
  do 26 (f_contractive || f_equiv). apply Hwp.
Qed.

Local Definition wp_def := fixpoint wp_pre.
Local Definition wp_aux : seal (@wp_def). Proof. by eexists. Qed.
Definition wp_expr := wp_aux.(unseal).
Local Lemma wp_unseal   : wp_expr = @wp_def.
Proof. rewrite -wp_aux.(seal_eq) //. Qed.


End wp.