(* wp for implang *)
From iris.base_logic Require Import gen_heap.
From iris.base_logic.lib Require Export fancy_updates.
From iris_simp_lang Require Import stack_ra implang imp_notation.

Section wp_expr.

Context `{!gen_heapGS loc val Σ} `{!envGS val Σ} `{!invGS_gen HasNoLc Σ}.

Implicit Types (ρ : @env_state val) (σ : gmap loc val).

Definition state_interp σ ρ := (gen_heap_interp σ ∗ env_auth ρ)%I.

Definition env_match ρ r := λ n, ρ !! n = Some r.

Definition wp_expr_pre (wp : func_env -d> coPset -d> stmt -d> iPropO Σ -d> iPropO Σ) :
    func_env -d> coPset -d> stmt -d> iPropO Σ -d> iPropO Σ := λ F E s Q,
 (
  ∀ σ ρ n, state_interp σ ρ ={E,∅}=∗ ∀ r, ⌜env_match ρ r n⌝ -∗ ∃ s' r' σ' stk stk',
        ⌜step F s (Build_state r σ stk) s' (Build_state r' σ' stk')⌝ ∗
        ▷ |={∅,E}=> ∃ ρ', state_interp σ' ρ' ∗ ⌜env_match ρ' r' n⌝ ∗ wp F E s' Q)%I.

Local Instance wp_expr_contractive : Contractive (wp_expr_pre).
Proof.
  rewrite /wp_expr_pre /= => n wp wp' Hwp F E s Q.
  do 28 (f_contractive || f_equiv). apply Hwp.
Qed.

Local Definition wp_expr_def := fixpoint wp_expr_pre.
Local Definition wp_expr_aux : seal (@wp_expr_def). Proof. by eexists. Qed.
Definition wp_expr := wp_expr_aux.(unseal).
Local Lemma wp_expr_unseal   : wp_expr = @wp_expr_def.
Proof. rewrite -wp_expr_aux.(seal_eq) //. Qed.

  
End wp_expr.