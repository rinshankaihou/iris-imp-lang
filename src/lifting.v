(* wp for implang *)
From iris.base_logic Require Import gen_heap.
From iris_simp_lang Require Import stack_ra implang imp_notation lifting_expr.

Section wp.

Context `{!gen_heapGS loc val Σ} `{!envGS val Σ} `{!invGS_gen HasNoLc Σ}.
Variable (F : func_env).

Implicit Types (ρ : @env_state val) (σ : gmap loc val).

Fixpoint make_stack (k : stack) : env_state * nat :=
  match k with
  | [] => (∅, O)
  | (r, _) :: k' => let '(ρ, n) := make_stack k' in (<[n := r]>ρ, S n)
  end.

Definition stack_match ρ r k := assert_of (λ n, ⌜let '(ρ0, n0) := make_stack k in n = n0 ∧ ρ = <[n := r]>ρ0⌝)%I.

Definition wp_pre (wp : coPset -d> stmt -d> assert -d> assert) :
    coPset -d> stmt -d> assert -d> assert := λ E s Q,
 (∀ σ ρ, state_interp σ ρ ={E,∅}=∗ ∀ r k, stack_match ρ r k -∗ ∃ s' r' σ' k',
        ⌜step F s (Build_state r σ k) s' (Build_state r' σ' k')⌝ ∗
        ▷ |={∅,E}=> ∃ ρ', state_interp σ' ρ' ∗ stack_match ρ' r' k' ∗ wp E s' Q)%I.

Local Instance wp_contractive : Contractive (wp_pre).
Proof.
  rewrite /wp_pre /= => n wp wp' Hwp E s Q.
  do 26 (f_contractive || f_equiv). apply Hwp.
Qed.

Local Definition wp_def := fixpoint wp_pre.
Local Definition wp_aux : seal (@wp_def). Proof. by eexists. Qed.
Definition wp := wp_aux.(unseal).
Local Lemma wp_unseal   : wp = @wp_def.
Proof. rewrite -wp_aux.(seal_eq) //. Qed.

Lemma wp_unfold E s Q : wp E s Q ⊣⊢ wp_pre wp E s Q.
Proof. rewrite wp_unseal. apply (fixpoint_unfold wp_pre). Qed.

End wp.