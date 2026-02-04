From iris.base_logic Require Import gen_heap.
From iris_simp_lang Require Import imp_cont_notation stack_ra lifting_expr.

Section wp.

Context `{!gen_heapGS loc val Σ} `{!envGS val Σ} `{!invGS_gen HasNoLc Σ}.

Definition state_interp σ ρ := (gen_heap_interp σ ∗ env_auth ρ)%I.

Fixpoint cont_to_stack k : env_state * nat :=
  match k with
  | Kstop => (∅, O)
  | Kcall _ r k' => let '(ρ, n) := cont_to_stack k' in (<[n := r]>ρ, S n)
  | Kseq _ k' | Kwhile _ _ k' => cont_to_stack k'
  end.

Definition stack_match ρ r k := let '(ρ0, n) := cont_to_stack k in ρ = <[n := r]>ρ0.

Definition wp_sk_pre (wp : func_env -d> coPset -d> stmt -d> cont -d> iPropO Σ -d> iPropO Σ) :
    func_env -d> coPset -d> stmt -d> cont -d> iPropO Σ -d> iPropO Σ := λ F E s k Q,
 ((⌜s = Sskip ∧ k = Kstop⌝ ∗ |={E}=> Q) ∨
  ∀ σ ρ, state_interp σ ρ ={E,∅}=∗ ∀ r, ⌜stack_match ρ r k⌝ -∗ ∃ s' r' σ' k',
        ⌜step F s (Build_state r σ k) s' (Build_state r' σ' k')⌝ ∗
        ▷ |={∅,E}=> ∃ ρ', state_interp σ' ρ' ∗ ⌜stack_match ρ' r' k'⌝ ∗ wp F E s' k' Q)%I.

Local Instance wp_sk_pre_contractive : Contractive (wp_sk_pre).
Proof.
  rewrite /wp_sk_pre /= => n wp wp' Hwp F E s k Q.
  do 25 (f_contractive || f_equiv); apply Hwp.
Qed.

Local Definition wp_sk_def := fixpoint wp_sk_pre.
Local Definition wp_sk_aux : seal (@wp_sk_def). Proof. by eexists. Qed.
Definition wp_sk := wp_sk_aux.(unseal).
Local Lemma wp_sk_unseal   : wp_sk = @wp_sk_def.
Proof. rewrite -wp_sk_aux.(seal_eq) //. Qed.

Record postassert :=
  { Qnormal : iProp Σ; Qbreak : iProp Σ; Qcontinue : iProp Σ; Qreturn : val → iProp Σ }.

Definition guarded F E Q k R :=
  (Qnormal Q -∗ wp_sk F E Sskip k R) ∧
  (Qbreak Q -∗ ∃ e s k', ⌜find_loop k = Some (Kwhile e s k')⌝ ∧ wp_sk F E Sskip k' R) ∧
  (Qcontinue Q -∗ ∃ k', ⌜find_loop k = Some k'⌝ ∧ wp_sk F E Sskip k' R) ∧
  (∀ e, wp_expr E e (Qreturn Q) -∗ ∃ k', ⌜find_call k = Some k'⌝ ∧ wp_sk F E (Sreturn e) k' R).

End wp.