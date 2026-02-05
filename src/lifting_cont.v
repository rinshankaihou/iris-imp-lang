From iris.base_logic Require Import gen_heap.
From iris_simp_lang Require Import imp_cont_notation stack_ra lifting_expr.

Section wp.

Context `{!gen_heapGS loc val Σ} `{!envGS val Σ} `{!invGS_gen HasNoLc Σ}.

Variable (F : func_env).

Fixpoint cont_to_stack k : env_state * nat :=
  match k with
  | Kstop => (∅, O)
  | Kcall _ r k' => let '(ρ, n) := cont_to_stack k' in (<[n := r]>ρ, S n)
  | Kseq _ k' | Kwhile _ _ k' => cont_to_stack k'
  end.

Definition stack_match ρ r k := assert_of (λ n, ⌜let '(ρ0, n0) := cont_to_stack k in n = n0 ∧ ρ = <[n := r]>ρ0⌝)%I.

Lemma stack_env_match ρ r k : stack_match ρ r k ⊢ env_match ρ r.
Proof.
  split => n /=; apply bi.pure_mono.
  destruct (cont_to_stack k); intros (_ & ->); by rewrite lookup_insert.
Qed.

Definition wp_sk_pre (wp : coPset -d> stmt -d> cont -d> assert -d> assert) :
    coPset -d> stmt -d> cont -d> assert -d> assert := λ E s k Q,
 ((⌜s = Sskip ∧ k = Kstop⌝ ∗ |={E}=> Q) ∨
  ∀ σ ρ, state_interp σ ρ ={E,∅}=∗ ∀ r, stack_match ρ r k -∗ ∃ s' r' σ' k',
        ⌜step F s (Build_state r σ k) s' (Build_state r' σ' k')⌝ ∗
        ▷ |={∅,E}=> ∃ ρ', state_interp σ' ρ' ∗ stack_match ρ' r' k' ∗ wp E s' k' Q)%I.

Local Instance wp_sk_pre_contractive : Contractive (wp_sk_pre).
Proof.
  rewrite /wp_sk_pre /= => n wp wp' Hwp E s k Q.
  do 25 (f_contractive || f_equiv); apply Hwp.
Qed.

Local Definition wp_sk_def := fixpoint wp_sk_pre.
Local Definition wp_sk_aux : seal (@wp_sk_def). Proof. by eexists. Qed.
Definition wp_sk := wp_sk_aux.(unseal).
Local Lemma wp_sk_unseal   : wp_sk = @wp_sk_def.
Proof. rewrite -wp_sk_aux.(seal_eq) //. Qed.

Lemma wp_sk_unfold E s k Q : wp_sk E s k Q ⊣⊢ wp_sk_pre wp_sk E s k Q.
Proof. rewrite wp_sk_unseal. apply (fixpoint_unfold wp_sk_pre). Qed.

Record postassert :=
  { Qnormal : assert; Qbreak : assert; Qcontinue : assert; Qreturn : val → assert }.

Definition guarded E Q k R :=
  ((Qnormal Q -∗ wp_sk E Sskip k R) ∧
   (Qbreak Q -∗ ∃ e s k', ⌜find_loop k = Some (Kwhile e s k')⌝ ∧ wp_sk E Sskip k' R) ∧
   (Qcontinue Q -∗ ∃ k', ⌜find_loop k = Some k'⌝ ∧ wp_sk E Sskip k' R) ∧
   (∀ e, wp_expr E e (Qreturn Q) -∗ ∃ k', ⌜find_call k = Some k'⌝ ∧ wp_sk E (Sreturn e) k' R))%I.

Definition wp E s Q := (∀ k R, guarded E Q k R -∗ wp_sk E s k R)%I.

Lemma wp_skip E Q : Qnormal Q ⊢ wp E skip Q.
Proof.
  iIntros "H %% Hguard"; by iApply "Hguard".
Qed.

Lemma var_e : forall x v σ ρ r k, points_to_var x v ∗ state_interp σ ρ ∗ stack_match ρ r k ⊢ ⌜r !! x = Some v⌝.
Proof.
  intros; rewrite /state_interp; split => n; monPred.unseal.
  iIntros "(Hx & (_ & Hρ) & Hmatch)".
  iDestruct (var_e with "[$Hx $Hρ]") as %?.
  destruct (cont_to_stack k) eqn: Hk; iDestruct "Hmatch" as %(<- & ->).
  by rewrite /env_to_environ lookup_insert in H.
Qed.

Lemma var_update : forall x v v' σ ρ r k, points_to_var x v ∗ state_interp σ ρ ∗ stack_match ρ r k ⊢
  |==> ∃ ρ', points_to_var x v' ∗ state_interp σ ρ' ∗ stack_match ρ' (<[x := v']>r) k.
Proof.
  intros; rewrite /state_interp; split => n; monPred.unseal.
  iIntros "(Hx & ($ & Hρ) & Hmatch)".
  iMod (var_update with "[$Hx $Hρ]") as "($ & $)".
  iModIntro; iStopProof; apply bi.pure_mono.
  destruct (cont_to_stack k) eqn: Hk; intros (<- & ->).
  rewrite /set_var lookup_insert insert_insert //.
Qed.

Lemma wp_assign E x e Q : wp_expr E e (λ v, (∃ v0, points_to_var x v0) ∗
  (points_to_var x v -∗ Qnormal Q)) ⊢ wp E (Sassign x e) Q.
Proof.
  iIntros "H %% Hguard".
  rewrite wp_sk_unfold /wp_sk_pre; iRight.
  iIntros (??) "S".
  rewrite /wp_expr.
  iMod ("H" with "S") as (?) "(He & S & (% & Hx) & Hpost)".
  iApply fupd_mask_intro; first set_solver; iIntros "Hclose" (?) "Hstack".
  iDestruct (var_e with "[$Hx $S $Hstack]") as %?.
  iDestruct ("He" with "[Hstack]") as %?; first by iApply stack_env_match.
  iExists _, _, _, _; iSplit.
  { iPureIntro; by constructor. }
  iNext.
  iMod (var_update with "[$Hx $S $Hstack]") as (?) "(Hx & $ & $)".
  iMod "Hclose"; iModIntro.
  by iApply "Hguard"; iApply "Hpost".
Qed.

Lemma wp_alloc E x Q : (∃ v0, points_to_var x v0) ∗
  (∀ l, points_to_var x (LocV l) -∗ l ↦ NumV 0 -∗ Qnormal Q) ⊢ wp E (Salloc x) Q.
Proof.
  iIntros "H %% Hguard".
  rewrite wp_sk_unfold /wp_sk_pre; iRight.
  iIntros (??) "S".
  iDestruct "H" as "((% & Hx) & Hpost)".
  iApply fupd_mask_intro; first set_solver; iIntros "Hclose" (?) "Hstack".
  iDestruct (var_e with "[$Hx $S $Hstack]") as %?.
  iExists _, _, _, _; iSplit.
  { iPureIntro; by apply alloc_fresh. }
  iNext.
  iMod (var_update with "[$Hx $S $Hstack]") as (?) "(Hx & S & $)".
  iMod (state_interp_alloc with "S") as "($ & ?)".
  { apply not_elem_of_dom, fresh_locs_fresh. }
  iMod "Hclose"; iModIntro.
  by iApply "Hguard"; iApply ("Hpost" with "[$]").
Qed.

Lemma wp_store E e1 e2 Q : wp_expr E e2 (λ v, wp_expr E e1 (λ v1, ∃ l v0, ⌜v1 = LocV l⌝ ∧
  l ↦ v0 ∗ (l ↦ v -∗ Qnormal Q))) ⊢ wp E (Sstore e1 e2) Q.
Proof.
  iIntros "H %% Hguard".
  rewrite wp_sk_unfold /wp_sk_pre; iRight.
  iIntros (??) "S".
  rewrite /wp_expr.
  iMod ("H" with "S") as (?) "(He2 & S & H)".
  iMod ("H" with "S") as (?) "(He1 & S & % & % & -> & Hl & Hpost)".
  iApply fupd_mask_intro; first set_solver; iIntros "Hclose" (?) "Hstack".
  iDestruct (state_interp_load with "S Hl") as %?.
  iDestruct ("He1" with "[Hstack]") as %?; first by iApply stack_env_match.
  iDestruct ("He2" with "[Hstack]") as %?; first by iApply stack_env_match.
  iExists _, _, _, _; iSplit.
  { iPureIntro; by econstructor. }
  iNext.
  iMod (state_interp_store with "S Hl") as "($ & ?)"; iFrame.
  iMod "Hclose"; iModIntro.
  by iApply "Hguard"; iApply "Hpost".
Qed.

End wp.