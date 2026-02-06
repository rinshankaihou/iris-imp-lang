(* wp for implang *)
From iris.base_logic Require Import gen_heap.
From iris_simp_lang Require Import implang imp_notation lifting_expr.

Section wp.

Context `{!gen_heapGS loc val Σ} `{!envGS val Σ} `{!invGS_gen HasNoLc Σ}.
Variable (F : func_env).

Implicit Types (ρ : @env_state val) (σ : gmap loc val).

Fixpoint make_stack (k : stack) : env_state * nat :=
  match k with
  | [] => (∅, O)
  | (r, _) :: k' => let '(ρ, n) := make_stack k' in (<[n := r]>ρ, S n)
  end.

Definition stack_depth k := snd (make_stack k).

Definition stack_match ρ r k := let '(ρ0, n) := make_stack k in (stack_level n ∗ ⌜ρ = <[n := r]>ρ0⌝)%I.

Lemma stack_env_match ρ r k : stack_match ρ r k ⊢ env_match ρ r.
Proof.
  unfold stack_match.
  destruct (make_stack k) eqn: Hk.
  unfold stack_level; split => ?; monPred.unseal.
  iIntros "(<- & ->)"; iPureIntro.
  by rewrite lookup_insert.
Qed.

Definition wp_pre (wp : coPset -d> stmt -d> assert -d> assert) :
    coPset -d> stmt -d> assert -d> assert := λ E s Q,
  ((⌜s = skip⌝ ∧ |={E}=> Q) ∨
   (∀ σ ρ, ⎡state_interp σ ρ⎤ ={E,∅}=∗ ∀ r k, stack_match ρ r k -∗ ∃ s' r' σ' k',
        ⌜step F s (Build_state r σ k) s' (Build_state r' σ' k')⌝ ∗
        ▷ |={∅,E}=> ∃ ρ', ⎡state_interp σ' ρ' ∗ (stack_match ρ' r' k' ∗ wp E s' Q) (stack_depth k')⎤))%I.

Local Instance wp_contractive : Contractive (wp_pre).
Proof.
  rewrite /wp_pre /= => n wp wp' Hwp E s Q.
  do 29 (f_contractive || f_equiv). apply Hwp.
Qed.

Local Definition wp_def := fixpoint wp_pre.
Local Definition wp_aux : seal (@wp_def). Proof. by eexists. Qed.
Definition wp := wp_aux.(unseal).
Local Lemma wp_unseal   : wp = @wp_def.
Proof. rewrite -wp_aux.(seal_eq) //. Qed.

Lemma wp_unfold E s Q : wp E s Q ⊣⊢ wp_pre wp E s Q.
Proof. rewrite wp_unseal. apply (fixpoint_unfold wp_pre). Qed.

Lemma wp_skip E Q : Q ⊢ wp E skip Q.
Proof.
  rewrite wp_unfold /wp_pre. iIntros. iLeft. iSplit; done.
Qed.

Lemma var_e : forall x v σ ρ r k,
  stack_match ρ r k ∗ x ↦v v ∗ ⎡state_interp σ ρ⎤ ⊢ ⌜r !! x = Some v⌝.
Proof.
  intros; rewrite /stack_match /stack_level;
  destruct (make_stack k) eqn: Hk.
  split => ?; monPred.unseal.
  iIntros "((-> & ->) & Hx & (_ & Hρ))".
  iDestruct (var_e with "[$Hx $Hρ]") as %?.
  by rewrite /env_to_environ lookup_insert in H.
Qed.

Lemma var_update : forall x v v' σ ρ r k,
  stack_match ρ r k ∗ x ↦v v ∗ ⎡state_interp σ ρ⎤ ⊢
  |==> ∃ ρ', stack_match ρ' (<[x := v']>r) k ∗ x ↦v v' ∗ ⎡state_interp σ ρ'⎤.
Proof.
  intros; rewrite /stack_match /stack_level;
  destruct (make_stack k) eqn: Hk.
  split => ?; monPred.unseal.
  iIntros "((-> & ->) & Hx & ($ & Hρ))".
  iMod (var_update with "[$Hx $Hρ]") as "($ & $)".
  iModIntro; iSplit; try done.
  rewrite /set_var lookup_insert insert_insert H //.
Qed.

Lemma stack_match_embed ρ r k (P : assert) : stack_match ρ r k -∗ P -∗
  ⎡(stack_match ρ r k ∗ P) (stack_depth k)⎤.
Proof.
  unfold stack_match, stack_depth.
  destruct (make_stack k).
  iIntros "(#? & %) P"; iApply stack_level_embed; by iFrame "# ∗".
Qed.

Lemma wp_assign E x e Q : wp_expr E e (λ v, (∃ v0, x ↦v v0) ∗
  ▷ (x ↦v v -∗ Q)) ⊢ wp E (Sassign x e) Q.
Proof.
  rewrite wp_unfold /wp_pre /stack_depth. iIntros "H". iRight.
  iIntros (??) "S".
  rewrite /wp_expr.
  iMod ("H" with "S") as (?) "(He & S & (% & Hx) & Hpost)".
  iApply fupd_mask_intro; first set_solver; iIntros "Hclose" (r k) "Hstack".
  iDestruct (var_e with "[$Hx $S $Hstack]") as %?.
  iDestruct ("He" with "[Hstack]") as %?; first by iApply stack_env_match.
  iExists _, _, _, _; iSplit.
  { iPureIntro; by constructor. }
  iNext.
  iMod (var_update with "[$Hx $S $Hstack]") as (?) "(match & ? & $)".
  iMod "Hclose"; iModIntro.
  simpl.
  iApply (stack_match_embed with "[$]").
  rewrite -wp_skip; by iApply "Hpost".
Qed.

Lemma wp_alloc E x Q : (∃ v0, x ↦v v0) ∗
  ▷ (∀ l, points_to_var x (LocV l) -∗ l ↦ NumV 0 -∗ Q) ⊢ wp E (Salloc x) Q.
Proof.
  rewrite wp_unfold /wp_pre. iIntros "H". iRight.
  iIntros (??) "S".
  iDestruct "H" as "((% & Hx) & Hpost)".
  iApply fupd_mask_intro; first set_solver; iIntros "Hclose" (??) "Hstack".
  iDestruct (var_e with "[$Hx $S $Hstack]") as %?.
  iExists _, _, _, _; iSplit.
  { iPureIntro; by apply alloc_fresh. }
  iNext.
  iMod (var_update with "[$Hx $S $Hstack]") as (?) "(? & Hx & S)".
  iMod (state_interp_alloc with "S") as "($ & S)".
  { apply not_elem_of_dom, fresh_locs_fresh. }
  iMod "Hclose"; iModIntro.
  iApply (stack_match_embed with "[$]").
  rewrite -wp_skip. by iApply ("Hpost" with "[$]").
Qed.

Lemma wp_store E e1 e2 Q : wp_expr E e2 (λ v, wp_expr E e1 (λ v1, ∃ l v0, ⌜v1 = LocV l⌝ ∧
  l ↦ v0 ∗ ▷ (l ↦ v -∗ Q))) ⊢ wp E (Sstore e1 e2) Q.
Proof.
  rewrite wp_unfold /wp_pre. iIntros "H". iRight.
  iIntros (??) "S".
  rewrite /wp_expr.
  iMod ("H" with "S") as (?) "(He2 & S & H)".
  iMod ("H" with "S") as (?) "(He1 & S & % & % & -> & Hl & Hpost)".
  iApply fupd_mask_intro; first set_solver; iIntros "Hclose" (??) "Hstack".
  iDestruct (state_interp_load with "S Hl") as %?.
  iDestruct ("He1" with "[Hstack]") as %?; first by iApply stack_env_match.
  iDestruct ("He2" with "[Hstack]") as %?; first by iApply stack_env_match.
  iExists _, _, _, _; iSplit.
  { iPureIntro; by econstructor. }
  iNext.
  iMod (state_interp_store with "S Hl") as "($ & ?)"; iFrame.
  iMod "Hclose"; iModIntro.
  iApply (stack_match_embed with "[$]").
  rewrite -wp_skip. by iApply "Hpost".
Qed.

Lemma wp_seq E s1 s2 Q : wp E s1 (▷ wp E s2 Q) ⊢ wp E (Sseq s1 s2) Q.
Proof.
  iIntros "H".
  iLöb as "IH" forall (s1 s2 Q).
  rewrite wp_unfold [wp _ (s1;;s2)%S _]wp_unfold /wp_pre. iRight.
  iIntros (??) "S".
  iDestruct "H" as "[[-> >Hs1] | H]".
  - iApply fupd_mask_intro; first set_solver; iIntros "Hclose" (??) "Hstack".
   iExists _, _, _, _. iSplit.
    { iPureIntro. apply SeqS2. }
    { iNext; iFrame.
      iApply (stack_match_embed with "[$]").
      by iMod "Hclose". }
  - iDestruct ("H" with "[$]") as ">H".
    iModIntro.
    iIntros (r k) "Hmatch".
    iDestruct ("H" with "[$Hmatch]") as (????) "(% & H)".
    iExists _, _, _, _.
    iSplit; first by (iPureIntro; econstructor).
    clear.
    iNext; iMod "H" as (ρ) "($ & Hs2)"; iModIntro.
Admitted.

Lemma wp_if E e s1 s2 Q : wp_expr E e (λ v, ∃ n, ⌜v = NumV n⌝ ∧
  ▷ wp E (if Z.eqb n 0 then s2 else s1) Q) ⊢ wp E (Sif e s1 s2) Q.
Proof.
  rewrite wp_unfold /wp_pre. iIntros "H". iRight.
  iIntros (??) "S".
  rewrite /wp_expr.
  iMod ("H" with "S") as (?) "(He & S & % & -> & H)".
  iApply fupd_mask_intro; first set_solver; iIntros "Hclose" (??) "Hstack".
  iDestruct ("He" with "[Hstack]") as %?; first by iApply stack_env_match.
  iExists _, _, _, _; iSplit.
  { iPureIntro; by econstructor. }
  iNext; iFrame.
  iApply (stack_match_embed with "[$]").
  by iMod "Hclose".
Qed.

Lemma wp_while E e s Q : wp_expr E e (λ v, ∃ n, ⌜v = NumV n⌝ ∧
  ▷ if Z.eqb n 0 then Q else wp E s (▷ wp E (Swhile e s) Q)) ⊢
  wp E (Swhile e s) Q.
Proof.
  rewrite [X in _ ⊢ X]wp_unfold /wp_pre. iIntros "H". iRight.
  iIntros (??) "S".
  rewrite /wp_expr.
  iMod ("H" with "S") as (?) "(He & S & % & -> & H)".
  iApply fupd_mask_intro; first set_solver; iIntros "Hclose" (??) "Hstack".
  iDestruct ("He" with "[Hstack]") as %?; first by iApply stack_env_match.
  destruct (Z.eqb n 0) eqn:?.
  -  iExists _, _, _, _; iSplit.
    { iPureIntro. econstructor; eauto. }
    iNext; iFrame.
    iMod "Hclose" as "_"; iModIntro.
    rewrite Heqb -wp_skip //.
    by iApply (stack_match_embed with "[$]").
  - iExists _, _, _, _; iSplit.
    { iPureIntro; econstructor; eauto. }
    iNext; iFrame.
    iMod "Hclose" as "_"; iModIntro.
    rewrite Heqb -wp_seq //.
    by iApply (stack_match_embed with "[$]").
Qed.

End wp.
