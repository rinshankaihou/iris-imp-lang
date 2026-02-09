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

Definition stack_depth k := snd (cont_to_stack k).

Definition stack_match ρ r k := let '(ρ0, n) := cont_to_stack k in (stack_level n ∗ ⌜ρ = <[n := r]>ρ0⌝)%I.

Lemma stack_env_match ρ r k : stack_match ρ r k ⊢ env_match ρ r.
Proof.
  unfold stack_match.
  destruct (cont_to_stack k) eqn: Hk.
  unfold stack_level; split => ?; monPred.unseal.
  iIntros "(<- & ->)"; iPureIntro.
  by rewrite lookup_insert.
Qed.

Lemma stack_match_embed ρ r k (P : assert) : stack_match ρ r k -∗ P -∗
  ⎡(stack_match ρ r k ∗ P) (stack_depth k)⎤.
Proof.
  unfold stack_match, stack_depth.
  destruct (cont_to_stack k).
  iIntros "(#? & %) P"; iApply stack_level_embed; by iFrame "# ∗".
Qed.

Definition wp_sk_pre (wp : coPset -d> stmt -d> cont -d> assert -d> assert) :
    coPset -d> stmt -d> cont -d> assert -d> assert := λ E s k Q,
 ((⌜s = Sskip ∧ k = Kstop⌝ ∗ |={E}=> Q) ∨
  ∀ σ ρ, ⎡state_interp σ ρ⎤ ={E,∅}=∗ ∀ r, stack_match ρ r k -∗ ∃ s' r' σ' k',
        ⌜step F s (Build_state r σ k) s' (Build_state r' σ' k')⌝ ∗
        ▷ |={∅,E}=> ∃ ρ', ⎡state_interp σ' ρ' ∗ (stack_match ρ' r' k' ∗ wp E s' k' Q) (stack_depth k')⎤)%I.

Local Instance wp_sk_pre_contractive : Contractive (wp_sk_pre).
Proof.
  rewrite /wp_sk_pre /= => n wp wp' Hwp E s k Q.
  do 27 (f_contractive || f_equiv); apply Hwp.
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
   (∀ e, wp_expr E e (Qreturn Q) -∗ wp_sk E (Sreturn e) (find_call k) R))%I.

Definition wp E s Q := (∀ k R, guarded E Q k R -∗ wp_sk E s k R)%I.

Lemma wp_skip E Q : Qnormal Q ⊢ wp E skip Q.
Proof.
  iIntros "H %% Hguard"; by iApply "Hguard".
Qed.

Lemma var_e : forall x v σ ρ r k,
  stack_match ρ r k ∗ points_to_var x v ∗ ⎡state_interp σ ρ⎤ ⊢ ⌜r !! x = Some v⌝.
Proof.
  intros; rewrite /stack_match /stack_level.
  destruct (cont_to_stack k) eqn: Hk.
  split => ?; monPred.unseal.
  iIntros "((<- & ->) & Hx & (_ & Hρ))".
  iDestruct (var_e with "[$Hx $Hρ]") as %Hr.
  by rewrite /env_to_environ lookup_insert in Hr.
Qed.

Lemma var_update : forall x v v' σ ρ r k,
  stack_match ρ r k ∗ points_to_var x v ∗ ⎡state_interp σ ρ⎤ ⊢
  |==> ∃ ρ', stack_match ρ' (<[x := v']>r) k ∗ points_to_var x v' ∗ ⎡state_interp σ ρ'⎤.
Proof.
  intros; rewrite /stack_match /stack_level.
  destruct (cont_to_stack k) eqn: Hk.
  split => ?; monPred.unseal.
  iIntros "((%Hl & ->) & Hx & ($ & Hρ))"; hnf in Hl; subst.
  iMod (var_update with "[$Hx $Hρ]") as "($ & $)".
  iPureIntro.
  rewrite /set_var lookup_insert insert_insert //.
Qed.

Lemma wp_assign E x e Q : wp_expr E e (λ v, (∃ v0, points_to_var x v0) ∗
  ▷ (points_to_var x v -∗ Qnormal Q)) ⊢ wp E (Sassign x e) Q.
Proof.
  iIntros "H %% Hguard".
  rewrite wp_sk_unfold /wp_sk_pre; iRight.
  iIntros (??) "S".
  rewrite /wp_expr.
  iMod ("H" with "S") as (?) "(He & S & (% & Hx) & Hpost)".
  iApply fupd_mask_intro; first set_solver; iIntros "Hclose" (?) "Hstack".
  iDestruct (var_e with "[$Hstack $Hx $S]") as %?.
  iDestruct ("He" with "[Hstack]") as %?; first by iApply stack_env_match.
  iExists _, _, _, _; iSplit.
  { iPureIntro; by constructor. }
  iNext; simpl.
  iMod (var_update with "[$Hstack $Hx $S]") as (?) "(? & Hx & $)".
  iMod "Hclose"; iModIntro.
  iApply (stack_match_embed with "[$]").
  by iApply "Hguard"; iApply "Hpost".
Qed.

Lemma wp_alloc E x Q : (∃ v0, points_to_var x v0) ∗
  ▷ (∀ l, points_to_var x (LocV l) -∗ l ↦ NumV 0 -∗ Qnormal Q) ⊢ wp E (Salloc x) Q.
Proof.
  iIntros "H %% Hguard".
  rewrite wp_sk_unfold /wp_sk_pre; iRight.
  iIntros (??) "S".
  iDestruct "H" as "((% & Hx) & Hpost)".
  iApply fupd_mask_intro; first set_solver; iIntros "Hclose" (?) "Hstack".
  iDestruct (var_e with "[$Hx $S $Hstack]") as %?.
  iExists _, _, _, _; iSplit.
  { iPureIntro; by apply alloc_fresh. }
  iNext; simpl.
  iMod (var_update with "[$Hx $S $Hstack]") as (?) "(? & Hx & S)".
  iMod (state_interp_alloc with "S") as "($ & ?)".
  { apply not_elem_of_dom, fresh_locs_fresh. }
  iMod "Hclose"; iModIntro.
  iApply (stack_match_embed with "[$]").
  by iApply "Hguard"; iApply ("Hpost" with "[$]").
Qed.

Lemma wp_store E e1 e2 Q : wp_expr E e2 (λ v, wp_expr E e1 (λ v1, ∃ l v0, ⌜v1 = LocV l⌝ ∧
  l ↦ v0 ∗ ▷ (l ↦ v -∗ Qnormal Q))) ⊢ wp E (Sstore e1 e2) Q.
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
  iApply (stack_match_embed with "[$]").
  by iApply "Hguard"; iApply "Hpost".
Qed.

Definition set_normal Q R :=
  {| Qnormal := R; Qbreak := Qbreak Q; Qcontinue := Qcontinue Q; Qreturn := Qreturn Q |}.

Lemma wp_seq E s1 s2 Q : ▷ wp E s1 (set_normal Q (▷ wp E s2 Q)) ⊢ wp E (Sseq s1 s2) Q.
Proof.
  iIntros "H %% Hguard".
  rewrite wp_sk_unfold /wp_sk_pre; iRight.
  iIntros (??) "S".
  iApply fupd_mask_intro; first set_solver; iIntros "Hclose" (?) "Hstack".
  iExists _, _, _, _; iSplit.
  { iPureIntro; by econstructor. }
  iNext; iFrame.
  iMod "Hclose" as "_"; iModIntro.
  iApply (stack_match_embed with "[$]").
  iApply "H".
  rewrite /guarded.
  iSplit => /=; last by iDestruct "Hguard" as "[_ $]".
  iIntros "H"; rewrite (wp_sk_unfold _ _ (Kseq _ _)) /wp_sk_pre; iRight.
  iIntros (??) "S".
  iApply fupd_mask_intro; first set_solver; iIntros "Hclose" (?) "Hstack".
  iExists _, _, _, _; iSplit.
  { iPureIntro; by econstructor. }
  iNext; iFrame.
  iMod "Hclose" as "_"; iModIntro.
  iApply (stack_match_embed with "[$]").
  by iApply "H".
Qed.

Lemma wp_if E e s1 s2 Q : wp_expr E e (λ v, ∃ n, ⌜v = NumV n⌝ ∧
  ▷ wp E (if Z.eqb n 0 then s2 else s1) Q) ⊢ wp E (Sif e s1 s2) Q.
Proof.
  iIntros "H %% Hguard".
  rewrite wp_sk_unfold /wp_sk_pre; iRight.
  iIntros (??) "S".
  rewrite /wp_expr.
  iMod ("H" with "S") as (?) "(He & S & % & -> & H)".
  iApply fupd_mask_intro; first set_solver; iIntros "Hclose" (?) "Hstack".
  iDestruct ("He" with "[Hstack]") as %?; first by iApply stack_env_match.
  iExists _, _, _, _; iSplit.
  { iPureIntro; by econstructor. }
  iNext; iFrame.
  iMod "Hclose" as "_"; iModIntro.
  iApply (stack_match_embed with "[$]").
  by iApply "H".
Qed.

Definition loop_post Q R :=
  {| Qnormal := R; Qbreak := Qnormal Q; Qcontinue := R; Qreturn := Qreturn Q |}.

Lemma wp_while E e s Q : wp_expr E e (λ v, ∃ n, ⌜v = NumV n⌝ ∧
  ▷ if Z.eqb n 0 then Qnormal Q else wp E s (loop_post Q (▷ wp E (Swhile e s) Q))) ⊢
  wp E (Swhile e s) Q.
Proof.
  iIntros "H %% Hguard".
  rewrite wp_sk_unfold /wp_sk_pre; iRight.
  iIntros (??) "S".
  rewrite /wp_expr.
  iMod ("H" with "S") as (?) "(He & S & % & -> & H)".
  iApply fupd_mask_intro; first set_solver; iIntros "Hclose" (?) "Hstack".
  iDestruct ("He" with "[Hstack]") as %?; first by iApply stack_env_match.
  destruct (Z.eqb_spec n 0).
  - subst; iExists _, _, _, _; iSplit.
    { iPureIntro; by apply WhileFS. }
    iNext; iFrame.
    iMod "Hclose" as "_"; iModIntro.
    iApply (stack_match_embed with "[$]").
    by iApply "Hguard".
  - iExists _, _, _, _; iSplit.
    { iPureIntro; by eapply WhileTS. }
    iNext; iFrame.
    iMod "Hclose" as "_"; iModIntro.
    iApply (stack_match_embed with "[$]").
    iApply "H".
    rewrite /guarded.
    iSplit; [|iSplit; [|iSplit]]; simpl.
    + iIntros "H"; rewrite (wp_sk_unfold _ _ (Kwhile _ _ _)) /wp_sk_pre; iRight.
      iIntros (??) "S".
      iApply fupd_mask_intro; first set_solver; iIntros "Hclose" (?) "Hstack".
      iExists _, _, _, _; iSplit.
      { iPureIntro; by econstructor. }
      iNext; iFrame.
      iMod "Hclose" as "_"; iModIntro.
      iApply (stack_match_embed with "[$]").
      by iApply "H".
    + iIntros "H"; iExists _, _, _; iSplit => //.
      by iApply "Hguard".
    + iIntros "H"; iExists _; iSplit => //.
      rewrite (wp_sk_unfold _ _ (Kwhile _ _ _)) /wp_sk_pre; iRight.
      iIntros (??) "S".
      iApply fupd_mask_intro; first set_solver; iIntros "Hclose" (?) "Hstack".
      iExists _, _, _, _; iSplit.
      { iPureIntro; by econstructor. }
      iNext; iFrame.
      iMod "Hclose" as "_"; iModIntro.
      iApply (stack_match_embed with "[$]").
      by iApply "H".
    + iDestruct "Hguard" as "(_ & _ & _ & $)".
Qed.

Lemma cont_to_stack_loop k e s k' : find_loop k = Some (Kwhile e s k') →
  cont_to_stack k = cont_to_stack k'.
Proof.
  induction k; try done; simpl.
  by inversion 1.
Qed.

Lemma stack_match_loop ρ r k e s k' : find_loop k = Some (Kwhile e s k') →
  stack_match ρ r k ⊢ stack_match ρ r k'.
Proof.
  intros. rewrite /stack_match /stack_level.
  rewrite -(cont_to_stack_loop _ _ _ _ H) //.
Qed.

Lemma wp_break E Q : Qbreak Q ⊢ wp E Sbreak Q.
Proof.
  iIntros "H %% Hguard".
  iDestruct "Hguard" as "(_ & Hguard & _)".
  iDestruct ("Hguard" with "H") as (????) "H".
  rewrite (wp_sk_unfold _ Sbreak) /wp_sk_pre; iRight.
  iIntros (??) "S".
  iApply fupd_mask_intro; first set_solver; iIntros "Hclose" (?) "Hstack".
  iExists _, _, _, _; iSplit.
  { iPureIntro; by econstructor. }
  iNext; iFrame.
  iMod "Hclose" as "_"; iModIntro.
  rewrite stack_match_loop //.
  by iApply (stack_match_embed with "[$]"). 
Qed.

Lemma find_loop_while k k' : find_loop k = Some k' → ∃ el sl kl, k' = Kwhile el sl kl.
Proof.
  induction k; try done; simpl.
  inversion 1; eauto.
Qed.

Lemma cont_to_stack_loop' k k' : find_loop k = Some k' →
  cont_to_stack k = cont_to_stack k'.
Proof.
  induction k; try done; simpl.
  by inversion 1.
Qed.

Lemma stack_match_loop' ρ r k k' : find_loop k = Some k' →
  stack_match ρ r k ⊢ stack_match ρ r k'.
Proof.
  split => n. rewrite /stack_match /stack_level.
  rewrite -(cont_to_stack_loop' _ _ H) //.
Qed.

Lemma wp_continue E Q : Qcontinue Q ⊢ wp E Scontinue Q.
Proof.
  iIntros "H %% Hguard".
  iDestruct "Hguard" as "(_ & _ & Hguard & _)".
  iDestruct ("Hguard" with "H") as (? Hk') "H".
  edestruct find_loop_while as (? & ? & ? & ?); first done; subst.
  rewrite (wp_sk_unfold _ Scontinue) /wp_sk_pre; iRight.
  iIntros (??) "S".
  iApply fupd_mask_intro; first set_solver; iIntros "Hclose" (?) "Hstack".
  iExists _, _, _, _; iSplit.
  { iPureIntro; by econstructor. }
  iNext; iFrame.
  iMod "Hclose" as "_"; iModIntro.
  rewrite stack_match_loop' //.
  by iApply (stack_match_embed with "[$]").
Qed.

Definition get_params f := let 'Func params _ _ := f in params.
Definition get_locals f := let 'Func _ locals _ := f in locals.
Definition get_body f := let 'Func _ _ body := f in body.

Definition stack_size f := let 'Func params locals _ := f in
  (length params + length locals)%nat.

Definition stack_frac f := (/ pos_to_Qp (Pos.of_nat (1 + stack_size f)))%Qp.

Definition stack_retainer f := assert_of (λ n,
  stack_frag n (stack_frac f) (stack_frac f) ∅).

Definition stackframe f vs := ([∗ list] x;v ∈ (get_params f ++ get_locals f);vs, points_to_var x v)%I.

Definition ret_post R :=
  {| Qnormal := False%I; Qbreak := False%I; Qcontinue := False%I; Qreturn := R |}.

Definition call_assert E f vs x R := (⇑ (stack_retainer f -∗ stackframe f vs -∗
  wp E (get_body f) (ret_post (λ v, stack_retainer f ∗
    (∃ vs, ⌜stack_size f = length vs⌝ ∧ stackframe f vs) ∗
    ⇓ ((∃ v, points_to_var x v) ∗ ▷ (points_to_var x v -∗ R))))))%I.

Lemma wp_exprs_app E es Q σ ρ : wp_exprs E es Q -∗ ⎡state_interp σ ρ⎤ ={E}=∗
  ∃ vs, (∀ r k, env_match ρ r -∗ ⌜eval_exprs' es (Build_state r σ k) vs⌝) ∗ ⎡state_interp σ ρ⎤ ∗ Q vs.
Proof.
  iIntros "Hes S"; iInduction es as [|e es] "IH" forall (Q); simpl.
  - iFrame. iIntros "!> %% ?"; iPureIntro; constructor.
  - rewrite /wp_expr.
    iMod ("Hes" with "S") as (?) "(He & S & Hes)".
    iMod ("IH" with "Hes S") as (?) "(Hes & $ & $)".
    iIntros "!> %% Henv".
    iDestruct ("He" with "Henv") as %?; iDestruct ("Hes" $! _ k with "Henv") as %?.
    iPureIntro; by constructor.
Qed.

Lemma stack_depth_max : forall k ρ n, cont_to_stack k = (ρ, n) → ∀ m, n ≤ m → ρ !! m = None.
Proof.
  induction k; simpl; try done.
  - inversion 1; intros; by rewrite lookup_empty.
  - destruct (cont_to_stack k) eqn: Hk; inversion 1; subst; intros.
    rewrite lookup_insert_ne; last lia.
    eapply IHk; eauto; lia.
Qed.

Lemma add_frame σ ρ r k x xs vs : ⎡state_interp σ ρ⎤ ∗ stack_match ρ r k ⊢
  |==> ∃ ρ', ⎡state_interp σ ρ'⎤ ∗ ⇑ (stack_match ρ' (bind_vars xs vs) (Kcall x r k) ∗
    assert_of (λ n, stack_frag n (/ pos_to_Qp (Pos.of_nat (1 + size (bind_vars xs vs))))%Qp 1%Qp (bind_vars xs vs))).
Proof.
  intros; rewrite /stack_match /=.
  destruct (cont_to_stack k) eqn: Hk.
  iIntros "(Hρ & #Hl & ->)".
  iMod (state_interp_alloc_frame _ _ (S n) with "Hρ") as "($ & ?)".
  { rewrite lookup_insert_ne //.
    eapply stack_depth_max; eauto. }
  iModIntro.
  rewrite -!up1_sep.
  iPoseProof (stack_level_up with "Hl") as "$".
  rewrite -up1_objective; iSplit; first done.
  iStopProof; split => ?; rewrite /stack_level; monPred.unseal; rewrite monPred_at_intuitionistically /=.
  iIntros "((<- & _) & $)".
Qed.

Lemma monPred_at_big_sepL2 : forall {I : biIndex} {PROP : bi} {A B} (Φ : A → B → monPred I PROP) (l1 : list A) (l2 : list B) n,
  (([∗ list] a1;a2 ∈ l1;l2, Φ a1 a2) n) ⊣⊢ ([∗ list] a1;a2 ∈ l1;l2, Φ a1 a2 n).
Proof.
  induction l1; destruct l2; simpl; intros; monPred.unseal; try done.
  rewrite IHl1 //.
Qed.

Lemma split_stackframe params locals body vs :
  length (params ++ locals) = length vs → NoDup (params ++ locals) →
  let r' := bind_vars (params ++ locals) vs in
  assert_of (λ n, stack_frag n (/ pos_to_Qp (Pos.of_nat (1 + size r')))%Qp 1%Qp r') ⊣⊢
  stack_retainer (Func params locals body) ∗ stackframe (Func params locals body) vs.
Proof.
  split => n /=; rewrite /stack_retainer /stackframe; monPred.unseal.
  rewrite monPred_at_big_sepL2 vars_equiv //.
  case_decide.
  - destruct params; last done; destruct locals; last done; rewrite /bind_vars /stack_frac /= bi.sep_emp.
    by rewrite map_size_empty Qp.inv_1.
  - rewrite /stack_frac /=.
    replace (size _) with (length (params ++ locals)).
    rewrite -app_length.
    iSplit.
    + rewrite Nat2Pos.inj_succ // Pplus_one_succ_l -pos_to_Qp_add.
      set (q := (1 + _)%Qp).
      rewrite -(Qp.mul_inv_r q).
      destruct (q - 1)%Qp eqn: Hq.
      apply Qp.sub_Some in Hq; rewrite {2} Hq Qp.mul_add_distr_r -frac_op.
      rewrite -{1}(map_empty_union (bind_vars _ _)) stack_frag_split.
      rewrite Qp.mul_1_l; iIntros "($ & ?)".
      iExists _; iStopProof; f_equiv; try done.
      * apply Qp.add_inj_r in Hq as <-; done.
      * apply map_disjoint_empty_l.
      * by apply Qp.sub_None, Qp.not_add_le_l in Hq.
    + iIntros "(Hret & % & H)".
      iDestruct (stack_frag_join with "[$Hret $H]") as ((<- & _)) "H".
      rewrite !left_id Nat2Pos.inj_succ // Pplus_one_succ_l -pos_to_Qp_add.
      set (q := (1 + _)%Qp).
      by rewrite -{2}(Qp.mul_1_l (/ q)) -Qp.mul_add_distr_r Qp.mul_inv_r.
    + rewrite map_size_list_to_map; last by rewrite fst_zip; try lia.
      rewrite length_zip_with_l_eq //.
Qed.

Lemma remove_frame σ ρ r x r0 k q r' : ⎡state_interp σ ρ⎤ ∗ stack_match ρ r (Kcall x r0 k) ∗ assert_of (λ n, stack_frag n q 1%Qp r') ⊢
  |==> ∃ ρ', ⎡state_interp σ ρ'⎤ ∗ ⇓ stack_match ρ' r0 k.
Proof.
  intros; rewrite /stack_match /=.
  destruct (cont_to_stack k) eqn: Hk.
  iIntros "(Hρ & (#Hl & ->) & H)".
  iMod (state_interp_dealloc_frame _ _ (S n) with "[$Hρ H]") as "$".
  { iApply (stack_level_embed with "Hl H"). }
  iModIntro.
  rewrite -!down1_sep.
  iPoseProof (stack_level_down with "Hl") as "$".
  rewrite -down1_objective; iPureIntro.
  apply (delete_insert _ _ r).
  rewrite lookup_insert_ne //; eapply stack_depth_max; eauto.
Qed.

Lemma wp_call E x f es Q : wp_exprs E es (λ vs, ∃ fd, ⌜F !! f = Some fd ∧
    length es = length (get_params fd) ∧ NoDup (get_params fd ++ get_locals fd)⌝ ∧
  ▷ call_assert E fd (vs ++ repeat (NumV 0) (length (get_locals fd))) x (Qnormal Q)) ⊢
  wp E (Scall x f es) Q.
Proof.
  iIntros "H %% Hguard".
  rewrite wp_sk_unfold /wp_sk_pre; iRight.
  iIntros (??) "S".
  iMod (wp_exprs_app with "H S") as (?) "(Hes & S & %fd & (% & %Hlen & %) & H)".
  destruct fd; simpl in *.
  iApply fupd_mask_intro; first set_solver; iIntros "Hclose" (?) "Hstack".
  iDestruct ("Hes" with "[Hstack]") as %?; first by iApply stack_env_match.
  iExists _, _, _, _; iSplit.
  { iPureIntro; by econstructor. }
  iNext.
  iMod (add_frame with "[$S $Hstack]") as (?) "($ & Hstack)".
  iMod "Hclose" as "_"; iModIntro; simpl.
  iApply up1_obj_elim; iApply up1_mono; last first.
  { rewrite -(up1_down1 (guarded _ _ _ _)) /call_assert.
    iCombine "Hguard H Hstack" as "H"; rewrite !up1_sep; iApply "H". }
  iIntros "(Hguard & H & Hstack & Hframe)".
  iApply (stack_match_embed with "Hstack").
  assert (length (func_params ++ func_locals) = length (vs ++ repeat (NumV 0) (length func_locals))).
  { rewrite !app_length repeat_length; f_equal.
    rewrite -Hlen; by eapply Forall2_length. }
  rewrite split_stackframe //; iDestruct "Hframe" as "(Hret & Hframe)".
  iApply ("H" with "Hret Hframe").
  do 3 (iSplit; first iIntros "[]").
  iIntros (?) "He"; simpl.
  clear dependent σ; rewrite wp_sk_unfold /wp_sk_pre; iRight.
  iIntros (??) "S".
  rewrite /wp_expr.
  iMod ("He" with "S") as (?) "(He & S & Hret & (% & % & Hframe) & Hpost)".
  iApply fupd_mask_intro; first set_solver; iIntros "Hclose" (?) "Hstack".
  iDestruct ("He" with "[Hstack]") as %?; first by iApply stack_env_match.
  iExists _,_, _, _; iSplit.
  { iPureIntro; by econstructor. }
  rewrite -down1_sep down1_later.
  iNext.
  iMod (remove_frame with "[$S $Hstack Hret Hframe]") as (?) "(S & Hstack)".
  { iCombine "Hret Hframe" as "H"; rewrite -split_stackframe //.
    rewrite app_length //. }
  iDestruct "Hpost" as "(Hx & Hpost)".
  iAssert (⇓ |==> ∃ ρ', stack_match ρ' (<[x:=v]> r) k ∗ x ↦v v ∗ ⎡state_interp σ ρ'⎤)%I
    with "[S Hx Hstack]" as "H'".
  { rewrite (down1_objective ⎡_⎤%I).
    iCombine "Hstack Hx S" as "H"; rewrite !down1_sep; iApply (down1_mono with "H").
    iIntros "(? & (% & ?) & ?)"; iApply var_update; iFrame. }
  rewrite down1_bupd; iMod "H'".
  rewrite down1_exist; iDestruct "H'" as (?) "H'".
  iMod "Hclose"; iModIntro.
  iExists _; iApply down1_obj_elim; iApply down1_mono; last first.
  { iCombine "Hguard Hpost H'" as "H"; rewrite !down1_sep; iApply "H". }
  iIntros "(Hguard & H & ? & ? & $)"; iApply (stack_match_embed with "[$]").
  by iApply "Hguard"; iApply "H".
Qed.

Lemma find_call_idem k : find_call (find_call k) = find_call k.
Proof.
  by induction k.
Qed.

Lemma cont_to_stack_call k : cont_to_stack k = cont_to_stack (find_call k).
Proof.
  by induction k.
Qed.

Lemma stack_match_call ρ r k :
  stack_match ρ r k ⊢ stack_match ρ r (find_call k).
Proof.
  intros.
  rewrite /stack_match /stack_level cont_to_stack_call //.
Qed.

Lemma wp_return E e Q : wp_expr E e (Qreturn Q) ⊢ wp E (Sreturn e) Q.
Proof.
  iIntros "H %% Hguard".
  iDestruct "Hguard" as "(_ & _ & _ & Hguard)".
  iSpecialize ("Hguard" with "H").
  iStopProof.
  rewrite !wp_sk_unfold /wp_sk_pre; do 3 f_equiv.
  { by intros (? & ?). }
  do 7 f_equiv.
  - by apply stack_match_call.
  - do 10 f_equiv.
    inversion 1; subst; constructor; auto; simpl in *.
    by rewrite -> find_call_idem in *.
Qed.

End wp.

Section adequacy.

(* generalize? *)
Definition not_stuck F s σ := (s = skip ∧ σ.(k) = Kstop) ∨
  (∃ s' σ', step F s σ s' σ').

Record adequate F s (σ1 : state) (φ : state → Prop) := {
  adequate_result σ2 : σ2.(k) = Kstop →
   step_star F s σ1 skip σ2 → φ σ2;
  adequate_not_stuck s2 σ2 :
   step_star F s σ1 s2 σ2 →
   not_stuck F s2 σ2
}.

Lemma adequate_alt F s1 σ1 (φ : state → Prop) :
  adequate F s1 σ1 φ ↔ ∀ s2 σ2,
    step_star F s1 σ1 s2 σ2 →
      ((s2 = skip ∧ σ2.(k) = Kstop) → φ σ2) ∧
      (not_stuck F s2 σ2).
Proof.
  split.
  - intros []; naive_solver.
  - constructor; naive_solver.
Qed.

Inductive nsteps (F : func_env) : nat → stmt → state → stmt → state → Prop :=
  | nsteps_refl s σ :
     nsteps F 0 s σ s σ
  | nsteps_l n s1 σ1 s2 σ2 s3 σ3 :
     step F s1 σ1 s2 σ2 →
     nsteps F n s2 σ2 s3 σ3 →
     nsteps F (S n) s1 σ1 s3 σ3.
Local Hint Constructors nsteps : core.

Lemma step_star_nsteps F s1 σ1 s2 σ2 :
  step_star F s1 σ1 s2 σ2 ↔ ∃ n, nsteps F n s1 σ1 s2 σ2.
Proof.
  split.
  - induction 1; firstorder eauto.
  - intros (n & Hsteps).
    induction Hsteps; eauto using Step0, Step1.
Qed.

Definition normal_post `{envGS val Σ} Q :=
  {| Qnormal := Q; Qbreak := False%I; Qcontinue := False%I; Qreturn := λ _, False%I |}.

Section lemmas.

Context `{!gen_heapGS loc val Σ} `{!envGS val Σ} `{!invGS_gen HasNoLc Σ}.

Lemma guarded_stop F φ : ⊢ guarded F ⊤ (normal_post ⌜φ⌝%I) Kstop ⌜φ⌝%I.
Proof.
  iSplit; last repeat (iSplit; [iIntros "[]"|]); simpl.
  - iIntros (?); rewrite wp_sk_unfold /wp_sk_pre; by iLeft.
  - iIntros (?) "He".
    rewrite wp_sk_unfold /wp_sk_pre /wp_expr.
    iRight.
    iIntros (??) "S"; iMod ("He" with "S") as (?) "(_ & _ & [])".
Qed.

Local Lemma wp_not_stuck F s k σ ρ r Q :
  ⎡state_interp σ ρ⎤ -∗ stack_match ρ r k -∗ wp_sk F ⊤ s k Q ={⊤, ∅}=∗ ⌜not_stuck F s (Build_state r σ k)⌝.
Proof.
  rewrite wp_sk_unfold /wp_sk_pre /not_stuck /=. iIntros "Hσ Hr [(% & _) | H]".
  - iApply fupd_mask_intro; auto.
  - iMod ("H" with "Hσ") as "H".
    iDestruct ("H" with "Hr") as (?????) "_"; eauto.
Qed.

End lemmas.

Lemma wp_adequacy Σ `{!gen_heapGpreS loc val Σ} `{!inG Σ (@envR val)} `{!invGpreS Σ} F s σ φ :
  (∀ `{!gen_heapGS loc val Σ} `{!envGS val Σ} `{Hinv : !invGS_gen HasNoLc Σ},
     ⊢ |={⊤}=> wp F ⊤ s (normal_post ⌜φ⌝)) →
  adequate F s (Build_state ∅ σ Kstop) (λ _, φ).
Proof.
  intros Hwp. apply adequate_alt; intros s2 σ2 H.
  eapply uPred.pure_soundness.
  apply step_star_nsteps in H as (n & H).
  eapply (step_fupdN_soundness_gen _ HasNoLc n n).
  iIntros (Hinv) "_".
  iApply (embed_emp_valid_inj(PROP2 := monPred stack_index _)).
  iMod (gen_heap_init σ) as (?) "[Hh _]".
  iMod env_init as (?) "He".
  iMod Hwp as "Hwp"; clear Hwp.
  iSpecialize ("Hwp" with "[]"); first by iApply guarded_stop.
  iAssert (stack_match ∅ ∅ Kstop) as "Hstack".
  { rewrite /stack_match /=.

  }
  set (ρ := ∅) in H |- *; clearbody ρ.
  set (k := Kstop) at 1; fold k in H; clearbody k.
  iInduction n as [|n] "IH" forall (σ ρ k s H).
  - inv H.
    rewrite wp_sk_unfold /wp_sk_pre; iDestruct "Hwp" as "[Hwp | Hwp]".
    + iDestruct "Hwp" as "((-> & ->) & >%)".
      rewrite embed_fupd; iApply fupd_mask_intro; first set_solver.
      iIntros "_"; iPureIntro; rewrite /not_stuck /=; auto.
    + admit.
  - inv H.
    rewrite wp_sk_unfold /wp_sk_pre; iDestruct "Hwp" as "[Hwp | Hwp]".
    { iDestruct "Hwp" as "((-> & ->) & _)"; inv H3. }
    iMod ("Hwp" with "[]" )
Qed.
