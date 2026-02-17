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
  | r :: k' => let '(ρ, n) := make_stack k' in (<[n := r]>ρ, S n)
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
   (∀ σ ρ, ⎡state_interp σ ρ⎤ ={E,∅}=∗ ∀ r k, stack_match ρ r k -∗
    ∃ s' r' σ' k',
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

Lemma wp_mono E s P Q : <obj> (P -∗ Q) ⊢ wp E s P -∗ wp E s Q.
Proof.
  split => n; monPred.unseal.
  iIntros "HPQ" (? <-) "H".
  iLöb as "IH" forall (n s P Q).
  rewrite !wp_unfold /wp_pre; monPred.unseal.
  iDestruct "H" as "[(% & H) | H]".
  - iLeft; iSplit => //.
    by iApply "HPQ".
  - iRight.
    iIntros (???<-) "S"; iMod ("H" with "[//] S") as "H".
    iIntros "!> %%%<- Hstack".
    rewrite {1 3}/stack_match.
    destruct (make_stack _) eqn: Hstack.
    rewrite /stack_level; monPred.unseal.
    iDestruct "Hstack" as %(<- & ?).
    iDestruct ("H" with "[//] []") as (?????) "H".
    { setoid_rewrite Hstack; done. }
    iExists _, _, _, _; iSplit => //.
    iNext; iMod "H" as (?) "($ & $ & H)".
    iApply ("IH" with "[HPQ] H").
    iIntros (??); iApply "HPQ".
Qed.

Lemma wp_skip E R : R ⊢ wp E skip R.
Proof.
  iIntros "R".
  rewrite wp_unfold /wp_pre. iLeft.
  iSplit; done.
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

Lemma stack_match_stack_depth ρ r k (P : assert) i:
  (stack_match ρ r k) i -∗ P i -∗
  (stack_match ρ r k ∗ P) (stack_depth k).
Proof.
  unfold stack_match, stack_depth.
  destruct (make_stack k).
  rewrite /stack_level; monPred.unseal.
  iIntros "(<- & ->) $". done.
Qed.

Lemma stack_match_embed ρ r k (P : assert) : stack_match ρ r k -∗ P -∗
  ⎡(stack_match ρ r k ∗ P) (stack_depth k)⎤.
Proof.
  unfold stack_match, stack_depth.
  destruct (make_stack k).
  iIntros "(#? & %) P"; iApply stack_level_embed; by iFrame "# ∗".
Qed.

Lemma wp_seq E s1 s2 Q : wp E s1 (▷ wp E s2 Q) ⊢ wp E (Sseq s1 s2) Q.
Proof.
  split => n.
  iIntros "H".
  iLöb as "IH" forall (s1 s2 Q n).
  rewrite wp_unfold [wp _ (s1;;s2)%S _]wp_unfold /wp_pre.
  monPred.unseal.
  iRight.
  iIntros (???<-) "S".
  iDestruct "H" as "[[-> >Hs1] | H]".
  - iApply fupd_mask_intro; first set_solver; iIntros "Hclose" (???<-) "Hstack".
    iExists _, _, _, _. iSplit.
    { iPureIntro. apply SeqS2. }
    { iNext; iFrame.
      rewrite /stack_match /stack_depth.
      destruct (make_stack x2).
      rewrite /stack_level; monPred.unseal.
      iDestruct "Hstack" as (<-) "$".
      iMod "Hclose". iModIntro; iSplit => //.
    }
  - iDestruct ("H" with "[//] [$]") as ">H".
    iModIntro.
    iIntros (r k ? <-) "Hmatch".
    iDestruct ("H" with "[//] [$Hmatch]") as (????) "(% & H)".
    iExists _, _, _, _.
    iSplit; first by (iPureIntro; econstructor).
    clear.
    iNext; iMod "H" as (ρ) "($ & ? & ?)"; iModIntro.
    rewrite -monPred_at_sep.
    iApply (stack_match_stack_depth with "[$] [-]").
    iApply "IH"; iFrame.
Qed.

Definition get_params f := let 'Func params _ _ _ := f in params.
Definition get_locals f := let 'Func _ locals _ _ := f in locals.
Definition get_body f := let 'Func _ _ body _ := f in body.
Definition get_ret f := let 'Func _ _ _ e := f in e.

Definition stack_size f := let 'Func params locals _ _ := f in
  (length params + length locals)%nat.

Definition stack_frac f := (/ pos_to_Qp (Pos.of_nat (1 + stack_size f)))%Qp.

Definition stack_retainer f := (∃ n, stack_level (S n) ∗ ⎡stack_frag (S n) (stack_frac f) (stack_frac f) ∅⎤)%I.

Definition stackframe f vs := ([∗ list] x;v ∈ (get_params f ++ get_locals f);vs, points_to_var x v)%I.

Definition call_assert E f vs x R := (⇑ (stack_retainer f -∗ stackframe f vs -∗
  wp E (get_body f) (wp_expr E (get_ret f) (λ v, stack_retainer f ∗
    (∃ vs, ⌜stack_size f = length vs⌝ ∧ stackframe f vs) ∗
    ⇓ ((∃ v, points_to_var x v) ∗ ▷ (points_to_var x v -∗ R))))))%I.

Lemma wp_exprs_app E es Q σ ρ : wp_exprs E es Q -∗ ⎡state_interp σ ρ⎤ ={E}=∗
  ∃ vs, (∀ r k, env_match ρ r -∗ ⌜eval_exprs' es (Build_state r σ k) vs⌝) ∗ ⎡state_interp σ ρ⎤ ∗ Q vs.
Proof.
  iIntros "Hes S"; iInduction es as [|e es] "IH" forall (Q); simpl.
  - iFrame. iIntros "!> %% ?"; iPureIntro; constructor.
  - wp_expr.unseal.
    iMod ("Hes" with "S") as (?) "(He & S & Hes)".
    iMod ("IH" with "Hes S") as (?) "(Hes & $ & $)".
    iIntros "!> %% Henv".
    iDestruct ("He" with "Henv") as %?; iDestruct ("Hes" $! _ k with "Henv") as %?.
    iPureIntro; by constructor.
Qed.

Lemma stack_depth_max : forall k ρ n, make_stack k = (ρ, n) → ∀ m, n ≤ m → ρ !! m = None.
Proof.
  induction k; simpl; try done.
  - inversion 1; intros; by rewrite lookup_empty.
  - destruct (make_stack k) eqn: Hk; inversion 1; subst; intros.
    rewrite lookup_insert_ne; last lia.
    eapply IHk; eauto; lia.
Qed.

Lemma add_frame σ ρ r k xs vs : ⎡state_interp σ ρ⎤ ∗ stack_match ρ r k ⊢
  |==> ∃ ρ', ⎡state_interp σ ρ'⎤ ∗ ⇑ (stack_match ρ' (bind_vars xs vs) (r :: k) ∗
    assert_of (λ n, stack_frag n (/ pos_to_Qp (Pos.of_nat (1 + size (bind_vars xs vs))))%Qp 1%Qp (bind_vars xs vs))).
Proof.
  intros; rewrite /stack_match /=.
  destruct (make_stack k) eqn: Hk.
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

Lemma pure_sep_equiv P (Q R : iProp Σ) : (P → (Q ⊣⊢ R)) → ⌜P⌝ ∗ Q ⊣⊢ ⌜P⌝ ∗ R.
Proof.
  intros; iSplit; iIntros "(% & ?)"; iSplit => //.
  - rewrite H //.
  - rewrite -H //.
Qed.

Lemma split_stackframe params locals body e vs :
  length (params ++ locals) = length vs → NoDup (params ++ locals) →
  let r' := bind_vars (params ++ locals) vs in
  (∃ n, stack_level (S n) ∗ assert_of (λ n, stack_frag n (/ pos_to_Qp (Pos.of_nat (1 + size r')))%Qp 1%Qp r')) ⊣⊢
  stack_retainer (Func params locals body e) ∗ stackframe (Func params locals body e) vs.
Proof.
  split => n /=; rewrite /stack_retainer /stackframe /stack_level; monPred.unseal.
  rewrite bi.sep_exist_r; do 2 f_equiv.
  rewrite -assoc; apply pure_sep_equiv; intros [=]; subst.
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

Lemma remove_frame σ ρ r r0 k q r' : ⎡state_interp σ ρ⎤ ∗ stack_match ρ r (r0 :: k) ∗ assert_of (λ n, stack_frag n q 1%Qp r') ⊢
  |==> ∃ ρ', ⎡state_interp σ ρ'⎤ ∗ ⇓ stack_match ρ' r0 k.
Proof.
  intros; rewrite /stack_match /=.
  destruct (make_stack k) eqn: Hk.
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
  ▷ call_assert E fd (vs ++ repeat (NumV 0) (length (get_locals fd))) x Q) ⊢
  wp E (Scall x f es) Q.
Proof.
  iIntros "H".
  rewrite wp_unfold /wp_pre; iRight.
  iIntros (??) "S".
  iMod (wp_exprs_app with "H S") as (?) "(Hes & S & %fd & (% & %Hlen & %) & H)".
  destruct fd; simpl in *.
  iApply fupd_mask_intro; first set_solver; iIntros "Hclose" (??) "Hstack".
  iDestruct ("Hes" with "[Hstack]") as %?; first by iApply stack_env_match.
  iExists _, _, _, _; iSplit.
  { iPureIntro; by econstructor. }
  iNext.
  iMod (add_frame with "[$S $Hstack]") as (?) "($ & Hstack)".
  iMod "Hclose" as "_"; iModIntro; simpl.
  iApply up1_obj_elim; iApply up1_mono; last first.
  { rewrite /call_assert.
    iCombine "H Hstack" as "H"; rewrite !up1_sep; iApply "H". }
  iIntros "(H & Hstack & Hframe)".
  iAssert (stack_level (S (stack_depth k))) with "[Hstack]" as "#Hl".
  { rewrite /stack_match /stack_depth /=. destruct (make_stack k); iDestruct "Hstack" as "($ & _)". }
  iApply (stack_match_embed with "Hstack").
  assert (length (func_params ++ func_locals) = length (vs ++ repeat (NumV 0) (length func_locals))).
  { rewrite !app_length repeat_length; f_equal.
    rewrite -Hlen; by eapply Forall2_length. }
  iPoseProof (bi.equiv_entails_1_1 with "[Hframe]") as "Hframe"; first by apply split_stackframe.
  { iFrame; eauto. }
  iDestruct "Hframe" as "(Hret & Hframe)".
  iApply wp_seq. iApply wp_mono; last by iApply ("H" with "Hret Hframe").
  rewrite monPred_objectively_unfold; iIntros "!>" (?); monPred.unseal.
  iIntros (??) "H !>".
  rewrite wp_unfold /wp_pre; wp_expr.unseal; monPred.unseal.
  iRight; iStopProof; do 8 f_equiv.
  iIntros ">(% & He & (Hσ & Hρ) & Hret & Hframe & (% & Hx) & H)".
  iDestruct (stack_ra.var_e with "[$Hx $Hρ]") as %?.
  iApply fupd_mask_intro; first set_solver; iIntros "Hclose" (???<-) "Hstack".
  rewrite {1}/stack_match.
  destruct (make_stack _) eqn: Hstack.
  rewrite /stack_level; monPred.unseal.
  iDestruct "Hstack" as %([=] & ->).
  rewrite /stack_retainer /stack_level; monPred.unseal.
  iDestruct "Hret" as (? [=]) "Hret"; subst; simpl in *.
  iDestruct ("He" with "[//] []") as %?.
  { by rewrite lookup_insert. }
  destruct x3; try done.
  iExists _,_, _, _; iSplit.
  { iPureIntro; by econstructor. }
  iNext.
  iDestruct "Hframe" as (??) "Hframe".
  iPoseProof (monPred_in_entails with "[Hσ Hρ Hret Hframe]") as "H'"; first apply remove_frame.
  { monPred.unseal; iFrame.
    iAssert (stack_retainer (Func func_params func_locals func_body func_ret) (S x4)) with "[Hret]" as "Hret".
    { rewrite /stack_retainer /stack_level; monPred.unseal; by iFrame. }
    iCombine "Hret Hframe" as "H".
    rewrite -monPred_at_sep monPred_in_equiv; last by symmetry; apply split_stackframe; rewrite ?app_length.
    monPred.unseal; iDestruct "H" as (?) "(_ & $)".
    rewrite /stack_match /stack_level; setoid_rewrite Hstack; by monPred.unseal. }
  monPred.unseal; iMod "H'" as (?) "(S & Hstack)".
  iPoseProof (monPred_in_entails with "[S Hstack Hx]") as "H'"; first apply var_update.
  { monPred.unseal; iFrame. }
  monPred.unseal; iMod "H'" as (?) "(Hstack & Hx & $)".
  iMod "Hclose"; iModIntro.
  iSplitR "H Hx".
  - rewrite /stack_match /stack_depth; destruct (make_stack x3); monPred.unseal.
    iDestruct "Hstack" as "(_ & $)"; rewrite /stack_level; by monPred.unseal.
  - simpl in Hstack.
    rewrite /stack_depth; destruct (make_stack _).
    inv Hstack.
    rewrite -wp_skip; by iApply "H".
Qed.

Lemma wp_assign E x e Q : wp_expr E e (λ v, (∃ v0, x ↦v v0) ∗
  ▷ (x ↦v v -∗ Q)) ⊢ wp E (Sassign x e) Q.
Proof.
  iIntros "H".
  rewrite wp_unfold /wp_pre /stack_depth. iRight.
  iIntros (??) "S".
  wp_expr.unseal.
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
  rewrite -wp_skip. by iApply "Hpost".
Qed.

Lemma wp_alloc E x Q : (∃ v0, x ↦v v0) ∗
  ▷ (∀ l, points_to_var x (LocV l) -∗ l ↦ NumV 0 -∗ Q) ⊢ wp E (Salloc x) Q.
Proof.
  iIntros "H".
  rewrite wp_unfold /wp_pre. iRight.
  iIntros (??) "S".
  iDestruct "H" as "((% & Hx) & Hpost)".
  iApply fupd_mask_intro; first set_solver; iIntros "Hclose" (??) "Hstack".
  iDestruct (var_e with "[$Hx $S $Hstack]") as %?.
  iExists _, _, _, _; iSplit.
  { iPureIntro; by econstructor. }
  iNext.
  iMod (var_update with "[$Hx $S $Hstack]") as (?) "(? & Hx & S)".
  iMod (state_interp_alloc with "S") as "($ & S)".
  { apply next_loc_new. }
  iMod "Hclose"; iModIntro.
  iApply (stack_match_embed with "[$]").
  rewrite -wp_skip. by iApply ("Hpost" with "[$]").
Qed.

Lemma wp_store E e1 e2 Q : wp_expr E e2 (λ v, wp_expr E e1 (λ v1, ∃ l v0, ⌜v1 = LocV l⌝ ∧
  l ↦ v0 ∗ ▷ (l ↦ v -∗ Q))) ⊢ wp E (Sstore e1 e2) Q.
Proof.
  iIntros "H".
  rewrite wp_unfold /wp_pre. iRight.
  iIntros (??) "S".
  wp_expr.unseal.
  iMod ("H" with "S") as (?) "(He2 & S & H)".
  wp_expr.unseal.
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

Lemma wp_if E e s1 s2 Q : wp_expr E e (λ v, ∃ n, ⌜v = NumV n⌝ ∧
  ▷ wp E (if Z.eqb n 0 then s2 else s1) Q) ⊢ wp E (Sif e s1 s2) Q.
Proof.
  iIntros "H".
  rewrite wp_unfold /wp_pre. iRight.
  iIntros (??) "S".
  wp_expr.unseal.
  iMod ("H" with "S") as (?) "(He & S & % & -> & H)".
  iApply fupd_mask_intro; first set_solver; iIntros "Hclose" (??) "Hstack".
  iDestruct ("He" with "[Hstack]") as %?; first by iApply stack_env_match.
  iExists _, _, _, _; iSplit.
  { iPureIntro; by econstructor. }
  iNext; iFrame.
  iApply (stack_match_embed with "[$]").
  iMod "Hclose". iApply "H".
Qed.

Lemma wp_while E e s Q : wp_expr E e (λ v, ∃ n, ⌜v = NumV n⌝ ∧
  ▷ if Z.eqb n 0 then Q else wp E s (▷ wp E (Swhile e s) Q)) ⊢
  wp E (Swhile e s) Q.
Proof.
  iIntros "H".
  rewrite {2}[wp _ (Swhile _ _) _]wp_unfold /wp_pre. iRight.
  iIntros (??) "S".
  wp_expr.unseal.
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

Section adequacy.

(* generalize? *)
Definition not_stuck F s σ := s = skip ∨
  (∃ s' σ', step F s σ s' σ').

Record adequate F s (σ1 : state) (φ : state → Prop) := {
  adequate_result σ2 :
   step_star F s σ1 skip σ2 → φ σ2;
  adequate_not_stuck s2 σ2 :
   step_star F s σ1 s2 σ2 →
   not_stuck F s2 σ2
}.

Lemma adequate_alt F s1 σ1 (φ : state → Prop) :
  adequate F s1 σ1 φ ↔ ∀ s2 σ2,
    step_star F s1 σ1 s2 σ2 →
      (s2 = skip → φ σ2) ∧
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

Lemma eval_expr_det e r m v1 : eval_expr e r m v1 → forall v2, eval_expr e r m v2 →
  v1 = v2.
Proof.
  induction 1; inversion 1; subst; try congruence.
  - specialize (IHeval_expr1 _ ltac:(eassumption)).
    specialize (IHeval_expr2 _ ltac:(eassumption)); congruence.
  - specialize (IHeval_expr _ ltac:(eassumption)); congruence.
Qed.

Ltac expr_det := match goal with H1 : eval_expr' ?a ?b ?v1, H2 : eval_expr' ?a ?b ?v2 |- _ =>
  let H := fresh "Heq" in pose proof (eval_expr_det _ _ _ _ H1 _ H2) as H; clear H2; inv H end.

Lemma eval_exprs_det e σ v1 : eval_exprs' e σ v1 → forall v2, eval_exprs' e σ v2 →
  v1 = v2.
Proof.
  induction 1; inversion 1; subst; try congruence.
  expr_det; f_equiv; auto.
Qed.

Lemma step_det F s σ s1 σ1 s2 σ2 : step F s σ s1 σ1 → step F s σ s2 σ2 →
  s1 = s2 ∧ σ1 = σ2.
Proof.
  intros; generalize dependent s2.
  induction H; inversion 1; subst; repeat expr_det; try done; try congruence.
  - edestruct IHstep; first done; by subst.
  - inv H.
  - inv H6.
  - rewrite H in H7; inv H7. eapply eval_exprs_det in H1; last done. by subst.
Qed.

Lemma wp_adequacy Σ `{!gen_heapGpreS loc val Σ} `{!inG Σ (@envR val)} `{!invGpreS Σ} F s σ φ :
  (∀ `{!gen_heapGS loc val Σ} `{!envGS val Σ} `{Hinv : !invGS_gen HasNoLc Σ},
     ⊢ |={⊤}=> wp F ⊤ s (⌜φ⌝)) →
  adequate F s (Build_state ∅ σ []) (λ _, φ).
Proof.
  intros Hwp. apply adequate_alt; intros s2 σ2 H.
  eapply uPred.pure_soundness.
  apply step_star_nsteps in H as (n & H).
  eapply (step_fupdN_soundness_gen _ HasNoLc n n).
  iIntros (Hinv) "_".
  iMod (gen_heap_init σ) as (?) "[Hh _]".
  iMod (env_init ∅) as (?) "(He & _)".
  iPoseProof (monPred_in_entails _ _ (Hwp _ _ _) O with "[]") as "Hwp"; clear Hwp.
  { by monPred.unseal. }
  rewrite monPred_at_fupd; iMod "Hwp".
  iAssert (stack_match {[0 := ∅]} ∅ [] O) as "-#Hstack".
  { rewrite /stack_match /stack_level; by monPred.unseal. }

  set (r := ∅) in *; clearbody r.
  set (k := []) in *; clearbody k.
  set (ρ := {[0 := r]}); clearbody ρ.
  set (l := 0); clearbody l.
  iInduction n as [|n] "IH" forall (σ ρ r k l s H).
  - inv H.
     rewrite wp_unfold /wp_pre; monPred.unseal.
    iDestruct "Hwp" as "[Hwp | Hwp]".
    + iDestruct "Hwp" as "(-> & >%)".
      iApply fupd_mask_intro; first set_solver.
      iIntros "_"; iPureIntro; rewrite /not_stuck /=; auto.
    + iMod ("Hwp" with "[//] [$Hh $He]") as "Hwp".
      iDestruct ("Hwp" with "[//] Hstack") as (???? Hstep) "H".
      iPureIntro; split.
      * intros ->; inv Hstep.
      * right; eauto.
  - inv H.
    rewrite wp_unfold /wp_pre; monPred.unseal; iDestruct "Hwp" as "[Hwp | Hwp]".
    { iDestruct "Hwp" as "(-> & _)"; inv H3. }
    iMod ("Hwp" with "[//] [$Hh $He]") as "Hwp".
    iDestruct ("Hwp" with "[//] Hstack") as (???? Hstep) "H".
    eapply step_det in H3; last done.
    destruct H3 as (<- & <-).
    iModIntro; simpl.
    iModIntro; iNext.
    iMod "H" as (?) "((Hh & He) & Hstack & H)".
    iApply ("IH" with "[//] Hh He H Hstack").
Qed.

End adequacy.
