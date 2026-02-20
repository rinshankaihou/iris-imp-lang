(* wp for implang *)
From iris.algebra.lib Require Import excl_auth.
From iris.base_logic Require Import gen_heap.
From iris.program_logic Require Import weakestpre adequacy.
From iris_imp_lang Require Import lifting_expr.
From iris_imp_lang.imp Require Import notation.
From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.

Definition to_val s := match s with skip => Some tt | _ => None end.

Lemma implang_mixin F : LanguageMixin(observation := Empty_set) (λ _, skip) to_val
    (λ s σ obs s' σ' es, obs = [] ∧ es = [] ∧ step F s σ s' σ').
Proof.
  split.
  - by intros [].
  - by destruct e; inversion 1.
  - by intros ?????? (? & ? & H); inv H.
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

Section wp.

Context `{!gen_heapGS loc val Σ} `{!envGS val Σ} `{!invGS_gen hlc Σ} `{!inG Σ (excl_authR nat)}.
Variable (F : func_env).
Variable (γ : gname).

Canonical Structure imp_lang := Language (implang_mixin F).

Implicit Types (ρ : @env_state val) (σ : gmap loc val).

Fixpoint make_stack (k : stack) : env_state * nat :=
  match k with
  | [] => (∅, O)
  | r :: k' => let '(ρ, n) := make_stack k' in (<[n := r]>ρ, S n)
  end.

Definition stack_depth k := snd (make_stack k).

Definition state_ctx (s : state) := (gen_heap_interp s.(m) ∗
  let '(ρ0, n) := make_stack s.(k) in
    env_auth (<[n := s.(ρ)]>ρ0) ∗ own γ (●E n))%I.

Global Instance implang_irisG : irisGS_gen hlc imp_lang Σ := {
  iris_invGS := _;
  state_interp s _ _ _ := state_ctx s;
  fork_post _ := True%I;
  num_laters_per_step _ := 0%nat;
  state_interp_mono _ _ _ _ := fupd_intro _ _;
}.

Definition stack_top n := (⎡own γ (◯E n)⎤ ∗ stack_level n)%I.

Definition wp E s (Q : assert) : assert := (∀ n, stack_top n -∗
  ⎡wp NotStuck E s (λ _, ∃ n', own γ (◯E n') ∗ Q n')⎤)%I.

Lemma wp_mono E s P Q : <obj> (P -∗ Q) ⊢ wp E s P -∗ wp E s Q.
Proof.
  iIntros "HPQ H" (?) "N".
  iSpecialize ("H" with "N").
  iApply (wp_wand with "H").
  iIntros (_) "(% & $ & ?)".
  iStopProof; split => ?; monPred.unseal.
  iIntros "(HPQ & H)"; by iApply "HPQ".
Qed.

Lemma wp_skip E R : R ⊢ wp E skip R.
Proof.
  iIntros "R" (?) "(N & L)".
  rewrite /wp wp_unfold /wp_pre /=.
  rewrite embed_fupd; iModIntro; iFrame.
  by iApply (stack_level_embed with "L").
Qed.

Lemma var_e : forall n x v s,
  stack_top n ∗ x ↦v v ∗ ⎡state_ctx s⎤ ⊢ ⌜s.(ρ) !! x = Some v⌝.
Proof.
  intros; rewrite /state_ctx /stack_top /stack_level.
  destruct (make_stack _) eqn: Hk.
  split => ?; monPred.unseal.
  iIntros "((N & <-) & Hx & _ & Hρ & N')".
  iCombine "N N'" gives %->%excl_auth_agree_L.
  iDestruct (var_e with "[$Hx $Hρ]") as %?.
  by rewrite /env_to_environ lookup_insert in H.
Qed.

Lemma var_update : forall n x v v' s,
  stack_top n ∗ x ↦v v ∗ ⎡state_ctx s⎤ ⊢
  |==> stack_top n ∗ x ↦v v' ∗ ⎡state_ctx (s <| ρ ::= <[x := v']> |>)⎤.
Proof.
  intros; rewrite /state_ctx /stack_top /stack_level.
  destruct (make_stack _) eqn: Hk.
  split => ?; monPred.unseal.
  iIntros "((N & %H) & Hx & $ & Hρ & N')"; hnf in H; subst.
  iCombine "N N'" gives %<-%excl_auth_agree_L.
  iMod (var_update with "[$Hx $Hρ]") as "(? & $)".
  rewrite /set_var lookup_insert insert_insert; by iFrame.
Qed.

Lemma state_level_elim s n : state_ctx s -∗ own γ (◯E n) -∗ ⌜n = stack_depth s.(k)⌝.
Proof.
  rewrite /state_ctx /stack_depth.
  destruct (make_stack _).
  iIntros "(_ & _ & Ha) Hb".
  by iCombine "Ha Hb" gives %->%excl_auth_agree_L.
Qed.

Lemma wp_seq E s1 s2 Q : wp E s1 (▷ wp E s2 Q) ⊢ wp E (Sseq s1 s2) Q.
Proof.
  split => n; rewrite /wp /stack_top /stack_level; monPred.unseal.
  iIntros "H" (?? <-) "(N & ->)".
  iSpecialize ("H" with "[//] [$N //]").
  clear.
  iLöb as "IH" forall (s1 s2 Q).
  rewrite wp_unfold (wp_unfold _ _ (s1;; s2)%S) /wp_pre /=.
  iIntros (?????) "S".
  destruct (to_val s1) eqn: Hs1.
  - destruct s1; inv Hs1.
    iMod "H" as (?) "(N & H)".
    iApply fupd_mask_intro; first set_solver; iIntros "Hclose".
    iSplit.
    { iPureIntro. eexists _, _, _, _; split; first done; split; first done.
      apply SeqS2. }
    iIntros (??? (-> & -> & H)); inv H.
    { inv H6. }
    iDestruct (state_level_elim with "S N") as %->; iFrame.
    iIntros "_ !> !> !>".
    iMod "Hclose".
    iModIntro; iSplit => //.
    by iApply ("H" with "[//] [$N //]").
  - iDestruct ("H" $! _ O [] [] O with "[$]") as ">(%Hred & H)".
    iModIntro; iSplit.
    { iPureIntro; destruct Hred as (? & ? & ? & ? & -> & -> & H).
      eexists _, _, _, _; split; first done; split; first done.
      by constructor. }
    iIntros (??? (-> & -> & H)) "?".
    inv H.
    iMod ("H" with "[//] [$]") as "H".
    iIntros "!> !> !>".
    iMod "H"; iMod "H" as "($ & H & $)".
    by iApply "IH".
Qed.

Lemma wp_expr_app E e Q n s : wp_expr E e Q -∗ stack_top n -∗
  ⎡state_ctx s⎤ ={E}=∗ ∃ v, ⌜eval_expr e s.(ρ) s.(m) v⌝ ∗ stack_top n ∗
  ⎡state_ctx s⎤ ∗ Q v.
Proof.
  rewrite /state_ctx; wp_expr.unseal.
  iIntros "H (N & #L) (Hσ & Hρ)".
  destruct (make_stack _) eqn: Hstack; iDestruct "Hρ" as "(Hρ & N')".
  iMod ("H" with "[$Hσ $Hρ]") as (?) "(He & ($ & $) & HQ)".
  iCombine "N N'" gives %->%excl_auth_agree_L.
  iFrame; iFrame "#".
  iStopProof; split => ?; rewrite /stack_level; monPred.unseal; rewrite monPred_at_intuitionistically.
  iIntros "(% & H)"; iApply ("H" with "[//]").
  by rewrite lookup_insert.
Qed.

Lemma stack_top_embed n (P : assert) : stack_top n -∗ P -∗ ⎡own γ (◯E n) ∗ P n⎤.
Proof.
  iIntros "($ & #L) P". by iApply stack_level_embed.
Qed.

Lemma wp_assign E x e Q : wp_expr E e (λ v, (∃ v0, x ↦v v0) ∗
  ▷ (x ↦v v -∗ Q)) ⊢ wp E (Sassign x e) Q.
Proof.
  iIntros "H" (?) "N".
  rewrite /wp wp_unfold /wp_pre /=.
  iIntros (?????) "S".
  iMod (wp_expr_app with "H N S") as (? He) "(N & S & (% & Hx) & Hpost)".
  rewrite embed_fupd.
  iApply fupd_mask_intro; first set_solver; iIntros "Hclose"; iSplit.
  { iPureIntro; eexists _, _, _, _; split; first done; split; first done; by constructor. }
  iIntros (??? (-> & -> & H)) "?".
  inv H.
  eapply eval_expr_det in He; last done; subst.
  rewrite embed_fupd; iModIntro; iNext.
  rewrite embed_fupd; iModIntro.
  iDestruct (var_e with "[$Hx $S $N]") as %?.
  iMod (var_update with "[$Hx $S $N]") as "(N & ? & $)".
  iMod "Hclose".
  rewrite /= bi.sep_emp wp_unfold /wp_pre /=.
  do 2 (rewrite embed_fupd; iModIntro).
  iPoseProof (stack_top_embed with "N [-]") as "($ & H)"; last done.
  by iApply "Hpost".
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

Lemma wp_exprs_app E es Q n s : wp_exprs E es Q -∗ stack_top n -∗ ⎡state_ctx s⎤ ={E}=∗
  ∃ vs, ⌜eval_exprs' es s vs⌝ ∗ stack_top n ∗ ⎡state_ctx s⎤ ∗ Q vs.
Proof.
  iIntros "Hes N S"; iInduction es as [|e es] "IH" forall (Q); simpl.
  - iFrame. iPureIntro; constructor.
  - iMod (wp_expr_app with "Hes N S") as (??) "(N & S & Hes)".
    iMod ("IH" with "Hes N S") as (??) "$".
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

Lemma add_frame s n xs vs : ⎡state_ctx s⎤ ∗ stack_top n ⊢
  |==> ⎡state_ctx (s <| ρ := bind_vars xs vs |> <| k:= s.(ρ) :: s.(k) |>)⎤ ∗ ⇑ (stack_top (S n) ∗
    assert_of (λ n, stack_frag n (/ pos_to_Qp (Pos.of_nat (1 + size (bind_vars xs vs))))%Qp 1%Qp (bind_vars xs vs))).
Proof.
  intros; rewrite /state_ctx /stack_top /=.
  iIntros "((Hσ & Hρ) & N & #L)".
  destruct (make_stack _) eqn: Hstack; iDestruct "Hρ" as "(Hρ & N')".
  iCombine "N N'" gives %->%excl_auth_agree_L.
  iMod (state_interp_alloc_frame _ _ (S n) with "[$Hσ $Hρ]") as "(($ & $) & ?)".
  { rewrite lookup_insert_ne //.
    eapply stack_depth_max; eauto. }
  iMod (own_update_2 with "N' N") as "($ & N)".
  { apply excl_auth_update. }
  iModIntro.
  rewrite -!up1_sep -up1_objective; iFrame.
  iSplit; first by iApply stack_level_up.
  iStopProof; split => ?; rewrite /stack_level; monPred.unseal; rewrite monPred_at_intuitionistically /=.
  iIntros "(<- & $)".
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

Lemma remove_frame s r0 k0 n q r' : s.(k) = r0 :: k0 →
  ⎡state_ctx s⎤ ∗ stack_top (S n) ∗ assert_of (λ n, stack_frag n q 1%Qp r') ⊢
  |==> ⎡state_ctx (s <| ρ := r0 |> <| k := k0 |>)⎤ ∗ ⇓ stack_top n.
Proof.
  intros; rewrite /state_ctx /stack_top H /=.
  destruct (make_stack _) eqn: Hk.
  iIntros "((Hσ & Hρ & N') & (N & #Hl) & H)".
  iCombine "N N'" gives %[=]%excl_auth_agree_L; subst.
  iMod (state_interp_dealloc_frame _ _ (S n) with "[$Hσ $Hρ H]") as "($ & ?)".
  { iApply (stack_level_embed with "Hl H"). }
  iMod (own_update_2 with "N' N") as "($ & N)".
  { apply excl_auth_update. }
  iModIntro.
  rewrite -!down1_sep -down1_objective; iFrame.
  iPoseProof (stack_level_down with "Hl") as "$".
  iClear "#"; iStopProof; do 2 f_equiv.
  apply (delete_insert _ _ s.(ρ)).
  rewrite lookup_insert_ne //; eapply stack_depth_max; eauto.
Qed.

Lemma eval_exprs_det e s v1 : eval_exprs' e s v1 → forall v2, eval_exprs' e s v2 →
  v1 = v2.
Proof.
  induction 1; inversion 1; subst; try congruence.
  expr_det; f_equiv; auto.
Qed.

Lemma bi_entails_obj (P Q : assert) : (P ⊢ Q) → ⊢ <obj> (P -∗ Q).
Proof.
  intros; split => n; monPred.unseal.
  iIntros "_" (???); by iApply monPred_in_entails.
Qed.

Lemma wp_call E x f es Q : wp_exprs E es (λ vs, ∃ fd, ⌜F !! f = Some fd ∧
    length es = length (get_params fd) ∧ NoDup (get_params fd ++ get_locals fd)⌝ ∧
  ▷ call_assert E fd (vs ++ repeat (NumV 0) (length (get_locals fd))) x Q) ⊢
  wp E (Scall x f es) Q.
Proof.
  iIntros "H" (?) "N".
  rewrite wp_unfold /wp_pre /=.
  iIntros (?????) "S".
  iMod (wp_exprs_app with "H N S") as (? Hes) "(N & S & %fd & (%Hf & %Hlen & %Hnodup) & H)".
  destruct fd; simpl in *.
  rewrite embed_fupd; iApply fupd_mask_intro; first set_solver; iIntros "Hclose"; iSplit.
  { iPureIntro. eexists _, _, _, _; split; first done; split; first done; by constructor. }
  iIntros (??? (-> & -> & H)) "?"; inv H.
  eapply eval_exprs_det in Hes; last done; subst.
  rewrite embed_fupd; iModIntro; iNext; rewrite embed_fupd; iModIntro.
  iMod (add_frame with "[$S $N]") as "($ & N)".
  rewrite embed_fupd; iMod "Hclose" as "_"; iModIntro; simpl.
  iApply up1_obj_elim; iApply up1_mono; last first.
  { rewrite /call_assert.
    iCombine "H N" as "H"; rewrite !up1_sep; iApply "H". }
  iIntros "(H & (N & #L) & Hframe)".
  (*iAssert (stack_level (S (stack_depth k))) with "[Hstack]" as "#Hl".
  { rewrite /stack_match /stack_depth /=. destruct (make_stack k); iDestruct "Hstack" as "($ & _)". }
  iApply (stack_match_embed with "Hstack").*)
  assert (length (func_params ++ func_locals) = length (vs ++ repeat (NumV 0) (length func_locals))).
  { rewrite !app_length repeat_length; f_equal.
    rewrite -Hlen; by eapply Forall2_length. }
  iPoseProof (bi.equiv_entails_1_1 with "[Hframe]") as "Hframe"; first by apply split_stackframe.
  { iFrame; eauto. }
  iDestruct "Hframe" as "(Hret & Hframe)".
  rewrite bi.sep_emp; iApply (wp_seq with "[-N] [$N //]").
  iApply wp_mono; last by iApply ("H" with "Hret Hframe").
  iApply bi_entails_obj.
  iIntros "H !>" (?) "N".
  rewrite wp_unfold /wp_pre /=.
  iIntros (?????) "S".
  iMod (wp_expr_app with "H N S") as (? He) "(N & S & Hret & Hframe & H)".
  iStopProof; split => ?; monPred.unseal.
  iIntros "(N & (Hσ & Hρ) & Hret & Hframe & (% & Hx) & H)".
  destruct (make_stack _) eqn: Hk; iDestruct "Hρ" as "(Hρ & N')".
  iDestruct (stack_ra.var_e with "[$Hx $Hρ]") as %?.
  rewrite /stack_top /stack_level; monPred.unseal.
  iDestruct "N" as "(N & ->)".
  rewrite /stack_retainer /stack_level; monPred.unseal.
  iDestruct "Hret" as (? [=]) "Hret"; subst; simpl in *.
  iCombine "N N'" gives %->%excl_auth_agree_L.
  destruct σ0; simpl in *; destruct k; try done.
  iApply fupd_mask_intro; first set_solver; iIntros "Hclose"; iSplit.
  { iPureIntro. eexists _, _, _, _; split; first done; split; first done; by econstructor. }
  iIntros (??? (-> & -> & Hstep)) "?"; inv Hstep; simpl in *.
  eapply eval_expr_det in He; last done; subst.
  iIntros "!> !> !>".
  iDestruct "Hframe" as (??) "Hframe".
  iPoseProof (monPred_in_entails with "[Hσ Hρ N N' Hret Hframe]") as "H'"; first apply (remove_frame (Build_state ρ0 m0 (ρ1 :: k0))).
  { done. }
  { monPred.unseal; iFrame.
    iAssert (stack_retainer (Func func_params func_locals func_body func_ret) (S x1)) with "[Hret]" as "Hret".
    { rewrite /stack_retainer /stack_level; monPred.unseal; by iFrame. }
    iCombine "Hret Hframe" as "H".
    rewrite -monPred_at_sep monPred_in_equiv; last by symmetry; apply split_stackframe; rewrite ?app_length.
    monPred.unseal; iDestruct "H" as (?) "(_ & $)".
    rewrite Hk; iFrame.
    rewrite /stack_top /stack_level; monPred.unseal; by iFrame. }
  monPred.unseal; iMod "H'" as "(S & Hstack)".
  iPoseProof (monPred_in_entails with "[S Hstack Hx]") as "H'"; first apply var_update.
  { monPred.unseal; iFrame. }
  monPred.unseal; iMod "H'" as "(Hstack & Hx & $)".
  iMod "Hclose"; iModIntro.
  rewrite bi.sep_emp wp_unfold /wp_pre /=.
  rewrite /stack_top; monPred.unseal; iDestruct "Hstack" as "($ & ?)".
  by iApply "H".
Qed.

Lemma wp_alloc E x Q : (∃ v0, x ↦v v0) ∗
  ▷ (∀ l, points_to_var x (LocV l) -∗ l ↦ NumV 0 -∗ Q) ⊢ wp E (Salloc x) Q.
Proof.
  iIntros "H" (?) "N".
  rewrite wp_unfold /wp_pre /=.
  iIntros (?????) "S".
  iDestruct "H" as "((% & Hx) & Hpost)".
  rewrite embed_fupd; iApply fupd_mask_intro; first set_solver; iIntros "Hclose".
  iDestruct (var_e with "[$Hx $S $N]") as %He.
  iSplit.
  { iPureIntro. eexists _, _, _, _; split; first done; split; first done; constructor. }
  iIntros (??? (-> & -> & H)) "?"; inv H.
  rewrite embed_fupd; iModIntro; iNext; rewrite embed_fupd; iModIntro.
  iMod (var_update with "[$Hx $S $N]") as "(N & Hx & S)".
  rewrite /state_ctx.
  destruct (make_stack _) eqn: Hk.
  iDestruct "S" as "(Hσ & Hρ & $)".
  iMod (state_interp_alloc with "[$Hσ $Hρ]") as "($ & S)".
  { apply next_loc_new. }
  iMod "Hclose".
  rewrite wp_unfold /wp_pre /= bi.sep_emp.
  do 2 (rewrite embed_fupd; iModIntro); iExists _; iApply (stack_top_embed with "N").
  by iApply ("Hpost" with "Hx").
Qed.

Lemma wp_store E e1 e2 Q : wp_expr E e2 (λ v, wp_expr E e1 (λ v1, ∃ l v0, ⌜v1 = LocV l⌝ ∧
  l ↦ v0 ∗ ▷ (l ↦ v -∗ Q))) ⊢ wp E (Sstore e1 e2) Q.
Proof.
  iIntros "H" (?) "N".
  rewrite wp_unfold /wp_pre /=.
  iIntros (?????) "S".
  iMod (wp_expr_app with "H N S") as (? He2) "(N & S & H)".
  iMod (wp_expr_app with "H N S") as (? He1) "(N & S & % & % & -> & Hl & Hpost)".
  rewrite embed_fupd; iApply fupd_mask_intro; first set_solver; iIntros "Hclose".
  rewrite /state_ctx.
  destruct (make_stack _) eqn: Hk; iDestruct "S" as "(Hσ & Hρ & N')".
  iDestruct (state_interp_load with "[$Hσ $Hρ] Hl") as %Hl.
  iSplit.
  { iPureIntro. eexists _, _, _, _; split; first done; split; first done; by econstructor. }
  iIntros (??? (-> & -> & H)) "?"; inv H.
  eapply eval_expr_det in He2; last done.
  eapply eval_expr_det in He1; last done; inv He1.
  rewrite embed_fupd; iModIntro; iNext; rewrite embed_fupd; iModIntro.
  rewrite /= Hk.
  iMod (state_interp_store with "[$Hσ $Hρ] Hl") as "(($ & ?) & ?)"; iFrame.
  iMod "Hclose".
  rewrite wp_unfold /wp_pre /= bi.sep_emp.
  do 2 (rewrite embed_fupd; iModIntro); iExists _; iApply (stack_top_embed with "N").
  by iApply "Hpost".
Qed.

Lemma wp_if E e s1 s2 Q : wp_expr E e (λ v, ∃ n, ⌜v = NumV n⌝ ∧
  ▷ wp E (if Z.eqb n 0 then s2 else s1) Q) ⊢ wp E (Sif e s1 s2) Q.
Proof.
  iIntros "H" (?) "N".
  rewrite wp_unfold /wp_pre /=.
  iIntros (?????) "S".
  iMod (wp_expr_app with "H N S") as (? He) "(N & S & % & -> & H)".
  rewrite embed_fupd; iApply fupd_mask_intro; first set_solver; iIntros "Hclose"; iSplit.
  { iPureIntro. eexists _, _, _, _; split; first done; split; first done; by econstructor. }
  iIntros (??? (-> & -> & H)) "?"; inv H.
  eapply eval_expr_det in He; last done; inv He.
  rewrite embed_fupd; iModIntro; iNext; rewrite embed_fupd; iModIntro; iFrame.
  rewrite bi.sep_emp.
  iMod "Hclose". rewrite embed_fupd; iModIntro. iApply ("H" with "N").
Qed.

Lemma wp_while E e s Q : wp_expr E e (λ v, ∃ n, ⌜v = NumV n⌝ ∧
  ▷ if Z.eqb n 0 then Q else wp E s (▷ wp E (Swhile e s) Q)) ⊢
  wp E (Swhile e s) Q.
Proof.
  iIntros "H" (l) "N".
  rewrite wp_unfold /wp_pre /=.
  iIntros (?????) "S".
  iMod (wp_expr_app with "H N S") as (? He) "(N & S & % & -> & H)".
  rewrite embed_fupd; iApply fupd_mask_intro; first set_solver; iIntros "Hclose".
  destruct (Z.eqb n 0) eqn:Hn.
  - iSplit.
    { iPureIntro. eexists _, _, _, _; split; first done; split; first done; by constructor. }
    iIntros (??? (-> & -> & H)) "?"; inv H.
    eapply eval_expr_det in He; last done; inv He.
    rewrite Hn; iFrame.
    rewrite embed_fupd; iModIntro; iNext; rewrite embed_fupd; iModIntro; iFrame.
    rewrite wp_unfold /wp_pre /= bi.sep_emp.
    iMod "Hclose". do 2 (rewrite embed_fupd; iModIntro).
    iExists _; by iApply (stack_top_embed with "N").
  - iSplit.
    { iPureIntro. eexists _, _, _, _; split; first done; split; first done; by constructor. }
    iIntros (??? (-> & -> & H)) "?"; inv H.
    eapply eval_expr_det in He; last done; inv He.
    rewrite Hn; iFrame.
    rewrite embed_fupd; iModIntro; iNext; rewrite embed_fupd; iModIntro; iFrame.
    iMod "Hclose". rewrite embed_fupd; iModIntro.
    rewrite bi.sep_emp.
    by iApply (wp_seq with "H").
Qed.

End wp.

Section adequacy.

Lemma wp_adequacy hlc Σ `{!gen_heapGpreS loc val Σ} `{!inG Σ (@envR val)} `{!invGpreS Σ} `{!inG Σ (excl_authR nat)} F (s : stmt) σ φ :
  (∀ `{!gen_heapGS loc val Σ} `{!envGS val Σ} `{Hinv : !invGS_gen hlc Σ} γ,
     ⊢ |={⊤}=> wp F γ ⊤ s (⌜φ⌝)) →
  adequate(Λ := imp_lang F) NotStuck s (Build_state ∅ σ []) (λ _ _, φ).
Proof.
  intros; eapply wp_adequacy_gen; first done.
  intros; iIntros.
  iMod (gen_heap_init σ) as (?) "[Hh _]".
  iMod (env_init ∅) as (?) "(He & _)".
  iMod (own_alloc) as (?) "H"; first apply (excl_auth_valid O); iDestruct "H" as "(? & N)".
  iExists (λ σ _, state_ctx γ σ), (λ _, True%I).
  rewrite /state_ctx /=; iFrame.
  iPoseProof (monPred_in_entails _ _ (H _ _ _ _) O with "[]") as "Hwp"; clear H;
    monPred.unseal; first done.
  iMod "Hwp" as "Hwp".
  rewrite /wp /stack_top /stack_level; monPred.unseal.
  iSpecialize ("Hwp" with "[//] [$N //]").
  iApply (wp_wand with "Hwp").
  iIntros "!> % (% & _ & $)".
Qed.

End adequacy.
