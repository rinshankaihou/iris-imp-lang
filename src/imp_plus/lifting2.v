From iris.algebra.lib Require Import excl_auth.
From iris.base_logic Require Import gen_heap.
From iris.program_logic Require Import weakestpre adequacy.
From iris_imp_lang Require Import lifting_expr class_instances stack_ra.
From iris_imp_lang.imp_plus Require Import notation.

Definition to_val s := match s with (skip, Kstop) => Some tt | _ => None end.

Lemma implang_mixin F : LanguageMixin(observation := Empty_set) (λ _, (skip, Kstop)) to_val
    (λ s σ obs s' σ' es, obs = [] ∧ es = [] ∧ step F s.1 (Build_state σ.1 σ.2 s.2) s'.1 (Build_state σ'.1 σ'.2 s'.2)).
Proof.
  split.
  - by intros [].
  - by destruct e as [[] []]; inversion 1.
  - by intros (?,?)??(?,?)?? (? & ? & H); inv H; simpl in *; subst.
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

Context `{!gen_heapGS loc val Σ} `{!envGS val Σ} `{!invGS_gen hlc Σ} `{!inG Σ (excl_authR (leibnizO cont))}.

Variable (F : func_env).
Variable (γ : gname).

Fixpoint cont_to_stack k : env_state * nat :=
  match k with
  | Kstop => (∅, O)
  | Kcall _ r k' => let '(ρ, n) := cont_to_stack k' in (<[n := r]>ρ, S n)
  | Kseq _ k' | Kwhile _ _ k' => cont_to_stack k'
  end.

Definition stack_depth k := snd (cont_to_stack k).

Canonical Structure imp_plus_lang := Language (implang_mixin F).

Definition state_ctx s := (gen_heap_interp s.2 ∗
  ∃ k, let '(ρ0, n) := cont_to_stack k in env_auth (<[n := s.1]>ρ0) ∗ own γ (●E (k : leibnizO cont)))%I.

Global Instance implang_irisG : irisGS_gen hlc imp_plus_lang Σ := {
  iris_invGS := _;
  state_interp s _ _ _ := state_ctx s;
  fork_post _ := True%I;
  num_laters_per_step _ := 0%nat;
  state_interp_mono _ _ _ _ := fupd_intro _ _;
}.

Definition stack_match k := (⎡own γ (◯E k)⎤ ∗ stack_level (stack_depth k))%I.

Definition wp_sk E s k Q := (stack_match k -∗
  ⎡wp NotStuck E (s, k) (λ _, ∃ k', own γ (◯E k') ∗ Q (stack_depth k'))⎤)%I.

Record postassert :=
  { Qnormal : assert; Qbreak : assert; Qcontinue : assert; Qreturn : val → assert }.

Definition guarded E Q k R :=
  ((Qnormal Q -∗ wp_sk E Sskip k R) ∧
   (Qbreak Q -∗ ∃ e s k', ⌜find_loop k = Some (Kwhile e s k')⌝ ∧ wp_sk E Sskip k' R) ∧
   (Qcontinue Q -∗ ∃ k', ⌜find_loop k = Some k'⌝ ∧ wp_sk E Sskip k' R) ∧
   (∀ e, wp_expr E e (Qreturn Q) -∗ wp_sk E (Sreturn e) (find_call k) R))%I.

Definition wp E s Q := (∀ k R, guarded E Q k R -∗ wp_sk E s k R)%I.

Lemma guarded_mono E P Q k R :
  (Qnormal P -∗ Qnormal Q) ∧
  (Qbreak P -∗ Qbreak Q) ∧
  (Qcontinue P -∗ Qcontinue Q) ∧
  (∀ v, Qreturn P v -∗ Qreturn Q v) ⊢
  guarded E Q k R -∗ guarded E P k R.
Proof.
  rewrite /guarded; iIntros "HPQ H"; iSplit; [|iSplit; [|iSplit]].
  - by iIntros "HQ"; iApply "H"; iApply "HPQ".
  - by iIntros "HQ"; iApply "H"; iApply "HPQ".
  - by iIntros "HQ"; iApply "H"; iApply "HPQ".
  - iIntros (?) "He"; iApply "H".
    iApply (wp_expr_mono with "[HPQ] He").
    iDestruct "HPQ" as "(_ & _ & _ & $)".
Qed.

Lemma wp_mono E s P Q :
  (Qnormal P -∗ Qnormal Q) ∧
  (Qbreak P -∗ Qbreak Q) ∧
  (Qcontinue P -∗ Qcontinue Q) ∧
  (∀ v, Qreturn P v -∗ Qreturn Q v) ⊢
  wp E s P -∗ wp E s Q.
Proof.
  rewrite /wp; iIntros "HPQ H" (??) "Hguard".
  by iApply "H"; iApply (guarded_mono with "HPQ").
Qed.

Lemma wp_skip E Q : Qnormal Q ⊢ wp E skip Q.
Proof.
  iIntros "H %% Hguard"; by iApply "Hguard".
Qed.

(* Lemma var_e : forall k x v s,
  stack_match k ∗ x ↦v v ∗ ⎡state_ctx s⎤ ⊢ ⌜s.1 !! x = Some v⌝.
Proof.
  intros; rewrite /state_ctx /stack_match /stack_level.
  split => ?; monPred.unseal.
  iIntros "((N & <-) & Hx & _ & % & % & %Hm & Hρ & N')".
  iCombine "N N'" gives %->%excl_auth_agree_L.
  iDestruct (var_e with "[$Hx $Hρ]") as %?.
  by rewrite /env_to_environ lookup_insert in H.
Qed.

Lemma var_update : forall n x v v' s,
  stack_top n ∗ x ↦v v ∗ ⎡state_ctx s⎤ ⊢
  |==> stack_top n ∗ x ↦v v' ∗ ⎡state_ctx (<[x := v']> s.1, s.2)⎤.
Proof.
  intros; rewrite /state_ctx /stack_top /stack_level.
  split => ?; monPred.unseal.
  iIntros "((N & %H) & Hx & $ & % & % & % & Hρ & N')"; hnf in H; subst.
  iCombine "N N'" gives %<-%excl_auth_agree_L.
  iMod (var_update with "[$Hx $Hρ]") as "(? & $)".
  rewrite /set_var lookup_insert insert_insert; by iFrame.
Qed. 

Lemma wp_expr_app E e Q n s : wp_expr E e Q -∗ stack_top n -∗
  ⎡state_ctx s⎤ ={E}=∗ ∃ v, ⌜eval_expr e s.1 s.2 v⌝ ∗ stack_top n ∗
  ⎡state_ctx s⎤ ∗ Q v.
Proof.
  rewrite /state_ctx; wp_expr.unseal.
  iIntros "H (N & #L) (Hσ & % & % & % & Hρ & N')".
  iMod ("H" with "[$Hσ $Hρ]") as (?) "(He & ($ & $) & HQ)".
  iCombine "N N'" gives %->%excl_auth_agree_L.
  iFrame; iFrame "#".
  iStopProof; split => ?; rewrite /stack_level; monPred.unseal; rewrite monPred_at_intuitionistically.
  iIntros "(% & H) !>"; iSplit => //.
  iApply ("H" with "[//]").
  by rewrite lookup_insert.
Qed.

Lemma stack_top_embed n (P : assert) : stack_top n -∗ P -∗ ⎡own γ (◯E n) ∗ P n⎤.
Proof.
  iIntros "($ & #L) P". by iApply stack_level_embed.
Qed.

Lemma wp_assign E x e Q : wp_expr E e (λ v, (∃ v0, points_to_var x v0) ∗
  ▷ (points_to_var x v -∗ Qnormal Q)) ⊢ wp E (Sassign x e) Q.
Proof.
  iIntros "H %% Hguard".
  rewrite /wp_sk wp_unfold /wp_pre /=.
  iIntros "N" (?????) "S".
  iMod (wp_expr_app with "H N S") as (? He) "(N & S & (% & Hx) & Hpost)".
  rewrite embed_fupd; iApply fupd_mask_intro; first set_solver; iIntros "Hclose".
  iDestruct (var_e with "[$N $Hx $S]") as %Hx.
  iSplit.
  { iPureIntro. eexists _, (_,_), (_,_), _; split; first done; split; first done; by constructor. }
  iIntros ((?,?)(?,?)? (-> & -> & H)); inv H; simpl in *; subst.
  eapply eval_expr_det in He; last done; subst.
  iIntros "?".
  rewrite embed_fupd; iModIntro; iNext; rewrite embed_fupd; iModIntro.
  iMod (var_update with "[$N $Hx $S]") as "(N & Hx & $)".
  iMod "Hclose"; rewrite embed_fupd; iModIntro.
  rewrite bi.sep_emp.
  iDestruct "Hguard" as "(Hguard & _)".
  iApply ("Hguard" with "[-N] N").
  by iApply "Hpost".
Qed.

Lemma wp_alloc E x Q : (∃ v0, points_to_var x v0) ∗
  ▷ (∀ l, points_to_var x (LocV l) -∗ l ↦ NumV 0 -∗ Qnormal Q) ⊢ wp E (Salloc x) Q.
Proof.
  iIntros "H %% Hguard N".
  rewrite wp_unfold /wp_pre /=.
  iIntros (?????) "S".
  iDestruct "H" as "((% & Hx) & Hpost)".
  rewrite embed_fupd; iApply fupd_mask_intro; first set_solver; iIntros "Hclose".
  iDestruct (var_e with "[$Hx $S $N]") as %Hx.
  iSplit.
  { iPureIntro. eexists _, (_,_), (_,_), _; split; first done; split; first done; constructor. }
  iIntros ((?,?)(?,?)? (-> & -> & H)) "?"; inv H; simpl in *; subst.
  rewrite embed_fupd; iModIntro; iNext; rewrite embed_fupd; iModIntro.
  iMod (var_update with "[$Hx $S $N]") as "(N & Hx & S)".
  iDestruct "S" as "(Hσ & % & % & % & Hρ & $)".
  iMod (state_interp_alloc with "[$Hσ $Hρ]") as "(($ & $) & ?)".
  { apply next_loc_new. }
  iMod "Hclose"; rewrite embed_fupd; iModIntro.
  rewrite bi.sep_emp; iSplit => //.
  iDestruct "Hguard" as "(Hguard & _)".
  iApply ("Hguard" with "[-N] N").
  by iApply ("Hpost" with "[$]").
Qed.

Lemma wp_store E e1 e2 Q : wp_expr E e2 (λ v, wp_expr E e1 (λ v1, ∃ l v0, ⌜v1 = LocV l⌝ ∧
  l ↦ v0 ∗ ▷ (l ↦ v -∗ Qnormal Q))) ⊢ wp E (Sstore e1 e2) Q.
Proof.
  iIntros "H %% Hguard N".
  rewrite wp_unfold /wp_pre /=.
  iIntros (?????) "S".
  iMod (wp_expr_app with "H N S") as (? He2) "(N & S & H)".
  iMod (wp_expr_app with "H N S") as (? He1) "(N & S & % & % & -> & Hl & Hpost)".
  rewrite embed_fupd; iApply fupd_mask_intro; first set_solver; iIntros "Hclose".
  iDestruct "S" as "(Hσ & % & % & %Hm & Hρ & ?)".
  iDestruct (state_interp_load with "[$Hσ $Hρ] Hl") as %Hl.
  iSplit.
  { iPureIntro. eexists _, (_,_), (_,_), _; split; first done; split; first done; by econstructor. }
  iIntros ((?,?)(?,?)? (-> & -> & H)) "?"; inv H; simpl in *; subst.
  eapply eval_expr_det in He2; last done.
  eapply eval_expr_det in He1; last done; inv He1.
  rewrite embed_fupd; iModIntro; iNext; rewrite embed_fupd; iModIntro.
  iMod (state_interp_store with "[$Hσ $Hρ] Hl") as "(($ & ?) & ?)"; iFrame.
  iMod "Hclose"; rewrite embed_fupd; iModIntro.
  rewrite bi.sep_emp; iSplit => //.
  iDestruct "Hguard" as "(Hguard & _)".
  iApply ("Hguard" with "[-N] N").
  by iApply ("Hpost" with "[$]").
Qed.

Definition set_normal Q R :=
  {| Qnormal := R; Qbreak := Qbreak Q; Qcontinue := Qcontinue Q; Qreturn := Qreturn Q |}.

Lemma wp_seq E s1 s2 Q : ▷ wp E s1 (set_normal Q (▷ wp E s2 Q)) ⊢ wp E (Sseq s1 s2) Q.
Proof.
  iIntros "H %% Hguard N".
  rewrite wp_unfold /wp_pre /=.
  iIntros (?????) "S".
  rewrite embed_fupd; iApply fupd_mask_intro; first set_solver; iIntros "Hclose".
  iSplit.
  { iPureIntro. eexists _, (_,_), (_,_), _; split; first done; split; first done; by econstructor. }
  iIntros ((?,?)(?,?)? (-> & -> & H)) "?"; inv H; simpl in *; subst.
  rewrite embed_fupd; iModIntro; iNext; rewrite embed_fupd; iModIntro.
  iFrame; rewrite bi.sep_emp.
  iMod "Hclose" as "_"; rewrite embed_fupd; iModIntro.
  iApply ("H" with "[-N] [N]"); last done.
  rewrite /guarded.
  iSplit => /=; last by iDestruct "Hguard" as "[_ $]".
  iIntros "H N"; rewrite wp_unfold /wp_pre /=.
  iIntros (?????) "S".
  rewrite embed_fupd; iApply fupd_mask_intro; first set_solver; iIntros "Hclose".
  iSplit.
  { iPureIntro. eexists _, (_,_), (_,_), _; split; first done; split; first done; by econstructor. }
  iIntros ((?,?)(?,?)? (-> & -> & H)) "?"; inv H; simpl in *; subst.
  inv H5.
  rewrite embed_fupd; iModIntro; iNext; rewrite embed_fupd; iModIntro.
  iFrame; rewrite bi.sep_emp.
  iMod "Hclose" as "_".
  rewrite embed_fupd; iModIntro.
  by iApply ("H" with "Hguard").
Qed.

Lemma wp_if E e s1 s2 Q : wp_expr E e (λ v, ∃ n, ⌜v = NumV n⌝ ∧
  ▷ wp E (if Z.eqb n 0 then s2 else s1) Q) ⊢ wp E (Sif e s1 s2) Q.
Proof.
  iIntros "H %% Hguard N".
  rewrite wp_unfold /wp_pre /=.
  iIntros (?????) "S".
  iMod (wp_expr_app with "H N S") as (? He) "(N & S & % & -> & H)".
  rewrite embed_fupd; iApply fupd_mask_intro; first set_solver; iIntros "Hclose".
  iSplit.
  { iPureIntro. eexists _, (_,_), (_,_), _; split; first done; split; first done; by econstructor. }
  iIntros ((?,?)(?,?)? (-> & -> & H)) "?"; inv H; simpl in *; subst.
  eapply eval_expr_det in He; last done; inv He.
  rewrite embed_fupd; iModIntro; iNext; rewrite embed_fupd; iModIntro.
  iMod "Hclose" as "_".
  iFrame; rewrite bi.sep_emp embed_fupd; iModIntro.
  by iApply ("H" with "Hguard").
Qed.

Definition loop_post Q R :=
  {| Qnormal := R; Qbreak := Qnormal Q; Qcontinue := R; Qreturn := Qreturn Q |}.

Lemma wp_while E e s Q : wp_expr E e (λ v, ∃ n, ⌜v = NumV n⌝ ∧
  ▷ if Z.eqb n 0 then Qnormal Q else wp E s (loop_post Q (▷ wp E (Swhile e s) Q))) ⊢
  wp E (Swhile e s) Q.
Proof.
  iIntros "H %% Hguard N".
  rewrite wp_unfold /wp_pre /=.
  iIntros (?????) "S".
  iMod (wp_expr_app with "H N S") as (? He) "(N & S & % & -> & H)".
  rewrite embed_fupd; iApply fupd_mask_intro; first set_solver; iIntros "Hclose".
  destruct (Z.eqb_spec n 0).
  - subst; iSplit.
    { iPureIntro. eexists _, (_,_), (_,_), _; split; first done; split; first done; by econstructor. }
    iIntros ((?,?)(?,?)? (-> & -> & H)) "?"; inv H; simpl in *; subst.
    eapply eval_expr_det in He; last done; inv He.
    rewrite embed_fupd; iModIntro; iNext; rewrite embed_fupd; iModIntro.
    iMod "Hclose"; rewrite embed_fupd; iModIntro.
    iFrame; rewrite bi.sep_emp.
    iDestruct "Hguard" as "(Hguard & _)".
    by iApply ("Hguard" with "[-N] N").
  - iSplit.
    { iPureIntro. eexists _, (_,_), (_,_), _; split; first done; split; first done; simpl; by eapply WhileTS. }
    iIntros ((?,?)(?,?)? (-> & -> & H)) "?"; inv H; simpl in *; subst.
    2: { eapply eval_expr_det in He; last done; inv He. }
    eapply eval_expr_det in He; last done; inv He.
    rewrite embed_fupd; iModIntro; iNext; rewrite embed_fupd; iModIntro.
    iMod "Hclose" as "_"; rewrite embed_fupd; iModIntro.
    iFrame; rewrite bi.sep_emp.
    iApply ("H" with "[-N] [N]"); last done.
    rewrite /guarded.
    iSplit; [|iSplit; [|iSplit]]; simpl.
    + iIntros "H N"; rewrite wp_unfold /wp_pre /=.
      iIntros (?????) "S".
      rewrite embed_fupd; iApply fupd_mask_intro; first set_solver; iIntros "Hclose".
      iSplit.
      { iPureIntro. eexists _, (_,_), (_,_), _; split; first done; split; first done; simpl; by constructor. }
      iIntros ((?,?)(?,?)? (-> & -> & H)) "?"; inv H; simpl in *; subst.
      inv H5.
      rewrite embed_fupd; iModIntro; iNext; rewrite embed_fupd; iModIntro.
      iMod "Hclose"; rewrite embed_fupd; iModIntro.
      iFrame; rewrite bi.sep_emp.
      by iApply ("H" with "[-N] [N]").
    + iIntros "H"; iExists _, _, _; iSplit => //.
      by iApply "Hguard".
    + iIntros "H"; iExists _; iSplit => //.
      iIntros "N"; rewrite wp_unfold /wp_pre /=.
      iIntros (?????) "S".
      rewrite embed_fupd; iApply fupd_mask_intro; first set_solver; iIntros "Hclose".
      iSplit.
      { iPureIntro. eexists _, (_,_), (_,_), _; split; first done; split; first done; simpl; by constructor. }
      iIntros ((?,?)(?,?)? (-> & -> & H)) "?"; inv H; simpl in *; subst.
      inv H5.
      rewrite embed_fupd; iModIntro; iNext; rewrite embed_fupd; iModIntro.
      iMod "Hclose"; rewrite embed_fupd; iModIntro.
      iFrame; rewrite bi.sep_emp.
      by iApply ("H" with "[-N] [N]").
    + iDestruct "Hguard" as "(_ & _ & _ & $)".
Qed.

Lemma wp_while_inv E e s P Q : □ (P -∗ wp_expr E e (λ v, ∃ n, ⌜v = NumV n⌝ ∧
  ▷ if Z.eqb n 0 then Qnormal Q else wp E s (loop_post Q P))) ⊢
  P -∗ ▷ (P -∗ wp_expr E e (λ v, ⌜v = NumV 0⌝ → Qnormal Q)) -∗ wp E (Swhile e s) Q.
Proof.
  iIntros "#He HP HQ".
  iLöb as "IH".
  iApply wp_while.
  iPoseProof ("He" with "HP") as "H"; iApply (wp_expr_mono with "[-H] H").
  iIntros (?) "(% & -> & H)".
  iExists _; iSplit => //; iNext.
  destruct (n =? 0)%Z eqn: Hn; first done.
  iApply (wp_mono with "[HQ] H"); simpl.
  iSplit; [|iSplit; [|iSplit]]; try by iIntros.
  - iIntros "HP"; iApply ("IH" with "HP HQ").
  - iIntros "HP"; iApply ("IH" with "HP HQ").
Qed.
  
Lemma cont_to_stack_loop k e s k' : find_loop k = Some (Kwhile e s k') →
  cont_to_stack k = cont_to_stack k'.
Proof.
  induction k; try done; simpl.
  by inversion 1.
Qed.

Lemma stack_depth_loop k e s k' : find_loop k = Some (Kwhile e s k') →
  stack_depth k = stack_depth k'.
Proof.
  intros; rewrite /stack_depth; f_equal; by eapply cont_to_stack_loop.
Qed.

Lemma wp_break E Q : Qbreak Q ⊢ wp E Sbreak Q.
Proof.
  iIntros "H %% Hguard N".
  iDestruct "Hguard" as "(_ & Hguard & _)".
  iDestruct ("Hguard" with "H") as (??? Hk) "H".
  rewrite wp_unfold /wp_pre /=.
  iIntros (?????) "S".
  rewrite embed_fupd; iApply fupd_mask_intro; first set_solver; iIntros "Hclose".
  iSplit.
  { iPureIntro. eexists _, (_,_), (_,_), _; split; first done; split; first done; by econstructor. }
  iIntros ((?,?)(?,?)? (-> & -> & H)) "?"; inv H; simpl in *; subst.
  rewrite embed_fupd; iModIntro; iNext; rewrite embed_fupd; iModIntro.
  iFrame; rewrite bi.sep_emp.
  rewrite H5 in Hk; inv Hk.
  iMod "Hclose" as "_"; rewrite embed_fupd; iModIntro.
  erewrite stack_depth_loop by done.
  iApply ("H" with "N").
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

Lemma stack_depth_loop' k k' : find_loop k = Some k' →
  stack_depth k = stack_depth k'.
Proof.
  intros; rewrite /stack_depth; f_equal; by eapply cont_to_stack_loop'.
Qed.

Lemma wp_continue E Q : Qcontinue Q ⊢ wp E Scontinue Q.
Proof.
  iIntros "H %% Hguard N".
  iDestruct "Hguard" as "(_ & _ & Hguard & _)".
  iDestruct ("Hguard" with "H") as (? Hk') "H".
  edestruct find_loop_while as (? & ? & ? & ?); first done; subst.
  rewrite wp_unfold /wp_pre /=.
  iIntros (?????) "S".
  rewrite embed_fupd; iApply fupd_mask_intro; first set_solver; iIntros "Hclose".
  iSplit.
  { iPureIntro. eexists _, (_,_), (_,_), _; split; first done; split; first done; by econstructor. }
  iIntros ((?,?)(?,?)? (-> & -> & H)) "?"; inv H; simpl in *; subst.
  rewrite embed_fupd; iModIntro; iNext; rewrite embed_fupd; iModIntro.
  iFrame; rewrite bi.sep_emp.
  rewrite H5 in Hk'; inv Hk'.
  iMod "Hclose" as "_"; rewrite embed_fupd; iModIntro.
  erewrite stack_depth_loop' by done.
  iApply ("H" with "N").
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

Lemma wp_exprs_app E es Q n s k : wp_exprs E es Q -∗ stack_top n -∗ ⎡state_ctx s⎤ ={E}=∗
  ∃ vs, ⌜eval_exprs' es (Build_state s.1 s.2 k) vs⌝ ∗ stack_top n ∗ ⎡state_ctx s⎤ ∗ Q vs.
Proof.
  iIntros "Hes N S"; iInduction es as [|e es] "IH" forall (Q); simpl.
  - iFrame. iPureIntro; constructor.
  - iMod (wp_expr_app with "Hes N S") as (??) "(N & S & Hes)".
    iMod ("IH" with "Hes N S") as (??) "$".
    iPureIntro; by constructor.
Qed.

Lemma stack_depth_max : forall k ρ n,
  cont_to_stack k = (ρ, n) → ∀ m, (n ≤ m)%nat → ρ !! m = None.
Proof.
  induction k; simpl; try done.
  - inversion 1; intros; by rewrite lookup_empty.
  - destruct (cont_to_stack k) eqn: Hk; inversion 1; subst; intros.
    rewrite lookup_insert_ne; last lia.
    eapply IHk; eauto; lia.
Qed.

Lemma add_frame s n xs vs : ⎡state_ctx s⎤ ∗ stack_top n ⊢
  |==> ⎡state_ctx (bind_vars xs vs, s.2)⎤ ∗ ⇑ (stack_top (S n) ∗
    assert_of (λ n, stack_frag n (/ pos_to_Qp (Pos.of_nat (1 + size (bind_vars xs vs))))%Qp 1%Qp (bind_vars xs vs))).
Proof.
  intros; rewrite /state_ctx /stack_top /=.
  iIntros "((Hσ & % & % & % & Hρ & N') & N & #L)".
  iCombine "N N'" gives %->%excl_auth_agree_L.
  iMod (state_interp_alloc_frame _ _ (S n) with "[$Hσ $Hρ]") as "(($ & $) & ?)".
  { rewrite lookup_insert_ne //.
    apply H; lia. }
  iMod (own_update_2 with "N' N") as "($ & N)".
  { apply excl_auth_update. }
  iModIntro.
  rewrite -!up1_sep -up1_objective; iFrame.
  iSplit.
  { iPureIntro; intros; rewrite lookup_insert_ne; last lia; apply H; lia. }
  iSplit; first by iApply stack_level_up.
  iStopProof; split => ?; rewrite /stack_level; monPred.unseal; rewrite monPred_at_intuitionistically /=.
  iIntros "(<- & $)".
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

(*Lemma remove_frame s r0 n q r' :
  ⎡state_ctx s⎤ ∗ stack_top (S n) ∗ assert_of (λ n, stack_frag n q 1%Qp r') ⊢
  |==> ⎡state_ctx (r0, s.2)⎤ ∗ ⇓ stack_top n.
Proof.
  intros; rewrite /state_ctx /stack_top /=.
  iIntros "((Hσ & % & % & % & Hρ & N') & (N & #Hl) & H)".
  iCombine "N N'" gives %[=]%excl_auth_agree_L; subst.
  iMod (state_interp_dealloc_frame _ _ (S n) with "[$Hσ $Hρ H]") as "($ & ?)".
  { iApply (stack_level_embed with "Hl H"). }
  iMod (own_update_2 with "N' N") as "($ & N)".
  { apply excl_auth_update. }
  iModIntro.
  rewrite -!down1_sep -down1_objective; iFrame.
  iPoseProof (stack_level_down with "Hl") as "$".
  iExists 
  iClear "#"; iStopProof; do 2 f_equiv.
  apply (delete_insert _ _ s.(ρ)).
  rewrite lookup_insert_ne //; eapply stack_depth_max; eauto.
Qed.*)

Lemma eval_exprs_det e s v1 : eval_exprs' e s v1 → forall v2, eval_exprs' e s v2 →
  v1 = v2.
Proof.
  induction 1; inversion 1; subst; try congruence.
  expr_det; f_equiv; auto.
Qed.

Lemma wp_call E x f es Q : wp_exprs E es (λ vs, ∃ fd, ⌜F !! f = Some fd ∧
    length es = length (get_params fd) ∧ NoDup (get_params fd ++ get_locals fd)⌝ ∧
  ▷ call_assert E fd (vs ++ repeat (NumV 0) (length (get_locals fd))) x (Qnormal Q)) ⊢
  wp E (Scall x f es) Q.
Proof.
  iIntros "H %% Hguard N".
  rewrite wp_unfold /wp_pre /=.
  iIntros (?????) "S".
  iMod (wp_exprs_app with "H N S") as (? Hes) "(N & S & %fd & (%Hf & %Hlen & %Hnodup) & H)".
  destruct fd; simpl in *.
  rewrite embed_fupd; iApply fupd_mask_intro; first set_solver; iIntros "Hclose".
  iSplit.
  { iPureIntro. eexists _, (_,_), (_,_), _; split; first done; split; first done; by econstructor. }
  iIntros ((?,?)(?,?)? (-> & -> & H)) "?"; inv H; simpl in *; subst.
  eapply eval_exprs_det in Hes; last done; subst.
  rewrite embed_fupd; iModIntro; iNext; rewrite embed_fupd; iModIntro.
  iMod (add_frame with "[$S $N]") as "($ & N)".
  iMod "Hclose" as "_".
  iApply up1_obj_elim; iApply up1_mono; last first.
  { rewrite -(up1_down1 (guarded _ _ _ _)) /call_assert.
    iCombine "Hguard H N" as "H"; rewrite !up1_sep; iApply "H". }
  iIntros "(Hguard & H & N & Hframe)".
  rewrite bi.sep_emp.
  assert (length (func_params ++ func_locals) = length (vs ++ repeat (NumV 0) (length func_locals))) as Hlen'.
  { rewrite !app_length repeat_length; f_equal.
    rewrite -Hlen; by eapply Forall2_length. }
  rewrite split_stackframe //; iDestruct "Hframe" as "(Hret & Hframe)".
  rewrite embed_fupd; iModIntro.
  iApply ("H" with "Hret Hframe [Hguard]").
  do 3 (iSplit; first iIntros "[]").
  iIntros (?) "He N"; simpl.
  rewrite wp_unfold /wp_pre /=.
  iIntros (?????) "S".
  iMod (wp_expr_app with "He N S") as (? He) "(N & S & Hret & (% & %Hlens & Hframe) & Hpost)".
  rewrite embed_fupd; iApply fupd_mask_intro; first set_solver; iIntros "Hclose".
  iSplit.
  { iPureIntro. eexists _, (_,_), (_,_), _; split; first done; split; first done; by econstructor. }
  iIntros ((?,?)(?,?)? (-> & -> & H)) "?"; inv H; simpl in *; subst.
  inv H8.
  rewrite embed_fupd; iModIntro; iNext; rewrite embed_fupd; iModIntro.
  rewrite -down1_sep down1_later.
  iMod (remove_frame with "[$S $N Hret Hframe]") as "(S & N)".
  { iCombine "Hret Hframe" as "H"; rewrite -split_stackframe //.
    rewrite app_length //. }
  iDestruct "Hpost" as "(Hx & Hpost)".
  iAssert (⇓ |==> ∃ ρ', stack_match ρ' (<[x:=v]> r) k ∗ x ↦v v ∗ ⎡state_interp σ ρ'⎤)%I
    with "[S Hx Hstack]" as "H'".
  { iModIntro. iDestruct "Hx" as "[% ?]". iApply var_update; iFrame. }
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
  iIntros "H %% Hguard N".
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
*)
End wp.
(*
Section adequacy.

Definition normal_post `{envGS val Σ} Q :=
  {| Qnormal := Q; Qbreak := False%I; Qcontinue := False%I; Qreturn := λ _, False%I |}.

Lemma guarded_stop `{!gen_heapGS loc val Σ} `{!envGS val Σ} `{!invGS_gen hlc Σ} `{!inG Σ (excl_authR nat)}
  F γ Q : ⊢ guarded F γ ⊤ (normal_post Q) Kstop Q.
Proof.
  iSplit; last repeat (iSplit; [iIntros "[]"|]); simpl.
  - iIntros "? ?"; rewrite wp_unfold /wp_pre /=.
    rewrite embed_fupd; iModIntro; iExists _; by iApply (stack_top_embed with "[$]").
  - iIntros (?) "He N".
    rewrite wp_unfold /wp_pre /=.
    iIntros (?????) "S".
    iMod (wp_expr_app with "He N S") as (? He) "(N & S & [])".
Qed.

Lemma wp_adequacy hlc Σ `{!gen_heapGpreS loc val Σ} `{!inG Σ (@envR val)} `{!invGpreS Σ} `{!inG Σ (excl_authR nat)} F (s : stmt) σ φ :
  (∀ `{!gen_heapGS loc val Σ} `{!envGS val Σ} `{Hinv : !invGS_gen hlc Σ} γ,
     ⊢ |={⊤}=> wp F γ ⊤ s (normal_post ⌜φ⌝)) →
  adequate(Λ := imp_plus_lang F) NotStuck (s, Kstop) (∅, σ) (λ _ _, φ).
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
  rewrite /wp /wp_sk /stack_top /stack_level; monPred.unseal.
  iSpecialize ("Hwp" with "[//] [] [//] [N]").
  { iApply (monPred_in_entails with "[-]"); first apply guarded_stop.
    by monPred.unseal. }
  { by iFrame. }
  iApply (wp_wand with "Hwp").
  iIntros "!> % (% & _ & $)".
Qed.

End adequacy.
*)