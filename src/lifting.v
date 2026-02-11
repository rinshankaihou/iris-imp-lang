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

Fixpoint no_return (s:stmt) :=
  match s with
  | Sseq s1 s2 => no_return s1 ∧ no_return s2
  | Sif _ s1 s2 => no_return s1 ∧ no_return s2
  | Swhile _ s => no_return s
  | Sreturn _ => False
  | _ => True
  end.
  
Definition wp_pre' (wp : coPset -d> stmt -d> ( assert) -d> assert) :
    coPset -d> stmt -d> (assert) -d> assert := λ E s Q,
  ((⌜s = skip⌝ ∧ |={E}=> Q) ∨
   (∀ σ ρ, ⎡state_interp σ ρ⎤ ={E,∅}=∗ ∀ r k, stack_match ρ r k -∗
    (* (⌜k=[] -> no_return s⌝) -∗ *)
    ∃ s' r' σ' k',
        ⌜step F s (Build_state r σ k) s' (Build_state r' σ' k')⌝ ∗
        ▷ |={∅,E}=> ∃ ρ', ⎡state_interp σ' ρ' ∗ (stack_match ρ' r' k' ∗ wp E s' Q) (stack_depth k')⎤))%I.

Local Instance wp_pre'_contractive : Contractive (wp_pre').
Proof.
  rewrite /wp_pre' /= => n wp wp' Hwp E s Q.
  do 29 (f_contractive || f_equiv). apply Hwp.
Qed.

Local Definition wp_pre_def := fixpoint wp_pre'.
Local Definition wp_pre_aux : seal (@wp_pre_def). Proof. by eexists. Qed.
Definition wp_pre := wp_pre_aux.(unseal).
Local Lemma wp_pre_unseal   : wp_pre = @wp_pre_def.
Proof. rewrite -wp_pre_aux.(seal_eq) //. Qed.

Lemma wp_unfold E s Q : wp_pre E s Q ⊣⊢ wp_pre' wp_pre E s Q.
Proof. rewrite wp_pre_unseal. apply (fixpoint_unfold wp_pre'). Qed.

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

Definition get_params f := let 'Func params _ _ := f in params.
Definition get_locals f := let 'Func _ locals _ := f in locals.
Definition get_body f := let 'Func _ _ body := f in body.

Definition stack_size f := let 'Func params locals _ := f in
  (length params + length locals)%nat.

Definition stack_frac f := (/ pos_to_Qp (Pos.of_nat (1 + stack_size f)))%Qp.

Definition stack_retainer f := assert_of (λ n,
  stack_frag n (stack_frac f) (stack_frac f) ∅).

Definition stackframe f vs := ([∗ list] x;v ∈ (get_params f ++ get_locals f);vs, points_to_var x v)%I.

(* Definition call_assert E f vs x R := (⇑ (stack_retainer f -∗ stackframe f vs -∗
  wp_pre E (get_body f) ((λ v', ∃ v, ⌜Some v = v'⌝ ∧ stack_retainer f ∗
    (∃ vs, ⌜stack_size f = length vs⌝ ∧ stackframe f vs) ∗
    ⇓ ((∃ v, points_to_var x v) ∗ ▷ (points_to_var x v -∗ R))))))%I. *)

Definition guarded E Q R :=
  ((∀ v, Q v -∗ wp_pre E Sskip R) ∧
   (∀ e, wp_expr E e Q -∗ wp_pre E (Sreturn e) R))%I.

Definition wp_base E s Q := (∀ R, guarded E Q R -∗ wp_pre E s R)%I.
Definition wp E s (Q: assert) := wp_base E s (λ _, Q).

Instance val_inhabited : Inhabited val.
Proof. constructor. refine (NumV 0). Qed.

Lemma wp_skip E Q : Q ⊢ wp E skip Q.
Proof.
  iIntros "Q" (R) "[G _]".
  iApply ("G" $! _ with "[$]").
  Unshelve. repeat constructor. 
Qed.

Lemma wp_return E e Q : wp_expr E e Q ⊢ wp_base E (Sreturn e) Q.
Proof.
  iIntros "Q" (R) "[_ G]".
  by iApply "G".
Qed.

Lemma wp_assign E x e Q : wp_expr E e (λ v, (∃ v0, x ↦v v0) ∗
  ▷ (x ↦v v -∗ Q)) ⊢ wp E (Sassign x e) Q.
Proof.
  iIntros "H" (R) "[G _]".
  iEval (rewrite wp_unfold /wp_pre' /stack_depth). iRight.
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
  iApply ("G" $! (NumV 0) with "[-]").
  iApply ("Hpost" with "[$]").
Qed.

(* Lemma wp_alloc E x Q : (∃ v0, x ↦v v0) ∗
  ▷ (∀ l, points_to_var x (LocV l) -∗ l ↦ NumV 0 -∗ Q None) ⊢ wp E (Salloc x) Q.
Proof.
  iIntros "H" (R) "[G _]".
  iEval (rewrite wp_unfold /wp_pre' /stack_depth). iRight.
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
  l ↦ v0 ∗ ▷ (l ↦ v -∗ Q None))) ⊢ wp E (Sstore e1 e2) Q.
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

Lemma wp_seq E s1 s2 Q : wp E s1 (λ _, ▷ wp E s2 Q) ⊢ wp E (Sseq s1 s2) Q.
Proof.
  split => i.
  iIntros "H".
  iLöb as "IH" forall (s1 s2 Q i).
  rewrite wp_unfold [wp _ (s1;;s2)%S _]wp_unfold /wp_pre.
  (* set (wp as IH. *)
  monPred.unseal.
  iRight.
  iIntros (???<-) "S".
  iDestruct "H" as "[[-> >Hs1] | H]".
  - iApply fupd_mask_intro; first set_solver; iIntros "Hclose" (???<-) "Hstack".
   iExists _, _, _, _. iSplit.
    { iPureIntro. apply SeqS2. }
    { iNext; iFrame.
      destruct (make_stack x2).
      iMod "Hclose". iModIntro.
      rewrite -monPred_at_sep.
      iApply (stack_match_stack_depth with "[$] [$]").
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
    iApply ("IH" with "[$]").
Qed.

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
  ▷ if Z.eqb n 0 then Q None else wp E s (λ _, ▷ wp E (Swhile e s) Q)) ⊢
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
Qed. *)

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
     ⊢ |={⊤}=> wp F ⊤ s (λ _, ⌜φ⌝)) →
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
