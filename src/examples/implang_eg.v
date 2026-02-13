From iris_simp_lang Require Import implang imp_notation lifting_expr lifting stack_ra.

Open Scope func_scope.

Definition incr :=
    fn "x" <{ ( )
            "x" <a- "x" + #1  |
            Return "x"
        }>.

Definition F : func_env :=
    <[ "incr" := incr ]> ∅.

Definition call_incr : stmt :=
    Alloc "a";;
    "a" <s- #2 ;;
    "r" <- "incr" (!"a").

Section WPExample.

    Context `{!gen_heapGS loc val Σ} `{!envGS val Σ} `{!invGS_gen HasNoLc Σ}.

    Instance nodup_val_decision (vs: list val): Decision (NoDup vs).
    Proof. apply NoDup_dec. Qed.

    Ltac contradict_in_list :=
        match goal with H : _ ∈ _ |- _ => inversion H end.
    Ltac solve_not_in :=
        match goal with
        | |- _ ∉ _ => intro H; inversion H
        end;
        repeat contradict_in_list.
    Ltac solve_no_dup :=
        repeat constructor; solve_not_in.

    Global Instance up1_proper_entails : Proper (flip bi_entails ==> flip bi_entails) up1.
    Proof. split => ? /=. apply H. Qed.
    Global Instance down1_proper_entail : Proper (flip bi_entails ==> flip bi_entails) down1.
    Proof. split => ? /=. apply H. Qed.

    Lemma wp_incr E z' z:
        "r" ↦v NumV z'
        ⊢ call_assert F E incr [NumV z%Z] "r" ("r" ↦v NumV (z+1)).
    Proof.
        rewrite /call_assert !up1_wand /stackframe -up1_sep /=.
        iIntros "r retainer [x _]".
        remember stack_retainer as retainer.
        rewrite -wp_assign -wp_binop -wp_var -up1_sep.
        iFrame. rewrite up1_wand. iIntros "x".
        rewrite -wp_val /= -up1_sep up1_exist. iFrame.
        rewrite up1_later up1_wand. iIntros "!> x".
        rewrite -wp_var.
        rewrite -up1_sep. iFrame.
        rewrite up1_wand. iIntros "x".
        rewrite -!up1_sep up1_exist up1_down1. iFrame.
        iSplitL "x".
        {
            iExists (cons _ nil). simpl.
            iStopProof; apply up1_mono.
            iIntros; iSplit; [done | iFrame].
        }
        iIntros "!> $".
    Qed.

    Lemma wp_call_incr E :
        "a" ↦v NumV 0 ∗ "r" ↦v NumV 0
        ⊢ wp F E call_incr ("r" ↦v NumV 3)%I.
    Proof.
        iIntros "[a r]".
        rewrite -wp_seq -wp_alloc. iFrame.
        iIntros "!>" (l) "a l !>".
        rewrite -wp_seq -wp_store -wp_val -wp_var.
        iFrame. iIntros "a".
        iExists _, _. iSplit; try done. iFrame. iIntros "!> l !>".
        rewrite -wp_call /= -wp_load -wp_var. 
        iFrame. iIntros "a".
        iExists _, _. iSplit; try done. iFrame. iIntros "?".
        iExists _.
        iSplit; [iPureIntro; split; last split|].
        { rewrite lookup_insert_Some; left; done. }
        { done. }
        { solve_no_dup. }
        iModIntro.
        simpl.
        rewrite -wp_incr.
        iFrame.
    Qed.

End WPExample.