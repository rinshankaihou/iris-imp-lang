From iris_imp_lang.imp Require Import imp.

Local Open Scope func_scope.

Definition incr :=
    fn "x" <{ ( )
            "x" <a- "x" + #1  |
            Return "x"
        }>.

Definition F : func_env :=
    <[ "incr" := incr ]> ∅.

Definition call_incr : stmt :=
    Alloc "a";;
    (* store #2 to the location stored in variable "a" *)
    "a" <s- #2 ;;
    (* load the stored value, increment the value, stores return value in variable "r" *)
    "r" <- "incr" (!"a"). 

Section spec.

    Context `{!impGS hlc Σ}.

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

    (* spec for function incr *)
    Lemma wp_incr E z' z:
        "r" ↦v NumV z'
        ⊢ call_assert F E incr [NumV z%Z] "r" ("r" ↦v NumV (z+1)).
    Proof.
        rewrite /call_assert /=.
        iIntros "r retainer [x _] !>".
        remember stack_retainer as retainer.
        rewrite -wp_assign -wp_binop -wp_var.
        iFrame. iIntros "x".
        rewrite -wp_val /=. iFrame.
        iIntros "!> x".
        rewrite -wp_var. iFrame. iIntros "x".
        iFrame.
        iSplitL "x".
        {
            iExists (cons _ nil). iSplit; first done.
            rewrite /stackframe /=. iFrame.
        }
        iIntros "!> !> $".
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

End spec.