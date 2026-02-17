From iris_simp_lang Require Import implang_cont imp_cont_notation lifting_expr lifting_cont
  stack_ra proofmode_imp_cont imp_class_instances.

Local Open Scope func_scope.

(* Returns the minimum positive integer, or #0 if there isn't one.
  l: pointer to a linked list or null, each cell is (value, ptr_to_next_cell) *)
Definition min_positive :=
  fn "l" <{ ( "min" "v" )
    "min" <a- #0 ;;
    While "l" ≠ #0 <{
      (* If !"l" < !"min" <{ break }> ;; *)
      "v" <a- !"l";;
      "l" <a- !("l" + #1);;
      If "v" <= #0 <{ continue }> ;;
      If "min" = #0 || "v" < "min" <{ "min" <a- "v" }> 
    }>;;
    Return "min"
  }>.

Definition F : func_env :=
    <[ "min_positive" := min_positive ]> ∅.

Section spec.

  Context `{!gen_heapGS loc val Σ} `{!envGS val Σ} `{!invGS_gen HasNoLc Σ}.

  Local Open Scope bi_scope.

  Definition min_positive_r (lv: list Z) : Z :=
    foldr Z.min 0%Z lv.

  Definition ptr_add (l: loc) (i: Z) : loc :=
    (l + i)%Z.
  Notation "l +ₗ i" := (ptr_add l i) (at level 10, left associativity).

  (* a segment of linked list starting with l and stores lv;
    the last cell has pointer `last` that might or might not be empty *)
  Fixpoint llist_seg (l: loc) (lv: list Z) (last: loc) : assert :=
    match lv with
    | [] => ⌜l = last⌝
    | v :: lv' => ⌜l≠0%Z⌝ ∧ ∃ l', l ↦ NumV v ∗ (l+ₗ1) ↦ LocV l' ∗ llist_seg l' lv' last
    end.

  Definition llist (l: loc) (lv: list Z) := llist_seg l lv 0%Z.

  Global Instance llist_seg_objective l lv last : Objective (llist_seg l lv last).
  Proof.
    generalize l.
    induction lv => ?; apply _.
  Qed.
  Global Instance llist_objective l lv : Objective (llist l lv).
  Proof.
    generalize l.
    induction lv => ?; apply _.
  Qed.

  Notation "l ↦ₛ lv" := (llist_seg l lv) (at level 9) : bi_scope.
  Notation "l ↦ₗ lv" := (llist l lv) (at level 10) : bi_scope.


  (* FIXME make this into a lemma up1_fupd *)
  (* equiv to rewrite /= !(monPred_at_fupd(BiFUpd0:=uPred_bi_fupd)). *)
  Ltac up1_fupd :=
    match goal with
    | |- context[up1 (fupd ?E1 ?E2 ?P)] => assert (fupd E1 E2 (up1 P) ⊢ up1 (fupd E1 E2 P)) as <- by (split => ?;
      rewrite /= !monPred_at_fupd //)
    end.

  (* ad-hoc, aggressive *)
  Ltac iSteps := repeat first [iStep | iModIntro | progress iFrame | progress iIntros ].

  Lemma min_positive_spec E (l: loc) (lv: list Z) :
    (∃ _z, "r" ↦v NumV _z) ∗ l ↦ₗ lv
    ⊢ call_assert F E min_positive [LocV l; NumV 0; NumV 0] "r" ("r" ↦v NumV (min_positive_r lv) ∗ l ↦ₗ lv).
  Proof.
    iIntros "((%_z & r) & arr)".
    wp_start_func with_retainer "retainer" and_locals "(l & min & v & _)".
    iSteps.
    simpl.

    set (∃ l_m lv_a lv_b v, ⌜lv = lv_a++lv_b ⌝ ∧ l ↦ₛ lv_a l_m ∗ l_m ↦ₗ lv_b ∗
                "l" ↦v (LocV l_m) ∗ "v" ↦v v ∗ "min" ↦v (NumV (min_positive_r lv_a)) ∗
                stack_retainer min_positive ∗ (∃ _z, ⇓ ("r" ↦v _z)))%I%Z as inv.
    wp_apply (wp_while_inv  _ _ _ _ inv with "[] [-]" ) ; simpl.
    {
      iIntros "!> (%l_m & %lv_a & %lv_b & %v & -> & arr_a & arr_b & l & v & min & retainer & (%_z' & r))".
      iSteps.
      destruct (bool_decide (l_m = 0%Z)) eqn: Heqb; rewrite Heqb;
        [rewrite bool_decide_eq_true in Heqb; subst | rewrite bool_decide_eq_false in Heqb].
      - iExists _. iSplit; first done.
        iSteps.
        iSplitL "l v min".
        { iExists [_;_;_]. iSplit; first done. by iFrame. }
        iIntros "!> !> r". iFrame.
        destruct lv_b. 2: { rewrite /llist {2}/llist_seg /=. iDestruct "arr_b" as "[% ?]". done. }
        rewrite app_nil_r. iFrame.
      - iExists _. iSplit; first done.
        iSteps. simpl.
        iSteps.
        admit.
    }
    {
      rewrite /inv. iFrame. iExists []. rewrite app_nil_l /=. by iFrame.
    }
    iSteps.
    iRename select (_) into "inv".
    iDestruct "inv" as "(%l_m & %lv_a & %lv_b & %v & -> & arr_a & arr_b & l & v & min & retainer & (%_z' & r))".
    (* TODO need to show l_m=0 or lv_b=[] *)
    iSteps.
  Admitted.

End spec.


