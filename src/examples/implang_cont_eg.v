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
  Local Open Scope Z_scope.

  Definition min_positive_r (lv: list Z) : Z :=
    Z.max 0 (foldr Z.min 0 lv).

  Lemma min_positive_r_cons x l : min_positive_r (x::l) = Z.max 0 (Z.min x (min_positive_r l)).
  Proof.
    rewrite /min_positive_r /=. lia.
  Qed.

  Lemma min_positive_r_app_r (lv_a : list Z) (z: Z) :
    z ≤ 0 →
    min_positive_r (lv_a ++ [z]) = min_positive_r lv_a.
  Proof.
    revert z.
    induction lv_a as [|x lv_a IH]; intros.
    - rewrite /min_positive_r /=; lia.
    - rewrite -app_comm_cons min_positive_r_cons IH //.
      rewrite /min_positive_r /=. lia.
  Qed.

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
  
  Lemma llist_seg_app l lv1 lv2 last :
    l ↦ₛ (lv1 ++ lv2) last ⊣⊢ ∃ l', l ↦ₛ lv1 l' ∗ l' ↦ₛ lv2 last.
  Proof.
    revert l.
    induction lv1 => ?; simpl.
    - iSplit; by [iIntros "$"|iIntros "(% & -> & $)"].
    - iSplit; iIntros "H".
      + iDestruct "H" as "(% & %l' & $ & $ & H3)". rewrite IHlv1.
        by iDestruct "H3" as "(% & $ & $)".
      + iDestruct "H" as "(% & (% & % & $ & $ & H2) & H3)".
        iSplit; first done. rewrite IHlv1. iFrame.
  Qed.

  (* FIXME make this into a lemma up1_fupd *)
  (* equiv to rewrite /= !(monPred_at_fupd(BiFUpd0:=uPred_bi_fupd)). *)
  Ltac up1_fupd :=
    match goal with
    | |- context[up1 (fupd ?E1 ?E2 ?P)] => assert (fupd E1 E2 (up1 P) ⊢ up1 (fupd E1 E2 P)) as <- by (split => ?;
      rewrite /= !monPred_at_fupd //)
    end.

  (* ad-hoc, aggressive *)
  Ltac iSteps := repeat first [iStep | iModIntro | progress iFrame | progress iIntros | progress simpl].

  Lemma min_positive_spec E (l: loc) (lv: list Z) :
    (∃ _z, "r" ↦v NumV _z) ∗ l ↦ₗ lv
    ⊢ call_assert F E min_positive [LocV l; NumV 0; NumV 0] "r" ("r" ↦v NumV (min_positive_r lv) ∗ l ↦ₗ lv).
  Proof.
    iIntros "((%_z & r) & arr)".
    wp_start_func with_retainer "retainer" and_locals "(l & min & v & _)".
    iSteps.
    set (∃ l_m lv_a lv_b v,
          (* split arr into two parts *)
          ⌜lv = lv_a++lv_b ⌝ ∧ l ↦ₛ lv_a l_m ∗ l_m ↦ₗ lv_b ∗ 
          (* "min" always store min of the first part*)
          "l" ↦v (LocV l_m) ∗ "v" ↦v v ∗ "min" ↦v (NumV (min_positive_r lv_a)) ∗
          stack_retainer min_positive ∗ (∃ _z, ⇓ ("r" ↦v _z)))%I%Z as inv.
    wp_apply (wp_while_inv  _ _ _ _ inv with "[] [-]" ); simpl.
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
        destruct lv_b. 2: { iDestruct "arr_b" as "[% ?]". done. }
        rewrite app_nil_r. iFrame.
      - iExists _. iSplit; first done.
        iSteps.
        destruct lv_b. { iDestruct "arr_b" as "%". done. }
        iDestruct "arr_b" as "(% & %l_n & arr_b_0 & arr_b_1 & arr_c)". fold llist_seg.
        iFrame. iIntros "arr_b_0".
        iFrame. iIntros "!> v".
        iSteps.
        destruct (bool_decide (z ≤ 0)%Z) eqn:Heqz;
          [rewrite bool_decide_eq_true in Heqz; subst | rewrite bool_decide_eq_false in Heqz].
        + iExists _. iSplit; first done.
          iModIntro. simpl. iStep. simpl.
          iRename select (⎡pointsto (l_m + 1)%Z _ _⎤)%I into "arr_b_1".
          iPoseProof (bi.equiv_entails_1_2  _ _ (llist_seg_app l lv_a [z] l_n) with "[$arr_a $arr_b_0 $arr_b_1]") as "?".
          { done. }
          iFrame.
          rewrite -app_assoc /= min_positive_r_app_r //.
          by iFrame.
        + iExists _. iSplit; first done.
          iSteps.
          (* FIXME fill in the boring case analysis here *)
          admit.
    }
    {
      rewrite /inv. iFrame. iExists []. rewrite app_nil_l /=. by iFrame.
    }
    iSteps.
    iRename select (_) into "inv".
    iDestruct "inv" as "(%l_m & %lv_a & %lv_b & %v & -> & arr_a & arr_b & l & v & min & retainer & (%_z' & r))".
    iSteps.
    rewrite /BoolV in H.
    destruct (bool_decide (l_m = 0%Z)) eqn:Heqb; rewrite Heqb in H;
      [rewrite bool_decide_eq_true in Heqb; subst | done].
    iSplitL "l v min".
    { iExists [_;_;_]. iSplit; first done. by iFrame. }
    iIntros "!> !> r". iFrame.
    destruct lv_b. 2: { rewrite /llist {2}/llist_seg /=. iDestruct "arr_b" as "[% ?]". done. }
    rewrite app_nil_r. iFrame.
  Admitted.

End spec.


