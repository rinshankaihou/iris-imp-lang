From iris_simp_lang Require Import implang_cont imp_cont_notation lifting_expr lifting_cont
  stack_ra proofmode_imp_cont imp_class_instances.

Local Open Scope func_scope.

(* Returns the minimum positive integer, or #0 if there isn't one.
  l: pointer to a linked list or null, each cell is (value, ptr_to_next_cell) *)
Definition min_positive :=
  fn "l" <{ ( "min" "v" )
    "min" <a- #0 ;;
    While #1 <{
      If "l" = #0 <{ break }> ;;
      "v" <a- !"l";;
      "l" <a- !("l" + #1);;
      If "v" <= #0 <{ continue }> ;;
      If ("min" = #0) || ("v" < "min") <{ "min" <a- "v" }>
    }>;;
    Return "min"
  }>.

Definition F : func_env :=
    <[ "min_positive" := min_positive ]> ∅.

Section spec.

  Context `{!gen_heapGS loc val Σ} `{!envGS val Σ} `{!invGS_gen HasNoLc Σ}.

  Local Open Scope bi_scope.
  Local Open Scope Z_scope.

  Definition pos_elems (l: list Z) :=
    filter (λ x, x > 0) l.

  Definition min_l (l: list Z) : Z :=
    match l with
    | [] => 0
    | h::t => foldr Z.min h t
    end.

  Definition min_positive_r (n: Z) (l: list Z) : Prop :=
    let l' := pos_elems l in
    ((n = 0 ∧ l' = []) ∨ n=min_l l').

  Definition compute_min_positive (l: list Z) : Z :=
    min_l (pos_elems l).

  Lemma compute_min_positive_is_min_positive_r l :
    min_positive_r (compute_min_positive l) l.
  Proof.
     rewrite /compute_min_positive /min_positive_r.
     right. done.
  Qed.
  
  Lemma min_l_cons x l :
    l ≠ [] ->
    min_l (x::l) = Z.min x (min_l l).
  Proof.
    intros. destruct l; try done.
    simpl.
    rewrite -!foldr_comm_acc.
    2-3: intros; rewrite !Z.min_assoc [X in Z.min X _]Z.min_comm //.
    rewrite [X in foldr _ X _]Z.min_comm //.
  Qed.

  Lemma pos_elems_cons x l :
    pos_elems (x::l) = (if bool_decide (x > 0) then [x] else []) ++ pos_elems l.
  Proof.
    intros. rewrite /pos_elems filter_cons decide_bool_decide //.
    destruct (bool_decide (x > 0)) eqn:Heq; done.
  Qed.

  Lemma foldr_Z_min_in_list h t :
     foldr Z.min h t ∈ h::t.
  Proof.
    induction t; simpl; try done.
    - constructor.
    - destruct (Z.min_dec a (foldr Z.min h t)).
      + rewrite e. repeat constructor.
      + rewrite e. eapply elem_of_subseteq. 2: apply IHt.
        intros.
        rewrite /elem_of in H.
        inversion H; subst; by repeat constructor.
  Qed.


  Lemma pos_elems_foldr_ge_0 l h t:
    pos_elems l = h :: t -> foldr Z.min h t > 0.
  Proof.
    intros.
    set (foldr Z.min h t) as m.
    assert (m ∈ pos_elems l). { rewrite H. apply foldr_Z_min_in_list. }
    rewrite elem_of_list_filter in H0. easy.
  Qed.

  Lemma compute_min_positive_cons x l :
    compute_min_positive (x::l) = if bool_decide (x > 0 ∧ (compute_min_positive l = 0 ∨ x < compute_min_positive l)) 
                                  then x else compute_min_positive l.
  Proof.
    intros.
    rewrite {1}/compute_min_positive pos_elems_cons /=.
    destruct (bool_decide (x > 0)) eqn:Heqx.
    2: { rewrite bool_decide_and Heqx //. }
    destruct (pos_elems l) eqn:Hpos.
    { rewrite /compute_min_positive Hpos /=. rewrite bool_decide_and Heqx //. }
    rewrite min_l_cons //. rewrite -Hpos.
    rewrite bool_decide_and Heqx /=. 
    assert (bool_decide (compute_min_positive l = 0) = false).
    {
      apply bool_decide_eq_false. rewrite /compute_min_positive /=.
      apply pos_elems_foldr_ge_0 in Hpos as ?.
      rewrite /min_l Hpos.
      lia.
     }
    rewrite bool_decide_or H /=.
    destruct (bool_decide (x < compute_min_positive l)) eqn:Heq2.
    - rewrite bool_decide_eq_true /compute_min_positive in Heq2.
      lia.
    - rewrite bool_decide_eq_false /compute_min_positive in Heq2.
      rewrite /compute_min_positive. lia.
  Qed.

  Lemma compute_min_positive_snoc x l : compute_min_positive (l++[x]) = compute_min_positive ([x]++l).
  Proof.
     revert x.
     induction l; intros.
    - rewrite /compute_min_positive /min_l /pos_elems /=.
      destruct (decide (x > 0)) eqn:Heq; try lia.
    - rewrite -app_comm_cons !compute_min_positive_cons !IHl !compute_min_positive_cons.
      rewrite !bool_decide_and !bool_decide_or.
      set (compute_min_positive l) as c.
      (destruct (bool_decide (a > 0)) eqn:H1; 
       destruct (bool_decide (x > 0)) eqn:H2;
       destruct (bool_decide (c = 0)) eqn:H3;
       destruct (bool_decide (x < c)) eqn:H4;
       destruct (bool_decide (a < c)) eqn:H5;
       rewrite ?H1 ?H2 ?H3 ?H4 ? H5 //=;
       rewrite ->?bool_decide_eq_true, ->?bool_decide_eq_false in *; try lia);
      (destruct (bool_decide (x = 0)) eqn:H6;
       destruct (bool_decide (a = 0)) eqn:H7;
       destruct (bool_decide (a < x)) eqn:H8;
       destruct (bool_decide (x < a)) eqn:H9;
       rewrite ?H6 ?H7 ?H8 ?H9 //=);
       rewrite ->?bool_decide_eq_true, ->?bool_decide_eq_false in *; try lia.
   Qed.

  Lemma compute_min_positive_app_comm (lv_a lv_b: list Z) :
    compute_min_positive (lv_a ++ lv_b) = compute_min_positive (lv_b ++ lv_a).
  Proof.
    revert lv_b.
    induction lv_a as [|x lv_a IH]; intros.
    - rewrite app_nil_r app_nil_l //.
    - rewrite -app_comm_cons cons_middle app_assoc -IH app_assoc
      compute_min_positive_snoc //.
  Qed.

  Lemma min_positive_r_app (lv_a : list Z) (z: Z) :
    z ≤ 0 →
    compute_min_positive (lv_a ++ [z]) = compute_min_positive lv_a.
  Proof.
    rewrite compute_min_positive_snoc compute_min_positive_cons => ?.
    rewrite bool_decide_and.
    destruct (bool_decide (z > 0)) eqn:Hz; [rewrite bool_decide_eq_true in Hz; lia|].
    done.
  Qed. 

  Definition ptr_add (l: loc) (i: Z) : loc :=
    (l + i)%Z.
  Notation "l +ₗ i" := (ptr_add l i) (at level 10, left associativity).

  (* a segment of linked list starting with l and stores lv;
    the last cell has pointer `last` that might or might not be empty *)
  Fixpoint llist_seg (l: val) (lv: list Z) (last: val) : assert :=
    match lv with
    | [] => ⌜l = last⌝
    | v :: lv' => ∃ p, ⌜l=LocV p⌝ ∧ ∃ l', p ↦ NumV v ∗ (p+ₗ1) ↦ l' ∗ llist_seg l' lv' last
    end.

  Definition llist (l: val) (lv: list Z) := llist_seg l lv 0.

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
      + iDestruct "H" as "(%l' & % & % & $ & $ & H3)". rewrite IHlv1.
        by iDestruct "H3" as "(% & $ & $)".
      + iDestruct "H" as "(% & (%& % & % & $ & $ & H2) & H3)".
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

  Lemma min_positive_spec E (l: val) (lv: list Z) :
    (∃ _z, "r" ↦v NumV _z) ∗ l ↦ₗ lv
    ⊢ call_assert F E min_positive [l; NumV 0; NumV 0] "r" (∃ r, ⌜min_positive_r r lv⌝ ∧ "r" ↦v NumV r ∗ l ↦ₗ lv).
  Proof.
    iIntros "((%_z & r) & arr)".
    wp_start_func with_retainer "retainer" and_locals "(l & min & v & _)".
    iSteps.
    set (∃ l_m lv_a lv_b v,
          (* split arr into two parts *)
          ⌜lv = lv_a++lv_b ⌝ ∧ l ↦ₛ lv_a l_m ∗ l_m ↦ₗ lv_b ∗ 
          (* "min" always store min of the first part*)
          "l" ↦v l_m ∗ "v" ↦v v ∗ "min" ↦v (NumV (compute_min_positive lv_a)) ∗
          stack_retainer min_positive ∗ (∃ _z, ⇓ ("r" ↦v _z)))%I%Z as inv.
    wp_apply (wp_while_inv  _ _ _ _ inv with "[] [-]" ); simpl.
    {
      iIntros "!> (%l_m & %lv_a & %lv_b & %v & -> & arr_a & arr_b & l & v & min & retainer & (%_z' & r))".
      iSteps.
      iExists _. iSplit; first done.
      iSteps.
      destruct (bool_decide (l_m = 0)) eqn: Heqb;
        [rewrite bool_decide_eq_true in Heqb; subst | rewrite bool_decide_eq_false in Heqb].
      - iExists _. iSplit; first done.
        iSteps.
        iSplitL "l v min".
        { iExists [_;_;_]. iSplit; first done. by iFrame. }
        iIntros "!> !> r". iFrame.
        destruct lv_b. 2: { iDestruct "arr_b" as "(% & % & % & ?)". done. }
        rewrite app_nil_r. iFrame. iPureIntro. apply compute_min_positive_is_min_positive_r.
      - simpl.
        destruct (lv_b).
        { iDestruct "arr_b" as "->". simpl.
          iExists _. iSplit; first done.
          iSteps.
          iSplitL "l v min".
          { iExists [_]. iSplit; first done. by iFrame. }
          iIntros "!> !> r". iFrame.
          rewrite app_nil_r. by iFrame.
        }

        iDestruct "arr_b" as "(% & -> & %l' & arr_b_0 & arr_b_1 & arr_c)".
        fold llist_seg.
        simpl.
        iExists _. iSplit; first done.
        iSteps.
        iExists _. iSplit; first done.
        iSteps.
        destruct (bool_decide (z ≤ 0)%Z) eqn:Heqz.
        +  simpl. iStep. simpl.
          iRename select (⎡pointsto _ _ l'⎤) into "arr_b_1".
          iRename select (⎡pointsto _ _ (NumV z)⎤) into "arr_b_0".
          iPoseProof (bi.equiv_entails_1_2  _ _ (llist_seg_app l lv_a [z] _) with "[$arr_a $arr_b_0 $arr_b_1]") as "?".
          { done. }
          iFrame.
          rewrite -app_assoc min_positive_r_app //=. by iFrame. rewrite bool_decide_eq_true // in Heqz.
        + destruct (bool_decide (z > 0)) eqn: Heqz'.
          2: { rewrite bool_decide_eq_false in Heqz'.
                rewrite bool_decide_eq_false  in Heqz.
                lia. }
          iSteps.
          iExists _. iSplit; first done.
          iSteps.
          destruct (bool_decide ((compute_min_positive lv_a = 0) ∨ (z < compute_min_positive lv_a))) eqn:Heq1;
          rewrite bool_decide_or in Heq1.
          ++ rewrite orb_true_iff in Heq1.
            destruct Heq1 as [Heq1 | Heq1]; simpl.
            +++ rewrite Heq1. iSteps. rewrite {1}cons_middle {1}app_assoc. iExists _; iSplit; first done.
                rewrite llist_seg_app. iFrame.
                rewrite compute_min_positive_snoc compute_min_positive_cons.
                rewrite bool_decide_and bool_decide_or Heq1 Heqz' /=.
                by iFrame.
            +++ rewrite !Heq1.
                assert (bool_decide (compute_min_positive lv_a = 0) = false) as ?.
                {
                  rewrite bool_decide_eq_true in Heq1.
                  rewrite bool_decide_eq_false in Heqz.
                  apply bool_decide_eq_false. lia. 
                }
                rewrite H /=.
                iSteps.
                rewrite {1}cons_middle {1}app_assoc. iExists _; iSplit; first done.
                rewrite llist_seg_app. iFrame.
                iSplit; first done.
                rewrite compute_min_positive_snoc compute_min_positive_cons bool_decide_and bool_decide_or.
                rewrite Heqz' H Heq1 //.
          ++ rewrite orb_false_iff in Heq1.
            destruct Heq1 as [Heq1  Heq2].
            rewrite Heq1 Heq2 /=.
            iStep. simpl.
            rewrite /inv.
            rewrite {1}cons_middle {1}app_assoc.
            iExists _, _, _, _. iSplit; first done.
            iFrame.
            rewrite llist_seg_app. iFrame.
            iSplit; first done.
            rewrite compute_min_positive_snoc compute_min_positive_cons bool_decide_and bool_decide_or.
            rewrite Heqz' Heq1 Heq2 //.
    }
    {
      rewrite /inv. iFrame. iExists []. rewrite app_nil_l /=. by iFrame.
    }
    iSteps.
    iRename select (_) into "inv".
    iDestruct "inv" as "(%l_m & %lv_a & %lv_b & %v & -> & arr_a & arr_b & l & v & min & retainer & (%_z' & r))".
    iSteps.
    (* destruct (bool_decide (l_m = 0%Z)) eqn:Heqb; rewrite Heqb in H;
      [rewrite bool_decide_eq_true in Heqb; subst | done]. *)
    iSplitL "l v min".
    { iExists [_;_;_]. iSplit; first done. by iFrame. }
    iIntros "!> !> r". iFrame.
    destruct lv_b. 2: { rewrite /llist {2}/llist_seg /=. iDestruct "arr_b" as "[% ?]". done. }
    rewrite app_nil_r.
    iDestruct "arr_b" as "->". iFrame.
    iPureIntro. apply compute_min_positive_is_min_positive_r.
  Qed.

End spec.


