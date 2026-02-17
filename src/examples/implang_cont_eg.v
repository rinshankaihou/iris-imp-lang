From iris_simp_lang Require Import implang_cont imp_cont_notation lifting_expr lifting_cont
  stack_ra proofmode_imp_cont imp_class_instances.

Local Open Scope func_scope.

(* Returns the minimum positive integer, or #0 if there isn't one.
  l: pointer to a linked list or null, each cell is (value, ptr_to_next_cell) *)
Definition min_positive :=
  fn "l" <{ ( "min" "v" )
    "min" <a- #0 ;;
    While !"l" ≠ #0 <{
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

  (* a linked list starting with l and stores lv; tail pointer is `last` *)
  Fixpoint llist_seg (l: loc) (lv: list Z) (last: loc) : assert :=
    match lv with
    | [] => ⌜l = last⌝
    | v :: lv' => ∃ l', l ↦ NumV v ∗ (l+ₗ1) ↦ LocV l' ∗ llist_seg l' lv' last
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

  Lemma min_positive_spec E (l: loc) (lv: list Z) z :
    (∃ _z, "r" ↦v NumV _z) ∗ l ↦ₗ lv
    ⊢ call_assert F E min_positive [LocV l; NumV 0; NumV 0] "r" ("r" ↦v NumV z ∗ l ↦ₗ lv ∗ ⌜min_positive_r lv = z⌝).
  Proof.
    iIntros "((%_z & r) & arr)".
    wp_start_func with_retainer "retainer" and_locals "(l & min & v & _)".
    iSteps.
    simpl.

    set (∃ l_m lv_a lv_b, ⌜lv = lv_a++lv_b⌝ ∧ l ↦ₛ lv_a l_m ∗ l_m ↦ₗ lv_b ∗
                "l" ↦v (LocV l_m) ∗ "v" ↦v (NumV (min_positive_r lv_a)))%I%Z as inv.
    wp_apply (wp_while_inv  _ _ _ _ inv with "[] [-r retainer]" ) ; simpl.
    {
      iIntros "!> (%l_m & %lv_a & %lv_b & %Hlv & arr_a & arr_b & l & v)".
      { iSteps. 
      
  Admitted.

End spec.


