From iris_simp_lang Require Import implang_cont imp_cont_notation lifting_expr lifting_cont stack_ra proofmode_imp_cont imp_class_instances.

Local Open Scope func_scope.

(* Returns the minimum positive integer, or #0 if there isn't one.
  l: address of head of an array *)
Definition min_positive :=
  fn "l" <{ ( "min" "v" )
    "min" <a- #0 ;;
    While !"l" ≠ #0 <{
      If !"l" < !"min" <{ break }> <{ skip }>;;
      "v" <a- !"l";;
      "l" <a- !("l" + #1);;
      If "v" <= #0 <{ continue }> <{ skip }>;;
      If "min" = #0 || "v" < "min" <{ "min" <a- "v" }> <{ skip }>
    }>;;
    Return "min"
  }>.

Definition F : func_env :=
    <[ "min_positive" := min_positive ]> ∅.

Section spec.

  Context `{!gen_heapGS loc val Σ} `{!envGS val Σ} `{!invGS_gen HasNoLc Σ}.

  Definition min_positive_r (lv: list Z) : Z :=
    foldr Z.min 0%Z lv.

  Definition ptr_add (l: loc) (i: Z) : loc :=
    (l + i)%Z.
  Notation "l +ₗ i" := (ptr_add l i) (at level 10, left associativity).

  (* a list of [0;1;...; (n-1)] *)
  Definition indices n := map (Z.of_nat) (seq 0%nat n).
  Definition array_points_to (l: loc) (lv: list Z) : assert :=
    ([∗ list] i; v ∈ indices (length lv); lv, (l +ₗ i) ↦ (NumV v))%I.
  Instance array_points_to_objective l lv : Objective (array_points_to l lv).
  Proof.
    rewrite /array_points_to. generalize (indices (length lv)).
    induction lv => indices.
    - destruct indices; simpl; apply _.
    - destruct indices; simpl; apply _.
  Qed.
  Notation "l ↦ₐ lv" := (array_points_to l lv) (at level 10) : bi_scope.


  (* FIXME make this into a lemma up1_fupd *)
  (* equiv to rewrite /= !(monPred_at_fupd(BiFUpd0:=uPred_bi_fupd)). *)
  Ltac up1_fupd :=
    match goal with
    | |- context[up1 (fupd ?E1 ?E2 ?P)] => assert (fupd E1 E2 (up1 P) ⊢ up1 (fupd E1 E2 P)) as <- by (split => ?;
      rewrite /= !monPred_at_fupd //)
    end.

  Ltac wp_seq := iApply wp_seq.
  Lemma min_positive_spec E (l: loc) (lv: list Z) z :
    (∃ _z, "r" ↦v NumV _z) ∗ l ↦ₐ lv
    ⊢ call_assert F E min_positive [LocV l; NumV 0; NumV 0] "r" ("r" ↦v NumV z ∗ l ↦ₐ lv ∗ ⌜min_positive_r lv = z⌝).
  Proof.
    iIntros "((%_z & r) & arr) retainer (l & min & v & _)".
    iEval (rewrite -[(_↦v_)%I]up1_down1) in "r".
    iModIntro.
    
    wp_seq.
    rewrite -wp_seq.
    rewrite -wp_assign.
    rewrite -wp_expr.

    
    Set Typeclasses Debug.
    Search stack_match.
    iSplitR.


  Admitted.

End spec.


