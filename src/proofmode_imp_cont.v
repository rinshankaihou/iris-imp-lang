From iris.proofmode Require Import coq_tactics reduction spec_patterns.
From iris.proofmode Require Export tactics.
From iris_simp_lang Require Import implang_cont imp_class_instances lifting_expr lifting_cont.

Ltac reshape_seq :=
  lazymatch goal with
  | |- envs_entails _ (wp _ _ (Sseq _ _) _) => iApply wp_seq; reshape_seq
  | _ => idtac
  end.

Lemma tac_wp_expr_eval `{!gen_heapGS loc val Σ} `{!envGS val Σ} `{!invGS_gen hlc Σ}
  Δ E Q e e' :
  (∀ (e'':=e'), e = e'') →
  envs_entails Δ (wp_expr E e' Q) →
  envs_entails Δ (wp_expr E e Q).
Proof. by intros ->. Qed.

Tactic Notation "wp_expr_eval" tactic3(t) :=
  iStartProof;
  lazymatch goal with
  | |- envs_entails _ (wp_expr ?E ?e ?Q) =>
    notypeclasses refine (tac_wp_expr_eval _ _ _ e _ _ _);
      [let x := fresh in intros x; t; unfold x; notypeclasses refine eq_refl|]
  | _ => fail "wp_expr_eval: not a 'wp_expr'"
  end.
Ltac wp_expr_simpl := wp_expr_eval simpl.

Lemma tac_wp_var `{!gen_heapGS loc val Σ} `{!envGS val Σ} `{!invGS_gen hlc Σ}
  Δ E Q x v b i :
  envs_lookup i Δ = Some (b, x ↦v v)%I →
  envs_entails Δ (Q v) →
  envs_entails Δ (wp_expr E (Var x) Q).
Proof.
  rewrite envs_entails_unseal=> ? Hi.
  iIntros "Henv".
  iDestruct (envs_lookup_split with "Henv") as "[Hl Henv]"; first by eauto.
  rewrite -wp_var Hi.
  destruct b; simpl.
  - iDestruct "Hl" as "#Hl".
    iFrame "Hl". iIntros "?". by iApply "Henv".
  - iFrame "Hl". done.
Qed.

Lemma tac_wp_deref `{!gen_heapGS loc val Σ} `{!envGS val Σ} `{!invGS_gen hlc Σ}
  Δ E Q e :
  envs_entails Δ (wp_expr E e (λ v0,
    match v0 with
    | LocV l => ∃ v, l ↦ v ∗ (l ↦ v -∗ Q v) 
    | _ => False end))%I →
  envs_entails Δ (wp_expr E (UnOp DerefOp e) Q).
Proof.
  rewrite -wp_load envs_entails_unseal => ->.
  iIntros "H"; iRevert "H".
  iApply wp_expr_mono. iIntros (v) "H".
  destruct v; try done.
  iDestruct "H" as (v) "H".
  iExists _, _; by iFrame.
Qed.

Tactic Notation "wp_var" :=
  let solve_lvar _ :=
    let i := match goal with |- _ = Some (_, ?i ↦v _)%I => i end in
    iAssumptionCore || fail "wp_var: cannot find var" i in
  lazymatch goal with
  | |- envs_entails _ (wp_expr ?E ?e ?Q) =>
    first
      [eapply tac_wp_var
      |fail 1 "wp_var: cannot find 'Evar' in" e];
    [solve_lvar ()
    |pm_reduce]
  | _ => fail "wp_var: not a 'wp'"
  end.

Ltac wp_expr_head :=
  lazymatch goal with
  | |- envs_entails _ (wp_expr _ (Num _) _) => iApply wp_val
  | |- envs_entails _ (wp_expr _ (Var _) _) => wp_var
  | |- envs_entails _ (wp_expr _ (UnOp DerefOp _) _) => iApply tac_wp_deref
  | |- envs_entails _ (wp_expr _ (BinOp _ _ _) _) => iApply wp_binop
  end.
  
Ltac wp_finish :=
  repeat wp_expr_head;
  pm_prettify.

Ltac wp_apply_core lem tac_suc tac_fail := first
  [iPoseProofCore lem as false (fun H =>
     lazymatch goal with
     | |- envs_entails _ (wp _ _ _ _) =>
            reshape_seq; tac_suc H
     | _ => fail 1 "wp_apply: not a 'wp'"
     end)
  |tac_fail ltac:(fun _ => wp_apply_core lem tac_suc tac_fail)
  |let P := type of lem in
   fail "wp_apply: cannot apply" lem ":" P ].

Tactic Notation "wp_apply" open_constr(lem) :=
  wp_apply_core lem ltac:(fun H => iApplyHyp H; try iNext; try wp_expr_simpl)
                    ltac:(fun cont => fail).

Tactic Notation "wp_apply" open_constr(lem) "as" constr(pat) :=
  wp_apply lem; last iIntros pat.
Tactic Notation "wp_apply" open_constr(lem) "as" "(" simple_intropattern(x1) ")"
    constr(pat) :=
  wp_apply lem; last iIntros ( x1 ) pat.
Tactic Notation "wp_apply" open_constr(lem) "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) ")" constr(pat) :=
  wp_apply lem; last iIntros ( x1 x2 ) pat.
Tactic Notation "wp_apply" open_constr(lem) "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) ")" constr(pat) :=
  wp_apply lem; last iIntros ( x1 x2 x3 ) pat.
Tactic Notation "wp_apply" open_constr(lem) "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4) ")"
    constr(pat) :=
  wp_apply lem; last iIntros ( x1 x2 x3 x4 ) pat.
Tactic Notation "wp_apply" open_constr(lem) "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
    simple_intropattern(x5) ")" constr(pat) :=
  wp_apply lem; last iIntros ( x1 x2 x3 x4 x5 ) pat.
Tactic Notation "wp_apply" open_constr(lem) "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
    simple_intropattern(x5) simple_intropattern(x6) ")" constr(pat) :=
  wp_apply lem; last iIntros ( x1 x2 x3 x4 x5 x6 ) pat.
Tactic Notation "wp_apply" open_constr(lem) "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
    simple_intropattern(x5) simple_intropattern(x6) simple_intropattern(x7) ")"
    constr(pat) :=
  wp_apply lem; last iIntros ( x1 x2 x3 x4 x5 x6 x7 ) pat.
Tactic Notation "wp_apply" open_constr(lem) "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
    simple_intropattern(x5) simple_intropattern(x6) simple_intropattern(x7)
    simple_intropattern(x8) ")" constr(pat) :=
  wp_apply lem; last iIntros ( x1 x2 x3 x4 x5 x6 x7 x8 ) pat.
Tactic Notation "wp_apply" open_constr(lem) "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
    simple_intropattern(x5) simple_intropattern(x6) simple_intropattern(x7)
    simple_intropattern(x8) simple_intropattern(x9) ")" constr(pat) :=
  wp_apply lem; last iIntros ( x1 x2 x3 x4 x5 x6 x7 x8 x9 ) pat.
Tactic Notation "wp_apply" open_constr(lem) "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
    simple_intropattern(x5) simple_intropattern(x6) simple_intropattern(x7)
    simple_intropattern(x8) simple_intropattern(x9) simple_intropattern(x10) ")"
    constr(pat) :=
  wp_apply lem; last iIntros ( x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 ) pat.

Tactic Notation "wp_assign" :=
  lazymatch goal with
  | |- envs_entails _ (wp _ ?E ?s ?Q) =>
    first
      [reshape_seq; iApply wp_assign
      |fail 1 "wp_assign: cannot find 'Sassign' in" s];
    [pm_reduce; wp_finish]
  | _ => fail "wp_assign: not a 'wp'"
  end.

Tactic Notation "wp_store" :=
  lazymatch goal with
  | |- envs_entails _ (wp _ ?E ?s ?Q) =>
    first
      [reshape_seq; iApply wp_store
      |fail 1 "wp_store: cannot find 'Sstore' in" s];
    [pm_reduce; wp_finish]
  | _ => fail "wp_store: not a 'wp'"
  end.

Tactic Notation "wp_break" :=
  lazymatch goal with
  | |- envs_entails _ (wp _ ?E ?s ?Q) =>
    first
      [reshape_seq; iApply wp_break
      |fail 1 "wp_break: cannot find 'Sbreak' in" s]
  | _ => fail "wp_break: not a 'wp'"
  end.

Tactic Notation "wp_continue" :=
  lazymatch goal with
  | |- envs_entails _ (wp _ ?E ?s ?Q) =>
    first
      [reshape_seq; iApply wp_continue
      |fail 1 "wp_continue: cannot find 'Scontinue' in" s]
  | _ => fail "wp_continue: not a 'wp'"
  end.

Tactic Notation "wp_return" :=
  lazymatch goal with
  | |- envs_entails _ (wp _ ?E ?s ?Q) =>
    first
      [reshape_seq; iApply wp_return
      |fail 1 "wp_return: cannot find 'Sreturn' in" s];
    [pm_reduce; wp_finish]
  | _ => fail "wp_return: not a 'wp'"
  end.

Ltac iStep :=
  lazymatch goal with
  | |- envs_entails _ (wp _ ?E (Sseq ?s _) ?Q) =>
    match s with
    | Sassign _ _ => wp_assign
    | Sstore _ _ => wp_store
    | Sbreak => wp_break
    | Scontinue => wp_continue
    | Sreturn _ => wp_return
    | ?s => fail 1 "iStep: does not support (Seq " s " _)"
    end
  | |- envs_entails _ (wp _ ?E ?s _) =>
    fail 2 "iStep: does not support" s
  | |- envs_entails _ (wp_expr _ _ _) =>
    wp_finish
  | _ => fail "iStep: not a 'wp' or 'wp_expr'" 
  end.

Tactic Notation "wp_start_func" "with_retainer" constr(pat1) "and_locals" constr(pat2) :=
  iIntros pat1; iIntros pat2; iModIntro; simpl get_body.