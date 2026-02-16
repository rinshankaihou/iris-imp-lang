From iris.proofmode Require Import coq_tactics reduction spec_patterns.
From iris.proofmode Require Export tactics.
From iris_simp_lang Require Import implang_cont imp_class_instances lifting_expr lifting_cont.

Ltac reshape_seq :=
  lazymatch goal with
  | |- envs_entails _ (wp _ _ ?E _ (Sseq ?s _) ?Q) => iApply wp_seq; reshape_seq
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

Lemma tac_wp_expr_num `{!gen_heapGS loc val Σ} `{!envGS val Σ} `{!invGS_gen hlc Σ}
  Δ E Q n :
  envs_entails Δ (Q (NumV n)) →
  envs_entails Δ (wp_expr E (Num n) Q).
Proof. rewrite envs_entails_unseal=> ->. rewrite -wp_val //. Qed.
Lemma tac_wp_expr_var `{!gen_heapGS loc val Σ} `{!envGS val Σ} `{!invGS_gen hlc Σ}
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
