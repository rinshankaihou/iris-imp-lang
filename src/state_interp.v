From iris.base_logic Require Export gen_heap.
From iris_imp_lang Require Import expr.
From iris_imp_lang Require Export stack_ra.

Notation "l ↦ v" := (⎡pointsto l (DfracOwn 1) v⎤ : assert)%I (at level 20).

Section state_interp.

Context `{!gen_heapGS loc val Σ} `{!envGS val Σ}.

Definition state_interp σ ρ : iProp Σ := (gen_heap_interp σ ∗ env_auth ρ)%I.

Lemma state_interp_alloc σ ρ l v : σ !! l = None →
 ⎡state_interp σ ρ⎤ ==∗ ⎡state_interp (<[l := v]>σ) ρ⎤ ∗ l ↦ v.
Proof.
  intros; iIntros "(? & $)".
  by iMod (gen_heap_alloc with "[$]") as "($ & $ & _)".
Qed.

Lemma state_interp_load σ ρ l v : ⎡state_interp σ ρ⎤ -∗ l ↦ v -∗ ⌜σ !! l = Some v⌝.
Proof.
  by iIntros "(? & _) ?"; iDestruct (gen_heap_valid with "[$] [$]") as %?.
Qed.

Lemma state_interp_store σ ρ l v v' : ⎡state_interp σ ρ⎤ -∗ l ↦ v ==∗
  ⎡state_interp (<[l := v']>σ) ρ⎤ ∗ l ↦ v'.
Proof.
  by iIntros "(? & $) ?"; iMod (gen_heap_update with "[$] [$]") as "($ & $)".
Qed.

Lemma state_interp_alloc_frame : forall σ ρ n r, ρ !! n = None →
  (⎡state_interp σ ρ⎤ : assert) ⊢ |==> ⎡state_interp σ (<[n := r]> ρ)⎤ ∗ ⎡stack_frag n (/ pos_to_Qp (Pos.of_nat (1 + size r)))%Qp 1%Qp r⎤.
Proof.
  by intros; iIntros "($ & ?)"; iMod (env_alloc with "[$]") as "($ & $)".
Qed.

Lemma state_interp_dealloc_frame : forall σ ρ n q r,
  (⎡state_interp σ ρ⎤ : assert) ∗ ⎡stack_frag n q 1%Qp r⎤⊢ |==> ⎡state_interp σ (delete n ρ)⎤.
Proof.
  by intros; iIntros "(($ & ?) & ?)"; iMod (env_dealloc with "[$]") as "$".
Qed.

End state_interp.
