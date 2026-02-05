From iris.base_logic Require Export gen_heap.
From iris_simp_lang Require Import implang_expr.
From iris_simp_lang Require Export stack_ra.

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

End state_interp.
