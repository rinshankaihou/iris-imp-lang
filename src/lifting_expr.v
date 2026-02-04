(* wp for implang *)
From iris.base_logic Require Import gen_heap.
From iris.base_logic.lib Require Export fancy_updates.
From iris_simp_lang Require Import stack_ra implang_expr.

Section wp_expr.

Context `{!gen_heapGS loc val Σ} `{!envGS val Σ} `{!invGS_gen HasNoLc Σ}.

Implicit Types (ρ : @env_state val) (σ : gmap loc val).

Definition state_interp σ ρ : assert := (⎡gen_heap_interp σ⎤ ∗ ⎡env_auth ρ⎤)%I.

Definition env_match ρ r := assert_of (λ n, ⌜ρ !! n = Some r⌝)%I.

Definition wp_expr E e Q : assert :=
  (∀ σ ρ, state_interp σ ρ ={E}=∗
     ∃ v, (∀ r, env_match ρ r -∗ ⌜eval_expr e r σ v⌝) ∗
          state_interp σ ρ ∗ Q v)%I.



End wp_expr.