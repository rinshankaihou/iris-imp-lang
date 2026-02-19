From stdpp Require Export binders strings.
From stdpp Require Import gmap.
From iris.algebra Require Export ofe.
From iris_imp_lang Require Export expr.
From iris.prelude Require Import options.
From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.




(* s ::= skip | x := e | x := alloc | *e := e | s;s | if (e){s}else{s}
         | while(e){s} | x := f(\vec{e}) | return e 
*)
Inductive stmt :=
  | Sskip
  | Sassign (x : string) (e : expr)
  | Salloc (x : string)
  | Sstore (e1 e2 : expr)
  | Sseq (s1 s2 : stmt)
  | Sif (e : expr) (s1 s2 : stmt)
  | Swhile (e : expr) (s : stmt)
  | Sbreak
  | Scontinue
  | Scall (x : string) (f : string) (args : list expr)
  | Sreturn (e : expr)
.

Inductive func :=
  | Func (func_params : list string) (func_locals : list string) (func_body : stmt).

Bind Scope stmt_scope with stmt.
Bind Scope func_scope with func.

(** Equality and other typeclass stuff *)

(*|
We will now do a bunch of boring work to prove that expressions have decidable
equality and are countable for technical reasons.
|*)

Lemma stmt_eq_dec (s1 s2: stmt) : Decision (s1 = s2).
Proof. solve_decision. Defined.
Global Instance stmt_eq_dec' : EqDecision stmt := stmt_eq_dec.
Lemma func_eq_dec (f1 f2: func) : Decision (f1 = f2).
Proof. solve_decision. Defined.
Global Instance func_eq_dec' : EqDecision func := func_eq_dec.

(* semantics *)

(* make into a list? *)
Inductive cont :=
  | Kstop
  | Kseq (s : stmt) (k : cont)
  | Kwhile (e : expr) (s : stmt) (k : cont)
  | Kcall (x : string) (r : gmap string val) (k : cont).

Fixpoint find_loop k :=
  match k with
  | Kseq _ k' => find_loop k'
  | Kwhile _ _ _ => Some k
  | _ => None
  end.

Fixpoint find_call k :=
  match k with
  | Kseq _ k' => find_call k'
  | Kwhile _ _ k' => find_call k'
  | Kcall _ _ _ => k
  | Kstop => Kstop
  end.

Record state : Type := {
  (* variables and their values on the current stack frame*)
  ρ : gmap string val;
  (* heap mapping locations to values *)
  m : gmap loc val;
  (* continuation instead of stack *)
  k : cont;
}.

(** the language interface needs these things to be inhabited, I believe *)
Global Instance state_inhabited : Inhabited state :=
  populate {| ρ := inhabitant; m := inhabitant; k := Kstop  |}.

#[export] Instance settable_state : Settable state :=
  settable! Build_state <ρ; m; k>. 
Example state_upd_env (f: gmap string val → gmap string val) (s: state) : state :=
  s <| ρ ::= f |>.
Example state_upd_heap (f: gmap loc val → gmap loc val) (s: state) : state :=
  s <| m ::= f |>.

Definition eval_expr' e s v : Prop := (eval_expr e s.(ρ) s.(m) v).
Definition eval_exprs' es s vs : Prop :=
  Forall2 (λ e v, eval_expr' e s v) es vs.

Definition bind_vars (ns: list string) (vs: list val) : gmap string val :=
  foldr (λ x ρ', <[ x.1 := x.2 ]> ρ') ∅ (zip ns vs).

Definition func_env := gmap string func.

Inductive step : func_env -> stmt → state → stmt → state → Prop :=
  | AssignS F (x: string) e σ (v: val) :
    eval_expr' e σ v →
    step F (Sassign x e) σ Sskip (σ <| ρ ::= <[x := v]> |>)
  | AllocS F x σ :
    step F (Salloc x) σ Sskip
              (σ <| ρ ::= <[x := LocV (next_loc σ.(m))]> |>
                 <| m ::= <[(next_loc σ.(m)) := NumV 0]> |>)
  | StoreS F e1 e2 σ l v1 v2 :
    eval_expr' e1 σ (LocV l) →
    eval_expr' e2 σ v2 →
    (* must be allocated *)
    σ.(m) !! l = Some v1 →
    step F (Sstore e1 e2) σ Sskip
              (σ <| m ::= <[l := v2]> |>)
  | SeqS F s1 s2 σ :
    step F (Sseq s1 s2) σ s1 (σ <| k := Kseq s2 σ.(k) |>)
  | SkipSeqS F s2 σ k0 :
    σ.(k) = Kseq s2 k0 →
    step F Sskip σ s2 (σ <| k := k0 |>)
  | IfS F e s1 s2 σ v :
    eval_expr' e σ (NumV v) →
    step F (Sif e s1 s2) σ (if Z.eqb v 0 then s2 else s1) σ
  | WhileTS F e s σ v :
    eval_expr' e σ (NumV v) → v ≠ 0 →
    step F (Swhile e s) σ s (σ <| k := Kwhile e s σ.(k) |>)
  | WhileFS F e s σ :
    eval_expr' e σ (NumV 0) →
    step F (Swhile e s) σ Sskip σ
  | SkipWhileS F e s k0 σ :
    σ.(k) = Kwhile e s k0 →
    step F Sskip σ (Swhile e s) (σ <| k := k0 |>)
  | BreakS F σ e s k' :
    find_loop σ.(k) = Some (Kwhile e s k') →
    step F Sbreak σ Sskip (σ <| k := k' |>)
  | ContinueS F σ e s k' :
    find_loop σ.(k) = Some (Kwhile e s k') →
    step F Scontinue σ Sskip (σ <| k := Kwhile e s k' |>)
  | CallS F f es σ ps ls s vs rv :
    F !! f = Some (Func ps ls s) →
    length ps = length es →
    eval_exprs' es σ vs →
    let ρ' := bind_vars (ps ++ ls) (vs ++ repeat (NumV 0) (length ls)) in
    let k' := Kcall rv σ.(ρ) σ.(k) in
    step F (Scall rv f es) σ s 
                (σ <| ρ := ρ' |> <| k:=k' |>)
  | ReturnS F e σ v ρ0 r k' :
    eval_expr' e σ v →
    find_call σ.(k) = Kcall r ρ0 k' →
    step F (Sreturn e) σ Sskip 
              (Build_state (<[r := v]> ρ0) σ.(m) k')
  .

Inductive step_star : func_env -> stmt → state → stmt → state → Prop :=
  | Step0 F s σ : step_star F s σ s σ
  | Step1 F s σ s' σ' s'' σ'' : step F s σ s' σ' → step_star F s' σ' s'' σ'' →
      step_star F s σ s'' σ''.

(*Definition fresh_locs (ls : gset loc) : loc :=
  set_fold (λ k r, (1 + k) `max` r) 1 ls.

Lemma fresh_locs_fresh ls :
  fresh_locs ls ∉ ls.
Proof.
  cut (∀ l, l ∈ ls → l < fresh_locs ls).
  { intros help Hf%help. lia. }
  apply (set_fold_ind_L (λ r ls, ∀ l, l ∈ ls → l < r));
    set_solver by eauto with lia.
Qed.

(** this theorem will be needed to show that allocation is never stuck when we
prove a WP for it *)
Lemma alloc_fresh F x σ :
  (* this invocation of [dom] is for backwards compatibility with Iris 3.6.0 *)
  let l := fresh_locs (@dom _ (gset _) _ σ.(m)) in
  step F (Salloc x) σ Sskip (σ <| ρ ::= <[x := LocV l]> |>
                                    <| m ::= <[l := NumV 0]> |>).
Proof.
  intros.
  apply AllocS.
  apply (not_elem_of_dom (D := gset loc)).
  by apply fresh_locs_fresh.
Qed.*)
