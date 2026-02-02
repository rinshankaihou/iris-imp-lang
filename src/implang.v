From stdpp Require Export binders strings.
From stdpp Require Import gmap.
From iris.algebra Require Export ofe.
(* From iris.program_logic Require Export language ectx_language ectxi_language. *)
From iris.prelude Require Import options.
Open Scope Z.
From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.


Inductive base_lit :=
  | LitInt (n:Z)
  (* not sure if unit is necessary *)
  | LitUnit.

Inductive bin_op :=
  | PlusOp
  | EqOp.

Inductive un_op :=
  | DerefOp.

(*|
Expressions are defined mutually recursively with values. As explained above, an
expression is a value iff it uses the Val constructor, which makes defining
reduction and substitution much simpler, but requires duplicating `Rec` and
`Pair` to `val` as `RecV` and `PairV`.
|*)

Variant val :=
  | LitV (l : base_lit).

Inductive expr :=
  (* Values *)
  | Val (v : val)
  (* local variable *)
  | Var (x : string)
  (* Pure operations *)
  | BinOp (op : bin_op) (e1 e2 : expr)
  | UnOp (op : un_op) (e : expr)
.

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
  | Scall (x : string) (f : string) (args : list expr)
  | Sreturn (e : expr)
.

Inductive func :=
  | Func (func_params : list string) (func_body : stmt).

Bind Scope val_scope with val.
Bind Scope expr_scope with expr.
Bind Scope stmt_scope with stmt.
Bind Scope func_scope with func.

Notation of_val := Val (only parsing).

Definition to_val (e : expr) : option val :=
  match e with
  | Val v => Some v
  | _ => None
  end.

(** Equality and other typeclass stuff *)
Lemma to_of_val v : to_val (of_val v) = Some v.
Proof. by destruct v. Qed.

Lemma of_to_val e v : to_val e = Some v → of_val v = e.
Proof. destruct e=>//=. by intros [= <-]. Qed.

Global Instance of_val_inj : Inj (=) (=) of_val.
Proof. intros ??. congruence. Qed.

(*|
We will now do a bunch of boring work to prove that expressions have decidable
equality and are countable for technical reasons.
|*)

Global Instance base_lit_eq_dec : EqDecision base_lit.
Proof. solve_decision. Defined.
Global Instance bin_op_eq_dec : EqDecision bin_op.
Proof. solve_decision. Defined.
Global Instance un_op_eq_dec : EqDecision un_op.
Proof. solve_decision. Defined.
Lemma val_eq_dec (v1 v2 : val) : Decision (v1 = v2).
Proof. solve_decision. Defined.
Global Instance val_eq_dec' : EqDecision val := val_eq_dec.
Lemma expr_eq_dec (e1 e2: expr) : Decision (e1 = e2).
Proof. solve_decision. Defined.
Global Instance expr_eq_dec' : EqDecision expr := expr_eq_dec.
Lemma stmt_eq_dec (s1 s2: stmt) : Decision (s1 = s2).
Proof. solve_decision. Defined.
Global Instance stmt_eq_dec' : EqDecision stmt := stmt_eq_dec.
Lemma func_eq_dec (f1 f2: func) : Decision (f1 = f2).
Proof. solve_decision. Defined.
Global Instance func_eq_dec' : EqDecision func := func_eq_dec.

Global Instance base_lit_countable : Countable base_lit.
Proof.
  refine (inj_countable'
            (λ l, match l with | LitInt n => inl n | LitUnit => inr () end)
            (λ v, match v with | inl n => _ | inr _ => _ end) _).
  intros []; eauto.
Qed.

Global Instance val_countable : Countable val.
Proof. 
  refine (inj_countable'
            (λ l, match l with | LitV l' => l' end)
            (λ v, LitV v) _).
  intros []; eauto.
Qed.

Global Instance bin_op_countable : Countable bin_op.
Proof.
  refine (inj_countable'
            (λ op, match op with | PlusOp => 0 | EqOp => 1  end)
            (λ n, match n with | 0 => _ | 1 => _
                          | _ => ltac:(constructor) end) _).
  intros []; eauto.
Qed.

Global Instance un_op_countable : Countable un_op.
Proof.
  refine (inj_countable'
            (λ op, match op with | DerefOp => 0  end)
            (λ n, match n with | 0 => _ | _ => ltac:(constructor) end) _).
  intros []; eauto.
Qed.

Global Instance expr_countable : Countable expr.
Proof.

 set (enc :=
   fix go e :=
     match e with
     | Val v => GenLeaf (inl (inl v))
     | Var x => GenLeaf (inl (inr x))
     | UnOp op e => GenNode 1 [GenLeaf (inr (inl op)); go e]
     | BinOp op e1 e2 => GenNode 2 [GenLeaf (inr (inr op)); go e1; go e2]
     end).
 set (dec :=
   fix go e :=
      match e with
      | GenLeaf (inl (inl v)) => Val v
      | GenLeaf (inl (inr x)) => Var x
      | GenNode 1 [GenLeaf (inr (inl op)); e] =>
        UnOp op $ go e
      | GenNode 2 [GenLeaf (inr (inr op)); e1; e2] =>
        BinOp op (go e1) (go e2)
      | _ => Val (LitV LitUnit)  (* default case, won't be used *)
      end).
 refine (inj_countable' enc dec _) => e.
 induction e; simpl; f_equal; done.
Qed.

Global Instance stmt_countable : Countable stmt.
Proof.
Admitted.
Global Instance func_countable : Countable func.
Proof.
Admitted.



(** Substitution *)
(* Fixpoint subst (x : string) (v : val) (e : expr)  : expr :=
  match e with
  | Val _ => e
  | Var y => if decide (x = y) then Val v else Var y
  | Rec f y e =>
    Rec f y $ if decide (BNamed x ≠ f ∧ BNamed x ≠ y) then subst x v e else e
  | App e1 e2 => App (subst x v e1) (subst x v e2)
  | BinOp op e1 e2 => BinOp op (subst x v e1) (subst x v e2)
  | UnOp op e => UnOp op (subst x v e)
  | If e0 e1 e2 => If (subst x v e0) (subst x v e1) (subst x v e2)
  | Fork e => Fork (subst x v e)
  | HeapOp op e1 e2 => HeapOp op (subst x v e1) (subst x v e2)
  end.

Definition subst' (mx : binder) (v : val) : expr → expr :=
  match mx with BNamed x => subst x v | BAnon => id end. *)

(*|
Now we'll give the pure semantics of simp_lang. These two Gallina definitions
`bin_op_eval` and `un_op_eval` define the semantics of all the pure operations,
when the types of their arguments make sense.
|*)

Definition LitBool (b:bool) : base_lit :=
  if b then LitInt 1 else LitInt 0.

Definition bin_op_eval (op: bin_op) (v1 v2: val) : option val :=
  match op with
  | PlusOp => match v1, v2 with
              | LitV (LitInt n1), LitV (LitInt n2) =>
                Some (LitV (LitInt (n1 + n2)))
              | _, _ => None
              end
  | EqOp => Some (LitV $ LitBool $ bool_decide (v1 = v2))
  end.

(* semantics *)

Definition loc := Z.

Record state : Type := {
  (* variables and their values on the current stack frame*)
  ρ : gmap string val;
  (* heap mapping locations to values *)
  m : gmap loc val;
  (* each element in the stack k is a pair of the previous variable environment 
    and a variable that will get the return value once the program returns *)
  k : list (gmap string val * string);
}.

(** the language interface needs these things to be inhabited, I believe *)
Global Instance state_inhabited : Inhabited state :=
  populate {| ρ := inhabitant; m := inhabitant; k := []  |}.
Global Instance val_inhabited : Inhabited val := populate (LitV LitUnit).
Global Instance expr_inhabited : Inhabited expr := populate (Val inhabitant).

#[export] Instance settable_state : Settable state :=
  settable! Build_state <ρ; m; k>. 
Example state_upd_env (f: gmap string val → gmap string val) (s: state) : state :=
  s <| ρ ::= f |>.
Example state_upd_heap (f: gmap loc val → gmap loc val) (s: state) : state :=
  s <| m ::= f |>.


Inductive eval_expr : expr → gmap string val → gmap loc val → val → Prop :=
  | EvalVal v ρ m :
    eval_expr (Val v) ρ m v
  | EvalVar x v ρ m :
    ρ !! x = Some v →
    eval_expr (Var x) ρ m v
  | EvalBinOp op e1 e2 v1 v2 v ρ m :
    eval_expr e1 ρ m v1 →
    eval_expr e2 ρ m v2 →
    bin_op_eval op v1 v2 = Some v →
    eval_expr (BinOp op e1 e2) ρ m v
  | EvalLoad e v l ρ m :
    eval_expr e ρ m (LitV (LitInt l)) →
    m !! l = Some v →
    eval_expr (UnOp DerefOp e) ρ m v
  .

Fixpoint exec_eval_expr (e : expr) (ρ : gmap string val) (m : gmap loc val) : option val :=
  match e with
  | Val v => Some v
  | Var x => ρ !! x
  | BinOp op e1 e2 =>
    v1 ← exec_eval_expr e1 ρ m ;
    v2 ← exec_eval_expr e2 ρ m ;
    bin_op_eval op v1 v2
  | UnOp op e1 =>
    v1 ← exec_eval_expr e1 ρ m ;
    match op, v1 with
    | DerefOp, LitV (LitInt l) =>
      m !! l
    | _, _ => None
    end
  end.

Definition eval_expr' e s v : Prop := (eval_expr e s.(ρ) s.(m) v).
Definition eval_exprs' es s vs : Prop :=
  Forall2 (λ e v, eval_expr' e s v) es vs.

Definition bind_vars (ρ: gmap string val) (ns: list string) (vs: list val) : gmap string val :=
  foldr (λ x ρ', <[ x.1 := x.2 ]> ρ') ρ (zip ns vs).

Definition func_env := gmap string func.

Inductive base_step : func_env -> stmt → state → stmt → state → Prop :=
  | AssignS F (x: string) e σ (v: val) :
    eval_expr' e σ v →
    base_step F (Sassign x e) σ Sskip (σ <| ρ ::= <[x := v]> |>)
  | AllocS F x σ l :
    σ.(m) !! l = None →
    base_step F (Salloc x) σ Sskip
              (σ <| ρ ::= <[x := LitV $ LitInt l]> |>
                 <| m ::= <[l := LitV LitUnit]> |>)
  | StoreS F e1 e2 σ l v1 v2 :
    eval_expr' e1 σ (LitV (LitInt l)) →
    eval_expr' e2 σ v2 →
    (* must be allocated *)
    σ.(m) !! l = Some v1 →
    base_step F (Sstore e1 e2) σ Sskip
              (σ <| m ::= <[l := v2]> |>)
  | SeqS1 F s1 s1' s2 σ σ':
    base_step F s1 σ s1' σ' →
    base_step F (Sseq s1 s2) σ (Sseq s1' s2) σ'
  | SeqS2 F s2 σ :
    base_step F (Sseq Sskip s2) σ s2 σ
  | IfS F e s1 s2 σ v :
    eval_expr' e σ (LitV $ LitInt v) →
    base_step F (Sif e s1 s2) σ (if Z.eqb v 0 then s2 else s1) σ
  | WhileS F e s σ v :
    eval_expr' e σ (LitV $ LitInt v) →
    base_step F (Swhile e s) σ (if Z.eqb v 0 then Sskip else Sseq s (Swhile e s)) σ
  | CallS F f es σ ps s vs rv :
    F !! f = Some (Func ps s) →
    length ps = length es →
    eval_exprs' es σ vs →
    let ρ' := bind_vars σ.(ρ) ps vs in
    let k' := ((σ.(ρ), rv) :: σ.(k)) in
    base_step F (Scall rv f es) σ s 
                (σ <| ρ := ρ' |> <| k:=k' |>)
  | ReturnS F e σ v ρ m ρ0 r k :
    eval_expr' e σ v →
    σ = Build_state ρ m ((ρ0, r) :: k) →
    base_step F (Sreturn e) σ Sskip 
              (Build_state (<[r := v]> ρ0) m k)
  .

Definition fresh_locs (ls : gset loc) : loc :=
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
  base_step F (Salloc x) σ Sskip (σ <| ρ ::= <[x := LitV $ LitInt l]> |>
                                    <| m ::= <[l := LitV LitUnit]> |>).
Proof.
  intros.
  apply AllocS.
  apply (not_elem_of_dom (D := gset loc)).
  by apply fresh_locs_fresh.
Qed.
