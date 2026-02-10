From stdpp Require Export binders strings.
From stdpp Require Import gmap.
From iris.algebra Require Export ofe.
From iris.prelude Require Import options.
Open Scope Z.
From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.


Inductive bin_op :=
  | PlusOp
  | EqOp.

Inductive un_op :=
  | DerefOp.

Inductive expr :=
  (* Values *)
  | Num (n : Z)
  (* local variable *)
  | Var (x : string)
  (* Pure operations *)
  | BinOp (op : bin_op) (e1 e2 : expr)
  | UnOp (op : un_op) (e : expr)
.

Bind Scope expr_scope with expr.

(** Equality and other typeclass stuff *)

(*|
We will now do a bunch of boring work to prove that expressions have decidable
equality and are countable for technical reasons.
|*)

Global Instance bin_op_eq_dec : EqDecision bin_op.
Proof. solve_decision. Defined.
Global Instance un_op_eq_dec : EqDecision un_op.
Proof. solve_decision. Defined.
Lemma expr_eq_dec (e1 e2: expr) : Decision (e1 = e2).
Proof. solve_decision. Defined.
Global Instance expr_eq_dec' : EqDecision expr := expr_eq_dec.

Definition Bool (b:bool) : expr := Num (if b then 1 else 0).

(* semantics *)
Definition loc := Z.

Inductive val :=
  | NumV (n : Z)
  | LocV (l : loc).

Lemma val_eq_dec (v1 v2 : val) : Decision (v1 = v2).
Proof. solve_decision. Defined.
Global Instance val_eq_dec' : EqDecision val := val_eq_dec.

Definition BoolV (b:bool) : val := NumV (if b then 1 else 0).

Definition bin_op_eval (op: bin_op) (v1 v2: val) : option val :=
  match op with
  | PlusOp => match v1, v2 with
              | NumV n1, NumV n2 =>
                Some (NumV (n1 + n2))
              | LocV n1, NumV n2 | NumV n1, LocV n2 =>
                Some (LocV (n1 + n2))
              | _, _ => None
              end
  | EqOp => Some (BoolV $ bool_decide (v1 = v2))
  end.

(** the language interface needs these things to be inhabited, I believe *)
Global Instance val_inhabited : Inhabited val := populate (NumV 0).
Global Instance expr_inhabited : Inhabited expr := populate (Num 0).

Inductive eval_expr : expr → gmap string val → gmap loc val → val → Prop :=
  | EvalVal v ρ m :
    eval_expr (Num v) ρ m (NumV v)
  | EvalVar x v ρ m :
    ρ !! x = Some v →
    eval_expr (Var x) ρ m v
  | EvalBinOp op e1 e2 v1 v2 v ρ m :
    eval_expr e1 ρ m v1 →
    eval_expr e2 ρ m v2 →
    bin_op_eval op v1 v2 = Some v →
    eval_expr (BinOp op e1 e2) ρ m v
  | EvalLoad e v l ρ m :
    eval_expr e ρ m (LocV l) →
    m !! l = Some v →
    eval_expr (UnOp DerefOp e) ρ m v
  .

Fixpoint exec_eval_expr (e : expr) (ρ : gmap string val) (m : gmap loc val) : option val :=
  match e with
  | Num v => Some (NumV v)
  | Var x => ρ !! x
  | BinOp op e1 e2 =>
    v1 ← exec_eval_expr e1 ρ m ;
    v2 ← exec_eval_expr e2 ρ m ;
    bin_op_eval op v1 v2
  | UnOp op e1 =>
    v1 ← exec_eval_expr e1 ρ m ;
    match op, v1 with
    | DerefOp, LocV l =>
      m !! l
    | _, _ => None
    end
  end.

Definition max_loc (m : gmap loc val) := map_fold (λ l _ x, Z.max l x) 0 m .
Definition next_loc (m : gmap loc val) := max_loc m + 1.

Lemma max_loc_max : forall a l, a !! l ≠ None → l ≤ max_loc a.
Proof.
  induction a using map_first_key_ind; intros.
  - rewrite lookup_empty // in H.
  - rewrite /max_loc map_fold_insert_L //; last lia.
    destruct (decide (l = i)); try lia.
    rewrite lookup_insert_ne // in H1.
    specialize (IHa _ H1); rewrite /max_loc in IHa; lia.
Qed.

Lemma next_loc_new : forall a, a !! (next_loc a) = None.
Proof.
  intros; destruct (decide (a !! (next_loc a) = None)); first done.
  apply max_loc_max in n; rewrite /next_loc in n; lia.
Qed.
