From stdpp Require Export binders strings.
From iris_simp_lang Require Export implang.
From iris Require Import options.

(* for the expr and val notation scopes *)
From iris Require Import bi.weakestpre.

Declare Scope stmt_scope.
Delimit Scope stmt_scope with S.

Declare Scope func_scope.
Delimit Scope func_scope with F.

Coercion LitInt : Z >-> base_lit.

Coercion Val : val >-> expr.
Coercion Var : string >-> expr.

Notation Load e := (UnOp DerefOp e).

(* No scope for the values, does not conflict and scope is often not inferred
properly. *)
Notation "# l" := (LitV l%Z%V%stdpp) (at level 8, format "# l").

Notation "()" := LitUnit : val_scope.
Notation "! e" := (Load e%E) (at level 9, right associativity) : expr_scope.
Notation "e1 + e2" := (BinOp PlusOp e1%E e2%E) : expr_scope.

Notation "'ref' x" := (Salloc x%binder) (at level 10) : stmt_scope.
Notation "e1 <- e2" := (Sstore e1%E e2%E) (at level 80) : stmt_scope.
Notation "'ret' e" := (Sreturn e%E) (at level 200) : stmt_scope.

Notation "x '<<-' f ( e )" := (Scall x%binder f%binder (@cons expr e%E nil))
  (at level 200, f at level 1, e at level 200,
  format " x '<<-' f ( '/  ' e )") : stmt_scope.
Notation "x '<<-' f ( e1 , e2 , .. , e3 )" := (Scall x%binder f%binder (@cons expr e1%E (cons e2%E .. (cons e3%E nil) ..)))
  (at level 200, f at level 1, e1,e2,e3 at level 200) : stmt_scope.
Notation "'if:' e1 '<{' s2 '}>' '<{' s3 '}>'" := (Sif e1%E s2%S s3%S)
  (at level 200, e1 at level 1, s2,s3 at level 200) : stmt_scope.
Notation "'while' e <{ s }>" := (Swhile e%E s%S)
  (at level 200, e at level 1, s at level 200) : stmt_scope.


Notation "'fn' x '<{' s '}>'" := (Func [x%binder] s%S)
  (at level 200, x at level 1, s at level 200,
  format "'fn' x '/  ' '<{' '/  ' s '}>'") : func_scope.
Notation "'fn' x y .. z '<{' s '}>'" := (Func (cons x%binder (cons y%binder .. (cons z%binder nil) ..)) s%S)
  (at level 200, x,y,z at level 1, s at level 200,
  format "'fn' x y .. z '/  ' '<{' '/  ' s '}>'") : func_scope.
  
Notation "s1 ;; s2" := (Sseq s1%S s2%S)
  (at level 100, s2 at level 200,
  format "s1 ;; '/  ' s2") : stmt_scope.

Section NotationExample.

    Local Open Scope func_scope.
    Example emm := 
        fn "x" "y" <{
            "x" <- #1;;
            ref "a" ;;
            if: "y" <{ Sskip }> <{ Sskip }> ;;
            while "y" <{ Sskip }> ;;
            (* FIXME *)
            (* "c" <<- "f" (!"x") ;; *)
            (* "d" <<- "g" (#0, !"x"+!"y");; *)
            ret #0
        }>.

End NotationExample.