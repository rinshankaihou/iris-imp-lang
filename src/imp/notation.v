From stdpp Require Export binders strings.
From iris_imp_lang.imp Require Export lang.
From iris Require Import options.

(* for the expr and val notation scopes *)
From iris Require Import bi.weakestpre.

Declare Scope stmt_scope.
Delimit Scope stmt_scope with S.

Declare Scope func_scope.
Delimit Scope func_scope with F.

Coercion NumV : Z >-> val.

Coercion Var : string >-> expr.

Notation Load e := (UnOp DerefOp e).

(* No scope for the values, does not conflict and scope is often not inferred
properly. *)
Notation "# l" := (Num l%Z%stdpp) (at level 8, format "# l").

Notation "! e" := (Load e%E) (at level 9, right associativity) : expr_scope.
Notation "e1 + e2" := (BinOp PlusOp e1%E e2%E) : expr_scope.

Notation " x <a- e " := (Sassign x%binder e%E) (at level 80) : stmt_scope.
Notation "e1 <s- e2" := (Sstore e1%E e2%E) (at level 80) : stmt_scope.
Notation "'Alloc' x" := (Salloc x%binder) (at level 10) : stmt_scope.
Notation "'Return' x e" := (Sreturn x%binder e%E) (at level 200) : stmt_scope.
Notation skip := Sskip.

Notation "x <- f ( e )" := (Scall x%binder f%binder (@cons expr e%E nil))
  (at level 80, f at level 1, e at level 200,
  format "'[' x  <-  f ( '/  ' e ) ']'") : stmt_scope.
Notation "x <- f ( e1 , e2 , .. , e3 )" := (Scall x%binder f%binder (@cons expr e1%E (@cons expr e2%E .. (@cons expr e3%E nil) ..)))
  (at level 80, f at level 1, e1,e2,e3 at level 200,
  format "'[' x  <-  f ( e1 , e2 , .. , e3 ) ']'") : stmt_scope.
Notation "'If' e1 <{ s2 }> <{ s3 }> " := (Sif e1%E s2%S s3%S)
  (at level 200, e1 at level 1, s2,s3 at level 200,
  format "'[' 'If'  e1  <{ s2 }>  '/' <{ s3 }> ']'" ) : stmt_scope.
Notation "'If' e1 <{ s2 }> " := (Sif e1%E s2%S (skip)%S)
  (at level 200, e1 at level 1, s2 at level 200,
  format "'[' 'If'  e1  <{ s2 }>  ']'" ) : stmt_scope.

Notation "'While' e '<{' s '}>'" := (Swhile e%E s%S)
  (at level 200, e at level 1, s at level 200,
  format "'[' 'While'  e  '<{' '//'  s  '//' '}>' ']'") : stmt_scope.
Notation "s1 ;; s2" := (Sseq s1%S s2%S)
  (at level 100, s2 at level 200,
  format "'[' '[hv' '[' s1 ']' ;;  ']' '/' s2 ']'",
  right associativity) : stmt_scope.

Notation "'fn' <{ ( ) s '|' 'Return' e }> " := (Func [] [] s%S e%E)
  (at level 200, s at level 200, e at level 200,
  format "'fn' <{ ( ) '/  ' s '|' 'Return' e '/' }> ") : func_scope.
Notation "'fn' <{ ( a ) s '|' 'Return' e }> " := (Func [] [a%binder] s%S e%E)
  (at level 200, a at level 1, s at level 200, e at level 200,
  format "'fn' <{ ( a ) '/  ' s '|' 'Return' e '/' }> ") : func_scope.
Notation "'fn' <{ ( a b .. c ) s '|' 'Return' e }> " := (Func []
  (cons a%binder (cons b%binder .. (cons c%binder nil) ..)) s%S e%E)
  (at level 200, a,b,c at level 1, s at level 200, e at level 200,
  format "'fn' <{ ( a  b  ..  c ) '/  ' s '|' 'Return' e '/' }> ") : func_scope.
Notation "'fn' x <{ ( ) s '|' 'Return' e }> " := (Func [x%binder] [] s%S e%E)
  (at level 200, x at level 1, s at level 200, e at level 200,
  format "'fn'  x  <{ ( ) '/  ' s '|' 'Return' e '/' }> ") : func_scope.
Notation "'fn' x <{ ( a ) s '|' 'Return' e }> " := (Func [x%binder] [a%binder] s%S e%E)
  (at level 200, x,a at level 1, s at level 200, e at level 200,
  format "'fn'  x  <{ ( a ) '/  ' s '|' 'Return' e '/' }> ") : func_scope.
Notation "'fn' x <{ ( a b .. c ) s '|' 'Return' e }> " := (Func (cons x%binder nil)
  (cons a%binder (cons b%binder .. (cons c%binder nil) ..)) s%S e%E)
  (at level 200, x,a,b,c at level 1, s at level 200, e at level 200,
  format "'fn' x <{ ( a  b  ..  c ) '/  ' s '|' 'Return' e '/' }> ") : func_scope.
Notation "'fn' x y .. z <{ ( ) s '|' 'Return' e }> " := (Func (cons x%binder (cons y%binder .. (cons z%binder nil) ..))
  nil s%S e%E)
  (at level 200, x,y,z at level 1, s at level 200, e at level 200,
  format "'fn'  x  y  ..  z  <{ ( ) '/  ' s '|' 'Return' e '/' }> ") : func_scope.
Notation "'fn' x y .. z <{ ( a ) s '|' 'Return' e }> " := (Func (cons x%binder (cons y%binder .. (cons z%binder nil) ..))
  (cons a%binder nil) s%S e%E)
  (at level 200, x,y,z,a at level 1, s at level 200, e at level 200,
  format "'fn'  x  y  ..  z  <{ ( a ) '/  ' s '|' 'Return' e '/' }> ") : func_scope.
Notation "'fn' x y .. z <{ ( a b .. c ) s '|' 'Return' e }> " := (Func (cons x%binder (cons y%binder .. (cons z%binder nil) ..))
  (cons a%binder (cons b%binder .. (cons c%binder nil) ..)) s%S e%E)
  (at level 200, x,y,z,a,b,c at level 1, s at level 200, e at level 200,
  format "'fn'  x  y  ..  z  <{ ( a  b  ..  c ) '/  ' s '|' 'Return' e '/' }> ") : func_scope.

Section NotationExample.

    Local Open Scope func_scope.

    Example if_expr := (If ("y":expr) <{ skip }> <{ skip }> )%S.

    Example while_expr := 
        (While ("y":expr) <{
            While ("y":expr) <{
                If ("y":expr) <{ skip }> <{ skip }>
            }>
        }> )%S.

    Example fun_ex := 
        fn "x" "y" <{ ( "a" "c" "d" )
            Alloc "a" ;;
            If "y" <{ skip }> <{ skip }> ;;
            While "y" <{
                While "y" <{
                    If "y" <{ skip }> <{ skip }>
                }>
            }>;;
            "a" <- "f" (!"x") ;;
            "c" <a- (Num 0) ;; (* assignment *)
            "d" <s- #2 ;; (* store to the address (Num 0) *)
            "d" <- "g" (#0, !"x"+!"y", "z") |
            Return #0
        }>.

End NotationExample.