# iris-imp-lang

Two simple imperative languages instantiated in Iris. Most Iris instances for imperative languages
are encoded in a functional language (e.g. control flow translated to blocks and jumps); we define an imperative language `imp` that
models stack variables, named functions directly; `imp+` extends implang and additionally models
break/continue in a while loop.

To see how a functional language instance is instantiated, see the tutorial [iris-simp-lang](https://github.com/tchajed/iris-simp-lang). The structure of this development follows iris-simp-lang, but the contents are mostly different.

## Compiling

### Dependencies

This development relies on Rocq (Coq) 8.20.0 and Iris 4.3.0.

### Compilation

Simply run `make`.

## File Structure

`imp` and `imp+` has many shared components: expressions, the stack resource algebra and the state interpretation. On top of that, we define their components individually in `src/imp/` and `src/imp_plus/`, including their own semantics and proof rules. We do not model `imp+` as a strict extension of `imp`: `imp+` uses continuation in the program state and a special kind of predicate -- `postassert` -- in the logic to support `break` and `continue`, while `imp` only supports `return`ing from a function and has a more straightforward model.

Both `imp` and `imp+` support two kinds of weakest precondition `wp`s: one instantiated with the standard Iris `wp` (`lifting2.v`) and one without (`lifting.v`). 
The proof rules are the same regardless of which style.

**`src/` Shared components:**
- `expr.v` - Expression (shared by both `imp` and `imp+`)
- `stack_ra.v` - Resource algebra for stack frames; borrowed from 
- `state_interp.v` - State interpretation for the heap and stack frames
- `modality_instances.v` - Iris modality instances that declares `up1` & `down1` as modalities
- `class_instances.v` - Typeclass instances that provides Iris proof mode support for `assert` (monotonic predicate on stack) and the `up1` & `down1` modality
- `lifting_expr.v` - Proof rules for expressions, in the form of Weakest precondition `wp_expr`

**`src/imp/` - Defines imp-lang:**
- `lang.v` - Language definition
- `notation.v` - Notations for statements and functions
- `lifting.v` - `imp` proof rules with a custom definition of `wp`
- `lifting2.v` - `imp` proof rules with the standard Iris `wp`
- `examples/incr.v` - A verification example demonstrating (de)allocation of a stack frame during function call

**`src/imp_plus/` - Extended imperative language (with break/continue):**
- `lang.v` - Language definition
- `notation.v` - Notations for statements and functions
- `lifting.v` - `imp+` proof rules with a custom definition of `wp`
- `lifting2.v` - `imp` proof rules with the standard Iris `wp` (work-in-progress)
- `proofmode.v` - Proof mode tactics for applying `wp` rules
- `examples/min_positive.v` - A verification example demonstrating break/continue in a while loop
