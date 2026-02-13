# iris-implang

A simple imperative language instantiated in Iris. Most Iris instances for imperative languages
are encoded in a functional language (e.g. control flow translated to blocks and jumps); implang
models stack variables, named functions directly; implang+ extends implang and additionally models
break/continue in a while loop.

To see how a functional language instance is instantiated, see the tutorial [iris-simp-lang](https://github.com/tchajed/iris-simp-lang). The structure of this development follows iris-simp-lang, but the contents are mostly different.

## Compiling

### Dependencies

This development relies on a Iris 4.3.0 and Coq 8.20.0.

### Compilation

Simply run `make`.