# iris-implang

A simple imperative language instantiated in Iris. Most Iris instances for imperative languages
are encoded in a functional language (e.g. control flow translated to blocks and jumps); implang
models stack variables, named functions directly; implang+ extends implang and additionally models
break/continue in a while loop.

To see how a functional instance is instantiated, see the tutorial [iris-simp-lang](https://github.com/tchajed/iris-simp-lang).

## Compiling

### Dependencies

You'll need to install Iris, which is easiest done through opam. There are
installation instructions at https://gitlab.mpi-sws.org/iris/iris.

This development relies on a development version of Iris 4.3.0 and Coq 8.20.0.

### Compilation
Simply run `make`.