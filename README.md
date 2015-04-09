# TIP: Tons of Inductive Problems - tools

This repository contains tools for working with the TIP suite of
benchmarks for inductive theorem provers. The tools are currently
rough around the edges but include:

* `tip-ghc` - translate a Haskell file to TIP format
* `tip-parser` - translate a TIP file to Why3 or SMTLIB format

## Building the tools

Check out this repository, make sure you have Haskell installed and
run `cabal update` and then
`cabal install ./tip-lib ./tip-haskell-frontend`.
The tools will be put in your `~/.cabal/bin` directory.

## Using the tools

To translate a Haskell file to TIP, run `tip-ghc name-of-file.hs`.
Properties to be proved must be written in a special syntax; to
see some examples, look at
[the benchmarks repository](http://github.com/tip-org/benchmarks)
under the directory `originals`.

To translate a TIP file to some other format, run:

* `tip-parser name-of-file.smt2 why3` to convert it to Why3 format;
* `tip-parser name-of-file.smt2 cvc4` to convert it to a
  CVC4-compatible version of SMTLIB.
