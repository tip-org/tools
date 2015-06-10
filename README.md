# TIP: Tons of Inductive Problems - tools

This repository contains tools for working with the TIP suite of
benchmarks for inductive theorem provers. The tools are currently
rough around the edges but include:

* `tip` - transform a TIP file or translate it to various formats
* `tip-ghc` - translate a Haskell file to TIP format

## Installing from Hackage

To install the latest released version of TIP, run

    cabal update
    cabal install tip-lib tip-haskell-frontend

The tools will be put in your `~/.cabal/bin` directory.

## Building the development version of the tools

Check out this repository, make sure you have Haskell installed and then:

    cabal update
    cabal install bnfc
    ./make_parser.sh
    cabal install ./tip-lib ./tip-haskell-frontend

The tools will be put in your `~/.cabal/bin` directory.

## Working with TIP problems

You can find a large collection of problems in TIP format in
[the benchmarks repository](http://github.com/tip-org/benchmarks)
under the directory `benchmarks`. You can use the `tip` tool
to run transformations on these problems or translate them to another format.

To translate a TIP file to some other format, run:

* `tip name-of-file.smt2 --why` to convert it to WhyML format;
* `tip name-of-file.smt2 --smtlib` to convert it to a
  CVC4-compatible version of SMTLIB;
* `tip-parser name-of-file.smt2 --isabelle` to convert it to Isabelle;
* `tip-parser name-of-file.smt2 --haskell` to convert it to
  Haskell (plus scaffolding for running QuickSpec).

You can also use `tip` to run various transformations on the input problem.
For example, `tip name-of-file.smt2 --commute-match --simplify-aggressively`
will first simplify the structure of `match` expressions in the problem
and then run a general simplification pass. For a list of all passes
run `tip --help`.

## Translating Haskell to TIP

To translate a Haskell file to TIP, run `tip-ghc name-of-file.hs`.
Properties to be proved must be written in a special syntax; to
see some examples, look at
[the benchmarks repository](http://github.com/tip-org/benchmarks)
under the directory `originals`.

