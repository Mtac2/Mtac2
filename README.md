# Mtac2

A typed tactic language for Coq.

Copyright (c) 2020 Jan-Oliver Kaiser <janno@mpi-sws.org>
                   Beta Ziliani <beta@mpi-sws.org>

Distributed under the terms of the MIT License, see LICENSE for details. Accepted contributions will be
held under scrutiny to ensure they do not incur in a copyright infringement.

This repository contains a plugin for Coq with the tactic language
described in the paper
[Mtac2: Typed Tactics for Backward Reasoning in Coq](http://plv.mpi-sws.org/mtac).

The project has 3 subdirectories:
* `src` contains the code of the plugin.
  - `run.ml` is the interpreter.

* `theories` contains support Coq files for the plugin.
  - `Mtac2.v` declares the plugin on the Coq side and imports all the
     required theories.
  - The `intf` folder contains the basics: the `M` monad with its operations documented, exceptions, etc.
  - The folder `tactics` contains everything relating to tactics:
     + `Tactics.v` defines the tactic type and several tactics and combinators.
     + `Ttactics.v` defines the type for typed tactics and combinators.
     + `IntroPatt.v` defines intro patterns.
     + `ConstrSelector.v` defines a selector based on the indices of an inductive type's constructors.

* `examples` contains simple examples to show the different features of Mtac2.
  - `tactics.v` shows how to standard, Ltac's like, proving. But with some
    interesting features not present in Ltac.
  - `tauto.v` shows many different ways to code a simple tautology prover, with
    different degrees of certainty and verboseness.
* `test-suite` contains several tests, including some uses of the plugin.

Installation
============

The plugin works currently with Coq v8.7 (and any minor version). It requires
[UniCoq](http://github.com/unicoq/unicoq) to be
installed. Mtac2 will be available in OPAM soon.
For the moment you should have coqc, ocamlc and make in your path.
Then simply do:
```
 coq_makefile -f _CoqProject -o Makefile
```
To generate a makefile from the description in `_CoqProject`, then `make`.
This will consecutively build the plugin and the supporting
theories.

You can then either `make install` the plugin or leave it in its
current directory. To be able to import it from anywhere in Coq,
simply add the following to `~/.coqrc`:
```
Add LoadPath "path_to_mtac2/theories" as Mtac2.
Add ML Path "path_to_mtac2/src".
```
# Usage

Once installed, you can `Require Import Mtac2.Mtac2` to load the
plugin. The plugin defines a tactic `mrun t` to execute code `t` and a proof
mode `MProof` where Mtac2's tactic can be executed directly.
