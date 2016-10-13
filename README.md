# MetaCoq

An typed tactic language for Coq.

Copyright (c) 2015 Beta Ziliani <bziliani@famaf.unc.edu.ar>,
	           Yann Régis-Gianas <yrg@irif.fr>,
		   Jan-Oliver Kaiser <janno@mpi-sws.org>

Distributed under the terms of the MIT License,
see LICENSE for details.

This archive is a plugin for Coq containing a new tactic lanugage.

The archive has 3 subdirectories:
* `src` contains the code of the plugin.

* `theories` contains support Coq files for the plugin.
  `MetaCoq.v` declares the plugin on the Coq side and imports all the
  required theories.

* `test-suite` just demonstrates a use of the plugin.
  `Showcase.v` is at the moment a good place to start.

Installation
============

The plugin works currently with Coq v8.5pl2. It requires
[UniCoq](http://github.com/unicoq/unicoq) to be
installed. MetaCoq will be available in OPAM soon.
For the moment you should have coqc, ocamlc and make in your path.
Then simply do:
```
 coq_makefile -f _CoqProject -o Makefile
```
To generate a makefile from the description in _CoqProject, then `make`.
This will consecutively build the plugin and the supporting
theories.

You can then either `make install` the plugin or leave it in its
current directory. To be able to import it from anywhere in Coq,
simply add the following to `~/.coqrc`:
```
Add LoadPath "path_to_unicoq/theories" as Unicoq.
Add ML Path "path_to_unicoq/src".
```
# Usage

Once installed, you can `Require Import MetaCoq.MetaCoq` to load the
plugin. The plugin defines a tactic `mrun t` to execute code `t`.
