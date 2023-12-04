#! /usr/bin/sh
coqc LibTactics.v
coqc LHCoqTactics.v
coqc IntNatExample.v
cp -f LibTactics.vo ~/.opam/4.07.1/lib/coq
cp -f LibTactics.vos ~/.opam/4.07.1/lib/coq
cp -f LHCoqTactics.vo ~/.opam/4.07.1/lib/coq
cp -f LHCoqTactics.vos ~/.opam/4.07.1/lib/coq
cp -f IntNatExample.vo ~/.opam/4.07.1/lib/coq
cp -f IntNatExample.vos ~/.opam/4.07.1/lib/coq

coqc -R . ZFC LibTactics.v
coqc -R . ZFC LHCoqTactics.v
coqc -R . ZFC IntNatExample.v
