A mechanization of Incorrectness Separation Logic
=================================================

This repository contains the Coq mechanization I describe in my master thesis.

The mechanization is divided in 3 parts.

1. The operational semantics for a expression-oriented programming language in the style of ML
   with errors, references and nondeterminism.
2. The mechanization of Incorrectness Separation Logic for said language.
3. Example programs, their verification in Incorrectness Separation Logic and a top-level
   statement of incorrectness verified using a ``no false positive'' theorem described
   in my thesis.

Each part corresponds to the following files: part one corresponds to `lang.v`, part two
corresponds to `ISL.v` and part 3 corresponds to `examples.v`.

The mechanization was done in Coq using the Stdpp library and using various bits
of notation and tactics from the Iris project. At the time of writing I am using
the following versions: Coq 8.14.1, Stdpp dev.2021-12-09.0.e6194e28 and
Iris dev.2021-12-16.0.f083f007.

Each part is also described in depth in the thesis as follows.

Chapter 2 describes the programming language syntax, operational semantics
and the model of the heap.

Chapters 3 and 4 describe the adaptation of Incorrectness Separation Logic
to an expression-oriented programming language as well as the definition
of a more primitive notion `post` that we use to define incorrectness triples.

Chapter 5 describes at a high level the implementation of this mechanization
and how it relates to the previous chapters.
