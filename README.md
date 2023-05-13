# Artifact Description

Title of the submitted paper: A Direct-Style Effect Notation for Sequential and Parallel Programs
ECOOP Round 1 submission number for the paper: #56
ECOOP Round 2 submission number for the paper: #174

## Changes since last submission

The coq proof has changed.

We now work over an arbitrary lawful applicative and monad;
this includes the following changes:

– Define the Monad and a lawful Monad class in Coq. (Listing 1)

– The type denotation is now parametrized over the type constructor
  of the monad (Listing 2a)

– The evaluation function (Listing 2d) is now parametrized by a monad
  and monadlaw instance; its body was also updated slightly: Previously,
  the evaluation function used only monadic binds and no applicative
  ap. To show that translation preserves evaluation, evaluation must
  already use applicative operations when evaluating terms with multiple
  subterms (in the cases App, Prd, Map, Ap).

– The semantics preservation theorem needs to be parametrized by a
  monad and monadlaw instance (Thm. 5). The description of the proof
  for the semantic preservation theorem remains unchanged because,
  as it was the case already before, the proof consists of auto-rewriting
  via laws and previously proven lemmas.

– Whereas evaluation does require a monad instance to run, the trans-
  lation, span and work functions, and span preservation and work
  preservation theorems remain unchanged because they do not evalu-
  ate the terms.

Furthermore:

- instead of describing the differences between the names of the theorems and definitions in coq and the paper,
  we renamed them to be aligned with each other.

- we got rid of the Axiom functional_extensionality_dep, e.g.,
  the proofs are now closed over the global context, e.g., make use of no axiom.

The scala source has not changed.

## Overview: What does the artifact comprise?

The artifact comprises:

* Type: Docker Image with Dependencies
  Format: Docker Image
  Location: docker-image.tar

* Type: Proof
  Format: Coq source code
  Location: src/coq/proof.v

* Type: Program
  Format: Scala source code
  Location: src/scala/build.sbt
  Location: src/scala/project/build.properties
  Location: src/scala/src/main/parseq/Tests.scala
  Location: src/scala/src/main/parseq/Macro.scala
  Location: src/scala/src/main/parseq/Monads.scala
  Location: src/scala/src/main/parseq/WithLift.scala
  Location: src/scala/src/main/parseq/WithPrint.scala

We claim all three badges available, functional and reusable.

## For authors claiming a functional or reusable badge: What are claims about the artifact’s functionality to be evaluated by the committee?

* Which data or conclusions from the paper are generated/supported by the artifact components?

  The proof of the paper is mechanised in Coq. The compiler is implemented as well in Scala 3 via Macros, and a few tests.

* Which activities described in the paper have led to the creation of the artifact components?

  In the paper we have described the formal definition of a structurally recursive code-to-code translation function
  from a direct-style effect notation to monadic and applicative combinators,
  together with a proof of preservation of important properties.
  These can be found in the `coq` folder.

  Additionally, we mentioned an implementation in Scala, that works similar.
  These can be found in the `scala` folder.

Please provide explicit references that link processes, data, or conclusions in the paper with the location of the supporting component in the artifact, e.g., 

* Listing 1 in the paper defines
  - the class `Monad`
  - the class `LawfulMonad`
* Listing 2 in the paper defines
  - the inductive `ty`
  - the function `EVAL`
  - the inductive `ef`
  - the function `EF`
  - the inductive `tm`
  - the function `eval`
  - the function `relabel`
* Listing 3 in the paper defines
  - the function `PURE`
  - the function `AP`
  - the function `JOIN`
* Figure 4 in the paper defines
  - the function `SPAN` which corresponds to the use of `(fun _ => nat)` in the mechanisation
  - the function `WORK` which corresponds to the use of `(fun _ => nat)` in the mechanisation
  - the function `span`
  - the function `work`
* Thereom 1 in the paper corresponds to the definition of the function `PURE` itself,
  e.g., the well-formedness of the translated term is guaranteed by the fact that PURE is well-typed.
* Lemma 2 "(AP respects semantics)" in the paper corresponds to the function `AP_eval` in the mechanisation
* Lemma 3 "(JOIN respects semantics)" in the paper corresponds to the function `JOIN_eval` in the mechanisation
* Lemma 4 "(relabel respects semantics)" in the paper corresponds to the functions `to_eval_src`, `to_eval_tgt` in the mechanisation
* Theorem 5 "(PURE preserves semantics)" in the paper corresponds to the function `eval_pres` in the mechanisation
* Theorem 5 "(PURE preserves semantics)" in the paper corresponds to the function `eval_pres` in the mechanisation
* Lemma 6 "(AP respects span and work)" in the paper corresponds to the functions `AP_span` and `AP_work` in the mechanisation
* Lemma 7 "(JOIN respects span and work)" in the paper corresponds to the functions `JOIN_span` and `JOIN_work` in the mechanisation
* Lemma 8 "(com is side-effect free)" in the paper corresponds to the functions `span_com_zero` and `work_com_zero` in the mechanisation
* Lemma 9 "(relabeled terms remain effect-free)" in the paper are separated into two steps,
  first the functions `to_span_src`, `to_span_tgt`, `to_work_src`, `to_work_tgt` in the mechanisation
  show that the span and work is preserved,
  and second the function `span_com_zero` and `work_com_zero` show that the span and work is not only preserved,
  but also equal to zero.
* Theorem 10 "(PURE preserves span and work)" in the paper corresponds to the functions `span_pres` and `work_pres` in the mechanisation

## For authors claiming a reusable badge: What are the authors' claims about the artifact's reusability to be evaluated by the committee?

Please list any reuse scenarios that you envision for your artifact, i.e.,
state how the artifact can be reused or repurposed beyond its role in the submitted paper. Example:

* The Scala implementation provides a direct-style notation as an alternative
  to the for-comprehensions (do-notation), that compiles not only to sequential (monadic),
  but also parallel (applicative) combinators.
  This can be re-used by importing it.
  An example of how our artifact can be reused in new applications can be found in the
  "An example How to change a Case Study (for the Reusable Badge)" section below.

  For evaluation, we suggest writing an additional
  direct-style notation in file `src/scala/src/main/parseq/Tests.scala` and re-running
  the compilation process via the docker image.

  (If you are already familiar with IntelliJ and the Scala3 plugin, you can try that.)
  Otherwise, we suggest a text editor and this very same docker image should suffice
  for testing the reusability by simple changes and compilation.

## For authors claiming an available badge

We agree to publishing our artifact under a Creative Commons license via DARTS.


## Artifact Requirements

HW:
There are no special hardware requirements.
The device you execute the docker image should provide a performance
comparable to a modern Computer or a Laptop.

SW:
We expect artifact reviewers to have preinstalled
- docker,
- a text editor,
- a terminal (tested with `bash`)
- .tar.gz extraction tool

## Getting Started

1) Download the file `par-seq-notation.tar.gz` specified via hotcrp.
2) Extract the .tar.gz in an empty folder, you should get another `docker-image.tar` and a folder `src`.

### Reproduce our Evaluation (for the Functional Badge)

Load the docker image:
`docker load -i docker-image.tar`

Start and execute a docker container:
`docker run -it -e HOST_UID=$(id -u) -v "$PWD"/src:/app par-seq-notation`

Depending on your computer, running the docker image could take between 2 and 10 minutes.

Explanation:

 -  (The argument `-it` will run the container with a text-terminal attached,
    and in interactive mode. This means you can press CTRL-C to stop it.)

 -  (The argument `-v $PWD/src:/app` gives the docker container
    read/write access to the folder `src`, which contains the source code.
    This is also the place where the results will be placed.)

 -  (The argument `-e HOST_UID=(id -u)` will pass an additional environment
    variable into the docker container that contains your user ID.
    Docker creates files by default as user `root`, so you can get confusing
    "permission denied" errors, if you attempt to modify those files later.
    We use the provided user id to give ownership of created files
    back to the current user.)

This will run the Coq and Scala compiler on the provided sources.
Ignore any log messages that describe the progress of compilation,
and ignore any warnings.

The expected output is:

### For coq:

```
 done
 done
 done
 done
 done
 done
 done
 done
Finished transaction in 2.414 secs (0.798u,0.223s) (successful)
Finished transaction in 12.911 secs (12.862u,0.052s) (successful)
 done
Finished transaction in 0.498 secs (0.498u,0.s) (successful)
Finished transaction in 1.635 secs (1.632u,0.004s) (successful)
 done
Finished transaction in 0.493 secs (0.493u,0.s) (successful)
Finished transaction in 1.548 secs (1.537u,0.012s) (successful)
Closed under the global context
Closed under the global context
Closed under the global context
```

What does this mean?
At the end of the proof.v file we use `Print Assumptions` to check that
we did not cheat and use any bad axioms. It looks like this:
```
Succeed Print Assumptions eval_pres. (* -> Closed under the global context *)
Succeed Print Assumptions span_pres. (* -> Closed under the global context *)
Succeed Print Assumptions work_pres. (* -> Closed under the global context *)
```

We expect no axiom to be used; in this case coq will say that the proof is closed under the global context.
For a few additional comments, please look at the comments in the proof.v file directly.

### For scala:

```
...
...
...

Test results:
 - SUCCESS purify each/pure eliminates?
 - SUCCESS purify each/pure eliminates?
 - SUCCESS purify 1+1
 - SUCCESS purify bind
 - SUCCESS purify blocks
 - SUCCESS nested II
 - SUCCESS purify extr extr extr
 - SUCCESS purify if/else body .5
 - SUCCESS purify if/else body
 - SUCCESS purify if/else condition
 - SUCCESS purify extr valdef correctly updates scope
 - SUCCESS purify extr stmt correctly updates scope
 - SUCCESS purify valdef of blocks
 - SUCCESS purify valdef of blocks of unit type, compilercrash
 - SUCCESS purify vardef simple
 - SUCCESS purify vardef extr

...
```

### How to change a Case Study (for the Reusable Badge)

We give an example of how the artifact can be applied to additional programs.
We describe a simple change to demonstrate that the case studies
can be modified and still be compiled:

Open the file `src/scala/src/main/parseq/Tests.scala`.
This file contains the tests that print `- SUCCESS purify vardef extr`.
You can duplicate one of the tests, for example,

```
  tests append Test("purify 1 2 + 3 4",
    actual =
      purify { (each: Extractor[List]) =>
        each(list2(1, 2)) + each(list2(3, 4)) },
    expected =
      List(4,5,5,6)
  )
```

Purify has roughly type `pureify : ((List[X] => X) => X) => List[X]`,
e.g., it will give you an "extractor", e.g., a way to perform a direct-style effect.

(This is extractor is not a normal method -- for example an extraction function
can not actually be implemented for the list type. If the list is non-empty the
extractor could return the head element, but what should it return given an empty list?
Instead the compiler will re-write the expression, such that the surrounding code "continuation"
is called once FOREACH possible answer, e.g., given a list with multiple elements,
all combinations will be tried, and called for an empty list, nothing will be done.)

For example in the expression
`purify { (each: Extractor[List]) => each(list2(1, 2)) + each(list2(3, 4))`

we expect the result
`List(1+3, 1+4, 2+3, 2+4)`

or in other words
`List(4,5,5,6)`.

Note that not all features of scala are supported, for example you cannot
currently use try/catch, while, class/object/function definitions,
but only simple expressions like the Tests demonstrate inside purify.

This is to mimic the features that the for-comprehension in Scala supports.

With the for-comprehension of Scala the previous expression could be written as well, but not in direct-style:
```
for {
  x <- list2(1, 2)
  y <- list2(3, 4)
} yield x + y
```

For the reusable badge, another simple expression that could normally be written with for-comprehensions can be tried out to be formulated in direct-style using purify instead, by duplicating and modifying one of the existing tests like the one described above.
Afterwards the docker container can be invoked again to compile the program again and see whether an additional SUCCESS shows up in the output, demonstrating that the test did run with the expected result.

### Remarks

Depending on your settings and the location of the files,
you might need to execute the docker commands with `sudo`.

