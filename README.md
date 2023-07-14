      _____           _____            
     |  __ \         / ____|           
     | |__) |_ _ _ _| (___   ___  __ _ 
     |  ___/ _` | '__\___ \ / _ \/ _` |
     | |  | (_| | |  ____) |  __/ (_| |
     |_|   \__,_|_| |_____/ \___|\__, |
                                    | |
                                    |_|

# A Direct-Style Effect Notation for Sequential and Parallel Programs

*(This is the code corresponding to the paper 'A Direct-Style Effect Notation for Sequential and Parallel Programs', published at ECOOP 2023.)*

The Scala implementation provides a direct-style notation as an alternative
to the for-comprehensions (do-notation), that compiles not only to sequential (monadic),
but also parallel (applicative) combinators.
This can be re-used by importing it.
An example of how our artifact can be reused in new applications can be found below.

Besides that, you can also find here the proof that
our translation of our direct-style effect-notation
into explicit functor/applicative/monad-operations
preserves typability, semantics, work and span of the translated terms,
mechanised in Coq and described in the paper.

Arxiv: https://arxiv.org/abs/2305.08496

DOI: https://doi.org/10.4230/LIPIcs.ECOOP.2023.25

## Quickstart - Try it out online

You can try writing programs using parseq via the Scastie Web Editor:
https://scastie.scala-lang.org/vNIbTSQjRKyvHeLOdC6iVw

If you want to know how to write programs using parseq, see the examples here:
[/scala/src/main/scala/parseq/Tests.scala](/scala/src/main/scala/parseq/Tests.scala)

Otherwise, to use in a scala project, you can add the following to your sbt file:
```sbt
resolvers += "jitpack" at "https://jitpack.io"
libraryDependencies += "com.github.stg-tud" % "parseq-notation" % "b3ba165274"	
```

And then use it like this in your scala files:
```
import parseq.{*, given}
purify { (each: Extractor[List]) =>
  each(List(1, 2)) + each(List(3, 4))
}
```

## Getting Started

1) CoqIde for proofs
2) Install IntelliJ + Scala-plugin or VSCode + Metals-plugin for scala code
3) Clone and import repo
4) Have fun!

### Run Tests

Run `run.sh`.

The expected output is:

#### For coq:

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

#### For scala:

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

# How to use parseq notation

For evaluation, we suggest experimenting with writing an additional
direct-style notation expression in file `src/scala/src/main/parseq/Tests.scala`,
and taking it from there.

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

Purify has roughly type `purify : ((List[X] => X) => X) => List[X]`,
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

## Correspondence to the paper

* Which data or conclusions from the paper are generated/supported by the artifact components?

  The proof of the paper is mechanised in Coq. The compiler is implemented as well in Scala 3 via Macros, and a few tests.

* Which activities described in the paper have led to the creation of the artifact components?

  In the paper we have described the formal definition of a structurally recursive code-to-code translation function
  from a direct-style effect notation to monadic and applicative combinators,
  together with a proof of preservation of important properties.
  These can be found in the `coq` folder.

  Additionally, we mentioned an implementation in Scala, that works similar.
  These can be found in the `scala` folder.

More specifically:

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

