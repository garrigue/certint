## A Certified Interpreter for ML with Structural Polymorphism
### Jacques Garrigue, updated November 2019

The files in this archive contain a proof of type soundness for structural
polymorphism based on local constraints [1], together with soundness
and principality of the type inference algorithm.
I started from a proof of type soundness for core ML by Arthur
Chargueraud, which accompanied "Engineering formal metatheory" [2].
The library files (Lib_* and Metatheory*) are almost untouched.
For compatibility we also copied FSetList.v from Coq 8.2.
The new files are as follows.
* `Metatheory_SP`: new generic lemmas used in developments
* `Cardinal`: lemmas about finite set cardinals
* `ML_SP_Definitions`: basic definitions
* `ML_SP_Infrastructure`: structural lemmas on kinds and types
* `ML_SP_Soundness`: lemmas on derivations and proof of type soundness
* `ML_SP_Eval`: proof of type soundness for a stack-based evaluator
* `ML_SP_Rename`: renaming lemmas, and Gc elimination
* `ML_SP_Unify`: soundness and completeness of unification
* `ML_SP_Inference`: soundness and principality of type inference
* `ML_SP_Domain`: instantiation of all the above proofs to polymorphic variants
* `ML_SP_Unify/Inference_wf`: termination counters are in Prop

Of the above, Definitions, Infrastructure and Soundness are base on
the core ML proof, but were heavily modified.
Eval, Unify, Inference and Domain are completely new.
Read the accompanying paper [3] for information on the proof.

All the above development were checked with coq 8.10.1.
(Porting to 8.10.1 is the only change wrt. the version of september 2010)
You can compile them with "sh build.sh"

You can also play with the type checker. It does not work inside Coq
at this point, but you should compile typinf.mli and typinf.ml
(obtained by running Extraction.v), and look at use_typinf.ml for how
to use them. (It contains a number of petty printers and conversion
functions that make things easier).

Here are all the steps: (the first 3 steps are optional)
```
$ sh mkmakefile.sh
$ make Extraction.vo
$ make html
$ ocamlc -c typinf.mli
$ ocamlc -c typinf.ml
$ ocaml
        Objective Caml version ...
# #use "use_typinf.ml";;
```

[1] Jacques Garrigue: Simple Type Inference for Structural Polymorphism.
    FOOL 9, Portland, Oregon, January 2002.
    [link](http://www.math.nagoya-u.ac.jp/~garrigue/papers/#strucpoly)

[2] Brian Aydemir, Arthur Chargueraud, Benjamin C. Pierce, Randy Pollack
    and Stephanie Weirich: Engineering Formal Metatheory. POPL'08.
    [link](http://www.chargueraud.org/arthur/research/2007/binders/)

[3] Jacques Garrigue: A Certified Interpreter of ML with Structural
                      Polymorphism and Recursive Types.
    Mathematical Structures in Computer Science, November 2014, pages 1-25.
    Earlier version presented at APLAS'10, Shanghai, China, November 2010.
    [link](http://www.math.nagoya-u.ac.jp/~garrigue/papers/aplas2010.html)
