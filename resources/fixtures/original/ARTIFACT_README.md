
# Refinement Kinds: Type-safe Programming with Practical Type-level Computation (Artifact)


## Introduction

This is the artifact for the paper Refinement Kinds: Type-safe
Programming with Practical Type-level Computation. The artifact
consists of a prototype kind and type-checker (which also includes
an evaluator) for the language described in the paper.

The artifact is distributed as a Docker image that bundles the source
code, all its dependencies, the code examples from the paper and
various additional examples.

## Getting Started Guide

Since the artifact is distributed as a Docker image, the `docker`
runtime must be installed on the machine where the artifact is to be
tested. If the docker runtime has not yet been installed on the
machine, the installation procedure below should be followed:

### Linux Users

We refer to the URL below for installation instructions:

https://www.digitalocean.com/community/tutorials/how-to-install-and-use-docker-on-ubuntu-18-04

### Windows Users

Docker can be downloaded and installed from the URL below:

https://download.docker.com/win/stable/Docker%20for%20Windows%20Installer.exe

### Mac Users

Docker can be downloaded and installed from the URL below:

https://download.docker.com/mac/stable/Docker.dmg

----

Reviewers should at this point have a working Docker installation on
their machine, with the `docker` command available on the command
line.

To build the artifact, reviewers should uncompress the supplied
archive file, which should produce a directory with the following
contents:

* `Dockerfile` -- configuration file and setup script for the docker image
* `README.md`  -- This file
* `cvc4` -- Linux binary for the CVC4 SMT solver (v1.7)
* `ocaml/` -- Folder containing the ocaml source files for the artifact
* `examples/` -- Folder containing the examples
* `examples/fun_and_rec.rk` -- File with various function and record examples
* `examples/larger_examples.rk` -- File with various larger (mostly record-based) examples
* `examples/paper_examples.rk` -- File with examples from the paper and variations
* `examples/small_examples.rk` -- File with various small examples
* `run_file.sh` -- Helper scripts
* `run_repl.sh` -- Helper scripts
* `run_paper_examples.sh` -- Helper scripts
* `run_all_examples.sh` -- Helper scripts


To build the artifact, proceed as follows:

 1. Ensure that the `docker` daemon (installed above) is running.
 2. Run the command `docker build --tag=refkindchecker .` to build the
 docker image. 
 3. When the build finishes you should see a message with
 "Successfully built" and "Successfully tagged refkindchecker:latest"
 4. To run the docker image (named refkindchecker), execute the
 command `docker run -it refkindchecker`, which will start the
 image and its bash shell in a directory identical to the root of 
 the artifact archive.
 5. To run the artifact as an interactive REPL (inside the running docker image), 
 execute `./run_repl.sh`
 6. Alternatively, the artifact can be run as `./run_file.sh <filename>`,
 which will use as input the contents of `<filename>`.
 7. For convenience, we have provided `run_paper_examples.sh`
 and `run_all_examples.sh` scripts that invoke the prototype on
 examples from the paper and on all sets of examples, respectively.
 Note that when running the artifact while using as input the contents
 of a file, the term or type being checked may not be visible. Only its 
 normal-form is printed.
 8. All files containing the examples can be found in the examples
 folder inside the docker image and in the archive file.
 9. To exit the docker image, press Ctrl-D or run the command `exit`.
 
 
## Step-by-Step Instructions

The artifact is accompanied by a suite of examples that are available
in folder examples. Each of the files in examples has a fairly 
extensive list of example code. All examples pass their respective checks
unless explicitly marked with an appropriate comment. The syntax for 
multi-line comments is `/* ... */`.

Our artifact is intended to illustrate the algorithmic feasibility of
our refinement kind theory, consisting of a prototype implementation
of the key type and kind features presented in the paper.

### Main differences from the paper / Limitations

We did not implement the Collection type, its destructor and corresponding
term level constructs for the sake of simplicity, since its type-level
operations are fundamentally the same as that of reference types and
the term-level operations are standard. We also did not implement the kind 
case construct(s), since they are not crucial to illustrate our main features.

We note that our prototype does not produce very descriptive or useful
error messages. Any failures of checking that are a result from a
failed VC that was passed to the SMT solver can be seen in more detail
by executing the prototype with the `--debug` flag. We also note that 
our implementation is mostly naive and is not optimized for efficiency 
(e.g. we very eagerly query the SMT solver to check that the VC context 
allows us to derive false) and serves mostly as a proof-of-concept for 
the overall approach.



### Interacting with the REPL

The artifact consists of a REPL which expects the following top-level
commands:

  1. `type M;;`
  2.  `type M : T;;`
  3.  `kind T;;`
  4.  `kind T :: K;;`
  5.  `ok K;;`
  6.  `quit;;`

Commands (1) tries to synthesize a type for term M. Command (2) checks
the type of M against T. Commands (3) and (4) are the type-level
analogs of (1) and (2). Command (5) checks that kind K is well-formed
and command (6) terminates the REPL.

### Concrete Syntax

The concrete syntax of our prototype differs somewhat from the syntax
of the paper, for both readability and to simplify the
parser. For instance, functions are written as:

`(fun x:T -> M)`

`(fun t::K -> T)`

with the `:` or `::` distinguishing between a term or type-level
function. We also allow for ML-style let-bindings:

`let TypeID::K = T in ... end`

`let TermID:T = M in ... end`

Recursive (type and term) definitions are provided by using ``letrec``
over ``let``.

We now detail the rest of our concrete syntax.
The concrete syntax of kinds is given by:

``BK ::= Type | Rec | Lab | Ref | Gen T |``

``K  ::= Pi t::K.K | { s :: BK | F }``

The concrete syntax of types is given by:

        T ::= int | bool | top | string | ref T
            | T1 -> T2
            | fun t::K -> T
            | T1 T2
            | All t::K . T
            | `L
            | [||]
            | [|`L:T|]@T
            | headlb T | head T| tail T
            | dom T | cod T
            | refof T
            | if F then T1 else T2
    

We provide some syntactic sugar to ease the writing of record types.
We allow ``[| `L1:T1 , .... , `Ln:Tn |]`` to stand for the record type
``[|`L:T|]@ .... @([| `Ln:Tn|])@[||]``. Note that record labels must
always begin with the symbol . The record destructors are written
`headlb`, `head` and `tail`, with the expected semantics according to the
paper.

The function type destructors are written `dom T` and `cod T`,
with `dom T` projecting the domain type of T and `cod T` the co-domain.

The reference type destructors is written `refof T`.

The type-level property test is written `if F then T1 else T2`.

The concrete syntax of refinements is given by:

        ET ::= T| labSet(T) | ET1 U ET2
        F  ::= ~F| F && F | F || F | F => F | true
            | ET1 == ET2
            | empty(ET)
            | ET1 # ET2
            | ET1 inl ET2
     
    
As in the paper, we use extended types in order to reason about
record label sets, which are written `labSet(T)`. We allow for
union of label sets, written `ET1 U ET2`.

The syntax of propositional formulas is standard, noting that negation
is written `~F`.

Equality of types in refinements is written `ET1 == ET2`.

Record emptyness tests are written `empty(T)`. Label set apartness is
written `ET1 # ET2` and the label membership test is written `ET1 inl ET2`.

The concrete syntax of terms is given by:

        M ::= x | <integers>| <strings> | true | false
            | fun x:T -> M
            | M1 M2
            | fun t::K -> M
            | []
            | [L=M]@M
            | head M
            | tail M
            | if F then M else M
            | new M
            | !M
            | M := M
 

The syntax of term-level records is distinguished from type-level records
by omitting the use of `|`. We allow for the same sugaring of multiple concatenations of
term-level records as for type-level records. References are created using `new M` instead of 
`ref M` from the abstract syntax in the paper.

Recall that recursive definitions are allowed via the let-rec construct
described earlier.

### Final Remarks

We emphasize again that our artifact serves as a proof of concept implementation
of the key concepts of refinement kinds presented in the paper. Usability (and
even efficiency) was not a significant concern. To this end, the artifact has
some instabilities that we hope to address in an upcoming version that will employ
better overall engineering and design.






