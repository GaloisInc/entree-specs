# Overview
This artifact is the ECOOP submission, Interaction Tree Specifications: A Framework for Specifying Recursive, Effectful Computations that Supports Auto-active Verification, submission #10.

It contains a Coq library containing formalized versions of all definitions and proofs contained in the paper relating to ITree Specifications.
It also contains code for typechecking and extraction for Heapster types, as part of the `saw` tool
Finally, it contains the C source code for the `mbox` examples, with Heapster types already included, as well as Coq proofs of the correctness of the output specifications.
 We have included the source code, relevant build scripts, as well as a Docker image (to quickly verify that the code builds without needing to install dependencies).

# Core Claims
We claim this artifact deserves the reusable badge (and therefore functional and available as well).
This document provides a mapping from definitions and proofs in the paper to formalized versions in the artifact, as well as all of the code needed to run all examples.

## Potential Reuse Scenario
A research team could apply the techniques we used to verify the `mbox` examples to other C programs.
This would involve giving correct Heapster types to the program, extracting functional specifications, writing correctness specifications as ITree Specs, and running the `prove_refinement` tactic and solving all goals that it provides.

A research team could also use ITree Specifications as a target semantics for another programming language.
This would enable them towrite similar specifications, and use the `prove_refinement` tactic to help verify them.

# Getting Started
## Docker

## Build from Source

### Dependencies
#### Saw dependencies
- ghc 8.10.7
- cabal 3.8.1.0
- z3
#### Coq dependencies
- coq 8.15.2
- coq-paco >= 4.1.2
- coq-ext-lib >= 0.11.7
- coq-itree >= 5.0.0
### Build
To build `saw`, which includes the `heapster` tool, navigate to the `saw-script` directory and run `cabal build saw`. This will produce the `saw` executable

To build the ITree Specification library, navigate to the `entree_specs` directory, and run `make && make install`.

To run the `mbox` examples, first navigate to `saw-script/saw-core-coq/coq` and run `make`. Then navigate to `saw-script/heapster-saw/examples` and run `make`.
### Heapster Tool

Heapster can be run using the `saw` executible installed in the Docker image.
For example, running `saw mbox.saw` as discussed below.


### MBox Example

The `mbox` example is located in `/home/coq/saw-script/heapster-saw/examples` in the Docker image. The relevant files are:
- `mbox.c` – the source C file
- `mbox.saw` – the saw-script file which, when executed using `saw mbox.saw`, instructs Heapster to generate `mbox_gen.v`
- `mbox_gen.v` – contains the Heaspter-generated Coq specifications extracted from the C functions in `mbox.c`
- `mbox_proofs.v` – contains proofs of correctness of most of the functions above

The Docker image comes with `mbox_gen.v` generated and `mbox_proofs.v` verified.
However, you can also generate and verify these files yourself as follows:
```
$ rm -rf mbox_gen.v
$ make
```
Instead of calling `make`, you can also go through each step individually by running: `saw mbox.saw` (or `make mbox_gen.v`), `make mbox_gen.vo`, and `make mbox_proofs.vo`.



# Core ITree Specifications Library
## Definitions Table
- `paper_name` -> `repo_name` at `filpath:line#`
    - Notes
- `server_impl` -> `server_impl` at `theories/Rel/SortEx.v:600`
- `server_spec` -> `server_spec` at `theories/Rel/SortEx.v:608`
- `EncodingType` -> `EncodingType` at `theories/Basics/HeterogeneousRelations.v:13`
    - While in the paper, the `EncodingType` class requires a function named `response_type`, in the code it is called `encodes`
- `ReSum` -> `ReSum` at `theories/Core/SubEvent.v:18` and `theories/Core/SubEvent.v:19`
    - While in the paper, `ReSum` is presented as a single typeclass requiring two functions, in the code it is presented as two typeclasses each requiring one function
- `trigger` -> `trigger` at `theories/Core/SubEvent.v:30`
- `itree` -> `entree` at `theories/Core/EnTreeDefinition.v:9-21`
    - The paper presents `itree` with a positive type coinductive definition, while the code repository uses negative types. This causes minor differences in many definitions related to ITrees
- `spin` -> `spin` at `theories/Core/EnTreeDefinition.v:77`
- `euttF` -> `eqitF` at `theories/Eq/Eqit.v:37`
    - `eqitF` is more general than `euttF`, containing boolean parameters that control whether inductive `Tau` steps can be made, as well as the `vclo` parameter which can be useful for certain interactions with the `paco` library, but to understand this code you can assume it is always set to the identity function and can be ignored
- `eutt` -> `eutt` at `theories/Eq/Eqit.v:78`
    - While `eutt` is defined on line `78`, the application of the `paco` libraries greatest fixpoint combinator occurs on line `74`
- `bind` -> `bind` at `theories/Core/EnTreeDefinition.v:46-61`
    - In the code, `bind` is defined in terms of `subst`, which performs an identical computation with the continuation and the tree swapped
- `interp_mrec` -> `interp_mrec` at `theories/Ref/MRecSpec.v:26-37`
- `mrec` -> `mrec` at `theories/Ref/MRecSpec.v:38`
- `evenodd` -> `evenodd` at `theories/Ref/Example.v:24-44`
- `Rel` -> `Rel` at `theories/Basics/HeterogeneousRelations.v:20`
- `PostRel` -> `PostRel` at `theories/Basics/HeterogeneousRelations.v:21`
- `RComposePostRel` -> `RComposePostRel` at `theories/Basics/HeterogeneousRelations.v:31`
- `CoveredType` -> `QuantType` at `theories/Basics/QuantType.v:33`
- `forall_spec` -> `forall_spec` at `theories/Ref/EnTreeSpecDefinition.v:99`
- `exists_spec` -> `exists_spec` at `theories/Ref/EnTreeSpecDefinition.v:101`
- `assume_spec` -> `assume_spec` at `theories/Ref/EnTreeSpecDefinition.v:104`
- `assert_spec` -> `assert_spec` at `theories/Ref/EnTreeSpecDefinition.v:107`
- `SpecEvent` -> `SpecEvent` at `theories/Ref/EnTreeSpecDefinition.v:26`
- `itree_spec` -> `entree_spec` at `theories/Ref/EnTreeSpecDefinition.v:51`
- `refinesF` -> `refinesF` at `theories/Ref/EnTreeSpecDefinition.v:65`
- `refines` -> `refines` at `theories/Ref/EnTreeSpecDefinition.v:95`
- `padded_refines` -> `padded_refines` at `theories/Ref/EnTreeSpecFacts.v:838`
- `interp_mrec_spec` -> `interp_mrec_spec` at `theories/Ref/MRecSpec.v:43-55`
- `mrec_spec` -> `mrec_spec` at `theories/Ref/MRecSpec.v:56`
- `concreteF` -> `isConcreteF` at `theories/Ref/Concrete.v:29`
- `rec_fix_spec` -> `rec_fix_spec` at `theories/Ref/RecSpecFix.v:50`
-  `total_spec` -> `total_spec'` at `theories/Ref/RecFixSpecTotal.v:43`
- `total_spec_fix` -> `total_spec_fix` at `theories/Ref/RecFixSpecTotal.v:53`
- `merge` -> `merge` at `theories/Ref/SortEx.v:241`
- `merge_pre` -> `merge_pre` at `theories/Ref/SortEx.v:261` 
- `merge_post` -> `merge_post` at `theories/Ref/SortEx.v:264`
- `rdec_merge` -> `rdec_merge` at `theories/Ref/SortEx.v:107`
## Theorems
- `padded_refines_bind` -> `padded_refines_bind` at `theories/Ref/EnTreeSpecCombinatorFacts.v:110`
- `padded_refines_trans` -> `padded_refines_trans` at `theories/Ref/EnTreeSpecFacts/v:872`
- `padded_refines_mrec` -> `padded_refine_mrec` at `theories/Ref/EnTreeSpecCombinatorFacts.v:423`
- `total_spec_fix_correct` -> `total_spec_fix_refines_total_spec'` at `theories/Ref/RecFixSpecTotal.v:66`
- `merge_correct` -> `merge_correct` at `theories/Ref/SortEx.v:423`
- `server_correct` -> `server_correct` at `theories/Ref/RecFixSpecTotal.v:619`