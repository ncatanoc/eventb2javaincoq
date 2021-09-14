Require Import coqpredicate.
Require Import state_types.
Require Import b2jml.
Require Import theproof.
Require Import btypes.

Extraction Language Ocaml. 


(*Extract Constant CoqPred => "set*state->bool".*)
Extract Inductive bool => "bool" ["true" "false"].
        
Extract Constant CoqPred => "Set.Make(String).t*(nat state)->bool".

Extraction "machine2jml.ml" Machine2Jml state CoqPred BPredicate.

