(* Copyright (c) 2016, Nestor Catano, Shigeo Nishi, Camilo Rueda
 * EventB2Java  
 * Coq Predicates
 *)
Require Import state_types.
Require Import ZArith.

Definition CoqPred := Ensemble Id -> (state Z) -> Prop.