(* Copyright (c) 2016, Nestor Catano, Shigeo Nishi, Camilo Rueda
 * EventB2Java  
 * Definition of state
 *)

Require Import ZArith.
Require Export Ensembles.

Delimit Scope eventb_state_scope with eventb_state_scope.

Section EventBStates.

Inductive Id: Type :=
 | Identifier : nat -> Id.

(* boolean equality for elements of type Id *)
Definition beq_id id1 id2: bool :=
 match id1, id2 with
  | Identifier n1, Identifier n2 => beq_nat n1 n2
 end.

(* state modelled as a total function of type A *)
Definition total_state (A: Type) : Type :=
  Id -> A.

(* The empty total_state function in which v is the default value *)
Definition empty_total_state {A: Type} (v: A) : total_state A :=
 (fun _ => v).

(* update of state s *)
Definition total_update {A: Type} (s: total_state A)
           (x: Id) (v: A) :=
  fun y => if beq_id y x then v else s y.

(* partial function state definition *)
Definition state (A: Type) : Type :=
 Id -> option A.

(* the empty partial state function *)
Definition empty_state {A:Type} : state A :=
 empty_total_state None.

(* update of state s *)
Definition update {A: Type} (s: state A) 
           (x: Id) (v: A) :=
 total_update s x (Some v).

(* finds the value of variable i in state s *)
Definition find {A: Type} (s: state A) (x: Id) : option A:=
  s x.

Hint Unfold find.

(* checks if identifier i is in the domain of state s *)
Definition isFound {A:Type} (s: state A)(x: Id): Prop := 
match find s x with
   Some _ => True
  | None => False
end.

Hint Unfold isFound.

Definition inState {A:Type} (s: state A)(w: Ensemble Id): Prop :=
  forall x:Id, In Id w x -> isFound s x.

Hint Unfold inState.

(* state equality *)
Definition beq_state {A: Type} (s1: state A)(s2: state A) : Prop :=
  forall y, find s1 y = find s2 y.
End EventBStates.


Module EBStateNotations.
(* Notations: within a Module to avoid conflicts *)
  
(* Notation for checking if variable x is in the domain of state s *)
(* It returns a Prop *)
(* Ctrl + x 8 Enter 03b5 *)   
Notation " x 'ε' s "  := 
 (isFound s x)
   (at level 50, no associativity).

(* Notation for checking if a variable x is part of a set w *)
(* It returns a Prop *)
(* Ctrl + x 8 Enter 03f5 *)   
Notation " x 'ϵ' w "  := 
 (w x)
(at level 50, no associativity).

(* Notation for checking if a set of variables is included in the domain of state s *)
(* It returns a Prop *)
(* Ctrl + x 8 Enter 2286  *)  
Notation " w '⊆' s "  := 
 (inState s w)
(at level 50, no associativity).

(* Notation for overriding state s with pair x |-> y;
   if x is not in the domain of s, then the notation extends the 
   state s with the pair x |-> y.
 Ctrl + x 8 Enter 21e8
*)
Notation " s '[' x '⇨' y ']' " := 
 (update s x y)
(at level 50, no associativity).

(* Notation for variable evaluation *)
Notation "s '[' x ']'" := 
 (find s x)
(at level 50, no associativity).

(* Notation for state equivalence *)
(* It returns a Prop *)
(* Ctrl + x 8 Enter 225b *)
Notation "s1 '≛' s2" := 
 (beq_state s1 s2)
(at level 50, no associativity).

(* it substitutes the value of x in the domain of state s with n; 
   if x is not in the domain of state s, then it returns s unchanged *)
(*Notation "'[' x '\' n ']' s " := 
 match find s x with
   None => s
 | Some v => (update s x n)
end
(at level 50, no associativity).*)
End EBStateNotations.

Import EBStateNotations.