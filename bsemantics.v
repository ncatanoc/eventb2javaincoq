(* Copyright (c) 2016, Nestor Catano, Shigeo Nishi, Camilo Rueda
 * EventB2Java  
 * Semantics of Event-B
 *)
Require Import state_types.
Require Import btypes.
Require Import ZArith.

Definition value := Z.

Local Open Scope eventb_state_scope.

(* Evaluation of a BPredicate *)
Definition BPredEval(p: BPredicate)(s: state value) : Prop :=
  match p with
    | BPred coq W => (coq W s)
  end.

Hint Unfold BPredEval.

(* semantics of a BPredicate *)
Inductive BPredSem(p: BPredicate)(s: state value) : Prop :=
| CPredSem : (BPredEval p s) -> (BPredSem p s).


(* Notations are within a Module so as to avoid conflicts *)
Module EBSemanticNotations.  
(* Notation for semantics of a predicate (ctrl+ x 8 + Enter + u2191) *)
Notation " s '↑' p " := 
  (BPredSem p s) (at level 50, no associativity).

(* Notation for semantics of an assignment (ctrl+ x 8 + Enter + u21c8) *)
Notation " s '⇈' asg " := 
  (s ↑ (getAssgPred asg)) (at level 50, no associativity).

End EBSemanticNotations.  

Import EBSemanticNotations.
Import EBStateNotations.

Section EBSemantics.

Inductive AssgSem: Assignment -> BPredicate -> Ensemble Id ->
                   state value -> state value -> Prop :=
| CAssgSem : forall (asg: Assignment)
                    (invariant: BPredicate)
                    (W U: Ensemble Id)
                    (v v': Id)
                    (a b: state value),
               W  = (getBPredVars invariant)
               -> U  = (getBPredVars (getAssgPred asg)) 
               -> v  = (getAssignedVar asg) 
               -> v' = (getPrimedVar asg)
               -> (Setminus Id U W) = (Singleton Id v')
               -> (W ⊆ a)
               -> (W ⊆ b)
               -> (v ϵ W)
               -> not (v' ε a)
               -> (v' <> v)
               -> not(v' ϵ W)
               -> (a ↑ invariant) 
               -> (exists(z: value),
                      (a[v'⇨ z]) ⇈ asg /\
                      (a[v ⇨ z]) ≛ b /\
                      (b ↑ invariant))
                -> (AssgSem asg invariant W a b).

Inductive EventSem : Event -> BPredicate -> Ensemble Id ->
                   state value -> state value -> Prop :=
| AnySem : forall (any: Event)
                  (asg: Assignment)
                  (guard: BPredicate)
                  (invariant: BPredicate)
                  (W: Ensemble Id)
                  (v v' x: Id)
                  (a b: state value),
             asg = (getEventAssg any)
             -> guard = (getEventGuard any)
             -> W  = (getBPredVars invariant)
             -> v  = (getAssignedVar asg)
             -> v' = (getPrimedVar asg)
             -> x  = (getEventPar any)
             -> (W ⊆ a)
             -> (W ⊆ b)
             -> (v ϵ W)
             -> not (v' ε a)
             -> (v' <> v)
             -> not(v' ϵ W)
             -> not (x ε a)
             -> (x <> v)
             -> (a ↑ invariant) 
             -> ( exists(y: value),
                    (a[x ⇨ y] ↑ guard) -> 
                     ( exists(z: value),
                         ((a[x ⇨ y])[v'⇨ z]) ⇈ asg /\
                         (a[x ⇨ y][v ⇨ z]) ≛ b /\
                         (b ↑ invariant) ) )
             -> (EventSem any invariant W a b).

Inductive InitSem : Init -> BPredicate -> Ensemble Id ->
                    state value -> state value -> Prop :=
| CInitSem : forall (init: Init)
                    (invariant: BPredicate)
                    (W: Ensemble Id)
                    (v v': Id)
                    (a b: state value),
               W = (getBPredVars invariant) 
               -> v  = (getAssignedVar init) 
               -> v' = (getPrimedVar init)
               -> a = empty_state
               -> (*(W ⊆ a) /\*) (W ⊆ b)
               -> (v ϵ W)
               -> not (v' ε a)
               -> (v' <> v)
               -> not(v' ϵ W)
               -> ( exists(z: value),
                      (a[v'⇨ z]) ⇈ init /\
                      (a[v ⇨ z]) ≛ b /\
                      (b ↑ invariant) )
               -> (InitSem init invariant W a b).

Inductive MachineSem : Machine -> state value -> state value -> Prop :=
| CMachineSem : forall (m: Machine)
                       (invariant: BPredicate)
                       (init: Init)
                       (W: Ensemble Id)
                       (any: Event)
                       (a b: state value),
                  init = (getMachineInit m)
                  -> invariant = (getMachineInvariant m) 
                  -> W = (getMachineVars m) 
                  -> any = (getMachineEvent m)
                  -> ( (InitSem init invariant W empty_state b) \/ (EventSem any invariant W a b) )
                  -> (MachineSem m a b).

End EBSemantics.