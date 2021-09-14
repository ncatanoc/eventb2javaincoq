(* Copyright (c) 2016, Nestor Catano, Shigeo Nishi, Camilo Rueda
 * EventB2Java  
 * Semantics of JML
 *)
Require Import ZArith.
Require Import Classical_Prop.
Require Import state_types.
Require Import coqpredicate.
Require Import jmltypes.

Definition value := Z.

Local Open Scope eventb_state_scope.

Import EBStateNotations.

(* Eval a BPredicate inner Prop in a given state *)
(*Fixpoint JmlPredEval (jml: JmlPredicate)(s: state value) :=
  match jml with
    | JPred coq W => (coq W s)
    | JExists v' p => (exists (z: value), (JmlPredEval p (s[v' ⇨ z])))
    | JAnd p1 p2   => (JmlPredEval p1 s) /\ (JmlPredEval p2 s)
    | JNot p       => not (JmlPredEval p s)
    | JTrue        => True
end.*)

Definition JmlPredEval (jml: JmlPredicate)(s: state value): Prop :=
  match jml with
    | JPred coq W => (coq W s)
    | JTrue => True
  end.

Inductive JmlPredSem : JmlPredicate -> state value -> Prop :=
| JPredSem: forall (s: state value)(jml: JmlPredicate),
              (JmlPredEval jml s)
              -> (JmlPredSem jml s).

Module JMLSemanticNotations.  
(* Notation for semantics of a JML predicate (ctrl+ x 8 + Enter + u21d1) *)
Notation " s '⇑' jpred "  := 
  (JmlPredSem jpred s)    (at level 50, no associativity).

(* Notation for semantics of a before-after predicate (ctrl+ x 8 + Enter + u21e7) *)
Notation " s '⇧' befAft "  := 
  (s ⇑ (getJPred befAft))    (at level 50, no associativity).


End JMLSemanticNotations.
Import JMLSemanticNotations.

Section JMLSemantics.
  
  Inductive JmlMethSem : JmlMethod -> JmlPredicate -> Ensemble Id ->
                         state value -> state value -> Prop :=
  | JMethSem : forall(method: JmlMethod)
                     (jml: JmlBehaviour)
                     (invariant requires: JmlPredicate)
                     (ensures: BeforeAfter)
                     (W: Ensemble Id)
                     (v v' x: Id)
                     (a b: state value),
                 jml = (getJmlSpec method) 
                 -> requires = (getRequires jml)
                 -> ensures = (getEnsures jml)
                 -> W  = (getJPredVars invariant)
                 -> v  = (getBeforeVar ensures)
                 -> v' = (getAfterVar ensures)
                 -> x  = (getMethodPar method)
                 -> (W ⊆ a)
                 -> (W ⊆ b)
                 -> (v ϵ W)
                 -> not (v' ε a)
                 -> (v' <> v)
                 -> not(v' ϵ W)
                 -> not (x ε a)
                 -> (x <> v)
                 -> (a ⇑ invariant)
                 -> ( exists(y: value),
                        (a[x⇨y] ⇑ requires) ->
                        ( exists(z:value),
                            (a[x⇨y][v'⇨ z] ⇧ ensures) /\
                            (a[x ⇨ y][v ⇨ z] ≛ b) /\
                            (b ⇑ invariant) ) )
                 -> (JmlMethSem method invariant W a b).


  Inductive JmlConsSem : JmlConstructor -> JmlPredicate -> Ensemble Id ->
                         state value -> state value -> Prop :=
  | JConsSem : forall(constructor: JmlConstructor)
                     (jml: JmlBehaviour)
                     (invariant: JmlPredicate)
                     (ensures: BeforeAfter)
                     (W: Ensemble Id)
                     (v v': Id)
                     (a b: state value),
                 jml = (getJmlConsSpec constructor)
                 -> JTrue = (getRequires jml)
                 -> ensures = (getEnsures jml)
                 -> W  = (getJPredVars invariant)
                 -> v  = (getBeforeVar ensures)
                 -> v' = (getAfterVar ensures)  
                 -> a = empty_state
                 -> (*(W ⊆ a) /\*) (W ⊆ b)
                 -> (v ϵ W)
                 -> not (v' ε a)
                 -> (v' <> v)
                 -> not(v' ϵ W)
                 -> ( exists(z: value),
                        (a[v'⇨ z] ⇧ ensures) /\
                        (a[v ⇨ z] ≛ b) /\
                        (b ⇑ invariant) )
                 -> (JmlConsSem constructor invariant W a b).

Inductive JmlClassSem : JmlClass -> state value -> state value -> Prop :=
| JClassSem : forall (class: JmlClass )(method: JmlMethod)(constr: JmlConstructor)
                     (invariant: JmlPredicate)(jml: JmlBehaviour)(W: Ensemble Id)
                     (a b: state value),
                method = (getMethod class) 
                -> constr = (getConstructor class) 
                -> jml = (getJmlSpec method)
                -> W = (getClassVars class)
                -> invariant = (getClassInv class)
                -> ( (JmlConsSem constr invariant W empty_state b) \/
                     (JmlMethSem method invariant W a b) )
                -> (JmlClassSem class a b).
End JMLSemantics.
