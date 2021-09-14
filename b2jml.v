(* Copyright (c) 2016, Nestor Catano, Shigeo Nishi, Camilo Rueda
 * EventB2Java  
 * Event-B to JML Translation
 *)
Require Import state_types.
Require Import btypes.
Require Import jmltypes.

Definition BPred2Jml (bp: BPredicate) : JmlPredicate := 
match bp with
| BPred coq W => JPred coq W
end.

Hint Unfold BPred2Jml.

Definition Assg2Jml(asg: Assignment) : BeforeAfter := 
match asg with
| Assg (BPred coq W) v v' => JBeforeAfter (JPred coq W) v v'
end.

Hint Unfold Assg2Jml.

Definition Guard2Jml (g: Guard) : JmlPredicate :=
match g with
| BPred coq W => JPred coq W
end.

Hint Unfold Guard2Jml.


(*Definition Assg2Jml (asg: Assignment): JmlPredicate := 
  match asg with
    | Assg p v v' => JExists v' (BPred2Jml p)
  end.

Hint Unfold Assg2Jml.*)

(*Definition Init2JmlAux (init: Init) : BeforeAfter := 
match init with
| Assg (BPred coq W) v v' => JBeforeAfter (JPred coq W) v v'
end.

Hint Unfold Init2JmlAux.*)

Definition Event2Jml (e: Event) : JmlMethod := 
match e with
| Any x guard assg => 
  ( JMeth
      x  
      (JBehaviour (Guard2Jml guard)  (*requires*)
                  (Assg2Jml assg)) ) (*ensures*)
end.

Hint Unfold Event2Jml.

Definition Init2Jml(init: Init) : JmlConstructor := 
(JCons
   (JBehaviour
      (JTrue)         (*requires*)
      (Assg2Jml init) (*ensures*)
   )
).

Hint Unfold Init2Jml.

Definition Machine2Jml (m: Machine) : JmlClass := 
match m with
| Mach invariant init W any => 
  JClass
    (BPred2Jml invariant)
    (Init2Jml init)
    W
    (Event2Jml any)
end.

Hint Unfold Machine2Jml.
  