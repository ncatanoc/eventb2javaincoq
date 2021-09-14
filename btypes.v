(* Copyright (c) 2016, Nestor Catano, Shigeo Nishi, Camilo Rueda
 * EventB2Java  
 * Definition of Event-B Types
 *)
Require Import state_types.
Require Import ZArith.
Require Import coqpredicate.

Section EBTypes.

Inductive BPredicate :=
| BPred : CoqPred -> Ensemble Id -> BPredicate.

Definition Guard := BPredicate.

(* BPredicate that depends on v and v' *)
Inductive Assignment :=
| Assg : BPredicate -> Id -> Id -> Assignment.

Definition Init := Assignment.

Inductive Event := 
| Any : Id -> Guard -> Assignment -> Event.

Inductive Machine := 
| Mach : BPredicate -> Init -> Ensemble Id -> Event -> Machine.

End EBTypes.


Section EBTypesAux.

Definition getEventGuard (any: Event) :=
match any with 
| Any x g asg => g
end.

Hint Unfold getEventGuard.

Definition getEventAssg (any: Event) :=
match any with 
| Any x g asg => asg
end.

Hint Unfold getEventAssg.

Definition getBPredVars(p: BPredicate): Ensemble Id :=
  match p with
    | BPred coq W => W
  end.

Hint Unfold getBPredVars.

Definition getEventPar (any: Event) :=
match any with 
| Any x g asg => x
end.

Hint Unfold getEventPar.

Definition getAssgPred (asg: Assignment) :=
match asg with
| Assg p v v' => p
end.

Hint Unfold getAssgPred.

Definition getAssignedVar (asg: Assignment): Id :=
match asg with 
| Assg coq v v' => v
end.

Hint Unfold getAssignedVar.

Definition getPrimedVar (asg: Assignment): Id :=
match asg with 
| Assg coq v v' => v'
end.

Hint Unfold getPrimedVar.

Definition getMachineVars(m: Machine):=
  match m with
    | Mach inv init w any => w
  end.

Hint Unfold getMachineVars.

Definition getMachineInit(m: Machine):=
  match m with
    | Mach inv init w any => init
  end.

Hint Unfold getMachineInit.

Definition getMachineInvariant(m: Machine):=
  match m with
    | Mach invariant init w any => invariant
  end.

Hint Unfold getMachineInvariant.

Definition getMachineEvent(m: Machine):=
  match m with
    | Mach invariant init w any => any
  end.

Hint Unfold getMachineEvent.

End EBTypesAux.