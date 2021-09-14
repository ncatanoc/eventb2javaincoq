Require Import state_types.
Require Import coqpredicate.
Require Import btypes.
Require Import ZArith.
Require Import bsemantics.
Import EBSemanticNotations.

Open Scope Z_scope.

Definition create_state (x y z : Z):state Z :=
(update 
 (update 
  (update empty_state 
   (Identifier 1) x) 
   (Identifier 2) y) 
   (Identifier 3) z).

Definition create_ensemble : Ensemble Id :=
(Add Id (Add Id (Add Id (Empty_set Id) (Identifier 1)) (Identifier 2)) (Identifier 3)). 

(* id1 + id2 > 10 *)
Definition pred_sum (vars: Ensemble Id) (s: state Z) : Prop :=
match (find s (Identifier 1)) with
| Some x => match (find s (Identifier 2)) with
            | Some y => x+y>10
            | None => False
            end
| None => False
end.

(* 
   id1 and id2 don't exist in s, so 
   id1+id2>10 -> False 
*)
Example ex_pred1 : forall (s:state Z)(pred:CoqPred),
        s=empty_state
     -> (pred_sum (Empty_set Id) s)
     -> False.
Proof.
intros.
subst.
compute in H0.
trivial.
Qed.

(* 5 + 5 > 10  ->  FALSE *)
Example ex_pred2 : forall (s:state Z),
        s=(create_state 5 5 0) 
     -> (pred_sum create_ensemble s)
     -> False.
Proof.
intros.
subst.
compute in H0.
inversion H0.
Qed.


(* 6 + 5 > 10 *)
Example ex_pred3 : forall (s:state Z),
        s=(create_state 6 5 0) 
     -> (pred_sum create_ensemble s).
Proof.
intros.
subst.
unfold create_ensemble;unfold create_state;compute.
reflexivity.
Qed.

