(* Copyright (c) 2016, Nestor Catano, Shigeo Nishi, Camilo Rueda
 * EventB2Java  
 * Definition of JML Types
 *)
Require Import state_types.
Require Import coqpredicate.

(*Inductive JmlPredicate :=
| JExists : Id -> JmlPredicate -> JmlPredicate
| JAnd    : JmlPredicate -> JmlPredicate -> JmlPredicate
| JPred   : CoqPred -> Ensemble Id -> JmlPredicate
| JNot    : JmlPredicate -> JmlPredicate
| JTrue.*)

Inductive JmlPredicate :=
| JPred   : CoqPred -> Ensemble Id -> JmlPredicate
| JTrue.

Inductive BeforeAfter :=
  | JBeforeAfter : JmlPredicate -> Id -> Id -> BeforeAfter.

Inductive JmlBehaviour :=
| JBehaviour: JmlPredicate -> BeforeAfter -> JmlBehaviour.

Inductive JmlMethod :=
| JMeth: Id -> JmlBehaviour -> JmlMethod.

Inductive JmlConstructor :=
| JCons: JmlBehaviour -> JmlConstructor.

Inductive JmlClass :=
| JClass: JmlPredicate -> JmlConstructor -> Ensemble Id -> JmlMethod -> JmlClass.

Section JMLTypesAux.
Definition getClassInv (c: JmlClass):=
match c with 
| JClass inv constr W meth => inv
end.

Hint Unfold getClassInv.

Definition getClassVars (c: JmlClass):=
match c with 
| JClass inv constr W meth => W
end.

Hint Unfold getClassVars.

Definition getMethod(c: JmlClass): JmlMethod :=
match c with 
| JClass inv constr W meth => meth
end.

Hint Unfold getMethod.

Definition getConstructor(c: JmlClass): JmlConstructor:=
match c with 
| JClass inv constr W meth => constr
end.

Hint Unfold getConstructor.

Definition getJmlSpec(m: JmlMethod): JmlBehaviour :=
  match m with
    | JMeth x jml => jml
  end.

Hint Unfold getJmlSpec.

Definition getJmlConsSpec(c: JmlConstructor): JmlBehaviour :=
  match c with
    | JCons jml => jml
  end.

Hint Unfold getJmlConsSpec.

Definition getMethodPar(m: JmlMethod): Id :=
  match m with
    | JMeth x jml => x
  end.

Hint Unfold getMethodPar.

Definition getRequires(jml: JmlBehaviour): JmlPredicate :=
  match jml with
    | JBehaviour requires ensures => requires
  end.

Hint Unfold getRequires.

Definition getEnsures(jml: JmlBehaviour): BeforeAfter :=
  match jml with
    | JBehaviour requires ensures => ensures
  end.

Hint Unfold getEnsures.

Definition getBeforeVar(ensures: BeforeAfter): Id :=
  match ensures with
    | JBeforeAfter p v v' => v
  end.

Hint Unfold getBeforeVar.

Definition getAfterVar(ensures: BeforeAfter): Id :=
  match ensures with
    | JBeforeAfter p v v' => v'
  end.

Hint Unfold getAfterVar.

Definition getJPred(ensures: BeforeAfter): JmlPredicate :=
  match ensures with
    | JBeforeAfter p v v' => p
  end.

Hint Unfold getJPred.

(*Fixpoint getJPredVars(jp: JmlPredicate): Ensemble Id :=
  match jp with
    | JTrue => Empty_set Id
    | JNot q => getJPredVars q
    | JAnd q1 q2 => Union Id (getJPredVars q1) (getJPredVars q2)
    | JPred _ W => W
    | JExists _ q => getJPredVars q
  end.*)

Definition getJPredVars(p: JmlPredicate): Ensemble Id :=
  match p with
    | JPred coq W => W
    | JTrue => Empty_set Id
  end.

Hint Unfold getJPredVars.

End JMLTypesAux.