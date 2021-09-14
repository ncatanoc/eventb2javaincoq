(* Copyright (c) 2016, Nestor Catano, Shigeo Nishi, Camilo Rueda
 * EventB2Java  
 * Soundness Proof of the Translation from Event-B to JML
 *)
Require Import state_types.
Require Import coqpredicate.
Require Import btypes.
Require Import ZArith.
Require Import bsemantics.
Require Import jmlsemantics.
Require Import b2jml.
Require Import jmltypes.

Import EBSemanticNotations.
Import JMLSemanticNotations.
Open Scope Z_scope.

Ltac b2jtac_inversion H:=
inversion H; repeat (try congruence;subst;simpl in *;auto).

Ltac b2jtac_unfold :=
repeat (autounfold in *;try congruence;subst;simpl in *;auto).

Lemma empty_state_is_empty:
  forall (s: state value)
         (i: Id),
    s = empty_state 
    -> ~ (isFound s i).
Proof.
  intros.
  unfold isFound; unfold find.
  rewrite -> H.
  destruct 1.
Qed.

Lemma BPred2Jml_preserves_state_vars:
  forall(bpred: BPredicate)
        (jpred: JmlPredicate),
    jpred = (BPred2Jml bpred)
    -> (getJPredVars jpred) = (getBPredVars bpred).
Proof.
  destruct bpred.
  unfold BPred2Jml.
  unfold getBPredVars.
  intros.
  rewrite -> H.
  unfold getJPredVars.
  reflexivity.
Qed.

Lemma BPred2Jml_preserves_invariants:
  forall(binv: BPredicate)
        (s: state value),
    (s ↑ binv) <->
    (s ⇑ (BPred2Jml binv)).
Proof.
  intros;split;intros;
  repeat (destruct binv;inversion H;constructor 1;
          unfold BPred2Jml;simpl in *;auto).
Qed.

Lemma Init2Jml_preserves_framed_vars:
  forall(init: Init),
    (getBeforeVar (getEnsures (getJmlConsSpec (Init2Jml init)))) = (getAssignedVar init) /\
    (getAfterVar (getEnsures (getJmlConsSpec (Init2Jml init)))) = (getPrimedVar init).
Proof.
intros;split;destruct init;
  destruct b;b2jtac_unfold.
Qed.


Lemma Init2Jml_preserves_poststate:
  forall(init: Init)
        (s: state value),
    (s ⇈ init) <->
    (s ⇧ (getEnsures (getJmlConsSpec (Init2Jml init)))).
Proof.
intros;split;intros;constructor 1;
  b2jtac_inversion H;destruct init;
  destruct b;b2jtac_unfold.
Qed.

Lemma EventB2Jml_preserves_prestate:
  forall(any: Event)
        (s: state value),
    (s ↑ (getEventGuard any)) <->
    (s ⇑ (getRequires (getJmlSpec (Event2Jml any)))).
Proof.
intros;split;intros;
  destruct any;
  destruct g;constructor 1;
  b2jtac_inversion H;b2jtac_unfold.
Qed.

Lemma EventB2Jml_preserves_poststate:
  forall(any: Event)
        (s: state value),
    (s ⇈ (getEventAssg any)) <->
    (s ⇧ (getEnsures (getJmlSpec (Event2Jml any)))).
Proof.
intros;split;intros;
  destruct any;
  b2jtac_inversion H;
  constructor 1;destruct a;destruct b;b2jtac_unfold.
Qed.

Lemma Event2Jml_preserves_framed_vars:
  forall(any: Event),
    (getBeforeVar (getEnsures (getJmlSpec (Event2Jml any)))) = (getAssignedVar (getEventAssg any)) /\
    (getAfterVar (getEnsures (getJmlSpec (Event2Jml any)))) = (getPrimedVar (getEventAssg any)) /\
    (getMethodPar (Event2Jml any)) = (getEventPar any).
Proof.
intros;
repeat(split;
       destruct any;
       destruct a;destruct b;b2jtac_unfold).
Qed.

Lemma Machine2Jml_preserves_state_vars:
  forall(m: Machine)
        (class: JmlClass),
	class = (Machine2Jml m)
	-> (getMachineVars m) = (getClassVars class).
Proof.
intros;destruct m; destruct class;b2jtac_unfold.
Qed.

Lemma Machine2Jml_preserves_invariant:
  forall(m: Machine)
	(binv: BPredicate),
    binv = (getMachineInvariant m)
    -> (BPred2Jml binv) = (getClassInv (Machine2Jml m)).
Proof.
intros;destruct binv; destruct m;b2jtac_unfold.
Qed.

Lemma Machine2Jml_Init:
  forall(m: Machine)
        (init: Init),
    init = (getMachineInit m)
    -> (Init2Jml init) = (getConstructor (Machine2Jml m)).
Proof.
intros;destruct m; destruct init;b2jtac_unfold.
Qed.

Lemma Machine2Jml_preserves_framed_vars:
  forall(m: Machine),
    (getBeforeVar (getEnsures (getJmlSpec (getMethod (Machine2Jml m))))) = (getAssignedVar (getEventAssg (getMachineEvent m))) /\
    (getAfterVar (getEnsures (getJmlSpec (getMethod (Machine2Jml m))))) = (getPrimedVar (getEventAssg (getMachineEvent m))) /\
    (getMethodPar (getMethod (Machine2Jml m))) = (getEventPar (getMachineEvent m)).
Proof.
intros;split;
repeat(destruct m;
       apply Event2Jml_preserves_framed_vars).
Qed.

Lemma Machine2Jml_preserves_prestate:
  forall(m: Machine)
        (s: state value),
    (s ↑ (getEventGuard (getMachineEvent m))) <->
    (s ⇑ (getRequires (getJmlSpec (getMethod (Machine2Jml m))))).
Proof.
intros;split;
repeat(destruct m;
       apply EventB2Jml_preserves_prestate).
Qed.

Lemma Machine2Jml_preserves_poststate:
  forall(m: Machine)
        (s: state value),
    (s ⇈ (getEventAssg (getMachineEvent m))) <->
    (s ⇧ (getEnsures (getJmlSpec (getMethod (Machine2Jml m))))).
Proof.
intros;split;
repeat(destruct m;
       apply EventB2Jml_preserves_poststate).
Qed.

Lemma Machine2Jml_preserves_invariants:
  forall(m: Machine)
        (s: state value),
    (s ↑ (getMachineInvariant m)) <->
    (s ⇑ (getClassInv (Machine2Jml m))).
Proof.
intros;split;intros;
  destruct m;b2jtac_inversion H;constructor 1;destruct b;
  b2jtac_unfold.
Qed.

Theorem eb2jml_init_sound:
  forall(binv: BPredicate)
        (jinv: JmlPredicate)
        (init: Init)
        (constr: JmlConstructor)
        (W: Ensemble Id)
        (b: state value),
    jinv = (BPred2Jml binv)
    -> constr = (Init2Jml init)
    -> (JmlConsSem constr jinv W empty_state b)
    -> (InitSem init binv W empty_state b).
Proof.
  intros.
  destruct H1.
  assert (getJPredVars(BPred2Jml binv) = getBPredVars(binv)).
  apply BPred2Jml_preserves_state_vars with (bpred:= binv)(jpred:= (BPred2Jml binv));reflexivity.
  assert ((getBeforeVar (getEnsures (getJmlConsSpec (Init2Jml init)))) = (getAssignedVar init) /\
          (getAfterVar (getEnsures (getJmlConsSpec (Init2Jml init)))) = (getPrimedVar init)).
  apply Init2Jml_preserves_framed_vars with (init:= init).
  destruct H15 as [H15 H16].
  constructor 1 with (v:=v)(v':=v');try congruence; try assumption.
  apply empty_state_is_empty with (s:= empty_state)(i:= v');reflexivity.
  destruct H13 as [zz H13].
  destruct H13 as [H13 [H13_1 H13_2]].
  exists zz.
  split;try apply Init2Jml_preserves_poststate with (init:= init)(s:=(update empty_state v' zz));try congruence.
  split;try rewrite -> H7 in *.
  assumption.
  apply BPred2Jml_preserves_invariants with (binv:= binv)(s:= b); congruence.
Qed.

Theorem eb2jml_event_sound:
  forall(binv: BPredicate)
        (jinv: JmlPredicate)
        (any: Event)
        (asg: Assignment)
        (method: JmlMethod)
        (W: Ensemble Id)
        (a b: state value),
    jinv = (BPred2Jml binv)
    -> asg = (getEventAssg any)
    -> method = (Event2Jml any)
    -> (JmlMethSem method jinv W a b)
    -> (EventSem any binv W a b).
Proof.
  intros.
  destruct H2.
  assert (getJPredVars(BPred2Jml binv) = getBPredVars(binv)).
  apply BPred2Jml_preserves_state_vars with (bpred:= binv)(jpred:= (BPred2Jml binv));reflexivity.
  assert ((getBeforeVar (getEnsures (getJmlSpec (Event2Jml any)))) = (getAssignedVar (getEventAssg any)) /\
          (getAfterVar (getEnsures (getJmlSpec (Event2Jml any)))) = (getPrimedVar (getEventAssg any)) /\
          (getMethodPar (Event2Jml any)) = (getEventPar any)).
  apply Event2Jml_preserves_framed_vars with (any:= any);reflexivity.
  destruct H20 as [H20 [H21 H22]].
  constructor 1 with (asg:= asg)(v:= v)(v':= v')(x:= x)(guard:=(getEventGuard any));try congruence; try assumption.
  apply BPred2Jml_preserves_invariants with (binv:= binv)(s:= a);congruence.
  destruct H18 as [yy H18].
  exists yy.
  intro.
  assert (requires = getRequires (getJmlSpec (Event2Jml any))); try congruence.
  rewrite -> H24 in *.
  assert (update a x yy ⇑ (getRequires (getJmlSpec (Event2Jml any)))).
  apply EventB2Jml_preserves_prestate with (any:= any)(s:=(update a x yy));assumption.
  destruct H18 as [zz [H18_1 [H18_2 H18_3]]];try assumption.
  exists zz.
  split.
  rewrite -> H0 in *.
  apply EventB2Jml_preserves_poststate with (any:=any)(s:=(update (update a x yy) v' zz)).
  congruence.
  split; try assumption.
  apply BPred2Jml_preserves_invariants with (binv:=binv)(s:=b);congruence.
  Qed.
  
Theorem eb2jml_machine_sound:
  forall(m: Machine)
        (init: Init)
        (any: Event)
        (binv: BPredicate)
        (class: JmlClass)
        (W: Ensemble Id)
        (a b: state value),
    init = (getMachineInit m) /\ any = (getMachineEvent m) /\
    binv = (getMachineInvariant m) /\ class = (Machine2Jml m) /\
    W = (getMachineVars m)
    -> (JmlClassSem class a b)
    -> (MachineSem m a b).
Proof.
intros.
destruct H as [H [H1 [H2 [H3 H4]]]].
constructor 1 with
  (invariant:= binv)(init:= init)(W:= W)(any:=any);auto.
destruct class as [jinv constr Wj method].
destruct m as [binv0 init0 W0 any0].
unfold getMachineInit in *; subst.
unfold Machine2Jml in *; subst.
injection H3;intros;subst;clear H3.
b2jtac_inversion H0;elim H5;intros.
left.
apply eb2jml_init_sound with 
  (jinv:=(BPred2Jml binv0))
  (constr:=(Init2Jml init0));auto.
right.
  apply eb2jml_event_sound with 
    (jinv:=(BPred2Jml binv0))
    (asg:=(getEventAssg any0))
    (method:=(Event2Jml any0));auto.
Qed.

