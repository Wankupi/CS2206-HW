Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Psatz.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Equivalence.
Require Import Coq.Classes.Morphisms.
Require Import SetsClass.SetsClass. Import SetsNotation.
Require Import PV.InductiveType.
Require Import PV.RecurProp.
Require Import PV.Syntax.
Require Import PV.DenotationalSemantics.
Import Lang_SimpleWhile
       StateModel_SimpleWhile1
       DntSem_SimpleWhile2.
Local Open Scope string.
Local Open Scope Z.
Local Open Scope sets.

(************)
(** 习题：  *)
(************)

(** 请证明下面关于布尔表达式行为等价的命题。*)

Example true_and_fact:
  forall e: expr_bool,
    [[ ETrue && e ]] ~=~ e.
Proof.
  intros.
  unfold bequiv.
  simpl.
  unfold and_sem.
  simpl.
  reflexivity.
Qed.

(** 请利用已有的结论_[lt_plus_one_fact]_证明下面命题。*)

Example lt_plus_one_and_fact:
  forall e: expr_bool,
    [[ "x" < "x" + 1 && e ]] ~=~ e.
Proof.
  intros.
  unfold bequiv.
  intros s.
  simpl eval_expr_bool.
  unfold and_sem.
  specialize (lt_plus_one_fact s) as H.
  simpl eval_expr_bool in H. 
  rewrite H.
  reflexivity. 
Qed.


