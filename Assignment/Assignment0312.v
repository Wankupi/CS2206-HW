Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Psatz.
Require Import SetsClass.SetsClass.
Require Import PV.Syntax.
Import Lang_SimpleWhile.
Require Import PV.DenotationalSemantics.
Require Import PV.RelsAsDenotations.
Import DntSem_SimpleWhile2 DntSem_SimpleWhile3 DntSem_SimpleWhile3_Properties.
Local Open Scope Z.
Local Open Scope sets.
Local Open Scope string.

(************)
(** 习题：  *)
(************)

(** 下面我们定义一项简单的程序变换：右结合变换。例如，将_[(c1;c2);c3]_变换为
    _[c1;(c2;c3)]_。

    首先，这里定义一个辅助函数，该函数假设_[c]_与_[c0]_已经是右结合的，计算
    _[c; c0]_转换后的结果*)

Fixpoint CSeq_right_assoc (c c0: com): com :=
  match c with
  | CSeq c1 c2 => CSeq c1 (CSeq_right_assoc c2 c0)
  | _ => CSeq c c0
  end.

(** 现在，可以在_[CSeq_right_assoc]_的基础上定义右结合变换_[right_assoc]_。*)

Fixpoint right_assoc (c: com): com :=
  match c with
  | CSeq c1 c2 =>
      CSeq_right_assoc (right_assoc c1) (right_assoc c2)
  | CIf e c1 c2 =>
      CIf e (right_assoc c1) (right_assoc c2)
  | CWhile e c1 =>
      CWhile e (right_assoc c1)
  | _ =>
      c
  end.

(** 下面证明：经过右结合变换后，确实程序语句中不再有左结合的结构了。下面分为两步
    定义『无左结合结构』，即_[no_left_assoc]_。*)

Definition not_left_assoc (c: com): Prop :=
  match c with
  | CSeq (CSeq _ _) _ => False
  | _ => True
  end.

Fixpoint no_left_assoc (c: com): Prop :=
  match c with
  | CSeq c1 c2 =>
      not_left_assoc c /\
      no_left_assoc c1 /\ no_left_assoc c2
  | CIf e c1 c2 =>
      no_left_assoc c1 /\ no_left_assoc c2
  | CWhile e c1 =>
      no_left_assoc c1
  | _ =>
      True
  end.

(** 证明也需要分两步进行。请先证明关于_[CSeq_right_assoc]_的引理。*)

Lemma CSeq_right_assoc_no_left_assoc: forall c c0,
  no_left_assoc c ->
  no_left_assoc c0 ->
  no_left_assoc (CSeq_right_assoc c c0).
Proof.
  intros.
  induction c; simpl; try tauto.
  split.
  + apply H.
  + split.
    apply H.
    apply IHc2.
    apply H.
Qed.

(** 下面是需要证明的最终结论。*)

Theorem right_assoc_no_left_assoc: forall c,
  no_left_assoc (right_assoc c).
Proof.
  intros.
  induction c; simpl; try tauto.
  apply CSeq_right_assoc_no_left_assoc; tauto.
Qed.

(************)
(** 习题：  *)
(************)

(** 请证明下面关于行为等价的性质。*)

Theorem if_seq:
  forall e c1 c2 c3,
    [[ if (e) then { c1 } else { c2 }; c3 ]] ~=~
    [[ if (e) then { c1; c3 } else { c2; c3 } ]].
Proof.
  intros.
  unfold cequiv.
  simpl.
  unfold_sem.
  rewrite Rels22_concat_union_distr_r.
  rewrite Rels22_concat_assoc.
  rewrite Rels22_concat_assoc.
  reflexivity.
Qed.

(************)
(** 习题：  *)
(************)

(** 下面请分两步证明：_[right_assoc]_变换前后的程序是语义等价的。*)

Lemma CSeq_right_assoc_sound: forall c c0,
  CSeq_right_assoc c c0 ~=~ [[ c; c0 ]].
Proof.
  intros.
  unfold cequiv.
  simpl.
  induction c, c0;
  simpl;
  try tauto;
  try reflexivity;
  rewrite IHc2;
  unfold_sem;
  rewrite Rels22_concat_assoc;
  reflexivity.
Qed.

Theorem right_assoc_sound: forall c,
  right_assoc c ~=~ c.
Proof.
  intros.
  induction c;
  simpl;
  try rewrite CSeq_right_assoc_sound;
  try rewrite IHc;
  try rewrite IHc1;
  try rewrite IHc2;
  try reflexivity.
Qed.

