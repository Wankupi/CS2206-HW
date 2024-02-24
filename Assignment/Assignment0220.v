
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Psatz.
Require Import PV.Intro.
Local Open Scope Z.

(************)
(** 习题：  *)
(************)

(** 我们可以使用乘法运算定义“正负号不同”这个二元谓词。请基于这一定义完成相关性质的Coq证
    明。*)

Definition opposite_sgn (x y: Z): Prop := x * y < 0.

Fact opposite_sgn_plus_2: forall x,
  opposite_sgn (x + 2) x ->
  x = -1.
Proof.
  unfold opposite_sgn.
  nia.
Qed.


Fact opposite_sgn_odds: forall x,
  opposite_sgn (square x) x ->
  x < 0.
Proof.
  unfold opposite_sgn.
  unfold square.
  nia.
Qed.
