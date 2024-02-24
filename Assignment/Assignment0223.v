Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Psatz.
Require Import PV.InductiveType.
Local Open Scope Z.

(************)
(** 习题：  *)
(************)

Lemma size_nonneg: forall t,
  0 <= tree_size t.
Proof.
  intro.
  induction t; simpl; lia.
Qed.


(************)
(** 习题：  *)
(************)

Lemma reverse_result_Node: forall t t1 k t2,
  tree_reverse t = Node t1 k t2 ->
  t = Node (tree_reverse t2) k (tree_reverse t1).
Proof.
  intros.
  assert(tree_reverse t = Node t1 k t2 -> tree_reverse (tree_reverse t) = tree_reverse (Node t1 k t2)).
  {
    intros.
    rewrite H0.
    reflexivity.
  }
  apply H0 in H.
  specialize (reverse_involutive t) as H3.
  rewrite H3 in H.
  rewrite H.
  reflexivity.
Qed.

(************)
(** 习题：  *)
(************)

(** 下面的_[left_most]_函数与_[right_most]_函数计算了二叉树中最左侧的节点信息与
    最右侧的节点信息。如果树为空，则返回_[default]_。*)

Fixpoint left_most (t: tree) (default: Z): Z :=
  match t with
  | Leaf => default
  | Node l n r => left_most l n
  end.

Fixpoint right_most (t: tree) (default: Z): Z :=
  match t with
  | Leaf => default
  | Node l n r => right_most r n
  end.

(** 很显然，这两个函数应当满足：任意一棵二叉树的最右侧节点，就是将其左右翻转之后
    最左侧节点。这个性质可以在Coq中如下描述：*)

Lemma left_most_reverse: forall t default,
  left_most (tree_reverse t) default = right_most t default.
Proof.
  intros t.
  induction t.

  + simpl.
    reflexivity.

  + intro.
    simpl.
    specialize (IHt2 v) as H3.
    rewrite H3.
    reflexivity.
Qed.

