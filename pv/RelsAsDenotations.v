Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Psatz.
Require Import Coq.Classes.Morphisms.
Require Import SetsClass.SetsClass. Import SetsNotation.
Require Import PV.InductiveType.
Require Import PV.RecurProp.
Require Import PV.Syntax.
Require Import PV.DenotationalSemantics.
Local Open Scope string.
Local Open Scope Z.
Local Open Scope sets.


(** * 在Coq中表示集合与二元关系 *)

(** SetsClass拓展库中提供了有关集合的一系列定义。例如：
   
    - 空集：用 _[∅]_ 或者一堆方括号表示，定义为_[Sets.empty]_；

    - 全集：定义为_[Sets.full]_（全集没有专门的表示符号）；

    - 单元集：用一对方括号表示，定义为_[Sets.singleton]_；

    - 补集：定义为_[Sets.complement]_（补集没有专门的表示符号）；

    - 并集：用_[∪]_表示，定义为_[Sets.union]_；

    - 交集：用_[∩]_表示，定义为_[Sets.intersect]_；

    - 集合相等：用_[==]_表示，定义为_[Sets.equiv]_；

    - 元素与集合关系：用_[∈]_表示，定义为_[Sets.In]_；

    - 子集关系：用_[⊆]_表示，定义为_[Sets.included]_；

    在这些符号中，补集以及其他Coq函数的优先级最高，交集的优先级其次，并集的优先级再次，
    集合相等、集合包含与属于号的优先级最低。

    SetsClass拓展库中提供了这些关于二元关系的定义：
   
    - 二元关系的连接：用 _[∘]_表示，定义为_[Rels.concat]_；

    - 相等关系：定义为_[Rels.id]_（没有专门的表示符号）；

    - 测试：定义为_[Rels.test]_（没有专门的表示符号）。
*)



(** * Coq中定义程序语句的指称语义 *)

Module DntSem_SimpleWhile3.
Import Lang_SimpleWhile
       StateModel_SimpleWhile1
       DntSem_SimpleWhile2.

Record asgn_sem
         (X: var_name)
         (D: state -> Z)
         (s1 s2: state): Prop :=
  {
    asgn_sem_asgn_var: s2 X = D s1;
    asgn_sem_other_var: forall Y, X <> Y -> s2 Y = s1 Y;
  }.

Notation "H '.(asgn_sem_asgn_var)'" :=
  (asgn_sem_asgn_var _ _ _ _ H)
  (at level 1).

Notation "H '.(asgn_sem_other_var)'" :=
  (asgn_sem_other_var _ _ _ _ H)
  (at level 1).


Definition skip_sem: state -> state -> Prop :=
  Rels.id.

Definition seq_sem (D1 D2: state -> state -> Prop):
  state -> state -> Prop :=
  D1 ∘ D2.

Definition test_true
             (D: state -> bool):
  state -> state -> Prop :=
  Rels.test (fun s => D s = true).

Definition test_false
             (D: state -> bool):
  state -> state -> Prop :=
  Rels.test (fun s => D s = false).

Definition if_sem
             (D0: state -> bool)
             (D1 D2: state -> state -> Prop):
  state -> state -> Prop :=
  (test_true D0 ∘ D1) ∪ (test_false D0 ∘ D2).

Fixpoint iterLB
           (D0: state -> bool)
           (D1: state -> state -> Prop)
           (n: nat):
  state -> state -> Prop :=
  match n with
  | O => test_false D0
  | S n0 => test_true D0 ∘ D1 ∘ iterLB D0 D1 n0
  end.

Module WhileSem1.

(** 第一种定义方式 *)
Definition while_sem
             (D0: state -> bool)
             (D1: state -> state -> Prop):
  state -> state -> Prop :=
  ⋃ (iterLB D0 D1).

End WhileSem1.

Fixpoint boundedLB
           (D0: state -> bool)
           (D1: state -> state -> Prop)
           (n: nat):
  state -> state -> Prop :=
  match n with
  | O => ∅
  | S n0 =>
      (test_true D0 ∘ D1 ∘ boundedLB D0 D1 n0) ∪
      (test_false D0)
  end.

Module WhileSem2.

(** 第二种定义方式 *)
Definition while_sem
             (D0: state -> bool)
             (D1: state -> state -> Prop):
  state -> state -> Prop :=
  ⋃ (boundedLB D0 D1).

End WhileSem2.

(** 我们选择第二种定义。*)

Export WhileSem2.


(** 下面是程序语句指称语义的递归定义。*)

Fixpoint eval_com (c: com): state -> state -> Prop :=
  match c with
  | CSkip =>
      skip_sem
  | CAsgn X e =>
      asgn_sem X (eval_expr_int e)
  | CSeq c1 c2 =>
      seq_sem (eval_com c1) (eval_com c2)
  | CIf e c1 c2 =>
      if_sem (eval_expr_bool e) (eval_com c1) (eval_com c2)
  | CWhile e c1 =>
      while_sem (eval_expr_bool e) (eval_com c1)
  end.

Notation "⟦ c ⟧" := (eval_com c)
  (at level 0, only printing, c custom prog_lang_entry at level 99).

Ltac get_prog_syntax x ::=
  match type of x with
  | expr_int => constr:(x)
  | Z => constr:(EConst x)
  | string => constr:(EVar' x)
  | var_name => constr:(EVar x)
  | expr_bool => constr:(x)
  | com => constr:(x)
  end.

Ltac any_eval' x ::=
  match goal with
  | |- _ -> Z    => exact (eval_expr_int x)
  | |- _ -> bool => exact (eval_expr_bool x)
  | |- _ -> Prop => exact (eval_com x)
  | _            =>
    match type of x with
    | expr_int  => exact (eval_expr_int x)
    | expr_bool => exact (eval_expr_bool x)
    | com       => exact (eval_com x)
    end
  end.

Ltac unfold_com_sem :=
  cbv [seq_sem if_sem while_sem skip_sem].

Ltac unfold_com_sem_in_hyp H :=
  cbv [seq_sem if_sem while_sem skip_sem] in H.

Ltac ___unfold_sem ::=
  simpl eval_com; simpl eval_expr_bool; simpl eval_expr_int;
  unfold_com_sem; unfold_expr_bool_sem; unfold_expr_int_sem.

Ltac ___unfold_sem_in_hyp H ::=
  simpl eval_com in H;
  simpl eval_expr_bool in H;
  simpl eval_expr_int in H;
  unfold_com_sem_in_hyp H;
  unfold_expr_bool_sem_in_hyp H;
  unfold_expr_int_sem_in_hyp H.


End DntSem_SimpleWhile3.

(** * 集合、关系与逻辑命题的Coq证明 *)

(** ** 集合命题的基本证明方法 *)

(** _[Sets_unfold]_指令可以将集合的性质转化为逻辑命题。 *)

Theorem Sets1_intersect_included1: forall A (X Y: A -> Prop),
  X ∩ Y ⊆ X.
Proof.
  intros.
  (** 下面一条命令_[Sets_unfold]_是SetsClass库提供的自动证明指令，它可以将有关
      集合的性质转化为有关命题的性质。*)
  Sets_unfold.
  (** 原本要证明的关于交集的性质现在就转化为了：
        _[forall a : A, a ∈ X /\ a ∈ Y -> a ∈ X]_
      这个关于逻辑的命题在Coq中是容易证明的。*)
  intros.
  tauto.
Qed.

Lemma Sets1_included_union1: forall A (X Y: A -> Prop),
  X ⊆ X ∪ Y.
Proof.
  intros.
  Sets_unfold.
  (** 经过转化，要证明的结论是：_[forall a : A, a ∈ X -> a ∈ X \/ a ∈ Y]_。*)
  intros.
  tauto.
Qed.

Example Sets2_proof_sample1: forall A B (X Y Z: A -> B -> Prop),
  X ∪ Y ⊆ Z ->
  Y ⊆ Z.
Proof.
  intros.
  Sets_unfold in H.
  Sets_unfold.
  intros a b.
  specialize (H a b).
  tauto.
Qed.


(** 集合相等是一个等价关系，集合包含具有自反性和传递性。集合间的交集、并集和补集运算保
    持“包含”与“被包含”关系，也会保持集合相等关系。SetsClass拓展库提供了这些性质的证
    明，从而支持利用_[rewrite]_指令证明集合性质。*)

Example Sets1_proof_sample2: forall (A: Type) (X Y Z: A -> Prop),
  X == Y -> X == Z -> Y == Z.
Proof.
  intros.
  rewrite <- H, <- H0.
  reflexivity.
Qed.

Example Sets1_proof_sample3: forall (A: Type) (F: (A -> Prop) -> (A -> Prop)),
  (forall X: A -> Prop, X ⊆ F X) ->
  (forall X: A -> Prop, X ⊆ F (F X)).
Proof.
  intros.
  rewrite <- H, <- H.
  reflexivity.
Qed.

Example Sets1_proof_sample4: forall (A: Type) (X1 X2 Y1 Y2: A -> Prop),
  X1 == X2 -> Y1 ⊆ Y2 -> X1 ∪ Y1 ⊆ X2 ∪ Y2.
Proof.
  intros.
  rewrite H, H0.
  reflexivity.
Qed.


(** ** 交集与并集性质的Coq证明 *)

(** 证明集合相等的方法： 
   
        Sets_equiv_Sets_included:
          forall x y, x == y <-> x ⊆ y /\ y ⊆ x
      

    证明交集有关的性质： 

        _[x ⊆ y ∩ z]_可以被规约为_[x ⊆ y]_与_[x ⊆ z]_; 

        _[x ∩ y ⊆ z]_可以被规约为_[x ⊆ z]_; 

        _[x ∩ y ⊆ z]_也可以被规约为_[y ⊆ z]_。 

    在Coq中，前一种证明可以通过_[apply]_下面引理实现。
   
        Sets_included_intersect:
          forall x y z, x ⊆ y -> x ⊆ z -> x ⊆ y ∩ z
      
    而后两种证明可以通过_[rewrite]_下面引理实现。
   
        Sets_intersect_included1:
          forall x y, x ∩ y ⊆ x
        Sets_intersect_included2:
          forall x y, x ∩ y ⊆ y
      
    例如，我们可以如下证明集合交具有交换律和结合律。*)

Theorem Sets1_intersect_comm:
  forall {A: Type} (x y: A -> Prop),
    x ∩ y == y ∩ x.
Proof.
  intros.
  apply Sets_equiv_Sets_included; split.
  + apply Sets_included_intersect.
    - rewrite Sets_intersect_included2.
      reflexivity.
    - rewrite Sets_intersect_included1.
      reflexivity.
  + apply Sets_included_intersect.
  - rewrite Sets_intersect_included2.
    reflexivity.
  - rewrite Sets_intersect_included1.
    reflexivity.
Qed.

Theorem Sets1_intersect_assoc:
  forall {A: Type} (x y z: A -> Prop),
    (x ∩ y) ∩ z == x ∩ (y ∩ z).
Proof.
  intros.
  apply Sets_equiv_Sets_included; split.
  + apply Sets_included_intersect; [| apply Sets_included_intersect].
    - rewrite Sets_intersect_included1.
      rewrite Sets_intersect_included1.
      reflexivity.
    - rewrite Sets_intersect_included1.
      rewrite Sets_intersect_included2.
      reflexivity.
    - rewrite Sets_intersect_included2.
      reflexivity.
  + apply Sets_included_intersect; [apply Sets_included_intersect |].
    - rewrite Sets_intersect_included1.
      reflexivity.
    - rewrite Sets_intersect_included2.
      rewrite Sets_intersect_included1.
      reflexivity.
    - rewrite Sets_intersect_included2.
      rewrite Sets_intersect_included2.
      reflexivity.
Qed.


(** 证明并集有关的性质： 

        _[x ⊆ y ∪ z]_可以被规约为_[x ⊆ y]_; 

        _[x ⊆ y ∪ z]_也可以被规约为_[x ⊆ z]_; 

        _[x ∪ y ⊆ z]_可以被规约为_[x ⊆ z]_与_[y ⊆ z]_。 

    在Coq中，前两种证明可以通过从右向左_[rewrite]_下面引理实现。
   
        Sets_included_union1:
          forall x y, x ⊆ x ∪ y
        Sets_included_union2:
          forall x y, y ⊆ x ∪ y
      
    而后一种证明则可以通过_[apply]_下面引理实现。
   
        Sets_union_included:
          forall x y z, x ⊆ z -> y ⊆ z -> x ∪ y ⊆ z;
      
    有时，包含号_[⊆]_左侧的集合不是一个并集，需要先使用交集对于并集的分配律才能使用
    _[Sets_union_included]_。*)

(************)
(** 习题：  *)
(************)

(** 请证明下面集合运算的性质。*)

Example Sets1_intersect_absorb_union:
  forall {A: Type} (x y: A -> Prop),
    x ∩ (x ∪ y) == x.
Admitted. (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)

(************)
(** 习题：  *)
(************)

(** 请证明下面集合运算的性质。*)

Example Sets1_union_absorb_intersect:
  forall {A: Type} (x y: A -> Prop),
    x ∪ (x ∩ y) == x.
Admitted. (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)


(** 基本证明方法汇总：
   
        Sets_equiv_Sets_included:
          forall x y, x == y <-> x ⊆ y /\ y ⊆ x
        Sets_intersect_included1:
          forall x y, x ∩ y ⊆ x
        Sets_intersect_included2:
          forall x y, x ∩ y ⊆ y
        Sets_included_intersect:
          forall x y z, x ⊆ y -> x ⊆ z -> x ⊆ y ∩ z
        Sets_included_union1:
          forall x y, x ⊆ x ∪ y
        Sets_included_union2:
          forall x y, y ⊆ x ∪ y
        Sets_union_included:
          forall x y z, x ⊆ z -> y ⊆ z -> x ∪ y ⊆ z
        Sets_intersect_union_distr_r:
          forall x y z, (x ∪ y) ∩ z == x ∩ z ∪ y ∩ z
        Sets_intersect_union_distr_l:
          forall x y z, x ∩ (y ∪ z) == x ∩ y ∪ x ∩ z
      

    其他常用性质汇总：
   
        Sets_intersect_comm:
          forall x y, x ∩ y == y ∩ x
        Sets_intersect_assoc:
          forall x y z, (x ∩ y) ∩ z == x ∩ (y ∩ z)
        Sets_union_comm:
          forall x y, x ∪ y == y ∪ x
        Sets_union_assoc:
          forall x y z, (x ∪ y) ∪ z == x ∪ (y ∪ z)
        Sets_union_intersect_distr_l:
          forall x y z, x ∪ (y ∩ z) == (x ∪ y) ∩ (x ∪ z)
        Sets_union_intersect_distr_r:
          forall x y z, (x ∩ y) ∪ z == (x ∪ z) ∩ (y ∪ z)
      *)


(** ** 空集、全集、无穷交与无穷并性质的Coq证明 *)

(** SetsClass拓展库对于空集的支持主要是通过以下性质：空集是一切集合的子集。
   
        Sets_empty_included: forall x, ∅ ⊆ x
      

    相对应的，一切集合都是全集的子集。 
   
        Sets_included_full: forall x, x ⊆ Sets.full
      
    基于这两条性质，可以证明许多有用的导出性质。SetsClass提供的导出性质有：
   
        Sets_union_empty_l: forall x, ∅ ∪ x == x
        Sets_union_empty_r: forall x, x ∪ ∅ == x
        Sets_intersect_empty_l: forall x, ∅ ∩ x == ∅
        Sets_intersect_empty_r: forall x, x ∩ ∅ == ∅
        Sets_union_full_l: forall x, Sets.full ∪ x == Sets.full
        Sets_union_full_r: forall x, Sets.full ∪ ∅ == Sets.full
        Sets_intersect_full_l: forall x, Sets.full ∩ x == x
        Sets_intersect_full_r: forall x, x ∩ Sets.full == x
        Sets_equiv_empty_fact: forall x, x ⊆ ∅ <-> x == ∅
        Sets_equiv_full_fact: forall x, Sets.full ⊆ x <-> x == Sets.full
      *)

(************)
(** 习题：  *)
(************)

(** 前面已经提到，SetsClass拓展库已经证明了_[Sets_intersect_empty_l]_。请你只使用
    _[Sets_empty_included]_以及交集的性质证明它。*)

Lemma Sets1_intersect_empty_l:
  forall (A: Type) (x: A -> Prop), ∅ ∩ x == ∅.
Admitted. (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)


(** SetsClass拓展库提供了两种支持无穷交集和无穷并集的定义。它们的证明方式与普通的并集
    与交集的证明方式是类似的。
   
    - 基于指标集的集合并：如果对于所有_[i: I]_，_[X i]_都是集合，那么_[⋃ X]_表示它们
      这些集合的并，定义为_[Sets.indexed_union]_；
    
    - 基于指标集的集合交：如果对于所有_[i: I]_，_[X i]_都是集合，那么_[⋂ X]_表示它们
      这些集合的交，定义为_[Sets.indexed_intersect]_；
    
    - 广义并：如果_[U]_是集合的集合，那么_[⨆ U]_表示它们的广义并，定义为
      _[Sets.general_union]_；

    - 广义交：如果_[U]_是集合的集合，那么_[⨆ U]_表示它们的广义交，定义为
      _[Sets.general_intersect]_。
*)

Example Sets1_union_indexed_intersect_fact:
  forall {A: Type} (x: nat -> A -> Prop) (y: A -> Prop),
    (⋂ x) ∪ y ⊆ ⋂ (fun n => x n ∪ y).
Proof.
  intros.
  apply Sets_included_indexed_intersect.
  intros n.
  rewrite (Sets_indexed_intersect_included n).
  reflexivity.
Qed.


(** ** 逻辑命题的Coq证明 *)

(** 下面是证明“并且”、“或”与“当且仅当”时常用的证明指令汇总与拓展。 *)


(** ** 二元关系运算性质的Coq证明 *)

(** 二元关系的运算性质： 
   
    - 结合律：_[(x ∘ y) ∘ z == x ∘ (y ∘ z)]_
    
    - 左单位元：_[Rels.id ∘ x == x]_
    
    - 右单位元：_[x ∘ Rels.id == x]_
    
    - 左分配律：_[x ∘ (y ∪ z) == x ∘ y ∪ x ∘ z]_

    - 右分配律：_[(x ∪ y) ∘ z == x ∘ z ∪ y ∘ z]_

    另外，二元关系对并集的分配律对于无穷并集也成立。*)

(************)
(** 习题：  *)
(************)

(** 请根据二元关系连接的定义证明下面性质。*)

Lemma Rels22_concat_assoc:
  forall {A: Type} (x y z: A -> A -> Prop),
    (x ∘ y) ∘ z == x ∘ (y ∘ z).
Admitted. (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)

Lemma Rels22_concat_id_l:
  forall {A: Type} (x: A -> A -> Prop),
    Rels.id ∘ x == x.
Admitted. (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)

Lemma Rels22_concat_union_distr_r:
  forall {A: Type} (x y z: A -> A -> Prop),
    (x ∪ y) ∘ z == x ∘ z ∪ y ∘ z.
Admitted. (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)

