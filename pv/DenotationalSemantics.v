Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Psatz.
Require Import Coq.Classes.Morphisms.
Require Import SetsClass.SetsClass. Import SetsNotation.
Require Import PV.InductiveType.
Require Import PV.RecurProp.
Require Import PV.Syntax.
Local Open Scope string.
Local Open Scope Z.
Local Open Scope sets.

(** * 简单表达式的指称语义 *)

Module DntSem_SimpleWhile1.
Import Lang_SimpleWhile.

(** 程序状态的定义：*)

Definition state: Type := var_name -> Z.

(** 整数类型表达式的行为：*)

Fixpoint eval_expr_int (e: expr_int) (s: state) : Z :=
  match e with
  | EConst n => n
  | EVar X => s X
  | EAdd e1 e2 => eval_expr_int e1 s + eval_expr_int e2 s
  | ESub e1 e2 => eval_expr_int e1 s - eval_expr_int e2 s
  | EMul e1 e2 => eval_expr_int e1 s * eval_expr_int e2 s
  end.

Notation "⟦ e ⟧" := (eval_expr_int e)
  (at level 0, e custom prog_lang_entry at level 99).

(** 下面是两个具体的例子。*)

Example eval_example1: forall (s: state),
  s "x" = 1 ->
  s "y" = 2 ->
  ⟦ "x" + "y" ⟧ s = 3.
Proof. intros. simpl. rewrite H, H0. reflexivity. Qed.

Example eval_example2: forall (s: state),
  s "x" = 1 ->
  s "y" = 2 ->
  ⟦ "x" * "y" + 1 ⟧ s = 3.
Proof. intros. simpl. rewrite H, H0. reflexivity. Qed.






(** * 行为等价 *)

(** 基于整数类型表达式的语义定义_[eval_expr_int]_，我们可以定义整数类型表达式之
    间的行为等价（亦称语义等价）：两个表达式_[e1]_与_[e2]_是等价的当且仅当它们在
    任何程序状态上的求值结果都相同。*)

Definition iequiv (e1 e2: expr_int): Prop :=
  forall s, ⟦ e1 ⟧ s = ⟦ e2 ⟧ s.

(** 之后我们将在Coq中用_[e1 ~=~ e2]_表示_[iequiv e1 e2]_。*)

Notation "e1 '~=~' e2" := (iequiv e1 e2)
  (at level 69, no associativity).

Example iequiv_sample:
  [["x" + "x"]] ~=~ [["x" * 2]].
Proof.
  intros.
  unfold iequiv.
  intros.
  simpl.
  lia.
Qed.

(** 下面罗列的都是整数类型表达式语义等价的例子。*)

Lemma zero_plus_equiv: forall (a: expr_int),
  [[0 + a]] ~=~ a.
Proof.
  intros.
  unfold iequiv.
  intros.
  simpl.
  lia.
Qed.

Lemma plus_zero_equiv: forall (a: expr_int),
  [[a + 0]] ~=~ a.
Proof.
  intros.
  unfold iequiv.
  intros.
  simpl.
  lia.
Qed.

Lemma minus_zero_equiv: forall (a: expr_int),
  [[a - 0]] ~=~ a.
Proof.
  intros.
  unfold iequiv.
  intros.
  simpl.
  lia.
Qed.

Lemma zero_mult_equiv: forall (a: expr_int),
  [[0 * a]] ~=~ 0.
Proof.
  intros.
  unfold iequiv.
  intros.
  simpl.
  lia.
Qed.

Lemma mult_zero_equiv: forall (a: expr_int),
  [[a * 0]] ~=~ 0.
Proof.
  intros.
  unfold iequiv.
  intros.
  simpl.
  lia.
Qed.

Lemma const_plus_const: forall n m: Z,
  [[EConst n + EConst m]] ~=~ EConst (n + m).
Proof.
  intros.
  unfold iequiv.
  intros.
  simpl.
  reflexivity.
Qed.

Lemma const_minus_const: forall n m: Z,
  [[EConst n - EConst m]] ~=~ EConst (n - m).
Proof.
  intros.
  unfold iequiv.
  intros.
  simpl.
  reflexivity.
Qed.

Lemma const_mult_const: forall n m: Z,
  [[EConst n * EConst m]] ~=~ EConst (n * m).
Proof.
  intros.
  unfold iequiv.
  intros.
  simpl.
  reflexivity.
Qed.

(** 下面定义一种简单的语法变换---常量折叠---并证明其保持语义等价性。所谓常量折叠
    指的是将只包含常量而不包含变量的表达式替换成为这个表达式的值。*)

Fixpoint fold_constants (e : expr_int) : expr_int :=
  match e with
  | EConst n    => EConst n
  | EVar x      => EVar x
  | EAdd e1 e2  =>
      match fold_constants e1, fold_constants e2 with
      | EConst n1, EConst n2 => EConst (n1 + n2)
      | _, _ => EAdd (fold_constants e1) (fold_constants e2)
      end
  | ESub e1 e2 =>
      match fold_constants e1, fold_constants e2 with
      | EConst n1, EConst n2 => EConst (n1 - n2)
      | _, _ => ESub (fold_constants e1) (fold_constants e2)
    end
  | EMul e1 e2 =>
      match fold_constants e1, fold_constants e2 with
      | EConst n1, EConst n2 => EConst (n1 * n2)
      | _, _ => EMul (fold_constants e1) (fold_constants e2)
    end
  end.

(** 这里我们可以看到，Coq中_[match]_的使用是非常灵活的。(1) 我们不仅可以对一个变
    量的值做分类讨论，还可以对一个复杂的Coq式子的取值做分类讨论；(2) 我们可以对
    多个值同时做分类讨论；(3) 我们可以用下划线表示_[match]_的缺省情况。下面是两
    个例子：*)

Example fold_constants_ex1:
  fold_constants [[(1 + 2) * "k"]] =
  [[3 * "k"]].
Proof. intros. reflexivity. Qed.

(** 注意，根据我们的定义，_[fold_constants]_并不会将_[0 + "y"]_中的_[0]_消去。*)

Example fold_expr_int_ex2 :
  fold_constants [["x" - ((0 * 6) + "y")]] =
  [["x" - (0 + "y")]].
Proof. intros. reflexivity. Qed.

(** 下面我们在Coq中证明，_[fold_constants]_保持表达式行为不变。 *)

Theorem fold_constants_sound:
  forall a, fold_constants a ~=~ a.
Proof.
  unfold iequiv. intros.
  induction a.
  + (** 常量的情况 *)
    simpl.
    reflexivity.
  + (** 变量的情况 *)
    simpl.
    reflexivity.
  + (** 加号的情况 *)
    simpl.
    destruct (fold_constants a1), (fold_constants a2);
    rewrite <- IHa1, <- IHa2;
    reflexivity.
  + (** 减号的情况 *)
    simpl.
    destruct (fold_constants a1), (fold_constants a2);
    rewrite <- IHa1, <- IHa2;
    reflexivity.
  + (** 乘号的情况 *)
    simpl.
    destruct (fold_constants a1), (fold_constants a2);
    rewrite <- IHa1, <- IHa2;
    reflexivity.
Qed.


End DntSem_SimpleWhile1.

(** * Coq代数结构：等价关系 *)


(** 先前我们利用Coq归纳类型与递归函数定义了二叉树_[tree]_与二叉树结构相等
    _[same_structure]_。我们还证明过，_[same_structure]_具有传递性
    （_[same_structure_trans]_），事实上，我们还知道_[same_structure]_是一个等价关
    系！数学上，一个二元关系“≡”是一个等价关系当且仅当它满足下面三个性质：

        (1) 自反性：_[forall a, a ≡ a]_ 

        (2) 对称性：_[forall a b, a ≡ b -> b ≡ a]_ 

        (3) 传递性：_[forall a b c, a ≡ b -> b ≡ c -> a ≡ c]_ *)


Lemma same_structure_refl: forall t: tree,
  same_structure t t.
Proof.
  intros.
  induction t; simpl.
  + tauto.
  + tauto.
Qed.

Lemma same_structure_symm: forall t1 t2: tree,
  same_structure t1 t2 -> same_structure t2 t1.
Proof.
  intros.
  revert t2 H; induction t1; simpl; intros.
  + destruct t2; simpl.
    - tauto.
    - tauto.
  + destruct t2; simpl.
    - tauto.
    - specialize (IHt1_1 t2_1).
      specialize (IHt1_2 t2_2).
      tauto.
Qed.

(** 基于等价关系，我们可以对等价的元素进行替换。 *)

Example same_structure_ex1: forall t1 t2 t3 t4,
  same_structure t1 t2 ->
  same_structure t3 t2 ->
  same_structure t3 t4 ->
  same_structure t1 t4.

(** 它的Coq证明如下：*)

Proof.
  intros t1 t2 t3 t4 H12 H32 H34.
  apply (same_structure_trans t1 t2 t4).
  + apply H12.
  + apply (same_structure_trans t2 t3 t4).
    - apply same_structure_symm.
      apply H32.
    - apply H34.
Qed.

(** 在上面的这段Coq证明中，使用了_[same_structure]_的对称性和传递性。然而，更直观的证
    明思路也许应当用_[rewrite]_来刻画。例如，当我们证明整数相等的类似性质时，我们可以
    下面这样写证明。*)

Example Zeq_ex: forall x1 x2 x3 x4: Z,
  x1 = x2 ->
  x3 = x2 ->
  x3 = x4 ->
  x1 = x4.
Proof.
  intros x1 x2 x3 x4 H12 H32 H34.
  rewrite H12, <- H32, H34.
  reflexivity.
Qed.

(** Coq标准库提供了自反、对称、传递与等价的统一定义，并基于这些统一定义提供了
    _[rewrite]_、_[reflexivity]_等证明指令支持。下面三条证明中，_[Reflexive]_、
    _[Symmetric]_与_[Transitive]_是Coq标准库对于自反、对称与传递的定义。Coq标准库还
    将这三个定义注册成了Coq的Class，这使得Coq能够提供一些特定的证明支持。这里的关键字
    也不再使用_[Lemma]_或_[Theorem]_，而是使用_[Instance]_，这表示Coq将在后续证明过
    程中为_[same_structure]_提供自反、对称与传递相关的专门支持。*)

#[export] Instance same_structure_refl': Reflexive same_structure.
Proof. unfold Reflexive. apply same_structure_refl. Qed.

#[export] Instance same_structure_symm': Symmetric same_structure.
Proof. unfold Symmetric. apply same_structure_symm. Qed.

#[export] Instance same_structure_trans': Transitive same_structure.
Proof. unfold Transitive. apply same_structure_trans. Qed.

(** Coq还将这三条性质打包起来，定义了等价关系_[Equivalence]_。要在Coq中证明
    _[same_structure]_是一个等价关系，可以使用_[split]_指令，将“等价关系”规约为“自反
    性”、“对称性”与“传递性”。*)

#[export] Instance same_structure_equiv: Equivalence same_structure.
Proof.
  split.
  + apply same_structure_refl'.
  + apply same_structure_symm'.
  + apply same_structure_trans'.
Qed.

(** 现在，我们可以用_[rewrite]_与_[reflexivity]_重新证明上面的性质：*)

Example same_structure_ex2: forall t1 t2 t3 t4,
  same_structure t1 t2 ->
  same_structure t3 t2 ->
  same_structure t3 t4 ->
  same_structure t1 t4.
Proof.
  intros t1 t2 t3 t4 H12 H32 H34.
  rewrite H12, <- H32, H34.
  reflexivity.
Qed.



(** * Coq代数结构：Morphism *)

(** 尽管_[same_structure]_与普通的等号具有很多相似的性质，但是Coq现在并不支持我们能够
    像处理等号那样使用_[rewrite]_做替换。例如：*)

Example tree_reverse_same_structure_congr_ind_step:
  forall t11 t12 t21 t22 n1 n2,
    same_structure (tree_reverse t11) (tree_reverse t21) ->
    same_structure (tree_reverse t12) (tree_reverse t22) ->
    same_structure
      (Node (tree_reverse t11) n1 (tree_reverse t12))
      (Node (tree_reverse t21) n2 (tree_reverse t22)).
Proof.
  intros.
  Fail rewrite H, H0.
Abort.

(** 下面是_[same_structure]_与等号_[=]_的对比：*)

Example same_structure_vs_eq:
  forall t11 t12 t21 t22 n,
    tree_reverse t11 = tree_reverse t21 ->
    tree_reverse t12 = tree_reverse t22 ->
    Node (tree_reverse t11) n (tree_reverse t12) =
    Node (tree_reverse t21) n (tree_reverse t22).
Proof.
  intros.
  rewrite H, H0.
  reflexivity.
Qed.

(** Coq标准库提供了_[Proper]_表示“保持等价性”。*)

Definition any {A: Type} (a b: A): Prop := True.

#[export] Instance Node_same_structure_morphism:
  Proper (same_structure ==>
          any ==>
          same_structure ==>
          same_structure) Node.

(** 这个性质说得是：_[Node]_是一个三元函数，如果对其第一个参数做_[same_structure]_
    变换，对其第二个参数做任意变换，同时对其第三个参数做_[same_structure]_变换，那么
    这个三元函数的计算结果也会做_[same_structure]_变换。在证明这一结论时，需要展开
    _[Proper]_的定义，还需要展开_[==>]_的定义，它的Coq名字是_[respectful]_。*)

Proof.
  intros.
  unfold Proper, respectful.
  intros t11 t21 ? n1 n2 _ t12 t22 ?.
  simpl.
  tauto.
Qed.

(** 下面补充证明，_[any]_是一个自反关系。*)

#[export] Instance any_refl: forall A: Type, Reflexive (@any A).
Proof.
  intros.
  unfold Reflexive; intros.
  unfold any; tauto.
Qed.

(** 这样我们就可以让_[rewrite]_用上_[Node]_保持_[same_structure]_变换这一性质了。*)

Example tree_reverse_same_structure_congr_ind_step:
  forall t11 t12 t21 t22 n1 n2,
    same_structure (tree_reverse t11) (tree_reverse t21) ->
    same_structure (tree_reverse t12) (tree_reverse t22) ->
    same_structure
      (Node (tree_reverse t11) n1 (tree_reverse t12))
      (Node (tree_reverse t21) n2 (tree_reverse t22)).
Proof.
  intros.
  rewrite H, H0.
  simpl; split; reflexivity.
Qed.

(** 自然，_[tree_reverse]_保持_[same_structure]_也可以用_[Proper]_刻画。*)

#[export] Instance tree_reverse_same_structure_morphism:
  Proper (same_structure ==> same_structure) tree_reverse.
Proof.
  unfold Proper, respectful.
  intros t1.
  induction t1 as [| t11 IHt11 ? t12 IHt12]; intros t2 H;
    destruct t2 as [| t21 ? t22].
  + reflexivity.
  + simpl in H. tauto.
  + simpl in H. tauto.
  + simpl tree_reverse.
    simpl in H. destruct H as [Ht11 Ht12].
    specialize (IHt11 _ Ht11).
    specialize (IHt12 _ Ht12).
    rewrite IHt11, IHt12.
    simpl; split; reflexivity.
Qed.

(** 上面的例子中用_[Proper]_描述了_[Node]_与_[tree_reverse]_这两个函数的性质。其实
    _[Proper]_也可以用于描述谓词的性质。例如，下面性质说的是，如果对
    _[same_structure]_这个谓词的两个参数分别做_[same_structure]_变换，那么变换前后
    的两个命题要么全都成立要么全都不成立，即变换之前的命题成立当且仅当变换之后的命题成
    立，这个“当且仅当”就是下面定理描述中的_[iff]_。 *)

#[export] Instance same_structure_same_structure_morphism:
  Proper (same_structure ==> same_structure ==> iff) same_structure.
Proof.
  unfold Proper, respectful.
  intros.
  rewrite H, H0.
  reflexivity.
Qed.


(** * 行为等价的性质 *)

Module DntSem_SimpleWhile1_Properties.
Import Lang_SimpleWhile DntSem_SimpleWhile1.

(** 整数类型表达式之间的行为等价符合下面几条重要的代数性质。*)

#[export] Instance iequiv_refl: Reflexive iequiv.
Proof.
  unfold Reflexive, iequiv.
  intros.
  reflexivity.
Qed.

#[export] Instance iequiv_symm: Symmetric iequiv.
Proof.
  unfold Symmetric, iequiv.
  intros.
  rewrite H.
  reflexivity.
Qed.

#[export] Instance iequiv_trans: Transitive iequiv.
Proof.
  unfold Transitive, iequiv.
  intros.
  rewrite H, H0.
  reflexivity.
Qed.

#[export] Instance iequiv_equiv: Equivalence iequiv.
Proof.
  split.
  + apply iequiv_refl.
  + apply iequiv_symm.
  + apply iequiv_trans.
Qed.

#[export] Instance EAdd_iequiv_morphism:
  Proper (iequiv ==> iequiv ==> iequiv) EAdd.
Proof.
  unfold Proper, respectful, iequiv.
  intros.
  simpl.
  rewrite H, H0.
  reflexivity.
Qed.

#[export] Instance ESub_iequiv_morphism:
  Proper (iequiv ==> iequiv ==> iequiv) ESub.
Proof.
  unfold Proper, respectful, iequiv.
  intros.
  simpl.
  rewrite H, H0.
  reflexivity.
Qed.

#[export] Instance EMul_iequiv_morphism:
  Proper (iequiv ==> iequiv ==> iequiv) EMul.
Proof.
  unfold Proper, respectful, iequiv.
  intros.
  simpl.
  rewrite H, H0.
  reflexivity.
Qed.

(** 利用这些代数性质，我们可以重新证明_[fold_constants_sound]_。*)

Theorem fold_constants_sound_again:
  forall a, fold_constants a ~=~ a.
Proof.
  intros.
  induction a.
  + simpl.
    reflexivity.
  + simpl.
    reflexivity.
  + simpl.
    destruct (fold_constants a1), (fold_constants a2);
    try (simpl; rewrite IHa1, IHa2; reflexivity).
    rewrite <- IHa1, <- IHa2, const_plus_const.
    reflexivity.
  + simpl.
    destruct (fold_constants a1), (fold_constants a2);
    try (simpl; rewrite IHa1, IHa2; reflexivity).
    rewrite <- IHa1, <- IHa2, const_minus_const.
    reflexivity.
  + simpl.
    destruct (fold_constants a1), (fold_constants a2);
    try (simpl; rewrite IHa1, IHa2; reflexivity).
    rewrite <- IHa1, <- IHa2, const_mult_const.
    reflexivity.
Qed.


End DntSem_SimpleWhile1_Properties.

(** * 利用高阶函数定义指称语义 *)

Module DntSem_SimpleWhile2.
Import Lang_SimpleWhile.

Definition state: Type := var_name -> Z.

Definition add_sem (D1 D2: state -> Z) (s: state): Z :=
  D1 s + D2 s.

Definition sub_sem (D1 D2: state -> Z) (s: state): Z :=
  D1 s - D2 s.

Definition mul_sem (D1 D2: state -> Z) (s: state): Z :=
  D1 s * D2 s.

(** 下面是用于类型查询的_[Check]_指令。*)

Check add_sem.

(** 可以看到_[add_sem]_的类型是_[(state -> Z) -> (state -> Z) -> state -> Z]_，
    这既可以被看做一个三元函数，也可以被看做一个二元函数，即函数之间的二元函数。

    基于上面高阶函数，可以重新定义表达式的指称语义。*)

Definition const_sem (n: Z) (s: state): Z := n.
Definition var_sem (X: var_name) (s: state): Z := s X.

Fixpoint eval_expr_int (e: expr_int): state -> Z :=
  match e with
  | EConst n =>
      const_sem n
  | EVar X =>
      var_sem X
  | EAdd e1 e2 =>
      add_sem (eval_expr_int e1) (eval_expr_int e2)
  | ESub e1 e2 =>
      sub_sem (eval_expr_int e1) (eval_expr_int e2)
  | EMul e1 e2 =>
      mul_sem (eval_expr_int e1) (eval_expr_int e2)
  end.

End DntSem_SimpleWhile2.
