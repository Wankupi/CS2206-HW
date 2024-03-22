Require Import Coq.micromega.Psatz.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Strings.String.
Require Import Coq.Classes.Morphisms.
Require Import SetsClass.SetsClass. Import SetsNotation.
Require Import compcert.lib.Integers.
Require Import PV.Syntax.
Require Import PV.DenotationalSemantics.
Require Import PV.RelsAsDenotations.
Require Import PV.FixedPoint.
Local Open Scope bool.
Local Open Scope string.
Local Open Scope Z.
Local Open Scope sets.

(** * 将运算越界定义为表达式求值错误 - 用部分函数 *)

Module DntSem_SimpleWhile5.
Import Lang_SimpleWhile
       StateModel_SimpleWhile1.

(** 在表达式的指称语义中表示表达式求值错误（有符号64位整数的运算越界的情况）这一概
    念，数学上有两种常见方案。其一是将求值结果由整数改为整数或求值失败。


    我们在定义中会用到CompCert库中定义的64位整数相关常数，即有符号64位整数与无符号64位
    整数的大小边界：_[Int64.max_unsigned]_, _[Int64.max_signed]_, 
    _[Int64.min_signed]_。*)

Ltac int64_lia :=
  change Int64.min_signed with (-9223372036854775808) in *;
  change Int64.max_signed with 9223372036854775807 in *;
  lia.


Definition const_sem (n: Z) (s: state): option Z :=
  if (n <=? Int64.max_signed) && (n >=? Int64.min_signed)
  then Some n
  else None.

Definition var_sem (x: var_name) (s: state): option Z :=
  Some (s x).

Definition add_sem (D1 D2: state -> option Z) (s: state): option Z :=
  match D1 s, D2 s with
  | Some i1, Some i2 =>
      if (i1 + i2 <=? Int64.max_signed) &&
         (i1 + i2 >=? Int64.min_signed)
      then Some (i1 + i2)
      else None
  | _, _ => None
  end.

Definition sub_sem (D1 D2: state -> option Z) (s: state): option Z :=
  match D1 s, D2 s with
  | Some i1, Some i2 =>
      if (i1 - i2 <=? Int64.max_signed) &&
         (i1 - i2 >=? Int64.min_signed)
      then Some (i1 - i2)
      else None
  | _, _ => None
  end.

Definition mul_sem (D1 D2: state -> option Z) (s: state): option Z :=
  match D1 s, D2 s with
  | Some i1, Some i2 =>
      if (i1 * i2 <=? Int64.max_signed) &&
         (i1 * i2 >=? Int64.min_signed)
      then Some (i1 * i2)
      else None
  | _, _ => None
  end.

(** 最终，整数类型表达式的语义可以归结为下面递归定义。*)

Fixpoint eval_expr_int (e: expr_int): state -> option Z :=
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

(** 下面是一些证明自动化指令（可以跳过）。*)

Ltac int64_arith_simpl :=
  repeat
  match goal with
  | |- context [if ?X then Some ?A else None] =>
         match X with
         | context [?A <=? ?B] =>
            first
            [ assert (A <= B) as HHH by int64_lia;
              apply Z.leb_le in HHH;
              rewrite HHH; clear HHH]
         | context [?A >=? ?B] =>
            first
            [ assert (B <= A) as HHH by int64_lia;
              apply Z.geb_le in HHH;
              rewrite HHH; clear HHH]
         | context [true && ?b] => change (true && b) with b
         | context [false && ?b] => change (false && b) with false
         end
  | |- context [if true then ?A else ?B] =>
         change (if true then A else B) with A
  | |- context [if false then ?A else ?B] =>
         change (if false then A else B) with B
  | |- context [match Some ?A with | Some _ => _ | None => _ end] =>
         cbv beta iota
  | |- context [Int64.signed (Int64.repr ?n)] =>
         rewrite (Int64.signed_repr n) by int64_lia
  end.

(** 我们可以在Coq中证明一些关于表达式指称语义的基本性质。*)

Example eval_expr_int_fact0: forall s,
  s "x" = 0 ->
  eval_expr_int [["x" + 1]] s = Some 1.
Proof.
  intros.
  simpl.
  unfold add_sem, var_sem, const_sem.
  rewrite H.
  int64_arith_simpl.
  reflexivity.
Qed.

End DntSem_SimpleWhile5.

Module DntSem_SimpleWhile6.
Import Lang_SimpleWhile
       StateModel_SimpleWhile1
       DntSem_SimpleWhile5.


(** 上面定义中有三个分支的定义是相似，我们也可以统一定义。

    这里，_[Zfun: Z -> Z -> Z]_可以看做对整数加法（_[Z.add]_)、整数减法
    （_[Z.sub]_）与整数乘法（_[Z.mul]_）的抽象。*)

Definition arith_sem
             (Zfun: Z -> Z -> Z)
             (D1 D2: state -> option Z)
             (s: state): option Z :=
  match D1 s, D2 s with
  | Some i1, Some i2 => 
      if (Zfun i1 i2 <=? Int64.max_signed) &&
         (Zfun i1 i2 >=? Int64.min_signed)
      then Some (Zfun i1 i2)
      else None
  | _, _ => None
  end.

(** 例如，下面将_[Zfun]_取_[Z.add]_、_[int64fun]_取_[Int64.add]_代入：*)

Example arith_sem_add_fact: forall D1 D2 s,
  arith_sem Z.add D1 D2 s =
  match D1 s, D2 s with
  | Some i1, Some i2 => 
      if (i1 + i2 <=? Int64.max_signed) &&
         (i1 + i2 >=? Int64.min_signed)
      then Some (i1 + i2)
      else None
  | _, _ => None
  end.
Proof. intros. reflexivity. Qed.

(** 这样，_[eval_expr_int]_的定义就可以简化为：*)

Fixpoint eval_expr_int (e: expr_int):
  state -> option Z :=
  match e with
  | EConst n =>
      const_sem n
  | EVar X =>
      var_sem X
  | EAdd e1 e2 =>
      arith_sem Z.add
        (eval_expr_int e1) (eval_expr_int e2)
  | ESub e1 e2 =>
      arith_sem Z.sub
        (eval_expr_int e1) (eval_expr_int e2)
  | EMul e1 e2 =>
      arith_sem Z.mul
        (eval_expr_int e1) (eval_expr_int e2)
  end.


End DntSem_SimpleWhile6.

(** * 将运算越界定义为表达式求值错误 - 用二元关系 *)


(** 下面给出相应的Coq定义。首先定义64位整数之间在有符号64位整数范围内的运算关系。*)

Definition arith_compute1_nrm
             (Zfun: Z -> Z -> Z)
             (i1 i2 i: Z): Prop :=
  i = Zfun i1 i2 /\
  Int64.min_signed <= Zfun i1 i2 <= Int64.max_signed.

Definition arith_compute1_err
             (Zfun: Z -> Z -> Z)
             (i1 i2: Z): Prop :=
  Zfun i1 i2 < Int64.min_signed \/
  Zfun i1 i2 > Int64.max_signed.

Module DntSem_SimpleWhile7.
Import Lang_SimpleWhile
       StateModel_SimpleWhile1.

(** 接下去利用表达式与64位整数值间的二元关系表达『程序表达式求值出错』这一概念。
    具体而言，如果表达式_[e]_在程序状态_[s]_上能成果求值且求值结果为_[i]_，那么
    _[s]_与_[i]_这个有序对就在_[e]_的语义中。

    下面定义统一刻画了三种算术运算的语义。*)

Definition arith_sem1_nrm
             (Zfun: Z -> Z -> Z)
             (D1 D2: state -> Z -> Prop)
             (s: state)
             (i: Z): Prop :=
  exists i1 i2,
    D1 s i1 /\ D2 s i2 /\
    arith_compute1_nrm Zfun i1 i2 i.

Definition arith_sem1_err
             (Zfun: Z -> Z -> Z)
             (D1 D2: state -> Z -> Prop)
             (s: state): Prop :=
  exists i1 i2,
    D1 s i1 /\ D2 s i2 /\
    arith_compute1_err Zfun i1 i2.

(** 一个表达式的语义分为两部分：求值成功的情况与求值出错的情况。*)

Record denote: Type := {
  nrm: state -> Z -> Prop;
  err: state -> Prop;
}.

(** 下面_[Notation]_定义用于提供便捷易懂的表示方法，可以忽略其中的声明细节。*)

Notation "x '.(nrm)'" := (nrm x) (at level 1).
Notation "x '.(err)'" := (err x) (at level 1).


(** Coq中的_[Record]_与许多程序语言中的结构体是类似的。在上面定义中，每个表达式
    的语义_[D: denote]_都有两个域：_[D.(nrm)]_与_[D.(err)]_分别描述前面提到的两
    种情况。*)

Definition arith_sem1 Zfun (D1 D2: denote): denote :=
  {|
    nrm := arith_sem1_nrm Zfun D1.(nrm) D2.(nrm);
    err := D1.(err) ∪ D2.(err) ∪
           arith_sem1_err Zfun D1.(nrm) D2.(nrm);
  |}.

Definition const_sem (n: Z): denote :=
  {|
    nrm := fun s i =>
             i = n /\
             Int64.min_signed <= n <= Int64.max_signed;
    err := fun s =>
             n < Int64.min_signed \/
             n > Int64.max_signed;
  |}.

Definition var_sem (X: var_name): denote :=
  {|
    nrm := fun s i => i = s X;
    err := ∅;
  |}.

(** 最终，整数类型表达式的语义可以归结为下面递归定义。*)

Fixpoint eval_expr_int (e: expr_int): denote :=
  match e with
  | EConst n =>
      const_sem n
  | EVar X =>
      var_sem X
  | EAdd e1 e2 =>
      arith_sem1 Z.add (eval_expr_int e1) (eval_expr_int e2)
  | ESub e1 e2 =>
      arith_sem1 Z.sub (eval_expr_int e1) (eval_expr_int e2)
  | EMul e1 e2 =>
      arith_sem1 Z.mul (eval_expr_int e1) (eval_expr_int e2)
  end.


End DntSem_SimpleWhile7.

(** * 未初始化的变量 *)

(** 在C语言和很多实际编程语言中，都不允许或不建议在运算中或赋值中使用未初始化的
    变量的值。若要根据这一设定定义程序语义，那么就需要修改程序状态的定义。变量的
    值可能是一个整数，也可能是未初始化。*)

Inductive val: Type :=
| Vuninit: val
| Vint (i: Z): val.

Module DntSem_SimpleWhile8.
Import Lang_SimpleWhile.

(** 程序状态就变成变量名到_[val]_的函数。*)

Definition state: Type := var_name -> val.

(** 表达式的指称依旧包含原有的两部分。*)

Record denote: Type := {
  nrm: state -> Z -> Prop;
  err: state -> Prop;
}.

Notation "x '.(nrm)'" := (nrm x) (at level 1).
Notation "x '.(err)'" := (err x) (at level 1).

(** 下面这些Coq定义也不变。*)

Definition arith_sem1_nrm
             (Zfun: Z -> Z -> Z)
             (D1 D2: state -> Z -> Prop)
             (s: state)
             (i: Z): Prop :=
  exists i1 i2,
    D1 s i1 /\ D2 s i2 /\
    arith_compute1_nrm Zfun i1 i2 i.

Definition arith_sem1_err
             (Zfun: Z -> Z -> Z)
             (D1 D2: state -> Z -> Prop)
             (s: state): Prop :=
  exists i1 i2,
    D1 s i1 /\ D2 s i2 /\
    arith_compute1_err Zfun i1 i2.

Definition arith_sem1 Zfun (D1 D2: denote): denote :=
  {|
    nrm := arith_sem1_nrm Zfun D1.(nrm) D2.(nrm);
    err := D1.(err) ∪ D2.(err) ∪
           arith_sem1_err Zfun D1.(nrm) D2.(nrm);
  |}.

Definition const_sem (n: Z): denote :=
  {|
    nrm := fun s i =>
             i = n /\
             Int64.min_signed <= n <= Int64.max_signed;
    err := fun s =>
             n < Int64.min_signed \/
             n > Int64.max_signed;
  |}.

(** 唯有整数类型表达式中变量的语义需要重新定义。*)

Definition var_sem (X: var_name): denote :=
  {|
    nrm := fun s i => s X = Vint i;
    err := fun s => s X = Vuninit;
  |}.

(** 最终，整数类型表达式的语义还是可以写成同样的递归定义。*)

Fixpoint eval_expr_int (e: expr_int): denote :=
  match e with
  | EConst n =>
      const_sem n
  | EVar X =>
      var_sem X
  | EAdd e1 e2 =>
      arith_sem1 Z.add (eval_expr_int e1) (eval_expr_int e2)
  | ESub e1 e2 =>
      arith_sem1 Z.sub (eval_expr_int e1) (eval_expr_int e2)
  | EMul e1 e2 =>
      arith_sem1 Z.mul (eval_expr_int e1) (eval_expr_int e2)
  end.

End DntSem_SimpleWhile8.

(** * While语言的语义 *)

(** 有了上面这些准备工作，我们可以定义完整While语言的语义。完整While语言中支持更
    多运算符，要描述除法和取余运算符的行为，要定义不同于加减乘的运算关系。下面定
    义参考了C标准对于有符号整数除法和取余的规定。*)

Definition arith_compute2_nrm
             (Zfun: Z -> Z -> Z)
             (i1 i2 i: Z): Prop :=
  i = Zfun i1 i2 /\
  i2 <> 0 /\
  (i1 <> Int64.min_signed \/ i2 <> - 1).

Definition arith_compute2_err (i1 i2: Z): Prop :=
  i2 = 0 \/
  (i1 = Int64.min_signed /\ i2 = - 1).

(** 下面定义的比较运算关系利用了CompCert库定义的_[comparison]_类型和_[Int64.cmp]_
    函数。*)

Definition cmp_prop
             (c: comparison)
             (i1 i2: Z): Prop :=
  match c with
  | Clt => i1 < i2
  | Cle => i1 <= i2
  | Cgt => i1 > i2
  | Cge => i1 >= i2
  | Ceq => i1 = i2
  | Cne => i1 <> i2
  end.

Definition cmp_compute_nrm
             (c: comparison)
             (i1 i2 i: Z): Prop :=
  cmp_prop c i1 i2 /\ i = 1 \/
  ~ cmp_prop c i1 i2 /\ i = 0.

(** 一元运算的行为比较容易定义：*)

Definition neg_compute_nrm (i1 i: Z): Prop :=
  i = - i1 /\
  i1 <> Int64.min_signed.

Definition neg_compute_err (i1: Z): Prop :=
  i1 = Int64.min_signed.

Definition not_compute_nrm (i1 i: Z): Prop :=
  i1 <> 0 /\ i = 0 \/
  i1 = 0 /\ i = 1.

(** 最后，二元布尔运算的行为需要考虑短路求值的情况。下面定义中的缩写_[SC]_表示
    short circuit。*)

Definition SC_and_compute_nrm (i1 i: Z): Prop :=
  i1 = 0 /\ i = 0.

Definition SC_or_compute_nrm (i1 i: Z): Prop :=
  i1 <> 0 /\ i = 1.

Definition NonSC_and (i1: Z): Prop :=
  i1 <> 0.

Definition NonSC_or (i1: Z): Prop :=
  i1 = 0.

Definition NonSC_compute_nrm (i2 i: Z): Prop :=
  i2 = 0 /\ i = 0 \/
  i2 <> 0 /\ i = 1.


Module DntSem_While1.
Import Lang_While
       KleeneFix Sets_CPO.

(** 程序状态依旧是变量名到整数或未初始化值的函数，表达式的指称依旧包含成功求
    值情况与求值失败情况这两部分。*)

Definition state: Type := var_name -> val.

Module EDenote.

Record EDenote: Type := {
  nrm: state -> Z -> Prop;
  err: state -> Prop;
}.

End EDenote.

(** 以下为_[Notation]_声明，细节可以忽略。*)

Import EDenote.

Notation "x '.(nrm)'" := (EDenote.nrm x)
  (at level 1, only printing).

Notation "x '.(err)'" := (EDenote.err x)
  (at level 1, only printing).

Ltac any_nrm x := exact (EDenote.nrm x).

Ltac any_err x := exact (EDenote.err x).

Notation "x '.(nrm)'" := (ltac:(any_nrm x))
  (at level 1, only parsing).

Notation "x '.(err)'" := (ltac:(any_err x))
  (at level 1, only parsing).

(** 以下为语义定义。*)

Definition arith_sem1_nrm
             (Zfun: Z -> Z -> Z)
             (D1 D2: state -> Z -> Prop)
             (s: state)
             (i: Z): Prop :=
  exists i1 i2,
    D1 s i1 /\ D2 s i2 /\
    arith_compute1_nrm Zfun i1 i2 i.

Definition arith_sem1_err
             (Zfun: Z -> Z -> Z)
             (D1 D2: state -> Z -> Prop)
             (s: state): Prop :=
  exists i1 i2,
    D1 s i1 /\ D2 s i2 /\
    arith_compute1_err Zfun i1 i2.

Definition arith_sem1 Zfun (D1 D2: EDenote): EDenote :=
  {|
    nrm := arith_sem1_nrm Zfun D1.(nrm) D2.(nrm);
    err := D1.(err) ∪ D2.(err) ∪
           arith_sem1_err Zfun D1.(nrm) D2.(nrm);
  |}.

Definition arith_sem2_nrm
             (Zfun: Z -> Z -> Z)
             (D1 D2: state -> Z -> Prop)
             (s: state)
             (i: Z): Prop :=
  exists i1 i2,
    D1 s i1 /\ D2 s i2 /\
    arith_compute2_nrm Zfun i1 i2 i.

Definition arith_sem2_err
             (D1 D2: state -> Z -> Prop)
             (s: state): Prop :=
  exists i1 i2,
    D1 s i1 /\ D2 s i2 /\
    arith_compute2_err i1 i2.

Definition arith_sem2 int64fun (D1 D2: EDenote): EDenote :=
  {|
    nrm := arith_sem2_nrm int64fun D1.(nrm) D2.(nrm);
    err := D1.(err) ∪ D2.(err) ∪
           arith_sem2_err D1.(nrm) D2.(nrm);
  |}.

Definition cmp_sem_nrm
             (c: comparison)
             (D1 D2: state -> Z -> Prop)
             (s: state)
             (i: Z): Prop :=
  exists i1 i2,
    D1 s i1 /\ D2 s i2 /\ cmp_compute_nrm c i1 i2 i.

Definition cmp_sem c (D1 D2: EDenote): EDenote :=
  {|
    nrm := cmp_sem_nrm c D1.(nrm) D2.(nrm);
    err := D1.(err) ∪ D2.(err);
  |}.

Definition neg_sem_nrm
             (D1: state -> Z -> Prop)
             (s: state)
             (i: Z): Prop :=
  exists i1, D1 s i1 /\ neg_compute_nrm i1 i.

Definition neg_sem_err
             (D1: state -> Z -> Prop)
             (s: state): Prop :=
  exists i1, D1 s i1 /\ neg_compute_err i1.

Definition neg_sem (D1: EDenote): EDenote :=
  {|
    nrm := neg_sem_nrm D1.(nrm);
    err := D1.(err) ∪ neg_sem_err D1.(nrm);
  |}.

Definition not_sem_nrm
             (D1: state -> Z -> Prop)
             (s: state)
             (i: Z): Prop :=
  exists i1, D1 s i1 /\ not_compute_nrm i1 i.

Definition not_sem (D1: EDenote): EDenote :=
  {|
    nrm := not_sem_nrm D1.(nrm);
    err := D1.(err);
  |}.

(** 所有运算符的语义中，二元布尔运算由于涉及短路求值，其定义是最复杂的。*)

Definition and_sem_nrm
             (D1 D2: state -> Z -> Prop)
             (s: state)
             (i: Z): Prop :=
  exists i1,
    D1 s i1 /\
    (SC_and_compute_nrm i1 i \/
     NonSC_and i1 /\
     exists i2,
       D2 s i2 /\ NonSC_compute_nrm i2 i).

Definition and_sem_err
             (D1: state -> Z -> Prop)
             (D2: state -> Prop)
             (s: state): Prop :=
  exists i1,
    D1 s i1 /\ NonSC_and i1 /\ D2 s.

Definition and_sem (D1 D2: EDenote): EDenote :=
  {|
    nrm := and_sem_nrm D1.(nrm) D2.(nrm);
    err := D1.(err) ∪ and_sem_err D1.(nrm) D2.(err);
  |}.

Definition or_sem_nrm
             (D1 D2: state -> Z -> Prop)
             (s: state)
             (i: Z): Prop :=
  exists i1,
    D1 s i1 /\
    (SC_or_compute_nrm i1 i \/
     NonSC_or i1 /\
     exists i2,
       D2 s i2 /\ NonSC_compute_nrm i2 i).

Definition or_sem_err
             (D1: state -> Z -> Prop)
             (D2: state -> Prop)
             (s: state): Prop :=
  exists i1,
    D1 s i1 /\ NonSC_or i1 /\ D2 s.

Definition or_sem (D1 D2: EDenote): EDenote :=
  {|
    nrm := or_sem_nrm D1.(nrm) D2.(nrm);
    err := D1.(err) ∪ or_sem_err D1.(nrm) D2.(err);
  |}.

(** 最终我们可以将所有一元运算与二元运算的语义汇总起来：*)

Definition unop_sem (op: unop) (D: EDenote): EDenote :=
  match op with
  | ONeg => neg_sem D
  | ONot => not_sem D
  end.

Definition binop_sem (op: binop) (D1 D2: EDenote): EDenote :=
  match op with
  | OOr => or_sem D1 D2
  | OAnd => and_sem D1 D2
  | OLt => cmp_sem Clt D1 D2
  | OLe => cmp_sem Cle D1 D2
  | OGt => cmp_sem Cgt D1 D2
  | OGe => cmp_sem Cge D1 D2
  | OEq => cmp_sem Ceq D1 D2
  | ONe => cmp_sem Cne D1 D2
  | OPlus => arith_sem1 Z.add D1 D2
  | OMinus => arith_sem1 Z.sub D1 D2
  | OMul => arith_sem1 Z.mul D1 D2
  | ODiv => arith_sem2 Z.div D1 D2
  | OMod => arith_sem2 Z.rem D1 D2
  end.

(** 最后补上常数和变量的语义即可得到完整的表达式语义。*)

Definition const_sem (n: Z): EDenote :=
  {|
    nrm := fun s i =>
             i = n /\
             Int64.min_signed <= n <= Int64.max_signed;
    err := fun s =>
             n < Int64.min_signed \/
             n > Int64.max_signed;
  |}.

Definition var_sem (X: var_name): EDenote :=
  {|
    nrm := fun s i => s X = Vint i;
    err := fun s => s X = Vuninit;
  |}.

Fixpoint eval_expr (e: expr): EDenote :=
  match e with
  | EConst n =>
      const_sem n
  | EVar X =>
      var_sem X
  | EBinop op e1 e2 =>
      binop_sem op (eval_expr e1) (eval_expr e2)
  | EUnop op e1 =>
      unop_sem op (eval_expr e1)
  end.

(** 基于表达式的指称语义，可以证明一些简单性质。*)

Lemma const_plus_const_nrm:
  forall (n m: Z) (s: state) (i: Z),
    (eval_expr (EBinop OPlus (EConst n) (EConst m))).(nrm) s i ->
    (eval_expr (EConst (n + m))).(nrm) s i.
Proof.
  intros.
  simpl in H; unfold arith_sem1_nrm, arith_compute1_nrm in H.
  simpl.
  destruct H as [i1 [i2 [? [? [? ?] ] ] ] ].
  destruct H, H0.
  rewrite H1.
  rewrite <- H in H3.
  rewrite <- H0 in H4.
  lia.
Qed.

(** 下面定义程序语句的语义。程序语句的语义包含三种情况：正常运行终止、运行出错以
    及安全运行但不终止。*)

Module CDenote.

Record CDenote: Type := {
  nrm: state -> state -> Prop;
  err: state -> Prop;
  inf: state -> Prop
}.

End CDenote.

(** 以下为_[Notation]_声明，细节可以忽略。*)

Import CDenote.

Notation "x '.(nrm)'" := (CDenote.nrm x)
  (at level 1, only printing).

Notation "x '.(err)'" := (CDenote.err x)
  (at level 1, only printing).

Notation "x '.(inf)'" := (CDenote.inf x)
  (at level 1).

Ltac any_nrm x ::=
  match type of x with
  | EDenote => exact (EDenote.nrm x)
  | CDenote => exact (CDenote.nrm x)
  end.

Ltac any_err x ::=
  match type of x with
  | EDenote => exact (EDenote.err x)
  | CDenote => exact (CDenote.err x)
  end.

(** 空语句的语义：*)

Definition skip_sem: CDenote :=
  {|
    nrm := Rels.id;
    err := ∅;
    inf := ∅;
  |}.

(** 赋值语句的语义：*)

Definition asgn_sem
             (X: var_name)
             (D: EDenote): CDenote :=
  {|
    nrm := fun s1 s2 =>
      exists i,
        D.(nrm) s1 i /\ s2 X = Vint i /\
        (forall Y, X <> Y -> s2 Y = s1 Y);
    err := D.(err);
    inf := ∅;
  |}.

(** 顺序执行语句的语义：*)

Definition seq_sem (D1 D2: CDenote): CDenote :=
  {|
    nrm := D1.(nrm) ∘ D2.(nrm);
    err := D1.(err) ∪ (D1.(nrm) ∘ D2.(err));
    inf := D1.(inf) ∪ (D1.(nrm) ∘ D2.(inf));
  |}.

(** 条件分支语句的语义：*)

Definition test_true (D: EDenote):
  state -> state -> Prop :=
  Rels.test
    (fun s =>
       exists i, D.(nrm) s i /\ i <> 0).

Definition test_false (D: EDenote):
  state -> state -> Prop :=
  Rels.test (fun s => D.(nrm) s 0).

Definition if_sem
             (D0: EDenote)
             (D1 D2: CDenote): CDenote :=
  {|
    nrm := (test_true D0 ∘ D1.(nrm)) ∪
           (test_false D0 ∘ D2.(nrm));
    err := D0.(err) ∪
           (test_true D0 ∘ D1.(err)) ∪
           (test_false D0 ∘ D2.(err));
    inf := (test_true D0 ∘ D1.(inf)) ∪
           (test_false D0 ∘ D2.(inf))
  |}.




(** While循环语句不终止的情况分为两种：每次执行循环体程序都正常运行终止但是
    由于一直满足循环条件将执行无穷多次循环体；某次执行循环体时，执行循环体的过程
    本身不终止。


    下面定义的_[is_inf]_描述了以下关于程序状态集合_[X]_的性质：从集
    合_[X]_中的任意一个状态出发，计算循环条件的结果都为真（也不会计算出错），进
    入循环体执行后，要么正常运行终止并且终止于另一个（可以是同一个）_[X]_集合中
    的状态上，要么循环体运行不终止。*)

Definition is_inf
             (D0: EDenote)
             (D1: CDenote)
             (X: state -> Prop): Prop :=
  X ⊆ test_true D0 ∘ ((D1.(nrm) ∘ X) ∪ D1.(inf)).

(** 这样一来，循环不终止的情况可以定义为所有满足_[is_inf]_性质的集合的并集。*)

Definition while_sem
             (D0: EDenote)
             (D1: CDenote): CDenote :=
  {|
    nrm := Kleene_LFix
             (fun X =>
                test_true D0 ∘ D1.(nrm) ∘ X ∪
                test_false D0);
    err := Kleene_LFix
             (fun X =>
                test_true D0 ∘ D1.(nrm) ∘ X ∪
                test_true D0 ∘ D1.(err) ∪ D0.(err));
    inf := ⨆ (is_inf D0 D1);
  |}.

(** 程序语句的语义可以最后表示成下面递归函数。*)

Fixpoint eval_com (c: com): CDenote :=
  match c with
  | CSkip =>
      skip_sem
  | CAsgn X e =>
      asgn_sem X (eval_expr e)
  | CSeq c1 c2 =>
      seq_sem (eval_com c1) (eval_com c2)
  | CIf e c1 c2 =>
      if_sem (eval_expr e) (eval_com c1) (eval_com c2)
  | CWhile e c1 =>
      while_sem (eval_expr e) (eval_com c1)
  end.



End DntSem_While1.

