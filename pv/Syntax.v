Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Psatz.
Local Open Scope string.
Local Open Scope Z.

(** * 一个极简的指令式程序语言：SimpleWhile *)

(** 在Coq中，我们就用字符串表示变量名，*)

Definition var_name: Type := string.

Declare Custom Entry prog_lang_entry.

Module Lang_SimpleWhile.

(** 并且使用Coq归纳类型定义表达式和语句的语法树。*)

Inductive expr_int : Type :=
  | EConst (n: Z): expr_int
  | EVar (x: var_name): expr_int
  | EAdd (e1 e2: expr_int): expr_int
  | ESub (e1 e2: expr_int): expr_int
  | EMul (e1 e2: expr_int): expr_int.

Inductive expr_bool: Type :=
  | ETrue: expr_bool
  | EFalse: expr_bool
  | ELt (e1 e2: expr_int): expr_bool
  | EAnd (e1 e2: expr_bool): expr_bool
  | ENot (e: expr_bool): expr_bool.

Inductive com : Type :=
  | CSkip: com
  | CAsgn (x: var_name) (e: expr_int): com
  | CSeq (c1 c2: com): com
  | CIf (e: expr_bool) (c1 c2: com): com
  | CWhile (e: expr_bool) (c: com): com.

(** 在Coq中，可以利用_[Notation]_使得这些表达式和程序语句更加易读。*)

Definition EVar': string -> expr_int := EVar.
Coercion EConst: Z >-> expr_int.
Coercion EVar: var_name >-> expr_int.
Coercion EVar': string >-> expr_int.
Notation "[[ e ]]" := e
  (at level 0, e custom prog_lang_entry at level 99).
Notation "( x )" := x
  (in custom prog_lang_entry, x custom prog_lang_entry at level 99).
Notation "x" := x
  (in custom prog_lang_entry at level 0, x constr at level 0).
Notation "f x" := (f x)
  (in custom prog_lang_entry at level 1, only parsing,
   f custom prog_lang_entry,
   x custom prog_lang_entry at level 0).
Notation "x * y" := (EMul x y)
  (in custom prog_lang_entry at level 11, left associativity).
Notation "x + y" := (EAdd x y)
  (in custom prog_lang_entry at level 12, left associativity).
Notation "x - y" := (ESub x y)
  (in custom prog_lang_entry at level 12, left associativity).
Notation "x < y" := (ELt x y)
  (in custom prog_lang_entry at level 13, no associativity).
Notation "x && y" := (EAnd x y)
  (in custom prog_lang_entry at level 14, left associativity).
Notation "! x" := (ENot x)
  (in custom prog_lang_entry at level 10).
Notation "x = e" := (CAsgn x e)
  (in custom prog_lang_entry at level 18, no associativity).
Notation "c1 ; c2" := (CSeq c1 c2)
  (in custom prog_lang_entry at level 20, right associativity).
Notation "'skip'" := (CSkip)
  (in custom prog_lang_entry at level 10).
Notation "'if' e 'then' '{' c1 '}' 'else' '{' c2 '}'" := (CIf e c1 c2)
  (in custom prog_lang_entry at level 19,
   e custom prog_lang_entry at level 5,
   c1 custom prog_lang_entry at level 99,
   c2 custom prog_lang_entry at level 99,
   format  "'if'  e  'then'  '{'  c1  '}'  'else'  '{'  c2  '}'").
Notation "'while' e 'do' '{' c1 '}'" := (CWhile e c1)
  (in custom prog_lang_entry at level 19,
   e custom prog_lang_entry at level 5,
   c1 custom prog_lang_entry at level 99).

(** 使用_[Notation]_的效果如下：*)

Check [[1 + "x"]].
Check [["x" * ("a" + "b" + 1)]].
Check [[1 + "x" < "x"]].
Check [["x" < 0 && 0 < "y"]].
Check [["x" = "x" + 1]].
Check [[while (0 < "x") do { "x" = "x" - 1}]].


End Lang_SimpleWhile.

(** * 更多的程序语言：While语言 *)

(** 在许多以C语言为代表的常用程序语言中，往往不区分整数类型表达式与布尔类型表达
    式，同时表达式中也包含更多运算符。例如，我们可以如下规定一种程序语言的语法。

    下面依次在Coq中定义该语言中的二元运算符和一元运算符。*)

Inductive binop : Type :=
  | OOr | OAnd
  | OLt | OLe | OGt | OGe | OEq | ONe
  | OPlus | OMinus | OMul | ODiv | OMod.

Inductive unop : Type :=
  | ONot | ONeg.

Module Lang_While.

(** 然后再定义表达式的抽象语法树。*)

Inductive expr : Type :=
  | EConst (n: Z): expr
  | EVar (x: var_name): expr
  | EBinop (op: binop) (e1 e2: expr): expr
  | EUnop (op: unop) (e: expr): expr.

(** 最后是程序语句的抽象语法树。*)

Inductive com : Type :=
  | CSkip: com
  | CAsgn (x: var_name) (e: expr): com
  | CSeq (c1 c2: com): com
  | CIf (e: expr) (c1 c2: com): com
  | CWhile (e: expr) (c: com): com.


End Lang_While.

(** * 更多的程序语言：WhileDeref *)

Module Lang_WhileDeref.

(** 下面在While程序语言中增加取地址上的值_[EDeref]_操作。*)

Inductive expr : Type :=
  | EConst (n: Z): expr
  | EVar (x: var_name): expr
  | EBinop (op: binop) (e1 e2: expr): expr
  | EUnop (op: unop) (e: expr): expr
  | EDeref (e: expr): expr.

(** 相应的，赋值语句也可以分为两种情况。*)

Inductive com : Type :=
  | CSkip: com
  | CAsgnVar (x: var_name) (e: expr): com
  | CAsgnDeref (e1 e2: expr): com
  | CSeq (c1 c2: com): com
  | CIf (e: expr) (c1 c2: com): com
  | CWhile (e: expr) (c: com): com.

End Lang_WhileDeref.

(** * 更多的程序语言：WhileD *)

Module Lang_WhileD.

(** 在大多数程序语言中，会同时支持或不支持取地址_[EAddrOf]_与取地址上的值
    _[EDeref]_两类操作，我们也可以在WhileDeref语言中再加入取地址操作。*)

Inductive expr : Type :=
  | EConst (n: Z): expr
  | EVar (x: var_name): expr
  | EBinop (op: binop) (e1 e2: expr): expr
  | EUnop (op: unop) (e: expr): expr
  | EDeref (e: expr): expr
  | EAddrOf (e: expr): expr.

(** 程序语句的语法树不变。*)

Inductive com : Type :=
  | CSkip: com
  | CAsgnVar (x: var_name) (e: expr): com
  | CAsgnDeref (e1 e2: expr): com
  | CSeq (c1 c2: com): com
  | CIf (e: expr) (c1 c2: com): com
  | CWhile (e: expr) (c: com): com.

End Lang_WhileD.

(** * 更多的程序语言：WhileDC *)

Module Lang_WhileDC.

(** 下面在程序语句中增加控制流语句continue与break，并增加多种循环语句。*)

Inductive expr : Type :=
  | EConst (n: Z): expr
  | EVar (x: var_name): expr
  | EBinop (op: binop) (e1 e2: expr): expr
  | EUnop (op: unop) (e: expr): expr
  | EDeref (e: expr): expr
  | EAddrOf (e: expr): expr.

Inductive com : Type :=
  | CSkip: com
  | CAsgnVar (x: var_name) (e: expr): com
  | CAsgnDeref (e1 e2: expr): com
  | CSeq (c1 c2: com): com
  | CIf (e: expr) (c1 c2: com): com
  | CWhile (e: expr) (c: com): com
  | CFor (c1: com) (e: expr) (c2: com) (c3: com): com
  | CDoWhile (c: com) (e: expr): com
  | CContinue: com
  | CBreak: com.

End Lang_WhileDC.

(** * 简单语法变换与证明 *)

Module LangTrans.
Import Lang_SimpleWhile.


(************)
(** 习题：  *)
(************)

(** 下面的递归函数_[remove_skip]_定义了在程序语句中删除多余空语句的操作。*)

Fixpoint remove_skip (c: com): com :=
  match c with
  | CSeq c1 c2 =>
      match remove_skip c1, remove_skip c2 with
      | CSkip, _ => remove_skip c2
      | _, CSkip => remove_skip c1
      | _, _ => CSeq (remove_skip c1) (remove_skip c2)
      end
  | CIf e c1 c2 =>
      CIf e (remove_skip c1) (remove_skip c2)
  | CWhile e c1 =>
      CWhile e (remove_skip c1)
  | _ =>
      c
  end.

(** 下面请证明：_[remove_skip]_之后，确实不再有多余的空语句了。所谓没有空语句，
    是指不出现_[c; SKIP]_或_[SKIP; c]_这样的语句。首先定义：局部不存在多余的空语
    句。*)

Definition not_sequencing_skip (c: com): Prop :=
  match c with
  | CSeq CSkip _ => False
  | CSeq _ CSkip => False
  | _ => True
  end.

(** 其次定义语法树的所有子树中都不存在多余的空语句。*)

Fixpoint no_sequenced_skip (c: com): Prop :=
  match c with
  | CSeq c1 c2 =>
      not_sequencing_skip c /\
      no_sequenced_skip c1 /\ no_sequenced_skip c2
  | CIf e c1 c2 =>
      no_sequenced_skip c1 /\ no_sequenced_skip c2
  | CWhile e c1 =>
      no_sequenced_skip c1
  | _ =>
      True
  end.

(** 下面是需要证明的结论。*)

Theorem remove_skip_no_sequenced_skip: forall c,
  no_sequenced_skip (remove_skip c).
Admitted. (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)


End LangTrans.


