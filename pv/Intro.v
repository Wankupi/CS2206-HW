Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Psatz.
Local Open Scope Z.

(** * Coq中的函数、谓词与证明 *)

(** 函数是一类重要的数学对象。例如，“加一”这个函数往往可以写作：f(x) = x + 1。
    在Coq中，我们可以用以下代码将其定义为_[plus_one]_函数。*)

Definition plus_one (x: Z): Z := x + 1.

Example One_plus_one: plus_one 1 = 2.
Proof. unfold plus_one. lia. Qed.

Example One_plus_one_plus_one: plus_one (plus_one 1) = 3.
Proof. unfold plus_one. lia. Qed.

(** 下面是更多函数的例子。我们可以采用类似于定义“加一”的方法定义“平方”函数。*)

Definition square (x: Z): Z := x * x.

Example square_5: square 5 = 25.
Proof. unfold square. lia. Qed.

(** Coq中也可以定义多元函数。*)

Definition smul (x y: Z): Z := x * y + x + y.

Example smul_ex1: smul 1 1 = 3.
Proof. unfold smul. lia. Qed.

Example smul_ex2: smul 2 3 = 11.
Proof. unfold smul. lia. Qed.

(** 下面Coq代码定义了“非负”这一概念。在Coq中，可以通过定义类型为_[Prop]_的函数来定义
    谓词。以下面定义为例，对于每个整数_[x]_，_[:=]_符号右侧表达式_[x >= 0]_是真还是假
    决定了_[x]_是否满足性质_[nonneg]_（即，非负）。 *)

Definition nonneg (x: Z): Prop := x >= 0.

Fact nonneg_plus_one: forall x: Z,
  nonneg x -> nonneg (plus_one x).
Proof. unfold nonneg, plus_one. lia. Qed.

Fact nonneg_square: forall x: Z,
  nonneg (square x).
Proof. unfold nonneg, square. nia. Qed.

(************)
(** 习题：  *)
(************)

(** 请在Coq中证明下面结论。*)

Fact nonneg_smul: forall x y: Z,
  nonneg x -> nonneg y -> nonneg (smul x y).
Admitted. (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)


