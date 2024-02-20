Require Import Coq.Setoids.Setoid.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Psatz.
Require Import PV.Intro.
Local Open Scope Z.

(** * 整数算数运算与大小比较 *)


(** 算术与数量之间的大小关系是日常生活中最常见的数学概念。我们可以用数描述物体的数量、
    几何图形的长度与面积、人的年龄等等。作为Coq验证工具的入门篇，这一章将介绍如何使用
    Coq表达一些简单的数量关系，并证明一些简单的性质。

    大约在1500年前，《孙子算经》一书中记载了这样一个有趣的问题：今有雉兔同笼，上有三十 
    五头，下有九十四足，问雉兔各几何？这就是著名的鸡兔同笼问题。我们都知道，如果用C表示
    鸡（Chicken）的数量，用R表示兔（Rabbit）的数量，那么这一问题中的数量关系就可以表示
    为：

        _[C + R = 35]_ 

        _[2 * C + 4 * R = 94]_ 

    进而可以求解得知_[C = 23]_（也可以求解得到_[R = 12]_）。这一推理过程可以在Coq中表
    示成为下面命题。*)

Fact chickens_and_rabbits: forall C R: Z,
  C + R = 35 ->
  2 * C + 4 * R = 94 ->
  C = 23.

(** 字面意思上，这个命题说的是：对于任意整数_[C]_与_[R]_，如果_[C + R = 35]_并且
    _[2 * C + 4 * R = 94]_，那么_[C = 23]_。其中，_[forall]_与_[->]_是Coq中描述数
    学命题的常用符号。

    在Fact指令之后，我们可以在Coq中证明这个数学命题成立。如果要用中学数学知识完成这一
    证明，恐怕要使用加减消元法、代入消元法等代数技巧。Coq并不需要我们掌握这些数学技巧，
    Coq系统可以自动完成整数线性运算性质（linear integer arithmetic，简称lia）的证
    明，_[chickens_and_rabbits]_这一命题在Coq中的证明只需一行：*)

Proof. lia. Qed.

(** 在这一行代码中，Proof和Qed表示一段证明的开头与结尾，在它们之间的_[lia]_指令是证明
    脚本。

    一般而言，编写Coq证明的过程是交互式的——“交互式”的意思是：在编写证明代码的同时，我
    们可以在Coq定理证明环境中运行证明脚本，获得反馈，让定理证明系统告诉我们“已经证明了
    哪些结论”、“还需要证明哪些结论”等等，并以此为依据编写后续的证明代码。安装VSCoq插
    件的VSCode编辑器、安装proof-general插件的emacs编辑器以及CoqIDE都是成熟易用的Coq
    定理证明环境。
    
    以上面的证明为例，执行_[lia]_指令前，证明窗口显示了当前还需证明的性质（亦称为证明
    目标，proof goal）：
   
------------------------------------------
(1/1)
forall C R : Z,
C + R = 35 -> 2 * C + 4 * R = 94 -> C = 23

    这里横线上方的是目前可以使用的前提，横线下方的是目前要证明的结论，目前，前提集合为
    空。横线下方的(1/1)表示总共还有1个证明目标需要证明，当前显示的是其中的第一个证明目
    标。利用证明脚本证明的过程中，每一条证明指令可以将一个证明目标规约为0个，1个或者更
    多的证明目标。执行_[lia]_指令之后，证明窗口显示：Proof finished。表示证明已经完
    成。一般情况下，Coq证明往往是不能只靠一条证明指令完成证明的。

    Coq证明指令_[lia]_除了能够证明关于线性运算的等式，也可以证明关于线性运算的不等式。
    下面这个例子选自熊斌教授所著《奥数教程》的小学部分：幼儿园的小朋友去春游，有男孩、
    女孩、男老师与女老师共16人，已知小朋友比老师人数多，但是女老师比女孩人数多，女孩又
    比男孩人数多，男孩比男老师人数多，请证明幼儿园只有一位男老师。*)

Fact teachers_and_children: forall MT FT MC FC: Z,
  MT > 0 ->
  FT > 0 ->
  MC > 0 ->
  FC > 0 ->
  MT + FT + MC + FC = 16 ->
  MC + FC > MT + FT ->
  FT > FC ->
  FC > MC ->
  MC > MT ->
  MT = 1.
Proof. lia. Qed.

(************)
(** 习题：  *)
(************)

(** 请在Coq中描述下面结论并证明：如果今年甲的年龄是乙5倍，并且5年后甲的年龄是乙的3倍，
    那么今年甲的年龄是25岁。*)


(** 除了线性性质之外，Coq中还可以证明的一些更复杂的性质。例如下面就可以证明，任意两个整
    数的平方和总是大于它们的乘积。证明中使用的指令_[nia]_表示的是非线性整数运算
    （nonlinear integer arithmetic）求解。*)

Fact sum_of_sqr1: forall x y: Z,
  x * x + y * y >= x * y.
Proof. nia. Qed.

(** 不过，_[nia]_与_[lia]_不同，后者能够保证关于线性运算的真命题总能被自动证明（规模过
    大的除外），但是有不少非线性的算数运算性质是_[nia]_无法自动求解的。例如，下面例子说明，一些很简单的命题_[nia]_都无法完成自动验证。*)

Fact sum_of_sqr2: forall x y: Z,
  x * x + y * y >= 2 * x * y.
Proof. Fail nia. Abort.

(** 这时，我们就需要编写证明脚本，给出中间证明步骤。证明过程中，可以使用Coq标准库中的结
    论，也可以使用我们自己实现证明的结论。例如，Coq标准库中，_[sqr_pos]_定理证明了任意
    一个整数_[x]_的平方都是非负数，即：

       _[sqr_pos: forall x: Z, x * x >= 0]_ 

    我们可以借助这一性质完成上面_[sum_of_sqr2]_的证明。*)

Fact sum_of_sqr2: forall x y: Z,
  x * x + y * y >= 2 * x * y.
Proof.
  intros.
  pose proof sqr_pos (x - y).
  nia.
Qed.

(** 这段证明有三个证明步骤。证明指令_[intros]_将待证明结论中的逻辑结构“对于任意整数x与
    y”移除，并在前提中假如“x与y是整数”这两条假设。第二条指令_[pose proof]_表示对x-y使
    用标准库中的定理_[sqr_pos]_。从Coq定理证明界面中可以看到，使用该定理得到的命题会被
    添加到证明目标的前提中去，Coq系统将这个新命题自动命名为H（表示Hypothesis）。最后，
    _[nia]_可以自动根据当前证明目标中的前提证明结论。

    下面证明演示了如何使用我们刚刚证明的性质_[sum_of_sqr1]_。*)

Example quad_ex1: forall x y: Z,
  x * x + 2 * x * y + y * y + x + y + 1 >= 0.
Proof.
  intros.
  pose proof sum_of_sqr1 (x + y) (-1).
  nia.
Qed.

(** 下面这个例子说的是：如果_[x < y]_，那么_[x * x + x * y + y * y]_一定大于零。*)

Fact sum_of_sqr_lt: forall x y: Z,
  x < y ->
  x * x + x * y + y * y > 0.

(** 在我们学习数学知识时，我们知道_[x * x + x * y + y * y]_是恒为非负的，而且只有在
    _[x]_与_[y]_都为0的时候，这个式子才能取到0，因此，在_[x < y]_的前提下，这个式子恒
    为正。在进一步学习Coq定理证明器的使用之后，我们完全可以在Coq中表达上述证明过程。不
    过，如果仅仅使用目前所介绍的几条Coq证明指令，其实也是可以完成上面命题的Coq证明的。
    不过，此处就需要换一条证明思路。

    我们可以利用下面两式相等证明：

        _[4 * (x * x + x * y + y * y)]_ 

        _[3 * (x + y) * (x + y) + (x - y) * (x - y)]_ 

    于是，在_[x < y]_的假设下，等式右边的两个平方式一个恒为非负，一个恒为正。因此，等
    式的左边也恒为正。将这一思路写成Coq证明如下：*)

Proof.
  intros.
  pose proof sqr_pos (x + y).
  nia.
Qed.

(** 可以看到，在_[x < y]_的前提下，Coq的_[nia]_指令可以自动推断得知_[(x - y)]_的平方
    恒为正。不过，我们仍然需要手动提示Coq，_[(x + y)]_的平方恒为非负。*)

(************)
(** 习题：  *)
(************)

(** 请证明下面结论。提示：可以利用以下代数变换完成证明 

        _[4 * (x * x + 3 * x + 4) = (2 * x + 3) * (2 * x + 3) + 7]_ *)

Example quad_ex2: forall x: Z,
  x * x + 3 * x + 4 > 0.
Proof.
Admitted. (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)


(** * 高阶函数 *)


(** 在Coq中，函数的参数也可以是函数。下面定义的_[shift_left1]_是一个二元函数，它的第
    一个参数_[f: Z -> Z]_是一个从整数到整数的一元函数，第二个参数_[x: Z]_是一个整数，这个函数依据两个参数计算出的函数值是_[f (x + 1)]_。*)

Definition shift_left1 (f: Z -> Z) (x: Z): Z :=
  f (x + 1).

(** 下面是两个_[shift_left1]_的例子。*)

Example shift_left1_square: forall x,
  shift_left1 square x = (x + 1) * (x + 1).
Proof. unfold shift_left1, square. lia. Qed.

Example shift_left1_plus_one: forall x,
  shift_left1 plus_one x = x + 2.
Proof. unfold shift_left1, plus_one. lia. Qed.

(** 从这两个例子可以看出，_[shift_left1]_作为一个二元函数，也可以被看作一个一元函数，
    这个一元函数的参数是一个整数到整数的函数，这个一元函数的计算结果也是一个整数到整数
    的函数。例如，_[shift_left1 square]_的计算结果在数学上可以写作函数 
        f(x) = (x + 1) * (x + 1)。
    更一般的，_[shift_left1 f]_可以看作将函数_[f]_在坐标平面中的图像左移一个单位的结
    果。这样的观点也可以在Coq中更直白地表达出来，下面定义的_[shift_left1']_实际上是与
    _[shift_left1]_完全相同的函数，但是这一定义在形式上是一个一元函数。*)

Definition shift_left1' (f: Z -> Z): Z -> Z :=
  fun x => f (x + 1).

(** 与_[shift_left1]_类似，我们还可以定义将一元函数图像向上移动一个单位的结果。*)

Definition shift_up1 (f: Z -> Z) (x: Z): Z :=
  f x + 1.

Example shift_up1_square: forall x,
  shift_up1 square x = x * x + 1.
Proof. unfold shift_up1, square. lia. Qed.

Example shift_up1_plus_one: forall x,
  shift_up1 plus_one x = x + 2.
Proof. unfold shift_up1, plus_one. lia. Qed.

(** 像_[shift_left1]_和_[shift_up1]_这样以函数为参数的函数称为高阶函数。高阶函数也可
    以是多元函数。例如下面的_[func_plus]_与_[func_mult]_定义了函数的加法和乘法。*)

Definition func_plus (f g: Z -> Z): Z -> Z :=
  fun x => f x + g x.

Definition func_mult (f g: Z -> Z): Z -> Z :=
  fun x => f x * g x.

(** 下面证明几条关于高阶函数的简单性质。首先我们证明，对于任意函数_[f]_，对它先左移再上
    移和先上移再左移的结果是一样的。*)

Lemma shift_up1_shift_left1_comm: forall f,
  shift_up1 (shift_left1 f) = shift_left1 (shift_up1 f).
Proof.
  intros.
  unfold shift_left1, shift_up1.
  reflexivity.
Qed.

(** 在上面证明中，在展开“左移”与“上移”的定义后，需要证明的结论是：

        _[(fun x : Z => f (x + 1) + 1) = (fun x : Z => f (x + 1) + 1)]_ 

    这个等式两边的表达式字面上完全相同，因此该结论显然成立。证明指令_[reflexivity]_
    表示利用“自反性”完成证明，所谓等式的自反性就是“任意一个数学对象都等于它自身”。下面
    我们还可以证明，将_[f]_与_[g]_两个函数先相加再图像左移，与先图像左移再函数相加得到
    的结果是一样的。*)

Lemma shift_left1_func_plus: forall f g,
  shift_left1 (func_plus f g) =
  func_plus (shift_left1 f) (shift_left1 g).
Proof.
  intros.
  unfold shift_left1, func_plus.
  reflexivity.
Qed.

(************)
(** 习题：  *)
(************)

(** 请证明下面命题。*)

Fact shift_up1_eq: forall f,
  shift_up1 f = func_plus f (fun x => 1).
Proof.
Admitted. (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)


(** * 高阶谓词 *)


(** 类似于高阶函数，如果一个谓词的参数中有函数（或谓词），那它就是一个高阶谓词。其实，
    许多常见数学概念都是高阶谓词。例如，函数的单调性就是一个高阶谓词。*)

Definition mono (f: Z -> Z): Prop :=
  forall n m, n <= m -> f n <= f m.

(** 有许多函数都是单调的。前面我们定义的_[plus_one]_函数就是个单调函数。*)

Example plus_one_mono: mono plus_one.
Proof.
  unfold mono, plus_one.
  intros.
  lia.
Qed.

(** 我们还可以定义整数函数的复合，然后证明复合函数能保持单调性。*)

Definition Zcomp (f g: Z -> Z): Z -> Z :=
  fun x => f (g x).

Lemma mono_compose: forall f g,
  mono f ->
  mono g ->
  mono (Zcomp f g).
Proof.
  unfold mono, Zcomp.
  intros f g Hf Hg n m Hnm.
  pose proof Hg n m Hnm as Hgnm.
  pose proof Hf (g n) (g m) Hgnm.
  lia.
Qed.

(************)
(** 习题：  *)
(************)

(** 请证明常值函数都是单调的。*)

Lemma const_mono: forall a: Z,
  mono (fun x => a).
Proof.
Admitted. (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)

(************)
(** 习题：  *)
(************)

(** 请证明立方函数是单调的。*)

Example cube_mono: mono (fun x => x * x * x).
Proof.
Admitted. (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)

(************)
(** 习题：  *)
(************)

(** 请证明函数加法能保持单调性。*)

Lemma mono_func_plus: forall f g,
  mono f ->
  mono g ->
  mono (func_plus f g).
Proof.
Admitted. (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)

(** “结合律”也是一个常用的数学概念。如下面定义所示，一个二元函数_[f]_具有结合律，当且
    仅当它满足_[f x (f y z) = f (f x y) z]_。*)

Definition assoc (f: Z -> Z -> Z): Prop :=
  forall x y z,
    f x (f y z) = f (f x y) z.

(** 我们熟知整数的加法于乘法都满足结合律。下面是加法结合律与乘法结合律的Coq证明。*)

Lemma plus_assoc: assoc (fun x y => x + y).
Proof. unfold assoc. lia. Qed.

Lemma mult_assoc: assoc (fun x y => x * y).
Proof. unfold assoc. nia. Qed.

(************)
(** 习题：  *)
(************)

(** 请证明，我们先前定义的_[smul]_函数也符合结合律。*)
Lemma smul_assoc: assoc smul.
Proof.
Admitted. (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)

(** 上面例子中的两个高阶谓词都是以函数为参数的高阶谓词，下面两个例子都是以谓词为参数的
    高阶谓词，甚至它们的参数本身也是高阶谓词。它们分别说的是，函数的性质_[P]_能被图像上
    移变换（_[shift_up1]_）保持以及能被图像左移变换（_[shift_left1]_）保持。*)

Definition preserved_by_shifting_up (P: (Z -> Z) -> Prop): Prop :=
  forall f, P f -> P (shift_up1 f).

Definition preserved_by_shifting_left (P: (Z -> Z) -> Prop): Prop :=
  forall f, P f -> P (shift_left1 f).

(** 不难发现，单调性就能被这两种图像平移变换保持。*)

Lemma mono_pu: preserved_by_shifting_up mono.
Proof.
  unfold preserved_by_shifting_up, mono, shift_up1.
  intros.
  pose proof H _ _ H0.
  lia.
Qed.

Lemma mono_pl: preserved_by_shifting_left mono.
Proof.
  unfold preserved_by_shifting_left, mono, shift_left1.
  intros.
  pose proof H (n + 1) (m + 1) ltac:(lia).
  lia.
Qed.

(************)
(** 习题：  *)
(************)

(** 请证明“恒为非负”这一性质（见下面Coq定义）也被图像上移与图像左移变换保持。*)

Definition univ_nonneg {A: Type} (f: A -> Z): Prop :=
  forall a: A, f a >= 0.

Lemma univ_nonneg_pu: preserved_by_shifting_up univ_nonneg.
Admitted. (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)

Lemma univ_nonneg_pl: preserved_by_shifting_left univ_nonneg.
Admitted. (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)

(** 在数学证明中，我们往往会先证明一些具有一般性的定理或引理，并后续的证明中使用这些定
    理或引理。站在编写Coq证明脚本的角度看，使用先前已经证明的定理也可以看作对定理本身证
    明代码的复用。反过来，如果一系列数学对象具有相似的性质，这些性质的证明方式上也是相似的，那么我们在Coq编码时就可以利用函数与谓词（特别是高阶函数和高阶谓词）概括性地描述这些数学对象之间的关系，并给出统一的证明。例如，当我们要证明

        _[fun x => x * x * x - 3 * x * x + 3 * x]_ 

    具备单调性时，可以基于下面代数变换并多次使用复合函数保持单调性这一引理完成证明。

        _[x * x * x - 3 * x * x + 3 * x = (x - 1)^3 + 1]_ *)

Example mono_ex1: mono (fun x => x * x * x - 3 * x * x + 3 * x).

(** 具体而言，下面在Coq中证明这一单调性性质的时候，将分两步进行。第一步先证明
    _[fun x => x - 1]_、_[fun x => x + 1]_与_[fun x => x * x * x]_这三个简单函数
    都是单调的；第二步则利用复合函数的单调性性质将这三个结论组合起来完成证明。*)

Proof.
  assert (mono (fun x => x - 1)) as H_minus.
  (** 这里的_[assert]_指令表示：声明_[mono (fun x => x - 1)]_这一命题成立。逻辑上
      看，一个合理的逻辑系统不应当允许我们凭空声明一条性质。因此，我们在完成声明后需要
      首先证明“为什么这一命题成立”，再基于此进行后续证明。在执行完这一条指令后，Coq系
      统显示目前有两个证明目标需要证明，它们分别对应这里所说的“为什么这一命题成立”与后
      续证明两部分。*)
  { unfold mono. lia. }
  (** 在有多个证明目标需要证明的时候，证明脚本中的左大括号表示进入其中的第一个证明目标
      的证明。这里的第一个证明目标就是要证明_[fun x => x - 1]_是一个单调函数。该证明
      结束后，证明脚本中的右大括号表示返回其余证明目标。返回后可以看到，证明目标中增加
      了一条前提：_[H_minus: fun x => x - 1]_。这一前提的名称_[H_minus]_是先前的
      _[assert]_指令选定的。*)
  assert (mono (fun x => x + 1)) as H_plus.
  { unfold mono. lia. }
  (** 类似的，这里可以使用声明+证明的方式证明_[fun x => x + 1]_也是一个单调函数。*)
  pose proof cube_mono as H_cube.
  (** 先前已经证明过，立方函数是单调的，这里直接_[pose proof]_这一结论。至此，我们已
      经完成了三个子命题的证明，下面的将通过复合函数的形式把它们组合起来。*)
  pose proof mono_compose _ _ H_plus (mono_compose _ _ H_cube H_minus).
  unfold mono.
  intros n m Hnm.
  unfold mono, Zcomp, plus_one in H.
  pose proof H n m Hnm.
  nia.
Qed.

(************)
(** 习题：  *)
(************)

(** 请证明下面Coq命题。*)

Example mono_ex2: mono (fun x => x * x * x + 3 * x * x + 3 * x).
Proof.
Admitted. (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)


