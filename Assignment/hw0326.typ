#set text(12pt,font:("Times New Roman","Noto Serif CJK SC"))

#set heading(numbering: "1.1")
#show heading: it=>{
  if it.level == 1 {
    set align(center)
    it.body
  } else if it.level == 2 {
    set align(center)
    it.body
  } else {
    // counter(heading).display()
    it.body
    parbreak()
  }
}

= 作业 03/26

1.
#let T = "True"
#let F = "False"
#list(F, T, F, T, F)

2.

存在。

设 $A={a,b,c}$，满足 $a <= b$ 且 $a <= c$，但 $b$ 与 $c$ 不能比较。

则 $(A, <=)$ 是完备偏序集，但并不是完备格，因为 ${b,c}$ 不存在上确界。

3.

#let leA = $scripts(<=)_A$

令 $a=mu G$，带入得 $F(mu G) leA G(mu G)=mu G$.

由 Knaster-Tarski 定理，$mu F = inf S = inf { x | F(x) <= x }$。

而 $mu G in S$，所以 $inf S leA mu G$，即 $mu F <= mu G$。

4.
#let botA = $scripts(bot)_A$
简记 $F^k (botA) = cases(botA & "if" k = 0, F(F^(k-1)(botA)) & "if" k > 0)$.

可证，对任意 $k in bb(N)$, $F^k (botA) leA mu F$：
- 当 $k = 0$ 时，$F^k (botA) = botA <= mu F$
- 当 $k > 0$ 时，归纳假设 $F^(k-1) (botA) leA mu F$。

  因为 $F$ 是单调函数，所以 $F^k (botA) leA F(mu F)=mu F$。

从而 $mu F$ 是 ${botA, F(botA), F(F(botA)), ...}$ 的上界。

从而 $op("lub")(botA, F(botA), F(F(botA)), ...) leA mu F$。
