#import "void-import.typ": *

== 导出范畴中的陈述

本节把本章发展出的结果翻译成导出范畴中的陈述。我们先翻译消没定理，因为它们为紧合基变换的翻译提供了一个有用的有界性条件。 

消没定理包括 Artin 消没（@artin-vanishing）、Grothendieck 消没（@grothendieck-vanishing）以及它们的相对版本（@relative-artin-grothendieck-vanishing），我们翻译如下： 

#theorem(name: <derived-artin-grothendieck-vanishing>)[
  + (绝对消没) 设 $K$ 是域，$X$ 是有限型 $K$-概形。假设 $cd(K) < +oo$。 

    + (Artin) 若 $X$ 是仿射的，则 $R Gamma(X, -): D_#[tor] (X_et, Lambda) -> D(Lambda)$ 的上方上同调维数 $<= cd(K) + dim(X)$； 

    + (Grothendieck) $R Gamma(X, -): D_#[tor] (X_et, Lambda) -> D(Lambda)$ 的上方上同调维数 $<= cd(K) + 2 dim(X)$。 

    无论哪种情形，$R Gamma(X, -)$ 都上有界。 

  + (相对消没) 设 $f: X -> Y$ 是概形间的态射。 

    + (Artin) 若对某个域 $K$，$f$ 是有限型 $K$-概形之间的仿射态射，则 $R f_*: D_#[tor] (X_et, Lambda) -> D(Y_et, Lambda)$ 的上方上同调维数 $<= dim(X)$； 

    + (Grothendieck) 若对某个域 $K$，$f$ 是有限型 $K$-概形之间的态射，则 $R f_*: D_#[tor] (X_et, Lambda) -> D(Y_et, Lambda)$ 的上方上同调维数 $<= 2 dim(X)$； 

    + (逐纤维) 若 $f$ 紧合，且各纤维的维数 $<=d$，则 $R f_*: D_#[tor] (X_et, Lambda) -> D(Y_et, Lambda)$ 的上方上同调维数 $<=2d$。 

    以上各情形中，$R f_*$ 都上有界。 
]

至于紧合基变换（@proper-base-change）： 

#theorem(name: <derived-base-changes>)[
  在拉回图表中： 
  // https://q.uiver.app/#r=typst&q=WzAsNCxbMCwwLCJYJyJdLFsxLDAsIlknIl0sWzAsMSwiWCJdLFsxLDEsIlkiXSxbMiwzLCJmIl0sWzAsMSwiZiciXSxbMSwzLCJnIl0sWzAsMiwiZyciLDJdXQ==
  #align(center, diagram({
    node((-1, -1), [$X'$])
    node((0, -1), [$Y'$])
    node((-1, 0), [$X$])
    node((0, 0), [$Y$])
    node((-0.7, -0.7), $cart$)
    edge((-1, 0), (0, 0), [$f$], label-side: left, "->")
    edge((-1, -1), (0, -1), [$f'$], label-side: left, "->")
    edge((0, -1), (0, 0), [$g$], label-side: left, "->")
    edge((-1, -1), (-1, 0), [$g'$], label-side: right, "->")
  }))
  给定 $cal(K) in D(X_et, Lambda)$，基变换映射如下： 
  $
    g^(-1) R f_* cal(K) -> R f'_* g'^(-1) cal(K)
  $
  只要下列条件之一成立，它就是拟同构： 

  + $f$ 有限；

  + $g$ 平展；

  + (紧合基变换) $f$ 紧合，$Y,Y'$ 局部 Noether，$cal(K) in D_#[tor] (X_et, Lambda)$。 
]
#proof[
  (1) 可以逐项验证，(2) 则取 K-内射消解来验证。 
  
  (3) $R f_*$ 与 $g^(-1)$ 都与任意的平展基变换交换，因此在 $Y$ 上 Zariski 局部地验证即可。由此不妨设 $Y = Spec(A)$ 是仿射的。此时 $X$ 在 $Y$ 上紧合，从而至少是有限型的，故 $X$ 可被有限多个有限型 $A$-代数覆盖。设其中每个都由 $d$ 个元素生成，则 $X -> Y$ 各纤维的维数都 $<=d$。于是由逐纤维的 Grothendieck 消没，$R f_*: D_#[tor] (X_et, Lambda) -> D(Y_et, Lambda)$ 上有界。从而该基变换映射两端的复形都上有界且下有界，无界复形的情形便由 way-out 引理得到。 
]
