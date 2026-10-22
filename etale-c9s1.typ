// audit-exception: 展示公式内的 #[...] 文字块夹有多段行内公式，且部分块内含 ZZ[n^(-1)] 之类的方括号；审计按相邻美元符号配对会把块内散文切成伪公式段，翻译这些文字块必然改变数学指纹。块内公式与全部其余数学均逐段核对未动。
#import "void-import.typ": *

本章是全书最后一章，我们要建立 Poincaré 对偶。我们将继续推进平展上同调与奇异上同调之间的类比。对可定向的 $n$ 维流形 $X$，经典 Poincaré 对偶断言：存在杯积配对 $smile$ 与迹同构 $Tr: H^n_c (X, QQ) ->^tilde QQ$，使得下面的配对是完美配对： 
$
  H^q_c (X, QQ) times H^(n-q) (X, QQ) ->^smile H^n_c (X, QQ) ->^Tr QQ
$

对平展上同调而言，可定向 $d$ 维流形对应的正确类比对象，是 $k$ 上相对维数为 $d$ 的光滑概形 $X$。系数环 $QQ$ 要换成一个常值挠层，比如 $ZZ\/n$，其中 $n in k^times$；这是因为平展上同调在非挠系数下、以及在基底域中不可逆的挠系数下，都表现得十分糟糕。 

但即便做了这些看似自然的修改，仍然不存在形如 $H^(2d)_c (X, ul(ZZ\/n)) -> ZZ\/n$ 的迹映射 (trace map)。线索藏在曲线的上同调里。 

- 对光滑射影曲线 $X$，Kummer 理论给出典范同构：#h(1fr)
  $
    H^2 (X, mu_n) cong Pic(X)\/n Pic(X) -->^deg_(tilde) ZZ\/n
  $
  由投影公式，有典范同构 $H^2 (X, ul(ZZ\/n)) cong mu_n^(otimes -1)$。 

  换言之，不存在典范同构 $H^2 (X, ul(ZZ\/n)) cong ZZ\/n$，因为这需要在 $k$ 中人为选取一个本原 $n$ 次单位根。 

因此必须修改迹映射的形式。正确的形式不是迹映射 $Tr_(X\/k): H^(2d)_c (X, ul(ZZ\/n)) -> ZZ\/n$，而应当是： 
$
  Tr_(X\/k): H^(2d)_c (X, mu_n^(otimes d)) -> ZZ\/n
$
这正是曲线情形所提示的。事实上，迹映射还有相对版本：设 $f: X -> Y$ 是相对维数为 $d$ 的光滑态射，其几何纤维非空连通，则存在典范同构： 
$
  R^(2d) f_! mu_n^(otimes d) -> ul(ZZ\/n)
$
由投影公式，对每个复形 $cal(K)$，这确实给出典范同构： 
$
  R f_! (cal(K) Lotimes_(ZZ\/n) mu_n^(otimes d))[2d] -> cal(K)
$
接下来我们要证明经典 Poincaré 对偶的平展类比，即： 
$
  H^q_c (X, mu_n^(otimes d)) times H^(2d-q) (X, ul(ZZ\/n)) ->^smile H^(2d)_c (X, mu_n^(otimes d)) ->^Tr ZZ\/n
$
只要 $X$ 是代数闭域 $k$ 上相对维数为 $d$ 的光滑概形，上述配对就是完美配对。 

不过，我们要证明的不止这一条。事实上，抽象地审视这些目标陈述，便会看到一些迹象：只要 $f$ 是有限型的分离态射，$R f_!$ 就应当有右伴随 $R f^!$。随后我们会看到，Poincaré 对偶可由下面的纯性陈述推出： 

- 若 $f: X -> Y$ 是相对维数为 $d$ 的光滑态射，且 $n in cal(O)_Y^times$，则：#h(1fr)
  $
    R f^! ul(ZZ\/n) = mu_n^(otimes d)[2d]
  $

函子 $R f^!$ 不只对 Poincaré 对偶有用；引入它之后，我们还能把平展上同调放进一个非常优雅的公理框架，即 Grothendieck 的_六函子形式_。在本章后面的几节里，我们会借助 Poincaré 对偶，通过一连串归约逐步自举，证明一个很强的基变换结果——一般基变换；再用它给出陈述六函子形式所需的有限性结果。 

== 光滑态射的迹映射

// 0. 若在所有光滑映射的族上存在迹态射，则它唯一
// 1. 对相对维数为 0/1、具有平展坐标的光滑态射，存在相容的迹态射族
// 2. 对具有平展坐标的光滑态射，存在相容的迹态射族
// 3. 存在相容的迹态射族

本节我们打算定义迹映射。 

迹映射可以由公理唯一刻画：它与复合、基变换相容，并在平展态射与曲线的情形有显式描述。 

本节对迹映射的公理式处理，受到 @cite-freitag-kiehl[Section II.1] 中做法的启发。 

#notation[
  设 $cal(S)$ 是一族纯相对维数的分离光滑态射，定义在 Noether 的 $ZZ[n^(-1)]$-概形之间，且对复合与 (Noether) 基变换封闭。 
  
  一族*类迹映射* (trace-like maps) 是指一族 ${S_f = S_(X\/Y)}_((f:X->Y) in cal(S))$，其中对任意相对维数为 $d$ 的 $f: X -> Y$，$S_(X\/Y)$ 形如： 
  $
    S_(X\/Y): R^(2d) f_! mu_(n,X)^(otimes d) -> ul(ZZ\/n)_Y
  $
  等价地，由 Grothendieck 消没，$R f_! mu_(n,X)^(otimes d)$ 集中在次数 $[0,2d]$ 内，因此映射 $S_(X\/Y): R^(2d) f_! mu_(n,X)^(otimes d) -> ul(ZZ\/n)_Y$ 等价于一个映射： 
  $
    S_(X\/Y): R f_! mu_(n,X)^(otimes d)[2d] -> ul(ZZ\/n)_Y
  $

  称一族类迹映射 ${S_(X\/Y)}_((f:X->Y) in cal(S))$ 是： 

  - *与基变换相容*：若对每个态射 $g: Y' -> Y$（$Y'$ 为 Noether 的）以及拉回图表：#h(1fr)
    // https://q.uiver.app/#r=typst&q=WzAsNCxbMCwwLCJYJyJdLFsxLDAsIlknIl0sWzAsMSwiWCJdLFsxLDEsIlkiXSxbMiwzLCJmIiwyXSxbMCwxLCJmJyJdLFsxLDMsImciXSxbMCwyLCJnJyIsMl1d
    #align(center, diagram({
      node((0, 0), [$X'$])
      node((1, 0), [$Y'$])
      node((0, 1), [$X$])
      node((1, 1), [$Y$])
      node((0.3, 0.3), [$cart$])
      edge((0, 1), (1, 1), [$f$], label-side: right, "->")
      edge((0, 0), (1, 0), [$f'$], label-side: left, "->")
      edge((1, 0), (1, 1), [$g$], label-side: left, "->")
      edge((0, 0), (0, 1), [$g'$], label-side: right, "->")
    }))
    下面的映射图表交换：
    // https://q.uiver.app/#r=typst&q=WzAsNCxbMCwwLCJnXigtMSkgUiBmXyEgbXVfbl4ob3RpbWVzIGQpWzJkXSJdLFsxLDAsInVsKFpaXFwvbikiXSxbMSwxLCJ1bChaWlxcL24pIl0sWzAsMSwiUiBmJ18hIG11X25eKG90aW1lcyBkKVsyZF0iXSxbMCwxLCJnXigtMSkgU18oWFxcL1kpIl0sWzAsMywiQkMiLDJdLFszLDIsIlNfKFgnXFwvWScpIiwyXV0=
    #align(center, diagram({
      node((0, 0), [$g^(-1) R f_! mu_n^(otimes d)[2d]$])
      node((1, 0), [$ul(ZZ\/n)$])
      node((1, 1), [$ul(ZZ\/n)$])
      node((0, 1), [$R f'_! mu_n^(otimes d)[2d]$])
      edge((0, 0), (1, 0), [$g^(-1) S_f$], label-side: left, "->")
      edge((0, 0), (0, 1), [$BC$], label-side: right, "->")
      edge((0, 1), (1, 1), [$S_(f')$], label-side: right, "->")
      edge((1, 0), (1, 1), "=")
    }))

  - *与复合相容*：若 $f: X -> Y, g: Y -> Z$ 都在族 $cal(S)$ 中，分别是相对维数 $d,e$ 的光滑态射，则复合
    $
      R g_! R f_! mu_n^(otimes (d+e)) [2(d+e)] -->^P R g_! (R f_! mu_n^(otimes d)[2d] Lotimes_(ZZ\/n) mu_n^(otimes e)[2e]) -->^(S_(X\/Y)) R g_! mu_n^(otimes e)[2e] -->^(S_(Y\/Z)) ul(ZZ\/n)
    $
    恰好就是 $S_(X\/Z)$。（这里 $P$ 是投影同构。）

    为记号方便，我们把上面的复合记为：
    $
      S_(Y\/Z) diamond.small S_(X\/Y)
    $
    于是与复合相容可写成 $S_(Y\/Z) diamond.small S_(X\/Y) = S_(X\/Z)$。

    由投影映射的自然性，$diamond.small$ 满足结合律。
]

下面用公理刻画迹映射的唯一性。 

#proposition(name: <pd-trace-uniqueness>)[
  假设在 Noether 的 $ZZ[n^(-1)]$-概形之间纯相对维数的所有分离光滑态射构成的族上，存在一族类迹映射 ${Tr_(X\/Y)}$，满足：

  0. ${Tr_(X\/Y)}$ 与基变换、复合相容；

  + 对平展态射 $f: X -> Y$（即相对维数为 0 的光滑态射），#h(1fr)
    $
      Tr_(X\/Y): f_! ul(ZZ\/n) -> ul(ZZ\/n)
    $
    是伴随的余单位。

  + 设 $f: X -> Spec(k)$ 是代数闭域 $k$ 上的光滑射影曲线，则 $Tr_(X\/k)$ 刻画为：
    $
      Tr_(X\/k): H^2 (X, mu_n) cong Pic(X)\/n Pic(X) ->^deg ZZ\/n 
    $
    其中典范同构 $H^2 (X, mu_n) cong Pic(X)\/n Pic(X)$ 来自 @cohom-of-proj-curve (1)。

  那么这族类迹映射是唯一的。
]
#proof[
  由与复合相容，当 $k$ 代数闭、$f: AA^1_k -> Spec(k)$、紧化为 $AA^1_k ->^j PP^1_k ->^(ol(f)) Spec(k)$ 时，$Tr_(AA^1_k\/k)$ 分解为：
  $
    H^2_c (AA^1_k, mu_n) -->^(Tr_(AA^1_k\/PP^1_k)) H^2 (PP^1_k, mu_n) -->^(Tr_(PP^1_k\/k)) ZZ\/n
  $
  由 (1) 与 (2)，这两个映射都已知。因此 $Tr_(AA^1_k\/k)$ 唯一确定。由与基变换相容，每个 $Tr_(AA^1_Y\/Y)$ 都唯一确定。于是由与复合相容，每个 $Tr_(AA^d_Y\/Y)$ 都唯一确定。

  现在由 @equiv-defns-of-smooth (3)，对每个相对维数为 $d$ 的光滑态射 $f: X -> Y$，都存在交换图表：
  // https://q.uiver.app/#r=typst&q=WzAsNCxbMCwwLCJVIl0sWzEsMCwiQUFeZF9ZIl0sWzAsMSwiWCJdLFsxLDEsIlkiXSxbMCwyLCJnIiwyXSxbMCwxLCJmXzEiXSxbMSwzLCJwIl0sWzIsMywiZiIsMl1d
  #align(center, diagram({
    node((0, 0), [$U$])
    node((1, 0), [$AA^d_Y$])
    node((0, 1), [$X$])
    node((1, 1), [$Y$])
    edge((0, 0), (0, 1), [$g$], label-side: right, "->")
    edge((0, 0), (1, 0), [$f_1$], label-side: left, "->")
    edge((1, 0), (1, 1), [$p$], label-side: left, "->")
    edge((0, 1), (1, 1), [$f$], label-side: right, "->")
  }))
  其中 $g$ 是平展覆盖，$f_1$ 平展，$p$ 是 $AA^d$ 的投影。我们已经看到 $Tr_(AA^d_Y\/Y)$ 唯一确定，于是由 (1) 以及与复合相容，$Tr_(U\/Y)$ 唯一确定。而 $Tr_(U\/X)$ 是余单位：
  $
    g_! ul(ZZ\/n) -> ul(ZZ\/n)
  $
  检查茎可知它是满射，因为 $g$ 是满射且平展。由 Grothendieck 消没，$R^(2d) f_!$ 右正合，故 $R^(2d) f_! g_! mu_n^(otimes d) -> R^(2d) f_! mu_n^(otimes d)$ 是满射。现在，复合
  $
    R^(2d) f_! g_! mu_n^(otimes d) -> R^(2d) f_! mu_n^(otimes d) -->^(Tr_(X\/Y)) ul(ZZ\/n)
  $
  等于 $Tr_(U\/Y)$，因而唯一确定；其中第一个映射是唯一确定的满射。于是第二个映射 $Tr_(X\/Y)$ 唯一确定。
]

上述对迹映射唯一性的公理刻画已经暗示了它的构造方式：用若干刻画其相容性的引理，把下面三种构造粘在一起：

- 对分离平展态射 $f: X -> Y$，取余单位 $Tr_(X\/Y)^compose: f_! ul(ZZ\/n) -> ul(ZZ\/n)$；

- 对光滑曲线 $f: X -> Spec(k)$（$k$ 代数闭），映射：#h(1fr)
  $
    Tr_(X\/k)^tilde: H^2_c (X, mu_n) cong Pic(X)\/n Pic(X) ->^deg ZZ\/n 
  $

- 对仿射空间的投影 $p: AA^d_Y -> Y$，映射：
  $
    Tr_(AA^d_Y\/Y)^square: R^(2d) p_! mu_n^(otimes d) -> ul(ZZ\/n)
  $
  它取为典范同构 $ul(ZZ\/n) -> R p_! mu_n^(otimes d)[2d]$ 的逆。

只有第三种构造我们还不知道，所以我们先构造它。

#lemma(name: <pd-trace-affine-constr>)[
  给定任意 Noether 概形 $Y$ 及仿射空间投影 $p_d: AA^d_Y -> Y$，存在典范同构：
  $
    Tr_(AA^d_Y\/Y)^square: R p_(d,!) mu_n^(otimes d)[2d] -> ul(ZZ\/n)
  $
  它作为下面这族态射上的类迹映射族：
  $
    cal(S)^square = {AA^(d_1+d_2)_Y -> AA^(d_1)_Y #[到前 $d_1$ 个坐标的投影] : d_(1,2) in NN, Y #[Noether 的 $ZZ[n^(-1)]$-概形]}
  $
  它与基变换、复合相容。此外，对任意由置换 $sigma in S_d$ 置换坐标而定义的自同构 $sigma: AA^d_Y -> AA^d_Y$，都有交换图表：
  // https://q.uiver.app/#r=typst&q=WzAsNCxbMCwwLCJSIHBfKGQsISkgbXVfbl4ob3RpbWVzIGQpIFsyZF0iXSxbMCwyLCJSIHBfKGQsISkgc2lnbWFfISBtdV9uXihvdGltZXMgZCkgWzJkXSJdLFsyLDAsInVsKFpaXFwvbikiXSxbMiwyLCJSIHBfKGQsISkgbXVfbl4ob3RpbWVzIGQpIFsyZF0iXSxbMCwyLCJUcl5zcXVhcmVfKHBfZCkiXSxbMSwwLCJUcl9zaWdtYV5jb21wb3NlIl0sWzEsMywidGlsZGUiLDJdLFszLDIsIlRyXnNxdWFyZV8ocF9kKSIsMl1d
  #align(center, diagram({
    node((0, 0), [$R p_(d,!) mu_n^(otimes d) [2d]$])
    node((0, 2), [$R p_(d,!) sigma_! mu_n^(otimes d) [2d]$])
    node((2, 0), [$ul(ZZ\/n)$])
    node((2, 2), [$R p_(d,!) mu_n^(otimes d) [2d]$])
    edge((0, 0), (2, 0), [$Tr^square_(p_d)$], label-side: left, "->")
    edge((0, 2), (0, 0), [$Tr_sigma^compose$], label-side: left, "->")
    edge((0, 2), (2, 2), [$tilde$], label-side: right, "->")
    edge((2, 2), (2, 0), [$Tr^square_(p_d)$], label-side: right, "->")
  }))
  其中底部的同构由 $p_d compose sigma = p_d$ 诱导，左边的映射 $Tr_sigma^compose$ 是 $sigma_! tack.l sigma^(-1)$ 的余单位。
]
#proof[
  先构造映射 $Tr_(AA^1_Y\/Y)^square$。设 $p_1: AA^1_Y -> Y$，其紧化为 $AA^1_Y ->^j PP^1_Y ->^(ol(p_1)) Y$。由 Kummer 序列，存在典范映射：
  $
    Pic(PP^1_Y) = H^1 (PP^1_Y, GG_m) -> H^2 (PP^1_Y, mu_n)
  $
  设 $c_(1,Y) in H^2 (PP^1_Y, mu_n)$ 是典范丛 $cal(O)_(PP^1_Y) (1)$ 在此映射下的像。回忆 $R^2 ol(p_1)_* mu_n = (U |-> H^2 (PP^1_U, mu_n))^\#$，故类 $c_1 in H^2 (PP^1_Y, mu_n)$ 对应整体截面 $c_Y in Gamma(PP^1_Y, R^2 ol(p_1)_* mu_n)$。这就定义了映射：
  $
    alpha_Y: ul(ZZ\/n)_Y -> R^2 ol(p_1)_* mu_n
  $

  我们断言 $alpha_Y$ 与基变换相容。
  #proof_[断言的证明][
    事实上，对拉回图表：#h(1fr)
    // https://q.uiver.app/#r=typst&q=WzAsNixbMCwwLCJBQV4xXyhZJykiXSxbMSwwLCJQUF4xXyhZJykiXSxbMiwwLCJZJyJdLFswLDEsIkFBXjFfWSJdLFsxLDEsIlBQXjFfWSJdLFsyLDEsIlkiXSxbMyw0LCJqIiwyXSxbNCw1LCJvbChwXzEpIiwyXSxbMiw1LCJnIl0sWzAsMywiZyciLDJdLFsxLDQsIm9sKGcpJyJdLFsxLDIsIm9sKHAnXzEpIl0sWzAsMSwiaiciXV0=
    #align(center, diagram({
      node((0, 0), [$AA^1_(Y')$])
      node((1, 0), [$PP^1_(Y')$])
      node((2, 0), [$Y'$])
      node((0, 1), [$AA^1_Y$])
      node((1, 1), [$PP^1_Y$])
      node((2, 1), [$Y$])
      edge((0, 1), (1, 1), [$j$], label-side: right, "->")
      edge((1, 1), (2, 1), [$ol(p_1)$], label-side: right, "->")
      edge((2, 0), (2, 1), [$g$], label-side: left, "->")
      edge((0, 0), (0, 1), [$g'$], label-side: right, "->")
      edge((1, 0), (1, 1), [$ol(g)'$], label-side: left, "->")
      edge((1, 0), (2, 0), [$ol(p'_1)$], label-side: left, "->")
      edge((0, 0), (1, 0), [$j'$], label-side: left, "->")
    }))
    我们要证明下面的图表交换：
    // https://q.uiver.app/#r=typst&q=WzAsOSxbMCwwLCJaWlxcL24iXSxbMSwwLCJQaWMoUFBeMV9ZKSJdLFswLDIsIlpaXFwvbiJdLFsxLDIsIlBpYyhQUF4xXyhZJykpIl0sWzIsMCwiSF4yIChQUF4xX1ksIG11X24pIl0sWzIsMiwiSF4yIChQUF4xXyhZJyksIG11X24pIl0sWzMsMCwiR2FtbWEoWSwgUl4yIG9sKHBfMSlfKiBtdV9uKSJdLFszLDIsIkdhbW1hKFknLCBSXjIgb2wocCdfMSlfKiBtdV9uKSJdLFszLDEsIkdhbW1hKFksIGdeKC0xKSBSXjIgb2wocF8xKV8qIG11X24pIl0sWzAsMSwiY2FsKE8pKDEpIl0sWzIsMywiY2FsKE8pKDEpIl0sWzEsNF0sWzMsNV0sWzQsNl0sWzUsN10sWzAsMiwiIiwxLHsic3R5bGUiOnsiYm9keSI6eyJuYW1lIjoiZG91YmxlIGJhcnJlZCJ9fX1dLFsxLDMsIm9sKGcpJ14oLTEpIl0sWzQsNSwicmVzIl0sWzYsOCwicmVzIl0sWzgsNywiQkMiLDFdXQ==
    #align(center, diagram({
      node((0, 0), [$ZZ\/n$])
      node((1, 0), [$Pic(PP^1_Y)$])
      node((0, 2), [$ZZ\/n$])
      node((1, 2), [$Pic(PP^1_(Y'))$])
      node((2, 0), [$H^2 (PP^1_Y, mu_n)$])
      node((2, 2), [$H^2 (PP^1_(Y'), mu_n)$])
      node((3, 0), [$Gamma(Y, R^2 ol(p_1)_* mu_n)$])
      node((3, 2), [$Gamma(Y', R^2 ol(p'_1)_* mu_n)$])
      node((3, 1), [$Gamma(Y, g^(-1) R^2 ol(p_1)_* mu_n)$])
      edge((0, 0), (1, 0), [$cal(O)(1)$], label-side: left, "->")
      edge((0, 2), (1, 2), [$cal(O)(1)$], label-side: left, "->")
      edge((1, 0), (2, 0), "->")
      edge((1, 2), (2, 2), "->")
      edge((2, 0), (3, 0), "->")
      edge((2, 2), (3, 2), "->")
      edge((0, 0), (0, 2), "=")
      edge((1, 0), (1, 2), [$ol(g)'^*$], label-side: left, "->")
      edge((2, 0), (2, 2), [$res$], label-side: left, "->")
      edge((3, 0), (3, 1), [$res$], label-side: left, "->")
      edge((3, 1), (3, 2), [$BC$], label-side: left, "->")
    }))
    
    回忆，把定义展开可得：

    - 对 $f: X -> Y$，映射 $f^*: Pic(Y) -> Pic(X)$ 等同于映射：#h(1fr)
      $
        H^1 (Y, GG_(m,X)) ->^res H^1 (X, f^(-1) GG_(m,Y)) -> H^1 (X, GG_(m,X))
      $
      其中映射 $f^(-1) GG_(m,Y) -> GG_(m,X)$ 由伴随性从 $GG_(m,Y) -> GG_(m,X)$ 诱导得到。此外还有交换图表：
      // https://q.uiver.app/#r=typst&q=WzAsMTAsWzAsMCwiMCJdLFsxLDAsImZeKC0xKSBtdV8obixZKSJdLFsyLDAsImZeKC0xKSBHR18obSxZKSJdLFszLDAsImZeKC0xKSBHR18obSxZKSJdLFs0LDAsIjAiXSxbMCwxLCIwIl0sWzEsMSwibXVfKG4sWCkiXSxbMiwxLCJHR18obSxYKSJdLFszLDEsIkdHXyhtLFgpIl0sWzQsMSwiMCJdLFswLDFdLFsxLDJdLFsyLDMsIigtKV5uIl0sWzMsNF0sWzUsNl0sWzYsN10sWzcsOCwiKC0pXm4iLDJdLFs4LDldLFsxLDYsInRpbGRlIiwxXSxbMiw3XSxbMyw4XV0=
      #context align(center, diagram({
        node((0, 0), [$0$])
        node((1, 0), [$f^(-1) mu_(n,Y)$])
        node((2, 0), [$f^(-1) GG_(m,Y)$])
        node((3, 0), [$f^(-1) GG_(m,Y)$])
        node((4, 0), [$0$])
        node((0, 1), [$0$])
        node((1, 1), [$mu_(n,X)$])
        node((2, 1), [$GG_(m,X)$])
        node((3, 1), [$GG_(m,X)$])
        node((4, 1), [$0$])
        edge((0, 0), (1, 0), "->")
        edge((1, 0), (2, 0), "->")
        edge((2, 0), (3, 0), [$(-)^n$], label-side: left, "->")
        edge((3, 0), (4, 0), "->")
        edge((0, 1), (1, 1), "->")
        edge((1, 1), (2, 1), "->")
        edge((2, 1), (3, 1), [$(-)^n$], label-side: right, "->")
        edge((3, 1), (4, 1), "->")
        edge((1, 0), (1, 1), [$tilde$], label-side: center, "->")
        edge((2, 0), (2, 1), "->")
        edge((3, 0), (3, 1), "->")
      }, crossing-fill: thm-box-curr-color()))

      （我们在紧合基变换证明的末尾已经见过这一点。）
    
    于是，我们要证明其交换性的图表分解为：
    // https://q.uiver.app/#r=typst&q=WzAsMTEsWzAsMCwiWlpcXC9uIl0sWzEsMCwiSF4xKFBQXjFfWSwgR0dfbSkiXSxbMCwyLCJaWlxcL24iXSxbMSwyLCJIXjEoUFBeMV8oWScpLCBHR19tKSJdLFsyLDAsIkheMiAoUFBeMV9ZLCBtdV9uKSJdLFsyLDIsIkheMiAoUFBeMV8oWScpLCBtdV9uKSJdLFszLDAsIkdhbW1hKFksIFJeMiBvbChwXzEpXyogbXVfbikiXSxbMywyLCJHYW1tYShZJywgUl4yIG9sKHAnXzEpXyogbXVfbikiXSxbMywxLCJHYW1tYShZLCBnXigtMSkgUl4yIG9sKHBfMSlfKiBtdV9uKSJdLFsxLDEsIkheMShQUF4xXyhZJyksIG9sKGcpJ14oLTEpIEdHX20pIl0sWzIsMSwiSF4yIChQUF4xXyhZJyksIG11X24pIl0sWzAsMSwiY2FsKE8pKDEpIl0sWzIsMywiY2FsKE8pKDEpIl0sWzEsNF0sWzMsNV0sWzQsNl0sWzUsN10sWzYsOCwicmVzIl0sWzgsNywiQkMiLDFdLFsxLDksInJlcyJdLFs5LDNdLFswLDIsIiIsMSx7InN0eWxlIjp7ImJvZHkiOnsibmFtZSI6ImRvdWJsZSBiYXJyZWQifX19XSxbNCwxMCwicmVzIl0sWzEwLDUsIiIsMCx7InN0eWxlIjp7ImJvZHkiOnsibmFtZSI6ImRvdWJsZSBiYXJyZWQifX19XSxbOSwxMF1d
    #align(center, diagram({
      node((0, 0), [$ZZ\/n$])
      node((1, 0), [$H^1(PP^1_Y, GG_m)$])
      node((0, 2), [$ZZ\/n$])
      node((1, 2), [$H^1(PP^1_(Y'), GG_m)$])
      node((2, 0), [$H^2 (PP^1_Y, mu_n)$])
      node((2, 2), [$H^2 (PP^1_(Y'), mu_n)$])
      node((3, 0), [$Gamma(Y, R^2 ol(p_1)_* mu_n)$])
      node((3, 2), [$Gamma(Y', R^2 ol(p'_1)_* mu_n)$])
      node((3, 1), [$Gamma(Y, g^(-1) R^2 ol(p_1)_* mu_n)$])
      node((1, 1), [$H^1(PP^1_(Y'), ol(g)'^(-1) GG_m)$])
      node((2, 1), [$H^2 (PP^1_(Y'),ol(g)'^(-1) mu_n)$])
      edge((0, 0), (1, 0), [$cal(O)(1)$], label-side: left, "->")
      edge((0, 2), (1, 2), [$cal(O)(1)$], label-side: left, "->")
      edge((1, 0), (2, 0), "->")
      edge((1, 2), (2, 2), "->")
      edge((2, 0), (3, 0), "->")
      edge((2, 2), (3, 2), "->")
      edge((3, 0), (3, 1), [$res$], label-side: left, "->")
      edge((3, 1), (3, 2), [$BC$], label-side: left, "->")
      edge((1, 0), (1, 1), [$res$], label-side: left, "->")
      edge((1, 1), (1, 2), "->")
      edge((0, 0), (0, 2), "=")
      edge((2, 0), (2, 1), [$res$], label-side: left, "->")
      edge((2, 1), (2, 2), "->", $tilde$)
      edge((1, 1), (2, 1), "->")
    }))

    左方块交换，因为 $ol(g)'^* cal(O)(1) cong cal(O)(1)$。中间两个方块由自然性交换。因此只剩右方块需要证明。把 $ol(g)'^(-1) mu_n cong mu_n$ 的自然性方块约去，便归结为下面的引理：

    #lemma[
      给定拉回图表：
      #align(center, diagram({
        node((0, 0), [$X'$])
        node((1, 0), [$Y'$])
        node((0, 1), [$X$])
        node((1, 1), [$Y$])
        node((0.3, 0.3), [$cart$])
        edge((0, 1), (1, 1), [$f$], label-side: right, "->")
        edge((0, 0), (1, 0), [$f'$], label-side: left, "->")
        edge((1, 0), (1, 1), [$g$], label-side: left, "->")
        edge((0, 0), (0, 1), [$g'$], label-side: right, "->")
      }))
      对每个 $cal(F) in cAb(X_et)$，下面的映射图表都交换：
      // https://q.uiver.app/#r=typst&q=WzAsNSxbMCwwLCJIXnEgKFgsIGNhbChGKSkiXSxbMSwwLCJHYW1tYShZLCBSXnEgZl8qIGNhbChGKSkiXSxbMCwyLCJIXnEgKFgnLCBnJ14oLTEpIGNhbChGKSkiXSxbMSwyLCJHYW1tYShZJywgUl5xIGYnXyogZydeKC0xKSBjYWwoRikpIl0sWzEsMSwiR2FtbWEoWSwgZ14oLTEpIFJecSBmXyogY2FsKEYpKSJdLFswLDFdLFsyLDNdLFswLDIsInJlcyIsMl0sWzEsNCwicmVzIl0sWzQsMywiQkMiXV0=
      #align(center, diagram({
        node((0, 0), [$H^q (X, cal(F))$])
        node((1, 0), [$Gamma(Y, R^q f_* cal(F))$])
        node((0, 2), [$H^q (X', g'^(-1) cal(F))$])
        node((1, 2), [$Gamma(Y', R^q f'_* g'^(-1) cal(F))$])
        node((1, 1), [$Gamma(Y, g^(-1) R^q f_* cal(F))$])
        edge((0, 0), (1, 0), "->")
        edge((0, 2), (1, 2), "->")
        edge((0, 0), (0, 2), [$res$], label-side: right, "->")
        edge((1, 0), (1, 1), [$res$], label-side: left, "->")
        edge((1, 1), (1, 2), [$BC$], label-side: left, "->")
      }))
    ]
    #proof[
      两条路径都是 $delta$-函子之间的自然变换 $H^q (X, -) -> Gamma(Y', R^q f'_* g'^(-1) (-))$。注意 ${H^q (X, -)}$ 是泛 $delta$-函子。因此要证明一般的 $q$，只需在 $q = 0$ 时证明。此时图表中的一切都是整体截面。把每个层都推到 $Y$ 上，就只需证明下面的图表交换：
      // https://q.uiver.app/#r=typst&q=WzAsNSxbMCwwLCJmXyogY2FsKEYpIl0sWzEsMCwiZl8qIGNhbChGKSJdLFswLDIsImZfKiBnJ18qIGcnXigtMSkiXSxbMSwyLCJnXyogZidfKiBnJ14oLTEpIl0sWzEsMSwiZ18qIGdeKC0xKSBmXyogY2FsKEYpIl0sWzAsMSwiIiwwLHsic3R5bGUiOnsiYm9keSI6eyJuYW1lIjoiZG91YmxlIGJhcnJlZCJ9fX1dLFsyLDMsInRpbGRlIiwyXSxbMCwyLCIjW3VuaXRdIiwyXSxbMSw0LCIjW3VuaXRdIl0sWzQsMywiQkMiXV0=
      #align(center, diagram({
        node((0, 0), [$f_* cal(F)$])
        node((1, 0), [$f_* cal(F)$])
        node((0, 2), [$f_* g'_* g'^(-1)$])
        node((1, 2), [$g_* f'_* g'^(-1)$])
        node((1, 1), [$g_* g^(-1) f_* cal(F)$])
        edge((0, 0), (1, 0), "=")
        edge((0, 2), (1, 2), [$tilde$], label-side: right, "->")
        edge((0, 0), (0, 2), [$#[unit]$], label-side: right, "->")
        edge((1, 0), (1, 1), [$#[unit]$], label-side: left, "->")
        edge((1, 1), (1, 2), [$BC$], label-side: left, "->")
      }))
      这是形式推导。
    ]
    至此我们证明了 $alpha_Y: ul(ZZ\/n)_Y -> R^2 ol(p_1)_* mu_n$ 与基变换相容。
  ]

  定义 $Tr_(AA^1_Y\/Y)^square$ 为映射：
  $
    Tr_(AA^1_Y\/Y)^square: R^2 p_(1,!) mu_n -> R^2 ol(p_1)_* mu_n ->^(alpha_Y^(-1)) ul(ZZ\/n)
  $
  其中第一个映射由零延拓三角诱导（它是同构，因为其余项为 $Y ->^id Y$，其推前没有 $R^1$ 与 $R^2$）。零延拓三角与 $alpha_Y$ 都与基变换相容，故 $Tr_(AA^1_Y\/Y)^square$ 亦然。

  由我们在 @cohom-with-proper-supp-of-Ad-and-Pd 中的计算以及紧合基变换，$R p_(1,!) mu_n$ 集中在 2 次。于是我们构造出同构：
  $
    Tr_(AA^1_Y\/Y)^square: R p_(1,!) mu_n [2] -> ul(ZZ\/n)
  $
  它与基变换相容。

  现在定义 $Tr_(AA^d_Y\/Y)^square$。设 $q_i: AA^d_Y -> AA^1_Y, 1<=i<=d$ 是到各个坐标的投影。取 $Tr_(AA^d_Y\/Y)^square$ 为如下定义的同构：
  $
    R p_(d,!) mu_n^(otimes d)[2d] &cong R p_(d_!) (q_1^(-1) mu_n [2] Lotimes_(ZZ\/n) dots.c Lotimes_(ZZ\/n) q_d^(-1) mu_n [2]) \
    &cong underbrace(R p_(1,!) mu_n [2] Lotimes_(ZZ\/n) dots.c Lotimes_(ZZ\/n) R p_(1,!) mu_n [2], #[$d$ 份]) #[由 Künneth 公式] \
    &cong ul(ZZ\/n) Lotimes_(ZZ\/n) dots.c Lotimes_(ZZ\/n) ul(ZZ\/n) #[由 $d$ 份 $Tr_(AA^1_Y\/Y)^square$] \
    &cong ul(ZZ\/n)
  $
  此时：

  - Künneth 映射是对称的。因此 $Tr_(AA^d_Y\/Y)^square$ 在 $AA^d_Y$ 的 $d$ 个坐标的置换下不变。

  - Künneth 映射与基变换相容，$Tr_(AA^1_Y\/Y)^square$ 也是。因此 $Tr_(AA^d_Y\/Y)^square$ 与基变换相容。

  - 检查 Künneth 映射的定义可以看出：
    $
      Tr_(AA^d_Y\/Y)^square = Tr_(AA^1_Y\/Y)^square diamond.small Tr_(AA^2_Y\/AA^1_Y)^square diamond.small dots.c diamond.small Tr_(AA^d_Y\/AA^(d-1)_Y)^square
    $
    因此 $Tr_(AA^d_Y\/Y)^square$ 立刻与复合相容。

  至此我们证明了所断言的全部性质。
]

#notation[
  迹映射的三个组成部分的记法如下：

  - 对分离平展态射 $f: X -> Y$，余单位：
    $
      Tr_(X\/Y)^compose: f_! ul(ZZ\/n) -> ul(ZZ\/n)
    $ 

  - 对光滑曲线 $f: X -> Spec(k)$（$k$ 代数闭），映射：#h(1fr)
    $
      Tr_(X\/k)^tilde: H^2_c (X, mu_n) ->^tilde H^2 (ol(X), mu_n) cong Pic(X)\/n Pic(X) ->^deg_tilde ZZ\/n 
    $
    其中：

    - $ol(X)$ 是 $X$ 的紧化，它是 $k$ 上的光滑射影曲线；

    - 第一个映射由零延拓三角诱导，它是同构，因为 $ol(X) - X$ 是 $k$ 上有限个闭点构成的集合，没有 $H^1_c, H^2_c$；

    - 同构 $H^2 (ol(X), mu_n) cong Pic(X)\/n Pic(X) ->^deg_tilde$ 如 @cohom-of-proj-curve 中所述。

  - 对仿射空间的投影 $p: AA^d_Y -> Y$，映射：
    $
      Tr_(AA^d_Y\/Y)^square: R^(2d) p_! mu_n^(otimes d) -> ul(ZZ\/n)
    $
    即上一引理中定义的映射。

  $Tr^compose_(X\/Y)$ 与基变换、复合的相容性是形式上的；$Tr^square_(AA^d_Y\/Y)$ 与基变换、复合的相容性则如上一引理所述。
]

下面我们通过证明若干相容性引理，把这些构造粘起来。

#lemma(name: <pd-trace-etale-curve-compat>)[
  设 $f: U -> X$ 是代数闭域 $k$ 上光滑曲线之间的平展态射，$n in k^times$。则：
  $
    Tr_(U\/k)^tilde = Tr_(X\/k)^tilde diamond.small Tr^compose_(U\/X)
  $
]
#proof[
  设 $X -> ol(X)$ 是 $X$ 的紧化，于是 $ol(X)$ 是 $k$ 上的光滑射影曲线。按定义：
  $
    Tr_(X\/k)^tilde diamond.small Tr^compose_(U\/X) = Tr_(ol(X)\/k)^tilde diamond.small Tr_(X\/ol(X))^compose diamond.small Tr^compose_(U\/X) = Tr_(ol(X)\/k)^tilde diamond.small Tr_(U\/ol(X))^compose
  $
  因此只需在 $X$ 为光滑射影曲线的情形证明本引理。设 $ol(U)$ 是 $U$ 的紧化。则 $f: U -> X$ 延拓为曲线之间的有限映射 $ol(f): ol(U) -> X$。设 $j: U -> ol(U)$ 是包含映射。
  
  于是需要证明下面的图表交换：
  // https://q.uiver.app/#r=typst&q=WzAsOCxbMCwwLCJIXjJfYyAoVSwgbXVfbikiXSxbMCwxLCJIXjJfYyAoVSwgbXVfbikiXSxbMSwwLCJIXjIgKG9sKFUpLCBtdV9uKSJdLFsyLDAsIlBpYyhvbChVKSlcXC9uIFBpYyhvbChVKSkiXSxbMywwLCJaWlxcL24iXSxbMywxLCJaWlxcL24iXSxbMSwxLCJIXjIgKFgsIG11X24pIl0sWzIsMSwiUGljKFgpXFwvbiBQaWMoWCkiXSxbMCwxLCIiLDAseyJzdHlsZSI6eyJib2R5Ijp7Im5hbWUiOiJkb3VibGUgYmFycmVkIn19fV0sWzQsNSwiIiwwLHsic3R5bGUiOnsiYm9keSI6eyJuYW1lIjoiZG91YmxlIGJhcnJlZCJ9fX1dLFswLDIsIlRyXyhVXFwvb2woVSkpXmNvbXBvc2UiXSxbMiwzLCJ0aWxkZSJdLFszLDQsImRlZyJdLFsxLDYsIlRyXyhVXFwvWCleY29tcG9zZSIsMl0sWzYsNywidGlsZGUiLDJdLFs3LDUsImRlZyIsMl1d
  #align(center, diagram({
    node((0, 0), [$H^2_c (U, mu_n)$])
    node((0, 1), [$H^2_c (U, mu_n)$])
    node((1, 0), [$H^2 (ol(U), mu_n)$])
    node((2, 0), [$Pic(ol(U))\/n Pic(ol(U))$])
    node((3, 0), [$ZZ\/n$])
    node((3, 1), [$ZZ\/n$])
    node((1, 1), [$H^2 (X, mu_n)$])
    node((2, 1), [$Pic(X)\/n Pic(X)$])
    edge((0, 0), (0, 1), "=")
    edge((3, 0), (3, 1), "=")
    edge((0, 0), (1, 0), [$Tr_(U\/ol(U))^compose$], label-side: left, "->")
    edge((1, 0), (2, 0), [$tilde$], label-side: left, "->")
    edge((2, 0), (3, 0), [$deg$], label-side: left, "->")
    edge((0, 1), (1, 1), [$Tr_(U\/X)^compose$], label-side: right, "->")
    edge((1, 1), (2, 1), [$tilde$], label-side: right, "->")
    edge((2, 1), (3, 1), [$deg$], label-side: right, "->")
  }))

  为此需要一些准备。

  #lemma[
    设 $f: X -> Y$ 是代数闭域 $k$ 上光滑射影曲线之间的有限态射，它自动是次数为 $r$ 的平坦态射。则：

    + $f_*: Div(X) -> Div(Y), sum_x n_x x |-> sum_x n_x f(x)$ 保持主除子，并诱导同态：#h(1fr)
      $
        Nm_f: Pic(X) -> Pic(Y)
      $

    + 对任意 $cal(L) in Pic(X)$，$f_* cal(L)$ 是秩 $r$ 的局部自由层。$Nm_f$ 可显式描述为：
      $
        Nm_f ([cal(L)]) = [det(f_* cal(L)) otimes det(f_* cal(O)_X)^(otimes -1)] 
      $

    + 存在态射 $Nm_f: f_* GG_(m,X) -> GG_(m,Y)$，它在 $H^1$ 上诱导 $Nm_f: Pic(X) -> Pic(Y)$。
  ]
  #proof[
    （$f: X -> Y$ 自动平坦：对闭点 $x in X, y = f(x)$，每个 $cal(O)_(Y,y) -> cal(O)_(X,x)$ 都是 DVR 之间的态射，且因 $f$ 支配而为单射。于是每个 $cal(O)_(X,x)$ 都是有限无挠的 $cal(O)_(Y,y)$-模，从而是自由模，特别地平坦。）

    (1) 设 $D = (s) in Div(X)$ 是主除子，即 $0 != s in K(X)$ 是有理函数，使得 $D = sum_(x in abs(X)) v_x (s) x in Div(X)$，其中每个 $v_x$ 是 $x$ 处的赋值 $K(X)^times -> ZZ$。取 $0 != Nm_(K(X)\/K(Y)) (s)$。则对 $y in abs(Y)$，我们断言：
    $
      v_y (Nm_(K(X)\/K(Y)) (s)) = sum_(x in f^(-1)(y)) v_x (s)
    $

    - 事实上，设 $B_y$ 是 $cal(O)_(Y,y)$ 在 $K(X)$ 中的整闭包。则 $B_y$ 是 Dedekind 整环，作为 $cal(O)_(Y,y)$-模有限自由、秩为 $r$，其极大理想与 $x in f^(-1)(y)$ 相应，对应的局部环是 $cal(O)_(X,x)$。
    
      现设 $s in B_y$。由于 $B_y$ 是有限自由的 $cal(O)_(Y,y)$-模，$Nm_(K(X)\/K(Y)) (s) = det_(cal(O)_(Y,y)) (times s: B_y -> B_y)$。取 Smith 标准形，可知：
      $
        v_y (Nm_(K(X)\/K(Y)) (s)) = length_(cal(O)_(Y,y)) (B_y\/s B_y) 
      $

      - 对任意挠 $B_y$-模 $M$，有长度分解：#h(1fr)
        $
          length_(cal(O)_(Y,y)) (M) = sum_(x in f^(-1)(y)) length_(cal(O)_(X,x)) (M_x)
        $
        由于 $M$ 作为 $cal(O)_(Y,y)$-模有有限长度，它作为 $B_y$-模也有有限长度，因此可把 $M$ 换成它的 $B_y$-Jordan–Hölder 因子。这些因子必定形如 $B_y\/frak(m)_x B_y$，其中 $x in f^(-1) (y)$。对它们只需证明：
        $
          length_(cal(O)_(Y,y)) (B_y\/frak(m)_x B_y) = 1
        $ 
        现在：
        $
          length_(cal(O)_(Y,y)) (B_y\/frak(m)_x B_y) = dim_(k(y)) (B_y\/frak(m)_x B_y) = dim_(k(y)) (k(x)) = 1
        $
        因为 $k(x) = k(y) = 1$，证毕。
      
      于是由长度分解，
      $
        v_y (Nm_(K(X)\/K(Y))(s)) &= length_(cal(O)_(Y,y)) (B_y\/s B_y) = sum_(x in f^(-1)(y)) length_(cal(O)_(X,x)) (cal(O)_(X,x)\/s cal(O)_(X,x)) \
        &= sum_(x in f^(-1)(y)) v_x (s)
      $
      因此，
      $
        f_* D = sum_(y in abs(Y)) (sum_(x in f^(-1)(y)) v_x (s)) y = sum_(y in abs(Y)) v_y (Nm_(K(X)\/K(Y)) (s)) y = (Nm_(K(X)\/K(Y))(s))
      $
      是主除子。

    (2) 首先注意，对每个 $cal(L) in Pic(X)$，$f_* cal(L)$ 都是秩 $r$ 的局部自由层。事实上，每个 $cal(O)_(Y,y) -> cal(O)_(X,x)$ 都是单射，故 $f_* cal(L)$ 无挠。又因 $f$ 有限，$f_* cal(L)$ 凝聚。$f_* cal(L)$ 的茎是 $Y$ 的局部环上的有限无挠模，而这些局部环是域或 DVR，故这些茎自由。于是 $f_* cal(L)$ 局部自由。最后，$f_* cal(L)$ 的泛点处的茎是 $K(X)$，它作为 $K(Y)$-向量空间的维数是 $r = [K(X):K(Y)]$。因此 $f_* cal(L)$ 是秩 $r$ 的局部自由层。
    
    由 @cite-hartshorne-ag[Exercise II.6.11(b)]，我们有下面的事实：

    - 设 $X$ 是代数闭域 $k$ 上的光滑曲线，给定短正合列：#h(1fr)
      $
        0 -> cal(E) -> cal(E)' -> cal(T) -> 0
      $
      其中 $cal(E), cal(E)'$ 是同秩的局部自由层，$cal(T)$ 是挠层，
      $
        det(cal(E)') cong det(cal(E)) otimes cal(L)(sum_(x in abs(X)) length_(cal(O)_(X,x)) (cal(T)_x) x)
      $
    
    现在对有效除子 $D in Div(X)$，考虑短正合列
    $
      0 -> cal(L)_X (-D) -> cal(O)_X -> cal(O)_D -> 0
    $
    由于 $f$ 有限，$f_*$ 正合，于是有短正合列：
    $
      0 -> f_* cal(L)_X (-D) -> f_* cal(O)_X -> f_* cal(O)_D -> 0
    $
    直接验证可知 $f_* cal(O)_D = cal(O)_(f_* D)$，因为：
    $
      length_(cal(O)_(Y,y)) ((f_* cal(O)_D)_y) = sum_(x in f^(-1) (y)) length_(cal(O)_(X,x)) (cal(O)_(D,x))
    $
    这用的是 (1) 中的长度公式。于是由本证明开头列出的事实，
    $
      det(f_* cal(O)_X) cong det(f_* cal(L)_X (-D)) otimes cal(L)_Y (f_* D)
    $

    现在对任意除子 $E in Div(X)$ 与任意有效除子 $D$，把同样的论证用于序列：
    $
      0 -> f_* cal(L)_X (E - D) -> f_* cal(L)_X (E) -> f_* cal(O)_D -> 0
    $
    即可看出：
    $
      det(f_* cal(L)_X (E)) cong det(f_* cal(L)_X (E - D)) otimes cal(L)_Y (f_* D)
    $
    于是对任意除子 $D in Div(X)$，写 $D = D_+ - D_-$，其中 $D_(plus.minus)$ 有效，从而：
    $
      det(f_* cal(L)_X (D)) &cong det(f_* cal(L)_X (-D_-)) otimes cal(L)_Y (f_* D_+) \
      &cong det(f_* cal(O)_X) otimes cal(L)_Y (f_* D_-)^(otimes -1) cal(L)_Y (f_* D_+) \
      &cong det(f_* cal(O)_X) otimes cal(L)_Y (f_* D)
    $
    因此，
    $
      cal(L)_Y (f_* D) = det(f_* cal(L)_X (D)) otimes det(f_* cal(O)_X)^(otimes -1)
    $
    证毕。

    (3) 先定义 Zariski 层之间的映射：
    $
      Nm_f: f_* cal(O)_X^times -> cal(O)_Y^times
    $
    注意 $f_* cal(O)_X$ 是局部自由的 $cal(O)_Y$-模层。于是局部地取范数，得到映射：
    $
      Nm_f: f_* cal(O)_X -> cal(O)_Y
    $
    它把单位送到单位，因此诱导 Zariski 层之间的映射 $Nm_f: f_* cal(O)_X^times -> cal(O)_Y^times$。

    接下来，把 $Nm_f$ 延拓为平展层之间的映射 $f_* GG_(m,X) -> GG_(m,Y)$。由 @etale-local-properties (2)，任意平展 $U in Et_Y$ 都是正则的，从而是 $k$ 上光滑曲线的不交并。因此要构造 $Nm_f: f_* GG_(m,X) -> GG_(m,Y)$，只需在 $U$ 的截面上构造它。
    
    作 $f$ 沿 $U -> Y$ 的基变换 $f_U: X_U -> U$，则 $f_U$ 是秩 $r$ 的有限平坦态射。由与 (2) 开头相同的论证，$f_(U,*) cal(O)_(X_U)$ 是秩 $r$ 的局部自由层。于是可以定义映射：
    $
      Nm_(f_U): f_(U,*) cal(O)_(X_U)^times -> cal(O)_U^times
    $
    它的整体截面给出 $Nm_f: f_* GG_(m,X) (U) -> GG_(m,Y) (U)$。为说明它与限制相容，对光滑曲线 $V, U in Et_Y$ 之间的平展态射 $V -> U$，需要证明下面的图表交换：
    // https://q.uiver.app/#r=typst&q=WzAsNCxbMCwwLCJjYWwoTylfKFhfVikgKFhfVikiXSxbMSwwLCJjYWwoTylfViAoVikiXSxbMCwxLCJjYWwoTylfKFhfVSkgKFhfVSkiXSxbMSwxLCJjYWwoTylfVSAoVSkiXSxbMCwxLCJObV8oZl9WKSJdLFsyLDMsIk5tXyhmX1UpIl0sWzMsMV0sWzIsMF1d
    #align(center, diagram({
      node((0, 0), [$cal(O)_(X_V) (X_V)$])
      node((1, 0), [$cal(O)_V (V)$])
      node((0, 1), [$cal(O)_(X_U) (X_U)$])
      node((1, 1), [$cal(O)_U (U)$])
      edge((0, 0), (1, 0), [$Nm_(f_V)$], label-side: left, "->")
      edge((0, 1), (1, 1), [$Nm_(f_U)$], label-side: right, "->")
      edge((1, 1), (1, 0), "->")
      edge((0, 1), (0, 0), "->")
    }))
    这可以局部地检查：把 $U, V$ 换成各自的仿射开集即可。因此不妨设 $U, V$ 仿射。于是问题归结为证明：给定秩为 $r$ 的有限局部自由 $A$-代数 $B$，对任意 $A$-代数 $A'$（$B' = B' otimes_A A'$），下图交换：
    // https://q.uiver.app/#r=typst&q=WzAsNCxbMCwwLCJCJyJdLFswLDEsIkIiXSxbMSwxLCJBIl0sWzEsMCwiQSciXSxbMSwwXSxbMiwzXSxbMSwyLCJObSIsMl0sWzAsMywiTm0iXV0=
    #align(center, diagram({
      node((0, 0), [$B'$])
      node((0, 1), [$B$])
      node((1, 1), [$A$])
      node((1, 0), [$A'$])
      edge((0, 1), (0, 0), "->")
      edge((1, 1), (1, 0), "->")
      edge((0, 1), (1, 1), [$Nm$], label-side: right, "->")
      edge((0, 0), (1, 0), [$Nm$], label-side: left, "->")
    }))
    这是显然的。

    最后，只需证明 $Nm_f: f_* GG_(m,X) -> GG_(m,Y)$ 在 $H^1$ 上诱导 $Nm_f: Pic(X) -> Pic(Y)$。由于 $GG_m$ 的 $H^1_et$ 与 $H^1_#[Zar]$ 典范同构，只需证明：
    $
      Nm_f: f_* cal(O)_X^times -> cal(O)_Y^times
    $
    经由 $H^1_#[Zar]$ 诱导 $Nm_f: Pic(X) -> Pic(Y)$。

    - 任意 $cal(L) in Pic(X)$ 都可以用 $X$ 的一个 Zariski 覆盖来平凡化，而这个覆盖来自 $Y$ 的某个 Zariski 覆盖。

      事实上，对任意 $y in abs(Y)$，$X times_Y Spec(cal(O)_(Y,y)) = Spec(B_y)$ 是 Dedekind 整环，特别地是唯一分解整环，故其类群平凡。因此线丛 $cal(L)|_(X times_Y Spec(cal(O)_(Y,y)))$ 必然平凡。由铺开，存在 Zariski 开集 $V subset Y$，使得 $cal(L)|_(f^(-1)(V))$ 平凡。

      因此可以取 $Y$ 的 Zariski 覆盖 ${Y_i}$，基变换得到 $X$ 的覆盖 ${X_i}$，并配有同构 $phi_i: cal(L)|_(X_i) -> cal(O)_(X_i)$。由此得到截面 $s_(i,j) in cal(O)_(X_(i,j)) (X_(i,j))^times$，它们定义过渡映射：
      $
        phi_j compose phi_i^(-1): cal(O)_(X_(i,j)) -> cal(O)_(X_(i,j))
      $

    现在考虑：
    $
      Nm_f (cal(L)) = det(f_* cal(L)) otimes det(f_* cal(O)_X)^(otimes -1)
    $

    把 $f_*$ 作用于 $phi_i$，得到同构 $psi_i: f_* cal(L)|_(X_i) -> f_* cal(O)_(X_i)$；再取行列式，得到同构：
    $
      det(psi_i): det(f_* cal(L))|_(Y_i) -> det(f_* cal(O)_X)|_(Y_i)
    $
    即平凡化：
    $
      chi_i: Nm_f (cal(L))|_(Y_i) -> cal(O)_(Y_i)
    $
    于是需要比较重叠部分 $Y_(i,j)$ 上的平凡化。按定义，
    $
      phi_j = s_(i,j) compose phi_i: cal(L)_(X_(i,j)) -> cal(O)_(X_(i,j))
    $
    于是作用 $f_*$，
    $
      psi_j = f_* s_(i,j) compose psi_i: cal(L)_(X_(i,j)) -> cal(O)_(X_(i,j))
    $
    再取行列式，
    $
      det(psi_j) = det(f_* s_(i,j)) compose det(psi_i): det(f_* cal(L))|_(Y_(i,j)) -> det(f_* cal(O)_X)|_(Y_(i,j))
    $
    于是看到，给出映射 ${chi_i}$ 之间过渡的元素 $t_(i,j) in cal(O)_(Y_(i,j)) (Y_(i,j))^times$，恰好就是定义下面映射的那些元素：
    $
      det(f_* s_(i,j)): det(f_* cal(O)_X)|_(Y_(i,j)) -> det(f_* cal(O)_X)|_(Y_(i,j))
    $
    在 $f_* cal(O)_(X_(i,j))$ 上，$f_* s_(i,j)$ 就是局部自由 $cal(O)_(Y_(i,j))$-模 $f_* cal(O)_(X_(i,j))$ 上乘以元素 $s_(i,j)$ 的映射。因此按 $Nm_f$ 的定义，$det(f_* s_(i,j))$ 是乘以 $Nm_f (s_(i,j))$ 的映射。于是 $t_(i,j) = Nm_f (s_(i,j))$。这样我们就得到：
    $
      Nm_f: Pic(X) -> Pic(Y)
    $
    由 $Nm_f: f_* GG_(m,X) -> GG_(m,Y)$ 诱导。
  ]

  回忆我们要证明的是下面图表的交换性：
  #align(center, diagram({
    node((0, 0), [$H^2_c (U, mu_n)$])
    node((0, 1), [$H^2_c (U, mu_n)$])
    node((1, 0), [$H^2 (ol(U), mu_n)$])
    node((2, 0), [$Pic(ol(U))\/n Pic(ol(U))$])
    node((3, 0), [$ZZ\/n$])
    node((3, 1), [$ZZ\/n$])
    node((1, 1), [$H^2 (X, mu_n)$])
    node((2, 1), [$Pic(X)\/n Pic(X)$])
    edge((0, 0), (0, 1), "=")
    edge((3, 0), (3, 1), "=")
    edge((0, 0), (1, 0), [$Tr_(U\/ol(U))^compose$], label-side: left, "->")
    edge((1, 0), (2, 0), [$tilde$], label-side: left, "->")
    edge((2, 0), (3, 0), [$deg$], label-side: left, "->")
    edge((0, 1), (1, 1), [$Tr_(U\/X)^compose$], label-side: right, "->")
    edge((1, 1), (2, 1), [$tilde$], label-side: right, "->")
    edge((2, 1), (3, 1), [$deg$], label-side: right, "->")
  }))
  注意，利用 Kummer 序列，存在唯一的 $Nm_(ol(f)): ol(f)_* mu_n -> mu_n$ 使下面的图表交换：
  // https://q.uiver.app/#r=typst&q=WzAsMTAsWzAsMCwiMCJdLFsxLDAsIm9sKGYpXyogbXVfKG4sb2woVSkpIl0sWzIsMCwib2woZilfKiBHR18obSxvbChVKSkiXSxbMywwLCJvbChmKV8qIEdHXyhtLG9sKFUpKSJdLFs0LDAsIjAiXSxbMCwxLCIwIl0sWzEsMSwibXVfKG4sWCkiXSxbMiwxLCJHR18obSxYKSJdLFszLDEsIkdHXyhtLFgpIl0sWzQsMSwiMCJdLFswLDFdLFsxLDJdLFsyLDMsIigtKV5uIl0sWzMsNF0sWzUsNl0sWzYsN10sWzcsOCwiKC0pXm4iLDJdLFs4LDldLFsxLDYsIk5tXyhvbChmKSkiLDJdLFsyLDcsIk5tXyhvbChmKSkiXSxbMyw4LCJObV8ob2woZikpIl1d
  #align(center, diagram({
    node((0, 0), [$0$])
    node((1, 0), [$ol(f)_* mu_(n,ol(U))$])
    node((2, 0), [$ol(f)_* GG_(m,ol(U))$])
    node((3, 0), [$ol(f)_* GG_(m,ol(U))$])
    node((4, 0), [$0$])
    node((0, 1), [$0$])
    node((1, 1), [$mu_(n,X)$])
    node((2, 1), [$GG_(m,X)$])
    node((3, 1), [$GG_(m,X)$])
    node((4, 1), [$0$])
    edge((0, 0), (1, 0), "->")
    edge((1, 0), (2, 0), "->")
    edge((2, 0), (3, 0), [$(-)^n$], label-side: left, "->")
    edge((3, 0), (4, 0), "->")
    edge((0, 1), (1, 1), "->")
    edge((1, 1), (2, 1), "->")
    edge((2, 1), (3, 1), [$(-)^n$], label-side: right, "->")
    edge((3, 1), (4, 1), "->")
    edge((1, 0), (1, 1), [$Nm_(ol(f))$], label-side: right, "->")
    edge((2, 0), (2, 1), [$Nm_(ol(f))$], label-side: left, "->")
    edge((3, 0), (3, 1), [$Nm_(ol(f))$], label-side: left, "->")
  }))

  于是目标图表分解为：
  // https://q.uiver.app/#r=typst&q=WzAsOCxbMCwwLCJIXjJfYyAoVSwgbXVfbikiXSxbMCwxLCJIXjJfYyAoVSwgbXVfbikiXSxbMSwwLCJIXjIgKG9sKFUpLCBtdV9uKSJdLFsyLDAsIlBpYyhvbChVKSlcXC9uIFBpYyhvbChVKSkiXSxbMywwLCJaWlxcL24iXSxbMywxLCJaWlxcL24iXSxbMSwxLCJIXjIgKFgsIG11X24pIl0sWzIsMSwiUGljKFgpXFwvbiBQaWMoWCkiXSxbMCwxLCIiLDAseyJzdHlsZSI6eyJib2R5Ijp7Im5hbWUiOiJkb3VibGUgYmFycmVkIn19fV0sWzQsNSwiIiwwLHsic3R5bGUiOnsiYm9keSI6eyJuYW1lIjoiZG91YmxlIGJhcnJlZCJ9fX1dLFswLDIsIlRyXyhVXFwvb2woVSkpXmNvbXBvc2UiXSxbMiwzLCJ0aWxkZSJdLFszLDQsImRlZyJdLFsxLDYsIlRyXyhVXFwvWCleY29tcG9zZSIsMl0sWzYsNywidGlsZGUiLDJdLFs3LDUsImRlZyIsMl0sWzIsNiwiTm1fKG9sKGYpKSJdLFszLDcsIk5tXyhvbChmKSkiXV0=
  #align(center, diagram({
    node((0, 0), [$H^2_c (U, mu_n)$])
    node((0, 1), [$H^2_c (U, mu_n)$])
    node((1, 0), [$H^2 (ol(U), mu_n)$])
    node((2, 0), [$Pic(ol(U))\/n Pic(ol(U))$])
    node((3, 0), [$ZZ\/n$])
    node((3, 1), [$ZZ\/n$])
    node((1, 1), [$H^2 (X, mu_n)$])
    node((2, 1), [$Pic(X)\/n Pic(X)$])
    edge((0, 0), (0, 1), "=")
    edge((3, 0), (3, 1), "=")
    edge((0, 0), (1, 0), [$Tr_(U\/ol(U))^compose$], label-side: left, "->")
    edge((1, 0), (2, 0), [$tilde$], label-side: left, "->")
    edge((2, 0), (3, 0), [$deg$], label-side: left, "->")
    edge((0, 1), (1, 1), [$Tr_(U\/X)^compose$], label-side: right, "->")
    edge((1, 1), (2, 1), [$tilde$], label-side: right, "->")
    edge((2, 1), (3, 1), [$deg$], label-side: right, "->")
    edge((1, 0), (1, 1), [$Nm_(ol(f))$], label-side: left, "->")
    edge((2, 0), (2, 1), [$Nm_(ol(f))$], label-side: left, "->")
  }))

  现在：

  - 中间方块交换，因为两条 Kummer 序列连同 $Nm_(ol(f))$ 构成的图表交换；

  - 右方块交换，因为 $ol(f)_* (sum_(u in ol(U)) n_u u) = sum_(u in ol(U)) n_u ol(f)(u)$，所以在除子层面 $ol(f): Div(ol(U)) -> Div(X)$ 保持次数。于是 $Nm_(ol(f)): Pic(ol(U)) -> Pic(X)$ 保持次数。

  - 为证明左方块交换，只需证明复合
    $
      f_! mu_(n,U) cong ol(f)_* j_! mu_(n,U) -> ol(f)_* mu_(n,ol(U)) ->^(Nm_(ol(f))) mu_n
    $
    恰好就是余单位映射 $f_! mu_(n,U) -> mu_n$。/*检查茎，只需证明 $Nm_(ol(f)): ol(f)_* mu_(n,ol(U)) -> mu_(n,X)$ 在 $x in abs(X)$ 处的茎是：
    $
      oplus.big_(u in ol(f)^(-1)(x)) mu_n -> mu_n
    $
    即逐因子作乘积。为此需要证明 $Nm_(ol(f)): ol(f)_* GG_(m,ol(U)) -> GG_(m,X)$ 在 $x in abs(X)$ 处的茎是：
    $
      oplus.big_(u in ol(f)^(-1)(x)) (cal(O)_(ol(U),u)^#[sh])^times -> (cal(O)_(X,x)^#[sh])^times
    $ 
    逐因子作乘积。*/

    #lemma[
      设 $f: X -> Y$ 是代数闭域 $k$ 上光滑射影曲线之间的有限态射，它自动是次数为 $r$ 的平坦态射。则 $Nm_f: f_* GG_(m,X) -> GG_(m,Y)$ 在 $y in abs(Y)$ 处的茎可等同于：
      $
        oplus.big_(x in f^(-1)(y)) (cal(O)_(X,x)^#[sh])^times -> (cal(O)_(Y,y)^#[sh])^times, (a_x)_x |-> product_(x in f^(-1)(y)) Nm_(cal(O)_(X,x)^#[sh]\/cal(O)_(Y,y)^#[sh]) (a_x)
      $ 
      其中 $cal(O)_(X,x)^#[sh]\/cal(O)_(Y,y)^#[sh]$ 是 DVR 的扩张。（这里 $X$ 与 $Y$ 的闭点剩余域都是代数闭的，因而自动是几何点。）
    ]
    #proof[
      考虑范数映射：
      $
        Nm_f: f_* cal(O)_X -> cal(O)_Y
      $
      即 $cal(O)_Y$ 上局部自由层 $f_* cal(O)_X$ 的范数映射。局部地，这个构造就是局部自由有限 $A$-代数 $B$ 的 $Nm_(B\/A): B -> A$，并且在 $A$ 的任意基变换以及 $A$ 的极限下保持不变。于是对 $y in Y$ 的所有仿射平展邻域取极限，$Nm_f: f_* GG_(m,X) -> GG_(m,Y)$ 在 $y$ 处的茎是：
      $
        Nm: Gamma(X times_Y tilde(Y)_y, cal(O)_(X times_Y tilde(Y)_y))^times -> (cal(O)_(Y,y)^#[sh])^times
      $
      由 @strict-henselization-and-finite-base-change，因 $f$ 有限，$X times_Y tilde(Y)_y = union.sq.big_(x in f^(-1)(y)) tilde(X)_x$，其中每个 $cal(O)_(X,x)^#[sh]\/cal(O)_(Y,y)^#[sh]$ 都是 DVR 的扩张。因此上面的范数可等同于：
      $
        oplus.big_(x in f^(-1)(y)) (cal(O)_(X,x)^#[sh])^times -> (cal(O)_(Y,y)^#[sh])^times, (a_x)_x |-> product_(x in f^(-1)(y)) Nm_(cal(O)_(X,x)^#[sh]\/cal(O)_(Y,y)^#[sh]) (a_x)
      $
      引理得证。
    ]
    于是由前一引理，$Nm_(ol(f)): ol(f)_* mu_(n,ol(U)) -> mu_(n,X)$ 在 $x in abs(X)$ 处的茎等同于：
    $
      oplus.big_(u in ol(f)^(-1)(x)) mu_n -> mu_n, (a_u)_u |-> product_(u in ol(f)^(-1)(x)) a_u^(r_u)
    $
    其中 $r_u := "rk"_(cal(O)_(X,x)^#[sh]) (cal(O)_(ol(U),u)^#[sh])$。现在检查复合：
    $
      f_! mu_(n,U) cong ol(f)_* j_! mu_(n,U) -> ol(f)_* mu_(n,ol(U)) ->^(Nm_(ol(f))) mu_(n,X)
    $
    在 $x in abs(X)$ 处的茎。它是：
    $
      oplus.big_(u in f^(-1)(x)) mu_n cong oplus.big_(u in ol(f)^(-1)(x) \ u in U) mu_n -> oplus.big_(u in ol(f)^(-1)(x)) mu_n -> mu_n
    $
    其中第一个映射把缺失的分量补为 1，第二个映射是 $Nm_(ol(f))$ 在茎上的映射。于是如上所述，这个复合是：
    $
      (a_u)_(u in f^(-1)(x)) &|-> (a'_u)_(u in ol(f)^(-1)(x)) #[其中] a'_u = cases(a_u &\, u in abs(U), 1 &\, u in ol(U) - U) \
      &|-> product_(u in ol(f)^(-1)(x)) (a'_u)^(r_u) \
      &= product_(u in f^(-1)(x)) a_u^(r_u) #[因为当 $u in ol(U) - U$ 时 $a'_u = 1$] \
      &= product_(u in f^(-1)(x)) a_u
    $
    其中最后一步用了：$f: U -> X$ 平展，故 $cal(O)_(U,u)^#[sh] = cal(O)_(X,x)^#[sh]$，从而每个 $r_u = 1$。这正是余单位 $f_! mu_(n,U) -> mu_(n,X)$ 在茎上的表现。

    于是左方块交换，证明完成。
]

#lemma(name: <pd-trace-curve-affine-compat>)[
  设 $p: AA^1_k -> Spec(k)$，其中 $k$ 是代数闭域。则：
  $
    Tr^tilde_(AA^1_k\/k) = Tr^square_(AA^1_k\/k)
  $
]
#proof[
  按定义，$Tr^tilde_(AA^1_k\/k)$ 是：
  $
    H^2_c (AA^1_k, mu_n) ->^tilde H^2 (PP^1_k, mu_n) cong Pic(PP^1_k)\/n Pic(PP^1_k) -->^deg_tilde ZZ\/n
  $
  注意 $deg(cal(O)(1)) = 1$，故 $H^2 (PP^1_k, mu_n) -> Pic(PP^1_k)\/n Pic(PP^1_k) ->^deg ZZ\/n$ 恰好是下面映射的逆：
  $
    alpha_k: ZZ\/n ->^(cal(O)(1)) Pic(PP^1_k)\/n Pic(PP^1_k) -> H^2 (PP^1_k, mu_n)
  $
  因此按 $Tr_(AA^1_k\/k)^square$ 的定义，$Tr^tilde_(AA^1_k\/k) = Tr^square_(AA^1_k\/k)$。
]

#lemma(name: <pd-trace-etale-affine-compat>)[
  设 $f: X -> Y$ 是相对维数为 $d$ 的分离光滑态射。一列整体截面 $s_1, dots.c, s_d in cal(O)_X (X)$ 等价于一个映射 $j_(s_1,dots.c,s_d): X -> AA^d_Y$。
  
  设两列整体截面 $s_i, s'_i in cal(O)_X (X)$ 都定义平展态射 $j_(s_1,dots.c,s_d), j_(s'_1,dots.c,s'_d): X -> AA^d_Y$。则：
  $
    Tr^square_(AA^d_Y\/Y) diamond.small Tr^compose_(j_(s_1,dots.c,s_d)) = Tr^square_(AA^d_Y\/Y) diamond.small Tr^compose_(j_(s'_1,dots.c,s'_d))
  $
]
#proof[
  首先注意，这个问题对 $x$ 是 Zariski 局部的。
  
  - 事实上，假设对任意 $x in X$，都存在 $x$ 的 Zariski 邻域 $U -> X$，使得：
    $
      Tr^square_(AA^d_Y\/Y) diamond.small Tr^compose_(j_(s_1|_U,dots.c,s_d|_U)) = Tr^square_(AA^d_Y\/Y) diamond.small Tr^compose_(j_(s'_1|_U,dots.c,s'_d|_U))
    $
    注意 $j_(s_1|_U,dots.c,s_d|_U): U -> AA^d_k$ 正是复合：
    $
      U -> X -->^(j_(s_1,dots.c,s_d)) AA^d_k
    $
    带撇的版本同理。由于 $Tr^compose$ 与复合相容，
    $
      Tr^square_(AA^d_Y\/Y) diamond.small Tr^compose_(j_(s_1,dots.c,s_d)) diamond.small Tr^compose_(U\/X) = Tr^square_(AA^d_Y\/Y) diamond.small Tr^compose_(j_(s'_1,dots.c,s'_d)) diamond.small Tr^compose_(U\/X)
    $
    把这样得到的开覆盖取不交并，便得到满射平展的 $ell: U -> X$，使上述关系成立。现在：
    $
      Tr_(U\/X)^compose: R^(2d) f_! ell_! mu_n^(otimes d) -> R^(2d) f_! mu_n^(otimes d) 
    $
    是满射，因为 $ell_! mu_n^(otimes d) -> mu_n^(otimes d)$ 是满射，且由 Grothendieck 消没 $R^(2d) f_!$ 右正合。因此可以在 $Tr^square_(AA^d_Y\/Y) diamond.small Tr^compose_(j_(s_1,dots.c,s_d)) diamond.small Tr^compose_(U\/X) = Tr^square_(AA^d_Y\/Y) diamond.small Tr^compose_(j_(s'_1,dots.c,s'_d)) diamond.small Tr^compose_(U\/X)$ 两端同时右约去 $Tr_(U\/X)^compose$，得到：
    $
      Tr^square_(AA^d_Y\/Y) diamond.small Tr^compose_(j_(s_1,dots.c,s_d)) = Tr^square_(AA^d_Y\/Y) diamond.small Tr^compose_(j_(s'_1,dots.c,s'_d))
    $

  其次，由与基变换相容，不妨设 $Y = Spec(k)$，$k$ 代数闭。于是固定闭点 $x in abs(X)$，只需证明存在 Zariski 开集 $x in U subset X$，使得：
  $
    Tr^square_(AA^d_k\/k) diamond.small Tr^compose_(j_(s_1|_U,dots.c,s_d|_U)) = Tr^square_(AA^d_k\/k) diamond.small Tr^compose_(j_(s'_1|_U,dots.c,s'_d|_U))
  $

  观察到：

  + 注意对置换 $sigma in S_d$，
    $
      Tr^square_(AA^d_k\/k) diamond.small Tr^compose_(j_(s_1,dots.c,s_d)) =  Tr^square_(AA^d_k\/k) diamond.small Tr^compose_(j_(s_(sigma(1)),dots.c,s_(sigma(d))))
    $
    事实上，把 $sigma$ 看作自同构 $phi_sigma: AA^d_k -> AA^d_k, (x_1, dots.c, x_d) |-> (x_(sigma(1)), dots.c, x_(sigma(d)))$，就有：
    $
      j_(s_1,dots.c,s_d) compose phi_sigma = j_(s_(sigma(1)),dots.c,s_(sigma(d)))
    $
    于是，
    $
      Tr^square_(AA^d_k\/k) diamond.small Tr^compose_(j_(s_1,dots.c,s_d)) =  Tr^square_(AA^d_k\/k) diamond.small Tr^compose_(phi_sigma) diamond.small Tr^compose_(j_(s_(sigma(1)),dots.c,s_(sigma(d))))
    $
    而由 @pd-trace-affine-constr，$Tr^square_(AA^d_k\/k) = Tr^square_(AA^d_k\/k) diamond.small Tr^compose_(phi_sigma)$。

  + /*注意，对 $c_1, dots.c, c_d in k$，有#h(1fr)
    $
      Tr^square_(AA^d_k\/k) diamond.small Tr^compose_(j_(s_1,dots.c,s_d)) = Tr^square_(AA^d_k\/k) diamond.small Tr^compose_(j_(s_1-c_1,dots.c,s_d-c_d))
    $
    事实上，只要每次只对一个截面作平移，就可设我们只对某个单个的 $i$ 把 $s_i$ 换成 $s_i - c_i$。由上一小点的置换不变性，不妨设 $i=d$，即我们改动的是最后一项。 */
    假设对所有 $i!=i_0$ 都有 $s_i = s'_i$，即两列截面只相差一个元素。由 (1) 中的置换不变性，不妨设 $i_0 = d$，即两列截面只在最后一个元素处不同。
    
    令 $pi_d: AA^d_k -> AA^(d-1)_k$ 为到前 $(d-1)$ 个分量的投影，于是：
    $
      pi_d compose j_(s_1,dots.c,s_(d-1),s_d) = j_(s_1,dots.c,s_(d-1)) = pi_d compose j_(s_1,dots.c,s_(d-1),s'_d)
    $
    由 @pd-trace-affine-constr，
    $
      Tr^square_(AA^d_k\/k) diamond.small Tr^compose_(j_(s_1,dots.c,s_d)) = Tr^square_(AA^(d-1)_k\/k) diamond.small Tr^square_(AA^d_k\/AA^(d-1)_k) diamond.small Tr^compose_(j_(s_1,dots.c,s_(d-1),s_d)) \
      Tr^square_(AA^d_k\/k) diamond.small Tr^compose_(j_(s_1,dots.c,s'_d)) = Tr^square_(AA^(d-1)_k\/k) diamond.small Tr^square_(AA^d_k\/AA^(d-1)_k) diamond.small Tr^compose_(j_(s_1,dots.c,s_(d-1),s'_d))
    $
    因此只需证明 $Tr^square_(AA^d_k\/AA^(d-1)_k) diamond.small Tr^compose_(j_(s_1,dots.c,s_(d-1),s_d)) = Tr^square_(AA^d_k\/AA^(d-1)_k) diamond.small Tr^compose_(j_(s_1,dots.c,s_(d-1),s'_d))$。作基变换到茎上，只需证明：

    - 设 $K$ 是代数闭域，$j, j': U -> AA^1_K$ 是平展态射，且对 $p_1: AA^1_K -> Spec(K)$ 有 $g = p_1 compose j = p_1 compose j': U -> Spec(K)$。则：#h(1fr)
      $
        Tr^square_(AA^1_K\/K) diamond.small Tr^compose_j = Tr^square_(AA^1_K\/K) diamond.small Tr^compose_(j')
      $
      此时 $U$ 在 $K$ 上分离光滑、相对维数为 $1$，因而是光滑曲线的不交并。把 $U$ 换成一个连通分支，不妨设 $U$ 是 $K$ 上的光滑曲线。于是由 @pd-trace-curve-affine-compat，更重要的是由 @pd-trace-etale-curve-compat，
      $
        Tr^square_(AA^1_K\/K) diamond.small Tr^compose_j = Tr^tilde_(AA^1_K\/K) diamond.small Tr^compose_j = Tr^tilde_(g:U\/K) \
        
        Tr^square_(AA^1_K\/K) diamond.small Tr^compose_(j') = Tr^tilde_(AA^1_K\/K) diamond.small Tr^compose_(j') = Tr^tilde_(g:U\/K)
      $
      两者相等。

  现在由观察 (2)，可把 $s_i$ 换成 $s_i - (s_i mod frak(m)_x in k)$，从而假设每个 $s_i in frak(m)_x$，$s'_i$ 也照此处理。这些对截面的修改相当于把 $j_(s_1,dots.c,s_d)$ 与一个平移 $AA^d_k -> AA^d_k$ 复合，不影响平展性，所以观察 (2) 确实适用。
  
  为此先建立一条引理：

  #lemma[
    设 $k$ 是代数闭域，$X -> Spec(k)$ 分离光滑、相对维数为 $d$，等价地，$X$ 正则。对闭点 $x in abs(X)$，设整体截面 $s_1, dots.c, s_d in cal(O)_X (X)$ 都在 $frak(m)_x cal(O)_(X,x)$ 中。则它们定义的、把 $x$ 送到 $0$ 的映射 $j_(s_1,dots.c,s_d): X -> AA^d_k$ 在 $x$ 处平展，当且仅当：
    $
      [s_1], dots.c, [s_d] in frak(m)_x\/frak(m)_x^2
    $ 
    构成 $d$ 维 $k$-向量空间 $frak(m)_x\/frak(m)_x^2$ 的一组基。
  ]
  #proof[
    所给条件等价于：
    $
      frak(m)_x = (s_1, dots.c, s_d) cal(O)_(X,x)
    $
    这用的是 Nakayama 引理。

    （$==>$）由于 $j_(s_1,dots.c,s_d)$ 平展，$frak(m)_x = frak(m)_0 cal(O)_(X,x) = (s_1, dots.c, s_d) cal(O)_(X,x)$。

    （$<==$）设：
    $
      frak(m)_x = (s_1, dots.c, s_d) cal(O)_(X,x) = frak(m)_0 cal(O)_(X,x)
    $
    注意 $x in X$ 与 $0 in AA^d_k$ 的剩余域都是 $k$。因此 $j_(s_1,dots.c,s_d)$ 在 $x$ 处非分歧。要证它在 $x$ 处平展，只需证明它在 $x$ 处平坦。由奇迹平坦性，只需证明：
    $
      dim(cal(O)_(X,x)) = dim(cal(O)_(AA^d_k,0)) + dim(cal(O)_(X_0,x))
    $
    因此只需证明 $dim(cal(O)_(X_0,x)) = 0$，即 $x$ 是其纤维的孤立点。事实上，$cal(O)_(X_0,x) = cal(O)_(X,x)\/(s_1,dots.c,s_d) cal(O)_(X,x) = cal(O)_(X,x)\/frak(m)_x = k$ 是零维的。
  ]

  现在，由于 $j_(s_1,dots.c,s_d)$ 与带撇的版本都平展，$[s_1], dots.c, [s_d]$ 与 $[s'_1], dots.c, [s'_d]$ 是 $d$ 维 $k$-向量空间 $frak(m)_x\/frak(m)_x^2$ 的两组基。由线性代数，存在有限的一串基：
  $
    [s_1^((t))], dots.c, [s_d^((t))] in frak(m)_x\/frak(m)_x^2, 0 <= t <= T
  $
  使得：

  - $[s_i^((0))] = [s_i], [s_i^((T))] = [s'_i]$；

  - 对每个 $1<=t<=T$，$[s_1^((t-1))], dots.c, [s_d^((t-1))]$ 与 $[s_1^((t))], dots.c, [s_d^((t))]$ 恰有一个元素不同。

  现在把它们提升为截面 $s_i^((t)), 0 <= t <= T + d$，办法如下：

  - 取 $s_i^((0)) = s_i$；

  - 对任意 $1<=t<=T$，设 $s_i^((t-1))$ 已定义，令 $i_t$ 是唯一使得 $[s_(i_t)^((t))] != [s_(i_t)^((t-1))]$ 的指标。然后取：
    $
      s_i^((t)) = cases(
        s_i^((t-1)) &\, i != i_t, 
        #[$[s_i^((t))]$ 在 $frak(m)_x$ 中的任意提升] &\, i = i_t
      )
    $

  - 对 $t = T + alpha, 1 <= alpha <= T$，取：
    $
      s_i^((T+alpha)) = cases(
        s_i^((T)) &\, i > alpha, 
        s'_i &\, i <= alpha
      )
    $
    于是所有 $[s_i^((T+alpha))] = [s_i^((T))] = [s'_i]$。

  那么这一串截面列 $s_i^((t)) in frak(m)_x, 0 <= t <= T+d$ 具有下面的性质：
  
  - 对每个 $t$，$[s_1^((t))], dots.c, [s_d^((t))] in frak(m)_x\/frak(m)_x^2$ 是一组基；

  - $s_i^((0)) = s_i, s_i^((T+d)) = s'_i$；

  - 对每个 $1<=t<=T$，$s_1^((t-1)), dots.c, s_d^((t-1))$ 与 $s_1^((t)), dots.c, s_d^((t))$ 至多有一个元素不同。

  由前一引理，每个 $j_(s_1^((t)), dots.c, s_d^((t))): X -> AA^d_k$ 都在 $x$ 处平展。平展点构成开集，故把 $X$ 换成 $x$ 附近合适的 Zariski 开集，不妨设每个 $j_(s_1^((t)), dots.c, s_d^((t))): X -> AA^d_k$ 都平展。现在由观察 (2) 以及 $s_1^((t-1)), dots.c, s_d^((t-1))$ 与 $s_1^((t)), dots.c, s_d^((t))$ 至多相差一个元素，
  $
    Tr^square_(AA^d_k\/k) diamond.small Tr^compose_(j_(s_1^((t-1)),dots.c,s_d^((t-1)))) = Tr^square_(AA^d_k\/k) diamond.small Tr^compose_(j_(s_1^((t)),dots.c,s_d^((t)))), forall 1<=t<=T+d
  $
  把这些等式串起来，即得：
  $
    Tr^square_(AA^d_k\/k) diamond.small Tr^compose_(j_(s_1,dots.c,s_d)) = Tr^square_(AA^d_k\/k) diamond.small Tr^compose_(j_(s'_1,dots.c,s'_d))
  $
]

作为推论，现在可以在那些允许分解 $X -> AA^d_Y -> Y$（其中第一个映射平展）的分离光滑态射 $X -> Y$ 上定义一族迹映射。

#proposition(name: <pd-trace-1>)[
  在分离光滑态射构成的族 $cal(S)^((1))$ 上存在一族类迹映射 ${Tr^((1))_(X\/Y)}$，其定义如下：
  $
    cal(S)^((1)) = {&f:X -> Y #[相对维数为 $d$ 的分离光滑态射]\
    &: #[$X,Y$ 是 Noether 的 $ZZ[n^(-1)]$-概形，$f$ 分解为 $X ->^j AA^d_Y -> Y$，其中 $j: X -> AA^d_Y$ 平展]}
  $
  这里平展态射 $j$ 自动分离。这族类迹映射构造为：
  $
    Tr_(X\/Y)^((1)) := Tr_(AA^d_Y\/Y)^square diamond.small Tr_j^compose
  $
  其中 $f: X ->^j AA^d_Y -> Y$ 是分解，$j$ 平展。此外，

  0. ${Tr^((1))_(X\/Y)}_((f:X->Y) in cal(S)^((1)))$ 与复合、基变换相容；

  + 对分离平展的 $X -> Y$，有#h(1fr)
    $
      Tr_(X\/Y)^((1)) = Tr_(X\/Y)^compose
    $
]
#proof[
  $
    Tr_(X\/Y)^((1)) := Tr_(AA^d_Y\/Y)^square diamond.small Tr_j^compose
  $
  按 @pd-trace-etale-affine-compat，这个定义是良定的（即不依赖分解 $X ->^j AA^d_Y -> Y$）。(1) 由定义自动成立，与基变换的相容性则由 $Tr^square$ 与 $Tr^compose$ 的相应性质推出。

  为证明与复合相容，设 $f: X -> Y, g: Y -> Z$ 都在 $cal(S)^((1))$ 中，分解为：
  $
    f: X ->^j AA^d_Y -> Y, g: Y ->^ell AA^e_Z -> Z
  $
  其中 $j,ell$ 平展。则 $g compose f$ 分解为：
  $
    X ->^q AA^(d+e)_Z -> Z
  $
  其中 $q: X ->^j AA^d_Y ->^(ell_d) AA^(d+e)_Z$ 平展。于是由 $Tr^square$ 与 $Tr^compose$ 和复合相容这一点：
  $
    Tr^((1))_g diamond.small Tr^((1))_f = Tr^square_(AA^e_Z\/Z) diamond.small Tr^compose_ell diamond.small Tr^square_(AA^d_Y\/Y) diamond.small Tr^square_j \

    Tr^((1))_(g compose f) = Tr^square_(AA^e_Z\/Z) diamond.small Tr^square_(AA^(d+e)_Z\/AA^e_Z) diamond.small Tr^compose_(ell_d) diamond.small Tr^square_j
  $
  因此只需证明：
  $
    Tr^compose_ell diamond.small Tr^square_(AA^d_Y\/Y) = Tr^square_(AA^(d+e)_Z\/AA^e_Z) diamond.small Tr^compose_(ell_d)
  $
  其中 $ell: Y -> AA^e_Z$ 平展，$ell_d: AA^d_Y -> AA^(d+e)_Z$ 是它沿投影 $AA^(d+e)_Z -> AA^e_Z$（到前 $e$ 个坐标）的基变换。假设 $d=1$ 的情形已经证明。由分解
  $
    Tr^square_(AA^d_Y\/Y) = Tr^square_(AA^d_Y\/AA^(d-1)_Y) diamond.small dots.c diamond.small Tr^square_(AA^1_Y\/Y)
  $
  并按 $d=1$ 的情形逐步交换，即得一般情形。于是不妨设 $d=1$，目标化为证明：
  $
    Tr^compose_ell diamond.small Tr^square_(AA^1_Y\/Y) = Tr^square_(AA^(e+1)_Z\/AA^e_Z) diamond.small Tr^compose_(ell_1)
  $
  基变换到代数闭几何点 $Spec(K) -> AA^e_Z$，此时 $ell: Y -> Spec(K)$ 成为有限个 $Spec(K)$ 的不交并。于是只需证明：
  $
    Tr^compose_ell diamond.small Tr^square_(AA^1_Y\/Y) = Tr^square_(AA^1_K\/K) diamond.small Tr^compose_(Y\/K)
  $ 
  事实上，在 $Y$ 的每个连通分支 $Spec(K)$ 上，两边都是 $Tr^square_(AA^1_K\/K)$。至此完成。
]

现在可以把 ${Tr^((1))_(X\/Y)}$ 粘起来，最终得到迹映射。

#theorem(name: <existence-of-trace-map>)[
  在 Noether 的 $ZZ[n^(-1)]$-概形之间纯相对维数的所有分离光滑态射构成的族上，存在唯一的族 ${Tr_(X\/Y)}$，满足：

  0. ${Tr_(X\/Y)}$ 与基变换、复合相容；

  + 对分离平展的 $f: X -> Y$（即相对维数为 0 的光滑态射），有#h(1fr)
    $
      Tr_(X\/Y) = Tr_(X\/Y)^compose
    $

  + 设 $f: X -> Spec(k)$ 是代数闭域 $k$ 上的光滑曲线，则
    $
      Tr_(X\/k) = Tr_(X\/k)^tilde
    $ 

  + 对任意 $d$，
    $
      Tr_(AA^d_Y\/Y) = Tr_(AA^d_Y\/Y)^square
    $

  // + 若 $X -> Y$ 分离光滑、相对维数为 $d$，且几何纤维非空连通，则 $Tr_(X\/Y): R^(2d) f_! mu_(n,X)^(otimes d) -> ul(ZZ\/n)_Y$ 是同构。
]
#proof[
  唯一性由 @pd-trace-uniqueness 得到，故只证存在性。

  任取 Noether 的 $ZZ[n^(-1)]$-概形之间相对维数为 $d$ 的分离光滑态射 $f: X -> Y$。由光滑态射的局部结构，对 $X$ 的每个几何点 $ol(x)$，都有平展邻域 $(U, ol(u)) -> (X, ol(x))$（事实上取 Zariski 邻域即可），使得 $U -> Y$ 分解为 $U ->^j AA^d_Y -> Y$，其中 $j$ 平展。于是取有限子覆盖并把选出的 $U$ 取不交并，就得到满射平展映射 $q: X' -> X$，使得 $f compose q: X' -> Y$ 分解为 $X' ->^j AA^d_Y -> Y$。令 $X'' = X' times_X X'$，$q': X'' -> X$ 为诱导映射，$q_1, q_2: X'' -> X'$ 为两个投影。作相应的基变换。

  注意对 $X$ 上的任意层 $cal(F)$，都有右正合列：
  $
    q'_! q'^(-1) cal(F) -->^(Tr^compose_(q_1) - Tr^compose_(q_2)) q_! q^(-1) cal(F) -->^(Tr^compose_q) cal(F) -> 0
  $
  这既可在茎上检查，也可通过作用 $Hom(-, cal(G))$ 并用 Yoneda 引理来检查。作用 $R^(2d)f_!$ 后仍右正合，因为由 Grothendieck 消没 $R^(2d) f_!$ 右正合。于是得到交换图表：
  // https://q.uiver.app/#r=typst&q=WzAsOCxbMCwwLCJxJ18hIFJeKDJkKSBmXyEgbXVfbl4ob3RpbWVzIGQpIl0sWzEsMCwicV8hIFJeKDJkKSBmXyEgbXVfbl4ob3RpbWVzIGQpIl0sWzIsMCwiUl4oMmQpIGZfISBtdV9uXihvdGltZXMgZCkiXSxbMSwxLCJ1bChaWlxcL24pIl0sWzAsMSwidWwoWlpcXC9uKSJdLFsyLDEsInVsKFpaXFwvbikiXSxbMywwLCIwIl0sWzMsMSwiMCJdLFswLDEsIlRyXmNvbXBvc2VfKHFfMSkgLSBUcl5jb21wb3NlXyhxXzIpIl0sWzQsMywiMCIsMl0sWzMsNSwiIiwyLHsic3R5bGUiOnsiYm9keSI6eyJuYW1lIjoiZG91YmxlIGJhcnJlZCJ9fX1dLFs1LDddLFsxLDIsIlRyXmNvbXBvc2VfcSJdLFsyLDZdLFswLDQsIlRyXigoMSkpXyhYJydcXC9ZKSIsMl0sWzEsMywiVHJeKCgxKSlfKFgnXFwvWSkiXV0=
  #align(center, diagram({
    node((0, 0), [$R^(2d) f_! q'_! mu_n^(otimes d)$])
    node((1, 0), [$R^(2d) f_! q_! mu_n^(otimes d)$])
    node((2, 0), [$R^(2d) f_! mu_n^(otimes d)$])
    node((1, 1), [$ul(ZZ\/n)$])
    node((0, 1), [$ul(ZZ\/n)$])
    node((2, 1), [$ul(ZZ\/n)$])
    node((3, 0), [$0$])
    node((3, 1), [$0$])
    edge((0, 0), (1, 0), [$Tr^compose_(q_1) - Tr^compose_(q_2)$], label-side: left, "->")
    edge((0, 1), (1, 1), [$0$], label-side: right, "->")
    edge((1, 1), (2, 1), "=")
    edge((2, 1), (3, 1), "->")
    edge((1, 0), (2, 0), [$Tr^compose_q$], label-side: left, "->")
    edge((2, 0), (3, 0), "->")
    edge((0, 0), (0, 1), [$Tr^((1))_(X''\/Y)$], label-side: right, "->")
    edge((1, 0), (1, 1), [$Tr^((1))_(X'\/Y)$], label-side: left, "->")
  }, spacing: (4.5em, 3em)))
  其中左方块交换，因为：
  $
    Tr^((1))_(X'\/Y) diamond.small Tr^compose_(q_1) = Tr^((1))_(X''\/Y) = Tr^((1))_(X'\/Y) diamond.small Tr^compose_(q_2)
  $
  由追图，存在唯一的映射 $Tr^((q))_(X\/Y)$ 使下面的图表交换：
  // https://q.uiver.app/#r=typst&q=WzAsOCxbMCwwLCJxJ18hIFJeKDJkKSBmXyEgbXVfbl4ob3RpbWVzIGQpIl0sWzEsMCwicV8hIFJeKDJkKSBmXyEgbXVfbl4ob3RpbWVzIGQpIl0sWzIsMCwiUl4oMmQpIGZfISBtdV9uXihvdGltZXMgZCkiXSxbMSwxLCJ1bChaWlxcL24pIl0sWzAsMSwidWwoWlpcXC9uKSJdLFsyLDEsInVsKFpaXFwvbikiXSxbMywwLCIwIl0sWzMsMSwiMCJdLFswLDEsIlRyXmNvbXBvc2VfKHFfMSkgLSBUcl5jb21wb3NlXyhxXzIpIl0sWzQsMywiMCIsMl0sWzMsNSwiIiwyLHsic3R5bGUiOnsiYm9keSI6eyJuYW1lIjoiZG91YmxlIGJhcnJlZCJ9fX1dLFs1LDddLFsxLDIsIlRyXmNvbXBvc2VfcSJdLFsyLDZdLFswLDQsIlRyXigoMSkpXyhYJydcXC9ZKSIsMl0sWzEsMywiVHJeKCgxKSlfKFgnXFwvWSkiXSxbMiw1LCJUcl4oKHEpKV8oWFxcL1kpIl1d
  #align(center, diagram({
    node((0, 0), [$R^(2d) f_! q'_! mu_n^(otimes d)$])
    node((1, 0), [$R^(2d) f_! q_! mu_n^(otimes d)$])
    node((2, 0), [$R^(2d) f_! mu_n^(otimes d)$])
    node((1, 1), [$ul(ZZ\/n)$])
    node((0, 1), [$ul(ZZ\/n)$])
    node((2, 1), [$ul(ZZ\/n)$])
    node((3, 0), [$0$])
    node((3, 1), [$0$])
    edge((0, 0), (1, 0), [$Tr^compose_(q_1) - Tr^compose_(q_2)$], label-side: left, "->")
    edge((0, 1), (1, 1), [$0$], label-side: right, "->")
    edge((1, 1), (2, 1), "=")
    edge((2, 1), (3, 1), "->")
    edge((1, 0), (2, 0), [$Tr^compose_q$], label-side: left, "->")
    edge((2, 0), (3, 0), "->")
    edge((0, 0), (0, 1), [$Tr^((1))_(X''\/Y)$], label-side: right, "->")
    edge((1, 0), (1, 1), [$Tr^((1))_(X'\/Y)$], label-side: left, "->")
    edge((2, 0), (2, 1), [$Tr^((q))_(X\/Y)$], label-side: left, "-->")
  }))
  换言之，存在唯一的类迹映射 $Tr^((q))_(X\/Y)$，使得：
  $
    Tr^((1))_(X'\/Y) = Tr^((q))_(X\/Y) diamond.small Tr^compose_q
  $
  映射 $Tr^((q))_(X\/Y)$ 不依赖平展覆盖 $q$ 的选取。事实上：

  - 设另有平展覆盖 $tilde(q): tilde(X)' -> X$ 加细 $q: X' -> X$，即 $tilde(X)' ->^r X' ->^q X$。则 $f compose tilde(q) in cal(S)^((1))$，且：
    $
      Tr^((1))_(tilde(X)'\/Y) = Tr^((1))_(X'\/Y) diamond.small Tr^compose_(r:tilde(X)'\/X') = Tr^((q))_(X\/Y) diamond.small Tr^compose_q diamond.small Tr^compose_(r:tilde(X)'\/X') = Tr^((q))_(X\/Y) diamond.small Tr^compose_(tilde(q))
    $
    由唯一性，$Tr^((q))_(X\/Y) = Tr^((tilde(q)))_(X\/Y)$。

    对一般的两个不同平展覆盖 $q, tilde(q)'$，取它们的纤维积作为共同加细，再把 $Tr^((q))_(X\/Y), Tr^((tilde(q)))_(X\/Y)$ 都与这个共同加细比较即可。

  $Tr^((q))_(X\/Y)$ 既然不依赖 $q$ 的选取，就可以定义：
  $
    Tr_(X\/Y) := Tr^((q))_(X\/Y)
  $
  按定义，若 $(f: X -> Y) in cal(S)^((1))$，则 $Tr_(X\/Y) = Tr^((1))_(X\/Y)$。因此 (1) 与 (3) 自动成立。

  - 关于与基变换的相容性：设 $g: Y' -> Y$，$Y'$ 为 Noether 的，作拉回图表：#h(1fr)
    // https://q.uiver.app/#r=typst&q=WzAsNCxbMCwwLCJYJyJdLFsxLDAsIlknIl0sWzAsMSwiWCJdLFsxLDEsIlkiXSxbMiwzLCJmIiwyXSxbMCwxLCJmJyJdLFsxLDMsImciXSxbMCwyLCJnJyIsMl1d
    #align(center, diagram({
      node((0, 0), [$X'$])
      node((1, 0), [$Y'$])
      node((0, 1), [$X$])
      node((1, 1), [$Y$])
      node((0.3, 0.3), [$cart$])
      edge((0, 1), (1, 1), [$f$], label-side: right, "->")
      edge((0, 0), (1, 0), [$f'$], label-side: left, "->")
      edge((1, 0), (1, 1), [$g$], label-side: left, "->")
      edge((0, 0), (0, 1), [$g'$], label-side: right, "->")
    }))
    我们要证明 $Tr_(X'\/Y')$ 恰好是复合：
    $
      Phi: R^(2d) f'_! mu_n^(otimes d) -->^(BC^(-1)) g^(-1) R^(2d) f_! mu_n^(otimes d) -->^(Tr_(X\/Y)) ul(ZZ\/n)
    $
    事实上，取平展覆盖 $q: Z -> X$ 使 $f compose q in cal(S)^((1))$，再基变换到 $q': Z' -> X'$。则 $f' compose q' in cal(S)^((1))$。把等式 $Tr^((1))_(Z\/Y) = Tr_(X\/Y) diamond.small Tr_q^compose$ 作基变换，得到：
    $
      Tr^((1))_(Z'\/Y') = Phi diamond.small Tr_(q')^compose
    $
    由唯一性，$Phi = Tr_(X'\/Y')$。

  - 关于与复合的相容性：设 $f: X -> Y, g: Y -> Z$ 都是分离光滑态射，相对维数分别为 $d,e$。取平展覆盖 $r: tilde(X) -> X$、$q: Y' -> Y$，使 $f compose r, g compose q in cal(S)^((1))$。作下面的交换图表：
    // https://q.uiver.app/#r=typst&q=WzAsNyxbMSwxLCJYIl0sWzIsMSwiWSJdLFszLDEsIloiXSxbMiwwLCJZJyJdLFsxLDAsIlgnIl0sWzAsMSwidGlsZGUoWCkiXSxbMCwwLCJ0aWxkZShYKSciXSxbMCwxLCJmIiwyXSxbMSwyLCJnIiwyXSxbMywxLCJxIl0sWzUsMCwiciIsMl0sWzQsMywiZiciXSxbNiw0LCJyJyJdLFs0LDAsInEnIiwyXSxbNiw1LCJ0aWxkZShxJykiLDJdXQ==
    #align(center, diagram({
      node((0, 1), [$X$])
      node((1, 1), [$Y$])
      node((2, 1), [$Z$])
      node((1, 0), [$Y'$])
      node((0, 0), [$X'$])
      node((-1, 1), [$tilde(X)$])
      node((-1, 0), [$tilde(X)'$])
      node((-0.7, 0.3), $cart$)
      node((0.3, 0.3), $cart$)
      edge((0, 1), (1, 1), [$f$], label-side: right, "->")
      edge((1, 1), (2, 1), [$g$], label-side: right, "->")
      edge((1, 0), (1, 1), [$q$], label-side: left, "->")
      edge((-1, 1), (0, 1), [$r$], label-side: right, "->")
      edge((0, 0), (1, 0), [$f'$], label-side: left, "->")
      edge((-1, 0), (0, 0), [$r'$], label-side: left, "->")
      edge((0, 0), (0, 1), [$q'$], label-side: right, "->")
      edge((-1, 0), (-1, 1), [$tilde(q')$], label-side: right, "->")
    }))
    其中两个方块都是拉回。由于 $f compose r in cal(S)^((1))$，有 $f' compose r' in cal(S)^((1))$。又 $g compose q in cal(S)^((1))$，故：
    $
      g compose f compose r compose tilde(q)' = g compose q compose f' compose r' in cal(S)^((1))
    $
    于是 $r compose tilde(q'): tilde(X)' -> X$ 是 $X$ 的一个合适平展覆盖，可用于定义 $Tr_(X\/Z)$。$Tr_(X\/Z)$ 是下面等式中唯一的映射：
    $
      Tr_(tilde(X)'\/Z)^((1)) = Tr_(X\/Z) diamond.small Tr^compose_(r compose tilde(q')) = Tr_(X\/Z) diamond.small Tr^compose_(q' compose r') = Tr_(X\/Z) diamond.small Tr^compose_(q') diamond.small Tr^compose_(r')
    $
    另一方面：
    $
      Tr_(tilde(X)'\/Z)^((1)) = Tr_(Y'\/Z)^((1)) diamond.small Tr_(tilde(X)'\/Y')^((1)) = Tr_(Y\/Z) diamond.small Tr^compose_q diamond.small Tr_(X'\/Y') diamond.small Tr^compose_(r')
    $
    因此只需证明 $Tr^compose_q diamond.small Tr_(X'\/Y') diamond.small Tr^compose_(r') = Tr_(X\/Y) diamond.small Tr^compose_(q') diamond.small Tr^compose_(r')$。现在：
    $
      & Tr^compose_q diamond.small Tr_(X'\/Y') diamond.small Tr^compose_(r') \
      =& Tr^compose_q diamond.small Tr^((1))_(tilde(X)'\/Y') \
      =& Tr^((1))_(tilde(X)\/Y) diamond.small Tr^compose_(tilde(q')) \
      =& Tr_(X\/Y) diamond.small Tr^compose_r diamond.small Tr^compose_(tilde(q')) \
      =& Tr_(X\/Y) diamond.small Tr^compose_(q') diamond.small Tr^compose_(r')
    $
    至此完成了与复合相容性的证明。
  
  于是 (0) 得证。

  (2) 这个问题对 $X$ 是平展局部的。设 $X$ 有平展覆盖 ${j_i: U_i -> X}_i$，其中每个 $U_i$ 是光滑曲线，且 $Tr_(U_i\/k) = Tr^tilde_(U_i\/k)$。则由 @pd-trace-etale-curve-compat：
  $
    Tr^tilde_(X\/k) diamond.small Tr^compose_(U_i\/X) = Tr^tilde_(U_i\/k) = Tr_(U_i\/k) = Tr_(X\/k) diamond.small Tr^compose_(U_i\/X)
  $
  加细为有限子覆盖并令 $U = union.sq.big_i U_i$，即可看出存在满射平展态射 $U -> X$，使得：
  $
    Tr^tilde_(X\/k) diamond.small Tr^compose_(U\/X) = Tr_(X\/k) diamond.small Tr^compose_(U\/X)
  $
  如我们所见，对满射平展的 $U -> X$，$Tr^compose_(U\/X)$ 可以在 $diamond.small$ 的右边约去。因此 $Tr^tilde_(X\/k) = Tr_(X\/k)$。

  剩下要在 $X$ 上平展局部地证明这一点。对 $X$ 的任意几何点 $ol(x)$，取平展邻域 $(U, ol(u)) -> (X, ol(x))$，使 $U -> Spec(k)$ 属于 $cal(S)^((1))$。取 $U$ 的一个连通分支，不妨设 $U$ 是光滑曲线。取分解 $U ->^j AA^1_k -> Spec(k)$，于是：
  $
    Tr_(U\/k) = Tr^((1))_(U\/k) = Tr^square_(AA^1_k\/k) diamond.small Tr^compose_(U\/AA^1_k) = Tr^tilde_(AA^1_k\/k) diamond.small Tr^compose_(U\/AA^1_k) = Tr^tilde_(U\/k)
  $
  这里用了 @pd-trace-etale-curve-compat 与 @pd-trace-curve-affine-compat。至此完成。
]

现在可以把迹映射延拓到任意挠系数环。

#definition(name: <defn-tate-twists>)[
  设 $Lambda$ 是 $n$-挠系数环。把某个 $ZZ[n^(-1)]$-概形上的平展层 $Lambda$ 的*Tate 扭*定义为：
  $
    ul(Lambda)(m) = cases(
      Lambda otimes_(ZZ\/n) mu_n^(otimes m) &\, m > 0, 
      Lambda &\, m = 0, 
      Hom_(ZZ\/n) (mu_n^(otimes -m), Lambda) &\, m < 0
    )
  $
  当底概形在 $ZZ[n^(-1),zeta_n]$ 上（即有 $n$ 次单位根）时，通过人为选取一个本原 $n$ 次单位根，这个层非典范地同构于 $ul(Lambda)$。
  
  对 $Lambda$-模平展层的任意复形 $cal(K)$，定义它的*Tate 扭*：
  $
    cal(K)(m) = cal(K) otimes_Lambda ul(Lambda)(m)
  $
  当底概形在 $ZZ[n^(-1),zeta_n]$ 上（即有 $n$ 次单位根）时，通过人为选取一个本原 $n$ 次单位根，它们都非典范地同构于 $cal(K)$。
  
  现在，张量关系给出：
  $
    RHHom_Lambda (cal(K)(m_1), cal(L)(m_2)) = RHHom_Lambda (cal(K), cal(L))(m_2 - m_1) \
    cal(K)(m_1) Lotimes_Lambda cal(L)(m_2) = (cal(K) Lotimes_Lambda cal(L))(m_1 + m_2) \
    f^(-1) (cal(K)(m)) = (f^(-1) cal(K))(m)
  $
  而由投影公式给出：
  $
    R f_! (cal(K)(m)) = (R f_! cal(K))(m) 
  $
  以及：
  $
    R f_* (cal(K)(m)) = (R f_* cal(K))(m)
  $
  （$R f_*$ 的公式并非自动成立。若底概形 $X$ 有 $n$ 次单位根，则由非典范同构 $ul(Lambda)(m) cong ul(Lambda)$，这个投影是同构。一般情形下，给底概形 $X$ 添上 $n$ 次单位根，得到一个有限平展覆叠，即 Kummer 覆叠。此时投影沿 Kummer 覆叠的拉回是同构，故由 @surjective-pullback-conservative，投影本身是同构。）

  因此，在涉及 Tate 扭的表达式里，我们总把 Tate 扭丢到最右边，并且不在记号中显示 Tate 扭附着于表达式的哪一部分。
]

#construction(name: <trace-map-with-coefficients>)[
  刚刚定义的迹映射是一个典范映射：
  $
    Tr_(X\/Y): R f_! ul(ZZ\/n)(d)[2d] -> ul(ZZ\/n)
  $
  于是，对任意 $n$-挠系数环与任意复形 $cal(K) in D(Y_et, Lambda)$，把 $- Lotimes_(ZZ\/n) cal(K)$ 与投影公式作用于上面的迹映射，即得典范映射：
  $
    Tr_(X\/Y): R f_! f^(-1) cal(K)(d)[2d] -> cal(K)
  $
  它也称为*迹映射*。这个映射同样与基变换、复合相容，这是从迹映射 $R f_! ul(ZZ\/n)(d)[2d] -> ul(ZZ\/n)$ 继承来的。
]
