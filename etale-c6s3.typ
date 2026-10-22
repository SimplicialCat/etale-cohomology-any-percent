// audit-exception: 展示公式中的 #[...] 文字块内嵌 $n$、$g^(-1)$、$g''^(-1)$ 等行内公式，审计按相邻美元符号配对会把块内说明文字切成伪公式段；只译块内说明文字，块内与块外公式逐段核对未变。
#import "void-import.typ": *

== Devissage：证明 (Dev) 与 (Comp)

本节我们用可构造层作 devissage 论证，证明陈述 (Dev) 与 (Comp)。 

#theorem(name: <pbc-comp>)[
  (Comp) 
  
  + 考虑如下的逐次基变换图表：
    // https://q.uiver.app/#r=typst&q=WzAsNixbMCwwLCJaJyJdLFsxLDAsIlgnIl0sWzIsMCwiWSciXSxbMiwxLCJZIl0sWzEsMSwiWCJdLFswLDEsIloiXSxbMiwzLCJnIl0sWzEsNCwiZyciXSxbMCw1LCJnJyciXSxbNCwzLCJmIiwyXSxbNSw0LCJoIiwyXSxbMCwxLCJoJyJdLFsxLDIsImYnIl1d
    #align(center, diagram({
      node((-2, -1), [$Z'$])
      node((-1, -1), [$X'$])
      node((0, -1), [$Y'$])
      node((0, 0), [$Y$])
      node((-1, 0), [$X$])
      node((-2, 0), [$Z$])
      edge((0, -1), (0, 0), [$g$], label-side: left, "->")
      edge((-1, -1), (-1, 0), [$g'$], label-side: left, "->")
      edge((-2, -1), (-2, 0), [$g''$], label-side: left, "->")
      edge((-1, 0), (0, 0), [$h$], label-side: right, "->")
      edge((-2, 0), (-1, 0), [$f$], label-side: right, "->")
      edge((-2, -1), (-1, -1), [$f'$], label-side: left, "->")
      edge((-1, -1), (0, -1), [$h'$], label-side: left, "->")
    }))
    我们有：
    $
      BC (f, g) and BC (h, g') ==> BC (h compose f, g)
    $
    即：若基变换定理对左、右两个小方块成立，则它对大矩形也成立。 

  + 考虑如下的逐次基变换图表：
    // https://q.uiver.app/#r=typst&q=WzAsNixbMCwxLCJYJyJdLFsxLDEsIlknIl0sWzAsMiwiWCJdLFsxLDIsIlkiXSxbMSwwLCJZJyciXSxbMCwwLCJYJyciXSxbMiwzLCJmIl0sWzAsMSwiZiciXSxbMSwzLCJnIl0sWzAsMiwiZyciLDJdLFs1LDQsImYnJyJdLFs0LDEsImgiXSxbNSwwLCJoJyciLDJdXQ==
    #align(center, diagram({
      node((0, 0), [$X'$])
      node((1, 0), [$Y'$])
      node((0, 1), [$X$])
      node((1, 1), [$Y$])
      node((1, -1), [$Y''$])
      node((0, -1), [$X''$])
      edge((0, 1), (1, 1), [$f$], label-side: left, "->")
      edge((0, 0), (1, 0), [$f'$], label-side: left, "->")
      edge((1, 0), (1, 1), [$g$], label-side: left, "->")
      edge((0, 0), (0, 1), [$g'$], label-side: right, "->")
      edge((0, -1), (1, -1), [$f''$], label-side: left, "->")
      edge((1, -1), (1, 0), [$h$], label-side: left, "->")
      edge((0, -1), (0, 0), [$h'$], label-side: right, "->")
    }))
    我们有： 
    $
      BC(f, g) and BC(f', h) ==> BC(f, g compose h)
    $
    即：若基变换定理对上、下两个小方块成立，则它对大矩形也成立。 
]
#proof[
  （1）先证基变换映射： 
  $
    g^(-1) R^q (h compose f)_* cal(F) -> R^q (h' compose f')_* g''^(-1) cal(F)
  $
  对 $cal(F) in cAb(Z_et)$ 是同构，其中 $n >= 1$ 固定，$cal(F)$ 是 $n$-挠的。 

  设 $cal(F) in cAb(Z_et)$ 是 $n$-挠的，考虑 Leray 谱序列（@derived-lower-star-first-props (1)）： 
  $
    R^p h_* (R^q f_* cal(F)) ==> R^(p+q) (h compose f)_* cal(F)
  $
  用正合函子 $g^(-1)$ 作用在这个谱序列上，得到新的谱序列： 
  $
    g^(-1) (R^p h_* (R^q f_* cal(F))) ==> g^(-1) (R^(p+q) (h compose f)_* cal(F))
  $
  另一方面，由左、右两个方块上的基变换定理： 
  $
    g^(-1) (R^p h_* (R^q f_* cal(F))) cong R^p h'_* (g'^(-1) (R^q f_* cal(F))) cong R^p h'_* (R^q f'_* (g''^(-1) cal(F)))
  $
  这里 $times n: cal(F) -> cal(F)$ 是零映射，故 $times n: R^q f_* cal(F) -> R^q f_* cal(F)$ 也是零映射，从而 $cal(F)$ 与 $R^q f_* cal(F)$ 都是 $n$-挠的，基变换定理可以应用。又由 @base-change-naturality，Leray 谱序列与基变换映射相容，于是借助基变换同构，这个谱序列化为： 
  $
    R^p h'_* (R^q f'_* (g''^(-1) cal(F))) ==> g^(-1) (R^(p+q) (h compose f)_* cal(F))
  $
  不过，由 Leray 谱序列 @derived-lower-star-first-props (1) 可得： 
  $
    R^p h'_* (R^q f'_* (g''^(-1) cal(F))) ==> R^(p+q) (h' compose f')_* (g''^(-1) cal(F))
  $
  因此基变换映射 $g^(-1) (R^q (h compose f)_* cal(F)) -> R^q (h' compose f')_* (g''^(-1) cal(F))$ 是同构。 

  接下来考虑一般的挠层 $cal(F) in cAb(Z_et)$。按挠层的定义有 $cal(F) = dirlim_(n>=1) cal(F)[n]$。把 $cal(F)$ 写成 $cal(F) = dirlim_i cal(F)_i$，其中每个 $cal(F)_i$ 对某个 $n_i$ 都是 $n_i$-挠的，然后应用 @relative-limit-formula-for-sheaves 以及关于被固定整数零化的挠层已经得到的结论： 
  $
    & g^(-1) (R^q (h compose f)_* cal(F)) cong g^(-1) (R^q (h compose f)_* (dirlim_(i in I) cal(F)_i)) \
    cong& dirlim_(i in I) g^(-1) (R^q (h compose f)_* cal(F)_i) #[由 @relative-limit-formula-for-sheaves 以及 $g^(-1)$ 是左伴随] \
    cong& dirlim_(i in I) R^q (h' compose f')_* (g''^(-1) cal(F)_i) #[由 $n$-挠层的结论] \
    cong& R^q (h' compose f')_* (g''^(-1) cal(F)) #[由 @relative-limit-formula-for-sheaves 以及 $g''^(-1)$ 是左伴随]
  $

  （2）则非常简单：由 @base-change-naturality，基变换与拉回方块的竖直拼接相容，所以可以直接写出： 
  $
    (g compose h)^(-1) R^q f_* cal(F) cong h^(-1) g^(-1) R^q f_* cal(F) cong h^(-1) R^q f'_* (g'^(-1) cal(F)) cong R^q f''_* (h'^(-1) g'^(-1) cal(F)) cong R^q f''_* (g' compose h')^(-1) cal(F)
  $
  这里由于 $cal(F)$ 是挠层，由 @pullback-of-torsion-sheaf，$g'^(-1) cal(F)$ 也是挠层，因此基变换可以应用。 
]

对 (Comp) 的这个论证主要靠一个谱序列完成；一旦放到导出范畴里看，它几乎变得平凡： 
$
  g^(-1) R(h compose f)_* cal(F) cong g^(-1) (R h_* (R f_* cal(F))) cong R h'_* (g'^(-1) (R f_* cal(F))) cong R h'_* (R f'_* (g''^(-1) cal(F))) = R(h' compose f')_* (g''^(-1) cal(F))
$
在导出范畴里，Leray 谱序列其实不过是 $R(h compose f)_* = R h_* compose R f_*$。 

接下来，把任意挠层化归到 $ul(ZZ\/n)$ 所需的这个关键 devissage，正好能展示可构造层的威力。 

#theorem(name: <pbc-dev>)[
  (Dev) 只要 $A$ 是严格 Hensel 的 Noether 环，且 $X -> Spec(A)$ 是 Noether 的， 
  $
      ( & forall tilde(X) -> X #[finite], forall n >= 1, \
        & BC^0_* (tilde(X) -> X -> Spec(A), ul(ZZ\/n)) and (forall q>=1, BC^q_(*,#[surj]) (tilde(X) -> X -> Spec(A), ul(ZZ\/n)))) \
    // ==>&(&&forall tilde(X) -> X #[finite], forall cal(F) in cAb(tilde(X)_et) #[torsion], forall q>=0, \
    // &&& BC^q_(*,#[surj])(tilde(X) -> X -> Spec(A), cal(F))))
    ==> & (forall tilde(X) -> X #[finite], BC_* (tilde(X) -> Spec(A)))
  $
  用大白话说：给定 $X -> Spec(A)$，其中 $A$ 是严格 Hensel 的 Noether 环，$X$ 是 Noether 概形。若对一切有限态射 $tilde(X) -> X$，基变换映射： 
  $
    res_(ul(ZZ\/n))^(q,tilde(X)): H^q (tilde(X), ul(ZZ\/n)) -> H^q (tilde(X)_0, ul(ZZ\/n))
  $
  在 $q = 0$ 时是双射，对一切 $q >= 1$ 都是满射，则对一切有限态射 $tilde(X) -> X$，基变换映射：
  $
    res_(cal(F))^(q,tilde(X)): H^q (tilde(X), cal(F)) -> H^q (tilde(X)_0, cal(F)|_(tilde(X)_0))
  $
  对所有挠层 $cal(F) in cAb(tilde(X)_et)$ 都是双射。 
]
#proof[
  主要思路是沿两个正合列做降维。 

  #lemma(name: <pbc-dev-lem1>)[
    设 $X -> Spec(A)$ 是 Noether 的，$q >= 0$ 固定。若对一切可构造层 $cal(F) in cAb(X_et)$，$res_(cal(F))^(q,tilde(X))$ 都是单射/满射/双射，则对一切挠层 $cal(F) in cAb(X_et)$ 也同样成立。 
  ]
  #proof[
    由 @constructible-sheaves-first-props (6)，每个挠层 $cal(F)$ 都可以写成其可构造子层的正向极限： 
    $
      cal(F) = dirlim_(i in I) cal(F)_i
    $
    其中每个 $cal(F)_i$ 都可构造。现在由 @limit-formula-for-sheaves，并利用拉回作为左伴随保持余极限这一事实，可得： 
    $
      H^q (X, cal(F)) = dirlim_(i in I) H^q (X, cal(F)_i) \
      H^q (X_0, cal(F)|_(X_0)) = dirlim_(i in I) H^q (X_0, cal(F)_i|_(X_0))
    $
    于是作为态射： 
    $
      res^(q,X)_(cal(F)) = dirlim_(i in I) res^(q,X)_(cal(F)_i)
    $
    由 $cAb$ 的 (Ab5)，$res^(q,X)_(cal(F)_i)$ 是单射/满射/双射，则 $res^(q,X)_(cal(F))$ 也是。 
  ]

  #lemma(name: <pbc-dev-lem2>)[
    设 $X -> Spec(A)$ 是 Noether 的，$q >= 1$ 固定。若： 

    - 对一切 $p < q$ 与一切挠层 $cal(F) in cAb(X_et)$，$res^(p,X)_(cal(F))$ 都是双射。 

    则： 

    - 对一切挠层 $cal(F) in cAb(X_et)$，$res^(q,X)_(cal(F))$ 都是单射。 
  ]
  #proof[
    由 @pbc-dev-lem1，只需对一切可构造层 $cal(F) in cAb(X_et)$ 证明 $res^(q,X)_(cal(F))$ 是单射。设 $cal(F)$ 是 $n$-挠的。由 @acyclic-godement-resolution，存在 $n$-挠的 $Gamma(X, -)$-零调层 $cal(C)$ 与单射 $cal(F) -> cal(C)$。取其余核，得到正合列： 
    $
      0 -> cal(F) -> cal(C) -> cal(R) -> 0
    $
    这是 $X$ 上 $n$-挠层的正合列。于是又有： 
    $
      0 -> cal(F)|_(X_0) -> cal(C)|_(X_0) -> cal(R)|_(X_0) -> 0
    $
    这是 $X_0$ 上 $n$-挠层的正合列。现在考虑上同调长正合列，配上基变换映射的自然性： 
    // https://q.uiver.app/#r=typst&q=WzAsMTIsWzEsMCwiSF4ocS0xKSAoWCwgY2FsKEMpKSJdLFsyLDAsIkheKHEtMSkgKFgsIGNhbChSKSkiXSxbMywwLCJIXnEgKFgsIGNhbChGKSkiXSxbNCwwLCJvdmVyYnJhY2UoSF5xIChYLCBjYWwoQykpLCAwKSJdLFsxLDEsIkheKHEtMSkgKFhfMCwgY2FsKEMpfF8oWF8wKSkiXSxbMiwxLCJIXihxLTEpIChYXzAsIGNhbChSKXxfKFhfMCkpIl0sWzMsMSwiSF5xIChYXzAsIGNhbChGKXxfKFhfMCkpIl0sWzQsMSwiSF5xIChYXzAsIGNhbChDKXxfKFhfMCkpIl0sWzAsMCwiZG90cy5jIl0sWzAsMSwiZG90cy5jIl0sWzUsMCwiZG90cy5jIl0sWzUsMSwiZG90cy5jIl0sWzAsMV0sWzEsMl0sWzIsM10sWzQsNV0sWzUsNl0sWzYsN10sWzgsMF0sWzksNF0sWzMsMTBdLFs3LDExXSxbMCw0LCJyZXNeKHEtMSxYKV8oY2FsKEMpKSIsMCx7InN0eWxlIjp7InRhaWwiOnsibmFtZSI6Imhvb2siLCJzaWRlIjoidG9wIn0sImhlYWQiOnsibmFtZSI6ImVwaSJ9fX1dLFsxLDUsInJlc14ocS0xLFgpXyhjYWwoUikpIiwxLHsic3R5bGUiOnsidGFpbCI6eyJuYW1lIjoiaG9vayIsInNpZGUiOiJ0b3AifSwiaGVhZCI6eyJuYW1lIjoiZXBpIn19fV0sWzIsNiwicmVzXihxLFgpXyhjYWwoRikpIiwxXSxbMyw3LCJyZXNeKHEsWClfKGNhbChDKSkiLDEseyJzdHlsZSI6eyJ0YWlsIjp7Im5hbWUiOiJob29rIiwic2lkZSI6InRvcCJ9fX1dXQ==
    #align(center, diagram({
      node((-2, -1), [$H^(q-1) (X, cal(C))$])
      node((-1, -1), [$H^(q-1) (X, cal(R))$])
      node((0, -1), [$H^q (X, cal(F))$])
      node((1, -1), [$overbrace(H^q (X, cal(C)), 0)$])
      node((-2, 0), [$H^(q-1) (X_0, cal(C)|_(X_0))$])
      node((-1, 0), [$H^(q-1) (X_0, cal(R)|_(X_0))$])
      node((0, 0), [$H^q (X_0, cal(F)|_(X_0))$])
      node((1, 0), [$H^q (X_0, cal(C)|_(X_0))$])
      node((-3, -1), [$dots.c$])
      node((-3, 0), [$dots.c$])
      node((2, -1), [$dots.c$])
      node((2, 0), [$dots.c$])
      edge((-2, -1), (-1, -1), "->")
      edge((-1, -1), (0, -1), "->")
      edge((0, -1), (1, -1), "->")
      edge((-2, 0), (-1, 0), "->")
      edge((-1, 0), (0, 0), "->")
      edge((0, 0), (1, 0), "->")
      edge((-3, -1), (-2, -1), "->")
      edge((-3, 0), (-2, 0), "->")
      edge((1, -1), (2, -1), "->")
      edge((1, 0), (2, 0), "->")
      edge((-2, -1), (-2, 0), [$res^(q-1,X)_(cal(C))$], label-side: left, "hook->>")
      edge((-1, -1), (-1, 0), [$res^(q-1,X)_(cal(R))$], label-side: left, "hook->>")
      edge((0, -1), (0, 0), [$res^(q,X)_(cal(F))$], label-side: left, "->")
      edge((1, -1), (1, 0), [$res^(q,X)_(cal(C))$], label-side: left, "hook->")
    }, spacing: (2.4em, 3em)))
    其中：

    - 前两个竖直箭头由归纳假设是双射，因为 $cal(C), cal(R)$ 都是 $n$-挠的； 

    - 第四个竖直箭头是单射：$cal(C)$ 零调，故 $H^q (X, cal(C)) = 0$。 

    由单射四引理，$res^(q,X)_(cal(F))$ 是单射。 
  ]

  #lemma(name: <pbc-dev-lem3>)[
    设 $X -> Spec(A)$ 是 Noether 的，$q >= 0$ 固定。若： 

    - 对一切 $p < q$、一切有限态射 $tilde(X) -> X$ 与一切挠层 $cal(F) in cAb(tilde(X)_et)$，$res_(cal(F))^(p,tilde(X))$ 都是双射。 

    - 对一切有限态射 $tilde(X) -> X$，$res_(ul(ZZ\/n))^(q,tilde(X))$ 是满射；并且当 $q = 0$ 时还是双射。 

    则： 

    - 对一切有限态射 $tilde(X) -> X$ 与一切挠层 $cal(F) in cAb(tilde(X)_et)$，$res_(cal(F))^(q,tilde(X))$ 都是双射。 
  ]
  #proof[
    由 @pbc-dev-lem1，只需在 $cal(F)$ 可构造时证明。把 $X$ 换成 $tilde(X)$，还可以假设 $cal(F) in cAb(X_et)$。现在由 @finite-morphisms-and-constructible-sheaves (2)，存在有限态射 $g: tilde(X) -> X$ 与单射 $cal(F) -> g_* ul(ZZ\/n)_(tilde(X))$。取其余核，得到可构造层的正合列： 
    $
      0 -> cal(F) -> g_* ul(ZZ\/n)_(tilde(X)) -> cal(R) -> 0
    $
    对 $g: tilde(X) -> X$ 作基变换，得到 $g_0: tilde(X)_0 -> X_0$。于是由 (Finite)（@pbc-finite），拉回到 $X_0$ 便得到可构造层的正合列： 
    $
      0 -> cal(F)|_(X_0) -> g_(0,*) ul(ZZ\/n)_(tilde(X)_0) -> cal(R)|_(X_0) -> 0
    $
    现在考虑上同调长正合列，配上基变换映射的自然性，再加上 @pushforward-by-finite-morphism： 

    - 情形 $q = 0$：我们有交换图：#h(1fr)
      // https://q.uiver.app/#r=typst&q=WzAsMTAsWzAsMCwiMCJdLFswLDEsIjAiXSxbMSwwLCJIXjAgKFgsIGNhbChGKSkiXSxbMSwxLCJIXjAgKFhfMCwgY2FsKEYpfF8oWF8wKSkiXSxbMywwLCJIXjAgKFgsIGNhbChSKSkiXSxbMywxLCJIXjAgKFhfMCwgY2FsKFIpfF8oWF8wKSkiXSxbMiwwLCJIXjAgKHRpbGRlKFgpLCB1bChaWlxcL24pKSJdLFsyLDEsIkheMCAodGlsZGUoWClfMCwgdWwoWlpcXC9uKSkiXSxbNCwwLCJkb3RzLmMiXSxbNCwxLCJkb3RzLmMiXSxbMiw2LCIiLDAseyJzdHlsZSI6eyJ0YWlsIjp7Im5hbWUiOiJob29rIiwic2lkZSI6InRvcCJ9fX1dLFswLDJdLFs2LDRdLFsxLDNdLFszLDcsIiIsMCx7InN0eWxlIjp7InRhaWwiOnsibmFtZSI6Imhvb2siLCJzaWRlIjoidG9wIn19fV0sWzcsNV0sWzIsMywicmVzXigwLFgpXyhjYWwoRikpIl0sWzQsNSwicmVzXigwLFgpXyhjYWwoUikpIl0sWzYsNywicmVzXigwLHRpbGRlKFgpKV8odWwoWlpcXC9uKSkiLDAseyJzdHlsZSI6eyJ0YWlsIjp7Im5hbWUiOiJob29rIiwic2lkZSI6InRvcCJ9LCJoZWFkIjp7Im5hbWUiOiJlcGkifX19XSxbNCw4XSxbNSw5XV0=
      #align(center, diagram({
        node((-3, -1), [$0$])
        node((-3, 0), [$0$])
        node((-2, -1), [$H^0 (X, cal(F))$])
        node((-2, 0), [$H^0 (X_0, cal(F)|_(X_0))$])
        node((0, -1), [$H^0 (X, cal(R))$])
        node((0, 0), [$H^0 (X_0, cal(R)|_(X_0))$])
        node((-1, -1), [$H^0 (tilde(X), ul(ZZ\/n))$])
        node((-1, 0), [$H^0 (tilde(X)_0, ul(ZZ\/n))$])
        node((1, -1), [$dots.c$])
        node((1, 0), [$dots.c$])
        edge((-2, -1), (-1, -1), "hook->")
        edge((-3, -1), (-2, -1), "->")
        edge((-1, -1), (0, -1), "->")
        edge((-3, 0), (-2, 0), "->")
        edge((-2, 0), (-1, 0), "hook->")
        edge((-1, 0), (0, 0), "->")
        edge((-2, -1), (-2, 0), [$res^(0,X)_(cal(F))$], label-side: left, "->")
        edge((0, -1), (0, 0), [$res^(0,X)_(cal(R))$], label-side: left, "->")
        edge((-1, -1), (-1, 0), [$res^(0,tilde(X))_(ul(ZZ\/n))$], label-side: left, "hook->>")
        edge((0, -1), (1, -1), "->")
        edge((0, 0), (1, 0), "->")
      }, spacing: (2.4em, 3em)))
      
      - 第一个竖直箭头 $res^(0,X)_(cal(F))$ 是单射，因为第一个方块中的其余箭头都是单射。 

      - 这就说明：对一切可构造层 $cal(F) in cAb(X_et)$，$res^(0,X)_(cal(F))$ 是单射。特别地，第三个竖直箭头 $res^(0,X)_(cal(R))$ 是单射。 

      - 第二个竖直箭头 $res^(0,tilde(X))_(ul(ZZ\/n))$ 是满射，第三个竖直箭头 $res^(0,X)_(cal(R))$ 是单射，故由满射四引理，$res^(0,X)_(cal(F))$ 是满射。 

      本情形至此证毕。 

    - 情形 $q >= 1$。此时由归纳假设可应用 @pbc-dev-lem2，从而得到： 

      - 对一切有限态射 $tilde(X) -> X$ 与一切挠层 $cal(F) in cAb(tilde(X)_et)$，$res_(cal(F))^(q,tilde(X))$ 都是单射。 

      现在看同一个长正合列： 
      // https://q.uiver.app/#r=typst&q=WzAsMTIsWzEsMCwiSF4ocS0xKSAoWCwgY2FsKFIpKSJdLFsyLDAsIkhecSAoWCwgY2FsKEYpKSJdLFszLDAsIkhecSAodGlsZGUoWCksIHVsKFpaXFwvbikpIl0sWzQsMCwiSF5xIChYLCBjYWwoUikpIl0sWzMsMSwiSF5xICh0aWxkZShYKV8wLCB1bChaWlxcL24pKSJdLFs0LDEsIkhecSAoWF8wLCBjYWwoUil8XyhYXzApKSJdLFsxLDEsIkheKHEtMSkgKFhfMCwgY2FsKFIpfF8oWF8wKSkiXSxbMiwxLCJIXnEgKFhfMCwgY2FsKEYpfF8oWF8wKSkiXSxbMCwwLCJkb3RzLmMiXSxbMCwxLCJkb3RzLmMiXSxbNSwwLCJkb3RzLmMiXSxbNSwxLCJkb3RzLmMiXSxbMCwxXSxbMSwyXSxbMiwzXSxbNiw3XSxbNyw0XSxbNCw1XSxbMiw0LCJyZXNeKHEsdGlsZGUoWCkpXyh1bChaWlxcL24pKSIsMCx7InN0eWxlIjp7InRhaWwiOnsibmFtZSI6Imhvb2siLCJzaWRlIjoidG9wIn0sImhlYWQiOnsibmFtZSI6ImVwaSJ9fX1dLFsxLDcsInJlc14ocSxYKV8oY2FsKEYpKSIsMCx7InN0eWxlIjp7InRhaWwiOnsibmFtZSI6Imhvb2siLCJzaWRlIjoidG9wIn19fV0sWzAsNiwicmVzXihxLTEsWClfKGNhbChSKSkiLDAseyJzdHlsZSI6eyJ0YWlsIjp7Im5hbWUiOiJob29rIiwic2lkZSI6InRvcCJ9LCJoZWFkIjp7Im5hbWUiOiJlcGkifX19XSxbOCwwXSxbOSw2XSxbMywxMF0sWzUsMTFdLFszLDUsInJlc14ocSxYKV8oY2FsKFIpKSIsMCx7InN0eWxlIjp7InRhaWwiOnsibmFtZSI6Imhvb2siLCJzaWRlIjoidG9wIn19fV1d
      #align(center, diagram({
        node((2, 0), [$H^(q-1) (X, cal(R))$])
        node((3, 0), [$H^q (X, cal(F))$])
        node((4, 0), [$H^q (tilde(X), ul(ZZ\/n))$])
        node((5, 0), [$H^q (X, cal(R))$])
        node((4, 1), [$H^q (tilde(X)_0, ul(ZZ\/n))$])
        node((5, 1), [$H^q (X_0, cal(R)|_(X_0))$])
        node((2, 1), [$H^(q-1) (X_0, cal(R)|_(X_0))$])
        node((3, 1), [$H^q (X_0, cal(F)|_(X_0))$])
        node((1, 0), [$dots.c$])
        node((1, 1), [$dots.c$])
        node((6, 0), [$dots.c$])
        node((6, 1), [$dots.c$])
        edge((2, 0), (3, 0), "->")
        edge((3, 0), (4, 0), "->")
        edge((4, 0), (5, 0), "->")
        edge((2, 1), (3, 1), "->")
        edge((3, 1), (4, 1), "->")
        edge((4, 1), (5, 1), "->")
        edge((4, 0), (4, 1), [$res^(q,tilde(X))_(ul(ZZ\/n))$], label-side: left, "hook->>")
        edge((3, 0), (3, 1), [$res^(q,X)_(cal(F))$], label-side: left, "hook->")
        edge((2, 0), (2, 1), [$res^(q-1,X)_(cal(R))$], label-side: left, "hook->>")
        edge((1, 0), (2, 0), "->")
        edge((1, 1), (2, 1), "->")
        edge((5, 0), (6, 0), "->")
        edge((5, 1), (6, 1), "->")
        edge((5, 0), (5, 1), [$res^(q,X)_(cal(R))$], label-side: left, "hook->")
      }, spacing: (2.4em, 3em)))
      其中：
      - 第一个竖直箭头由归纳假设是双射； 

      - 第二、第三、第四个竖直箭头都是单射，因为我们已经用 @pbc-dev-lem2 证明了：对一切有限态射 $tilde(X) -> X$ 与一切挠层 $cal(F) in cAb(tilde(X)_et)$，$res_(cal(F))^(q,tilde(X))$ 都是单射。 

      - 第三个竖直箭头是满射，这是我们关于 $res^(q,tilde(X))_(ul(ZZ\/n))$ 的假设。 

      由满射四引理，第二个竖直箭头 $res^(q,X)_(cal(F))$ 是满射，从而是双射。至此证毕。 
  ]
  三个引理证完之后，用第三个引理（@pbc-dev-lem3）与定理的假设做归纳，就得到：对一切 $q >= 0$ 与一切挠层 $cal(F) in cAb(X_et)$，$res^(q,X)_(cal(F))$ 都是双射。 
]
