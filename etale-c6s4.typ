#import "void-import.typ": *

== (Shift) 的证明

本节证明 (Shift)。这是一个中间步骤，使我们能在不同概形之间转移基变换的结论。本节的方法取自 #cite-stacks("095S")[Section 59.91]。 

#proposition(name: <pbc-seed-precursor-0>)[
  对任意 Noether 的 Hensel 局部环 $A$、紧合态射 $f: X -> Spec(A)$ 以及任意挠层 $cal(F) in cAb(X_et)$，连通分支上的自然映射： 
  $
    pi_0 (X_0) -> pi_0 (X)
  $
  是双射。 
]
#proof[
  由 Stein 分解，$f: X -> Spec(A)$ 分解为 $f: X ->^g Y ->^h Spec(A)$，其中 $g$ 满射且纤维连通，$h$ 有限。此时 $f_0$ 分解为 $f_0: X_0 ->^(g_0) Y_0 ->^(h_0) Spec(k)$，其中 $g_0$ 的纤维连通，$h_0$ 有限。 

  #lemma[
    设 $f: X -> Y$ 是局部连通拓扑空间之间的满射闭映射，且纤维连通，则 $pi_0 (f): pi_0 (X) -> pi_0 (Y)$ 是双射。 
  ]
  #proof[
    对连通分支 $C subset Y$，$f^(-1) (C)$ 在 $X$ 中既开又闭，从而是 $X$ 的若干连通分支的不交并。把 $X -> Y$ 换成 $f^(-1) (C) -> C$，便可假设 $Y$ 连通，此时只需证 $X$ 连通。 

    反设 $X = X_1 union.sq X_2$，其中 $X_1, X_2 subset X$ 既闭又开。由于 $f$ 闭，$f(X_1), f(X_2) subset Y$ 都是闭集；由于 $f$ 满射，$Y = f(X_1) union f(X_2)$。若这两个闭集互不相交，则 $Y$ 就是两个真开闭子集的不交并，与 $Y$ 的连通性矛盾。于是存在 $y in Y$ 使得 $y in f(X_1) ∩ f(X_2)$。按假设，$f^(-1)(y)$ 连通。然而 $f^(-1)(y) = (X_1 ∩ f^(-1)(y)) union.sq (X_2 ∩ f^(-1)(y))$ 是两个真开闭子集的不交并，与 $f^(-1)(y)$ 的连通性矛盾。 
  ]

  于是 $pi_0 (g): pi_0 (X) -> pi_0 (Y)$ 与 $pi_0 (g_0): pi_0 (X_0) -> pi_0 (Y_0)$ 都是双射。因此只需证明 $pi_0 (Y_0) -> pi_0 (Y)$ 是双射。把 $X$ 换成 $Y$，不妨设 $X -> Spec(A)$ 有限，即 $X = Spec(B)$，其中 $B$ 是有限 $A$-代数。因 $A$ 是 Hensel 局部环，由 @equiv-defns-of-henselian (1) 知 $B = B_1 times dots.c times B_m$ 是有限局部 $A$-代数的直积，而 $Spec(B) = union.sq.big_(i=1)^m Spec(B_i)$ 给出其连通分支分解。现在 $X_0 = Spec(B_0), B_0 = B\/frak(m) B$，故 $B_0 = B_(1,0) times dots.c times B_(m,0)$，其中每个 $B_(i,0) = B_i\/frak(m) B_i$ 都是有限局部 $k$-代数。于是 $Spec(B_0) = union.sq.big_(i=1)^m Spec(B_(i,0))$ 给出其连通分支分解，且 $pi_0 (Spec(B_0)) -> pi_0 (Spec(B))$ 把 $Spec(B_(i,0))$ 送到 $Spec(B_i)$。可见在这个情形下 $pi_0 (X_0) -> pi_0 (X)$ 是双射，证毕。 
]

#lemma(name: <pbc-point-deg0>)[
  对任意 Noether 的严格 Hensel 局部环 $A$、紧合态射 $X -> Spec(A)$ 以及任意挠层 $cal(F) in cAb(X_et)$，自然限制映射： 
  $
    Gamma(X, cal(F)) -> Gamma(X_0, cal(F)|_(X_0))
  $
  是双射。换言之，沿 $X -> Spec(A)$ 的紧合基变换在 $0$ 次上总成立。 
]
#proof[
  由 @pbc-dev-lem3，只需对 $cal(F) = ul(ZZ\/n)$ 的情形证明。此时： 
  $
    Gamma(X, ul(ZZ\/n)) = (ZZ\/n)^(oplus pi_0 (X)), Gamma(X_0, ul(ZZ\/n)) = (ZZ\/n)^(oplus pi_0 (X_0))
  $
  其中自然限制映射由连通分支上的态射 $pi_0 (X_0) -> pi_0 (X)$ 诱导，而由 @pbc-seed-precursor-0，它是双射。于是证毕。 
]

#lemma(name: <pbc-and-injectives-of-ab-zn>)[
  对任意 Noether 的严格 Hensel 局部环 $A$ 与紧合态射 $f: X -> Spec(A)$，下列条件等价： 
  
  - 沿 $X -> Spec(A)$ 的基变换成立，即对所有挠层 $cal(F) in cAb(X_et)$，自然限制映射： 
    $
      H^q (X, cal(F)) -> H^q (X_0, cal(F)|_(X_0))
    $
    是双射。 

  - 对任意内射对象 $cal(I) in cAb(X_et, ZZ\/n)$，当 $q >= 1$ 时都有 $H^q (X_0, cal(I)|_(X_0)) = 0$。 
]
#proof[
  ($==>$) 由 @etale-zn-sheaves-first-props (3) 自动成立，因此只需证明 ($<==$)。由 @pbc-dev-lem1，不妨设 $cal(F)$ 可构造，从而存在 $n>=1$ 使它是 $n$-挠的。现取 $cal(F)$ 在 $cAb(X_et, ZZ\/n)$ 中的一个内射消解： 
  $
    0 -> cal(F) -> cal(I)^bullet
  $
  由 @etale-zn-sheaves-first-props (3)，每个 $cal(I)^i$ 都是 $Gamma(X, -)$-零调的，故： 
  $
    H^q (X, cal(F)) = h^q (0 -> Gamma(X, cal(I)^bullet))
  $
  由于拉回正合，我们在 $cAb((X_0)_et)$ 中有正合列： 
  $
    0 -> cal(F)|_(X_0) -> cal(I)^bullet|_(X_0)
  $
  按假设，每个 $cal(I)^bullet|_(X_0)$ 都是 $Gamma(X_0, -)$-零调的，因此： 
  $
    H^q (X_0, cal(F)|_(X_0)) = h^q (0 -> Gamma(X_0, cal(I)^bullet|_(X_0)))
  $
  自然限制映射 $H^q (X, cal(F)) -> H^q (X_0, cal(F)|_(X_0))$ 由复形之间的限制映射 $Gamma(X, cal(I)^bullet) -> Gamma(X_0, cal(I)^bullet|_(X_0))$ 诱导。由 @pbc-point-deg0，这些映射逐项同构，因此自然限制映射 $H^q (X, cal(F)) -> H^q (X_0, cal(F)|_(X_0))$ 也是同构。 
]

#theorem[
  (Shift) 考虑一个逐次基变换的图表，其中所有概形都是 Noether 的，$A$ 是严格 Hensel 局部环，且 $X', X$ 在 $Spec(A)$ 上紧合：
  // https://q.uiver.app/#r=typst&q=WzAsNixbMCwxLCJYJyJdLFsxLDEsIlgiXSxbMiwxLCJTcGVjKEEpIl0sWzIsMCwiU3BlYyhrKSJdLFsxLDAsIlhfMCJdLFswLDAsIlgnXzAiXSxbMCwxLCJwaSIsMl0sWzEsMl0sWzMsMl0sWzUsNCwicGlfMCJdLFs0LDEsImkiXSxbNSwwLCJpJyIsMl0sWzQsM11d
  #align(center, diagram({
    node((-1, 0), [$X'$])
    node((0, 0), [$X$])
    node((1, 0), [$Spec(A)$])
    node((1, -1), [$Spec(k)$])
    node((0, -1), [$X_0$])
    node((-1, -1), [$X'_0$])
    edge((-1, 0), (0, 0), [$pi$], label-side: right, "->")
    edge((0, 0), (1, 0), "->")
    edge((1, -1), (1, 0), "->")
    edge((-1, -1), (0, -1), [$pi_0$], label-side: left, "->")
    edge((0, -1), (0, 0), [$i$], label-side: left, "->")
    edge((-1, -1), (-1, 0), [$i'$], label-side: right, "->")
    edge((0, -1), (1, -1), "->")
  }))
  我们有：
  $
        & BC(pi, i) \
    ==> & (BC_* (X -> Spec(A)) <==> BC_* (X' -> Spec(A)))
  $
  说得直白些：若基变换对左边的方块成立，则“对右边的方块成立”与“对整个大矩形成立”等价。 
]
#proof[
  我们先证明一个技术性引理： 
  #lemma(name: <surjection-has-injective-unit>)[
    设 $f: X -> Y$ 满射，则对所有 $cal(F) in cAb(Y_et)$，单位映射： 
    $
      eta_(cal(F)): cal(F) -> f_* f^(-1) cal(F)
    $
    是单射。 
  ]
  #proof[
    /*令 $cal(K) = ker(cal(F) -> f_* f^(-1) cal(F))$，并构造正合列： 
    $
      0 -> cal(K) -> cal(F) ->^eta f_* f^(-1) cal(F)
    $
    对之应用 $f^(-1)$，得到正合列： 
    $
      0 -> f^(-1) cal(K) -> f^(-1) cal(F) -->^(f^(-1) eta_(cal(F))) f^(-1) f_* f^(-1) cal(F)
    $
    然而，*/从范畴论可知，余单位 $epsilon_(cal(G)): f^(-1) f_* cal(G) -> cal(G)$ 与单位 $eta_(cal(F))$ 满足恒等式，即复合 
    $
      f^(-1) cal(F) -->^(f^(-1) eta_(cal(F))) f^(-1) f_* f^(-1) cal(F) -->^(epsilon_(f^(-1) cal(F))) f^(-1) cal(F)
    $
    是恒等映射。特别地，$f^(-1) eta_(cal(F)): f^(-1) cal(F) -> f^(-1) f_* f^(-1) cal(F)$ 是单射。而由 @surjective-pullback-conservative 知，$eta_(cal(F))$ 是单射。 
  ]
  由 @pbc-and-injectives-of-ab-zn，只需证明：对每个内射对象 $cal(I) in cAb(X_et, ZZ\/n)$，当 $q >= 1$ 时 $H^q (X_0, cal(I)|_(X_0)) = 0$。取一个单射 $pi^(-1) cal(I) -> cal(J)$，其中 $cal(J) in cAb(X'_et, ZZ\/n)$ 是内射对象。由于 $pi_*$ 左正合，而单位映射 $cal(I) -> pi_* pi^(-1) cal(I)$ 由上一个引理知是单射，故伴随给出的态射： 
  $
    cal(I) -> pi_* pi^(-1) cal(I) -> pi_* cal(J)
  $
  是 $cAb(X_et, ZZ\/n)$ 中的单射。由于 $cal(I) in cAb(X_et, ZZ\/n)$ 是内射对象，它是 $pi_* cal(J)$ 的直和项。因此，要证明 $q>=1$ 时 $H^q (X_0, cal(I)|_(X_0)) = 0$，只需证明 $H^q (X_0, pi_* cal(J)|_(X_0)) = 0$。 

  由于 $cal(J)$ 是 $n$-挠的，且基变换对左边方块成立，故 $pi_* cal(J)|_(X_0) = pi_(0,*) (cal(J)|_(X'_0))$。于是只需证明： 
  $
    H^q (X_0, pi_(0,*) (cal(J)|_(X'_0))) = 0, forall q >= 1
  $
  对任意 $q >= 1$，有 
  $
    R^q pi_(0,*) (cal(J)|_(X'_0)) cong (R^q pi_* cal(J))|_(X_0) = 0
  $
  这是因为基变换对左边方块成立，而 $R^q pi_* cal(J) = 0$ 由 @etale-zn-sheaves-first-props (3) 得到。于是有 Leray 谱序列（@derived-lower-star-first-props (2)）： 
  $
    H^p (X_0, R^q pi_(0,*) (cal(J)|_(X'_0))) ==> H^(p+q) (X'_0, cal(J)|_(X'_0))
  $
  该谱序列退化，诱导出同构： 
  $
    H^q (X_0, pi_(0,*) (cal(J)|_(X'_0))) cong H^q (X'_0, cal(J)|_(X'_0))
  $
  由 @pbc-and-injectives-of-ab-zn 的第二条（此处基变换对大矩形成立），$q>=1$ 时同构的右端为 $0$。于是对所有 $q >= 1$ 都有 $H^q (X_0, pi_* cal(J)|_(X_0)) = 0$，证毕。 
]
// 我们对这个结果给出两个本质相同的证明：一个用显式的消解与复形来表述，另一个在导出范畴中表述。第二个证明本质上就是第一个，只是把一些细节封装进了导出范畴的机制。不过，我认为我们到目前为止还没有用到导出范畴，大概也不该要求读者在一个冗长证明的中途绕去啃一个困难的范畴论构造。因此，手写证明将是主线；至于如何用导出范畴的语言把这段冗长的手写证明缩短，我会写在嵌套的证明框里。 

// 这个证明本质上需要导出范畴的理论与语言。读者在读这个证明之前，应当先阅读关于导出范畴的附录。 

// #proof[
//   ($==>$) 就是 (Comp)（@pbc-comp），所以我们只需证明 ($<==$)，即：若基变换对左边方块与大矩形成立，则它对右边方块成立。 

//   // 由 @pbc-dev-lem1，只需证明基变换对所有可构造层 $cal(F) in cAb(X_et)$ 成立。特别地，$cal(F)$ 对某个固定的 $n>=1$ 是 $n$-挠的，于是由零调 Godement 消解（@acyclic-godement-resolution），存在一个 $Gamma(X, -)$-零调消解： 
//   // $
//   //   0 -> cal(F) -> cal(I)^bullet
//   // $
//   // 其中每个 $cal(I)^p$ 都是 $n$-挠的。 
// ]
