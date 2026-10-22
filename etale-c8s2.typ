#import "void-import.typ": *

== 局部零调性

回顾上一节所做的归约，现在可以引入局部零调性了。局部零调性刻画了态射的特殊纤维与泛纤维之间的某种相容性，它也正是使相对基变换映射（关于某个复形 $cal(L)$）成为泛同构所要求的恰当相容性条件。 

#definition(name: <defn-local-acyclicity>)[
  给定概形态射 $f: X -> S$，取 $X$ 的几何点 $ol(x)$ 并令 $ol(s) = f(ol(x))$，再取 $tilde(S)_(ol(s))$ 的几何点 $ol(t)$（即 $ol(s)$ 的一个一般化）。我们定义*消没圈簇* (vanishing cycle variety) 为： 
  $
    F_(ol(x),ol(t)) := ol(t) times_(tilde(S)_(ol(s))) tilde(X)_(ol(x))
  $
  由于 $tilde(X)_(ol(x))$ 是严格 Hensel 的，$Gamma(tilde(X)_(ol(x)), -)$ 正合，且同构于 $(-)_(ol(x))$。因此 $R Gamma(tilde(X)_(ol(x)), -) = (-)_(ol(x))$，从而对任意复形 $cal(K) in D^+ (X_et, Lambda)$，都有如下限制态射： 

  $
    alpha_(cal(K),ol(x),ol(t)): cal(K)_(ol(x)) -> R Gamma(F_(ol(x),ol(t)), cal(K)|_(F_(ol(x),ol(t))))
  $
  我们规定： 

  - 若对 $tilde(S)_(ol(s))$ 的任意几何点 $ol(t)$，$alpha_(cal(K),ol(x),ol(t))$ 都是同构，则称 $f$ 在 $ol(x)$ 处*关于 $cal(K)$ 局部零调*。 

  - 若 $f$ 在每个几何点处都关于 $cal(K)$ 局部零调，则称它*关于 $cal(K)$ 局部零调*；若对每个自然数 $n in cal(O)_S^times$，$f$ 都关于 $ul(ZZ\/n)$ 局部零调，则称它*局部零调*。 

  - 若沿任意 $g: S' -> S$ 作基变换所得的 $f': X' -> S'$ 都（关于 $g^(-1) cal(K)$）局部零调，则称 $f$（关于 $cal(K)$）是*泛局部零调* (universally locally acyclic)。 

  注意： 
  
  // - 由 @bc-along-extension-of-sep-cl-fields，只要 $cal(K) in D^+_(#[tor]\/S) (X_et, Lambda)$，性质“$alpha_(cal(K),ol(x),ol(t))$ 是同构”就与 $tilde(S)_(ol(s))$ 中同一点上方不同几何点 $ol(t)$ 的选取无关。因此，对这类复形检验局部零调性时，不妨假设 $ol(t)$ 是代数几何点。 

  - 局部零调性只依赖于映射 $tilde(X)_(ol(x)) -> tilde(S)_(ol(s))$。特别地，它是平展局部的性质，并且与 $X$ 中点 $x$ 上方几何点 $ol(x)$ 的选取无关。 
]

局部零调性是 $cal(K)$ 在泛纤维与特殊纤维上的上同调之间的一种相容性条件，下面的命题说明了这一点。 

#proposition(name: <loc-acyc-alt-desc>)[
  设 $f: X -> S$ 是概形态射，$cal(K) in D^+ (X_et, Lambda)$。对 $S$ 的几何点 $ol(s)$，以下条件等价： 

  + $f: X -> S$ 在 $X_(ol(s))$ 的每个几何点处都关于 $cal(K)$ 局部零调； 

  + 对 $tilde(S)_(ol(s))$ 的任意几何点 $ol(t)$，作拉回图表：#h(1fr)
    // https://q.uiver.app/#r=typst&q=WzAsNixbMCwwLCJYXyhvbCh0KSkiXSxbMSwwLCJYIHRpbWVzX1MgdGlsZGUoUylfKG9sKHMpKSJdLFsyLDAsIlhfKG9sKHMpKSJdLFsyLDEsIm9sKHMpIl0sWzEsMSwidGlsZGUoUylfKG9sKHMpKSJdLFswLDEsIm9sKHQpIl0sWzUsNCwiaiIsMl0sWzMsNCwiaSJdLFsyLDMsImZfKG9sKHMpKSJdLFsxLDQsInRpbGRlKGYpIl0sWzAsNSwiZl8ob2wodCkpIiwyXSxbMiwxLCJpJyIsMl0sWzAsMSwiaiciXV0=
    #align(center, diagram({
      node((0, 0), [$X_(ol(t))$])
      node((1, 0), [$X times_S tilde(S)_(ol(s))$])
      node((2, 0), [$X_(ol(s))$])
      node((2, 1), [$ol(s)$])
      node((1, 1), [$tilde(S)_(ol(s))$])
      node((0, 1), [$ol(t)$])
      edge((0, 1), (1, 1), [$j$], label-side: right, "->")
      edge((2, 1), (1, 1), [$i$], label-side: left, "->")
      edge((2, 0), (2, 1), [$f_(ol(s))$], label-side: left, "->")
      edge((1, 0), (1, 1), [$tilde(f)$], label-side: left, "->")
      edge((0, 0), (0, 1), [$f_(ol(t))$], label-side: right, "->")
      edge((2, 0), (1, 0), [$i'$], label-side: right, "->")
      edge((0, 0), (1, 0), [$j'$], label-side: left, "->")
    }))
    并令 $tilde(cal(K)) = cal(K)|_(X times_S tilde(S)_(ol(s)))$。则单位映射：
    $
      i'^(-1) tilde(cal(K)) -> i'^(-1) R j'_* j'^(-1) tilde(cal(K))
    $
    是同构。 
]
#proof[
  我们为条件 (2) 找一个等价表述。对 $X_(ol(s))$ 的任意几何点 $ol(x)$（它同时也是 $X$ 的几何点）取茎，单位映射便成为： 
  $
    cal(K)_(ol(x)) -> (R j'_* j'^(-1) tilde(cal(K)))_(i'(ol(x))) cong R Gamma(X_(ol(t)) times_(X times_S tilde(S)_(ol(s))) (X times_S tilde(S)_(ol(s)))^tilde_(i'(ol(x))), tilde(cal(K))|_(X_(ol(t)) times_(X times_S tilde(S)_(ol(s))) (X times_S tilde(S)_(ol(s)))^tilde_(i'(ol(x)))))
  $
  注意： 
  $
    X_(ol(t)) times_(X times_S tilde(S)_(ol(s))) (X times_S tilde(S)_(ol(s)))^tilde_(i'(ol(x))) = ol(t) times_(tilde(S)_(ol(s))) (X times_S tilde(S)_(ol(s)))^tilde_(i'(ol(x)))
  $
  我们断言：由投影 $X times_S tilde(S)_(ol(s)) -> X$ 给出的典范映射 $(X times_S tilde(S)_(ol(s)))^tilde_(i'(ol(x))) -> tilde(X)_(ol(x))$ 是同构。 

  - 事实上，这相当于要证明：#h(1fr)
    $
      cal(O)_(X,x)^#[sh] cong (cal(O)_(X,x) otimes_(cal(O)_(S,s)) cal(O)_(S,s)^#[sh])^#[sh]_(ker(cal(O)_(X,x) otimes_(cal(O)_(S,s)) cal(O)_(S,s)^#[sh] -> k(ol(x))))
    $
    由于 $cal(O)_(S,s)^#[sh]$ 是拟有限 $cal(O)_(S,s)$-代数的滤余极限，可以引用 @strict-henselizations-tensors-and-qfinites；而右端恰好就是 $cal(O)_(X,x)^#[sh] otimes_(cal(O)_(S,s)^#[sh]) cal(O)_(S,s)^#[sh] cong cal(O)_(X,x)^#[sh]$。 
    

  总之，所讨论的单位映射变成： 
  $
    cal(K)_(ol(x)) = R Gamma(tilde(X)_(ol(x)), cal(K)|_(tilde(X)_(ol(x)))) -> R Gamma(ol(t) times_(tilde(S)_(ol(s))) tilde(X)_(ol(x)), cal(K)|_(ol(t) times_(tilde(S)_(ol(s))) tilde(X)_(ol(x))))
  $
  即限制映射。存在几何点之间的典范映射 $f(ol(x)) -> ol(s)$，它诱导典范同构 $tilde(S)_(ol(s)) cong tilde(S)_(f(ol(x)))$。在这个同构下，上面的限制映射就是： 
  $
    cal(K)_(ol(x)) = R Gamma(tilde(X)_(ol(x)), cal(K)|_(tilde(X)_(ol(x)))) -> R Gamma(F_(ol(x),ol(t)), cal(K)|_(F_(ol(x),ol(t))))
  $
  其中 $F_(ol(x),ol(t))$ 是消没圈簇。这恰好就是局部零调性定义中的映射 $alpha_(cal(K),ol(x),ol(t))$。 
  
  因此，通过检查茎可知，条件 (2) 等价于下述陈述： 

  - 对 $X_(ol(s))$ 的任意几何点 $ol(x)$ 与 $tilde(S)_(f(ol(x)))$ 的任意几何点 $ol(t)$，#h(1fr)
    $
      alpha_(cal(K),ol(x),ol(t)): cal(K)_(ol(x)) = R Gamma(tilde(X)_(ol(x)), cal(K)|_(tilde(X)_(ol(x)))) -> R Gamma(F_(ol(x),ol(t)), cal(K)|_(F_(ol(x),ol(t))))
    $
    是同构。 

  按定义，这正是 $f$ 在 $X_(ol(s))$ 的每个几何点 $ol(x)$ 处的局部零调性，即条件 (1)。 
]

现在可以建立局部零调性与基变换之间的联系了。 

#theorem(name: <loc-acyc-and-base-change>)[
  设 $Lambda$ 是挠 Noether 环，$S$ 是 Noether 概形，$g: S' -> S$ 是态射，且 $cal(L)_S in D^b_#[ctf] (S'_et, Lambda)$。 
  
  则下列陈述之间有 (1) $==>$(2) $==>$(3)；此外，若每个有限 $Lambda$-模都能嵌入某个有限自由 $Lambda$-模，则还有 (3) $==>$(1)。 

  + 对拟紧拟分离 $S$-概形之间的任意态射 $f: X -> Y$，作基变换得到如下拉回方块： 
    $
      // http://q.uiver.app/#r=typst&q=WzAsNCxbMCwwLCJYJyJdLFsxLDAsIlknIl0sWzAsMSwiWCJdLFsxLDEsIlkiXSxbMiwzLCJmIiwyXSxbMCwxLCJmJyJdLFsxLDMsImciXSxbMCwyLCJnJyIsMl1d
      #align(center, diagram({
        node((0, 0), [$X'$])
        node((1, 0), [$Y'$])
        node((0, 1), [$X$])
        node((1, 1), [$Y$])
        node((0.3, 0.3), $cart$)
        edge((0, 1), (1, 1), [$f$], label-side: right, "->")
        edge((0, 0), (1, 0), [$f'$], label-side: left, "->")
        edge((1, 0), (1, 1), [$g_Y$], label-side: left, "->")
        edge((0, 0), (0, 1), [$g_X$], label-side: right, "->")
      }))
    $
    并令 $cal(L)_X = cal(L)_S|_(X')$、$cal(L)_Y = cal(L)_S|_(Y')$。则相对基变换映射： 
    $
      g_Y^(-1) R f_* cal(K) Lotimes_Lambda cal(L)_Y -> R f'_* (g_X^(-1) cal(K) Lotimes_Lambda cal(L)_X)
    $
    对一切 $cal(K) in D^+ (X_et, Lambda)$ 都是同构。 

  + $g$ 关于 $cal(L)_S$ 泛局部零调。 

  + 设 $X$ 是任一 $S$-概形，它是某个有限型 $S$-概形在其函数域代数闭包中的正规化，其泛点为 $xi$。则基变换 $g_X: X' -> X$ 与 $cal(L)_X = cal(L)_S|_(X')$ 满足： 

    - 对极稠密子集 $E subset X'$，以及 $E$ 中每一点上方的一族几何点 ${ol(x')}$，映射： 
      $
        alpha_(ol(x'),xi): (cal(L)_X)_(ol(x')) -> R Gamma(F_(ol(x'),xi), cal(L)_X|_(F_(ol(x'),xi)))
      $
      是同构。 

    特别地，若 $g_X$ 关于 $cal(L)_X$ 局部零调，则上述条件自动成立。 
]
#proof[
  (1) $==>$(2)：先设我们能由 (1) 推出 $g$ 局部零调。注意条件 (1) 在拟紧拟分离基变换下保持不变。于是对每个拟紧拟分离态射 $X -> S$，基变换 $g_X: X' -> X$ 都关于 $cal(L)_X$ 局部零调。现在设 $h: X -> S$ 是任意态射。要证 $g_X: X' -> X$ 关于 $cal(L)_X$ 局部零调，可以用局部零调性的平展局部性：只需对任意仿射开集 $U subset X$ 证明 $g_U: U' -> U$ 关于 $cal(L)_U$ 局部零调。而这一点已经得证，因为 $U -> S$ 是拟紧拟分离的。 

  于是，只需证明 $g$ 局部零调。 

  #lemma[
    对拉回图表， 
    $
      // http://localhost:8000/#r=typst&q=WzAsNCxbMCwwLCJYJyJdLFsxLDAsIlknIl0sWzAsMSwiWCJdLFsxLDEsIlkiXSxbMiwzLCJmIiwyXSxbMCwxLCJmJyJdLFsxLDMsImciXSxbMCwyLCJnJyIsMl1d
      #align(center, diagram({
        node((0, 0), [$X'$])
        node((1, 0), [$Y'$])
        node((0, 1), [$X$])
        node((1, 1), [$Y$])
        node((0.3, 0.3), $cart$)
        edge((0, 1), (1, 1), [$f$], label-side: right, "->")
        edge((0, 0), (1, 0), [$f'$], label-side: left, "->")
        edge((1, 0), (1, 1), [$g$], label-side: left, "->")
        edge((0, 0), (0, 1), [$g'$], label-side: right, "->")
      }))
    $
    并设 $cal(L) in D(Y'_et, Lambda)$，则单位映射 $cal(L) -> R f'_* f'^(-1) cal(L)$ 是如下复合： 
    $
      cal(L) cong g^(-1) ul(Lambda) Lotimes_Lambda cal(L) -> g^(-1) R f_* ul(Lambda) Lotimes_Lambda cal(L) -> R f'_* (g'^(-1) ul(Lambda) Lotimes_Lambda f'^(-1) cal(L)) cong R f'_* f'^(-1) cal(L)
    $
    其中第一个映射是单位，第二个映射是相对基变换。 
  ]
  #proof[
    在伴随之下，这个映射就是： 
    $
      f'^(-1) cal(L) cong g'^(-1) f^(-1) ul(Lambda) Lotimes_Lambda f'^(-1) cal(L) cong g'^(-1) ul(Lambda) Lotimes_Lambda f'^(-1) cal(L) cong f'^(-1) cal(L)
    $
    其中每一步都是恒等映射。证毕。 
  ]

  现在来证明局部零调性。取 $S$ 的任意代数几何点 $ol(s)$，以及 $tilde(S)_(ol(s))$ 的任意代数几何点 $ol(t)$。作拉回图表： 
  #align(center, diagram({
    node((0, 0), [$S'_(ol(t))$])
    node((1, 0), [$S' times_S tilde(S)_(ol(s))$])
    node((2, 0), [$S'_(ol(s))$])
    node((2, 1), [$ol(s)$])
    node((1, 1), [$tilde(S)_(ol(s))$])
    node((0, 1), [$ol(t)$])
    edge((0, 1), (1, 1), [$j$], label-side: right, "->")
    edge((2, 1), (1, 1), [$i$], label-side: left, "->")
    edge((2, 0), (2, 1), [$g_(ol(s))$], label-side: left, "->")
    edge((1, 0), (1, 1), [$tilde(g)$], label-side: left, "->")
    edge((0, 0), (0, 1), [$g_(ol(t))$], label-side: right, "->")
    edge((2, 0), (1, 0), [$i'$], label-side: right, "->")
    edge((0, 0), (1, 0), [$j'$], label-side: left, "->")
  }))
  并令 $tilde(cal(L)) = cal(L)_S|_(S' times_S tilde(S)_(ol(s)))$。由前一个引理，单位映射：
  $
    tilde(cal(L)) -> R j'_* j'^(-1) tilde(cal(L))
  $
  分解为： 
  $
    tilde(cal(L)) cong tilde(g)^(-1) ul(Lambda) Lotimes_Lambda tilde(cal(L)) -> tilde(g)^(-1) R j_* ul(Lambda) Lotimes_Lambda tilde(cal(L)) -> R j'_* (g_(ol(t))^(-1) ul(Lambda) Lotimes_Lambda j'^(-1) tilde(cal(L))) cong R j'_* j'^(-1) tilde(cal(L)) 
  $
  现在 $ol(t) -> tilde(S)_(ol(s))$ 是拟紧拟分离概形之间的态射，所以第二个映射是沿左侧方块、关于 $cal(L)|_(S' times_S tilde(S)_(ol(s)))$ 的相对基变换，从而是同构。因此，要证： 
  $
    i'^(-1) tilde(cal(L)) -> i'^(-1) R j'_* j'^(-1) tilde(cal(L))
  $
  是同构，只需证明 $tilde(g)^(-1) ul(Lambda) Lotimes_Lambda tilde(cal(L)) -> tilde(g)^(-1) R j_* ul(Lambda) Lotimes_Lambda tilde(cal(L))$ 沿 $i'^(-1)$ 拉回后是同构。也就是说，需要证明： 
  $
    g_(ol(s))^(-1) i^(-1) ul(Lambda) -> g_(ol(s))^(-1) i^(-1) R j_* ul(Lambda)
  $
  是同构。于是只需证明 $ul(Lambda) -> i^(-1) R j_* ul(Lambda)$ 是同构，即 $(R j_* ul(Lambda))_(ol(s)) = Lambda$。事实上， 
  $
    (R j_* ul(Lambda))_(ol(s)) = R Gamma(ol(t) times_(tilde(S)_(ol(s))) (tilde(S)_(ol(s)))^tilde_(ol(s)), ul(Lambda)) = R Gamma(ol(t) times_(tilde(S)_(ol(s))) tilde(S)_(ol(s)), ul(Lambda)) = R Gamma(ol(t), ul(Lambda)) = Lambda
  $
  这就证明了 $i'^(-1) tilde(cal(L)) -> i'^(-1) R j'_* j'^(-1) tilde(cal(L))$ 是同构。于是由 @loc-acyc-alt-desc，$g$ 局部零调。 

  (2) $==>$(3) 是显然的。 

  (3) $==>$(1)：回忆我们假设了每个有限 $Lambda$-模都能嵌入某个有限自由 $Lambda$-模。由 @rel-bc-reductions，只需在下列情形证明结论：$X = Spec(A)$ 是某个有限型 $S$-概形在其函数域 $K$ 的代数闭包中的正规化，$j: xi = Spec(K) -> X$ 是泛点的包含，且给定拉回图表： 
  // https://q.uiver.app/#r=typst&q=WzAsNCxbMCwwLCJ4aSciXSxbMCwxLCJ4aSJdLFsxLDEsIlgiXSxbMSwwLCJYJyJdLFszLDIsImdfWCJdLFswLDEsImdfeGkiLDJdLFsxLDIsImoiLDJdLFswLDMsImonIl1d
  #align(center, diagram({
    node((0, 0), [$X'_xi$])
    node((0, 1), [$xi$])
    node((1, 1), [$X$])
    node((1, 0), [$X'$])
    node((0.3, 0.3), $cart$)
    edge((1, 0), (1, 1), [$g_X$], label-side: left, "->")
    edge((0, 0), (0, 1), [$g_xi$], label-side: right, "->")
    edge((0, 1), (1, 1), [$j$], label-side: right, "->")
    edge((0, 0), (1, 0), [$j'$], label-side: left, "->")
  }))
  相对基变换： 
  $
    g_X^(-1) R j_* ul(Lambda) Lotimes_Lambda cal(L)_X -> R j'_* j'^(-1) cal(L)_X
  $
  （其中 $cal(L)_X = cal(L)_S|_(X')$）是同构。 

  我们先证明一个关于函数域代数闭的整正规概形的引理。 

  #lemma(name: <integral-normal-affine-with-ac-func-field>)[
    设 $S = Spec(A)$ 是仿射的整正规概形，其函数域 $K$ 代数闭。则： 

    (1) $A[T]$ 中任意首一多项式都在 $A$ 中完全分裂；把 $A$ 换成 $S$ 的局部环后，同样的结论成立； 

    (2) $S$ 的局部环都是整的、正规的、严格 Hensel 的，且剩余域代数闭。 
  ]
  #proof[
    (1) 由于 $K$ 代数闭，$A[T]$ 中任意首一多项式在 $K$ 中完全分裂。又因 $A$ 在 $K$ 中整闭，该首一多项式的根必落在 $A$ 中。于是它在 $A$ 中完全分裂。 

    对 $S$ 的局部环，同样的论证适用，因为这些局部环也是整正规的，且分式域都是代数闭域 $K$。 

    (2) 设 $frak(p) in Spec(A)$。对首一多项式 $f_0 (T) in k(frak(p))[T]$，我们可以把它提升为首一多项式 $f(T) in A_(frak(p)) [T]$。由 (1)，$f(T)$ 在 $A_(frak(p))$ 上完全分裂。模去 $frak(p) A_(frak(p))$ 作约化，即知 $f_0 (T)$ 在 $k(frak(p))$ 中完全分裂。 

    对任意约化到 $f_0 (T) in k(frak(p))[T]$ 的首一多项式 $f(T) in A_(frak(p)) [T]$，$f(T)$ 在 $A_(frak(p))$ 上完全分裂，且其根约化后给出 $f_0 (T)$ 的根。于是 Hensel 引理平凡成立，因为 $f_0 (T)$ 的每个根都平凡地提升为 $f(T)$ 的某个根。因此 $A_(frak(p))$ 是 Hensel 的。又因其剩余域代数闭（从而可分闭），$A_(frak(p))$ 是严格 Hensel 的。 
  ]

  注意，由 @generic-pt-pushforward-of-const-shv-on-normal-sch 与 @geom-point-pushforward-exact， 
  $
    R j_* ul(Lambda) cong ul(Lambda)
  $
  从而 $g_X^(-1) R j_* ul(Lambda) Lotimes_Lambda cal(L)_X cong cal(L)_X$。于是只需证明单位映射： 
  $
    cal(L)_X -> R j'_* j'^(-1) cal(L)_X
  $
  是同构，因为由 (3)，$g_X$ 关于 $cal(L)_X$ 局部零调。 

  取 $X'$ 的几何点 $ol(x')$，它位于 $x in X$ 上方，是假设中为 $E$ 上每一点选定的那族几何点 ${ol(x')}$ 中的一个，于是： 
  $
    (R j'_* j'^(-1) cal(L)_X)_(ol(x')) = R Gamma(xi times_X tilde(X')_(ol(x')), cal(L)_X|_(tilde(X')_(ol(x'))))
  $
  由 @integral-normal-affine-with-ac-func-field，$x$ 总是 $X$ 的几何点，且：  
  $
    xi = xi times_X tilde(X)_x
  $
  于是， 
  $
    (R j'_* j'^(-1) cal(L)_X)_(ol(x')) = R Gamma(xi times_X tilde(X')_(ol(x')), cal(L)_X|_(tilde(X')_(ol(x')))) = R Gamma(xi times_(tilde(X)_x) tilde(X')_(ol(x')), cal(L)_X|_(xi times_(tilde(X)_x) tilde(X')_(ol(x')))) = R Gamma(F_(ol(x'),xi), cal(L)_X|_(F_(ol(x'),xi)))
  $
  因此单位映射 $cal(L)_X -> R j'_* j'^(-1) cal(L)_X$ 的茎就是限制映射： 
  $
    (cal(L)_X)_(ol(x')) -> R Gamma(F_(ol(x'),xi), cal(L)_X|_(F_(ol(x'),xi)))
  $
  由假设它是同构。证毕。 
  /*由上述引理，$X$ 的每个点都是几何点。对点 $x in X$，作拉回图表： 
  // https://q.uiver.app/#r=typst&q=WzAsNixbMCwwLCJ4aSciXSxbMCwxLCJ4aSJdLFsxLDEsInRpbGRlKFgpXyhvbCh4KSkiXSxbMSwwLCJYJyB0aW1lc19YIHRpbGRlKFgpXyhvbCh4KSkiXSxbMiwxLCJ4Il0sWzIsMCwieCciXSxbMywyLCJnX1giXSxbMCwxLCJnX3hpIiwyXSxbMSwyLCJqIiwyXSxbMCwzLCJqJyJdLFs0LDIsImkiXSxbNSw0LCJnX3giXSxbNSwzLCJpJyIsMl1d
  #align(center, diagram({
    node((0, 0), [$X'_xi$])
    node((0, 1), [$xi$])
    node((1, 1), [$tilde(X)_(x)$])
    node((1, 0), [$X' times_X tilde(X)_(x)$])
    node((2, 1), [$x$])
    node((2, 0), [$x'$])
    edge((1, 0), (1, 1), [$g_X$], label-side: left, "->")
    edge((0, 0), (0, 1), [$g_xi$], label-side: right, "->")
    edge((0, 1), (1, 1), [$j_1$], label-side: right, "->")
    edge((0, 0), (1, 0), [$tilde(j)$], label-side: left, "->")
    edge((2, 1), (1, 1), [$tilde(i)$], label-side: left, "->")
    edge((2, 0), (2, 1), [$g_x$], label-side: left, "->")
    edge((2, 0), (1, 0), [$i'$], label-side: right, "->")
  }))
  再在底部接上两个拉回方块： 
  // https://q.uiver.app/#r=typst&q=WzAsOSxbMCwwLCJ4aSciXSxbMCwxLCJ4aSJdLFsxLDEsInRpbGRlKFgpX3giXSxbMSwwLCJYJyB0aW1lc19YIHRpbGRlKFgpX3giXSxbMiwxLCJ4Il0sWzIsMCwieCciXSxbMSwyLCJYIl0sWzIsMiwieCJdLFswLDIsInhpIl0sWzMsMiwidGlsZGUoZykiXSxbMCwxLCJnX3hpIiwyXSxbMSwyLCJqXzEiLDJdLFswLDMsImonIl0sWzQsMiwiaV8xIl0sWzUsNCwiZ194Il0sWzUsMywiaSciLDJdLFsyLDYsImdhbW1hIl0sWzgsNiwiaiIsMl0sWzcsNiwiaSJdLFs0LDcsIiIsMix7InN0eWxlIjp7ImJvZHkiOnsibmFtZSI6ImRvdWJsZSBiYXJyZWQifX19XSxbMSw4LCIiLDIseyJzdHlsZSI6eyJib2R5Ijp7Im5hbWUiOiJkb3VibGUgYmFycmVkIn19fV1d
  #align(center, diagram({
    node((0, 0), [$X'_xi$])
    node((0, 1), [$xi$])
    node((1, 1), [$tilde(X)_x$])
    node((1, 0), [$X' times_X tilde(X)_x$])
    node((2, 1), [$x$])
    node((2, 0), [$X'_x$])
    node((1, 2), [$X$])
    node((2, 2), [$x$])
    node((0, 2), [$xi$])
    edge((1, 0), (1, 1), [$tilde(g)$], label-side: left, "->")
    edge((0, 0), (0, 1), [$g_xi$], label-side: right, "->")
    edge((0, 1), (1, 1), [$j_1$], label-side: right, "->")
    edge((0, 0), (1, 0), [$tilde(j)$], label-side: left, "->")
    edge((2, 1), (1, 1), [$i_1$], label-side: left, "->")
    edge((2, 0), (2, 1), [$g_x$], label-side: left, "->")
    edge((2, 0), (1, 0), [$tilde(i)$], label-side: right, "->")
    edge((1, 1), (1, 2), [$gamma$], label-side: left, "->")
    edge((0, 2), (1, 2), [$j$], label-side: right, "->")
    edge((2, 2), (1, 2), [$i$], label-side: left, "->")
    edge((2, 1), (2, 2), "=")
    edge((0, 1), (0, 2), "=")
  }))
  由 @loc-acyc-alt-desc，单位映射： 
  $
    tilde(i)^(-1) (cal(L)_X|_(X' times_X tilde(X)_x)) -> tilde(i)^(-1) R tilde(j)_* tilde(j)^(-1) (cal(L)_X|_(X' times_X tilde(X)_x))
  $
  是同构。取茎，这说明
  $
    
  $*/
]

我们已经看到局部零调性与基变换之间的紧密联系。接下来我们研究余特殊化映射 (cospecialization map)——这是由局部零调性产生的一种构造——并研究那些让我们得以运用局部零调性的性质。 

#properties(name: <loc-acyc-and-limits-of-qfinite>)[
  在概形的拉回图表中： 
  // https://q.uiver.app/#r=typst&q=WzAsNCxbMCwwLCJYJyJdLFswLDEsIlMnIl0sWzEsMCwiWCJdLFsxLDEsIlMiXSxbMSwzLCJnIiwyXSxbMCwyLCJnJyJdLFsyLDMsImYiXSxbMCwxLCJmJyIsMl1d
  #align(center, diagram({
    node((0, 0), [$X'$])
    node((0, 1), [$S'$])
    node((1, 0), [$X$])
    node((1, 1), [$S$])
    node((0.3, 0.3), $cart$)
    edge((0, 1), (1, 1), [$g$], label-side: right, "->")
    edge((0, 0), (1, 0), [$g'$], label-side: left, "->")
    edge((1, 0), (1, 1), [$f$], label-side: left, "->")
    edge((0, 0), (0, 1), [$f'$], label-side: right, "->")
  }))
  设 $ol(x')$ 是 $X'$ 的几何点，$ol(x) = g'(ol(x'))$。假设 $S'$ 是带仿射过渡映射的局部拟有限 $S$-概形的逆向极限。则：
    
  - 若 $f$ 在 $ol(x)$ 处关于 $cal(K)$ 局部零调，则 $f'$ 在 $ol(x')$ 处关于 $cal(K)|_(X')$ 局部零调。 
]
#proof[
  (1) 令 $ol(s') = f'(ol(x')), ol(s) = f(ol(x))$。取 $tilde(S')_(ol(s'))$ 的几何点 $ol(t')$，它位于 $tilde(S)_(ol(s))$ 的几何点 $ol(t)$ 上方。现在比较两个消没圈簇：一个是 
  $
    F_(ol(x'),ol(t')) = ol(t') times_(tilde(S')_(ol(s'))) tilde(X')_(ol(x')) 
  $
  另一个是 
  $
    F_(ol(x),ol(t)) = ol(t) times_(tilde(S)_(ol(s))) tilde(X)_(ol(x))
  $

  在 @strict-henselizations-tensors-and-qfinites 中取 $Omega$ 为 $ol(x')$ 的剩余域，得： 
  $
    cal(O)_(X,ol(x))^#[sh] otimes_(cal(O)_(s,ol(s))^#[sh]) cal(O)_(S',ol(s'))^#[sh] cong cal(O)_(X',ol(x'))
  $
  于是： 
  $
    Omega otimes_(cal(O)_(S',ol(s'))^#[sh]) cal(O)_(X',ol(x')) cong Omega otimes_(cal(O)_(s,ol(s))^#[sh]) cal(O)_(X,ol(x))^#[sh]
  $
  即 $F_(ol(x'),ol(t')) cong F_(ol(x),ol(t))$。现在，由 $f$ 在 $ol(x)$ 处关于 $cal(K)$ 的局部零调性，映射
  $
    cal(K)_(ol(x)) -> R Gamma(F_(ol(x),ol(t)), cal(K)|_(F_(ol(x),ol(t))))
  $
  是同构，因此 $cal(K)_(ol(x)) -> R Gamma(F_(ol(x'),ol(t')), cal(K)|_(F_(ol(x'),ol(t'))))$ 也必是同构。因此 $f'$ 在 $ol(x')$ 处关于 $cal(K)|_(X')$ 局部零调。 
]

#construction(name: <cospecialization-map>)[
  设 $cal(K) in D^+ (X_et, Lambda)$，$f: X -> S$ 是关于 $cal(K)$ 局部零调的态射。对 $S$ 的任意几何点 $ol(s)$ 与 $tilde(S)_(ol(s))$ 的任意几何点 $ol(t)$，作拉回图表：#h(1fr)
    // https://q.uiver.app/#r=typst&q=WzAsNixbMCwwLCJYXyhvbCh0KSkiXSxbMSwwLCJYIHRpbWVzX1MgdGlsZGUoUylfKG9sKHMpKSJdLFsyLDAsIlhfKG9sKHMpKSJdLFsyLDEsIm9sKHMpIl0sWzEsMSwidGlsZGUoUylfKG9sKHMpKSJdLFswLDEsIm9sKHQpIl0sWzUsNCwiaiIsMl0sWzMsNCwiaSJdLFsyLDMsImZfKG9sKHMpKSJdLFsxLDQsInRpbGRlKGYpIl0sWzAsNSwiZl8ob2wodCkpIiwyXSxbMiwxLCJpJyIsMl0sWzAsMSwiaiciXV0=
    #align(center, diagram({
      node((0, 0), [$X_(ol(t))$])
      node((1, 0), [$X times_S tilde(S)_(ol(s))$])
      node((2, 0), [$X_(ol(s))$])
      node((2, 1), [$ol(s)$])
      node((1, 1), [$tilde(S)_(ol(s))$])
      node((0, 1), [$ol(t)$])
      edge((0, 1), (1, 1), [$j$], label-side: right, "->")
      edge((2, 1), (1, 1), [$i$], label-side: left, "->")
      edge((2, 0), (2, 1), [$f_(ol(s))$], label-side: left, "->")
      edge((1, 0), (1, 1), [$tilde(f)$], label-side: left, "->")
      edge((0, 0), (0, 1), [$f_(ol(t))$], label-side: right, "->")
      edge((2, 0), (1, 0), [$i'$], label-side: right, "->")
      edge((0, 0), (1, 0), [$j'$], label-side: left, "->")
    }))
    并令 $tilde(cal(K)) = cal(K)|_(X times_S tilde(S)_(ol(s)))$。由 @loc-acyc-alt-desc，单位映射：
    $
      beta_(cal(K),ol(s),ol(t)): i'^(-1) tilde(cal(K)) -> i'^(-1) R j'_* j'^(-1) tilde(cal(K))
    $
    是 $D^+ ((X_(ol(s)))_et, Lambda)$ 中的复形同构。于是可以定义如下复合： 
    $
      R Gamma(X_(ol(t)), cal(K)|_(X_(ol(t)))) &= R Gamma(X_(ol(t)), j'^(-1) tilde(cal(K))) = R Gamma(X times_S tilde(S)_(ol(s)), R j'_* j'^(-1) tilde(cal(K))) \
      &-> R Gamma(X_(ol(s)), i'^(-1) R j'_* j'^(-1) tilde(cal(K))) \
      &->^(beta_(cal(K),ol(s),ol(t))^(-1)) R Gamma(X_(ol(s)), i'^(-1) tilde(cal(K))) = R Gamma(X_(ol(s)), cal(K)|_(X_(ol(s))))
    $
    其中第一个映射是沿 $i'^(-1)$ 的限制，第二个映射由同构 $beta_(cal(K),ol(s),ol(t))$ 的逆诱导。这个映射称为*余特殊化映射*，记作： 
    $
      cosp: R Gamma(X_(ol(t)), cal(K)|_(X_(ol(t)))) -> R Gamma(X_(ol(s)), cal(K)|_(X_(ol(s))))
    $
    按构造，沿几何点的一般化链，余特殊化映射具有传递性。 
]

#proposition(name: <loc-acyc-sp-cosp-square>)[
  设 $f: X -> S$ 是拟紧拟分离的态射，且关于 $cal(K) in D^+ (X_et, Lambda)$ 局部零调。则对 $S$ 的每个几何点 $ol(s)$、每个 $ol(s)$ 的一般化（即 $tilde(S)_(ol(s))$ 的几何点 $ol(t)$），下图交换： 
  // https://q.uiver.app/#r=typst&q=WzAsNCxbMCwwLCIoUiBmXyogY2FsKEspKV8ob2wocykpIl0sWzAsMSwiKFIgZl8qIGNhbChLKSlfKG9sKHQpKSJdLFsxLDAsIlIgR2FtbWEoWF8ob2wocykpLCBjYWwoSyl8XyhYXyhvbChzKSkpKSJdLFsxLDEsIlIgR2FtbWEoWF8ob2wodCkpLCBjYWwoSyl8XyhYXyhvbCh0KSkpKSJdLFswLDIsIkJDIl0sWzEsMywiQkMiLDJdLFswLDEsInNwIiwyXSxbMiwzLCJjb3NwIl1d
  #align(center, diagram({
    node((0, 0), [$(R f_* cal(K))_(ol(s))$])
    node((0, 1), [$(R f_* cal(K))_(ol(t))$])
    node((1, 0), [$R Gamma(X_(ol(s)), cal(K)|_(X_(ol(s))))$])
    node((1, 1), [$R Gamma(X_(ol(t)), cal(K)|_(X_(ol(t))))$])
    edge((0, 0), (1, 0), [$BC$], label-side: left, "->")
    edge((0, 1), (1, 1), [$BC$], label-side: right, "->")
    edge((0, 0), (0, 1), [$sp$], label-side: right, "->")
    edge((1, 1), (1, 0), [$cosp$], label-side: right, "->")
  }))
  其中水平映射是基变换，左边的映射是特殊化映射，右边的映射是余特殊化映射。 
]
#proof[
  展开定义即可看出，我们可以把 $f: X -> S$ 换成 $tilde(f): tilde(X) = X times_S tilde(S)_(ol(s)) -> tilde(S)_(ol(s))$，把 $cal(K)$ 换成 $tilde(cal(K)) = cal(K)|_(X times_S tilde(S)_(ol(s)))$。理由如下： 

  - $tilde(f)$ 关于 $tilde(cal(K))$ 局部零调。事实上，$tilde(S)_(ol(s)) -> S$ 是 $S$ 中 $ol(s)$ 的平展邻域的逆向极限，因此 $tilde(S)_(ol(s))$ 是拟有限 $S$-概形的逆向极限。由 @loc-acyc-and-limits-of-qfinite，$tilde(f)$ 关于 $tilde(cal(K))$ 局部零调。 

  - 由 @derived-stalks-of-derived-pushforward，有同构： 
    $
      (R f_* cal(K))_(ol(t)) = R Gamma(X times_S tilde(S)_(ol(t)), cal(K)|_(X times_S tilde(S)_(ol(t)))) = R Gamma(tilde(X) times_(tilde(S)_(ol(s))) (tilde(S)_(ol(s)))^tilde_(ol(t)), tilde(cal(K))|_(tilde(X) times_(tilde(S)_(ol(s))) (tilde(S)_(ol(s)))^tilde_(ol(t)))) = (R tilde(f)_* tilde(cal(K)))_(ol(t))
    $
    这些同构与限制、以及与取茎的基变换（本质上都是限制）相容，从而与特殊化（本质上同样是限制）相容。于是图表左侧可以整体过渡过来。 

  - $cosp$ 的构造只依赖于映射 $tilde(f): X times_S tilde(S)_(ol(s))$ 以及它在 $ol(s)$ 与 $ol(t)$ 上方的纤维，所以图表右侧也可以整体过渡过去。 

  于是，不妨假设 $S$ 是严格 Hensel 局部环的谱，且 $ol(s)$ 是 $S$ 的闭点。 

  作拉回图表： 
  #align(center, diagram({
    node((0, 0), [$X_(ol(t))$])
    node((1, 0), [$X$])
    node((2, 0), [$X_(ol(s))$])
    node((2, 1), [$ol(s)$])
    node((1, 1), [$S$])
    node((0, 1), [$ol(t)$])
    edge((0, 1), (1, 1), [$j$], label-side: right, "->")
    edge((2, 1), (1, 1), [$i$], label-side: left, "->")
    edge((2, 0), (2, 1), [$f_(ol(s))$], label-side: left, "->")
    edge((1, 0), (1, 1), [$f$], label-side: left, "->")
    edge((0, 0), (0, 1), [$f_(ol(t))$], label-side: right, "->")
    edge((2, 0), (1, 0), [$i'$], label-side: right, "->")
    edge((0, 0), (1, 0), [$j'$], label-side: left, "->")
  }))

  检视特殊化与余特殊化的定义，我们需要证明下图交换： 

  // https://q.uiver.app/#r=typst&q=WzAsNixbMCwwLCJSIEdhbW1hKFgsIGNhbChLKSkiXSxbMSwwLCJSIEdhbW1hKFhfKG9sKHMpKSwgaSdeKC0xKSBjYWwoSykpIl0sWzAsMiwiUiBHYW1tYShYIHRpbWVzX1MgdGlsZGUoUylfKG9sKHQpKSwgY2FsKEspfF8oWCB0aW1lc19TIHRpbGRlKFMpXyhvbCh0KSkpKSJdLFsxLDIsIlIgR2FtbWEoWF8ob2wodCkpLCBqJ14oLTEpIGNhbChLKSkiXSxbMiwyLCJSIEdhbW1hKFgsIFIgaidfKiBqJ14oLTEpIGNhbChLKSkiXSxbMiwwLCJSIEdhbW1hKFhfKG9sKHMpKSwgaSdeKC0xKSBSIGonXyogaideKC0xKSBjYWwoSykpIl0sWzAsMiwicmVzIiwyXSxbMiwzLCJyZXMiLDJdLFswLDEsInJlcyJdLFszLDQsIiIsMix7InN0eWxlIjp7ImJvZHkiOnsibmFtZSI6ImRvdWJsZSBiYXJyZWQifX19XSxbMSw1LCJiZXRhIl0sWzQsNSwicmVzIiwyXV0=
  #align(center, diagram({
    node((0, 0), [$R Gamma(X, cal(K))$])
    node((1, 0), [$R Gamma(X_(ol(s)), i'^(-1) cal(K))$])
    node((0, 2), [$R Gamma(X times_S tilde(S)_(ol(t)), cal(K)|_(X times_S tilde(S)_(ol(t))))$])
    node((1, 2), [$R Gamma(X_(ol(t)), j'^(-1) cal(K))$])
    node((2, 2), [$R Gamma(X, R j'_* j'^(-1) cal(K))$])
    node((2, 0), [$R Gamma(X_(ol(s)), i'^(-1) R j'_* j'^(-1) cal(K))$])
    edge((0, 0), (0, 2), [$res$], label-side: right, "->")
    edge((0, 2), (1, 2), [$res$], label-side: right, "->")
    edge((0, 0), (1, 0), [$res$], label-side: left, "->")
    edge((1, 2), (2, 2), "=")
    edge((1, 0), (2, 0), [$beta$], label-side: left, "->")
    edge((2, 2), (2, 0), [$res$], label-side: right, "->")
  }))
  其中 $beta$ 是单位映射，各 $res$ 都是限制映射。左侧竖直与底部水平两个限制箭头的复合，就是限制映射 $res: R Gamma(X, cal(K)) -> R Gamma(X_(ol(t)), cal(K)|_(X_(ol(t))))$。现在在 $D(Lambda) cong D(ol(s)_et, Lambda)$ 之下，有自然同构： 
  $
    R Gamma(X, -) cong i^(-1) R f_* (-) \
    R Gamma(X_(ol(s)), -) cong R f_(ol(s),*) \
    R Gamma(X_(ol(t)), -) cong i^(-1) R j_* R f_(ol(t),*) cong i^(-1) R f_* R j'_*
  $
  在这个等同之下，只需验证下图交换： 
  // https://q.uiver.app/#r=typst&q=WzAsNCxbMCwwLCJpXigtMSkgUiBmXyogY2FsKEspIl0sWzAsMSwiaV4oLTEpIFIgZl8qIFIgaidfKiBqJ14oLTEpIGNhbChLKSJdLFsxLDEsIlIgZl8ob2wocyksKikgaSdeKC0xKSBSIGonXyogaideKC0xKSBjYWwoSykiXSxbMSwwLCJSIGZfKG9sKHMpLCopIGknXigtMSkgY2FsKEspIl0sWzAsMywiQkMiXSxbMywyXSxbMCwxXSxbMSwyLCJCQyIsMl1d
  #align(center, diagram({
    node((0, 0), [$i^(-1) R f_* cal(K)$])
    node((0, 1), [$i^(-1) R f_* R j'_* j'^(-1) cal(K)$])
    node((1, 1), [$R f_(ol(s),*) i'^(-1) R j'_* j'^(-1) cal(K)$])
    node((1, 0), [$R f_(ol(s),*) i'^(-1) cal(K)$])
    edge((0, 0), (1, 0), [$BC$], label-side: left, "->")
    edge((1, 0), (1, 1), "->")
    edge((0, 0), (0, 1), "->")
    edge((0, 1), (1, 1), [$BC$], label-side: right, "->")
  }))
  这不过是一个自然性方块。 
]

#corollary(name: <proper-loc-acyc-bc>)[
  设 $f: X -> S$ 是局部 Noether 概形之间的紧合态射，且关于 $cal(K) in D^+_#[tor] (X_et, Lambda)$ 局部零调。则对 $S$ 的每个几何点 $ol(s)$、每个 $ol(s)$ 的一般化（即 $tilde(S)_(ol(s))$ 的几何点 $ol(t)$），特殊化映射与余特殊化映射： 
  $
    sp: (R f_* cal(K))_(ol(s)) -> (R f_* cal(K))_(ol(t)) \

    cosp: R Gamma(X_(ol(t)), cal(K)|_(X_(ol(t)))) -> R Gamma(X_(ol(s)), cal(K)|_(X_(ol(s))))
  $
  都是同构。 
]
#proof[
  在 @loc-acyc-sp-cosp-square 的交换图表中，由于 $f$ 紧合，两个基变换映射按紧合基变换都是同构。因此，只需证明 $sp$ 与 $cosp$ 之一同构。 

  我们直接证明 $cosp$ 是同构。事实上，$cosp$ 如下构造： 
  $
    R Gamma(X_(ol(t)), cal(K)|_(X_(ol(t)))) &= R Gamma(X_(ol(t)), j'^(-1) tilde(K)) = R Gamma(X times_S tilde(S)_(ol(s)), R j'_* j'^(-1) tilde(cal(K))) \
    &-> R Gamma(X_(ol(s)), i'^(-1) R j'_* j'^(-1) tilde(cal(K))) \
    &->^(beta_(cal(K),ol(s),ol(t))^(-1)) R Gamma(X_(ol(s)), i'^(-1) tilde(cal(K))) = R Gamma(X_(ol(s)), cal(K)|_(X_(ol(s))))
  $
  第二个映射按定义就是同构。至于第一个映射： 
  $
    R Gamma(X times_S tilde(S)_(ol(s)), R j'_* j'^(-1) tilde(cal(K))) -> R Gamma(X_(ol(s)), i'^(-1) R j'_* j'^(-1) tilde(cal(K)))
  $
  它是紧合映射 $X times_S tilde(S)_(ol(s)) -> tilde(S)_(ol(s))$ 沿闭几何点 $ol(s) -> tilde(S)_(ol(s))$ 的基变换。这里 $tilde(S)_(ol(s))$ 是 Noether 的，且 $R j'_* j'^(-1) tilde(cal(K)) in D^+_#[tor]$，故紧合基变换适用。因此这个映射也是同构。这就证明了 $cosp$ 是同构。 
]

#properties(name: <loc-acyc-compose>)[
  局部零调性与复合相容，具体含义如下。设 $X ->^f Y ->^g S$ 是局部 Noether 概形之间的拟紧拟分离态射，$cal(K) in D^b_#[ctf] (X_et, Lambda)$，$ol(x)$ 是 $X$ 的几何点，$ol(y) = f(ol(x))$。 
  
  若 $f$ 在 $tilde(X)_(ol(x))$ 的每个点处都关于 $cal(K)$ 局部零调，且 $g$ 在 $ol(y)$ 处关于 $ul(cal(K)_(ol(x)))$ 局部零调，则 $g compose f$ 在 $ol(x)$ 处关于 $cal(K)$ 局部零调。 
]
#proof[
  令 $ol(s) = g(ol(y))$。由于局部零调性只依赖于严格局部邻域，我们可以把 $X, Y, S$ 换成 $tilde(X)_(ol(x)), tilde(Y)_(ol(y)), tilde(S)_(ol(s))$，并假设： 

  - $X, Y, S$ 是 Noether 严格 Hensel 局部环的谱，且 $ol(x), ol(y), ol(s)$ 位于各自的闭点上方。 

  - $f$ 关于 $cal(K)$ 局部零调，且 $g$ 在 $ol(y)$ 处关于 $ul(cal(K)_(ol(x))) = ul(R Gamma(X, cal(K)))$ 局部零调。 

  取 $S$ 的任意几何点 $ol(t)$。要证 $g compose f$ 在 $ol(x)$ 处关于 $cal(K)$ 局部零调，只需证明映射： 
  $
    cal(K)_(ol(x)) -> R Gamma(X_(ol(t)), cal(K)|_(X_(ol(t))))
  $
  是同构。把 $f$ 基变换为 $f_(ol(t)): X_(ol(t)) -> Y_(ol(t))$。由 Leray 谱序列， 
  $
    R Gamma(X_(ol(t)), cal(K)|_(X_(ol(t)))) cong R Gamma(Y_(ol(t)), R f_(ol(t),*) (cal(K)|_(X_(ol(t)))))
  $
  此外，存在映射 $ul(cal(K)_(ol(x))) = ul(R Gamma(X, cal(K))) -> cal(K)$，从而有映射 $ul(cal(K)_(ol(x))) -> cal(K)|_(X_(ol(t)))$。于是由伴随，有典范映射： 
  $
    ul(cal(K)_(ol(x))) -> R f_(ol(t),*) (cal(K)|_(X_(ol(t))))
  $
  假设这个映射是同构，则： 
  $
    R Gamma(X_(ol(t)), cal(K)|_(X_(ol(t)))) cong R Gamma(Y_(ol(t)), R f_(ol(t),*) (cal(K)|_(X_(ol(t))))) cong R Gamma(Y_(ol(t)), ul(cal(K)_(ol(x)))) cong cal(K)_(ol(x))
  $
  其中最后一个同构来自 $g$ 关于 $ul(cal(K)_(ol(x)))$ 的局部零调性。若该映射是同构，证明即告完成；于是归结为证明典范映射 $ul(cal(K)_(ol(x))) -> R f_(ol(t),*) (cal(K)|_(X_(ol(t))))$ 是同构。 
  #lemma[
    设 $cal(K) in D^+ (X_et, Lambda)$，$f: X -> S$ 是关于 $cal(K)$ 局部零调的态射。则对 $S$ 的每个几何点 $ol(t)$，作拉回图表： 
    // https://q.uiver.app/#r=typst&q=WzAsNCxbMCwwLCJYXyhvbCh0KSkiXSxbMSwwLCJYIl0sWzEsMSwiUyJdLFswLDEsIm9sKHQpIl0sWzAsMSwiaiciXSxbMywyLCJqIiwyXSxbMSwyLCJmIl0sWzAsMywiZl8ob2wodCkpIiwyXV0=
    #align(center, diagram({
      node((0, 0), [$X_(ol(t))$])
      node((1, 0), [$X$])
      node((1, 1), [$S$])
      node((0, 1), [$ol(t)$])
      edge((0, 0), (1, 0), [$j'$], label-side: left, "->")
      edge((0, 1), (1, 1), [$j$], label-side: right, "->")
      edge((1, 0), (1, 1), [$f$], label-side: left, "->")
      edge((0, 0), (0, 1), [$f_(ol(t))$], label-side: right, "->")
    }))
    则相对基变换映射： 
    $
      cal(K) Lotimes_Lambda f^(-1) j_* ul(Lambda) -> R j'_* j'^(-1) cal(K)
    $
    是同构。 
  ]
  #proof[
    设 $ol(t)$ 位于 $t in S$ 上方。取 $ol({t})$（带其约化结构）在其函数域的代数闭包中的正规化，记为 $S'$。则： 
    $
      S' -> ol({t}) -> S
    $
    是整映射与闭浸入的复合，从而是整映射。于是由 @loc-acyc-and-limits-of-qfinite，$f: X -> S$ 沿 $S' -> S$ 的基变换 $f': X' -> S'$ 关于 $cal(K)|_(X')$ 局部零调。 

    由于相对基变换与拉回方块的水平拼接相容，由 @finite-bc-in-the-limit，只需处理沿 $ol(t) -> S'$ 与 $X' -> S'$ 的基变换。换言之，不妨假设： 

    - $S$ 是正规整概形，其函数域代数闭，且 $ol(t)$ 位于其泛点上方。 

    设 $t$ 是 $S$ 的泛点，它是代数几何点。把 $j: ol(t) -> S$ 分解为 $ol(t) ->^q t -> S$，其中 $t$ 正是前述 $S$ 的泛点，它已是代数几何点。由 @integral-normal-affine-with-ac-func-field， 
    $
      f^(-1) j_* ul(Lambda) = f^(-1) h_* q_* ul(Lambda) = f^(-1) h_* ul(Lambda) = f^(-1) ul(Lambda) = ul(Lambda)
    $
    于是，只需证明 $cal(K) -> R j'_* j'^(-1) cal(K)$ 是同构。事实上，对位于 $x in X$ 上方的几何点 $ol(x)$， 
    $
      (R j'_* j'^(-1) cal(K))_(ol(x)) = R Gamma(X_(ol(t)) times_X tilde(X)_(ol(x)), cal(K)|_(X_(ol(t)) times_X tilde(X)_(ol(x)))) = R Gamma(ol(t) times_S tilde(X)_(ol(x)), cal(K)|_(ol(t) times_S tilde(X)_(ol(x))))
    $

    对 $s = f(x)$，$tilde(X)_(ol(x))$ 是 $Spec(cal(O)_(S,s))$ 上方的局部概形，且： 
    $
      ol(t) times_S tilde(X)_(ol(x)) = ol(t) otimes_(cal(O)_(S,s)) tilde(X)_(ol(x))
    $
    然而由 @integral-normal-affine-with-ac-func-field，$s$ 是 $S$ 的几何点，且 $cal(O)_(S,s)$ 是严格 Hensel 的。于是： 
    $
      ol(t) times_S tilde(X)_(ol(x)) = ol(t) otimes_(cal(O)_(S,s)) tilde(X)_(ol(x)) = ol(t) times_(tilde(S)_s) tilde(X)_(ol(x)) = F_(ol(x),ol(t))
    $
    是消没圈簇。因此，映射： 
    $
      cal(K)_(ol(x)) -> (R j'_* j'^(-1) cal(K))_(ol(x)) = R Gamma(F_(ol(x),ol(t)), cal(K)|_(F_(ol(x),ol(t))))
    $
    按局部零调性的定义，它是同构。故 $cal(K) -> R j'_* j'^(-1) cal(K)$ 是同构。 
  ]

  #lemma[
    设 $Lambda$ 是 Noether 环，且每个有限 $Lambda$-模都能嵌入某个有限自由 $Lambda$-模。设 $f: X -> S$ 是拟紧拟分离的态射，关于 $cal(K) in D^b_#[ctf] (X_et, Lambda)$ 局部零调，且 $S$ 是局部 Noether 概形。又设 $ol(s)$ 是 $S$ 的几何点，使得对 $tilde(S)_(ol(s))$ 的几何点 $ol(t)$，所有余特殊化： 
    $
      R Gamma(X_(ol(t)), cal(K)|_(X_(ol(t)))) -> R Gamma(X_(ol(s)), cal(K)|_(X_(ol(s))))
    $
    都是同构。则基变换： 
    $
      (R f_* cal(K))_(ol(s)) -> R Gamma(X_(ol(s)), cal(K)|_(X_(ol(s))))
    $
    是同构。 
  ]
  #proof[
    与 @loc-acyc-sp-cosp-square 证明的开头一样，我们可以把 $f: X -> S$ 换成 $X times_S tilde(S)_(ol(s)) -> tilde(S)_(ol(s))$，把 $cal(K)$ 换成 $cal(K)|_(X times_S tilde(S)_(ol(s)))$。于是不妨假设 $S$ 是 Noether 严格 Hensel 局部环的谱，且 $ol(s)$ 位于其闭点上方。 

    为证明所要的结论，我们对 $S$ 上所有 $Lambda$-模层 $cal(F)$ 证明基变换： 
    $
      (R f_* (cal(K) Lotimes_Lambda f^(-1) cal(F)))_(ol(s)) = R Gamma(X, cal(K) Lotimes_Lambda f^(-1) cal(F)) -> R Gamma (X_(ol(s)), (cal(K) Lotimes_Lambda f^(-1) cal(F))|_(X_(ol(s))))
    $
    是同构。最后取 $cal(F) = ul(Lambda)$ 即可完成证明。 

    首先假设 $cal(F) = j_* ul(Lambda)$，其中 $j: ol(t) -> S$ 是几何点。作拉回图表： 
    #align(center, diagram({
      node((0, 0), [$X_(ol(t))$])
      node((1, 0), [$X$])
      node((2, 0), [$X_(ol(s))$])
      node((2, 1), [$ol(s)$])
      node((1, 1), [$S$])
      node((0, 1), [$ol(t)$])
      edge((0, 1), (1, 1), [$j$], label-side: right, "->")
      edge((2, 1), (1, 1), [$i$], label-side: left, "->")
      edge((2, 0), (2, 1), [$f_(ol(s))$], label-side: left, "->")
      edge((1, 0), (1, 1), [$f$], label-side: left, "->")
      edge((0, 0), (0, 1), [$f_(ol(t))$], label-side: right, "->")
      edge((2, 0), (1, 0), [$i'$], label-side: right, "->")
      edge((0, 0), (1, 0), [$j'$], label-side: left, "->")
    }))
    由上一个引理，左端为： 
    $
      R Gamma(X, cal(K) Lotimes_Lambda f^(-1) j_* ul(Lambda)) = R Gamma(X, R j'_* j'^(-1) cal(K)) = R Gamma(X_(ol(t)), j'^(-1) cal(K))
    $ 
    而右端为： 
    $
      i'^(-1) (cal(K) Lotimes_Lambda f^(-1) j_* ul(Lambda)) = i'^(-1) cal(K) Lotimes_Lambda f_(ol(s))^(-1) i^(-1) j_* ul(Lambda)
    $
    现在 $i^(-1) j_* ul(Lambda) = ul((j_* ul(Lambda))_(ol(s))) = ul(R Gamma(S, j_* ul(Lambda))) = ul(Lambda)$，故 $f_(ol(s))^(-1) i^(-1) j_* ul(Lambda) = ul(Lambda)$。于是右端为： 
    $
      R Gamma (X_(ol(s)), (cal(K) Lotimes_Lambda f^(-1) cal(F))|_(X_(ol(s)))) = R Gamma(X_(ol(s)), i'^(-1) cal(K))
    $
    展开定义可以验证：在左端与右端的这些等同之下，基变换映射恰好变成余特殊化： 
    $
      cosp: R Gamma(X_(ol(t)), j'^(-1) cal(K)) -> R Gamma(X_(ol(s)), i'^(-1) cal(K))
    $
    而它由假设是同构。换言之，我们已经证明：只要 $cal(F) = j_* ul(Lambda)$ 且 $j: ol(t) -> S$ 是几何点，基变换： 
    $
      (R f_* (cal(K) Lotimes_Lambda f^(-1) cal(F)))_(ol(s)) -> R Gamma (X_(ol(s)), (cal(K) Lotimes_Lambda f^(-1) cal(F))|_(X_(ol(s))))
    $
    就是同构。 

    把 $cal(K)$ 换成有界平坦消解 $cal(P)^bullet$，便得到超上同调谱序列： 
    $
      E_1^(p,q) (cal(F)) := R^q f_* (cal(P)^p otimes_Lambda f^(-1) cal(F)) => h^(p+q) ((R f_* (cal(K) Lotimes_Lambda f^(-1) cal(F)))_(ol(s))) =: L^q (cal(F)) \

      tilde(E)_1^(p,q) (cal(F)) := H^q (X_(ol(s)), (cal(P)^p Lotimes_Lambda f^(-1) cal(F))|_(X_(ol(s)))) => h^(p+q) (R Gamma (X_(ol(s)), (cal(K) Lotimes_Lambda f^(-1) cal(F))|_(X_(ol(s))))) =: S^q (cal(F))
    $
    由于 $f$ 是拟紧拟分离的，由极限公式 @limit-formula-for-sheaves 与 @relative-limit-formula-for-sheaves，$E_1^(p,q)$ 与 $tilde(E)_1^(p,q)$ 都与正向极限交换。因此 $L^q (cal(F))$ 与 $S^q (cal(F))$ 作为 $cal(F)$ 的函子都与正向极限交换。 

    固定 $q$，假设对所有 $r < q$ 及所有 $cal(F) in cAb(S_et, Lambda)$，$L^r (cal(F)) -> S^r (cal(F))$ 都是同构。注意： 

    - $S$ 是 Noether 的，因此每个层 $cal(F) in cAb(S_et, Lambda)$ 都可以写成 $cal(F) = dirlim_lambda cal(F)_lambda$，也就是可构造 $Lambda$-模层的正向极限。而 $L^q (cal(F)) -> S^q (cal(F))$ 是 $L^q (cal(F)_lambda) -> S^q (cal(F)_lambda)$ 的正向极限，故以下条件等价： 

      - 对一切 $cal(F) in cAb(S_et, Lambda)$，$L^q (cal(F)) -> S^q (cal(F))$ 是单射； 

      - 对一切可构造的 $cal(F) in cAb(S_et, Lambda)$，$L^q (cal(F)) -> S^q (cal(F))$ 是单射。 
  
    - 对每个可构造层 $cal(F)$，由 @constructible-godement-resolution 可以得到单射 $cal(F) -> oplus.big_(i=1)^m ol(t_i)_* ul(M_i)$，其中 $M_i$ 是有限 $Lambda$-模，$ol(t_i) -> S$ 是几何点。由于每个有限 $Lambda$-模都能嵌入某个有限自由 $Lambda$-模，不妨设每个 $M_i$ 都是有限自由；再把它们拆分，不妨设每个 $M_i = Lambda$。作短正合列：#h(1fr)
      $
        0 -> cal(F) -> cal(C) = oplus.big_(i=1)^m ol(t_i)_* ul(Lambda) -> cal(R) -> 0
      $
      现在考虑如下各行正合的交换图表： 
      // https://q.uiver.app/#r=typst&q=WzAsMTQsWzAsMCwiZG90cy5jIl0sWzEsMCwiTF4ocS0xKSAoY2FsKEMpKSJdLFsyLDAsIkxeKHEtMSkgKGNhbChSKSkiXSxbMywwLCJMXnEgKGNhbChGKSkiXSxbNCwwLCJMXnEgKGNhbChDKSkiXSxbNSwwLCJMXnEgKGNhbChSKSkiXSxbNiwwLCJkb3RzLmMiXSxbMCwxLCJkb3RzLmMiXSxbNiwxLCJkb3RzLmMiXSxbMSwxLCJTXihxLTEpIChjYWwoQykpIl0sWzIsMSwiU14ocS0xKSAoY2FsKFIpKSJdLFszLDEsIlNecSAoY2FsKEYpKSJdLFs0LDEsIlNecSAoY2FsKEMpKSJdLFs1LDEsIlNecSAoY2FsKFIpKSJdLFswLDFdLFsxLDJdLFsyLDNdLFszLDRdLFs0LDVdLFs1LDZdLFs3LDldLFs5LDEwXSxbMTAsMTFdLFsxMSwxMl0sWzEyLDEzXSxbMTMsOF0sWzEsOV0sWzIsMTBdLFszLDExXSxbNCwxMl0sWzUsMTNdXQ==
      #align(center, diagram({
        node((0, 0), [$dots.c$])
        node((1, 0), [$L^(q-1) (cal(C))$])
        node((2, 0), [$L^(q-1) (cal(R))$])
        node((3, 0), [$L^q (cal(F))$])
        node((4, 0), [$L^q (cal(C))$])
        node((5, 0), [$L^q (cal(R))$])
        node((6, 0), [$dots.c$])
        node((0, 1), [$dots.c$])
        node((6, 1), [$dots.c$])
        node((1, 1), [$S^(q-1) (cal(C))$])
        node((2, 1), [$S^(q-1) (cal(R))$])
        node((3, 1), [$S^q (cal(F))$])
        node((4, 1), [$S^q (cal(C))$])
        node((5, 1), [$S^q (cal(R))$])
        edge((0, 0), (1, 0), "->")
        edge((1, 0), (2, 0), "->")
        edge((2, 0), (3, 0), "->")
        edge((3, 0), (4, 0), "->")
        edge((4, 0), (5, 0), "->")
        edge((5, 0), (6, 0), "->")
        edge((0, 1), (1, 1), "->")
        edge((1, 1), (2, 1), "->")
        edge((2, 1), (3, 1), "->")
        edge((3, 1), (4, 1), "->")
        edge((4, 1), (5, 1), "->")
        edge((5, 1), (6, 1), "->")
        edge((1, 0), (1, 1), "->")
        edge((2, 0), (2, 1), "->")
        edge((3, 0), (3, 1), "->")
        edge((4, 0), (4, 1), "->")
        edge((5, 0), (5, 1), "->")
      }))
      
      - 由归纳假设，前两个竖直映射是同构。由上面关于形如 $ul(t)_* ul(Lambda)$ 的层的讨论，第四个竖直映射是同构。 

        于是由单射四引理，第三个竖直箭头是单射。因此对一切可构造层 $cal(F)$，$L^q (cal(F)) -> S^q (cal(F))$ 是单射；再由前面关于正向极限的等价条件，对一切层都成立。 

        特别地，第五个竖直箭头 $L^q (cal(R)) -> S^q (cal(R))$ 是单射，故由满射四引理，第三个竖直箭头是满射。因此对一切可构造层 $cal(F)$，$L^q (cal(F)) -> S^q (cal(F))$ 是双射；再由前面关于正向极限的等价条件，对一切层 $cal(F)$ 都成立。

    取 $cal(F) = ul(Lambda)$ 即完成证明。  
  ]

  #lemma(name: <loc-acyc-constancy-of-pushforward>)[
    设 $Lambda$ 是 Noether 环，且每个有限 $Lambda$-模都能嵌入某个有限自由 $Lambda$-模。设 $cal(K) in D^b_#[ctf] (X_et, Lambda)$，$f: X -> S$ 是局部 Noether 概形之间的拟紧拟分离态射，关于该复形局部零调。 

    设给定复形 $A in D^b (Lambda)$ 与态射 $alpha: ul(A)_X -> cal(K)$，使得对 $S$ 的每个几何点 $ol(s)$，由 $alpha$ 诱导的映射： 
    $
      A -> R Gamma(X_(ol(s)), ul(A)) -> R Gamma(X_(ol(s)), cal(K)|_(X_(ol(s))))
    $
    都是同构。则由伴随从 $alpha$ 诱导的映射： 
    $
      beta: ul(A)_S -> R f_* cal(K)
    $
    是同构。 
  ]
  #proof[
    展开定义可以验证，这些同构 $A -> R Gamma(X_(ol(s)), cal(K)|_(X_(ol(s))))$ 与不同几何纤维之间的余特殊化相容。因此 $f$ 关于 $cal(K)$ 的所有余特殊化都是同构。 

    对 $S$ 的每个几何点 $ol(s)$，考虑映射 $tilde(f)_(ol(s)): X times_S tilde(S)_(ol(s)) -> tilde(S)_(ol(s))$。$tilde(S)_(ol(s))$ 是 $S$ 中 $ol(s)$ 的仿射平展邻域的逆向极限，从而是带仿射过渡映射的拟有限 $S$-概形的逆向极限。于是由 @loc-acyc-and-limits-of-qfinite，$tilde(f)_(ol(s))$ 关于 $cal(K)|_(X times_S tilde(S)_(ol(s)))$ 局部零调。 

    此外，按定义，$tilde(f)_(ol(s))$ 关于 $cal(K)|_(X times_S tilde(S)_(ol(s)))$ 的余特殊化与 $f$ 关于 $cal(K)$ 的余特殊化完全相同。因此 $tilde(f)_(ol(s))$ 关于 $cal(K)|_(X times_S tilde(S)_(ol(s)))$ 的所有余特殊化都是同构。 

    现在可以应用上一个引理，得到基变换同构： 
    $
      R Gamma(X times_S tilde(S)_(ol(s)), cal(K)|_(X times_S tilde(S)_(ol(s)))) cong R tilde(f)_(ol(s),*) (cal(K)|_(X times_S tilde(S)_(ol(s))))_(ol(s)) cong R Gamma(X_(ol(s)), cal(K)|_(X_(ol(s))))
    $
    然而由 @derived-stalks-of-derived-pushforward，$R Gamma(X times_S tilde(S)_(ol(s)), cal(K)|_(X times_S tilde(S)_(ol(s)))) cong (R f_* cal(K))_(ol(s))$。于是我们证明了： 
    $
      (R f_* cal(K))_(ol(s)) cong R Gamma(X_(ol(s)), cal(K)|_(X_(ol(s)))) cong A
    $
    可以验证，这个同构恰好就是态射 $beta_(ol(x)): A -> (R f_* cal(K))_(ol(s))$。故 $beta$ 是同构。 
  ]

  回忆我们要证明：由 $ul(cal(K)_(ol(x))) -> cal(K)|_(X_(ol(t)))$ 诱导的映射 $ul(cal(K)_(ol(x))) -> R f_(ol(t),*) (cal(K)|_(X_(ol(t))))$ 是同构。$ol(t) -> S$ 拟有限，故由 @loc-acyc-and-limits-of-qfinite，$f_(ol(t))$ 关于 $cal(K)|_(X_(ol(t)))$ 局部零调。现在对 $Y_(ol(t))$ 的几何点 $ol(u)$， 
  $
    R Gamma(X_(ol(t)) times_(Y_(ol(t))) ol(u), cal(K)|_(X_(ol(t)) times_(Y_(ol(t))) ol(u))) cong R Gamma(X_(ol(u)), cal(K)|_(X_(ol(u))))
  $
  然而 $X_(ol(u)) = ol(u) times_Y X = ol(u) times_(tilde(Y)_(ol(y))) tilde(X)_(ol(x)) = F_(ol(x),ol(u))$ 是 $f: X -> Y$ 的消没圈簇，故由局部零调性的定义，$R Gamma(X_(ol(u)), cal(K)|_(X_(ol(u)))) = R Gamma(F_(ol(x),ol(u)), cal(K)|_(F_(ol(x),ol(u)))) = cal(K)_(ol(x))$。于是有自然同构 $cal(K)_(ol(x)) cong R Gamma(X_(ol(t)) times_(Y_(ol(t))) ol(u), cal(K)|_(X_(ol(t)) times_(Y_(ol(t))) ol(u)))$。现在可以引用上一个引理，说明我们得到了所要的同构： 
  $
    ul(cal(K)_(ol(x))) cong R f_(ol(t),*) (cal(K)|_(X_(ol(t))))
  $
]

#lemma(name: <loc-acyc-pass-to-lcc-sheaves>)[
  设 $f: X -> S$ 是局部零调的概形态射，$Lambda$ 是挠 Noether 环，其挠系数 $n in cal(O)_S^times$。 
  
  则对任意局部常值 $Lambda$-模层 $cal(F) in cAb(X_et, Lambda)$，$f$ 都关于 $cal(F)$ 局部零调。 
]
#proof[
  由于局部零调性只依赖于严格局部环，对 $X$ 的几何点 $ol(x)$（令 $ol(s) = f(ol(x))$），要证 $f$ 在 $ol(x)$ 处关于 $cal(F)$ 局部零调，只需证明 $tilde(X)_(ol(x)) -> tilde(S)_(ol(s))$ 关于 $cal(F)|_(tilde(X)_(ol(x)))$ 局部零调。而 $tilde(X)_(ol(x)) -> tilde(S)_(ol(s))$ 是局部零调的，故可用它替换 $f$，并假设 $X, S$ 是严格 Hensel 局部环的谱。 

  现在 $cal(F)$ 是 $X$ 上的 l.c.c. $Lambda$-模层。于是按定义存在平展覆盖 $U -> X$，使 $cal(F)|_U$ 为常值层。由于 $X$ 是严格 Hensel 局部环的谱，对 $U -> X$ 特殊纤维上的任一点，都至少有一个截面 $s: X -> U$ 经过它（@equiv-defns-of-henselian (4)），故 $s^(-1) (cal(F)|_U) = cal(F)$ 是常值层。于是 $cal(F) = ul(M)$，其中 $M$ 是 $Lambda$-模。又因 $Lambda$ 是 $n$-挠的，$M$ 是 $n$-挠交换群，故作为交换群有： 
  $
    M = oplus.big_i ZZ\/d_i
  $
  其中 $d_i|n$。由极限公式 @limit-formula-for-sheaves， 
  $
    H^q (F_(ol(x),ol(t)), ul(M)) = H^q (F_(ol(x),ol(t)), oplus.big_i ZZ\/d_i) = oplus.big_i H^q (F_(ol(x),ol(t)), ZZ\/d_i) = cases(
      0 &\, q >= 1, 
      oplus.big_i ZZ\/d_i = M &\, q = 0
    )
  $
  这里用到了 $f$ 关于每个 $ZZ\/d_i$ 的局部零调性（其中 $d_i | n$ 属于 $cal(O)_S^times$）。这就证明了 $f$ 关于 $cal(F) = ul(M)$ 的局部零调性。 
]
