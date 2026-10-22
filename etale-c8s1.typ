#import "void-import.typ": *

本节所做的这一系列归约，可以分别在 #cite-stacks("0EZQ")[Section 59.86] 与 @cite-lei-fu[Section 7.6] 中看到。

粗略地说，局部零调性这套理论由以下几项陈述组成：

+ (光滑基变换) 在如下拉回图表中：#h(1fr)
  // https://q.uiver.app/#r=typst&q=WzAsNCxbMCwxLCJYIl0sWzEsMSwiUyJdLFswLDAsIlgnIl0sWzEsMCwiUyciXSxbMywxLCJnIl0sWzIsMCwiZyciLDJdLFsyLDMsImYnIl0sWzAsMSwiZiIsMl1d
  #align(center, diagram({
    node((-1, 1), [$X$])
    node((0, 1), [$S$])
    node((-1, 0), [$X'$])
    node((0, 0), [$S'$])
    node((-0.7, 0.3), $cart$)
    edge((0, 0), (0, 1), [$g$], label-side: left, "->")
    edge((-1, 0), (-1, 1), [$g'$], label-side: right, "->")
    edge((-1, 0), (0, 0), [$f'$], label-side: left, "->")
    edge((-1, 1), (0, 1), [$f$], label-side: right, "->")
  }))
  其中 $f$ 是拟紧拟分离、$g$ 光滑。若 $n in cal(O)_S (S)^times$，则对 $X$ 上任意 $n$-挠交换群层 $cal(F)in cAb(X_et, ZZ\/n)$，基变换态射：
  $
    g^(-1) R^q f_* cal(F) -> R^q f'_* g'^(-1) cal(F)
  $
  是同构。

+ (光滑态射的局部零调性) 设 $f: X -> S$ 是光滑态射，$f(x) = s$；取 $x$ 上方的一个代数几何点 $ol(x)$，以及 $S$ 的一对代数几何点 $ol(s), ol(t)$，其中 $t succ s$，则
  $
    H^q (tilde(X)_(ol(x)) times_(tilde(S)_(ol(s))) ol(t), ul(ZZ\/n)) = cases(
      ZZ\/n &\, q = 0, 
      0 &\, q>=1
    )
  $
  对任意自然数 $n in cal(O)_S (S)^times$ 成立。

+ (紧合光滑基变换) 设 $f: X -> S$ 是 Noether 概形之间的紧合光滑态射。则对任意 $n$-挠 l.c.c. 层 $cal(F) in cAb(X_et, ZZ\/n)$（其中 $n in cal(O)_S (S)^times$），$R^q f_* cal(F)$ 也是 l.c.c. 层。

+ ($R f_!$ 的有限性) 设 $f: X -> S$ 是 Noether 概形之间分离、有限型的态射。则对任意可构造层 $cal(F) in cAb(X_et, ZZ\/n)$，$R^q f_! cal(F)$ 可构造。换言之，$R f_!$ 是函子 $D^b_c (X_et, Lambda) -> D^b_c (S_et, Lambda)$。

从逻辑上看，(1) 光滑基变换与 (2) 光滑态射的局部零调性等价，而 (3) 紧合光滑基变换与 (4) $R f_!$ 的有限性依赖于 (1)(2)。发展这套理论的动机来自 (3)，以及层论结果 @descs-of-lcc-sheaves (a) $<==>$(b)：

- 茎有限的层 $cal(F) in cAb(X_et)$ 是 l.c.c. 层，当且仅当对 $X$ 中每一对 $t succ s$，特殊化映射 $cal(F)_(ol(t)) -> cal(F)_(ol(s))$ 都是同构。

于是可以提出这样的问题：对紧合态射 $f: X -> S$，$R^q f_* ul(ZZ\/n)$ 何时是 l.c.c. 层？茎的有限性可以借助化归到曲线来建立，于是剩下的要求只有一条：特殊化映射都是同构。由紧合基变换，这归结为如下同构：
$
  H^q (X_(ol(t)), ul(ZZ\/n)) ->^tilde H^q (X_(ol(s)), ul(ZZ\/n))
$
我们将看到，把两条几何纤维都嵌入 $X times_S tilde(S)_(ol(s))$，就能表达出这个态射；再经由消没圈构造，它便转译为陈述 (2)。随后通过 devissage 论证，(3) 将推出 (4)。

最后还有一点关于系数环的附注。

#remark[
  平展上同调理论的主要应用是证明 Weil 猜想，而这需要建立 $ell$-进层理论。也就是说，对特征为 $p$ 的概形 $X$，只要 $ell != p$，就有一套以 $ol(QQ_ell)$ 为系数的上同调理论。这套理论对每个有限扩张 $E\/QQ_ell$ 分别建立，做法是借助整数环 $cal(O)_E$；而 $cal(O)_E$ 上的理论本身，又是由系数为 $cal(O)_E\/frak(m)_E^N$ 的平展层出发、取极限构造出来的。

  因此，最重要的系数环——也是一类足以应付应用的系数环——就是 $Lambda = cal(O)_E\/frak(m)_E^N$，其中 $E\/QQ_ell$ 是有限扩张且 $ell in cal(O)_X^times$。（这包括环 $ZZ\/ell^N$。）这些 $Lambda$ 连同 $Lambda = ZZ\/n, n in cal(O)_X^times$ 具有下列优良性质：

  - $Lambda$ 是挠环，其挠系数属于 $cal(O)_X^times$；

  - $Lambda$ 是有限环，因此 $Lambda$-模的可构造层，恰好就是那些作为交换群层可构造的 $Lambda$-模层；

  - 每个有限 $Lambda$-模都能嵌入某个有限自由 $Lambda$-模；

  - $Lambda$ 是内射 $Lambda$-模。

  因此，每当在某个命题的假设里看到这类看似随意的条件，你都可以放心：这些条件在实践中都是满足的。
]

本章自始至终假定 $Lambda$ 是挠环。

== 基变换的一般归约

#notation(name: <constructible-finite-tor-derived-category>)[
  我们用记号 $D^b_#[ctf] (X_et, Lambda)$ 表示 $X$ 上 $Lambda$-模平展层的有界复形构成的三角范畴，这些复形的上同调层可构造，且具有有限 Tor 维数 (finite Tor-dimension)，即该函子 $cal(K) Lotimes_Lambda -$ 的幅度上有界且下有界。等价地，这样的复形属于 $D^b_c$，且有有界平坦消解。

  #lemma(name: <resolution-of-ctf-complexes>)[
    (#cite-stacks("03TT")[Lemma 59.77.3]) 设 $X$ 是 Noether 概形，$cal(K) in D^b_#[ctf] (X_et, Lambda)$，且对一切层 $cal(G) in cAb(X_et, Lambda)$ 都有 $cal(K) Lotimes_Lambda cal(G) in D_([a,b]) (X_et, Lambda)$。则 $cal(K)$ 可由如下复形代表：
    $
      0 -> cal(F)^a -> cal(F)^(a+1) -> dots.c -> cal(F)^b -> 0
    $ 
    其中每个 $cal(F)^q = j_(q,!) ul(Lambda)$ 都可构造且平坦。
  ]
  #proof[
    我们对 $b-a$ 归纳。若 $a=b$，则 $cal(K) = h^a (cal(K))[-a]$。此时由假设可知 $h^a (cal(K))$ 可构造且平坦，故结论成立。
    
    现在设 $b>a$，并把 $cal(K)$ 用由平坦层组成的 K-平坦复形 $dots.c -> cal(K)^a -> cal(K)^(a+1) -> dots.c -> cal(K)^b -> dots.c$ 代表。由可构造性，存在平展态射 $j: U -> X$（$U$ 仿射）以及满射：
    $
      j_! ul(Lambda) -> h^b (cal(K))
    $
    这相当于给出 $h^b (cal(K))|_U$ 上的一个整体截面。由于 $ker(cal(K)^b -> cal(K)^(b+1)) -> h^b (cal(K))$ 是满射，存在进一步的仿射平展覆盖 $U' -> U$，使该截面提升为 $ker(cal(K)^b -> cal(K)^(b+1))|_(U')$ 的整体截面。令 $j': U' -> X$，便得到映射 $cal(F) := j'_! ul(Lambda) -> ker(cal(K)^b -> cal(K)^(b+1))$；把它进一步映射到 $h^b (cal(K))$ 后仍是满射。现在构造特殊三角：
    $
      cal(F)[-b] -> cal(K) -> cal(L) ->^(+1)
    $
    复形 $cal(L) in D^b_#[ctf] (X_et, Lambda)$，且其 Tor 幅度落在 $[a,b-1]$ 中。事实上，映射 $cal(F) -> h^b (cal(K))$ 是满射。于是与任意层 $cal(G)$ 张量，得到长正合列：
    $
      dots.c -> h^q (cal(G) Lotimes_Lambda cal(K)) -> h^q (cal(G) Lotimes_Lambda cal(L)) -> h^(q-b+1) (cal(G) Lotimes_Lambda cal(F)) -> dots.c
    $
    现在来看各项：

    - 项 $h^q (cal(G) Lotimes_Lambda cal(K))$ 仅在 $q in [a,b]$ 时可能非零，项 $h^(q-b+1) (cal(G) Lotimes_Lambda cal(F))$ 仅在 $q = b-1$ 时可能非零（因 $cal(F)$ 可构造且平坦）。于是当 $q<a$ 或 $q>b$ 时，$h^q (cal(G) Lotimes_Lambda cal(L)) = 0$。

    - 对 $h^b$，有：#h(1fr)
      $
        dots.c -> cal(G) otimes_Lambda cal(F) -> h^b (cal(G) Lotimes_Lambda cal(K)) -> h^b (cal(G) Lotimes_Lambda cal(L)) -> 0
      $
      第一个映射分解为：
      $
        cal(G) otimes_Lambda cal(F) -> cal(G) otimes_Lambda h^b (cal(K)) ->^tilde h^b (cal(G) Lotimes_Lambda cal(K)).
      $
      第一个箭头是满射，因为张量积右正合。第二个箭头是超上同调谱序列的边缘同构，该谱序列为：
      $
        E_2^(p,q) = "Tor"_p^Lambda (cal(G), h^q (cal(K))) => h^(q-p)(cal(G) Lotimes_Lambda cal(K)),
      $
      其中当 $q>b$ 时 $h^q (cal(K))=0$。因此 $h^b (cal(G) Lotimes_Lambda cal(L)) = 0$。

    于是 $cal(L)$ 的 Tor 幅度落在 $[a,b-1]$ 中。由归纳假设，把 $cal(L)$ 用如下复形代表：
    $
      cal(F)^a -> dots.c -> cal(F)^(b-1)
    $
    其中每个 $cal(F)^q$ 都可构造且平坦。$+1$ 态射 $cal(L) -> cal(F)[-b+1]$ 由映射 $cal(F)^(b-1) -> cal(F)$ 代表，该映射湮灭 $cal(F)^(b-2)$ 的像。它的锥平移 $-1$ 后代表 $cal(K)$，恰好就是
    $
      0 -> cal(F)^a -> dots.c -> cal(F)^(b-1) -> cal(F) -> 0
    $
    归纳完成。
  ]
]

#construction(name: <relative-base-change-constr>)[
  （相对基变换 (relative base change)）对拉回图表，
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
  以及 $cal(L) in D(Y'_et, Lambda)$，我们定义关于 $cal(K)$ 的相对基变换映射：
  $
    g^(-1) R f_* cal(K) Lotimes_Lambda cal(L) --> R f'_* g'^(-1) cal(K) Lotimes_Lambda cal(L) --> R f'_* (g'^(-1) cal(K) Lotimes_Lambda f'^(-1) cal(L))
  $
  其中第一个映射是通常的基变换映射，第二个映射是 $R f'_*$ 的投影映射。

  由紧合基变换与投影公式，只要 $f$ 紧合，这样的相对基变换映射就是同构。

  由基变换映射与投影映射的自然性，相对基变换映射具有以下自然性陈述：

  - 对拉回图表的竖直拼接，#h(1fr)
    // http://localhost:8000/#r=typst&q=WzAsNixbMCwxLCJYJyJdLFsxLDEsIlknIl0sWzAsMiwiWCJdLFsxLDIsIlkiXSxbMSwwLCJZJyciXSxbMCwwLCJYJyciXSxbMiwzLCJmIiwyXSxbMCwxLCJmJyJdLFsxLDMsImciXSxbMCwyLCJnJyIsMl0sWzUsNCwiZicnIl0sWzQsMSwiaCJdLFs1LDAsImgnIiwyXV0=
    #align(center, diagram({
      node((0, 0), [$X'$])
      node((1, 0), [$Y'$])
      node((0, 1), [$X$])
      node((1, 1), [$Y$])
      node((1, -1), [$Y''$])
      node((0, -1), [$X''$])
      edge((0, 1), (1, 1), [$f$], label-side: right, "->")
      edge((0, 0), (1, 0), [$f'$], label-side: left, "->")
      edge((1, 0), (1, 1), [$g$], label-side: left, "->")
      edge((0, 0), (0, 1), [$g'$], label-side: right, "->")
      edge((0, -1), (1, -1), [$f''$], label-side: left, "->")
      edge((1, -1), (1, 0), [$h$], label-side: left, "->")
      edge((0, -1), (0, 0), [$h'$], label-side: right, "->")
    }))
    相对于 $h^(-1) cal(L)$ 的相对基变换 $h^(-1) g^(-1) R f_* cal(K) Lotimes_Lambda h^(-1) cal(L) -> R f''_* (h'^(-1) g'^(-1) cal(K) Lotimes_Lambda h^(-1) f''^(-1) cal(L))$，是如下复合：
    $
      h^(-1) g^(-1) R f_* cal(K) Lotimes_Lambda h^(-1) cal(L) &cong h^(-1) (g^(-1) R f_* cal(K) Lotimes_Lambda cal(L)) \
      &-> h^(-1) R f'_* (g'^(-1) cal(K) Lotimes_Lambda f'^(-1) cal(L)) \
      &-> R f''_* h'^(-1) (g'^(-1) cal(K) Lotimes_Lambda f'^(-1) cal(L)) \
      &cong R f''_* (h'^(-1) g'^(-1) cal(K) Lotimes_Lambda h^(-1) f''^(-1) cal(L))
    $
    ——即下方方块关于 $cal(L)$ 的相对基变换与上方方块的基变换。

  - 对拉回方块的横向拼接，
    // http://localhost:8000/#r=typst&q=WzAsNixbMSwwLCJYJyJdLFsyLDAsIlknIl0sWzEsMSwiWCJdLFsyLDEsIlkiXSxbMCwxLCJaIl0sWzAsMCwiWiciXSxbMiwzLCJmIiwyXSxbMCwxLCJmJyJdLFsxLDMsImciXSxbMCwyLCJnJyIsMl0sWzQsMiwiaCIsMl0sWzUsMCwiaCciXSxbNSw0LCJnJyciLDJdXQ==
    #align(center, diagram({
      node((0, 0), [$X'$])
      node((1, 0), [$Y'$])
      node((0, 1), [$X$])
      node((1, 1), [$Y$])
      node((-1, 1), [$Z$])
      node((-1, 0), [$Z'$])
      edge((0, 1), (1, 1), [$f$], label-side: right, "->")
      edge((0, 0), (1, 0), [$f'$], label-side: left, "->")
      edge((1, 0), (1, 1), [$g$], label-side: left, "->")
      edge((0, 0), (0, 1), [$g'$], label-side: right, "->")
      edge((-1, 1), (0, 1), [$h$], label-side: right, "->")
      edge((-1, 0), (0, 0), [$h'$], label-side: left, "->")
      edge((-1, 0), (-1, 1), [$g''$], label-side: right, "->")
    }))
    相对基变换 $g^(-1) R f_* R h_* cal(K) Lotimes_Lambda cal(L) -> R f'_* R h'_* (g''^(-1) cal(K) Lotimes_Lambda h'^(-1) f'^(-1) cal(L))$ 是如下复合：
    $
      g^(-1) R f_* R h_* cal(K) Lotimes_Lambda cal(L) -> R f'_* (g'^(-1) R h_* cal(K) Lotimes_Lambda f'^(-1) cal(L)) -> R h'_* R f'_* (g''^(-1) cal(K) Lotimes_Lambda h'^(-1) f'^(-1) cal(L))
    $
    ——即右方方块关于 $cal(L)$ 的相对基变换与左方方块关于 $f'^(-1) cal(L)$ 的相对基变换。
]

紧合基变换给出了使相对基变换映射成为同构的关于 $f$ 的条件，即 $f$ 紧合。因此，从 $g$ 这一侧研究该问题就很自然：我们想找出关于 $g$ 的条件，使上面建立的相对基变换映射成为同构。

为建立主要结果，我们需要一些预备陈述。

#lemma(name: <constructible-godement-resolution>)[
  设 $X$ 是 Noether 概形，$cal(F) in cAb(X_et, ZZ\/n)$ 是 $n$-挠可构造层。则存在有限多个几何点 $ol(x_1), dots.c, ol(x_m) in X$ 以及单射：
  $
    cal(F) -> oplus.big_(i=1)^m ol(x_i)_* ul(ZZ\/n)
  $
]
#proof[
  由 @finite-morphisms-and-constructible-sheaves，存在有限态射 $h: X' -> X$ 以及单射 $cal(F) -> h_* ul(ZZ\/n)$。注意 $h$ 有限，故 $h_*$ 正合；又由 Leray 谱序列 @derived-lower-star-first-props (1)，有 $h_* ol(x')_* ul(ZZ\/n) = (h(ol(x')))_* ul(ZZ\/n)$。于是把 $X$ 换成 $X'$，便可假定 $cal(F) = ul(ZZ\/n)$。

  设 $x_1, dots.c, x_m in X$ 是 $X$ 的所有不可约分支的泛点，$ol(x_i)$ 是 $x_i$ 上方的一个几何点。我们断言如下典范映射
  $
    ul(ZZ\/n)_X -> oplus.big_(i=1)^m ol(x_i)_* ul(ZZ\/n)
  $
  是单射。事实上，对任意连通的仿射 $U in Et_X$，该映射在 $U$ 上诱导出如下截面映射：
  $
    ZZ\/n -> oplus.big_(i=1)^m (ZZ\/n)^(oplus pi_0 (U_(ol(x_i))))
  $
  这个对角映射是单射：$U$ 在 $X$ 中的像必定包含 $X$ 某个不可约分支的泛点，从而 $U_(ol(x_i))$ 非空，右端的直和也就不为零。证毕。
]

#proposition(name: <finite-bc-in-the-limit>)[
  对任意整态射 $f: X -> Y$，$f_*$ 都正合；并且，在拉回图表
  #align(center, diagram({
    node((-1, 1), [$X$])
    node((0, 1), [$Y$])
    node((-1, 0), [$X'$])
    node((0, 0), [$Y'$])
    node((-0.7, 0.3), $cart$)
    edge((0, 0), (0, 1), [$g$], label-side: left, "->")
    edge((-1, 0), (-1, 1), [$g'$], label-side: right, "->")
    edge((-1, 0), (0, 0), [$f'$], label-side: left, "->")
    edge((-1, 1), (0, 1), [$f$], label-side: right, "->")
  }))
  中，$f: X -> Y$ 是整态射，基变换态射：
  $
    g^(-1) f_* cal(K) Lotimes_Lambda cal(L) -> f'_* (g'^(-1) cal(K) Lotimes_Lambda f'^(-1) cal(L))
  $
  对一切复形 $cal(K) in D(X_et, Lambda), cal(L) in D(Y'_et, Lambda)$ 都是同构。
]
#proof[
  只需在 $Y$ 上 Zariski 局部（或平展局部）地考虑此问题：把 $Y$ 换成它的一个仿射开集，并沿其开浸入对整个拉回图表作基变换。这样便可假定 $Y = Spec(A)$ 与 $X = Spec(B)$ 都是仿射的，且 $B$ 是整 $A$-代数。
  
  现在可以把 $B$ 写成有限 $A$-代数的正向极限。换言之，可以把 $X = invlim_i X_i$ 写成有限 $Y$-概形的逆向极限。 //由极限公式与 $cal(F) = dirlim_(n>=1) cal(F)[n]$，可以假定 $cal(F) $ 对某个固定的 $n$ 是 $n$-挠的，从而所涉及的层都是 $n$-挠的。
  
  把涉及的态射记为：
  // https://q.uiver.app/#r=typst&q=WzAsNixbMiwwLCJZJyJdLFsyLDEsIlkiXSxbMSwxLCJYX2kiXSxbMCwxLCJYIl0sWzAsMCwiWCciXSxbMSwwLCJYJ19pIl0sWzQsNSwiaCdfaSJdLFs1LDAsImYnX2kiXSxbMiwxLCJmX2kiXSxbMywyLCJoX2kiXSxbMCwxLCJnIl0sWzUsMiwiZydfaSJdLFs0LDMsImcnIiwyXV0=
  #align(center, diagram({
    node((1, -1), [$Y'$])
    node((1, 0), [$Y$])
    node((0, 0), [$X_i$])
    node((-1, 0), [$X$])
    node((-1, -1), [$X'$])
    node((0, -1), [$X'_i$])
    edge((-1, -1), (0, -1), [$h'_i$], label-side: left, "->")
    edge((0, -1), (1, -1), [$f'_i$], label-side: left, "->")
    edge((0, 0), (1, 0), [$f_i$], label-side: left, "->")
    edge((-1, 0), (0, 0), [$h_i$], label-side: left, "->")
    edge((1, -1), (1, 0), [$g$], label-side: left, "->")
    edge((0, -1), (0, 0), [$g'_i$], label-side: left, "->")
    edge((-1, -1), (-1, 0), [$g'$], label-side: right, "->")
  }))
  由 @limit-formula-adjunction，$cal(F) = dirlim_i h_i^(-1) h_(i,*) cal(F)$。记 $cal(F)_i = h_(i,*) cal(F)$。于是由 @relative-limit-formula-composite，
  $
    R^q f_* cal(F) = dirlim_i R^q f_(i,*) cal(F)_i
  $
  当 $q >= 1$ 时，每个 $f_i$ 都有限，故 $R^q f_(i,*) = 0$，而上述余极限的各项全为零。因此 $R^q f_* cal(F) = 0$。这就证明了 $f_*$ 正合这一部分。

  至于基变换，由 @pbc-finite，
  $
    g^(-1) f_* cal(F) = dirlim_i g^(-1) f_(i,*) cal(F)_i = dirlim_i f'_(i,*) g'_i^(-1) cal(F)_i 
  $
  最后注意：
  $
    dirlim_i h'_i^(-1) g'_i^(-1) cal(F)_i = dirlim_i g'^(-1) h_i^(-1) cal(F)_i = g'^(-1) (dirlim_i h_i^(-1) cal(F)_i) = g'^(-1) cal(F) 
  $
  于是可对极限 $dirlim_i f'_(i,*) g'_i^(-1) cal(F)_i$ 应用 @relative-limit-formula-composite，得到：
  $
    g^(-1) f_* cal(F) = dirlim_i f'_(i,*) g'_i^(-1) cal(F)_i = f'_* g'^(-1) cal(F)
  $
  即对整态射的推前，标准基变换是同构。至于相对基变换，只需证明投影那部分是同构。这由基变换部分、投影与基变换的相容性以及 @projection-formula-for-global-sections 推出。（这里整态射的几何纤维有限，故 @projection-formula-for-global-sections 的有限型假设成立。）
]

下面这个定理给出主要的归约结果。

#theorem(name: <rel-bc-reductions>)[
  设 $Lambda$ 是挠 Noether 环。设 $g: S' -> S$ 是态射，其中 $S$ 是 Noether 概形，且 $cal(L)_S in D^b_#[ctf] (S'_et, Lambda)$。则以下各项等价：

  + 对拟紧拟分离 $S$-概形之间的每个态射 $f: X -> Y$，沿下述拉回方块作基变换：
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
    并令 $cal(L)_X = cal(L)_S|_(X')$，$cal(L)_Y = cal(L)_S|_(Y')$。则相对基变换映射
    $
      g_Y^(-1) R f_* cal(K) Lotimes_Lambda cal(L)_Y -> R f'_* (g_X^(-1) cal(K) Lotimes_Lambda cal(L)_X)
    $
    对一切 $cal(K) in D^+ (X_et, Lambda)$ 都是同构。

  + 上述条件对 $f: xi -> X$ 成立，只要：

    - $X$ 是某个有限型仿射整 $S$-概形在其函数域的代数闭包中的正规化；
    
    - $xi$ 是 $X$ 的泛点，且该泛点是代数闭的；

    且 $cal(K) = ul(M)$，其中 $M$ 是有限 $Lambda$-模。此外，如果每个有限 $Lambda$-模都能嵌入某个有限自由 $Lambda$-模，那么只需对 $cal(K) = ul(Lambda)$ 要求该条件成立。
]
#proof[
  (1) $==>$(2) 是同义反复，故只需证明 (2) $==>$(1)。整个证明本质上是一连串归约。另外注意，由于 $cal(L)_S in D^b_#[ctf] (S'_et, Lambda)$，而任意拉回都保持 $Lambda$-模层的平坦性，$cal(L)_X, cal(L)_Y$ 始终分别属于相应概形的 $D^b_#[ctf]$。

  于是 $g_Y^(-1) R f_* cal(K) Lotimes_Lambda cal(L)_Y -> R f'_* (g_X^(-1) cal(K) Lotimes_Lambda cal(L)_X)$ 的两边作为 $cal(K)$ 的函子都上有界且下有界。由 way-out 引理，只需处理 $cal(K) = cal(F) in cAb(X_et, Lambda)$ 只是单个层的情形。此后我们总假定 $cal(K) = cal(F)$ 是单个层。

  此外，为使用极限公式，我们需要把导出范畴中的陈述转译为 Abel 范畴中的陈述。把 $cal(L)_S$ 换成平坦层的有界复形 $cal(P)_S^bullet$。则由超上同调谱序列，相对基变换的左端有一个谱序列：
  $
    E_1^(p,q) = g_Y^(-1) R^q f_* cal(F) otimes_Lambda cal(P)_Y^p ==> h^(p+q) (g_Y^(-1) R f_* cal(F) Lotimes_Lambda cal(L)_Y)
  $
  右端也有一个谱序列：
  $
    tilde(E)_1^(p,q) = R^q f'_* (g_X^(-1) cal(F) otimes_Lambda cal(P)_X^p) ==> h^(p+q) (R f'_* (g_X^(-1) cal(F) otimes_Lambda cal(L)_X))
  $
  进一步，相对基变换映射 $h^(p+q) (g_Y^(-1) R f_* cal(F) Lotimes_Lambda cal(L)_Y) -> h^(p+q) (R f'_* (g_X^(-1) cal(F) otimes_Lambda cal(L)_X))$ 由下面这些相对基变换映射诱导：
  $
    E_1^(p,q) = g_Y^(-1) R^q f_* cal(F) otimes_Lambda cal(P)_Y^p -> R^q f'_* (g_X^(-1) cal(F) otimes_Lambda cal(P)_X^p) = tilde(E)_1^(p,q)
  $

  第一步。只需处理 $X -> Y$ 是有限展示的情形。

  #proof_[第一步的证明][
    注意 $f: X -> Y$ 是拟紧拟分离的，故由 @relative-approx，可把 $X = invlim_lambda X_lambda$ 写成有限展示 $Y$-概形的逆向极限，过渡态射都是仿射的。于是我们有如下 $S$-概形的拉回图表：
    // https://q.uiver.app/#r=typst&q=WzAsNixbMCwwLCJYJyJdLFsxLDAsIlgnX2xhbWJkYSJdLFsyLDAsIlknIl0sWzAsMSwiWCJdLFsxLDEsIlhfbGFtYmRhIl0sWzIsMSwiWSJdLFsyLDUsImciXSxbMSw0LCJnJ19sYW1iZGEiXSxbMCwzLCJnJyIsMl0sWzQsNSwiZl9sYW1iZGEiLDJdLFszLDQsImhfbGFtYmRhIiwyXSxbMCwxLCJoJ19sYW1iZGEiXSxbMSwyLCJmJ19sYW1iZGEiXV0=
    #align(center, diagram({
      node((0, 0), [$X'$])
      node((1, 0), [$X'_lambda$])
      node((2, 0), [$Y'$])
      node((0, 1), [$X$])
      node((1, 1), [$X_lambda$])
      node((2, 1), [$Y$])
      edge((2, 0), (2, 1), [$g_Y$], label-side: left, "->")
      edge((1, 0), (1, 1), [$g_lambda$], label-side: left, "->")
      edge((0, 0), (0, 1), [$g_X$], label-side: right, "->")
      edge((1, 1), (2, 1), [$f_lambda$], label-side: right, "->")
      edge((0, 1), (1, 1), [$h_lambda$], label-side: right, "->")
      edge((0, 0), (1, 0), [$h'_lambda$], label-side: left, "->")
      edge((1, 0), (2, 0), [$f'_lambda$], label-side: left, "->")
    }))
    取 $cal(F)_lambda = h_(lambda,*) cal(F)$，并取 $cal(L)_Y$ 的有界平坦消解 $cal(P)^bullet$。由 @limit-formula-adjunction，$cal(F) = dirlim_lambda h_lambda^(-1) cal(F)_lambda$。现在对各个 $lambda$，考虑右方方块的相对基变换在左端与右端给出的两个谱序列：
    $
      E_(1,lambda)^(p,q) = g_Y^(-1) R^q f_(lambda,*) cal(F)_lambda otimes_Lambda cal(P)^p => h^(p+q) (g_Y^(-1) R f_(lambda,*) cal(F)_lambda Lotimes_Lambda cal(L)_Y) \

      tilde(E)_(1,lambda)^(p,q) = R^q f'_(lambda,*) (g_lambda^(-1) cal(F)_lambda otimes_Lambda f'_lambda^(-1) cal(P)^p) => h^(p+q) (R f'_(lambda,*) (g_lambda^(-1) cal(F)_lambda Lotimes_Lambda f'_lambda^(-1) cal(L)_Y))
    $
    对 $lambda$ 取正向极限：
    $
      dirlim_lambda (g_Y^(-1) R^q f_(lambda,*) cal(F)_lambda otimes_Lambda cal(P)^p) = g_Y^(-1) (dirlim_lambda R^q f_(lambda,*) cal(F)_lambda) otimes_Lambda cal(P)^p cong g_Y^(-1) R^q f_* cal(F) otimes_Lambda cal(P)^p
    $
    这里用了 @relative-limit-formula-for-schemes；同样由该极限公式：
    $
      dirlim_lambda (R^q f'_(lambda,*) (g_lambda^(-1) cal(F) otimes_Lambda f'_lambda^(-1) cal(P)^p)) &cong R^q f'_* (dirlim_lambda (h'_lambda^(-1) g_lambda^(-1) cal(F)_lambda otimes_Lambda f'^(-1) cal(P)^p)) \
      &= R^q f'_* ((dirlim_lambda g_X^(-1) h_lambda^(-1) cal(F)_lambda) otimes_Lambda f'^(-1) cal(P)^p) \
      &= R^q f'_* (g_X^(-1) cal(F) otimes_Lambda f'^(-1) cal(P)^p)
    $
    于是得到典范谱序列：
    $
      E_1^(p,q) = g_Y^(-1) R^q f_* cal(F) otimes_Lambda cal(P)^p => dirlim_lambda h^(p+q) (g_Y^(-1) R f_(lambda,*) cal(F)_lambda Lotimes_Lambda cal(L)_Y) \
      tilde(E)_1^(p,q) = R^q f'_* (g_X^(-1) cal(F) otimes_Lambda f'^(-1) cal(P)^p) => dirlim_lambda h^(p+q) (R f'_(lambda,*) (g_lambda^(-1) cal(F)_lambda Lotimes_Lambda f'_lambda^(-1) cal(L)_Y))
    $
    然而，同样的典范正合列分别收敛到 $h^(p+q) (g_Y^(-1) R f_* cal(F) Lotimes_Lambda cal(L)_Y)$ 与 $h^(p+q) (R f'_* (g_X^(-1) cal(F) Lotimes_Lambda cal(L)_X))$。更确切地说，存在两个谱序列的典范态射，各自在 $E_1$-页上都是恒等，故两者的极限同构。于是得到典范同构：
    $
      h^(p+q) (g_Y^(-1) R f_* cal(F) Lotimes_Lambda cal(L)_Y) cong dirlim_lambda h^(p+q) (g_Y^(-1) R f_(lambda,*) cal(F)_lambda Lotimes_Lambda cal(L)_Y) \

      h^(p+q) (R f'_* (g_X^(-1) cal(F) otimes_Lambda cal(L)_X)) cong dirlim_lambda h^(p+q) (R f'_(lambda,*) (g_lambda^(-1) cal(F)_lambda Lotimes_Lambda f'_lambda^(-1) cal(L)_Y))
    $
    这两个同构的右端彼此同构，因为已假定沿有限展示态射 $f_lambda: X_lambda -> Y$、关于 $cal(L)$ 的相对基变换是同构。于是两个左端同构，证毕。
  ]  

  第二步。只需处理 $f: X -> Y$ 是有限型 $S$-概形之间的态射的情形。

  #proof_[第二步的证明][
    由第一步，可假定 $f: X -> Y$ 是拟紧拟分离 $S$-概形之间的有限展示态射。由 @passage-to-limit-of-morphisms 与 @relative-approx，可写出 $Y = invlim_i Y_i$，其中 $i >= 0$ 时 $Y_i$ 是有限型 $S$-概形；并且有有限型态射 $f_0: X_0 -> Y_0$，它沿 $Y -> Y_0$ 的基变换正是 $f: X -> Y$。令 $f_i: X_i -> Y_i$ 为 $f_0$ 沿 $Y_i -> Y_0$ 的基变换。

    现在有一个各面都是拉回的立方体：
    // https://q.uiver.app/#r=typst&q=WzAsOCxbMCwwLCJYJyJdLFsyLDAsIlknIl0sWzEsMSwiWCdfaSJdLFszLDEsIlknX2kiXSxbMCwyLCJYIl0sWzIsMiwiWSJdLFsxLDMsIlhfaSJdLFszLDMsIllfaSJdLFszLDcsImdfKFlfaSkiLDEseyJsYWJlbF9wb3NpdGlvbiI6MjB9XSxbMSw1LCJnX1kiLDEseyJsYWJlbF9wb3NpdGlvbiI6ODB9XSxbMiw2LCJnXyhYX2kpIiwxLHsibGFiZWxfcG9zaXRpb24iOjIwfV0sWzAsNCwiZ19YIiwxLHsibGFiZWxfcG9zaXRpb24iOjgwfV0sWzQsNSwiZiIsMSx7ImxhYmVsX3Bvc2l0aW9uIjozMH1dLFswLDEsImYnIiwxXSxbNiw3LCJmX2kiLDFdLFsyLDMsImYnX2kiLDEseyJsYWJlbF9wb3NpdGlvbiI6ODB9XSxbNSw3LCJoX2kiLDFdLFsxLDMsImgnX2kiLDFdLFs0LDYsImtfaSIsMV0sWzAsMiwiaydfaSIsMV1d
    #context align(center, diagram({
      node((0, 0), [$X'$])
      node((2, 0), [$Y'$])
      node((1, 1), [$X'_i$])
      node((3, 1), [$Y'_i$])
      node((0, 2), [$X$])
      node((2, 2), [$Y$])
      node((1, 3), [$X_i$])
      node((3, 3), [$Y_i$])
      edge((3, 1), (3, 3), [$g_(Y_i)$], label-side: center, label-pos: 0.2, "->")
      edge((2, 0), (2, 2), [$g_Y$], label-side: center, label-pos: 0.8, "->")
      edge((1, 1), (1, 3), [$g_(X_i)$], label-side: center, label-pos: 0.2, "->")
      edge((0, 0), (0, 2), [$g_X$], label-side: center, label-pos: 0.8, "->")
      edge((0, 2), (2, 2), [$f$], label-side: center, label-pos: 0.8, "->")
      edge((0, 0), (2, 0), [$f'$], label-side: center, "->")
      edge((1, 3), (3, 3), [$f_i$], label-side: center, "->")
      edge((1, 1), (3, 1), [$f'_i$], label-side: center, label-pos: 0.2, "->")
      edge((2, 2), (3, 3), [$h_i$], label-side: center, "->")
      edge((2, 0), (3, 1), [$h'_i$], label-side: center, "->")
      edge((0, 2), (1, 3), [$k_i$], label-side: center, "->")
      edge((0, 0), (1, 1), [$k'_i$], label-side: center, "->")
    }, crossing-fill: thm-box-curr-color()))
    其中竖直态射都是 $g: S' -> S$ 的基变换。令 $cal(L) = cal(L)_Y$、$cal(L)_i = cal(L)_(Y_i)$，并取 $cal(L), cal(L)_i$ 的平坦消解 $cal(P)^bullet, cal(P)_i^bullet$，它们都支撑在某个有界区间上。令 $cal(F)_i = k_(i,*) cal(F)$，则由 @limit-formula-adjunction 有 $cal(F) = dirlim_i k_i^(-1) cal(F)_i$。
    
    考虑典范谱序列：
    $
      E_(1,i)^(p,q) = g_(Y_i)^(-1) R^q f_(i,*) cal(F)_i otimes_Lambda cal(P)^p_i => h^(p+q) (g_(Y_i)^(-1) R f_(i,*) cal(F)_i Lotimes_Lambda cal(L)_i) \

      tilde(E)_1^(p,q) = R^q f'_(i,*) (g_(X_i)^(-1) cal(F)_i otimes_Lambda f'_i^(-1) cal(P)^p_i) => h^(p+q) (R f'_(i,*) (g_(X_i)^(-1) cal(F)_i Lotimes_Lambda f'_i^(-1) cal(L)_i))
    $
    取极限 $dirlim_i h'_i^(-1) E_1^(p,q)$ 与 $dirlim_i h'_i^(-1) tilde(E)_1^(p,q)$：
    $
      dirlim_i h'_i^(-1) E_1^(p,q) &= dirlim_i (h'_i^(-1) g_(Y_i)^(-1) R^q f_(i,*) cal(F)_i otimes_Lambda h'_i^(-1) cal(P)^p_i) \
      &= g_Y^(-1) dirlim_i h_i^(-1) R^q f_(i,*) cal(F)_i otimes_Lambda cal(P)^p \
      &cong g_Y^(-1) R^q f_* cal(F) otimes_Lambda cal(P)^p
    $
    这里用了 @limit-formula-for-base-change。同样由该极限公式，
    $
      dirlim_i h'_i^(-1) tilde(E)_1^(p,q) &= dirlim_i h'_i^(-1) R^q f'_(i,*) (g_(X_i)^(-1) cal(F)_i otimes_Lambda f'_i^(-1) cal(P)^p_i) \
      &cong R^q f'_* (dirlim_i k'_i^(-1) (g_(X_i)^(-1) cal(F)_i otimes_Lambda f'_i^(-1) cal(P)^p_i)) \
      &= R^q f'_* (dirlim_i (g_X^(-1) k_i^(-1) cal(F)_i otimes_Lambda f'^(-1) h'_i^(-1) cal(P)^p_i)) \
      &= R^q f'_* (g_X^(-1) (dirlim_i k_i^(-1) cal(F)_i) otimes_Lambda cal(P)^p) \
      &= R^q f'_* (g_X^(-1) cal(F) otimes_Lambda cal(P)^p)
    $
    于是得到典范谱序列：
    $
      E_1^(p,q) = g_Y^(-1) R^q f_* cal(F) otimes_Lambda cal(P)^p => dirlim_i h'_i^(-1) h^(p+q) (g_(Y_i)^(-1) R f_(i,*) cal(F)_i Lotimes_Lambda cal(L)_i) \

      tilde(E)_1^(p,q) = R^q f'_* (g_X^(-1) cal(F) otimes_Lambda cal(P)^p) => dirlim_i h'_i^(-1) h^(p+q) (R f'_(i,*) (g_(X_i)^(-1) cal(F)_i Lotimes_Lambda f'_i^(-1) cal(L)_i))
    $
    然而，同样的典范正合列分别收敛到 $h^(p+q) (g_Y^(-1) R f_* cal(F) Lotimes_Lambda cal(L)_Y)$ 与 $h^(p+q) (R f'_* (g_X^(-1) cal(F) Lotimes_Lambda cal(L)_X))$。更确切地说，存在两个谱序列的典范态射，各自在 $E_1$-页上都是恒等，故两者的极限同构。于是得到典范同构：
    $
      h^(p+q) (g_Y^(-1) R f_* cal(F) Lotimes_Lambda cal(L)_Y) cong dirlim_i h'_i^(-1) h^(p+q) (g_(Y_i)^(-1) R f_(i,*) cal(F)_i Lotimes_Lambda cal(L)_i) \

      h^(p+q) (R f'_* (g_X^(-1) cal(F) otimes_Lambda cal(L)_X)) cong dirlim_i h'_i^(-1) h^(p+q) (R f'_(i,*) (g_(X_i)^(-1) cal(F)_i Lotimes_Lambda f'_i^(-1) cal(L)_i))
    $
    这两个同构的右端彼此同构，因为已假定沿有限型 $S$-概形之间的态射 $f_i: X_i -> Y_i$、关于 $cal(L)_i$ 的相对基变换是同构。于是两个左端同构，证毕。
  ]

  第三步。只需处理 $f: X -> Y$ 是开浸入、且 $Y$ 在 $S$ 上有限型的情形。

  #proof_[第三步的证明][
    由第二步，可假定 $f: X -> Y$ 是有限型 $S$-概形之间的态射。

    再假定 $f$ 分离。由于 $S$ 是 Noether 概形，$X$ 与 $Y$ 也是，故可取紧化 $X ->^j ol(X) ->^(ol(f)) Y$。此时由假设，沿 $j$ 的相对基变换关于 $cal(L)_(ol(X))$ 是同构；而沿 $ol(f)$ 的相对基变换关于 $cal(L)_Y$ 由紧合基变换也是同构。因此沿 $f$ 的相对基变换关于 $cal(L)_Y$ 是同构，分离情形得证。

    由于 $X$ 是 Noether 概形，可用有限多个仿射开集覆盖它。也就是说，存在仿射概形 $Z$ 以及满射 $j: Z -> X$。由已证的分离情形，沿 $j$ 与沿 $f compose j$ 的相对基变换关于 $cal(L)_Y$ 都是同构。对形如 $R j_* cal(K)_Z$ 的复形 $cal(K)$，如下复合：
    $
      g_Y^(-1) R f_* R j_* cal(K)_Z Lotimes_Lambda cal(L)_Y -> R f'_* (g_X^(-1) R j_* cal(K)_Z Lotimes_Lambda cal(L)_X) -> R f'_* R j_* (g_Z^(-1) cal(K)_Z Lotimes_Lambda cal(L)_Z) 
    $
    它由 $f$ 与 $j$ 的相对基变换复合而成，等于沿 $f compose j$ 的相对基变换。因此这里的复合是同构，而第二个映射由分离情形也是同构。于是第一个映射
    $
      g_Y^(-1) R f_* R j_* cal(K)_Z Lotimes_Lambda cal(L)_Y -> R f'_* (g_X^(-1) R j_* cal(K)_Z Lotimes_Lambda cal(L)_X)
    $
    总是同构。

    设 $cal(L)_S$ 有支撑在 $[b_1, b_2]$ 上的平坦消解。则对任意复形 $cal(K) in D_(>=a) (X_et, Lambda)$，下式两边
    $
      g_Y^(-1) R f_* cal(K) Lotimes_Lambda cal(L)_Y -> R f'_* (g_X^(-1) cal(K) Lotimes_Lambda cal(L)_X)
    $
    都支撑在 $>=a-b_1$ 上。构造特殊三角：
    $
      cal(K) -> R j_* j^(-1) cal(K) -> cal(R) ->^(+1) 
    $
    由超上同调谱序列，$h^a (R j_* j^(-1) cal(K)) cong j_* j^(-1) h^a (cal(K))$。由 @surjection-has-injective-unit，$h^a (cal(K)) -> h^a (R j_* j^(-1) cal(K)) cong j_* j^(-1) h^a (cal(K))$ 是单射，故其核 $h^(a-1) (cal(R)) = 0$。因此 $cal(R) in D_(>=a) (X_et, Lambda)$。现在构造长正合列：
    
    // https://q.uiver.app/#r=typst&q=WzAsMTQsWzAsMCwiZG90cy52Il0sWzAsMSwiaF5xIChnX1heKC0xKSBSIGZfKiBSIGpfKiBqXigtMSkgY2FsKEspIExvdGltZXNfTGFtYmRhIGNhbChMKV9ZKSJdLFswLDIsImhecSAoZ19YXigtMSkgUiBmXyogY2FsKFIpIExvdGltZXNfTGFtYmRhIGNhbChMKV9ZKSJdLFswLDMsImheKHErMSkgKGdfWF4oLTEpIFIgZl8qIGNhbChLKSBMb3RpbWVzX0xhbWJkYSBjYWwoTClfWSkiXSxbMCw0LCJoXihxKzEpIChnX1heKC0xKSBSIGZfKiBSIGpfKiBqXigtMSkgY2FsKEspIExvdGltZXNfTGFtYmRhIGNhbChMKV9ZKSJdLFswLDUsImheKHErMSkgKGdfWF4oLTEpIFIgZl8qIGNhbChSKSBMb3RpbWVzX0xhbWJkYSBjYWwoTClfWSkiXSxbMCw2LCJkb3RzLnYiXSxbMiwwLCJkb3RzLnYiXSxbMiw2LCJkb3RzLnYiXSxbMiwxLCJoXnEgKFIgZidfKiAoZ19ZXigtMSkgUiBqXyogal4oLTEpIGNhbChLKSBMb3RpbWVzX0xhbWJkYSBjYWwoTClfWCkpIl0sWzIsNCwiaF4ocSsxKSAoUiBmJ18qIChnX1leKC0xKSBSIGpfKiBqXigtMSkgY2FsKEspIExvdGltZXNfTGFtYmRhIGNhbChMKV9YKSkiXSxbMiwyLCJoXnEgKFIgZidfKiAoZ19ZXigtMSkgY2FsKFIpIExvdGltZXNfTGFtYmRhIGNhbChMKV9YKSkiXSxbMiwzLCJoXihxKzEpIChSIGYnXyogKGdfWV4oLTEpIGNhbChLKSBMb3RpbWVzX0xhbWJkYSBjYWwoTClfWCkpIl0sWzIsNSwiaF4ocSsxKSAoUiBmJ18qIChnX1leKC0xKSBjYWwoUikgTG90aW1lc19MYW1iZGEgY2FsKEwpX1gpKSJdLFsxLDldLFsyLDExXSxbMywxMl0sWzQsMTBdLFs1LDEzXSxbMSwyXSxbMiwzXSxbMyw0XSxbNCw1XSxbMCwxXSxbNSw2XSxbNyw5XSxbOSwxMV0sWzExLDEyXSxbMTIsMTBdLFsxMCwxM10sWzEzLDhdXQ==
    #align(center, diagram({
      node((0, 0), [$dots.v$])
      node((0, 1), [$h^q (g_Y^(-1) R f_* R j_* j^(-1) cal(K) Lotimes_Lambda cal(L)_Y)$])
      node((0, 2), [$h^q (g_Y^(-1) R f_* cal(R) Lotimes_Lambda cal(L)_Y)$])
      node((0, 3), [$h^(q+1) (g_Y^(-1) R f_* cal(K) Lotimes_Lambda cal(L)_Y)$])
      node((0, 4), [$h^(q+1) (g_Y^(-1) R f_* R j_* j^(-1) cal(K) Lotimes_Lambda cal(L)_Y)$])
      node((0, 5), [$h^(q+1) (g_Y^(-1) R f_* cal(R) Lotimes_Lambda cal(L)_Y)$])
      node((0, 6), [$dots.v$])
      node((2, 0), [$dots.v$])
      node((2, 6), [$dots.v$])
      node((2, 1), [$h^q (R f'_* (g_X^(-1) R j_* j^(-1) cal(K) Lotimes_Lambda cal(L)_X))$])
      node((2, 4), [$h^(q+1) (R f'_* (g_X^(-1) R j_* j^(-1) cal(K) Lotimes_Lambda cal(L)_X))$])
      node((2, 2), [$h^q (R f'_* (g_X^(-1) cal(R) Lotimes_Lambda cal(L)_X))$])
      node((2, 3), [$h^(q+1) (R f'_* (g_X^(-1) cal(K) Lotimes_Lambda cal(L)_X))$])
      node((2, 5), [$h^(q+1) (R f'_* (g_X^(-1) cal(R) Lotimes_Lambda cal(L)_X))$])
      edge((0, 1), (2, 1), "->")
      edge((0, 2), (2, 2), "->")
      edge((0, 3), (2, 3), "->")
      edge((0, 4), (2, 4), "->")
      edge((0, 5), (2, 5), "->")
      edge((0, 1), (0, 2), "->")
      edge((0, 2), (0, 3), "->")
      edge((0, 3), (0, 4), "->")
      edge((0, 4), (0, 5), "->")
      edge((0, 0), (0, 1), "->")
      edge((0, 5), (0, 6), "->")
      edge((2, 0), (2, 1), "->")
      edge((2, 1), (2, 2), "->")
      edge((2, 2), (2, 3), "->")
      edge((2, 3), (2, 4), "->")
      edge((2, 4), (2, 5), "->")
      edge((2, 5), (2, 6), "->")
    }))

    这个图表的各列正合；由分离情形，我们已经推出第一与第四个水平映射是同构。设对一切 $cal(K) in D_(>=a)$，映射 $g_Y^(-1) R f_* cal(K) Lotimes_Lambda cal(L)_Y -> R f'_* (g_X^(-1) cal(K) Lotimes_Lambda cal(L)_X)$ 对一切 $r <= q$ 都在 $h^r$ 上是同构。则第二个水平箭头是同构，再由单射四引理，第三个水平箭头成为单射。

    由于 $cal(K)$ 可以是 $D_(>=a)$ 中任意复形，且 $cal(R) in D_(>=a)$，同样的论证表明第五个水平箭头是单射。于是由满射四引理，第三个水平箭头是满射。因此，若
    $
      g_Y^(-1) R f_* cal(K) Lotimes_Lambda cal(L)_Y -> R f'_* (g_X^(-1) cal(K) Lotimes_Lambda cal(L)_X)
    $
    对一切 $r<=q$ 与一切 $cal(K) in D_(>=a)$ 都在 $h^r$ 上同构，则同一陈述对 $h^(q+1)$ 也成立。两边都支撑在 $>=a-b_1$ 上，故该映射对 $r<=a-b_1-1$ 在 $h^r$ 上自动是同构。由归纳法，这个映射是拟同构。
  ]

  第四步。证明的收尾。

  #proof[
    设 $f: X -> Y$ 是有限型 $S$-概形之间的开浸入。特别地，$X, Y$ 都是 Noether 概形。设 $cal(F) = dirlim_lambda cal(F)_lambda$。

    对 $cal(F)_lambda$ 取左端与右端的谱序列：
    $
      E_(1,lambda)^(p,q) = g_Y^(-1) R^q f_* cal(F)_lambda otimes_Lambda cal(P)_Y^p ==> h^(p+q) (g_Y^(-1) R f_* cal(F)_lambda Lotimes_Lambda cal(L)_Y)
    $
    右端也有一个谱序列：
    $
      tilde(E)_(1,lambda)^(p,q) = R^q f'_* (g_X^(-1) cal(F)_lambda otimes_Lambda cal(P)_X^p) ==> h^(p+q) (R f'_* (g_X^(-1) cal(F)_lambda otimes_Lambda cal(L)_X))
    $
    对所有 $lambda$ 取极限，并用 @relative-limit-formula-for-sheaves，便得到（论证与第二步、第三步类似）：
    $
      dirlim_lambda h^(p+q) (g_Y^(-1) R f_* cal(F)_lambda Lotimes_Lambda cal(L)_Y) cong h^(p+q) (g_Y^(-1) R f_* cal(F) Lotimes_Lambda cal(L)_Y) \
      dirlim_lambda h^(p+q) (R f'_* (g_X^(-1) cal(F)_lambda otimes_Lambda cal(L)_X)) cong h^(p+q) (R f'_* (g_X^(-1) cal(F) otimes_Lambda cal(L)_X))
    $
    因此，若对每个 $cal(F)_lambda$，映射 $g_Y^(-1) R f_* cal(F)_lambda Lotimes_Lambda cal(L)_Y -> R f'_* (g_X^(-1) cal(F)_lambda otimes_Lambda cal(L)_X)$ 都是拟同构，则它对 $cal(F)$ 也是拟同构。由 @constructible-sheaves-first-props，可假定 $cal(F)$ 是 $Lambda$-模的可构造层。

    由 @constructible-godement-resolution，存在 $X$ 的有限多个代数几何点 $ol(x_1), dots.c, ol(x_m)$，以及单射 $cal(F) -> oplus.big_(i=1)^m ol(x_i)_* ul(M_i)$，其中 $M_i$ 是有限 $Lambda$-模。对正合列 $0 -> cal(F) -> oplus.big_(i=1)^m ol(x_i)_* ul(M_i) -> cal(R) -> 0$ 照第三步那样作两阶段四引理论证，便只需对每个直和项证明相对基变换。于是可假定 $cal(F) = ol(x)_* ul(M)$，其中 $M$ 是有限 $Lambda$-模。构造拉回图表：
    // https://q.uiver.app/#r=typst&q=WzAsNixbMSwwLCJYJyJdLFsyLDAsIlknIl0sWzEsMSwiWCJdLFsyLDEsIlkiXSxbMCwxLCJQID0gb2woeCkiXSxbMCwwLCJQJyJdLFsyLDMsImYiLDJdLFswLDEsImYnIl0sWzEsMywiZ19YIl0sWzAsMiwiZ19ZIiwyXSxbNCwyLCJwIiwyXSxbNSw0LCJnX1AiLDJdLFs1LDAsInAnIl1d
    #align(center, diagram({
      node((0, 0), [$X'$])
      node((1, 0), [$Y'$])
      node((0, 1), [$X$])
      node((1, 1), [$Y$])
      node((-1, 1), [$P = ol(x)$])
      node((-1, 0), [$P'$])
      edge((0, 1), (1, 1), [$f$], label-side: right, "->")
      edge((0, 0), (1, 0), [$f'$], label-side: left, "->")
      edge((1, 0), (1, 1), [$g_Y$], label-side: left, "->")
      edge((0, 0), (0, 1), [$g_X$], label-side: right, "->")
      edge((-1, 1), (0, 1), [$p$], label-side: right, "->")
      edge((-1, 0), (-1, 1), [$g_P$], label-side: right, "->")
      edge((-1, 0), (0, 0), [$p'$], label-side: left, "->")
    }))
    考虑相对基变换的复合：
    $
      g_Y^(-1) R f_* p_* ul(M) Lotimes_Lambda cal(L)_Y -> R f'_* (g_X^(-1) p_* ul(M) Lotimes_Lambda cal(L)_X) -> R f'_* R p'_* (ul(M) Lotimes_Lambda cal(L)_P)
    $
    它正是沿 $f compose p: ol(x) -> Y$ 的相对基变换。我们要证明第一个映射是同构。为此只需说明第二个映射与整个复合都是同构。它们分别是沿 $p: ol(x) -> X$ 与沿 $f compose p: ol(x) -> Y$ 关于层 $ul(M)$ 的相对基变换。由于 $X -> Y$ 是开浸入，$ol(x) -> Y$ 是代数几何点。于是剩下要证的是：

    - 对每个代数几何点 $p: ol(x) = P -> X$，相对基变换 #h(1fr)
      $
        g_X^(-1) p_* ul(M) Lotimes_Lambda cal(L)_X -> g_P^(-1) (ul(M) Lotimes_Lambda cal(L)_P)
      $
      是同构。

    注意此问题在 $X$ 上是 Zariski 局部的，故可假定 $X$ 仿射。

    设 $ol(x)$ 位于 $x in X$ 上方，故 $ol(x) = Spec(ol(k(x)))$。令 $Z$ 为 $X$ 的闭子概形 $ol({x})$，并赋予既约子结构，于是 $Z$ 是整概形，函数域为 $k(x)$。令 $ol(Z)$ 为 $Z$ 在 $ol(k(x))$ 中的正规化，于是 $ol(Z)$ 是正规整概形，函数域为 $ol(k(x))$。因此 $ol(x)$ 是 $ol(Z)$ 的泛点。现在 $ol(x) -> X$ 有如下分解：
    $
      ol(x) ->^j ol(Z) ->^nu Z ->^i X
    $
    这里 $nu$ 是正规化映射，故为整态射；$i$ 是闭浸入。沿它们的相对基变换由 @finite-bc-in-the-limit 总是同构。因此只需证明 $ul(M)$ 沿 $j: ol(x) -> ol(Z)$ 的相对基变换是同构。

    此时 $ol(Z)$ 是整、有限型 $S$-概形 $Z$ 在其函数域的代数闭包中的正规化；由于已假定 $X$ 仿射，$ol(Z)$ 是仿射的。于是由假设即得结论。

    最后，若每个有限 $Lambda$-模都能嵌入某个有限自由 $Lambda$-模，还可以进一步嵌入：
    $
      cal(F) arrow.hook oplus.big_i ol(x_i)_* ul(M) arrow.hook oplus.big_j ol(x_j)_* ul(Lambda)
    $
    于是上面出现的 $M$ 全都可以换成 $Lambda$ 本身。因此假设中的 $M$ 也可以换成 $Lambda$。
  ]
]
