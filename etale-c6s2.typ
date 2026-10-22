// audit-exception: 展示公式内的 #[...] 文字块嵌有多段 $...$，朴素配对会把块内散文切成伪公式段（如 $above$、$s.t.$）；译文只改文字说明，块内公式与全部数学内容逐段核对未变。
#import "void-import.typ": *

== 可构造层

本节引入可构造层。可构造层是挠层中合适的一类：结构温和，比可能千变万化的任意挠层容易研究得多。在某种意义上，可构造性是对层的一项合理的有限性条件——它是介于常值层 $ul(ZZ\/n)$ 与任意挠层之间的一个中间层次。平展上同调后续理论的很大一部分都围绕可构造层展开（以及其中限制更强的一类，即局部系统）。 

可构造层的这套机制将在紧合基变换的证明中首次登场，借 _devissage_ 论证展示其威力：先用层的极限公式把一般挠层化归为可构造层，再在相差一个有限态射的意义下把可构造层化归为常值层 $ul(ZZ\/n)$，从而把关于一般挠层的结论化归为关于 $ul(ZZ\/n)$ 的结论。 

为简单起见，本节假定 $X$ 是 Noether 概形。$Lambda$ 表示系数环，它始终是 Noether 环。 

/*
#definition[
  给定 $X$-概形 $X'$，回忆 $cSh(X_et)$ 中存在一个平展层，定义为： 
  $
    Et_X -> cSet, U |-> Hom_X (U, X')
  $
  以上定义依据 @examples-of-etale-sheaves。若再给 $X'$ 配上 $X$ 上交换群概形的结构，它就定义了 $cAb(X_et)$ 中的一个交换群层。 

  该层记为 $h_(X')$ 或 $tilde(X')$。 
]

#example[
  对有限交换群 $G$，记：
  $
    G_X = union.big_(g in G) X
  $
  这是有限平展 $X$-群概形。它表示 $X_et$ 上的常值层 $ul(G)$。事实上，它把 $U in Et_X$ 送到 $Hom_X (U, G_X)$，即连续（也就是局部常值）函数 $X -> G$ 构成的空间。这与我们对 $ul(G)$ 的刻画相符。我们写作： 
  $
    ul(G) = tilde(G_X)
  $
  以此表示这一点。 
]*/

#definition(name: <defn-locally-constant-and-lcc-sheaves>)[
  设 $X$ 是 Noether 概形，其上取值于交换群（相应地，集合；相应地，$Lambda$-模）的平展层 $cal(F)$，若存在平展覆盖 $cal(U) = {U_i -> X}$，使每个 $cal(F)|_(U_i)$ 都是常值层，则称它为*局部常值层* (locally constant sheaf)。 

  取值于 $Lambda$-模（相应地，集合；相应地，交换群）的平展层 $cal(F)$，若 $cal(F)$ 是局部常值层，且其各茎都是有限 $Lambda$-模（相应地，有限集；相应地，有限交换群），则称它为 #furi[locally constant constructible][局部常值可构造] (l.c.c.)。 

  换言之，交换群的 l.c.c. 平展层就是挠的 $ZZ$-模 l.c.c. 平展层；等价地，是对某个 $n$ 而言的 $ZZ\/n$-模 l.c.c. 平展层。 

  只说一个*l.c.c. 层*时，指的是交换群的 l.c.c. 层。 
]

#definition(name: <defn-specialization-morphism>)[
  给定 $X$ 的几何点 $ol(x)$。所谓 $ol(x)$ 的*一般化* (generalization)，是 $tilde(X)_(ol(x))$ 的一个几何点 $ol(eta)$；我们同样把 $ol(eta)$ 在 $tilde(X)_(ol(x)) -> X$ 下的像记为 $ol(eta)$。 

  设 $cal(F) in cAb(X_et)$ 或 $cSh(X_et)$。给定一般化 $ol(x)$ 的 $ol(eta)$，*特殊化态射* (specialization morphism) 定义为如下态射： 
  $
    sp_(ol(x),ol(eta)): cal(F)_(ol(x)) = Gamma(tilde(X)_(ol(x)), cal(F)|_(tilde(X)_(ol(x)))) -> Gamma(tilde(X)_(ol(eta)), cal(F)|_(tilde(X)_(ol(eta)))) = cal(F)_(ol(eta))
  $
  它等同于整体截面的限制映射，其中 $tilde(X)_(ol(eta)) = (tilde(X)_(ol(x)))^tilde_(ol(eta)) -> tilde(X)_(ol(x))$。 

  #remark[
    展开定义以及极限公式中的同构，即可看出： 

    - $ol(eta) -> tilde(X)_(ol(x))$ 对每个平展邻域 $(U, ol(u))$ 函子性地诱导出 $U$ 的一个几何点 $ol(v)$，位于 $ol(eta) -> X$ 之上。由此得到函子： 
      $
        (U, ol(u)) |-> (U, ol(v))
      $
      它从 $ol(x)$ 的带基点平展邻域，映到 $ol(eta)$ 的带基点平展邻域。 

    于是特殊化映射可由如下极限构造出来： 
    $
      cal(F)_(ol(x)) = dirlim_((U,ol(u)) -> (X,ol(x))\ #[etale]) cal(F)(U) -> dirlim_((U,ol(v)) -> (X,ol(eta))\ #[etale]) cal(F)(U) = cal(F)_(ol(eta))
    $
    它把 $(U,ol(u))$ 对应的 $cal(F)(U)$ 送到相应 $(U,ol(v))$ 对应的 $cal(F)(U)$。 
  ]
]

#notation(name: <representable-etale-sheaf>)[
  回忆一下：对每个 $X$-概形 $Y$，都存在由 $Y$ 表示的可表示层 (representable sheaf)： 
  $
    Et_X^opp -> cSet, Z |-> Hom_X (Z, Y)
  $
  该层记为 $h_Y$。 

  例如，对集合 $G$，常值层 $ul(G)$ 由 $X times G = union.big_(g in G) X$ 表示，后者是以 $G$ 为指标的一族 $X$ 的不交并。因此可以写： 
  $
    ul(G)_X cong h_(X times G)
  $
]

#lemma(name: <descs-of-lcc-sheaves-of-sets>)[
  #set enum(numbering: "(a)")
  设 $cal(F) in cSh(X_et)$ 是集合层。以下条件等价：
  
  + $cal(F) cong h_Y$，即由有限平展覆叠 $Y in Et_X$ 表示；
  
  + $cal(F)$ 是 l.c.c；//存在平展覆盖 ${U_i -> X}_i$，使对某些有限集 $G_i$ 有 $cal(F)|_(U_i) cong h_(U_i times G_i) = ul(G_i)_(U_i) $。
  
  + 对 $X$ 的每个连通分支 $X_0$，存在有限平展覆叠空间 $U_0 -> X_0$ 与有限集 $G$，使得 $cal(F)|_(U_0) cong ul(G)_(U_0)$。
]
#proof[
  在 $X$ 的每个连通分支上分别论证，不妨设 $X$ 连通。 

  (c) $==>$(b)：同义反复。
  
  (b) $==>$(a)：//不妨设 $X$ 仿射（因为一般 $X$ 可以用开仿射集 ${V_i}$ 覆盖。若对每个 $i$ 都能找到表示 $cal(F) $ 的 $V'_i -> V_i$，则由 $cal(F)|_(V_i)|_(V_i ∩ V_j) cong cal(F)|_(V_j)|_(V_i ∩ V_j) $ 的典范性，表示概形 $V'_i, V'_j$ 可以粘合），设 $X$ 连通，再设 ${U_i -> X}$ 是有限族，其中每个 $U_i$ 都仿射连通。此时 $U = union.sq.big_(i \ "有限") U_i -> X$ 是 fpqc 覆盖。
  //
  //按我们的假设，$cal(F)|_U = tilde(G_U)$。现在考虑 $p_(1,2): U times_X U arrows.rr U$，同构 $p_2^(-1) (cal(F)|_U) cong cal(F)|_(U times_X U) cong p_1^(-1) (cal(F)|_U)$ 在 $U times_X U$ 上给出 $eta: p_2^(-1) G_U -> p_1^(-1) G_U$，它满足余圈条件。于是它下降为所求的平展覆盖 $X' -> X$。（有限性与平展性在 fpqc 下降下保持。）
  在每块 $U_i$ 上，$cal(F)|_(U_i) cong h_(G_i times U_i)$。于是对 $U_(i,j) = U_i times_X U_j$，有同构 $cal(F)|_(U_i)|_(U_(i,j)) cong cal(F)|_(U_j)|_(U_(i,j))$，从而是 $U_(i,j)$ 上有限平展覆叠之间的同构：
  $
    U_(i,j) times G_i cong U_(i,j) times G_j
  $
  满足余圈条件。 

  换言之，$union.sq.big_i (U_i times G_i)$ 是 $union.sq.big_i U_i -> X$ 上的有限平展覆叠，并带有满足余圈条件的过渡同构。由相对仿射概形的 fpqc 下降（@fpqc-descent-of-relatively-affine-schemes），它来自某个态射 $X' -> X$ 沿 $union.sq.big_i U_i -> X$ 的基变换；由 @fpqc-descent-of-properties (2)(5) 知该态射有限且平展。 

  既然有了相容的同构 $cal(F)|_(U_i) cong h_(X' times_X U_i)$，我们就得到了同构： 
  $
    cal(F) cong h_(X')
  $
  
  (a) $==>$(c)：设 $cal(F) = h_(X')$，其中 $X'$ 是有限平展覆叠。注意对任意 $U in Et_X$： 

  $
    h_(X')|_(U)(Y) = Hom_X (Y, X') = Hom_U (Y, X' times_X U)
  $
  换言之，$h_(X')|_U = h_(X' times_X U)$。于是只需找到有限平展覆叠 $Z -> X$，使 $X' times_X Z$ 是 $Z$ 的平凡覆叠。由 @fet-trivializes-fet-locally 即得。 
]

#lemma(name: <descs-of-lcc-sheaves>)[
  #set enum(numbering: "(a)")
  设 $Lambda$ 是 Noether 环。对取值于 $Lambda$-模（相应地，交换群）、且各茎都是有限 $Lambda$-模（相应地，有限交换群）的平展层 $cal(F)$，以下条件等价：
  
  + $cal(F)$ 局部常值，从而是 l.c.c；

  + $cal(F)$ 的所有特殊化态射都是同构； 
  
  // + 存在平展覆盖 ${U_i -> X}_i$，使对某些有限交换群 $G_i$ 有 $cal(F)|_(U_i) cong tilde((G_i)_(U_i)) = ul(G_i)_(U_i)$。
  
  若 $Lambda$ 作为集合有限，则这两条还等价于： 

  3. 对 $X$ 的每个连通分支 $X_0$，存在有限平展覆叠空间 $U_0 ->> X_0$ 与有限 $Lambda$-模（相应地，交换群）$G$，使得 $cal(F)|_(U_0) cong /*tilde(G_U) =*/ ul(G)_(U_0)$。
]
#proof[
  我们只处理 $Lambda$-模的情形：在交换群的情形，l.c.c. 交换群层就是对某个 $n$ 而言的 $ZZ\/n$-模 l.c.c. 层；而且容易验证，在 (a)(b)(c) 的任一条之下，都存在某个 $n$，使 $cal(F)$ 是 $n$-挠的。 

  (c) $==>$(a) 按定义即成立。 

  (a) $==>$(b)：需要证明特殊化与拉回相容： 

  #lemma[
    设 $f: X -> Y$ 是概形态射，$ol(x)$ 是 $X$ 的几何点，$ol(y) = f(ol(x))$，$ol(xi) -> tilde(X)_(ol(x))$ 是一般化 $ol(x)$ 的几何点，而 $ol(eta) = ol(xi) -> tilde(X)_(ol(x)) -> tilde(Y)_(ol(y))$ 是一般化 $ol(y)$ 的几何点。则下图交换： 
    // https://q.uiver.app/#r=typst&q=WzAsNCxbMCwwLCJjYWwoRilfKG9sKHgpKSJdLFswLDEsImNhbChGKV8ob2woeGkpKSJdLFsxLDAsIihmXigtMSkgY2FsKEYpKV8ob2woeSkpIl0sWzEsMSwiKGZeKC0xKSBjYWwoRikpXyhvbChldGEpKSJdLFswLDIsIiIsMCx7InN0eWxlIjp7InRhaWwiOnsibmFtZSI6Im1hcHMgdG8ifX19XSxbMSwzLCIiLDAseyJzdHlsZSI6eyJ0YWlsIjp7Im5hbWUiOiJtYXBzIHRvIn19fV0sWzAsMSwic3BfKG9sKHhpKSxvbCh4KSkiLDJdLFsyLDMsInNwXyhvbChldGEpLG9sKHkpKSJdXQ==
    #align(center, diagram({
      node((-1, -1), [$(f^(-1) cal(F))_(ol(x))$])
      node((-1, 0), [$(f^(-1) cal(F))_(ol(xi))$])
      node((0, -1), [$cal(F)_(ol(y))$])
      node((0, 0), [$cal(F)_(ol(eta))$])
      edge((-1, -1), (0, -1), "=")
      edge((-1, 0), (0, 0), "=")
      edge((-1, -1), (-1, 0), [$sp_(ol(xi),ol(x))$], label-side: right, "->")
      edge((0, -1), (0, 0), [$sp_(ol(eta),ol(y))$], label-side: left, "->")
    }))
  ]
  #proof[
    这个图表其实只是由限制映射构成的： 
    // https://q.uiver.app/#r=typst&q=WzAsNCxbMCwwLCJHYW1tYSh0aWxkZShYKV8ob2woeCkpLCBjYWwoRil8Xyh0aWxkZShYKV8ob2woeCkpKSkiXSxbMCwxLCJHYW1tYSh0aWxkZShYKV8ob2woeGkpKSwgY2FsKEYpfF8odGlsZGUoWClfKG9sKHhpKSkpKSJdLFsxLDAsIkdhbW1hKHRpbGRlKFkpXyhvbCh5KSksIGNhbChGKXxfKHRpbGRlKFkpXyhvbCh5KSkpKSJdLFsxLDEsIkdhbW1hKHRpbGRlKFkpXyhvbChldGEpKSwgY2FsKEYpfF8odGlsZGUoWSlfKG9sKGV0YSkpKSkiXSxbMCwxXSxbMiwzXSxbMiwwXSxbMywxXV0=
    #align(center, diagram({
      node((-1, -1), [$Gamma(tilde(X)_(ol(x)), cal(F)|_(tilde(X)_(ol(x))))$])
      node((-1, 0), [$Gamma(tilde(X)_(ol(xi)), cal(F)|_(tilde(X)_(ol(xi))))$])
      node((0, -1), [$Gamma(tilde(Y)_(ol(y)), cal(F)|_(tilde(Y)_(ol(y))))$])
      node((0, 0), [$Gamma(tilde(Y)_(ol(eta)), cal(F)|_(tilde(Y)_(ol(eta))))$])
      edge((-1, -1), (-1, 0), "->")
      edge((0, -1), (0, 0), "->")
      edge((0, -1), (-1, -1), "->")
      edge((0, 0), (-1, 0), "->")
    }))
    因而交换。 
  ]

  于是，给定 $X$ 的一对几何点 $(ol(x),ol(xi))$，其中 $ol(xi)$ 一般化 $ol(x)$；任取使 $cal(F)|_U$ 为常值层的平展邻域 $(U, ol(u)) -> (X, ol(x))$。由于 $ol(xi)$ 是 $tilde(X)_(ol(x))$ 的几何点，它典范地提升为 $U$ 的一个几何点 $ol(v)$，位于 $ol(xi)$ 之上。于是特殊化映射： 
  $
    sp_(ol(xi),ol(x)): cal(F)_(ol(x)) -> cal(F)_(ol(xi))
  $
  其实只是如下特殊化： 
  $
    sp_(ol(v),ol(u)): (cal(F)|_U)_(ol(u)) -> (cal(F)|_U)_(ol(v))
  $
  然而 $cal(F)|_U$ 是常值层，常值层中的特殊化映射总是同构。于是证毕。 

  (b) $==>$(a)：对 $X$ 的几何点 $ol(x)$，需要找到平展邻域 $(U, ol(u)) -> (X, ol(x))$，使 $cal(F)|_U cong ul(M)_U$，其中 $M$ 是有限 $Lambda$-模。取 $M = cal(F)_(ol(x))$，已知它是有限 $Lambda$-模。由于 $Lambda$ 是 Noether 环，可以选取一个展示： 
  $
    Lambda^r ->^A Lambda^m -> M -> 0
  $
  这就是 $M$ 的一个展示。把 $M$ 中对应于 $Lambda^r ->> M$ 的生成元记为 $s_1, dots.c, s_m in M = cal(F)_(ol(x))$。按茎的定义，每个 $s_i$ 都来自某个平展邻域 $(U_i, ol(u)_i) -> (X, ol(x))$ 上的截面，即属于 $cal(F)(U_i)$。取一个同时包含所有 $u_i$ 的公共平展邻域 $(U, ol(u))$，便可假定每个 $s_i in cal(F)_(ol(x))$ 都来自 $s_i in cal(F)(U)$。 

  进一步缩小平展邻域，还可假定这些 $s_i$ 满足 $M$ 的 $m$ 个生成元之间的全部 $r$ 个关系。事实上，对每个关系，$s_i$ 都在 $cal(F)_(ol(x))$ 中满足它，因而在某个更小的平展邻域中也满足它。 
  
  于是截面 $s_i in cal(F)(U)$ 定义了映射： 
  $
    ul(Lambda^r)_U ->^A ul(Lambda^m)_U ->^({s_i}) cal(F)|_U -> 0
  $
  即映射 $phi: ul(M)_U -> cal(F)|_U$。按定义，$phi_(ol(u))$ 是同构。最后，把 $U$ 换成 $ol(u)$ 附近的仿射开集，再把后者换成 $ol(u)$ 所在的连通分支，使 $U$ 是 Noether 连通概形。 
  
  令： 
  $
    E = {v in U : exists#[几何点 $ol(v) $ 位于 $v$ 上方，且使 $phi_(ol(v)): M -> (cal(F)|_U)_(ol(v)) $ 为同构]}
  $
  由 @stalks-detects-properties (0)，定义 $E$ 的性质与 $v$ 上方几何点的选取无关。此外，对 $v, w in U$，若 $w$ 一般化 $v$，则取 $v$ 上方的一个几何点 $ol(v)$，并把 $w$ 任意提升为 $tilde(U)_(ol(v))$ 的一个几何点 $ol(w)$。 

  由于 $cal(F)$ 的特殊化映射都是同构，$cal(F)|_U$ 的特殊化映射也都是同构。由特殊化的自然性，我们有交换图表： 
  // https://q.uiver.app/#r=typst&q=WzAsNCxbMCwwLCJNIl0sWzAsMSwiTSJdLFsxLDAsIihjYWwoRil8X1UpXyhvbCh2KSkiXSxbMSwxLCIoY2FsKEYpfF9VKV8ob2wodykpIl0sWzIsMywic3AiXSxbMCwxLCIiLDAseyJzdHlsZSI6eyJib2R5Ijp7Im5hbWUiOiJkb3VibGUgYmFycmVkIn19fV0sWzAsMiwicGhpXyhvbCh2KSkiXSxbMSwzLCJwaGlfKG9sKHcpKSIsMV1d
  #align(center, diagram({
    node((0, 0), [$M$])
    node((0, 1), [$M$])
    node((1, 0), [$(cal(F)|_U)_(ol(v))$])
    node((1, 1), [$(cal(F)|_U)_(ol(w))$])
    edge((1, 0), (1, 1), [$sp$], label-side: left, "->")
    edge((0, 0), (0, 1), "=")
    edge((0, 0), (1, 0), [$phi_(ol(v))$], label-side: left, "->")
    edge((0, 1), (1, 1), [$phi_(ol(w))$], label-side: right, "->")
  }))
  其中 $sp$ 是同构。因此，$phi_(ol(v))$ 是同构当且仅当 $phi_(ol(w))$ 是同构。换言之，$E$ 对一般化与特殊化都封闭。于是 $E$ 是 $U$ 的若干不可约分支的不交并。由于 $U$ 是 Noether 连通概形，它的各不可约分支在相交关系下构成连通图。因此 $E$ 要么为空，要么就是整个 $U$。由于 $u in E$，必有 $E = U$，从而 $phi: ul(M)_U -> cal(F)|_U$ 是同构。 

  (a) $==>$(c)（$Lambda$ 是有限环的情形）：可以逐个连通分支处理，故设 $X$ 连通。按 l.c.c. 层的定义，存在平展覆盖 ${U_i -> X}$，使每个 $cal(F)|_(U_i)$ 都是常值层。于是 $X$ 的全部几何点处的茎作为 $Lambda$-模彼此同构。把这个有限 $Lambda$-模记为 $G$。 
  
  考虑如下集合层： 
  $
    cal(J): Et_X^opp -> cSet, U |-> "Isom"(ul(G)_U, cal(F)|_U) = {#[$phi: ul(G)_U -> cal(F)|_U$ 的同构]}
  $

  对每个使 $cal(F)|_U cong ul(G)_U$ 成立的平展开集 $U -> X$，都有： 
  $
    cal(J)|_U: Et_U^opp -> cSet, V |-> "Isom"(ul(G)_V, ul(G)_V) = Aut_(Lambda)(G)^(pi_0 (V))
  $
  换言之，$cal(J)|_U cong ul(Aut_Lambda (G))_U$ 是常值层。于是 $cal(J)$ 是局部常值的集合层。又因 $Lambda$ 是有限环、$G$ 是有限 $Lambda$-模，$Aut_Lambda (G)$ 作为集合有限，故 $cal(J)$ 是集合的 l.c.c. 层。由 @descs-of-lcc-sheaves-of-sets，存在有限平展覆叠 $U ->> X$，使 $cal(J)|_U cong ul(Aut_Lambda (G))_U$。取对应于恒等元 $id in Aut_Lambda (G)$ 的整体截面，便得到同构 $cal(F)|_U cong ul(G)_U$。 
]

#definition(name: <defn-constructible-sheaf>)[
  $X$ 上取值于 $Lambda$-模（相应地，交换群）的平展层 $cal(F)$，若存在由有限多个局部闭子概形 $X_i subset X$ 给出的分层 $X = union.sq.big_i X_i$，使对每个 $i$ 都有 $cal(F)|_(X_i)$ 是 $Lambda$-模（相应地，交换群）的 l.c.c. 层，则称它为*可构造层*。 

  只说一个*可构造层*时，指的是交换群的可构造层。 
]

#properties(name: <constructible-sheaves-first-props>)[
  设 $Lambda$ 是 Noether 环，$cal(F)$ 表示 $X$ 上的 $Lambda$-模层。 

  + 若 $cal(F)$ 是 l.c.c./可构造的，则对任意使 $X'$ 为 Noether 概形的 $g: X' -> X$，$g^(-1) cal(F)$ 也是 l.c.c./可构造的。
    
  
  + 以下条件等价： 
    + $cal(F)$ 可构造； 
    
    + 对任意带有既约子概形结构的不可约闭子集 $Y subset X$，存在非空开集 $emptyset != V subset Y$，使 $cal(F)|_V$ 是 l.c.c； 

    + 对任意带有既约子概形结构的不可约闭子集 $Y subset X$，存在非空开集 $emptyset != V subset Y$，使 $cal(F)|_V$ 可构造。 
  
  + 若 $f: U -> X$ 平展且拟紧，则：
    - $f_! ul(Lambda)$ 是 $Lambda$-模的可构造层。 
    - $f_! ul(ZZ\/n)$ 是交换群的可构造层。 

  + 对 $Lambda$-模层 $cal(F)$，以下条件等价：
    + $cal(F)$ 可构造；
    + $cal(F)$ 是 /*挠的且 */Noether 的（即交换群子层的任意上升链 $0 = cal(F)_0 subset cal(F)_1 subset dots.c subset cal(F)$ 最终稳定）。
    + 存在平展拟紧映射 $f: U -> X$、$f': U' -> X$，以及右正合列：
      $
        f'_! ul(Lambda)_(U') -> f_! ul(Lambda)_U -> cal(F) -> 0
      $

    对交换群层 $cal(F)$，以下条件等价： 
    + $cal(F)$ 可构造；
    + $cal(F)$ 是挠的且 Noether 的； 
    + 存在平展拟紧映射 $f: U -> X$、$f': U' -> X$，以及右正合列：
      $
        f'_! ul(ZZ\/n)_(U') -> f_! ul(ZZ\/n)_U -> cal(F) -> 0
      $
      其中 $n >= 1$。 

  
  + $Lambda$-模（相应地，交换群）可构造层的任意子层或商层都可构造。$Lambda$-模（相应地，交换群）可构造层的任意扩张都可构造。$X$ 上 $Lambda$-模（相应地，交换群）的可构造层构成 Abel 范畴。
  
  + 
    - 每个 $Lambda$-模层 $cal(F)$ 都是其可构造子层（按包含排序）的正向极限。 
    - 每个挠交换群层 $cal(F)$ 都是其可构造子层（按包含排序）的正向极限。
]
#proof[
  容易看出，这里关于交换群的所有陈述都可由关于 $Lambda$-模的陈述推出：适当取 $Lambda = ZZ\/n$ 即可，其中 $n$ 取得合适。(6) 稍显不平凡：对每个挠交换群层 $cal(F)$，可以写成 $cal(F) = dirlim_n cal(F)[n]$，再把每个 $cal(F)[n]$ 写成其 $ZZ\/n$-模可构造子层的正向极限。从 (5b) 开始的论证也稍显不平凡，因为需要说明：若 $cal(F)$ 是挠的且 Noether，则由 $cal(F) = dirlim_n cal(F)[n!]$ 可知存在 $n$ 使 $cal(F) = cal(F)[n!]$。于是 $cal(F)$ 是对某个 $n$ 而言的 $ZZ\/n$-模层。 

  (1)
  #proof[
    取由局部闭子概形给出的分层 $X = union.sq.big_i X_i$，使 $cal(F)|_(X_i)$ 是 l.c.c。则 $X' = union.sq.big X'_i$ 是 $X'$ 的由局部闭子概形给出的分层，其中 $X'_i = X_i times_X X'$。于是只需证明每个 $cal(F)|_(X'_i)$ 都是 l.c.c，即对 l.c.c. 层证明本命题。
    
    设对某个平展覆盖 $f: U -> X$，有 $f^(-1) cal(F) cong ul(G)_U$，其中 $G$ 是有限 $Lambda$-模。作基变换：
    // https://q.uiver.app/#r=typst&q=WzAsNCxbMSwxLCJYIl0sWzEsMCwiVSJdLFswLDEsIlgnIl0sWzAsMCwiVSciXSxbMiwwLCJnIiwyXSxbMSwwLCJmIl0sWzMsMSwiZyciXSxbMywyLCJmJyIsMl1d
    #align(center, diagram(
      {
        node((0, 0), [$X$])
        node((0, -1), [$U$])
        node((-1, 0), [$X'$])
        node((-1, -1), [$U'$])
        edge((-1, 0), (0, 0), [$g$], label-side: right, "->")
        edge((0, -1), (0, 0), [$f$], label-side: left, "->")
        edge((-1, -1), (0, -1), [$g'$], label-side: left, "->")
        edge((-1, -1), (-1, 0), [$f'$], label-side: right, "->")
      },
      spacing: 1.5em,
    ))
    于是 $f': U' -> X'$ 是 $X'$ 的平展覆盖。由此：
    $
      f'^(-1)g^(-1) cal(F) cong g'^(-1)f^(-1) cal(F) cong g'^(-1) ul(G)_U cong ul(G)_(U')
    $
    因此 $g^(-1) cal(F)$ 是 l.c.c。
  ]

  (2)
  #proof[
    (a) $==>$(b)：由 (1)，$cal(F)|_Z$ 可构造。在局部闭分层 $Z = union.sq.big_i Z_i$ 中，取包含 $Z$ 的泛点的那一层，记作 $Z_1$。则 $Z_1$ 是 $Z$ 的非空开集，且 $cal(F)|_(Z_1)$ 是 l.c.c。
    
    (b) $==>$(a)：由 Noether 归纳法，存在极大的开子集 $U subset X$，使 $cal(F)|_U$ 可构造。若 $U != X$，则取非空闭子集 $X - U$ 的一个不可约分支 $Z$。按假设，存在开集 $V subset Z$，使 $cal(F)|_V$ 是 l.c.c。$V$ 是 $X$ 的局部闭子集。取有限分层 $U = union.sq.big_i U_i$，使每个 $cal(F)|_(U_i)$ 都是 l.c.c。此时 $U union V = (Z - V)^c$ 是 $X$ 的开子集，带有有限局部闭分层 $(union.sq.big_i U_i) union.sq V$，且 $cal(F)$ 限制到每个分层上都是 l.c.c。于是 $cal(F)|_(U union V)$ 可构造，这与 $U$ 的极大性矛盾。故 $U = X$，$cal(F)$ 可构造。 

    (b) $==>$(c)：同义反复。 
    
    (c) $==>$(b)：对任意不可约闭集 $Y subset X$，按假设存在稠密开集 $V subset Y$，使 $cal(F)|_V$ 可构造。再由 (a) $==>$(b)，存在稠密开集 $W subset V$，使 $cal(F)|_W$ 是 l.c.c。此时 $W subset Y$ 是 $Y$ 中的稠密开集，证毕。 
  ]

  (3)
  #proof[
    由 (2) 以及 $f_!$ 与基变换交换（@etale-lower-shriek-first-props (4)），不妨设 $X$ 是整概形，泛点为 $eta$//，且 $U times_X eta -> Spec(k(eta)) $ 是有限平展的。（域上的平展态射总是有限平展。）于是由极限论证，存在满足 $eta in V subset X$ 的开集，使 $f^(-1) (V) -> V$ 有限平展。此时容易验证：
    // $
    //   (f_! underline(ZZ\/n))|_V = (f|_(f^(-1)(U)))_! underline(ZZ\/n)
    // $
    // 是 l.c.c。
    而我们需要证明 $f_! ul(Lambda)$ 限制到 $X$ 的某个非空开集上是 l.c.c。
    
    由于 $f$ 平展拟紧，它是有限展示的。而态射 $U_eta -> eta = Spec(k(eta))$ 是域上的有限展示平展态射，故按 @struct-of-spec-k-et 中讨论的结构，它是有限平展的。考虑：
    $
      Spec(k(eta)) = invlim_(eta in V subset X \ V #[仿射开集]) V
    $
    这是具有仿射过渡态射的概形的逆向极限。由态射性质在极限下的传播（@passage-to-limit-of-properties），存在满足 $eta in V subset X$ 的仿射开集，使 $f|_(f^(-1)(V)): f^(-1)(V) -> V$ 有限平展。此时：
    $
      (f_! ul(Lambda))|_V cong (f|_(f^(-1)(V)))_! (ul(Lambda)|_(f^(-1)(V))) = (f|_(f^(-1)(V)))_! ul(Lambda)
    $
    这一步用到 @etale-lower-shriek-first-props (4)。因此只需证明如下引理：
    #lemma[
      若 $X$ 是连通 Noether 概形，且 $f: U -> X$ 是有限平展覆叠，则 $f_! ul(Lambda)$ 是 $Lambda$-模的 l.c.c. 层。
    ]
    #proof[
      由 @fet-trivializes-fet-locally，可以取连通的 $Z in FEt_X$，使有限平展覆叠 $f_Z: U times_X Z -> Z$ 成为平凡覆叠。此时：
      $
        (f_! ul(Lambda))|_Z cong f_(Z,!) (ul(Lambda)|_(U times_X Z)) cong f_(Z,!) ul(Lambda)
      $
      这里用到 @etale-lower-shriek-first-props (4)。另一方面，$f_Z$ 是平凡的平展覆叠空间，设其次数为 $d$，于是 $f_(Z,!) ul(Lambda) cong ul((Lambda)^(oplus d))$ 是常值层。由 @descs-of-lcc-sheaves (c) $==>$(a)，$f_! ul(Lambda)$ 是 l.c.c。
    ]
  ]

  (4)
  #proof[
    (a)$==>$(b)：/*先证 $cal(F)$ 是挠层。取由局部闭子概形给出的有限分层 $X = union.sq.big_i X_i$，使每个 $cal(F)|_(X_i)$ 都是 l.c.c。按定义，l.c.c. 层是挠层，故可取某个 $n$，使每个 $cal(F)|_(X_i)$ 都是 $n$-挠的。任取点 $x in X$ 以及 $x$ 上方的一个几何点 $ol(x)$，并设 $x in X_i$。由于 $X_i -> X$ 作为浸入保持剩余域，$ol(x)$ 唯一地提升为 $X_i$ 的一个几何点 $ol(x)$。此时 $(cal(F)|_(X_i))_(ol(x)) = cal(F)_(ol(x))$，而 $times n$ 在 $(cal(F)|_(X_i))_(ol(x))$ 上为零。换言之，每个 $cal(F)_(ol(x))$ 都是 $n$-挠的。于是 $times n: cal(F) -> cal(F)$ 在所有茎上为零，从而是零态射。*/
    为证明 $cal(F)$ 是 Noether 的，任取上升链 $0 = cal(F)_0 subset cal(F)_1 subset dots.c subset cal(F)$，并令：
    $
      cal(S) = {emptyset != Y subset X "闭": 0 = cal(F)_0|_Y subset cal(F)_1|_Y subset dots.c subset cal(F)|_Y "不平稳"}
    $
    我们要证 $cal(S) = emptyset$。否则，由于 $X$ 是 Noether 概形，存在极小的 $Y in cal(S)$。把包含链 $0 = cal(F)_0 subset cal(F)_1 subset dots.c subset cal(F)$ 沿闭浸入 $Y -> X$ 拉回（其中 $Y$ 赋予诱导的既约子概形结构），并利用 (1) 与逆像的正合性，便可假定：
    
    - $X$ 是既约 Noether 概形，$0 = cal(F)_0 subset cal(F)_1 subset dots.c subset cal(F)$ 在 $X$ 上不稳定，但拉回到 $X$ 的任意真闭子概形上都稳定。
    
    假设 $X$ 不是不可约概形。由于 $X$ 是 Noether 概形，它只有有限多个不可约分支 $Z_1, dots.c, Z_m subset X$，这些都是 $X$ 的真闭子概形（赋予诱导的既约子概形结构）。于是每个：
    $
      0 = cal(F)_0|_(Z_i) subset cal(F)_1|_(Z_i) subset dots.c subset cal(F)|_(Z_i)
    $
    都在某个阶段 $N_i$ 之后稳定。取 $N = max(N_1, dots.c, N_m)$。现在对一切 $n > N$，考虑含入态射 $cal(F)_N arrow.hook cal(F)_n$。按假设，它沿 $union.sq.big_(i=1)^m Z_i -> X$ 拉回后是同构。于是由 @surjective-pullback-conservative，$cal(F)_N -> cal(F)_n$ 是同构。
    
    于是不妨设 $X$ 不可约，从而是整概形。由 (2)，存在非空开集 $V subset X$，使 $cal(F)|_V$ 是 l.c.c；于是存在平展覆盖 $U -> V$，使 $cal(F)|_U cong ul(G)_U$，其中 $G$ 是有限 $Lambda$-模。把包含链拉回到 $U$：
    $
      0 = cal(F)_0|_U subset cal(F)_1|_U subset dots.c subset ul(G)_U
    $
    我们要证明这条链最终稳定。
    
    #lemma[
      设 $X$ 是 Noether 概形，$G$ 是有限 $Lambda$-模。则 $Lambda$-模子层的每条包含链：
      $
        0 = cal(G)_0 subset cal(G)_1 subset dots.c subset ul(G)_X
      $
      都必最终稳定。
    ]
    #proof[
      重复性质 (4) 的 (a) $==>$(b) 证明开头所用的 Noether 归纳论证，不妨设 $X$ 是整概形，且本引理对 $X$ 的一切真子概形成立。设 $eta in X$ 是泛点，并令：
      $
        H = union.big_(m>=0) (cal(G)_m)_(ol(eta)) <= G
      $
      $H <= G$ 是有限 $Lambda$-模的子模。由于 $Lambda$ 是 Noether 环，$H$ 是有限 $Lambda$-模，从而是 Noether 的。于是存在有限阶段 $N$，使 $(cal(G)_N)_(ol(eta)) = H$。考虑：
      $
        (cal(G)_m)_(ol(eta)) = dircolim_((U,ol(u)) -> (X,ol(eta)) #[etale]) cal(G)_m (U) = dircolim_((U,ol(u)) -> (X,ol(eta)) #[etale] \ U #[connected]) cal(G)_m (U)
      $
      其中连通平展邻域是共尾的，因为 $X$ 是 Noether 概形。然而在 $X$ 的连通平展开集上，常值层 $ul(G)_X$ 取值于 $G$，且限制映射都是恒等映射。于是每个 $cal(G)_m$ 作为 $ul(G)_X$ 的子层，在连通平展开集之间的限制映射都是单射。因此，对 $m >= N$，同构：
      $
        dircolim_((U,ol(u)) -> (X,ol(eta)) #[etale] \ U #[connected]) cal(G)_m (U) -> H
      $
      其左端是过渡态射为单射的滤余极限。于是每个 $cal(G)_m (U) -> dircolim_((U,ol(u)) -> (X,ol(eta)) #[etale] \ U #[connected]) cal(G)_m (U) -> H$ 都是单射。
      
      - 取 $m = N$。由于 $H$ 是有限 $Lambda$-模，存在固定的连通平展开集 $U$，使 $cal(G)_N (U) = H$（取 $(cal(G)_N)_(ol(eta)) = H$ 的一组有限生成元，再对其代表截面取公共平展邻域即可）。
      
      - 对每个 $m >= N$ 以及连通平展开集的每个加细 $V -> U$，都有单射的复合：
        $
          H = cal(G)_N (U) arrow.hook cal(G)_m (U) arrow.hook cal(G)_m (V) arrow.hook (cal(G)_m)_(ol(eta)) = H
        $
        其复合是双射。于是这条链的每一步都是双射，特别地 $cal(G)_N (U) -> cal(G)_m (V)$ 是双射。取 $m = N$，则 $cal(G)_N (U) -> cal(G)_N (V)$ 也是双射。因此对所有这样的 $V$，$cal(G)_N (V) -> cal(G)_m (V)$ 都是双射。
      
      于是存在非空平展开集 $phi: U -> X$，使对一切 $m >= N$，$cal(G)_N|_U -> cal(G)_m|_U$ 都是同构。令 $Z = X - phi(U)$，这是 $X$ 的闭子概形，赋予诱导的既约子概形结构。按归纳假设，必要时把 $N$ 放大，则对一切 $m >= N$，$cal(G)_N|_U -> cal(G)_m|_U$ 与 $cal(G)_N|_Z -> cal(G)_m|_Z$ 都是同构。对 $U union.sq Z -> X$ 应用 @surjective-pullback-conservative，便知包含链在阶段 $N$ 稳定。
    ]
    由引理，包含链 $0 = cal(F)_0|_U subset cal(F)_1|_U subset dots.c subset ul(G)_U$ 在某个阶段 $N$ 稳定。必要时把 $N$ 放大，由归纳假设，对 $Z = X - V$，链 $0 = cal(F)_0|_Z subset cal(F)_1|_Z subset dots.c subset cal(F)|_Z$ 在阶段 $N$ 稳定。现在对 $U union.sq Z -> X$ 应用 @surjective-pullback-conservative，便知 $0 = cal(F)_0 subset cal(F)_1 subset dots.c subset cal(F)$ 在阶段 $N$ 稳定。
    
    (b)$==>$(c)：假定 $cal(F)$ 是 Noether 的。/*由于 $cal(F) = union.big_(n>=1) cal(F)[n!]$ 是自身的 $n!$-挠部分之并，存在 $n$ 使 $n cal(F) = 0$。*/现在考虑典范映射：
    $
      gamma: oplus.big_(f_alpha: U_alpha -> X "平展" \ U_alpha "仿射" \ f_alpha (U_alpha) subset "某个仿射开集" subset X) oplus.big_(s_alpha in cal(F)(U_alpha)) f_(alpha,!) underline(Lambda) -> cal(F)
    $
    其中对应于 $f_alpha, s_alpha$ 的态射 $f_(alpha,!) underline(Lambda) -> cal(F)$ 由伴随性从 $underline(Lambda) -> f_alpha^(-1) cal(F)$ 得到，对应关系为 $1 |-> s_alpha$。展开定义可知，$s_alpha$ 落在该态射的像中。于是按构造，$gamma$ 是满射。
    
    #remark[
      第一个直和 $oplus.big_(f_alpha: U_alpha -> X "平展" \ U_alpha "仿射" \ f_alpha (U_alpha) subset "某个仿射开集" subset X)$ 的指标范围如此古怪，是为了避开集合论问题，做法与 @set-categorical-subtleties 中相同。
    ]
    
    由于 $cal(F)$ 是 Noether 的，$gamma$ 左端那个遍历所有 $f_alpha, s_alpha$ 的直和可以换成有限直和而仍保持满射。于是得到满射：
    $
      gamma_0: oplus.big_(i=1)^N f_(i,!) ul(Lambda) -> cal(F)
    $
    其中 $f_i: U_i -> X$ 平展拟紧。取：
    $
      f: U = union.sq.big_(i=1)^N U_i -> X
    $
    它平展拟紧。于是得到满射 $gamma_0: f_! ul(Lambda) ->> cal(F)$，从一个可构造层到一个 Noether 层。
    
    由 (a) $==>$(b)，$f_! ul(Lambda)$ 是 Noether 的，故 $ker(gamma_0)$ 也是 Noether 的。于是可以重做同样的构造，得到平展拟紧的 $f': U' -> X$，以及右正合列：
    $
      f'_! underline(Lambda) -> f_! underline(Lambda) -> cal(F) -> 0
    $
    
    (c) $==>$(a)：
    
    #lemma[
      Noether 概形 $X$ 上 $Lambda$-模可构造层之间态射的余核可构造。
    ]
    #proof[
      考虑 $X$ 上的层的右正合列：
      $
        cal(F) -> cal(G) -> cal(H) -> 0
      $
      其中 $cal(F), cal(G)$ 可构造。由 (2)，只需证明：对每个不可约闭子概形 $Z subset X$，$cal(H)|_Z$ 拉回到 $Z$ 的某个非空开集上是 l.c.c。
      
      由 (1)，不妨设 $X$ 是整概形；只需证明存在 $X$ 的非空开集，使 $cal(H)|_U$ 是 l.c.c。
      
      由于 $cal(F), cal(G)$ 都可构造，存在非空开集 $U subset X$，使 $cal(F)|_U, cal(G)|_U$ 都是 l.c.c。由 @descs-of-lcc-sheaves (c)，存在公共平展覆盖 $V -> U$，使 $cal(F)|_V cong ul(F)_V, cal(G)|_V cong ul(G)_V$，其中 $F, G$ 是有限 $Lambda$-模。限制到 $V$，得到正合列：
      $
        ul(F)_V -> ul(G)_V -> cal(H)|_V -> 0
      $
      这给出态射 $phi: F -> G$，并把 $cal(H)|_V cong ul(coker(phi))_V$ 等同于与有限 $Lambda$-模相伴的常值层。于是由 @descs-of-lcc-sheaves (c)，$cal(H)|_U$ 是 l.c.c，证毕。
    ]
    
    取右正合列：
    $
      f'_! underline(Lambda) -> f_! underline(Lambda) -> cal(F) -> 0
    $
    即 $cal(F) = coker(f'_! underline(Lambda) -> f_! underline(Lambda))$。由 (3) 与上面的引理，证明完成。
  ]

  (5)
  #proof[
    由 (4)，可构造层与 Noether 层是一回事。
  ]

  (6)
  #proof[
    对拟紧的 $U -> X$，每个 $s in cal(F)(U)$ 都定义态射 $gamma_s: f_! underline(Lambda) -> cal(F)$，其像可构造且包含截面 $s$。
    
    考虑单射：
    $
      dirlim_(cal(G) subset cal(F) #[constructible]) cal(G) -> cal(F)
    $
    而我们需要证明它是满射。为此只需证明它在茎上满射。对 $X$ 的每个几何点 $ol(x)$，$(-)_(ol(x))$ 作为左伴随保持余极限。因此只需证明：
    $
      dirlim_(cal(G) subset cal(F) #[constructible]) cal(G)_(ol(x)) -> cal(F)_(ol(x))
    $
    是满射，即
    $
      dirlim_(cal(G) subset cal(F) #[constructible]) dircolim_((U,ol(u)) -> (X,ol(x)) #[etale]) cal(G)(U) -> dircolim_((U,ol(u)) -> (X,ol(x)) #[etale]) cal(F)(U)
    $
    是满射。由于 $X$ 是 Noether 概形，$(U, ol(u))$ 的 Noether 平展邻域是共尾的。因此只需证明：
    $
      dirlim_(cal(G) subset cal(F) #[constructible]) dircolim_((U,ol(u)) -> (X,ol(x)) #[etale] \ U #[noetherian]) cal(G)(U) -> dircolim_((U,ol(u)) -> (X,ol(x)) #[etale] \ U #[noetherian]) cal(F)(U)
    $
    是满射。然而对 Noether 的 $U$，每个平展 $U -> X$ 当然都拟紧，故按上面的论证，$cal(F)(U)$ 中的每个截面都属于某个可构造子层 $cal(G) subset cal(F)$ 的 $cal(G)(U)$。于是证毕。
  ]
]

#proposition(name: <supp-of-constructible-sheaf>)[
  设 $Lambda$ 是 Noether 环。对 $X$ 上取值于 $Lambda$-模或交换群的可构造层 $cal(F)$， 
  $
    supp(cal(F)) = {x in X : cal(F)_(ol(x)) != 0 #[其中 $ol(x) $ 是 $x$ 上方的某个几何点]}
  $
  是 $X$ 的可构造子集。 
]
#proof[
  只需证明：对任意带有诱导既约子概形结构的不可约闭子集 $Z subset X$，设其泛点为 $eta in Z$，若 $eta in supp(cal(F))$，则存在非空开集 $V subset Z$，使 $V subset supp(cal(F))$。由于可构造性在拉回下保持，且 $supp(cal(F)|_Z) = supp(cal(F)) ∩ Z$，可以把 $cal(F)$ 换成 $cal(F)|_Z$、把 $X$ 换成 $Z$，从而不妨设 $X$ 是整概形且 $Z = X$。 

  由于 $cal(F)$ 在整概形 $X$ 上可构造，存在满足 $eta in U subset X$ 的非空开集，使 $cal(F)|_U$ 是 l.c.c。于是存在平展覆盖 $pi: V ->> U$，使 $pi^(-1) (cal(F)|_U) cong ul(G)_V$，其中 $G$ 是有限 $Lambda$-模。因此，对位于 $u in U$ 上方的所有几何点 $ol(u)$，以及 $ol(v) in pi^(-1) (ol(u))$，有： 
  $
    cal(F)_(ol(u)) = (pi^(-1) (cal(F)|_U))_(ol(v)) cong (ul(G)_V)_(ol(v)) = G
  $
  由于 $G cong cal(F)_(ol(eta)) != 0$，有 $G != 0$，从而对位于 $u in U$ 上方的所有 $ol(u)$ 都有 $cal(F)_(ol(u)) cong G != 0$。于是 $U subset supp(cal(F))$。 
]

#theorem(name: <finite-morphisms-and-constructible-sheaves>)[
  设 $Lambda$ 是 Noether 环。 

  + 设 $f: X -> Y$ 是 Noether 概形之间的有限态射。则取值于 $Lambda$-模或交换群的平展层 $cal(F)$ 可构造，当且仅当 $f_* cal(F)$ 可构造。
  
  + 
    - 若 $cal(F)$ 是 $Lambda$-模的可构造层，则存在有限态射 $g: Z -> X$ 与单射 $cal(F) arrow.r.hook g_* ul(M)$，其中 $M$ 是有限 $Lambda$-模。 

    - 若 $cal(F)$ 是交换群的可构造层且 $n cal(F) = 0$，则存在有限态射 $g: Z -> X$ 与单射 $cal(F) arrow.r.hook g_* ul(ZZ\/n)$。 
]
#proof[
  (1) 的（$<==$）方向成立：对有限的 $f$，伴随映射 $f^(-1)f_* cal(F) -> cal(F)$ 是满射，用 @stalks-of-finite-pushforward 检查茎即可。
  
  ($==>$) 只需对 $Lambda$-模验证：若 $cal(F)$ 是交换群的可构造层，则它是对某个 $n$ 而言的 $ZZ\/n$-模可构造层。 
  
  我们要用 @constructible-sheaves-first-props (2)。设 $Y' subset Y$ 是 $Y$ 的不可约闭子概形，赋予诱导的既约子概形结构；要证明 $(f_* cal(F))|_(Y')$ 在 $Y'$ 的某个开子集上是 l.c.c。由 (Finite)（@pbc-finite）——即有限态射沿基变换成立——有 $(f_* cal(F))|_(Y') = f'_* (cal(F)|_(X'))$，其中我们作拉回方块： 
  // https://q.uiver.app/#r=typst&q=WzAsNCxbMCwxLCJYIl0sWzEsMSwiWSJdLFsxLDAsIlknIl0sWzAsMCwiWCciXSxbMCwxLCJmIiwyXSxbMywyLCJmJyJdLFsyLDFdLFszLDBdXQ==
  #align(center, diagram({
    node((-1, 0), [$X$])
    node((0, 0), [$Y$])
    node((0, -1), [$Y'$])
    node((-1, -1), [$X'$])
    edge((-1, 0), (0, 0), [$f$], label-side: right, "->")
    edge((-1, -1), (0, -1), [$f'$], label-side: left, "->")
    edge((0, -1), (0, 0), "->")
    edge((-1, -1), (-1, 0), "->")
  }))
  由于 $cal(F)|_(X')$ 可构造且 $f'$ 有限，不妨设 $Y$ 是整概形，泛点为 $eta$，并验证 $f_* cal(F)$ 在 $Y$ 的某个开子集上是 l.c.c。 
  
  由一般平坦性（见 @generic-flatness），并按上面同样的方式使用 (Finite)（@pbc-finite），在过渡到 $Y$ 的某个开子集后，不妨设 $f$ 是有限平坦的。由拓扑不变性，过渡到约化后可假设 $X$ 既约。现在设 $eta in Y$ 是泛点，考虑泛纤维 $X_eta -> eta = Spec(K(Y))$，它有限，且 $X_eta$ 既约。这迫使 $X_eta = Spec(A)$，其中 $A = product_(i=1)^m L_i$，且每个 $L_i\/K(Y)$ 都是有限域扩张。对每个 $i$，$L_i\/K(Y)$ 分解为 $L_i\/L'_i\/K(Y)$，其中 $L_i\/L'_i$ 纯不可分，$L'_i\/K(Y)$ 平展。于是取 $A' = product_(i=1)^m L'_i$，$f_eta: X_eta -> eta$ 分解为： 
  $
    underbrace(X_eta, Spec(A)) ->^(g_eta) underbrace(X'_eta, Spec(A')) ->^(h_eta) underbrace(eta, Spec(K(Y)))
  $
  其中 $g_eta$ 有限、满射、根性，$h_eta$ 有限平展。把 @passage-to-limit-of-morphisms 与 @passage-to-limit-of-properties 用于 $eta = invlim_(emptyset != V subset Y #[affine]) V$（根性也沿极限下降，因为根性等价于对角线满射，而满射性沿极限下降），可知存在非空开集 $V subset Y$，使 $f_V: f^(-1)(V) -> V$ 分解为： 
  $
    f_V: f^(-1)(V) ->^(g_V) V' ->^(h_V) V
  $
  其中 $g_V$ 有限、满射、根性，$h_V$ 有限平展。 

  再沿 $V -> Y$ 作一次基变换并再次使用 (Finite)（@pbc-finite），可以进一步假设 $f: X -> Y$ 分解为 $f: X ->^g X' ->^h Y$，其中 $g$ 有限、满射、根性，$h$ 是有限平展覆叠。此时 $f_* cal(F) = h_* g_* cal(F)$。 

  - 由于 $g$ 有限、满射、根性，它是泛同胚。由拓扑不变性，$cal(G) = g_* cal(F)$ 可构造（比如说，按 @constructible-sheaves-first-props (4) 所述，它是 Noether 的）。 

  - 由于 $h$ 有限平展，由 @fet-lower-star-is-lower-shriek 有 $h_* = h_!$。由 @constructible-sheaves-first-props (4)，可以找到平展拟紧的 $phi: V -> X'$ 与满射 $phi_! ul(Lambda) ->> cal(G)$。由于 $h_! = h_*$ 正合，得到满射 $(h compose phi)_! ul(Lambda) ->> h_* cal(G)$。此时 $h compose phi$ 平展拟紧，故由 @constructible-sheaves-first-props (3)，$(h compose phi)_! ul(Lambda)$ 可构造。于是由 @constructible-sheaves-first-props (5)，$h_* cal(G)$ 作为 $(h compose phi)_! ul(Lambda)$ 的商层可构造。 

  于是 $f_* cal(F)$ 可构造，从而限制到 $V$ 的某个非空开集上是 l.c.c。证毕。 
  
  (2) 交换群的情形可由 $Lambda$-模的情形推出：先对有限 $ZZ\/n$-模 $M$ 构造单射 $cal(F) arrow.r.hook g_* ul(M)$，再注意每个有限 $ZZ\/n$-模 $M$ 都能嵌入某个 $(ZZ\/n)^(oplus m)$ 中。我们先断言： 

  - 若对 $X$ 的每个几何点 $ol(x)$，都能找到有限 $Lambda$-模 $G$、有限态射 $g: Z -> X$ 以及态射 $phi: cal(F) -> g_* ul(G)_Z$，使 $phi$ 在 $x$ 处诱导茎上的单射 $cal(F)_(ol(x)) -> (g_* ul(G)_Z)_(ol(x))$，则已证完。 

  #proof_[断言的证明][
    固定一个由局部闭子概形给出的有限分层 $X = union.sq.big_i X_i$，使每个 $cal(F)|_(X_i)$ 都是 l.c.c；每个 $X_i$ 只有有限多个不可约分支，因而只有有限多个泛点 $eta_(i,j)$。现在对每个 $eta_(i,j)$，取： 
    $
      phi_(i,j): cal(F) -> g_(i,j,*) ul(G_(i,j))_Z
    $
    其中 $G_(i,j)$ 是有限交换群，且 $phi_(i,j)$ 在 $ol(eta_(i,j))$ 处的茎上是单射。现在作直和： 
    $
      phi = oplus.big_(i,j) phi_(i,j): cal(F) -> oplus.big_(i,j) g_(i,j,*) ul(G_(i,j))_Z
    $
    于是对每个 $i,j$ 都有 $ker(phi)_(ol(eta_(i,j))) = 0$。此外 $ker(phi) subset cal(F)$，从而 $ker(phi)|_(X_i) subset cal(F)|_(X_i)$。 

    #lemma[
      设 $X$ 是 Noether 概形，$cal(F) in cAb(X_et, Lambda)$ 是 $Lambda$-模的 l.c.c. 层，$cal(G) subset cal(F)$ 是子层，且对 $X$ 的每个不可约分支的泛点 $eta in X$ 都有 $cal(G)_(ol(eta)) = 0$。则 $cal(G) = 0$。 
    ]
    #proof[
      对 $X$ 的任意几何点 $ol(x)$，取 $X$ 中某个包含 $x$ 的不可约分支的泛点 $eta$，再取一个位于 $eta$ 上方、一般化 $ol(x)$ 的几何点 $ol(eta)$。则有交换图表： 
      // https://q.uiver.app/#r=typst&q=WzAsNCxbMCwwLCJjYWwoRilfKG9sKHgpKSJdLFsxLDAsImNhbChGKV8ob2woZXRhKSkiXSxbMSwxLCJjYWwoRylfKG9sKGV0YSkpIl0sWzAsMSwiY2FsKEcpXyhvbCh4KSkiXSxbMCwxLCJzcCJdLFszLDAsIiIsMix7InN0eWxlIjp7InRhaWwiOnsibmFtZSI6Imhvb2siLCJzaWRlIjoiYm90dG9tIn19fV0sWzIsMSwiIiwyLHsic3R5bGUiOnsidGFpbCI6eyJuYW1lIjoiaG9vayIsInNpZGUiOiJib3R0b20ifX19XSxbMywyLCJzcCIsMl1d
      #align(center, diagram({
        node((0, 0), [$cal(F)_(ol(x))$])
        node((1, 0), [$cal(F)_(ol(eta))$])
        node((1, 1), [$cal(G)_(ol(eta))$])
        node((0, 1), [$cal(G)_(ol(x))$])
        edge((0, 0), (1, 0), [$sp$], label-side: left, "->")
        edge((0, 1), (0, 0), "hook'->")
        edge((1, 1), (1, 0), "hook'->")
        edge((0, 1), (1, 1), [$sp$], label-side: right, "->")
      }))
      由于 $cal(F)$ 是 l.c.c，$sp: cal(F)_(ol(x)) -> cal(F)_(ol(eta))$ 是同构。于是 $cal(G)_(ol(x)) -> cal(G)_(ol(eta))$ 是单射。但 $cal(G)_(ol(eta)) = 0$，故 $cal(G)_(ol(x)) = 0$，这就完成了 $cal(G) = 0$ 的证明。 
      /*
      设 $X$ 的不可约分支为 $X_1, dots.c, X_m$，赋予既约子结构。每个 $cal(F)|_(X_i)$ 都是 l.c.c，且在泛点处的茎消没。若能证明每个 $cal(G)|_(X_i) = 0$，则由对 $union.sq.big_(i=1)^m X_i -> X$ 应用 @surjective-pullback-conservative 即可得出结论。 

      于是把 $X$ 换成 $X_i$、把 $cal(F)$ 换成 $cal(F)|_(X_i)$、把 $cal(G)$ 换成 $cal(G)|_(X_i)$，便可假定 $X$ 是整概形，泛点为 $eta$。现在取平展覆盖 $U ->> X$，使 $cal(F)|_U cong ul(G)_U$。由于 $X$ 是 Noether 概形，可以加细使 $U$ 也是 Noether 的。注意 $U$ 的所有泛点 $u$ 都映到 $eta in X$，故 $(cal(G)|_U)_(ol(u)) = cal(G)|_(ol(eta))$。应用 @surjective-pullback-conservative，并把 $X$ 换成 $U$ 的各不可约分支，便可假定： 

      - $X$ 是整 Noether 概形，且 $cal(F) = ul(G)_X$，其中 $G$ 是有限 $Lambda$-模。 

      对任意 $U in Et_X$，由于 $X$ 是 Noether 概形，$U$ 是局部 Noether 的，从而是其各连通分支（都是 Noether 的）的不交并。为证 $cal(G) = 0$，只需证明对连通的 $U in Et_X$，每个 $s in cal(G)(U)$ 都消没。然而 $cal(G)(U) subset ul(G)_X (U) = G$；而对位于 $eta in X$ 上方的点 $u in U$，取茎： 
      $
        (-)_(ol(u)): G = cal(F)(U) -> cal(F)_(ol(eta)) = G
      $
      这只是恒等映射。于是由 $s_(ol(u)) in cal(G)_(ol(eta)) = 0$ 得 $s = 0$。*/
    ]
    由引理，对每个 $i$ 都有 $ker(phi)|_(X_i) = 0$。对 $union.sq.big_i X_i -> X$ 应用 @surjective-pullback-conservative，可知 $ker(phi) = 0$，即 $phi$ 是单射。/*最后，统一取定 $n$，把每个有限群 $G_(i,j)$ 嵌入有限直和 $(ZZ\/n)^(oplus m_(i,j))$，把 $G_(i,j)$ 换成 $ZZ\/n$，就找到了有限多个有限态射 $g_k: Z_k -> X$ 与单射 $cal(F) arrow.r.hook oplus.big_k g_(k,*) ul(ZZ\/n)$。最后作不交并 $g: Z := union.sq.big_k Z_k -> X$，便得到单射 $cal(F) -> g_* ul(ZZ\/n)$。*/最后，取 $M = oplus.big_(i,j) G_(i,j)$，于是找到有限 $Lambda$-模 $M$ 与有限多个有限态射 $g_k: Z_k -> X$，以及单射： 
    $
      cal(F) arrow.r.hook oplus.big_k g_(k,*) ul(M)
    $
    最后，作不交并 $g: Z := union.sq.big_k Z_k -> X$，便得到单射 $cal(F) -> g_* ul(M)$。 
  ]

  对 $X$ 的每个几何点 $ol(x)$，剩下要找到有限 $Lambda$-模 $G$、有限态射 $g: Z -> X$ 与态射 $phi: cal(F) -> g_* ul(G)_Z$，使 $phi$ 在 $x$ 处诱导茎上的单射 $cal(F)_(ol(x)) -> (g_* ul(G)_Z)_(ol(x))$。 

  令 $Z = ol({x}) subset X$，赋予诱导的既约子概形结构；这使 $Z$ 成为整概形，泛点为 $x$，函数域为 $K := K(Z) = k(x)$。此时 $cal(F)_(ol(x))$ 是带 $Gal_K$-作用的有限 $Lambda$-模，故存在有限 Galois 扩张 $L\/K$，使 $Gal_L$ 在 $cal(F)_(ol(x))$ 上平凡作用（取有限生成元组各稳定子群的交即可）。 

  取正规化 $nu: Y -> Z$，其中 $Y$ 是 $Z$ 在 $L$ 中的正规化；这使 $Y$ 成为正规整概形，$nu$ 为整态射。由于 $L\/K$ 有限，有 $L = K(Y)$（在仿射开集上验证即可）。设 $y in Y$ 是 $Y$ 的泛点，$k(y) = L$，则 $nu(y) = x$。此时 $cal(F)|_y$ 是常值层 $ul(G)_y$，因为 $Gal_L$ 在有限交换群 $cal(F)_(ol(x))$ 上平凡作用。由伴随性，同构 $cal(F)|_y -> ul(G)_y$ 给出态射 $cal(F)|_Y -> y_* ul(G)_y$，从而给出态射 $phi: cal(F) -> f_* y_* ul(G)_y$，其中 $f: Y ->^nu Z arrow.r.hook X$。 

  #lemma(name: <generic-pt-pushforward-of-const-shv-on-normal-sch>)[
    设 $X$ 是整正规概形，函数域为 $K$。则泛点的包含映射 $eta: eta = Spec(K) -> X$ 满足： 
    $
      eta_* ul(G)_eta cong ul(G)_X
    $
  ]
  #proof[
    由伴随性 $eta^(-1) ul(G)_X cong ul(G)_eta$ 得到典范映射 $ul(G)_X -> eta_* ul(G)_eta$。另一方面，对 $X$ 的任意几何点 $ol(x)$， 
    $
      (eta_* ul(G)_eta)_(ol(x)) = Gamma(eta times_X tilde(X)_(ol(x)), ul(G)_eta|_(eta times_X tilde(X)_(ol(x)))) =  Gamma(eta times_X tilde(X)_(ol(x)), ul(G)_(eta times_X tilde(X)_(ol(x))))
    $
    由于 $cal(O)_(X,x)$ 是正规局部整环，由 @permanence-of-properties-under-henselization (3)，其严格 Hensel 化 $cal(O)_(X,x)^#[sh]$ 也是正规局部整环。于是由局部验证可知，$eta times_X Spec(cal(O)_(X,x)^#[sh])$ 是 $cal(O)_(X,x)^#[sh]$ 的某个局部化的谱，从而是整环的谱，因而不可约。因此 $Gamma(eta times_X tilde(X)_(ol(x)), ul(G)_(eta times_X tilde(X)_(ol(x)))) = G$，于是典范映射 $ul(G)_X -> eta_* ul(G)_eta$ 是同构。 
  ]
  这样便定义了态射 $phi: cal(F) -> f_* ul(G)_Y$，其中 $f: Y ->^nu Z arrow.r.hook X$ 是整态射。这就是所要的态射：在 $ol(x)$ 处取茎，展开伴随性便得到交换图表： 
  // https://q.uiver.app/#r=typst&q=WzAsNCxbMCwwLCJjYWwoRilfKG9sKHgpKSJdLFsxLDAsIihjYWwoRil8X1kpXyhvbCh4KSkiXSxbMSwxLCIodWwoRylfWSlfKG9sKHkpKSJdLFswLDEsIihmXyp1bChHKSlfKG9sKHgpKSJdLFswLDNdLFszLDJdLFswLDFdLFsxLDJdXQ==
  #align(center, diagram({
    node((-1, -1), [$cal(F)_(ol(x))$])
    node((0, -1), [$(cal(F)|_Y)_(ol(x))$])
    node((0, 0), [$(ul(G)_Y)_(ol(y))$])
    node((-1, 0), [$(f_*ul(G))_(ol(x))$])
    edge((-1, -1), (-1, 0), "->", $phi_(ol(x))$)
    edge((-1, 0), (0, 0), "->")
    edge((-1, -1), (0, -1), "=")
    edge((0, -1), (0, 0), "=")
  }))
  于是 $phi_(ol(x))$ 是单射。 

  若 $f$ 有限，则已经完成。然而一般来说 $f$ 只是整态射。注意 $Y = invlim_i Y_i$ 是 $Y_i = SPec(cal(A)_i)$ 的逆向极限，其中 $cal(A)_i$ 构成 $nu_* cal(O)_Y$ 的有限凝聚 $cal(O)_Z$-子代数的正向系统。此时每个 $Y_i$ 都是整概形，而 $f_i: Y_i -> Z -> X$ 有限。由 @relative-limit-formula-for-schemes，
  $
    f_* ul(G)_Y = dirlim_i f_(i,*) ul(G)_(Y_i)
  $
  于是有态射 $phi: cal(F) -> dirlim_i f_(i,*) ul(G)_(Y_i)$，它在 $ol(x)$ 处的茎上是单射。

  #lemma[
    设 $cal(F) in cAb(X_et, Lambda)$ 是可构造层，${cal(G)_i}_(i in I)$ 是 $Lambda$-模层的正向系统。则： 
    $
      Hom_(cAb(X_et,Lambda)) (cal(F), dirlim_(i in I) cal(G)_i) = dirlim_(i in I) Hom_(cAb(X_et,Lambda)) (cal(F), cal(G)_i)
    $ 
  ]
  #proof[
    先证明对拟紧平展的 $f: U -> X$ 与 $cal(F) = f_! ul(Lambda)$，该结论成立。事实上由伴随性，这等价于给出态射： 
    $
      ul(Lambda) -> f^(-1) (dirlim_(i in I) cal(G)_i) = dirlim_(i in I) f^(-1) cal(G)_i
    $
    即 $dirlim_(i in I) f^(-1) cal(G)_i$ 的每个截面都来自某个 $f^(-1)cal(G)_i$。现在由 @limit-formula-for-sheaves， 
    $
      Gamma(U, dirlim_(i in I) f^(-1) cal(G)_i) = dirlim_(i in I) Gamma(U, f^(-1) cal(G)_i)
    $
    /*而取 $n$-挠（作为核，即有限极限）与正向极限交换，故有：*/
    于是得到： 
    $
      Hom(ul(Lambda), dirlim_(i in I) f^(-1) cal(G)_i) = dirlim_(i in I) Hom(ul(Lambda), f^(-1) cal(G)_i)
    $ 
    证毕。 

    现在回到一般情形。取拟紧平展的 $f: U -> X$ 与 $g: V -> X$，以及正合列： 
    $
      g_! ul(Lambda) -> f_! ul(Lambda) -> cal(F) -> 0
    $
    这依据 @constructible-sheaves-first-props (4)。剩下的就是抽象的范畴论证： 
    $
      & Hom (cal(F), dirlim_(i in I) cal(G)_i) = Hom(coker(g_! ul(Lambda) -> f_! ul(Lambda)), dirlim_(i in I) cal(G)_i) \
      =& ker(Hom(f_! ul(Lambda), dirlim_(i in I) cal(G)_i) -> Hom(g_! ul(Lambda), dirlim_(i in I) cal(G)_i)) \
      =& ker(dirlim_(i in I) Hom(f_! ul(Lambda), cal(G)_i) -> dirlim_(i in I) Hom(g_! ul(Lambda), cal(G)_i)) #[由关于 $f_! ul(Lambda) $ 的结果] \
      =& dirlim_(i in I) ker(Hom(f_! ul(Lambda), cal(G)_i) ->Hom(g_! ul(Lambda), cal(G)_i)) \
      =& dirlim_(i in I) Hom(cal(F), cal(G)_i)
    $
  ]
  于是 $phi: cal(F) -> dirlim_i f_(i,*) ul(G)_(Y_i)$ 分解为某个 $phi_i: cal(F) -> f_(i,*) ul(G)_(Y_i)$。此外，$phi$ 在 $ol(x)$ 处的茎上是单射，而 $cal(F)_(ol(x))$ 是有限群，故把阶段 $i$ 放大后，$phi_i$ 在 $ol(x)$ 处的茎上也是单射。取这样的 $phi_i$ 即可。 
]

最后指出：可构造层构成 $cAb(X_et, Lambda)$ 的厚子范畴，从而是 $D^bullet (X_et, Lambda)$ 的三角子范畴： 

#construction(name: <constructible-derived-categories>)[
  设 $X$ 是 Noether 概形，$Lambda$ 是 Noether 环。由 @constructible-sheaves-first-props (5)，$cAb(X_et, Lambda)$ 中由 $Lambda$-模可构造层构成的满子范畴 $cAb_c (X_et, Lambda)$，以及 $cAb(X_et)$ 中由交换群可构造层构成的满子范畴 $cAb_c (X_et)$，都是厚子范畴。于是对 $bullet in {#`blank`, -, +, b}$，有： 

  - $D^bullet_c (X_et, Lambda)$ 是 $D^bullet (X_et, Lambda)$ 的三角子范畴； 

  - $D^bullet_c (X_et)$ 是 $D^bullet (X_et)$ 的三角子范畴。 
]
