#import "void-import.typ": *

== Fpqc 下降
#let DD = math.op[DD]

本节我们将建立一件重要的技术工具，称为 fpqc 下降。它正是平展层构造背后关键的代数引擎，另外还有几处要用它来下降线丛、平展主丛 (étale torsor) 之类的结构。

简而言之，下降理论回答下面这些问题。给定态射 $f: S' -> S$：

- 何时 $cal(G) in QCoh(S')$ 来自某个 $cal(F) in QCoh(S)$ 的拉回？这个构造有多自然？

- 何时态射 $S' -> X$ 能提升为态射 $S -> X$？这个构造有多自然？

结果表明，只要 $S' -> S$ 是 fpqc 的，这两个问题都有令人满意的答案。

#definition(name: <defn-faithfully-flat-and-fpqc-morphisms>)[
  若概形态射 $f: S' -> S$ 平坦且满射，则称之为*忠实平坦*的。若 $Spec(B) -> Spec(A)$ 忠实平坦，则称环同态 $A -> B$ 为*忠实平坦*的。
  
  若概形态射 $f: S' -> S$ #furi[fidelement plat][忠实平坦]且拟紧，则称之为 *fpqc*。
]

#notation(name: <descent-notation>)[
  设 $f: S' -> S$ 是概形间的态射。记 $S'' = S' times_S S'$，$S''' = S' times_S S' times_S S'$。于是有投影：
  $
    p_(12), p_(13), p_(23): S''' -> S''
  $
  它们分别是到分量 $(1,2),(1,3),(2,3)$ 的投影。此外还有投影：
  $
    p_1, p_2: S'' -> S'
  $
  分别投影到其中一个分量上。

  对 $S$ 上的任意对象 $X$，用 $X', X'', X'''$ 分别表示它沿上述态射作基变换到 $S', S'', S'''$ 所得的对象。
]

#construction(name: <descent-data>)[
  设 $cal(F) in QCoh(S)$，$cal(F)' = f^* cal(F)$。则有典范同构：
  $
    eta: p_1^* cal(F)' -> p_2^* cal(F)'
  $
  它是 $S''$ 上拟凝聚层之间的同构。局部地，这个同构应当看成：
  $
    (M otimes_A A') otimes_A A' -> A' otimes (M otimes_A A'), (m otimes a'_1) otimes a'_2 |-> a'_1 otimes (m otimes a'_2)
  $
  其中 $A'$ 是 $A$-代数，$M$ 是 $A$-模。$eta$ 自然满足余圈条件：
  $
    p_(13)^* eta = p_(23)^* eta compose p_(12)^* eta
  $
  我们把这一对 $(cal(F)', eta)$ 称为 $cal(F)'$ 的*典范下降数据* (canonical descent datum)。

  仿照这个构造，$S' -> S$ 的*下降数据*是一对 $(cal(F)', eta)$，其中 $cal(F)' in QCoh(S')$，且 $eta: p_1^* cal(F)' -> p_2^* cal(F)'$ 满足余圈条件 $p_(13)^* eta = p_(23)^* eta compose p_(12)^* eta$。两个下降数据之间的态射，就是它们所对应的层之间、与同构 $eta$ 相容的态射。
  
  记 $f: S' -> S$ 的下降数据范畴为 $DD(f)$。典范下降数据的构造给出一个函子：
  $
    QCoh(S) -> DD(f), cal(F) |-> (cal(F)', eta)
  $
  我们要回答的问题是：这个函子是否为范畴等价。
]

#lemma[
  设 $f: S' -> S$ 忠实平坦，$(cal(G), eta) in DD(f)$ 是任意下降数据。则 $eta$ 满足余单位条件：
  $
    Delta^* eta = id_(Delta^* cal(G))
  $
]
#proof[
  考虑余圈条件：
  $
    p_(13)^* eta = p_(23)^* eta compose p_(12)^* eta
  $
  取态射 $D: S'' -> S''', (x, y) |-> (x, x, y)$，即 $(p_1, p_1, p_2)$ 的纤维积。把 $D^*$ 作用到上面的关系式上，得到：
  $
    (p_(13) compose D)^* eta = (p_(23) compose D)^* eta compose (p_(12) compose D)^* eta
  $
  即
  $
    eta = eta compose (Delta compose p_1)^* eta
  $
  由于 $eta$ 是同构，可以把它消去，得到 $p_1^* Delta^* eta = id_(p_1^* Delta^* cal(G))$。$p_1$ 是 $f$ 的基变换，因此也忠实平坦。于是 $p_1^*$ 在态射上是忠实的，故 $Delta^* eta = id_(Delta^* cal(G))$。
]

#lemma(name: <amitsur-complex-exact>)[
  （Amitsur 序列）设 $A -> A'$ 忠实平坦，令 $A^((n))$ 为 $n$ 个 $A'$ 在 $A$ 上的张量积。对任意 $M in AMod(A)$，记 $M^((n)) = M otimes_A A^((n))$。则序列：
  $
    0 -> M -> M' -> dots.c -> M^((n)) &-> M^((n+1)) -> dots.c \
    m otimes a_1 otimes dots.c otimes a_n &|-> m otimes (sum_(i=0)^n (-1)^i (dots.c otimes a_(i-1) otimes 1 otimes a_i otimes dots.c))
  $
  正合。特别地，我们有左正合序列：
  $
    0 -> M &-> M' &&-> M'' \
     m &|-> m otimes 1 #killcol \
     && #killcol m otimes a' &|-> m otimes (1 otimes a' - a' otimes 1) 
  $
  对每个 $M in AMod(A)$ 都成立。
]
#proof[
  直接验证可知 Amitsur 序列是链复形。（在代数拓扑里证明奇异复形确实是链复形时，你应该见过这个组合论证。）

  由于 $A -> A'$ 忠实平坦，要证 Amitsur 序列正合，只需证明它作基变换到 $A'$ 之后正合。令 $N^((n)) = A' otimes_A M^((n))$，并重排张量因子，将两者等同：
  $
    N^((n)) = M otimes_A A' otimes_A A^((n))
  $
  其中第一个 $A'$ 是来自 $A' otimes_A -$ 的那个指定张量因子。现在看基变换后的复形，其微分是：
  $
    d^n: N^((n)) &-> N^((n+1)) \
    m otimes a_0 otimes a_1 otimes dots.c otimes a_n &|-> m otimes a_0 otimes (sum_(i=0)^n (-1)^i (dots.c otimes a_(i-1) otimes 1 otimes a_i otimes dots.c))
  $
  它保持指定因子 $a_0$ 不动。令：
  $
    delta^n_i (m otimes a_0 otimes a_1 otimes dots.c otimes a_n) = m otimes a_0 otimes dots.c otimes a_(i-1) otimes 1 otimes a_i otimes dots.c
  $
  它是定义 $d^n$ 的和式中的第 $i$ 个余面映射，于是 $d^n = sum_(i=0)^n (-1)^i delta^n_i$。下面定义：
  $
    phi^n: N^((n+1)) &-> N^((n)) \
    m otimes a_0 otimes a_1 otimes dots.c otimes a_n &|-> m otimes a_0 a_1 otimes a_2 otimes dots.c otimes a_n
  $
  于是：

  - $delta^n_0$ 把 $1$ 插入第 $1$ 个位置，因此 $phi^n compose delta^n_0$ 的作用是 $m otimes a_0 otimes dots.c |-> m otimes a_0 otimes 1 otimes dots.c |-> m otimes a_0 otimes dots.c $，即恒等映射：
    $
      phi^n compose delta^n_0 = id_(N^((n)))
    $

  - 对 $i >= 1$，$delta^n_i$ 把 $1$ 插入第 $i+1>=2$ 个位置。于是 $phi^n$ 会把原来的第 $0$ 个与第 $1$ 个张量因子乘起来，而插入的 $1$ 留在第 $i$ 个位置。因此：
    $
      phi^n compose delta^n_i = delta^(n-1)_(i-1) compose phi^(n-1)
    $

  因此，
  $
    phi^n compose d^n = sum_(i=0)^n (-1)^i phi^n compose delta^n_i = id_(N^((n))) - sum_(i=0)^(n-1) (-1)^i delta_i^(n-1) compose phi^(n-1) = id_(N^((n))) - d^(n-1) compose phi^(n-1)
  $
  于是 $phi^n$ 定义了从 $id_(N^((bullet)))$ 到 $0$ 的链同伦，因此链复形 $0 -> N^((bullet))$ 正合。
]

#proposition[
  （fpqc 下降的仿射情形）设 $f: A -> A'$ 忠实平坦。则：
  
  + 对任意 $M, N in AMod(A)$，序列：#h(1fr)
    $
      0 -> Hom_A (M, N) -->^(f^*) Hom_(A') (M', N') -->^(p_1^* - p_2^*) Hom_(A'') (M'', N'')
    $
    左正合，其中 $p_1, p_2: A' -> A'' = A' otimes_A A'$ 是到 $A''$ 两个分量的自然映射。换言之，
    $
      QCoh(Spec(A)) -> DD(Spec(A') -> Spec(A))
    $
    是全忠实的。

  + 给定模 $N' in AMod(A')$，以及 $A''$-同构 $eta: N' otimes_A A' -> A' otimes_A N'$；设 $eta$ 满足余圈条件 $p_(13)^* eta = p_(23)^* eta compose p_(12)^* eta$（其中 $p_(12), p_(13), p_(23): A'' -> A'''$ 是对三种两两分量组合的自然映射）。则存在模 $N in AMod(A)$ 与同构 $N' cong N otimes_A A'$，使得在这一同构之下，自然同构 $(N otimes_A A') otimes_A A' -> A' otimes_A (N otimes_A A')$ 与 $eta$ 相容。

    换言之，
    $
      QCoh(Spec(A)) -> DD(Spec(A') -> Spec(A))
    $
    是本质满的。
]
#proof[
  （1）$f^*$ 是单射，这是忠实平坦性的特点；又因 $p_1 compose f = p_2 compose f$，这个序列自然是链复形。只需证明：任何满足 $p_1^* phi = p_2^* phi$ 的态射 $phi in Hom_(A') (M', N')$（等价地，展开定义后，它满足下式）
  $
    phi(m otimes a'_1) otimes a'_2 = a'_1 otimes phi(m otimes a'_2)
  $
  都是某个 $psi in Hom_A (M, N)$ 的提升。对每个固定的 $m in M$，考虑 $phi(m otimes 1) in N'$。则有：
  $
    phi(m otimes 1) otimes 1 = 1 otimes phi(m otimes 1)
  $
  这是由上面的条件得到的。由 Amitsur 序列，存在唯一的 $n in N$ 使得 $n otimes 1 = phi(m otimes 1)$。于是定义 $psi(m) := n$。由于 $n$ 的选取唯一，容易看出 $psi$ 是 $A$-线性的，从而 $phi$ 是 $psi$ 的基变换。

  （2）令：
  $
    N = {x in N': eta(x otimes 1) = 1 otimes x in A' otimes_A N'}
  $
  则 $N$ 是一个 $A$-模，它使如下序列正合：
  $
    0 -> N arrow.r.hook^i N' ->^(gamma - delta) A' otimes_A N'
  $
  其中 $gamma, delta: N' -> A' otimes_A N'$，$gamma(x) := 1 otimes x$，$delta(x) := eta(x otimes 1)$。考虑图表：
  #align(center, diagram({
    node((-1, 0), $0$)
    edge("->")
    node((0, 0), $N otimes_A A'$)
    edge("hook->")
    node((1, 0), $N' otimes_A A'$)
    edge("->", $(gamma - delta) otimes id_(A')$)
    node((2, 0), $A' otimes_A N' otimes_A A'$)

    node((-1, 1), $0$)
    edge("->")
    node((0, 1), $N'$)
    edge("hook->", label-side: right/*, $x |-> x otimes 1$*/)
    node((1, 1), $A' otimes_A N'$)
    edge("->", label-side: right/*, $x otimes a' |-> x otimes (1 otimes a' - a' otimes 1)$*/)
    node((2, 1), $A' otimes A' otimes N'$)
    edge((1, 0), (1, 1), "->", $eta$)
    edge((2, 0), (2, 1), "->", $p_(23)^* eta$)
  }, spacing: 4.5em))
  其中第一行是上述序列 $0 -> N arrow.r.hook^i N' ->^(gamma - delta) A' otimes_A N'$ 与 $A'$ 作张量积所得，仍然正合；第二行是 Amitsur 序列。我们断言右边的方块交换。事实上，令 $eta(x otimes 1) = sum_i a'_i otimes x_i$，则：
  #align(center, diagram({
    node((0, 0), $x otimes a'$)
    edge("|->", $(gamma-delta) otimes id_(A')$)
    node((1, -1), $(1 otimes x - sum_i a'_i otimes x_i) otimes a'$)
    edge("|->", $p_(23)^* eta$)
    node((2, -1), $1 otimes eta(x otimes a') - sum_i a'_i otimes eta(x_i otimes a')$)
    edge((0, 0), (1, 1), "|->", $eta$)
    node((1, 1), $sum_i a'_i otimes a' x_i$)
    edge("|->", [Amitsur])
    node((2, 1), $sum_i 1 otimes a'_i otimes a' x_i - sum_i a'_i otimes 1 otimes a' x_i$)
  }))
  现在由线性性，$eta(x otimes a') = sum_i a'_i otimes a' x_i$。因此要证右边的方块交换，只需证明：
  $
    sum_i a'_i otimes eta(x_i otimes a') = sum_i a'_i otimes 1 otimes a' x_i
  $
  这正是余圈条件：
  #align(center, diagram({
    node((0, 0), $x otimes 1 otimes a'$)
    edge("|->", $p_(12)^* eta$)
    node((0, 1), $sum_i a'_i otimes x_i otimes a'$)
    edge("|->", $p_(23)^* eta$)
    node((1, 1), $sum_i a'_i otimes eta(x_i otimes a')$)
    edge("=")
    node((1, 0), $sum_i a'_i otimes 1 otimes a' x_i$)
    edge((0, 0), (1, 0), "|->", $p_(13)^* eta$)
  }))
  换言之，在交换图表
  #align(center, diagram(
    {
      node((-1, 0), $0$)
      edge("->")
      node((0, 0), $N otimes_A A'$)
      edge("hook->")
      node((1, 0), $N' otimes_A A'$)
      edge("->", $(gamma - delta) otimes id_(A')$)
      node((2, 0), $A' otimes_A N' otimes_A A'$)
      
      node((-1, 1), $0$)
      edge("->")
      node((0, 1), $N'$)
      edge("hook->", label-side: right /*, $x |-> x otimes 1$*/)
      node((1, 1), $A' otimes_A N'$)
      edge("->", label-side: right /*, $x otimes a' |-> x otimes (1 otimes a' - a' otimes 1)$*/)
      node((2, 1), $A' otimes A' otimes N'$)
      edge((1, 0), (1, 1), "->", $eta$)
      edge((2, 0), (2, 1), "->", $p_(23)^* eta$)
      edge((0, 0), (0, 1), "-->", $q$)
    },
    spacing: 4.5em,
  ))
  中，两行都正合，且 $eta, p_(23)^* eta$ 都是同构。于是存在同构 $q: N otimes_A A' -> N'$ 补在虚线箭头处，从而把两个本质上相同的态射的核等同起来。换言之，同构 $q$ 满足：
  $
    1 otimes q(n otimes 1) = eta(n otimes 1) = 1 otimes n, forall n in N
  $
  从而 $q(n otimes 1) = n, forall n in N$。下面验证下图交换：
  #align(center, diagram({
    node((0, 0), $(N otimes_A A') otimes_A A'$)
    edge("->"/*, $(x otimes a'_1) otimes a'_2 |-> a'_1 otimes (x otimes a'_2)$*/)
    node((1, 0), $A' otimes_A (N otimes_A A')$)
    edge((0, 0), (0, 1), "->", $q otimes id_(A')$)
    node((0, 1), $N' otimes_A A'$)
    edge("->", $eta$)
    node((1, 1), $A' otimes_A N'$)
    edge((1, 0), (1, 1), "->", $id_(A') otimes q$)
  }, spacing: 4em))
  事实上，由线性性，只需对这个图表中所有形如 $(n otimes 1) otimes 1$ 的元素验证交换性：
  #align(center, diagram({
      node((0, 0), $(n otimes 1) otimes 1$)
      edge("|->" /*, $(x otimes a'_1) otimes a'_2 |-> a'_1 otimes (x otimes a'_2)$*/)
      node((1, 0), $1 otimes (n otimes 1)$)
      edge((0, 0), (0, 1), "|->", $q otimes id_(A')$)
      node((0, 1), $n otimes 1$)
      edge("|->", $eta$)
      node((1, 1), $1 otimes n$)
      edge((1, 0), (1, 1), "|->", $id_(A') otimes q$)
  }, spacing: 4em))
  至此证毕。
]

#theorem(name: <fpqc-descent-of-sheaves>)[
  （拟凝聚层的 fpqc 下降）设 $f: S' -> S$ 是 fpqc 的。则函子：
  $
    QCoh(S) -> DD(f), cal(F) |-> (cal(F)', eta)
  $
  把 $S$ 上的拟凝聚层 $cal(F)$ 对应到它沿 $f: S' -> S$ 的典范下降数据，是范畴等价。
]
#proof[
  上一个命题正是本定理在 $S', S$ 仿射时的情形。化归到仿射情形这一步并不太关键，所以我会跳过一些细节。

  用仿射开集 ${S_i}$ 覆盖 $S$。对每个 $S_i$，取有限多个仿射开集 ${S'_(i,j)}$ 覆盖 $f^(-1) (S_i)$，并令 $S'_i = union.sq.big_j S'_(i,j)$。$S'_i$ 是仿射概形的_有限不交_并，因此是仿射的。换言之，我们有仿射概形之间的一族联合满射 (jointly surjective) 的局部同构 ${lambda_i: S'_i -> S'}_i$，以及一族忠实平坦态射 ${f_i: S'_i -> S_i}$。

  全忠实性：
  #proof[
    设 $cal(F), cal(G) in QCoh(S)$。要证：
    $
      Hom_(QCoh(S)) (cal(F), cal(G)) -> Hom_(DD(f)) (f^* cal(F), f^* cal(G))
    $
    是同构。令 $S_(i,j) = S_i ∩ S_j, S'_(i,j) = S'_i times_(S') S'_j$，$f_(i,j): S'_(i,j) -> S_(i,j)$。我们有一个所有平行四边形都交换的图表：
    #align(center, diagram({
      node((0, 0), $Hom_(QCoh(S)) (cal(F), cal(G))$)
      edge("->")
      node((1, 0), $product_i Hom_(QCoh(S_i)) (cal(F)|_(S_i), cal(G)|_(S_i))$)
      edge("->", shift: (0, 0.1))
      edge("->", shift: (0, -0.1))
      node((2, 0), $product_(i,j) Hom_(QCoh(S_(i,j))) (cal(F)|_(S_(i,j)), cal(G)|_(S_(i,j)))$)

      node((0, 1), $Hom_(DD(f)) (f^* cal(F), f^* cal(G))$)
      edge("->")
      node((1, 1), $product_i Hom_(DD(f_i)) (f_i^* cal(F)|_(S_i), f_i^* cal(G)|_(S_i))$)
      edge("->", shift: (0, 0.1))
      edge("->", shift: (0, -0.1))
      node((2, 1), $product_(i,j) Hom_(DD(f_(i,j))) (cal(F)|_(f_(i,j)^* S_(i,j)), f_(i,j)^* cal(G)|_(S_(i,j)))$)

      for i in range(3) { edge((i, 0), (i, 1), "->") }
    }, spacing: (3em, 5em), node-defocus: 0))
    其中竖直箭头都是下降函子。

    两行都是等化子，因为层与态射都能沿由局部同构组成的覆盖粘起来。由仿射情形，第二个竖直箭头是双射。

    - 在左边的方块中，上方箭头与右侧箭头都是单射，因此左侧箭头是单射。

      换言之，对任何 fpqc 的 $f$，$QCoh(S) -> DD(f)$ 都是忠实的。把它用到 $f_(i,j)$ 上，可知第三个竖直箭头也是单射。

    - 第二个竖直箭头是双射，所有竖直箭头都是单射，而各行都是等化子。简单追图即可知，左侧箭头是满射。

      换言之，对任何 fpqc 的 $f$，$QCoh(S) -> DD(f)$ 都是满的。
    #suppress-qed
  ]

  本质满性：
  #proof[
    给定任意下降数据 $(cal(G), eta) in DD(f)$。注意 $(cal(G)|_(S'_i), lambda_i^* eta)$ 是关于 $f_i: S'_i -> S_i$ 的下降数据。由仿射情形，它同构于 $(f_i^* cal(F)_i, eta_(cal(F)_i))$，其中 $cal(F)_i in QCoh(S_i)$。

    接下来，由 ${(cal(G)|_(S'_i), lambda_i^* eta)}$ 之间的相容性，我们看到 $DD(f_(i,j))$ 中存在同构 $(f_(i,j)^* cal(F)_i|_(S_(i,j)), eta_#[natural]) cong (f_(i,j)^* cal(F)_j|_(S_(i,j)), eta_#[natural])$，且满足余圈条件。由全忠实性，它们下降为满足余圈条件的同构 $cal(F)_i|_(S_(i,j)) cong cal(F)_j|_(S_(i,j))$。于是这些 $cal(F)_i$ 粘成 $cal(F) in QCoh(S)$。
    #suppress-qed
  ]
]

#theorem(name: <fpqc-descent-of-morphisms>)[
  （态射的 fpqc 下降）设 $f: S' -> S$ 是 $T$-概形之间的 fpqc 态射。则自然映射：
  $
    Hom_T (S, X) ->^(- compose f) Hom_T (S', X) arrows.rr^(- compose p_1)_(- compose p_2) Hom_T (S'', X)
  $
  对每个 $T$-概形 $X$，上述自然映射都构成等化子。
]
#proof[
  先假定 $X = Spec(A)$ 仿射，且落在 $T$ 的一个仿射开集 $Spec(R) subset T$ 之上。此时只需证明：
  $
    Hom_(AAlg(R)) (A, cal(O)_S (S)) -> Hom_(AAlg(R)) (A, cal(O)_(S') (S')) arrows.rr Hom_(AAlg(R)) (A, cal(O)_(S'') (S''))
  $
  是等化子。由于 $Hom_(AAlg(R)) (A, -)$ 保持等化子，只需证明：
  $
    cal(O)_S (S) ->^(f^\#) cal(O)_(S') (S') arrows.rr^(p_1^\#)_(p_2^\#) cal(O)_(S'') (S'')
  $
  是等化子。这个序列可以写成：
  $
    Hom_(cal(O)_S) (cal(O)_S, cal(O)_S) -> Hom_(cal(O)_(S')) (cal(O)_(S'), cal(O)_(S')) arrows.rr Hom_(cal(O)_(S'')) (cal(O)_(S''), cal(O)_(S''))
  $
  由拟凝聚层 fpqc 下降的全忠实性，它是等化子。

  接下来，我们断言 $S, S', S''$ 的开子集构成等化子：
  $
    "Open"(S) ->^(f^(-1)) "Open"(S') arrows.rr^(p_1^(-1))_(p_2^(-1)) "Open"(S'')
  $
  事实上，

  - 由于 $f$ 满射，$V = f(f^(-1)(V))$，故 $f^(-1)$ 在开集上是单射；

  - 设 $V' in "Open"(S')$ 满足 $p_1^(-1) (V') = p_2^(-1) (V')$。
    
    若 $s'_(1,2) in S'$ 落在同一个点 $s in S$ 之上，则存在点 $s'' in S''$ 使得 $p_(1,2) (s'') = s'_(1,2)$。于是：
    $
      p_1 (s'') = s'_1 in V' <==> s'' in p_1^(-1) (V') <==> s'' in p_2^(-1) (V') <==> p_2 (s'') = s'_2 in V'
    $ 
    于是 $V'$ 是 $f: S' -> S$ 的一些纤维的不交并。也就是说，存在子集 $V subset S$ 使得 $V' = f^(-1) (V)$。由于 $f$ 满射，$V = f(V')$；又因 $f$ 平坦，从而是开映射，于是 $V subset S$ 是开集。这样我们就找到了 $V in "Open"(S)$ 使得 $f^(-1)(V) = V'$。

  现在可以处理一般情形了。取 $X$ 的仿射开覆盖 ${X_i}$，使得每个 $X_i$ 都落在 $T$ 的某个仿射开集之上。现在：

  - 给定 $T$-态射 $a,b: S -> X$ 且 $a compose f = b compose f$。由于 $f$ 满射，$a$ 与 $b$ 在底拓扑空间上一致。令 $S_i = a^(-1) (X_i) = b^(-1) (X_i)$，并记 $a_i, b_i: S_i -> X_i$。再令 $f_i: S'_i -> S_i$ 为 $f$ 的基变换，它仍是 fpqc 的。此时 $a_i compose f_i = b_i compose f_i$，由仿射情形得 $a_i = b_i$。因此 $a = b$。

  - 设 $phi: S' -> X$ 是 $T$-态射且 $phi compose p_1 = phi compose p_2$。令 $V'_i = phi^(-1) (X_i)$。则有：
    $
      p_1^(-1) (V'_i) = p_1^(-1) (phi^(-1) (X_i)) = p_2^(-1) (phi^(-1) (X_i)) = p_2^(-1) (V'_i)
    $
    于是由前面关于提升开集的讨论，存在开集 $V_i subset S$ 使得 $V'_i = f^(-1) (V_i)$。${V'_i}$ 是 $S'$ 的开覆盖，而 $f$ 满射，故 ${V_i}$ 是 $S$ 的开覆盖。记 $f_i: V'_i -> V_i$，它仍是 fpqc 的。
    
    令 $p_(1,i), p_(2,i): p_1^(-1) (V'_i) = p_2^(-1) (V'_i) = V'_i times_(V_i) V'_i -> V'_i$，则由给定条件，$phi|_(V'_i) compose p_(1,i) = phi|_(V'_i) compose p_(2,i)$。$phi|_(V'_i)$ 是映射 $V'_i -> X_i$，故由仿射情形，存在 $T$-态射 $psi_i: V_i -> X_i$ 使得 $phi|_(V'_i) = psi_i compose f_i$。

    把 $f$ 限制到 $f_(i,j): V'_i inter V'_j -> V_i inter V_j$，它是 $f$ 的基变换，仍是 fpqc 的。现在在交集上，
    $
      psi_i|_(V_(i,j)) compose f_(i,j) = phi|_(V'_i inter V'_j) = psi_j|_(V_(i,j)) compose f_(i,j)
    $
    由刚证明的单射性部分，$psi_i|_(V_(i,j)) = psi_j|_(V_(i,j))$。于是这些 ${psi_i}$ 粘成整体的 $T$-态射 $psi: S -> X$，使得 $phi = psi compose f$。

  至此证毕。
]

接下来，我们列出一些有用的、可以沿 fpqc 基变换下降的性质。

#theorem(name: <fpqc-descent-of-properties>)[
  考虑一个拉回图表：
  // https://q.uiver.app/#r=typst&q=WzAsNCxbMCwwLCJYJyJdLFsxLDAsIlknIl0sWzAsMSwiWCJdLFsxLDEsIlkiXSxbMiwzLCJmIiwyXSxbMCwxLCJmJyJdLFsxLDMsImciXSxbMCwyLCJnJyIsMl1d
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
  其中 $g$ 是 fpqc 的。则下列性质中的任何一条对 $f$ 成立，当且仅当它对 $f'$ 成立。
  + 仿射；
  + 有限；
  + 平坦；
  + 非分歧；
  + 平展。
]
#proof[
  这些性质都在基变换下保持，所以只需证明各条性质都能从 $f'$ 下降到 $f$。

  注意这些性质对底空间而言都是 Zariski 局部的。因此可以基变换到 $Y$ 的一个仿射开集上，假定 $Y = Spec(A)$ 仿射。接下来，由于 $g$ 是 fpqc 的，$Y'$ 拟紧。用有限多个仿射开集 ${Y'_i}$ 覆盖 $Y'$，令 $Y'' = union.sq.big_i Y'_i$，并作基变换：
  // https://q.uiver.app/#r=typst&q=WzAsNixbMCwxLCJYJyJdLFsxLDEsIlknIl0sWzAsMiwiWCJdLFsxLDIsIlkiXSxbMSwwLCJZJyciXSxbMCwwLCJYJyciXSxbMiwzLCJmIiwyXSxbMCwxLCJmJyJdLFsxLDMsImciXSxbMCwyLCJnJyIsMl0sWzQsMV0sWzUsMF0sWzUsNCwiZicnIl1d
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
    edge((1, -1), (1, 0), "->")
    edge((0, -1), (0, 0), "->")
    edge((0, -1), (1, -1), [$f''$], label-side: left, "->")
  }))
  此时各条性质对 $f''$ 成立，且 $Y'' -> Y$ 是仿射 fpqc 的。于是可以把 $g$ 换成 $Y'' -> Y$，并假定 $Y' = Spec(A')$，其中 $A'$ 是忠实平坦的 $A$-代数。

  （1）先证 $X$ 既拟紧又拟分离。事实上，

  - $g$ 满射，故 $g'$ 也满射。$X'$ 仿射，因而拟紧，所以 $X = g'(X')$ 拟紧。

  - 任取两个仿射开集 $U, V subset X$。则 $g'^(-1) (U) = U times_Y Y'$ 是两个仿射概形在仿射概形上的纤维积，因而仿射。同理 $g'^(-1) (V)$ 仿射。于是因为 $X'$ 仿射，$g'^(-1) (U inter V) = g'^(-1) (U) inter g'^(-1) (V)$ 仿射。从而 $U inter V = g'(g'^(-1) (U inter V))$ 拟紧。故 $X$ 是拟分离的。

  既然这个图表里的一切都拟紧拟分离，就可以引用拟凝聚层的平坦基变换。对任何拟凝聚理想层 $cal(I) subset cal(O)_X$，
  $
    g^* R^1 f_* cal(I) = R^1 f'_* g'^* cal(I) = 0
  $
  这是因为 $f'$ 仿射。令 $R^1 f_* cal(I) = tilde(M)$，于是 $M otimes_A A' = 0$。由于 $A'$ 在 $A$ 上忠实平坦，由 @amitsur-complex-exact，$M -> M otimes_A A'$ 是单射，故 $M = 0$。从而 $R^1 f_* cal(I) = 0$。由 Serre 的仿射性判别法（#cite-stacks("0F83")[Lemma 30.3.4]），$f$ 是仿射的。

  （2）由（1）知 $f$ 仿射，故可设 $X = Spec(B)$、$Y = Spec(A)$。此时 $B'$ 在 $A'$ 上有限，$A'$ 在 $A$ 上忠实平坦，所以 $B$ 在 $A$ 上有限（譬如由 #cite-stacks("03C4")[Lemma 10.83.2] 可得）。

  （3）（4）（5）在源上都是 Zariski 局部的，故可设 $X = Spec(B)$ 仿射，$X' = Spec(B')$。

  （3）由于 $B'$ 在 $A'$ 上平坦，由 @cite-matsumura-ca[(4.E)(1)] 知 $B$ 在 $A$ 上平坦。因此 $f$ 平坦。

  （4）注意：
  $
    0 = Omega_(B'\/A') = Omega_(B\/A) otimes_B B'
  $
  由于 $B'$ 在 $B$ 上忠实平坦，这证明了 $Omega_(B\/A) = 0$。因此 $f$ 非分歧。

  （5）不过是（3）与（4）合在一起。
]

最后，作为拟凝聚层 fpqc 下降的推论，我们证明相对仿射概形的 fpqc 下降。

#theorem(name: <fpqc-descent-of-relatively-affine-schemes>)[
  设 $f: X' -> X$ 是 fpqc 映射。假定 $Y' -> X'$ 是仿射态射，并带有下降数据：
  $
    eta: Y' times_X X' -> X' times_X Y'
  $
  它是 $X'' = X' times_X X'$-概形的同构，且使下图交换：
  // https://q.uiver.app/#r=typst&q=WzAsMyxbMCwxLCJZJyB0aW1lc19YIFgnIHRpbWVzX1ggWCciXSxbMSwwLCJYJyB0aW1lc19YIFknIHRpbWVzX1ggWCciXSxbMiwxLCJYJyB0aW1lc19YIFgnIHRpbWVzX1ggWSciXSxbMCwyLCJwXygxMyleKiBldGEiLDJdLFswLDEsInBfKDEyKV4qIGV0YSJdLFsxLDIsInBfKDIzKV4qIGV0YSJdXQ==
  #align(center, diagram({
    node((0, 1), [$Y' times_X X' times_X X'$])
    node((1, 0), [$X' times_X Y' times_X X'$])
    node((2, 1), [$X' times_X X' times_X Y'$])
    edge((0, 1), (2, 1), [$p_(13)^* eta$], label-side: right, "->")
    edge((0, 1), (1, 0), [$p_(12)^* eta$], label-side: left, "->")
    edge((1, 0), (2, 1), [$p_(23)^* eta$], label-side: left, "->")
  }))
  则存在仿射态射 $Y -> X$，使得存在 $X'$-概形的同构 $Y' cong Y times_X X'$；并且在这一同构之下，$eta$ 对应于将 $Y$ 移到另一个分量上的典范映射 $(Y times_X X') times_X X' -> X' times_X (Y times_X X')$。
]
#proof[
  记 $g': Y' -> X'$，$cal(A)' = g'_* cal(O)_(Y')$，于是 $Y' = SPec(cal(A)')$。同构 $eta$ 在拟凝聚 $cal(O)_(X')$-代数 $cal(A)'$ 上诱导出下降数据。由 @fpqc-descent-of-sheaves，它底下的拟凝聚模下降到某个 $cal(A) in QCoh(X)$。

  $cal(A)'$ 的单位与乘法都是下降数据的态射。由全忠实性，它们唯一地下降为映射：
  $
    u: cal(O)_X -> cal(A) \
    m: cal(A) otimes_(cal(O)_X) cal(A) -> cal(A)
  $
  $cal(A)$ 满足代数公理，因为拉到 $X'$ 上之后公理成立，且 fpqc 下降是忠实的。因此 $cal(A)$ 是拟凝聚 $cal(O)_X$-代数。

  令 $Y = SPec(cal(A))$。则 $Y -> X$ 仿射。由于 $SPec$ 与基变换交换，有
  $
    Y times_X X' cong SPec(f^* cal(A)) cong SPec(cal(A)') 
  $
  由于 $cal(A)$ 上的典范下降数据正是 $cal(A)'$ 上给定的下降数据，$Y$ 上的典范下降数据就是 $Y'$ 上给定的下降数据 $eta$。
]
