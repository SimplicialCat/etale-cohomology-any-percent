#import "void-import.typ": *

回忆一下：对概形 $X$，有 $Et_X$，即全体平展映射 ${f: Z -> X}$ 构成的范畴。随后我们引入了#furi[recouvrement][平展覆盖] (étale cover) 的概念。此外还有范畴 $FEt_X$，由全体有限平展映射 ${f: Z -> X}$ 构成。在这个语境下，所谓平展#furi[revêtement][覆叠空间]，指的是 $FEt_X$ 中的一个态射。

平展基本群要解决的，正是下面这个分类问题：
#question[
  用 Galois 理论的方式，对 $FEt_X$ 进行分类与描述。
]

直观想法如下。在代数拓扑中，给定一个好的#footnote[别问我什么叫“好”。大概是指 CW 复形。]道路连通拓扑空间 $X$，我们把它的（拓扑）基本群 $pi_1^"top" (X, x)$ 定义为以 $x$ 为基点的回路的同伦等价类。这样的空间有万有覆叠空间 $tilde(X) ->> X$。$pi_1^"top" (X)$ 可以定义为 $tilde(X)$ 在 $X$ 上的自同构群，并且有范畴等价：
$
  bold("Cov")(X) &-> GSet(pi_1^"top" (X, x)) \
  (p: X' -> X) &|-> p^(-1) (x)
$
即 $X$ 的覆叠空间与 $pi_1^"top" (X, x)$-集合之间的范畴等价，其中有限覆叠空间对应同一个群 $pi_1^"top" (X)$ 上的有限集。

同样地，对适当的概形 $X$，我们希望把平展基本群 $pi_1^et (X)$ 定义为_某个东西_的自同构群。平展情形没有万有覆叠空间，所以得另想办法。事实证明，$X$ 的有限平展覆叠空间构成一个滤过系统。于是可以取各个平展覆叠空间的自同构群，作逆向极限，以此定义 $pi_1^et (X)$，得到的是一个投射有限群。

于是我们期望得到如下分类：
$
  FEt_X &-> GSet(pi_1^et (X, ol(x)))^"fin,cont" \
  (p: X' -> X) &|-> p^(-1)(ol(x))
$
（$ol(x)$ 是什么意思先不管。）这是 $X$ 的有限平展覆叠与带连续群作用的有限 $pi_1^et (X, ol(x))$-集之间的范畴等价。

可以想象一下，群 $pi_1^et (X, ol(x))$ 究竟可能长什么样。直观来自 $X = Spec(K)$、$K$ 是域的情形。
#example(name: <pi1et-motivation-eg>)[
  若 $X = Spec(K)$，其中 $K$ 是域，则 $FEt_X$ 中任何对象 $Z$ 都是不交并 $union.sq.big_i Spec(L_i)$，其中 $L_i\/K$ 是有限可分扩张。由 Galois 理论，有限可分扩张 $L\/K$ 对应于绝对 Galois 群 $Gal(K^sep\/K)$ 的开子群 $Gal(K^sep\/L)$。于是
  $
    FEt_X &-> GSet(Gal(K^sep\/K))^#[fin,cont] \
    union.sq.big_i Spec(L_i) &|-> union.sq.big_i Gal(K^sep\/K)\/Gal(K^sep\/L_i)
  $
  是范畴等价。换言之，我们期望 $pi_1^et (Spec(K)) = Gal(K^sep\/K)$，也就是说，平展基本群就是绝对 Galois 群。
]
这个例子提示我们，应当用 Galois 理论的方式建立平展基本群的理论，也就是把 Galois 理论适当推广到有限平展覆叠上。

本章假定 $X$ 是连通的 Noether 概形，并且出现的概形都假定是 Noether 的。这里之所以需要 Noether 假设，是因为一旦没有它，连通分支的行为就可能很病态。

非 Noether 的情形下，平展基本群的理论同样可以发展。不过我们希望这份材料保持简洁、自足，就不去折腾了。

#notation(name: <terminology-etale-coverings>)[
  #furi[recouvrement][平展覆盖] 与 #furi[revêtement][覆叠空间] 这两个法语词看上去差别很大，可惜它们在中文和英文里长得都很像。请务必分清这两个概念。本书用下面这套记号来消除歧义：
  - _平展覆盖_指的是一族联合满射的平展态射 ${f_i: Z_i -> X}$；
  - _有限平展覆叠空间_指的是有限平展态射 $f: Z -> X$。
  不过我本人也不完美，隔三岔五就会忘记该用“cover”还是“covering”。“有限平展覆叠空间”有八个字，多数情况下我懒得写全。经验法则是：看到“有限”或“覆叠空间”，我说的就是第二个概念；看到“平展覆盖”，指的就是第一个；若看到“平展覆叠”却既没有“有限”也没有“空间”，就得靠上下文判断，而且多半该来问我了。
]

== 平展覆叠空间
/*#date[
  第 4 讲，2025/10/15
  #align(left)[
    今天我们介绍：
    - 平展覆叠空间
    - 对有限群取商
    - Galois 理论
    并引入平展基本群。

    提醒：注意左右。
  ]
]*/


#definition(name: <defn-geometric-points>)[
  概形 $X$ 的*几何点*，指的是一个态射 $ol(x) : Spec(Omega) -> X$，其中 $Omega$ 是可分闭域。若普通的点 $x in X$ 是 $ol(x)$ 的像，则称 $ol(x)$ *位于* $x$ 之上。

  *带基点概形* (pointed scheme) $(X,ol(x))$，说的不过是一个概形 $X$ 连同它的一个几何点 $ol(x)$。带基点概形之间的态射 $f: (X, ol(x)) -> (Y, ol(y))$，指的是使下图交换的态射：
  // https://q.uiver.app/#r=typst&q=WzAsMyxbMSwwLCJTcGVjKE9tZWdhKSJdLFswLDIsIlgiXSxbMiwyLCJZIl0sWzAsMSwib3ZlcmxpbmUoeCkiXSxbMCwyLCJvdmVybGluZSh5KSIsMl0sWzEsMiwiZiJdXQ==
  #align(center, diagram({
    node((0, -1), [$Spec(Omega)$])
    node((-1, 1), [$X$])
    node((1, 1), [$Y$])
    edge((0, -1), (-1, 1), [$ol(x)$], label-side: right, "->")
    edge((0, -1), (1, 1), [$ol(y)$], label-side: left, "->")
    edge((-1, 1), (1, 1), [$f$], label-side: right, "->")
  }, spacing: 1.5em))
  #example[
    - 对 $X = Spec(K)$，$X$ 的几何点不过是选定一个落入可分闭域的嵌入 $K arrow.r.hook Omega$。通常取 $Omega = K^sep$ 为可分闭包，或取 $ol(K)$ 为代数闭包。

    - 对一般的概形 $X$，位于 $x in X$ 之上的几何点 $ol(x)$ 也不过是剩余域到可分闭域的一个嵌入 $k(x) -> Omega$。通常同样取 $Omega = k(x)^sep$ 为可分闭包，或取 $ol(k(x))$ 为代数闭包。

    后面会看到，$Omega$ 的选取并不太重要，直接取 $Omega = k(x)^sep$ 或 $ol(k(x))$ 就足以抓住全部本质信息。不过要到课程很后面，我们才会把这层意思说精确。
  ]
]

#definition(name: <defn-fiber-functor>)[
  固定几何点 $ol(x): Spec(Omega) -> X$，定义*纤维函子* (fiber functor)：
  $
    F_(ol(x)): FEt_X &-> cSet^"fin" \
    (p: Z -> X) &|-> p^(-1)(ol(x))
  $
  它把平展覆叠空间送到几何点 $ol(x)$ 处的纤维，即一个有限集。
  
  换言之，这等同于全体二元组 $(z, psi)$ 构成的集合，其中 $z in p^(-1)(x)$ 是普通的点，$psi: k(z) -> Omega$ 是与 $k(x) -> Omega$ 相容的嵌入。特别地，
  $
    abs(F_(ol(x)) (Z)) = dim_(k(x)) (cal(O)_(Z_x) (Z_x)) = deg(p)
  $
  这个数与 $x$ 的选取无关，因为 $p$ 平坦。
]

#properties(name: <fet-first-props>)[
  0. 若有图表：
  // https://q.uiver.app/#r=typst&q=WzAsMyxbMCwwLCJaIl0sWzIsMCwiWiciXSxbMSwxLCJYIl0sWzAsMiwiZiJdLFsxLDIsImYnIiwyXSxbMCwxLCJnIl1d
    #align(center, diagram({
      node((-1, -1), [$Z$])
      node((1, -1), [$Z'$])
      node((0, 0), [$X$])
      edge((-1, -1), (0, 0), [$f$], label-side: right, "->")
      edge((1, -1), (0, 0), [$f'$], label-side: left, "->")
      edge((-1, -1), (1, -1), [$g$], label-side: left, "->")
    }, spacing: 1.5em))
    其中 $(f: Z -> X), (f': Z' -> X) in FEt_X$，则 $g$ 有限平展。
    #proof[
      $g$ 是平展的，这由 @etale-first-props 可得。$g$ 的有限性则不容易从定义验证。不过这里 $g$ 是紧合的，而 $g^(-1)(z') subset f^(-1)(f'(z'))$ 有限，故 $g$ 拟有限。于是由 Zariski 主定理，$g$ 有限。#footnote[这里完全不需要 Zariski 主定理。$g$ 的有限性在这里当然可以手工验证，但我想要一个能快速说服你的简短证明。]
    ]

  1. 设带基点概形 $(Z, ol(z)), (Z', ol(z'))$ 在 $(X, ol(x))$ 上平展。若 $Z$ 连通、$Z'$ 在 $X$ 上分离（有限平展覆叠自然满足这一点），则在 $(X, ol(x))$ 上至多存在一个映射 $g: (Z, ol(z)) -> (Z', ol(z'))$。
    #proof[
      这样的映射 $g$ 使图像 $Gamma_g$ 出现在如下图表中：
      // https://q.uiver.app/#r=typst&q=WzAsNCxbMCwxLCJaIl0sWzIsMSwiWiB0aW1lc19YIFonIl0sWzIsMiwiWiJdLFswLDAsIlNwZWMoT21lZ2EpIl0sWzAsMSwiR2FtbWFfZyIsMV0sWzEsMiwiXCJwclwiX1oiLDFdLFswLDIsIiIsMSx7InN0eWxlIjp7ImhlYWQiOnsibmFtZSI6ImVwaSJ9fX1dLFszLDAsIm92ZXJsaW5lKHopIiwxXSxbMywxLCIob3ZlcmxpbmUoeiksIG92ZXJsaW5lKHonKSkiLDFdXQ==
      #context align(center, diagram({
        node((0, 0), [$Z$])
        node((2, 0), [$Z times_X Z'$])
        node((2, 1), [$Z$])
        node((0, -1), [$Spec(Omega)$])
        edge((0, 0), (2, 0), [$Gamma_g$], label-side: center, "->")
        edge((2, 0), (2, 1), [$"pr"_Z$], label-side: center, "->")
        edge((0, 0), (2, 1), "=")
        edge((0, -1), (0, 0), [$ol(z)$], label-side: center, "->")
        edge((0, -1), (2, 0), [$(ol(z), ol(z'))$], label-side: center, "->")
      }, crossing-fill: thm-box-curr-color()))
      $Gamma_g$ 是对角态射 $Delta_(Z'\/X): Z' -> Z' times_X Z'$ 沿 $g: Z -> Z'$ 的基变换；由于 $Z' -> X$ 平展，$Gamma_g$ 局部是开浸入。又因 $"pr"_Z compose Gamma_g = id_Z$，$Gamma_g$ 是单射，从而必是开浸入。由 $Z' -> X$ 分离，$Gamma_g$ 也是闭浸入。
      
      于是 $Gamma_g: Z -> Z times_X Z'$ 只能是这样的嵌入：把 $Z$ 嵌入 $Z times_X Z'$，作为它的一个连通分支。而 $Z times_X Z'$ 中含 $(ol(z), ol(z'))$ 的连通分支只有一个，故 $Gamma_g$ 若存在则唯一。进而 $g = "pr"_(Z') compose Gamma_g$ 若存在也唯一。
    ]

  + 给定 $(X, ol(x))$ 的有限平展覆叠 $(Z, ol(z))$ 与 $(Z', ol(z'))$，存在连通的有限平展覆叠 $(tilde(Z), ol(tilde(z)))$，使它落在如下交换图表中：
    // https://q.uiver.app/#r=typst&q=WzAsNCxbMSwwLCIodGlsZGUoWiksIG92ZXJsaW5lKHRpbGRlKHopKSkiXSxbMCwxLCIoWiwgb3ZlcmxpbmUoeikpIl0sWzIsMSwiKFonLCBvdmVybGluZSh6JykpIl0sWzEsMiwiKFgsIG92ZXJsaW5lKHgpKSJdLFswLDEsImV4aXN0cyIsMV0sWzAsMiwiZXhpc3RzIiwxXSxbMSwzXSxbMiwzXV0=
    #context align(center, diagram({
      node((0, -1), [$(tilde(Z), ol(tilde(z)))$])
      node((-1, 0), [$(Z, ol(z))$])
      node((1, 0), [$(Z', ol(z'))$])
      node((0, 1), [$(X, ol(x))$])
      edge((0, -1), (-1, 0), [$exists$], label-side: center, "->")
      edge((0, -1), (1, 0), [$exists$], label-side: center, "->")
      edge((-1, 0), (0, 1), "->")
      edge((1, 0), (0, 1), "->")
    }, crossing-fill: thm-box-curr-color(), spacing: 2em))
    这应当看作合成域存在性的推广。
    #proof[
      取 $Z times_X Z'$ 中含 $(ol(z), ol(z')))$ 的像的连通分支。
    ]
  
  + 固定 $X$ 的一个几何点 $ol(x)$。对 $FEt_X$ 中的态射 $g: Z -> Z'$，若 $F_(ol(x)) (g): F_(ol(x)) (Z) -> F_(ol(x)) (Z')$ 是双射，则 $g$ 是同构。

    #proof[
      由于 $g$ 有限平展，$g$ 是同构 $<==>$ $deg(g) = 1$，这等价于 $g$ 的几何纤维基数都是 $1$，即 $F_(ol(x)) (g)$ 的各纤维基数都是 $1$。
    ]
  
  + 若 $Z in FEt_X$ 连通，则任何 $X$-自态射 $g: Z -> Z$ 都是同构。
    #proof[
      由于 $Z$ 连通，由 (1)，$F_(ol(x)) (g): F_(ol(x)) (Z) -> F_(ol(x)) (Z)$ 是单射。有个深刻定理说：基数相同的两个有限集之间的映射，单射 $<==>$ 满射 $<==>$ 双射。于是 $F_(ol(x)) (g)$ 是双射，再由 (3) 知 $g$ 是同构。
    ]
]

#notation[
  对每个 $Z in FEt_X$，定义群：
  $
    Aut(Z\/X) = {g: Z overset(->, tilde) Z "是" FEt_X #[中的自同构]}
  $
  于是 $Aut(Z\/X)$ 在 $Z$ 上有左作用。考虑反群 $Aut(Z\/X)^opp$，它在 $Z$ 上有右作用。
  
  /*今天起，每当我们看到有限抽象群 $G$ 作用在 $Z$ 上，都一律考虑右作用。*/
  #remark[
    从心理上说，之所以考虑反群，是因为：
    $
      Aut(Spec(K^sep)\/Spec(K))^opp cong Gal(K^sep\/K)
    $
    （$K^sep$ 在 $K$ 上并非 _有限_ 平展。不过只要把 $K^sep$ 换成有限 Galois 扩张 $L\/K$，这个关系就成立。）我们真正想要的是绝对 Galois 群，因为在 @pi1et-motivation-eg 中，我们期望 $pi_1^et (Spec(K)) = Gal(K^sep\/K)$，也就是说，平展基本群就是绝对 Galois 群。
  ]
]
