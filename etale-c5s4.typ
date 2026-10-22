// audit-exception: 展示公式内的 #[...] 文字块夹有多段 $...$，朴素配对会把块内中文切成伪公式片段；此处只改文字说明，块内公式已逐段核对未变。
#import "void-import.typ": *

== 常值层的 $H^1$

本节我们要证明下面这个结果，它把常值层的 $H^1$ 与平展基本群联系起来。 

- 设 $X$ 是连通 Noether 概形，$G$ 是有限交换群，则 #h(1fr)
  $
    H^1_et (X, ul(G)) cong Hom_#[cont] (pi_1^et (X, ol(x)), G)
  $
  此同构是典范的。 

这最终会成为一件核心的理论工具，用来把抽象的上同调陈述归约为有限平展覆叠上的具体几何。 

这个命题通过两步分类来证明，中间用平展 $G$-主丛的概念搭桥。我们将通过证明下面两点来建立该同构： 

- $Hom_#[cont] (pi_1^et (X, ol(x)), G)$ 分类平展 $G$-主丛； 

- $H^1_et (X, ul(G))$ 也分类平展 $G$-主丛。 

#definition(name: <defn-etale-g-torsor>)[
  设 $G$ 是有限群。$X$ 上的*平展 $G$-主丛*是指带有一个单传递右 $G$-作用的满射平展映射 $Y ->> X$。也就是说，给定 $X$ 上的群概形 $X_G = union.sq.big_(g in G) X$，存在同构： 
  $
    Y times_X X_G -> Y times_X Y, (y, g) |-> (y, y g)
  $
  // #lemma[
  //   For a finite group $G$, an etale torsor $Y$ of $G$ over $X$ must be etale locally trivial, in the sense that there exists 
  // ]
  特别地，$Y -> X$ 是有限平展覆叠：$Y times_X Y -> Y times_X X_G -> Y$ 有限，而有限性沿 $Y -> X$ 自身的忠实平坦基变换下降。 

  相对于 $X$ 的一个几何点 $ol(x)$，$X$ 上的*带基点平展 $G$-主丛* (pointed étale torsor) 是指一对 $(Y, ol(y))$，其中 $Y$ 是 $X$ 上的平展 $G$-主丛，而 $ol(y) in F_(ol(x)) (Y)$ 是 $Y$ 的一个几何点，位于 $ol(x)$ 上方。 
]

我们先用 $Hom_#[cont] (pi_1^et (X, ol(x)), G)$ 分类 $X$ 上的平展 $G$-主丛： 

#proposition[
  设 $X$ 是连通 Noether 概形，$G$ 是有限群，则存在典范双射： 
  $
    {#[带基点平展 $G$-主丛 $(Y, ol(y)) $，以 $X$ 为底，相对于 $ol(x) $]}/cong -> Hom_#[cont] (pi_1^et (X, ol(x)), G)
  $
  即从 $X$ 上相对于 $ol(x)$ 的带基点平展 $G$-主丛的同构类，到连续同态 $pi_1^et (X, ol(x)) -> G$ 的双射。 
]
#proof[
  第一步。映射的构造。 

  设有 $X$ 上相对于 $ol(x)$ 的带基点平展 $G$-主丛 $(Y, ol(y))$。我们如下定义表示 $rho_(Y,ol(y)): pi_1^et (X, ol(x)) -> G$。考虑同构： 
  $
    Y times G -> Y times_X Y, (y, g) |-> (y, y g)
  $
  取 $ol(x)$ 处的纤维，得到集合之间的双射： 
  $
    F_(ol(x)) (Y) times G -> F_(ol(x)) (Y) times F_(ol(x)) (Y), (ol(u), g) |-> (ol(u), ol(u) g)
  $
  因此，$G$ 在 $F_(ol(x)) (Y)$ 上的右作用是单传递的。于是基点 $ol(y)$ 定义了一个双射 $q_(Y,ol(y)): G -> F_(ol(x)) (Y), g |-> ol(y) g$。 
  
  此外，注意 $F_(ol(x)) (Y)$ 上的右 $G$-作用与左 $pi_1^et (X, ol(x))$-作用相容。每个 $g in G$ 都诱导自同构 $Y -> Y$，于是由函子性，对任意 $gamma in pi_1^et (X, ol(x))$ 都有 $gamma (ol(u) g) = (gamma ol(u)) g$。 

  元素 $gamma in pi_1^et (X, ol(x))$ 会在 $F_(ol(x)) (Y)$ 上诱导一个自同构。现在我们定义： 
  $
    rho_(Y,ol(y)) (gamma) = q_(Y,ol(y))^(-1) (gamma ol(y)) in G
  $
  也就是说，$rho_(Y,ol(y)) (gamma) in G$ 是满足 $gamma ol(y) = ol(y) rho_(Y,ol(y)) (gamma)$ 的唯一元素。 

  - 对 $gamma, delta in pi_1^et (X, ol(x))$， #h(1fr)
    $
      gamma delta ol(y) = gamma (ol(y) rho_(Y,ol(y)) (delta)) = (gamma ol(y)) rho_(Y,ol(y)) (delta) = ol(y) rho_(Y,ol(y)) (gamma) rho_(Y,ol(y)) (delta)
    $
    于是 $rho_(Y,ol(y)) (gamma) rho_(Y,ol(y)) (delta) = rho_(Y,ol(y)) (gamma delta)$，故 $rho_(Y,ol(y))$ 是群同态； 

  - 取有限平展覆叠 $Y -> X$ 的 Galois 闭包 $tilde(Y) -> X$，使得 $Aut(tilde(Y)\/X)$ 是 $pi_1^et (X, ol(x))$ 的有限商。若 $gamma in pi_1^et (X, ol(x))$ 映到 $id in Aut(tilde(Y)\/X)$，则 $gamma(ol(y)) = ol(y)$，于是 $rho_(Y,ol(y)) (gamma) = 1_G in G$。可见 $rho_(Y,ol(y))$ 穿过 $pi_1^et (X, ol(x))$ 的一个有限商分解，其核是开子群，因此它是连续的。 

  第二步。反向构造。 

  给定连续同态 $rho: pi_1^et (X, ol(x)) -> G$，我们现在构造带基点主丛 $(Y_(rho), ol(y)_rho)$。具体说来，$rho$ 把 $G$ 看成带连续左 $pi_1^et (X, ol(x))$-作用的有限离散集 $G_rho$，作用由 $(gamma, g) |-> rho(gamma) g$ 给出。 
  
  于是存在有限平展覆叠 $Y_rho -> X$ 以及同构 $F_(ol(x)) (Y_rho) cong G_rho$。让指定的点 $ol(y)_rho in F_(ol(x)) (Y_rho)$ 对应于元素 $1_G in G_rho$。现在： 

  - $F_(ol(x)) (Y_rho) cong G_rho$ 带有单传递的右 $G$-作用，且与左 $pi_1^et (X, ol(x))$-作用相容。于是得到有限离散 $pi_1^et (X, ol(x))$-集合的同构： 
    $
      F_(ol(x)) (Y_rho) times G -> F_(ol(x)) (Y_rho) times F_(ol(x)) (Y_rho)
    $
    经 $F_(ol(x)) (Y_rho) cong G$ 等同后，它就是 $(u, g) |-> (u, u g)$。于是诱导出 $X$ 的有限平展覆叠之间的同构： 
    $
      Y_rho times_X X_G -> Y_rho times_X Y_rho
    $
    这是因为 $X$ 的有限平展覆叠等价于有限离散 $pi_1^et (X, ol(x))$-集合。 

    可以验证映射 $Y_rho times_X X_G -> Y_rho times_X Y_rho$ 给出右 $G$-作用（只需把映射送到 $F_(ol(x))$ 上验证）。因此 $(Y_rho, ol(y)_rho)$ 具有带基点平展 $G$-主丛的结构。 

  第三步。这两个构造互为逆构造。 

  - 固定 $rho in Hom_#[cont] (pi_1^et (X, ol(x)), G)$。对 $gamma in pi_1^et (X, ol(x))$，$rho_(Y_rho,ol(y)_rho) (gamma) in G$ 是满足下式的唯一元素： 
    $
      gamma ol(y)_rho = ol(y)_rho rho_(Y_rho,ol(y)_rho) (gamma)
    $
    然而，在同构 $F_(ol(x)) (Y_rho) cong G_rho$ 下，$ol(y)_rho |-> 1_G$，而 $gamma$ 通过左乘 $rho(gamma)$ 作用。于是把上式经同构 $F_(ol(x)) (Y_rho) cong G_rho$ 送到另一侧，得到： 
    $
      rho(gamma) = rho_(Y_rho,ol(y)_rho) (gamma)
    $
    故 $rho = rho_(Y_rho,ol(y)_rho)$。 
  
  - 固定带基点平展 $G$-主丛 $(Y, ol(y))$，令 $rho = rho_(Y,ol(y))$。我们要证：$(Y, ol(y)) cong (Y_rho, ol(y)_rho)$ 是平展 $G$-主丛的同构。事实上，有双射： 
    $
      G_rho cong F_(ol(x)) (Y_rho) -> F_(ol(x)) (Y), g |-> ol(y) g
    $
    对 $gamma in pi_1^et (X, ol(x))$，$gamma$ 从左侧作用，把 $g$ 送到 $rho(gamma) g$。按 $rho$ 的定义，这个元素又被送到 $ol(y) rho(gamma) g = gamma ol(y) g$。因此上述双射是 $pi_1^et (X, ol(x))$-等变的。按定义，它把 $1_G in G$（即 $ol(y)_rho in F_(ol(x)) (Y_rho)$）送到 $ol(y)$。 

    由于 $X$ 的有限平展覆叠等价于有限离散 $pi_1^et (X, ol(x))$-集合，上述映射诱导带基点平展覆叠的同构 $(Y_rho, ol(y)_rho) -> (Y, ol(y))$。 

    最后，注意上面的同构 $G_rho -> F_(ol(x)) (Y), g |-> ol(y) g$ 是右 $G$-等变的。于是同构 $(Y_rho, ol(y)_rho) -> (Y, ol(y))$ 也是右 $G$-等变的，从而是平展 $G$-主丛的同构。 

  至此完成了这一分类。 
]

#corollary(name: <hom-from-pi1-classifies-torsors>)[
  设 $X$ 是连通 Noether 概形，$G$ 是有限群，则存在典范双射： 
  $
    {#[平展 $G$-主丛 $Y$，以 $X$ 为底]}/cong -> (Hom_#[cont] (pi_1^et (X, ol(x)), G))/(#[在 $G$ 中共轭])
  $
  即从 $X$ 上平展 $G$-主丛的同构类，到连续同态 $pi_1^et (X, ol(x)) -> G$ 在 $G$ 中共轭作用下的等价类。 

  #remark[
    注意左端不依赖基点 $ol(x)$ 的选取，而右端形式上依赖于 $ol(x)$。不过右端实际上与 $ol(x)$ 无关。事实上，对任何另一个基点 $ol(x')$，都有同构 $pi_1^et (X, ol(x)) cong pi_1^et (X, ol(x'))$，它在共轭意义下唯一。于是 
    $
      (Hom_#[cont] (pi_1^et (X, ol(x)), G))/(#[在 $G$ 中共轭]) cong (Hom_#[cont] (pi_1^et (X, ol(x')), G))/(#[在 $G$ 中共轭])
    $
    是一个典范双射，不依赖同构 $pi_1^et (X, ol(x)) cong pi_1^et (X, ol(x'))$ 的选取，因为共轭带来的不确定性已经被商掉。 
  ]
]
#proof[
  固定 $(X, ol(x))$ 上的带基点平展 $G$-主丛 $(Y, ol(y))$。如前一条命题所讨论，$F_(ol(x)) (Y) = ol(y) G$，因此，$(X, ol(x))$ 上与 $(Y, ol(y))$ 共用同一个主丛的带基点平展 $G$-主丛，恰好是 ${(Y, ol(y) h)}_(h in G)$。现在对 $gamma in pi_1^et (X, ol(x))$，  
  $
    ol(y) h rho_(Y,ol(y) h) (gamma) = gamma ol(y) h = ol(y) rho_(Y,ol(y)) (gamma) h
  $
  即 $h rho_(Y,ol(y) h) (gamma) = rho_(Y,ol(y)) (gamma) h$。于是 $rho_(Y,ol(y) h) (gamma) = h^(-1) rho_(Y,ol(y)) (gamma) h$，可见 $rho_(Y,ol(y)h)$ 就是 $rho_(Y,ol(y))$ 经 $h$ 共轭所得。 

  因此，在分类双射的左端把带基点平展主丛的指定点忘掉，与在右端把 $G$ 中共轭造成的差异商掉，完全是同一件事。证毕。 
]

接下来，我们用 $caron(H)^1_et (X, ul(G))$ 分类 $X$ 上的平展 $G$-主丛。 

#proposition(name: <cech-h1-classifies-torsors>)[
  设 $X$ 是连通 Noether 概形，$G$ 是有限交换群，则存在典范双射： 
  $
    {#[平展 $G$-主丛 $Y$，以 $X$ 为底]}/cong -> caron(H)^1_et (X, ul(G)) cong H^1_et (X, ul(G))
  $
]
#proof[
  第一步。正向映射的构造。 

  设 $p: Y -> X$ 是平展 $G$-主丛，其平凡化为 $Y times_X X_G -> Y times_X Y$。由 @fet-trivializes-fet-locally，$Y -> X$ 在平展局部上平凡。于是存在平展覆盖 $cal(U) = {U_i -> X}$，以及 $p_i: Y_i -> U_i$ 的截面 $s_i: U_i -> Y_i = U_i times_X Y$。这些截面 $s_i$ 通过下式把该主丛平凡化： 
  $
    psi_i: U_i times G -> Y_i, (u_i, g) |-> s_i (u_i) g 
  $
  这是同构：任取 $U_i$ 上一个位于 $X$ 的 $ol(x)$ 上方的几何点 $ol(u_i)$，取 $F_(ol(u_i))$ 之后，该映射成为： 
  $
    G -> F_(ol(u_i)) (Y_i) cong F_(ol(x)) (Y), g |-> s_i (ol(u_i)) g
  $ 
  由主丛条件，它是双射。 

  现在在每个交 $U_(i,j) = U_i times_X U_j$ 上，有相应的限制： 
  $
    psi^((1))_(i,j) = psi_i|_(U_(i,j) times G): U_(i,j) times G cong Y_(i,j) \
    psi^((2))_(i,j) = psi_j|_(U_(i,j) times G): U_(i,j) times G cong Y_(i,j)
  $
  此时 $(psi_(i,j)^((2)))^(-1) compose psi_(i,j)^((1)): U_(i,j) times G -> U_(i,j) times G$ 是 $G$-等变的 $U_(i,j)$-态射，因此它由某个局部常值函数 $U_(i,j) -> G$ 的右作用（即加法）给出，也就是说，对应于一个截面 $alpha_(i,j) in ul(G)(U_(i,j))$。 

  - ${alpha_(i,j)}$ 满足余圈条件。事实上，记 $psi_(i,j,k)^((1,2,3))$ 为 $psi_i, psi_j, psi_k$ 限制到 $U_(i,j,k) times G -> Y_(i,j,k)$ 所得的映射。则： 

    - $alpha_(i,j)|_(U_(i,j,k)) + alpha_(j,k)|_(U_(i,j,k))$ 对应于映射： #h(1fr)
      $
        (psi_(j,k)^((2)))^(-1)|_(U_(i,j,k) times G) compose psi_(j,k)^((1))|_(U_(i,j,k) times G) compose (psi_(i,j)^((2)))^(-1)|_(U_(i,j,k) times G) compose psi_(i,j)^((1))|_(U_(i,j,k) times G)
      $
      而它等于： 
      $
        (psi_(i,j,k)^((3)))^(-1) compose psi_(i,j,k)^((2)) compose (psi_(i,j,k)^((2)))^(-1) compose psi_(i,j,k)^((1)) = (psi_(i,j,k)^((3)))^(-1)  compose psi_(i,j,k)^((1))
      $
      也就是 $(psi_(i,k)^((2)))^(-1)|_(U_(i,j,k) times G) compose psi_(i,k)^((1))|_(U_(i,j,k) times G)$，它对应于 $alpha_(i,k)|_(U_(i,j,k))$。 

      于是得到余圈条件： 
      $
        alpha_(i,j)|_(U_(i,j,k)) + alpha_(j,k)|_(U_(i,j,k)) = alpha_(i,k)|_(U_(i,j,k))
      $
  
  因此 $(alpha_(i,j))$ 定义了 Čech 1-余圈，从而是 $caron(H)^1 (cal(U), ul(G))$ 中的一个类。于是我们得到类 $alpha in caron(H)^1 (X, ul(G))$。 

  - $alpha$ 与截面 $s_i$ 的选取无关。给定另一组截面 $s'_i: U_i -> Y_i$，它们定义平凡化： 
    $
      psi'_i: U_i times G -> Y_i
    $
    此时 $chi_i = psi'_i^(-1) compose psi_i: U_i times G -> U_i times G$ 是 $G$-等变的 $U_i$-态射，因而由某个局部常值函数 $U_i -> G$ 的右作用（即加法）确定，这个局部常值函数也就是一个截面 $h_i in ul(G)(U_i)$。 

    于是： 
    $
      (psi'_(i,j)^((2)))^(-1) compose psi'_(i,j)^((1)) = chi_j|_(U_(i,j) times G) compose (psi_(i,j)^((2)))^(-1) compose psi_(i,j)^((1)) compose chi_i^(-1)|_(U_(i,j) times G)
    $
    而由截面 ${s'_i}$ 定义的 $alpha'_(i,j) in ul(G)(U_(i,j))$ 满足： 
    $
      alpha'_(i,j) = alpha_(i,j) + h_j - h_i
    $
    于是 $(alpha'_(i,j)) - (alpha_(i,j)) = (h_j - h_i)_(i,j)$ 是 Čech 1-边缘，故 $(alpha'_(i,j))$ 与 $(alpha_(i,j))$ 在 $caron(H)^1 (cal(U), ul(G))$ 中诱导同一个类。 

  - 对于 $cal(U)$ 的加细 $cal(V) = {V_j -> X}$（由 $V_j -> U_(lambda(j))$ 给出），有 $Y'_j -> V_j$ 的截面 $t_j: V_j -> Y'_j = V_j times_X Y$，它们由 $s_(lambda(j))$ 作基变换得到。这些截面诱导平凡化： 
    $
      phi_j: V_j times G -> Y'_j
    $
    则 $(phi_(j_1,j_2)^((2)))^(-1) compose phi_(j_1,j_2)^((1))$ 是 $(psi_(lambda(j_1),lambda(j_2))^((2)))^(-1) compose psi_(lambda(j_1),lambda(j_2))^((1))$ 的基变换。因此由截面 $t_j$ 定义的 $(beta_(j_1,j_2))$ 满足： 
    $
      alpha_(lambda(j_1), lambda(j_2))|_(V_(j_1,j_2)) = beta_(j_1,j_2)
    $
    于是 $alpha in caron(H)^1 (cal(U), ul(G))$ 与 $beta in caron(H)^1 (cal(V), ul(G))$ 在定义 $caron(H)^1 (X, ul(G))$ 的正向极限中诱导同一个类。 

    任取两个平展覆盖，与一个能同时加细两者的新平展覆盖作比较，即知类 $alpha in caron(H)^1 (X, ul(G))$ 的构造与平凡化覆盖的选取无关。 

  把这个类记为 $alpha = alpha(Y) in caron(H)^1 (X, ul(G))$。至此定义了正向映射： 
  $
    {#[平展 $G$-主丛 $Y$，以 $X$ 为底]}/cong -> caron(H)^1_et (X, ul(G)), Y |-> alpha(Y)
  $

  第二步。反向映射的构造。 

  - 由于 $X$ 是 Noether 的，每个平展覆盖 $cal(U)$ 都可以被一个平展覆盖加细，后者只用到有限多个从 Noether 仿射平展 $X$-概形出发的映射。由层条件，把这些概形换成它们的不交并，并不改变 $caron(H)^1 (cal(U), ul(G))$。于是 
    $
      caron(H)^1 (X, ul(G)) = dirlim_(X' ->> X #[etale] \ X' #[noetherian]) caron(H)^1 ({X'}, ul(G))
    $

  给定类 $alpha in caron(H)^1 (X, ul(G))$，我们可以用如下元素表示它：
  $
    [alpha_(X')] in caron(H)^1 ({X'}, ul(G)) = (ker(ul(G)(X'') -> ul(G)(X''')))/(im(ul(G)(X') -> ul(G)(X'')))
  $
  其中 $alpha_(X') in ul(G)(X'')$。 

  令 $X'' = X' times_X X', X''' = X' times_X X' times_X X'$，则有投影： 
  $
    p_(12), p_(23), p_(13): X''' -> X''
  $
  我们如下定义 $X$ 上的平展 $G$-主丛 $Y$。取平凡 $G$-主丛 $X'_G = X' times G$，再定义一个同构： 
  $
    eta: X'_G times_X X' -> X' times_X X'_G
  $
  具体如下：把两边都等同于 $X''_G$，并用局部常值函数 $alpha_(X'): X'' -> G$ 的右作用（即加法）定义同构 $X''_G -> X''_G$。则 
  $
    alpha_(X')|_(p_(12)) + alpha_(X')|_(p_(23)) = alpha_(X')|_(p_(13))
  $
  恰好就是 $eta$ 的余圈条件。于是由相对仿射概形的 fpqc 下降，以及有限性与平展性在 fpqc 下降下的保持，存在有限平展映射 $Y -> X$，并有同构 $X' times_X Y cong X' times G$，且该同构的典范下降数据与 $eta$ 等同。 

  注意 $eta$ 是 $G$-等变的。由态射的 fpqc 下降，$Y$ 带有右 $G$-作用。此外，$Y times_X X_G -> Y times_X Y$ 基变换到 $X'$ 后是同构，故本身就是同构。因此 $Y$ 是 $X$ 上的平展 $G$-主丛，我们把它记为 $Y_alpha$。 

  - $Y_alpha$ 的同构类与代表元 $[alpha_(X')] in caron(H)^1 ({X'}, ul(G))$ 的选取无关。事实上，对另一个代表元 $tilde(alpha)_(X')$，存在 $beta in ul(G)(X')$ 使 $tilde(alpha)_(X') - alpha_(X') = beta|_(p_2) - beta|_(p_1)$。 

    $beta$ 通过加 $beta$ 诱导自同构 $psi: X'_G -> X'_G$。而 $tilde(alpha)_(X') - alpha_(X') = beta|_(p_2) - beta|_(p_1)$ 给出交换图表： 
    // https://q.uiver.app/#r=typst&q=WzAsNCxbMCwwLCJYJ19HIHRpbWVzX1ggWCciXSxbMCwxLCJYJ19HIHRpbWVzX1ggWCciXSxbMSwwLCJYJyB0aW1lc19YIFgnX0ciXSxbMSwxLCJYJyB0aW1lc19YIFgnX0ciXSxbMCwyLCJldGEiXSxbMSwzLCJ0aWxkZShldGEpIiwyXSxbMCwxLCJiZXRhIiwyXSxbMiwzLCJiZXRhIl1d
    #align(center, diagram({
      node((0, 0), [$X'_G times_X X'$])
      node((0, 1), [$X'_G times_X X'$])
      node((1, 0), [$X' times_X X'_G$])
      node((1, 1), [$X' times_X X'_G$])
      edge((0, 0), (1, 0), [$eta$], label-side: left, "->")
      edge((0, 1), (1, 1), [$tilde(eta)$], label-side: right, "->")
      edge((0, 0), (0, 1), [$beta$], label-side: right, "->")
      edge((1, 0), (1, 1), [$beta$], label-side: left, "->")
    }))
    也就是说，$beta$ 把由 $alpha_(X'), tilde(alpha)_(X')$ 定义的下降映射 $eta, tilde(eta): X'_G times_X X' -> X' times_X X'_G$ 缠绕起来。 
    
    由 fpqc 下降，$beta$ 下降为同构 $Y -> tilde(Y)$，它连接由 $alpha_(X'), tilde(alpha)_(X')$ 定义的两个 $X$ 上平展 $G$-主丛。由于 $beta$ 是 $G$-等变的，同构 $Y -> tilde(Y)$ 也是 $G$-等变的，从而是 $G$-主丛的同构。 

  - $Y_alpha$ 的同构类与 $X'$ 的选取无关。事实上，若另有平展覆盖 $tilde(X)' -> X$，其中 $tilde(X)'$ 是 Noether 的，并有加细 $tilde(X)' -> X'$，我们断言：由 $alpha_(X')$ 定义的平展 $G$-主丛 $Y$，与由 $alpha_(tilde(X)') = alpha_(X')|_(tilde(X)'')$ 定义的是同一个。 

    事实上，按定义，由 $alpha_(X')$ 定义的映射： 
    $
      eta: X'_G times_X X' -> X' times_X X'_G
    $
    沿 $tilde(X)'' -> X''$ 作基变换后，成为由 $alpha_(tilde(X)')$ 定义的映射： 
    $
      tilde(eta): tilde(X)'_G times_X tilde(X)' -> tilde(X)' times_X tilde(X)'_G
    $
    于是由 $eta$ 定义的 $Y$ 诱导出与 $tilde(eta)$ 相同的下降数据，故 $Y cong tilde(Y)$。 

  至此，我们由 $alpha in caron(H)^1 (X, ul(G))$ 构造出了 $X$ 上平展 $G$-主丛的一个良定义的同构类 $Y_alpha$。 

  第三步。这两个构造互为逆构造。 

  - 固定 $alpha in caron(H)^1 (X, ul(G))$，要证 $alpha(Y_alpha) = alpha$。 

    设 $alpha$ 由 $alpha_(X') in caron(H)^1 ({X'}, ul(G))$ 代表，其中 $X' ->> X$ 是平展覆盖，$X'$ 是 Noether 的。则按定义，$Y_alpha$ 有一个平凡化： 
    $
      psi: X' times G cong X' times_X Y_alpha
    $
    取出对应于 $1_G in G$ 的分支，得到截面 $s: X' -> X' times_X Y_alpha$，它直接给出平凡化 $psi$。于是： 
    $
      (psi|_(p_2))^(-1) compose psi|_(p_1): X''_G -> X''_G
    $
    它与下降数据 $eta: X'_G times_X X' -> X' times_X X'_G$ 等同，因此就是加 $alpha_(X') in ul(G)(X'')$ 所得。于是按定义 $alpha(Y_alpha) = [alpha_(X')] = alpha$。 

  - 对主丛 $Y$，适当加细平凡化覆盖，不妨设 $Y$ 由平展覆盖 $X' ->> X$ 平凡化，且 $X'$ 是 Noether 的，于是有 $psi: X' times_X Y cong X' times G$。映射： 
    $
      (psi|_(p_2))^(-1) compose psi|_(p_1): X''_G -> X''_G
    $
    它由局部常值函数 $alpha_(X') in ul(G)(X'')$ 代表。换言之，$Y$ 关于 $X' -> X$ 的典范下降数据同构于： 
    $
      eta: X'_G times_X X' -> X' times_X X'_G
    $
    后者由加 $alpha_(X')$ 构造。于是由 fpqc 下降，$Y cong Y_([alpha_(X')]) = Y_(alpha(Y))$。 

  分类至此完成。从 $caron(H)^1_et$ 到 $H^1_et$ 的同构来自 @h1-is-cech-h1。 
]

#theorem(name: <h1-of-const-sheaf>)[
  设 $X$ 是连通 Noether 概形。对任意有限交换群 $G$，存在典范同构： 
  $
    H^1_et (X, ul(G)) cong Hom_#[cont] (pi_1^et (X, ol(x)), G)
  $
]
#proof[
  注意 $G$ 作为交换群，共轭作用是平凡的。于是由 @hom-from-pi1-classifies-torsors 与 @cech-h1-classifies-torsors，得到双射： 
  $
    Hom_#[cont] (pi_1^et (X, ol(x)), G) ->^tilde {#[平展 $G$-主丛 $Y$，以 $X$ 为底]}/cong ->^tilde caron(H)^1 (X, ul(G)), rho |-> c_rho
  $
  还需说明这是交换群同态。为此，我们给出该映射的一个显式描述。 

  - 取 $rho in Hom_#[cont] (pi_1^et (X, ol(x)), G)$，设 $N <= pi_1^et (X, ol(x))$ 是包含于 $ker(rho)$ 的有限指数开子群。则 $N$ 对应于 Galois 覆叠 $(X', ol(x')) -> (X, ol(x))$，使得 $rho$ 穿过有限商 $Q = Aut(X'\/X)$ 分解为 $rho_Q: Q -> G$。 

    另一方面，设 $Y_rho$ 是 $rho$ 对应的 $G$-主丛。按构造，$F_(ol(x)) (Y_rho) cong G_rho$ 上带有由 $rho$ 给出的左 $pi_1^et (X, ol(x))$-作用，以及右正则 $G$-作用。 

    现在 $X' -> X$ 把 $Y_rho$ 平凡化。事实上， 
    $
      F_(ol(x)) (X' times_X Y) cong F_(ol(x)) (X') times F_(ol(x)) (Y) cong Q times G_rho = union.sq.big_(g in G) {(q, rho_Q (q) + g)}
    $
    它分成若干同构于 $Q$ 的左 $Q$-轨道（即 $pi_1^et (X,ol(x))$-轨道），从而诱导平凡化： 
    $
      phi: X' times G -> X' times_X Y
    $
    它在 $F_(ol(x))$ 上是： 
    $
      Q times G -> Q times G_rho, (q, g) |-> (q, rho_Q (q) + g)
    $

    设 $p_(1,2): X'' -> X'$ 是投影。接下来要考虑由下式代表的局部常值函数： 
    $
      (phi|_(p_2))^(-1) compose phi|_(p_1): X'' times G -> X'' times G
    $
    在 $F_(ol(x))$ 上，这个映射是： 
    $
      Q times Q times G &-> Q times Q times G \
      (q_1, q_2, g) &|-> (q_1, q_2, g + rho_Q (q_1)) |-> (q_1, q_2, g + rho_Q (q_1) - rho_Q (q_2))
    $
    即加上元素 $rho_Q (q_1) - rho_Q (q_2) in G$。于是对 $q_1, q_2 in Q$，$c_rho in caron(H)^1 (X, ul(G))$ 由类 $alpha_rho in ul(G)(X'')$ 代表，也就是一个局部常值函数 $alpha_rho: X'' = X' times_X X' -> G$，由下式刻画： 
    $
      alpha_rho (q_1 ol(x'), q_2 ol(x')) = rho_Q (q_1) - rho_Q (q_2)
    $
    由于 $X''$ 的每个连通分支都含有位于 $ol(x)$ 上方的一个几何点，这个等式唯一地刻画了 $alpha_rho: X'' = X' times_X X' -> G$。 

    总结如下： 

    - 类 $c_rho$ 由 $alpha_rho in ul(G)(X'')$ 代表，即由一个局部常值函数 $alpha_rho: X' times_X X' -> G$ 代表，它由下式唯一刻画： 
      $
        alpha_rho (q_1 ol(x'), q_2 ol(x')) = rho_Q (q_1) - rho_Q (q_2)
      $

    现在要证 $rho |-> c_rho$ 是加性的。给定 $rho_(1,2)$，取有限指数子群 $N subset ker(rho_1) inter ker(rho_2)$，上面的刻画立刻给出加性。 

  这样我们就构造出交换群同构： 
  $
    Hom_#[cont] (pi_1^et (X, ol(x)), G) ->^tilde caron(H)^1 (X, ul(G))
  $
  再与 @h1-is-cech-h1 中的同构 $caron(H)^1 (X, ul(G)) cong H^1_et (X, ul(G))$ 复合，便完成证明。 
]
