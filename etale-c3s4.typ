// audit-exception: construction 环境的三处公式在方括号文本块内含行内公式，审计把美元符号逐个配对后会把块内散文切成伪公式段，故翻译这些散文必然改变数学指纹；公式本体未改动。
#import "void-import.typ": *
== $pi_1^et$ 的基本性质与例子

下面介绍平展基本群的初步性质。

#properties[
  + （对 $ol(x)$ 的依赖）对另一个几何点 $ol(x'): Spec(Omega') -> X$，存在自然同构（即一条路径）$eta: F_(ol(x)) -> F_(ol(x'))$，它诱导出连续同构：
    $
      pi_1^et (X, ol(x)) cong pi_1^et (X, ol(x'))
    $
    路径 $eta$ 的选取并不唯一，但由此得到的同构 $pi_1^et (X, ol(x)) cong pi_1^et (X, ol(x'))$ 彼此只差一个共轭（即 $pi_1^et (X, ol(x))$ 的内自同构）。
    #proof[
      不同的 $eta$ 给出的同构只差一个内自同构，这纯粹是形式推导：设有两条不同的路径 $eta, eta': F_(ol(x)) -> F_(ol(x'))$，则 $gamma := eta^(-1) compose eta' in Aut(F_(ol(x))) = pi_1^et (X, ol(x))$。现在对 $pi_1^et (X, ol(x))$ 中任意元素 $delta$，由 $eta'$ 定义的同构把它送到：
      $
        eta' compose delta compose (eta')^(-1) = eta compose (gamma delta gamma^(-1)) compose eta^(-1)
      $
      它和由 $eta$ 定义的同构只差 $pi_1^et (X, ol(x))$ 的一个内自同构。

      剩下要证的是路径确实存在，即存在自然同构 $eta: F_(ol(x)) -> F_(ol(x'))$。我们先在 $FEt_X$ 的满子范畴，也就是由 Galois 覆叠空间构成的那个范畴上构造 $eta$。
      
      设 ${(X_i, ol(x_i))}_(i in I)$ 是 $(X, ol(x))$ 的带基点 Galois 覆叠构成的正向系统。假定给出一族几何点 ${ol(x'_i) in F_(ol(x'))(X_i)}_(i in I)$，则可定义映射：
      $
        eta_i: F_(ol(x)) (X_i) -> F_(ol(x')) (X_i), sigma(ol(x_i)) |-> sigma(ol(x'_i)), forall sigma in Aut(X_i\/X)
      $
      由于 $Aut(X_i\/X)$ 作用在 $ol(x_i)$ 与 $ol(x'_i)$ 上，分别给出到 $F_(ol(x)) (X_i)$ 与 $F_(ol(x')) (X_i)$ 的双射，故对每个 $i$ 构造出的这个映射都是双射。

      接着考察：要让这族映射 ${eta_i}_(i in I)$ 是自然的（相对于 $(X, ol(x))$ 的带基点 Galois 覆叠之间的态射），需要对 ${ol(x'_i)}_(i in I)$ 施加什么要求。对每个态射 $f_(i,j): (X_j, ol(x_j)) -> (X_i, ol(x_i))$，要求：
      $
        eta_i (f_(i,j) (ol(y))) = f_(i,j) (eta_j (ol(y))), forall ol(y) in F_(ol(x)) (X_j)
      $
      等价地，
      $
        eta_i (f_(i,j) (sigma_j (ol(x_j)))) = f_(i,j) (eta_j (sigma_j (ol(x_j)))), forall sigma_j in Aut(X_j\/X)
      $
      设 $sigma_j |-> sigma_i$ 是 $f_(i,j)$ 诱导的映射 $Aut(X_j\/X) -> Aut(X_i\/X)$。现在右端是 $f_(i,j) (eta_j (sigma_j (ol(x_j)))) = f_(i,j) (sigma_j (ol(x'_j))) = sigma_i (f_(i,j) (ol(x'_j)))$，左端是 $eta_i (f_(i,j) (sigma_j (ol(x_j)))) = eta_i (sigma_i (ol(x_i))) = sigma_i (ol(x'_i))$。换言之，上述对所有 $i<=j$ 的自然性条件等价于：
      $
        f_(i,j) (ol(x'_j)) = ol(x'_i), forall i <= j
      $
      即
      $
        (ol(x'_i))_(i in I) in invlim_(i in I) F_(ol(x')) (X_i)
      $
      其中这个逆向系统中的映射由 $f_(i,j): X_j -> X_i$ 诱导。我们断言这样的相容点族 $(ol(x'_i))_(i in I)$ 存在，即逆向极限 $invlim_(i in I) F_(ol(x')) (X_i)$ 非空。这源于下面这个集合论事实：
      #lemma[
        非空有限集带上满射过渡映射，其逆向极限必非空。
      ]
      #proof[
        设 ${X_i}_(i in I)$ 是非空有限集的一个逆向极限，过渡映射为 $f_(i,j): X_j -> X_i$。这个逆向极限是子集：
        $
          invlim_(i in I) X_i = {(x_i)_(i in I) in product_(i in I) X_i : f_(i,j)(x_j) = x_i, forall i<=j} = inter.big_(i<=j) C_(i,j)
        $
        其中：
        $
          C_(i,j) = {(x_i)_(i in I) in product_(i in I) X_i : f_(i,j)(x_j) = x_i}
        $
        给每个 $X_i$ 装上离散拓扑，给 $product_(i in I) X_i$ 装上积拓扑。每个 $X_i$ 都紧（因为有限），故由 Tychonoff 定理，$product_(i in I) X_i$ 必紧。$C_(i,j)$ 是 $X_i times X_i$ 的对角线在映射 $product_(i in I) X_i -> X_i times X_i, (x_i)_(i in I) |-> (x_i, f_(i,j) (x_j))$ 下的原像。由于 $X_i times X_i$ 离散，对角线是闭的，故 $C_(i,j)$ 在 $product_(i in I) X_i$ 中闭。

        既然 $product_(i in I) X_i$ 紧，要证这些闭集 $C_(i,j)$ 的交非空，只需证明其中任意有限个的交非空。设 $i_1 <= j_1, dots.c, i_t <= j_t$ 是有限多对，取 $j_1, dots.c, j_t$ 的一个上界 $k$。由于 $X_k$ 非空，任取 $x_k in X_k$，再取 $(x_i)_(i in I)$，使得当 $i<=k$ 时 $x_i = f_(i,k)(x_k)$（其余的 $x_i$ 随意取）。于是容易看出 $(x_i)_(i in I) in inter.big_(s=1)^t C_(i_s,j_s)$。至此证毕。
        #suppress-qed
      ]
      由于每个 $F_(ol(x')) (X_i)$ 都非空，这样的相容选取 $(ol(x'_i))_(i in I)$ 存在。换言之，我们构造出了自然双射：
      $
        eta_i : F_(ol(x)) (X_i) -> F_(ol(x')) (X_i)
      $
      设 $Z in FEt_X$ 是 Galois 覆叠。假定有 $X$ 上的同构 $Z cong X_i$，并忘掉 $X_i$ 的带基点结构。则定义 $eta_Z : F_(ol(x)) (X_i) -> F_(ol(x')) (X_i)$ 为 $eta_i$。这个定义与 $i$ 的选取无关：换一个 $j$ 就对应一个同构 $(X_i, ol(x_i)) -> (X_j, ol(x_j))$，而 ${eta_i}$ 的自然性给出同样的 $eta_Z$。${eta_Z}$ 的自然性则由 ${eta_i}$ 的自然性推出。这样我们就在 $FEt_X$ 中由 Galois 覆叠构成的满子范畴上定义了 $eta$。

      从 Galois 覆叠过渡到一般覆叠的剩余论证，与 @pi1et-as-invlim 证明的最后一段完全相同。所以你要是愿意，剩下的证明可以跳过。

      最后，对任意的覆叠 $Y in FEt_X$，取 Galois 覆叠 $f: Z -> Y$，然后定义：
      $
        eta_Y: F_(ol(x)) (Y) -> F_(ol(x')) (Y), f(ol(z)) |-> f(eta_Z (ol(z)))
      $

      - $eta_Y$ 良定义：假定 $ol(y) in F_(ol(x))(Y)$ 写成 $ol(y) = f(ol(z_1)) = f(ol(z_2))$，其中 $ol(z_1), ol(z_2) in F_(ol(y))(Z) subset F_(ol(x))(Z)$。由于 $Z\/X$ 是 Galois 的，由 @galois-theory-of-coverings (0)，$Z\/Y$ 也是 Galois 的，故存在 $sigma in Aut(Z\/Y)$ 使得 $ol(z_2) = sigma(ol(z_1))$。现在：
        $
          f(eta_Z (ol(z_2))) &= f(eta_Z (sigma(ol(z_1)))) \
          &= f(sigma(eta_Z (ol(z_1)))) #[由 $eta$ 的定义或自然性] \
          &= f(eta_Z (ol(z_1))) #[因为 $sigma in Aut(Z\/Y) $]
        $
        还要说明 $eta_Y$ 不依赖于 Galois 覆叠 $Z$ 的选取。取复合覆叠的 Galois 闭包，问题就归结为：在给定 $W ->^g Z ->^f Y -> X$ 时，用 Galois 覆叠 $W$ 与 $Z$ 定义的 $eta_Y$ 是同一个映射。按 $W$ 的定义：
        $
          f(g(ol(w))) |-> f(g(eta_W (ol(w))))
        $
        而按 $Z$ 的定义：
        $
          f(g(ol(w))) |-> f(eta_Z (g(ol(w))))
        $
        由 ${eta_Z}$ 在 Galois 覆叠之间的自然性，$g(eta_W (ol(w))) = eta_Z (g(ol(w)))$，证毕。

      - $eta_Y$ 是双射：由于 $eta_Z$ 是双射，$eta_Y$ 的像包含所有形如 $f(ol(z'))$ 的点，其中 $ol(z') in F_(ol(x'))(Z)$。而 $F_(ol(x')) (Z) -> F_(ol(x')) (Y)$ 是满射，故 $eta_Y$ 是满射。

        我们当然可以手工证明 $eta_Y$ 是单射。但不如直接搬出那条极其深刻的定理——同样大小的有限集之间的满射必是双射——然后收工。

      - ${eta_Y}$ 是自然的：给定 $FEt_X$ 中的态射 $g: Y_1 -> Y$，存在公共的 Galois 覆叠 $Z$：
        // https://q.uiver.app/#r=typst&q=WzAsNCxbMSwwLCJZIl0sWzIsMSwiWCJdLFsxLDIsIllfMSJdLFswLDEsIloiXSxbMywwLCJmIl0sWzMsMiwiZl8xIiwyXSxbMCwxXSxbMiwxXV0=
        #context align(center, diagram({
          node((0, -1), [$Y$])
          node((1, 0), [$X$])
          node((0, 1), [$Y_1$])
          node((-1, 0), [$Z$])
          edge((-1, 0), (0, -1), [$f$], label-side: left, "->")
          edge((-1, 0), (0, 1), [$f_1$], label-side: right, "->")
          edge((0, 1), (0, -1), [$g$], "->", label-side: center)
          edge((0, -1), (1, 0), "->")
          edge((0, 1), (1, 0), "->")
        }, spacing: 2em, crossing-fill: thm-box-curr-color()))
        则对任意的 $ol(y_1) = f_1 (ol(z)) in F_(ol(x)) (Y_1)$，
        $
          g(eta_(Y_1) (ol(y_1))) &= g(eta_(Y_1) (f_1 (ol(z)))) \
          &= g(f_1 (eta_Z (ol(z)))) #[由 $eta_(Y_1) $ 的定义] \
          &= f(eta_Z (ol(z))) \
          &= eta_Y (f(ol(z))) #[由 $eta_(Y) $ 的定义] \
          &= eta_Y (g(ol(y_1)))
        $
        自然性得证。

      最后还要验证由这样的 $eta$ 得到的同构 $pi_1^et (X, ol(x)) -> pi_1^et (X, ol(x'))$ 连续。然而，我们构造 $eta$ 时把 ${(X_i, ol(x'_i))}_(i in I)$ 实现成了 $(X, ol(x'))$ 的带基点 Galois 覆叠构成的正向系统，因此构造出的同构本质上是：
      $
        pi_1^et (X, ol(x)) cong invlim_(i in I) Aut(X_i\/X)^opp cong pi_1^et (X, ol(x')) 
      $
      换言之，由定理 @pi1et-as-invlim，$pi_1^et (X, ol(x))$ 与 $pi_1^et (X, ol(x'))$ 上的拓扑都由 $invlim_(i in I) Aut(X_i\/X)^opp$ 定义。这就给出该同构的连续性。
    ]
  
  + （函子性）给定带几何点的连通 Noether 概形之间的态射 $alpha: (X, ol(x)) -> (Y, ol(y))$，存在典范的连续群同态：
    $
      alpha_*: pi_1^et (X, ol(x)) -> pi_1^et (Y, ol(y))
    $
    使得下图交换：
    // https://q.uiver.app/#r=typst&q=WzAsNCxbMCwwLCJGRXRfWSJdLFsyLDAsIkZFdF9YIl0sWzAsMiwicGlfMSAoWSwgb3ZlcmxpbmUoeSkpXCItXCJjU2V0XlwiZi5jXCIiXSxbMiwyLCJwaV8xIChYLCBvdmVybGluZSh4KSlcIi1cImNTZXReXCJmLmNcIiJdLFswLDEsImFscGhhXigtMSkiXSxbMCwyLCJ0aWxkZSIsMl0sWzEsMywidGlsZGUiXSxbMiwzLCIoLSkgY29tcG9zZSBhbHBoYV8qIiwyXV0=
    #align(center, diagram({
      node((-1, -1), [$FEt_Y$])
      node((1, -1), [$FEt_X$])
      node((-1, 1), [$GSet(pi_1 (Y, ol(y)))^#[fin,cont]$])
      node((1, 1), [$GSet(pi_1 (X, ol(x)))^#[fin,cont]$])
      edge((-1, -1), (1, -1), [$alpha^(-1)$], label-side: left, "->")
      edge((-1, -1), (-1, 1), [$tilde$], label-side: right, "->")
      edge((1, -1), (1, 1), [$tilde$], label-side: left, "->")
      edge((-1, 1), (1, 1), [$(-) compose alpha_*$], label-side: right, "->")
    }, spacing: 2em))
    其中 $alpha^(-1)$ 把 $Y' -> Y$ 送到 $X times_Y Y' -> X$。
    #proof[
      由纤维积的泛性质，对任意 $Y' in FEt_Y$，
      $
        F_(ol(x)) (X times_Y Y') = F_(ol(y)) (Y')
      $
      /*
      由交换图表：
      // https://q.uiver.app/#r=typst&q=WzAsNixbMiwwLCJYIHRpbWVzX1kgWSciXSxbNCwwLCJZJyJdLFsyLDIsIlgiXSxbNCwyLCJZIl0sWzAsMiwiU3BlYyhPbWVnYSkiXSxbMCwwLCJGXyhvdmVybGluZSh4KSkgKFggdGltZXNfWSBZJykiXSxbNSwwXSxbNSw0XSxbNCwyLCJvdmVybGluZSh4KSIsMl0sWzIsMywiYWxwaGEiLDJdLFs0LDMsIm92ZXJsaW5lKHkpIiwyLHsiY3VydmUiOjR9XSxbMCwxXSxbMSwzXSxbMCwyXV0=
      #align(center, diagram(
        {
          node((0, -1), [$X times_Y Y'$])
          node((2, -1), [$Y'$])
          node((0, 1), [$X$])
          node((2, 1), [$Y$])
          node((-2, 1), [$Spec(Omega)$])
          node((-2, -1), [$F_(ol(x)) (X times_Y Y')$])
          edge((-2, -1), (0, -1), "->")
          edge((-2, -1), (-2, 1), "->")
          edge((-2, 1), (0, 1), [$ol(x)$], label-side: right, "->")
          edge((0, 1), (2, 1), [$alpha$], label-side: right, "->")
          edge((-2, 1), (2, 1), [$ol(y)$], label-side: right, "->", bend: -36deg)
          edge((0, -1), (2, -1), "->")
          edge((2, -1), (2, 1), "->")
          edge((0, -1), (0, 1), "->")
        },
        spacing: (2em, 2em),
      ))*/
      这诱导出自然同态：
      $
        alpha_*: Aut(F_(ol(x))) &-> Aut(F_(ol(y))) \
        gamma &|-> (gamma_(X times_Y Y'): F_(ol(y)) (Y') -> F_(ol(y)) (Y'))_(Y' in FEt_Y)
      $
      陈述中的交换图表由这个构造立得。
      
      连续性也不难：只需证对每个带基点 Galois 覆叠 $(Z, ol(z)) -> (Y, ol(y))$，如下映射
      $
        pi_1^et (X, ol(x)) ->^(alpha_*) pi_1^et (Y, ol(y)) ->> Aut(Z\/Y)
      $
      的核包含 $pi_1^et (X, ol(x))$ 的某个开子群。按 $alpha_*$ 的构造，这个核由那些在 $F_(ol(x)) (Z times_Y X) in GSet(pi_1^et (X, ol(x)))^#[fin,cont]$ 上平凡作用的元素 $sigma in pi_1^et (X, ol(x))$ 组成。由等价 $FEt_X cong GSet(pi_1^et (X, ol(x)))^#[fin,cont]$ 立知，它必包含 $pi_1^et (X, ol(x))$ 的某个开正规子群。
    ]
]

接下来回答这个问题：

- 从 $alpha^(-1): FEt_Y -> FEt_X$ 能读出多少关于 $alpha_*: pi_1^et (X, ol(x)) -> pi_1^et (Y, ol(y))$ 的信息？

注意 $FEt_X cong GSet(pi_1^et (X, ol(X)))^#[fin,cont]$。因此这实际上是在问：从群同态在“带群作用的有限集”范畴上诱导出的态射，能读出关于这个群同态的多少信息。

#construction[
  设 $alpha: G -> H$ 是有限群之间的同态，则可构造映射 $alpha^(-1): GSet(H)^#[fin] -> GSet(G)^#[fin]$。由初等论证可得：
  $
    alpha #[满射]
    & <==> #[$G$ 传递地作用在 $H$ 上] \
    & <==> #[$alpha^(-1) $ 把传递 $H$-集送到传递 $G$-集]
  $
  以及：
  $
    alpha #[平凡]
    & <==> #[$alpha^(-1) $ 把每个 $H$-集送到 $G$-作用平凡的 $G$-集]
  $
  还有：
  $
    & alpha #[单射] <==> #[存在 $G$-等变映射 $G\/ker(alpha) -> G$] \
    <==>& #[$forall T in GSet(G)^#[fin]$,  $exists S in GSet(H)^#[fin]$，以及 $G$-等变映射 $S_0 -> T$，其中 $S_0$ 是 $alpha^(-1)(S) $ 的某条 $G$-轨道]
  $
]

有了这个玩具例子，我们提出关于投射有限群的如下结果：
#lemma(name: <profin-grp-action-props>)[
  设 $G, H$ 是投射有限群，$alpha: G -> H$ 是连续同态，它诱导出函子 $alpha^(-1): GSet(H)^#[fin,cont] -> GSet(G)^#[fin,cont]$。则：

  + $alpha$ 是满射，当且仅当 $alpha^(-1)$ 把传递 $H$-集送到传递 $G$-集；

  + $alpha$ 是平凡同态，当且仅当 $alpha^(-1)$ 把每个 $H$-集送到作用平凡的 $G$-集；

  + $alpha$ 是单射，当且仅当：$forall T in GSet(G)^#[fin,cont]$，$exists S in GSet(H)^#[fin,cont]$，以及 $G$-等变映射 $S_0 -> T$，其中 $S_0$ 是 $alpha^(-1)(S)$ 的某条 $G$-轨道。

  + 再取第三个投射有限群 $K$ 与连续满同态 $beta: H -> K$。则：
  $
    G -> H -> K -> 1
  $
    在中间正合，当且仅当对每个传递的 $S in GSet(H)^#[fin,cont]$，下述两条彼此等价：$alpha^(-1)(S) in GSet(G)^#[fin,cont]$ 有被 $G$ 全体元素固定的点 $<==>$ 存在 $Q in GSet(K)^#[fin,cont]$ 使得 $S cong beta^(-1)(Q)$。
]
#proof[
  证明完全是初等的，与有限群情形类似。这里只证 (3)(4) 作示范，因为 (3)(4) 的陈述最长。

  (4) 设 $I = im(alpha)$，$H_0 = ker(beta)$。对对象 $T in GSet(G)^#[fin,cont]$，用 $rho_T$ 表示连续同态 $G -> Sym(T)$，其中 $Sym(T)$ 是 $T$ 上的置换群，是个有限群。

  于是可以把所提出的等价条件翻译成关于 $rho$ 的条件。给定传递的 $S in GSet(H)^#[fin,cont]$，不妨设 $S cong H\/H_1$，其中 $H_1$ 是 $H$ 的开子群：

  - $alpha^(-1) (S)$ 有不动点 $h H_1$，意思是 $h^(-1) I h subset H_1$。

  - 我们断言：存在 $Q in GSet(K)^#[fin,cont]$ 使得 $S cong beta^(-1) (Q)$，等价于 $H_0 subset ker(rho_S)$。事实上，若 $S cong beta^(-1) (Q)$，则 $Q$ 作为集合必与 $S$ 一一对应。于是 $S$ 上存在与其给定的 $H$-作用相容的 $K$-作用，等价于 $rho_S: H -> Sym(S)$ 穿过 $beta: H -> K$ 分解。

    若 $rho_S$ 分解为 $H ->^beta K -> Sym(S)$，则 $H_0 = ker(beta) subset ker(rho_S)$。反之，若 $H_0 subset ker(rho_S)$，则由 $beta: H ->> K$ 是满射，有 $K cong H\/H_0$，再由第一同构定理，$rho_S$ 穿过 $beta$ 分解。

  换言之，等价条件可以改述为：对每个开子群 $H_1 <= H$，
  $
    exists h, I subset h^(-1)H_1 h <==> H_0 subset ker(H -> Sym(H\/H_1)) = inter.big_(h in H) h^(-1)H_1 h
  $
  由于 $H_0 = ker(beta)$ 是正规子群，$H_0 subset inter.big_(h in H) h^(-1)H_1 h$ 就等价于 $H_0 subset H_1$。于是等价条件可改写为：
  $
    exists h, I subset h^(-1)H_1 h <==> H_0 subset H_1
  $
  当 $I = H_0$ 时，$I$ 自动正规，故 $exists h, I subset h^(-1)H_1 h$ 等价于 $I subset H_1$，而这个条件自动成立。

  反之，假定这个条件成立。特别地有 $I subset H_1 ==> H_0 subset H_1$。现在 $I$ 与 $H_0$ 都是 $H$ 的闭子群，而投射有限群的任何闭子群都是包含它的开子群的交。因此 $I supset H_0$。
  
  接下来只看开正规子群 $H_1$。此时条件变成：对 $H$ 的任意开正规子群 $H_1$，$H_0 subset H_1 ==> I subset H_1$。在投射有限群中，闭正规子群是包含它的开正规子群的交。于是取交得到 $H_0 supset I$。

  (3)（$==>$）设 $alpha$ 是单射，从而把 $G$ 等同于 $H$ 的闭子群（带子空间拓扑）。对每个 $T in GSet(G)^#[fin,cont]$，把 $T$ 换成它的一条 $G$-轨道，不妨设 $T$ 在 $G$ 下传递。再取 $T$ 中某个元素的稳定子群，不妨设作为 $G$-集有 $T cong G\/G_0$，其中 $G_0$ 是 $G$ 的有限指数子群，从而是开且闭的子群。

  由于 $G_0 <= G$ 开且闭，存在开且闭的子群 $H_0 <= H$ 使得 $G_0 = H_0 ∩ G$。$H_0$ 必为有限指数，故可取 $H$-集 $S = H\/H_0 in GSet(H)^#[fin,cont]$。考察类 $[1] in S = H\/H_0$ 的 $G$-轨道，由第二同构定理，
  $
    im(G -> H\/H_0) cong G\/(G ∩ H_0) = G\/G_0 cong T
  $
  作为 $G$-集。至此证毕。

  （$<==$）设 $ker(alpha) != {1}$，取元素 $1 != g in ker(alpha)$。由投射有限拓扑，存在 $G$ 的有限指数正规子群 $N$ 使得 $g in.not N$。令 $T = G\/N in GSet(G)^#[fin,cont]$。
  
  按假设，存在有限连续 $H$-集 $S$、它的一条 $G$-轨道 $S_0$，以及 $G$-等变态射：
  $
    phi: S_0 -> T = G\/N
  $
  由于 $G\/N$ 是传递 $G$-集，$phi(S_0)$ 作为 $G\/N$ 的 $G$-不变子集必等于 $G\/N$ 本身。也就是说，$phi$ 是满射。另一方面，$g in ker(alpha)$，故 $g$ 在 $S_0$ 上的作用等于 $alpha(g) = 1 in H$ 的作用，即 $g$ 平凡地作用在 $S_0$ 上。于是由 $phi$ 的 $G$-等变性，$g$ 平凡地作用在 $phi(S_0) = G\/N$ 上。特别地 $g N = N$，即 $g in N$，矛盾。

]

把这些代数结果翻译成平展覆叠空间的语言，就得到下面的结果；可与 @cite-lei-fu[Proposition 3.3.4] 对照：

#properties(name: <pi1et-mor-props>)[
  设 $alpha: (X, ol(x)) -> (Y, ol(y))$ 是带几何点的连通 Noether 概形之间的态射。

  + $alpha_*$ 是满射，当且仅当对任意连通的 $Y' in FEt_Y$，$X times_Y Y' in FEt_X$ 连通。
  
  + $alpha_*$ 是平凡同态，当且仅当对一切 $Y' in FEt_Y$，$X times_Y Y' in FEt_X$ 都是若干份 $X$ 的不交并。
  
  + $alpha_*$ 是单射，当且仅当对任意 $(Z -> X) in FEt_X$，都存在 $(W -> Y) in FEt_Y$ 以及 $FEt_X$ 中从 $X times_Y W$ 的某个连通分支到 $Z$ 的态射。

  + 再给定第三个概形 $(Z, ol(z))$ 与 $beta: (Y, ol(y)) -> (Z, ol(z))$，使得 $beta_*$ 是满射，则：
    $
      pi_1^et (X, ol(x)) ->^(alpha_*) pi_1^et (Y, ol(y)) ->^(beta_*) pi_1^et (Z, ol(z)) -> 1
    $
    正合，当且仅当对每个连通的 $Y' in FEt_Y$，$Y'$ 都是某个 $Z' in FEt_Z$ 的基变换，当且仅当 $X' = Y' times_Y X in FEt_X$ 有某个连通分支恰好就是 $X$。
  /*
  + $alpha_*$ 是满射，当且仅当 $alpha^(-1)$ 把传递 $pi_1 (Y)$-集送到传递 $pi_1 (X)$-集，当且仅当 $Y' in FEt_Y$ 连通 $==>$ $X times_Y Y' in FEt_X$ 连通。
  
  + $alpha_*$ 是平凡同态，当且仅当对一切 $Y' in FEt_Y$，$X times_Y Y' in FEt_X$ 都是若干份 $X$ 的不交并。
  
  + $alpha_*$ 是单射，当且仅当对任意 $T in GSet(pi_1 (X))^"f.c"$，存在传递的 $S in GSet(pi_1 (Y))^"f.c"$，以及从 $alpha_*^(-1) (S) -> T$ 中的一条 $pi_1 (X)$-轨道到 $T$ 的 $pi_1 (X)$-等变映射。这等价于：对任意 $(Z -> X) in FEt_X$，存在连通的 $(W -> Y) in FEt_Y$ 以及 $FEt_X$ 中的态射，从 $X times_Y W$ 的某个连通分支到 $Z$。*/
]
#proof[
  这只是把 @profin-grp-action-props (1)(2)(3)(4) 直接翻译过来：在等价 $F_(ol(x)): FEt_X -> GSet(pi_1^et (X, ol(x)))^#[fin,cont]$ 之下，有限连续 $pi_1^et (X, ol(x))$-集对应 $FEt_X$ 中的对象。具体对应如下：

  - $Z in FEt_X$ 连通，当且仅当 $F_(ol(x)) (Z)$ 传递；

  - $Z in FEt_X$ 平凡（即若干份 $X$ 的不交并），当且仅当 $F_(ol(x)) (Z)$ 上的 $pi_1^et (X, ol(x))$-作用平凡；

  - 取 $Z in FEt_X$ 的连通分支，等价于取 $F_(ol(x)) (Z)$ 的一条 $pi_1^et (X, ol(x))$-轨道。
]

借助 $pi_1^et$ 的函子性，可以得到各种办法来获取不同类型概形的 $pi_1^et$ 的信息。第一个要处理的情形，是使基域可分闭的基变换。

#corollary[
  设 $k$ 是域，固定一个可分闭包 $k^sep$。设 $X$ 是 $k$ 上有限型的几何连通概形#footnote[几何连通性的两种说法等价，这是 @cite-hartshorne-ag[Section II.4] 中的一道习题。]，即 $X_(k^sep) = X otimes_k k^sep$ 连通，或等价地，对每个域扩张 $L\/k$ 都有 $X_L = X otimes_k L$ 连通。
  
  固定几何点 $ol(x): Spec(k^sep) -> X_(k^sep) -> X -> Spec(k)$。则态射 $X_(k^sep) -> X -> Spec(k)$ 诱导出正合列：
  $
    1 -> pi_1^et (X_(k^sep), ol(x)) -> pi_1^et (X, ol(x)) -> underbrace(Gal(k^sep\/k), pi_1^et (Spec(k), Spec(k^sep))) -> 1
  $
]
#proof[
  右端正合性：
  #proof[
    要证 $pi_1^et (X, ol(x)) -> Gal(k^sep\/k)$ 是满射，用 @pi1et-mor-props (1)。$Spec(k)$ 的连通平展覆叠空间都形如 $Spec(L)$，其中 $L\/k$ 是有限可分扩张；而由几何连通性，$X_L = X otimes_k L$ 连通。于是 @pi1et-mor-props (1) 的条件全部满足。
    #suppress-qed
  ]

  中间的正合性：
  #proof[
    既已得到右端正合性，就可以用 @pi1et-mor-props (4)。

    给定 $Spec(L) in FEt_(Spec(k))$，即 $L\/k$ 是有限可分扩张，其基变换 $X_L times_X X_(k^sep) cong X times_k Spec(L) times_k Spec(k^sep) = X times_k union.sq.big_([L:k]) Spec(k^sep) = union.sq.big_([L:k]) X_(k^sep)$ 恰好是若干份 $X_(k^sep)$ 的不交并。

    反之，设 $X' in FEt_X$ 连通，且 $X'_(k^sep) = X' otimes_k k^sep = X' times_X X_(k^sep) in FEt_(X_(k^sep))$ 有某个连通分支恰好就是 $X_(k^sep)$。

    设 $C$ 是 $X'_(k^sep)$ 的这样一个连通分支，则在 $X_(k^sep)$ 上有 $C cong X_(k^sep)$。$Gal(k^sep\/k)$ 在 $X'_(k^sep)$ 上的自然作用置换其连通分支；又因 $X'$ 连通，这个作用是传递的。因此 $X'_(k^sep)$ 的每个连通分支在 $X_(k^sep)$ 上都是一份 $X_(k^sep)$。

    设 $H <= Gal(k^sep\/k)$ 是 $C$ 的稳定子群。连通分支只有有限多个，故 $H$ 是开的，于是 $L := (k^sep)^H$ 是 $k$ 的有限可分扩张。我们断言在 $X$ 上有 $X' cong X_L$。事实上，
    $
      X' otimes_k k^sep = X'_(k^sep) = union.sq.big_(Gal(k^sep\/k)\/H) X_(k^sep) cong X_L otimes_k k^sep
    $
    此外，$X'$ 与 $X_L$ 从 $X_(k^sep)$ 到 $X$ 的下降数据一致，这可以直接验证。于是由 @fpqc-descent-of-morphisms，$X' cong X_L$。

    #suppress-qed
  ]

  要证 $pi_1^et (X_(k^sep), ol(x)) -> pi_1^et (X, ol(x))$ 是单射，用 @pi1et-mor-props (3)。只需对连通的覆叠空间 $Z in FEt_(X_(k^sep))$ 验证 (3)。于是要证：存在 $W in FEt_X$ 与 $X_(k^sep) times_X W$ 的连通分支 $V$，以及态射 $V -> Z$。
   
  由于 $Z -> X_(k^sep)$ 有限平展，从而是有限展示的，故可下降到 $k^sep$ 内某个有限可分扩张 $L\/k$ 上：存在 $Z_L in FEt_(X_L)$，使得
  $
    Z cong Z_L times_(X_L) X_(k^sep)
  $
  在 $X_(k^sep)$ 上成立。把 $Z_L$ 经由 $Z_L -> X_L -> X$ 看作 $X$ 的有限平展覆叠，记为 $W$。则
  $
    X_(k^sep) times_X W = Z_L otimes_k k^sep.
  $
  由于 $L otimes_k k^sep cong union.sq.big_(Hom_k(L, k^sep)) k^sep$，这是 $Z$ 的各共轭的不交并，而对应于所选嵌入 $L subset k^sep$ 的那个分支恰好是 $Z$。取这个分支为 $V$，就得到所需的态射 $V cong Z -> Z$。
]

#remark[
  在上述正合列中：
  $
    1 -> pi_1^et (X_(k^sep), ol(x)) -> pi_1^et (X, ol(x)) ->^q underbrace(Gal(k^sep\/k), pi_1^et (Spec(k), Spec(k^sep))) -> 1
  $
  若 $y in X(k)$ 是 $X$ 的一个 $k$-点，则 $y_*: Gal(k^sep\/k) -> pi_1^et (X, ol(x))$ 是 $q$ 的一个截面，并且与 $pi_1$-共轭相容。
  
  有一个猜想说：若 $X$ 是所谓的“双曲”的，则这是得到 $q$ 的截面的唯一方式。这称为 Grothendieck 截面猜想。
]

下一个要处理的情形是计算正规概形的 $pi_1^et$。

#proposition(name: <p1et-of-normal-scheme>)[
  设 $X$ 是连通 Noether 正规概形，$K$ 是 $X$ 的函数域 $K(X)$，而泛点为
  $
    ol(eta): Spec(K^sep) -> Spec(K) ->^eta X
  $
  则诱导的态射
  $
    eta_*: underbrace(Gal(K^sep\/K), pi_1^et (Spec(K), Spec(K^sep))) -> pi_1^et (X, ol(eta))
  $
  是满射，其核为 $Gal(K^sep\/K^"ur" (X))$。这里 $K^sep\/K^"ur" (X)\/K$ 中间的域有两种等价的刻画：

  - $K^"ur" (X)$ 是所有满足下述条件的有限可分 $L\/K$ 的并：$X$ 在 $L$ 中的正规化 $X_L$（先验地，由 #cite-stacks("032L")[Lemma 10.161.8] 知它在 $X$ 上有限）在 $X$ 上平展；

  - $K^"ur" (X)$ 是 $K$ 的最大的可分代数扩张，使得对 $K^"ur" (X)$ 的每个有限子扩张 $L\/K$，$X$ 在 $L$ 中的正规化 $X_L$ 都在 $X$ 上平展。
  
  换言之，$eta_*$ 给出等同：
  $
    pi_1^et (X, ol(eta)) cong Gal(K^"ur" (X)\/K)
  $
]
这个命题原则上给出了计算 $pi_1^et (X)$ 的方法。但 $K$ 往往是某个熟悉域（比如有限域或数域）上超越次数很大的复杂域，$K^"ur" (X)$ 并不好算。尽管如此，在 $X$ 是局部域或整体域的整数环的谱这种典型情形下，这个命题是管用的。
#proof[
  由 @pi1et-mor-props (1)，$eta_*$ 是满射：对任意连通的 $Z in FEt_X$，由于 $X$ 正规、$Z\/X$ 平展，由 @etale-local-properties (5) 知 $Z$ 正规。由于 $Z$ 正规且连通，$Z$ 是整的。于是 $Z$ 在 $X$ 上的泛纤维 $Z_K := Z times_X Spec(K)$ 也是整的，从而连通。此时 $Z_K$ 在 $Spec(K)$ 上也平展，故必有 $Z_K = Spec(L)$，其中 $L = K(Z)\/K$ 是有限可分扩张。

  下面证明 $K^"ur" (X)$ 的两种刻画等价。只需证明：若 $M\/L\/K$ 是有限可分扩张，且 $X_M -> X$ 有限平展，则 $X_L -> X$ 必有限平展。

  - 设 $N$ 是 $M$ 的 Galois 闭包。若能证明 $X_N -> X$ 有限平展，则由 $X_L = X_N\/Gal(N\/L)$ 与 @galois-theory-of-coverings (2) 知 $X_L -> X$ 有限平展。
  
    设 $M_1, dots, M_r$ 是 $M$ 在 $K^sep$ 中的全体 Galois 共轭。每个 $X_(M_i)$ 都在 $X$ 上同构于 $X_M$，从而在 $X$ 上有限平展。因此 $X_(M_1) times_X dots times_X X_(M_r)$ 在 $X$ 上有限平展。由于作为 $K^sep$ 的子域有 $N = M_1 dots.c M_r$，$N$ 是 $M_1 otimes_K dots.c otimes_K M_r$ 的商，而后者是 Artin 环。
    
    现在说明 $M_1 otimes_K dots.c otimes_K M_r$ 既约。事实上，把它与 $N$ 作张量积得到：
    $
      (M_1 otimes_K N) otimes_N dots.c otimes_N (M_r otimes_K N)
    $
    每个 $M_i otimes_K N cong N^([M:K])$，故这个环是若干份 $N$ 的直积，从而是既约的。又 $Spec(N) -> Spec(K)$ 平展，故该环在 $M_1 otimes_K dots.c otimes_K M_r$ 上平展。于是由 @etale-local-properties (4)，$M_1 otimes_K dots.c otimes_K M_r$ 既约。因此 $Spec(N)$ 是 $Spec(M_1 otimes_K dots.c otimes_K M_r)$ 的一个连通分支。于是 $X_N$ 是 $X_(M_1) times_X dots times_X X_(M_r)$ 的连通分支，且在 $X$ 上有限平展。

  现在考察序列：
  $
    Gal(K^sep\/K^"ur" (X)) -> Gal(K^sep\/K) ->^(eta_*) pi_1^et (X, ol(eta)) -> 1
  $
  由 @pi1et-mor-props (4)，只需证明：对有限可分扩张 $L\/K$，存在 $Z in FEt_X$ 使 $L = K(Z)$，当且仅当 $L otimes_K K^"ur" (X)$ 是若干域的直积且其中一个因子为 $K^"ur" (X)$。而这个条件又等价于 $L subset K^"ur" (X)$。

  （$<==$）若 $L subset K^"ur" (X)$，则正规化 $X_L$ 已知在 $X$ 上有限，且按 $K^"ur" (X)$ 的定义是平展的。于是 $L = K(X_L)$。

  （$==>$）若对某个连通的 $Z in FEt_X$ 有 $L = K(Z)$，则由 @etale-local-properties (5) 知 $Z$ 正规。又 $Z -> X$ 有限，故 $Z$ 就是 $X$ 在 $K(Z)$ 中的正规化。按 $K^"ur" (X)$ 的定义，$K(Z) subset K^"ur" (X)$。
]

#example[
  // 该态射：
  // $
  //   Gal(QQ_p^sep\/QQ_p) ->> Gal(QQ_p^"ur"\/QQ_p) cong pi_1^et (Spec(ZZ_p))
  // $
  // 可以这样得到。
  设 $K$ 是局部域，$cal(O)_K$ 是其整数环。由上一个命题可知：
  $
    pi_1^et (Spec(cal(O)_K)) cong Gal(K^"ur"\/K)
  $
  而 $K$ 的剩余域 $k$ 是有限域。$K$ 的有限非分歧扩张完全由 $k$ 的有限扩张刻画，因此：
  $
    pi_1^et (Spec(cal(O)_K)) cong Gal(K^"ur"\/K) cong Gal(ol(k)\/k) cong hat(ZZ)
  $
]

#example[
  设 $K$ 是整体域，$U subset Spec(cal(O)_K)$ 是其整数环的谱的开子集。则由上一个命题可知：
  $
    pi_1^et (U) cong Gal(K_U^"ur"\/K)
  $
  其中 $K_U^"ur"$ 是 $K$ 相对于 $U$ 中的点（即素位）的最大非分歧扩张。
  
  #example[
    数域上的 Minkowski 界：
    $
      (4/pi)^(s_2) (n!)/(n^n) sqrt(abs("disc"(K))) >= 1
    $
    它表明对任意数域 $K != QQ$ 都有 $abs("disc"(K)) > 1$。于是对任意数域 $K != QQ$，$ZZ$ 总有某个素子在 $K$ 中分歧。这意味着下面这个群是平凡的：
    $
      pi_1^et (Spec(ZZ)) = 1
    $
  ]
]

最后再看一个情形：两条最简单的曲线（即 $PP^1$ 与椭圆曲线）的平展基本群。这两个情形可以直接用定义算出。

#example[
  设 $k$ 是代数闭域。回忆：对 $k$ 上光滑射影曲线之间的有限支配态射 $f: X -> Y$，若 $K(X)\/K(Y)$ 可分，则有单射态射
  $
    f^* Omega_(Y\/k) arrow.r.hook Omega_(X\/k)
  $
  它在泛点处的茎上是同构。于是 $cal(F) = Omega_(X\/k)\/f^* Omega_(Y\/k)$ 的支集是有限集。这个层称为分歧除子 (ramification divisor)。
  
  Riemann–Hurwitz 定理断言：设 $n = [K(X):K(Y)]$ 为 $f$ 的次数，则
  $
    2 - 2g(X) = n (2 - 2g(Y)) - deg(cal(F)),
  $
  其中 $deg(cal(F))$ 是分歧除子的次数。

  若 $Z -> X$ 是连通有限平展覆叠，且 $X$ 是 $k$ 上的非奇异曲线，则 $Z$ 自动是非奇异曲线（因为正规性是平展局部的）。平展态射都是非分歧的，故 Riemann–Hurwitz 在这里适用，给出：
  $
    2 - 2g(Z) = n (2 - 2g(X))
  $

  - 若 $X = PP^1_k$ 是射影直线，则 $g(X) = 0$。于是 $2 - 2g(Z) = 2n > 0$，故 $g(Z) = 0$ 且 $n = 1$。换言之，$PP^1_k$ 的唯一连通有限平展覆叠就是它自己。因此下面这个群是平凡的：
    $
      pi_1^et (PP^1_k) = 1
    $

  - 为简单起见再设 $k$ 的特征为 $0$，并取椭圆曲线 $X = E$。此时 $g(X) = 1$，故 $2 - 2g(Z) = 0$，$g(Z) = 1$。取原点 $0 in E(k)$ 上方的一点 $z in Z(k)$。以 $z$ 为原点使 $Z$ 成为椭圆曲线，而覆叠 $Z -> E$ 作为带基点的椭圆曲线态射，必是同态。于是 $E$ 的每个连通有限平展覆叠都是有限平展同源。反之，每个以 $E$ 为目标的有限平展同源都是这样的覆叠。

    由于 $"char"(k) = 0$，每个倍乘映射 $[n]: E -> E$ 都有限平展。这些映射以按整除关系排序的正整数为指标，构成 $(E, 0)$ 的带基点 Galois 覆叠的共尾系统。事实上，设 $f: (Z, z) -> (E, 0)$ 是 $d$ 次有限平展同源，其对偶同源 $hat(f): (E, 0) -> (Z, z)$ 满足：
    $
      f compose hat(f) = [d]: E -> E,
    $
    故 $[d]$ 支配 $f$。

    $[n]$ 的覆叠变换是沿 $E[n](k)$ 中的点所作的平移。若 $m = n s$，则从 $[m]$ 到 $[n]$ 的态射是 $[s]: E -> E$，诱导的过渡映射 $E[m](k) -> E[n](k)$ 是乘以 $s$。因此由 @pi1et-as-invlim 得到典范同构：
    $
      pi_1^et (E, 0) cong invlim_(n>=1) E[n](k) cong product_(ell) T_ell (E),
    $
    其中 $ell$ 取遍素数，而
    $
      T_ell (E) := invlim_(r>=1) E[ell^r](k).
    $
    这就是 Tate 模。由于 $k$ 的特征为 $0$，每个 $T_ell (E)$ 都（非典范地）是秩 $2$ 的自由 $ZZ_ell$-模。于是（非典范地）：
    $
      pi_1^et (E, 0) cong product_(ell) ZZ_ell^2 cong hat(ZZ)^2.
    $
]
