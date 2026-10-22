// audit-exception: 推论 4.9.9 证明中取直和的指标条件写在 #[...] 文字块内且含行内公式；审计把美元符号逐对匹配后，块内两段散文被切成伪公式段，翻译这两处必然改变数学指纹。公式本体与全部数学内容未动。
#import "void-import.typ": *
== 内 Hom 与张量 <sect-hom-tensor>

本节我们建立平展层的 Hom-张量对偶。 

#definition(name: <defn-etale-ring-and-module-sheaves>)[
  设 $X$ 是一个概形。所谓 $X$ 上的*平展环（预）层* (presheaf/sheaf of rings) $cal(A)$，指的是一个平展交换群（预）层 $cal(A) in cPAb(X_et)$ 或 $cAb(X_et)$，其中每个 $cal(A)(U)$ 都带有环结构，且这些结构与限制映射相容，即下图交换： 
  // https://q.uiver.app/#r=typst&q=WzAsNCxbMCwwLCJjYWwoQSkoVSkgdGltZXMgY2FsKEEpKFUpIl0sWzAsMSwiY2FsKEEpKFYpIHRpbWVzIGNhbChBKShWKSJdLFsxLDAsImNhbChBKShVKSJdLFsxLDEsImNhbChBKShWKSJdLFswLDIsInRpbWVzIl0sWzEsMywidGltZXMiLDJdLFswLDEsInJlc15VX1YgdGltZXMgcmVzXlVfViIsMV0sWzIsMywicmVzXlVfViIsMV1d
  #context align(center, diagram({
    node((-1, -1), [$cal(A)(U) times cal(A)(U)$])
    node((-1, 0), [$cal(A)(V) times cal(A)(V)$])
    node((0, -1), [$cal(A)(U)$])
    node((0, 0), [$cal(A)(V)$])
    edge((-1, -1), (0, -1), [$times$], label-side: left, "->")
    edge((-1, 0), (0, 0), [$times$], label-side: right, "->")
    edge((-1, -1), (-1, 0), [$res^U_V times res^U_V$], label-side: center, "->")
    edge((0, -1), (0, 0), [$res^U_V$], label-side: center, "->")
  }, crossing-fill: thm-box-curr-color()))

  给定 $X$ 上的平展环（预）层 $cal(A)$，所谓*平展 $cal(A)$-模（预）层* (presheaf/sheaf of modules) $cal(M)$，指的是一个平展交换群（预）层 $cal(M)$，其中每个 $cal(M)(U)$ 都带有 $cal(A)(U)$-模结构，且这些结构与限制映射相容，即下图交换： 

  // https://q.uiver.app/#r=typst&q=WzAsNCxbMCwwLCJjYWwoQSkoVSkgdGltZXMgY2FsKE0pKFUpIl0sWzAsMSwiY2FsKEEpKFYpIHRpbWVzIGNhbChNKShWKSJdLFsxLDAsImNhbChNKShVKSJdLFsxLDEsImNhbChNKShWKSJdLFswLDIsInRpbWVzIl0sWzEsMywidGltZXMiLDJdLFswLDEsInJlc15VX1YgdGltZXMgcmVzXlVfViIsMV0sWzIsMywicmVzXlVfViIsMV1d
  #context align(center, diagram({
    node((0, 0), [$cal(A)(U) times cal(M)(U)$])
    node((0, 1), [$cal(A)(V) times cal(M)(V)$])
    node((1, 0), [$cal(M)(U)$])
    node((1, 1), [$cal(M)(V)$])
    edge((0, 0), (1, 0), [$times$], label-side: left, "->")
    edge((0, 1), (1, 1), [$times$], label-side: right, "->")
    edge((0, 0), (0, 1), [$res^U_V times res^U_V$], label-side: center, "->")
    edge((1, 0), (1, 1), [$res^U_V$], label-side: center, "->")
  }, crossing-fill: thm-box-curr-color()))

  $cal(A)$-模的平展预层/层范畴记为 $cPAb(X_et, cal(A))$ 或 $cAb(X_et, cal(A))$。 
]

#example[
  - 从 $ul(ZZ)_X$-模层范畴到交换群层范畴的遗忘函子 $cAb(X_et, ul(ZZ)_X) -> cAb(X_et)$ 是范畴等价。事实上，这个拟逆可以构造出来：每个平展交换群层 $cal(F)$ 都能唯一地配备 $ul(ZZ)_X$-模层结构，具体如下： 
    $
      ul(ZZ)_X (U) times cal(F)(U) -> cal(F)(U), f, s |-> f s
    $
    其中 $f in ul(ZZ)_X (U)$ 是局部常值函数 $U -> ZZ$，于是 $f s$ 由粘合得到：把 $U$ 按划分 ${f^(-1)(n)}_(n in ZZ)$ 拆开，在每一块上取 $n s|_(f^(-1)(n))$，再拼起来。 

  - 同样地，从 $ul(ZZ\/n)$-模层到 $n$-挠层的遗忘函子 $cAb(X_et, ul(ZZ\/n)_X) -> cAb(X_et, ZZ\/n)$ 也是范畴等价。 
]

实际上，本文档中要用到的例子差不多就是这些。尽管如此，内 Hom (internal Hom) 与张量积的理论仍值得在一般情形下陈述一遍。 

#proposition[
  设 $X$ 是一个概形，$cal(A)$ 是 $X$ 上的平展环层。给定 $cal(M), cal(N) in cAb(X_et, cal(A))$，则预层： 
  $
    HHom_(cal(A)) (cal(M), cal(N)): Et_X^opp -> cAb, U |-> Hom_(cal(A)|_U) (cal(M)|_U, cal(N)|_U)
  $ 
  是平展的 $cal(A)$-模层。 
]
#proof[
  这个论证完全是形式化的，与 Zariski 层的层 Hom 论证一模一样，而且对一切景都成立，并不局限于平展景。 

  取 $U in Et_X$ 与平展覆盖 $cal(U) = {U_i -> U}_(i in I)$。 

  - 分离性：给定 $phi in Hom_(cal(A)|_U) (cal(M)|_U, cal(N)|_U)$，满足对每个 $i$ 都有 $phi|_(U_i) = 0$，则对任意 $V in Et_U$ 都有： 
    $
      phi_V (s)|_(U_i times_U V) = phi|_(U_i) (s|_(U_i times_U V)) = 0
    $
    于是由 $cal(N)$ 的分离性得 $phi_V (s) = 0$，从而 $phi = 0$。 

  - 粘合：给定彼此相容的 $phi_i in Hom_(cal(A)|_(U_i)) (cal(M)|_(U_i), cal(N)|_(U_i))$；对任意 $V in Et_U$，如下定义 $phi in Hom_(cal(A)|_U) (cal(M)|_U, cal(N)|_U)$： 
    $
      phi_V (s)|_(U_i times_U V) = phi_i (s|_(U_i times_U V))
    $
    再将上式右端的这些截面粘合起来，即得 $phi_V (s)$。由于 ${phi_i}$ 彼此相容，这些截面确实可以粘合；至于 $phi|_(U_i) = phi_i$，则是例行验证。 

  $cal(A)$-模结构是自然的。 
]

#definition(name: <defn-internal-hom>)[
  设 $X$ 是一个概形，$cal(A)$ 是 $X$ 上的平展环（预）层。给定 $cal(M), cal(N) in cPAb(X_et, cal(A))$ 或 $cAb(X_et, cal(A))$，它们的*内 Hom*，也称*预层/层 Hom*，$HHom_(cal(A)) (cal(M), cal(N))$ 是由下式定义的 $cal(A)$-模（预）层： 
  $
    HHom_(cal(A)) (cal(M), cal(N)): Et_X^opp -> cAb, U |-> Hom_(cal(A)|_U) (cal(M)|_U, cal(N)|_U)
  $
]

下面我们定义张量积，并证明 Hom-张量对偶： 

#definition(name: <defn-sheaf-tensor-product>)[
  给定 $X$ 上的平展环预层 $cal(A)$ 与 $cal(M), cal(N) in cPAb(X_et, cal(A))$，定义它们的*预层张量积* (presheaf tensor product) 为如下 $cal(A)$-模预层： 
  $
    cal(M) otimes_(cal(A),cPSh) cal(N): Et_X^opp -> cAb, U |-> cal(M)(U) otimes_(cal(A)(U)) cal(N)(U)
  $

  给定 $X$ 上的平展环层 $cal(A)$ 与 $cal(M), cal(N) in cAb(X_et, cal(A))$，定义它们的*层张量积* (sheaf tensor product) 为如下 $cal(A)$-模层： 
  $
    cal(M) otimes_(cal(A)) cal(N) := (cal(M) otimes_(cal(A),cPSh) cal(N))^\#
  $
  即预层张量积的层化。 
]

#proposition(name: <hom-tensor-first-props>)[
  + 给定 $X$ 上的平展环预层 $cal(A)$ 与 $cal(N) in cPAb(X_et, cal(A))$，则对任意 $cal(M), cal(P) in cPAb(X_et, cal(A))$ 都存在自然同构： #h(1fr)
    $
      HHom_(cal(A)) (cal(M), HHom_(cal(A)) (cal(N), cal(P))) cong HHom_(cal(A)) (cal(M) otimes_(cal(A),cPSh) cal(N), cal(P))
    $
    特别地，取整体截面得到： 
    $
      Hom_(cal(A)) (cal(M), HHom_(cal(A)) (cal(N), cal(P))) cong Hom_(cal(A)) (cal(M) otimes_(cal(A),cPSh) cal(N), cal(P))
    $
    因此张量积 $- otimes_(cal(A),cPSh) cal(N)$ 是 $HHom_(cal(A)) (cal(N), -): cPAb(X_et, cal(A)) -> cPAb(X_et, cal(A))$ 的左伴随。 

  + 给定 $X$ 上的平展环层 $cal(A)$ 与 $cal(N) in cAb(X_et, cal(A))$，则对任意 $cal(M), cal(P) in cAb(X_et, cal(A))$ 都存在自然同构： #h(1fr)
    $
      HHom_(cal(A)) (cal(M), HHom_(cal(A)) (cal(N), cal(P))) cong HHom_(cal(A)) (cal(M) otimes_(cal(A)) cal(N), cal(P))
    $
    特别地，取整体截面得到： 
    $
      Hom_(cal(A)) (cal(M), HHom_(cal(A)) (cal(N), cal(P))) cong Hom_(cal(A)) (cal(M) otimes_(cal(A)) cal(N), cal(P))
    $
    因此张量积 $- otimes_(cal(A)) cal(N)$ 是 $HHom_(cal(A)) (cal(N), -): cAb(X_et, cal(A)) -> cAb(X_et, cal(A))$ 的左伴随。 
]
#proof[
  这个证明同样只是形式论证，细节不一一写出： 
  
  (1) 把 $cal(A), cal(M), cal(N), cal(P)$ 换成 $cal(A)|_U, cal(M)|_U, cal(N)|_U, cal(P)|_U$，便知只需证明下述结论： 
  $
    Hom_(cal(A)) (cal(M), HHom_(cal(A)) (cal(N), cal(P))) cong Hom_(cal(A)) (cal(M) otimes_(cal(A),cPSh) cal(N), cal(P))
  $
  现在： 
  $
    & Hom_(cal(A)) (cal(M), HHom_(cal(A)) (cal(N), cal(P))) \
    =& {{phi_U in Hom_(cal(A)(U)) (cal(M)(U), Hom_(cal(A)|_U) (cal(N)|_U, cal(P)|_U))}_(U in Et_X) #[与限制相容]} \
    =& {{phi_U in Hom_(cal(A)(U)) (cal(M)(U), Hom_(cal(A)(U)) (cal(N)(U), cal(P)(U)))}_(U in Et_X) #[与限制相容]} \
    =& {{phi_U in Hom_(cal(A)(U)) (cal(M)(U) otimes_(cal(A)(U)) cal(N)(U), cal(P)(U))}_(U in Et_X) #[与限制相容]} \
    =& Hom_(cal(A)) (cal(M) otimes_(cal(A),cPSh) cal(N), cal(P))
  $ 
  这个推导中只有第三行需要解释：存在自然映射： 
  $
    & {{phi_U in Hom_(cal(A)(U)) (cal(M)(U), Hom_(cal(A)|_U) (cal(N)|_U, cal(P)|_U))}_(U in Et_X) #[与限制相容]} \
    ->& {{psi_U in Hom_(cal(A)(U)) (cal(M)(U), Hom_(cal(A)(U)) (cal(N)(U), cal(P)(U)))}_(U in Et_X) #[与限制相容]}
  $
  它就是由取整体截面得到的映射。其逆映射如下给出：给定 ${psi_U in Hom_(cal(A)(U)) (cal(M)(U), Hom_(cal(A)(U)) (cal(N)(U), cal(P)(U)))}_(U in Et_X) #[与限制相容]$，取： 
  $
    phi_U (s in cal(M)(U)): cal(N)(V) &-> cal(P)(V), V in Et_U \
    t &|-> psi_V (s|_V) (t|_V)
  $
  两者互逆，验证是例行而形式化的。于是证毕。 

  (2) 同样地，只需证明伴随关系。不过，由预层情形的伴随关系以及层化： 
  $
    Hom_(cal(A)) (cal(M), HHom_(cal(A)) (cal(N), cal(P))) &cong Hom_(cal(A)) (cal(M) otimes_(cal(A),cPSh) cal(N), cal(P)) \
    &cong Hom_(cal(A)) ((cal(M) otimes_(cal(A),cPSh) cal(N))^\#, cal(P)) \
    &= Hom_(cal(A)) (cal(M) otimes_(cal(A)) cal(N), cal(P))
  $
  证毕。 
]

接下来我们研究 $f_*$ 与 $f^(-1)$ 这类函子同 Hom、张量积的相互作用。 

#proposition[
  设 $f: X -> Y$ 是概形态射，$cal(A)$ 是 $Y$ 上的平展环层。 
  
  + 对任意 $cal(F) in cAb(X_et, f^(-1)cal(A)), cal(G) in cAb(Y_et, cal(A))$，都有自然同构： #h(1fr)
    $
      f_* HHom_(f^(-1) cal(A)) (f^(-1) cal(G), cal(F)) cong HHom_(cal(A)) (cal(G), f_* cal(F))
    $

  + 对任意 $cal(F), cal(G) in cAb(Y_et, cal(A))$，都有自然同构： 
    $
      f^(-1) cal(F) otimes_(f^(-1) cal(A)) f^(-1) cal(G) cong f^(-1) (cal(F) otimes_(cal(A)) cal(G))
    $

  + 若 $f$ 平展，则对任意 $cal(F) in cAb(X_et, f^(-1)cal(A)), cal(G) in cAb(Y_et, cal(A))$，都有自然同构： 
    $
      f_* HHom_(f^(-1) cal(A)) (cal(F), f^(-1) cal(G)) cong HHom_(cal(A)) (f_! cal(F), cal(G))
    $

  + （投影公式）若 $f$ 平展，则对任意 $cal(F) in cAb(X_et, f^(-1) cal(A)), cal(G) in cAb(Y_et, cal(A))$，都有自然同构： 
    $
      f_! (f^(-1) cal(G) otimes_(f^(-1) cal(A)) cal(F)) cong cal(G) otimes_(cal(A)) f_! cal(F)
    $

  
]
#proof[
  (1) 与 (3) 可以逐截面验证，实际上归结为 $f_*$ 与 $f^(-1)$ 的伴随关系，以及 $f^(-1)$ 与 $f_!$ 的伴随关系。 

  (2) 可以用 Yoneda 引理与 (1) 来验证： 
  $
    Hom_(f^(-1) cal(A)) (f^(-1) cal(F) otimes_(f^(-1) cal(A)) f^(-1) cal(G), cal(R)) &= Hom_(f^(-1) cal(A)) (f^(-1) cal(F), HHom_(f^(-1) cal(A)) (f^(-1) cal(G), cal(R))) \
    &= Hom_(cal(A)) (cal(F), f_* HHom_(f^(-1) cal(A)) (f^(-1) cal(G), cal(R))) \
    &= Hom_(cal(A)) (cal(F), HHom_(cal(A)) (cal(G), f_* cal(R))) \
    &= Hom_(cal(A)) (cal(F) otimes_(cal(A)) cal(G), f_* cal(R)) \
    &= Hom_(f^(-1) cal(A)) (f^(-1) (cal(F) otimes_(cal(A)) cal(G)), cal(R))
  $

  (4) 存在典范态射： 
  $
    f_! (f^(-1) cal(G) otimes_(f^(-1) cal(A)) cal(F)) -> cal(G) otimes_(cal(A)) f_! cal(F)
  $
  它由 $f^(-1) cal(G) otimes_(f^(-1) cal(A)) cal(F) -> f^(-1) cal(G) otimes_(f^(-1) cal(A)) f^(-1) f_! cal(F) = f^(-1) (cal(G) otimes_(cal(A)) f_! cal(F))$ 经伴随得到（其中最后一个同构由 (2) 给出）。这个态射是同构，只需在茎上验证，而这由 (2) 与 @etale-lower-shriek-first-props 给出： 
  $
    (f_! (f^(-1) cal(G) otimes_(f^(-1) cal(A)) cal(F)))_(ol(x)) &= oplus.big_(ol(u) in f^(-1)(ol(x))) (f^(-1) cal(G) otimes_(f^(-1) cal(A)) cal(F))_(ol(u)) = oplus.big_(ol(u) in f^(-1)(ol(x))) cal(G)_(f(ol(u))) otimes_(cal(A)_(f(ol(u)))) cal(F)_(ol(u)) \
    &= cal(G)_(ol(x)) otimes_(cal(A)_(ol(x))) oplus.big_(ol(u) in f^(-1)(ol(x))) cal(F)_(ol(u)) \
    &= cal(G)_(ol(x)) otimes_(cal(A)_(ol(x))) (f_! cal(F))_(ol(x)) = (cal(G) otimes_(cal(A)) f_! cal(F))_(ol(x))
  $
]

最后我们处理平坦对象。 
#lemma[
  设 $X$ 是一个概形，$cal(A)$ 是 $X$ 上的平展环层。若对 $X$ 的每个几何点 $ol(x)$，$cal(M)_(ol(x))$ 都是平坦的 $cal(A)_(ol(x))$-模，则 $cal(M) in cAb(X_et, cal(A))$ 是平坦对象。 
]
#proof[
  给定 $cAb(X_et, cal(A))$ 中的单射 $cal(F) -> cal(G)$，需要验证 $cal(F) otimes_(cal(A)) cal(M) -> cal(G) otimes_(cal(A)) cal(M)$ 是单射。这可以在茎上验证：由于 $cal(M)_(ol(x))$ 是平坦的 $cal(A)_(ol(x))$-模，$cal(F)_(ol(x)) otimes_(cal(A)_(ol(x))) cal(M)_(ol(x)) -> cal(G)_(ol(x)) otimes_(cal(A)_(ol(x))) cal(M)_(ol(x))$ 是单射。 
]

#corollary(name: <flat-resolution-of-et-sheaf>)[
  设 $X$ 是一个概形，$cal(A)$ 是 $X$ 上的平展环层。对每个 $(f: U -> X) in Et_X$，$f_! f^(-1) cal(A)$ 都是 $cAb(X_et, cal(A))$ 中的平坦对象。特别地，$cAb(X_et, cal(A))$ 有足够多的平坦对象。 
]
#proof[
  我们先验证： 
  $
    (f_! f^(-1) cal(A))_(ol(x)) = oplus.big_(ol(u) in f^(-1)(ol(x))) (f^(-1) cal(A))_(ol(u)) = cal(A)_(ol(x))^(oplus f^(-1)(ol(x)))
  $
  是自由的 $cal(A)_(ol(x))$-模，从而平坦。 

  对任意 $cal(M) in cAb(X_et, cal(A))$，都存在从某个平坦 $cal(A)$-模到它的满射，构造如下： 
  $
    oplus.big_((f: U -> X) in Et_X \ #[$U$ 仿射 \ $exists V subset X$ 仿射，$f(U) subset V$]) oplus.big_(s in cal(M)(f)) f_! f^(-1) cal(A) -> cal(M)
  $
  其中对该直和的每个指标 $(f, s)$，态射 $f_! f^(-1) cal(A) -> cal(M)$ 由 $f^(-1) cal(A) -> f^(-1) cal(M)$ 经伴随得到，而后者由 $f^(-1) cal(M)$ 的整体截面 $s$ 定义。于是 $s in cal(M)(f)$ 落在这个 $f_! f^(-1) cal(A) -> cal(M)$ 的像中。由于 $Et_X$ 的每个对象都能被 $Et_X$ 中这样的对象覆盖：$f: U -> X$，其中 $U$ 仿射、$f(U)$ 含于 $X$ 的某个仿射开集，所以这个态射是满射，而它的左边是平坦对象的直和，从而是平坦对象。 

  #remark[
    直和中之所以要对 $f in Et_X$ 加以限制，是为了避开集合论上的困难，详见 @set-categorical-subtleties。 
  ]
]
