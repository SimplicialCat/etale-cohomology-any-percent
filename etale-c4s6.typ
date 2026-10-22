// audit-exception: 作者英文修正同步：加细改用 μ,λ 指代，原 “d” 改为 partial；中文相应改为“这两个加细”“该映射”。数学内容按英文修正。
#import "void-import.typ": *

== Čech 上同调

#construction(name: <constr-cech-cohom>)[
  设 $X$ 是概形。给定 $U in Et_X$ 以及平展覆盖 $cal(U) = {U_i -> U}_(i in I)$。记 $U_(i_0,dots.c,i_p) = U_(i_0) times_U dots.c times_U U_(i_p)$。 
  
  给定 $cal(G) in cPAb(X_et)$，定义 $cal(G)$ 关于 $cal(U)$ 的*Čech 复形*为如下上链复形： 
  $
    0 -> C^0 (cal(U), cal(G)) -> dots.c -> C^p (cal(U), cal(G)) ->^d C^(p+1) (cal(U), cal(G)) -> dots.c
  $
  其中各项取为： 
  $
    C^p (cal(U), cal(G)) = product_(i_0,dots.c,i_p in I) cal(G) (U_(i_0,dots.c,i_p))
  $
  微分取通常的形式： 
  $
    d: C^p (cal(U), cal(G)) &-> C^(p+1) (cal(U), cal(G)) \
    (s_(i_0, dots.c, i_p))_(i_0,dots.c,i_p) &|-> (sum_(k=0)^(p+1) (-1)^k s_(i_0,dots.c,cancel(i_k),dots.c,i_(p+1))|_(U_(i_0,dots.c,i_(p+1))))_(i_0,dots.c,i_(p+1))
  $
  于是，$cal(G)$ 关于 $cal(U)$ 的第 $p$ 次 *Čech 上同调*定义如下： 
  $
    caron(H)^p (cal(U), cal(G)) = h^p (0 -> C^bullet (cal(U), cal(G)))
  $
  与通常一样，给定从 $cal(U)$ 到 $cal(V)$ 的一个加细，就得到链映射： 
  $
    C^p (cal(U), cal(G)) &-> C^p (cal(V), cal(G)) \
    (s_(i_0,dots.c,i_p))_(i_0,dots.c,i_p) &|-> (s_(lambda(j_0),dots.c,lambda(j_p))|_(V_(j_0,dots.c,j_p)))_(j_0,dots.c,j_p)
  $
  它诱导映射 $caron(H)^p (cal(U), cal(G)) -> caron(H)^p (cal(V), cal(G))$。 
  #lemma[
    给定从 $cal(U)$ 到 $cal(V)$ 的两个不同加细，它们诱导的链映射 $C^bullet (cal(U), cal(G)) -> C^bullet (cal(V), cal(G))$ 彼此链同伦，因而诱导出的映射相同： 
    $
      caron(H)^p (cal(U), cal(G)) -> caron(H)^p (cal(V), cal(G))
    $
  ]
  #proof[
    // 由于覆盖 $cal(U) = {U_i -> U}_i$ 等价于用单个映射给出的覆盖 ${U' = union.sq.big_i U_i -> U}$，不妨设 $cal(U) = {U' ->> U}, cal(V) = {V' ->> U}$，且 $V' -> U$ 分解为 $V' arrows.rr^(g_1)_(g_2) U' -> U$。为明确起见，我们用 $V'_1$ 与 $V'_2$ 分别表示带有映射 $g_1$ 与 $g_2$ 的 $U'$-概形 $V'$。另外，定义 $V'_(12)$ 为由 $(g_1, g_2): V' -> U'' = U' times_U U'$ 给出的 $U''$-概形。
    设 $cal(U) = {u_i: U_i -> U}_(i in I), cal(V) = {v_j: V_j -> U}_(j in J)$，并设这两个加细由 $mu, lambda: J -> I$ 以及相应的分解给出： 
    #align(center, diagram({
      node((-1, 0), $V_j$)
      node((0, -1), $U_(mu(j))$)
      node((0, 1), $U_(lambda(j))$)
      node((1, 0), $U$)
      edge((-1, 0), (0, -1), $f_j$, "->")
      edge((-1, 0), (0, 1), $g_j$, "->", label-side: right)
      edge((-1, 0), (1, 0), $v_j$, "->")
      edge((0, -1), (1, 0), $u_(mu(j))$, "->")
      edge((0, 1), (1, 0), $u_(lambda(j))$, "->", label-side: right)
    }, spacing: 2em))
    
    现在定义： 
    $
      h: C^p (cal(U), cal(G)) &-> C^(p-1) (cal(V), cal(G)) \

      (s_(i_0,dots.c,i_p))_(i_0,dots.c,i_p) &|-> (sum_(k=0)^(p-1) (-1)^k s_(mu(j_0),dots.c,mu(j_k),lambda(j_k),dots.c,lambda(j_(p-1)))|_(phi_k))_(j_0,dots.c,j_(p-1))
    $
    其中 $phi_k$ 是平展映射： 
    $
      phi_k: V_(j_0) times_U dots.c times_U V_(j_(p-1)) -> U_(mu(j_0)) times_U dots.c times_U U_(mu(j_k)) times_U U_(lambda(j_k)) times_U dots.c times_U U_(lambda(j_(p-1)))
    $
    它定义为下列映射的纤维积： 

    - 当 $0 <= s < k$ 时，$f_(j_s): V_(j_s) -> U_(mu(j_s))$； 

    - 中间一项是单个映射 $(f_(j_k), g_(j_k)): V_(j_k) -> U_(mu(j_k)) times_U U_(lambda(j_k))$； 

    - 当 $k < s <= p-1$ 时，$g_(j_s): V_(j_s) -> U_(lambda(j_s))$。 

    论证与单纯恒等式的情形相同，$h$ 是这两个加细所诱导的链映射之间的链同伦。 
  ]
  于是，$cal(G) in cPAb(X_et)$ 在 $U$ 上的第 $p$ 次 *Čech 上同调*定义为： 
  $
    caron(H)^p (U, cal(G)) = dirlim_(cal(U)) caron(H)^p (cal(U), cal(G))
  $
]

#lemma[
  + 对 $X_et$ 中的每个平展覆盖 $cal(U)$，$caron(H)^0 (cal(U), -): cPAb(X_et) -> cAb$ 的右导出函子为 ${caron(H)^p (cal(U), -)}_(p>=0)$； 

  + 对每个 $U in Et_X$，$caron(H)^0 (U, -): cPAb(X_et) -> cAb$ 的右导出函子为 ${caron(H)^p (U, -)}_(p>=0)$。 
]
#proof[
  (1) $caron(H)^p (cal(U), -)$ 是 $delta$-函子。这是因为预层的短正合列 $0 -> cal(F) -> cal(G) -> cal(H) -> 0$ 在每个截面上正合，从而诱导出链复形的短正合列： 
  $
    0 -> C^bullet (cal(U), cal(F)) -> C^bullet (cal(U), cal(G)) -> C^bullet (cal(U), cal(H)) -> 0
  $
  并在上同调上诱导出长正合列。因此，要证明 $caron(H)^p (cal(U), -) cong R^p caron(H)^0 (cal(U), -)$，只需证明：对每个 $p >= 1$ 与每个内射对象 $cal(I) in cPAb(X_et)$，都有 $caron(H)^p (cal(U), cal(I)) = 0$。设 $cal(U) = {U_i -> U}_(i in I)$。于是问题化为证明：Čech 复形 
  $
    0 -> product_(i_0 in I) cal(I) (U_(i_0)) -> dots.c -> product_(i_0,dots.c,i_p in I) cal(I) (U_(i_0,dots.c,i_p)) -> product_(i_0,dots.c,i_(p+1) in I) cal(I) (U_(i_0,dots.c,i_(p+1))) -> dots.c
  $
  在每个 $p >= 1$ 处正合。现在 $cal(I)(U^((p))) = Hom_(cPAb)(ul(ZZ)_(!,U^((p)),0), cal(I))$，而 $cal(I)$ 是内射对象，故 $Hom_(cPAb) (-, cal(I))$ 反变正合。因此，只需证明下列序列： 
  $
    dots.c -> product_(i_0,dots.c,i_(p+1) in I) ul(ZZ)_(!,U_(i_0,dots.c,i_(p+1)),0) ->^partial product_(i_0,dots.c,i_p in I) ul(ZZ)_(!,U_(i_0,dots.c,i_p),0)  -> dots.c -> product_(i_0 in I) ul(ZZ)_(!,U_(i_0),0)
  $
  其中该映射定义为： 
  $
    partial: ul(ZZ)_(!,U^((p+1)),0) (V) = oplus.big_(Hom(U^((p+1)),V)) ZZ &-> ul(ZZ)_(!,U^((p)),0) (V) = oplus.big_(Hom(U^((p)), V)) ZZ \

    (s(f))_(f in Hom(U^((p+1)), V)) &|-> (sum_(k=0)^p (-1)^k s(g compose #[pr]_(0,dots.c,cancel(k),dots.c,p)))_(g in Hom(U^((p)), V))
  $
  其中 $#[pr] _(0,dots.c,cancel(k),dots.c,p): U^((p+1)) -> U^((p))$ 是 $U^((p+1))$ 投影到除第 $k$ 个分量以外的所有分量上。 

  这个链复形在拓扑学中我们再熟悉不过：它就是单纯形的奇异链复形。因此不妨接受它是正合的。 

  (2) 由 (1) 可知，$caron(H)^p (U, -)$ 也是 $delta$-函子：把每个 $caron(H)^p (cal(U), -)$ 的长正合列取正向极限、利用 $cAb$ 的 (Ab5) 即可；此外，对内射对象 $cal(I) in cPAb(X_et)$，$caron(H)^p (U, cal(I)) = 0$，因为它是一族零对象的正向极限。 
]

#theorem(name: <cech-to-derived-functor-spectral-sequence>)[
  (Čech 到导出函子的谱序列 / Cartan–Leray 谱序列) 
  
  对任意 $cal(F) in cAb(X_et)$，定义预层 $ul(H)^q (cal(F)): Et_X^opp -> cAb, U |-> H^q (U, cal(F))$，其限制映射由 $cal(F)$ 某个内射消解上的限制映射给出。 

  对 $U in Et_X$ 的每个平展覆盖 $cal(U)$，都有自然的谱序列： 
  $
    E_2^(p,q) = caron(H)^p (cal(U), ul(H)^q (cal(F))) => H^(p+q) (U, cal(F))
  $
  而对每个 $U in Et_X$，也有自然的谱序列： 
  $
    E_2^(p,q) = caron(H)^p (U, ul(H)^q (cal(F))) => H^(p+q) (U, cal(F))
  $
]
#proof[
  注意遗忘函子 $iota: cAb(X_et) -> cPAb(X_et)$ 有正合左伴随 $(-)^\#$，且把内射对象送到内射对象；此外 $caron(H)^p = R^p caron(H)^0$。 
  
  下面证明 $ul(H)^q = R^q iota$。事实上，对每个 $cal(F) in cAb(X_et)$，取它在 $cAb(X_et)$ 中的一个内射消解 $0 -> cal(F) -> cal(I)^bullet$，则： 
  $
    R^q iota(cal(F)) = h^q (0 -> iota(cal(I)^bullet))
  $
  而 $cPAb$ 中的上同调是逐截面取的，因此这个预层就是 $U |-> h^q (0 -> iota(cal(I)^bullet)(U)) = H^q (U, cal(F))$，即预层 $ul(H)^q (cal(F))$。 
  
  于是，对下面两个复合分别应用 Grothendieck–Leray 谱序列，即得定理： 
  // https://q.uiver.app/#r=typst&q=WzAsMyxbMiwxLCJjQWIiXSxbMCwxLCJjQWIoWF9ldCkiXSxbMSwwLCJjUEFiKFhfZXQpIl0sWzEsMiwiaW90YSJdLFsyLDAsImNhcm9uKEgpXjAgKGNhbChVKSwgLSkiXSxbMSwwLCJHYW1tYShVLCAtKSIsMl1d
  #align(center, {
  diagram({
    node((1, 0), [$cAb$])
    node((-1, 0), [$cAb(X_et)$])
    node((0, -1), [$cPAb(X_et)$])
    edge((-1, 0), (0, -1), [$iota$], label-side: left, "->")
    edge((0, -1), (1, 0), [$caron(H)^0 (cal(U), -)$], label-side: left, "->")
    edge((-1, 0), (1, 0), [$Gamma(U, -)$], label-side: right, "->")
  })
  h(10%)
  diagram({
    node((1, 0), [$cAb$])
    node((-1, 0), [$cAb(X_et)$])
    node((0, -1), [$cPAb(X_et)$])
    edge((-1, 0), (0, -1), [$iota$], label-side: left, "->")
    edge((0, -1), (1, 0), [$caron(H)^0 (U, -)$], label-side: left, "->")
    edge((-1, 0), (1, 0), [$Gamma(U, -)$], label-side: right, "->")
  })
  })
]

#proposition(name: <cech-h0-of-hq-psh-vanish>)[
  对任意 $q >= 1$、$cal(F) in cAb(X_et)$、$U in Et_X$，以及任意类 $alpha in ul(H)^q (cal(F))(U) = H^q (U, cal(F))$，都存在平展覆盖 $V ->> U$ 使得 $alpha|_V = 0$。 

  特别地，对每个 $U in Et_X$ 都有 $caron(H)^0 (U, ul(H)^q (cal(F))) = 0$，即 $ul(H)^q (cal(F))^+ = 0$。 
]
#proof[
  取 $cal(F)$ 在 $cAb(X_et)$ 中的一个内射消解： 
  $
    0 -> cal(F) -> cal(I)^bullet
  $
  于是 $alpha in h^q (0 -> cal(I)^bullet (U))$。由于 $cal(I)^(q-1) -> cal(I)^q -> cal(I)^(q+1)$ 在 $q$ 处正合，作为层有： 
  $
    im(cal(I)^(q-1) -> cal(I)^q) = ker(cal(I)^q -> cal(I)^(q+1))
  $
  设 $alpha = [alpha_0]$，其中 $alpha_0 in ker(cal(I)^q -> cal(I)^(q+1)) = im(cal(I)^(q-1) -> cal(I)^q)$。层像就是对预层像做一次加号构造（层化）得到的（因为预层像是某个层的子预层，从而是分离的），所以存在平展覆盖 ${V_i -> U}$，使得 $alpha_0|_(V_i) in im(cal(I)^(q-1) (V_i) -> cal(I)^q (V_i))$。过渡到不交并，就存在平展覆盖 $V ->> U$，使得 $alpha_0|_V in im(cal(I)^(q-1) (V) -> cal(I)^q (V))$。因此 $alpha|_V = 0$。 

  $caron(H)^0 (U, ul(H)^q (cal(F))) = 0$ 是显然的：对任意平展覆盖 $cal(U) = {U' -> U}$，任意类 $alpha in caron(H)^0 (cal(U), ul(H)^q (cal(F))) subset H^q (U', cal(F))$ 在过渡到某个加细 $V ->> U'$ 后消没，因而在正向极限中消没。 
]

#corollary(name: <h1-is-cech-h1>)[
  对每个 $U in Et_X, cal(F) in cAb(X_et)$，都有自然同构： 
  $
    caron(H)^1 (U, cal(F)) ->^tilde H^1 (U, cal(F))
  $
]
#proof[
  取 Čech 到导出函子的谱序列的五项正合列： 
  $
    E_2^(p,q) = caron(H)^p (U, ul(H)^q (cal(F))) => H^(p+q) (U, cal(F))
  $
  注意 $ul(H)^0 (cal(F)) = cal(F)$，理由非常显然，于是得到： 
  $
    0 -> caron(H)^1 (U, cal(F)) -> H^1 (U, cal(F)) -> caron(H)^0 (U, ul(H)^1 (cal(F))) -> caron(H)^2 (U, cal(F)) -> H^2 (U, cal(F))
  $
  然而我们已经证明 $caron(H)^0 (U, ul(H)^1 (cal(F))) = 0$，因此得到同构： 
  $
    caron(H)^1 (U, cal(F)) ->^tilde H^1 (U, cal(F))
  $
]

/*
#lemma[
  若 $X$ 是这样的概形，其中任意有限点集都包含在一个仿射开集中；又设 $cal(P) in cPAb(X_et)$ 满足 $cal(P)^+ = 0$，则对一切 $U in Et_X$： 
  $
    caron(H)^p (U, cal(P)) = 0, forall p >= 0
  $
]
#proof[

]

#corollary[
  若 $X$ 是这样的概形，其中任意有限点集都包含在一个仿射开集中（很多情形下都成立，例如只要 $X$ 在某个仿射概形上拟射影），则对一切 $U in Et_X$、$cal(F) in cAb(X_et)$，都有自然同构： 
  $
    caron(H)^q (U, cal(F)) ->^tilde H^q (U, cal(F)), forall q >= 0
  $
]
#proof[

]*/
