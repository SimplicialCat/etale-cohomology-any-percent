#import "void-import.typ": *

== $R f_!$ 的有限性

本节我们建立紧合光滑基变换定理与 $R f_!$ 的有限性，即： 

- $f$ 紧合光滑时，$R f_*$ 保持 l.c.c. 层； 

- $f$ 分离、有限型时，$R f_!$ 保持可构造层。 

证明的重头戏，在于应用一次局部零调性：紧合基变换、局部零调性与可构造层的 devissage 在这里环环相扣。 

紧合光滑基变换与 $R f_!$ 有限性的证明彼此交织，所以我们先为维数 $1$ 证明一条引理，用它启动归纳。 

#lemma(name: <proper-smooth-base-change-bootstrap>)[
  (维数 $1$ 的紧合光滑基变换) 设 $f: X -> Y$ 是紧合态射，各纤维的维数 $<=1$。则对任意自然数 $n in cal(O)_Y^times$，层 $R^q f_* ul(ZZ\/n)$ 对一切 $q>=0$ 都是 l.c.c.。 
]
#proof[
  我们先证明 $R^q f_* ul(ZZ\/n)$ 的茎有限。由紧合基变换，$(R^q f_* ul(ZZ\/n))_(ol(y)) = H^q (X_(ol(y)), ul(ZZ\/n))$。由下面的引理，这些茎都是有限交换群： 
  
  #lemma[
    设 $X$ 是代数闭域 $k$ 上紧合、维数 $<=1$ 的有限型概形，则群 $H^q (X, ul(ZZ\/n))$ 都是有限的。  
  ]
  #proof[
    由 Grothendieck 消没，只需处理 $q = 0,1,2$。$X$ 只有有限多个不可约分支，故 $H^0 (X, ul(ZZ\/n)) = (ZZ\/n)^(pi_0 (X))$ 有限，于是只剩 $q = 1,2$ 两种情形。 

    设 $X_1, dots.c, X_m$ 是 $X$ 的不可约分支，各自赋以既约子结构，含入映射记为 $i_j: X_j -> X$。有短正合列： 
    $
      0 -> ul(ZZ\/n)_X -> oplus.big_(j=1)^m i_(j,*) ul(ZZ\/n) -> cal(R) -> 0
    $
    其中 $cal(R)$ 的支集是有限个闭点，故对一切 $q >= 1$ 都有 $H^q (X, cal(R)) = 0$。于是得到正合列： 
    $
      dots.c -> H^0 (X, cal(R)) -> H^1 (X, ul(ZZ\/n)) -> oplus.big_(j=1)^m H^1 (X_j, ul(ZZ\/n)) -> 0
    $
    以及同构 $H^2 (X, ul(ZZ\/n)) cong oplus.big_(j=1)^m H^2 (X_j, ul(ZZ\/n))$。上面的论证已说明 $H^0$ 有限。于是只需证明 $q=1,2$ 时 $H^q (X_j, ul(ZZ\/n))$ 有限；把 $X$ 换成 $X_j$，便可假设 $X$ 是整的。 

    现在考虑正规化 $nu: X' -> X$。$nu$ 有限且满射，$X'$ 是光滑射影曲线。由于 $nu$ 满射，由 @surjection-has-injective-unit 可知 $ul(ZZ\/n) -> nu_* ul(ZZ\/n)$ 是单射。于是可以构成短正合列： 
    $
      0 -> ul(ZZ\/n) -> nu_* ul(ZZ\/n) -> cal(R) -> 0
    $
    $nu$ 在稠密开集 $U -> X$ 上是同构，因此 $ul(ZZ\/n) -> nu_* ul(ZZ\/n)$ 也在稠密开集 $U -> X$ 上是同构。于是 $cal(R)$ 的支集是有限个闭点。类似地有正合列： 
    $
      dots.c -> H^0 (X, cal(R)) -> H^1 (X, ul(ZZ\/n)) -> H^1 (X', ul(ZZ\/n)) -> dots.c
    $
    以及同构 $H^2 (X', ul(ZZ\/n)) cong H^2 (X, ul(ZZ\/n))$。于是可把 $X$ 换成 $X'$，不妨设 $X$ 是光滑射影曲线。这时由 @cohom-of-proj-curve，$H^q (X, ul(ZZ\/n))$ 都是有限交换群。 
  ]

  既然 $R^q f_* ul(ZZ\/n)$ 的茎有限，由 @descs-of-lcc-sheaves，要证明这些层都是 l.c.c.，只需证明所有特殊化映射都是同构。这由 @loc-acyc-of-smooth-maps（光滑态射的局部零调性）与 @proper-loc-acyc-bc 推出。 
]

#theorem(name: <finiteness-of-lower-shriek>)[
  ($R f_!$ 的有限性) 设 $f: X -> Y$ 是 Noether 概形之间分离、有限型的态射，$Lambda$ 是 $n$-挠 Noether 环，且 $n in cal(O)_Y^times$。 
  
  则对 $X$ 上任意 $Lambda$-模的可构造层 $cal(F)$，$R^q f_! cal(F)$ 都是 $Y$ 上 $Lambda$-模的可构造层。结合 Grothendieck 消没，这便给出导出范畴的陈述：$R f_!: D(X_et, Lambda) -> D(Y_et, Lambda)$ 限制为函子： 
  $
    R f_!: D^b_c (X_et, Lambda) -> D^b_c (Y_et, Lambda)
  $
  即 $R f_!$ 保持 $D^b_c$。 
]
#proof[
  我们先假定 $Lambda = ZZ\/n$。 //对任意可构造层 $cal(F) in cAb_c (X_et, ZZ\/n) $，考虑： 
  // $
  //   cal(S) = {Z subset Y #[闭] : (R^q f_! cal(F))|_Z #[对某个 $q$ 不可构造]}
  // $
  // 假设 $cal(S) != emptyset$。由 Noether 归纳法，$cal(S)$ 有极小元 $Z$。反设 $(R^q f_! cal(F))|_Z$ 不可构造，而 $Z$ 不是不可约的，其不可约分支为 $Z_1, dots.c, Z_m$。则由极小性，每个 $(R^q f_! cal(F))|_(Z_i)$ 都可构造。对每个不可约闭子集 $W subset Z$，都有某个 $Z_i$ 使 $W subset Z_i$；于是由 @constructible-sheaves-first-props (2)，利用 $(R^q f_! cal(F))|_(Z_i)$ 的可构造性，存在非空开集 $U subset W$，使 $(R^q f_! cal(F))|_W$ 是 l.c.c.。再由 @constructible-sheaves-first-props (2)，$(R^q f_! cal(F))|_Z$ 可构造，这与 $Z in cal(S)$ 矛盾。 

  // 因此 $Z$ 必定不可约。给 $Z$ 赋予既约子结构，便可假设 $Z$ 是整的。由紧合基变换，$(R^q f_! cal(F))|_Z = R^q f_(Z,!) (cal(F)|_(X_Z))$，其中 $f_Z: X_Z -> Z$ 是 $f$ 沿 $Z -> Y$ 的基变换。$cal(F)|_(X_Z)$ 可构造，故把 $f$ 换成 $f_Z$，便可假设： 

  // - $X$ 是整的； 

  // - 对一切真闭子概形 $Z subset.neq X$ 与一切 $q>=0$，$(R^q f_! cal(F))|_Z$ 都可构造。 

  // 现在取仿射开集 $j: U -> Y$，其互补闭浸入为 $i: Z -> Y$。有零延拓三角： 
  // $
  //   j_! (R f_! cal(F)|_U) -> R f_! cal(F) -> i_* (R f_! cal(F)|_Z) ->^(+1)
  // $
  // 既然已假定 $R f_! cal(F)|_Z in D^b_c (Z_et, ZZ\/n)$，就有 $i_* (R f_! cal(F)|_Z) in D^b_c (Y_et, ZZ\/n)$。于是要证明 $R f_! cal(F) in D^b_c (X_et, ZZ\/n)$，只需证明
  
  // 作拉回图表： 
  // // // https://q.uiver.app/#r=typst&q=WzAsNixbMCwwLCJYX1UiXSxbMCwxLCJVIl0sWzEsMSwiWSJdLFsyLDEsIloiXSxbMSwwLCJYIl0sWzIsMCwiWF9aIl0sWzEsMiwiaiIsMl0sWzMsMiwiaSJdLFswLDQsImonIl0sWzUsNCwiaSciLDJdLFs0LDIsImYiXSxbNSwzLCJmX1oiXSxbMCwxLCJmX1UiLDJdXQ==
  // // #align(center, diagram({
  // //   node((0, 0), [$X_U$])
  // //   node((0, 1), [$U$])
  // //   node((1, 1), [$Y$])
  // //   node((2, 1), [$Z$])
  // //   node((1, 0), [$X$])
  // //   node((2, 0), [$X_Z$])
  // //   edge((0, 1), (1, 1), [$j$], label-side: right, "->")
  // //   edge((2, 1), (1, 1), [$i$], label-side: left, "->")
  // //   edge((0, 0), (1, 0), [$j'$], label-side: left, "->")
  // //   edge((2, 0), (1, 0), [$i'$], label-side: right, "->")
  // //   edge((1, 0), (1, 1), [$f$], label-side: left, "->")
  // //   edge((2, 0), (2, 1), [$f_Z$], label-side: left, "->")
  // //   edge((0, 0), (0, 1), [$f_U$], label-side: right, "->")
  // // }))
  // // 现在有零延拓三角： 
  // // $
  // //   R(f compose j')_! j'^(-1) cal(F) -> R f_! cal(F) -> R(f compose i')_! i'^(-1) cal(F) ->^(+1)
  // // $
  
  首先我们说明，层的陈述与导出范畴的陈述等价。导出范畴的陈述显然更强；反之，若层的陈述成立，则对 $cal(K) in D^b_c (X_et, ZZ\/n)$，有超上同调谱序列： 
  $
    E_1^(p,q) = R^q f_! (h^p (cal(K))) => h^(p+q) (R f_! cal(K))
  $
  由层的陈述可知，每个 $E_1^(p,q)$ 都可构造。由 Grothendieck 消没，$E_1^(p,q)$ 的支集落在一个有界矩形内。于是每个 $h^(p+q) (R f_! cal(K))$ 都是有限多个可构造层的扩张，从而可构造。因此 $R f_! cal(K) in D^b_c (Y_et, ZZ\/n)$。下面我们专注于层的陈述。 

  由 @constructible-sheaves-first-props (2)，只需证明：对每个不可约闭子集 $Z subset Y$（赋予既约子结构），都存在 $Z$ 的非空开集 $V subset Z$，使 $(R^q f_! cal(F))|_V$ 可构造。 

  任取 $Z$ 的一个仿射开集 $V$，作 $f$ 沿 $V -> Y$ 的基变换 $f_V: X_V -> V$。则： 
  $
    (R^q f_! cal(F))|_V = R^q f_(V,!) (cal(F)|_(X_V))
  $
  由于 $cal(F)|_(X_V)$ 可构造，可把 $f$ 换成 $f_V$。于是不妨假设： 

  - $Y$ 是整仿射概形。 

  假设我们已证明：在 $X$ 仿射这一附加假设下，每个 $R^q f_!$ 都保持可构造层。那么一般情形下，设 $X = union.big_(i=1)^k X_i$ 被 $k$ 个仿射开集覆盖。令 $j_1: X_1 -> X$ 是开浸入，$i_1: Z_1 = X - X_1 -> X$ 是互补的闭浸入。则有零延拓三角： 
  $
    R(f compose j_1)_! j_1^(-1) cal(F) -> R f_! cal(F) -> R(f compose i_1)_! i_1^(-1) cal(F) ->^(+1)
  $
  由 $X$ 为仿射时的情形，$R(f compose j_1)_! j_1^(-1) cal(F) in D^b_c (Y_et, ZZ\/n)$。于是要证明 $R f_! cal(F) in D^b_c (Y_et, ZZ\/n)$，只需证明 $R(f compose i_1)_! i_1^(-1) cal(F) in D^b_c (Y_et, ZZ\/n)$。现在 $Z_1 = union.big_(i=2)^k (X_i inter Z_1)$，而每个 $X_i inter Z_1$ 都是仿射概形 $X_i$ 的闭子概形，从而是仿射的。因此 $Z_1$ 至多被 $(k-1)$ 个仿射开集覆盖。对覆盖 $X$ 所需仿射开集的最少个数作归纳，便可假设 $R(f compose i_1)_! i_1^(-1) cal(F) in D^b_c (Y_et, ZZ\/n)$，这就完成了一般情形的证明。 

  于是不妨进一步假设： 

  - $Y = Spec(A)$ 是整仿射的，$X = Spec(B)$ 也是仿射的。 

  由于 $X -> Y$ 有限型，$B$ 是有限型 $A$-代数。于是将其写成 $B = A[x_1, dots.c, x_d]\/I$，便可将 $f$ 分解为： 
  $
    X ->^i AA^d_Y ->^(p_d) AA^(d-1)_Y ->^(p_(d-1)) dots.c -> AA^1_Y ->^(p_1) Y
  $
  其中第一个映射是闭浸入，其后每个映射都是形如 $AA^1_S -> S$ 的投影。 
  
  由 @finite-morphisms-and-constructible-sheaves，$i_* cal(F)$ 可构造。若能证明对每个 $p_j$，$R p_(j,!)$ 都保持 $D^b_c$，则： 
  $
    R f_! cal(F) = R p_(1,!) dots.c R p_(d,!) i_* cal(F) in D^b_c (Y_et, ZZ\/n)
  $
  这便完成了证明。于是把 $f$ 换成某个投影 $p_j$，便可假设： 

  - $Y = Spec(A)$ 是整仿射的，$X = AA^1_Y$，而 $f: AA^1_Y -> Y$ 是投影。 

  对可构造层 $cal(F) in cAb(X_et, ZZ\/n)$，由 @constructible-sheaves-first-props (4)，存在拟紧平展态射 $j: U -> X$ 与满射 $j_! ul(ZZ\/n) -> cal(F)$。用仿射开集 $j_i: U_i -> U$ 覆盖 $U$，把 $U$ 换成 $union.sq.big_i U_i$，并利用满射 $oplus.big_i j_! j_(i,!) ul(ZZ\/n) -> j_! ul(ZZ\/n)$，便可假设 $j$ 是仿射的。重复这一消解过程，便得到： 
  $
    dots.c -> cal(P)^(-1) -> cal(P)^0 -> cal(F) -> 0
  $
  它是 $cal(F)$ 的消解，其中每个 $cal(P)^(-p) = j_(p,!) ul(ZZ\/n)$，而 $j_p: U_p -> X$ 仿射平展。于是 $R f_! cal(F) = R f_! cal(P)^bullet$，并有超上同调谱序列： 
  $
    E_1^(p,q) = R^q f_! cal(P)^p => R^(p+q) f_! cal(F)
  $
  它在 $q$ 方向有界。因此，若能证明每个 $E_1^(p,q)$ 都可构造，则每个 $R^q f_! cal(F)$ 作为有限多个可构造层的扩张，也都可构造。 

  于是只需证明每个 $R^q f_! j_(p,!) ul(ZZ\/n) = R^q (f compose j_p)_! ul(ZZ\/n)$ 都可构造。固定仿射平展态射 $j: U -> X = AA^1_Y$，剩下要证的是： 
  $
    R^q f_! j_! ul(ZZ\/n)
  $
  都是可构造的。对每个整闭子概形 $Z subset Y$，由紧合基变换，$(R^q f_! j_! ul(ZZ\/n))|_Z = R^q f_(Z,!) j_(Z,!) ul(ZZ\/n)$，其中 $f_Z: AA^1_Z -> Z$，而 $j_Z: U_Z -> AA^1_Z$ 仍仿射平展。于是由 @constructible-sheaves-first-props (2)，把 $f, j$ 换成 $f_Z, j_Z$ 之后，只需证明存在仿射开集 $V subset Y$，使得： 
  $
    (R^q f_! j_! ul(ZZ\/n))|_V = R^q f_(V,!) j_(V,!) ul(ZZ\/n)
  $
  可构造。令 $g = f compose j: U -> Y$。 

  设 $K$ 是 $Y$ 的函数域，$L\/K$ 是 $K$ 的完全闭包 (perfect closure)。（也就是说，当 $"char"(K) = p$ 时，$L$ 是 $ol(K)$ 的子域，在 $K$ 中添加其元素的所有 $p^m$ 次根，$m$ 取遍所有值，即可得到；当 $"char"(K) = 0$ 时，$L = K$。）特别地，$L$ 是完全域。再把 $f$ 与 $j$ 作基变换，得到： 
  $
    g_L: U_L ->^(j_L) AA^1_L ->^(f_L) Spec(L)
  $
  这是相对维数为 1 的仿射光滑态射。 
  
  #lemma[
    设 $K$ 是完全域，$X$ 是整仿射概形，$f: X -> Spec(K)$ 是相对维数为 1 的光滑态射。则 $f$ 有紧化： 
    $
      X ->^j ol(X) ->^(ol(f)) Spec(K)
    $
    其中 $ol(f): ol(X) -> Spec(K)$ 紧合光滑，$ol(X) - X$ 在 $Spec(K)$ 上有限（即有限个闭点）。 
  ]
  #proof[
    任取仿射嵌入 $X -> AA^d_K$，得到射影闭包 $X_1 -> PP^d_K$。这就给出紧化： 
    $
      X ->^h X_1 ->^(f_1) Spec(K)
    $
    其中 $f_1$ 射影，且 $X_1$ 是整的。$X$ 在其射影闭包 $X_1$ 中稠密，故 $X_1$ 的维数为 1，而 $X_1 - X$ 的维数更小，即维数 0。因此 $X_1 - X$ 是有限个点。 

    设 $nu: ol(X) -> X_1$ 是 $X_1$ 的正规化，它是有限映射。现在 $X$ 在域上光滑，故正规；又 $h: X -> X_1$ 支配，于是由正规化的泛性质，$h$ 唯一地分解为 $X ->^j ol(X) ->^nu X_1$。$nu$ 在 $X_1$ 的正规轨迹上方是同构；既然 $X$ 正规，$nu$ 特别地在像 $h(X)$ 上方是同构。因此 $j: X -> ol(X)$ 是开浸入。这就给出紧化： 
    $
      X ->^j ol(X) ->^(ol(f)) Spec(K)
    $
    其中 $ol(X)$ 正规且维数为 1。现在对每个有限域扩张 $L\/K$，由于 $K$ 完全，$L\/K$ 可分，$Spec(L) -> Spec(K)$ 平展。于是基变换 $ol(X)_L -> ol(X)$ 平展。由于 $ol(X)$ 正规，由 @etale-local-properties (5)，$ol(X)_L$ 正规。又 $ol(X)_L$ 的维数为 1，故必定正则。于是我们证明了 $ol(X)$ 在 $K$ 上几何正则，从而在 $K$ 上光滑。因此 $ol(f)$ 紧合光滑。此外，由于 $nu$ 有限，$ol(X) - X$ 在 $X_1 - X$ 上有限。因此 $ol(X) - X$ 在 $K$ 上有限。 
  ]

  由上述引理，$g_L$ 有紧化： 
  $
    g_L: U_L ->^(h_L) U'_L ->^(r_L) Spec(L)
  $
  其中 $U'_L - h_L (U_L)$ 在 $L$ 上有限，$r_L$ 紧合光滑。 

  回忆：当 $"char"(K) = p$ 时，在 $K$ 中添加所有 $p^m$ 次根得到 $L$；当 $"char"(K) = 0$ 时，$L = K$。接下来： 

  - 当 $"char"(K) = p$ 时，每个元素 $x in L$ 都属于某个 $K(x_1^(p^(-m_1)), dots.c, x_s^(p^(-m_s)))$，其中 $x_1, dots.c, x_s in K$ 取自某个有限集，$m_1, dots.c, m_s >= 1$ 是某些幂次。把它写成 $x = display((alpha(x_1^(p^(-m_1)), dots.c, x_s^(p^(-m_s))))/(beta(x_1^(p^(-m_1)), dots.c, x_s^(p^(-m_s)))))$，其中 $alpha, beta$ 是多项式，且 $0 != beta_0 = beta(x_1^(p^(-m_1)), dots.c, x_s^(p^(-m_s))) in L$。于是存在某个 $m_0$，使得 $x_0 = beta_0^(p^(m_0)) in K$。因此 $x in K[x_1^(p^(-m_1)), dots.c, x_s^(p^(-m_s)), x_0^(p^(-m_0))]$。现在，把 $x$ 写成多项式表示，其系数必落在某个 $A_u$ 中，其中 $u in A^times$ 取某个固定值，故： 
    $
      x in A_u [x_0^(p^(-m_0)), dots.c, x_s^(p^(-m_s))]
    $
    其中 $u in A^times$ 取某个固定值，$x_0, dots.c, x_s in A_u$，$m_0, dots.c, m_s >= 0$ 为某些幂次。 

    此时 $Spec(A_u) -> Spec(A)$ 是主仿射开集，而由 @adjoining-pth-root-in-char-p-is-univ-homeo，$Spec(A_u [x_0^(p^(-m_0)), dots.c, x_s^(p^(-m_s))]) -> Spec(A_u)$ 是有限泛同胚。 

    换言之，$L = dirlim_R R$，其中每个 $R$ 对某个 $u in A^times$ 都是有限、满射、根性的 $A_u$-代数。 

  - 当 $"char"(K) = 0$ 时，$L = K = dirlim_(u in A^times) A_u$，故特征 $p$ 情形下的结论在这里同样成立。 

  应用 @passage-to-limit-of-morphisms 与 @passage-to-limit-of-properties (2e)(3f)，可知存在 $u in A^times$ 与有限、满射、根性的 $A_u$-代数 $R$，使得 $g_R: U_R -> Spec(R)$ 有紧化： 
  $
    g_R: U_R ->^(h_R) U'_R ->^(r_R) Spec(R)
  $
  其中 $r_R$ 紧合光滑，$U'_R - h_R (U_R)$ 在 $Spec(R)$ 上有限。特别地，$U'_R -> Spec(R)$ 的每条纤维与 $U_R$ 的相应纤维只相差有限个闭点，故每条纤维的维数 $<=1$。于是： 
  $
    (R g_! ul(ZZ\/n))|_(Spec(R)) = R g_(R,!) ul(ZZ\/n) = R r_(R,*) h_(R,!) ul(ZZ\/n) 
  $
  设 $ell_R: Z_R = U'_R - h_R (U_R) -> U'_R$ 是 $h_R$ 的互补闭浸入，于是 $r_R compose ell_R$ 有限。则有零延拓三角： 
  $
    R r_(R,*) h_(R,!) ul(ZZ\/n) -> R r_(R,*) ul(ZZ\/n) -> R r_(R,*) ell_(R,*) ul(ZZ\/n)
  $
  现在： 

  - 由那条启动归纳的引理 @proper-smooth-base-change-bootstrap：$r_R$ 紧合光滑，纤维维数 $<=1$，故层 $R^q r_(R,*) ul(ZZ\/n)$ 都是 l.c.c.。于是 
    $
      R r_(R,*) ul(ZZ\/n) in D^b_c (Spec(R)_et, ZZ\/n)
    $

  - 由 @finite-morphisms-and-constructible-sheaves，$R r_(R,*) ell_(R,*) ul(ZZ\/n) = R(r_R compose ell_R)_* ul(ZZ\/n) in D^b_c (Spec(R)_et, ZZ\/n)$。 

  因此 $(R g_! ul(ZZ\/n))|_(Spec(R)) = R r_(R,*) h_(R,!) ul(ZZ\/n) in D^b_c (Spec(R)_et, ZZ\/n)$，从而每个 
  $
    (R^q g_! ul(ZZ\/n))|_(Spec(R))
  $
  都可构造。$Spec(R) -> Spec(A_u)$ 有限、满射、根性，从而是泛同胚。于是由拓扑不变性，$(R^q g_! ul(ZZ\/n))|_(Spec(A_u))$ 可构造。 
  
  至此，$Lambda = ZZ\/n$ 的情形证毕。 

  对一般的 $n$-挠 Noether 环 $Lambda$，重复 $Lambda = ZZ\/n$ 的论证，不妨设 $cal(F) = ul(Lambda)$。于是由投影公式， 
  $
    R f_! ul(Lambda) = R f_! ul(ZZ\/n) Lotimes_(ZZ\/n) ul(Lambda)
  $
  由截断三角，只需证明每个 $R^q f_! ul(ZZ\/n) Lotimes_(ZZ\/n) ul(Lambda) in D^b_c (Y_et, Lambda)$。由于 $R^q f_! ul(ZZ\/n)$ 可构造，可把它消解为 $dots.c -> cal(P)^(-1) -> cal(P)^0 -> R^q f_! ul(ZZ\/n)$，其中每个 $cal(P)^p = j_(-p,!) ul(ZZ\/n)$，$j_p: U_p -> Y$ 拟紧平展。现在每个 $cal(P)^p$ 作为 $ul(ZZ\/n)$-模层都平坦，故： 
  $
    h^p (R^q f_! ul(ZZ\/n) Lotimes_(ZZ\/n) ul(Lambda)) = h^p (cal(P)^bullet otimes_(ZZ\/n) ul(Lambda))
  $
  每个 $cal(P)^p otimes_(ZZ\/n) ul(Lambda) = j_(-p,!) ul(Lambda)$ 都是 $Lambda$-模的可构造层，故每个 $h^p (R^q f_! ul(ZZ\/n) Lotimes_(ZZ\/n) ul(Lambda))$ 也都是 $Lambda$-模的可构造层。一般系数情形至此证毕。 
]

#theorem[
  (紧合光滑基变换) 设 $f: X -> Y$ 是 Noether 概形之间的紧合光滑态射，$Lambda$ 是 $n$-挠 Noether 环，且 $n in cal(O)_Y^times$。设 $cal(F) in cAb(X_et, Lambda)$ 是 $X$ 上 $Lambda$-模的 l.c.c. 层。则每个 $R^q f_* cal(F)$ 都是 $Y$ 上 $Lambda$-模的 l.c.c. 层。 
]
#proof[
  由 @loc-acyc-of-smooth-maps，$f$ 作为光滑映射，关于 $cal(F)$ 局部零调。于是由 @proper-loc-acyc-bc，层 $R^q f_* cal(F)$ 的所有特殊化映射都是同构。由 @finiteness-of-lower-shriek，$R^q f_* cal(F)$ 是 $Lambda$-模的可构造层，从而其 $Lambda$-模茎有限。于是由 @descs-of-lcc-sheaves，$R^q f_* cal(F)$ 都是 l.c.c. 层。 
]
