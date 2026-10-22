// audit-exception: 长正合列内 #[...] 文字说明块内的 $0$ 与 @引用，审计按相邻 $ 配对会把文字说明切成伪公式段；只译说明文字，公式未动。
#import "void-import.typ": *
== 一维的消没定理

#lemma[
  设 $X$ 是 Noether 概形，$E subset X$ 是对特殊化封闭的子集。设 $cal(F) in cAb(X_et)$ 是挠层，其支集 $supp(cal(F)) subset E$。则 $cal(F)$ 可写成正向极限： 
  $
    cal(F) = dirlim_(lambda) cal(F)_lambda
  $
  其中每个 $cal(F)_lambda$ 都是支集含于 $E$ 的某个闭子集的挠层。 
]
#proof[
  由 @constructible-sheaves-first-props (6)，$cal(F)$ 是其可构造子层 ${cal(F)_lambda}$ 的正向极限。由 @supp-of-constructible-sheaf，对每一项都有： 
  $
    supp(cal(F)_lambda) subset E
  $
  而每一项的支集都是 $E$ 的可构造子集。可构造集的闭包，恰由该集合中某个点的所有特殊化组成。由于 $E$ 对特殊化封闭，故 $ol(supp(cal(F)_lambda)) subset E$，证毕。 
]

#notation(name: <notation-supp-on-dim-a>)[
  设 $X$ 是域 $K$ 上的有限型概形。我们把 $X$ 中*维数 $<=a$ 的点*构成的集合记为： 
  $
    E_a (X) := {x in X : dim(ol({x})) <= a}
  $
  
  对 $cal(F) in cAb(X_et)$，若 $supp(cal(F)) subset E_a (X)$，则称它*支撑在维数 $<=a$ 上*。 
]

#corollary(name: <supp-of-torsion-sheaf-dim>)[
  设 $X$ 是域 $K$ 上的有限型概形，$cal(F) in cAb(X_et)$ 是支撑在维数 $<=a$ 上的挠层。则 $cal(F)$ 可写成正向极限： 
  $
    cal(F) = dirlim_(lambda) cal(F)_lambda
  $
  其中每个 $cal(F)_lambda$ 都是挠层，其支集含于 $X$ 的某个闭子概形，且该子概形的维数 $<=a$。 
]
#proof[
  在上一个引理中取 $E = E_a (X)$，证明便完成了。 
]

#corollary(name: <supp-of-torsion-sheaf-dim-0>)[
  设 $X$ 是可分闭域 $k$ 上的有限型概形，$cal(F) in cAb(X_et)$ 是支撑在维数 $<=0$ 上的挠层。则对一切 $q >= 1$， 
  $
    H^q (X_et, cal(F)) = 0
  $
]
#proof[
  由 @supp-of-torsion-sheaf-dim， 
  $
    cal(F) = dirlim_lambda cal(F)_lambda
  $
  其中每一项都满足 $supp(cal(F)_lambda) subset Z$，这里的子概形是 $X$ 中某个维数为 $0$ 的子概形，而这样的子概形无非是有限个闭点。由 @pushforward-by-closed-immersion (1)、@pushforward-by-finite-morphism 与 @struct-of-spec-omega-et， 
  $
    H^q (X, cal(F)_lambda) = 0, forall q>=1
  $
  再由极限公式 @limit-formula-for-sheaves 即可完成证明。 
]

#proposition(name: <grothendieck-vanishing-for-curves>)[
  设 $X$ 是可分闭域 $k$ 上的任意曲线，$cal(F) in cAb(X_et)$ 是挠层。则对一切 $q >= 3$， 
  $
    H^q (X, cal(F)) = 0
  $
]
#proof[
  由于 $ol(k)\/k$ 是纯不可分扩张，由拓扑不变性，可以基变换到 $ol(k)$，从而不妨设 $k$ 代数闭。 

  设 $j: eta = Spec(K(X)) -> X$ 是泛点的包含映射。考虑自然态射： 
  $
    gamma: cal(F) -> j_* j^(-1) cal(F)
  $
  我们断言 $gamma$ 在 $ol(eta)$ 处的茎上是同构。事实上，$tilde(X)_(ol(eta)) = Spec(cal(O)_(X,eta)^#[sh]) = Spec(K(X)^#[sh]) = Spec(K(X)^sep) = ol(eta)$，于是： 
  $
    (R^q j_* j^(-1) cal(F))_(ol(eta)) = H^q (eta times_X ol(eta), j^(-1) cal(F)|_(eta times_X ol(eta))) = H^q (ol(eta), cal(F)_(ol(eta))) = cases(
      cal(F)_(ol(eta)) &\, q = 0, 
      0 &\, q >= 1
    )
  $
  换言之，$ker(gamma)_(ol(eta)) = coker(gamma)_(ol(eta)) = 0$，且对 $q >= 1$ 有 $(R^q j_* j^(-1) cal(F))_(ol(eta)) = 0$。由 @supp-of-torsion-sheaf-dim-0， 
  $
    H^p (X, ker(gamma)) = H^p (X, coker(gamma)) = 0, forall p >= 1 \
    H^p (X, R^q j_* j^(-1) cal(F)) = 0, forall p >= 1
  $
  由于 $H^p (X, ker(gamma)) = H^p (X, coker(gamma)) = 0, forall p >= 1$，借助短正合列可知，对一切 $p >= 2$， 
  $
    H^p (X, cal(F)) cong H^p (X, im(gamma)) cong H^p (X, j_* j^(-1) cal(F))
  $
  因此只需对 $p >= 3$ 证明 $H^p (X, j_* j^(-1) cal(F)) = 0$。为此使用 Leray 谱序列 @derived-lower-star-first-props (2)： 
  $
    E_2^(p,q) = H^p (X, R^q j_* j^(-1) cal(F)) ==> H^(p+q) (eta, j^(-1) cal(F)) 
  $
  现在对 $q >= 2$、$x in abs(X)$，有 
  $
    (R^q j_* j^(-1) cal(F))_x = H^q (eta times_X tilde(X)_x, cal(F)|_(eta times_X tilde(X)_x))
  $
  如 @gm-generic-pushforward-higher-vanishing 的证明中那样，$eta times_X tilde(X)_x = Spec(L)$，其中 $L$ 是 $k$ 的超越次数为 $1$ 的扩域。于是这个上同调是把 $H^q_#[cont] (Gal_L, -)$ 作用在离散挠 $Gal_L$-模上所得，因为 $cal(F)$ 是挠的。由 @tsen-thm-in-galois-cohom (1)（曾炯定理的推论），该上同调消没。因此 $(R^q j_* j^(-1) cal(F))_x = 0$。从而对一切 $q >= 2$，$R^q j_* j^(-1) cal(F) = 0$。 
  
  我们还证明了对 $p >= 1$ 有 $H^p (X, R^1 j_* j^(-1) cal(F)) = 0$。于是在 Leray 谱序列中： 
  $
    E_2^(p,q) = H^p (X, R^q j_* j^(-1) cal(F)) ==> H^(p+q) (eta, j^(-1) cal(F)) 
  $
  $E_2$-页上只有 $E_2^(p,0)$ 与 $E_2^(0,1)$ 非零。唯一存活的微分是 $d_2: E_2^(0,1) -> E_2^(2,0)$，谱序列在 $E_3$-页上稳定。于是对一切 $p >= 3$，这个谱序列诱导出同构： 
  $
    H^p (X, j_* j^(-1) cal(F)) = H^p (eta, j^(-1) cal(F))
  $
  右端由 @tsen-thm-in-galois-cohom (1) 消没（这是曾炯定理的推论），因为 $eta = Spec(K(X))$ 是 $k$ 的某个超越次数为 1 的扩域的谱，而 $j^(-1) cal(F)$ 是挠 $Gal_(K(X))$-模，因为 $cal(F)$ 是挠层。 

  这样我们就证明了对一切 $p >= 3$， 
  $
    H^p (X, cal(F)) cong H^p (X, j_* j^(-1) cal(F)) cong H^p (eta, j^(-1) cal(F)) = 0
  $
  证毕。 
]

现在可以证明一维的 Grothendieck 消没定理了。 

#theorem(name: <grothendieck-vanishing-in-dim-1>)[
  设 $X$ 是可分闭域 $k$ 上维数 $<=1$ 的任意有限型概形，$cal(F) in cAb(X_et)$ 是挠层。则对一切 $q >= 3$， 
  $
    H^q (X, cal(F)) = 0
  $
]
#proof[
  我们对 $X$ 的不可约分支个数作归纳。 

  先设 $X$ 不可约。由拓扑不变性，可以把 $X$ 换成它的约化，从而不妨设 $X$ 是整的。此时 $X$ 要么是点 $Spec(k)$，要么是曲线：点情形由 @struct-of-spec-omega-et 解决，曲线情形由上一个命题解决。 

  归纳步：设定理对所有不可约分支个数 $<n$ 的 $X$ 都成立；现在 $X$ 有 $n$ 个不可约分支。取 $X$ 的一个不可约分支 $Z$，赋以诱导的既约子概形结构，令 $U = X - Z$ 为其补集，它有 $n-1$ 个不可约分支。设 $i: Z -> X, j: U -> X$ 是包含映射。由 @etale-lower-shriek-first-props (3)，有短正合列： 
  $
    0 -> j_! j^(-1) cal(F) -> cal(F) -> i_* i^(-1) cal(F) -> 0
  $
  现在设 $q >= 3$： 

  - 由不可约情形，$H^q (X, i_* i^(-1) cal(F)) = H^q (Z, i^(-1) cal(F)) = 0$； 

  - $supp(j_! j^(-1) cal(F)) subset U subset Y := ol(U)$。$Y$ 有 $n-1$ 个不可约分支；给它赋以诱导的既约子概形结构，并考虑包含映射 $h: Y -> X$。 

    于是存在 $cal(G) in cAb(Y_et)$，使 $j_! j^(-1) cal(F) = h_* cal(G)$。对任意 $ol(y) in Y_et$，$cal(G)_(ol(y)) = (h_* cal(G))_(ol(y)) = (j_! j^(-1) cal(F))_(ol(y))$ 都是挠群，故由 @torsion-sheaves-first-props，$cal(G)$ 是挠层。于是由 $n-1$ 个不可约分支的情形， 
    $
      H^q (X, j_! j^(-1) cal(F)) = H^q (Y, cal(G)) = 0
    $
    即得。 

  再由长正合列，对一切 $q >= 3$ 都有 $H^q (X, cal(F)) = 0$，证毕。 
]

接下来处理一维的 Artin 消没定理。 

#proposition(name: <artin-vanishing-of-zn>)[
  设 $X$ 是可分闭域 $k$ 上维数 $<=1$ 的任意有限型仿射概形。则对一切 $q >= 2$ 与一切 $n >= 1$， 
  $
    H^q (X, ul(ZZ\/n)) = 0
  $
]
#proof[
  $q >= 3$ 的消没由 @grothendieck-vanishing-in-dim-1 给出，故只需处理 $q = 2$ 的消没。 

  由于 $ol(k)\/k$ 是纯不可分扩张，由拓扑不变性，可以基变换到 $ol(k)$，从而不妨设 $k$ 代数闭。当 $X$ 是仿射光滑曲线时，本命题已在 @h2-zn-of-affine-smooth-curve 中证明。接下来设 $X$ 是任意的仿射曲线，取它的正规化： 
  $
    nu: tilde(X) -> X
  $
  这是一个有限映射。考虑典范映射： 
  $
    ul(ZZ\/n)_X -> nu_* ul(ZZ\/n)_(tilde(X))
  $
  由于存在稠密开集 $U subset X$，使 $nu: nu^(-1) (U) -> U$ 是同构，$ul(ZZ\/n)_X -> nu_* ul(ZZ\/n)_(tilde(X))$ 限制到 $U$ 上便是同构。于是它的核与余核都支撑在有限多个闭点上，从而是零调的。#footnote[这个态射应当是单射，但我们这里并不需要这一点。] 于是用短正合列， 
  $
    H^2 (X, ul(ZZ\/n)) = H^2 (X, im(ul(ZZ\/n)_X -> nu_* ul(ZZ\/n)_(tilde(X)))) = H^2 (X, nu_* ul(ZZ\/n)_(tilde(X))) = H^2 (tilde(X), ul(ZZ\/n))
  $
  最后一步用到 @pushforward-by-finite-morphism。现在 $tilde(X)$ 是光滑仿射曲线，故该上同调消没，仿射曲线情形即得。 

  最后设 $X$ 是 $k$ 上一般的有限型仿射概形，维数 $<=1$，$Z_1, dots.c, Z_m$ 是它的不可约分支，均赋以诱导的既约子概形结构。于是每个 $Z_i$ 要么是曲线，要么是点 $Spec(k)$，故如前面所证 $H^q (Z_i, ul(ZZ\/n)) = 0$。设 $h_i: Z_i -> X$ 是相应的闭浸入，并令 $h: Z := union.sq.big_(i=1)^m Z_i -> X$ 为不交并，它是有限映射。考虑典范映射： 
  $
    ul(ZZ\/n)_X -> h_* ul(ZZ\/n)_Z
  $
  $X$ 中恰好落在一个不可约分支里的点构成稠密开集 $U$，并且 $h^(-1) (U) -> U$ 是同构。于是 $ul(ZZ\/n)_X -> h_* ul(ZZ\/n)_Z$ 限制到 $U$ 上是同构，其核与余核都支撑在有限多个闭点上。#footnote[这个态射也应当是单射，但我们这里并不需要这一点。] 同理， 
  $
    H^2 (X, ul(ZZ\/n)) = H^2 (Z, ul(ZZ\/n)) = oplus.big_(i=1)^m H^2 (Z_i, ul(ZZ\/n)) = 0
  $
  证毕。 
]

#theorem(name: <artin-vanishing-in-dim-1>)[
  设 $X$ 是可分闭域 $k$ 上维数 $<=1$ 的任意有限型仿射概形，$cal(F) in cAb(X_et)$ 是挠层。则对一切 $q >= 2$，  
  $
    H^q (X, cal(F)) = 0
  $
]
#proof[
  $q >= 3$ 的情形已在 @grothendieck-vanishing-in-dim-1 中处理，故不妨取 $q = 2$。 

  仿照 @grothendieck-vanishing-in-dim-1 的证明，对不可约分支个数作同样的归纳，不妨设 $X$ 不可约。由拓扑不变性把 $X$ 换成其约化，不妨设 $X$ 是整的，即一条曲线。再由极限公式 @limit-formula-for-sheaves 以及对可构造层作 devissage（@constructible-sheaves-first-props (6)），不妨设 $cal(F)$ 是可构造层。 

  由 @constructible-sheaves-first-props (2)，存在稠密开集 $j: U -> X$，使 $cal(F)|_U$ 是 l.c.c.。取补集 $i: Z -> X$，其中 $Z$ 是有限个闭点，赋以诱导的既约子概形结构。现在看 @etale-lower-shriek-first-props (3) 给出的正合列： 
  $
    0 -> j_! (cal(F)|_U) -> cal(F) -> i_* (cal(F)|_Z) -> 0
  $
  其中有 $H^2 (X, i_* (cal(F)|_Z)) = H^2 (Z, cal(F)|_Z) = 0$。因此，要得到所要的消没，只需证明 $H^2 (X, j_! (cal(F)|_U)) = 0$。 

  由于 $cal(F)|_U = j^(-1) cal(F)$ 是 l.c.c.，可以取有限平展覆叠 $pi: V -> U$，使 $pi^(-1) j^(-1) cal(F) cong ul(G)_V$，其中 $G$ 是有限群。 

  #lemma[
    设 $f: X -> Y$ 是平展满射。则由伴随余单位给出的典范态射： 
    $
      f_! f^(-1) cal(F) -> cal(F)
    $
    是满射。 
  ]
  #proof[
    伴随的单位与余单位 
    $
      epsilon_(cal(F)): f_! f^(-1) cal(F) -> cal(F) \
      eta_(cal(G)): cal(G) -> f^(-1) f_! cal(G)
    $
    满足一个恒等式：其复合 
    $
      f^(-1) cal(F) ->^(eta_(f^(-1) cal(F))) f^(-1) f_! f^(-1) cal(F) ->^(f^(-1) epsilon_(cal(F))) f^(-1) cal(F)
    $
    是恒等态射。于是 $f^(-1) epsilon_(cal(F))$ 是满射，再由 @surjective-pullback-conservative，$epsilon_(cal(F))$ 也是满射。 
  ]
  于是得到满射： 
  $
    pi_* ul(G)_V = pi_* pi^(-1) j^(-1) cal(F) ->> j^(-1) cal(F)
  $
  由于 $j_!$ 正合，$j_! pi_* ul(G)_V -> j_! j^(-1) cal(F)$ 是满射。取其核，得短正合列： 
  $
    0 -> cal(K) -> j_! pi_* ul(G)_V -> j_! j^(-1) cal(F) -> 0
  $
  它诱导长正合列： 
  $
        dots.c -> H^2 (X, j_! pi_* ul(G)_V) -> H^2 (X, j_! j^(-1) cal(F)) -> underbrace(H^3 (X, cal(K)), #[由 @grothendieck-vanishing-in-dim-1 得 $0$]) -> dots.c
  $
  因此只需证明 $H^2 (X, j_! pi_* ul(G)_V) = 0$。现在 $j compose pi: V -> X$ 拟有限且分离，故由 Zariski 主定理，可将它分解为： 
  // https://q.uiver.app/#r=typst&q=WzAsNCxbMCwwLCJWIl0sWzEsMSwiWCJdLFswLDEsIlUiXSxbMSwwLCJXIl0sWzIsMSwiaiIsMl0sWzAsMiwicGkiLDJdLFswLDMsImpfMSJdLFszLDEsInBpXzEiXV0=
  #align(center, diagram({
    node((-1, -1), [$V$])
    node((0, 0), [$X$])
    node((-1, 0), [$U$])
    node((0, -1), [$W$])
    edge((-1, 0), (0, 0), [$j$], label-side: right, "->")
    edge((-1, -1), (-1, 0), [$pi$], label-side: right, "->")
    edge((-1, -1), (0, -1), [$h$], label-side: left, "->")
    edge((0, -1), (0, 0), [$pi.alt$], label-side: left, "->")
  }))
  其中 $pi.alt$ 有限，$h$ 是开浸入。我们断言 $j_! pi_* ul(G)_V cong pi.alt_* h_! ul(G)_V$。事实上，由伴随与基变换可以构造出自然映射 $j_! pi_* ul(G)_V -> pi.alt_* h_! ul(G)_V$；它是否为同构，可按 @stalks-of-finite-pushforward 与 @etale-lower-shriek-first-props (2) 在茎上检验。因此只需证明： 
  $
    H^2 (X, j_! pi_* ul(G)_V) = H^2 (X, pi.alt_* h_! ul(G)_V) = H^2 (W, h_! ul(G)_V)
  $
  上式中每一项都消没。 

  取 $Z$ 为 $h: V -> W$ 的概形像，则 $h$ 可分解为： 
  $
    h: V ->^g Z ->^i W
  $ 
  其中 $g$ 是支配开浸入，$i$ 是闭浸入。而 $h_! ul(G)_V = i_* g_! ul(G)_V$：自然映射可由基变换与伴随构造出来，再按 @stalks-of-finite-pushforward 与 @etale-lower-shriek-first-props (2) 在茎上检验，便知它是同构。 
  
  因此 $H^2 (W, h_! ul(G)_V) = H^2 (W, i_* g_! ul(G)_V) = H^2 (Z, g_! ul(G)_V)$。 

  现在令 $g': Y := Z - V -> Z$ 为补闭浸入，其中 $Y$ 赋以诱导的既约子概形结构。由于 $V subset Z$ 是稠密开集，$Y$ 是有限个闭点。考虑正合列： 
  $
    0 -> g_! ul(G)_V -> ul(G)_Z -> g'_* ul(G)_Y -> 0
  $
  它诱导长正合列： 
  $
    dots.c -> H^1 (Z, g'_* ul(G)_Y) -> H^2 (Z, g_! ul(G)_V) -> H^2 (Z, ul(G)_Z) -> dots.c
  $
  现在： 

  - 由于 $Y$ 是有限个闭点，$H^1 (Z, g'_* ul(G)_Y) = H^1 (Y, ul(G)_Y)$； 

  - 由 @artin-vanishing-of-zn，$H^2 (Z, ul(G)_Z) = 0$：这里 $G$ 是有限交换群，且 $Z ->^i W ->^(pi.alt) X$ 有限，故 $Z$ 是 $k$ 上维数 $<=1$ 的有限型仿射概形。 

  于是 $H^2 (Z, g_! ul(G)_V) = 0$，证毕。 
]
