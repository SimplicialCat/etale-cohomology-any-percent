// audit-exception: $$ 展示公式内的 #[...] 谓词块嵌有多段 $...$，朴素配对会把块内文字切成伪公式；译文只改文字，块内公式逐段核对未变。
#import "void-import.typ": *

== 茎 <sect-stalks>

设 $Omega$ 是可分闭域。 

#lemma(name: <struct-of-spec-omega-et>)[
  0. 存在范畴等价： 
    $
      cSet -> Et_(Spec(Omega)), I |-> union.sq.big_(i in I) Spec(Omega)
    $

  + 对任意 $cal(G) in cPSh(Spec(Omega)_et)$，有#h(1fr)
    $
      cal(G) (Spec(Omega)) = cal(G)^\# (Spec(Omega))
    $
    且 $cal(G)^\# (Spec(Omega))$ 是与 $cal(G)(Spec(Omega))$ 相伴的常值层。 

  + 取整体截面 $Gamma (Spec(Omega), -)$ 给出范畴等价： 
    $
      cSh(Spec(Omega)_et) overset(->, tilde) cSet , cAb(Spec(Omega)_et) overset(->, tilde) cAb
    $
]
#proof[
  (0) 全忠实性显然，所以只需证明本质满性，即每个平展 $X -> Spec(Omega)$ 都是若干 $Spec(Omega)$ 副本的不交并。 
  
  对任意平展 $X -> Spec(Omega)$ 与任意点 $x in X$，按定义 $k(x)\/Omega$ 是有限可分扩张。由于 $Omega$ 可分闭，只能有 $k(x) = Omega$。于是包含映射 $Spec(k(x)) -> X -> Spec(Omega)$ 是同构，从而 $Spec(k(x)) -> X$ 是闭浸入。因此 $x$ 是 $X$ 的闭点，其剩余域为 $Omega$。 

  另一方面，固定 $x in X$，任取 $x$ 附近的一个仿射开集 $U = Spec(A) subset X$。则 $U$ 的每个点都是闭点。$A\/Omega$ 是有限型的，故 $A$ 是 Noether 环。再加上 $U$ 的每个点都是闭点，可知 $A$ 是 Artin 环。于是 $U$ 是有限离散概形，从而 ${x}$ 是 $U$ 的开子集，进而是 $X$ 的开子集。 

  换言之，$X$ 的每个点都既开又闭，且剩余域为 $Omega$。因此 
  $
    X cong union.sq.big_(x in X) Spec(Omega)
  $

  (1) 由 (0)，任一平展覆盖 $cal(U) = {U_i -> Spec(Omega)}$ 都被单个平展覆盖 $id: Spec(Omega) -> Spec(Omega)$ 非典范地加细：只需把 $Spec(Omega)$ 到自身的映射经任一 $U_i$ 的任一连通分支 $Spec(Omega)$ 分解。换言之，正向极限 
  $
    cal(G)^+ (Spec(Omega)) = dircolim_(cal(U)) caron(H)^0 (cal(U), cal(G))
  $
  是在一个有最大对象的正向系统上取的。因此存在典范同构： 
  $
    cal(G)^+ (Spec(Omega)) cong caron(H)^0 ({id}, cal(G)) = cal(G) (Spec(Omega))
  $
  把 $(-)^+$ 作用两次，即得 $cal(G)^\# (Spec(Omega)) = cal(G) (Spec(Omega))$。 

  (2) 由 (0) 可知，$Spec(Omega)$ 上的每个平展层 $cal(G)$ 都由它在 $Spec(Omega)$ 上的截面决定：它在 $union.sq.big_(i in I) Spec(Omega)$ 上的截面正是 $product_(i in I) Gamma(Spec(Omega), cal(G))$。换言之，$Spec(Omega)$ 上的每个平展层都是常值层，于是范畴等价显然成立。 
]

#definition(name: <defn-etale-stalk>)[
  对几何点 $overline(x): Spec(Omega) -> X$，定义在 $overline(x)$ 处的*茎*为： 
  $
    (-)_(overline(x)): cSh(X_et) &overset(->, overline(x)^(-1)) cSh(Spec(Omega)_et) overset(->, tilde) cSet, cAb(X_et) overset(->, overline(x)^(-1)) cAb(Spec(Omega)_et) overset(->, tilde) cAb \
    
    cal(F) &|-> cal(F)_(overline(x)) := (overline(x)^(-1) cal(F)) (Spec(Omega))
  $
  #remark[
    点与茎的概念可以在任意景上定义。不过平展景有足够多的点，单射性、满射性都能由茎检测出来，而这种现象在一般的景上并不会出现。 
  ]
]

#properties(name: <stalks-first-props>)[
  + $(-)_(overline(x))$ 与有限极限交换。因此 $(-)_(overline(x)): cAb(X_et) -> cAb$ 是正合函子。 

  + $cal(F)_(ol(x))$ 可以写成滤余极限：#h(1fr)
    $
      cal(F)_(overline(x)) = dircolim_(phi: (U, ol(u)) -> (X, ol(x))) cal(F)(U)
    $
    其中 $U in Et_X$ 取遍带有映到 $ol(x)$ 的几何点 $ol(u)$ 的对象；这样的对象连同几何点才构成 $ol(x)$ 的*平展邻域*。 

  + 给定带基点的态射 $f: (X, overline(x)) -> (Y, overline(y))$，有典范同构 $(f^(-1) cal(G))_(overline(x)) cong cal(G)_(overline(y))$。 
]
#proof[
  (1) 由 $ol(x)^(-1)$ 的相应性质可得。 

  (2) 直接展开 $ol(x)^(-1)_cPSh$ 的定义即可。要计算 $ol(x)^(-1)_cPSh cal(F) (Spec(Omega))$，就要对一切如下形状的图表取滤余极限： 
  // https://q.uiver.app/#r=typst&q=WzAsNCxbMCwwLCJTcGVjKE9tZWdhKSJdLFswLDEsIlNwZWMoT21lZ2EpIl0sWzEsMCwiVSJdLFsxLDEsIlgiXSxbMSwzLCJvbCh4KSIsMl0sWzAsMiwib2wodSkiXSxbMiwzXSxbMCwxXV0=
  #align(center, diagram({
    node((-1, -1), [$Spec(Omega)$])
    node((-1, 0), [$Spec(Omega)$])
    node((0, -1), [$U$])
    node((0, 0), [$X$])
    edge((-1, 0), (0, 0), [$ol(x)$], label-side: right, "->")
    edge((-1, -1), (0, -1), [$ol(u)$], label-side: left, "->")
    edge((0, -1), (0, 0), "->")
    edge((-1, -1), (-1, 0), "=")
  }, spacing: 2em))
  而这正是在 $(X, ol(x))$ 的所有平展邻域上取的滤余极限。于是 
  $
    ol(x)^(-1) cal(F) (Spec(Omega)) = (ol(x)^(-1)_cPSh cal(F))^\# (Spec(Omega)) = ol(x)^(-1)_cPSh cal(F) (Spec(Omega))
  $
  这在此前已经证过。 

  (3) 由 $ol(x)^(-1) compose f^(-1) = (f compose ol(x))^(-1) = ol(y)^(-1)$ 可得。 
]

#definition(name: <defn-germs-and-support>)[
  设 $cal(F) in cSh(X_et)$，$U in Et_X$，$ol(u)$ 是 $U$ 的几何点。则 $(U, ol(u))$ 是 $(X, ol(u))$ 的平展邻域，于是诱导出自然态射： 
  $
    (-)_(ol(u)): cal(F)(U) -> cal(F)_(ol(u))
  $
  对截面 $s in cal(F)(U)$，称 $s_(ol(u))$ 为 $s$ 在 $ol(u)$ 处的*芽* (germ)。显然这个构造与限制相容（展开 $cal(F)_(ol(u))$ 的滤余极限定义即可看出）。 

  定义 $s in cal(F)(U)$ 的*支集* (support) 为集合： 
  $
    supp(s) := {u in U: exists#[一个几何点 $ol(u)$，位于 $u$ 上方且满足 $s_(ol(u)) != 0$]}
  $
]

本节余下的内容只用 $cAb(X_et)$ 来叙述。你要记住，这些结果对 $cSh(X_et)$ 都有类似版本，只是本课程主要与交换群层打交道。 

#lemma(name: <vanishing-stalks-spreads-out>)[
  设 $cal(F) in cAb(X_et)$，$s in cal(F)(U)$，$ol(u)$ 是 $U$ 的几何点，位于 $u in U$ 上方，且 $s_(ol(u)) = 0$。则存在 Zariski 邻域 $u in V subset U$，使得 $s|_V = 0$。 

  特别地， 
  $
    supp(s) &= {u in U: exists#[一个几何点 $ol(u)$，位于 $u$ 上方且满足 $s_(ol(u)) != 0$]} \
    &= {u in U: forall#[位于 $u$ 上方的几何点 $ol(u)$，$s_(ol(u)) != 0$]} subset U
  $
  是 $U$ 的闭子集。 
  // 因此，若存在子集 $E subset U$ 与 $U$ 的每个非空闭子集都相交
]
#proof[
  由于 $cal(F)_(ol(u))$ 是滤余极限： 
  $
    cal(F)_(ol(u)) = dircolim_((V,ol(v)) -> (X,ol(u))) cal(F)(V)
  $
  而 $s in cal(F)(U)$ 在这个滤余极限中的像是 $0$，这意味着存在平展邻域 $phi: (W, ol(w)) -> (U, ol(u))$ 使得 $s|_W = 0$。此时 $phi(W)$ 是 $U$ 中含 $u$ 的开子集，而 $phi: W -> phi(W)$ 是满射平展，从而是 $phi(W)$ 的平展覆盖。于是 
  $
    s|_W = (s|_(phi(W)))|_W = 0
  $
  由层条件即得 $s|_(phi(W)) = 0$。取 $V = phi(W)$ 便完成了证明。 

  至于 $supp(s)$ 的条件，注意若 $u in U - supp(s)$，则对 $u in U$ 的某个 Zariski 邻域 $V$ 有 $s|_V = 0$。于是对 $V$ 中任一点上方的所有几何点 $ol(v)$ 都有 $s_(ol(v)) = 0$。因此 $supp(s)$ 的定义中对 $ol(u)$ 的存在量词可以换成全称量词，且 $V subset U - supp(s)$。所以 $U - supp(s)$ 是 $U$ 的开子集，从而 $supp(s) subset U$ 是闭的。  
]

#proposition(name: <stalks-detects-properties>)[
  0. 给定 $cal(F) in cAb(X_et)$ 以及 $X$ 的两个位于同一点 $x in X$ 上方的几何点 $ol(x)_1, ol(x)_2$，存在非典范同构： 
    $
      cal(F)_(ol(x)_1) cong cal(F)_(ol(x)_2)
    $

  + 给定 $cal(F) in cAb(X_et)$，以下条件等价： 
    + $cal(F) = 0$； 
    + 对 $X$ 的每个几何点 $ol(x)$ 都有 $cal(F)_(ol(x)) = 0$； 
    + 存在子集 $E subset X$，使它与 $X$ 的每个非空局部闭子集都相交，且对每个 $x in E$，存在 $X$ 的某个位于 $x$ 上方的几何点 $ol(x)$ 使 $cal(F)_(ol(x)) = 0$。 

  + 取茎与取核、余核、像交换。 

  + 以下条件等价： 
    + $X$ 上平展层的态射 $cal(F) -> cal(G)$ 是单射/满射/同构/零态射，或者 $cal(F) -> cal(G) -> cal(H)$ 在中间正合。 
    + 对 $X$ 的每个几何点 $ol(x)$，$cal(F)_(ol(x)) -> cal(G)_(ol(x))$ 或 $cal(F)_(ol(x)) -> cal(G)_(ol(x)) -> cal(H)_(ol(x))$ 满足同样的条件； 
    + 存在子集 $E subset X$，使它与 $X$ 的每个非空局部闭子集都相交，且对每个 $x in E$，存在 $X$ 的某个位于 $x$ 上方的几何点 $ol(x)$，使 $cal(F)_(ol(x)) -> cal(G)_(ol(x))$ 或 $cal(F)_(ol(x)) -> cal(G)_(ol(x)) -> cal(H)_(ol(x))$ 满足同样的条件。 
]
#proof[
  (0) 取 $ol(x) = Spec(k(x)^sep)$ 为 $k(x)$ 的可分闭包，作为 $x$ 上方的一个几何点。只需证明 $cal(F)_(ol(x)) cong cal(F)_(ol(x)_1)$。 

  事实上，设 $ol(x)_1: Spec(Omega) -> X$。由于 $Omega$ 包含 $k(x)$ 且可分闭，我们可以选取非典范的嵌入 $k(x)^sep -> Omega$（在 $k(x)$ 上）。这给出分解 $ol(x)_1: Spec(Omega) ->^(ol(xi)) Spec(k(x)^sep) ->^(ol(x)) X$。此时 
  $
    (ol(x)^(-1) cal(F))_(ol(xi)) = cal(F)_(ol(x_1))
  $
  而 $ol(x)^(-1) cal(F)$ 是与 $cal(F)_(ol(x))$ 相伴的常值层，因而在任意几何点处的茎都是 $cal(F)_(ol(x))$。 

  (2) 由 $(-)_(ol(x))$ 的正合性可得。考虑态射 $f: cal(F) -> cal(G)$，可以写出正合列： 
  $
    0 -> ker(f) -> cal(F) ->^f cal(G) -> coker(f) -> 0
  $
  在 $ol(x)$ 处取茎，得到正合列： 
  $
    0 -> ker(f)_(ol(x)) -> cal(F)_(ol(x)) ->^(f_(ol(x))) cal(G)_(ol(x)) -> coker(f)_(ol(x)) -> 0
  $
  这说明 $ker(f)_(ol(x)) = ker(f_(ol(x)))$，$coker(f)_(ol(x)) = coker(f_(ol(x)))$。像既是余核的核，所以也与取茎交换。 

  (1) (a) $==>$(b) $==>$(c) 显然，所以只需证 (c) $==>$(a)。 

  给定任意 $(f: U -> X) in Et_X$ 与任意截面 $s in cal(F)(U)$，我们要证明 $s = 0$。此外还假设 $U$ 仿射，且 $f(U)$ 含于 $X$ 的某个仿射开集中。反设 $s != 0$。令 $Z = supp(s) subset U$，它是 $U$ 的闭子集。由于 $s != 0$，$Z$ 必非空。 

  取 $X$ 的仿射开集 $X_0$ 包含 $f(U)$，于是 $f$ 分解为 $f: U ->^(f_0) X_0 -> X$。此时 $f_0$ 仿射（从而拟紧），且是有限展示的。由 Chevalley 定理（比如 #cite-stacks("054K", [Theorem 29.22.3]) 中的版本），$f(Z)$ 是 $X_0$ 的非空可构造子集。于是它含有 $X_0$ 的非空局部闭子集，从而含有 $X$ 的非空局部闭子集。 

  按我们对 $E$ 的假设，存在 $x in E$ 使 $x in f(Z)$。取 $x$ 上方的任一几何点 $ol(x)$，由 (0) 有 $cal(F)_(ol(x)) = 0$；再取 $z in Z$ 使 $x = f(z)$。由于 $f$ 平展，存在 $z$ 上方的几何点 $ol(z)$ 使 $ol(x) = f(ol(z))$。那么 $s_(ol(z)) != 0$，而它却是零群 $cal(F)_(ol(x)) = 0$ 中的元素，矛盾。 

  换言之，对任意仿射 $U in Et_X$，只要它在 $X$ 中的像含于一个仿射开集，就有 $cal(F)(U) = 0$。而任一 $U in Et_X$ 都能被足够小、且满足此条件的仿射开集覆盖，由层条件即知对一切 $U in Et_X$ 有 $cal(F)(U) = 0$，故 $cal(F) = 0$。 

  (3) 不过是 (1) 与 (2) 的结合。 
]
#remark(name: <very-dense-sets-of-pts>)[
  子集 $E subset X$ 与每个非空局部闭子集都相交，这个条件称为*极稠密* (very dense)。常见的极稠密子集有： 

  + 平凡地，$E = X$； 

  + 若 $x: Spec(k(x)) -> X$ 是有限型态射，则称点 $x in X$ 为*有限型点* (finite type point)。$X$ 的有限型点构成的子集总是 $X$ 中的极稠密子集。（#cite-stacks("02J4", [Lemma 29.16.7])）

  + 若概形的闭点集极稠密，或者等价地说，每个有限型点都是闭点，则称该概形为 *Jacobson* 概形。（#cite-stacks("01TB", [Lemma 29.16.8])）在 Jacobson 概形中，取 $E$ 为闭点集即可。 

    常见的 Jacobson 概形包括域上的有限型概形，以及一维且有无穷多个素理想的 Noether 整环（例如数域的整数环，特别是 $ZZ$）上的有限型概形。（#cite-stacks("02J6", [Lemma 29.16.10])） 
    
    一个著名的非 Jacobson 概形是离散赋值环的谱。 
]

#corollary[
  $cAb(X_et)$ 中的链复形 $0 -> cal(F) -> cal(G) -> cal(H)$ 左正合，当且仅当对每个 $U in Et_X$， 
  $
    0 -> cal(F)(U) -> cal(G)(U) -> cal(H)(U)
  $
  都左正合。此外，只需对这样的仿射 $U in Et_X$ 检验这一点：它在 $X$ 中的像含于某个仿射开集。 
]
#proof[
  ($==>$) 就是 $Gamma(U, -)$ 的左正合性，我们在 @sections-left-exact 中证过。 

  至于 ($<==$)，只需证明对每个几何点 $ol(x)$，茎上的序列 
  $
    0 -> cal(F)_(ol(x)) -> cal(G)_(ol(x)) -> cal(H)_(ol(x))
  $
  左正合。把茎写成滤余极限，就是： 
  $
    0 -> dircolim_((U,ol(u)) -> (X, ol(x))) cal(F)(U) -> dircolim_((U,ol(u)) -> (X, ol(x))) cal(G)(U) -> dircolim_((U,ol(u)) -> (X, ol(x))) cal(H)(U)
  $
  而这是左正合列 $0 -> cal(F)(U) -> cal(G)(U) -> cal(H)(U)$ 的滤余极限。不过 $cAb$ 满足 (Ab5) 条件，即滤余极限正合，所以证毕。 

  $(X, ol(x))$ 的每个平展邻域都被某个 $(V, ol(v))$ 加细，其中 $V$ 仿射，且它在 $X$ 中的像含于 $X$ 的某个仿射开集，因此后一个论断成立。 
]

#corollary(name: <surjective-pullback-conservative>)[
  对概形间的任意满射 $f: X -> Y$，$f^(-1): cAb(Y_et) -> cAb(X_et)$ 是保守函子。也就是说，$cAb(Y_et)$ 中的态射 $phi: cal(F) -> cal(G)$ 是单射/满射/同构/零态射，当且仅当 $f^(-1) phi: f^(-1) cal(F) -> f^(-1) cal(G)$ 也如此。 
]
#proof[
  ($==>$) 是 $f^(-1)$ 的正合性，所以只验证 ($<==$)。只需证明对每个 $y in Y$，存在 $y$ 上方的几何点 $ol(y)$ 使 $cal(F)_(ol(y)) -> cal(G)_(ol(y))$ 是单射/满射/同构/零态射。由于 $f$ 满射，可以取 $x in X$ 使 $f(x) = y$。取 $x$ 上方的任一几何点 $ol(x)$，令 $ol(y) = f(ol(x))$ 作为 $y$ 上方的几何点。既然 $f^(-1) phi: f^(-1) cal(F) -> f^(-1) cal(G)$ 是单射/满射/同构/零态射，$(f^(-1) cal(F))_(ol(x)) -> (f^(-1) cal(G))_(ol(x))$ 也有同样的性质；而由 @stalks-first-props (3)，它就是 $cal(F)_(ol(y)) -> cal(G)_(ol(y))$。证毕。 
]

#example[
  概形 $X$ 上有两个重要的平展层正合列： 

  - 若 $n in cal(O)_X (X)^times$ 且为正整数，就有*Kummer 序列*：#h(1fr)
    $
      0 -> mu_n arrow.r.hook GG_m -->^(x |-> x^n) GG_m -> 0
    $
    回忆 $mu_n (U) = mu_n (cal(O)_U (U))$ 是 $cal(O)_U (U)$ 中的 $n$ 次单位根，而 $GG_m (U) = cal(O)_U (U)^times$ 是 $cal(O)_U (U)$ 的可逆元（单位）全体。这个序列左正合，因为它在截面上显然左正合： 
    $
      0 -> mu_n (cal(O)_U (U)) -> cal(O)_U (U)^times -->^(x |-> x^n) cal(O)_U (U)^times 
    $
    剩下要证 $GG_m -->^(x |-> x^n) GG_m$ 满射，这是平展层特有的结果，对 Zariski 层不成立。需要证明：对任意 $s in cal(O)_U (U)^times$，存在 $U$ 的平展覆盖，使 $s$ 在每一块上都有 $n$ 次方根。为此取*Kummer 覆叠*： 
    $
      U' = SPec((cal(O)_U [T])/((T^n - s)))
    $
    它是 $U$ 的有限平展覆叠。回忆它平展是因为 $(T^n - s)' = n T^(n-1)$，而 $n in cal(O)_X^times$，故 $n in cal(O)_U^times$，从而 $gcd(T^n - s, n T^(n-1)) = 1$。 

    现在 $s|_(U') = T^n$，证毕。 

  - 若 $p$ 是素数且 $X$ 是 $FF_p$ 上的概形，就有 Artin–Schreier 序列： 
    $
      0 -> ul(ZZ\/p) arrow.r.hook GG_a -->^(x |-> x^p - x) GG_a -> 0 
    $
    这里的态射 $ul(ZZ\/p) -> GG_a$，是对如下预层态射作层化的结果：在每个 $U in Et_X$ 上，该预层态射由包含 $FF_p arrow.r.hook cal(O)_U (U)$ 给出；层化正合，所以它是单射。对每个仿射 $U = Spec(A) in Et_X$，序列在 $U$ 上截面中的左半部分是： 
    $
      0 -> C(U; ZZ\/p) -> A -->^(x |-> x^p - x) A 
    $
    展开定义可知，第一个态射的构造如下：给定局部常值函数 $f: U -> ZZ\/p$，$f^(-1)(a)$（$a in FF_p$）把 $U = Spec(A)$ 分成 $p$ 个开闭集。这对应于 $A$ 的一族正交幂等元 ${e_a}_(a in FF_p)$。于是该态射为： 
    $
      C(U; ZZ\/p) -> A, f |-> sum_(a in FF_p) e_a a
    $
    设 $x in A$ 满足 $x^p - x = 0$，即 $product_(a in FF_p) (x-a) = 0$。此时 ${x-a}_(a in FF_p)$ 两两互素且乘积为 $0$，故由中国剩余定理有同构： 
    $
      A cong product_(a in FF_p) A\/(x-a)
    $
    换言之，存在一族正交幂等元 ${e_a}_(a in FF_p)$，使得 $e_a = 1 mod (x-a)$，且对 $a != b in FF_p$，相应的幂等元同余于 $0 mod (x-b)$。此时 $x$ 在 $A\/(x-a)$ 中的像为 $a$，所以在这个同构下 $x$ 被送到 $(0, 1, dots.c, p-1)$，从而 $x = sum_(a in FF_p) e_a a$ 来自 $C(U; ZZ\/p)$ 中的元素。 

    换言之，$0 -> C(U; ZZ\/p) -> A -->^(x |-> x^p - x) A$ 左正合。于是 $0 -> ul(ZZ\/p) arrow.r.hook GG_a -->^(x |-> x^p - x) GG_a$ 左正合，剩下要证 $GG_a -->^(x |-> x^p - x) GG_a$ 满射。 

    这里沿用 Kummer 序列的策略，只不过对 $s in cal(O)_U (U)$ 改用*Artin–Schreier* 覆叠，它也是有限平展覆叠： 
    $
      U' = Spec((cal(O)_U [T])/((T^p - T - s)))
    $
]

最后，还有我们先前许诺过的另一种方法，用来证明 $cAb(X_et)$ 有足够多的内射对象。 

#example[
  设 $ol(x)$ 是 $X$ 的几何点，$M in cAb$。可以把 $M$ 看作 $cAb(ol(x)_et)$ 中的常值层，并把它推前为 $ol(x)_* M in cAb(X_et)$。这个层称为与 $M$ 相伴、位于 $ol(x)$ 处的*摩天楼层* (skyscraper sheaf)。//容易验证，典范映射 $ol(x)^(-1) ol(x)_* M -> M$ 是同构，即 $(ol(x)_* M)_(ol(x)) = M$。

  摩天楼层的茎可能很难显式计算，但至少知道它在何处消没： 
  #lemma(name: <stalks-of-skyscraper-sheaves>)[
    设 $ol(y)$ 是 $X$ 的几何点。若 $x$ 不一般化 $y$，则 $(ol(x)_* M)_(ol(y)) = 0$。 
  ]
  #proof[
    若 $x$ 不一般化 $y$，取 Zariski 开集 $V subset X$ 使 $y in V, x in.not V$。对任意平展邻域 $(U, ol(u)) -> (X, ol(y))$，若 $U$ 在 $X$ 中的像不含 $x$，则 $ol(x)_* M (U) = ul(M)_(ol(x)) (U_(ol(x))) = 0$。而任意平展邻域 $(U, ol(u)) -> (X, ol(y))$ 都被 $(U times_X V, ol(u))$ 加细，后者在 $X$ 中的像不含 $x$，所以定义茎的滤余极限为 $0$。 
  ]
  
  给定任意层 $cal(F) in cAb(X_et)$ 与任意态射 $cal(F)_(ol(x)) -> M$，即态射 $ol(x)^(-1) cal(F) -> M$，由伴随性存在唯一的态射 $cal(F) -> ol(x)_* M$ 诱导它。 
]

#construction(name: <injective-godement-resolution>)[
  （内射 Godement 消解）还有另一种证明 $cAb(X_et)$ 有足够多的内射对象的方法，它不用 Grothendieck 的 Tohoku 定理，好处是显式而且具有函子性。这就是 Godement 消解。 

  首先回忆，在 $cAb$ 中，任意对象都可以嵌入一个内射对象： 
  $
    M -> I(M) := product_(chi in Hom(M, QQ\/ZZ)) QQ\/ZZ, x |-> (chi(x))_chi
  $
  而这一构造对 $M$ 具有函子性。 

  对每个 $x in X$，取 $x$ 上方的一个几何点 $ol(x)$。//此时 $ol(x)^(-1)cal(F) $ 就是 $cal(F)_(ol(x)) in cAb cong cAb(ol(x)_et) $，于是嵌入 $I(cal(F)_(ol(x))) in cAb cong cAb(ol(x)_et) $。这定义了态射 $ol(x)^(-1) cal(F) -> I(cal(F)_(ol(x))) $，由伴随性得到态射 $cal(F) -> ol(x)_* I(cal(F)_(ol(x))) $。 
  由包含 $cal(F)_(ol(x)) -> I(cal(F)_(ol(x)))$，得到指向摩天楼层的态射 $cal(F) -> ol(x)_* I(cal(F)_(ol(x)))$。 

  取直积，就定义了态射： 
  $
    gamma: cal(F) -> product_(x in X) ol(x)_* I(cal(F)_(ol(x)))
  $

  // 在每个几何点 $ol(x)$ 处，$gamma$ 诱导茎上的态射 $cal(F)_(ol(x)) -> I(cal(F)_(ol(x))) times dots.c$，且是单射。因此 $gamma$ 是单射。$ol(x)_*$ 有正合的左伴随，从而保持内射对象，所以 $product_(x in X) ol(x)_* I(cal(F)_(ol(x)))$ 是内射对象的直积，因而内射。 

  // 这给出了 $cal(F)$ 到内射对象的显式嵌入。该构造具有函子性，并且除了几何点族 ${ol(x)}_(x in X)$ 的选取#footnote[……只要你接受选择公理，这就不算什么大问题。]之外是典范的。 

  我们断言这个态射是单射。事实上，给定任意 $(f: U -> X) in Et_X$，要证明 
  $
    cal(F)(U) -> product_(x in X) (ol(x)_* I (cal(F)_(ol(x))))(U) = product_(x in X) product_(ol(u) in f^(-1)(ol(x))) cal(F)_(ol(x))
  $
  是单射。若 $s in cal(F)(U)$ 的像为零，则对每个 $ol(u) in f^(-1)(ol(x))$，芽 $s_(ol(u)) = 0$。$U$ 的每个点上方都有这种形状的几何点 $ol(u)$，故由 @vanishing-stalks-spreads-out 得 $s = 0$。因此 $gamma$ 是单射。 
]

除了这个内射 Godement 消解，实际上还有零调 Godement 消解： 

#lemma(name: <geom-point-pushforward-exact>)[
  设 $ol(x): Spec(Omega) -> X$ 是几何点，则 $ol(x)_*$ 是正合函子。
]
#proof[
  由 @struct-of-spec-omega-et，$cAb(Spec(Omega)_et) cong cAb$。现在给定交换群的正合列：
  $
    0 -> A -> B -> C -> 0
  $
  考虑它在 $ol(x)_*$ 之后的序列：
  $
    0 -> ol(x)_* A -> ol(x)_* B -> ol(x)_* C -> 0
  $
  在 $(f: U -> X) in Et_X$ 的截面上看，这就是：
  $
    0 -> product_(ol(u) in f^(-1)(ol(x))) A -> product_(ol(u) in f^(-1)(ol(x))) B -> product_(ol(u) in f^(-1)(ol(x))) C -> 0
  $
  它正合，因为它是正合列 $0 -> A -> B -> C -> 0$ 的直积。于是 $0 -> ol(x)_* A -> ol(x)_* B -> ol(x)_* C -> 0$ 正合。
]

#proposition(name: <acyclic-godement-resolution>)[
  对任意概形 $X$，在每个 $x in X$ 上方固定一个几何点，构成几何点系统 ${ol(x)}$。对任意 $cal(F) in cAb(X_et)$，
  $
    cal(C)^0 (cal(F)) := product_(x in X) ol(x)_* cal(F)_(ol(x))
  $
  满足：由 $ol(x)_*$ 与 $ol(x)^(-1)$ 的伴随性诱导的典范映射 $cal(F) -> cal(C)^0 (cal(F))$ 是单射，而且 $cal(C)^0 (cal(F))$ 是零调的，即
  $
    H^q (X, cal(C)^0 (cal(F))) = 0, forall q >= 1
  $
  于是取 $cal(C)^1 (cal(F)) = cal(C)^0 (coker(cal(F) -> cal(C)^0 (cal(F))))$，如此类推，就归纳构造出零调消解：
  $
    0 -> cal(F) -> cal(C)^0 (cal(F)) -> cal(C)^1 (cal(F)) -> dots.c -> cal(C)^p (cal(F)) -> dots.c
  $
  它对 $cal(F)$ 具有函子性。
]
#proof[
  零调性可由 Leray 谱序列 @derived-lower-star-first-props (2) 与上面证明的 $ol(x)_*$ 正合性推出。由于 $ol(x)_*$ 正合，$R^q ol(x)_* = 0$（$q >= 1$），故谱序列
  $
    H^p (X, R^q ol(x)_* A) ==> H^(p+q) (ol(x), A)
  $
  退化，给出同构：
  $
    H^q (X, ol(x)_* A) cong H^q (ol(x), A) = 0
  $
  对一切 $q >= 1$ 成立。因此 $cal(C)^0 (cal(F))$ 作为形如 $ol(x)_* A$ 的层的直积是零调的。
  
  接下来证明自然映射
  $
    gamma: cal(F) -> cal(C)^0 (cal(F)) = product_(x in X) ol(x)_* cal(F)_(ol(x))
  $
  是单射。这与 @injective-godement-resolution 中的证明相同。事实上，给定任意 $(f: U -> X) in Et_X$，要证明
  $
    cal(F)(U) -> product_(x in X) (ol(x)_* cal(F)_(ol(x)))(U) = product_(x in X) product_(ol(u) in f^(-1)(ol(x))) cal(F)_(ol(x))
  $
  是单射。若 $s in cal(F)(U)$ 的像为零，则对每个 $ol(u) in f^(-1)(ol(x))$，芽 $s_(ol(u)) = 0$。$U$ 的每个点上方都有这种形状的几何点 $ol(u)$，故由 @vanishing-stalks-spreads-out 得 $s = 0$。因此 $gamma$ 是单射。
]

这个零调 Godement 消解的好处在于：若 $cal(F)$ 是 $n$-挠的，则它的茎也如此，从而 $cal(C)^0 (cal(F))$ 也是 $n$-挠的。于是某些只对挠层 (torsion sheaf) 成立的结果也就能用上了。 
