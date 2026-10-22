#import "void-import.typ": *

（注：这里的 Tsen 指中国数学家曾炯（1898–1940），他是 Emmy Noether 的学生。看来当时 Noether 身边的人做了大量代数。）

曲线函数域就是代数闭域 $k$ 上 $k(t)$ 的有限扩张；曾炯定理描述的正是它的代数性质。这为计算曲线的上同调提供了关键输入。 
#let inf = math.op(limits: false)[inf]
#definition(name: <defn-c1-field>)[
  若对任意 $1 <= d < n$，每个次数为 $d$ 的非常数齐次多项式 $f(x_1, dots.c, x_n) in K[x_1, dots.c, x_n]$ 都有非平凡解，则称域 $K$ 为 *$C_1$/拟代数闭 (quasi-algebraically closed)*。
]

#proposition(name: <brauer-grp-of-c1-field-trivial>)[
  若 $K$ 是 $C_1$ 域，则 Brauer 群 $"Br"(K) := H^2_"cont" (Gal_K, (K^sep)^times) = 0$。
]
#proof[
  （Brauer 群的基础知识，请参考代数数论课程。）
  
  只需证明：若 $D$ 是 $K$ 上的中心可除代数，则 $D cong K$。
  
  考虑约化范数 (reduced norm) $"Nrd": D -> K$，它是乘性的（即保持乘法）。（定义如下：存在有限 Galois 扩张 $L\/K$，使得 $D_L overset(cong, alpha) "Mat"_r (L)$ 作为 $L$-代数。考虑映射 $D_L overset(->, alpha) "Mat"_r (L) overset(->, det) L$。于是由 Skolem-Noether，任意两个这样的 $alpha$ 相差内共轭。因此这个范数是 $Gal(L\/K)$-不变的，并下降为映射 $"Nrd": D -> K$。）
  
  观察到 $D$ 是可除代数，且 $"Nrd"$ 保持乘法，因此 $"Nrd"(x) = 0 <==> x = 0$。
  
  现在取 $D$ 的一组 $K$-基 $e_1, dots.c, e_(r^2)$，并令：
  $
    f(x_1, dots.c, x_(r^2)) := "Nrd"(x_1 e_1 + dots.c + x_(r^2) e_(r^2))
  $
  这是次数为 $r$ 的齐次多项式：基变换到 $L$ 后，$f$ 就是行列式，所以次数为 $r$。
  
  现在 $"Nrd"(x) = 0 <==> x = 0$，所以 $f$ 只有平凡零点。由 $C_1$ 条件，这给出 $r >= r^2$。于是 $r = 1$，从而 $D = K$。
]

#lemma(name: <finite-ext-of-c1-field-is-c1>)[
  若 $K$ 是 $C_1$ 域，则对任意有限扩张 $L\/K$，$L$ 亦然。 
]
#proof[
  不妨设 $L\/K$ 是次数为 $s$ 的有限扩张。
  
  取：
  $
    f(x_1, dots.c, x_n) = sum_(i=(i_1,dots.c,i_n) \ i_1+dots.c+i_n = d) a_i arrow(x)^i, a_i in L
  $
  取定 $L$ 的一组 $K$-基 $e_1, dots.c, e_s$，考虑 $n s$ 个未定元 $y_(j,k), 1<=j<=n, 1<=k<=s$，并记 $x_j (arrow(y)) = y_(j,1) e_1 + dots.c + y_(j,s) e_s$。考虑：
  $
    g(arrow(y)) = Nm_(L\/K) (f(arrow(x)(arrow(y))))
  $
  于是这是关于 $n s$ 个变量的次数为 $d s$ 的齐次多项式，故由第一步，$g$ 在 $K$ 中有非零解 $arrow(y)$。这给出 $arrow(x)$ 在 $L$ 中的非零解。 
]

#theorem(name: <tsen-theorem>)[
  (Tsen) 若 $K$ 是某个代数闭域上超越次数为 $1$ 的扩域，则 $K$ 是 $C_1$ 域。特别地，
  $
    H^2_et (Spec(K), GG_m) = H^2_"cont" (Gal_K, (K^sep)^times) = "Br"(K) = 0
  $
]
#proof[
  第一步：先考虑 $K = k(t)$，即最简单的函数域情形。假设 $d < n$，并设：
  $
    f(x_1, dots.c, x_n) = sum_(i=(i_1,dots.c,i_n) \ i_1+dots.c+i_n = d) a_i arrow(x)^i
  $
  （这里记 $x^i = x_1^(i_1) dots.c x_n^(i_n)$。）我们要找 $f$ 的非零解。不妨设每个 $a_i in k[t] subset K$，并令 $delta = max_i (deg(a_i))$。
  
  固定 $N$，考虑未定元 $y_(j,k), 1<=j<=n, 0<=k<=N$。令 $x_j (arrow(y)) = y_(j,N) t^N + dots.c + y_(j,1) t + y_(j,0)$。现在考虑：
  $
    g(arrow(y)) = f(x_1 (arrow(y)), dots.c, x_n (arrow(y))) in k[t, y_(1,0), dots.c, y_(n,N)]
  $
  其中 $deg_t (g) <= delta + d N$。
  
  考虑方程 $g(arrow(y)) = 0$。它等价于说，$t^ell, 0 <= ell <= d N + delta$ 的系数全为零。于是我们得到关于变量 $arrow(y)$ 的 $(delta + d N + 1)$ 个方程，而变量共有 $n(N+1)$ 个。由假设 $n>d$，当 $N$ 充分大时，$arrow(y)$ 有非零解；取 $arrow(x) = arrow(x)(arrow(y))$，便得到 $f(arrow(x)) = 0$ 的非零解（即非平凡解）。
  
  第二步：现在考虑一般情形。取一个在 $k$ 上超越的元素 $t in K$，则 $K$ 是 $k(t)$ 的一族有限扩张的并。
  
    要找一个齐次多项式的根，可以先取出它的系数；这些系数生成 $K$ 的一个有限生成子域，因而包含在 $k(t)$ 的某个有限扩张 $L$ 中。由前一条引理，$L$ 作为 $k(t)$ 的有限扩张是 $C_1$ 域，于是可以在 $L$ 中找到该多项式方程的非平凡解，从而在 $K$ 中也有非平凡解。 
]

现在应用曾炯定理，得到关于上同调的一些推论：

#theorem(name: <tsen-thm-in-galois-cohom>)[
  假设 $K$ 是 $C_1$ 域（特别地，可以是代数闭域 $k$ 上超越次数为 $1$ 的任意扩域）。 
  
  + 对任意离散挠 $Gal_K$-模 $M$，$H^q_"cont" (Gal_K, M) = 0, forall q >= 2$；
  
  + $H^q_"cont" (Gal_K, (K^sep)^times) = 0, forall q >= 1$。
]
#proof[
  （1）我们要对 $M$ 作 devissage。 

  第一步。对 $n >= 1$ 与任意有限可分扩张 $L\/K$，
  $
    H^2_#[cont] (Gal_L, ZZ\/n) = 0
  $
  #proof[
    由 @finite-ext-of-c1-field-is-c1 可知，$L$ 也是 $C_1$ 域，故不妨设 $L = K$。 

    利用正合列 $0 -> ZZ\/m -> ZZ\/m n -> ZZ\/n -> 0$，可以看出只需对所有素数 $n = p$ 证明。 

    情形 1。$p != "char"(K)$。考虑 Kummer 序列： 
    $
      0 -> mu_p (K^sep) -> (K^sep)^times -> (K^sep)^times -> 0
    $
    这是离散 $Gal_K$-模的正合列，于是有正合列： 
    $
      dots.c -> H^1_#[cont] (Gal_K, (K^sep)^times) -> H^2_#[cont] (Gal_K, mu_p (K^sep)) -> H^2_#[cont] (Gal_K, (K^sep)^times) -> dots.c
    $
    现在由 Hilbert 90，$H^1_#[cont] (Gal_K, (K^sep)^times) = 0$；由 @brauer-grp-of-c1-field-trivial，$H^2_#[cont] (Gal_K, (K^sep)^times) = 0$。因此 $H^2_#[cont] (Gal_K, mu_p (K^sep)) = 0$。 

    然而 $mu_p (K^sep) cong ZZ\/p$ 作为 $Gal_K$-模未必成立，因为 $K$ 未必包含全部 $p$ 次单位根。为此，令 $L = K(zeta_p)$，即给 $K$ 添加一个（等价地，任意一个）$p$ 次单位根所得的域，并考虑限制–余限制复合： 
    $
      H^2 (Gal_K, ZZ\/p) ->^#[res] H^2 (Gal_L, ZZ\/p) ->^#[cores] H^2 (Gal_K, ZZ\/p)
    $
    由群上同调理论，这不过是乘以 $[L:K]$。注意 $H^2 (Gal_K, ZZ\/p)$ 是 $p$-挠的，而 $gcd(p, [L:K]) = 1$。因此这个复合是同构，于是限制映射 $H^2 (Gal_K, ZZ\/p) ->^#[res] H^2 (Gal_L, ZZ\/p)$ 是单射。从而只需证明 $H^2 (Gal_L, ZZ\/p) = 0$。但 $L$ 是 $K$ 的有限扩张，故由 @finite-ext-of-c1-field-is-c1 知它是 $C_1$ 域。因此 $H^2 (Gal_L, mu_p (K^sep)) = 0$。而 $L$ 确实包含全部 $p$ 次单位根，故 $mu_p (K^sep) cong ZZ\/p$ 作为 $Gal_L$-模成立，证毕。 

    情形 2。$p = "char"(K) > 0$。考虑 Artin–Schreier 序列： 
    $
      0 -> ZZ\/p -> K^sep -->^(x |-> x^p - x) --> K^sep -> 0
    $
    这是 $Gal_K$-模的正合列。有正合列：
    $
      dots.c -> H^1_#[cont] (Gal_K, K^sep) -> H^2_#[cont] (Gal_K, ZZ\/p) -> H^2_#[cont] (Gal_K, K^sep) -> dots.c
    $
    然而由加性 Hilbert 90，$H^q_#[cont] (Gal_K, K^sep) = 0$ 对所有 $q >= 1$ 成立。（也可以从平展的观点看：$H^q_#[cont] (Gal_K, K^sep) = H^q_et (Spec(K), cal(O)_(Spec(K))) = H^q_#[Zar] (Spec(K), cal(O)_(Spec(K))) = 0$ 对所有 $q >= 1$ 成立，不过那有点小题大做。）因此，
    $
      H^2_#[cont] (Gal_K, ZZ\/p) = 0
    $
    #suppress-qed
  ]

  第二步。假设对固定的 $q >= 2$、所有有限可分扩张 $L\/K$ 与所有 $n >= 1$，都有：
  $
    H^q_#[cont] (Gal_L, ZZ\/n) = 0
  $
  则对所有有限可分扩张 $L\/K$ 与所有离散挠 $Gal_L$-模 $M$，$H^q_#[cont] (Gal_L, M) = 0$。 

  #proof[
    $L$ 的任意有限可分扩张都是 $K$ 的有限可分扩张，因此可以把 $L$ 换成 $K$，不妨设 $L = K$。 
    
    对任意 $x in M$，由于 $M$ 是带连续 $Gal_K$-作用的离散空间，存在有限 Galois 扩张 $E\/K$，使得 $x$ 被开正规子群 $Gal_E <= Gal_K$ 固定。于是这有限多个挠元 ${g x: [g] in Gal(E\/K) = Gal_K\/Gal_E}$ 生成 $M$ 的一个包含 $x$ 的 $Gal_K$-稳定有限子模。因此，作为抽象 $Gal_K$-模，有： 
    $
      M = dirlim_(N <= M #[有限子模]) N
    $
    上式右端的拓扑也是离散的，因此它们作为连续 $Gal_K$-模同构。由模的极限公式（@galois-cohom-props (1a)），只需证明： 
    $
      H^q_#[cont] (Gal_K, M) = 0
    $
    对所有有限离散 $Gal_K$-模 $M$ 成立。现在对每个素数 $p$，$M$ 的 $p^oo$-挠部分都是 $Gal_K$-稳定的，所以 $M$ 是其各 $p^oo$-挠部分的直和。由于： 
    $
      H^q_#[cont] (Gal_K, M) = dirlim_(E\/K #[有限 Galois] \ M = M^(Gal_E)) H^q (Gal(E\/K), M)
    $
    其中过渡映射是膨胀映射，因此只需证明：对有限 Galois 扩张 $E\/K$，若 $Gal_E$ 在 $M$ 上平凡作用，则任意类 $alpha_E in H^q (Gal(E\/K), M)$ 在过渡到更大的 Galois 扩张时膨胀为零。 

    令 $G = Gal(E\/K)$，这是有限群。它有一个 Sylow $p$-子群 $P$，即对应于中间域扩张 $E\/F\/K$ 的有限 $p$-群，亦即 $P = Gal(E\/F)$。我们先证明：当过渡到 $F$ 的更大 Galois 扩张时，$res^G_P (alpha_E) in H^q (P, M)$ 为零。 

    事实上，有限 $p$-群 $P$ 作用在有限交换 $p$-群 $M$ 上。$M$ 中每个 $P$-轨道的阶都是 $p$ 的幂，这些数之和为 $abs(M)$，而这个数被 $p$ 整除。由于 $0$ 总被 $P$ 固定，轨道大小中 $1$ 已经出现了一次，所以它必定出现不止一次。换言之，$M^P subset M$ 非平凡，于是可以取 $M_1 subset M^P subset M$，它作为交换群同构于 $ZZ\/p$。对 $M\/M_1$ 归纳地重复这一构造，便得到有限滤过： 
    $
      0 = M_0 subset M_1 subset dots.c subset M_k = M
    $
    这是 $P$-模的滤过，使得每个 $M_j\/M_(j-1)$ 都是 $M\/M_(j-1)$ 的一个 $P$-固定子模，作为交换群同构于 $ZZ\/p$，即（由 $P$ 在其上作用平凡）作为 $P$-模同构于 $ZZ\/p$。 

    我们断言：
    
    - 固定 $0 <= j <= k$ 与包含 $E$ 的 Galois 扩张 $T\/F$。任取类 $beta_j in H^q (Gal(T\/F), M_j)$，都存在包含 $T$ 的充分大的有限 Galois 扩张 $L\/F$，使其膨胀到 $Gal(L\/F)$ 后化为零。 

    基础情形 $j = 0$ 自动成立。假设情形 $j-1$ 已经证完，下面处理情形 $j$。考虑 $Gal_F$-模的正合列： 
    $
      0 -> M_(j-1) -> M_j -> M_j\/M_(j-1) cong ZZ\/p -> 0
    $
    它诱导出正合列： 
    $
      dots.c -> H^q (Gal(T\/F), M_(j-1)) ->^u H^q (Gal(T\/F), M_j) ->^v H^q (Gal(T\/F), ZZ\/p) -> dots.c
    $
    然而由假设 $H^q (Gal_F, ZZ\/p) = 0$，所以存在包含 $T$ 的有限 Galois 扩张 $L\/F$，使得 $inf_(Gal(T\/F))^(Gal(L\/F)) (v(beta_j)) = 0$。由于函子性与膨胀相容，我们有交换图表： 
    // https://q.uiver.app/#r=typst&q=WzAsMTAsWzAsMCwiZG90cy5jIl0sWzAsMSwiZG90cy5jIl0sWzQsMCwiZG90cy5jIl0sWzQsMSwiZG90cy5jIl0sWzEsMCwiSF5xIChQLCBNXyhqLTEpKSJdLFsyLDAsIkhecSAoUCwgTV9qKSJdLFszLDAsIkhecSAoUCxaWlxcL3ApIl0sWzEsMSwiSF5xIChHYWwoTFxcL0YpLCBNXyhqLTEpKSJdLFsyLDEsIkhecSAoR2FsKExcXC9GKSwgTV9qKSJdLFszLDEsIkhecSAoR2FsKExcXC9GKSwgWlpcXC9wKSJdLFswLDRdLFs0LDUsInUiXSxbNSw2LCJ2Il0sWzYsMl0sWzEsN10sWzcsOCwidV9MIl0sWzgsOSwidl9MIl0sWzksM10sWzQsNywiaW5mX1BeKEdhbChMXFwvRikpIiwxXSxbNSw4LCJpbmZfUF4oR2FsKExcXC9GKSkiLDFdLFs2LDksImluZl9QXihHYWwoTFxcL0YpKSIsMV1d
    #context align(center, diagram({
      node((-2, -1), [$dots.c$])
      node((-2, 0), [$dots.c$])
      node((2, -1), [$dots.c$])
      node((2, 0), [$dots.c$])
      node((-1, -1), [$H^q (Gal(T\/F), M_(j-1))$])
      node((0, -1), [$H^q (Gal(T\/F), M_j)$])
      node((1, -1), [$H^q (Gal(T\/F),ZZ\/p)$])
      node((-1, 0), [$H^q (Gal(L\/F), M_(j-1))$])
      node((0, 0), [$H^q (Gal(L\/F), M_j)$])
      node((1, 0), [$H^q (Gal(L\/F), ZZ\/p)$])
      edge((-2, -1), (-1, -1), "->")
      edge((-1, -1), (0, -1), [$u$], label-side: left, "->")
      edge((0, -1), (1, -1), [$v$], label-side: left, "->")
      edge((1, -1), (2, -1), "->")
      edge((-2, 0), (-1, 0), "->")
      edge((-1, 0), (0, 0), [$u_L$], label-side: left, "->")
      edge((0, 0), (1, 0), [$v_L$], label-side: left, "->")
      edge((1, 0), (2, 0), "->")
      edge((-1, -1), (-1, 0), [$inf_(Gal(T\/F))^(Gal(L\/F))$], label-side: center, "->")
      edge((0, -1), (0, 0), [$inf_(Gal(T\/F))^(Gal(L\/F))$], label-side: center, "->")
      edge((1, -1), (1, 0), [$inf_(Gal(T\/F))^(Gal(L\/F))$], label-side: center, "->")
    }, crossing-fill: thm-box-curr-color()))
    于是： 
    $
      v_L (inf_(Gal(T\/F))^(Gal(L\/F)) (beta_j)) = 0
    $
    由第二行的正合性，存在 $gamma_(j-1) in H^q (Gal(L\/F), M_(j-1))$，使得 $u_L (gamma_(j-1)) = inf_(Gal(T\/F))^(Gal(L\/F)) (beta_j)$。接下来，由归纳假设，存在包含 $L$ 的 Galois 扩张 $L'\/F$，使得 $inf_(Gal(L\/F))^(Gal(L'\/F)) (gamma_(j-1)) = 0$。对等式 $u_L (gamma_(j-1)) = inf_(Gal(T\/F))^(Gal(L\/F)) (beta_j)$ 的两端再作用 $inf_(Gal(L\/F))^(Gal(L'\/F))$，并利用相容性，我们得到： 
    $
      inf_(Gal(T\/F))^(Gal(L'\/F)) (beta_j) = inf_(Gal(L\/F))^(Gal(L'\/F)) (u_L (gamma_(j-1))) = u_(L') (inf_(Gal(L\/F))^(Gal(L'\/F)) (gamma_(j-1))) = u_(L') (0) = 0
    $
    至此完成。 

    换言之，我们已经证明： 

    - 对每个类 $beta in H^q (P, M)$，存在包含 $E$ 的有限 Galois 扩张 $L\/F$，使得 $inf_P^(Gal(L\/F)) (beta) = 0$。 

    把它应用于类 $res^G_P (alpha_E)$，我们看到： 
    $
      inf_P^(Gal(L\/F)) (res^G_P (alpha_E)) = 0
    $
    其中 $L\/F$ 是某个包含 $E$ 的有限 Galois 扩张。取 $L'$ 为 $L$ 在 $K$ 上的 Galois 闭包，于是再作一次膨胀： 
    $
      inf_(Gal(E\/F))^(Gal(L'\/F)) (res^(Gal(E\/K))_(Gal(E\/F)) (alpha_E)) = 0
    $

    由群上同调，膨胀与限制之间满足如下相容性： 
    #fact[
      设 $G$ 是有限群，$N <= G$ 是正规子群，$H <= G$ 是包含 $N$ 的子群。则： 
      $
        inf_(H\/N)^H compose res^(G\/N)_(H\/N) = res^G_H compose inf^G_(G\/N)
      $
    ]
    把这一事实应用于上面的情形，取事实记号中的 $N = Gal(L'\/E), G = Gal(L'\/K), H = Gal(L'\/F)$，得到： 
    $
      res^(Gal(L'\/K))_(Gal(L'\/F)) (inf_(Gal(E\/K))^(Gal(L'\/K)) (alpha_E)) = inf_(Gal(E\/F))^(Gal(L'\/F)) (res^(Gal(E\/K))_(Gal(E\/F)) (alpha_E)) = 0
    $
    然而，考虑限制–膨胀复合： 
    $
      H^q (Gal(L'\/K), M) ->^(res^(Gal(L'\/K))_(Gal(L'\/F))) H^q (Gal(L'\/F), M) -> H^q (Gal(L'\/K), M)
    $
    它不过是乘以 $[Gal(L'\/K) : Gal(L'\/F)] = [F : K] = [G : P]$，而这个数与 $p$ 互素。由于 $H^q (Gal(L'\/K), M)$ 是 $p^k$-挠的，其中 $p^k = abs(M)$，所以这个复合是同构。因此 $res^(Gal(L'\/K))_(Gal(L'\/F)): H^q (Gal(L'\/K), M) -> H^q (Gal(L'\/F), M)$ 是单射。于是我们看到： 
    $
      inf_(Gal(E\/K))^(Gal(L'\/K)) (alpha_E) = 0
    $
    #suppress-qed
  ]

  第三步。对每个固定的 $q >= 3$，若对所有素数 $2 <= r < q$ 与任意离散挠 $M$ 都有 $H^r_#[cont] (Gal_K, M) = 0$，则： 
  $
    H^q (Gal_K, ZZ\/n) = 0
  $
  对所有 $n >= 1$ 成立。 

  #proof[
    我们将使用 $Gal_K$ 的正合列： 
    $
      0 -> ZZ\/n -> coInd_1^(Gal_K) (ZZ\/n) -> R -> 0
    $
    其中余诱导模 (co-induced module) $coInd_1^(Gal_K) (ZZ\/n)$ 是： 
    $
      coInd_1^(Gal_K) (ZZ\/n) = dirlim_(L\/K #[有限 Galois]) coInd_1^(Gal(L\/K)) (ZZ\/n) = dirlim_(L\/K #[有限 Galois]) C(Gal(L\/K), ZZ\/n) = C(Gal_K, ZZ\/n)
    $
    即全体局部常值函数 $Gal_K -> ZZ\/n$ 构成的模，带有左正则 $Gal_K$-作用，当然它是 $n$-挠的。此外，由正向极限可以验证这个模上的拓扑是离散的。 
    
    于是商 $R$ 是 $n$-挠的且离散。由 Shapiro 引理，$H^(q-1)_#[cont] (Gal_K, coInd_1^(Gal_K) (ZZ\/n)) = H^q_#[cont] (Gal_K, coInd_1^(Gal_K) (ZZ\/n)) = 0$。因此由导出函子的正合列，我们有： 
    $
      H^q_#[cont] (Gal_K, ZZ\/n) cong H^(q-1)_#[cont] (Gal_K, R) = 0
    $
    由归纳假设。 
    #suppress-qed
  ]

  对 $K$ 的任意有限可分扩张，第三步都可以应用于 $Gal_L$。于是我们证明了： 

  - 对 $n >= 1$ 与任意有限可分扩张 $L\/K$，$H^2_#[cont] (Gal_L, ZZ\/n) = 0$。 #h(1fr)

  - 假设对固定的 $q >= 2$ 与所有有限可分扩张 $L\/K$，
    $
      H^q_#[cont] (Gal_L, ZZ\/n) = 0
    $
    对所有 $n >= 1$ 成立。则对所有有限可分扩张 $L\/K$ 与所有离散挠 $Gal_L$-模 $M$，$H^q_#[cont] (Gal_L, M) = 0$。 

  - 对每个有限可分扩张 $L\/K$ 与每个固定的 $q >= 3$，若对所有素数 $2 <= r < q$ 与任意离散挠 $M$ 都有 $H^r_#[cont] (Gal_L, M) = 0$，则：
    $
      H^q (Gal_L, ZZ\/n) = 0
    $
    对所有 $n >= 1$ 成立。 

  这三个结果足以通过归纳完成证明。 

  （2）$q = 1$ 的情形是 Hilbert 90，$q = 2$ 的情形由 @brauer-grp-of-c1-field-trivial 给出，故不妨设 $q >= 3$。对任意素数 $ell != "char"(K)$，考虑 Kummer 序列： 
  $
    0 -> mu_ell (K^sep) -> (K^sep)^times ->^((-)^ell) (K^sep)^times -> 0
  $
  它诱导出长正合列： 
  $
    dots.c -> H^q_#[cont] (Gal_K, mu_ell (K^sep)) -> H^q_#[cont] (Gal_K, (K^sep)^times) ->^(times ell) H^q_#[cont] (Gal_K, (K^sep)^times) -> H^(q+1)_#[cont] (Gal_K, mu_ell (K^sep)) -> dots.c
  $
  由（1），$H^q_#[cont] (Gal_K, mu_ell (K^sep)) = H^(q+1)_#[cont] (Gal_K, mu_ell (K^sep)) = 0$。因此，乘以 $ell$ 的映射： 
  $
    times ell: H^q_#[cont] (Gal_K, (K^sep)^times) -> H^q_#[cont] (Gal_K, (K^sep)^times)
  $
  是同构。 

  若 $p = "char"(K) > 0$，注意 $(-)^p: (K^sep)^times -> (K^sep)^times$ 是单射，这给出 $Gal_K$-模的正合列： 
  $
    0 -> (K^sep)^times ->^((-)^p) (K^sep)^times -> Q -> 0
  $
  由于 $(K^sep)^times$ 作为 $Gal_K$-模是离散的，$Q$ 也离散。按定义 $Q$ 是 $p$-挠的，故（1）适用于 $Q$。于是有长正合列： 
  $
    dots.c -> H^(q-1)_#[cont] (Gal_K, Q) -> H^q_#[cont] (Gal_K, (K^sep)^times) ->^(times p) H^q_#[cont] (Gal_K, (K^sep)^times) -> H^q_#[cont] (Gal_K, Q) -> dots.c
  $
  由于 $q >= 3$，由（1）$H^(q-1)_#[cont] (Gal_K, Q) = H^q_#[cont] (Gal_K, Q) = 0$。因此， 
  $
    times p: H^q_#[cont] (Gal_K, (K^sep)^times) -> H^q_#[cont] (Gal_K, (K^sep)^times)
  $
  是同构。 
  综合上面两个结果，对任意自然数 $n >= 1$，倍乘映射： 
  $
    times n: H^q_#[cont] (Gal_K, (K^sep)^times) -> H^q_#[cont] (Gal_K, (K^sep)^times)
  $
  总是同构。然而， 
  $
    H^q_#[cont] (Gal_K, (K^sep)^times) = dirlim_(L\/K #[有限 Galois]) H^q (Gal(L\/K), L^times)
  $
  是挠的。这迫使 $H^q_#[cont] (Gal_K, (K^sep)^times) = 0$。 
]
