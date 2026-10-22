#import "void-import.typ": *

上一章我们引入了平展景与平展层，并建立了层的一些基本运算。 

正如前面讨论过的，平展上同调由平展层上的整体截面函子作右导出得到，它是我们研究的核心对象。 

本章将建立平展上同调的基本结论，并考察最初的几个例子。我们会介绍： 

- 极限公式：这类公式让我们能计算： #h(1fr)
  $
    H^q (X, dirlim_i cal(F)_i) #[#h(10%) 与 #h(10%)] H^q (invlim_i X_i, u_(i_0)^(-1) cal(F))
  $
  即用各部分的上同调算出整体的上同调。极限公式在理论上的重要性在于，它们允许对挠层作 _devissage_。后面会看到，挠层总是这样一类层的滤余极限：这类层称为可构造层 (constructible sheaf)，而可构造层又归结为 $ul(ZZ\/n)$。这就把关于一般挠层的命题化归为关于 $ul(ZZ\/n)$ 的命题。 

- $cal(M)_et$ 的上同调，以及 $GG_m$ 与 $ul(M)$ 的一次上同调： 

  - 对 $cal(M) in QCoh(X)$，$cal(M)_et$ 的平展上同调就是 $cal(M)$ 的 Zariski 上同调： #h(1fr)
    $
      H^q (X_et, cal(M)_et) cong H^q (X_#[top], cal(M))
    $
    这说明来自拟凝聚层的平展层对平展上同调理论意义不大，它们给不出新的上同调不变量。 

  - 对乘法群 $GG_m$： 
    $
      H^1 (X_et, GG_m) cong Pic(X)
    $
    这一点在理论的后续发展中至关重要：与 Kummer 序列、Artin–Schreier 序列结合之后，它使我们能计算曲线上的 $ul(ZZ\/n)$ 上同调。而这些计算反过来又成为紧合基变换之类相当一般的结论的关键输入。 

  - 对常值层 $ul(M)$： 
    $
      H^1 (X_et, ul(M)) cong Hom_#[cont] (pi_1^et (X), M)
    $
    其中 $M$ 赋以离散拓扑。这把上同调理论与我们已经建立的基本群理论联系起来，并最终与有限平展覆叠联系起来；后面也会看到，它对紧合基变换之类的进一步理论同样有用。 

- 曲线的上同调： 

  对代数闭域 $k$ 上的非奇异曲线 $X$，我们将具体算出 $H^q_et (X, ul(ZZ\/n))$。这既有理论意义，也有教学意义。曲线的上同调将成为后续许多结论的动机性例子，例如消没定理与 Poincaré 对偶；它也会成为紧合基变换的关键输入。 

== 极限公式 <sect-limit-formulas>

我们先讨论固定概形上的层的极限公式。 

#theorem(name: <limit-formula-for-sheaves>)[
  (层的极限公式) 设 $X$ #furi[quasi-compact quasi-separated][拟紧拟分离]，并设 $cal(F) = dircolim_i cal(F)_i$ 是 $cAb(X_et)$ 中层的滤余极限，则有自然同构： 
  $
    H^q (U, cal(F)) cong dircolim_i H^q (U, cal(F)_i)
  $
  对每个拟紧拟分离的 $U in Et_X$。 
]
#proof[
  我们分四步证明这个定理。 

  第一步：$H^0$ 的情形。我们断言： 
  $
    Gamma(X, cal(F)) cong dircolim_i Gamma(X, cal(F)_i)
  $
  #proof[
    考虑预层的余极限： 
    $
      cal(P) = dircolim_(i,cPSh) cal(F)_i in cPAb(X_et), U |-> dircolim_i cal(F)_i (U)
    $
    于是 $cal(F) = cal(P)^\#$。我们要证明：对拟紧拟分离的 $U in Et_X$，有 $cal(P)^\# (U) = cal(P)(U)$。 

    我们断言：对每个拟紧的 $U in Et_X$，典范映射 $cal(P)(U) -> cal(P)^+ (U)$ 是同构。事实上，$U$ 拟紧时，$U$ 的每个平展覆盖都能被一个覆盖 $cal(U) = {U_i -> U}_(1<=i<=n)$ 所加细，其中只有有限多个映射，且每个 $U_i$ 都仿射。把这类平展覆盖的全体记为 $cal(S)$，于是： 
    $
      caron(H)^0 (U, cal(P)) = dirlim_(cal(U)) caron(H)^0 (cal(U), cal(P)) = dirlim_(cal(U) in cal(S)) caron(H)^0 (cal(U), cal(P))
    $
    并且断言：对每个 $cal(U) in cal(S)$，态射 $cal(P)(U) -> caron(H)^0 (cal(U), cal(P))$ 是同构。事实上，由每个 $cal(F)_i$ 的层条件，有正合列： 
    $
      0 -> cal(F)_i (U) -> product_(1<=j<=n) cal(F)_i (U_j) -> product_(1<=j,k<=n) cal(F)_i (U_j times_U U_k)
    $
    对 $I$ 取滤余极限，并用 $cAb$ 的 (Ab5)，得到： 
    $
      0 -> dircolim_i cal(F)_i (U) -> dircolim_i product_(1<=j<=n) cal(F)_i (U_j) -> dircolim_i product_(1<=j,k<=n) cal(F)_i (U_j times_U U_k)
    $
    然而滤余极限与有限极限交换，所以这个序列就是： 
    $
      0 -> dircolim_i cal(F)_i (U) -> product_(1<=j<=n) dircolim_i cal(F)_i (U_j) -> product_(1<=j,k<=n) dircolim_i cal(F)_i (U_j times_U U_k)
    $
    即
    $
      0 -> cal(P) (U) -> product_(1<=j<=n) cal(P) (U_j) -> product_(1<=j,k<=n) cal(P) (U_j times_U U_k)
    $
    换言之，$cal(P)$ 对 $cal(U)$ 满足层条件，且 $caron(H)^0 (cal(U), cal(P)) = cal(P)(U)$。这样我们就证明了对所有拟紧的 $U in Et_X$，都有 $cal(P)^+ (U) = cal(P) (U)$。 

    接下来证明：对拟紧拟分离的 $U in Et_X$，有 $cal(P)^\# (U) = cal(P)^+ (U) = cal(P)(U)$。同样地，$U$ 的平展覆盖构成的正向系统有一个共尾子系统 $cal(S)$，由形如 ${U_i -> U}_(1<=i<=n)$ 的平展覆盖组成，其中只有有限多个映射，且每个 $U_i$ 都仿射。现在对每个 $cal(U) in cal(S)$，有正合列： 
    $
      0 -> caron(H)^0 (cal(U), cal(P)^+) -> product_(1<=j<=n) cal(P)^+ (U_j) -> product_(1<=j,k<=n) cal(P)^+ (U_j times_U U_k) -> 0
    $
    由于 $U$ 拟分离，每个 $U_j times_U U_k$ 都拟紧。每个 $U_j$ 本身也拟紧，所以按前面“$U$ 拟紧时 $cal(P)^+ (U) = cal(P) (U)$”的结论，这个序列就是： 
    $
      0 -> caron(H)^0 (cal(U), cal(P)^+) -> product_(1<=j<=n) cal(P) (U_j) -> product_(1<=j,k<=n) cal(P) (U_j times_U U_k) -> 0
    $
    即 $caron(H)^0 (cal(U), cal(P)^+) = caron(H)^0 (cal(U), cal(P)) = cal(P)(U)$。因此，
    $
      cal(P)^\# (U) = dircolim_(cal(U) in cal(S)) caron(H)^0 (cal(U), cal(P)^+) = cal(P)(U)
    $
    #suppress-qed
  ]

  第二步：Čech 上同调的情形。我们断言：对每个 $p >= 0$ 与每个拟紧拟分离的 $U in Et_X$，
  $
    caron(H)^p (U, cal(F)) cong dircolim_i caron(H)^p (U, cal(F)_i)
  $

  #proof[
    照例，$U$ 的平展覆盖构成的正向系统有一个共尾子系统 $cal(S)$，由形如 ${U_i -> U}_(1<=i<=n)$ 的平展覆盖组成，其中只有有限多个映射，且每个 $U_i$ 都仿射。对其中每个 $cal(U) = {U_i -> U}_(1<=i<=n) in cal(S)$，$U$ 拟紧拟分离、每个 $U_i$ 仿射，因此每个
    $
      U_(i_0,dots.c,i_p) = U_(i_0) times_U dots.c times_U U_(i_p)
    $
    都拟紧拟分离。换言之，每个 $U_(i_0,dots.c,i_p)$ 都满足第一步的条件，故可对它应用第一步。于是，
    $
      C^p (cal(U), cal(F)) &= product_(1<=i_0,dots.c,i_p<=n) cal(F) (U_(i_0,dots.c,i_p)) \
      &= product_(1<=i_0,dots.c,i_p<=n) dircolim_i cal(F)_i (U_(i_0,dots.c,i_p)) #[由第一步] \
      &= dircolim_i product_(1<=i_0,dots.c,i_p<=n) cal(F)_i (U_(i_0,dots.c,i_p)) #[因为有限极限与滤余极限交换] \
      &= dircolim_i C^p (cal(U), cal(F)_i)
    $
    换言之，Čech 复形 $0 -> C^bullet (cal(U), cal(F))$ 是各个 $cal(F)_i$ 的 Čech 复形构成的滤余极限，也就是 $0 -> dircolim_i C^bullet (cal(U), cal(F)_i)$。由 $cAb$ 的 (Ab5)，取上同调与滤余极限交换，故： 
    $
      caron(H)^p (cal(U), cal(F)) = dircolim_i caron(H)^p (cal(U), cal(F)_i)
    $
    对 $cal(U) in cal(S)$ 取正向极限，并交换右端的两个余极限，得到： 
    $
      caron(H)^p (U, cal(F)) = dircolim_i caron(H)^p (U, cal(F)_i)
    $
    #suppress-qed
  ]
  第三步：内射对象的情形。我们断言：设 $cal(I) = dircolim_i cal(I)_i$ 是 ${cal(I)_i}$ 的滤余极限，其中每个 $cal(I)_i in cAb(X_et)$ 都内射，则它满足： 
  $
    H^q (U, cal(I)) = 0, forall q >= 1
  $
  对每个拟紧拟分离的 $U in Et_X$。换言之，$cal(I)$ 未必内射，但用它来计算 $H^q (U, -)$ 时，它必然零调。 
  #proof[
    我们对 $q$ 归纳。奠基情形 $q = 1$ 用典范同构 $H^1 (U, -) cong caron(H)^1 (U, -)$，它来自 @h1-is-cech-h1。于是： 
    $
      H^1 (U, cal(I)) &= caron(H)^1 (U, cal(I)) \
      &= dircolim_i caron(H)^1 (U, cal(I)_i) #[由第二步] \
      &= dircolim_i H^1 (U, cal(I)_i) \
      &= 0 #[因为每个 $cal(I)_i$ 都内射]
    $
    设已对一切 $1 <= q < n$ 证明断言，要证 $H^n (U, cal(I)) = 0$。为此使用 Čech 到导出函子的谱序列： 
    $
      E_2^(p,q) = caron(H)^p (U, ul(H)^q (cal(I))) => H^(p+q) (U, cal(I))
    $
    由归纳假设，对 $0 < q < n$ 及任意拟紧拟分离的 $U in Et_X$，有 $ul(H)^q (cal(I))(U) = H^q (U, cal(I)) = 0$。照例，$U$ 的平展覆盖构成的正向系统有一个共尾子系统 $cal(S)$，由形如 ${U_i -> U}_(1<=i<=n)$ 的平展覆盖组成，其中只有有限多个映射，且每个 $U_i$ 都仿射。对其中每个 $cal(U) = {U_i -> U}_(1<=i<=n) in cal(S)$，$U$ 拟紧拟分离、每个 $U_i$ 仿射，因此每个
    $
      U_(i_0,dots.c,i_p) = U_(i_0) times_U dots.c times_U U_(i_p)
    $
    都拟紧拟分离。因此对每个 $cal(U) in cal(S)$，整个 Čech 复形 $0 -> C^bullet (cal(U), ul(H)^q (cal(I)))$ 为零，从而 $caron(H)^p (cal(U), ul(H)^q (cal(I))) = 0$。对 $cal(U) in cal(S)$ 取正向极限，
    $
      caron(H)^p (U, ul(H)^q (cal(I))) = 0, forall 0<q<n
    $
    换言之，这个 Čech 到导出函子的谱序列有一条水平的消没带。下面用到一条上同调引理： 
    #lemma[
      设 $E_2^(p,q) => H^(p+q)$ 是第一象限的谱序列，且有一条水平的消没带。则存在修正的五项正合列： 
      $
        0 -> E_2^(n,0) -> H^n -> E_2^(0,n) -> E_2^(n+1,0) -> H^(n+1)
      $
    ]
    由这个修正的五项正合列，得到正合列： 
    $
      0 -> caron(H)^n (U, cal(I)) -> H^n (U, cal(I)) -> caron(H)^0 (U, ul(H)^n (cal(I))) -> dots.c
    $
    然而由第二步，$caron(H)^n (U, cal(I)) = dircolim_i caron(H)^n (U, cal(I)_i) = 0$；又由 @cech-h0-of-hq-psh-vanish，$caron(H)^0 (U, ul(H)^n (cal(I))) = 0$。于是 $H^n (U, cal(I))$ 在正合列中被夹在两个零之间，必为 $0$。 
    #suppress-qed
  ]

  第四步：一般情形。对 $X$ 的每个点，固定它上方的一个几何点，合起来记作 ${ol(x)}_(x in X)$。于是对每个 $cal(F)_i$ 都可以构造 Godement 消解： 
  $
    0 -> cal(F)_i -> cal(I)_i^bullet
  $
  // 然而，对每个 $p$，${cal(I)_i^p}$ 一般未必构成滤余极限，因为同调代数在它们之间诱导的映射只在同构意义下唯一，且
  现在，由 Godement 消解的函子性，对每个 $p$，${cal(I)^p_i}_i$ 构成一个滤过系统；再由 $cAb(X_et)$ 的 (Ab5)，得到正合列： 
  $
    0 -> cal(F) -> dircolim_i cal(I)_i^bullet
  $
  然而对每个拟紧拟分离的 $U in Et_X$，由第三步，每个 $dircolim_i cal(I)_i^p$ 关于 ${H^q (U, -)}_(q>=0)$ 都是零调的。换言之，我们得到了 $cal(F)$ 的一个零调消解，可以用它来计算 $cal(F)$ 的上同调： 
  $
    H^q (U, cal(F)) &= h^q (0 -> (dircolim_i cal(I)_i^bullet)(U)) \
    &= h^q (0 -> dircolim_i cal(I)_i^bullet (U)) #[由第一步] \
    &= dircolim_i h^q (0 -> cal(I)_i^bullet (U)) #[将 (Ab5) 应用于 $cAb$] \
    &= dircolim_i H^q (U, cal(F)_i) #[按定义]
  $
  #remark[
    这里 Godement 消解的函子性起了关键作用。若不能函子性地选取内射消解，我们就未必能让 ${cal(I)^p_i}_i$ 构成一个滤过系统：同调代数给出的内射消解之间的态射只在链同伦意义下唯一，一般并不构成函子 $I -> cAb(X_et)$。 
  ]
]

接下来处理概形的极限公式。 

#theorem(name: <limit-formula-for-schemes-0>)[
  (概形的极限公式) 设 ${Z_i}_(i in I)$ 是拟紧拟分离概形构成的逆向系统，所有过渡映射都仿射，且有终对象 $0 in I$。
  
  令：
  $
    Z = invlim_(i in I) Z_i
  $
  映射为 $v_i: Z -> Z_i, u_i: Z_i -> Z_0$。
  
  任取 $cal(F)_0 in cAb((Z_0)_et)$ 与拟紧拟分离的 $U in Et_Z$。则存在 $k in I$，使得 $U$ 是某个 $U_k in Et_(Z_k)$ 的基变换。于是由沿 $v_j$ 的拉回 $H^q (Z_j, u_j^(-1) cal(F)_0) -> H^q (Z, v_0^(-1) cal(F)_0)$ 诱导的典范映射：
  $
    dirlim_(j>=k) H^q (U_j, u_j^(-1) cal(F)_0) -> H^q (U, v_0^(-1) cal(F)_0) 
  $
  是同构。特别地，有典范同构： 
  $
    dirlim_(i in I) H^q (Z_i, u_i^(-1) cal(F)_0) -> H^q (Z, v_0^(-1) cal(F)_0)
  $
]
#proof[
  // 我们先用一个一般的范畴构造，把一般的余滤过极限化归为逆向极限。
  // #lemma[
  //   (Artin–Mazur 构造) 设 $I$ 是带终对象的余滤过范畴。则存在带最小元的正向偏序集 $P$，以及共尾函子 $P -> I^opp$。
  // ]
  // #proof[
  //   这基本上就是 #cite-stacks("0032", [Lemma 4.21.5])，只是我们额外把 $P$ 截断到某个元素 $>=$ 以上的部分，以保证最小元存在。
  // ]
  // 这个构造说明，可以把余滤过极限 $I$ 换成 $P$ 上的逆向极限。于是不妨假设余滤过范畴 $I$ 实际上就是带最小元 $0$ 的正向偏序集，而所处理的是概形的逆向极限。

  #lemma[
    + 任取 $Et_Z$ 中在 $Z$ 上有限展示的 $U$，都存在 $j in I$ 与在 $Z_j$ 上有限展示的 $U_j in Et_(Z_j)$，使得前者是后者的基变换。

    + 对 $Et_Z$ 中任何在 $Z$ 上有限展示的 $U$，其每个平展覆盖都能被下面定义的平展覆盖子系统 $cal(S)$ 中的覆盖加细：
    
      设 $U$ 由 $U_j in Et_(Z_j)$ 作基变换得到。则 $cal(S)$ 由这样的平展覆盖 $cal(U) = {U_alpha -> U}$ 组成，其中只有有限多个映射，且存在某个 $k in I$ 以及 $Et_(Z_k)$ 中的平展覆盖 $cal(U)_k = {U_(alpha,k) -> U_k}$，它在 $Z$ 上的基变换是 $cal(U)$，并且每个 $U_(alpha,k)$ 都在 $U_k$ 上仿射且有限展示（即在 $U_k$ 上拟紧拟分离；由平展性，局部有限展示已自动成立）。
  ]
  #proof[
    (1) 由定理 @passage-to-limit-of-morphisms 与 @passage-to-limit-of-properties 得到。

    (2) $U$ 在拟紧拟分离概形 $Z$ 上有限展示，故自身也拟紧拟分离。任给平展覆盖 $cal(U) = {U_alpha -> U}$，先把它加细为每个 $U_alpha$ 都仿射的覆盖。由于 $U$ 拟紧，还可进一步加细为有限子覆盖，因此指标 $alpha$ 的集合有限。
    
    由于 $U_alpha$ 与 $U$ 都拟紧拟分离，态射 $U_alpha -> U$ 拟紧拟分离。它又是平展的（从而局部有限展示），因此有限展示。由 @passage-to-limit-of-morphisms 与 @passage-to-limit-of-properties，对每个 $alpha$，存在某个 $j <= i_alpha in I$，使得 $U_alpha -> U$ 来自 $Et_(Z_(i_alpha))$ 中态射 $U_(alpha,i_alpha) -> U_(i_alpha)$ 的基变换。取所有 $alpha$ 的公共上界，便存在某个 $j <= k in I$ 以及 $Et_(Z_k)$ 中的态射族 ${U_(alpha,k) -> U_k}_alpha$，其到 $Z$ 的基变换为 ${U_alpha -> U}$。由于 $union.sq.big_alpha U_alpha -> U$ 满射，把 $k$ 换成更靠后的阶段，不妨设 $union.sq.big_alpha U_(alpha,k) -> U$ 也满射；于是 ${U_(alpha,k) -> U_k}_alpha$ 联合满射，从而是一个仿射覆盖。这就完成了证明。
  ]

  下面分三步证明：先证 $H^0$，再证 Čech 上同调，最后借助 Čech 到导出函子的谱序列处理一般情形；这与层的极限公式的证明类似。

  第一步：$q = 0$ 的情形。记 $cal(F)_i = u_i^(-1) cal(F)_0$、$cal(F) = v_0^(-1) cal(F)_0$。我们断言存在典范的等同：
  $
    cal(F) (U) = dirlim_(j >= k) cal(F)_j (U_j)
  $
  对 $Et_Z$ 中任何由某个拟紧拟分离（即在 $Z_k$ 上有限展示）的 $U_k in Et_(Z_k)$ 作基变换得到的 $U$，只要 $U$ 拟紧拟分离，上式就成立。（这样的 $U_k$ 由前一条引理总是存在。）

  #proof[
    先证一条引理：
    #lemma(name: <limit-formula-for-schemes-pab>)[
      设 ${Z_i}_(i in I)$ 是拟紧拟分离概形构成的逆向系统，所有过渡映射都仿射，且有终对象 $0 in I$。
      
      令：
      $
        Z = invlim_(i in I) Z_i
      $
      映射为 $v_i: Z -> Z_i, u_i: Z_i -> Z_0$。任取 $cal(F)_0 in cPAb((Z_0)_et)$。则对 $Et_Z$ 中任何由某个拟紧拟分离（即在 $Z_k$ 上有限展示）的 $U_k in Et_(Z_k)$ 作基变换得到的拟紧拟分离 $U$：
      $
        v_(0,cPSh)^(-1) cal(F)_0 (U) = dirlim_(j>=k) u_(j,cPSh)^(-1) cal(F)_0 (U_j)
      $
    ]
    #proof[
      回忆：对任意 $U in Et_Z$，
      $
        v_(0,cPSh)^(-1) cal(F)_0 (U) = dircolim_((V_0,phi)) cal(F)_0 (V_0)
      $
      其中滤余极限取遍所有如下形状的图表：
      // https://q.uiver.app/#r=typst&q=WzAsNCxbMCwxLCJaIl0sWzEsMSwiWl8wIl0sWzEsMCwiVl8wIl0sWzAsMCwiVSJdLFszLDIsInBoaSJdLFswLDFdLFszLDBdLFsyLDFdXQ==
      #align(center, diagram({
        node((-1, 0), [$Z$])
        node((0, 0), [$Z_0$])
        node((0, -1), [$V_0$])
        node((-1, -1), [$U$])
        edge((-1, -1), (0, -1), [$phi$], label-side: left, "->")
        edge((-1, 0), (0, 0), "->")
        edge((-1, -1), (-1, 0), "->")
        edge((0, -1), (0, 0), "->")
      }))
      其中 $V_0 in Et_(Z_0)$。换言之，我们面对的是一个滤余极限：
      $
        v_(0,cPSh)^(-1) cal(F)_0 (U) = dircolim_(V_0 in Et_(Z_0) \ phi in Hom_Z (U, Z times_(Z_0) V_0)) cal(F)_0 (V_0)
      $
      同样，
      $
        dirlim_(j>=k) u_(i,cPSh)^(-1) cal(F)_0 (U_j) = dirlim_(j>=k) dircolim_(V_0 in Et_(Z_0) \ phi_j in Hom_(Z_j) (U_j, Z_j times_(Z_0) V_0)) cal(F)_0 (V_0)
      $

      然而由 @passage-to-limit-of-morphisms，
      $
        Hom_Z (U, Z times_(Z_0) V_0) = dirlim_(j>=k) Hom_(Z_j) (U_j, Z_j times_(Z_0) V_0)
      $
      因此 $(j, V_0, phi_j) |-> (V_0, Z times_(Z_j) phi_j)$ 是这两个滤余极限的指标范畴之间的共尾函子。于是自然映射
      $
        dirlim_(j>=k) dircolim_(V_0 in Et_(Z_0) \ phi_j in Hom_(Z_j) (U_j, Z_j times_(Z_0) V_0)) cal(F)_0 (V_0) -> dircolim_(V_0 in Et_(Z_0) \ phi in Hom_Z (U, Z times_(Z_0) V_0)) cal(F)_0 (V_0)
      $
      是同构。
      /*
      然而，$U -> Z$ 是 $U_k -> Z_k$ 的基变换。由 @passage-to-limit-of-morphisms (2) 与 @passage-to-limit-of-properties，$Z$ 上的态射 $U -> V := V times_(Z_0) Z_k$ 是 $Z_j$ 上某个态射 $U_j -> V_j := V_0 times_(Z_0) Z_j$ 的基变换，也就是 $Z_0$ 上的一个态射 $U_j -> V_0$。取 $j >= k$，$U_j -> Z_j$ 仍是平展的。换言之，上面的图表分解为：
      // https://q.uiver.app/#r=typst&q=WzAsNixbMCwxLCJaIl0sWzEsMSwiWl9rIl0sWzEsMCwiVV9rIl0sWzAsMCwiVSJdLFsyLDAsIlZfMCJdLFsyLDEsIlpfMCJdLFszLDJdLFswLDFdLFszLDBdLFsyLDFdLFsxLDVdLFsyLDQsInBoaV9rIl0sWzQsNV1d
      #align(center, diagram({
        node((-1, 0), [$Z$])
        node((0, 0), [$Z_k$])
        node((0, -1), [$U_k$])
        node((-1, -1), [$U$])
        node((-0.7, -0.7), [$cart$])
        node((1, -1), [$V_0$])
        node((1, 0), [$Z_0$])
        edge((-1, -1), (0, -1), "->")
        edge((-1, 0), (0, 0), "->", $v_k$, label-side: right)
        edge((-1, -1), (-1, 0), "->")
        edge((0, -1), (0, 0), "->")
        edge((0, 0), (1, 0), "->", $u_k$, label-side: right)
        edge((0, -1), (1, -1), [$phi_k$], label-side: left, "->")
        edge((1, -1), (1, 0), "->")
      }))
      
      利用抽象的范畴论证，这个滤余极限取在满足 $j>=k$、$V_0 in Et_(Z_0)$ 且 $phi_j: U_j -> V_0$ 并嵌入上述图表的 $(j, V_0, phi_j)$ 上。于是，
      $
        v_(0,cPSh)^(-1) cal(F)_0 (U) &= dircolim_((V_0,phi)) cal(F)_0 (V_0) = dircolim_((j,V_0,phi_j) \ j>=k) cal(F)_0 (V_0) = dirlim_(j>=k) dircolim_((V_0,phi_j)) cal(F_0) (V_0) \
        &= dirlim_(j>=k) u_j^(-1) cal(F)_0 (U_k) = dirlim_(j>=k) cal(F)_k (U_k)
      $
      对所有拟紧拟分离的 $U in Et_Z$ 成立。 */
    ]

    现在证明：对所有拟紧拟分离的 $U in Et_Z$，$cal(F)(U) = v_(0,cPSh)^(-1) cal(F)_0 (U)$。设 $cal(S)$ 是前一条引理中 $U$ 的平展覆盖子系统。对某个 $cal(U) = {U_alpha -> U} in cal(S)$（它由 $Et_(Z_(k'))$ 中的平展覆盖 $cal(U)_(k') = {U_(alpha,k') -> U_(k')}$ 经基变换得到，$k' >= k$），计算 $caron(H)^0 (cal(U), v_(0,cPSh)^(-1) cal(F)_0)$。考虑：
    $
      & caron(H)^0 (cal(U), v_(0,cPSh)^(-1) cal(F)_0) \
      =& ker(product_alpha v_(0,cPSh)^(-1) cal(F)_0 (U_alpha) -> product_(alpha,beta) v_(0,cPSh)^(-1) cal(F)_0 (U_alpha times_U U_beta)) #[按定义]\
      =& ker(product_alpha dirlim_(j>=k') u_(j,cPSh)^(-1) cal(F)_0 (U_(alpha,j)) -> product_(alpha,beta) dirlim_(j>=k') u_(j,cPSh)^(-1) cal(F)_0 (U_(alpha,j) times_(U_j) U_(beta,j))) \
      & #[由我们对 $v_(0,cPSh)^(-1) cal(F)_0$ 的描述] \
      =& ker(dirlim_(j>=k') product_alpha u_(j,cPSh)^(-1) cal(F)_0 (U_(alpha,j)) -> dirlim_(j>=k') product_(alpha,beta) u_(j,cPSh)^(-1) cal(F)_0 (U_(alpha,j) times_(U_j) U_(beta,j))) \
      & #[因为有限极限与滤余极限交换] \
      =& dirlim_(j>=k') ker(product_alpha u_(j,cPSh)^(-1) cal(F)_0 (U_(alpha,j)) -> product_(alpha,beta) u_(j,cPSh)^(-1) cal(F)_0 (U_(alpha,j) times_(U_j) U_(beta,j))) #[将 (Ab5) 应用于 $cAb$] \
      =& dirlim_(j>=k') caron(H)^0 (cal(U), u_(j,cPSh)^(-1) cal(F)_0)
    $
    对一切 $cal(U) in cal(S)$ 取正向极限，得到：
    $
      caron(H)^0 (U, v_(0,cPSh)^(-1) cal(F)_0) = dirlim_(j>=k) caron(H)^0 (U_j, u_(j,cPSh)^(-1) cal(F)_0)
    $
    对一切拟紧拟分离的 $U in Et_Z$ 成立。换言之，
    $
      (v_(0,cPSh)^(-1) cal(F)_0)^+ (U) = dirlim_(j>=k) (u_(j,cPSh)^(-1) cal(F)_0)^+ (U_j)
    $
    对一切拟紧拟分离的 $U in Et_Z$ 成立。接下来，对 $caron(H)^0 (U, (v_(0,cPSh)^(-1) cal(F)_0)^+)$ 重复上面的论证：这里每个平展覆盖都能被 $cal(S)$ 中的覆盖加细，而 $cal(S)$ 中所有平展开集及其纤维积都拟紧拟分离。于是得到：
    $
      cal(F) (U) = (v_(0,cPSh)^(-1) cal(F)_0)^\# (U) = dirlim_(j>=k) (u_(j,cPSh)^(-1) cal(F)_0)^\# (U_j) = dirlim_(j>=k) cal(F)_j (U_j)
    $
    #suppress-qed
  ]

  第二步：Čech 上同调的情形。我们断言典范映射：
  $
    dirlim_(j>=k) caron(H)^p (U_j, cal(F)_j) -> caron(H)^p (U, cal(F)) 
  $
  是同构，其中 $U in Et_Z$ 取遍拟紧拟分离的对象，并且每个都来自某个拟紧拟分离的 $U_k in Et_(Z_k)$。

  #proof[
    任取 $cal(U) in cal(S)$，设 $cal(U) = {U_alpha -> U}$ 来自 $Et_(Z_(k'))$ 中的平展覆盖 $cal(U)_(k') = {U_(alpha,k') -> U_(k')}$，其中 $k' >= k$。考虑 Čech 复形：
    $
      C^p (cal(U), cal(F)) &= product_(alpha_0,dots.c,alpha_p) cal(F)(U_(alpha_0,dots.c,alpha_p)) #[按定义] \
      &= product_(alpha_0,dots.c,alpha_p) dirlim_(j>=k') cal(F)_j (U_(j,alpha_0,dots.c,alpha_p)) #[由第一步] \
      &= dirlim_(j>=k') product_(alpha_0,dots.c,alpha_p) cal(F)_j (U_(j,alpha_0,dots.c,alpha_p)) #[因为有限极限与滤余极限交换] \
      &= dirlim_(j>=k') C^p (cal(U)_j, cal(F)_j)
    $
    换言之，$cal(F)$ 关于 $cal(U)$ 的 Čech 复形，是那些 $cal(F)_j$ 关于 $cal(U)_j$（$j >= k'$）的 Čech 复形的正向极限。由 $cAb$ 的 (Ab5)，取上同调与滤余极限交换，故：
    $
      caron(H)^p (cal(U), cal(F)) = dirlim_(j>=k') caron(H)^p (cal(U)_j, cal(F)_j)
    $
    接下来想对 $cal(U) in cal(S)$ 取正向极限，并交换两个正向极限。然而 $k'$ 依赖于 $cal(U)$，这里有一些范畴上的微妙之处。我们得到同构
    $
      caron(H)^p (U, cal(F)) = dirlim_(cal(U)) dirlim_(j>=k') caron(H)^p (cal(U)_j, cal(F)_j) = dirlim_((k', cal(U),j) \ j>=k'>=k) caron(H)^p (cal(U)_j, cal(F)_j) = dirlim_(j>=k) caron(H)^p (U_j, cal(F)_j)
    $
    其中最后两个等号来自抽象的范畴论证。
  ]

  第三步：一般情形。$q = 0$ 的情形就是第一步，$q = 1$ 由第二步与 $caron(H)^1 = H^1$ 得到。设定理对一切 $q < n$ 成立，下面处理 $n$ 次上同调。
  
  对每个 $cal(F)_j$ 取 Čech 到导出函子的谱序列：
  $
    E_(2,j)^(p,q) = caron(H)^p (U_j, ul(H)^q (cal(F)_j)) => H^(p+q) (U_j, cal(F)_j) 
  $
  取正向极限（它是正合的），得到新的谱序列
  $
    tilde(E)_2^(p,q) = dirlim_(j>=k) caron(H)^p (U_j, ul(H)^q (cal(F)_j)) => dirlim_(j>=k) H^(p+q) (U_j, cal(F)_j)
  $
  另一方面，$cal(F)$ 也有 Čech 到导出函子的谱序列：
  $
    E_2^(p,q) = caron(H)^p (U, ul(H)^q (cal(F))) => H^(p+q) (U, cal(F))
  $
  滤过系统诱导谱序列的典范态射 $Phi: tilde(E)_2^(p,q) -> E_2^(p,q)$。

  由于 $U$ 拟紧拟分离，它的 Čech 上同调可以用 $cal(S)$ 中的覆盖来计算，而这些覆盖只涉及 $Et_Z$ 中拟紧拟分离的对象。因此计算 $caron(H)^p (U, ul(H)^q (cal(F)))$ 时，只需用到 $ul(H)^q (cal(F))$ 在拟紧拟分离对象上的取值，而归纳假设在这些对象上适用。又因 $cal(S)$ 中的覆盖只含有限多个映射，故对任意 $cal(U) in cal(S)$ 与任意 $0 <= q < n$，有：
  $
    caron(H)^p (cal(U), ul(H)^q (cal(F))) &= h^p (0 -> C^bullet (cal(U), ul(H)^q (cal(F)))) \
    &= h^p (dirlim_(j>=k') (0 -> C^bullet (cal(U)_j, ul(H)^q (cal(F)_j)))) #[因为有限极限与滤余极限交换] \
    &= dirlim_(j>=k') caron(H)^p (cal(U)_j, ul(H)^q (cal(F)_j))
  $
  对 $cal(U) in cal(S)$ 取正向极限，并像第二步那样处理范畴上的微妙之处，得到：
  $
    caron(H)^p (U, ul(H)^q (cal(F))) = dirlim_(j>=k) caron(H)^p (U_j, ul(H)^q (cal(F)_j))
  $
  换言之，作为谱序列的态射，$Phi: tilde(E)_2^(p,q) -> E_2^(p,q)$ 在区域 $0 <= q < n$ 上诱导同构。

  考虑满足 $p + q = n$ 的双次 $(p, q)$。对第 $r >= 2$ 页上涉及双次 $(p, q)$ 的微分：

  - 若 $q = n$，注意由 @cech-h0-of-hq-psh-vanish，$E_2^(0,n) = caron(H)^0 (U, ul(H)^n (cal(F))) = 0$，同理 $tilde(E)_2^(0,n) = 0$。于是所有涉及双次 $(0, n)$ 的微分都为零，$Phi$ 诱导同构 $tilde(E)_oo^(0,n) -> E_oo^(0,n)$，而其两端都是 $0$。

  - 设 $q < n$。

    - 若这个微分从 $(p, q)$ 发出，记作 $d^r: E_2^(p,q) -> E_2^(p+r,q-r+1)$。此时 $q - r + 1 < q < n$，故该微分位于区域 $0 <= q < n$ 内，于是对应于 $tilde(d)^r: tilde(E)_2^(p,q) -> tilde(E)_2^(p+r,q-r+1)$。

    - 若这个微分射入 $(p, q)$，记作 $d^r: E_2^(p-r,q+r-1) -> E_2^(p,q)$。由于这是第一象限的谱序列，该微分非零要求 $r <= p$，从而 $q + r - 1 <= q + p - 1 = n - 1$。于是该微分位于区域 $0 <= q < n$ 内，故对应于 $tilde(d)^r: tilde(E)_2^(p-r,q+r-1) -> tilde(E)_2^(p,q)$。

    于是 $Phi$ 在所有涉及双次 $(p, q)$ 的微分上诱导同构，并诱导同构 $tilde(E)_oo^(p,q) -> E_oo^(p,q)$。

  最后，存在滤过：
  $
    0 = tilde(F)_(n+1) subset tilde(F)_n subset dots.c subset tilde(F)_0 = tilde(H)^n = dirlim_(j>=k) H^n (U_j, cal(F)_j)
  $
  以及：
  $
    0 = F_(n+1) subset F_n subset dots.c subset F_0 = H^n = H^n (U, cal(F))
  $
  使得 $Phi$ 诱导与这些滤过相容的态射。此外还有交换图表：
  // https://q.uiver.app/#r=typst&q=WzAsMTAsWzAsMCwiMCJdLFsxLDAsInRpbGRlKEYpXihwKzEpIl0sWzIsMCwidGlsZGUoRilecCJdLFszLDAsInRpbGRlKEUpX29vXihwLG4tcCkiXSxbNCwwLCIwIl0sWzAsMSwiMCJdLFsxLDEsIkZeKHArMSkiXSxbMiwxLCJGXnAiXSxbMywxLCJFX29vXihwLG4tcCkiXSxbNCwxLCIwIl0sWzAsMV0sWzEsMl0sWzIsM10sWzMsNF0sWzUsNl0sWzYsN10sWzcsOF0sWzgsOV0sWzEsNiwiUGhpIl0sWzIsNywiUGhpIl0sWzMsOCwiUGhpIl1d
  #align(center, diagram({
    node((-2, -1), [$0$])
    node((-1, -1), [$tilde(F)^(p+1)$])
    node((0, -1), [$tilde(F)^p$])
    node((1, -1), [$tilde(E)_oo^(p,n-p)$])
    node((2, -1), [$0$])
    node((-2, 0), [$0$])
    node((-1, 0), [$F^(p+1)$])
    node((0, 0), [$F^p$])
    node((1, 0), [$E_oo^(p,n-p)$])
    node((2, 0), [$0$])
    edge((-2, -1), (-1, -1), "->")
    edge((-1, -1), (0, -1), "->")
    edge((0, -1), (1, -1), "->")
    edge((1, -1), (2, -1), "->")
    edge((-2, 0), (-1, 0), "->")
    edge((-1, 0), (0, 0), "->")
    edge((0, 0), (1, 0), "->")
    edge((1, 0), (2, 0), "->")
    edge((-1, -1), (-1, 0), [$Phi$], label-side: left, "->")
    edge((0, -1), (0, 0), [$Phi$], label-side: left, "->")
    edge((1, -1), (1, 0), [$Phi$], label-side: left, "->")
  }))
  对每个 $0 <= p <= n$。由五引理，既然 $Phi$ 诱导同构 $tilde(E)^(p,n-p)_oo -> E^(p,n-p)_oo$，便得到：
  $
    Phi: tilde(F)^(p+1) ->^tilde F^(p+1) ==> Phi: tilde(F)^p ->^tilde F^p
  $
  于是可以归纳地证明 $Phi$ 诱导同构 $tilde(F)^0 -> F^0$。换言之，我们得到了典范同构：
  $
    dirlim_(j>=k) H^q (U_j, u_j^(-1) cal(F)_0) ->^tilde H^q (U, v_0^(-1) cal(F)_0) 
  $
]

我们把这些极限公式用于计算平展层推前的茎。具体做法是：用严格 Hensel 化来刻画平展邻域的极限。这是严格 Hensel 化最重要的应用，也说明严格 Hensel 化给出了平展拓扑下正确的局部环。

#construction(name: <strict-local-ring-and-localization>)[
  给定概形 $X$ 与其几何点 $ol(x): Spec(Omega) -> X$，$X$ 在 $ol(x)$ 处的*严格局部环* (strict local ring) 定义为严格 Hensel 化：
  $
    cal(O)_(X,ol(x)) := cal(O)_(X,x)^#[sh] 
  $
  其中严格 Hensel 化是对包含 $k(x) -> k(x)^sep subset Omega$ 取的，这里 $k(x)^sep$ 是 $k(x)$ 在 $Omega$ 中的可分闭包。
  
  现在考虑正向极限：
  $
    dirlim_((Spec(C),ol(u)) -> (X,ol(x)) #[etale]) C = dirlim_((Spec(C),ol(u)) -> (X,ol(x)) #[etale]) cal(O)_(Spec(C),u)
  $
  即 $(X, ol(x))$ 的平展邻域组成的正向极限。
  
  任取平展邻域 $(Spec(B), frak(q)) -> (cal(O)_(X,x), frak(m)_x)$，连同包含 $phi: k(frak(q)) -> k(x)^sep$；它在定义 $A^#[sh]$ 的正向极限中给出一个阶段 $B_(frak(q))$。由 @passage-to-limit-of-morphisms (1) 与 @passage-to-limit-of-properties (3d)，该态射 $(Spec(B), frak(q)) -> (cal(O)_(X,x), frak(m)_x)$ 来自某个平展映射 $(Spec(C), frak(r)) -> (Spec(A), frak(m)_x)$ 的基变换，其中 $x in Spec(A) subset X$ 是仿射邻域。此外，相容的包含 $k(frak(q)) -> k(x)^sep$ 唯一地定义了 $Spec(C)$ 上一个位于 $frak(r)$ 之上、并落在 $ol(x)$ 之上的几何点。于是：
  $
    cal(O)_(X,ol(x)) = cal(O)_(X,x)^#[sh] = dirlim_((Spec(B),frak(q),phi)) B_(frak(q)) = dirlim_((Spec(C),ol(u)) -> (X,ol(x)) #[etale]) cal(O)_(Spec(C),u) = dirlim_((Spec(C),ol(u)) -> (X,ol(x)) #[etale]) C
  $  

  记：
  $
    tilde(X)_(ol(x)) = Spec(cal(O)_(X,ol(x)))
  $
  于是：
  $
    tilde(X)_(ol(x)) = lim_((Spec(C),ol(u)) -> (X,ol(x)) #[etale]) Spec(C)
  $
  它是 $(X, ol(x))$ 的一个共尾平展邻域系统在仿射过渡映射下的逆向极限。

  换言之，$x$ 处局部环的严格 Hensel 化就是 $(X, ol(x))$ 的平展邻域的极限。它之于平展拓扑，正如局部环之于 Zariski 拓扑。
]

#theorem(name: <limit-formula-for-schemes>)[
  (概形的极限公式) 设 ${Z_i}_(i in I)$ 是拟紧拟分离概形构成的余滤过系统，所有过渡映射都仿射，且有终对象 $0 in I$。
  
  令：
  $
    Z = lim_(i in I) Z_i
  $
  为余滤过极限，映射为 $v_i: Z -> Z_i, u_i: Z_i -> Z_0$。
  /*任取 $cal(F)_0 in cAb((Z_0)_et)$ 与拟紧拟分离的 $U in Et_Z$。则存在 $k in I$，使得前者是后者的基变换。于是由沿 $v_j$ 的拉回 $H^q (Z_j, u_j^(-1) cal(F)_0) -> H^q (Z, v_0^(-1) cal(F)_0)$ 诱导的典范映射：
  $
    dircolim_(j->k) H^q (U_j, u_j^(-1) cal(F)_0) -> H^q (U, v_0^(-1) cal(F)_0)
  $
  是同构。*/则存在典范同构：
  $
    dircolim_(i in I) H^q (Z_i, u_i^(-1) cal(F)_0) -> H^q (Z, v_0^(-1) cal(F)_0)
  $
]
#proof[
  $I$ 是正向集的情形上面已证。对一般的余滤过范畴 $I$，我们使用 Artin–Mazur 构造 @artin-mazur-construction。

  于是存在正向集 $P$ 与共尾函子 $F: P -> I^opp$。把 $P$ 换成某个元素 $0_P$ 对应的 $P_(>=0_P)$，不妨设 $P$ 有最小元 $0_P$。现在：
  $
    Z = lim_(i in I) Z_i = invlim_(p in P) Z_(F(p))
  $
  令 $cal(F)_i = u_i^(-1) cal(F)_0, cal(F) = v_0^(-1) cal(F)_0$。对给定的 $p in P$，过渡态射 $tilde(u)_p: Z_(F(p)) -> Z_(F(0_P))$ 满足 $u_(F(0_P)) compose tilde(u)_p = u_(F(p))$。特别地，
  $
    cal(F)_(F(p)) = tilde(u)_p^(-1) cal(F)_(F(0_P))
  $
  同样，令 $tilde(v)_p: Z -> Z_(F(p))$，则 $u_(F(0_P)) compose tilde(v)_(0_P) = v_0$。于是，
  $
    cal(F) = tilde(v)_(0_P)^(-1) cal(F)_(F(0_P))
  $
  因此，把前一个定理应用于正向集 $P$ 与概形族 ${Z_(F(p))}_(p in P)$，得到：
  $
    dircolim_(i in I) H^q (Z_i, cal(F)_i) = dirlim_(p in P) H^q (Z_(F(p)), cal(F)_(F(p))) = H^q (Z, cal(F))
  $
]

#theorem(name: <stalks-of-derived-lowerstar>)[
  设 $f: X -> Y$ 是概形间的拟紧拟分离态射。则对任意 $cal(F) in cAb(X_et)$ 与 $Y$ 的几何点 $ol(y)$，有自然同构：
  $
    (R^q f_* cal(F))_(ol(y)) = H^q (X times_Y tilde(Y)_(ol(y)), cal(F)|_(X times_Y tilde(Y)_(ol(y))))
  $
]
#proof[
  回忆：由 @derived-lower-star-first-props，$R^q f_* cal(F)$ 是 $U |-> H^q (X times_Y U, cal(F))$ 的层化；而由 @pullback-along-etale-morphism-derived，它也就是 $U |-> H^q (X times_Y U, cal(F)|_(X times_Y U))$ 的层化。又由 @pullback-first-props (3)，茎可以在预层层面取滤余极限来计算，故：
  $
    (R^q f_* cal(F))_(ol(y)) &= dircolim_((U,ol(u)) -> (Y,ol(y)) \ #[平展邻域]) H^q (X times_Y U, cal(F)|_(X times_Y U)) \
    &= dircolim_((U,ol(u)) -> (Y,ol(y)) \ #[仿射平展邻域]) H^q (X times_Y U, cal(F)|_(X times_Y U))
  $
  然而注意：
  $
    lim_((U,ol(u)) -> (Y,ol(y)) \ #[仿射平展邻域]) X times_Y U = X times_Y lim_((U,ol(u)) -> (Y,ol(y)) \ #[仿射平展邻域]) U = X times_Y tilde(Y)_(ol(y))
  $
  其中过渡映射都仿射，且每个 $X times_Y U$ 都在仿射概形 $U$ 上拟紧拟分离，因而自身拟紧拟分离。于是可以应用概形的极限公式（@limit-formula-for-schemes），得到：
  $
    (R^q f_* cal(F))_(ol(y)) = H^q (X times_Y tilde(Y)_(ol(y)), cal(F)|_(X times_Y tilde(Y)_(ol(y))))
  $
]

#corollary(name: <stalks-of-finite-pushforward>)[
  若 $f: X -> Y$ 是有限态射，则对任意 $cal(F) in cAb(X_et)$ 与 $Y$ 的任意代数闭几何点 $ol(y)$，存在典范同构：
  $
    (f_* cal(F))_(ol(y)) = oplus.big_(ol(x) in f^(-1)(ol(y))) cal(F)_(ol(x))
  $
  特别地，$f_*$ 正合。
]
#proof[
  由 @strict-henselization-and-finite-base-change，
  $
    X times_Y tilde(Y)_(ol(y)) = product_(ol(x) in f^(-1)(ol(y))) tilde(X)_(ol(x))
  $
  因此，
  $
    (f_* cal(F))_(ol(y)) &= Gamma(X times_Y tilde(Y)_(ol(y)), cal(F)|_(X times_Y tilde(Y)_(ol(y)))) = Gamma(product_(ol(x) in f^(-1)(ol(y))) tilde(X)_(ol(x)), cal(F)|_(product_(ol(x) in f^(-1)(ol(y))) tilde(X)_(ol(x)))) \
    &= oplus.big_(ol(x) in f^(-1)(ol(y))) Gamma(tilde(X)_(ol(x)), cal(F)|_(tilde(X)_(ol(x)))) = oplus.big_(ol(x) in f^(-1)(ol(y))) cal(F)_(ol(x))
  $
]

#corollary(name: <pushforward-by-finite-morphism>)[
  若 $f: X -> Y$ 是有限态射，则对任意 $cal(F) in cAb(X_et)$，有典范同构：
  $
    H^q (X, cal(F)) cong H^q (Y, f_* cal(F))
  $
]
#proof[
  考虑 Leray 谱序列：
  $
    E_2^(p,q) = H^p (Y, R^q f_* cal(F)) => H^(p+q) (X, cal(F))
  $
  由于 $f_*$ 正合，$q >= 1$ 时 $R^q f_* = 0$，于是 Leray 谱序列退化，给出典范同构：
  $
    H^q (Y, f_* cal(F)) ->^tilde H^q (X, cal(F))
  $
]

把层与概形的极限公式结合起来，就得到复合极限公式：

#theorem(name: <limit-formula-composite>)[
  (复合极限公式) 设 ${X_i}_(i in I)$ 是拟紧拟分离概形构成的逆向系统，其中所有过渡映射 $u_(i,j): X_i -> X_j$（$i>=j$）都仿射。令：
  $
    X = invlim_(i in I) X_i
  $
  投影为 $v_i: X -> X_i$。若以下两条成立，则称 $(cal(F)_i, psi_(i,j))$ 为逆向系统 ${X_i}$ 的*层系统* (system of sheaves)：

  - 每个 $cal(F)_i in cAb((X_i)_et)$ 都是 $X_i$ 上的平展交换群层。

  - 对任意 $i>=j$，$psi_(i,j): u_(i,j)^(-1) cal(F)_j -> cal(F)_i$ 是层态射，且对 $i>=j>=k$ 满足： #h(1fr)
    $
      psi_(i,k) = psi_(i,j) compose u_(i,j)^(-1) psi_(j,k)
    $

  这个层系统的*极限层* (limit sheaf) 定义为：
  $
    cal(F) := dirlim_(i in I) v_i^(-1) cal(F)_i
  $
  其中对 $i>=j$，过渡态射 $v_j^(-1) cal(F)_j -> v_i^(-1) cal(F)_i$ 就是态射 $v_i^(-1) psi_(i,j)$。于是，任取拟紧拟分离的 $U in Et_X$，都存在 $k$ 与拟紧拟分离的 $U_k in Et_(X_k)$，使得前者是后者的基变换；而典范态射
  $
    dirlim_(i>=k) H^q (U_i, cal(F)_i) -> H^q (U, cal(F))
  $
  是同构。
]
#proof[
  我们把层的极限公式（@limit-formula-for-sheaves）与概形的极限公式（@limit-formula-for-schemes）结合起来。由层的极限公式：
  $
    H^q (U, cal(F)) = H^q (U, dirlim_(j in I) v_j^(-1) cal(F)_j) = dirlim_(j in I) H^q (U, v_j^(-1) cal(F)_j) = dirlim_(j >=k) H^q (U, v_j^(-1) cal(F)_j)
  $
  现在对每个 $j>=k$ 应用概形的极限公式：
  $
    H^q (U, v_j^(-1) cal(F)_j) = dirlim_(i>=j) H^q (U_i, u_(i,j)^(-1) cal(F)_j)
  $
  于是得到一个二重正向极限：
  $
    H^q (U, cal(F)) = dirlim_(j>=k) dirlim_(i>=j) H^q (U_i, u_(i,j)^(-1) cal(F)_j)
  $
  由于 $I$ 是正向集，这个二重极限中的每一对 $(j,i)$ 都被 $(i,i)$ 支配。换言之，对应于 $i = j >= k$ 的对象在这个余极限的指标范畴中共尾。因此，
  $
    H^q (U, cal(F)) = dirlim_(j>=k) dirlim_(i>=j) H^q (U_i, u_(i,j)^(-1) cal(F)_j) = dirlim_(i>=k) H^q (U_i, cal(F)_i)
  $
  证毕。
]

由此得到一个推论，它是直接用极限概形上的层来陈述的极限公式。

#corollary(name: <limit-formula-adjunction>)[
  设 ${X_i}_(i in I)$ 是拟紧拟分离概形构成的逆向系统，其中所有过渡映射 $u_(i,j): X_i -> X_j$（$i>=j$）都仿射。令：
  $
    X = invlim_(i in I) X_i
  $
  投影为 $v_i: X -> X_i$。对任意 $cal(F) in cAb(X_et)$，${v_(i,*) cal(F)}_(i in I)$ 连同过渡态射
  $
    psi_(i,j): u_(i,j)^(-1) v_(j,*) cal(F) -> v_(i,*) cal(F)
  $
  构成 ${X_i}$ 的一个层系统，其极限层为 $cal(F)$；这些过渡态射由恒等态射 $v_(j,*) cal(F) -> u_(i,j,*) v_(i,*) cal(F) = v_(j,*) cal(F)$ 的伴随性定义。换言之，典范映射
  $
    dirlim_(i in I) v_i^(-1) v_(i,*) cal(F) -> cal(F)
  $
  是同构。特别地，由 @limit-formula-composite：
  $
    H^q (X, cal(F)) = dirlim_(i in I) H^q (X_i, v_(i,*) cal(F))
  $
]
#proof[
  为证 $dirlim_(i in I) v_i^(-1) v_(i,*) cal(F) cong cal(F)$，只需逐截面验证。对拟紧拟分离的 $U in Et_X$，若它由拟紧拟分离的 $U_k in Et_(X_k)$ 得到，则
  $
    (dirlim_(i in I) v_i^(-1) v_(i,*) cal(F))(U) &= dirlim_(i>=k) v_(i,*) cal(F) (U_i) #[由 @limit-formula-composite] \
    &= dirlim_(i>=k) cal(F)(U) = cal(F)(U)
  $
  由于每个 $U in Et_X$ 都能被拟紧拟分离的对象覆盖，我们便证明了 $dirlim_(i in I) v_i^(-1) v_(i,*) cal(F) cong cal(F)$。
]

极限公式还有相对版本：

#proposition(name: <relative-limit-formula-for-sheaves>)[
  设 $f: X -> S$ 是拟紧拟分离概形间的态射，${cal(F)_i}_(i in I)$ 是 $cAb(X_et)$ 中的一个正向系统，且
  $
    cal(F) = dirlim_(i in I) cal(F)_i
  $
  则自然映射
  $
    dirlim_(i in I) R^q f_* cal(F)_i -> R^q f_* cal(F)
  $
  是同构。
]
#proof[
  对 $S$ 的几何点 $ol(s)$，由于茎作为左伴随与余极限交换：
  $
    (dirlim_(i in I) R^q f_* cal(F)_i)_(ol(s)) = dirlim_(i in I) H^q (X times_S tilde(S)_(ol(s)), cal(F)_i|_(X times_S tilde(S)_(ol(s)))) = H^q (X times_S tilde(S)_(ol(s)), dirlim_(i in I) cal(F)_i|_(X times_S tilde(S)_(ol(s))))
  $
  这里用了 @limit-formula-for-sheaves。另一方面，
  $
    (R^q f_* cal(F))_(ol(s)) = H^q (X times_S tilde(S)_(ol(s)), cal(F)|_(X times_S tilde(S)_(ol(s))))
  $
  又因为拉回作为左伴随也与余极限交换，故：
  $
    cal(F)|_(X times_S tilde(S)_(ol(s))) = dirlim_(i in I) cal(F)_i|_(X times_S tilde(S)_(ol(s)))
  $
  证毕。
]

#proposition(name: <relative-limit-formula-for-schemes>)[
  设 $S$ 是拟紧拟分离概形，$X = invlim_(i in I) X_i$ 是拟紧拟分离 $S$-概形的逆向极限，过渡映射都仿射，有终对象 $0 in I$，结构映射为 $g: X -> S$ 与 $g_i: X_i -> S$。

  设 $cal(F)_0 in cAb((X_0)_et)$，并取 $cal(F)_i = cal(F)_0|_(X_i), cal(F) = cal(F)_0|_X$。则自然映射
  $
    dirlim_(i in I) R^q g_(i,*) cal(F)_i -> R^q g_* cal(F)
  $
  是同构。
]
#proof[
  对 $S$ 的几何点 $ol(s)$，由于茎作为左伴随与余极限交换：
  $
    (dirlim_(i in I) R^q g_(i,*) cal(F)_i)_(ol(s)) = dirlim_(i in I) (R^q g_(i,*) cal(F)_i)_(ol(s)) = dirlim_(i in I) H^q (X_i times_S tilde(S)_(ol(s)), cal(F)_i|_(X_i times_S tilde(S)_(ol(s))))
  $
  而由 @stalks-of-derived-lowerstar，
  $
    (R^q g_* cal(F))_(ol(s)) = H^q (X times_S tilde(S)_(ol(s)), cal(F)|_(X times_S tilde(S)_(ol(s))))
  $
  现在 $X_i times_S tilde(S)_(ol(s))$ 都拟紧拟分离，
  $
    cal(F)_i|_(X_i times_S tilde(S)_(ol(s))) = cal(F)_0|_(X_i)|_(X_i times_S tilde(S)_(ol(s))) = cal(F)_0|_(X_0 times_S tilde(S)_(ol(s)))|_(X_i times_S tilde(S)_(ol(s)))
  $
  去掉 $i$ 也有同样的等式。于是可以应用 @limit-formula-for-schemes，得到：
  $
    dirlim_(i in I) H^q (X_i times_S tilde(S)_(ol(s)), cal(F)_i|_(X_i times_S tilde(S)_(ol(s)))) -> H^q (X times_S tilde(S)_(ol(s)), cal(F)|_(X times_S tilde(S)_(ol(s))))
  $
  这就说明 $dirlim_(i in I) R^q g_(i,*) cal(F)_i -> R^q g_* cal(F)$ 是同构，证毕。
  /*
  对每个拟紧拟分离的 $U in Et_X$，
  $
    dirlim_(i in I) H^q (U times_S X_i, cal(F)_i) -> H^q (U times_S X, cal(F))
  $
  由 @limit-formula-for-schemes，它是同构。现在由 @derived-lower-star-first-props (3)，$R^q g_* cal(F)$ 是 $rho^q (g, cal(F)) := (U |-> H^q (U times_S X_i, cal(F)))$ 的层化。

  于是，自然预层态射：
  $
    dirlim_(i in I) rho^q (g_i, cal(F)_i) -> rho^q (g, cal(F))
  $
  在拟紧拟分离的 $U in Et_X$ 上逐截面为同构。层的余极限可以先按预层余极限计算再层化，而 $Et_X$ 中拟紧拟分离的 $U$ 上 $caron(H)^0 (U, -)$ 只需用拟紧拟分离的截面来计算，因此
  $
    R^q g_(i,*) cal(F)_i -> R^q g_* cal(F)
  $
  在 $Et_X$ 中所有拟紧拟分离的 $U$ 上为同构。每个 $U$ 都被拟紧拟分离的对象覆盖，故这个态射是层的同构。 */
]

#proposition(name: <relative-limit-formula-composite>)[
  设 $S$ 是拟紧拟分离概形。设 ${X_i}_(i in I)$ 是拟紧拟分离 $S$-概形构成的逆向系统，其中所有过渡映射 $u_(i,j): X_i -> X_j$（$i>=j$）都仿射。令：
  $
    X = invlim_(i in I) X_i
  $
  投影为 $v_i: X -> X_i$，结构映射为 $g_i: X_i -> S$。
  
  给定逆向系统 ${X_i}$ 的层系统 $(cal(F)_i, psi_(i,j))$，设其极限层为 $cal(F)$，则典范映射
  $
    dirlim_(i in I) R^q g_(i,*) cal(F)_i -> R^q g_* cal(F)
  $
  是同构。
]
#proof[
  我们把层的相对极限公式（@relative-limit-formula-for-sheaves）与概形的相对极限公式（@relative-limit-formula-for-schemes）结合起来：
  $
    R^q g_* cal(F) &= R^q g_* (dirlim_(j in I) v_j^(-1) cal(F)_j) = dirlim_(j in I) R^q g_* v_j^(-1) cal(F)_j \
    &= dirlim_(j in I) dirlim_(i>=j) R^q g_(i,*) u_(i,j)^(-1) cal(F)_j \
    &= dirlim_(i in I) R^q g_(i,*) cal(F)_i #[因为对角 $(i,i)$ 共尾]
  $
]

最后，我们在导出范畴中陈述 @stalks-of-derived-lowerstar。

#proposition(name: <derived-stalks-of-derived-pushforward>)[
  对 $cal(K) in D^+ (X_et, Lambda)$ 与概形间的拟紧拟分离态射 $f: X -> Y$，存在典范拟同构：
  $
    (R f_* cal(K))_(ol(y)) cong R Gamma(X times_Y tilde(Y)_(ol(y)), cal(K)|_(X times_Y tilde(Y)_(ol(y))))
  $
  若 $R f_*$ 与 $R Gamma (X times_Y tilde(Y)_(ol(y)), -)$ 上有界，则该拟同构对一切 $cal(K) in D(X_et, Lambda)$ 都成立。
]
#proof[
  我们应用 @stalks-of-derived-lowerstar 与 way-out 引理。
]
