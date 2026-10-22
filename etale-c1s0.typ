#import "void-import.typ": *

本引言中，我们简要说明为什么要发展平展上同调 (étale cohomology) 这套理论。 

#question[
  设 $M$ 是复流形。怎样研究 $M$ 的几何？ 
  - 度量；

  - 用上同调理论把 $M$ “线性化”： 
    + Betti 上同调 $H_B^bullet (M, ZZ)$ 既可以定义为奇异上同调 (singular cohomology)，也可以定义为常值层 (constant sheaf) 的层上同调 (sheaf cohomology)。 

      它是拓扑不变量，与微分结构之类的东西无关。 

    + de Rham 上同调 $H^bullet_"dR" (M)$。它可以定义为 $C^oo$ 形式的上同调，也可以定义为解析微分形式的上同调。在复流形上，这两种定义一致。 

      这些上同调理论具有一些很好的性质，例如：  

      #theorem[
        #set enum(numbering: "(11a)")
        + (de Rham 同构)
          $
            H^*_B (M, ZZ) otimes CC cong H^*_B (M, CC) cong H^*_"dR" (M)
          $
          （这是用全纯 Poincaré 引理证明的。）

        + (Hodge 分解) 若 $M$ 是紧 Kähler 流形（例如射影流形），则存在函子性的分解： 
        $
          H^n_"dR" (M) cong oplus.big_(p+q=n) underbrace(H^(p,q) (M), (p,q)"-Dolbeault 上同调")
        $
        其中 $H^n_"dR" (M)$ 上的复共轭作用为 $overline(H^(p,q)) = H^(q,p)$。 
      ]
]

#question[
  要研究代数簇，有没有代数上的对应物？设 $X$ 是域 $k$ 上的光滑 (smooth) 代数簇。 

  - 首先，我们有代数 de Rham 上同调： 
    $
      H^bullet_"dR" (X\/k) := h^bullet (R Gamma(X, cal(O)_X overset(->,d) Omega_(X\/k)^1 overset(->,d) dots.c))
    $
    它由代数 de Rham 复形定义。 
    #theorem[
      (Grothendieck; @cite-grothendieck-de-rham) 若 $k = CC$，则存在从 $X$ 的代数 de Rham 上同调到 $X(CC)$（视为复流形）的解析 de Rham 上同调的自然映射：
      $
        H^*_"dR" (X\/CC) -> H^*_"dR" (X(CC))
      $
      它是有限维 $CC$-向量空间之间的同构。 
    ]
    话虽如此，代数 de Rham 上同调在特征 $p$ 下表现很差。 
    #example[
      设 $X = AA_(FF_p)^1 = Spec(FF_p [x])$。这是仿射空间，故凝聚层的高阶上同调消没。于是： 
      $
        H^bullet_"dR" (X\/FF_p) = h^bullet (#box(baseline: 2em)[
        $
          underbrace(FF_p [x], cal(O)_X (X)) &overset(->, d) underbrace(FF_p [x] d x, Omega_(X\/FF_p)^1 (X))     \ f(x) &|-> f'(x) d x         
        $])
      $
      这个映射不只杀掉常数，还会杀掉 $x^p$ 之类的东西。因此 $H^0_"dR" (AA^1\/FF_p) = FF_p [x^p]$，它是无限维 $FF_p$-向量空间。 
    ]
]

#question[
  那么 $pi_1 (M)$ 和 Betti 上同调 $H^bullet_B (M, ZZ)$ 的代数对应物呢？ 

  - 答案是平展上同调 $H^bullet_et (X, underbrace(ZZ_ell "或" QQ_ell, "而非" ZZ))$ 与平展基本群 (étale fundamental group) $pi_1^et (X)$。 

    下面的比较定理其实只说了一件事：对代数簇而言，平展上同调是 Betti 上同调的良好类比。 

    #theorem[
      (Artin; @cite-SGA4[Exposé XI, Théorème 4.4]) 若 $k = CC$，则存在自然同构：
      $
        H^n_B (X(CC), ZZ) otimes_ZZ ZZ_ell cong H^n_et (X, ZZ_ell)
      $
      以及： 
      $
        pi_1^et (X) cong hat(pi_1^"top" (X(CC)))
      $
      其中 $pi_1^"top"$ 就是拓扑基本群 (topological fundamental group)，帽子表示投射有限完备化 (profinite completion)：$hat(G) := invlim_(N triangle.l.small G "有限指数") G\/N$。 
    ]

    #example[
      $
        H_et^n (AA^1_CC, ZZ_ell) = H_B^n (CC, ZZ_ell) = cases(ZZ_ell&\, n = 0, 0 &\, n!=0) \
        
        pi_1^et (AA^1) = hat(pi_1^"top" (CC)) = 0
      $
      而： 
      $
        pi_1^et (GG_m, 1)  = hat(pi_1^"top" (CC^times)) = hat(ZZ)
      $
      #footnote[严格说来，这里本应把基点写出来，结果应是 $hat(ZZ)(1)$，它是一个 Tate 扭。你现在不需要知道 Tate 扭是什么，它要到大约 400 页之后才会派上用场。]
    ]
]

#question[
  怎样定义 $H^bullet_et$ 和 $pi_1^et$？ 

  注意 $pi_1 (M) = Aut(tilde(M)\/M)$，其中 $tilde(M) -> M$ 是万有覆叠。这正是覆叠空间的 Galois 理论。因此，我们需要先为代数簇的覆叠空间确定合适的概念，再在这一概念上做 Galois 理论。 

  - 要把这套理论代数化，第一步是为局部同构找到代数的对应概念。这个概念就是*平展态射 (étale morphism)*。 

  在某种意义上，平展态射是拓扑空间开子集的类比物。因此， 

  - 平展基本群将对代数簇 $X$ 的平展覆叠空间进行分类，即 $X$ 上的有限平展态射； 

  - 对性质良好的拓扑空间 $X$，奇异上同调可以定义为 $X$ 上的层的导出函子上同调。 

    既然平展态射（按助记的说法，就是“平展开集”）正是开集的正确类比，我们就来定义_平展层 (étale sheaf)_的概念。它们与（拓扑）层类似，只不过把开集换成了平展态射。平展上同调于是定义为平展层的导出函子上同调。 
]

平展上同调的构造为特征 $p$ 下的代数簇给出了一套好的上同调理论。 
#construction[
  设 $X_0$ 是特征 $p$ 的域 $k = FF_q$ 上的光滑代数簇。定义 $F_(X_0): X_0 -> X_0$ 为 $q$ 次绝对 Frobenius，它在空间层面是恒等映射，在层/函数层面则作用为 $f |-> f^q$。 

  现在基变换到代数闭包 $X = X_0 times_(FF_q) overline(FF_q)$，于是 $F_(X_0)$ 基变换为 $F = F_(X_0) times id_(Spec(overline(FF_q))): X -> X$，这是 $overline(FF_q)$-概形的自态射。 

  于是，只要 $ell != p$，由平展上同调的函子性，$F^*$ 就作用在有限维 $QQ_ell$-向量空间 $H^n_et (X, QQ_ell)$ 上。$F$ 作用在 $overline(FF_q)$-点 $X(overline(FF_q))$ 上。可以验证，$F^n$ 的不动点恰为： 
  $
    (X(overline(FF_q)))^(F^n) = X_0 (FF_(q^n))
  $
  于是可以数点了。 

  #theorem[
    (Grothendieck–Lefschetz 迹公式) 若 $X$ 在 $FF_q$ 上紧合#footnote[这是一个技术性假设，用来避开紧支上同调 (compactly supported cohomology)。]，则 
    $
      \# X_0 (FF_(q^n)) = \# (X(overline(FF_q)))^(F^n) = sum_(m=0)^(2 dim(X)) (-1)^m tr((F^*)^n\; H^m_et (X, QQ_ell))
    $
    （事实上，平展上同调在次数大于维数的二倍时消没。）
  ]
  这给出一个生成级数： 
  $
    sum_(n>=1) (\# X_0 (FF_(q^n)))/n t^n = sum_(m=0)^(2 dim(X)) (-1)^m sum_(n>=1) tr((F^*)^n\; H^m_et (X, QQ_ell))/n t^n
  $
  看到这样的表达式，你现在就该取指数了。因为： 
  $
    exp(sum_(n>=1) (alpha^n t^n)/n) = 1/(1-alpha t)
  $
  右端取指数后得到： 
  $
    product_(m=0)^(2 dim(X)) det(1-t F^*\;H^m_et (X, QQ_ell))^((-1)^(m+1))
  $
  由初等分析，左端取指数后得到： 
  $
    product_(x in abs(X_0) "闭点") 1/(1-t^(deg(x)))
  $
  其中 $deg(x) = [k(x):FF_q]$，$k(x)$ 是 $x$ 处的剩余域。 
  现在： 
  $
    Z(X_0\/FF_q, t) = product_(x in abs(X_0)) 1/(1-t^deg(x))
  $
  这就给出了 $X_0$ 的 $zeta$ 函数： 
  $
    Z(X_0\/FF_q, q^(-s)) = product_(x in abs(X_0)) 1/(1-abs(k(x)^(-s)))
  $

  细致分析平展上同调的性质之后，我们就能陈述并证明 Weil 猜想。 
  #theorem[
    (Weil 猜想；@cite-deligne-weil1) 对光滑紧合的 $X_0$，
    $
      P_m (t) := det(1- t F^*\;H^m_et (X, QQ_ell)) in QQ_ell [t]
    $
    落在 $1 + t ZZ[t]$ 中，且与 $ell$ 无关。 

    此外，若在 $CC[t]$ 中把它写成 $P_m (t) = product_i (1 - alpha_(m, i) t)$，则每个 $abs(alpha_(m,i)) =q^(m\/2)$ 都成立。 
  ]

  Weil 猜想其实应当看作函数域上的 Riemann 假设，而且它还是 Riemann 假设的一个已获证明的类比！它在解析数论中有深刻的应用，能为代数指数和族给出最优的相消与不相关性。张益唐证明素数间隙有界时，就用到了这类方法#footnote[不过据我所知，这个用例已经被优化掉了。]。所谓_应用 $ell$-进上同调_，说的正是这类方法；它们的应用远不止这一例。   
]

平展上同调还能构造 Galois 表示。  
#construction[
  设 $X\/k$ 是一个簇，且 $ell != "char"(k)$。绝对 Galois 群 $Gal_k$ 作用在 $H^n_et (X_(overline(k)), QQ_ell)$ 上，也就是说，它作用在 $X_(overline(k)) = X times_k overline(k)$ 中的 $overline(k)$ 上。 

  这给出 $ell$-进 Galois 表示 $Gal_k -> GL_n (QQ_ell)$。通常很难构造出 $k$ 的 Galois 表示的例子（例如 $k = QQ$ 时）。 

  平展上同调与 Galois 表示之间的这种联系，在 Langlands 纲领中很重要。例如，把模形式的 Fourier 系数解释为平展上同调上的某些迹，就能由 Weil 猜想推出 Ramanujan 猜想。 
]

最后附带一提，平展上同调还与代数 de Rham 上同调相关，桥梁是 de Rham 同构的代数类比。$p$-进 Hodge 理论中有这样一个定理： 
#theorem[
  (Tsuji, Faltings, Nizioł, ..., \~2000) 设 $k$ 是 $QQ_p$ 的有限扩张，$X$ 是 $k$ 上光滑紧合的代数簇。则存在典范同构： 
  $
    H^n_et (X_(overline(k)), QQ_p) otimes_(QQ_p) B_("dR") cong H^n_"dR" (X\/k) otimes_k B_("dR")
  $
  这里 $B_"dR"$ 是 Fontaine 的 de Rham 周期环，它是包含 $overline(k)$ 的域，也是 $2 pi i$ 的 $p$-进类比。 
]
