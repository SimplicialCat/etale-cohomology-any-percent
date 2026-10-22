// audit-exception: 展示公式中的 #[...] 文字块内嵌两段行内公式，审计按相邻 $ 配对会把块内汉字切成伪公式段；只译块内说明文字，块内与块外公式逐段核对未变。
#import "void-import.typ": *

== 曲线的平展上同调 <sect-cohom-of-curves>
#let Jac = math.op[Jac]
本节中，“曲线”一词指域 $k$ 上一个整的、分离的、有限型且维数为 $1$ 的概形。我们并不假定曲线一定非奇异（即 $k$ 上光滑）；一旦作此假定，就写“光滑曲线”。不过，我们始终假定曲线是整的，因而连通。 

本节我们终于可以具体计算第一个非平凡的例子：光滑曲线的平展上同调。具体说来，曲线要么射影、要么仿射，而我们将证明下列结论： 

- 设 $X$ 是代数闭域 $k$ 上的任意曲线，$n >= 1$ 是任意自然数；则当 $q >= 3$ 时 $H^q_et (X, ZZ\/n) = 0$。 

- 若 $X$ 是代数闭域 $k$ 上的射影光滑曲线，且 $"char"(k) divides.not n$（包含 $"char"(k) = 0$ 的情形），则： #h(1fr)
  $
    H^q_et (X, ZZ\/n) cong cases(
      ZZ\/n &\, q = 0, 
      (ZZ\/n)^(oplus 2g(X)) &\, q = 1, 
      ZZ\/n &\, q = 2, 
      0 &\, q >= 3
    )
  $

- 若 $p = "char"(k) > 0$，$X$ 是代数闭域 $k$ 上的光滑曲线（仿射或射影均可），则： 
  $
    H^2_et (X, ZZ\/p) = 0
  $

- 若 $X$ 是代数闭域 $k$ 上的仿射曲线，则对任意 $n >= 1$， 
  $
    H^2_et (X, ZZ\/n) = 0
  $

我们先从 $GG_m$ 的上同调以及 $ZZ\/n$ 的上同调在次数 $>=3$ 时的消没入手。 

#proposition(name: <divisor-exact-sequence>)[
  （除子序列）设 $X$ 是代数闭域 $k$ 上的光滑曲线，$j: eta = Spec(K) -> X$，其中 $eta$ 是 $X$ 的泛点，$K$ 是其函数域。则有正合列： 
  $
    0 -> GG_m -> j_* GG_(m,eta) ->^#[div] oplus.big_(x in abs(X)) x_* ul(ZZ) -> 0
  $
]
#proof[
  由于 $X$ 是 Noether 概形，每个 $U in Et_X$ 都是局部 Noether 概形，因而局部连通。于是它是各个连通分支的不交并，所以只需对连通的 $U in Et_X$ 定义这个序列。 
  
  这样的 $U$ 在 $k$ 上光滑、相对维数为 $1$，因而非奇异。又因它连通，故是整的。于是 Weil 除子理论在 $U$ 上适用。此外 $U -> X$ 在 $k$ 上有限型，故把闭点送到闭点。因此 $U$ 在泛点 $eta in X$ 上的纤维就是 $U$ 的泛点 $eta_U$，从而 $j_* GG_(m,eta) (U) = GG_(m,eta) (eta_U) = cal(O)_(U,eta_U)^times = K(U)^times$。 
  
  这些态射定义如下： 
  $
    0 -> cal(O)_U (U)^times arrow.r.hook K(U)^times ->^#[div] oplus.big_(u in abs(U)) ZZ 
  $
  其中第一个映射就是函子的包含，第二个映射则在 $U$ 各闭点所对应的赋值处，对 $K(U)^times$ 中的函数求值。由 Weil 除子理论，这个序列左正合；中间的正合性大致就是下面这个代数事实： 
  #fact[
    设 $A$ 是 Noether 整闭环。则： 
    $
      A = inter.big_(frak(p) in Spec(A) \ "ht"(frak(p)) = 1) A_(frak(p))
    $
    其中交在 $Frac(A)$ 中取。 
  ]
  
  如此便得到一个左正合列： 
  $
    0 -> GG_m -> j_* GG_(m,eta) ->^#[div] oplus.big_(x in abs(X)) x_* ul(ZZ)
  $
  剩下要证它右正合，即每个 $d in oplus.big_(u in abs(U)) ZZ$ 都在 $U$ 上平展局部地来自 $K(U)^times$ 中的函数。但这在 $U$ 上 Zariski 局部成立：$U$ 非奇异，故局部唯一分解，于是 $U$ 上的每个 Weil 除子都 Zariski 局部主。 
]

// #lemma[
//   设 $X$ 是代数闭域 $k$ 上的有限型概形。则： 
  
//   + 若 $x in abs(X)$ 是闭点，则摩天楼层 $x_* M$ 满足： #h(1fr)
//     $
//       (x_* M)_(ol(y)) = cases(
//         M &\, y = x, 
//         0 &\, y != x
//       )
//     $
//     对任意位于 $y in X$ 之上的几何点 $ol(y)$。 

//   + 若某个 $cal(F)_(ol(x)) $
// ]

#proposition[
  设 $X$ 是代数闭域 $k$ 上的光滑曲线。则有典范同构： 
  $
    H^q_et (X, GG_m) cong cases(
      cal(O)_X (X)^times &\, q = 0, 
      Pic(X) &\, q = 1, 
      0 &\, q >= 2
    )
  $
]
#proof[
  $q = 0$ 的情形就是整体截面，$q = 1$ 的情形是 @h1-of-gm-is-pic。因此只需证明次数 $q >= 2$ 时的消没。 

  下面考虑除子正合列： 
  $
    0 -> GG_m -> j_* GG_(m,eta) ->^#[div] oplus.big_(x in abs(X)) x_* ul(ZZ) -> 0
  $
  它给出长正合列： 
  $
    dots.c -> H^(q-1) (X, oplus.big_(x in abs(X)) x_* ul(ZZ)) -> H^q (X, GG_m) -> H^q (X, j_* GG_(m,eta)) -> dots.c
  $
  于是要证 $H^q (X, GG_m) = 0$，只需证明以下两点： 
  
  - $H^(q-1) (X, oplus.big_(x in abs(X)) x_* ul(ZZ)) = 0$； 

  - $H^q (X, j_* GG_(m,eta)) = 0$。 

  第一点很容易： 
  $
    & H^(q-1) (X, oplus.big_(x in abs(X)) x_* ul(ZZ)) = oplus.big_(x in abs(X)) H^(q-1) (X, x_* ul(ZZ)) \
    =& oplus.big_(x in abs(X)) H^(q-1) (x, ul(ZZ)) #[由 @pushforward-by-finite-morphism 即得，因为包含映射 $x: x -> X$ 是闭浸入，从而是有限的] \
    =& 0 #[因为对每个 $x = Spec(k(x))$，$k(x) = k$ 是代数闭域，且 $q - 1 >= 1$]
  $
  于是只剩证明 $H^q (X, j_* GG_(m,eta)) = 0$。 

  #lemma(name: <gm-generic-pushforward-higher-vanishing>)[
    $R^q j_* GG_(m,eta) = 0$，对一切 $q >= 1$。 
  ]
  #proof[
    由于 $X$ 在域 $k$ 上有限型，其闭点极稠密。因此只需证明：对一切闭点 $x in abs(X)$， 
    $
      (R^q j_* GG_(m,eta))_x = 0
    $
    由 @stalks-of-derived-lowerstar，这等价于： 
    $
      H^q (eta times_X tilde(X)_x, GG_(m,eta)|_(eta times_X tilde(X)_x)) = 0
    $
    由 @divisor-exact-sequence 中的论证，每个连通 $U in Et_X$ 都是维数为 $1$ 的非奇异概形，且 $eta times_X U = eta_U = Spec(K(U))$ 是 $U$ 的泛点（由 @inverting-nonzeros-in-henselization (1)）。这样的 $U$ 在 $(X, x)$ 的平展邻域中也共尾。于是 
    $
      eta times_X tilde(X)_x &= lim_((U,ol(u)) -> (X,x) \ #[connected]) eta times_X U = lim_((U,ol(u)) -> (X,x) \ #[connected]) Spec(K(U)) \
      &= Spec(dircolim_((U,ol(u)) -> (X,x) \ #[connected])K(U))
    $
    取 $L = dircolim_((U,ol(u)) -> (X,x) \ #[connected]) K(U)$。每个 $K(U)$ 都是 $k$ 上超越次数为 $1$ 的域，故 $L$ 也是 $k$ 上超越次数为 $1$ 的域。此外，由非分歧性的定义，每个 $K(U)\/K(X)$ 都是有限可分扩张。因此 $L\/K(X)$ 是代数可分扩张。剩下要证： 
    $
      H^q (Spec(L), GG_(m,eta)|_(Spec(L))) = 0
    $

    #lemma[
      设 $L\/K$ 是代数可分扩张，则有典范同构： 
      $
        GG_(m,Spec(K))|_(Spec(L)) = GG_(m,Spec(L))
      $
    ]
    #proof[
      在 $Spec(L^sep) = Spec(K^sep)$ 处取茎，两边都得到 $Gal_L$-模 $(K^sep)^times$。再由 @struct-of-spec-k-et 即得。 
    ]

    由于 $L\/K(X)$ 是代数可分的， 
    $
      H^q (Spec(L), GG_(m,eta)|_(Spec(L))) = H^q (Spec(L), GG_(m,Spec(L))) = H^q_#[cont] (Gal_L, (L^sep)^times)
    $
    而 $L$ 在代数闭域 $k$ 上超越次数为 $1$，故由 @tsen-thm-in-galois-cohom (2)（曾炯定理的推论）可知它消没。 
  ]

  由于对一切 $q >= 1$ 有 $R^q j_* GG_(m,eta) = 0$，Leray 谱序列 
  $
    E_2^(p,q) = H^p (X, R^q j_* GG_(m,eta)) ==> H^(p+q) (eta, GG_(m,eta))
  $
  退化，给出同构： 
  $
    H^p (X, j_* GG_(m,eta)) cong H^p (eta, GG_(m,eta))
  $
  对一切 $p$。于是对 $q >= 1$， 
  $
    H^q (X, j_* GG_(m,eta)) cong H^q (eta, GG_(m,eta)) = H^q_#[cont] (Gal_(K(X)), (K(X)^sep)^times) = 0
  $
  因为 $K(X)$ 在代数闭域 $k$ 上超越次数为 $1$，由 @tsen-thm-in-galois-cohom (2)（曾炯定理的推论）即得。 
]

#corollary(name: <cohom-of-gm-on-general-curve>)[
  设 $X$ 是代数闭域 $k$ 上的任意曲线。则有典范同构：
  $
    H^q_et (X, GG_m) cong cases(
      cal(O)_X (X)^times & \, q = 0,
      Pic(X) & \, q = 1,
      0 & \, q >= 2
    )
  $
]
#proof[
  $q = 0$ 的情形就是整体截面，$q = 1$ 的情形是 @h1-of-gm-is-pic。因此只需证明次数 $q >= 2$ 时的消没。考虑正规化： 
  $
    nu: tilde(X) -> X
  $
  其中 $nu$ 有限满射，$tilde(X)$ 是 $k$ 上的光滑曲线，且存在非空开集 $V subset X$（即 $X$ 的非奇异轨迹），使得 $nu: nu^(-1) (V) -> V$ 是同构。考虑态射： 
  $
    GG_m -> nu_* GG_(m,tilde(X))
  $
  它在各个 $U in Et_X, tilde(U) = U times_X tilde(X)$ 上定义为 $cal(O)_U (U)^times -> cal(O)_(tilde(U)) (tilde(U))^times$。这个映射是单射，理由如下：有态射 $cal(O)_X -> nu_* cal(O)_(tilde(X))$，由正规化的构造它是单射。由于 $f: U -> X$ 平展、从而平坦，映射 $f^* cal(O)_X -> f^* nu_* cal(O)_(tilde(X))$ 是单射。又因拟凝聚层可沿平坦态射作基变换，有典范同构 $f^* nu_* cal(O)_(tilde(X)) cong nu'_* f'^* cal(O)_(tilde(X))$，其中 $f': tilde(U) -> tilde(X), nu': tilde(U) -> U$。换言之，态射 $cal(O)_U -> nu'_* cal(O)_(tilde(U))$ 是单射，从而 $cal(O)_U (U) -> cal(O)_(tilde(U)) (tilde(U))$ 是单射。因此在单位群上得到的态射也是单射。 

  取 $GG_m -> nu_* GG_(m,tilde(X))$ 的余核： 
  $
    0 -> GG_m -> nu_* GG_(m,tilde(X)) -> cal(R) -> 0
  $
  由于 $nu$ 诱导同构 $nu^(-1) (V) -> V$，对像落在 $V$ 中的任意 $U in Et_X$，$GG_m -> nu_* GG_(m,tilde(X))$ 在所有截面上都是同构。于是过渡到茎，$GG_m -> nu_* GG_(m,tilde(X))$ 在 $V$ 上方的所有几何点处都是同构。换言之，$cal(R)$ 在 $V$ 上方的所有几何点处茎为零，故它到 $V$ 的拉回为零。取 $Z = X - V$，这是有限个闭点，并取闭浸入 $i: Z -> X$。则由 @pushforward-by-closed-immersion (1)，存在 $cal(R)_0 in cAb(Z_et)$ 使得： 
  $
    cal(R) cong i_* cal(R)_0
  $
  现在由正规化序列得到长正合列： 
  $
    dots.c -> H^(q-1) (X, cal(R)) -> H^q (X, GG_m) -> H^q (X, nu_* GG_(m,tilde(X))) -> dots.c
  $
  当 $q >= 2$ 时， 

  - 由 @pushforward-by-finite-morphism，$H^(q-1) (X, cal(R)) = H^(q-1) (X, i_* cal(R)_0) = H^(q-1) (Z, cal(R)_0) = 0$。这是因为 $q - 1 >= 1$，而 $Z$ 是若干 $Spec(k)$ 的不交并，其中 $k$ 是代数闭域。 

  - 由 @pushforward-by-finite-morphism，因正规化 $nu$ 有限，$H^q (X, nu_* GG_(m,tilde(X))) = H^q (tilde(X), GG_(m,tilde(X)))$，而由光滑曲线的结论它等于 $0$。 

  因此 $H^q (X, GG_m) = 0$。 
]

#lemma(name: <mu-n-is-zn>)[
  设 $X$ 是严格 Hensel 局部环 $(A, frak(m), k)$ 上的概形，$n>=1$ 是满足 $n in k^times$ 的自然数。则对任意选定的 $n$ 次本原单位根 $zeta in k$，有同构： 
  $
    mu_n cong ul(ZZ\/n) in cAb(X_et)
  $
]
#proof[
  由于 $n in k^times$ 且 $k$ 可分闭，$k$ 有 $n$ 个互不相同的 $n$ 次单位根。由 Hensel 引理，$A$ 也有 $n$ 个互不相同的 $n$ 次单位根。固定一个 $n$ 次本原单位根 $zeta in A$。 

  下面定义预层态射： 
  $
    ul(ZZ\/n)_0 -> mu_n
  $
  在 $U in Et_X$ 上，这个预层态射由 $ZZ\/n -> mu_n (U), [m] |-> zeta^m$ 给出，其中 $mu_n (k) subset mu_n (U)$。这个预层态射在截面层面是单射，从而是单射。过渡到层化，得到单的层态射： 
  $
    ul(ZZ\/n) -> mu_n
  $
  因此只需证明这个态射是满射。对 $X$ 的任意几何点 $ol(x)$， 
  $
    (mu_n)_(ol(x)) &= dircolim_((U,ol(u)) -> (X,ol(x))) mu_n (cal(O)_U (U)) \
    &= mu_n (dircolim_((U,ol(u)) -> (X,ol(x))) cal(O)_U (U)) #[可以初等地验证] \
    &= mu_n (cal(O)_(X,ol(x)))
  $
  它可以借助 $X$ 处的严格局部环来表示。 

  #lemma[
    设 $(A, frak(m), k)$ 是 Hensel 局部环，$k$ 含 $n$ 个互不相同的 $n$ 次单位根，$(R, frak(n))$ 是局部 $A$-代数。则： 
    $
      mu_n (R) = mu_n (A) cong ZZ\/n
    $
  ]
  #proof[
    设 $1, zeta, dots.c, zeta^(n-1) in A^times$ 是 $A$ 中那 $n$ 个互不相同的 $n$ 次单位根。若 $r in R$ 满足 $r^n = 1 in R$，则： 
    $
      product_(j=0)^(n-1) (r - zeta^j) = 0 in R
    $
    于是存在某个 $0 <= j < n$ 使得 $r - zeta^j in frak(n)$。若对另一个 $0 <= i < n$ 也有 $r - zeta^i in frak(n)$，则 $zeta^i - zeta^j in frak(n)$ 不是 $R$ 的单位。然而这个元素在 $k^times$ 中的像非零，故它属于 $A^times$，从而属于 $R^times$，矛盾。 

    因此对一切满足 $i != j$ 的 $0 <= i < n$，$r - zeta^i in R - frak(n) = R^times$。把这些元素约去，即得 $r = zeta^j$。 
  ]
  于是作为抽象群有 $(mu_n)_(ol(x)) cong ZZ\/n$。现在态射 $ul(ZZ\/n) -> mu_n$ 在茎上诱导单射 $ZZ\/n -> (mu_n)_(ol(x)) cong ZZ\/n$。由于 $ZZ\/n$ 有限，这样的态射是满射。于是我们构造出了非典范同构： 
  $
    mu_n cong ul(ZZ\/n)
  $
]

#theorem(name: <cohom-of-general-curve>)[
  设 $X$ 是代数闭域 $k$ 上的任意曲线。 

  + 对任意自然数 $n in k^times$，有典范同构： #h(1fr)
    $
      H^q_et (X, mu_n) = cases(
        mu_n (k) &\, q = 0, 
        Pic(X)\/n Pic(X) &\, q = 2, 
        0&\, q >= 3
      )
    $

  + 若 $p = "char"(k) > 0$，则： 
    $
      H^q_et (X, ZZ\/p) = cases(
        ZZ\/p &\, q = 0, 
        0 &\, q >= 3
      ) 
    $

  + 对一切自然数 $n >= 1$，当 $q >= 3$ 时， 
    $
      H^q_et (X, ZZ\/n) = 0
    $
]
#proof[
  (1) 考虑 Kummer 序列： 
  $
    0 -> mu_n -> GG_m ->^((-)^n) GG_m -> 0
  $
  它诱导长正合列。在低次数部分，利用 $H^1_et (X, GG_m) = Pic(X)$，该长正合列为： 
  $
    0 &-> H^0_et (X, mu_n) -> cal(O)_X (X)^times ->^((-)^n) cal(O)_X (X)^times \
    &-> H^1_et (X, mu_n) -> Pic(X) ->^((-)^(otimes n)) Pic(X) \
    &-> H^2_et (X, mu_n) -> H^2_et (X, GG_m) = 0
  $
  由此可以确定： 
  $
    H^0_et (X, mu_n) = mu_n (k) \
    H^2_et (X, mu_n) = coker(Pic(X) ->^((-)^(otimes n)) Pic(X)) = Pic(X)\/n Pic(X)
  $
  对次数 $q >= 3$，长正合列给出： 
  $
    dots.c -> underbrace(H^(q-1) (X, GG_m), 0) -> H^q (X, mu_n) -> underbrace(H^q (X, GG_m), 0) -> dots.c
  $
  从而确定 $H^q (X, mu_n) = 0$。 

  (2) 考虑 Artin–Schreier 序列：
  $
    0 -> ul(ZZ\/p) -> GG_a -->^(x |-> x^p - x) GG_a -> 0
  $
  在次数 $0$ 处，由整体截面得 $H^0_et (X, ZZ\/p) = ZZ\/p$。在次数 $q >= 3$ 处有： 
  $
    dots.c -> H^(q-1)_et (X, GG_a) -> H^q_et (X, ZZ\/p) -> H^q_et (X, GG_a) -> dots.c
  $
  然而对 $r >= 2$， 
  $
    H^r_et (X, GG_a) = H^r_#[Zar] (X, cal(O)_X) = 0
  $
  因为 $dim(X) = 1$，而 Zariski 上同调在次数超过维数时消没。于是当 $q >= 3$ 时，$H^(q-1)_et (X, GG_a) = H^q_et (X, GG_a) = 0$，从而： 
  $
    H^q_et (X, ZZ\/p) = 0
  $

  (3) 由 (1)(2) 以及上一个引理， 
  $
    H^q_et (X, ZZ\/p) = 0
  $
  对一切素数 $p$ 与次数 $q >= 3$ 成立。再利用正合列 $0 -> ZZ\/n -> ZZ\/m n -> ZZ\/m -> 0$ 即可得出结论；该正合列诱导： 
  $
    dots.c -> H^q_et (X, ZZ\/n) -> H^q_et (X, ZZ\/m n) -> H^q_et (X, ZZ\/m) -> dots.c
  $
]

接下来，我们具体计算射影光滑曲线的上同调。 

#theorem(name: <cohom-of-proj-curve>)[
  若 $X$ 是代数闭域 $k$ 上的射影曲线，且 $"char"(k) divides.not n$（包含 $"char"(k) = 0$ 的情形），则： #h(1fr)

  + 有典范同构： #h(1fr)
    $
      H^q_et (X, mu_n) cong cases(
        mu_n (k) & \, q = 0,
        Pic(X)[n] & \, q = 1,
        Pic(X)\/n Pic(X) ->^deg_tilde ZZ\/n & \, q = 2,
        0 & \, q >= 3
      )
    $
    而当 $X$ 光滑时，有非典范同构： 
    $
      H^q_et (X, ZZ\/n) cong cases(
        ZZ\/n & \, q = 0,
        (ZZ\/n)^(oplus 2g(X)) & \, q = 1,
        ZZ\/n & \, q = 2,
        0 & \, q >= 3
      )
    $

  + 若 $p = "char"(k) > 0$，则有非典范同构：
    $
      H^q_et (X, ZZ\/p) cong cases(
        ZZ\/p &\, q = 0, 
        (ZZ\/p)^(oplus gamma(X)) &\, q = 1, 
        0 &\, q >= 2
      )
    $
    其中 $0 <= gamma(X) <= g(X)$ 是一个不变量，称为曲线 $X$ 的 *Hasse–Witt 不变量*。 

  + 若 $p = "char"(k) > 0$，则对一切 $q >= 2$ 有 $H^q_et (X, ZZ\/p^a) = 0$。 
]
#proof[
  (1) 由于 $X$ 射影，$cal(O)_X^times = k^times$。事实上 $cal(O)_X (X) = k$：
  
  - 理由如下：$cal(O)_X (X)$ 是既约的有限维 $k$-代数，从而是若干份 $k$ 的直积。若它是多于一份 $k$ 的直积，则有幂等元把 $X$ 分成两个开闭集，这与 $X$ 连通矛盾。 
  
  考虑由 Kummer 序列诱导的长正合列，它在低次数处的部分为： 
  $
     0 & -> H^0_et (X, mu_n) -> k^times ->^((-)^n) k^times \
       & -> H^1_et (X, mu_n) -> Pic(X) ->^((-)^(otimes n)) Pic(X) \
       & -> H^2_et (X, mu_n) -> 0
  $
  由于 $k$ 代数闭，$k^times ->^((-)^n) k^times$ 是满射。于是连接态射 $k^times -> H^1_et (X, mu_n)$ 为零。因此： 
  $
    H^1_et (X, mu_n) = ker(Pic(X) ->^((-)^(otimes n)) Pic(X)) = Pic(X)[n]
  $
  并且： 
  $
    H^2_et (X, mu_n) = coker(Pic(X) ->^((-)^(otimes n)) Pic(X)) = Pic(X)\/n Pic(X)
  $
  由 Abel 簇理论： 
  #fact[
    若 $X$ 是代数闭域 $k$ 上的光滑射影曲线，则存在正合列： 
    $
      0 -> Pic^0 (X) -> Pic(X) ->^deg ZZ -> 0
    $
    并且还存在 $k$ 上的 Abel 簇 $Jac(X)$，使得 $Pic^0 (X) cong Jac(X)(k)$，而后者可以等同于 $Jac(X)$ 的 $k$-点。此外 $times n: Jac(X)(k) -> Jac(X)(k)$ 是满射，其核同构于 $(ZZ\/n)^(oplus 2g(X))$。 
  ]
  利用这个事实， 
  $
    H^1_et (X, mu_n) = Pic(X)[n] cong Pic^0 (X)[n] cong (ZZ\/n)^(oplus 2g(X))
  $
  $
    H^2_et (X, mu_n) = Pic(X)\/n Pic(X) cong ZZ\/n
  $
  证毕。 

  (2) 由 Artin–Schreier 序列：
  $
    0 -> ul(ZZ\/p) -> GG_a ->^(wp) GG_a -> 0 
  $
  其中 $wp: x |-> x^p - x$，得到正合列： 
  $
    0 &-> ZZ\/p -> k ->^wp k \
    &-> H^1_et (X, ZZ\/p) -> H^1_et (X, GG_a) -->^(H^1 (wp)) H^1_et (X, GG_a) \
    &-> H^2_et (X, ZZ\/p) -> 0
  $
  由于 $k$ 代数闭，$wp: k -> k$ 是满射（因为对每个 $c in k$，方程 $X^p - X = c$ 在 $k$ 中都有根），故连接态射 $k -> H^1_et (X, ZZ\/p)$ 为零。此外 $H^1_et (X, GG_a) = H^1_#[Zar] (X, cal(O)_X)$。于是： 
  $
    H^1_et (X, ZZ\/p) = ker(H^1 (wp): H^1_#[Zar] (X, cal(O)_X) -> H^1_#[Zar] (X, cal(O)_X)) \
    H^2_et (X, ZZ\/p) = coker(H^1 (wp): H^1_#[Zar] (X, cal(O)_X) -> H^1_#[Zar] (X, cal(O)_X))
  $
  由于 $X$ 在 $k$ 上射影，$V = H^1_#[Zar] (X, cal(O)_X)$ 是有限维 $k$-向量空间。Frobenius $F: cal(O)_X -> cal(O)_X, x |-> x^p$ 满足 $F(c x) = c^p F(x)$，且 $wp = F - id$。因此态射 $wp := H^1 (wp): V -> V$ 可以写成 $wp = F - id$，其中 $F: V -> V$ 是满足 $F(c x) = c^p F(x)$ 的加性映射。 

  #lemma[
    设 $k$ 是特征 $p$ 的代数闭域，$V$ 是有限维 $k$-向量空间，并且 
    $
      F: V -> V
    $
    是 $p$-线性映射，即对一切 $c in k, v in V$ 满足 $F(c v) = c^p F(v)$ 的 $FF_p$-线性映射。则存在分解： 
    $
      V = V_#[ss] oplus V_#[nil]
    $
    其中这两个子空间都是 $F$-稳定的 $k$-线性子空间，并且： 

    - $V_#[ss]$ 由 $F$ 的不动点张成，且 $F: V_#[ss] -> V_#[ss]$ 是双射。 

    - $F: V_#[nil] -> V_#[nil]$ 幂零。 
  ]
  #proof[
    由于每个 $F^m$ 都是 $p^m$-线性的，子集 $im(F^m)$ 与 $ker(F^m)$ 实际上是 $V$ 的 $k$-线性子空间。事实上，若 $v = F^m w in im(F^m)$，则 $c v = F^m (c^(1\/p^m) w) in im(F^m)$。若 $v in ker(F^m)$，则 $F^m (c v) = c^(p^m) F^m(v) = 0$，故 $c v in ker(F^m)$。 

    取： 
    $
      V_#[ss] = inter.big_(m>=0) im(F^m), V_#[nil] = union.big_(m>=0) ker(F^m)
    $
    按定义，这两个子空间都是 $F$-稳定的。由于 $V$ 有限维，子空间链 ${im(F^m)}_(m>=0)$（递减）与 ${ker(F^m)}_(m>=0)$（递增）必然最终稳定，比如在第 $N$ 步之后。 

    现在证明 $V = V_#[ss] oplus V_#[nil]$。由第一同构定理，有 $k$-向量空间之间的 $p^m$-线性双射 $V\/ker(F^m) -> im(F^m)$。 

    我们断言：若有限维 $k$-向量空间之间存在 $p^m$-线性双射 $phi: U -> W$，则 $dim_k (U) = dim_k (W)$。 

      - 事实上，取 $U$ 的一组 $k$-基 $u_1, dots.c, u_d$，只需证明 $phi(u_1), dots.c, phi(u_d)$ 是 $W$ 的 $k$-基。 

      - 任取 $w in W$。由于 $phi$ 满射，可取 $u = sum_i c_i u_i in U$ 使得 $phi(u) = w$。则： #h(1fr)
        $
          w = phi (sum_i c_i u_i) = sum_i c_i^(p^m) phi(u_i)
        $
        它由 ${phi(u_i)}$ 张成。 

      - 若 $sum_i c_i phi(u_i) = 0$，则： 
        $
          phi (sum_i c_i^(1\/p^m) u_i) = 0
        $
        由于 $phi$ 单射，$sum_i c_i^(1\/p^m) u_i = 0$，故每个 $c_i^(1\/p^m) = 0$。于是每个 $c_i = 0$。 

    于是得到： 
    $
      dim_k (ker(F^m)) + dim_k (im(F^m)) = dim_k (V)
    $
    取 $m = N$，即得： 
    $
      dim_k (V_#[ss]) + dim_k (V_#[nil]) = dim_k (V)
    $
    此外，若 $v in V_#[ss] ∩ V_#[nil]$，则 $v in im(F^N)$，故存在 $x$ 使 $v = F^N x$。由于 $v in ker(F^N)$，有 $F^(2N) x = F^N v = 0$。于是 $x in ker(F^(2N)) = ker(F^N)$（因为 ${ker(F^m)}$ 在第 $N$ 步之后稳定），从而 $v = F^N x = 0$。因此 $V_#[ss] ∩ V_#[nil] = 0$。结合上面的维数等式，得到： 
    $
      V = V_#[ss] oplus V_#[nil]
    $
    在 $V_#[nil]$ 上已有 $F^N = 0$。在 $V_#[ss]$ 上，按定义 $F$ 是满射，故有 $p$-线性同构 $V_#[ss]\/ker(F|_(V_#[ss])) -> V_#[ss]$。由上面的断言得到 $dim_k (ker(F|_(V_#[ss]))) = 0$，因此 $F$ 在 $V_#[ss]$ 上也是单射。显然 $F$ 的不动点都在 $V_#[ss]$ 中，所以剩下要证 $V_#[ss]$ 由 $F$ 的不动点张成。 

    为此，把 $V$ 换成 $V_#[ss]$、$F$ 换成 $F|_(V_#[ss])$，并假定 $F$ 是双射。令 $n = dim(V_#[ss])$。任取一组基 $e_1, dots.c, e_n in V$，设 $F e_j = sum_(i=1)^n m_(i,j) e_i$，并作矩阵 $M = mat(m_(i,j))_(i,j) in GL_n (k)$。则： 
    $
      F(sum_i x_i e_j) = sum_(i,j) m_(i,j) x_j^p e_i
    $
    因此要找 $F$ 的不动点，只需解方程组： 
    $
      x_i = sum_(j=1)^n m_(i,j) x_j^p, forall 1<=i<=n
    $
    这些解与 $Spec(A)$ 的闭点一一对应，其中： 
    $
      A = k[X_1, dots.c, X_n]/(({X_i - sum_(j=1)^n m_(i,j) X_j^p, forall 1<=i<=n}))
    $
    由于 $M$ 可逆，这些方程等价于把每个 $x_i^p$ 写成各 $x_i$ 的线性组合。因此 $A$ 是 $p^n$ 维的有限 $k$-代数。现在： 
    $
      Omega_(A\/k) = (oplus.big_(i=1)^n k[X_1, dots.c, X_n] d X_i)/(({d(X_i - sum_(j=1)^n m_(i,j) X_j^p), forall 1<=i<=n}))
    $
    然而在特征 $p$ 下 $d(X_i - sum_(j=1)^n m_(i,j) X_j^p) = d X_i$，所以分母中的子模其实就是 $(d X_1, dots.c, d X_n)$，即整个 $oplus.big_(i=1)^n k[X_1, dots.c, X_n] d X_i$。换言之 $Omega_(A\/k) = 0$，故 $A$ 是平展 $k$-代数。由于 $k$ 代数闭，$A$ 是若干份 $k$ 的直积；又因 $dim_k (A) = p^n$，份数必为 $p^n$。于是 $Spec(A)$ 有 $p^n$ 个闭点，即 $F$ 有 $p^n$ 个不动点。 

    记 $V^F$ 为 $F$ 的不动点集。由于 $F$ 是 $FF_p$-线性的，$V^F$ 是基数为 $p^n$ 的 $FF_p$-向量空间，从而维数为 $n$。取 $V^F$ 的一组 $FF_p$-基 $v_1, dots.c, v_n in V^F$。我们断言这些向量在 $k$ 上确实线性无关。否则，取满足 $1<=m<=n$ 的最小下标，使得 $v_1, dots.c, v_m$ 在 $k$ 上存在非平凡线性关系。$v_m$ 的系数必然非零，否则便得到 $v_1, dots.c, v_(m-1)$ 的非平凡线性关系。把该系数归一化为 $1$，便得到线性关系： 
    $
      v_m = sum_(i=1)^(m-1) c_i v_i
    $
    施加 $F$ 并利用每个 $v_i$ 都是 $F$-不动点，得到： 
    $
      v_m = sum_(i=1)^(m-1) c_i^p v_i
    $
    于是 $sum_(i=1)^(m-1) (c_i^p - c_i) v_i = 0$。由于 $v_1, dots.c, v_(m-1)$ 线性无关，每个 $c_i^p - c_i = 0$，即 $c_i in FF_p$。换言之，$v_1, dots.c, v_m$ 之间实际上存在 $FF_p$ 上的线性关系，矛盾。 

    于是 $v_1, dots.c, v_n$ 是 $V$ 的一组由 $F$ 的不动点组成的基。 
  ]
  现在考察 $wp = F - id: V = H^1_#[Zar] (X, cal(O)_X) -> V$，其中 $F$ 是 $p$-线性的。由上一个引理，可按 $F$ 把它分解为 
  $
    V = V_#[ss] oplus V_#[nil]
  $
  并取 $gamma = gamma(X) := dim_k (V_#[ss])$。现在： 

  - 在 $V_#[nil]$ 上 $F$ 幂零，设 $F^N = 0$。则 $wp = F - id$ 有逆，即： #h(1fr)
    $
      wp^(-1) = - sum_(i=0)^(N-1) F^i
    $
    因此 $wp$ 在 $V_#[nil]$ 上的核与余核都是零。 

  - 在 $V_#[ss]$ 上，可取 $V_#[ss]$ 的一组由 $F$-不动向量组成的基 $v_1, dots.c, v_gamma$。则： 
    $
      wp(sum_(i=1)^gamma x_i v_i) = sum_(i=1)^gamma (x_i^p - x_i) v_i
    $
    由于 $k$ 代数闭，形如 $X^p - X - c, c in k$ 的方程在 $k$ 中都有根。因此 $wp$ 在 $V_#[ss]$ 上是满射。其核由满足 $x_i^p - x_i = 0$ 的系数 $x_i$ 组成，即 $x_i in FF_p$。换言之，$ker(wp)$ 是 $gamma$ 维的 $FF_p$-向量空间。 

  于是： 
  $
    H^1_et (X, ZZ\/p) = ker(wp\: V -> V) cong (ZZ\/p)^(oplus gamma(X)) \
    H^2_et (X, ZZ\/p) = coker(wp\: V -> V) = 0
  $
  结合次数 $>=3$ 时的消没，即得结论。 

  (3) 这由正合列 $0 -> ZZ\/n -> ZZ\/m n -> ZZ\/m -> 0$ 以及 $q >= 2$ 时 $H^q_et (X, ZZ\/p) = 0$ 的消没推出。 
]

接下来证明仿射光滑曲线上的消没： 

#theorem(name: <h2-zn-of-affine-smooth-curve>)[
  设 $X$ 是代数闭域 $k$ 上的仿射光滑曲线。则： 
  $
    H^q_et (X, ZZ\/n) = 0
  $
  对一切 $q >= 2$ 与一切自然数 $n$ 成立。 
]
#proof[
  由于已有 $q >= 3$ 时的消没，只需对一切 $n$ 证明 $H^2_et (X, ZZ\/n) = 0$。 

  当 $n = p = "char"(k)$ 时，用 Artin–Schreier 序列： 
  $
    dots.c -> H^1_et (X, GG_a) -> H^2_et (X, ZZ\/p) -> H^2_et (X, GG_a) -> dots.c
  $
  其中当 $q >= 1$ 时 $H^q_et (X, GG_a) = H^q_#[Zar] (X, cal(O)_X) = 0$，因为 $X$ 仿射。因此 $H^2_et (X, ZZ\/p) = 0$。 

  其次设 $n in k^times$。我们已经证明： 
  $
    H^2_et (X, ZZ\/n) = Pic(X)\/n Pic(X)
  $
  取 $X$ 的射影紧化 $ol(X)$，它是光滑射影曲线。由除子理论，有右正合列： 
  $
    oplus.big_(z in ol(X)-X) ZZ -> Pic(ol(X)) -> Pic(X) -> 0
  $
  取定一点 $z in ol(X)-X$，把 $Pic(ol(X))$ 中的除子 $D$ 平移 $-deg(D)z$，便可使其次数为 $0$，而它在 $Pic(X)$ 中的像保持不变。换言之，有满射 $Pic^0 (ol(X)) -> Pic(X)$。 
  // https://q.uiver.app/#r=typst&q=WzAsNCxbMCwwLCJQaWMob2woWCkpXjAiXSxbMSwwLCJQaWMoWCkiXSxbMSwxLCJQaWMoWCkiXSxbMCwxLCJQaWMob2woWCkpXjAiXSxbMCwxLCIiLDAseyJzdHlsZSI6eyJoZWFkIjp7Im5hbWUiOiJlcGkifX19XSxbMywyLCIiLDAseyJzdHlsZSI6eyJoZWFkIjp7Im5hbWUiOiJlcGkifX19XSxbMCwzLCJ0aW1lcyBuIiwxXSxbMSwyLCJ0aW1lcyBuIiwxXV0=
  #context align(center, diagram({
    node((-1, -1), [$Pic^0 (ol(X))$])
    node((0, -1), [$Pic(X)$])
    node((0, 0), [$Pic(X)$])
    node((-1, 0), [$Pic^0 (ol(X))$])
    edge((-1, -1), (0, -1), "->>")
    edge((-1, 0), (0, 0), "->>")
    edge((-1, -1), (-1, 0), [$times n$], label-side: center, "->>")
    edge((0, -1), (0, 0), [$times n$], label-side: center, "->")
  }, crossing-fill: thm-box-curr-color()))
  其中左侧竖箭头是满射，这由前面关于射影曲线的讨论可知。于是 $times n: Pic(X) -> Pic(X)$ 是满射，从而： 
  $
    H^2_et (X, ZZ\/n) = Pic(X)\/n Pic(X) = 0
  $
  再用 $n$ 与 $p$ 两种情形以及正合列 $0 -> ZZ\/n -> ZZ\/m n -> ZZ\/m -> 0$ 即可完成证明。 
]

常值层的具体计算到此结束；本节余下的篇幅用于讨论一般挠层的高次消没。 

#remark(name: <remark-on-vanishing>)[
  曲线的平展上同调这个例子展示了消没定理。 

  有一个比较定理（@cite-SGA4[Expos\'e XI, Th\'eor\`eme 4.4]）说：对 $CC$ 上的簇 $X$，有典范同构：
  $
    H^q_et (X, ul(ZZ\/ell)) cong H^q_#[sing] (X(CC), ZZ\/ell)
  $
  现在若 $X$ 的维数为 $n$，则 $X(CC)$ 的实维数为 $2n$。于是当 $q > 2n$ 时右端消没。我们自然期望左端在 $q > 2n$ 时也消没。由此可以猜想如下消没定理： 

  - （Grothendieck 消没）设 $X$ 是可分闭域 $k$ 上维数为 $d$ 的有限型概形。则对一切挠层 $cal(F) in cAb(X_et)$，当 $q > 2d$ 时 $H^q_et (X, cal(F)) = 0$。 

  这一点在曲线的情形已经得到验证：我们刚刚证明曲线的上同调在次数超过 $2$ 之后消没。 

  我们也看到，仿射光滑曲线的上同调在次数超过 $1$ 之后消没。这是仿射概形上更强的一个消没定理的例子： 

  - （Artin 消没）设 $X$ 是可分闭域 $k$ 上维数为 $d$ 的有限型仿射概形。则对一切挠层 $cal(F) in cAb(X_et)$，当 $q > d$ 时 $H^q_et (X, cal(F)) = 0$。 
]

/*
现在我们来证明曲线的 Grothendieck 消没。 

#lemma[
  设 $X$ 是可分闭域 $k$ 上维数为 1 的不可约 Noether 概形，泛点为 $eta$。假设 $cal(R) in cAb(X_et)$ 满足 $cal(R)_(ol(eta)) = 0$。则有自然同构： 
  $
    cal(R) cong oplus.big_(x in abs(X)) x_* cal(R)_x
  $
  特别地， 
  $
    H^q (X, cal(R)) = 0, forall q >= 1
  $
]
#proof[
  考虑由伴随给出的典范态射： 
  $
    gamma: cal(R) -> product_(x in abs(X)) x_* cal(R)_x
  $
  对每个拟紧拟分离的 $(f: U -> X) in Et_X$，$U$ 平展、从而在 $X$ 上拟有限，故也是 $K$ 上维数为 1 的 Noether 概形。现在对每个闭点 $x in abs(X)$ 与任意 $u in f^(-1)(x)$，$k(u)\/k(x)$ 是有限可分扩张，从而是 $K$ 的有限扩张。因此 $u$ 是闭点。换言之，$U$ 的各不可约分支的泛点 $eta_1, dots.c, eta_n in U$ 都必须落在 $eta in X$ 之上。 

  于是对每个截面 $s in cal(R)(U)$，有 $s_(ol(eta)_i) in cal(R)_(ol(eta)) = 0$。故由 @vanishing-stalks-spreads-out，存在 Zariski 开集 $V subset U$ 包含所有 $eta_1, dots.c, eta_n$，使得 $s|_V = 0$。由于 $V$ 包含 $U$ 各不可约分支的全部泛点，$V$ 是稠密开集，于是 $Z = U - V$ 是 $U$ 的有限个闭点。因此： 
  $
    gamma(s) in product_(x in abs(X)) x_* cal(R)_(x) (U) = product_(x in abs(X)) product_(ol(u) in f^(-1)(x)) cal(R)_(x)
  $
  它就是元素 $(s_(ol(u)))_(x,ol(u))$，其分量 $s_(ol(u))$ 在有限个 $ol(u)$ 之外全为零。于是 $gamma(s)$ 实际上落在： 
  $
    gamma(s) in oplus.big_(x in abs(X)) oplus.big_(ol(u) in f^(-1)(x)) cal(R)_(x) = (oplus.big_(x in abs(X)) x_* cal(R)_(x)) (U)
  $
  其中最后一个等号由 @limit-formula-for-sheaves 得到。换言之，$gamma(cal(R))$ 本来是 $product_(x in abs(X)) x_* cal(R)_(x)$ 的子层，现在实际上是 $oplus.big_(x in abs(X)) x_* cal(R)_(x)$ 的子层。于是有自然映射： 
  $
    gamma: cal(R) -> oplus.big_(x in abs(X)) x_* cal(R)_(x)
  $
  由于茎与直和交换，再结合 @stalks-of-skyscraper-sheaves 与 @stalks-of-finite-pushforward，得到： 
  $
    (oplus.big_(x in abs(X)) x_* cal(R)_(x))_(ol(y)) = cases(
      cal(R)_y &\, y in abs(X), 
      0 &\, y = eta
    ) = cal(R)_(ol(y))
  $
  于是 $gamma: cal(R) -> oplus.big_(x in abs(X)) x_* cal(R)_(x)$ 是同构。此外，由 @limit-formula-for-sheaves 与 @pushforward-by-finite-morphism， 
  $
    H^q (X, cal(R)) = oplus.big_(x in abs(X)) H^q (X, x_* cal(R)_(ol(x))) = oplus.big_(x in abs(X)) H^q (x, cal(R)_(ol(x))) = 0
  $
  对一切 $q >= 1$ 成立。 
]

#theorem(name: <grothendieck-vanishing-for-curve>)[
  设 $X$ 是可分闭域上的任意曲线，$cal(F) in cAb(X_et)$ 是挠层。则对一切 $q >= 3$， 
  $
    H^q (X, cal(F)) = 0
  $
]
#proof[
  设 $j: eta = Spec(K(X)) -> X$ 是泛点的包含。考虑自然态射： 
  $
    gamma: cal(F) -> j_* j^(-1) cal(F)
  $
  我们断言 $gamma$ 在 $ol(eta)$ 处的茎上是同构。事实上 $tilde(X)_(ol(eta)) = Spec(cal(O)_(X,eta)^#[sh]) = Spec(K(X)^#[sh]) = Spec(K(X)^sep) = ol(eta)$，于是： 
  $
    (R^q j_* j^(-1) cal(F))_(ol(eta)) = H^q (eta times_X ol(eta), j^(-1) cal(F)|_(eta times_X ol(eta))) = H^q (ol(eta), cal(F)_(ol(eta))) = cases(
      cal(F)_(ol(eta)) &\, q = 0, 
      0 &\, q >= 1
    )
  $
  换言之，$ker(gamma)_(ol(eta)) = coker(gamma)_(ol(eta)) = 0$，且对 $q >= 1$ 有 $(R^q j_* j^(-1) cal(F))_(ol(eta)) = 0$。由上一个引理， 
  $
    H^p (X, ker(gamma)) = H^p (X, coker(gamma)) = 0, forall p >= 1 \
    H^p (X, R^q j_* j^(-1) cal(F)) = 0, forall p >= 1
  $
  由于 $H^p (X, ker(gamma)) = H^p (X, coker(gamma)) = 0, forall p >= 1$，用短正合列可知，对一切 $p >= 2$， 
  $
    H^p (X, cal(F)) cong H^p (X, im(gamma)) cong H^p (X, j_* j^(-1) cal(F))
  $
  因此只需对 $p >= 3$ 证明 $H^p (X, j_* j^(-1) cal(F)) = 0$。为此使用 Leray 谱序列 @derived-lower-star-first-props (2)： 
  $
    E_2^(p,q) = H^p (X, R^q j_* j^(-1) cal(F)) ==> H^(p+q) (eta, j^(-1) cal(F)) 
  $
  现在对 $q >= 2$ 与 $x in abs(X)$， 
  $
    (R^q j_* j^(-1) cal(F))_x = H^q (eta times_X tilde(X)_x, cal(F)|_(eta times_X tilde(X)_x))
  $
  与 @gm-generic-pushforward-higher-vanishing 的证明相同，$eta times_X tilde(X)_x = Spec(L)$，其中 $L$ 是 $k$ 上超越次数为 $1$ 的扩域。于是这个上同调就是 $H^q_#[cont] (Gal_L, -)$ 作用于离散挠 $Gal_L$-模的值，因为 $cal(F)$ 是挠层。由 @tsen-thm-in-galois-cohom (1)（曾炯定理的推论），这个上同调消没。因此 $(R^q j_* j^(-1) cal(F))_x = 0$。于是对一切 $q >= 2$ 有 $R^q j_* j^(-1) cal(F) = 0$。 
  
  我们还证明了，对 $p >= 1$ 有 $H^p (X, R^1 j_* j^(-1) cal(F)) = 0$。于是在 Leray 谱序列 
  $
    E_2^(p,q) = H^p (X, R^q j_* j^(-1) cal(F)) ==> H^(p+q) (eta, j^(-1) cal(F)) 
  $
  中，$E_2$-页上仅有的非零项是 $E_2^(p,0)$ 与 $E_2^(0,1)$。唯一存活的微分是 $d_2: E_2^(0,1) -> E_2^(2,0)$，谱序列在 $E_3$-页稳定。于是对一切 $p >= 3$，该谱序列诱导同构： 
  $
    H^p (X, j_* j^(-1) cal(F)) = H^p (eta, j^(-1) cal(F))
  $
  而它由 @tsen-thm-in-galois-cohom (1) 消没，这是曾炯定理的推论；其中 $eta = Spec(K(X))$ 是 $k$ 的一个超越次数为 1 的扩张的谱，且因 $cal(F)$ 是挠层，$j^(-1) cal(F)$ 是挠 $Gal_(K(X))$-模。 

  于是对 $p >= 3$，我们证明了 
  $
    H^p (X, cal(F)) cong H^p (X, j_* j^(-1) cal(F)) cong H^p (eta, j^(-1) cal(F)) = 0
  $
  证毕。 
]
*/
