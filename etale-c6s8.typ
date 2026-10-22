#import "void-import.typ": *

== $R^q f_*$ 与 $H^q$ 的高阶消没

本节应用紧合基变换证明上同调的高阶消没。在较弱的假设下，我们同时给出相对陈述（即关于 $R^q f_*$ 的陈述）与绝对陈述（即关于 $H^q$ 的陈述）。

我们将论证 @remark-on-vanishing 中的论断：若 $X$ 是代数闭域 $k$ 上的有限型概形，则对挠层 $cal(F)$，当 $q > 2dim(X)$ 时 $H^q (X, cal(F))$ 消没；若再假定 $X$ 仿射，则当 $q > dim(X)$ 时它就消没。这一点既有形式上的理由，也有严格的动机：

- 建立这一消没，将为从关于 Abel 范畴 $cAb(X_et)$ 的陈述过渡到其导出范畴 $D^bullet (X_et)$ 铺平道路。具体来说，我们要证明 $R f_*$ 与 $R Gamma$ 这类三角函子既上有界又下有界，从而能在上有界导出范畴 $D^- (X_et)$ 乃至无界导出范畴 $D(X_et)$ 上定义它们，并使投影公式、Künneth 公式这类结论得以陈述。

- 一旦建立起 $H^q (X, -)$ 在 $q > 2d$（其中 $d = dim(X)$）时的消没，我们便看出 $H^(2d) (X, -): cAb(X_et, ZZ\/n) -> cAb$ 现在是右正合的。

  我们最终会陈述并证明 Poincaré 对偶。目前你可以这样理解它：只要 $X$ 是代数闭域 $k$ 上紧合光滑的，且 $cal(F)$ 满足某些条件，$H^q (X, cal(F))$ 与 $H^(2d-q) (X, caron(cal(F)))$ 之间就有对偶（模去 Tate 扭）。既然我们事后相信 $H^(2d)$ 与 $H^0$ 对偶，该函子就必定是右正合的。
  
  这不仅让我们有理由相信 Poincaré 对偶至少是合理的，还揭示出如下观点：Poincaré 对偶之所以有可能成立，完全取决于平展上同调在二倍维数以上的消没。如果我们现在不建立这一消没，那么想要推进到 Poincaré 对偶便是不合理的。

Artin 消没还有一个历史层面的理由，这使它在平展上同调理论中占据自然的位置：

- 我们一直在奇异上同调与平展上同调之间作类比。1959 年，@cite-andreotti-frankel 证明了光滑仿射复代数簇同伦等价于一个维数等于其复维数的 CW 复形。特别地，它的奇异上同调在该维数以上消没；这与流形的情形不同——流形上奇异上同调的高阶消没提示的是_实_维数。

  1963–1964 年，在 Grothendieck 那场催生了平展上同调的传奇讨论班上（讲义后来以 @cite-SGA4 之名流传），人们提出并证明了平展上同调的 Artin 消没。因此从历史角度看，它正是作为这种奇异上同调消没的类比，顺理成章地被形式化并确立下来的。

// 与平展上同调中大多数结果一样，Artin 消没通过对维数归纳来证明。在我们的情形中，启动归纳只需要一次看似无害的紧合基变换调用，以及一些一维的消没结果。

#lemma(name: <relative-grothendieck-vanishing-in-dim-1>)[
  设 $f: X -> Y$ 是紧合态射，其纤维的维数 $<=1$。则对一切挠层 $cal(F) in cAb(X_et)$ 及一切 $q>2$，都有 $R^q f_* cal(F) = 0$。
]
#proof[
  对 $Y$ 的每个几何点 $ol(y) = Spec(k(y)^sep)$，由紧合基变换（因 $f$ 紧合）有
  $
    (R^q f_* cal(F))_(ol(y)) cong H^q (X_(ol(y)), cal(F)|_(X_(ol(y))))
  $
  由 @pullback-of-torsion-sheaf，$cal(F)|_(X_(ol(y))) in cAb((X_(ol(y)))_et)$ 是挠层；而 $X_(ol(y))$ 是可分闭域 $k(y)^sep$ 上维数为 1 的紧合概形。于是由 @grothendieck-vanishing-in-dim-1，当 $q >= 3$ 时 $H^q (X_(ol(y)), cal(F)|_(X_(ol(y)))) = 0$。因此 $R^q f_* cal(F)$ 的各茎全为零，故：
  $
    R^q f_* cal(F) = 0, forall q>=3
  $
]

#notation(name: <etale-cohomological-dimension>)[
  设 $X$ 是概形。我们记：
  $
    cd(X) := min({d >= 0 : forall cal(F) in cAb(X_et) #[挠], forall q > d, H^q (X, cal(F)) = 0}) in NN union {oo}
  $
  并称之为该概形的*平展上同调维数* (étale cohomological dimension)。对环 $A$，用 $cd(A)$ 表示 $cd(Spec(A))$。
]

#lemma(name: <cohom-dim-of-rings-props>)[
  + 设 $K$ 是域，$A$ 是维数为 1 的有限型 $K$-代数。则：#h(1fr)
    $
      cd(A) <= cd(K) + 1
    $
  
  + 设 $A = dircolim_i A_i$ 是环的滤余极限。则：
    $
      cd(A) <= sup_i cd(A_i)
    $

  + 设 $L\/K$ 是超越次数为 $d$ 的域扩张。则：
    $
      cd(L) <= cd(K) + d
    $
]
#proof[
  证明这些结果时，对挠层 $cal(F)$，我们会按定义使用 $cal(F) = dirlim_(n>=1) cal(F)[n!]$，并结合极限公式 @limit-formula-for-sheaves，把问题化归为 $cal(F)$ 对某个固定 $n$ 是 $n$-挠的情形。此时，对 $cal(F)$ 施加加性函子得到的层仍是 $n$-挠，因此无需再论证所涉及的层为何是挠的。整个证明中我们会默认使用这一技巧，不在每次用到时说明。

  (1) 设 $X = Spec(A)$，$ol(X) = X otimes_K K^sep$。设 $f: X -> Spec(K)$ 是结构态射，$ol(k): Spec(K^sep) -> Spec(K)$ 是几何点。则对 $cal(F) in cAb(X_et, ZZ\/n)$，由 @stalks-of-derived-lowerstar，并注意 $tilde(Spec(K))_(ol(k)) = Spec(K^sep)$，有：
  $
    (R^q f_* cal(F))_(ol(k)) = H^q (X otimes_K K^sep, cal(F)|_(X otimes_K K^sep)) = H^q (ol(X), cal(F)|_(ol(X)))
  $
  由于 $ol(X)$ 是 $K^sep$ 上维数为 1 的有限型仿射概形，由 @artin-vanishing-in-dim-1 得 $cd(ol(X)) <= 1$。因此当 $q >= 2$ 时 $H^q (ol(X), cal(F)|_(ol(X))) = 0$，从而当 $q >= 2$ 时 $R^q f_* cal(F) = 0$。现在考虑 Leray 谱序列 @derived-lower-star-first-props (2)：
  $
    E_2^(p,q) = H^p (Spec(K), R^q f_* cal(F)) => H^(p+q) (X, cal(F))
  $
  由上同调维数的定义及上述论证，$E_2$ 页只在 $p <= cd(K), q <= 1$ 处非零。因此 $H^n (X, cal(F))$ 只在 $n <= cd(K) + 1$ 时可能非零，即：
  $
    cd(A) = cd(X) <= cd(K) + 1
  $

  (2) 由 @artin-mazur-construction，不妨假设 $A = dirlim_i A_i$ 是正向极限。取 $X = Spec(A), X_i = Spec(A_i)$，于是：
  $
    X = invlim_i X_i
  $
  是仿射概形的逆向极限。将投影记为 $v_i: X -> X_i$。对 $cal(F) in cAb(X_et, ZZ\/n)$，由极限公式 @limit-formula-adjunction，
  $
    H^q (X, cal(F)) = dirlim_i H^q (X_i, v_(i,*) cal(F)) = 0
  $
  只要 $q > sup_i cd(A_i)$ 就有上式，因为每个 $H^q (X_i, v_(i,*) cal(F)) = 0$ 都各自成立。因此：
  $
    cd(A) = cd(X) <= sup_i cd(A_i)
  $

  (3) 可以取一列域扩张 $L = L_d\/L_(d-1)\/dots.c\/L_0 = K$，使每一步的超越次数都是 1。只要解决了超越次数为 1 的情形，就可以归纳地得到一般情形。因此不妨设 $d = 1$，且 $L\/K$ 的超越次数为 1。现在：
  $
    L = dirlim_lambda A_lambda
  $
  是它的有限型 $K$-子代数 ${A_lambda}$ 的正向极限。由于 $L\/K$ 的超越次数为 $1$，每个 $Frac(A_lambda)\/K$ 的超越次数都 $<=1$，故 $dim(A_lambda) <= 1$。于是由 (1)，每个 $cd(A_lambda) <= cd(K) + 1$。再由 (2)，
  $
    cd(L) <= sup_i cd(A_lambda) <= cd(K) + 1
  $
  证毕。
]

Artin 消没的技术引擎是下述命题：

#proposition(name: <artin-vanishing-engine>)[
  设 $K$ 是域，$X$ 是 $K$ 上维数为 $d$ 的有限型概形。设 $x in X$，记 $a = dim(ol({x}))$。则存在 $K(t_1, dots.c, t_a)^sep$ 上维数 $<=d-a$ 的有限型概形 $Y$（它同时也是 $X$-概形），以及位于 $x in X$ 上方的一个闭点 $y in Y$，使得有 $K$-代数同构：
  $
    cal(O)_(X,x)^#[sh] cong cal(O)_(Y,y)^#[sh]
  $
  此外，若 $X$ 在 $x$ 附近正则，则可以取 $Y$ 为正则概形。
]
#proof[
  这个问题对 $X$ 是局部的，故不妨设 $X = Spec(A)$ 仿射。由于超越次数 $trd_K (k(x)) = a$，可以选取 $c_1, dots.c, c_a in A$，使其在 $k(x)$ 中的像代数无关，从而定义态射：
  $
    f: X -> AA^a_K
  $
  它把 $x$ 送到泛点 $eta in AA^a_K$。现在考虑泛纤维 $f_eta: X_eta -> eta = Spec(K(t_1, dots.c, t_a))$，它是有限型的。对任意 $z in X_eta subset X$，有
  $
    trd_(K(t_1, dots.c, t_a)) (k(z)) = trd_K (k(z)) - a
  $
  故 $X_eta$ 的维数为 $d-a$。进一步，$trd_(K(t_1, dots.c, t_a)) (k(x)) = trd_K (k(x)) - a = a - a = 0$，所以 $x in X_eta$ 是闭点。最后，
  $
    cal(O)_(X_eta,x) = cal(O)_(X,x)\/frak(m)_(AA^a_K,eta) cal(O)_(X,x) = cal(O)_(X,x)
  $
  接下来，考虑几何点 $ol(eta): Spec(K(t_1,dots.c,t_a)^sep) -> eta -> X$，它对应于 $K(t_1, dots.c, t_a)$ 的一个固定可分闭包。取 $Y = X_(ol(eta))$，并取 $y in Y$ 为 $x in X_eta$ 上方的任意一点。由于 $Y = X_eta times_eta ol(eta)$，可见 $dim(Y) = d - a$，且 $y$ 是闭点。现在：

  #lemma[
    设 $K$ 是域，$X$ 是 $K$-概形。固定一个可分闭包 $K -> K^sep$。设 $x in X$，取 $ol(x) in ol(X) = X otimes_K K^sep$ 为 $x in X$ 上方的一点。则存在 $K$-代数同构：
    $
      cal(O)_(X,x)^#[sh] cong cal(O)_(ol(X),ol(x))^#[sh]
    $
  ]
  #proof[
    对每个有限可分扩张 $L\/K$，取 $X_L = X otimes_K L$，令 $x_L in X_L$ 为 $ol(x)$ 的像。这给出相容的点系统 ${x_L in X_L}$。由于 $ol(X) = invlim_(L\/K #[有限可分]) X_L$，我们有：
    $
      cal(O)_(ol(X),ol(x)) = dirlim_(L\/K #[有限可分]) cal(O)_(X_L,x_L)
    $
    由于严格 Hensel 化与正向极限交换，
    $
      cal(O)_(ol(X),ol(x))^#[sh] = dirlim_(L\/K #[有限可分]) cal(O)_(X_L,x_L)^#[sh]
    $
    然而每个 $X_L$ 都在 $X$ 上平展，故有自然同构 $cal(O)_(X_L,x_L)^#[sh] cong cal(O)_(X,x)^#[sh]$。于是我们得到同构：
    $
      cal(O)_(ol(X),ol(x))^#[sh] cong cal(O)_(X,x)^#[sh]
    $
  ]
  由上述引理，
  $
    cal(O)_(Y,y)^#[sh] cong cal(O)_(X_eta,x)^#[sh] cong cal(O)_(X,x)^#[sh]
  $
  作为 $K$-代数成立。
  
  最后处理正则性部分。由 @permanence-of-properties-under-henselization (1)，Noether 局部环 $A$ 正则当且仅当 $A^#[sh]$ 正则。因此若 $X$ 在 $x$ 附近正则，则 $cal(O)_(X,x)$ 正则，故其严格 Hensel 化也正则；又 $cal(O)_(Y,y)^#[sh] cong cal(O)_(X,x)^#[sh]$，于是 $cal(O)_(Y,y)$ 正则。域上有限型概形的正则轨迹是开集（例如见 #cite-stacks("07R5")[Lemma 29.19.3]），所以 $Y$ 在 $y$ 附近正则。适当缩小 $Y$，即可取 $Y$ 正则。
]

现在可以开始证明 Artin 消没所需的归纳了。我们将沿用 @notation-supp-on-dim-a 中“支撑在维数 $<=a$ 上”这一说法。

#theorem(name: <artin-vanishing>)[
  (Artin 消没) 设 $K$ 是域，$X$ 是 $K$ 上维数为 $d$ 的有限型仿射概形。则：
  $
    cd(X) <= cd(K) + d
  $
]
#proof[
  $d = 0$ 的情形只需对有限扩张应用 @cohom-dim-of-rings-props (3)；$d = 1$ 的情形由 @cohom-dim-of-rings-props (1) 处理。于是我们假设 $d >= 2$，并且 Artin 消没在维数 $<= d - 1$ 时已经成立。

  #lemma[
    假设 Artin 消没在维数 $<= d - 1$ 时成立。

    设 $K$ 是域，$j: U -> X$ 是 $K$ 上维数为 $d$ 的正则代数簇之间的开浸入，其补集 $D = X - U$ 是 $X$ 上某个有效 Cartier 除子的支集。则对任意挠层 $cal(F) in cAb(U_et)$，$R^q j_* cal(F)$ 支撑在维数 $<= d - q$ 的闭子集上。
  ]
  #proof[
    $q = 0$ 时结论自动成立。于是不妨设 $q >= 1$。由于 $j$ 在 $U$ 上是同构，$R^q j_* cal(F)|_U = 0$。因此只需证明：对满足 $dim(ol({x})) = a > d - q$ 的 $x in D$，有 $(R^q j_* cal(F))_(ol(x)) = 0$。

    由 @pbc-etale-bc，这个问题对 $X$ 是局部的。由于 $D$ 是有效 Cartier 除子的支集，不妨设 $j$ 就是开浸入 $Spec(A[f^(-1)]) = U -> X = Spec(A)$，其中 $A$ 是正则整环，$0 != f in A$。现在由 @stalks-of-derived-lowerstar：
    $
    (R^q j_* cal(F))_(ol(x)) &= H^q (Spec(cal(O)_(X,x)^#[sh] otimes_A A[f^(-1)]), cal(F)|_(Spec(cal(O)_(X,x)^#[sh] otimes_A A[f^(-1)]))) \
    &= H^q (Spec(cal(O)_(X,x)^#[sh] [f^(-1)]), cal(F)|_(Spec(cal(O)_(X,x)^#[sh] [f^(-1)])))
    $
    由 @artin-vanishing-engine，存在 $K(t_1, dots.c, t_a)^sep$ 上维数 $<=d-a$ 的有限型正则概形 $Y$（它同时也是 $X$-概形），以及位于 $x in X$ 之上的闭点 $y in Y$，使得作为 $K$-代数有 $cal(O)_(Y,y)^#[sh] cong cal(O)_(X,x)^#[sh]$。

    #lemma[
      设 $k$ 是可分闭域，$Y = Spec(A)$ 是 $k$ 上维数为 $d$ 的有限型仿射正则概形，$y in Y$ 是一点。
      
      则对 $f in frak(p)_y$，$cal(O)_(Y,y)^#[sh] [f^(-1)]$ 是维数 $<=d-1$ 的有限型 $k(s)$-代数的正向极限。
    ]
    #proof[
      取 $Y$ 的一个连通分支，不妨设 $Y$ 是整的。由于问题对 $y$ 是局部的，适当缩小 $Y$，不妨设 $Y = Spec(A), f in frak(p)_y subset A$，其中 $frak(p)_y$ 是 $A$ 中对应于 $y in Spec(A)$ 的素理想。
      
      考虑：
      $
        cal(O)_(Y,y)^#[sh] = dircolim_((U,ol(u)) -> (Y,ol(y)) #[etale] \ U #[affine]) cal(O)_(U,u)
      $
      我们有：
      $
        cal(O)_(Y,y)^#[sh] [f^(-1)] = dircolim_((U,ol(u)) -> (Y,ol(y)) #[etale] \ U=Spec(B) #[affine]) cal(O)_(U,u) [f^(-1)]
      $
      对每个仿射平展邻域 $Spec(B) = U -> Y$，由于 $Y$ 正则，由 @etale-local-properties (1) 知 $U$ 也正则。取 $U$ 连通，不妨设 $U$ 是整的。稍后我们会比较分式域的超越次数。现在对每个这样的 $U$，都有自然态射：
      $
        k[s] -> cal(O)_(U,u), s |-> f in frak(m)_u
      $
      该态射把每个满足 $h(0) in k^times$ 的多项式 $h(s) in k[s]$ 送到 $h(f) in h(0) + f cal(O)_(U,u) subset h(0) + frak(m)_u subset cal(O)_(U,u)^times$，即其像是 $cal(O)_(U,u)$ 中的单位。于是在 $cal(O)_(U,u)$ 中把 $f$ 取逆后，每个非零的 $h(s) in k[s]$ 都满足 $h(f) in cal(O)_(U,u) [f^(-1)]^times$。因此该自然态射诱导出态射：
      $
        k(s) -> cal(O)_(U,u) [f^(-1)]
      $
      这些同态彼此相容，从而给每个 $cal(O)_(U,u) [f^(-1)]$ 赋予 $k(s)$-代数结构。现在：
      $
        Frac(cal(O)_(Y,y)^#[sh] [f^(-1)]) = union.big_((U,ol(u)) -> (Y,ol(y)) #[etale] \ U=Spec(B) #[仿射且整]) Frac(cal(O)_(U,u) [f^(-1)]) = union.big_((U,ol(u)) -> (Y,ol(y)) #[etale] \ U=Spec(B) #[仿射且整]) Frac(B)
      $
      这些分式域都看作 $k(s)$ 的域扩张。对极限中任意整的 $U$，由于 $U$ 在 $Y$ 上拟有限，$dim(U) <= d$。于是
      $
        trd_(k(s)) (Frac(B)) + 1 = trd_k (Frac(B)) <= d
      $
      从而 $trd_(k(s)) (Frac(B)) <= d - 1$。于是
      $
        trd_(k(s)) (Frac(cal(O)_(Y,y)^#[sh] [f^(-1)])) <= d - 1
      $
      现在 $cal(O)_(Y,y)^#[sh] [f^(-1)]$ 是其有限型 $k(s)$-子代数 ${A_lambda}$ 的正向极限。对每个这样的 $A_lambda$，$Frac(A_lambda) subset Frac(cal(O)_(Y,y)^#[sh] [f^(-1)])$ 在 $k(s)$ 上的超越次数 $<= d - 1$，故 $dim(A_lambda) <= d - 1$。至此证毕。
    ]
    现在用刚才证明的引理来证明 $R^q j_* cal(F)$ 的消没。回忆：
    $
      (R^q j_* cal(F))_(ol(x)) &= H^q (Spec(cal(O)_(X,x)^#[sh] [f^(-1)]), cal(F)|_(Spec(cal(O)_(X,x)^#[sh] [f^(-1)]))) \
      &cong H^q (Spec(cal(O)_(Y,y)^#[sh] [f^(-1)]), cal(G))
    $
    其中 $cal(G)$ 是某个挠层，而由于 $y$ 位于 $x$ 之上，$f$ 可以看作 $frak(p)_y$ 中的元素。于是应用该引理，可写成：
    $
      cal(O)_(Y,y)^#[sh] [f^(-1)] = dirlim_lambda A_lambda
    $
    即写成维数 $<= d - a - 1$ 的有限型 $k(t_1, dots.c, t_a)^sep (s)$-代数的正向极限。由于 Artin 消没在维数 $<= d - 1$ 时成立，
    $
      cd(A_lambda) <= d - a - 1 + cd(k(t_1, dots.c, t_a)^sep (s)) <= d - a
    $
    其中最后一个不等号来自 @cohom-dim-of-rings-props (3)。又由 @cohom-dim-of-rings-props (2)，
    $
      cd(cal(O)_(Y,y)^#[sh] [f^(-1)]) <= sup_lambda cd(A_lambda) <= d - a
    $
    因此，只要 $q > d - a$（即 $a = dim(ol({x})) > d - q$），就有 $(R^q j_* cal(F))_(ol(x)) = 0$。
  ]
  现在可以证明 Artin 消没了。设 $X$ 是 $K$ 上维数为 $d$ 的有限型仿射概形。由 Noether 正规化，存在有限态射：
  $
    pi: X -> AA^d_K
  $
  由 @pushforward-by-finite-morphism 有 $H^q (X, cal(F)) = H^q (X, pi_* cal(F))$，故只需证明 $cd(AA^d_K) <= cd(K) + d$。于是不妨设 $X = AA^d_K$。
  
  由极限公式 @limit-formula-for-sheaves，只需处理 $cal(F) in cAb((AA^d_K)_et, ZZ\/n)$ 的情形。取投影 $f: AA^d_K -> AA^(d-1)_(K)$，把它分解为：
  // https://q.uiver.app/#r=typst&q=WzAsMyxbMCwxLCJBQV5kX0siXSxbMiwxLCJBQV4oZC0xKV9LIl0sWzEsMCwiQUFeKGQtMSlfSyB0aW1lc19LIFBQXjFfSyJdLFswLDIsImoiXSxbMiwxLCJvbChmKSJdLFswLDEsImYiLDJdXQ==
  #align(center, diagram({
    node((-1, 0), [$AA^d_K$])
    node((1, 0), [$AA^(d-1)_K$])
    node((0, -1), [$AA^(d-1)_K times_K PP^1_K$])
    edge((-1, 0), (0, -1), [$j$], label-side: left, "->")
    edge((0, -1), (1, 0), [$ol(f)$], label-side: left, "->")
    edge((-1, 0), (1, 0), [$f$], label-side: right, "->")
  }))
  其中 $ol(f)$ 是到第一个坐标的投影。这给出 Leray 谱序列：
  $
    E_2^(p,q) = R^p ol(f)_* (R^q j_* cal(F)) => R^(p+q) f_* cal(F)
  $
  $j$ 是开浸入，其补集是有效 Cartier 除子 $D = AA^(d-1)_K times_K {oo}$。因此当 $q >= 1$ 时，$R^q j_* cal(F)$ 支撑在 $D$ 上。记闭浸入 $i: D -> AA^(d-1)_K times_K PP^1_K$，则
  $
    R^p ol(f)_* (R^q j_* cal(F)) = R^p ol(f)_* i_* (i^(-1) R^q j_* cal(F)) = R^p (ol(f) compose i)_* (i^(-1) R^q j_* cal(F)) = 0
  $
  这对 $p >= 1$ 成立，因为 $ol(f) compose i: D -> AA^(d-1)_K$ 是同构。因此该谱序列的 $E_2$ 页只在 $p = 0$ 或 $q = 0$ 处非零。进一步，由 @relative-grothendieck-vanishing-in-dim-1，由于 $ol(f)$ 紧合且纤维维数为 $1$，当 $p > 2$ 时 $R^p ol(f)_* (R^q j_* cal(F)) = 0$。换言之，这个 Leray 谱序列的 $E_2$ 页只在 $p = 0, q >= 0$ 或 $(p,q) = (1,0), (2,0)$ 处非零。
  
  因此对 $q >= 3$ 有同构：
  $
    ol(f)_* (R^q j_* cal(F)) cong R^q f_* cal(F)
  $

  我们断言：对一切 $q$，$R^q f_* cal(F) in cAb((AA^(d-1)_K)_et, ZZ\/n)$ 都支撑在维数 $<= d - q$ 的闭子集上。

  - $q <= 1$ 时自动成立。

  - $q = 2$ 时，只需证明对泛点 $xi in AA^(d-1)_K$ 有 $(R^2 f_* cal(F))_(ol(xi)) = 0$。事实上，$(tilde(AA^(d-1)_K))_(ol(xi)) = Spec(K(t_1,dots.c,t_(d-1))^sep) = ol(xi)$，因此：
    $
      (R^2 f_* cal(F))_(ol(xi)) &= H^2 (AA^d_K times_(AA^(d-1)_K) ol(xi), cal(F)|_(AA^d_K times_(AA^(d-1)_K) ol(xi))) \
      &= H^2 (AA^1_(ol(xi)), cal(F)|_(AA^1_(ol(xi)))) = 0
    $
    由 @artin-vanishing-in-dim-1 即得。

  - 对 $q >= 3$ 及满足 $a := dim(ol({x})) > d - q$ 的 $x in AA^(d-1)_K$，
    $
      (R^q f_* cal(F))_(ol(x)) &cong (ol(f)_* (R^q j_* cal(F)))_(ol(x)) \
      &cong ol(f)_(ol(x),*) (R^q j_* cal(F)|_(PP^1_(ol(x))))
    $
    其中 $ol(f)_(ol(x)): PP^1_(ol(x)) -> ol(x)$ 是 $ol(f)$ 的一次基变换。由于 $j$ 是维数为 $d$ 的正则代数簇的开浸入，且其补集是有效 Cartier 除子的支集，于是由前面那个关于高阶直像支撑维数的引理，$R^q j_* cal(F)$ 支撑在维数 $<= d - q$ 的闭子集上。对任意位于 $x$ 上方的点 $y in AA^(d-1)_K times_K PP^1_K$，有 $dim(ol({y})) >= dim(ol({x})) > d - q$，故 $(R^q j_* cal(F))_(ol(y)) = 0$。因此 $R^q j_* cal(F)|_(PP^1_x) = 0$，从而
    $
      R^q j_* cal(F)|_(PP^1_(ol(x))) = 0
    $
    所以 $(R^q f_* cal(F))_(ol(x)) = 0$。

  断言既已得证，我们再考虑另一个 Leray 谱序列：
  $
    E_2^(p,q) = H^p (AA^(d-1)_K, R^q f_* cal(F)) => H^(p+q) (AA^d_K, cal(F))
  $
  由于 $R^q f_* cal(F)$ 支撑在维数 $<= d - q$ 的闭子集上，由 @supp-of-torsion-sheaf-dim，可写成 $R^q f_* cal(F) = dirlim_lambda cal(G)_lambda$，其中每个 $cal(G)_lambda$ 都是挠层，支撑在 $AA^(d-1)_K$ 的闭子概形 $Z_lambda$ 上，而后者的维数 $<=d- max(1,q)$。于是
  $
    H^p (AA^(d-1)_K, R^q f_* cal(F)) = dirlim_lambda H^p (AA^(d-1)_K, cal(G)_lambda) = dirlim_lambda H^p (Z_lambda, cal(G)_lambda|_(Z_lambda)) = 0
  $
  只要 $p > cd(K) + d - q$ 就有上式，因为上述闭子概形的维数都满足 $dim(Z_lambda) <= d - max(1, q)$，而由归纳假设，Artin 消没在维数 $<= d - 1$ 时成立。换言之，Leray 谱序列 $E_2^(p,q) = H^p (AA^(d-1)_K, R^q f_* cal(F)) => H^(p+q) (AA^d_K, cal(F))$ 的 $E_2$ 页在 $p + q > cd(K) + d$ 时全为零。因此
  $
    H^m (AA^d_K, cal(F)) = 0, forall m > cd(K) + d
  $
  故 $cd(AA^d_K) <= cd(K) + d$，证毕。
]

Artin 消没证完之后，Grothendieck 消没只是一个形式推论。

#theorem(name: <grothendieck-vanishing>)[
  (Grothendieck 消没) 设 $K$ 是域，$X$ 是 $K$ 上维数为 $d$ 的任意有限型概形。则：
  $
    cd(X) <= cd(K) + 2d
  $
]
#proof[
  考虑从平展层到 Zariski 层的遗忘函子 $epsilon: cAb(X_et) -> cAb(X_#[Zar])$。取 $cal(F) in cAb(X_et)$ 为挠层。如同 @etale-cohom-of-qcoh-sheaf 的证明，存在谱序列：
  $
    E_2^(p,q) = H^p_#[Zar] (X, R^q epsilon (cal(F))) => H^(p+q)_et (X, cal(F))
  $
  其中 $R^q epsilon (cal(F))$ 是预层 $U |-> H^q_et (U, cal(F)|_U)$ 的 Zariski 层化。于是对任意 $x in X$，
  $
    (R^q epsilon (cal(F)))_x = dirlim_(x in U subset X \ U #[仿射开]) H^q_et (U, cal(F)|_U) = 0
  $
  只要 $q > cd(K) + d$ 就有上式，因为每个 $U$ 都是 $K$ 上维数为 $d$ 的有限型仿射概形，从而可以应用 Artin 消没 @artin-vanishing。换言之，当 $q > cd(K) + d$ 时 $R^q epsilon (cal(F)) = 0$。进一步，当 $p > d$ 时 $H^p_#[Zar] (X, R^q epsilon (cal(F))) = 0$，因为 Zariski 上同调在维数以上消没。

  因此上述谱序列只在 $0 <= p <= d, 0 <= q <= cd(K) + d$ 处非零。故
  $
    H^(m)_et (X, cal(F)) = 0, forall m > cd(K) + 2d
  $
  即 $cd(X) <= cd(K) + 2d$。
]

#corollary[
  设 $X$ 是可分闭域 $k$ 上维数为 $d$ 的有限型概形：
  
  + $cd(X) <= 2d$。也就是说，对任意挠层 $cal(F) in cAb(X_et)$，#h(1fr)
    $
      H^q (X, cal(F)) = 0, forall q > 2d
    $

  + 若再假定 $X$ 仿射，则 $cd(X) <= d$。也就是说，对任意挠层 $cal(F) in cAb(X_et)$，
    $
      H^q (X, cal(F)) = 0, forall q > d
    $
]
#proof[
  这正是把 Artin 消没（@artin-vanishing）与 Grothendieck 消没（@grothendieck-vanishing）应用于基域可分闭的情形。
]

最后，我们证明 Grothendieck 消没与 Artin 消没的相对版本。 
#proposition(name: <relative-artin-grothendieck-vanishing>)[
  + (相对 Artin 消没)
  
    若 $f: X -> Y$ 是有限型 $K$-概形之间的仿射态射，$cal(F) in cAb(X_et)$ 是支撑在维数 $<=m$ 的闭子集上的挠层，则 $R^q f_* cal(F)$ 支撑在维数 $<=m-q$ 的闭子集上。

    特别地，对任意挠层 $cal(F) in cAb(X_et)$，当 $q > dim(X)$ 时 $R^q f_* cal(F) = 0$；

  + (相对 Grothendieck 消没)

    若 $f: X -> Y$ 是有限型 $K$-概形之间的任意态射，$cal(F) in cAb(X_et)$ 是支撑在维数 $<=m$ 的闭子集上的挠层，则 $R^q f_* cal(F)$ 支撑在维数 $<=m - ceil(q\/2)$ 的闭子集上。

    特别地，对任意挠层 $cal(F) in cAb(X_et)$，当 $q > 2dim(X)$ 时 $R^q f_* cal(F) = 0$；

  + (逐纤维 Grothendieck 消没)

    若 $f: X -> Y$ 是概形之间的紧合态射，其纤维的维数 $<=d$，则对任意挠层 $cal(F) in cAb(X_et)$，当 $q > 2d$ 时 $R^q f_* cal(F) = 0$。
]
#proof[
  在 (1)(2) 中，若 $cal(F)$ 支撑在维数 $<=m$ 的闭子集上，则由 @supp-of-torsion-sheaf-dim，$cal(F) = dirlim_lambda cal(F)_lambda$，其中每个 $cal(F)_lambda$ 都支撑在 $X$ 的某个维数 $<=m$ 的闭子概形上。由 @relative-limit-formula-for-sheaves，$R^q f_* cal(F) = dirlim_lambda R^q f_* cal(F)_lambda$，而茎与正向极限交换，所以只需对每个 $cal(F)_lambda$ 证明所需消没。把 $cal(F)$ 换成 $cal(F)_lambda$，便可假设 $cal(F)$ 支撑在某个维数 $<=m$ 的闭子概形 $Z subset X$ 上。现在：
  $
    R^q f_* cal(F) = R^q f_* (i_* i^(-1) cal(F)) = R^q (f compose i)_* (i^(-1) cal(F))
  $
  于是把 $f$ 换成 $f compose i$、把 $X$ 换成 $Z$，便可假设 $m = dim(X)$，并去掉关于 $cal(F)$ 支集的条件。

  设 $y in Y$ 满足 $dim(ol({y})) = a$，并设 $dim(Y) = d$。由 @artin-vanishing-engine 的证明，存在仿射态射 $Y -> AA^a_K$，把 $y$ 送到泛点 $eta in AA^a_K$。沿几何点 $ol(eta) = Spec(K(t_1, dots.c, t_a)^sep)$ 作基变换，得到拉回图表：
  // https://q.uiver.app/#r=typst&q=WzAsNixbMSwxLCJZIl0sWzEsMCwiWSciXSxbMCwxLCJYIl0sWzAsMCwiWCciXSxbMiwxLCJBQV5hX0siXSxbMiwwLCJvbChldGEpIl0sWzMsMSwiZiciXSxbMSwwLCJnIl0sWzEsNV0sWzAsNF0sWzUsNF0sWzIsMCwiZiIsMl0sWzMsMiwiZyciLDJdXQ==
  #align(center, diagram({
    node((0, 0), [$Y$])
    node((0, -1), [$Y'$])
    node((0.3, -0.7), $cart$)
    node((-1, 0), [$X$])
    node((-1, -1), [$X'$])
    node((-0.7, -0.7), $cart$)
    node((1, 0), [$AA^a_K$])
    node((1, -1), [$ol(eta)$])
    edge((-1, -1), (0, -1), [$f'$], label-side: left, "->")
    edge((0, -1), (0, 0), [$g$], label-side: left, "->")
    edge((0, -1), (1, -1), "->")
    edge((0, 0), (1, 0), "->")
    edge((1, -1), (1, 0), "->")
    edge((-1, 0), (0, 0), [$f$], label-side: right, "->")
    edge((-1, -1), (-1, 0), [$g'$], label-side: right, "->")
  }))
  以及闭点 $y' in Y'$，使得 $g(y') = y$，并且局部态射 $cal(O)_(Y,y) -> cal(O)_(Y',y')$ 诱导出同构：
  $
    cal(O)_(Y,y)^#[sh] cong cal(O)_(Y',y')^#[sh]
  $
  于是：
  $
    (R^q f_* cal(F))_(ol(y)) &cong H^q (X times_Y Spec(cal(O)_(Y,y)^#[sh]), cal(F)|_(X times_Y Spec(cal(O)_(Y,y)^#[sh]))) \
    &cong H^q (X' times_(Y') Spec(cal(O)_(Y,y)^#[sh]), cal(F)|_(X' times_(Y') Spec(cal(O)_(Y,y)^#[sh]))) \
    &cong H^q (X' times_(Y') Spec(cal(O)_(Y',y')^#[sh]), cal(F)|_(X' times_(Y') Spec(cal(O)_(Y',y')^#[sh]))) \
    &cong (R^q f'_* (cal(F)|_(X')))_(ol(y'))
  $
  现在 $f': X' -> Y'$ 是有限型 $K(t_1,dots.c,t_a)^sep$-概形之间的态射，若 $f$ 仿射则它也是仿射的。进一步，对任意 $x' in X'$，$x'$ 位于某个 $x in X$ 之上，而后者位于泛点 $eta in AA^a_K$ 之上。因此
  $
    cal(O)_(X_eta,x) = cal(O)_(X,x)
  $
  从而：
  $
    dim(ol({x})_(X_eta)) &= trd_(K(t_1,dots.c,t_a)) (k_(X_eta) (x)) = trd_(K(t_1,dots.c,t_a)) (k_X (x)) = trd_K (k_X (x)) - a = dim(ol({x})_X) - a \
    &<= m - a
  $
  故 $dim(X_eta) <= m - a$。$X' = X_(ol(eta))$ 作为 $X_eta$ 的基域扩张 $X_eta times_eta ol(eta)$，因此 $dim(X') <= m - a$。于是可以使用同构：
  $
    (R^q f_* cal(F))_(ol(y)) cong (R^q f'_* (cal(F)|_(X')))_(ol(y'))
  $

  利用上面得到的同构，并注意到 $a > m - q$（相应地，$a > m - ceil(q\/2)$）蕴涵 $0 > m - a - q >= dim(X') - q$（相应地，$0 > m - a - ceil(q\/2) >= dim(X') - ceil(q\/2)$）。于是把 $f: X -> Y$ 换成 $f': X' -> Y'$、把 $y in Y$ 换成 $y' in Y'$，便可假设 $a = 0$，即 $y in Y$ 是闭点。进一步，$X', Y'$ 是 $K(t_1, dots.c, t_a)^sep$ 上的有限型概形，而这是一个可分闭域，故不妨假设 $K$ 可分闭。
  
  换言之，在 (1)(2) 中，只需对可分闭的 $K$ 证明最终的消没陈述，即当 $q > m$（相应地，$q > 2m$）时的消没。事实上，由 @derived-lower-star-first-props (3)，
  $
    R^q f_* cal(F) = (V |-> H^q (X times_Y V, cal(F)))^\#
  $
  对任意仿射 $V in Et_Y$，$V$ 在 $Y$ 上有限型，从而在 $K$ 上有限型。所以 $X times_Y V$ 在 $K$ 上有限型。由于 $X times_Y V -> X$ 平展，因而拟有限，$dim(X times_Y V) <= dim(X) = m$。进一步，若 $V$ 仿射且 $f$ 仿射，则 $X times_Y V$ 仿射。因此
  $
    H^q (X times_Y V, cal(F)) = 0
  $
  当 $q > 2m$ 时成立；若 $f$ 仿射，则当 $q > m$ 时成立。现在，对每个拟紧拟分离的 $V in Et_Y$，$V$ 的每个平展覆盖都可被一个由有限多个仿射概形 $V_i in Et_V$ 组成的覆盖加细。因此 $caron(H)^0 (V, -)$ 完全可以只用这些仿射 $V_i in Et_Y$ 来计算，于是上述结果给出：
  $
    R^q f_* cal(F) (V) = 0
  $
  对所有拟紧拟分离的 $V in Et_Y$，当 $q > 2m$ 时上式成立；若 $f$ 仿射，则当 $q > m$ 时成立。由于 $Et_Y$ 的每个对象都有由拟紧拟分离对象组成的覆盖，故当 $q > 2m$ 时 $R^q f_* cal(F) = 0$；若 $f$ 仿射，则当 $q > m$ 时它为零。

  (3) 对 $q > 2d$ 以及 $y in Y$ 上方的几何点 $ol(y) = Spec(k(y)^sep)$，由紧合基变换，
  $
    (R^q f_* cal(F))_(ol(y)) = H^q (X_(ol(y)), cal(F)|_(X_(ol(y))))
  $
  其中 $cal(F)|_(X_(ol(y)))$ 是 $X_(ol(y))$ 上的挠层，而后者是可分闭域 $k(y)^sep$ 上维数 $<=d$ 的有限型概形。由绝对 Grothendieck 消没，当 $q>2d$ 时该上同调群消没，从而当 $q>2d$ 时 $R^q f_* cal(F) = 0$。
]
