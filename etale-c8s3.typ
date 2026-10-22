// audit-exception: 公式 $E subset AA^1_X$ 的 #[...] 文字块内嵌 $x'$、$x in X$、$AA^1_(k(x))$ 等行内公式，审计按相邻美元符号配对会把块内说明文字（$lies above$、$and is a closed point in the fiber$）切成伪公式段；只译块内文字说明，块内外公式逐段核对未变。
#import "void-import.typ": *

== 光滑基变换

本节的核心论证来自 @cite-deligne-arcata。

本节把前几节关于局部零调性所做的归约与讨论汇总起来，用以证明光滑基变换定理。本节的主定理是： 

- 光滑态射都是泛局部零调的。 

我们先做若干归约。 

#notation[
  设 $(A, frak(m))$ 是严格 Hensel 局部环。记号 $A{T}$ 表示如下局部环： 
  $
    A{T} := A[T]_((frak(m),T))^#[h] = A[T]_((frak(m),T))^#[sh]
  $
]

#lemma(name: <loc-acyc-of-smooth-maps-reductions>)[
  在如下条件下，光滑态射都是泛局部零调的： 

  - 对任意 $A$，假设它是某个正规有限型 $ZZ$-代数在某个素理想处的严格 Hensel 化，且 $K = Frac(A)$。则对任意自然数 $n in A^times$，有#h(1fr)
    $
      H^0 (Spec(ol(K) otimes_A A{T}), ul(ZZ\/n)) = ZZ\/n \
      H^1 (Spec(ol(K) otimes_A A{T}), ul(ZZ\/n)) = 0
    $ 
]
#proof[
  局部零调性在源与目标上都是平展局部的。因此只需证明每个 $AA^d_S -> S$ 都局部零调：任意光滑态射 $X -> S$ 都在 Zariski 局部地分解为 $X ->^j AA^d_S -> S$，其中 $j$ 平展。 

  于是只需证明每个 $AA^d_(ZZ[n^(-1)]) -> Spec(ZZ[n^(-1)])$ 都关于 $ul(ZZ\/n)$ 泛局部零调。由 @loc-acyc-and-base-change，只需证明： 

  - 对每个 $A$，假设它是某个整的有限型 $ZZ[n^(-1)]$-代数 $A_0$ 在其分式域代数闭包中的正规化；则 $AA^d_A -> Spec(A)$ 关于 $ul(ZZ\/n)$ 局部零调。 

  由 @loc-acyc-and-limits-of-qfinite，若 $AA^d_(A_0) -> Spec(A_0)$ 局部零调，则局部零调性可沿整基变换 $Spec(A) -> Spec(A_0)$ 提升，从而 $AA^d_A -> Spec(A)$ 局部零调。而 $A_0$ 在 $ZZ$ 上有限型，特别地是 Noether 的，故可引用 @loc-acyc-compose。于是只需证明： 

  - 对每个整的有限型 $ZZ[n^(-1)]$-代数 $A_0$，$AA^1_(A_0) -> Spec(A_0)$ 关于 $ul(ZZ\/n)$ 局部零调。 

  为此只需证明 $AA^1_(ZZ[n^(-1)]) -> Spec(ZZ[n^(-1)])$ 关于 $ul(ZZ\/n)$ 泛局部零调。再次引用 @loc-acyc-and-base-change，只需证明： 

  - 对每个 $X = Spec(A)$，假设它是某个仿射、整、有限型 $ZZ[n^(-1)]$-概形 $Spec(A_0)$ 在其函数域 $K$ 的代数闭包中的正规化，泛点为 $xi$；此时 
    $
      R Gamma(F_(ol(x'),xi), ul(ZZ\/n)) cong ZZ\/n
    $
    其中 ${ol(x')}$ 是 $AA^1_X$ 的某个极稠密子集上方的一族几何点。 

  由 @integral-normal-affine-with-ac-func-field，$X$ 的局部环都是严格 Hensel 的，且其函数域代数闭。考虑如下子集： 
  $
    E = {x' in AA^1_X : #[$x'$ 位于 $x in X$ 上方，且是纤维 $AA^1_(k(x))$ 中的闭点]}
  $
  每个 $AA^1_(k(x))$ 的闭点集都是极稠密的。因此 $AA^1_X$ 的每个非空局部闭子集都必与某个纤维 $AA^1_(k(x))$ 交于非空局部闭子集，从而含有闭点。这说明 $E subset AA^1_X$ 是极稠密的。于是我们取 ${ol(x')}$ 为 $E$ 中各点上方的代数几何点所成的一族。 
  
  设 $x in X = Spec(A)$ 对应素理想 $frak(p)$，而 $x$ 上方的 $x' in E$ 由坐标 $[u] in k(x) = A_(frak(p))\/frak(p) A_(frak(p))$ 代表。$[u]$ 由某个元素 $u in A_(frak(p))$ 代表，从而对某个 $f in A - frak(p)$，它由 $u in A_f$ 代表。现在 $F_(ol(x'),xi)$ 对源与目标的同时缩小不敏感。于是可沿 $Spec(A_f) -> Spec(A)$ 作基变换，不妨设 $u in A$。此时 $x'$ 由素理想 $(frak(p), T - u) subset A[T]$ 代表。再作坐标变换 $A[T] -> A[T], T |-> T + u$，便可假设 $x' in AA^1_A = Spec(A[T])$ 由素理想 $(frak(p), T)$ 代表。于是 
  $
    F_(ol(x'),xi) = Spec(K otimes_(A_(frak(p))) A_(frak(p)) {T})
  $
  从而只需证明： 
  $
    R Gamma(Spec(K otimes_(A_(frak(p))) A_(frak(p)) {T}), ul(ZZ\/n)) = ZZ\/n
  $
  于是剩下要证的是： 

  - 若 $A$ 是严格 Hensel 正规局部整环，其函数域 $K$ 代数闭，且它是某个整的有限型 $ZZ$-代数在其分式域代数闭包中的正规化的一个局部环，$n in A^times$，则： 
    $
      R Gamma(Spec(K otimes_A A{T}), ul(ZZ\/n)) = ZZ\/n
    $

  我们再做一次极限论证。 
  
  - 把 $A$ 写成其有限型 $ZZ[n^(-1)]$-代数的正向极限 $A = dirlim_lambda A_lambda^((1))$。 
  
  - 每个 $A_lambda^((1))$ 都是整的，故可取它的正规化 $A_lambda^((2))$。由于 $A_lambda^((1))$ 在 $ZZ$ 上有限型，$A_lambda^((2))$ 在它上面有限，从而仍在 $ZZ$ 上有限型。由于 $A$ 正规，$A_lambda^((2))$ 是 $A$ 的含 $A_lambda^((1))$ 的子代数。于是有： 
    $
      A = dirlim_lambda A_lambda^((2))
    $

  - 设 $frak(q)_lambda in Spec(A_lambda^((2)))$ 是 $frak(m)_A$ 的像，并令 $A_lambda^((3)) = (A_lambda^((2)))_(frak(q)_lambda)$。$A_lambda^((2)) - frak(q)_lambda$ 中每个元素都属于 $A - frak(m) = A^times$，故每个 $(A_lambda^((2)))_(frak(q)_lambda)$ 都是 $A$ 的子代数。于是有： 
    $
      A = dirlim_lambda A_lambda^((3))
    $

  - 最后取 $A_lambda = (A_lambda^((3)))^#[sh]$。由于严格 Hensel 化与正向极限交换（@henselization-and-directed-limits）， 
    $
      A = A^#[sh] = dirlim_lambda (A_lambda^((3)))^#[sh] = dirlim_lambda A_lambda
    $
    其中每个 $A_lambda$ 都是某个整、正规、有限型 $ZZ[n^(-1)]$-代数在某个素理想处的严格 Hensel 化。 
    
  - 由 @inverting-nonzeros-in-henselization (2)，每个 $A_lambda -> A$ 都是单射。于是 $A$ 是其子代数 $A_lambda$ 的并，且： 
    $
      K = Frac(A) = dirlim_lambda Frac(A_lambda)
    $
    现在 $K = Frac(A)$ 是某个整的有限型 $ZZ$-代数的分式域的代数闭包，故它在 $QQ$ 或 $FF_p$ 上的超越次数有限。取 $K$ 在 $QQ$ 或 $FF_p$ 上的一组超越基 $u_1, dots.c, u_t in K$，则存在有限阶段 $lambda_0$，使得 $u_1, dots.c, u_t in Frac(A_lambda)$。把正向系统截断到 $lambda >= lambda_0$，便可假设 $K\/Frac(A_lambda)$ 是代数的。又因 $K$ 代数闭，故 $K = ol(Frac(A_lambda))$。 

  因此， 
  $
    Frac(A) otimes_A A{T} &= Frac(A) otimes_(dirlim_lambda A_lambda) (dirlim_lambda A_lambda {T}) = dirlim_lambda Frac(A) otimes_(A_lambda) A_lambda {T} \
    &= dirlim_lambda ol(Frac(A_lambda)) otimes_(A_lambda) A_lambda {T}
  $
  从而： 
  $
    H^q (Spec(K otimes_A A{T}), ul(ZZ\/n)) = dirlim_lambda H^q (Spec(ol(Frac(A_lambda)) otimes_(A_lambda) A_lambda {T}), ul(ZZ\/n))
  $
  于是，只要能证明对每一项都有 $R Gamma(Spec(ol(Frac(A_lambda)) otimes_(A_lambda) A_lambda {T}), ul(ZZ\/n)) = ZZ\/n$，就有 $R Gamma(Frac(A) otimes_A A{T}, ul(ZZ\/n)) = ZZ\/n$，从而完成这一步归约。因此只需证明： 

  - 对 $A$ 为某个有限型 $ZZ[n^(-1)]$-代数在某个素理想处的严格 Hensel 化、且 $K = Frac(A)$ 的情形，#h(1fr)
    $
      H^q (Spec(ol(K) otimes_A A{T}), ul(ZZ\/n)) = cases(
        ZZ\/n &\, q = 0, 
        0 &\, q >= 1
      )
    $

  // 现在 $A{T}$ 是正规局部整环，故作为它的一个局部化，$K otimes_A A{T}$ 是整的。于是 $Spec(K otimes_A A{T})$ 整，从而连通，并且： 
  // $
  //   H^0 (Spec(ol(K) otimes_A A{T}), ul(ZZ\/n)) = ZZ\/n
  // $ 
  // 现在 $q = 1$ 的情形是假设，故只需处理 $q = 2$ 的情形。然而， 
  情形 $q = 0,1$ 正是引理中的假设。对 $q >= 2$，$A{T}$ 是平展 $A[T]$-代数的正向极限。于是 $ol(K) otimes_A A{T}$ 是平展 $ol(K)[T]$-代数 $B_lambda$ 的正向极限。因此： 
  $
    H^q (Spec(ol(K) otimes_A A{T}), ul(ZZ\/n)) = dirlim_lambda H^q (Spec(B_lambda), ul(ZZ\/n))
  $
  每个 $B_lambda$ 都是 $ol(K)$ 上维数 $<=1$ 的有限型代数。于是由 Artin 消没（@artin-vanishing），右端极限中每一项在 $q >= 2$ 时都消没。故 $H^q (Spec(ol(K) otimes_A A{T}), ul(ZZ\/n)) = 0$。证毕。 
]

下面开始计算所需的 $H^0$ 与 $H^1$，这归结为连通分支与有限平展覆叠。 

#lemma(name: <a-braces-t-and-normalization-in-fin-sep-ext>)[
  设 $A$ 是 Noether 的严格 Hensel 正规局部整环，$K = Frac(A)$。则对任意有限可分扩张 $L\/K$，$A$ 在 $L$ 中的正规化 $B$ 在 $A$ 上有限，且仍是 Noether 的严格 Hensel 正规局部整环。此外， 
  $
    B otimes_A A{T} cong B{T}
  $
]
#proof[
  $B$ 在 $A$ 上有限，这来自一个初等事实：任何正规整环在其分式域的有限可分扩张中的正规化仍然有限（#cite-stacks("032L")[Lemma 10.161.8]）。按定义 $B$ 正规；又因它在 Noether 环 $A$ 上有限，故是 Noether 的。 
  
  由于 $B$ 在 $A$ 上有限，由 @finite-over-henselian-is-henselian，$B$ 是若干严格 Hensel 局部 $A$-代数的乘积。然而 $B$ 是整的，故它自身必须是严格 Hensel 局部环。 

  最后，由 @strict-henselizations-tensors-and-qfinites，由于 $B$ 在 $A$ 上有限且 $B[T] = B otimes_A A[T]$， 
  $
    B{T} = B[T]_((frak(m)_B,T))^#[sh] = B^#[sh] otimes_(A^#[sh]) A[T]_((frak(m)_A,T))^#[sh] = B otimes_A A{T}
  $
]

现在可以处理 $H^0$ 的情形了。 

#proposition(name: <sbc-core-h0>)[
  设 $A$ 是 Noether 的严格 Hensel 正规局部整环，$K = Frac(A)$。则 $Spec(ol(K) otimes_A A{T})$ 连通，即： 
  $
    H^0 (Spec(ol(K) otimes_A A{T}), ul(ZZ\/n)) = ZZ\/n
  $
]
#proof[
  对每个有限可分扩张 $L\/K$，设 $B$ 是 $A$ 在 $L$ 中的正规化。由 @a-braces-t-and-normalization-in-fin-sep-ext，$B$ 是 Noether 的严格 Hensel 正规整环，且： 
  $
    L otimes_A A{T} = L otimes_B B otimes_A A{T} cong L otimes_B B{T}
  $
  现在 $B{T}$ 是正规局部整环。于是 $L otimes_B B{T}$ 就是把 $B{T}$ 中 $B - {0}$ 的元素取逆所得的环，它仍是整的，从而连通。因此： 
  $
    H^0 (Spec(K^sep otimes_A A{T}), ul(ZZ\/n)) &= dirlim_(L\/K #[finite separable]) H^0 (Spec(L otimes_A A{T}), ul(ZZ\/n)) \
    &= dirlim_(L\/K #[finite separable]) ZZ\/n = ZZ\/n
  $
  由拓扑不变性，可把 $K^sep$ 换成 $ol(K)$，从而完成证明。 
]

$H^1$ 的情形要复杂得多，需要所谓 Abhyankar 引理的一个特例。核心代数工具是如下引理： 

#lemma(name: <normal-hartogs>)[
  （正规 Hartogs；@cite-matsumura-ca[Theorem 38]）设 $A$ 是正规 Noether 整环。则在 $Frac(A)$ 中，
  $
    A = inter.big_(frak(p) in Spec(A) \ "ht"(frak(p)) = 1) A_(frak(p))
  $
]

下面我们发展一些代数工具，把泛纤维上的有限平展覆叠铺开到余维度 $>=2$ 的开子集上。 

#lemma(name: <zariski-nagata-purity-in-dim-2>)[
  （$2$ 维的 Zariski–Nagata 纯性）设 $(A, frak(m))$ 是维数为 $2$ 的正则局部整环，并给定包含 $A arrow.hook B$，其中 $B$ 是正规的有限 $A$-代数。 
  
  若 $B$ 在去心谱 $Spec(A) - {frak(m)}$ 上平展，则它在 $A$ 上平展。 
]
#proof[
  由于 $A subset B$、$A$ 正规且 $B$ 在 $A$ 上有限，$A -> B$ 满足下行（见 @cite-atiyah-macdonald[Theorem 5.16]）。第一步是证明 $B$ 在 $A$ 上有限自由。

  - 我们断言：若 $z in Frac(B)$ 且 $frak(m) z subset B$，则 $z in B$。 
  
    事实上，对任意高度 $1$ 的素理想 $frak(q) in Spec(B)$，由下行，$frak(p) = frak(q) inter A$ 的高度 $<=1$。于是 $frak(p) != frak(m)$，可取 $a in frak(m) - frak(p)$。此时 $a z in B$ 且 $a in B_(frak(q))^times$，故 $z in B_(frak(q))$。因此， 
    $
      z in inter.big_(frak(q) in Spec(B) \ "ht"(frak(q)) = 1) B_(frak(q)) = B
    $
    由 @normal-hartogs。 

  取一组正则参数系 $frak(m) = (x, y)$。现在： 

  - 在 $B\/x B$ 上乘以 $y$ 是单射。事实上，假设 $b_1, b_2 in B$ 满足 $b_1 y = b_2 x$。则：#h(1fr)
    $
      z = b_1/x = b_2/y in Frac(B)
    $
    有 $x z, y z in B$，故 $frak(m) z subset B$。由上一项，$z in B$。于是 $x divides b_1$，从而 $[b_1] = 0 in B\/x B$。 

  现在 $A\/x A$ 是维数为 $1$ 的正则局部环，从而是以 $[y]$ 为一致化元的 DVR。$B\/x B$ 是有限 $A\/x A$-模，且在其上乘以 $[y]$ 是单射。于是 $B\/x B$ 是 $A\/x A$ 上的有限自由模。 

  取一组基 $B\/x B cong (A\/x A)^(oplus r)$，并把它任意提升为一个映射 $phi: A^(oplus r) -> B$。则 $coker(phi) = x coker(phi)$，故由 Nakayama 引理，$phi$ 是满射。又对任意 $k in ker(phi)$，$phi(k) = 0$，故 $k in (x A)^(oplus r)$。写 $k = x k_0$，则 $0 = phi(k) = x phi(k_0)$。$B$ 是整环且 $x != 0$，故 $phi(k_0) = 0$，即 $k_0 in ker(phi)$。于是 $ker(phi) = x ker(phi)$，再由 Nakayama 引理，$phi$ 是单射。这样我们就构造出 $A$-模同构 $B cong A^(oplus r)$。 

  为继续推进，需要如下引理： 
  #lemma[
    设 $A$ 是整环，$B$ 是有限自由 $A$-代数，基为 $e_1, dots.c, e_r in B$。则 $B\/A$ 有限平展当且仅当判别式： 
    $
      Delta = det mat(Tr_(B\/A) (e_i e_j))_(1<=i,j<=r) in A
    $
    是 $A^times$ 中的元素。 
  ]
  #proof[
    注意 $Delta in A^times$ 当且仅当迹配对 $B times B -> A, (u, v) |-> Tr_(B\/A) (u v)$ 是完美配对。 

    ($==>$) 对任意极大理想 $frak(m) in Spec(A)$，纤维 $B\/frak(m) B$ 在 $k(frak(m)) = A\/frak(m)$ 上平展，从而是 $k(frak(m))$ 的若干有限可分扩张的有限乘积。有限可分域扩张的迹配对是完美配对，故 $B\/frak(m) B$ 在 $k(frak(m))$ 上的迹配对也是完美配对。这说明 $Delta$ 在每个 $k(frak(m))$ 中都约化为单位。由于 $Delta$ 不含于任何极大理想，它是单位。 

    ($<==$) 假设迹配对是完美配对。取 $B$ 的一组基 $u_1, dots.c, u_r in B$ 及对偶基 $v_1, dots.c, v_r in B$，并令 $e = sum_(i=1)^r u_i otimes v_i in B otimes_A B$。元素 $e$ 具有如下性质： 
    $
      (b otimes 1)e &= sum_(i=1)^n b u_i otimes v_i = sum_(i=1)^n sum_(j=1)^n Tr_(B\/A) (b u_i v_j) u_j otimes v_i \
      &= sum_(i=1)^n sum_(j=1)^n u_i otimes Tr_(B\/A) (b u_j v_i) v_j = sum_(i=1)^n u_i otimes b v_i = (1 otimes b)e
    $
    取乘法映射 $mu: B otimes_A B -> B$。则对每个元素 $t in B otimes_A B$， 
    $
      t e = (mu(t) otimes 1) e = (1 otimes mu(t)) e
    $

    另一方面，对 $b in B$， 
    $
      Tr_(B\/A) (b mu(e)) = sum_(i=1)^n Tr_(B\/A) (b u_i v_i) = Tr_(B\/A) (b)
    $
    于是由迹配对的完美性，$mu(e) = 1$。现在令 $I = ker(mu)$，取 $z in I$。则： 
    $
      z e = (mu(z) otimes 1) e = 0
    $
    从而 $z = z(1-e)$。然而 $mu(e) = 1$，故 $1-e in I^2$。因此 $z = z(1-e) = I^2$，从而 $I = I^2$。于是， 
    $
      Omega_(B\/A) cong I\/I^2 = 0
    $
    故 $B$ 在 $A$ 上非分歧。又因 $B$ 在 $A$ 上自由，它平坦，从而平展。 
  ]

  由于 $B$ 是有限自由 $A$-代数，可以作出迹映射 $Tr_(B\/A): B -> A$。取 $B$ 的一组 $A$-基 $e_1, dots.c, e_r$，作出判别式： 
  $
    Delta = det mat(Tr_(B\/A) (e_i e_j))_(1<=i,j<=r) in A
  $
  由于 $Spec(B) -> Spec(A)$ 在去心谱 $Spec(A) - {frak(m)}$ 上平展，对任意高度 1 的素理想 $frak(p) in Spec(A)$，$Spec(B_(frak(p))) -> Spec(A_(frak(p)))$ 都平展。于是由上一引理， 
  $
    Delta in A_(frak(p))^times
  $
  因此， 
  $
    Delta = inter.big_(frak(p) in Spec(A) \ "ht"(frak(p)) = 1) A_(frak(p))^times = A^times
  $
  这里用了 @normal-hartogs。于是由上一引理，$B$ 是平展 $A$-代数。 
]

#lemma(name: <abhyankar-lemma-special-case>)[
  （Abhyankar 引理的特例）设 $R$ 是以 $pi.alt$ 为一致化元的 DVR，分式域为 $K$；设 $X$ 是相对维数为 $1$ 的仿射光滑 $R$-概形。令 $eta in S = Spec(R)$ 为泛点。 

  设 $n$ 是素数且 $n in R^times$，令 $R' = R[pi.alt^(1\/n)], S' = Spec(R')$。对象上的撇号表示它从 $R$ 到 $R'$ 的基变换。令 $eta' in S'$ 为泛点。 

  假设 $Z_eta -> X_eta$ 是平展 $ZZ\/n$-主丛。则基变换 $Z'_(eta') -> X'_(eta')$ 延拓为有限平展覆叠 $Z' -> X'$。 
]
#proof[
  /*We may assume that $X$ is affine. Indeed, pick an affine cover ${X_i}$ of $X$, and base change to an affine cover ${X'_i}$ of $X$. Then if the statement holds in the affine case, each $Z'_(i,eta') -> X'_(i,eta') $ must lift to a finite etale covering $pi_i: Z'_i -> X'_i$. To glue these lifts, we need a rigidity statement for finite etales. 

  #lemma[
    If $X$ is a normal noetherian scheme and $U subset X$ is dense open, then for any $Y, Z in FEt_X$ with base changes $Y_U, Z_U in FEt_U$, 
    $
      Hom_X (Y, Z) cong Hom_U (Y_U, Z_U)
    $
  ]
  #proof[
    By replacing $X$ with its connected components, we may assume that $X$ is integral normal. Now put $K = K(X) $, and by @p1et-of-normal-scheme, it suffices to show that for discrete finite $Gal(K^"ur" (X)\/K) $-sets $S, T$, 
    $
      Hom_(Gal(K^"ur" (X)\/K)) (S, T) = Hom_(Gal(K^"ur" (U)\/K)) (S, T)
    $
    Indeed, $Gal(K^"ur" (X)\/K) $ is a quotient of $Gal(K^"ur" (U)\/K) $, so the Hom sets are equal. 
  ]

  Now the finite etales $pi_i: Z'_i -> X'_i$ and $pi_j: Z'_j -> X'_j$ are both restrictions of $Z'_(eta') -> X'_(eta') $ upon base changing to the generic fiber $X'_eta$. Now: 

  - $X'$ is smooth over $S'$ the spectrum of a DVR, hence regular. Its connected components are thus integral regular schemes. Each of them must dominate $S'$ by openness of flat morphisms. Thus the generic point of every irreducible component of $X'$ lies above the generic point $eta' in S'$, and so $X'_(eta') subset X'$ is a dense open. 

    Consequently, for any open subset $U' subset X'$, $U'_(eta') subset U'$ is a dense open. 

  Hence, by the previous rigidity lemma, $pi_i$ and $pi_j$ agrees over $X'_(i,j) $ since they agree over $X'_(i,j,eta') $. Hence, we may glue the $pi_i$'s to a finite etale covering $pi: Z' -> X'$. */
  由于 $X$ 在 $R$ 上光滑，它正则，故 $X$ 的连通分支都是整的。于是可把 $X$ 换为其连通分支，不妨设 $X$ 是整的仿射概形。 

  由于 $X$ 是整的仿射概形，令 $X = Spec(A)$，并约定记号如下： 
  $
    X' &= Spec(A'), #h(2em) && A' := A otimes_R R' = A[pi.alt^(1\/n)] \
    X_eta &= Spec(A_1), && A_1 := A otimes_R K = A[pi.alt^(-1)] \
    X'_(eta') &= Spec(A'_1), && A'_1 := A' otimes_(R') Frac(R') = A[pi.alt^(1\/n), pi.alt^(-1)] \
    Z_eta &= Spec(C_1) \
    Z'_(eta') &= Spec(C'_1), && C'_1 := C_1 otimes_K Frac(R') = C_1 [pi.alt^(1\/n)]
  $
  这些环都因在 DVR 或域上光滑而正则。已知 $A$ 与 $A_1$ 是维数为 $2$ 的正则整环。令： 
  $
    F = Frac(A) = Frac(A_1) 
  $

  记 $S, S'$ 的闭点分别为 $s, s'$，它们有相同的剩余域 $k$。不妨假设 $X_s = X'_(s') != emptyset$，否则无需证明。此时 $X'$ 也必是整的： 

  - 取泛点 $frak(p) in X_s = Spec(A\/frak(pi.alt) A)$。该纤维在域上光滑，故正则。于是泛点处的局部环 $A_(frak(p))\/frak(pi.alt) A_(frak(p))$ 是域，从而 $A_(frak(p))$ 是以 $pi.alt A_(frak(p))$ 为一致化元的 DVR。 

    于是 $T^n - pi.alt$ 在 DVR $A_(frak(p))$ 上不可约，从而在其分式域 $F$ 上不可约。因此它在 $A$ 上不可约，故 $A' = A[T]\/(T^n - pi.alt)$ 是整环。 

  令： 
  $
    F' = Frac(A') = Frac(A'_1)
  $
  我们知道 $A, A_1, A', A'_1$ 都是正则整环，其中 $A, A'$ 的维数为 $2$，$A_1, A'_1$ 的维数为 $1$。 

  $Z'_(eta') -> X'_(eta')$ 是平展 $ZZ\/n$-主丛，$n$ 为素数。若它是平凡的，就取 $Z' = union.sq.big_(i=1)^n X'$，证明即完成。于是不妨假设： 

  - $Z'_(eta') -> X'_(eta')$ 与 $Z_eta -> X_eta$ 都是非平凡的平展 $ZZ\/n$-主丛。 

    $ZZ\/n$ 传递地作用在 $Z'_(eta')$ 与 $Z_eta$ 的连通分支上。由于 $n$ 是素数，它们只能有 $1$ 个或 $n$ 个连通分支。而有 $n$ 个连通分支的 $ZZ\/n$-主丛是平凡的。于是 $Z_eta, Z'_(eta')$ 都必连通，从而整且正则。因此 $C_1, C'_1$ 是维数为 1 的正则整环。令： 
    $
      L = Frac(C_1), L' = Frac(C'_1)
    $
    
  $Aut(C_1\/A_1)$ 中的 $n$ 个自同构都传递到泛纤维上，故 $L\/F$ 是 $n$ 次循环 Galois 扩张。同理 $L'\/F'$ 也是 $n$ 次循环 Galois 扩张。 

  由于 $C'_1$ 是 $A'_1$ 上有限的整环，必有： 
  $
    C'_1 otimes_(A'_1) F' = L'
  $
  又 $L' = C'_1 otimes_(A'_1) F' = (C_1 otimes_(A_1) F) otimes_F F' = L otimes_F F'$。于是作为 $L'$ 的子域，$L' = L F'$。 

  设 $C'$ 是 $A'$ 在 $L'$ 中的正规化。由于 $L'\/F'$ 有限可分，由 #cite-stacks("032L")[Lemma 10.161.8]，$C'$ 在 $A'$ 上有限。令 $Z' = Spec(C')$，我们要证明这个有限映射 $Z' -> X'$ 是有限平展的。此外，由于局部化与正规化交换， 
  $
    C' otimes_(A') A'_1 = C'[pi.alt^(-1)] = C'_1
  $
  （这里 $C'_1$ 正规且在 $A'_1$ 上有限，故它是 $A'_1$ 在 $Frac(C'_1) = L'$ 中的正规化。）于是 $pi': Z' -> X'$ 确实在泛纤维上还原为 $Z'_(eta') -> X'_(eta')$。特别地，$pi'$ 在泛纤维 $X'_(eta')$ 上方的每个点处都平展。 

  我们断言：$pi'$ 在 $X'$ 中高度 $<=1$ 的点上方的每个点处都平展。它在泛纤维上方已经平展。而 $X'_(s')$ 的闭点高度为 $2$，故只需处理 $X_s = X'_(s')$ 的泛点。 

  设 $xi in Spec(A')$ 是 $X'_(s') = X_s$ 的某个不可约分支的泛点。它由素理想 $frak(q)' in Spec(A'\/pi.alt A')$ 或 $frak(q) in Spec(A\/pi.alt A)$ 代表。令： 
  $
    V  &= A_(frak(q)) = cal(O)_(X,xi) \
    V' &= A'_(frak(q')) = cal(O)_(X',xi) = V[pi.alt^(1\/n)]
  $
  两者都是 DVR。现在 $V\/pi.alt V = cal(O)_(X_s,xi)$ 是域，故 $pi.alt$ 是 $V$ 的一致化元。于是 $T^n - pi.alt$ 在 $V$ 上是 Eisenstein 的，从而 $pi.alt^(1\/n)$ 是 $V' = V[pi.alt^(1\/n)]$ 的一致化元。 

  设 $W$ 是 $V$ 在 $L$ 中的正规化。由于 $L\/F$ 有限可分，由 #cite-stacks("032L")[Lemma 10.161.8]，$W$ 在 $V$ 上有限。由于 $V -> W$ 是包含映射且 $V$ 是 DVR，$W$ 在 $V$ 上有限自由，从而平坦。 
  
  由于 $L\/F$ 是 Galois 扩张，可以应用 Hilbert 理论。$Gal(L\/F) cong ZZ\/n$ 传递地作用在 $W$ 的 $g$ 个极大素理想上，且它们的分歧指数 $e$ 与剩余次数 $f$ 都相同。于是 $e f g = n$；由于 $n$ 是素数，只有三种可能： 
  $
    (e, f, g) = (1, 1, n), (1, n, 1), (n, 1, 1)
  $

  - 前两种情形下 $e = 1$。剩余域扩张的次数为 $1$ 或 $n$，都与剩余特征互素。因此这些剩余域扩张都是有限可分的。 
  
    于是 $W$ 在 $V$ 上非分歧。它又是有限自由的，故 $Spec(W) -> Spec(V)$ 有限平展。于是 $D = W otimes_V V'$ 在 $V'$ 上有限平展。另一方面， 
    $
      Frac(D) = D otimes_(V') F' = W otimes_V F' = W otimes_V F otimes_F F' = L otimes_F F' = L'
    $
    于是 $D$ 是 $L'$ 的正规 $V'$-子代数，且在 $V'$ 上有限，故它是 $V'$ 在 $L'$ 中的正规化。由于正规化与局部化交换， 
    $
      C' otimes_(A') V' cong D
    $
    因此 $C' otimes_(A') V'$ 在 $V'$ 上有限平展。由于底上的局部化不改变平展性，$Spec(C') -> Spec(A')$ 在 $xi$ 上方的点处平展。 

  - 在 $(e, f, g) = (n, 1, 1)$ 的情形，$W$ 本身就是 DVR，剩余域与 $V$ 相同，分歧指数为 $n$。取一致化元 $delta in W$，使得 $pi.alt = delta^n u$，其中 $u in W^times$。取： 
    $
      D = W[T]\/(T^n - u) = W[u^(1\/n)]
    $
    并通过 $V' -> D, pi.alt^(1\/n) |-> delta u^(1\/n)$ 赋予 $D$ 一个 $V'$-代数结构。这是良定义的，因为 $(delta u^(1\/n))^n = delta^n u = pi.alt$。$D$ 在 $W$ 上自由，从而无挠。于是 $delta in W$ 是 $D$ 的非零因子。而在 $D$ 中 $u^(1\/n)$ 是单位，故 $pi.alt^(1\/n) = delta u^(1\/n)$ 仍是非零因子。于是 $D$ 有限且无挠，从而在 DVR $V'$ 上有限。我们断言 $Spec(D) -> Spec(V')$ 有限平展。事实上， 
    $
      D\/pi.alt^(1\/n) D = D\/delta D = k(W)[T]\/(T^n - u)
    $
    作为 Kummer 覆叠，它在 $k(W)$ 上有限平展，因为 $u in W^times$。因此， 
    $
      Omega_(D\/V') otimes_D D\/pi.alt^(1\/n) D = 0
    $
    由 Nakayama 引理，$Omega_(D\/V') = 0$。于是 $Spec(D) -> Spec(V')$ 非分歧，且有限自由，从而有限平展。最后， 
    $
      D[pi.alt^(-1\/n)] &= L[T]\/(T^n - u) \
      &= L[T]\/(T^n - pi.alt) #[作替换 $T |-> delta T$] \
      &= L(pi.alt^(1\/n)) = L'
    $ 
    于是 $C' otimes_(A') V' = D$ 在 $V'$ 上有限平展。由于底上的局部化不改变平展性，$Spec(C') -> Spec(A')$ 在 $xi$ 上方的点处平展。 

  于是 $pi': Spec(C') -> Spec(A')$ 在 $Spec(A')$ 中高度 $<=1$ 的点上方的所有点处都平展。对任意高度 $2$ 的点 $frak(p) in Spec(A')$，有限态射 $Spec(C'_(frak(p))) -> Spec(A'_(frak(p)))$ 在去心谱 $Spec(A'_(frak(p))) - {frak(p) A'_(frak(p))}$ 上平展，且 $C'_(frak(p))$ 正规。由 $2$ 维的 Zariski–Nagata 纯性（@zariski-nagata-purity-in-dim-2），$Spec(C'_(frak(p))) -> Spec(A'_(frak(p)))$ 有限平展。由于底上的局部化不改变平展性，$Spec(C') -> Spec(A')$ 在 $frak(p)$ 上方的点处平展。这样我们便证明了 $Spec(C') -> Spec(A')$ 有限平展。 
]

#proposition(name: <sbc-core-h1>)[
  设 $A$ 是 Noether 的严格 Hensel 正规局部整环，$K = Frac(A)$。则对 $n in A^times$，$Spec(ol(K) otimes_A A{T})$ 没有次数为 $n$ 的非平凡有限平展覆叠。特别地， 
  $
    H^1 (Spec(ol(K) otimes_A A{T}), ul(ZZ\/n)) = 0
  $
]
#proof[
  利用正合列 $0 -> ul(ZZ\/n) -> ul(ZZ\/m n) -> ul(ZZ\/m) -> 0$，可把 $n$ 归结为它的素因子，从而不妨设 $n$ 是素数。 

  由拓扑不变性，只需证明： 
  $
    H^1 (Spec(K^sep otimes_A A{T}), ul(ZZ\/n)) = 0
  $

  由 @cech-h1-classifies-torsors，该上同调中的每个类都由平展 $ZZ\/n$-主丛代表。设 $pi: Z -> Y := Spec(K^sep otimes_A A{T})$ 是平展 $ZZ\/n$-主丛。 

  - 由于：#h(1fr)
    $
      K^sep otimes_A A{T} = dirlim_(L\/K #[finite separable]) L otimes_A A{T}
    $
    对 $pi$ 应用 @passage-to-limit-of-morphisms (1) 与 @passage-to-limit-of-properties (2a)(3d)，并对主丛同构 $Z times ZZ\/n cong Z times_Y Z$ 的逆应用 @passage-to-limit-of-morphisms (1)(3)，便可假设 $pi$ 来自某个有限可分扩张 $L\/K$ 上平展 $ZZ\/n$-主丛 $pi^((1)): Z^((1)) -> Y^((1)) := Spec(L otimes_A A{T})$ 的基变换。 

    由 @a-braces-t-and-normalization-in-fin-sep-ext，把 $A$ 换成它在 $L$ 中的正规化不会影响所讨论的概形。于是不妨假设 $pi$ 来自如下平展 $ZZ\/n$-主丛的基变换： 
    $
      pi^((1)): Z^((1)) -> Y^((1)) := Spec(K otimes_A A{T})
    $

  - 由于： 
    $
      Spec(K otimes_A A{T}) = invlim_(U subset Spec(A) #[open]) U times_A Spec(A{T})
    $
    由同样的极限论证，不妨假设存在稠密开集 $U subset Spec(A)$ 以及平展 $ZZ\/n$-主丛： 
    $
      pi^((2)): Z^((2)) -> Y^((2)) := U times_A Spec(A{T})
    $
    它经基变换得到 $pi^((1))$，从而得到 $pi$。 

  - 由于： 
    $
      U times_A Spec(A{T}) = invlim_((Spec(B),ol(u)) -> (Spec(A[T]),Spec(K(T)^sep)) #[etale]) U times_A Spec(B)
    $
    由同样的极限论证，不妨假设存在平展 $A[T]$-代数 $B$ 以及平展 $ZZ\/n$-主丛： 
    $
      pi^((3)): Z^((3)) -> Y^((3)) := U times_A Spec(B)
    $
    它经基变换得到 $pi^((2))$，从而得到 $pi^((1)), pi$。 

  在后面的段落中，我们将默认使用如下结果：若 $K'\/K$ 是有限可分扩张，$A'$ 是 $A$ 在 $K'$ 中的正规化，则 $Spec(A') -> Spec(A)$ 保持素理想的高度。事实上，素理想的上行由有限性成立，下行（高度不降）由正规性与有限性成立。 

  - $U subset Spec(A)$ 是稠密开集，故 $A$ 中只有有限多个高度 $1$ 的素理想不在 $U$ 中。设它们为 $frak(p)_1, dots.c, frak(p)_t$。由于 $A$ 正规，每个 $A_(frak(p)_i)$ 都是 DVR，设其一致化元为 $pi.alt_i$。令 $K' = K(pi.alt_1^(1\/n), dots.c, pi.alt_t^(1\/n))$，$A'$ 为 $A$ 在 $K'$ 中的正规化；由 @a-braces-t-and-normalization-in-fin-sep-ext，$A'$ 必是严格 Hensel 正规局部环，且在 $A$ 上有限。设 $U' subset Spec(A')$ 是 $U$ 的基变换。沿 $Spec(A') -> Spec(A)$ 对 $pi^((3)): Z^((3)) -> U times_A Spec(B)$ 作基变换，得到平展 $ZZ\/n$-主丛： 
    $
      pi': Z' -> U' times_(A') Spec(B')
    $ 
    其中 $B' = B otimes_A A'$ 是平展 $A'[T]$-代数。$pi'$ 有泛纤维： 
    $
      pi'_1: Z'_1 -> Spec(K') times_(A') Spec(B')
    $

    设 $frak(q) in Spec(A') - U'$ 是高度 $1$ 的素理想，则它必位于某个 $frak(p)_i in Spec(A) - U$ 上方。此时 $A_(frak(p)_i) -> A'_(frak(q))$ 是 DVR 的扩张。又因 $pi.alt_i^(1\/n) in K'$，而 $A'_(frak(q))$ 是 $A_(frak(p)_i)$ 在 $K'$ 中的正规化的一个局部环，故它必含 $pi.alt_i^(1\/n)$。于是我们得到 DVR 的扩张链： 
    $
      A_(frak(p)_i) arrow.hook A_(frak(p)_i) [pi.alt_i^(1\/n)] arrow.hook A'_(frak(q))
    $
    $B$ 是相对维数为 $1$ 的光滑 $A$-代数。由 @abhyankar-lemma-special-case，泛纤维 $Spec(K(pi.alt_i^(1\/n))) times_(U') Z'-> Spec(K(pi.alt_i^(1\/n))) times_A Spec(B)$ 延拓为 $Spec(A_(frak(p)_i) [pi.alt_i^(1\/n)]) times_A Spec(B)$ 上方的有限平展覆叠。 

    因此 $pi'_1: Z'_1 -> Spec(K') times_(A') Spec(B')$ 延拓为 $Spec(A'_(frak(q))) times_(A') Spec(B')$ 上方的有限平展覆叠。由 @passage-to-limit-of-morphisms (1)，它延拓为某个开邻域 $frak(q) in V_(frak(q)) subset Spec(A')$ 之上的有限平展覆叠，即 $V_(frak(q)) times_(A') Spec(B')$ 上的有限平展覆叠。适当缩小 $V_(frak(q))$（仍含 $frak(q)$），由 @passage-to-limit-of-morphisms (3)，该延拓在交 $(U' inter V_(frak(q))) times_(A') Spec(B')$ 上与 $pi': Z'_1 -> U' times_(A') Spec(B')$ 一致。 

    于是把 $U'$ 换成 $U' union V_(frak(q))$，便可延拓 $pi': Z' -> U' times_(A') Spec(B')$，从而从 $Spec(A') - U'$ 中消去一个高度 $1$ 的素理想。对 $Spec(A') - U'$ 中有限多个素理想重复这一构造，便得到有限平展覆叠： 
    $
      pi^((4)): Z^((4)) -> V times_(A') Spec(B')
    $
    其中 $V subset Spec(A')$ 是余维度 $>=2$ 的开子集，且 $pi^((4))$ 延拓了 $pi^((3))$ 的某个基变换。在泛纤维上，它经基变换得到 $pi$。 

  - 把 $A$ 换成 $A'$。沿 $Spec(A{T}) -> Spec(B)$ 对 $pi^((4))$ 作基变换，便得到有限平展覆叠： 
    $
      pi^((5)): Z^((5)) -> V times_A Spec(A{T})
    $
    其中 $V subset Spec(A)$ 是余维度 $>=2$ 的开子集，且 $pi^((5))$ 经基变换得到 $pi$。 

  - 取零截面 $i: Spec(A) -> Spec(A{T})$。沿零截面对 $pi^((5))$ 作基变换，得到有限平展覆叠 $Z_V -> V$，其中 $V subset Spec(A)$ 且 $A$ 正规。于是 $V$ 的有限平展覆叠由有限离散的 $pi_1^et (V) cong Gal(K^"ur" (V)\/K)$-集分类。因此存在有限可分扩张 $K'\/K$，使得 $V$ 在 $K'$ 中的正规化 $V'$ 在 $V$ 上有限平展，且 $Z_V times_V V' -> V'$ 是平凡有限平展覆叠。 
  
    设 $A'$ 是 $A$ 在 $K'$ 中的正规化。由于正规化是局部构造，$V' = V times_A Spec(A')$。于是沿 $Spec(A') -> Spec(A)$ 对 $pi^((5))$ 作基变换，得到有限平展覆叠： 
    $
      pi^((6)): Z^((6)) -> V' times_(A') Spec(A'{T})
    $
    再沿零截面 $Spec(A') -> Spec(A'{T})$ 作基变换，$pi^((6))$ 就成为平凡平展覆叠。此外，$pi$ 是 $pi^((6))$ 的基变换。 

  一旦证明 $pi^((6))$ 平凡，也就证明了 $pi$ 平凡，从而证明了 $Spec(K^sep otimes_A A{T})$ 上每个平展 $ZZ\/n$-主丛都平凡。于是证明便完成了，即下式： 
  $
    H^1 (Spec(K^sep otimes_A A{T}), ul(ZZ\/n)) = 0
  $
  而由如下引理，$pi^((6))$ 是平凡的。 

  #lemma[
    设 $A$ 是 Noether 的严格 Hensel 正规局部整环，$V subset Spec(A)$ 是余维度 $>=2$ 的开子集，且： 
    $
      pi: Z -> V times_A Spec(A{T})
    $
    是有限平展覆叠，它沿零截面 $i: Spec(A) -> Spec(A{T})$ 的基变换是 $V$ 的平凡有限平展覆叠。则 $pi$ 是平凡的。 
  ]
  #proof[
    设 $n$ 是 $pi$ 的次数。 

    注意 $A{T}\/T^m A{T} cong A[T]\/T^m A[T]$。事实上， 
    
    - 由 @henselization-and-quotients，$A{T}\/T^m A{T} cong (A[T]\/T^m)^#[sh]$。然而 $A[T]\/T^m$ 是严格 Hensel 局部环 $A$ 上有限的局部环，故由 @finite-over-henselian-is-henselian，它是严格 Hensel 的。于是， 
      $
        A{T}\/T^m A{T} cong A[T]\/T^m
      $

    于是我们有一族相容的闭浸入 $i_m: Spec(A[T]\/T^(m+1)) -> Spec(A{T})$，其中 $i_0: Spec(A) cong Spec(A[T]\/T) -> Spec(A{T})$ 是零截面。它们合起来诱导映射 $hat(i): Spec(A fps(T)) -> Spec(A{T})$。 
  
    由拓扑不变性，沿每个 $i_m: Spec(A[T]\/T^(m+1)) -> Spec(A{T})$ 作基变换后，$pi: Z -> V times_A Spec(A{T})$ 成为平凡覆叠。此外，不同 $m$ 的平凡化彼此相容。 

    用如下拉回图表固定记号： 
    // https://q.uiver.app/#r=typst&q=WzAsMTEsWzIsMiwiU3BlYyhBe1R9KSJdLFsyLDMsIlNwZWMoQSkiXSxbMSwzLCJWIl0sWzEsMiwiVyJdLFsyLDAsIlNwZWMoQVtUXVxcL1ReKG0rMSkpIl0sWzIsMSwiU3BlYyhBIGZwcyhUKSkiXSxbMSwwLCJXX20iXSxbMSwxLCJoYXQoVykiXSxbMCwyLCJaIl0sWzAsMCwiWl9tIl0sWzAsMSwiaGF0KFopIl0sWzQsNSwial9tIl0sWzUsMCwiaGF0KGkpIl0sWzAsMSwiZyJdLFsyLDEsIiIsMix7InN0eWxlIjp7InRhaWwiOnsibmFtZSI6Imhvb2siLCJzaWRlIjoidG9wIn19fV0sWzMsMCwiaCIsMix7InN0eWxlIjp7InRhaWwiOnsibmFtZSI6Imhvb2siLCJzaWRlIjoidG9wIn19fV0sWzcsNSwiaGF0KGgpIiwyLHsic3R5bGUiOnsidGFpbCI6eyJuYW1lIjoiaG9vayIsInNpZGUiOiJ0b3AifX19XSxbNiw0LCJoX20iLDAseyJzdHlsZSI6eyJ0YWlsIjp7Im5hbWUiOiJob29rIiwic2lkZSI6InRvcCJ9fX1dLFs4LDMsInBpIiwyXSxbOSw2LCJwaV9tIl0sWzYsNywiaidfbSJdLFs5LDEwLCJqJydfbSIsMl0sWzEwLDcsImhhdChwaSkiLDJdLFs3LDMsImhhdChpKSciXSxbMTAsOCwiaGF0KGkpJyciLDJdLFszLDIsImcnIl1d
    #align(center, diagram({
      node((2, 2), [$Spec(A{T})$])
      node((2, 3), [$Spec(A)$])
      node((1, 3), [$V$])
      node((1, 2), [$W$])
      node((2, 0), [$Spec(A[T]\/T^(m+1))$])
      node((2, 1), [$Spec(A fps(T))$])
      node((1, 0), [$W_m$])
      node((1, 1), [$hat(W)$])
      node((0, 2), [$Z$])
      node((0, 0), [$Z_m$])
      node((0, 1), [$hat(Z)$])
      edge((2, 0), (2, 1), [$j_m$], label-side: left, "->")
      edge((2, 1), (2, 2), [$hat(i)$], label-side: left, "->")
      edge((2, 2), (2, 3), [$g$], label-side: left, "->")
      edge((1, 3), (2, 3), "hook->")
      edge((1, 2), (2, 2), [$h$], label-side: right, "hook->")
      edge((1, 1), (2, 1), [$hat(h)$], label-side: right, "hook->")
      edge((1, 0), (2, 0), [$h_m$], label-side: left, "hook->")
      edge((0, 2), (1, 2), [$pi$], label-side: right, "->")
      edge((0, 0), (1, 0), [$pi_m$], label-side: left, "->")
      edge((1, 0), (1, 1), [$j'_m$], label-side: left, "->")
      edge((0, 0), (0, 1), [$j''_m$], label-side: right, "->")
      edge((0, 1), (1, 1), [$hat(pi)$], label-side: right, "->")
      edge((1, 1), (1, 2), [$hat(i)'$], label-side: left, "->")
      edge((0, 1), (0, 2), [$hat(i)''$], label-side: right, "->")
      edge((1, 2), (1, 3), [$g'$], label-side: left, "->")
    }))
    再令 $i'_m = hat(i)' compose j'_m$，$i''_m = hat(i)'' compose j''_m$。 

    令 $B = Gamma(Z, cal(O)_Z)$。这里每个态射都是 Noether 概形之间的分离态射，故所有推前与拉回都保持拟凝聚层。现在 $h_* pi_* cal(O)_Z in QCoh(Spec(A{T}))$，于是： 
    $
      h_* pi_* cal(O)_Z = Gamma(Spec(A{T}), h_* pi_* cal(O)_Z)^tilde = tilde(B)
    $
    从而 $pi_* cal(O)_Z = h^* tilde(B)$。由于 $pi$ 仿射， 
    $
      Z = SPec(pi_* cal(O)_Z) = SPec(h^* tilde(B)) = W times_(A{T}) Spec(B)
    $
    于是剩下要证 $B cong A{T}^n$。由于 $A{T} -> A fps(T)$ 是完备化映射，它忠实平坦。因此只需证明 $hat(B) := B otimes_(A{T}) A fps(T)$ 同构于 $A fps(T)^n$。由拟凝聚层的平坦基变换， 
    $
      hat(B)^tilde cong hat(i)^* h_* pi_* cal(O)_Z cong hat(h)_* hat(pi)_* cal(O)_(hat(Z))
    $
    又因 $hat(pi)$ 仿射， 
    $
      hat(Z) &= SPec(hat(pi)_* cal(O)_(hat(Z))) = SPec(hat(h)^* hat(h)_* hat(pi)_* cal(O)_(hat(Z))) &= SPec(hat(h)^* hat(B)^tilde) \
      &= hat(W) times_(A fps(T)) Spec(hat(B))
    $
    同理，由于 $pi_m$ 仿射， 
    $
      Z_m = W_m times_(A[T]\/T^(m+1)) Spec(Gamma(Z_m, cal(O)_(Z_m)))
    $

    于是取整体截面得 $hat(B) cong Gamma(hat(Z), cal(O)_(hat(Z)))$。现在通过整体截面的限制，有典范映射： 
    $
      Phi: hat(B) cong Gamma(hat(Z), cal(O)_(hat(Z))) -> invlim_(m>=0) Gamma(Z_m, cal(O)_(Z_m))
    $
    由于 $pi_m: Z_m -> W_m$ 有相容的平凡化，$Phi$ 是映射： 
    $
      Phi: hat(B) -> invlim_(m>=0) Gamma(Z_m, cal(O)_(Z_m)) cong (invlim_(m>=0) Gamma(W_m, cal(O)_(W_m)))^n
    $
    为辨认右端的逆向极限，我们需要正规 Hartogs 引理的一个层版本。 

    #lemma[
      （层的正规 Hartogs）设 $X = Spec(A)$ 是 Noether 整正规概形，$U subset X$ 是余维度 $>=2$ 的子集。则对 $X$ 上任意在 $cal(O)_X$ 上自由的凝聚层 $cal(F)$，限制映射： 
      $
        Gamma(X, cal(F)) -> Gamma(U, cal(F))
      $
      是同构。 
    ]
    #proof[
      写 $cal(F) cong cal(O)_X^(oplus r)$，可把 $cal(F)$ 换成 $cal(O)_X$，不妨设 $cal(F) = cal(O)_X$。于是由层 $tilde(A) in Coh(Spec(A))$ 的构造可知，该限制映射就是： 
      $
        A -> inter.big_(frak(p) in U) A_(frak(p))
      $
      这里把两边都看作 $Frac(A)$ 的子集。然而 $U$ 包含 $A$ 的全部高度为 $1$ 的素理想，故由 @normal-hartogs，右端的交恰为 $A$ 本身。 
    ]

    现在： 
    $
      Gamma(W_m, cal(O)_(W_m)) cong Gamma(V, i'_(m,*) cal(O)_(W_m)) cong Gamma(V, i_(m,*) cal(O)_(Spec(A[T]\/T^(m+1))))
    $
    由于 $i_(m,*) cal(O)_(Spec(A[T]\/T^(m+1)))$ 在 $cal(O)_(Spec(A))$ 上有限自由，且 $V$ 在 $Spec(A)$ 中的余维度 $>=2$，由上一引理， 
    $
      Gamma(V, i_(m,*) cal(O)_(Spec(A[T]\/(T^(m+1))))) cong Gamma(Spec(A), i_(m,*) cal(O)_(Spec(A[T]\/T^(m+1)))) cong A[T]\/T^(m+1)
    $
    于是 $Phi$ 等同于： 
    $
      Phi: hat(B) -> invlim_(m>=0) Gamma(Z_m, cal(O)_(Z_m)) cong (invlim_(m>=0) Gamma(W_m, cal(O)_(W_m)))^n cong (invlim_(m>=0) A[T]\/T^(m+1))^n = A fps(T)^n
    $
    已知 $hat(Z) = hat(W) times_(A fps(T)) Spec(hat(B))$，故 $n$ 个坐标映射 $Phi_1, dots.c, Phi_n: hat(B) -> A fps(T)$ 给出结构映射 $Spec(hat(B)) -> Spec(A fps(T))$ 的 $n$ 个截面 $Spec(A fps(T)) -> Spec(hat(B))$。这些截面为： 
    $
      sigma_1, dots.c, sigma_n: hat(W) -> hat(Z)
    $
    这些就是 $hat(pi)$ 的 $n$ 个截面。 

    - 模 $T$ 后，$Phi$ 变为：#h(1fr)
      $
        Phi_0: hat(B)\/T hat(B) = B\/T B -> Gamma(Z_0, cal(O)_(Z_0)) cong Gamma(W_0, cal(O)_(W_0))^n cong A^n
      $
      于是第 $t$ 个坐标映射是沿所选平凡化 $Z_0 cong union.sq.big_(j=1)^n W_0$ 的第 $t$ 个分量的限制 $Gamma(Z_0, cal(O)_(Z_0)) -> A$。在如下等同下： 
      $
        Z_0 = W_0 times_A Spec(Gamma(Z_0, cal(O)_(Z_0)))
      $
      按给定的平凡化，第 $t$ 个坐标映射必给出第 $t$ 个截面 $W_0 -> Z_0$。 

      因此沿 $i_0$ 作基变换后，截面 $sigma_t$ 就成为所选平凡化的第 $t$ 个截面 $W_0 -> Z_0$。特别地，$n$ 个截面 $sigma_1, dots.c, sigma_n$ 两两不同。 

    既然 $hat(Z) -> hat(W)$ 是带 $n$ 个截面的 $n$ 次有限平展覆叠，它必平凡。于是， 
    $
      hat(B) cong Gamma(hat(Z), cal(O)_(hat(Z))) cong Gamma(hat(W), cal(O)_(hat(W)))^n = Gamma(hat(W), cal(O)_(Spec(A fps(T))))^n
    $
    作为 $A fps(T)$-代数。由于 $A -> A fps(T)$ 平坦，下行（高度不降）成立，且 $Spec(A fps(T))$ 中每一点的高度至少等于其像在 $Spec(A)$ 中的高度。于是 $hat(W)$ 在 $Spec(A fps(T))$ 中的余维度 $>=2$。$A fps(T)$ 还是正规整环，故由上一引理： 
    $
      hat(B) cong Gamma(hat(W), cal(O)_(Spec(A fps(T))))^n cong A fps(T)^n
    $
    由性质的 fpqc 下降（@fpqc-descent-of-properties (2)(5)），由于 $hat(B)$ 是有限平展 $A fps(T)$-代数，且 $A{T} -> A fps(T)$ 忠实平坦，$B$ 是有限平展 $A{T}$-代数。由于 $A{T}$ 是严格 Hensel 的，$Spec(A{T})$ 没有非平凡的有限平展覆叠，故必有 $B cong A{T}^n$。证毕。 
  ]
]

#theorem(name: <loc-acyc-of-smooth-maps>)[
  光滑态射都是泛局部零调的。 

  若 $f: X -> S$ 光滑，$Lambda$ 是挠环且其挠系数在 $S$ 中可逆，则 $f$ 关于每个局部常值 $Lambda$-模层都局部零调。 
]
#proof[
  由 @loc-acyc-of-smooth-maps-reductions、@sbc-core-h0、@sbc-core-h1，所有光滑态射都是泛局部零调的。关于局部常值层的第二条陈述来自 @loc-acyc-pass-to-lcc-sheaves。 
]

#theorem(name: <smooth-base-change>)[
  （光滑基变换）设有如下拉回图表： 
  // https://q.uiver.app/#r=typst&q=WzAsNCxbMCwxLCJYIl0sWzEsMSwiUyJdLFswLDAsIlgnIl0sWzEsMCwiUyciXSxbMywxLCJnIl0sWzIsMCwiZyciLDJdLFsyLDMsImYnIl0sWzAsMSwiZiIsMl1d
  #align(center, diagram({
    node((-1, 1), [$X$])
    node((0, 1), [$S$])
    node((-1, 0), [$X'$])
    node((0, 0), [$S'$])
    node((-0.7, 0.3), $cart$)
    edge((0, 0), (0, 1), [$g$], label-side: left, "->")
    edge((-1, 0), (-1, 1), [$g'$], label-side: right, "->")
    edge((-1, 0), (0, 0), [$f'$], label-side: left, "->")
    edge((-1, 1), (0, 1), [$f$], label-side: right, "->")
  }))
  其中 $f$ 是拟紧拟分离的，$g$ 光滑。设 $Lambda$ 是 $n$-挠环，且 $n in cal(O)_S^times$。则对一切 $cal(K) in D^+ (X_et, Lambda)$，基变换映射： 
  $
    g^(-1) R f_* cal(K) -> R f'_* g'^(-1) cal(K)
  $
  是同构。 

  特别地，对任意层 $cal(F) in cAb(X_et, Lambda)$，基变换映射： 
  $
    g^(-1) R^q f_* cal(F) -> R^q f'_* g'^(-1) cal(F)
  $
  对一切 $q >= 0$ 都是同构。 
]
#proof[
  这由 @loc-acyc-of-smooth-maps 与 @loc-acyc-and-base-change 推出。 
]

作为光滑基变换的推论，我们说明：在可分闭域上，挠层的平展上同调（挠系数与底域特征互素）沿可分闭域扩张作基变换时不变。 

#corollary(name: <bc-along-extension-of-sep-cl-fields>)[
  设 $Omega\/K$ 是可分闭域扩张，$X$ 是 $K$ 上的拟紧拟分离概形，$X_Omega = X otimes_K Omega$。 

  则对任意复形 $cal(K) in D^+_(#[tor]\/K) (X_et, Lambda)$（即下有界复形，其各上同调层都是挠层且挠系数在 $K$ 中可逆），限制态射： 
  $
    R Gamma(X, cal(K)) -> R Gamma(X_Omega, cal(K)|_(X_Omega))
  $
  是同构。 
]
#proof[
  由 way-out 引理，可把 $cal(K)$ 换成单个挠层 $cal(F)$，其各茎的挠系数在 $K$ 中可逆，于是只需证明 $H^q (X, cal(F)) -> H^q (X_Omega, cal(F)|_(X_Omega))$ 是同构。 

  由拓扑不变性，把 $Omega$ 换成其代数闭包 $ol(Omega)$、把 $K$ 换成它在 $ol(Omega)$ 中的代数闭包 $ol(K)$ 是安全的。于是不妨假设 $Omega$ 与 $K$ 都代数闭。 

  把 $Omega$ 写成其有限超越次数的代数闭子域的正向极限 $Omega = dirlim_(I subset Omega #[finite]) ol(K(I))$，并用 @limit-formula-for-schemes 写出： 
  $
    H^q (X_Omega, cal(F)|_(X_Omega)) = dirlim_(I subset Omega #[finite]) H^q (X_(ol(K(I))), cal(F)|_(X_(ol(K(I)))))
  $
  便可把 $Omega$ 换成 $ol(K(I))$，从而假设 $Omega\/K$ 的超越次数有限，比如 $Omega = ol(K(t_1, dots.c, t_m))$。再对超越次数归纳，便可假设 $Omega = ol(K(t))$。 


  
  只需证明 $Omega = ol(K(t))$ 是光滑 $K$-代数 $A_lambda$ 的正向极限 $dirlim_lambda A_lambda$。因为此时可以作出如下拉回图表： 
  // https://q.uiver.app/#r=typst&q=WzAsNixbMCwyLCJYIl0sWzEsMiwiU3BlYyhLKSJdLFswLDEsIlhfKEFfbGFtYmRhKSJdLFsxLDEsIlNwZWMoQV9sYW1iZGEpIl0sWzEsMCwiU3BlYyhPbWVnYSkiXSxbMCwwLCJYX09tZWdhIl0sWzUsNCwiZl9PbWVnYSJdLFsyLDMsImZfbGFtYmRhIl0sWzAsMSwiZiJdLFs1LDIsImgnX2xhbWJkYSIsMl0sWzIsMCwiZydfbGFtYmRhIiwyXSxbNCwzLCJoX2xhbWJkYSJdLFszLDEsImdfbGFtYmRhIl1d
  #align(center, diagram({
    node((-1, 1), [$X$])
    node((0, 1), [$Spec(K)$])
    node((-1, 0), [$X_(A_lambda)$])
    node((0, 0), [$Spec(A_lambda)$])
    node((0, -1), [$Spec(Omega)$])
    node((-1, -1), [$X_Omega$])
    edge((-1, -1), (0, -1), [$f_Omega$], label-side: left, "->")
    edge((-1, 0), (0, 0), [$f_lambda$], label-side: left, "->")
    edge((-1, 1), (0, 1), [$f$], label-side: left, "->")
    edge((-1, -1), (-1, 0), [$h'_lambda$], label-side: right, "->")
    edge((-1, 0), (-1, 1), [$g'_lambda$], label-side: right, "->")
    edge((0, -1), (0, 0), [$h_lambda$], label-side: left, "->")
    edge((0, 0), (0, 1), [$g_lambda$], label-side: left, "->")
  }))
  再应用基变换的极限公式 @limit-formula-for-base-change，便知： 
  $
    R^q f_(Omega,*) (cal(F)|_(X_Omega)) &= dirlim_lambda h_lambda^(-1) R^q f_(lambda,*) (cal(F)|_(X_(A_lambda))) \
    &= dirlim_lambda h_lambda^(-1) g_lambda^(-1) R^q f_* cal(F) #[由光滑基变换 @smooth-base-change] \
    &= dirlim_lambda (R^q f_* cal(F))|_(Spec(Omega)) = (R^q f_* cal(F))|_(Spec(Omega))
  $
  换言之， 
  $
    H^q (X_Omega, cal(F)|_(X_Omega)) = H^q (X, cal(F))
  $
  剩下要证的是：$ol(K(t))$ 是光滑 $K$-代数的正向极限。对任意子域 $K(t) subset L subset ol(K(t))$，令 $A_L$ 为 $K[t]$ 在 $L$ 中的正规化，于是 $L = Frac(A_L)$。由于 $K[t]$ 是 Nagata 的（见 @cite-matsumura-ca[Theorem 31.H]），$A_L$ 是有限 $K[t]$-代数。于是 $A_L$ 是整的有限型 $K$-代数，维数为 $1$，并且整闭。由于 $A_L$ 维数为 $1$ 且整闭，其所有局部环都是域或 DVR，故 $A_L$ 正则。回忆：对代数闭域 $K$，有限型 $K$-概形光滑当且仅当它正则（见 @cite-hartshorne-ag[Theorem III.10.2]）。于是 $A_L$ 是光滑 $K$-代数，且 $Frac(A_L) = L$。

  现在： 
  $
    ol(K(t)) = dirlim_(L\/K(t) #[finite]) Frac(A_L) = dirlim_(L\/K(t) #[finite] \ 0 != f in A_L) A_L [f^(-1)]
  $
  其中 $Spec(A_L [f^(-1)])$ 是 $Spec(A_L)$ 的仿射开集，从而在 $K$ 上光滑。这样我们就把 $ol(K(t))$ 写成了光滑 $K$-代数的正向极限。 
]
