// audit-exception: 作者 R3 意见：两端的剩余域都是 k，删去多余的 “k cong k” 表述，数学内容未变。
#import "void-import.typ": *

== Hensel 化与严格 Hensel 化

平展态射模拟开子集，它们定义了一种更细的“拓扑”，这种拓扑适合应用，后文也将加以研究。在 Zariski 拓扑下，概形的一个重要对象是它在某点处的局部环：
$
  cal(O)_(X,x) = dirlim_(x in U subset X #[open]) cal(O)_U (U)
$
它是 $x$ 的所有 Zariski 邻域的极限。我们希望为平展邻域 (étale neighborhood) 定义类似的概念。

后文我们将看到，在平展拓扑下，$X$ 的点的正确概念是几何点 (geometric point)，即一个映射 $ol(x): Spec(Omega) -> X$，其中 $Omega$ 是可分闭域。于是，平展情形下局部环的正确概念是：
$
  dirlim_((U,ol(u))->(X,ol(x)) #[etale]) cal(O)_U (U)
$
最终会发现，这类环是一类特殊的局部环，刻画它们的正是我们熟悉的 Hensel 引理。它们称为（严格）Hensel 局部环，将在平展上同调的发展中起关键作用。

#proposition(name: <equiv-defns-of-henselian>)[
  设 $(A, frak(m))$ 是剩余域为 $k$ 的局部环，则以下条件等价：

  + 每个有限 $A$-代数 $B$ 都分解为 $B = product_i B_i$，即局部 $A$-代数的直积。

  + （Hensel 引理）对任意首一多项式 $f(T) in A[T]$，以及 $ol(f)$ 的任意根 $a_0 in k$，只要 $ol(f)'(a_0) != 0$（即 $a_0$ 不是重根），就存在 $a in A$ 使得 $a_0 = ol(a)$ 且 $f(a) = 0$。
  
  + （强 Hensel 引理）对任意首一多项式 $f in A[T]$，以及任意分解 $ol(f) (T) = g_0 (T) h_0 (T) in k[T]$，只要 $gcd(g_0, h_0) = 1$，就存在分解 $f(T) = g(T)h(T) in A[T]$，使得 $ol(g) = g_0$ 且 $ol(h) = h_0$。

  + 对每个平展态射 $alpha: X -> S = Spec(A)$，考虑它到特殊纤维的基变换 $alpha_0: X_0 -> S_0 = Spec(k)$。则从 $alpha$ 的截面到 $alpha_0$ 的截面的自然映射：
    $
      sec(alpha) -> sec(alpha_0), f |-> f otimes_A k
    $
    是双射。

  + 对任意平展 $A$-代数 $R$，若 $R$ 有一个 $k$-点，则 $alpha: Spec(R) -> Spec(A)$ 有截面。换言之，若 $sec(alpha_0)$ 非空，则 $sec(alpha)$ 也非空。
]
#proof[
  以下蕴含关系自动成立：(3) $==>$(2)，(4) $==>$(5)。

  我们先证 (5) $==>$(4)：
  #proof[
    注意，若 $(A, frak(m))$ 是局部环，则任何映射 $Spec(A) -> X$ 的像都落在任一包含 $Spec(frak(m))$ 的开集内。

    固定一个 $k$-点 $x_0: Spec(k) -> X_0$。则任何提升 $x_0$ 的截面 $x: Spec(A) -> X$，其像必定落在 $x_0$ 的任一邻域 $U$ 内。因此只需对 $x_0$ 的任意一个固定邻域 $U$ 证明：存在唯一的截面 $Spec(A) -> U$ 提升 $x_0: Spec(k) -> U_0$。

    于是，在 (4) 中不妨假设 $X = Spec(B)$，其中 $B$ 是平展 $A$-代数。我们对 $dim_k (B_0)$ 归纳，其中 $B_0 = B otimes_A k$。现在：

    - 若 $sec(Spec(B_0) -> Spec(k))$ 非空，则由 (5)，$sec(Spec(B) -> Spec(A))$ 也非空。于是分离的平展态射 $Spec(B) -> Spec(A)$ 有截面，而该截面必定既是开浸入又是闭浸入。因此作为 $A$-代数可以写成 $B = A times B'$，作为 $k$-代数有 $B_0 = k times B'_0$。现在：
      $
        sec(Spec(B) -> Spec(A)) = {*} union.sq sec(Spec(B') -> Spec(A)) \
        sec(Spec(B_0) -> Spec(k)) = {*} union.sq sec(Spec(B'_0) -> Spec(k))
      $
      于是可以用 $B'$ 替换 $B$。此时 $dim_k (B'_0) = dim_k (B_0) - 1$，故由归纳假设 $sec(Spec(B') -> Spec(A)) cong sec(Spec(B'_0) -> Spec(k))$。从而 $sec(Spec(B) -> Spec(A)) cong sec(Spec(B_0) -> Spec(k))$。

    - 若 $sec(Spec(B_0) -> Spec(k))$ 为空，则 $sec(Spec(B) -> Spec(A))$ 必定也为空。此时所要的双射平凡地成立。
  ]

  (2) $==>$(4)：
  #proof[
    注意，若 $(A, frak(m))$ 是局部环，则任何映射 $Spec(A) -> X$ 的像都落在任一包含 $Spec(frak(m))$ 的开集内。

    固定一个 $k$-点 $x_0: Spec(k) -> X_0$。则任何提升 $x_0$ 的截面 $x: Spec(A) -> X$，其像必定落在 $x_0$ 的任一邻域 $U$ 内。因此只需对 $x_0$ 的任意一个固定邻域 $U$ 证明：存在唯一的截面 $Spec(A) -> U$ 提升 $x_0: Spec(k) -> U_0$。

    由 @local-struct-of-etale-morphisms 所述的平展态射局部结构，把 $X$ 在 $x_0$ 附近、$Spec(A)$ 在 $frak(m)$ 附近适当缩小之后，可以使 $alpha$ 成为标准平展的。但 $Spec(A)$ 中含 $frak(m)$ 的开集只有 $Spec(A)$ 本身，所以只需缩小 $X$ 在 $x_0$ 附近的部分。于是不妨假设：
    $
      X = Spec(B), B = (A[T]_(h(T)))/((g(T)))
    $
    是 $Spec(A)$ 上的标准平展代数，其中 $g(T)$ 首一，且 $(g(T), g'(T)) = (1) subset A[T]_(h(T))$。

    此时 $X_0 -> Spec(k)$ 的截面不外乎满足下式的元素 $a_0 in k$：
    $
      ol(h)(a_0) in k^times, ol(g)(a_0) = 0
    $
    而 $X -> Spec(A)$ 的截面不外乎满足下式的元素 $a in A$：
    $
      h(a) in A^times, g(a) = 0
    $
    因此只需证明归约映射：
    $
      {a in A : h(a) in A^times, g(a) = 0} -> {a_0 in k: ol(h)(a_0) in k^times, ol(g)(a_0) = 0}
    $
    是双射。现在设 $a_0$ 属于右端。由于 $(ol(g)(T), ol(g)'(T)) = (1) subset k[T]_(ol(h)(T))$，必有 $ol(g)'(a_0) != 0$。于是由 Hensel 引理，存在唯一的提升 $a in A$ 使得 $g(a) = 0$。这样的提升必然满足 $h(a) in A^times$（因为它归约为 $ol(h)(a_0) in k^times$）。至此证毕。
    #suppress-qed
  ]

  (4) $==>$(1)：
  #proof[
    已知 (1) 对 $A$ 上有限自由的 $B$ 成立。对一般的有限 $A$-代数 $B$，取有限多个生成元 $b_1, dots.c, b_n in B$，使每个生成元都满足某个首一关系 $f_i (T) in A[T]$。于是有满射：
    $
      C = (A[T_1, dots.c, T_n])/((f_1 (T_1), dots.c, f_n (T_n))) ->> B
    $
    其中 $C$ 是有限自由 $A$-代数。由自由情形，$C$ 分解为 $C = product_i C_i$，即有限多个局部 $A$-代数的乘积。于是作为 $C$ 的商，$B$ 必定分解为 $product_i C_i\/I_i$，同样是有限多个局部 $A$-代数的乘积。

    现在不妨假设 $B$ 在 $A$ 上有限自由。取一组基 $B = oplus.big_(i=1)^n A e_i$，于是有结构常数：
    $
      e_i e_j = sum_(k=1)^n a_(i,j,k) e_k
    $
    其中交换性要求 $a_(i,j,k) = a_(j,i,k)$，结合性要求：
    $
      (e_i e_j) e_k = sum_(s=1)^n a_(i,j,s) e_s e_k = sum_(s=1)^n sum_(t=1)^n a_(i,j,s) a_(s,k,t) e_t \
      e_i (e_j e_k) = sum_(s=1)^n a_(j,k,s) e_i e_s = sum_(s=1)^n sum_(t=1)^n a_(j,k,s) a_(i,s,t) e_t
    $
    从而对每个 $t$，都有 $sum_(s=1)^n a_(i,j,s) a_(s,k,t) = sum_(s=1)^n a_(j,k,s) a_(i,s,t)$。

    引入未定元 $T_1, dots.c, T_n$。则：
    $
      (T_1 e_1 + dots.c + T_n e_n)^2 = sum_(k=1)^n (sum_(1<=i,j<=n) a_(i,j,k) T_i T_j) e_k
    $
    令 $p_k (T) = sum_(1<=i,j<=n) a_(i,j,k) T_i T_j - T_k$，$R = A[T_1, dots.c, T_n]\/(p_1 (T), dots.c, p_n (T))$。则：

    - $B$ 的幂等元函子由 $R$ 表示。事实上，任何环同态 $R -> A$ 都对应一组系数 $alpha_1, dots.c, alpha_n in A$，使得对每个 $k$ 都有：
      $
        sum_(1<=i,j<=n) a_(i,j,k) alpha_i alpha_j - alpha_k = 0
      $
      这等价于说 $sum_(i=1)^n alpha_i e_i in B$ 是幂等元。

      同样地，$R_0 = R otimes_A k$ 表示 $B_0 = B otimes_A k$ 的幂等元。

    - $R$ 是平展 $A$-代数。事实上，考虑 Jacobi 矩阵。多项式 $p_k (T)$ 模拟函数 $X^2 - X$，因此 Jacobi 矩阵应当模拟导数 $2X - 1$；由幂等性 $(2X - 1)^2 = 4 X^2 - 4 X + 1 = 1$，这个导数应当可逆。下面把这一点严格化。计算：
      $
        (partial p_j)/(partial T_i) (T) &= (partial)/(partial T_i) (sum_(1<=k,ell<=n) a_(k,ell,j) T_k T_ell) - delta_(i,j) \
        &= sum_(1<=ell<=n) a_(i,ell,j) T_ell + sum_(1<=k<=n) a_(k,i,j) T_k - delta_(i,j) \
        &= 2 sum_(k=1)^n a_(k,i,j) T_k - delta_(i,j)
      $
      
      考虑 Jacobi 矩阵：
      $
        J = mat(display((partial p_j)/(partial T_i) (T)))_(i,j) = mat(display(sum_(k=1)^n 2 a_(k,i,j) T_k - delta_(i,j)))_(i,j) = 2K - I
      $
      其中 $K = mat(display(sum_(k=1)^n a_(k,i,j) T_k))_(i,j)$。要证明在 $R$ 上 $J^2 = I$，只需证明在 $R$ 上 $K^2 = K$。事实上，比较下标为 $i,j$ 的那一项，需要证明：
      $
        sum_(k=1)^n a_(k,i,j) T_k = sum_(s=1)^n (sum_(k=1)^n a_(k,i,s) T_k) (sum_(ell=1)^n a_(ell,s,j) T_ell) in R
      $
      事实上，在 $R$ 中有
      $
        & sum_(s=1)^n (sum_(k=1)^n a_(k,i,s) T_k) (sum_(ell=1)^n a_(ell,s,j) T_ell) \
        =& sum_(k=1)^n T_k sum_(1<=ell,s<=n) a_(ell,s,j) a_(k,i,s) T_ell \
        =& sum_(k=1)^n T_k sum_(1<=ell,s<=n) a_(i,s,j) a_(k,ell,s) T_ell #[由结合律] \
        =& sum_(s=1)^n a_(s,i,j) sum_(1<=ell,k<=n) a_(k,ell,s) T_k T_ell \
        =& sum_(s=1)^n a_(s,i,j) T_s #[由关系 $p_s (T)$]
      $
      因此 $J^2 = I$ 在 $R$ 中成立，$J$ 可逆。于是 $R$ 是平展 $A$-代数。

    结合 (4) 与上述两点可知，归约映射：
    $
      Idem(B) -> Idem(B_0), b |-> [b]
    $
    是双射。现在 $B_0$ 是有限 $k$-代数，因而也是 Artin 环，故分解为：
    $
      B_0 = B_(1,0) times dots.c times B_(m,0)
    $
    即有限多个 Artin 局部 $k$-代数的乘积。这对应于一组完备的正交幂等元 $[e_1], dots.c, [e_m] in Idem(B_0)$。把它们提升为幂等元 $e_1, dots.c, e_m in Idem(B)$。当 $i != j$ 时，$e_i e_j$ 是归约为 $0$ 的幂等元，故为 $0$；而 $sum_(i=1)^m e_i$ 是归约为 $1$ 的幂等元，故为 $1$。于是 $B_0$ 的分解提升为 $A$-代数分解：
    $
      B = B_1 times dots.c times B_m
    $
    其中 $B_(i,0) = B_i otimes_A k$。由于有限态射是闭的，有限 $A$-代数 $B_i$ 的每个极大理想都位于 $frak(m)$ 之上；因此由 $B_(i,0) = B_i\/frak(m) B_i$ 是局部环，便知 $B_i$ 是局部环。至此证毕。
    #suppress-qed
  ]

  (1) $==>$(3)：
  #proof[
    用单位清除首项系数，不妨假设 $g_0, h_0$ 首一。

    令 $B = A[T]\/(f(T))$。由于 $f$ 首一，它是有限（自由）$A$-代数。由 (1)，
    $
      B = B_1 times dots.c times B_m
    $
    是局部 $A$-代数的乘积，模 $frak(m)$ 后归约为：
    $
      B_0 = B_(1,0) times dots.c times B_(m,0)
    $
    另一方面，$gcd(g_0, h_0) = 1$，故由中国剩余定理，$B_0 cong k[T]\/(g_0 (T)) times k[T]\/(h_0 (T))$。于是不妨假设：
    $
      B_(1,0) times dots.c times B_(ell,0) cong k[T]\/(g_0 (T)) \
      B_(ell+1,0) times dots.c times B_(m,0) cong k[T]\/(h_0 (T))
    $
    现在每个 $B_i$ 都是有限投射 $A$-模，从而是有限自由的。把 $T$ 在这些因子上的特征多项式记为：
    $
      g(X) = det(X id - T : B_1 times dots.c times B_ell) \
      h(X) = det(X id - T : B_(ell+1) times dots.c times B_m)
    $
    则 $g(X) h(X) = det(X id - T : B) = f(X)$，取归约得 $g_0 = g mod frak(m), h_0 = h mod frak(m)$。（这一步用到了 $g_0, h_0$ 首一的假设。）
    #suppress-qed
  ]

  我们已经证明了 (4) $<==>$(5) 以及 (1) $==>$(3) $==>$(2) $==>$(4) $==>$(1)，证毕。
]

#definition(name: <defn-henselian-local-rings>)[
  - 若上述等价条件 (1)--(5) 成立，则称局部环 $(A, frak(m))$ 是 *Hensel 的*；
  
  - 若 $A$ 是 Hensel 的，且剩余域 $k = A\/frak(m)$ 可分闭，则称它是 *严格 Hensel 的*。
]

#corollary[
  任何（$frak(m)$-进）完备的局部环 $(A,frak(m))$ 都是 Hensel 的。
]
#proof[
  众所周知，Hensel 引理对完备局部环成立。
]

#corollary(name: <finite-over-henselian-is-henselian>)[
  设 $A$ 是（严格）Hensel 局部环，则任何有限局部 $A$-代数 $B$ 必定是（严格）Hensel 的。

  于是，在 @equiv-defns-of-henselian (1) 中，每个有限 $A$-代数都分解为有限多个在 $A$ 上有限的局部（严格）Hensel 代数的乘积。
]
#proof[
  假设 $A$ 是 Hensel 的。任何有限 $B$-代数必定是有限 $A$-代数，因而分裂为局部环的直积。于是 @equiv-defns-of-henselian 的 (1) 得到满足，$B$ 是 Hensel 的。

  进一步，若 $A$ 是严格 Hensel 的，注意 $k(B)\/k(A)$ 是有限扩张。由于 $k(A)$ 可分闭，$k(B)\/k(A)$ 必定纯不可分，从而 $k(B)$ 也可分闭。因此 $B$ 是严格 Hensel 的。
]

我们已经刻画了 Hensel 局部环，接下来需要构造 Hensel 化。

#definition(name: <defn-henselizations>)[
  设 $(A, frak(m))$ 是剩余域为 $k$ 的局部环。

  - $A$ 的 *Hensel 化* $A^#[h]$ 定义为如下滤余极限：#h(1fr)
    $
      A^#[h] := dircolim_((Spec(B),frak(q)) -> (Spec(A),frak(m)) #[etale] \ k(frak(q)) = k) B_(frak(q))
    $
    也就是说，$A$ 的 Hensel 化是 $(A, frak(m))$ 的所有平展邻域的局部环所成的滤余极限，其中每个平展邻域都在 $frak(m)$ 处不扩张剩余域。

  - 固定一个可分闭包 $k arrow.r.hook k^sep$。局部环 $(A,frak(m))$ 的 *严格 Hensel 化* 是如下滤余极限：
    $
      A^#[sh] := dircolim_((Spec(B),frak(q)) -> (Spec(A),frak(m)) #[etale] \ phi: k(frak(q)) arrow.hook k^sep) B_(frak(q))
    $
    这里要求 $phi: k(frak(q)) -> k^sep$ 是包含映射，且在剩余域的包含映射 $k -> k(frak(q))$ 之下与给定的 $k -> k^sep$ 相容。

    也就是说，$A$ 的严格 Hensel 化是 $(A, frak(m))$ 的所有平展邻域的局部环的滤余极限。

  为使证明严谨，我们需要验证：定义 $A^#[h]$ 与 $A^#[sh]$ 的余极限所用的指标范畴，确实滤过。
  #proof[
    对 $A^#[h]$：

    - 设 $(B_1, frak(q)_1), (B_2, frak(q)_2)$ 是 $(A, frak(m))$ 的两个平展邻域，且 $k(frak(q)_(1,2)) = k$。取 $B = B_1 otimes_A B_2$，它仍是平展 $A$-代数。$B$ 中位于 $B_(1,2)$ 的 $frak(q)_(1,2)$ 之上的素理想，由纤维的谱分类：
      $
        k(frak(q)_1) otimes_k k(frak(q)_2) = k
      $
      因此存在唯一的 $frak(q) in Spec(B)$ 位于 $frak(q)_(1,2) in Spec(B_(1,2))$ 之上，且 $k(frak(q)) = k$。于是 $(B, frak(q))$ 同时支配 $(B_(1,2), frak(q)_(1,2))$。

    - 对两条平行的箭头 $g_(1,2): (Spec(C), frak(r)) -> (Spec(B), frak(q))$，取：
      $
        g = (g_1, g_2): Spec(C) -> Spec(B otimes_A B)
      $
      由于 $g_1, g_2$ 在剩余域上诱导出相同的映射 $k(frak(q)) -> k(frak(r))$，而两端的剩余域可自然等同，$g$ 把 $frak(r)$ 送进对角线 $Delta_(B\/A) subset Spec(B otimes_A B)$。由于 $B$ 在 $A$ 上平展，$Delta_(B\/A) subset Spec(B otimes_A B)$ 是开集。
      
      于是取仿射开集 $frak(r) in Spec(D) subset g^(-1) (Delta_(B\/A))$，便知 $(Spec(D), frak(r))$ 仍在指标范畴中，且包含映射 $(Spec(D), frak(r)) -> (Spec(C), frak(r))$ 是 $g_(1,2)$ 的等化映射。

    对 $A^#[sh]$：

    - 设 $(B_1, frak(q)_1, phi_1), (B_2, frak(q)_2, phi_2)$ 是 $(A, frak(m))$ 的两个平展邻域。取 $B = B_1 otimes_A B_2$，它仍是平展 $A$-代数。$B$ 中位于 $B_(1,2)$ 的 $frak(q)_(1,2)$ 之上的素理想，由纤维的谱分类：
      $
        k(frak(q)_1) otimes_k k(frak(q)_2)
      $
      映射 $k(frak(q)_1) otimes_k k(frak(q)_2) -> k^sep$，$x_1 otimes x_2 |-> phi_1 (x_1) phi_2 (x_2)$，以极大理想 $frak(r)$ 为核，而这个极大理想对应于位于 $frak(q)_(1,2) in Spec(B_(1,2))$ 之上的 $frak(q) in Spec(B)$。取：
      $
        phi: k(frak(q)) cong k(frak(q)_1) otimes_k k(frak(q)_2)\/frak(r) -> k^sep
      $
      其中最后一个映射为 $[x_1 otimes x_2] |-> phi_1 (x_1) phi_2 (x_2)$。则 $phi$ 同时与 $phi_(1,2)$ 相容。于是 $(Spec(B), frak(q), phi)$ 支配 $(B_1, frak(q)_1, phi_1), (B_2, frak(q)_2, phi_2)$。

    - 对两条平行的箭头 $g_(1,2): (Spec(C), frak(r), psi) -> (Spec(B), frak(q), phi)$，考虑映射 $ol(g)_(1,2): k(frak(q)) -> k(frak(r))$。由假设，$phi = psi compose ol(g)_1 = psi compose ol(g)_2$。由于 $psi$ 是单射，$ol(g)_1 = ol(g)_2$。因此 $g = (g_1, g_2): Spec(C) -> Spec(B otimes_A B)$ 仍把 $frak(r)$ 送到对角线上。与 $A^#[h]$ 的情形相同，同样的对角线论证给出 $(Spec(C), frak(r))$ 的一个 Zariski 仿射开集，其包含映射是 $g_(1,2)$ 的等化映射。

    至此证毕。
  ]

  作为局部环沿局部同态取滤余极限的结果，$A^#[h]$ 与 $A^#[sh]$ 都是局部 $A$-代数。

  注意开浸入都是平展的，因此可以改写这些滤余极限：
  $
    A^#[h] = dircolim_((Spec(B),frak(q)) -> (Spec(A),frak(m)) #[etale] \ k(frak(q)) = k) B \
    A^#[sh] := dircolim_((Spec(B),frak(q)) -> (Spec(A),frak(m)) #[etale] \ phi: k(frak(q)) arrow.hook k^sep) B
  $

  #remark[
    可分闭包 $k -> k^sep$ 的选取并非典范（而且只在非典范同构的意义下唯一）。因此严格说来，$A^#[sh]$ 并非完全典范的构造。不过实践中这很少成为问题，所以我们把所选的可分闭包 $k^sep$ 从记号中略去。
  ]
]

下面证明（严格）Hensel 化的基本性质。

#properties[
  设 $(A, frak(m))$ 是剩余域为 $k$ 的局部环。

  + Hensel 化 $A^#[h]$ 具有以下性质：

    + $A^#[h]$ 是 Hensel 局部环；
    + $A^#[h]$ 是平展 $A$-代数的滤余极限；
    + $A -> A^#[h]$ 是忠实平坦的局部同态；
    + $frak(m)_(A^#[h]) = frak(m) A^#[h]$；
    + $k(A^#[h]) = k$；
    + 对每个 Hensel 局部环 $R$，任何局部同态 $A -> R$ 都能唯一地分解为局部同态 $A -> A^#[h] -> R$。

  + （固定一个可分闭包 $k^sep$，并相对于它定义 $A^#[sh]$。）严格 Hensel 化 $A^#[sh]$ 具有以下性质：

    + $A^#[sh]$ 是严格 Hensel 局部环；
    + $A^#[sh]$ 是平展 $A$-代数的滤余极限；
    + $A -> A^#[sh]$ 是忠实平坦的局部同态；
    + $frak(m)_(A^#[sh]) = frak(m) A^#[sh]$；
    + $k(A^#[sh]) = k^sep$；
    + 对每个严格 Hensel 局部环 $R$ 以及固定的包含映射 $iota: k^sep -> k(R)$，任何局部同态 $A -> R$ 都能唯一地分解为局部同态 $A -> A^#[sh] -> R$，且 $A^#[sh] -> R$ 在剩余域上诱导出 $iota$。

]
#proof[
  (1b) 与 (2b) 直接由极限的另一种写法得到：
  $
    A^#[h] = dircolim_((Spec(B),frak(q)) -> (Spec(A),frak(m)) #[etale] \ k(frak(q)) = k) B \
    A^#[sh] := dircolim_((Spec(B),frak(q)) -> (Spec(A),frak(m)) #[etale] \ phi: k(frak(q)) arrow.hook k^sep) B
  $
  (1d)(2d) 对定义 $A^#[h]$ 或 $A^#[sh]$ 的滤余极限中的任意 $B_(frak(q))$，按定义，极大理想 $frak(q) B_(frak(q))$ 正是 $frak(m) B_(frak(q))$。$A^#[h]$ 与 $A^#[sh]$ 的极大理想都位于每个 $B_(frak(q))$ 的极大理想之上，因而由 $frak(m)$ 生成。于是
  $
    frak(m)_(A^#[h]) = frak(m) A^#[h], frak(m)_(A^#[sh]) = frak(m) A^#[sh]
  $

  (1c)(2c) 定义 $A^#[h]$ 或 $A^#[sh]$ 时出现的每个 $B_(frak(q))$ 都是忠实平坦的局部 $A$-代数。于是作为它们的正向极限，$A^#[h]$ 与 $A^#[sh]$ 是平坦 $A$-代数。既然 $A -> A^#[h]$ 与 $A -> A^#[sh]$ 是平坦的局部同态，它们就忠实平坦。（事实上，平坦态射在谱上是开的，而局部同态把闭点送到闭点。因此像集是 $Spec(A)$ 中含闭点的开子集，从而是 $Spec(A)$ 本身。）

  (1e)(2e) 剩余域可以写成：
  $
    k(A^#[h]) = dircolim_((Spec(B),frak(q)) -> (Spec(A),frak(m)) #[etale] \ k(frak(q)) = k) k(frak(q)) \

    k(A^#[sh]) := dircolim_((Spec(B),frak(q)) -> (Spec(A),frak(m)) #[etale] \ phi: k(frak(q)) arrow.hook k^sep) k(frak(q))
  $
  第一个极限中每个 $k(frak(q)) = k$，故 $k(A^#[h]) = k$。第二个极限中，$k(A^#[sh])$ 是各 $k(frak(q))$ 在 $k^sep$ 中的并。因此，要证 $k(A^#[sh]) = k^sep$，只需证明每个有限可分扩张 $L\/k$ 都作为某个平展 $A$-代数在 $frak(m)$ 之上某个素理想处的剩余域出现。

  - 取本原元 $alpha$，使 $L = k(alpha)$，且 $alpha$ 的极小多项式 $ol(p)(T) in k[T]$ 首一。把 $ol(p)(T)$ 任意提升为同次数的首一多项式 $p(T) in A[T]$。由于 $ol(p)(T) in k[T]$ 可分，可以取 $ol(a_0)(T), ol(a_1)(T) in k[T]$ 使得：
    $
      ol(p)(T) ol(a_0)(T) + ol(p)'(T) ol(a_1) (T) = 1 in k[T]
    $
    把 $ol(a_(0,1))(T)$ 任意提升为 $a_(0,1)(T) in A[T]$，于是：
    $
      p(T) a_0 (T) + p'(T) a_1 (T) = h(T) in 1 + frak(m)[T]
    $
    现在考虑：
    $
      B = (A[T]_(h(T)))/((p(T)))
    $
    则上式给出 $(p(T), p'(T)) = (1) subset A[T]_(h(T))$。因此 $B$ 在 $A$ 上标准平展。此时：
    $
      B\/frak(m) B &cong (k[T]_(ol(h)(T)))/((ol(p)(T))) \
      &cong k[T]\/(ol(p)(T)) #[因为 $ol(h)(T) = 1$] \
      &cong k(alpha) = L
    $
    于是 $frak(m) B$ 是平展 $A$-代数 $B$ 的一个极大理想，位于 $frak(m)$ 之上，且 $k(frak(m) B) = L$。

  较容易的几条性质已经证完，剩下只需证 (a) 与 (f) 两组。

  (1a) 为证明 $A^#[h]$ 的 Hensel 性，考虑平展 $A^#[h]$-代数 $R$ 及其位于 $frak(m)A^#[h]$ 之上、满足 $k(frak(q)) = k$ 的素理想 $frak(q)$。$R$ 必定在 $A^#[h]$ 上有限展示。我们的极限论证定理都以正向集来陈述，因此需要一个抽象的范畴引理，把滤过范畴换成正向集。这就是 Artin–Mazur 构造：

  #lemma(name: <artin-mazur-construction>)[
    (Artin–Mazur 构造，#cite-stacks("0032", [Lemma 4.21.5])) 设 $J$ 是余滤过范畴/* 带终对象*/。则存在正向偏序集 $P$ /*带最小元， */以及共尾函子 $P -> J^opp$。
  ]

  现在由 @passage-to-limit-of-morphisms 与 @passage-to-limit-of-properties (3d)，存在平展邻域 $(B, frak(q)) -> (A, frak(m))$，满足 $k(frak(q)) = k$，以及平展 $B$-代数 $C$，使得 $R = C otimes_B A^#[h]$。由于 $R\/A^#[h]$ 有 $k$-点，$C\/B$ 也有。于是存在 $frak(r) in Spec(C)$ 位于 $frak(q)$ 之上，且 $k(frak(r)) = k$。因此 $(Spec(C), frak(r)) -> (Spec(B), frak(q)) -> (Spec(A), frak(m))$ 是一串平展邻域。

  现在把 $Spec(C) -> Spec(B)$ 沿自身作基变换，投影 $p_1: Spec(C otimes_B C) -> Spec(C)$ 以对角线映射为截面。再基变换到 $A^#[h]$，$Spec(R) -> Spec(A^#[h])$ 便有截面。于是由 @equiv-defns-of-henselian (5)，$A^#[h]$ 是 Hensel 的。

  (2a) 类似地，对任意平展 $A^#[sh]$-代数 $R$ 及其中位于 $frak(m) A^#[sh]$ 之上的素理想 $frak(q)$，由 @passage-to-limit-of-morphisms 与 @passage-to-limit-of-properties (3d)，存在平展邻域 $(B, frak(q)) -> (A, frak(m))$、相容的包含映射 $phi: k(frak(q)) -> k^sep$，以及平展 $B$-代数 $C$，使得 $R = C otimes_B A^#[sh]$。此外还存在位于 $frak(q)$ 之上的 $frak(r) in Spec(C)$。
  
  现在把 $Spec(C) -> Spec(B)$ 沿自身作基变换，投影 $p_1: Spec(C otimes_B C) -> Spec(C)$ 以对角线映射为截面。此外，我们可以任意选取相容的包含映射 $psi: k(frak(r)) -> k^sep$，使 $(C, frak(r), psi)$ 成为定义 $A^#[sh]$ 的正向极限中的一个阶段，并支配 $(B, frak(q), phi)$。于是把 $Spec(C) -> Spec(B)$ 基变换到这个阶段便得到截面，再基变换到 $Spec(R) -> Spec(A^#[sh])$ 也仍有截面。

  (1f)(2f) 为证这些泛性质，需要下面的引理。

  #lemma[
    设 $(R, frak(n))$ 是 Hensel 局部环。则对任意局部同态：
    $
      phi: (A, frak(m)) -> (R, frak(n))
    $
    以及任意平展邻域 $(Spec(B), frak(q)) -> (Spec(A), frak(m))$；给定任意与包含映射 $k(A) -> k(R)$ 相容的包含映射 $iota: k(frak(q)) -> k(R)$，就存在唯一的局部同态 $(B_(frak(q)), frak(q) B_(frak(q))) -> (R, frak(n))$ 诱导 $iota$。
  ]
  #proof[
    令 $C = B otimes_A R$，它是平展 $R$-代数。如下定义 $C$ 的一个 $k(R)$-点：
    $
      sigma: C = B otimes_A R -> k(R), b otimes r |-> iota([b]) dot [r]
    $
    由 @equiv-defns-of-henselian (4)，该映射唯一地提升为截面 $C -> R$。与 $B -> C$ 复合，得到映射 $B -> R$，它在谱上给出 $frak(n) |-> frak(q)$，从而是局部同态 $(B_(frak(q)), frak(q) B_(frak(q))) -> (R, frak(n))$。反之，对任何提升 $theta: (B_(frak(q)), frak(q) B_(frak(q))) -> (R, frak(n))$，
    $
      C = B otimes_A R -> R, b otimes r |-> theta(b) r
    $
    必定归约为 $sigma$。因此这样的提升 $theta$ 唯一。
  ]

  无论哪种情形，对定义 $A^#[h]$ 或 $A^#[sh]$ 的正向极限中的每个 $B_(frak(q))$，该引理都把 $A -> R$ 唯一地提升为局部同态 $B_(frak(q)) -> R$；于是诱导出唯一的提升 $A^#[h] -> R$ 与 $A^#[sh] -> R$。
]

（严格）Hensel 化的一个重要特点，是各种良好性质在 Hensel 化下保持不变。

#proposition(name: <permanence-of-properties-under-henselization>)[
  设 $(A, frak(m))$ 是局部环。则下列任何一条性质对 $A$ 成立，当且仅当同一性质对 $A^#[h]$ 与 $A^#[sh]$ 都成立。

  0. Noether 性；此时 $dim(A) = dim(A^#[h]) = dim(A^#[sh])$；
  + 正则性；
  + 既约性；
  + 正规性；
  + 是 DVR。
]
#proof[
  只需对 $A$ 与 $A^#[sh]$ 证明这些性质等价，因为 $(A^#[h])^#[sh] cong A^#[sh]$。

  (0) $A -> A^#[sh]$ 忠实平坦，故若 $A^#[sh]$ 是 Noether 的，则由 @noetherianity-normality-descends-along-faithfully-flat-map (1)，$A$ 是 Noether 的。反之，假设 $A$ 是 Noether 的。考虑分次环：
  $
    G = "gr"_(frak(m)) (A) := oplus.big_(n>=0) frak(m)^n\/frak(m)^(n+1) \
    G' = "gr"_(frak(m) A^#[sh]) (A^#[sh]) := oplus.big_(n>=0) frak(m)^n A^#[sh]\/frak(m)^(n+1) A^#[sh]
  $
  由忠实平坦性，
  $
    G' = G otimes_k k^sep
  $
  由于 $A$ 是 Noether 的，$G$ 是有限型 $k$-代数。因此 $G'$ 是有限型 $k^sep$-代数。

  现在：

  - $A^#[sh]$ 是 $frak(m) A^#[sh]$-进分离的。事实上，若 $x in inter.big_(n>=0) frak(m)^n A^#[sh]$，不妨设 $x in B_(frak(q))$，其中 $B_(frak(q))$ 是定义 $A^#[sh]$ 的正向极限中的某个成员。注意 $A^#[sh]$ 在 $B_(frak(q))$ 上忠实平坦（因为检查正向极限可得 $A^#[sh] cong (B_(frak(q)))^#[sh]$）。于是
    $
      x in inter.big_(n>=0) (B_(frak(q)) inter frak(m)^n A^#[sh]) = inter.big_(n>=0) frak(m)^n B_(frak(q))
    $
    由于 $A$ 是 Noether 的，$B$ 是平展 $A$-代数，所以 $B_(frak(q))$ 是 Noether 的。于是上面的交为零，$x = 0$。

  - 由于 $A^#[sh]$ 是 $frak(m) A^#[sh]$-进分离的，对每个非零元素 $f in A^#[sh]$，存在唯一的 $N >= 0$，使得它落在 $frak(m)^N A^#[sh] - frak(m)^(N+1) A^#[sh]$ 中。令 $N = "ord"_(frak(m) A^#[sh]) (f)$。定义初始形式 (initial form) 映射：
    $
      "in"_(frak(m) A^#[sh]): A^#[sh] &-> G' = oplus.big_(n>=0) frak(m)^n A^#[sh]\/frak(m)^(n+1) A^#[sh] \
      (f in frak(m)^N A^#[sh] - frak(m)^(N+1) A^#[sh]) &|-> ([f] in frak(m)^N A^#[sh]\/frak(m)^(N+1) A^#[sh])
    $
    其中 $"in"_(frak(m) A^#[sh]) (0) = 0$。

  - 对任意理想 $I subset A^#[sh]$，定义它的初始理想 (initial ideal)：
    $
      "in"_(frak(m) A^#[sh]) (I) := ({"in"_(frak(m) A^#[sh]) (f) : f in I}) subset G'.
    $
    这是一个齐次理想。若 $I = 0$，它已经有限生成，故设 $I != 0$。由于 $"in"_(frak(m) A^#[sh]) (I)$ 由初始形式生成，而 $G'$ 是 Noether 的，其中有限多个初始形式便生成它。因此存在非零的 $f_1, dots.c, f_s in I$，使得：
    $
      "in"_(frak(m) A^#[sh]) (I) = ("in"_(frak(m) A^#[sh]) (f_1), dots.c, "in"_(frak(m) A^#[sh]) (f_s)).
    $
    现在设 $0 != f in I$，并令：
    $
      d = "ord"_(frak(m) A^#[sh]) (f), quad d_i = "ord"_(frak(m) A^#[sh]) (f_i).
    $
    取齐次次数为 $d$ 的部分，存在齐次元素 $g_i in G'$，使得：
    $
      "in"_(frak(m) A^#[sh]) (f) = sum_(i=1)^s g_i "in"_(frak(m) A^#[sh]) (f_i) in G',
    $
    其中若 $d_i > d$ 则 $g_i = 0$，否则 $g_i$ 的次数为 $d-d_i$。对每个满足 $d_i <= d$ 的 $i$，取 $a_i in frak(m)^(d-d_i) A^#[sh]$ 提升 $g_i$，并在 $d_i > d$ 时令 $a_i = 0$。则上述等式化为：
    $
      f - sum_(i=1)^s a_i f_i in I inter frak(m)^(d+1) A^#[sh].
    $
    令 $K = (f_1, dots.c, f_s) A^#[sh] subset I$。把这一步（提高阶数）重复有限多次——若余项变为零便停止，否则只进行到任意指定的阶数 $M$ 为止——便得到：
    $
      I = K + (I inter frak(m)^M A^#[sh])
    $
    对每个 $M >= 0$ 成立。

  - 现在固定 $x in I$。在定义 $A^#[sh]$ 的正向极限中选一个包含 $x, f_1, dots.c, f_s$ 的阶段 $B_(frak(q))$，并令：
    $
      K_B = (f_1, dots.c, f_s) B_(frak(q)).
    $
    于是 $K = K_B A^#[sh]$。对每个 $M >= 0$，前面的等式给出：
    $
      x in K + (I inter frak(m)^M A^#[sh]) subset K + frak(m)^M A^#[sh] = (K_B + frak(m)^M B_(frak(q))) A^#[sh].
    $
    如上所述，$A^#[sh] cong (B_(frak(q)))^#[sh]$ 在 $B_(frak(q))$ 上忠实平坦，故收缩可得：
    $
      x in K_B + frak(m)^M B_(frak(q))
    $
    对每个 $M >= 0$ 成立。环 $B_(frak(q))$ 是 Noether 局部环，$frak(m) B_(frak(q))$ 是它的极大理想。于是对 $B_(frak(q))\/K_B$ 应用 Krull 交定理（#cite-stacks("00IP")[Lemma 10.51.4]），得到：
    $
      inter.big_(M>=0) (K_B + frak(m)^M B_(frak(q))) = K_B.
    $
    因此 $x in K_B subset K$。由 $x in I$ 的任意性以及 $K subset I$，得 $I = K$。

  因此 $A^#[sh]$ 的每个理想都有限生成，$A^#[sh]$ 是 Noether 的。至于维数，由 #cite-stacks("00ON")[Lemma 10.112.7]，
  $
    dim(A^#[sh]) = dim(A) + underbrace(dim(A^#[sh]\/frak(m) A^#[sh]), = dim(k^sep) = 0) = dim(A)
  $

  (1) 由 (0)，不妨假设 $A, A^#[sh]$ 都是 Noether 的。由于 $frak(m)_(A^#[sh]) = frak(m) A^#[sh]$，平坦性给出：
  $
    frak(m) A^#[sh]\/frak(m)^2 A^#[sh] cong frak(m)\/frak(m)^2 otimes_k k^sep.
  $
  因此 $A$ 与 $A^#[sh]$ 的极大理想有相同的极小生成元个数。由 (0) 还有 $dim(A) = dim(A^#[sh])$。所以 $A$ 正则当且仅当 $A^#[sh]$ 正则。

  (2) 若 $A^#[sh]$ 既约，由于 $A -> A^#[sh]$ 是单射，$A$ 必定既约。反之，由 @etale-local-properties (4)，定义 $A^#[sh]$ 的正向极限中每个 $B_(frak(q))$ 都既约，故 $A^#[sh]$ 既约。

  (3) 若 $A^#[sh]$ 正规，由于 $A -> A^#[sh]$ 忠实平坦，由 @noetherianity-normality-descends-along-faithfully-flat-map (2) 可知 $A$ 正规。反之，由 @etale-local-properties (5)，定义 $A^#[sh]$ 的正向极限中每个 $B_(frak(q))$ 都正规，故 $A^#[sh]$ 正规。
  
  (4) 局部环是 DVR 当且仅当它是 Noether 的、维数为 $1$ 且正则。因此 (4) 由 (0)(1) 推出。
]

接下来证明关于 Hensel 化与严格 Hensel 化的一些杂项性质，它们在本书中会不时用到。

#proposition(name: <henselization-and-directed-limits>)[
  Hensel 化与严格 Hensel 化都与正向极限交换：设 $(A_lambda, frak(m)_lambda)$ 是局部环的正向系统，转移映射都是局部同态。则自然映射：
  $
    dirlim_lambda A_lambda^#[h] -> (dirlim_lambda A_lambda)^#[h]  \
     dirlim_lambda A_lambda^#[sh] -> (dirlim_lambda A_lambda)^#[sh]
  $
  是同构。（严格说来，对严格 Hensel 化，必须为剩余域的可分闭包选取一个相容的包含系统。）
]
#proof[
  这由 Hensel 局部环的泛性质形式地推出。事实上，对任意 Hensel 局部环 $(R, frak(n))$，
  $
    &{dirlim_lambda A_lambda^#[h] -> R #[局部同态]} \
    =& invlim_lambda {A_lambda^#[h] -> R #[局部同态]} \
    =& invlim_lambda {A_lambda -> R #[局部同态]} #[由泛性质]\
    =& {dirlim_lambda A_lambda -> R #[局部同态]}
  $
  因此 $dirlim_lambda A_lambda^#[h]$ 具有 $(dirlim_lambda A_lambda)^#[h]$ 的泛性质。它也是 Hensel 的，因为对任一多项式，Hensel 引理都可以在某个有限阶段 $A_lambda^#[h]$ 上验证。于是得到自然同构：
  $
    dirlim_lambda A_lambda^#[h] ->^tilde (dirlim_lambda A_lambda)^#[h]
  $ 
  严格 Hensel 化的情形同理。
]

#lemma(name: <henselization-and-quotients>)[
  （严格）Hensel 化与取商交换。设 $(A, frak(m))$ 是局部环，$I subset frak(m)$ 是理想，则
  $
    (A\/I)^#[h] cong A^#[h]\/I A^#[h] \
    (A\/I)^#[sh] cong A^#[sh]\/I A^#[sh]
  $
]
#proof[
  这由泛性质形式地推出。事实上，$A^#[h]\/I A^#[h]$ 仍是 Hensel 的：每个有限 $A^#[h]\/I A^#[h]$-代数都是有限 $A^#[h]$-代数，因而分裂为有限多个局部环的乘积。现在对 Hensel 局部环 $R$，
  $
    & {A\/I -> R #[局部同态]} \
    =& {A -> R #[在 $I$ 上为零的局部同态]} \
    =& {A^#[h] -> R #[在 $I$ 上为零的局部同态]} \
    =& {A^#[h]\/I A^#[h] -> R #[局部同态]}
  $
  于是由 Hensel 化的泛性质，$(A\/I)^#[h] cong A^#[h]\/I A^#[h]$。严格 Hensel 化的情形有同样的形式论证。
]

#lemma[
  设 $(A, frak(m))$ 是剩余域为 $k$ 的局部环，则自然映射：
  $
    (A^#[h])^#[sh] -> A^#[sh]
  $
  是同构（$k arrow.hook k^sep$ 的选取固定）。
]
#proof[
  这是形式论证。对任意严格 Hensel 局部环 $(R, frak(n))$ 与固定的包含映射 $iota: k^sep -> k(R)$：
  $
    &{(A^#[h])^#[sh] -> R #[与] iota #[相容的局部同态]} \
    =& {A^#[h] -> R #[局部同态]} \
    =& {A -> R #[局部同态]} \
    =& {A^#[sh] -> R #[与] iota #[相容的局部同态]}
  $
  $(A^#[h])^#[sh]$ 与 $A^#[sh]$ 都是严格 Hensel 的。因此 $(A^#[h])^#[sh] cong A^#[sh]$。
]

#lemma[
  对任意局部环 $(A, frak(m))$，自然映射：
  $
    A\/frak(m)^N -> A^#[h]\/frak(m)^N A^#[h]
  $
  对一切 $N >= 1$ 都是同构。于是完备化之间的自然映射：
  $
    hat(A) -> hat(A^#[h])
  $
  是同构。
]
#proof[
  事实上，
  $
    A^#[h]\/frak(m)^N A^#[h] &cong dircolim_((Spec(B),frak(q)) -> (Spec(A),frak(m)) #[etale] \ k(frak(q)) = k) B_(frak(q))\/frak(m)^N B_(frak(q)) \
    &cong dircolim_((Spec(B),frak(q)) -> (Spec(A),frak(m)) #[etale] \ k(frak(q)) = k) A\/frak(m)^N #[由 @etale-map-with-stable-residue-field-preserves-completions]\
    &cong A\/frak(m)^N
  $
]

#lemma(name: <inverting-nonzeros-in-henselization>)[
  + 设 $A$ 是正规局部整环，$S = A - {0}$。则：#h(1fr)
    $
      S^(-1) A^#[h] = dircolim_((Spec(B),frak(q)) -> (Spec(A),frak(m)) #[etale] \ k(frak(q)) = k) Frac(B_(frak(q))) = Frac(A^#[h]) \
      S^(-1) A^#[sh] = dircolim_((Spec(B),frak(q)) -> (Spec(A),frak(m)) #[etale] \ phi: k(frak(q)) arrow.hook k^sep) Frac(B_(frak(q))) = Frac(A^#[sh])
    $
    特别地，这两个环都是域。

  + 设 $A arrow.hook B$ 是正规局部整环的包含映射。则诱导的映射：
    $
      A^#[h] -> B^#[h], A^#[sh] -> B^#[sh]
    $
    都是包含映射。
]
#proof[
  (1) 由于局部化与正向极限交换，对极限部分，只需证明对每个带基点的平展邻域 $(Spec(B), frak(q)) -> (Spec(A), frak(m))$，都有 $S^(-1) B_(frak(q)) = Frac(B_(frak(q)))$。

  事实上，$S^(-1) B$ 是平展 $S^(-1) A = Frac(A)$-代数，因而必定是 $S^(-1) A$ 的有限多个有限可分扩张的乘积。于是作为 $S^(-1) B$ 的局部化，$S^(-1) B_(frak(q))$ 是有限多个域的乘积。然而 $B_(frak(q))$ 是整环，所以 $S^(-1) B_(frak(q))$ 也是整环。因此 $S^(-1) B_(frak(q))$ 必定是域。下面用到一个事实：

  - 若 $A$ 是整环，$S subset A - {0}$ 是乘法子集，且 $S^(-1) A$ 是域，则 $S^(-1) A = Frac(A)$。

    事实上，每个元素 $0 != a in A subset S^(-1) A$ 在 $S^(-1) A$ 中都有逆元。于是 $a^(-1) in S^(-1) A$，从而 $S^(-1) A$ 包含整个 $Frac(A)$。

  因此 $S^(-1) B_(frak(q)) = Frac(B_(frak(q)))$，两个极限断言都得证。现在 $S^(-1) A^#[h], S^(-1) A^#[sh]$ 都是域；再次应用上述事实，它们分别是 $Frac(A^#[h]), Frac(A^#[sh])$。

  (2) 令 $S = A - {0}$。注意 $S^(-1) A^#[h] -> S^(-1) B^#[h]$ 是单射，因为 $S^(-1) A^#[h] = Frac(A^#[h])$ 是域。由于 $A$ 是整环，$A^#[h] -> S^(-1) A^#[h]$ 是单射。于是映射：
  $
    A^#[h] -> S^(-1) B^#[h]
  $
  是单射。因此 $A^#[h] -> B^#[h]$ 是单射。严格 Hensel 化的情形同理。
]

#lemma(name: <henselization-and-finite-base-change>)[
  设 $(A, frak(m))$ 是剩余域为 $k$ 的局部环，$B$ 是有限 $A$-代数。设 $frak(q)_1, dots.c, frak(q)_m in Spec(B)$ 是 $B$ 中位于 $frak(m) in Spec(A)$ 之上的全部素理想。则：
  $
    B otimes_A A^#[h] cong product_(i=1)^m B_(frak(q)_i)^#[h]
  $
]
#proof[
  令 $C = B otimes_A A^#[h]$。则：
  
  - 由 @equiv-defns-of-henselian (1)，$Spec(C\/frak(m) C)$ 的点与 $Spec(C)$ 的连通分支一一对应；

  - 按定义，$C\/frak(m) C cong B\/frak(m) B$。设 $frak(n)_1, dots.c, frak(n)_m in Spec(C)$ 分别位于 $frak(q)_1, dots.c, frak(q)_m$ 之上。

  则：
  $
    C cong C_(frak(n)_1) times dots.c times C_(frak(n)_m)
  $
  其中每个因子都是 Hensel 的。沿 $Spec(C) -> Spec(B)$ 有自然映射 $B_(frak(q)_i) -> C_(frak(n)_i)$；于是由 Hensel 化的泛性质，有自然映射：
  $
    B_(frak(q)_i)^#[h] -> C_(frak(n)_i)
  $
  反之，由 Hensel 化的泛性质，存在局部映射 $A^#[h] -> B_(frak(q)_i)^#[h]$。于是有映射：
  $
    C = B otimes_A A^#[h] -> B_(frak(q)_i)^#[h] otimes_A B_(frak(q)_i)^#[h] -> B_(frak(q)_i)^#[h]
  $
  可以验证 $frak(n)_i$ 位于目标环的极大理想之上。于是上述映射诱导映射 $C_(frak(n)_i) -> B_(frak(q)_i)^#[h]$。由泛性质形式地可知，该映射是上面构造的映射 $B_(frak(q)_i)^#[h] -> C_(frak(n)_i)$ 的逆。
]

#lemma(name: <strict-henselization-and-finite-base-change>)[
  设 $(A, frak(m))$ 是剩余域为 $k$ 的局部环，$B$ 是有限 $A$-代数。设 $frak(q)_1, dots.c, frak(q)_m in Spec(B)$ 是 $B$ 中位于 $frak(m) in Spec(A)$ 之上的全部素理想。
  
  设 $k -> Omega$ 是 $k$ 到某个代数闭域的包含映射。对每个 $frak(q)_i$，令 $phi_(i,j): k(frak(q)_i) -> Omega$ 取遍与 $k -> Omega$ 相容的所有包含映射。令：

  - $A^#[sh]$ 为 $A$ 相对于包含映射 $k -> k^sep$ 的严格 Hensel 化，其中 $k^sep$ 是 $Omega$ 中由 $k$ 上全体可分代数元组成的子域；

  - $B_(frak(q)_i)^(#[sh],j)$ 为 $B_(frak(q)_i)$ 相对于包含映射 $k(frak(q)_i) -> k(frak(q)_i)^sep -> Omega$ 的严格 Hensel 化，其中 $k(frak(q)_i)^sep$ 是 $Omega$ 中由 $k(frak(q)_i)$ 上全体可分代数元组成的子域。

  则：
  $
    B otimes_A A^#[sh] cong product_(i,j) B_(frak(q)_i)^(#[sh],j)
  $
]
#proof[
  令 $C = B otimes_A A^#[sh]$。它的特殊纤维是：
  $
    C\/frak(m) C cong B otimes_A k^sep.
  $
  这个纤维的点自然地以数对 $(i,j)$ 为指标：对应于 $(i,j)$ 的点是由 $phi_(i,j)$ 诱导的映射的核，
  $
    k(frak(q)_i) otimes_k k^sep -> Omega.
  $
  设 $frak(n)_(i,j)$ 是 $C$ 中相应的素理想。由于 $A^#[sh]$ 是 Hensel 的，@equiv-defns-of-henselian (1) 给出：
  $
    C cong product_(i,j) C_(frak(n)_(i,j)).
  $
  每个因子都是 Hensel 的，其剩余域是合成域 $phi_(i,j)(k(frak(q)_i)) k^sep subset Omega$。它是可分闭域 $k^sep$ 的纯不可分扩张，因而也可分闭。于是每个 $C_(frak(n)_(i,j))$ 都是严格 Hensel 的。

  自然局部映射 $B_(frak(q)_i) -> C_(frak(n)_(i,j))$ 与选定的到 $Omega$ 的嵌入相容，故由严格 Hensel 化的泛性质得到映射：
  $
    B_(frak(q)_i)^(#[sh],j) -> C_(frak(n)_(i,j)).
  $

  反之，选定的包含映射 $k^sep subset k(frak(q)_i)^sep subset
  Omega$ 给出局部映射 $A^#[sh] -> B_(frak(q)_i)^(#[sh],j)$。连同
  $B -> B_(frak(q)_i)^(#[sh],j)$，它诱导出：
  $
    C = B otimes_A A^#[sh] -> B_(frak(q)_i)^(#[sh],j),
  $
  该映射在 $frak(n)_(i,j)$ 处局部化。由这两个泛性质，所得的映射互为逆。取它们的乘积即得断言。
]
