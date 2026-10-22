#import "void-import.typ": *

== Weierstrass 整除性归纳

现在可以用归纳法完成证明了。不过在此之前，还要做一些最后的准备，以便利用由 Néron 光滑化得到的行列式条件。

据 @cite-Art69，下面这个引理归功于 Tougeron。

#lemma[
  设 $(A, frak(m))$ 是 Hensel 局部环，$f_1, dots.c, f_(m-d) in A[Y_1,dots.c,Y_m]$，$arrow(y^0) in A^m$。记：
  $
    J = J_f (arrow(y^0)): A^m -> A^(m-d), e_i |-> sum_(j=1)^(m-d) (partial f_j)/(partial Y_i) e_j
  $
  于是 $J in MM_((m-d) times m) (A)$。

  设 $Delta = (d_1, dots.c, d_s)$ 是包含在零化子 $"ann"_A (coker(J))$ 中的有限生成理想。若：
  $
    f_1 (arrow(y^0)), dots.c, f_(m-d) (arrow(y^0)) in Delta^2 frak(m)
  $
  则存在 $arrow(y) in A^m$，使得：
  $
    f_1 (arrow(y)) = dots.c = f_(m-d) (arrow(y)) = 0 \

    arrow(y) - arrow(y^0) in Delta frak(m) dot A^m
  $
]
#proof[
  对每个 $i$，$A^(m-d)$ 上乘以 $d_i$ 的映射穿过 $J$ 分解。因此存在 $N_i in MM_(m times (m-d)) (A)$，使得：
  $
    J N_i = d_i I_(m-d)
  $
  记 $arrow(f)(arrow(y^0)) = sum_(i,j) d_i d_j arrow(epsilon)_(i,j)$，其中 $arrow(epsilon)_(i,j) in frak(m) dot A^(m-d)$。

  引入未定元矩阵 $U = display(mat(U_(i,j))_(i<=m,j<=s))$。令 $arrow(d) = (d_1,dots.c,d_s) in A^s$。由 Taylor 展开：
  $
    arrow(f)(arrow(y^0) + U arrow(d)) = arrow(f)(arrow(y^0)) + J U arrow(d) + sum_(i,j) d_i d_j arrow(Q)_(i,j) (U)
  $
  其中 $arrow(Q)_(i,j) (U)$ 的每个单项式的次数都 $>=2$。利用 $arrow(f)(arrow(y^0)) = sum_(i,j) d_i d_j arrow(epsilon)_(i,j)$ 与 $J N_i = d_i I_(m-d)$ 重写，得到：
  $
    arrow(f)(arrow(y^0) + U arrow(d)) = sum_(i=1)^s d_i J (underbrace(mat(U_(1,i); dots.v; U_(m,i)), arrow(U)_i) + sum_(j=1)^s N_j (arrow(Q)_(i,j) (U) + arrow(epsilon)_(i,j)))
  $
  因此，为求出解 $arrow(y)$，只需解方程组 $arrow(Phi)(U) = 0$，其中：
  $
    arrow(Phi)_i (U) := arrow(U)_i + sum_(j=1)^s N_j (arrow(Q)_(i,j) (U) + arrow(epsilon)_(i,j))
  $
  考虑多项式映射：
  $
    Phi: MM_(m times s) (A) -> MM_(m times s) (A), U |-> mat(arrow(Phi)_1 (U), dots.c, arrow(Phi)_s (U))
  $
  此时 $arrow(Phi)_i (0) = sum_(j=1)^s N_j arrow(epsilon)_(i,j)$ 中每个系数都落在 $frak(m)$ 中。此外，由于 $arrow(Q)_(i,j)$ 的每一项次数都 $>=2$，有微分 $d Phi(0) = id$。剩下只需引用下面的引理：

  #lemma[
    设 $(A, frak(m))$ 是 Hensel 局部环，且：
    $
      Phi: A^n -> A^n
    $
    是多项式映射，满足 $Phi(0) in frak(m) dot A^n$ 且 $d Phi(0) = id$。则 $Phi$ 在 $frak(m) dot A^n$ 中有解。
  ]
  #proof[
    取：
    $
      R = (A[T_1, dots.c, T_n])/((Phi_1 (T_1, dots.c, T_n), dots.c, Phi_n (T_1, dots.c, T_n)))
    $
    由于 $d Phi(0) = id$，Jacobi 矩阵 $J = display(mat(nabla Phi_1, dots.c, nabla Phi_n))$ 形如 $I_n + K$，其中 $K in (T_1, dots.c, T_n) dot MM_(n times n) (A[T_1, dots.c, T_n])$。因此 $J$ 在 $(frak(m), T_1, dots.c, T_n)$ 处局部化后可逆。于是存在 $h in A[T_1, dots.c, T_n] - (frak(m), T_1, dots.c, T_n)$，使得：
    $
      R_h = (A[T_1, dots.c, T_n]_h)/((Phi_1 (T_1, dots.c, T_n), dots.c, Phi_n (T_1, dots.c, T_n)))
    $
    是平展 $A$-代数，这里用到 @jacobian-criterion-for-etaleness。现在 $Phi(0) in frak(m) dot A^n$ 说明零截面就是截面 $Spec(k) -> Spec(R_h\/frak(m) R_h)$。由 @equiv-defns-of-henselian (4)，它提升为截面 $Spec(A) -> Spec(R_h)$，从而给出 $Phi = 0$ 的一个解，且该解模 $frak(m)$ 约化为 $0$。
  ]
]

#corollary(name: <jacobian-correction>)[
  设 $(A, frak(m))$ 是 Noether 的 Hensel 局部环，$f_1, dots.c, f_(m-d) in A[Y_1,dots.c,Y_m]$，$arrow(y^0) in A^m$。记：
  $
    J = J_f (arrow(y^0)): A^m -> A^(m-d), e_i |-> sum_(j=1)^(m-d) (partial f_j)/(partial Y_i) e_j
  $
  于是 $J in MM_((m-d) times m) (A)$。设 $d_0 in A$ 是 $J$ 的前 $m-d$ 列的行列式。若对 $N >= 0$ 有：
  $
    f_1 (arrow(y^0)), dots.c, f_(m-d) (arrow(y^0)) in d_0^2 frak(m)^(2N+1)
  $
  则存在 $arrow(y) in A^m$，使得：
  $
    f_1 (arrow(y)) = dots.c = f_(m-d) (arrow(y)) = 0 \

    arrow(y) - arrow(y^0) in d_0 frak(m)^(N+1) dot A^m
  $
]
#proof[
  我们想对 $Delta = d_0 frak(m)^N$ 应用上一个引理；只需证明 $d_0$ 零化 $coker(J)$。事实上，设 $M$ 是 $J$ 的前 $m-d$ 列，$M^*$ 是这一方阵的伴随矩阵。给 $M^*$ 补上 $d$ 行零得到 $N$，于是：
  $
    J N = d_0 I_(m-d)
  $
]

#lemma(name: <jacobian-improvement>)[
  沿用 @artin-approx-smoothing-reduction-2 (2) 的设定。令：
  $
    d_0 = "ord"_(frak(m)_n) (delta(arrow(X), hat(y))) < +oo
  $
  若 $N >= 2d_0 + 1$，且 $arrow(y^0) in A_n^m$ 满足 $arrow(y^0) = hat(y) mod frak(m)_n^N hat(A_n)$，并且：
  $
    arrow(f) (arrow(X), arrow(y^0)) in delta(arrow(X), arrow(y^0))^2 dot A_n^r
  $
  则：
  $
    arrow(f) (arrow(X), arrow(y^0)) in delta(arrow(X), arrow(y^0))^2 frak(m)_n^(N-2d_0) dot A_n^r
  $
]
#proof[
  由于 $N > d_0$，有 $delta(arrow(X), hat(y)) mod frak(m)_n^N = delta(arrow(X), arrow(y^0)) mod frak(m)_n^N$，从而 $"ord"_(frak(m)_n) (delta(arrow(X), arrow(y^0))) = d_0$。

  同样，由于 $arrow(f)(arrow(X), hat(y)) = 0$，有 $arrow(f) (arrow(X), arrow(y^0)) in frak(m)_n^N dot A_n^r$。

  由于 $A_n$ 是正则局部环，由 #cite-stacks("061P")[Definition 10.69.1] 与 #cite-stacks("00LN")[Lemma 10.69.2]，其分次代数是 $k(A_n) = k$ 上的多项式环。因此，关于 $frak(m)_n$ 的阶对乘积可加。记 $f_i (arrow(X), arrow(y^0)) = delta(arrow(X), arrow(y^0))^2 q_i$，则：
  $
    "ord"_(frak(m)_n) (q_i) = "ord"_(frak(m)_n) (f_i (arrow(X), arrow(y^0))) - 2 d_0 >= N - 2d_0
  $
]

现在可以开始归纳了。下面的引理是 Artin 的引理 5.12。

#lemma(name: <weierstrass-divisibility-induction>)[
  （Weierstrass 整除性）假设对所有 $i < n$，$A_i$ 上的 Artin 逼近成立。设：
  $
    g, f_1, dots.c, f_r in R[X_1, dots.c, X_n, Y_1, dots.c, Y_m]
  $
  并设 $hat(y) in hat(A_n)^m$ 满足：
  $
    g(arrow(X), hat(y)) in hat(A_n) - pi.alt hat(A_n) \

    f_i (arrow(X), hat(y)) in g(arrow(X), hat(y)) hat(A_n), forall 1 <= i <= r
  $
  则对每个 $N >= 1$，存在 $arrow(y) in A_n^m$，它与 $hat(y)$ 模 $frak(m)_n^N$ 一致，且满足：
  $
    f_i (arrow(X), arrow(y)) in g(arrow(X), arrow(y)) A_n, forall 1 <= i <= r
  $
]
#proof[
  记 $H = g(arrow(X), hat(y)) in hat(A_n)$。若 $H$ 是 $hat(A_n)$ 中的单位，则与 $hat(y)$ 足够接近的任意 $arrow(y)$ 都使 $g(arrow(X), arrow(y)) in A_n^times$，此时所需条件自动成立。特别地，$n = 0$ 时结论自动成立。于是不妨设 $n >= 1$，且 $H in frak(m)_n hat(A_n) - pi.alt hat(A_n)$。

  记 $arrow(X)' = (X_1, dots.c, X_(n-1))$，$T = X_n$。

  - $ol(H) in k fps(arrow(X)'\, T)$ 是 $H$ 的约化，且非零。我们断言存在 $e_1, dots.c, e_(n-1) in NN$，使得在施加自同构
    $
      T |-> T, X_i |-> X_i + T^(e_i), i < n
    $
    后，有 $ol(H)(0, dots.c, 0, T) != 0$。换言之，我们要的是 $ol(H)(T^(e_1), dots.c, T^(e_(n-1)), T) != 0$。记：
    $
      ol(H)(arrow(X)) = sum_(alpha in NN^n) c_alpha arrow(X)^alpha
    $
    设 $S = {alpha in NN^n : c_alpha != 0}$，并设 $alpha_0 = (a_1, dots.c, a_n)$ 是其中字典序最小的元素，坐标按 $X_1, dots.c, X_(n-1), T$ 的顺序比较。令 $e_n = 1$，并递归地令：
    $
      e_i = 1 + sum_(j=i+1)^n e_j a_j,
      quad i = n-1, dots.c, 1.
    $
    令：
    $
      w(alpha) = sum_(i=1)^n e_i alpha_i.
    $
    我们断言 $alpha_0$ 是 $S$ 中唯一具有最小权的元素。事实上，若 $beta in S$ 且 $beta != alpha_0$，设 $i$ 是第一个满足 $beta_i != a_i$ 的指标。由 $alpha_0$ 的选取，有 $beta_i > a_i$，因此：
    $
      w(beta) - w(alpha_0)
      = sum_(j=i)^n e_j (beta_j - a_j) >= e_i - sum_(j=i+1)^n e_j a_j = 1.
    $
    由于每个 $e_i$ 都为正，上述形式代换是良定义的。于是：
    $
      ol(H)(T^(e_1), dots.c, T^(e_(n-1)), T)
      = c_(alpha_0) T^(w(alpha_0))
        + O(T^(w(alpha_0) + 1))
      != 0.
    $

  三角自同构 $T |-> T, X_i |-> X_i + T^(e_i)$ 固定 $(pi.alt, X_1, dots.c, X_(n-1), T)$，从而固定 $frak(m)_n$ 与 $frak(m)_n hat(A_n)$。因此，对方程组与解施加这样的三角自同构，最后再对解作用它的逆，便可假设 $ol(H)(0, dots.c, 0, T) != 0$。

  令：
  $
    B = hat(A_(n-1)) = hat(R) fps(X_1\, dots.c\, X_(n-1)) \
    frak(b) = (pi.alt, X_1, dots.c, X_(n-1)) B
  $
  于是 $hat(A_n) = B fps(T)$，且 $B\/frak(b) cong k$。由于 $ol(H)(0, dots.c, 0, T) != 0$，由此可以断定 $H != 0 in B\/frak(b) fps(T)$。
  #lemma[
    （形式 Weierstrass 预备定理）设 $(A, frak(m))$ 是完备局部环，$H(T) in A fps(T)$，且 $H(T) mod frak(m) in k fps(T)$ 非零。则存在 $d in NN$、$a_0, dots.c, a_(d-1) in frak(m)$ 以及 $u in A fps(T)^times$，使得：
    $
      H(T) = u(T) (T^d + a_(d-1) T^(d-1) + dots.c + a_0)
    $
  ]
  #proof[
    设 $d$ 是 $H(T) mod frak(m) in k fps(T)$ 关于 $T$ 的阶（该级数已知非零）。则：
    $
      H(T) = sum_(j>=0) h_j T^j
    $
    其中：
    $
      h_0, dots.c, h_(d-1) in frak(m), h_d in A^times
    $
    令 $G(T) = sum_(j>=d) h_j T^(j-d)$。由于 $h_d in A^times$，有 $G(T) in A fps(T)^times$。于是：
    $
      H(T) = G(T) dot (T^d + G(T)^(-1) sum_(j=0)^(d-1) h_j T^j)
    $
    这里每个 $h_j in frak(m)$，故 $r(T) = G(T)^(-1) sum_(j=0)^(d-1) h_j T^j in frak(m) fps(T)$。只需对 $r(T)$ 做同样的分解。
    
    对每个 $f = sum_(j>=0) f_j T^j in A fps(T)$，记：
    $
      pi(f) = sum_(j=0)^(d-1) f_j T^j, sigma(f) = sum_(j>=d) f_j T^j
    $
    令 $D = A[T]_(<d)$ 为 $A$ 上次数 $<d$ 的多项式构成的 $A$-模。现在要寻找 $q in frak(m) A fps(T), a in frak(m) D$，使得：
    $
      T^d + r(T) = (1 + q(T))(T^d + a(T))
    $
    即 $r(T) = T^d q(T) + a(T) + a(T) q(T)$。也就是说，需要解：
    $
      a = pi(r - a q), q = sigma(r - a q)
    $
    令 $Phi(a, q) = (pi(r - a q), sigma(r - a q))$，其中 $q in frak(m) A fps(T), a in frak(m) D$。则 $Phi$ 在 $frak(m) D times frak(m) A fps(T)$ 上关于 $frak(m)$-进度量是压缩映射：

    - 若 $(a, q) equiv (a', q') mod frak(m)^N$，则：#h(1fr)
      $
        a q - a' q' = a(q - q') + (a - a')q' in frak(m)^(N+1) A fps(T)
      $
      于是 $(r - a q) - (r - a' q') in frak(m)^(N+1) A fps(T)$，从而：
      $
        pi(r - a q) - pi(r - a' q') in frak(m)^(N+1) D \
        sigma(r - a q) - sigma(r - a' q') in frak(m)^(N+1) A fps(T)
      $

    由 Banach–Picard 不动点迭代法，$Phi$ 有不动点，证毕。
  ]

  由这个引理，可把 $H$ 分解为：
  $
    H = hat(u) hat(a) \
    hat(u) in hat(A_n)^times \
    hat(a) = T^d + sum_(i=0)^(d-1) hat(a)_i (arrow(X')) T^i, hat(a)_i in frak(b)
  $

  现在用首一多项式 $hat(a)$ 对 $hat(y) in hat(A_n) = B fps(T)$ 的每个分量做长除法：
  $
    hat(y)_i (T) = hat(a) (T) hat(q)_i (T) + hat(y)_i^* (T), hat(y)_i^* (T) = sum_(s=0)^(d-1) hat(y)_(i,s) T^s
  $

  - 引入未定元 $A_0, dots.c, A_(d-1)$ 与 $Z_(i,s)$，并令：#h(1fr)
    $
      P(T) = T^d + sum_(s=0)^(d-1) A_s T^s \
      Z^*_i (T) = sum_(s=0)^(d-1) Z_(i,s) T^s
    $
    在环 $R[arrow(X'), T, arrow(A), arrow(Z)]$ 中可以用首一多项式 $P(T)$ 做长除法。于是可以写成：
    $
      g(arrow(X'), T, Z^*_1 (T), dots.c, Z^*_m (T)) = P Q_g + sum_(s=0)^(d-1) G_s T^s \

      f_i (arrow(X'), T, Z^*_1 (T), dots.c, Z^*_m (T)) = P Q_i + sum_(s=0)^(d-1) F_(i,s) T^s
    $
    其中 $Q_g, Q_i in R[arrow(X'), T, arrow(A), arrow(Z)]$，$G_s, F_(i,s) in R[arrow(X'), arrow(A), arrow(Z)]$。

  - 现在代入 $A_s = hat(a)_s, Z_(i,s) = hat(y)^*_(i,s)$，则这些关系式变为：
    $
      g(arrow(X'), T, hat(y)^*_1, dots.c, hat(y)^*_m) = hat(a) Q_g (arrow(X'), {hat(a)_s}, {hat(y)^*_(i,s)}) + sum_(s=0)^(d-1) G_s (arrow(X'), {hat(a)_s}, {hat(y)^*_(i,s)}) T^s \
      f_i (arrow(X'), T, hat(y)^*_1, dots.c, hat(y)^*_m) = hat(a) Q_i (arrow(X'), {hat(a)_s}, {hat(y)^*_(i,s)}) + sum_(s=0)^(d-1) F_(i,s) (arrow(X'), {hat(a)_s}, {hat(y)^*_(i,s)}) T^s
    $
    同时，$hat(y)_i equiv hat(y)_i^* mod hat(a)$。因此，由整除链 $hat(a) divides H = g(arrow(X), hat(y)) divides f_i (arrow(X), hat(y))$ 可得：
    $
      g(arrow(X), hat(y)) equiv f_i (arrow(X), hat(y)) equiv 0 mod hat(a)
    $
    于是在 $hat(A_n)\/hat(a)$ 中计算，得到：
    $
      g(arrow(X), hat(y)^*) equiv f_i (arrow(X), hat(y)^*) equiv 0 mod hat(a)
    $
    因此，用首一多项式 $hat(a)$ 做长除法的唯一性给出：
    $
      G_s (arrow(X'), {hat(a)_s}, {hat(y)^*_(i,s)}) = F_(i,s) (arrow(X'), {hat(a)_s}, {hat(y)^*_(i,s)}) = 0
    $
    其中 $hat(a)_s, hat(y)^*_(i,s) in hat(A_(n-1))$。

  - 由归纳假设，对每个 $N >= 1$，存在真正的解 $a_s, y^*_(i,s) in A_(n-1)$，它们与形式解 $hat(a)_s, hat(y)^*_(i,s)$ 模 $frak(m)_(n-1)^N$ 一致，且满足：
    $
      G_s (arrow(X'), {a_s}, {y^*_(i,s)}) = F_(i,s) (arrow(X'), {a_s}, {y^*_(i,s)}) = 0
    $
    特别地，$a_s in frak(m)_(n-1)$。令：
    $
      a(T) = T^d + sum_(s=0)^(d-1) a_s T^s in A_(n-1) [T] subset A_n \

      y_i^* (T) = sum_(s=0)^(d-1) y^*_(i,s) T^s in A_(n-1) [T] subset A_n
    $
    由稠密性，可以选取 $q_i in A_n$，使得 $q_i equiv hat(q)_i mod frak(m)_n^N$。现在令：
    $
      y_i = a q_i + y_i^*
    $
    则：
    $
      y_i - hat(y)_i = a (q_i - hat(q)_i) + (a - hat(a)) hat(q)_i + (y_i^* - hat(y)_i^*) in frak(m)_n^N hat(A_n)
    $
    从而 $arrow(y) - hat(y) in frak(m)_n^N dot (hat(A_n))^m$。

  - 由于：
    $
      G_s (arrow(X'), {a_s}, {y^*_(i,s)}) = F_(i,s) (arrow(X'), {a_s}, {y^*_(i,s)}) = 0
    $
    把 $A_s = a_s, Z_(i,s) = y^*_(i,s)$ 代入余式方程，便得到：
    $
      g(arrow(X), arrow(y)) in a A_n \
      f_i (arrow(X), arrow(y)) in a A_n
    $

  - 记 $g(arrow(X), arrow(y)) = a v$，其中 $v in A_n$。此时 $y equiv hat(y) mod frak(m)_n^N$，故
    $
      g(arrow(X), arrow(y)) - g(arrow(X), hat(y)) in frak(m)_n^N hat(A_n)
    $
    取把 $pi.alt$ 与 $arrow(X')$ 都映为零的映射 $rho: hat(A_n) -> k fps(T)$，用它约化上式。此时 $frak(m)_n^N$ 映到 $(T^N)$。因此，只要 $N > d = "ord"_T (rho(g(arrow(X'), hat(y))))$，就有
    $
      "ord"_T (rho(g(arrow(X), arrow(y)))) = d
    $
    另一方面，$a$ 作为 $T$ 的多项式是首一的、次数为 $d$，故 $"ord"_T (rho(a)) = d$。再利用 $g(arrow(X), arrow(y)) = a v$，得到：
    $
      "ord"_T (rho(v)) = "ord"_T (rho(g(arrow(X), arrow(y)))) - "ord"_T (rho(a)) = d - d = 0
    $
    于是 $v in A_n$ 不在该环的极大理想中，故 $v in A_n^times$。因此 $(g(arrow(X), arrow(y))) = (a) subset A_n$。再由 $f_i (arrow(X), arrow(y)) in a A_n$ 便得到所要的整除性。
]

#proposition(name: <artin-approx-core-conclusion>)[
  在 @artin-approx-smoothing-reduction-2 (2) 的设定下，对方程组 $f_1, dots.c, f_(m-d)$ 与解 $hat(y)$，Artin 逼近成立。
]
#proof[
  固定所需的逼近阶 $N$，令：
  $
    d_0 = "ord"_(frak(m)_n) (delta(arrow(X), hat(y)))
  $
  令 $g(arrow(X), arrow(Y)) = delta(arrow(X), arrow(Y))^2$。则：
  $
    g(arrow(X), hat(y)) in hat(A_n) - pi.alt hat(A_n) \
    f_i (arrow(X), hat(y)) = 0 in g(arrow(X), hat(y)) hat(A_n)
  $
  于是由 @weierstrass-divisibility-induction，存在 $arrow(y^0) in A_n^m$，它与 $hat(y)$ 模 $frak(m)_n^(2N+2d_0+10)$ 一致，且满足：
  $
    f_i (arrow(X), arrow(y^0)) in delta(arrow(X), arrow(y^0))^2 A_n
  $
  再由 @jacobian-improvement，得
  $
    f_i (arrow(X), arrow(y^0)) in delta(arrow(X), arrow(y^0))^2 frak(m)_n^(2N+1) A_n
  $
  于是由 @jacobian-correction，存在 $arrow(y) in A_n^m$，它与 $arrow(y^0)$（从而与 $hat(y)$）模 $frak(m)_n^(N+1)$ 一致，且满足：
  $
    f_i (arrow(X), arrow(y)) = 0
  $
  这样我们就找到了 $N+1$ 阶的逼近。证毕。
]

至此，我们完成了 Artin 逼近定理的证明。

#theorem(name: <artin-approximation-theorem>)[
  （Artin 逼近定理）设 $A$ 如下得到：取任意域上或优良离散赋值环上的有限型代数，再在任意素理想处作 Hensel 化。则：

  + 给定多项式方程组 $f_1, dots.c, f_r in A[Y_1, dots.c, Y_m]$，假设存在形式解 $hat(y)_1, dots.c, hat(y)_m in hat(A)$，即：
    $
      f_1 (hat(y)_1, dots.c, hat(y)_m) = dots.c = f_r (hat(y)_1, dots.c, hat(y)_m) = 0
    $
    则对每个 $N >= 1$，存在真正的解 $y_1, dots.c, y_m in A$，使得：
    $
      f_1 (y_1, dots.c, y_m) = dots.c = f_r (y_1, dots.c, y_m) = 0
    $
    且每个 $hat(y)_i equiv y_i (mod frak(m)^N)$。

  + 对任意与正向极限交换的函子 $F: AAlg(A) -> cSet$、任意 $N >= 1$ 以及任意元素 $hat(xi) in F(hat(A))$，都存在元素 $xi in F(A)$，使得 $hat(xi)$ 与 $xi$ 在 $F(A\/frak(m)^N)$ 中有相同的像。
]
#proof[
  把 @artin-approx-and-finitely-presented-functors、@artin-approx-reduce-to-std、@artin-approx-smoothing-reduction-2 与 @artin-approx-core-conclusion 综合起来，即得结论。
]
