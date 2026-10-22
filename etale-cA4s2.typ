#import "void-import.typ": *

== Néron 光滑化

我们先介绍本节的设定。

#notation(name: <situation-neron-smoothing>)[
  本节始终假定 $V subset V'$ 是 DVR 的扩张，且一致化元 $pi.alt in V$ 在 $V'$ 中仍是一致化元。

  $V -> V'$ 将分解为：
  $
    V arrow.hook D ->^phi V'
  $
  其中 $D$ 是某个有限型平坦 $V$-代数。令：
  $
    frak(q) = ker(phi) in Spec(D) \
    frak(p) = phi^(-1) (pi.alt V') in Spec(D)
  $
  它们是 $Spec(V')$ 的泛点与特殊点在 $Spec(D)$ 中的像。
]

#definition(name: <defn-affine-neron-blowup>)[
  $D$ 沿 $phi$ 的*仿射 Néron 爆破*定义为如下代数：
  $
    D^+ := D[pi.alt^(-1) frak(p)] subset D[pi.alt^(-1)]
  $
  等价地，若 $(pi.alt, g_1, dots.c, g_t)$ 是 $frak(p)$ 的一组生成元，则 $D^+$ 同构于 $D[Z_1,dots.c,Z_t]\/(pi.alt Z_1 - g_1, dots.c, pi.alt Z_t - g_t)$，再模去所有 $pi.alt^oo$-挠元。

  我们有交换图表：
  // https://q.uiver.app/#r=typst&q=WzAsNCxbMCwxLCJWIl0sWzEsMCwiRCJdLFsxLDIsIkReKyJdLFsyLDEsIlYnIl0sWzEsMl0sWzAsMSwiIiwwLHsic3R5bGUiOnsidGFpbCI6eyJuYW1lIjoiaG9vayIsInNpZGUiOiJ0b3AifX19XSxbMCwyLCIiLDIseyJzdHlsZSI6eyJ0YWlsIjp7Im5hbWUiOiJob29rIiwic2lkZSI6InRvcCJ9fX1dLFsxLDMsInBoaSJdLFsyLDMsInBoaV4rIl1d
  #align(center, diagram({
    node((0, 0), [$V$])
    node((1, -1), [$D$])
    node((1, 1), [$D^+$])
    node((2, 0), [$V'$])
    edge((1, -1), (1, 1), "->")
    edge((0, 0), (1, -1), "hook->")
    edge((0, 0), (1, 1), "hook->")
    edge((1, -1), (2, 0), [$phi$], label-side: left, "->")
    edge((1, 1), (2, 0), [$phi^+$], label-side: right, "->")
  }, spacing: (3em, 2em)))
  其中 $phi^+$ 由 $Z_i |-> pi.alt^(-1) phi(g_i)$ 定义。容易验证，这个定义与 $frak(p)$ 的生成元的选取无关。于是可以取：
  $
    frak(q)^+ = ker(phi^+), frak(p)^+ = (phi^+)^(-1) (pi.alt V')
  $
]

#properties(name: <neron-blowup-first-props>)[
  仿射 Néron 爆破满足：

  + $D[pi.alt^(-1)] cong D^+ [pi.alt^(-1)]$；

  + 对任意 $f in D - frak(p)$，都有 $phi(f) in.not pi.alt V'$，因此它在 $V'$ 中可逆。于是有自然映射 $phi_f: D_f -> V'$。此时：#h(1fr)
    $
      (D^+)_f cong (D_f)^+
    $
  
  + 给定满射 $rho: (E, psi) ->> (D, phi)$，其中 $(E, psi)$ 同样是 $V -> V'$ 的分解（同 @situation-neron-smoothing），并令 $J = ker(rho) subset E$，则
    $
      D^+ cong E^+/((J E^+ : pi.alt^oo)) cong (E^+\/J E^+)/(T_(pi.alt^oo) (E^+\/J E^+))
    $
    其中 $(J : pi.alt^oo)$ 是 $J$ 的 $pi.alt^oo$-饱和化，$T_(pi.alt^oo)$ 表示取 $pi.alt^oo$-挠部分。
]
#proof[
  (1) 由于每个 $Z_i$ 都等同于 $pi.alt^(-1) g_i$，有
  $
    D^+ [pi.alt^(-1)] &cong D[Z_1,dots.c,Z_t,pi.alt^(-1)]/((pi.alt Z_1 - g_1, dots.c, pi.alt Z_t - g_t))\ 
    &cong D[pi.alt^(-1)]
  $

  (2) 作为 $D[f^(-1), pi.alt^(-1)]$ 的子集，有
  $
    (D_f)^+ = (D^+)_f = D[f^(-1), pi.alt^(-1) frak(p)]
  $

  (3) 可以取 $D = E\/J$。现在取生成元 $(pi.alt, g_1, dots.c, g_t) = frak(p)_E$。则：
  $
    frak(p)_D = (pi.alt, g_1, dots.c, g_t)\/J
  $
  它同样以这组元素为生成元。现在：
  $
    E^+ cong E[Z_1,dots.c,Z_t]/(((pi.alt Z_1 - g_1, dots.c, pi.alt Z_t - g_t) : pi.alt^oo)) \

    D^+ cong D[Z_1,dots.c,Z_t]/(((pi.alt Z_1 - g_1, dots.c, pi.alt Z_t - g_t) : pi.alt^oo)) cong E[Z_1,dots.c,Z_t]/((J + (pi.alt Z_1 - g_1, dots.c, pi.alt Z_t - g_t) : pi.alt^oo))
  $
  于是经理想运算可得
  $
    D^+ cong E^+/((J E^+ : pi.alt^oo))
  $
]

仿射 Néron 爆破的用意在于：经过有限多次 Néron 爆破，可以让 $D$ 在 $frak(p)$ 处是 $V$ 上光滑的。为此，我们要证明每次爆破都使一个取值于自然数的缺陷测度严格下降。

#construction[
  假设 $D$ 在 $frak(q)$ 处是 $V$ 上光滑的，相对维数为 $d$。此时 $Omega_(D\/V)$ 是有限 $D$-模，故 $Omega_(D\/V) otimes_D V'$ 是有限 $V'$-模，从而有自由部分和 $pi.alt^oo$-挠部分。令 $Q_D = Omega_(D\/V) otimes_D V'$，并定义：
  $
    e(D, phi) := length_(V') (T_(pi.alt^oo) (Q_D))
  $

  取 $D$ 的一个 $V$-代数展示：
  $
    rho: E = V[T_1,dots.c,T_n] ->> D
  $
  并令 $J = ker(rho)$。则由第二正合列：
  $
    e(D, phi) = length_(V') (coker(J\/J^2 otimes_E V' -> Omega_(E\/V) otimes_E V'))
  $

  对位于 $y in Spec(V)$ 上方的点 $x in Spec(D)$，令：
  $
    rho(x) = dim_(k(x)) (Omega_(D\/V) otimes_D k(x)) \
    tau(x) = dim(cal(O)_(D_y,x)) + trd_(k(y))(k(x))
  $
  由 #cite-stacks("02FZ")[Lemma 29.29.4]，$tau$ 上半连续，故 $tau(frak(p)) >= tau(frak(q))$。

  现在由 @equiv-defns-of-smooth (1)，$D$ 在 $frak(q)$ 处光滑这一条件等价于 $d = rho(frak(q)) = tau(frak(q))$。又：
  $
    Omega_(D\/V) otimes_D k(frak(q)) otimes_(k(frak(q))) Frac(V') &cong Q_D otimes_(V') Frac(V') \
    Omega_(D\/V) otimes_D k(frak(p)) otimes_(k(frak(p))) k(V') &cong Q_D otimes_(V') k(V') \
  $ 
  因此，
  $
    rho(frak(q)) = d = "rk"_(V') (Q_D\/T_(pi.alt^oo) (Q_D))
  $
  这个公共值同时也是 $Q_D$ 的自由秩，并且：
  $
    rho(frak(p)) = d + e(D, phi)
  $
]

#lemma(name: <zero-defect-implies-smooth>)[
  若 $D$ 在 $frak(q)$ 处光滑且 $e(D, phi) = 0$，则 $D$ 在 $frak(p)$ 处光滑。
]
#proof[
  由于 $rho(frak(p)) = d + e(D, phi)$，代入 $e(D, phi) = 0$ 便得 $rho(frak(p)) = d$。又：
  $
    rho(frak(p)) = d = tau(frak(q)) <= tau(frak(p))
  $
  故由 @equiv-defns-of-smooth (1)，$D$ 在 $frak(p)$ 处光滑，且上述不等式取等号。
]

#proposition(name: <neron-smoothing-smoothness-pass>)[
  + 若 $D$ 在 $frak(q)$ 处是 $V$ 上光滑的，相对维数为 $d$，则 $D^+$ 在 $frak(q)^+$ 处是 $V$ 上光滑的，相对维数为 $d$；

  + 若 $D$ 在 $frak(p)$ 处是 $V$ 上光滑的，相对维数为 $d$，且 $k(V')\/k(V)$ 是可分扩张#footnote[非代数域扩张的可分性按 #cite-stacks("030O")[Definition 10.42.1] 的方式定义。]，则 $D^+$ 在 $frak(p)^+$ 处是 $V$ 上光滑的，相对维数为 $d$。

  + 在 (2) 的设定下，假定 $D cong V[T_1,dots.c,T_r]_s$ 是 $V$ 上多项式环的一个局部化。此时，必要时将 $s$ 换成 $V[T_1,dots.c,T_r] - frak(p)$ 中更大的元素，便有
    $
      Q_D &= Omega_(D\/V) otimes_D V' \
      Q_(D^+) &= Omega_(D^+\/V) otimes_(D^+) V'
    $
    这两个模 $Q_D, Q_(D^+)$ 都是 $V'$ 上秩为 $r$ 的自由模；而由第一正合列诱导的典范映射 $Q_D -> Q_(D^+)$ 在适当选取基之下，其矩阵为：
    $
      "diag"(pi.alt I_c, I_(r-c))
    $
    其中 $c = dim_(k(frak(p))) (D_(frak(p))\/pi.alt D_(frak(p)))$。
    
    于是可以认为 $pi.alt Q_(D^+) subset Q_D subset Q_(D^+)$，并且 $Q_(D^+)\/Q_D cong k(V')^(oplus c)$。
]
#proof[
  (1) 由 @equiv-defns-of-smooth (2) 可知，光滑性只取决于所选的纤维。现在 $D[pi.alt^(-1)] = D^+ [pi.alt^(-1)]$，故 $Spec(D)$ 与 $Spec(D^+)$ 在 $Spec(V)$ 上有相同的泛纤维。因此 $D$ 在 $frak(q)$ 处光滑蕴含 $D^+$ 在 $frak(q)^+$ 处光滑。

  (2) 由 @neron-blowup-first-props，可以把 $D$ 换成它在 $D - frak(p)$ 中某个元素处的适当局部化。

  令 $ol(frak(p)) = frak(p)\/pi.alt D in Spec(D\/pi.alt D)$。由于光滑性在基变换下保持，$D\/pi.alt D$ 在 $ol(frak(p))$ 处是 $k(V)$ 上光滑的。于是由 @equiv-defns-of-smooth (2)，$(D\/pi.alt D)_(ol(frak(p)))$ 是正则局部环。

  选取 $g_1, dots.c, g_c in frak(p)$，使它们在 $(D\/pi.alt D)_(ol(frak(p))) = D_(frak(p))\/pi.alt D_(frak(p))$ 中的像构成正则参数系。于是适当缩小 $D$（在 $frak(p)$ 附近）之后，有 $frak(p) = (pi.alt, g_1, dots.c, g_c)$。由平坦性，$pi.alt$ 是 $D_(frak(p))$ 中的非零因子，故 $pi.alt, g_1, dots.c, g_c$ 是 $D_(frak(p))$ 中的正则序列。于是再在 $frak(p)$ 附近缩小 $D$，便可假定 $pi.alt, g_1, dots.c, g_c$ 是 $D$ 中的正则序列。

  归纳地应用下面这个引理：
  #lemma[
    若 $a$ 是 $A$ 中的非零因子，且 $b in A$ 在 $A\/a$ 中是非零因子，则 $a$ 是 $A[Z]\/(a Z - b)$ 中的非零因子。
  ]
  #proof[
    若对某个 $f(Z), g(Z) in A[Z]$ 有 $a f(Z) = (a Z - b) g(Z)$，则模 $a$ 约化即得 $b g(Z) = 0 in A\/a [Z]$。由于 $b in A\/a$ 是非零因子，故 $g(Z) = 0 in A\/a [Z]$。于是存在 $h(Z) in A[Z]$ 使得 $g(Z) = a h(Z)$。现在：
    $
      a f(Z) = a (a Z - b) h(Z) 
    $
    又因 $a in A$ 是非零因子，故 $f(Z) = (a Z - b) h(Z)$。因此 $f(Z) = 0 in A[Z]\/(a Z - b)$。
  ]
  于是 $pi.alt Z_1 - g_1, dots.c, pi.alt Z_c - g_c$ 是 $D[Z_1,dots.c,Z_c]$ 中的正则序列，且 $pi.alt$ 在 $D[Z_1,dots.c,Z_c]\/(pi.alt Z_1 - g_1, dots.c, pi.alt Z_c - g_c)$ 中是非零因子。因此，
  $
    D^+ = D[Z_1,dots.c,Z_c]/((pi.alt Z_1 - g_1, dots.c, pi.alt Z_c - g_c))
  $
  令 $I = (pi.alt Z_1 - g_1, dots.c, pi.alt Z_c - g_c) subset D[Z_1,dots.c,Z_c]$。则：
  
  - 考虑第二正合列：#h(1fr)
    $
      ol(frak(p))(D\/pi.alt D)_(ol(frak(p)))\/ol(frak(p))^2(D\/pi.alt D)_(ol(frak(p))) -> Omega_((D\/pi.alt D)\/k(V)) otimes_D k(frak(p)) -> Omega_(k(frak(p))\/k(V)) -> 0
    $
    我们有：

    - 由正则性，$dim_(k(frak(p))) (ol(frak(p))(D\/pi.alt D)_(ol(frak(p)))\/ol(frak(p))^2 (D\/pi.alt D)_(ol(frak(p)))) = dim((D\/pi.alt D)_(ol(frak(p))))$；

    - 由光滑性与 @equiv-defns-of-smooth (1)，#h(1fr)
      $
        dim_(k(frak(p))) (Omega_((D\/pi.alt D)\/k(V)) otimes_D k(frak(p))) = dim((D\/pi.alt D)_(ol(frak(p)))) + trd_(k(V)) (k(frak(p)))
      $

    - $k(frak(p))\/k(V)$ 是可分扩张 $k(V')\/k(V)$ 的有限生成中间域，因此可分生成；于是由 @cite-matsumura-ca[Theorem 59]，
      $
        dim_(k(frak(p))) (Omega_(k(frak(p))\/k(V))) = trd_(k(V)) (k(frak(p)))
      $

    因此，比较维数可知这个序列短正合。于是 $d g_1, dots.c, d g_c$ 在 $Omega_((D\/pi.alt D)\/k(V)) otimes_D k(frak(p))$ 中线性无关。

  - 现在考虑另一个第二正合列：
    $
      (I\/I^2)_(frak(p)^+) -> (Omega_(D[Z_1,dots.c,Z_c]\/V))_(frak(p)^+) -> (Omega_(D^+\/V))_(frak(p)^+) -> 0
    $
    分裂第一正合列，可以作如下等同：
    $
      Omega_(D[Z_1,dots.c,Z_c]\/V) cong (Omega_(D\/V) otimes_D D[Z_1,dots.c,Z_c]) oplus oplus.big_(b=1)^c D[Z_1,dots.c,Z_c] d Z_b
    $
    于是第二正合列化为：
    $
      (I\/I^2)_(frak(p)^+) -> (Omega_(D\/V) otimes_D D^+_(frak(p)^+)) oplus oplus.big_(b=1)^c D^+_(frak(p)^+) d Z_b -> (Omega_(D^+\/V))_(frak(p)^+) -> 0
    $
    
    - 这些关系类映到 $pi.alt d Z_b - d g_b$。模去 $frak(p)^+$ 处的极大理想后，它们化为 $- d g_b$，并且线性无关。因此，该序列在模去极大理想之后短正合。

    - 由光滑性，中间项自由。由于 $I = (pi.alt Z_1 - g_1, dots.c, pi.alt Z_c - g_c)$ 由正则序列生成，由 #cite-stacks("061P")[Definition 10.69.1] 与 #cite-stacks("00LN")[Lemma 10.69.2] 可得 $I\/I^2 cong (D[Z_1,dots.c,Z_c]\/I)^(oplus c)$，其基为 $pi.alt Z_1 - g_1, dots.c, pi.alt Z_c - g_c$。

    总之，这个右正合列的第一项是秩为 $c$ 的自由模，第二项是秩为 $c + d$ 的自由模，并且模去 $frak(p)^+$ 处的极大理想后仍然正合。

    因此，第一个映射的矩阵有一个 $c times c$ 子式在 $k(frak(p)^+)$ 中可逆。这个子式因而在 $D^+_(frak(p)^+)$ 中可逆。于是该右正合列分裂正合，从而由 @equiv-defns-of-smooth (5)，$D^+$ 在 $frak(p)^+$ 处光滑。

  (3) 沿用 (2) 的设定。我们已经看到 $d g_1, dots.c, d g_c in Omega_((D\/pi.alt D)\/k(V)) otimes_D k(frak(p)) cong Omega_(D\/V) otimes_D k(frak(p))$。写成：
  $
    d g_i = sum_(j=1)^r a_(i,j) d T_j
  $
  则矩阵 $display(mat(a_(i,j))_(i<=c,j<=r))$ 的某个 $c times c$ 子式 $Delta$ 在 $k(frak(p))$ 中可逆。重排 $T_j$ 之后，可以假定：
  $
    Delta = mat(a_(i,j))_(i,j<=c) in MM_(c times c) (D)
  $
  满足 $det(Delta) in k(frak(p))^times$。于是 $det(Delta) in D_(frak(p))^times$。因此在 $frak(p)$ 附近缩小 $D$，便可假定 $det(Delta) in D^times$。

  于是 $d g_1, dots.c, d g_c, d T_(c+1), dots.c, d T_r$ 构成 $Omega_(D\/V)$ 的一组基，即：
  $
    Omega_(D\/V) = oplus.big_(i=1)^c D d g_i oplus oplus.big_(i=c+1)^r D d T_i
  $
  同时回忆：
  $
    Omega_(D^+\/V) cong ((Omega_(D\/V) otimes_D D^+) oplus oplus.big_(i=1)^c D^+ d Z_i)/((pi.alt d Z_1 - d g_1, dots.c, pi.alt d Z_c - d g_c)) cong (oplus.big_(i=1)^c D^+ d g_i oplus oplus.big_(i=c+1)^r D^+ d T_i oplus oplus.big_(i=1)^c D^+ d Z_i)/((pi.alt d Z_1 - d g_1, dots.c, pi.alt d Z_c - d g_c))
  $
  它因而自由，以 $d Z_1, dots.c, d Z_c, d T_(c+1), dots.c, d T_r$ 为基；而映射 $Omega_(D\/V) otimes_D D^+ -> Omega_(D^+\/V)$ 的作用是：
  $
    d g_i |-> pi.alt d Z_i, d T_i |-> d T_i
  $
  因此它在这两组基下的矩阵为 $"diag"(pi.alt I_c, I_(r-c))$。
]


#proposition(name: <neron-blowup-defect-drop>)[
  假设 $D$ 在 $frak(q)$ 处光滑，且剩余域扩张 $k(V')\/k(V)$ 可分，即每个有限生成中间域都是可分生成的。若 $D$ 在 $frak(p)$ 处不光滑，则：
  $
    e(D^+, phi^+) < e(D, phi)
  $
  同时 $D^+$ 仍在 $frak(q)^+$ 处光滑。
]
#proof[
  取 $D$ 的一个 $V$-代数展示：
  $
    0 -> J arrow.hook E ->> D -> 0 
  $
  其中 $E$ 是 $V$ 上的多项式代数。

  注意 $e(D_([q])^+, phi_([q])^+) = e(D^+, phi^+)$，因为 $Q_(D_([q])^+) cong Omega_(D\/V) otimes_D D_([q]) otimes_(D_([q])) V' cong Q_(D^+)$。因此，把 $E$ 与 $D$ 在某个元素 $q in E - frak(p)_E$ 处局部化是安全的。于是由 @neron-smoothing-smoothness-pass，可以把 $E$ 局部化，使得 $E$ 在 $V$ 上光滑、相对维数为 $d$，且映射
  $
    Q_E -> Q_(E^+)
  $ 
  的矩阵展示为 $"diag"(pi.alt I_c, I_(r-c))$。

  令 $J^+ = ker(E^+ ->> D^+) = (J E^+ : pi.alt^oo)$。再令：
  $
    M = Q_E = Omega_(E\/V) otimes_E V, N = im(J\/J^2 otimes_D V' -> M) \
    M^+ = Q_(E^+) = Omega_(E^+\/V) otimes_(E^+) V, N^+ = im(J^+\/(J^+)^2 otimes_(D^+) V' -> M^+)
  $
  由第二正合列有 $Q := M\/N cong Q_D$，同样有 $Q^+ := M^+\/N^+ cong Q_(D^+)$。由 @neron-smoothing-smoothness-pass (3)，
  $
    pi.alt M^+ subset M subset M^+
  $
  其中 $M, M^+$ 是 $V'$ 上秩为 $r$ 的自由模。

  令 $K = Frac(V), K' = Frac(V')$。现在：

  - 若 $h in J$，则 $h in frak(p)_E$，从而 $pi.alt^(-1) h in pi.alt^(-1) frak(p)_E subset E^+$。又有 $pi.alt^(-1) h in (J E^+: pi.alt^oo) in J^+$。此外，$d(pi.alt^(-1) h) = pi.alt^(-1) d h$。于是我们证明了 $N subset pi.alt N^+$，特别地：
    $
      N_(K') = N^+_(K')
    $
    其中我们已知 $M_(K') = M^+_(K')$。

  $N$ 与 $N^+$ 都是秩为 $r-d$ 的自由模。于是 $Q$ 与 $Q^+$ 的自由秩都是 $d$，因此 $d$ 就是 $D$ 在 $frak(q)$ 处的相对维数。
  
  令 $W = N_(K') = N^+_(K') subset M^+_(K')$，然后求交：
  $
    tilde(N) = W inter M, tilde(N)^+ = W inter M^+
  $
  其中的交都在 $M^+_(K')$ 中取。于是：
  $
    T_(pi.alt^oo) (Q) = tilde(N)\/N, T_(pi.alt^oo) (Q^+) = tilde(N)^+\/N^+
  $
  从而：
  $
    e(D, phi) - e(D^+, phi^+) &= length_(V') (tilde(N)\/N) - length_(V') (tilde(N)^+\/N^+) \
    &= length_(V') (N^+\/N) - length_(V') (tilde(N)^+\/tilde(N))
  $
  由包含关系 $pi.alt M^+ subset M$ 可得 $pi.alt tilde(N)^+ subset tilde(N)$，故 $length_(V') (tilde(N)^+\/tilde(N)) <= r - d$。另一方面，$N subset pi.alt N^+$ 表明 $length_(V') (N^+\/N) >= r-d$。因此，
  $
    e(D, phi) - e(D^+, phi^+) = length_(V') (N^+\/N) - length_(V') (tilde(N)^+\/tilde(N)) >= 0
  $
  还需证明这个量严格 $>0$。若等号成立，则必须有：
  $
    tilde(N) = pi.alt tilde(N)^+, N = pi.alt N^+
  $
  由于 $D$ 在 $frak(p)$ 处不光滑，由 @zero-defect-implies-smooth 可知 $e(D, phi) > 0$。于是仿照其证明中的论证，
  $
    s := dim_(k(frak(p))) (Omega_(D\/V) otimes_D k(frak(p))) > d
  $
  因此，对下面这个第二正合列：
  $
    J\/J^2 otimes_D k(frak(p)) -> oplus.big_(i=1)^r k(frak(p)) d T_i -> Omega_(D\/V) otimes_D k(frak(p)) -> 0
  $
  第一个映射的像维数为 $r-s$。因此可以选取一组生成元 $J = (h_1, dots.c, h_t)$，使得 $d h_1, dots.c, d h_(r-s)$ 构成这个像的一组基，而 $d h_(r-s+1), dots.c,  d h_t = 0 in oplus.big_(i=1)^r k(frak(p)) d T_i$。
  
  另一方面，像 @neron-smoothing-smoothness-pass (2) 的证明中那样选取一组生成元 $frak(p)_E = (pi.alt, g_1, dots.c, g_c)$。由于 $d g_1, dots.c, d g_c in Omega_(E\/V) otimes_E k(frak(p)_E)$ 线性无关，且 $d pi.alt = 0$，
  $
    ker(frak(p)_E E_(frak(p)_E)\/frak(p)_E^2 E_(frak(p)_E) -> Omega_(E\/V) otimes_E k(frak(p)_E)) = k(frak(p)_E) [pi.alt]
  $
  于是对 $i>r-s$，由于 $d h_i$ 的像在 $oplus.big_(i=1)^r k(frak(p)) d T_i$ 中为零，$d h_i$ 在 $Omega_(E\/V) otimes_E k(frak(p)_E)$ 中也必须为零。因此，
  $
    h_i = pi.alt b_i + u_i, b_i in E_(frak(p)), u_i in frak(p)_E^2 E_(frak(p)_E)
  $
  在 $frak(p)_E$ 附近缩小 $E$，可以假定 $b_i in E, u_i in frak(p)_E^2 E$。现在 $h_i$ 在 $V'$ 中的像为 $0$，而 $u_i$ 的像属于 $pi.alt^2 V'$。因此 $b_i$ 的像属于 $pi.alt V'$，于是也有 $b_i in frak(p)_E$。

  现在 $N$ 由 $d h_1, dots.c, d h_t$ 生成，而 $dim_(k(V)) (N\/pi.alt N) = r - d > r - s$。因此存在某个 $i > r - s$ 使得 $d h_i in.not pi.alt N$。对这个 $i$：

  - $pi.alt^(-2) h_i = pi.alt^(-1) b_i + pi.alt^(-2) u_i in E[pi.alt^(-1) frak(p)_E] = E^+$，并且属于 $(J E^+ : pi.alt^oo) = J^+$。因此有#h(1fr)
    $
      d(pi.alt^(-2) h_i) in N^+
    $
    从而 $d h_i in pi.alt^2 N^+$。但 $N = pi.alt N^+$，所以：
    $
      d h_i in pi.alt^2 N^+ = pi.alt N
    $
    矛盾。

  因此等号不能成立，故 $e(D, phi) > e(D^+, phi^+)$。
]

#theorem(name: <classical-neron-smoothing>)[
  (古典 Néron 光滑化) 设 $(D, phi)$ 如 @situation-neron-smoothing 中那样。若还假设：

  - $D$ 在 $frak(q)$ 处光滑；

  - $k(V')\/k(V)$ 可分。

  则对 $D$ 作有限多次 Néron 爆破得到代数 $E$ 之后，$E$ 在 $frak(p)_E$ 处光滑。
]
#proof[
  我们对 $D$ 接连作 Néron 爆破：
  $
    D = D_0 -> D_1 -> dots.c -> D_m -> D_(m+1) -> dots.c -> V'
  $
  其中 $D_(m+1) := D_m^+$。若每个 $D_m$ 在 $frak(p)_m$ 处都不光滑，便可无休止地应用 @neron-blowup-defect-drop，得到自然数的严格下降链：
  $
    e(D_0, phi_0) > e(D_1, phi_1) > dots.c > e(D_m, phi_m) > e(D_(m+1), phi_(m+1)) > dots.c
  $
  这不可能。因此，某个 $D_m$ 在 $frak(p)_m$ 处光滑。
]

#proposition(name: <artin-approx-smoothing-reduction>)[
  以下条件等价：

  + 对任意优良 DVR $R$，令 $A_n = R{X_1, dots.c, X_n}$。对任意 $N >= 1$，若多项式方程组 $f_1, dots.c, f_r in R[Y_1, dots.c, Y_m]$ 有形式解 $hat(y)_1, dots.c, hat(y)_m in hat(A_n)$（其中 $hat(A_n) = hat(R) fps(X_1\, dots.c\, X_n)$）：
    $
      f_1 (hat(y)_1, dots.c, hat(y)_m) = dots.c = f_r (hat(y)_1, dots.c, hat(y)_m) = 0
    $
    则存在解 $y_1, dots.c, y_m in A_n$，它与 $hat(y)_1, dots.c, hat(y)_m in hat(A_n)$ 模 $frak(m)_n^N$ 相符：
    $
      f_1 (y_1, dots.c, y_m) = dots.c = f_r (y_1, dots.c, y_m) = 0
    $

    也就是说，环 $A_n = R{X_1, dots.c, X_n}$ 对 $R[X_1,dots.c,X_n,Y_1,dots.c,Y_m]$ 中的多项式方程组满足 Artin 逼近。

  + 设定同 (1)，但额外假定：对映射
    $
      phi: R[arrow(X), arrow(Y)] -> hat(A_n), Y_i |-> hat(y)_i
    $
    有
    $
      (f_1, dots.c, f_r) = ker(phi)
    $
    并且 $D = R[arrow(X), arrow(Y)]\/ker(phi) = im(phi)$ 在素理想 $phi^(-1) (pi.alt hat(A_n)) in Spec(D)$ 处是 $R[arrow(X)]$ 上光滑的。
]
#proof[
  (1) $==>$(2) 是同义反复，故只需证明 (2) $==>$(1)。首先，我们可以无害地向方程组中添加有限多个方程，使得：
  $
    (f_1, dots.c, f_r) = ker(phi)
  $

  令 $D = im(phi)$。则 $Frac(D)$ 是 $Frac(hat(A_n))\/Frac(R)(arrow(X))$ 的一个有限生成中间扩张。
  
  由于 $R[arrow(X)]_((pi,arrow(X)))$ 是优良的，泛纤维 $Spec(Frac(hat(A_n))) -> Spec(Frac(R)(arrow(X)))$ 正则。由 #cite-stacks("07EQ")[Lemma 15.42.6]，$Frac(hat(A_n))\/Frac(R)(arrow(X))$ 是可分扩张。
  
  于是 $Frac(D)\/Frac(R)(arrow(X))$ 可分生成；对 $Frac(hat(A_n))\/Frac(R)(arrow(X))$ 再次应用 #cite-stacks("07EQ")[Lemma 15.42.6]，可知映射 $Spec(D) -> Spec(R[arrow(X)])$ 的泛纤维的泛点是几何正则的。于是由 @equiv-defns-of-smooth (2)，$Spec(D)$ 在 $Spec(R[arrow(X)])$ 的一个稠密开集上光滑。

  现在令 $V = R[arrow(X)]_((pi.alt)), V' = (hat(A_n))_(pi.alt hat(A_n))$。则 $V -> V'$ 是具有相同一致化元 $pi.alt$ 的 DVR 扩张。剩余域为：
  $
    k(V') = Frac(k fps(arrow(X))), k(V) = k(arrow(X))
  $
  其中 $k = k(R)$。于是 $k(V')\/k(V)$ 可分，因为 $k[arrow(X)]_((arrow(X)))$ 是优良的。我们打算对 $D otimes_(R[arrow(X)]) R[arrow(X)]_((pi.alt))$ 作 Néron 爆破，并且预期这只会给方程组带来无害的改动。

  #construction[
    假设：
    $
      C = R[arrow(X), arrow(Y)]\/frak(q), frak(q) = (f_1, dots.c, f_r)
    $
    是有限型 $R[arrow(X)]$-代数，即 $hat(A_n)$ 的 $R[arrow(X)]$-子代数。我们还假设 $Spec(C) -> Spec(R[arrow(X)])$ 在一个稠密开集上光滑。
    
    令 $frak(p) = pi.alt hat(A_n) inter C in Spec(C)$，并记：
    $
      C' := C[pi.alt^(-1) frak(p)] subset C[pi.alt^(-1)] subset hat(A_n)[pi.alt^(-1)]
    $
    实际上 $C'$ 是 $hat(A_n)$ 的子代数，因为按定义 $pi.alt^(-1) frak(p) subset hat(A_n)$。选取生成元 $frak(p) = (pi.alt, g_1, dots.c, g_t)$，便有同构：
    $
      C' cong C[Z_1,dots.c,Z_t]/(((pi.alt Z_1 - g_1, dots.c, pi.alt Z_t - g_t) : pi.alt^oo))
    $
    令：
    $
      J_0 = (f_1 (arrow(X), arrow(Y)), dots.c, f_r (arrow(X), arrow(Y)), pi.alt Z_1 - g_1 (arrow(X), arrow(Y)), dots.c, pi.alt Z_t - g_t (arrow(X), arrow(Y))) subset R[arrow(X), arrow(Y), arrow(Z)]
    $
    则 $J = (J_0 : pi.alt^oo)$ 是在 $J_0$ 上再添上有限多个新方程得到的，比如：
    $
      J = J_0 + (h_1 (arrow(X), arrow(Y), arrow(Z)), dots.c, h_s (arrow(X), arrow(Y), arrow(Z)))
    $
    于是 $J$ 满足：
    $
      C' cong R[arrow(X), arrow(Y), arrow(Z)]\/J
    $
    现在对给定的解 $hat(y) in hat(A_n)^m$，由定义 $g_i (X, hat(y)) in pi.alt hat(A_n)$，故可以取 $hat(z)_i = pi.alt^(-1) g_i (X, hat(y))$。于是形式解 $hat(y), hat(z)$ 满足 $J_0$ 的方程：
    $
      f_i (X, hat(y)) = 0 \
      pi.alt hat(z)_i - g_i (X, hat(y)) = 0
    $
    此外，对每个 $h_i$ 都存在某个 $M$ 使得 $pi.alt^M h_i in J_0$。于是 $pi.alt^M h_i (X, hat(y), hat(z)) = 0 in hat(A_n)$。然而 $hat(A_n)$ 是整环，故 $h_i (X, hat(y), hat(z)) = 0$。换言之：

    - $(f_1, dots.c, f_r) subset R[arrow(X), arrow(Y)]$ 的形式解 $hat(y) in hat(A_n)^m$ 诱导出 $J subset R[arrow(X), arrow(Y), arrow(Z)]$ 的形式解 $(hat(y), hat(z)) in hat(A_n)^(m+t)$。

      因此，若定义 $J$ 的方程组 $f_i, pi.alt Z_i - g_i, h_i$ 有逼近解 $(y, z) in A_n^(m+t)$，且它与 $(hat(y), hat(z))$ 模 $frak(m)_n^N$ 相符，则 $y in A_n^m$ 就是 $(f_1,dots.c,f_r)$ 的逼近解，且与 $hat(y)$ 模 $frak(m)_n^N$ 相符。

    因此，我们可以无害地把定义 $C$ 的、关于 $arrow(Y)$ 的原方程组换成定义 $C'$ 的、关于 $arrow(Y), arrow(Z)$ 的新方程组。
    
    现在令 $C_V := C otimes_(R[arrow(X)]) R[arrow(X)]_((pi.alt)) = C otimes_(R[arrow(X)]) V$，这是有限型 $V$-代数。它平坦，因为 $C$ 作为 $hat(A_n)$ 的子环没有 $pi.alt$-挠。
    
    有局部求值映射：
    $
      phi_V: C_V -> V', c otimes v |-> c v
    $
    这个映射先作 $phi$ 的基变换 $C_V -> hat(A_n) otimes_(R[arrow(X)]) V$，再复合上映射 $(hat(A_n))_(pi.alt R[arrow(X)]) = hat(A_n) otimes_(R[arrow(X)]) V -> V' = (hat(A_n))_(pi.alt hat(A_n))$。第二个映射是整环的局部化，故为单射；第一个映射是单射的局部化，故也是单射。因此 $phi_V$ 是单射。

    - 若 $c in C, f in R[arrow(X)] - pi.alt R[arrow(X)]$ 满足 $c\/f in pi.alt V'$，则：#h(1fr)
      $
        c in pi.alt f V' inter C subset (pi.alt V' inter hat(A_n)) inter C = pi.alt hat(A_n) inter C = frak(p)
      $
      反之，若 $c in frak(p), f in R[arrow(X)] - pi.alt R[arrow(X)]$，则 $c in pi.alt hat(A_n)$，且 $f in V' - pi.alt V' = (V')^times$，故 $c\/f in pi.alt V'$。

      因此 $phi_V^(-1) (pi.alt V') = frak(p) otimes_(R[arrow(X)]) V$ 是 $frak(p)$ 的扩张。它因而也由 $(pi.alt, g_1, dots.c, g_t)$ 生成。

      因此，
      $
        C_V^+ = (C_V [Z_1, dots.c, Z_t])/((pi.alt Z_1 - g_1, dots.c, pi.alt Z_t - g_t : pi.alt^oo)) = C' otimes_(R[arrow(X)]) V
      $

    - $Spec(C) -> Spec(R[arrow(X)])$ 在稠密开集上光滑。于是作为该映射的局部化，$Spec(C_V) -> Spec(V)$ 在泛点处也光滑。由于 $ker(phi_V) = 0$，@classical-neron-smoothing 的“在 $frak(q)$ 处光滑”这一假设得到满足。
  ]

  总结上述讨论：我们可以有限多次地施行 $C |-> C'$，而每次只对方程组作无害的扩充。由 @classical-neron-smoothing 及上述讨论，可以假定 $Spec(D_V) -> Spec(V)$ 在 $frak(p)_V = phi^(-1) (pi.alt hat(A_n)) otimes_(R[arrow(X)]) V$ 处光滑。现在比较局部化可知 $(D_V)_(frak(p)_V) cong D_(phi^(-1) (pi.alt hat(A_n)))$，故 $Spec(D) -> Spec(R[arrow(X)])$ 在 $phi^(-1) (pi.alt hat(A_n))$ 处光滑。这样就归约到了 (2) 的假设。
]

我们沿用上面的设定，把 @artin-approx-smoothing-reduction 改写成更好用的形式。

#construction[
  设 $f_1, dots.c, f_r in R[arrow(X), arrow(Y)]$ 是一个方程组，它如 @artin-approx-smoothing-reduction (2) 的设定那样有形式解 $hat(y) in hat(A_n)^m$。也就是说，对
  $
    phi: R[arrow(X), arrow(Y)] -> hat(A_n), Y_i |-> hat(y)_i
  $
  有：
  $
    frak(p) = ker(phi) = (f_1, dots.c, f_r)
  $
  并且 $D = im(phi)$ 在 $frak(r) = phi^(-1) (pi.alt hat(A_n))$ 处是 $R[arrow(X)]$ 上光滑的。设 $d$ 为该点处的相对维数。由 @equiv-defns-of-smooth (4) 得到第二正合列：
  $
    frak(p)\/frak(p)^2 -> oplus.big_(i=1)^m D d Y_i -> Omega_(D\/R[arrow(X)]) -> 0
  $
  该序列在 $ol(frak(r)) = frak(r)\/frak(p) in Spec(D)$ 处分裂正合。于是，在适当重排方程与未定元 $Y_i$ 之后，这一分裂表明：
  $
    delta(arrow(X), arrow(Y)) = det mat(display((partial f_i)/(partial Y_j)))_(i,j <= m-d) in D_(ol(frak(r)))^times
  $
  等价地，
  $
    delta(arrow(X), hat(y)) = det mat(display((partial f_i)/(partial Y_j)) (arrow(X), hat(y)))_(i,j <= m-d) in hat(A_n) - pi.alt hat(A_n)
  $
  我们断言，把方程组 $(f_1, dots.c, f_r)$ 换成 $(f_1, dots.c, f_(m-d))$ 是安全的。目标是找到 $h in R[arrow(X), arrow(Y)] - frak(r)$ 使得 $h frak(p) subset (f_1, dots.c, f_(m-d))$。

  - 取局部环 $C = R[arrow(X), arrow(Y)]_(frak(r))$。则 $C$ 正则；又因 $D = R[arrow(X), arrow(Y)]\/frak(p)$ 在 $ol(frak(r))$ 处光滑，$C\/frak(p) C$ 也正则。

    由于 $R[arrow(X), arrow(Y)]$ 在 $R[arrow(X)]$ 上光滑、相对维数为 $m$，而 $D$ 在 $ol(frak(r))$ 处是 $R[arrow(X)]$ 上光滑的，相对维数为 $d$，
    $
      m = dim(C) + trd_(k(arrow(X))) (C\/frak(r) C) \

      d = dim(C\/frak(p) C) + trd_(k(arrow(X))) (C\/frak(r) C)
    $
    于是 $dim(C) - dim(C\/frak(p) C) = m - d$。因此对 $C$ 中的正则序列 $a_1, dots.c, a_(m-d)$ 有 $frak(p) C = (a_1, dots.c, a_(m-d))$。由 #cite-stacks("061P")[Definition 10.69.1] 与 #cite-stacks("00LN")[Lemma 10.69.2]，$frak(p)C\/frak(p)^2 C$ 是秩为 $m-d$ 的自由 $C\/frak(p)$-模。

    于是可逆子式 $delta(arrow(X), arrow(Y))$ 表明：$f_1, dots.c, f_(m-d) in frak(p)$ 约化到 $frak(p)C\/frak(p)^2 C$ 后构成一组基。由 Nakayama 引理，
    $
      frak(p) C = (f_1, dots.c, f_(m-d)) + frak(p)^2 C
    $
    再次应用 Nakayama 引理得 $frak(p) C = (f_1, dots.c, f_(m-d))$。于是对每个生成元 $f_i in frak(p)$，存在 $g_i in C = R[arrow(X), arrow(Y)]_(frak(r))$ 使得 $f_i in g_i (f_1, dots.c, f_(m-d)) subset C$。消去 $R[arrow(X), arrow(Y)] - frak(r)$ 中的有限多个分母，就构造出 $h in R[arrow(X), arrow(Y)] - frak(r)$ 使得：
    $
      h frak(p) subset (f_1, dots.c, f_(m-d))
    $

  令 $M = "ord"_(frak(m)_n) (h(arrow(X), hat(y)))$。则：

  - 若有 $arrow(y) in A_n^m$ 与 $hat(y)$ 模 $frak(m)_n^N$ 相符，且 $N > M$，则：#h(1fr)
    $
      h(arrow(X), arrow(y)) mod frak(m)_n^N = h(arrow(X), hat(y)) mod frak(m)_n^N != 0
    $
    特别地 $h(arrow(X), arrow(y)) != 0$。现在，由于 $h frak(p) subset (f_1, dots.c, f_(m-d))$，对每个 $i<=r$ 有
    $
      h(arrow(X), arrow(y)) f_i (arrow(X), arrow(y)) = 0
    $
    其中 $h(arrow(X), arrow(y)) != 0$。由于 $A_n$ 是整环，每个 $f_i (arrow(X), arrow(y)) = 0$。

  总之，若能把 $hat(y)$ 作为 $(f_1, dots.c, f_(m-d))$ 的解逼近到任意阶，就能把 $hat(y)$ 作为 $(f_1, dots.c, f_r)$ 的解逼近到任意阶。
]

综合上述讨论并结合 @artin-approx-smoothing-reduction，我们有：

#proposition(name: <artin-approx-smoothing-reduction-2>)[
  以下条件等价：

  + 对任意优良 DVR $R$，令 $A_n = R{X_1, dots.c, X_n}$。对任意 $N >= 1$，若多项式方程组 $f_1, dots.c, f_r in R[Y_1, dots.c, Y_m]$ 有形式解 $hat(y)_1, dots.c, hat(y)_m in hat(A_n)$（其中 $hat(A_n) = hat(R) fps(X_1\, dots.c\, X_n)$）：
    $
      f_1 (hat(y)_1, dots.c, hat(y)_m) = dots.c = f_r (hat(y)_1, dots.c, hat(y)_m) = 0
    $
    则存在解 $y_1, dots.c, y_m in A_n$，它与 $hat(y)_1, dots.c, hat(y)_m in hat(A_n)$ 模 $frak(m)_n^N$ 相符：
    $
      f_1 (y_1, dots.c, y_m) = dots.c = f_r (y_1, dots.c, y_m) = 0
    $

    也就是说，环 $A_n = R{X_1, dots.c, X_n}$ 对 $R[X_1,dots.c,X_n,Y_1,dots.c,Y_m]$ 中的多项式方程组满足 Artin 逼近。

  + 在 (1) 的设定下，额外假定 $r = m - d <= m$，且 Jacobi 行列式满足：
    $
      delta(arrow(X), hat(y)) = det mat(display((partial f_i)/(partial Y_j)) (arrow(X), hat(y)))_(i,j <= m-d) in hat(A_n) - pi.alt hat(A_n)
    $
]
