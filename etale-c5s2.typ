#import "void-import.typ": *
== 拟凝聚层的平展上同调

#lemma[
  设 $U = Spec(A)$ 是仿射概形，$cal(M) = tilde(M) in QCoh(U)$ 是拟凝聚层。则：
  $
    H^q (U, cal(M)_et) = 0, forall q >= 1
  $
]
#proof[
  我们先对 Čech 上同调证明这一消没性，即证明：
  $
    caron(H)^q (U, cal(M)_et) = 0, forall q >= 1
  $
  为此，我们对 $U$ 的平展覆盖的一个共尾系统证明消没性。$U$ 仿射，因而拟紧，于是 $U$ 的每个平展覆盖都有由有限多个仿射概形组成的加细覆盖。对这样的覆盖取不交并，就得到由单个映射构成的覆盖，二者的 Čech 上同调相等。因此，只需对形如 $cal(U) = {U' = Spec(A') -> U}$ 的平展覆盖证明：
  $
    caron(H)^q (cal(U), cal(M)_et) = 0, forall q >= 1
  $
  现在，由于 $U' ->> U$ 是满射平展，$A -> A'$ 忠实平坦。于是 $cal(U)$ 的 Čech 复形是：
  $
    0 -> M otimes_A A' -> dots.c -> M otimes_A A^((q)) -> M otimes_A A^((q+1)) -> dots.c
  $
  这正是删去 $M$ 项后的 Amitsur 复形，故由 @amitsur-complex-exact 可知，它在每个 $q >= 1$ 处都正合。Čech 上同调的情形至此证毕。

  接下来，我们借助 Čech 到导出函子的谱序列与归纳法，过渡到平展上同调。由于 $caron(H)^1 (U, -) = H^1 (U, -)$，$q = 1$ 的情形已经解决。假设引理对所有 $0 < q < n$ 以及仿射概形上的一切拟凝聚层成立。考虑 Čech 到导出函子的谱序列：
  $
    E_2^(p,q) = caron(H)^p (U, ul(H)^q (cal(M)_et)) => H^(p+q) (U, cal(M)_et)
  $
  我们断言，这个谱序列在 $0 < q < n$ 的各行上全为零。$U$ 仿射，因而拟紧，故只需证明：对一切 $0 < q < n$，以及一切由有限多个仿射概形组成的 $cal(U) = {U_i = Spec(B_i) -> U}_(1<=i<=m)$，都有
  $
    caron(H)^p (cal(U), ul(H)^q (cal(M)_et)) = 0
  $
  于是由 @pullback-along-etale-morphism-derived，$ul(H)^q (cal(M)_et)$ 的 Čech 复形的第 $p$ 项是若干形如下式的项的直积：
  $
    H^q (U_(i_0,dots.c,i_p), cal(M)_et) = H^q (U_(i_0,dots.c,i_p), u_(i_0,dots.c,i_p)^(-1) cal(M)_et)
  $
  其中 $u_(i_0,dots.c,i_p): U_(i_0,dots.c,i_p) := U_(i_0) times_U dots.c times_U U_(i_p) -> U$ 是仿射平展的，且 $u_(i_0,dots.c,i_p)^(-1) cal(M)_et = (u_(i_0,dots.c,i_p)^* cal(M))_et$，后一等式可以逐截面验证。

  然而，只要 $0 < q < n$，由归纳假设，形如上式的项全为 $0$。换言之，对一切 $0 < q < n$ 都有 $caron(H)^p (U, ul(H)^q (cal(M)_et)) = 0$，于是这条谱序列上出现一条水平的消没带。应用修正后的五项正合列，我们得到正合列：
  $
    0 -> caron(H)^n (U, cal(M)_et) -> H^n (U, cal(M)_et) -> caron(H)^0 (U, ul(H)^n (cal(M)_et)) -> dots.c
  $
  现在，前文已证 $caron(H)^n (U, cal(M)_et) = 0$，而由 @cech-h0-of-hq-psh-vanish 有 $caron(H)^0 (U, ul(H)_n (cal(M)_et)) = 0$。至此便得到 $H^n (U, cal(M)_et) = 0$。
]

#theorem(name: <etale-cohom-of-qcoh-sheaf>)[
  设 $X$ 是任意概形，$cal(M) in QCoh(X)$。则 $cal(M)_et$ 的平展上同调与 $cal(M)$ 的 Zariski 上同调之间存在自然同构：
  $
    H^q_et (X, cal(M)_et) cong H^q_#[Zar] (X, cal(M)), forall q >= 0
  $
]
#proof[
  考虑遗忘函子：
  $
    epsilon: cAb(X_et) -> cAb(X_#[Zar])
  $
  它把 $X$ 上的平展层映到 $X$ 上的 Zariski 层。平展层与 Zariski 层上的左正合性都可以逐截面检验，所以 $epsilon$ 是左正合函子。我们希望把 Grothendieck–Leray 谱序列应用于下面这个复合函子：
  // https://q.uiver.app/#r=typst&q=WzAsMyxbMCwxLCJjQWIoWF9ldCkiXSxbMiwxLCJjQWIiXSxbMSwwLCJjQWIoWF8jW1phcl0pIl0sWzIsMSwiR2FtbWEoWCwtKSJdLFswLDEsIkdhbW1hKFgsLSkiLDJdLFswLDIsImVwc2lsb24iXV0=
  #align(center, diagram({
    node((-1, 0), [$cAb(X_et)$])
    node((1, 0), [$cAb$])
    node((0, -1), [$cAb(X_#[Zar])$])
    edge((0, -1), (1, 0), [$Gamma(X, -)$], label-side: left, "->")
    edge((-1, 0), (1, 0), [$Gamma(X, -)$], label-side: right, "->")
    edge((-1, 0), (0, -1), [$epsilon$], label-side: left, "->")
  }))
  为此，需要说明 $epsilon$ 把内射对象映到 ${H^q_#[Zar] (X, -)}_(q>=0)$-零调对象。

  #lemma[
    设 $F: cal(A) -> cal(B), G: cal(B) -> cal(C)$ 是 Abel 范畴之间的加性函子，这里 $cal(A), cal(B)$ 都有足够多的内射对象。假设存在 $cal(A)$ 的一族内射对象 $cal(I)$，使得：
    
    - $cal(A)$ 的每个对象都能嵌入 $cal(I)$ 中的某个对象；
    
    - $F$ 把 $cal(I)$ 的每个对象都映到 $G$-零调对象。
    
    则 $F$ 把内射对象映到 $G$-零调对象。
  ]
  #proof[
    对任意内射对象 $I in cal(A)$，取它到某个 $I_0 in cal(I)$ 的嵌入 $I ->^i I_0$，再取余核：
    $
      0 -> I ->^i I_0 -> coker(i) -> 0
    $
    于是由 $I$ 的内射性，这个正合列分裂，从而有 $I_0 = I oplus coker(i)$。因此 $F(I_0) = F(I) oplus F(coker(i))$，且对每个 $q >= 1$，
    $
      0 = R^q G (F(I_0)) = R^q G (F(I)) oplus R^q G (F(coker(i)))
    $
    从而 $R^q G(F(I)) = 0, forall q >= 1$。因此 $F(I)$ 是 $G$-零调对象。
  ]
  由 Godement 消解可知，$cAb(X_et)$ 中的每个层都能嵌入形如下式的内射层：
  $
    product_(x in X) ol(x)_* I_x
  $
  施加遗忘函子后，这个层变为 Zariski 层 $product_(x in X) x_* I_x$，即若干摩天楼层的直积。这样的层是松弛的，从而是 ${H^q_#[Zar] (X, -)}_(q>=0)$-零调的。
  #remark[
    如果诉诸一般的意象理论，会看到景之间有一对映射 $X_et arrows.rl X_#[Zar]$，它诱导出 $epsilon$ 的一个正合左伴随，从而使 $epsilon$ 把内射对象映到内射对象。不过，我更愿意采用简单、易读的权宜论证，而不愿只为了一个技术性条件就去引入一般意象理论。
  ]
  
  由 Grothendieck–Leray 谱序列，我们得到：
  $
    E_2^(p,q) = H^p_#[Zar] (X, R^q epsilon (cal(M)_et)) => H^(p+q)_et (X, cal(M)_et)
  $
  因此，要证明 $H^p_#[Zar] (X, cal(M)) cong H^p_et (X, cal(M)_et)$，只需证明这个谱序列退化，而这又只需证明对一切 $q >= 1$ 都有 $R^q epsilon (cal(M)_et) = 0$。

  对任意对象 $cal(F) in cAb(X_et)$，取内射消解 $0 -> cal(F) -> cal(I)^bullet$。再对这条链复形施加 $epsilon$，得到 $0 -> epsilon(cal(F)) -> epsilon(cal(I)^bullet)$。此时：
  $
    R^q epsilon (cal(F)) = h^q (0 -> epsilon(cal(I)^bullet))
  $
  由 Zariski 层理论，这个层是 $U |-> h^q (0 -> epsilon(cal(I)^bullet)(U)) = H^q_et (U, cal(F))$ 的 Zariski 层化。因此，要证明 $R^q epsilon (cal(M)_et) = 0$，只需证明：对 $X$ 的 Zariski 拓扑的某一组基中的每个元素 $U$，都有 $H^q_et (U, cal(M)_et) = 0$。然而，由前面的引理，对一切仿射开集 $U subset X$ 都有：
  $
    H^q_et (U, cal(M)_et) = H^q_et (U, (cal(M)|_U)_et) = 0
  $
  至此证毕。
]
