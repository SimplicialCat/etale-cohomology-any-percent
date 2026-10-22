#import "void-import.typ": *

== 乘法群的 $H^1$

#proposition[
  设 $X = Spec(A)$ 是仿射概形，则有典范同构：
  $
    H^1_et (X, GG_m) cong Pic(X) = H^1_#[Zar] (X, cal(O)_X^times)
  $
  这个同构可以显式地写成下面这样：Zariski 景与平展景上的 $H^1$ 都可用 $caron(H)^1$ 计算，于是有映射： 
  $
    caron(H)^1_#[Zar] (X, cal(O)_X^times) &-> Pic(X) = caron(H)^1_et (X, GG_m) \
    (u_(i,j) in cal(O)_X^times (U_i ∩ U_j))_(i,j) &|-> (u_(i,j) in GG_m (U_i times_X U_j))_(i,j)
  $
  其中每个 Zariski 开覆盖都是平展覆盖，我们只是把 Čech 余圈原样保留下来。 
]
#proof[
  我们直接构造一个映射： 
  $
    Phi: caron(H)^1_et (X, GG_m) -> Pic(X)
  $
  $X$ 仿射，故拟紧；于是每个平展覆盖都能加细为一个由有限多个仿射概形组成的子覆盖。取不交并，便得到：
  $
    caron(H)^1_et (X, GG_m) = dirlim_(cal(U) in cal(S)) caron(H)^1_et (cal(U), GG_m)
  $
  其中 $cal(S)$ 由那些只含一个形如 $cal(U) = {X' = Spec(A') -> X}$ 的映射的平展覆盖组成。现在：
  $
    caron(H)^1_et (cal(U), GG_m) = (ker((A'')^times -> (A''')^times, a'' |-> i_(12)(a'') i_(23)(a'') i_(13) (a'')^(-1)))/(im((A')^times -> (A'')^times, a' |-> a' otimes a'^(-1)))
  $
  其中 $i_(12), i_(23), i_(13): A'' -> A'''$ 是关于各分量的三个包含映射。下面定义 $Phi_(cal(U)): caron(H)^1_et (cal(U), GG_m) -> Pic(X)$ 如下： 

  - 任给一个类 $alpha in caron(H)^1_et (cal(U), GG_m)$，设它由 $u in (A'')^times$ 代表。此时 $(times u): A'' -> A''$ 是满足余圈条件的同构，也就是 $A'$ 到 $A$ 的某个下降数据。由 fpqc 下降，存在唯一的 $A$-模 $M$，并配有同构 $phi: M' := M otimes_A A' -> A'$，它把典范下降数据 $eta: M' otimes_A A' -> A' otimes_A M'$ 与乘以 $u$ 等同起来。 

    由于局部自由性沿忠实平坦态射下降，$M$ 是秩为 1 的局部自由 $A$-模，从而给出元素 $[M] in Pic(X)$。 

  换言之，$Phi_(cal(U)) ([u]) = [M]$，其中 $[M] in Pic(X)$ 是满足下述条件的唯一元素：存在同构 $phi: M' -> A'$，使得典范下降数据 $eta: M' otimes_A A' -> A' otimes_A M'$ 是如下复合： 
  $
    M' otimes_A A' -->^(phi otimes id) A'' -->^(times u) A'' -->^(id otimes phi^(-1)) A' otimes_A M'
  $

  下面有几件事要验证。 

  - 上面定义的映射 $ker((A'')^times -> (A''')^times) -> Pic(X)$ 是群同态。事实上，设 $u_1, u_2 in (A'')^times$ 分别映到 $[M_1], [M_2] in Pic(X)$，我们断言 $u_1 u_2$ 映到 $[M_1 otimes_A M_2]$。令 $N = M_1 otimes_A M_2$，取同构 $psi: N' -> A'$ 为下述映射的复合：$M_1 otimes_A M_2 otimes A' -->^(id otimes phi_2) M_1 otimes_A A' -->^(phi_1) A'$。 

    现在考虑交换图表： 
    // https://q.uiver.app/#r=typst&q=WzAsNixbMCwwLCJOJyBvdGltZXNfQSBBJyJdLFs0LDAsIkEnIG90aW1lc19BIE4nIl0sWzIsMCwiTSdfMSBvdGltZXNfQSBNJ18yIl0sWzAsMiwiQScnIl0sWzIsMiwiQScnIl0sWzQsMiwiQScnIl0sWzAsMiwiaWRfKE1fMSkgb3RpbWVzIGV0YV8yIl0sWzIsMSwiZXRhXzEgb3RpbWVzIGlkXyhNXzEpIl0sWzAsMywicHNpIG90aW1lcyBpZCIsMl0sWzIsNCwicGhpXzEgb3RpbWVzIHBoaV8yIiwyXSxbMSw1XSxbMyw0LCJ0aW1lcyB1XzIiXSxbNCw1LCJ0aW1lcyB1XzEiXV0=
    #align(center, diagram({
      node((-1, -1), [$N' otimes_A A'$])
      node((3, -1), [$A' otimes_A N'$])
      node((1, -1), [$M'_1 otimes_A M'_2$])
      node((-1, 1), [$A''$])
      node((1, 1), [$A''$])
      node((3, 1), [$A''$])
      edge((-1, -1), (1, -1), [$id_(M_1) otimes eta_2$], label-side: left, "->")
      edge((1, -1), (3, -1), [$eta_1 otimes id_(M_1)$], label-side: left, "->")
      edge((-1, -1), (-1, 1), [$psi otimes id$], label-side: right, "->")
      edge((1, -1), (1, 1), [$phi_1 otimes phi_2$], label-side: right, "->")
      edge((3, -1), (3, 1), "->", $id otimes psi$)
      edge((-1, 1), (1, 1), [$times u_2$], label-side: left, "->")
      edge((1, 1), (3, 1), [$times u_1$], label-side: left, "->")
    }))
    其中第一行是 $N'$ 的典范下降数据。这就证明了 $u_1 u_2$ 映到 $[M_1 otimes_A M_2]$。 

  - 上面定义的 $Phi_(cal(U))$ 是良定义的，且为单射。也就是说，要证明 $u in (A'')^times$ 映到 $[A] in Pic(X)$ 当且仅当 $u$ 形如 $a' otimes a'^(-1)$。
    
    （$==>$）若 $u$ 映到 $[A] in Pic(X)$，则存在同构 $phi: A' -> A'$，使得典范下降数据 $id: A' otimes_A A' -> A' otimes_A A'$ 是如下复合：
    $
      A' otimes_A A' -->^(phi otimes id) A'' -->^(times u) A'' -->^(id otimes phi^(-1)) A' otimes_A A'
    $
    设 $phi$ 是乘以 $a'^(-1) in (A')^times$ 给出的同构，便得到 $u = a' otimes a'^(-1)$。 

    （$<==$）若 $u = a' otimes a'^(-1)$，取 $phi: A' -> A'$ 为乘以 $a'^(-1)$ 的映射，于是：
    $
      A' otimes_A A' -->^(phi otimes id) A'' -->^(times u) A'' -->^(id otimes phi^(-1)) A' otimes_A A'
    $
    它就是典范下降数据 $id: A' otimes_A A' -> A' otimes_A A'$。因此 $u$ 映到 $[A] in Pic(X)$。 

  - $Phi_(cal(U))$ 与正向系统相容。 

    假设平展覆盖 $Spec(tilde(A)')$ 加细平展覆盖 $Spec(A') -> Spec(A)$，即有平展环映射 $A -> A' -> tilde(A)'$。给定元素 $u in A''$，它映到 $tilde(u) in tilde(A)''$；我们要证明由 $u$ 给出的与由 $tilde(u)$ 给出的 $Pic(Spec(A))$ 中的元素相同。为此，设 $[M] in Pic(Spec(A))$ 是 $u$ 的像。换言之，有同构 $phi: M otimes_A A' -> A'$，使得典范下降数据 $eta: (M otimes_A A') otimes_A A' -> A' otimes_A (M otimes_A A')$ 为：
    $
      (M otimes_A A') otimes_A A' -->^(phi otimes id) A' otimes_A A' -->^(times u) A' otimes_A A' -->^(id otimes phi^(-1)) A' otimes_A (M otimes_A A')
    $
    于是有同构 $tilde(phi): M otimes_A tilde(A)' -> tilde(A')$，它就是 $phi otimes_(A') id_(tilde(A)')$。这时便看出，典范下降数据 $tilde(eta): (M otimes_A tilde(A)') otimes_A tilde(A)' -> tilde(A)' otimes_A (M otimes_A tilde(A)')$ 无非是把 $eta$ 与 $tilde(A)' otimes_A tilde(A)'$ 在 $A' otimes_A A'$ 上作张量积的结果，因而为：
    $
      (M otimes_A tilde(A)') otimes_A tilde(A)' -->^(tilde(phi) otimes id) tilde(A)' otimes_A tilde(A)' -->^(times tilde(u)) tilde(A)' otimes_A tilde(A)' -->^(id otimes tilde(phi)^(-1)) tilde(A)' otimes_A (M otimes_A tilde(A)')
    $
    由下降的唯一性，$[M]$ 也是 $tilde(u)$ 的像。 

  单射性在取正向极限下保持，故取正向极限即得单射同态：
  $
    Phi: caron(H)^1_et (X, GG_m) -> Pic(X)
  $
  最后证明 $Phi$ 是满射。任取 $[M] in Pic(X)$，$M$ 是秩为 1 的局部自由 $A$-模。取 $X$ 的一个仿射开覆盖，使 $M$ 在其上平凡，再取不交并，便得到 Zariski 覆盖 $Spec(A') ->> Spec(A)$ 与同构 $phi: M otimes_A A' -> A'$。令 $cal(U) = {Spec(A') -> Spec(A)}$，并取元素 $u in (A'')^times$，使得典范下降数据 $M' otimes_A A' -> A' otimes_A M'$ 为： 
  $
    M' otimes_A A' -->^(phi otimes id) A'' -->^(times u) A'' -->^(id otimes phi^(-1)) A' otimes_A M'
  $
  于是 $Phi_(cal(U)) ([u]) = [M]$。因此 $Phi$ 是同构。证毕。 
  
  /*取不交并，不妨假设我们处理的是一个元素： 
  $
    u in caron(H)^1_et (cal(U), GG_m), cal(U) = {X' = Spec(A') ->> X}
  $
  特别地，$A -> A'$ 忠实平坦。展开定义，$u$ 由 $(A'')^times$ 中某个元素代表，这个元素以三种方式拉回成 $A'''$ 的自同构时满足余圈条件。换言之，这决定了 $A'$-模 $A'$ 到 $A$ 的某个下降数据。由 fpqc 下降，它下降到 $A$-模 $M$，满足 $M otimes_A A' cong A'$，其中下降数据里的同构就是乘以 $u$。由于局部自由性沿忠实平坦环映射下降，$M$ 是秩 1 的局部自由模。我们于是把 $u$ 送到元素 $[M] in Pic(Spec(A))$。 

  - 这个映射良定义。 

    假设平展覆盖 $Spec(tilde(A)')$ 加细 $Spec(A') -> Spec(A)$，即有平展环映射 $A -> A' -> tilde(A)'$。给定元素 $u in A''$，它映到 $tilde(u) in tilde(A)''$；我们要证明 $u$ 与 $tilde(u)$ 给出的 $Pic(Spec(A))$ 中元素相同。为此，设 $[M] in Pic(Spec(A))$ 是 $u$ 的像。换言之，有同构 $phi: M otimes_A A' -> A'$，使得典范下降数据 $eta: (M otimes_A A') otimes_A A' -> A' otimes_A (M otimes_A A')$ 为： 
    $
      (M otimes_A A') otimes_A A' -->^(phi otimes id) A' otimes_A A' -->^(times u) A' otimes_A A' -->^(id otimes phi^(-1)) A' otimes_A (M otimes_A A')
    $
    于是有同构 $tilde(phi): M otimes_A tilde(A)' -> tilde(A')$，它就是 $phi otimes_(A') id_(tilde(A)')$。这时便看出，典范下降数据 $tilde(eta): (M otimes_A tilde(A)') otimes_A tilde(A)' -> tilde(A)' otimes_A (M otimes_A tilde(A)')$ 无非是把 $eta$ 与 $tilde(A)' otimes_A tilde(A)'$ 关于 $A' otimes_A A'$ 作张量积，因而为： 
    $
      (M otimes_A tilde(A)') otimes_A tilde(A)' -->^(tilde(phi) otimes id) tilde(A)' otimes_A tilde(A)' -->^(times tilde(u)) tilde(A)' otimes_A tilde(A)' -->^(id otimes tilde(phi)^(-1)) tilde(A)' otimes_A (M otimes_A tilde(A)')
    $
    由下降的唯一性，$[M]$ 也是 $tilde(u)$ 的像。 

  - 这个映射是群同态： 

    设 $u_1, u_2 in A''$ 分别映到 $[M_1], [M_2] in Pic(Spec(A))$，并有同构 $phi_(1,2): M_(1,2) otimes_A A' -> A'$，按上面描述的方式把 $M_1, M_2$ 的典范下降数据与 $u_1, u_2$ 联系起来。再考虑 $N = M_1 otimes_A M_2$，以及同构 $psi: N otimes_A A' -->^(id_(M_1) otimes phi_2) M_1 otimes A' -->^(phi_1) A'$。此时 $N$ 的典范下降数据为： 
    $
      (M_1 otimes_A M_2 otimes_A A') otimes_A A' -->^(id_(M_1) otimes eta_2) (M_1 otimes_A A') otimes_A (M_2 otimes_A A') -->^(eta_1 otimes id_(M_2)) A' otimes_A (M_1 otimes_A M_2 otimes_A A')
    $
    应用同构 $phi_1, phi_2, psi$，便看出这个下降数据在 $psi$ 下就是乘以 $u_1 u_2$。证毕。 

  - 这个态射是满射。 

    对每个 $[M] in Pic(Spec(A))$，$M$ 都在 $Spec(A)$ 上 Zariski 局部平凡。于是存在局部同构 $f: Spec(A') ->> Spec(A)$，使得 $M otimes A' cong A'$。于是，$(A'')^times$ 中给出 $M otimes A'$ 的典范下降数据之同构的那个元素，就映到 $[M]$。 

  - 这个态射是单射。 

    给定 $u in (A'')^times$*/
]

#theorem(name: <h1-of-gm-is-pic>)[
  设 $X$ 是任意概形。则有典范同构：
  $
    H^1_et (X, GG_m) cong Pic(X) = H^1_#[Zar] (X, cal(O)_X^times)
  $
  这个同构可以显式地写成下面这样：Zariski 景与平展景上的 $H^1$ 都可用 $caron(H)^1$ 计算，于是有映射：
  $
    caron(H)^1_#[Zar] (X, cal(O)_X^times) & -> Pic(X) = caron(H)^1_et (X, GG_m) \
    (u_(i,j) in cal(O)_X^times (U_i ∩ U_j))_(i,j) & |-> (u_(i,j) in GG_m (U_i times_X U_j))_(i,j)
  $
  其中每个 Zariski 开覆盖都是平展覆盖，我们只是把 Čech 余圈原样保留下来。
]
#proof[
  正如 @etale-cohom-of-qcoh-sheaf 的证明中那样，遗忘函子： 
  $
    epsilon: cAb(X_et) -> cAb(X_#[Zar])
  $
  出现在如下谱序列中： 
  $
    E_2^(p,q) = H^p_#[Zar] (X, R^q epsilon (GG_m)) => H^(p+q)_et (X, GG_m)
  $
  五项正合列给出： 
  $
    0 -> H^1_#[Zar] (X, cal(O)_X^times) -> H^1_et (X, GG_m) -> H^0_#[Zar] (X, R^1 epsilon (GG_m)) -> dots.c
  $
  其中第一个映射正是定理陈述中给出的那个显式映射，展开定义即可验证。只需证明： 
  $
    R^1 epsilon (GG_m) = 0
  $
  而按 @etale-cohom-of-qcoh-sheaf 的证明，$R^1 epsilon (GG_m)$ 是预层 $cal(R): U |-> H^1_et (U, GG_m)$ 的 Zariski 层化。给定点 $x in X$，注意仿射开集构成 $x$ 处的一组邻域基。因此： 
  $
    cal(R)_x = dirlim_(x in U #[affine]) H^1_et (U, GG_m) cong dirlim_(x in U #[affine]) Pic(U)
  $
  这里用了上一个命题；其中正向系统的过渡映射就是 $x in V subset U$ 时的限制映射 $Pic(U) -> Pic(V)$。然而，任取 $[cal(L)] in Pic(U)$，都存在更小的仿射邻域 $x in V subset U$，使得 $cal(L)|_V cong cal(O)_V$，即 $cal(L)$ 在 $Pic(V)$ 中的像成为单位元。因此，正向极限 $dirlim_(x in U #[affine]) Pic(U)$ 中每个元素都是零。于是对一切 $x in X$ 都有 $cal(R)_x = 0$，从而 $cal(R) = 0$。而 $R^1 epsilon (GG_m)$ 作为 $cal(R)$ 的 Zariski 层化，必然为零。 
]
