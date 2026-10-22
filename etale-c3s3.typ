#import "void-import.typ": *

== 平展基本群 $pi_1^et (X)$

仿照拓扑情形，我们定义平展基本群：

#definition(name: <defn-etale-fundamental-group>)[
  $X$ 关于基点 $ol(x)$ 的*平展基本群*，定义为：
  $
    pi_1^et (X, ol(x)) := Aut(F_(ol(x)))
  $
  它是纤维函子 $F_(ol(x)) : FEt_X -> cSet^"fin"$ 的自同构群。也就是说，它是由自然同构 $gamma: F_(ol(x)) -> F_(ol(x))$ 构成的群。
]

#lemma(name: <galois-grp-exact-seq>)[
  设 $f: Z -> Y$ 是 $FEt_X$ 中的态射，其中 $Y, Z$ 都有限。假定 $Z\/X$ 与 $Y\/X$ 都是 Galois 的，则 $Z\/Y$ 也必是 Galois 的，且有自然的正合列：
  $
    1 -> Aut(Z\/Y) -> Aut(Z\/X) -> Aut(Y\/X) -> 1
  $
]
#proof[
  我们先构造态射 $Phi: Aut(Z\/X) -> Aut(Y\/X)$。取 $Z$ 的几何点 $ol(z)$、$Y$ 的几何点 $ol(y)$ 与 $X$ 的几何点 $ol(x)$，使三者相容。任取 $sigma in Aut(Z\/X)$，考虑 $Y$ 的几何点 $f(sigma(ol(z)))$。这个几何点位于 $ol(x)$ 之上；又因 $Y\/X$ 是 Galois 的，$Aut(Y\/X)$ 在纤维 $F_(ol(x)) (Y)$ 上忠实且传递地作用。因此存在唯一的 $tau in Aut(Y\/X)$ 使得 $tau(ol(y)) = f(sigma(ol(z)))$。于是定义 $Phi(sigma) = tau$。

  换言之，$tau = Phi(sigma)$ 是 $Aut(Y\/X)$ 中唯一满足 $tau(f(ol(z))) = f(sigma(ol(z)))$ 的元素。由于 $Z$ 连通，任何 $X$-态射 $Z -> Y$ 只要在单个几何点上一致就必须相等，故这个条件等价于 $tau compose f = f compose sigma$。特别地，$Phi$ 与 $ol(z),ol(y),ol(x)$ 的选取无关。此外，$Phi$ 确实是群同态：
  $
    f compose sigma_1 compose sigma_2 = Phi(sigma_1) compose f compose sigma_2 = Phi(sigma_1) compose Phi(sigma_2) compose f
  $
  从而 $Phi(sigma_1 compose sigma_2) = Phi(sigma_1) compose Phi(sigma_2)$。下面看 $Phi$ 的核。$sigma in Aut(Z\/X)$ 属于 $ker(Phi)$，当且仅当 $f = f compose sigma$，也就是说 $sigma$ 是 $Y$-态射。换言之，我们得到了正合列：
  $
    1 -> Aut(Z\/Y) -> Aut(Z\/X) ->^Phi Aut(Y\/X)
  $
  接着我们同时证明右正合性与 $Z\/Y$ 是 Galois 的。首先注意 $abs(F_(ol(x))(Z)) = abs(F_(ol(x))(Y)) abs(F_(ol(y))(Z))$，因为对 $Y$ 的任一其他几何点 $ol(y')$，只要它同样位于 $ol(x)$ 之上，根据平坦性就有 $abs(F_(ol(y'))(Z)) = abs(F_(ol(y))(Z))$。现在：
  $
    abs(F_(ol(x))(Y)) = abs(Aut(Y\/X)) >= abs(im(Phi)) = (abs(Aut(Z\/X)))/(abs(Aut(Z\/Y))) = (abs(F_(ol(x))(Z)))/(abs(Aut(Z\/Y)))
  $
  从而 $abs(Aut(Z\/Y)) >= abs(F_(ol(x))(Z))\/abs(F_(ol(x))(Y)) = abs(F_(ol(y))(Z))$。与此同时，由于 $Aut(Z\/Y)$ 在 $F_(ol(y))(Z)$ 上忠实作用，$<=$ 自动成立。于是等号成立，且 $im(Phi) = Aut(Y\/X)$；这既说明 $Z\/Y$ 是 Galois 的，又给出正合列：
  $
    1 -> Aut(Z\/Y) -> Aut(Z\/X) ->^Phi Aut(Y\/X) -> 1
  $
]

#theorem(name: <pi1et-as-invlim>)[
  平展基本群是 Galois 群逆向系统的极限。更明确地说，设 $I$ 是带基点 Galois 覆叠空间 $(X_i, ol(x_i)) -> (X, ol(x))$ 构成的正向集。则：
  $
    pi_1^et (X, ol(x)) = invlim_(i in I) Aut(X_i\/X)^opp
  $
  也就是说，这个逆向极限的过渡映射由 @galois-grp-exact-seq 给出。

  特别地，这给 $pi_1^et (X, ol(x))$ 赋予了投射有限群的结构。
  
  #example[
    在 $X = Spec(K)$ 这个例子里，$I$ 是全体中间 Galois 扩张 $K subset L subset K^sep$ 构成的范畴。于是：
    $
      pi_1^et (Spec(K), Spec(K^sep)) = invlim_(i in I) Gal(L\/K) = Gal(K^sep\/K)
    $
    它是 $K$ 的绝对 Galois 群。
  ]
]
#proof[
  先说明这个逆向极限是良定义的。指标范畴 $I$ 是余滤过的。

  对每个 Galois 覆叠空间 $(X_i, ol(x_i))$，其自同构群 $Aut(X_i\/X)$ 在 $F_(ol(x)) (X_i)$ 上传递且忠实地作用。因此存在同构：
  $
    eta_i: Aut(X_i\/X) -> F_(ol(x)) (X_i), g |-> g(ol(x_i))
  $

  我们构造映射：
  $
    Psi: pi_1^et (X, ol(x)) = Aut(F_(ol(x))) &-> invlim_(i in I) Aut(X_i\/X)^opp \

    gamma &|-> (eta_i^(-1) (gamma(ol(x_i))))_(i in I)
  $
  换言之，对每个 $X_i$，我们都把 $gamma$ 送到唯一满足 $sigma_i (ol(x_i)) = gamma(ol(x_i))$ 的 $sigma_i in Aut(X_i\/X)$。
  
  每个映射 $pi_1^et (X, ol(x)) -> Aut(X_i\/X)^opp, gamma |-> eta_i^(-1) (gamma(ol(x_i)))$ 都是群同态。事实上，取 $gamma, delta in pi_1^et (X, ol(x))$，设它们在该映射下的像分别为 $sigma_gamma, sigma_delta$，则
  $
    sigma_gamma sigma_delta (ol(x_i)) = sigma_gamma (delta(ol(x_i))) = delta (sigma_gamma (ol(x_i))) = delta(gamma(ol(x_i)))
  $
  （注意 $gamma$ 与 $delta$ 的次序颠倒了。这正是要在 $Aut(X_i\/X)^opp$ 里取反群的原因。）
  
  这些同态与逆向系统 $I$ 相容。事实上，给定态射 $f: (X_j, ol(x_j)) -> (X_i, ol(x_i))$，令 $sigma_i (ol(x_i)) = gamma(ol(x_i))$、$sigma_j (ol(x_j)) = gamma(ol(x_j))$。则：
  $
    sigma_i (f(ol(x_j))) = sigma_i (ol(x_i)) = gamma(ol(x_i)) = gamma(f(ol(x_j))) = f(gamma(ol(x_j))) = f(sigma_j (ol(x_j)))
  $
  其中 $gamma(f(ol(x_j))) = f(gamma(ol(x_j)))$ 来自 $gamma$ 的自然性。于是在过渡映射 $Aut(X_j\/X) -> Aut(X_i\/X)$ 下 $sigma_j |-> sigma_i$，这正是所需的相容性。
  
  只需证明 $Psi$ 是单射兼满射。先看单射性。若 $gamma in ker(Psi)$，则它在每个 $i$ 处都映到 $id_(X_i)$，即对每个 $i$ 都有 $gamma(ol(x_i)) = ol(x_i)$。于是对每个带基点平展覆叠空间 $(Y, ol(y)) -> (X, ol(x))$，都可以取它的 Galois 闭包，那是某个 $X_i$：
  $
    (X_i, ol(x_i)) ->^f (Y, ol(y)) -> (X, ol(x))
  $
  由此 $gamma(ol(y)) = gamma(f(ol(x_i))) = f(gamma(ol(x_i))) = f(ol(x_i)) = ol(y)$。也就是说，对每个 $Y in FEt_X$ 与每个 $ol(y) in F_(ol(x)) (Y)$，都有 $gamma(ol(y)) = ol(y)$。因此作为 $F_(ol(x))$ 的自然自同构，$gamma$ 就是恒等态射。

  剩下要证满射性。固定元素 $(sigma_i)_(i in I) in invlim_(i in I) Aut(X_i\/X)^opp$。如下定义候选的 $gamma in Aut(F_(ol(x)))$：对每个 $Y in FEt_X$ 与每个 $ol(y) in F_(ol(x)) (Y)$，取 Galois 覆叠空间 $X_i$，并取分解 $(X_i, ol(x_i)) ->^f (Y, ol(y)) -> (X, ol(x))$，然后令 $gamma(ol(y)) := f(sigma_i (ol(x_i)))$。这个构造与 $i$ 的选取无关。事实上，若选了两个下标 $i,j$，则存在第三个 $k in I$，使下图交换：
  // https://q.uiver.app/#r=typst&q=WzAsNSxbMCwxLCIoWF9rLG9sKHhfaykpIl0sWzEsMCwiKFhfaSxvbCh4X2kpKSJdLFsxLDIsIihYX2osb2woeF9qKSkiXSxbMiwxLCIoWSxvbCh5KSkiXSxbMywxLCIoWCxvbCh4KSkiXSxbMCwxLCJnX2kiXSxbMCwyLCJnX2oiLDJdLFsxLDMsImZfaSJdLFsyLDMsImZfaiIsMl0sWzMsNF1d
  #context align(center, diagram({
    node((-2, 0), [$(X_k,ol(x_k))$])
    node((-1, -1), [$(X_i,ol(x_i))$])
    node((-1, 1), [$(X_j,ol(x_j))$])
    node((0, 0), [$(Y,ol(y))$])
    node((1, 0), [$(X,ol(x))$])
    edge((-2, 0), (-1, -1), [$g_i$], label-side: left, "->")
    edge((-2, 0), (-1, 1), [$g_j$], label-side: right, "->")
    edge((-1, -1), (0, 0), [$f_i$], label-side: left, "->")
    edge((-1, 1), (0, 0), [$f_j$], label-side: right, "->")
    edge((0, 0), (1, 0), "->")
    edge((-2, 0), (0, 0), "->", [$f_k$], label-side: center)
  }, crossing-fill: thm-box-curr-color()))
  因此要说明用 $i$ 和用 $j$ 分别定义的 $gamma(ol(y))$ 相同，只需说明用 $i$ 和用 $k$ 分别定义的结果相同。事实上，
  $
    f_k (sigma_k (ol(x_k))) &= f_i (g_i (sigma_k (ol(x_k)))) \
    &= f_i (sigma_i (g_i (ol(x_k)))) #[由过渡映射的定义] \
    &= f_i (sigma_i (ol(x_i)))
  $
  接下来要证的是：这样定义出的 $gamma$ 先验地只是对每个 $Y in FEt_X$ 给出集合映射 $F_(ol(x)) (Y) -> F_(ol(x)) (Y)$，而它实际上是 $F_(ol(x))$ 的自然自同构。对 $FEt_X$ 中的每个态射 $f: (Z, ol(z)) -> (Y, ol(y))$，我们要证 $f(gamma(ol(z))) = gamma(ol(y)) = gamma(f(ol(z)))$。事实上，先取 Galois 闭包 $(X_i, ol(x_i)) -> (Y, ol(y))$，再依复合覆叠空间的存在性（@fet-first-props (2)）与 Galois 闭包的存在性（@galois-closure-exists），取 $(X_j, ol(x_j))$ 使下图交换：
  // https://q.uiver.app/#r=typst&q=WzAsNCxbMCwwLCIoWF9qLG9sKHhfaikpIl0sWzIsMCwiKFhfaSxvbCh4X2kpKSJdLFswLDIsIihaLCBvbCh6KSkiXSxbMiwyLCIoWSwgb2woeSkpIl0sWzIsMywiZiIsMl0sWzEsMywiZl9pIl0sWzAsMSwiZyJdLFswLDIsImZfaiIsMl1d
  #align(center, diagram({
    node((-1, -1), [$(X_j,ol(x_j))$])
    node((1, -1), [$(X_i,ol(x_i))$])
    node((-1, 1), [$(Z, ol(z))$])
    node((1, 1), [$(Y, ol(y))$])
    edge((-1, 1), (1, 1), [$f$], label-side: right, "->")
    edge((1, -1), (1, 1), [$f_i$], label-side: left, "->")
    edge((-1, -1), (1, -1), [$g$], label-side: left, "->")
    edge((-1, -1), (-1, 1), [$f_j$], label-side: right, "->")
  }))
  现在：
  $
    gamma(ol(y)) &= f_i (sigma_i (ol(x_i))) #[由 $gamma$ 的定义] \
    &= f_i (sigma_i (g(ol(x_j)))) \
    &= f_i (g(sigma_j (ol(x_j)))) #[由过渡映射的定义] \
    &= f(f_j (sigma_j (ol(x_j)))) \
    &= f(gamma(ol(z))) #[由 $gamma$ 的定义]
  $
  至此 $Psi$ 的满射性证完。总之，我们构造了典范同构：
  $
    Psi: pi_1^et (X, ol(x)) &-> invlim_(i in I) Aut(X_i\/X)^opp \
    gamma &|-> (sigma_i)_(i in I) #[其中] sigma_i (ol(x_i)) = gamma(ol(x_i))
  $
]

#corollary[
  给 $pi_1^et (X, ol(x))$ 装上由下式给出的投射有限拓扑：
  $
    pi_1^et (X, ol(x)) = invlim_(i in I) Aut(X_i\/X)^opp
  $
  在这个拓扑下，对每个 $Z in FEt_X$，$pi_1^et (X, ol(x))$ 在 $F_(ol(x)) (Z)$ 上的作用是连续的。这定义了一个函子：
  $
    F_(ol(x)): FEt_X -> GSet(pi_1^et (X, ol(x)))^#[fin,cont]
  $
  即从 $FEt_X$ 到带连续 $pi_1^et (X, ol(x))$-作用的有限集构成的范畴。
]
#proof[
  剩下只需说明 $pi_1^et (X, ol(x))$ 在 $F_(ol(x)) (Z)$ 上的作用连续。事实上，任取 Galois 闭包 $X_i -> Z$；按上面建立同构 $pi_1^et (X, ol(x)) = invlim_(i in I) Aut(X_i\/X)^opp$ 的方式，元素 $(sigma_i)_(i in I) in pi_1^et (X, ol(x))$ 在 $F_(ol(x)) (Z)$ 上的作用由 $sigma_i$ 决定。于是 $pi_1^et (X, ol(x))$ 的一个有限指数的正规子群固定 $F_(ol(x))(Z)$。
]

#theorem[
  $
    F_(ol(x)): FEt_X -> GSet(pi_1^et (X, ol(x)))^#[fin,cont]
  $
  定义了范畴等价，并与下图相容：
  // https://q.uiver.app/#r=typst&q=WzAsMyxbMCwwLCJGRXRfWCJdLFsyLDAsIkdTZXQocGlfMV5ldCAoWCwgb2woeCkpKV4jW2Zpbixjb250XSJdLFsxLDIsImNTZXReI1tmaW5dIl0sWzAsMSwiRl8ob2woeCkpIl0sWzAsMiwiRl8ob2woeCkpIiwyXSxbMSwyLCIjW2ZvcmdldF0iXV0=
  #align(center, diagram({
    node((-1, -1), [$FEt_X$])
    node((1, -1), [$GSet(pi_1^et (X, ol(x)))^#[fin,cont]$])
    node((0, 1), [$cSet^#[fin]$])
    edge((-1, -1), (1, -1), [$F_(ol(x))$], label-side: left, "->")
    edge((-1, -1), (1, -1), [$tilde$], label-side: right)
    edge((-1, -1), (0, 1), [$F_(ol(x))$], label-side: right, "->")
    edge((1, -1), (0, 1), [$#[forget]$], label-side: left, "->")
  }, spacing: 2em))
]
#proof[
  本质满性：
  #proof[
    设 $T$ 是带连续 $pi_1^et (X, ol(x))$-作用的有限集。可把 $T$ 按 $pi_1^et (X, ol(x))$-轨道分解为 ${T_s}$。若对每个 $T_s$ 都能找到 $Z_s in FEt_X$，使得 $F_(ol(x)) (Z_s) cong T_s$（作为 $pi_1^et (X, ol(x))$-集），则 $F_(ol(x)) (union.sq.big_s Z_s) cong T$（同样作为 $pi_1^et (X, ol(x))$-集）。于是问题归到 $T$ 在该作用下传递的情形。

    由于 $G = pi_1^et (X, ol(x))$ 是投射有限群，且传递地作用在 $T$ 上，故作为 $G$-集有 $T cong G\/H$，其中 $H <= G$ 是某个有限指数子群。按把 $G$ 表成逆向极限的构造方式，存在某个 $i$ 与 $G$ 的正规子群 $N$，使得 $N <= H$ 且 $G\/N = Aut(X_i\/X)$。设 $ol(H)$ 是 $H$ 在 $G\/N = Aut(X_i\/X)$ 中的像。则作为 $G$-集，$T cong G\/H cong Aut(X_i\/X)\/ol(H)$。

    可以取 $Z = X_i\/ol(H)$，其构造依 @galois-theory-of-coverings (2)。由 @affine-sch-quotient (2)，$X_i -> Z$ 的纤维恰好是 $ol(H)$-轨道，即 $Spec(k(z)) = (X_i)_z\/ol(H)$。过渡到几何纤维这一步是平坦基变换，因此保持商，于是作为 $Aut(X_i\/X)$-集有 $F_(ol(x))(Z) cong F_(ol(x))(X_i)\/ol(H) cong Aut(X_i\/X)\/ol(H) cong T$，从而作为 $G$-集也同构。

    #suppress-qed
  ]

  全忠实性：
  #proof[
    对任意 $Z, Y in FEt_X$，考虑：
    $
      F_(ol(x)): Hom_X (Z, Y) -> Hom_(pi_1^et (X, ol(x))) (F_(ol(x)) (Z), F_(ol(x)) (Y))
    $
    要证这个映射是双射。把 $Z, Y$ 写成各自连通分支的并：$Z = union.sq.big_t Z_t, Y = union.sq.big_s Y_s$，于是需要处理：
    $
      Hom_X (Z, Y) = product_t union.sq.big_s Hom_X (Z_t, Y_s) -> Hom_(pi_1^et (X, ol(x))) (F_(ol(x)) (Z), F_(ol(x)) (Y)) = product_t union.sq.big_s Hom_(pi_1^et (X, ol(x))) (F_(ol(x)) (Z_t), F_(ol(x)) (Y_s))
    $
    这样只需对每对 $Z_t$ 与 $Y_s$ 证明双射性，问题就归到 $Z, Y$ 连通的情形。

    - 单射性：设两个映射 $f,g: Z -> Y$ 满足 $F_(ol(x)) (f) = F_(ol(x)) (g)$。取 $ol(z) in F_(ol(x)) (Z)$。由 $f(ol(z)) = g(ol(z))$ 及 $Z$ 连通，依 @fet-first-props (1) 得 $f = g$。

    - 满射性：由纤维积的泛性质，有：
      $
        F_(ol(x)) (Y times_X Z) = F_(ol(x)) (Y) times F_(ol(x)) (Z)
      $
      任取元素 $phi in Hom_(pi_1^et (X, ol(x))) (F_(ol(x)) (Z), F_(ol(x)) (Y))$，考虑它的图 $Gamma_phi subset F_(ol(x)) (Y) times F_(ol(x)) (Z) = F_(ol(x)) (Y times_X Z)$。由于 $phi$ 是 $pi_1^et (X, ol(x))$-等变的，子集 $Gamma_phi$ 是 $pi_1^et (X, ol(x))$-不变的。按上面证明本质满性时所用的构造，存在开闭子概形 $W subset Y times_X Z$，使得作为 $pi_1^et (X, ol(x))$-集有 $F_(ol(x)) (W) cong Gamma_phi$。

      考虑投影映射 $p_Z: W -> Z$。按定义，$F_(ol(x)) (p_Z): Gamma_phi -> F_(ol(x)) (Z)$ 就是把图投影到第二个因子，因而是双射。由 @fet-first-props (4) 知 $p_Z$ 是同构。于是态射：
      $
        Z -->^(p_Z^(-1)) W -->^(p_Y) Y
      $
      是 $FEt_X$ 中的态射，在纤维上诱导映射 $F_(ol(x)) (Z) -> Gamma_phi -> F_(ol(x)) (Y)$，而这就是 $phi$。

    #suppress-qed
  ]
  全忠实性与本质满性都已证，可见 $F_(ol(x)): FEt_X -> GSet(pi_1^et (X, ol(x)))^#[fin,cont]$ 确实是范畴等价。
]

这样我们就得到了与拓扑基本群情形完全对应的结论：$bold("Cov")(X) -> GSet(pi_1^"top" (X, x)), 
(p: X' -> X) |-> p^(-1) (x)$ 是范畴等价。我们为概形建立了 Galois 理论，并用群 $pi_1^et (X, ol(x))$ 对 $FEt_X$ 作了分类。

#corollary(name: <fet-trivializes-fet-locally>)[
  每个有限平展覆叠 $X' -> X$ 都在有限平展局部意义下平凡。
]
#proof[
  这个证明有好几种做法，最快的还是走平展基本群。
  不妨设 $X$ 连通，因为可以在 $X$ 的每个连通分支上分别把 $X'$ 平凡化。固定 $X$ 的一个基点 $ol(x)$；由平展基本群的理论，$X'$ 对应于一个对象：
  $
    S in GSet(pi_1^et (X, ol(x)))^#[fin,cont]
  $
  于是 $pi_1^et (X, ol(x))$ 的作用经过一个有限商，这个有限商对应某个 Galois 覆叠 $(Z, ol(z)) in FEt_X$。换言之，$pi_1^et (Z, ol(z))$ 平凡地作用在 $S$ 上。现在，作为 $pi_1^et (Z, ol(z))$-集，$S$ 对应于 $FEt_Z$ 中的基变换 $X' times_X Z -> Z$，因此 $X' times_X Z -> Z$ 是平凡覆叠空间，即 $X' times_X Z$ 是若干份 $Z$ 的不交并。
]

/*
#date[
  第 5 讲，2025/10/22
  #set align(left)

  /*
  回忆上一讲，我们介绍了平展基本群 $pi_1^et (X, ol(x))$。设 $X$ 是连通的 Noether 概形，并固定几何点 $ol(x): Spec(Omega) -> X$。于是有函子 $FEt_X -> cSet^"fin", (f: Z -> X) |-> f^(-1)(ol(x))$。我们按下式给 $pi_1^et (X, ol(x))$ 装上拓扑：
  $
    pi_1^et (X, ol(x)) := Aut(F_(ol(x))) < product_(Z in FEt_X) Aut(F_(ol(x)) (Z))
  $
  即取右端那个乘积上的积拓扑所诱导的子空间拓扑。
  
  我们还得到：
  #theorem[
    （$(X, ol(x))$ 的 Galois 理论）$FEt_X$ 与 $pi_1^et (X, ol(X))"-"cSet^("fin,cont")$（即带 $pi_1^et (X, ol(X))$ 连续作用的有限集）之间有自然的范畴等价，且与 $F_(ol(x)) : FEt_X -> cSet^"fin"$ 以及遗忘函子 $pi_1^et (X, ol(X))"-"cSet^("fin,cont")-> cSet^"fin"$ 相容。
  ]
  
  我们还用 Galois 覆叠给出了 $pi_1^et$ 的另一种描述。回忆：$(f: Z -> X) in FEt_X$ 连通时称为 Galois 的 $:<==> \#Aut(Z\/X) = \#F_(ol(x)) (Z) <==> Z\/Aut(Z\/X)^opp cong X$。接着考虑：
  $
    I = {(X_i, ol(x_i)) "为" (X, ol(x)) "上的带基点 Galois 覆叠"}
  $
  并证明了：
  $
    dirlim_(i in I) Hom_X (X_i, Z) cong F_(ol(x)) (Z) \
    pi_1^et (X, ol(x)) cong invlim_(i in I) Aut(X_i\/X)^opp
  $
  #example[
    设 $X = Spec(K)$，并固定可分闭包 $K^sep\/K$。则：
    $
      pi_1^et (Spec(K), Spec(K^sep)) cong invlim_(L\/K "有限 Galois") Gal(L\/K) cong Gal(K^sep\/K)
    $
    它就是绝对 Galois 群。
  ]*/
  
  这一描述的关键在于：
  
  + 给定 $(X, ol(x)) $ 上连通的带基点平展覆叠空间 $(Z, ol(z)), (Z', ol(z')) $，它们之间与覆叠相容的映射至多有一个。
  
  + 设 $Z$ 是 $X$ 上连通的平展覆叠空间，$G <= Aut(Z\/X)^opp$ 是有限子群。则 $Z -> Z\/G$ 是 Galois 覆叠，且 $G cong Aut(Z\/(Z\/G))^opp$。
  
  为看出 $Z -> Z\/G$ 平展，需要对任意 $z in Z$ 验证惯性子群：
  $
    G_i (z) := {g in G: g(z) = z, g "固定" κ(z)}
  $
  是平凡的。而事实上，
  $
    G_i (z) & = {g in G: g dot ol(z) = ol(z) "其中" ol(z) = Spec(κ(z)^sep) -> {z} subset Z}
  $
  由 (1) 可知它只能有一个元素。
  
  第 (2) 条在证明 $FEt_X -> pi_1^et (X, ol(X))"-"cSet^("fin,cont") $ 本质满时很有用。事实上，对任意 $pi_1^et$-集 $T$ 都可以作轨道分解，于是只需为每个传递的 $pi_1^et$-集 $T$ 配上相应的平展覆叠空间。设 $S$ 是某点的稳定子群，$N$ 是 $pi_1^et$ 的有限指数正规子群，使得 $N <= S <= pi_1^et$。则 $pi_1^et\/N$ 对应 Galois 覆叠 $X_i$，$pi_1^et\/S$ 对应覆叠 $X_i -> X_i\/(S\/N) $。
]*/
