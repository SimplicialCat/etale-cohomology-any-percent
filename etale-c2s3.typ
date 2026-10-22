#import "void-import.typ": *

== 无穷小提升判别法

看到 @etale-first-props 里那些命题的样子，你或许会想起什么：非分歧/平展态射在复合、基变换与消去下的表现，和分离/紧合态射颇为相似——尽管这两类态射在几何上截然不同。而分离/紧合态射可以用赋值判别法检验，因此非分歧/平展态射有类似的判别法，也就不那么令人意外了。事实上，这就是无穷小提升判别法。 

#definition(name: <defn-formal-morphisms>)[
  设 $f: X -> Y$ 是概形态射。对任意环 $A$、任意满足 $I^2 = 0$ 的理想 $I subset A$，以及任意外侧方块交换的图表： 
  // https://q.uiver.app/#r=typst&q=WzAsNCxbMSwwLCJYIl0sWzEsMSwiWSJdLFswLDAsIlNwZWMoQVxcL0kpIl0sWzAsMSwiU3BlYyhBKSJdLFswLDEsImYiXSxbMiwzXSxbMywxXSxbMiwwXSxbMywwLCIiLDEseyJzdHlsZSI6eyJib2R5Ijp7Im5hbWUiOiJkYXNoZWQifX19XV0=
  #align(center, diagram({
    node((1, 0), [$X$])
    node((1, 1), [$Y$])
    node((0, 0), [$Spec(A\/I)$])
    node((0, 1), [$Spec(A)$])
    edge((1, 0), (1, 1), [$f$], label-side: left, "->")
    edge((0, 0), (0, 1), "->")
    edge((0, 1), (1, 1), "->")
    edge((0, 0), (1, 0), "->")
    edge((0, 1), (1, 0), "-->")
  }))
  我们要考察的是：使图表交换的虚线箭头是否存在、是否唯一。 

  - 若这样的虚线箭头总是存在，则称 $f$ 为*形式光滑* (formally smooth)； 

  - 若这样的虚线箭头只要存在就唯一，则称 $f$ 为*形式非分歧* (formally unramified)； 

  - 若这样的虚线箭头总是存在且唯一，则称 $f$ 为*形式平展* (formally étale)。 
]

无穷小提升判别法断言：只要 $f$ 是局部有限展示的，形式光滑/非分歧/平展态射就恰好是光滑/非分歧/平展态射。为证明这一定理，我们先要对可能的提升作一些一般性讨论。 

#lemma(name: <classifying-diff-of-infinitesimal-lifts>)[
  设 $f: X -> Y$ 是概形态射。设 $T$ 是概形，$T_0$ 是 $T$ 的闭子概形，由满足 $cal(I)^2 = 0$ 的理想层 $cal(I) subset cal(O)_T$ 定义。考虑交换方块： 
  // https://q.uiver.app/#r=typst&q=WzAsNCxbMSwwLCJYIl0sWzEsMSwiWSJdLFswLDAsIlNwZWMoQVxcL0kpIl0sWzAsMSwiU3BlYyhBKSJdLFswLDEsImYiXSxbMiwzXSxbMywxXSxbMiwwLCJ1XzAiXV0=
  #align(center, diagram({
    node((1, 0), [$X$])
    node((1, 1), [$Y$])
    node((0, 0), [$T_0$])
    node((0, 1), [$T$])
    edge((1, 0), (1, 1), [$f$], label-side: left, "->")
    edge((0, 0), (0, 1), "->", $i$)
    edge((0, 1), (1, 1), "->", $v$, label-side: right)
    edge((0, 0), (1, 0), [$u_0$], label-side: left, "->")
  }))
  设 $cal(L)$ 是拓扑空间 $T$ 上由下式定义的集合层： 
  $
    cal(L)(U) = {u: U -> X: u compose i|_(U_0) = u_0|_(U_0), f compose u = v|_U}
  $ 
  则有典范作用： 
  $
    HHom_(cal(O)_(T_0)) (u_0^* Omega_(X\/Y), cal(I)) times cal(L) -> cal(L)
  $
  只要 $cal(L)(U) != emptyset$，这个作用在 $U$ 上的截面上就是单传递的。 
]
#proof[
  我们局部地构造这个层作用。取仿射开集 $U = Spec(A) subset T$，使得 $v(U)$ 含于 $Y$ 的某个仿射开集 $Spec(B)$ 中，$u_0 (U_0)$ 含于 $X$ 的某个仿射开集 $Spec(C)$ 中。于是在 $U$ 上，截面 $cal(L)(U)$ 恰好由使下图交换的那些提升组成： 
  // https://q.uiver.app/#r=typst&q=WzAsNCxbMCwwLCJTcGVjKEFcXC9JKSJdLFswLDEsIlNwZWMoQSkiXSxbMSwwLCJTcGVjKEMpIl0sWzEsMSwiU3BlYyhCKSJdLFswLDIsInVfMCJdLFsyLDMsImYiXSxbMSwzLCJ2IiwyXSxbMCwxXSxbMSwyLCIiLDEseyJzdHlsZSI6eyJib2R5Ijp7Im5hbWUiOiJkYXNoZWQifX19XV0=
  #align(center, diagram({
    node((0, 0), [$Spec(A\/I)$])
    node((0, 1), [$Spec(A)$])
    node((1, 0), [$Spec(C)$])
    node((1, 1), [$Spec(B)$])
    edge((0, 0), (1, 0), [$u_0$], label-side: left, "->")
    edge((1, 0), (1, 1), [$f$], label-side: left, "->")
    edge((0, 1), (1, 1), [$v$], label-side: right, "->")
    edge((0, 0), (0, 1), "->")
    edge((0, 1), (1, 0), "-->")
  }))
  其中 $tilde(I) = cal(I)|_(Spec(A))$。对两个这样的提升 $u_(1,2): Spec(A) -> Spec(C)$，设它们由映射 $u_(1,2)^\#: C -> A$ 诱导，则按定义有： 
  $
    u_1^\# compose f^\# = v^\# = u_2^\# compose f^\#: B -> A
  $
  并且 $u_(1,2)^\#$ 约化到 $A\/I$ 之后彼此一致。于是 $delta = u_2^\# - u_1^\#: C -> A$ 的像落在 $I$ 中。我们断言 $delta$ 是 $B$-导子。事实上： 
  $
    delta(f^\# (b)) = u_2^\# (f(b)) - u_1^\# (f(b)) = 0
  $
  并且：
  $
    delta(c_1 c_2) &= u_2^\# (c_1) u_2^\# (c_2) - u_1^\# (c_1) u_1^\# (c_2) \
    &= u_2^\# (c_1) delta(c_2) + u_1^\# (c_2) delta(c_1) \
    &= u_0^\# (c_1) delta(c_2) + u_0^\# (c_2) delta(c_1) #[因为 $I^2 = 0$]
  $
  因此 $delta: C -> I$ 是 $B$-导子，即 $C$-线性映射 $Omega_(C\/B) -> I$。反之，若 $delta$ 是这样的导子，则由上面的计算，任取诱导出提升的 $u_1^\#: C -> A$，$u_1^\# + delta$ 也诱导出提升。于是我们构造出了单传递作用： 
  $
    Hom_C (Omega_(C\/B), I) times cal(L)(U) -> cal(L)(U)
  $
  现在： 
  $
    Hom_C (Omega_(C\/B), I) cong Hom_(A\/I) (Omega_(C\/B) otimes_C A\/I, I) cong Gamma(U, HHom_(cal(O)_(T_0)) (u_0^* Omega_(X\/Y), cal(I)))
  $
  于是我们构造出了单传递作用： 
  $
    Gamma(U, HHom_(cal(O)_(T_0)) (u_0^* Omega_(X\/Y), cal(I))) times cal(L)(U) -> cal(L)(U)
  $
  这些作用定义在充分小的仿射开集 $U subset T$ 上。容易验证，它们与从 $Spec(A)$ 到 $Spec(A_f)$ 的限制相容。而任意两个仿射开集的交，都可以用两侧均为主仿射开集的仿射开集覆盖（#cite-stacks("01IW")[Lemma 26.11.5]）。于是这些作用相容地粘成层作用： 
  $
    HHom_(cal(O)_(T_0)) (u_0^* Omega_(X\/Y), cal(I)) times cal(L) -> cal(L)
  $
  只要 $cal(L)(U) != emptyset$，这个作用在 $U$ 上的截面上就是单传递的。 
]

#lemma[
  对局部有限展示的态射，光滑性在源上是 Zariski 局部的。也就是说，对 $X$ 的任意开覆盖 ${X_i}$，局部有限展示的态射 $f: X -> Y$ 形式光滑，当且仅当 $f|_(X_i): X_i -> Y$ 形式光滑。 
]
#proof[
  ($==>$) 方向不难，故只证 ($<==$) 方向。对任意交换图表： 
  // https://q.uiver.app/#r=typst&q=WzAsNCxbMCwwLCJTcGVjKEFcXC9JKSJdLFswLDEsIlNwZWMoQSkiXSxbMSwxLCJZIl0sWzEsMCwiWCJdLFszLDIsImYiXSxbMCwxXSxbMSwyLCJ2IiwyXSxbMCwzLCJ1XzAiXV0=
  #align(center, diagram({
    node((0, 0), [$Spec(A\/I)$])
    node((0, 1), [$Spec(A)$])
    node((1, 1), [$Y$])
    node((1, 0), [$X$])
    edge((1, 0), (1, 1), [$f$], label-side: left, "->")
    edge((0, 0), (0, 1), "->")
    edge((0, 1), (1, 1), [$v$], label-side: right, "->")
    edge((0, 0), (1, 0), [$u_0$], label-side: left, "->")
  }))
  其中 $I^2 = 0$。设 ${X_i}$ 是 $X$ 的开覆盖，每个 $f_i = f|_(X_i): X_i -> Y$ 都形式光滑。每个 $u_0^(-1) (X_i)$ 都是 $Spec(A\/I)$ 的开集，而 $Spec(A\/I)$ 同胚于 $Spec(A)$。于是可以选取元素 $f_(i,j) in A$，使得 $u_0^(-1) (X_i) = union.big_j Spec(A_(f_(i,j))\/I_(f_(i,j)))$。考虑下述交换图表： 
  // https://q.uiver.app/#r=typst&q=WzAsNCxbMCwwLCJTcGVjKEFfKGZfKGksaikpXFwvSV8oZl8oaSxqKSkpIl0sWzAsMSwiU3BlYyhBXyhmXyhpLGopKSkiXSxbMSwxLCJZIl0sWzEsMCwiWF9pIl0sWzMsMiwiZl9pIl0sWzAsMV0sWzEsMiwidiIsMl0sWzAsMywidV8wIl0sWzEsMywidV9pIiwxLHsic3R5bGUiOnsiYm9keSI6eyJuYW1lIjoiZGFzaGVkIn19fV1d
  #context align(center, diagram({
    node((0, 0), [$Spec(A_(f_(i,j))\/I_(f_(i,j)))$])
    node((0, 1), [$Spec(A_(f_(i,j)))$])
    node((1, 1), [$Y$])
    node((1, 0), [$X_i$])
    edge((1, 0), (1, 1), [$f_i$], label-side: left, "->")
    edge((0, 0), (0, 1), "->")
    edge((0, 1), (1, 1), [$v$], label-side: right, "->")
    edge((0, 0), (1, 0), [$u_0$], label-side: left, "->")
    edge((0, 1), (1, 0), [$u_i$], label-side: center, "-->")
  }, crossing-fill: thm-box-curr-color()))
  由 $f_i$ 的形式光滑性，虚线提升 $u_i$ 存在。此时 $u_i: Spec(A_(f_(i,j))) ->^(u_i) X_i -> X$ 是 $u_0: Spec(A_(f_(i,j))\/I_(f_(i,j))) -> X_i$ 的提升。于是，取 $cal(L)$ 为上一引理中的提升层，则 
  $
    cal(L)(Spec(A_(f_(i,j)))) != emptyset
  $
  
  换言之，我们得到了 $Spec(A)$ 的一个开覆盖 ${U_alpha}$，其中每个都是主仿射开集，并且每个 $cal(L)(U_alpha) != emptyset$ 都成立。令 $cal(H) = HHom_(cal(O)_(Spec(A\/I))) (u_0^* Omega_(X\/Y), tilde(I))$，带有单传递作用： 
  $
    Phi: cal(H) times cal(L) -> cal(L)
  $
  如上一引理所示。现在： 

  - 存在唯一的 $h_(alpha,beta) in cal(H)(U_(alpha,beta))$，使得 $u_alpha|_(U_(alpha,beta)) = Phi(h_(alpha,beta)) (u_beta|_(U_(alpha,beta)))$。它们形式上满足余圈条件，从而定义出 Čech 余圈： 
    $
      (h_(alpha,beta)) in caron(H)^1_#[Zar] ({U_alpha}, cal(H))
    $

  - 现在 $Spec(A)$ 是仿射概形，${U_alpha}$ 是仿射覆盖。由于 $f$ 是局部有限展示的，$Omega_(X\/Y)$ 是 $X$ 上有限展示的拟凝聚层。因此： 
    $
      cal(H) = HHom_(cal(O)_(Spec(A\/I))) (u_0^* Omega_(X\/Y), tilde(I))
    $
    是 $Spec(A)$ 上的拟凝聚层。于是： 
    $
      caron(H)^1_#[Zar] ({U_alpha}, cal(H)) cong H^1_#[Zar] (Spec(A), cal(H)) = 0
    $
  
  - 于是存在截面 ${h_alpha in cal(H)(U_alpha)}$，使得 $h_(alpha,beta) = h_(beta)|_(U_(alpha,beta)) - h_(alpha)|_(U_(alpha,beta))$。令 $u'_alpha = Phi(h_alpha) u_alpha$。则在 $U_(alpha,beta)$ 上， 
    $
      u'_beta = Phi(h_beta) u_beta = Phi(h_alpha) Phi(h_(alpha,beta)) u_beta = Phi(h_alpha) u_alpha = u'_alpha
    $
    于是这些提升 $u'_alpha: U_alpha -> X$ 彼此相容，粘成整体提升 $Spec(A) -> X$。 
]

#theorem(name: <infinitesimal-lifting-criterion>)[
  设 $f: X -> Y$ 是局部有限展示的态射。则： 

  + $f$ 光滑，当且仅当它形式光滑； 

  + $f$ 非分歧，当且仅当它形式非分歧； 

  + $f$ 平展，当且仅当它形式平展。 
]
#proof[
  (3) 由 (1) 和 (2) 形式推出：（形式的）平展性不过是（形式的）非分歧性与光滑性二者。因此只需证明 (1) 和 (2)。 
  
  (1)($==>$) 
  #proof[
    既然已经证明形式光滑性在源上是局部的，只需证明标准光滑态射都形式光滑。现在取 $AA^d_Y -> Y$，考虑下述交换图表： 
    // https://q.uiver.app/#r=typst&q=WzAsNCxbMCwwLCJTcGVjKEFcXC9JKSJdLFswLDEsIlNwZWMoQSkiXSxbMSwxLCJZIl0sWzEsMCwiQUFeZF9ZIl0sWzMsMiwicCJdLFswLDFdLFsxLDIsInYiLDJdLFswLDMsInVfMCJdXQ==
    #align(center, diagram({
      node((0, 0), [$Spec(A\/I)$])
      node((0, 1), [$Spec(A)$])
      node((1, 1), [$Y$])
      node((1, 0), [$AA^d_Y$])
      edge((1, 0), (1, 1), [$p$], label-side: left, "->")
      edge((0, 0), (0, 1), "->")
      edge((0, 1), (1, 1), [$v$], label-side: right, "->")
      edge((0, 0), (1, 0), [$u_0$], label-side: left, "->")
    }))
    提升 $u: Spec(A) -> AA^d_Y$ 等价于 $d$ 个截面 $a_1, dots.c, a_d in A$，它们在 $A\/I$ 中约化为定义 $u_0$ 的那 $d$ 个函数。因此可以随意提升它们。既然已知形式光滑性与复合相容，就只需证明平展态射都形式光滑。再由源上的局部性，不妨设 $X = Spec(C), Y = Spec(B)$，并且： 
    $
      C = (B[T]_(h(T)))/((g(T)))
    $
    其中，作为 $B[T]_(h(T))$ 的理想，$(g(T), g'(T)) = (1)$。考虑交换图表： 
    // https://q.uiver.app/#r=typst&q=WzAsNCxbMCwwLCJBXFwvSSJdLFswLDEsIkEiXSxbMSwwLCJDIl0sWzEsMSwiQiJdLFszLDIsImciLDJdLFsxLDBdLFsyLDAsInVfMCIsMl0sWzMsMSwidiJdXQ==
    #align(center, diagram({
      node((0, 0), [$A\/I$])
      node((0, 1), [$A$])
      node((1, 0), [$C$])
      node((1, 1), [$B$])
      edge((1, 1), (1, 0), [$phi$], label-side: right, "->")
      edge((0, 1), (0, 0), "->")
      edge((1, 0), (0, 0), [$alpha_0$], label-side: right, "->")
      edge((1, 1), (0, 1), [$beta$], label-side: left, "->")
    }))
    令 $g_beta, h_beta in A[T]$ 为 $g, h$ 的系数经 $beta$ 作用后得到的多项式。于是 $alpha_0$ 由截面 $[a] in A\/I$ 定义，满足 $g_beta ([a]) = 0 in A\/I, h_beta ([a]) in (A\/I)^times$。我们只需构造截面 $a in A$，使得 $g_beta (a) = 0, h_beta (a) in A^times$。 
    
    任取 $[a]$ 的一个提升 $a in A$，则 $g_beta (a) in I$。注意，由于 $I^2 = 0$，$[h_beta (a)] in (A\/I)^times$ 蕴含 $h_beta (a) in A^times$。于是对 $epsilon in I$，由 $epsilon^2 = 0$ 得： 
    $
      g_beta (a + epsilon) = g_beta (a) + g'_beta (a) epsilon
    $
    由于在 $B[T]_(h(T))$ 中作为理想有 $(g(T), g'(T)) = (1)$，可以选取多项式 $p_0 (T), p_1 (T) in B[T]$，使得： 
    $
      p_0 (T) g(T) + p_1 (T) g'(T) = h(T)^N
    $
    于是， 
    $
      p_(0,beta) (a) g_beta (a) + p_(1,beta) (a) g'_beta (a) = h_beta (a)^N
    $
    令 $epsilon = -h_beta (a)^(-N) p_(1,beta) (a) dot g_beta (a) in I$。现在： 
    $
      g_beta (a + epsilon) &= g_beta (a) + g'_beta (a) epsilon = g_beta (a) (1 - h_beta (a)^(-N) p_(1,beta) (a) g'_beta (a)) \
      &= g_beta (a)^2 h_beta (a)^(-N) p_(0,beta) (a) in I^2 = 0
    $
    而 $h_beta (a+epsilon)$ 在 $A\/I$ 中约化为单位，从而是 $A^times$ 中的单位。因此代表元 $a+epsilon$ 合乎要求。 
    #suppress-qed
  ]

  ($<==$)
  #proof[
    对每个 $x in X$，只需局部地检验光滑性。于是（利用形式光滑性的局部性）适当缩小 $X$（在 $x$ 附近）与 $Y$（在 $f(x)$ 附近），不妨设 $X = Spec(C), Y = Spec(B)$ 都是仿射的。选取一个展示： 
    $
      C = (B[T_1, dots.c, T_n])/((f_1, dots.c, f_m)) = P\/I
    $
    其中 $P = B[T_1, dots.c, T_n], I = (f_1, dots.c, f_m) subset P$。考虑图表： 
    // https://q.uiver.app/#r=typst&q=WzAsNCxbMCwwLCJQXFwvSyJdLFswLDEsIlBcXC9LXjIiXSxbMSwwLCJDID0gUFxcL0siXSxbMSwxLCJCIl0sWzEsMF0sWzIsMCwiIiwyLHsic3R5bGUiOnsiYm9keSI6eyJuYW1lIjoiZG91YmxlIGJhcnJlZCJ9fX1dLFszLDJdLFszLDFdXQ==
    #align(center, diagram({
      node((0, 0), [$P\/I$])
      node((0, 1), [$P\/I^2$])
      node((1, 0), [$C = P\/I$])
      node((1, 1), [$B$])
      edge((0, 1), (0, 0), "->")
      edge((1, 0), (0, 0), "=")
      edge((1, 1), (1, 0), "->")
      edge((1, 1), (0, 1), "->")
    }))
    由形式光滑性，商映射 $P\/I^2 -> P\/I$ 有截面 $sigma: C = P\/I -> P\/I^2$。定义： 
    $
      delta: P -> I\/I^2, F |-> [F mod I^2] - sigma([F mod I])
    $
    则： 

    - #h(1fr)
      $
        delta(p_1 p_2) &= [p_1 mod I^2][p_2 mod I^2] - sigma([p_1 mod I])sigma([p_2 mod I]) \
        &= [p_1 mod I^2] delta(p_2) + sigma([p_2 mod I]) delta(p_1) = p_1 delta(p_2) + p_2 delta(p_1)
      $
    
    - 对 $b in B$， 
      $
        delta(b) = [b mod I^2] - sigma([b mod I]) = 0
      $
      因为这里每个态射都是 $B$-代数同态。 

    于是 $delta$ 是 $B$-导子，从而定义 $P$-线性映射 $rho: Omega_(P\/B) -> I\/I^2$，满足 $rho(d F) = [F mod I^2] - sigma([F mod I])$。这样就得到 $C$-线性映射： 
    $
      rho: Omega_(P\/B) otimes_P C -> I\/I^2, d F |-> [F mod I^2]
    $
    由于 $C = P\/I$，$sigma([F mod I])$ 这一项消失。在第二个正合列中： 
    $
      I\/I^2 -> Omega_(P\/B) otimes_P C -> Omega_(C\/B) -> 0
    $
    第一个映射为 $[F mod I^2] |-> d F$。于是 $rho$ 是这个映射的回缩，从而这个右正合列分裂正合。 

    由 @equiv-defns-of-smooth (5)，$f$ 是光滑态射。 
    
    #suppress-qed
  ]

  (2)($==>$) 若 $f$ 非分歧，则 $Omega_(X\/Y) = 0$，于是 @classifying-diff-of-infinitesimal-lifts 中的层 $HHom_(cal(O)_(T_0)) (u_0^* Omega_(X\/Y), cal(I))$ 总是消没。因此这样的无穷小提升只要存在就唯一。 

  ($<==$) 设 $f$ 形式非分歧。这一点形式上即可验证：只需局部地检验，故不妨设 $X = Spec(C), Y = Spec(B)$ 都是仿射的。对任意 $C$-模 $M$，取平方零代数 $C_M = C oplus M$（乘法为 $(c_1,m_1) times (c_2, m_2) := (c_1 c_2, c_1 m_2 + c_2 m_1)$）。则 $M subset C_M$ 是平方零理想，且 $C_M\/M cong C$。于是在下述图表中： 
  // https://q.uiver.app/#r=typst&q=WzAsNCxbMSwwLCJDIl0sWzEsMSwiQiJdLFswLDEsIkNfTSJdLFswLDAsIkMiXSxbMiwzXSxbMSwwXSxbMSwyXSxbMCwzLCIiLDEseyJzdHlsZSI6eyJib2R5Ijp7Im5hbWUiOiJkb3VibGUgYmFycmVkIn19fV0sWzAsMiwiIiwxLHsic3R5bGUiOnsiYm9keSI6eyJuYW1lIjoiZGFzaGVkIn19fV1d
  #align(center, diagram({
    node((1, 0), [$C$])
    node((1, 1), [$B$])
    node((0, 1), [$C_M$])
    node((0, 0), [$C$])
    edge((0, 1), (0, 0), "->")
    edge((1, 1), (1, 0), "->")
    edge((1, 1), (0, 1), "->")
    edge((1, 0), (0, 0), "=")
    edge((1, 0), (0, 1), "-->")
  }))
  这样的提升只要存在就唯一。然而，映射 $C_M -> C$ 的 $B$-线性截面由 $B$-导子 $C -> M$ 分类。零导子总是存在，所以其他任何导子都等于它。也就是说： 
  $
    Hom_C (Omega_(C\/B), M) = 0
  $
  对每个 $C$-模 $M$ 成立。因此 $Omega_(C\/B) = 0$，故 $Spec(C) -> Spec(B)$ 非分歧。 
]

#corollary(name: <etale-map-with-stable-residue-field-preserves-completions>)[
  设 $f: X -> Y$ 是在 $x$ 处平展的态射，$y = f(x)$，并假设 $k(x) = k(y)$。则自然映射： 
  $
    cal(O)_(Y,y)\/frak(m)_y^N -> cal(O)_(X,x)\/frak(m)_x^N
  $
  全都是同构；于是自然映射： 
  $
    hat(cal(O)_(Y,y)) -> hat(cal(O)_(X,x))
  $
  在局部环的完备化上是同构。 
]
#proof[
  由于 $k(x) = k(y)$，把 $x$ 包含进 $X$ 的含入映射就给出映射 $s_0: Spec(k(y)) = Spec(cal(O)_(Y,y)\/frak(m)_y) -> X$。现在对 $N >= 1$，每个 $Spec(cal(O)_(Y,y)\/frak(m)_y^N) -> Spec(cal(O)_(Y,y)\/frak(m)_y^(N+1))$ 都是平方零闭浸入，故由形式光滑性，存在唯一的提升 $s_N$，补全下述交换图表： 
  // https://q.uiver.app/#r=typst&q=WzAsNCxbMCwwLCJTcGVjKGNhbChPKV8oWSx5KVxcL2ZyYWsobSlfeV5OKSJdLFsxLDAsIlgiXSxbMSwxLCJZIl0sWzAsMSwiU3BlYyhjYWwoTylfKFkseSlcXC9mcmFrKG0pX3leKE4rMSkpIl0sWzAsMSwic18oTi0xKSJdLFsxLDIsImYiXSxbMywyXSxbMCwzXSxbMywxLCJzX04iLDFdXQ==
  #context align(center, diagram({
    node((0, 0), [$Spec(cal(O)_(Y,y)\/frak(m)_y^N)$])
    node((1, 0), [$X$])
    node((1, 1), [$Y$])
    node((0, 1), [$Spec(cal(O)_(Y,y)\/frak(m)_y^(N+1))$])
    edge((0, 0), (1, 0), [$s_(N-1)$], label-side: left, "->")
    edge((1, 0), (1, 1), [$f$], label-side: left, "->")
    edge((0, 1), (1, 1), "->")
    edge((0, 0), (0, 1), "->")
    edge((0, 1), (1, 0), [$s_N$], label-side: center, "->")
  }, crossing-fill: thm-box-curr-color()))

  $s_N$ 把 $Spec(cal(O)_(Y,y)\/frak(m)_y^(N+1))$ 的唯一点送到 $x$，因此 $s_N$ 由局部同态 $phi_N: cal(O)_(X,x) -> cal(O)_(Y,y)\/frak(m)_y^(N+1)$ 诱导，并且这些同态彼此相容。 

  它模 $frak(m)_x = frak(m)_y cal(O)_(X,x)$ 的约化是剩余映射 $k(x) = k(y)$，因此 $phi_N (frak(m)_x) subset frak(m)_y\/frak(m)_y^(N+1)$。于是 $phi_N$ 消去 $frak(m)_x^(N+1)$，诱导出映射 $psi_N: cal(O)_(X,x)\/frak(m)_x^(N+1) -> cal(O)_(Y,y)\/frak(m)_y^(N+1)$。这里出现的都是 $cal(O)_(Y,y)$-代数同态，故对结构映射 $g_N: cal(O)_(Y,y)\/frak(m)_y^(N+1) -> cal(O)_(X,x)\/frak(m)_x^(N+1)$，至少成立 $psi_N compose g_N = id$。 

  剩下要验证的是反方向的复合为恒等映射。由于 $k(x) = k(y)$，$g_0 compose psi_0$ 是恒等映射。假设已经证明 $g_(N-1) compose psi_(N-1) = id$。比较两个 $cal(O)_(Y,y)$-代数同态：其一是约化映射： 
  $
    cal(O)_(X,x) -> cal(O)_(X,x)\/frak(m)_x^(N+1)
  $
  其二是： 
  $
    cal(O)_(X,x) -->^(phi_N) cal(O)_(Y,y)\/frak(m)_y^(N+1) -->^(g_N) cal(O)_(X,x)\/frak(m)_x^(N+1)
  $
  按 $s_N$ 的构造，模 $frak(m)_x^N\/frak(m)_x^(N+1)$ 约化之后，第二个映射变成 $cal(O)_(X,x) -->^(phi_(N-1)) cal(O)_(Y,y)\/frak(m)_y^N -->^(g_(N-1)) cal(O)_(X,x)\/frak(m)_x^N$，由归纳假设它等于普通的约化映射。于是这两个映射 $cal(O)_(X,x) -> cal(O)_(X,x)\/frak(m)_x^(N+1)$ 都是下述图表中的提升： 
  // https://q.uiver.app/#r=typst&q=WzAsNCxbMCwwLCJTcGVjKGNhbChPKV8oWCx4KVxcL2ZyYWsobSlfeF5OKSJdLFsxLDAsIlgiXSxbMSwxLCJZIl0sWzAsMSwiU3BlYyhjYWwoTylfKFgseClcXC9mcmFrKG0pX3heKE4rMSkpIl0sWzAsMV0sWzEsMiwiZiJdLFszLDJdLFswLDNdLFszLDEsIiIsMSx7InN0eWxlIjp7ImJvZHkiOnsibmFtZSI6ImRhc2hlZCJ9fX1dXQ==
  #align(center, diagram({
    node((0, 0), [$Spec(cal(O)_(X,x)\/frak(m)_x^N)$])
    node((1, 0), [$X$])
    node((1, 1), [$Y$])
    node((0, 1), [$Spec(cal(O)_(X,x)\/frak(m)_x^(N+1))$])
    edge((0, 0), (1, 0), "->")
    edge((1, 0), (1, 1), [$f$], label-side: left, "->")
    edge((0, 1), (1, 1), "->")
    edge((0, 0), (0, 1), "->")
    edge((0, 1), (1, 0), "-->")
  }))
  由形式非分歧性，它们相等。因此 $g_N compose psi_N = id$，我们为每个 $g_N$ 构造出了逆映射。于是每个 $g_N$ 都是同构，证毕。 
]
