#import "void-import.typ": *

== 拓扑不变性 <sect-topological-invariance>

本节我们证明平展景的拓扑不变性：平展景对泛同胚（例如幂零加厚、基域的不可分扩张）不敏感。 

// #definition[
//   若概形态射 $f: X' -> X$ 在任意基变换下都诱导底拓扑空间的同胚，则称它为*泛同胚*。 
// ]

本节从头到尾都要记住：由 @radicial-morphism-first-props (2)，泛同胚等价于整、满射、根性的态射。下文默认使用这一结论，不再逐次说明。 

拓扑不变性的表述是： 

- 给定泛同胚 $f: X' -> X$，它在平展景上诱导的函子：#h(1fr)
  $
    Et_X -> Et_(X'), U |-> U' = U times_X X'
  $
  是范畴等价。 

既然底层的景已经等价，$X$ 与 $X'$ 上的平展层概念也随之等价：$f_*: cAb(X'_et) arrows.rl cAb(X_et): f^(-1)$ 是范畴等价，且互为拟逆。 

拓扑不变性的证明策略是对维数归纳。归纳之前先做一次极限论证，把问题化归到有限型 $ZZ$-概形之间的有限泛同胚；然后再借助下面这条陈述来做归纳： 

- 若对 $X$ 的每个几何点 $ol(x)$，拓扑不变性对 $X' times_X tilde(X)_(ol(x)) -> tilde(X)_(ol(x))$ 都成立，则拓扑不变性对 $f: X' -> X$ 成立。 

后面会看到，若 $A$ 是严格 Hensel 的，则对任何泛同胚 $Spec(A') -> Spec(A)$，$A'$ 也必定是严格 Hensel 的。于是由严格 Hensel 局部环的性质，对任何平展 $A$-代数 $B$，$B$ 的 $k(A)$-点对应于 $B$ 的直积项 $A$。这些直积项可以平凡地略去，问题于是化归为对去心谱 $U' = Spec(A') - frak(m)_(A') -> U = Spec(A) - frak(m)_A$ 证明拓扑不变性。不过由于闭点已被去掉，$U$ 的局部环维数都 $< dim(A)$。这样便能对维数做归纳了。 

这个方法是我不查文献、自己独立想出来的；后来查了文献，发现它与 @cite-SGA1 中的方法相像。 

现在开始证明。我们先证明一个供极限论证使用的引理。 

#lemma(name: <passage-of-limit-of-univ-homeo>)[
  设 $X' = Spec(A') -> Spec(A) = X$ 是泛同胚。则： 
  
  + 可把 $A' = dirlim_lambda A'_lambda$ 写成有限 $A$-代数的正向极限，其中每个 $Spec(A'_lambda) -> Spec(A)$ 都是泛同胚。 

  + 若 $A'$ 在 $A$ 上有限，则可把 $A' = dirlim_lambda A'_lambda$ 写成有限展示的有限 $A$-代数的正向极限，其中每个 $Spec(A'_lambda) -> Spec(A)$ 都是泛同胚。 
]
#proof[
  我们断言：若复合 $X -> Y -> Z$ 是泛同胚，其中 $X -> Y$ 满射且两个态射都仿射，则 $X -> Y$ 与 $Y -> Z$ 都是泛同胚。 

  - 由于 $X -> Y -> Z$ 中的两个态射都仿射，而 $X$ 在 $Z$ 上整，故 $X$ 在 $Y$ 上整。又 $X -> Z$ 是单射，所以 $X -> Y$ 也是单射。现在取 $x in X$，它位于 $y in Y$ 与 $z in Z$ 之上。由于 $X -> Z$ 根性，$k(x)\/k(z)$ 纯不可分，从而 $k(x)\/k(y)$ 也纯不可分。于是由 @equiv-defns-of-radicial (2) 知 $X -> Y$ 根性。因此它整、满射、根性，从而是泛同胚。 

    $X -> Y$ 与 $X -> Z$ 既然都是泛同胚，$Y -> Z$ 也是泛同胚。 

  （1）可把 $A' = dirlim_lambda A'_lambda$ 写成其有限型 $A$-子代数的正向极限；由于 $A'$ 在 $A$ 上整，这些子代数在 $A$ 上必定有限。现在考虑 $Spec(A') -> Spec(A'_lambda) -> Spec(A)$。 

  - 由于 $A'_lambda -> A'$ 是包含映射，$Spec(A') -> Spec(A'_lambda)$ 支配。它又因整性而闭，从而是满射。按定义，$A -> A'_lambda$ 有限型且整，故有限。 

  于是由上述断言，每个 $Spec(A'_lambda) -> Spec(A)$ 都是泛同胚。 

  （2）取 $t_1, dots.c, t_n in A'$ 使得 $A' = A[t_1, dots.c, t_n]$，于是存在理想 $I$ 使 $A' = A[T_1,dots.c,T_n]\/I$。由有限性，对每个 $i$ 都存在首一多项式 $p_i (T_i) in I$。现在令 $K_0 = (p_1 (T_1), dots.c, p_n (T_n))$，并置 $A'_0 = A[T_1,dots.c,T_n]\/K_0$，这是有限自由 $A$-代数。于是 $A'_0 ->> A'$ 是满射，其核为 $J$。再置： 
  $
    A' = dirlim_(K_lambda subset J \ #[有限生成理想]) A'_0\/K_lambda
  $
  记 $A'_lambda = A'_0\/K_lambda$，并考虑 $Spec(A') -> Spec(A'_lambda) -> Spec(A)$。由断言，只需证明当 $lambda$ 充分大时 $Spec(A') -> Spec(A'_lambda)$ 满射。而这又只需证明 $Spec(A'_0) - V(J)$ 拟紧。事实上： 

  - 若 $Spec(A'_0) - V(J)$ 拟紧，则存在有限多个 $f_1, dots.c, f_m in J$ 使得 $V(J) = V(f_1, dots.c, f_m)$。于是 $sqrt(J) = sqrt((f_1, dots.c, f_m))$。这样一来，只要 $K_lambda supset (f_1, dots.c, f_m)$，就有 $Spec(A'_0\/J) = Spec(A') -> Spec(A'_lambda) = Spec(A'_0\/K_lambda)$ 是由幂零理想定义的闭浸入，从而是满射。 

  为得到这个拟紧性，我们用泛同胚。由于 $Spec(A') -> Spec(A)$ 是泛同胚，$p: Spec(A' otimes_A A'_0) -> Spec(A'_0)$ 也是泛同胚。 
  
  考虑由乘法映射
  $
    phi: A' otimes_A A'_0 -> A'
  $
  定义的 $s: Spec(A') -> Spec(A' otimes_A A'_0)$。直接验证可知其核为 $([T_1] otimes 1 - 1 otimes [T_1], dots.c, [T_n] otimes 1 - 1 otimes [T_n])$，这是有限生成理想。因此， 
  $
    s(Spec(A')) = V(ker(phi))
  $
  该集合的补集拟紧。我们断言在底空间上有 $p^(-1) (V(J)) = s(Spec(A'))$。事实上，$p compose s: Spec(A') -> Spec(A'_0)$ 是结构映射，它把 $Spec(A')$ 与 $V(J)$ 等同起来。因此，既然 $p$ 是同胚，就有 $p^(-1) (V(J)) = s(Spec(A'))$。 
  
  于是 $p^(-1) (V(J))$ 的补集拟紧；又因 $p$ 是同胚，$V(J)$ 的补集也拟紧。因此，把正向系统截断到满足 $J supset K_lambda supset (f_1, dots.c, f_m)$ 的那部分，就完成了证明。 
]

#theorem(name: <top-invariance>)[
  对任何泛同胚 $f: X' -> X$，它在平展景上诱导的函子：#h(1fr)
  $
    Et_X -> Et_(X'), U |-> U' = U times_X X'
  $
  是范畴等价。 
]
#proof[
  所谓“对 $f: X' -> X$ 的拓扑不变性成立”，指的是平展景上诱导的映射
  $
    f: Et_X -> Et_(X'), U |-> U' = U times_X X'
  $
  是范畴等价。 

  // 最初几步都是用极限论证做化归。首先注意，由 @passage-to-limit-of-properties (3d)，给定拟紧拟分离概形在仿射过渡映射下的逆向极限 $S = invlim_i S_i$，
  // $
  //   Et_S^#[拟紧拟分离] cong dirlim_i Et_(S_i)^#[拟紧拟分离]
  // $
  // 其中 $Et_S^#[拟紧拟分离]$ 表示 $Et_S$ 中由拟紧拟分离概形组成的满子范畴。 
  
  #lemma[
    对每个泛同胚 $f: X' -> X$，$Et_X -> Et_(X')$ 忠实。 
  ]
  #proof[
    给定 $Y, Z in Et_X$ 与 $u, v in Hom_X (Y, Z)$，它们诱导 $u',v' in Hom_(X') (Y', Z')$。作图像 $Gamma_u, Gamma_v: Y -> Y times_X Z$。由于 $Z -> X$ 平展，这两个图像都是开浸入。此外，沿 $X' -> X$ 作基变换后它们变成下面的图像，这一点纯粹是形式上的：
    $
      Gamma_(u'), Gamma_(v'): Y' -> Y' times_(X') Z'
    $
    设 $u' = v'$，则 $Gamma_(u') (Y') = Gamma_(v') (Y')$。由于 $Y' times_(X') Z' -> Y times_X Z$ 是同胚，$Gamma_u (Y) = Gamma_v (Y)$。于是作为开浸入有 $Gamma_u = Gamma_v$；再沿 $Y times_X Z -> Z$ 投影，即见 $u = v$。 
  ]

  忠实性至此已无待证明，我们只需再证全与本质满。 

  第一步。若拓扑不变性对所有仿射概形之间的泛同胚成立，则它对所有泛同胚成立。 

  #proof_[第一步的证明][
    假定仿射概形之间的泛同胚满足拓扑不变性。设 $f: X' -> X$ 是一般的泛同胚。用仿射开集 ${X_i}$ 覆盖 $X$，令 $X_(i,j) = X_i inter X_j$，并作 $f$ 的基变换 $f_i: X'_i -> X_i, f_(i,j): X'_(i,j) -> X_(i,j)$。每个 $f_i$ 都是仿射概形之间的泛同胚（这里 $X'_i$ 仿射，因为 $f_i$ 整而 $X_i$ 仿射）。 

    先证全忠实。对平展 $X$-概形 $Y, Z$，作基变换 $Y_i, Z_i$ 与 $Y_(i,j), Z_(i,j)$。概形态射可以在开覆盖上粘接，因此有等化子： 
    $
      Hom_X (Y, Z) -> product_i Hom_(X_i) (Y_i, Z_i) arrows.rr product_(i,j) Hom_(X_(i,j)) (Y_(i,j), Z_(i,j))
    $
    以及： 
    $
      Hom_(X') (Y', Z') -> product_i Hom_(X'_i) (Y'_i, Z'_i) arrows.rr product_(i,j) Hom_(X'_(i,j)) (Y'_(i,j), Z'_(i,j))
    $
    于是得到图表： 
    // https://q.uiver.app/#r=typst&q=WzAsNixbMCwwLCJIb21fWCAoWSwgWikiXSxbMSwwLCJwcm9kdWN0X2kgSG9tXyhYX2kpIChZX2ksIFpfaSkiXSxbMiwwLCJwcm9kdWN0XyhpLGopIEhvbV8oWF8oaSxqKSkgKFlfKGksaiksIFpfKGksaikpIl0sWzAsMSwiSG9tXyhYJykgKFknLCBaJykiXSxbMSwxLCJwcm9kdWN0X2kgSG9tXyhYJ19pKSAoWSdfaSwgWidfaSkiXSxbMiwxLCJwcm9kdWN0XyhpLGopIEhvbV8oWCdfKGksaikpIChZJ18oaSxqKSwgWidfKGksaikpIl0sWzAsM10sWzEsNF0sWzIsNV0sWzAsMV0sWzEsMiwiIiwxLHsib2Zmc2V0IjoxfV0sWzEsMiwiIiwxLHsib2Zmc2V0IjotMX1dLFs0LDUsIiIsMSx7Im9mZnNldCI6LTF9XSxbNCw1LCIiLDEseyJvZmZzZXQiOjF9XSxbMyw0XV0=
    #align(center, diagram({
      node((0, 0), [$Hom_X (Y, Z)$])
      node((1, 0), [$product_i Hom_(X_i) (Y_i, Z_i)$])
      node((2, 0), [$product_(i,j) Hom_(X_(i,j)) (Y_(i,j), Z_(i,j))$])
      node((0, 1), [$Hom_(X') (Y', Z')$])
      node((1, 1), [$product_i Hom_(X'_i) (Y'_i, Z'_i)$])
      node((2, 1), [$product_(i,j) Hom_(X'_(i,j)) (Y'_(i,j), Z'_(i,j))$])
      edge((0, 0), (0, 1), "->")
      edge((1, 0), (1, 1), "->")
      edge((2, 0), (2, 1), "->")
      edge((0, 0), (1, 0), "->")
      edge((1, 0), (2, 0 - 0.12), "->")
      edge((1, 0), (2, 0 + 0.12), "->")
      edge((1, 1), (2, 1 - 0.12), "->")
      edge((1, 1), (2, 1 + 0.12), "->")
      edge((0, 1), (1, 1), "->")
    }))
    其中各个平行四边形都交换，每一行都是等化子。 

    - 按我们对仿射概形之间泛同胚的拓扑不变性假设，中间的竖直箭头是双射。忠实性已证，故所有竖直箭头都是单射。 

      追图可知第一个箭头满射，于是得到全忠实。 

    接着证本质满。对任何平展 $X'$-概形 $Y'$，作 $Y'_i = Y' times_(X') X'_i$。由仿射情形，每个 $Y'_i$ 都下降为平展 $X_i$-概形 $Y_i$。由全忠实，存在相容的同构 $Y_i times_(X_i) X_(i,j) cong Y_j times_(X_j) X_(i,j)$。于是它们粘成平展 $X$-概形 $Y$，使得 $Y' cong Y times_X X'$。 
  ]

  下面证明一个引理，借助它可以把 $Et_(Spec(A))$ 换成平展 $A$-代数构成的范畴，从而引入必要的拟紧拟分离条件。 

  #lemma(name: <top-invariance-et-to-et-aff>)[
    设 $f: X' = Spec(A') -> X = Spec(A)$ 是泛同胚，并记 $Et_S^#[aff]$ 为 $Et_S$ 中由仿射概形组成的满子范畴。则拓扑不变性对 $f$ 成立（即 $Et_X -> Et_(X')$ 是等价），当且仅当 $Et_X^#[aff] -> Et_(X')^#[aff]$ 是等价。 
  ]
  #proof[
    注意 $Y in Et_X$ 仿射当且仅当 $Y' = Y times_X X'$ 仿射。事实上，若 $Y$ 仿射则 $Y'$ 显然仿射。反之设 $Y'$ 仿射，注意 $Y' -> Y$ 整且满射。由 @passage-to-limit-of-morphisms，有 $Y' = invlim_i Y'_i -> Y$，其中各 $Y'_i$ 是有限展示的有限 $Y$-概形。每个 $Y'_i -> Y$ 都满射；由 #cite-stacks("01Z6")[Lemma 32.4.13]，当 $i$ 充分大时 $Y'_i$ 仿射。于是存在从仿射概形到 $Y$ 的有限满射，由 Chevalley 定理知 $Y$ 仿射。这立刻给出 ($==>$) 方向。下面集中处理 ($<==$) 方向，假定 $Et_X^#[aff] -> Et_(X')^#[aff]$ 是等价。 
 
    先证全忠实。忠实性已知，故只需证全。具体说，取 $Y, Z in Et_X$ 与 $u' in Hom_(X') (Y', Z')$，用仿射开集 ${Z'_i}$ 覆盖 $Z'$，用仿射开集 ${Y'_j}$ 覆盖 $Y'$，使得存在指标 $alpha(j)$ 满足 $u'(Y'_j) subset Z'_(alpha(j))$。于是可限制到映射 $u'_j: Y'_j -> Z'_(alpha(j))$。 

    由仿射情形的本质满，$Y'_j, Z'_i in Et_(X')$ 下降为 $Y_j, Z_i in Et_X$。再由仿射情形下的全忠实，存在基变换到 $u'_j$ 的映射 $u_j: Y_j -> Z_(alpha(j))$。由忠实性，映射 $Y_j ->^(u_j) Z_(alpha(j)) -> Z$ 在 $Y_j inter Y_(j')$ 上相容，于是粘成基变换到 $u'$ 的映射 $u: Y -> Z$。这样就得到全。 

    最后证本质满。取任意 $Y' in Et_(X')$，用仿射开集 ${Y'_i}$ 覆盖 $Y'$；由仿射情形，$Y'_i = Y_i times_X X'$，其中 $Y_i in Et_X$ 仿射。设 $Y'_(i,j) = Y'_i inter Y'_j$ 下降为开集 $Y^((1))_(i,j) subset Y_i, Y^((2))_(i,j) subset Y_j$；再由全忠实，存在相容的同构 $Y_(i,j)^((1)) cong Y_(i,j)^((2))$，从而可以把 ${Y_i}$ 粘成 $Y in Et_X$，它在基变换后给出 $Y'$。证毕。 
  ]

  下面的证明会默认使用上面这个引理。 

  接下来我们改用极限论证。设 $S = invlim_i S_i$ 是仿射概形的逆向极限。则由 @passage-to-limit-of-morphisms 与 @passage-to-limit-of-properties (1a)(3d) 有 
  $
    Et_S^#[aff] cong dirlim_i Et_(S_i)^#[aff]
  $ 

  第二步。若拓扑不变性对所有仿射概形之间有限展示的有限泛同胚成立，则它对所有泛同胚成立。 
  #proof[
    由第一步，只需处理仿射概形之间的泛同胚 $f: Spec(A') = X' -> X = Spec(A)$。由 @passage-of-limit-of-univ-homeo (1)，可把 $X' = invlim_i X'_i$ 写成有限 $X$-概形的逆向极限，其中每个 $f_i: Spec(A'_i) = X'_i -> X$ 都是泛同胚。由 @passage-of-limit-of-univ-homeo (2)，又可把每个 $X'_i = invlim_j X'_(i,j)$ 写成有限展示的有限 $X$-概形的逆向极限，其中每个 $f_(i,j): X'_(i,j) -> X$ 都是泛同胚。 

    既然每个 $f_(i,j)$ 都是有限展示的有限泛同胚，按所假定的这一情形，有 $Et_X cong Et_(X'_(i,j))$。现在， 
    $
      Et_(X'_i)^#[aff] cong dirlim_j Et_(X'_(i,j))^#[aff] cong dirlim_j Et_X^#[aff] cong Et_X^#[aff]
    $
    从而： 
    $
      Et_(X')^#[aff] cong dirlim_i Et_(X'_i)^#[aff] cong dirlim_i Et_X^#[aff] cong Et_X^#[aff]
    $
    证毕。 
  ]

  第三步。若拓扑不变性对所有有限型仿射 $ZZ$-概形之间的有限泛同胚成立，则它对所有泛同胚成立。 

  #proof[
    由第二步，只需处理仿射概形之间有限型的有限泛同胚 $f: Spec(A') = X' -> X = Spec(A)$。把 $A = dirlim_i A_i$ 写成有限型 $ZZ$-代数的正向极限。令 $X_i = Spec(A_i)$。由 @passage-to-limit-of-morphisms，存在有限阶段 $i_0$ 与 $f_(i_0): X'_(i_0) -> X_(i_0)$，它沿 $X -> X_(i_0)$ 的基变换就是 $f: X' -> X$。把 $f_(i_0)$ 在阶段 $i>=i_0$ 作基变换得 $f_i: X'_i -> X_i$；由 @passage-to-limit-of-properties (2a)(3g) 以及把 (3g) 用于对角态射，适当放大 $i_0$ 后可使所有 $f_i$ 都是有限泛同胚。于是每个 $f_i$ 都是有限型 $ZZ$-概形之间的有限泛同胚，按所假定的情形有 $Et_(X'_i) cong Et_(X_i)$。于是 
    $
      Et_(X')^#[aff] cong dirlim_i Et_(X'_i)^#[aff] cong dirlim_i Et_(X_i)^#[aff] cong Et_X^#[aff]
    $
    证毕。 
  ]

  极限论证到此结束，可以开始归纳了。我们先证明关键的引理： 

  #lemma[
    设 $f: Spec(A') = X' -> X = Spec(A)$ 是仿射概形之间的有限泛同胚。 

    若对 $X$ 的每个几何点 $ol(x)$，拓扑不变性对基变换 $tilde(f)_(ol(x)): tilde(X)_(ol(x)) times_X X' -> tilde(X)_(ol(x))$ 成立，则拓扑不变性对 $f$ 成立。 
  ]
  #proof[
    （全忠实）忠实性已知，故只处理全。取 $Y, Z in Et_X^#[aff]$ 与 $u' in Hom_(X') (Y', Z')$。对每一点 $x in X$，取 $x$ 上方的一个几何点 $ol(x)$。拓扑不变性对 $tilde(f)_(ol(x)): tilde(X)_(ol(x)) times_X X' -> tilde(X)_(ol(x))$ 成立。因此，存在某个态射 $tilde(u)_(ol(x)) in Hom_(tilde(X)_(ol(x))) (Y times_X tilde(X)_(ol(x)), Z times_X tilde(X)_(ol(x)))$，而 $tilde(u)'_(ol(x)) in Hom_(X' times_X tilde(X)_(ol(x))) (Y' times_X tilde(X)_(ol(x)), Z' times_X tilde(X)_(ol(x)))$ 正是它的基变换。 

    由 @passage-to-limit-of-morphisms (1)，存在平展邻域 $(V, ol(v)) -> (X, ol(x))$ 与态射 $u_V: Y times_X V -> Z times_X V$，它基变换到 $tilde(u)_(ol(x))$。由 @passage-to-limit-of-morphisms (3)，适当缩小 $(V, ol(v))$，不妨设基变换 $u'_V: Y' times_X V -> Z' times_X V$ 正是 $u'$ 沿 $V -> X$ 的基变换。再把 $V$ 缩小一点，不妨设 $V$ 仿射。 

    对每一点 $x in X$ 重复这一过程并取有限子覆盖，可知存在满射的平展态射 $V -> X$ 与态射 $u_V: Y times_X V -> Z times_X V$，满足： 

    - 沿 $X' -> X$ 的基变换 $u'_V: Y' times_X V -> Z' times_X V$，与 $u'$ 沿 $V -> X$ 的基变换完全一致。 

    令 $V_2 = V times_X V$，以及 $V' = X' times_X V, V'_2 = X' times_X V_2$。由态射的 fpqc 下降，我们有图表： 
    // https://q.uiver.app/#r=typst&q=WzAsNixbMCwwLCJIb21fWCAoWSwgWikiXSxbMCwxLCJIb21fKFgnKSAoWScsIFonKSJdLFsxLDAsIkhvbV9WIChZIHRpbWVzX1ggViwgWiB0aW1lc19YIFYpIl0sWzIsMCwiSG9tXyhWXzIpIChZIHRpbWVzX1ggVl8yLCBaIHRpbWVzX1ggVl8yKSJdLFsxLDEsIkhvbV8oVicpIChZJyB0aW1lc18oWCcpIFYnLCBaJyB0aW1lc18oWCcpIFYnKSJdLFsyLDEsIkhvbV8oVidfMikgKFknIHRpbWVzXyhYJykgVidfMiwgWicgdGltZXNfKFgnKSBWJ18yKSJdLFswLDJdLFsxLDRdLFswLDFdLFsyLDRdLFszLDVdXQ==
    #align(center, diagram({
      node((0, 0), [$Hom_X (Y, Z)$])
      node((0, 1), [$Hom_(X') (Y', Z')$])
      node((1, 0), [$Hom_V (Y times_X V, Z times_X V)$])
      node((2, 0), [$Hom_(V_2) (Y times_X V_2, Z times_X V_2)$])
      node((1, 1), [$Hom_(V') (Y' times_(X') V', Z' times_(X') V')$])
      node((2, 1), [$Hom_(V'_2) (Y' times_(X') V'_2, Z' times_(X') V'_2)$])
      edge((0, 0), (1, 0), "->", $alpha_1$)
      edge((0, 1), (1, 1), "->", $alpha_2$, label-side: right)
      edge((0, 0), (0, 1), "->", $g_1$)
      edge((1, 0), (1, 1), "->", $g_2$)
      edge((2, 0), (2, 1), "->", $g_3$, label-side: left)
      edge((1, 0), (2, 0 + 0.12), "->", $beta_(1,2)$, label-side: right)
      edge((1, 0), (2, 0 - 0.12), "->", $beta_(1,1)$, label-side: left)
      edge((1, 1), (2, 1 + 0.12), "->", $beta_(2,2)$, label-side: right)
      edge((1, 1), (2, 1 - 0.12), "->", $beta_(2,1)$, label-side: left)
    }))
    其中各行都是等化子，且整个图表交换。由忠实性，映射 $g_(1,2,3)$ 都是单射，并且 $g_2 (u_V) = u'_V = alpha_2 (u')$。现在： 
    $
      g_3 (beta_(1,1) (u_V)) = beta_(2,1) (g_2 (u_V)) = beta_(2,1) (alpha_2 (u')) = beta_(2,2) (alpha_2 (u')) = beta_(2,2) (g_2 (u_V)) = g_3 (beta_(1,2) (u_V))
    $
    由于 $g_3$ 是单射，$beta_(1,1) (u_V) = beta_(1,2) (u_V)$；又因第一行是等化子，存在 $u in Hom_X (Y, Z)$ 使得 $alpha_1 (u) = u_V$。于是： 
    $
      alpha_2 (u') = g_2 (u_V) = g_2 (alpha_1 (u)) = alpha_2 (g_1 (u))
    $
    从而 $u' = g_1 (u)$。这说明 $u'$ 落在 $Hom_X (Y, Z) -> Hom_(X') (Y', Z')$ 的像中，全忠实得证。 

    （本质满）设 $Y' in Et_(X')^#[aff]$。对每一点 $x in X$，取 $x$ 上方的一个几何点 $ol(x)$。拓扑不变性对 $tilde(f)_(ol(x)): tilde(X)_(ol(x)) times_X X' -> tilde(X)_(ol(x))$ 成立。因此存在某个 $tilde(Y)_(ol(x)) in Et_(tilde(X)_(ol(x)))$，使得 $X' times_X tilde(Y)_(ol(x)) cong tilde(X)_(ol(x)) times_X Y'$。由 @passage-to-limit-of-properties (1a)(3d)，存在仿射平展邻域 $(V, ol(v)) -> (X, ol(x))$ 与仿射平展的 $Y_V in Et_V^#[aff]$，使得 $tilde(Y)_(ol(x)) = tilde(X)_(ol(x)) times_V Y_V$。令 $Y'_V = X' times_X Y_V$。则 
    $
      tilde(X)_(ol(x)) times_X Y'_V cong tilde(X)_(ol(x)) times X' times_X Y_V cong X' times_X tilde(Y)_(ol(x)) cong tilde(X)_(ol(x)) times_X Y'
    $
    于是由 @passage-to-limit-of-morphisms (3)，缩小 $V$ 后不妨设 $V times_X Y' cong Y'_V := X' times_X Y_V$。 

    对每一点 $x in X$ 重复这一过程并取有限子覆盖，可知存在满射的仿射平展态射 $V ->> X$ 与仿射平展的 $Y_V in Et_V^#[aff]$，使得： 
    $
      X' times_X Y_V cong V times_X Y' 
    $

    写 $V = Spec(A_1)$，于是 $A_1$ 是满射的平展 $A$-代数，且 $A'_1 = A_1 otimes_A A'$。再写 $Y' = Spec(B')$。则上述条件变成： 

    - 我们有平展 $A_1$-代数 $B_1$ 与同构：#h(1fr)
      $
        phi: B_1 otimes_A A' -> B' otimes_A A_1
      $

    现在如下定义同构 $eta: B_1 otimes_A A_1 -> A_1 otimes_A B_1$。带置换下标的 $s$ 表示张量因子的置换；而态射的下标表示它所作用的张量因子。我们先定义它与 $A'$ 作张量积之后的版本： 
    $
      eta': B_1 otimes_A A_1 otimes_A A' &->^(phi_(1,3)) B' otimes_A A_1 otimes_A A_1 ->^(s_((1,2))) A_1 otimes_A B' otimes_A A_1 ->^(phi_(2,3)^(-1)) A_1 otimes_A B_1 otimes_A A'
    $
    现在 $B_1 otimes_A A_1$ 与 $A_1 otimes_A B_1$ 都是平展 $A$-代数。于是由全忠实，$eta'$ 下降为同构： 
    $
      eta: B_1 otimes_A A_1 -> A_1 otimes_A B_1
    $
    下面验证余圈条件。 

    - 由全忠实，只需验证与 $A'$ 作张量积之后的余圈条件。展开后，要证下述复合恰好是 $eta'_(1,3,4)$： 
      $
        B_1 otimes_A A_1 otimes_A A_1 otimes_A A' &-->^(phi_(1,4)) B' otimes_A A_1 otimes_A A_1 otimes_A A_1 -->^(s_((1,2))) A_1 otimes_A B' otimes_A A_1 otimes_A A_1 \
        &-->^(phi_(2,4)^(-1)) A_1 otimes_A B_1 otimes_A A_1 otimes_A A' -->^(phi_(2,4)) A_1 otimes_A B' otimes_A A_1 otimes_A A_1 \
        &-->^(s_((2,3))) A_1 otimes_A A_1 otimes_A B' otimes_A A_1 -->^(phi_(3,4)^(-1)) A_1 otimes_A A_1 otimes_A B_1 otimes_A A'
      $
      这里可以把 $phi_(2,4)^(-1)$ 与 $phi_(2,4)$ 消去，再利用 $s_((2,3)) compose s_((1,2)) = s_((1,3))$ 作合并。于是该复合变成： 
      $
        B_1 otimes_A A_1 otimes_A A_1 otimes_A A' &-->^(phi_(1,4)) B' otimes_A A_1 otimes_A A_1 otimes_A A_1 -->^(s_((1,3))) A_1 otimes_A A_1 otimes_A B' otimes_A A_1 \
        &-->^(phi_(3,4)^(-1)) A_1 otimes_A A_1 otimes_A B_1 otimes_A A'
      $
      而这就是 $eta_(1,3,4)$。 

    于是由 fpqc 下降，存在 $A$-模 $B$ 与同构 $delta: B otimes_A A_1 cong B_1$。进一步，把乘法映射 $B_1 otimes_(A_1) B_1 -> B_1$ 下降为映射 $B otimes_A B -> B$，就可使 $B$ 带有 $A$-代数结构，并使 $delta$ 成为环同态。现在有同构： 
    $
      B otimes_A A' otimes_A A_1 ->^(delta_(1,3)) B_1 otimes_A A' ->^phi B' otimes_A A_1 
    $
    由于 $A -> A_1$ 忠实平坦，这给出同构 $B otimes_A A' cong B'$，从而把 $B'$ 下降为 $A$-代数 $B$。剩下要证的是 $B$ 是平展 $A$-代数。事实上，$B otimes_A A_1 cong B_1$ 是平展 $A_1$-代数，而由平展性的忠实平坦下降（@fpqc-descent-of-properties (5)），$B$ 是平展 $A$-代数。取 $Y = Spec(B) in Et_X$，就有 $Y' cong X' times_X Y$，证毕。 
  ]

  接下来观察： 

  - 设 $Spec(A') = X' -> X = Spec(A)$ 是有限泛同胚，其中 $A$ 是严格 Hensel 局部环。则 $A'$ 是有限 $A$-代数。由 @finite-over-henselian-is-henselian，$A'$ 是严格 Hensel 局部 $A$-代数的直积。然而 $Spec(A')$ 同胚于 $Spec(A)$，只有一个闭点，故 $A'$ 本身是局部的。于是它也严格 Hensel。 

  现在可以做归纳了。 
  #lemma[
    拓扑不变性对有限维 Noether 概形之间的任何有限泛同胚 $f: X' -> X$ 成立。 
  ]
  #proof[
    对 $d = dim(X) = dim(X')$ 归纳。归纳假设是：拓扑不变性对维数 $<=d-1$ 的 Noether 概形之间的任何有限泛同胚成立。 

    与第一步同样的论证表明：要证拓扑不变性对 $f$ 成立，只需证它对 $f$ 在每个仿射开集 $X_i subset X$ 上的限制 $f_i: f^(-1) (X_i) -> X_i$ 成立。现在 $dim(X_i) <= dim(X) = d$，故可把 $f$ 换成 $f_i$，从而不妨设 $X', X$ 仿射。再由上一个引理，只需证：对 $X$ 的每个几何点 $ol(x)$，拓扑不变性对 $tilde(f)_(ol(x)): X' times_X tilde(X)_(ol(x)) -> tilde(X)_(ol(x))$ 成立。注意 $dim(tilde(X)_(ol(x))) = dim(cal(O)_(X,x)) <= dim(X) <= d$。 

    于是把 $f$ 换成 $tilde(f)_(ol(x))$，不妨设 $f: Spec(A') = X' -> X = Spec(A)$ 是有限泛同胚，其中 $A$ 是严格 Hensel 局部环且 $dim(A) <= d$。如上所观察，$A'$ 也是严格 Hensel 局部环。取去心谱 $U = Spec(A) - frak(m)_A, U' = Spec(A') - frak(m)_(A')$，则 $f_U: U' -> U$ 也是泛同胚。 
    
    注意作为去心谱，$dim(U) = dim(X) - 1 <= d - 1$。于是归纳假设给出 $f_U$ 的拓扑不变性。 

    现在： 

    - 对任何平展 $A$-代数 $B$，$Spec(B\/frak(m)_A B)$ 的点与截面 $B -> A$ 一一对应。这些截面 $Spec(A) -> Spec(B)$ 作为分离态射的截面是闭浸入，作为平展态射的截面是开浸入。于是 $Spec(B)$ 的每个 $k(A)$-点都对应 $Spec(B)$ 的一个同构于 $Spec(A)$ 的连通分支。因此 $B$ 有直积分解： 
      $
        B = A^(Spec(B\/frak(m)_A B)) times B_1
      $ 
      其中 $B_1$ 的像落在 $U$ 之上，故 $Spec(B_1) in Et_U$。 

      同样的分解 
      $
        B' = A'^(Spec(B'\/frak(m)_(A')B')) times B'_1
      $
      对任何平展 $A'$-代数 $B'$ 都存在。 

    - 现在对 $Spec(B), Spec(C) in Et_(Spec(A))^#[aff]$ 作分解： 
      $
        B = A^(Spec(B\/frak(m)_A B)) times B_1, C = A^(Spec(C\/frak(m)_A C)) times C_1
      $
      其中 $Spec(B_1), Spec(C_1) in Et_U$。于是基变换 $B', C'$ 分解为： 
      $
        B' = A'^(Spec(B'\/frak(m)_(A') B')) times B'_1, C' = A'^(Spec(C'\/frak(m)_(A') C')) times C'_1
      $
      这里 $Spec(B'_1), Spec(C'_1) in Et_(U')$ 分别是 $B_1, C_1$ 的基变换。 
      
      对态射 $Spec(B) -> Spec(C)$，$Spec(B)$ 中任何 $Spec(A)$-分支都必须同构地映入 $Spec(C)$ 的某个 $Spec(A)$-分支。而 $Spec(B_1)$ 映入 $Spec(C)$ 位于 $U$ 之上的部分，即 $union.sq.big_(Spec(C\/frak(m)_A C)) U union.sq Spec(C_1)$。因此， 
      $
        Hom_X (Spec(B), Spec(C)) = Spec(C\/frak(m)_A C)^(Spec(B\/frak(m)_A B)) times Hom_U (Spec(B_1), union.sq.big_(Spec(C\/frak(m)_A C)) U union.sq Spec(C_1))
      $
      类似地， 
      $
        Hom_(X') (Spec(B'), Spec(C')) = Spec(C\/frak(m)_A C)^(Spec(B\/frak(m)_A B)) times Hom_(U') (Spec(B'_1), union.sq.big_(Spec(C\/frak(m)_A C)) U' union.sq Spec(C'_1))
      $
      现在基变换映射 $Hom_X (Spec(B), Spec(C)) -> Hom_(X') (Spec(B'), Spec(C'))$ 在第一个因子 $Spec(C\/frak(m)_A C)^(Spec(B\/frak(m)_A B))$ 上是恒等，而这个因子是有限集。在第二个因子上它就是基变换映射： 
      $
        Hom_U (Spec(B_1), union.sq.big_(Spec(C\/frak(m)_A C)) U union.sq Spec(C_1)) -> Hom_(U') (Spec(B'_1), union.sq.big_(Spec(C\/frak(m)_A C)) U' union.sq Spec(C'_1))
      $
      于是由 $f_U: U' -> U$ 的拓扑不变性，这一分量也是同构。至此证明了 $Et_X^#[aff] -> Et_(X')^#[aff]$ 全忠实。 

    - 至于本质满，设 $Y' = Spec(B') in Et_(X')^#[aff]$。可作分解： 
      $
        B' = A'^r times B'_1
      $
      其中 $Spec(B'_1) in Et_(U')$。由 $U' -> U$ 的拓扑不变性，存在 $Y_1 in Et_U$ 使得 $Spec(B'_1) cong U' times_U Y_1$。现在取： 
      $
        Y = union.sq.big_(i=1)^r Spec(A) union.sq Y_1
      $
      于是 $Y' cong X' times_X Y$。现在 $Y' -> Y$ 是有限满射且 $Y'$ 仿射，故由 Chevalley 定理知 $Y$ 仿射。至此证明了 $Et_X^#[aff] -> Et_(X')^#[aff]$ 本质满。 

    由 @top-invariance-et-to-et-aff，$Et_X -> Et_(X')$ 是等价，证毕。 
  ]

  回忆第三步：我们只需对有限型 $ZZ$-概形之间的有限泛同胚证明拓扑不变性。由上一个引理，拓扑不变性在这种情形确实成立，于是证毕。 
]

#corollary(name: <top-invariance-sheaves>)[
  设 $f: X' -> X$ 是概形之间的泛同胚。则：
  
  0. 基变换：
    $
      f^(-1): Et_X -> Et_(X')
    $
    是范畴等价。$cal(U) = {U_i -> U}$ 是 $Et_X$ 中的平展覆盖，当且仅当 $f^(-1)(cal(U))$ 是 $Et_(X')$ 中的平展覆盖。 
  
  1. 对任何 $cal(F) in cAb(X_et)$，每个 $V in Et_(X')$ 都可写成 $U times_X X'$，其中 $U in Et_X$；并且有典范同构： 
    $
      (f^(-1) cal(F))(V) = cal(F)(U)
    $
    函子：
    $
      f_*: cAb(X'_et, Lambda) arrows.rl cAb(X_et, Lambda): f^(-1)
    $
    互为拟逆，并诱导范畴等价 $cAb(X'_et, Lambda) cong cAb(X_et, Lambda)$。 

    作为导出范畴中的陈述，函子：
    $
      f^(-1): D(X_et, Lambda) arrows.rl D(X'_et, Lambda): R f_*
    $
    互为拟逆，并诱导范畴等价 $D(X_et, Lambda) cong D(X'_et, Lambda)$。 

  2. 有典范同构： 
    $
      H^q (U, f_* cal(F)) = H^q (U times_X X', cal(F)) \

      H^q (U, cal(G)) = H^q (U times_X X', f^(-1) cal(G))
    $
    对任何 $U in Et_X, cal(F) in cAb(X'_et), cal(G) in cAb(X_et)$。 

  3. 设 $X, X'$ 是 Noether 概形。基变换：
    $
      f^(-1): FEt_X -> FEt_(X')
    $
    也是范畴等价。 
    
    作为推论，若 $X, X'$ 还连通，则对几何点 $ol(x) = f(ol(x'))$： 
    $
      f_*: pi_1^et (X', ol(x')) -> pi_1^et (X, ol(x))
    $
    是同构。 
]
#proof[
  （1）与（2）是（0）的显然推论。至于（0），$f^(-1)$ 是范畴等价已经证过。而 $cal(U)$ 联合满射当且仅当 $f^(-1)(cal(U))$ 联合满射，这是 $f$ 为泛同胚的推论。 

  （3）全忠实性由 $Et_X -> Et_(X')$ 的全忠实性直接得到，故只需证本质满。若能在 $X$（以及 $X'$）仿射的情形下证明本质满，就可以用全忠实性把下降得到的 $X$ 上的有限平展覆叠粘起来，从而得到一般情形。于是不妨设 $X, X'$ 仿射。

  设 $Y' in FEt_(X')$ 来自 $Y in Et_X$ 的基变换。由 @fet-trivializes-fet-locally，存在有限平展覆叠 $U' -> X'$，使得：
  $
    Y' times_(X') U' cong union.sq.big_(i=1)^m U'
  $
  作为 $U'$-概形。 
  
  现在由本质满，$U' -> X'$ 来自某个平展覆盖 $U -> X$ 的基变换。由全忠实： 
  $
    Y times_X U cong union.sq.big_(i=1)^m U
  $
  故 $Y times_X U -> U$ 有限。$U$ 同胚于仿射概形 $U'$，故拟紧。于是 $U -> X$ 是 fpqc，由 @fpqc-descent-of-properties (2) 知 $Y -> X$ 有限。因此 $Y in FEt_X$。 
]
