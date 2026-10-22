#import "void-import.typ": *
== 开浸入与闭浸入 <sect-open-closed>

// 回忆：对 $f: X -> Y$，有一对伴随函子 $cAb(X_et) overset(underset(arrows.lr, f_*), f^(-1)) cAb(Y_et)$，即 $f^(-1)$ 是 $f_*$ 的左伴随；而 $f^(-1)cal(G)$ 是 $(U -> X) |-> dirlim cal(G)(V)$ 的层化，其中极限取遍所有如下形状的图表： // https://q.uiver.app/#r=typst&q=WzAsNCxbMCwwLCJVIl0sWzEsMCwiViJdLFswLDEsIlgiXSxbMSwxLCJZIl0sWzIsMywiZiJdLFswLDFdLFswLDJdLFsxLDNdXQ==
// #align(center, diagram({
//   node((0, -1), [$U$])
//   node((1, -1), [$V$])
//   node((0, 0), [$X$])
//   node((1, 0), [$Y$])
//   edge((0, 0), (1, 0), [$f$], label-side: left, "->")
//   edge((0, -1), (1, -1), "->")
//   edge((0, -1), (0, 0), "->")
//   edge((1, -1), (1, 0), "->")
// }))

// 注意：若 $f$ 平展，则 $f^(-1)cal(G) (U) = cal(G)(U)$，因为 $id: U -> U$ 在上述形状的图表中是始对象。

设 $i: Z arrow.r.hook X$ 是闭浸入，$j: U = X - Z arrow.r.hook X$ 是互补的开浸入。我们想定义 $j^(-1)$ 的左伴随 $j_!$，以及 $i_*$ 的右伴随 $i^!$：
// https://q.uiver.app/#r=typst&q=WzAsMyxbMCwwLCJjQWIoVV9ldCkiXSxbMiwwLCJjQWIoWF9ldCkiXSxbNCwwLCJjQWIoWl9ldCkiXSxbMSwwLCJqXigtMSkiLDFdLFsyLDEsImlfKiIsMV0sWzAsMSwial8qIiwxLHsiY3VydmUiOjN9XSxbMiwxLCJpXiEiLDEseyJjdXJ2ZSI6LTMsInN0eWxlIjp7ImJvZHkiOnsibmFtZSI6ImRhc2hlZCJ9fX1dLFswLDEsImpfISIsMSx7ImN1cnZlIjotMywic3R5bGUiOnsiYm9keSI6eyJuYW1lIjoiZGFzaGVkIn19fV0sWzEsMiwiaV4oLTEpIiwxLHsiY3VydmUiOi0zfV1d
#context align(center, diagram(
  {
    node((-1, 0), [$cAb(U_et)$])
    node((1, 0), [$cAb(X_et)$])
    node((3, 0), [$cAb(Z_et)$])
    edge((1, 0), (-1, 0), [$j^(-1)$], label-side: center, "->")
    edge((3, 0), (1, 0), [$i_*$], label-side: center, "->")
    edge((-1, 0), (1, 0), [$j_*$], label-side: center, "->", bend: -54deg)
    edge((3, 0), (1, 0), [$i^!$], label-side: center, "-->", bend: 54deg)
    edge((-1, 0), (1, 0), [$j_!$], label-side: center, "-->", bend: 54deg)
    edge((1, 0), (3, 0), [$i^(-1)$], label-side: center, "->", bend: 54deg)
  },
  crossing-fill: thm-box-curr-color(),
))

// #remark[
//   A closed immersion $i$ is always finite, so:
//   $
//     (i_* cal(G))_(overline(x)) = cases(cal(G)_(overline(x)) &\, "if" overline(x) -> Z, 0 &\, "otherwise")
//   $
// ]

#construction(name: <etale-lower-shriek-defn>)[
  设 $f: U -> X$ 是平展态射。对任意 $cal(H) in cAb(U_et)$，定义 $f_! cal(H)$ 为下述预层的层化： 
  $
    f_(cPSh,!) cal(H): Et_X^opp &-> cAb \
    V &|-> oplus.big_(psi in Hom_X (V, U)) cal(H)(psi: V -> U)
  $
  其中限制的定义如下：对 $Et_X$ 中的态射 $W ->^phi V$，有相应的限制映射： 
  $
    oplus.big_(psi in Hom_X (V,U)) cal(H)(psi) -> oplus.big_(chi in Hom_X (W,U)) cal(H)(chi)
  $
  它把 $cal(H)(psi)$ 中的截面沿 $phi$ 限制，得到 $cal(H)(psi compose phi)$ 中的截面。 
  // 或者干脆写成核：
  // $
  //   ker(j_* cal(F) -> i_* i^(-1) j_* cal(F))
  // $
  // 可以验证这两种构造是等价的。
]

#properties(name: <etale-lower-shriek-first-props>)[
  0. 若 $j$ 是开浸入，则 $j^(-1) compose j_! = id$。 #h(1fr)
  
  1. 存在自然同构： 
    $
      Hom_(cAb(X_et)) (f_! cal(H), cal(F)) -> Hom_(cAb(U_et)) (cal(H), f^(-1)cal(F))
    $
    它把 $f_!$ 等同于 $f^(-1)$ 的左伴随。若 $f$ 是开浸入，这个映射不过是 $f^(-1)$ 函子性的体现。 
    
    此外，$f_!: cAb(U_et) -> cAb(X_et)$ 正合。 
  
  2. 对 $X$ 的几何点 $ol(x)$，存在自然同构： 
    $
      (f_! cal(H))_(ol(x)) = oplus.big_(ol(u) in f^(-1)(ol(x))) cal(H)_(ol(u))
    $
    （其中几何纤维 $U_(ol(x))$ 在 $ol(x)$ 上平展，从而是几何点构成的离散集 $f^(-1)(ol(x))$。）
  
  3. (零延拓序列) 设 $i: Z -> X$ 是闭浸入，$j: U = X - i(Z) -> X$ 是互补的开浸入。对任意 $cal(F) in cAb(X_et)$，下述序列正合： 
    $
      0 -> j_! j^(-1) cal(F) -> cal(F) -> i_* i^(-1) cal(F) -> 0
    $

  4. (基变换) $f_!$ 的构造与任意基变换交换。换言之，对拉回方块： 
    // https://q.uiver.app/#r=typst&q=WzAsNCxbMSwxLCJYIl0sWzAsMSwiVSJdLFswLDAsIlUnIl0sWzEsMCwiWCciXSxbMywwLCJnIl0sWzEsMCwiZiIsMl0sWzIsMywiZiciXSxbMiwxLCJnJyIsMl1d
    #align(center, diagram({
      node((0, 0), [$X$])
      node((-1, 0), [$U$])
      node((-1, -1), [$U'$])
      node((0, -1), [$X'$])
      edge((0, -1), (0, 0), [$g$], label-side: left, "->")
      edge((-1, 0), (0, 0), [$f$], label-side: right, "->")
      edge((-1, -1), (0, -1), [$f'$], label-side: left, "->")
      edge((-1, -1), (-1, 0), [$g'$], label-side: right, "->")
    }))
    有自然同构： 
    $
      g^(-1) f_! cal(H) cong f'_! g'^(-1) cal(H), forall cal(H) in cAb(U_et)
    $
]
#proof[
  (1) 只需验证： 
  $
    Hom_(cPAb(X_et)) (f_(cPSh,!) cal(H), cal(F)) cong Hom_(cPAb(U_et)) (cal(H), f^(-1) cal(F))
  $
  不过可以验证： 
  $
    & Hom_(cPAb(X_et)) (f_(cPSh,!) cal(H), cal(F)) \
    =& {#[与限制相容的态射族 $(phi_V: oplus.big_(psi in Hom_X (V,U)) cal(H)(psi) -> cal(F)(V))_(V in Et_X)$]} \
    cong& {#[与限制相容的态射 $(phi_V: cal(H)(V) -> cal(F)(V))_(V in Et_U)$]} \
    =& Hom_(cPAb(U_et)) (cal(H), f^(-1) cal(F))
  $
  其中第三行用到直和的泛性质并重排了指标，第四行用到 @pullback-along-etale-morphism。 

  作为左伴随，$f_!$ 右正合。$f_(cPSh,!) cal(H)$ 的截面就是 $cal(H)$ 的截面的直和，而层上态射是否为单射，可以逐截面检验，因此 $f_(cPSh,!)$ 保持单射态射。于是层化 $f_!$ 也保持单射态射。由于它已经右正合，故正合。 
  
  (4) 由 Yoneda 引理得到。对任意 $cal(F)' in cAb(X'_et)$，由伴随性有自然同构：
  $
    Hom_(X') (g^(-1) f_! cal(H), cal(F)') cong Hom_X (f_! cal(H), g_* cal(F)') cong Hom_U (cal(H), f^(-1) g_* cal(F)')
  $
  以及：
  $
    Hom_(X') (f'_! g'^(-1) cal(H), cal(F)') cong Hom_(U') (g'^(-1) cal(H), f'^(-1) cal(F)') cong Hom_U (cal(H), g'_* f'^(-1) cal(F)')
  $
  因此只需证明存在自然同构 $f^(-1) g_* cal(F)' cong g'_* f'^(-1) cal(F)'$。事实上，给定 $V in Et_U$，由 @pullback-along-etale-morphism，左端与右端在 $V$ 上的截面都自然地等同于 $cal(F)'(V times_X X')$，于是证毕。 

  (2) 由 (4) 得到。以几何点的包含映射作基变换，即可看出：若取基变换 $f_(ol(x)): f^(-1) (ol(x)) -> ol(x)$，则： 
  $
    (f_! cal(H))_(ol(x)) = f_(ol(x),!) (cal(H)|_(f^(-1)(ol(x))))
  $
  然而 $f^(-1) (ol(x))$ 是不交并 $union.sq.big_(ol(u) in f^(-1)(ol(x))) ol(u)$，于是显然： 
  $
    f_(ol(x),!) (cal(H)|_(f^(-1)(ol(x)))) = oplus.big_(ol(u) in f^(-1)(ol(x))) cal(H)_(ol(u))
  $
  /*(2) We try to apply Yoneda's lemma. For an abelian group $A in cAb$, 
  $
    Hom_cAb ((f_! cal(H))_(ol(x)), A) &= Hom_(cAb(X_et)) (f_! cal(H), ol(x)_* A) \
    &= Hom_(cAb(U_et)) (cal(H), f^(-1) ol(x)_* A)
  $
  #lemma[
    For $f: U -> X$ etale, there exists a canonical isomorphism: 
    $
      f^(-1) ol(x_*) A cong product_(ol(u) in f^(-1)(ol(x))) ol(u)_* A
    $
  ]
  #proof[
    This isomorphism can be directly constructed section-wise. Given $phi: V -> U$ in $Et_U$, 
    $
      f^(-1) ol(x)_* A (phi) = ol(x)_* A (f compose phi = product_(ol(v) in (f compose phi)^(-1) (ol(x))) A
    $
    while: 
    $
      (product_(ol(u) in f^(-1)(ol(x))) ol(u)_* A)(phi) = product_(ol(u) in f^(-1)(ol(x))) ol(u)_* A(phi) = product_(ol(u) in f^(-1)(ol(x))) product_(ol(v) in phi^(-1)(ol(u))) A
    $
    These two groups are obviously canonically isomorphic, since: 
    $
      (f compose phi)^(-1) (ol(x)) = union.sq.big_(ol(u) in f^(-1) (ol(x))) phi^(-1)(ol(u))
    $
  ]

    As such,
    $
      Hom_cAb ((f_! cal(H))_(ol(x)), A) & = Hom_(cAb(X_et)) (f_! cal(H), ol(x)_* A) \
      & = Hom_(cAb(U_et)) (cal(H), f^(-1) ol(x)_* A) \
      & = Hom_(cAb(U_et)) (cal(H), product_(ol(u) in f^(-1)(ol(x))) ol(u)_* A) \
      & = product_(ol(u) in f^(-1)(ol(x))) Hom_(cAb(U_et)) (cal(H), ol(u)_* A) \
      & = product_(ol(u) in f^(-1)(ol(x))) Hom_(cAb) (cal(H)_(ol(u)), A) \
      & = Hom_cAb (oplus.big_(ol(u) in f^(-1)(ol(x))) cal(H)_(ol(u)), A)
    $
    We are thereby done. */

  (0) 同样由 (2) 得到。事实上，自然态射： 
  $
    cal(H) -> j^(-1) j_! cal(H) 
  $
  由伴随性给出。按 (2)，它形如 $cal(H)_(ol(u)) -> (j^(-1) j_! cal(H))_(ol(u)) = (j_! cal(H))_(ol(u)) = cal(H)_(ol(u))$；展开定义可知它就是恒等映射。因此它是同构。  

  (3) 同样由 (2) 得到，只需先建立一条关于 $i_*$ 的茎的引理。 
  #lemma[
    设 $i: Z -> X$ 是闭浸入。则对 $X$ 的任意几何点 $ol(x)$（位于 $x$ 上方）： 
    $
      (i_* cal(F))_(ol(x)) = cases(
        cal(F)_(ol(z)) &\, x in i(Z), 
        0 &\, x in.not i(Z)
      )
    $
    这里因为 $i$ 是闭浸入，$k(z) = k(i(z))$，因此若 $x = i(z)$，则 $z$ 上方存在唯一的几何点 $ol(z)$ 使得 $i(ol(z)) = ol(x)$。     
  ]
  #proof_[证明占位][
    我们将在后面一节证明这条引理的推广，见 @stalks-of-finite-pushforward；届时会建立茎与严格 Hensel 化之间的关系。 
  ]
  // #proof[
  //   We prove the two cases separately. If $x in.not i(Z)$, 
  //   $
  //     (i_* cal(F))_(ol(x)) = dircolim_((U,ol(u)) -> (X,ol(x))) cal(F)(Z times_X U)
  //   $
  //   However, every etale neighborhood $phi: (U, ol(u)) -> (X, ol(x))$ can be refined by its Zariski open $phi^(-1) (X - i(Z))$, whose fiber product with $Z$ is empty. As such, the filtered colimit above has a cofinal subsystem in which the groups in the colimit are zero. As such, the colimit above is zero. 

  //   If $x = i(z)$ for some $z in Z$, so that $ol(x) = i(ol(z))$, we want to prove that there exists a canonical isomorphism: 
  //   $
  //     dircolim_((U,ol(u)) -> (X,ol(x))) cal(F)(U times_X Z) cong dircolim_((V,ol(v)) -> (Z,ol(z))) cal(F)(V)
  //   $
  //   Note that every $U times_X Z$ is an etale neighborhood of $Z$, so there is a natural morphism $dircolim_((U,ol(u)) -> (X,ol(x))) cal(F)(U times_X Z) -> dircolim_((V,ol(v)) -> (Z,ol(z))) cal(F)(V)$. To show that it is an isomorphism, we thus only have to show that there is a cofinal subsystem of etale neighborhoods of $(Z, ol(z))$ that can be written in the form $U times_X Z$ for etale neighborhoods $U$ of $(X, ol(x))$. 

  //   For this, recall the local structure of etale morphisms. We then see that every etale neighborhood of $(Z, ol(z))$ may be refined by one of the shape: 
  //   $
  //     Spec(((C[t])/((f(t))))_(g(t))) -> Spec(C) -> Z
  //   $
  //   where $f(t) in C[t]$ is monic s.t. $f'(t)$ is invertible in $(C[t]\/f(t))_(g(t))$, where $Spec(C)$ is an affine open of $Z$, coming from an affine open $Spec(B)$ of $X$ s.t. $C = B\/I$. 

  //   Now we arbitrarily lift monic $f(t) in C[t]$ to some $tilde(f)(t) in B[t]$, and $g(t) in C[t]$ to some $tilde(g)[t] in B[t]$. We claim that $tilde(f)'(t)$ is invertible in $(B[t]\/tilde(f)(t))_(tilde(g)(t))$. Indeed, if we take the quotient of the ring by the ideal $I[t]$ generated by $I$, we obtain the element $f'(t) in (C[t]\/f(t))_(g(t))$, which is invertible. 
  // ]
  取茎即可由 (2) 得到结论。事实上，对 $X$ 的几何点 $ol(x)$： 

  - 若 $x in U$，茎上的序列为： #h(1fr)
    $
      0 -> cal(F)_(ol(x)) -> cal(F)_(ol(x)) -> 0 -> 0
    $

  - 若 $x in Z$，茎上的序列为： 
    $
      0 -> 0 -> cal(F)_(ol(x)) -> cal(F)_(ol(x)) -> 0
    $

  这两个序列都正合。 
]

#example[
  @detection-and-const-sheaf 中定义的层 $ul(ZZ)_(!,V)$ 满足 $Hom_cAb (ul(ZZ)_(!,V), cal(F)) = cal(F)(V)$，它其实就是 $i_(V,!) ul(ZZ)_V$，其中 $i_V: V -> X$ 是结构态射；这一点用 Yoneda 引理或直接验证定义都可以看出。#footnote[记号 $ul(ZZ)_(!,V)$ 由此而来。我需要把这个层与常值层 $ul(ZZ)_V in cAb(V_et)$ 区分开，所以在下标上加了个叹号，因为这个层不过是 $i_(V,!) ul(ZZ)_V$。]
]

此外，对分离的平展态射 $f$，我们可以把 $f_! cal(H)$ 等同于 $f_* cal(H)$ 的一个子层： 

#proposition(name: <sep-etale-lower-shriek-alt-desc>)[
  给定拟紧分离平展态射 $f: U -> X$，存在典范单射： 
  $
    f_! cal(H) -> f_* cal(H)
  $
  它把 $f_! cal(H)$ 等同于 $f_* cal(H)$ 的下述子层：对 $V_X in Et_X$，令 $V_U = U times_X V_X in Et_U$，则： 
  $
    f_! cal(H)(V_X) = {s in cal(H)(V_U) : supp(s) -> V_U -> V_X #[紧合]} subset cal(H)(V_U) = f_* cal(H)(V_X)
  $
  这里 $supp(s)$ 带有既约子概形结构，但取任何闭子概形结构都无区别；条件中的“紧合”也可以换成“有限”。这个包含映射与平展映射的复合相容。 
]
#proof[
  我们直接定义映射 $f_! cal(H) -> f_* cal(H)$。对 $(g: V_X -> X) in Et_X$，令 $V_U = U times_X V_X in Et_U$，定义映射： 
  $
    f_(cPSh,!) cal(H) (V_X) = oplus.big_(psi in Hom_X (V_X,U)) cal(H) (V_(X,psi)) -> f_* cal(H)(V_X) = cal(H)(V_U)
  $
  其中 $V_(X,psi)$ 就是 $V_X$，只是借助 $psi$ 看作平展 $U$-概形。考虑 $V_X ->^psi U ->^f X$，它的复合正是结构态射 $g$。现在取它的图： 
  $
    Gamma_psi: V_(X,psi) -> V_X times_X U = V_U
  $
  这是 $U$-态射，其中 $V_(X,psi)$ 借助 $psi$ 成为 $U$-概形，而 $V_X times_X U$ 借助第二投影成为 $U$-概形。 

  注意 $Gamma_psi$ 是对角态射 $U -> U times_X U$ 的基变换。由于 $f: U -> X$ 是分离平展的，该对角态射是开闭浸入。于是 $Gamma_psi$ 也是开闭浸入，从而作为平展 $U$-概形，$V_U$ 有分解 $V_U = Gamma_psi (V_(X,psi)) union.sq W_psi$。现在定义映射 $cal(H)(V_(X,psi)) -> cal(H)(V_U)$，把截面 $s in cal(H)(V_(X,psi))$ 送到截面 $t in cal(H)(V_U)$，使得 $t|_(V_(X,psi)) = s$ 且 $t|_(W_psi) = 0$。再把各个 $psi$ 对应的映射汇总到直和上。 

  容易验证，该构造与限制相容，因而给出预层态射。而且它是单射。层化之后便得到层态射： 
  $
    f_! cal(H) -> f_* cal(H)
  $
  要验证这个态射是单射，只需证明：若 $s in f_(cPSh,!) cal(H) (V_X)$ 被送到零，则 $s$ 在平展局部上为零。按 $f_(cPSh,!)$ 的定义，可把 $s$ 写成有限和 $s = sum_i [psi_i, s_i]$，其中 $psi_i in Hom_X (V_X, U)$，$s_i in cal(H)(V_(X,psi_i))$。 

  对两个 $psi_i, psi_j$，可以取等化子： 
  $
    V_(i,j) = {v in V_X : psi_i (v) = psi_j (v)}
  $
  这是 $psi_i$ 与 $psi_j$ 的等化子，也是态射 $(psi_i, psi_j): V_X -> U times_X U$ 下对角线的逆像。$U times_X U$ 中的对角线既开又闭，因此 $V_(i,j) subset V_X$ 是开闭子集。 

  现在按 ${V_(i,j)}$ 把 $V_X$ 分拆成有限多个开闭子集，便可假设在每一块上 $psi_i, psi_j$ 要么相等，要么像不相交。于是用这些开闭小块替换 $V_X$，并把对应 $Hom_X (V_X,U)$ 中同一元素的截面合并，即可假设所有 $psi_i$ 的像互不相交。此时上面构造的 $Gamma_(psi_i) (V_(X,psi_i))$ 互不相交，因此 $s$ 的像为零，便推出每个 $s_i = 0$。至此证明了单射性。 

  接下来刻画 $iota: f_! cal(H) -> f_* cal(H)$ 的像。我们断言： 
  $
    f_! cal(H)(V_X) = {s in cal(H)(V_U) : supp(s) -> V_U -> V_X #[紧合]} subset cal(H)(V_U) = f_* cal(H)(V_X)
  $
  /*The choice of the closed subscheme structure on $supp(s)$ here is irrelevant. Indeed, $f$ being a quasi-compact separated etale morphism is separated of finite type. Now $supp(s) -> V_U$ is a closed immersion and $V_U -> V_X$ is separated of finite type. Thus, $supp(s) -> V_X$ is automatically separated of finite type, so we may replace "proper" in the condition above by "universally closed". Now any closed subscheme structure on $supp(s)$ differs from the reduced one by a nilpotent thickening, which is a universal homeomorphism, which does not affect universal closedness. */注意 $supp(s) -> V_U$ 是闭浸入。由于 $U -> X$ 拟紧平展，$V_U -> V_X$ 也拟紧平展，因此 $V_U -> V_X$ 的纤维有限。于是 $supp(s) -> V_U$ 的纤维总是有限。由 #cite-stacks("02LS")[Lemma 37.44.1]，概形态射有限当且仅当它紧合且纤维有限。因此条件中的“紧合”可以换成“有限”。这一条件也不依赖 $supp(s)$ 上的闭子概形结构，因为幂零加厚不影响有限性。 

  此外，所提条件在 $V_X$ 上是局部的。事实上，设 $phi_X: W_X -> V_X$ 平展，并作基变换得到 $phi_U: W_U -> V_U$。则对 $s in cal(H)(V_U)$： 
  $
    (s|_(W_U))_(ol(w)) = s_(phi_U (ol(w)))
  $
  因此作为集合有 $supp(s|_(W_U)) = phi_U^(-1)(supp(s))$。给 $supp(s)$ 配上既约子概形结构，则 $supp(s|_(W_U))$ 就是 $supp(s) times_(V_U) W_U = supp(s) times_(V_X) W_X$ 的底子集。于是： 

  - “$supp(s) -> V_X$ 有限”这一性质在基变换到平展覆盖后仍成立，因为有限性在基变换下保持。 

  - “$supp(s) -> V_X$ 有限”这一性质可从平展覆盖下降。事实上，有限性可在 Zariski 局部检验，因此可把 $V_X$ 换成一个仿射开集。接着用有限多个仿射概形组成的覆盖加细给定的平展覆盖，最后注意到由 @fpqc-descent-of-properties (2)，有限性在 fpqc 下降下保持。 

  此外，$supp(s+t) subset supp(s) union supp(t)$ 是闭子集。设 $supp(s) -> V_X, supp(t) -> V_X$ 都紧合，则下述复合紧合： 
  $
    supp(s) union.sq supp(t) -> supp(s) union supp(t) -> V_X
  $
  其中第一个箭头是有限满射。作为闭浸入与拟紧分离平展态射的复合，$supp(s) union supp(t) -> V_X$ 自动分离且有限型。因此只需证明它泛闭，这由下面的引理得到： 
  #lemma[
    给定概形态射 $X ->^q X' ->^(f') Y$，其中 $q$ 满射，且复合 $f = f' compose q$ 泛闭，则 $f'$ 泛闭。 
  ]
  #proof[
    注意对复合作基变换后，$q$ 仍满射、$f$ 仍泛闭。因此只需证明 $f'$ 闭。给定闭集 $C subset X'$，$q^(-1) (C)$ 是闭集。由于 $f$ 闭，$f(q^(-1)(C))$ 是闭集，即 $f'(q(q^(-1)(C)))$ 是闭集。而 $q$ 满射，故 $q(q^(-1) (C)) = C$。因此 $f'(C)$ 是闭集。 
  ]

  至此证明了： 
  $
    {s in cal(H)(V_U) : supp(s) -> V_U -> V_X #[有限]} subset cal(H)(V_U) = f_* cal(H)(V_X)
  $  
  这一对应确实定义了 $f_* cal(H)$ 的子层 $cal(P)$。 

  - $f_! cal(H)$ 的像落在 $cal(P)$ 中。事实上，$cal(P)$ 是子层，故只需证明 $f_(cPSh,!) cal(H)$ 中任一截面的像都属于 $cal(P)$。 

    给定截面 $s in f_(cPSh,!) cal(H) (V_X)$，可写成有限和 $s = sum_i [psi_i, s_i]$，其中 $psi_i in Hom_X (V_X,U), s in cal(H)(V_(X,psi_i))$。因此只需证明：对固定的 $psi in Hom_X (V_X, U)$ 与 $s in cal(H)(V_(X,psi))$，有 $iota(s) in cal(P)$。事实上，$iota(s) in f_* cal(H)(V_X) = cal(H)(V_U)$ 作为 $cal(H)$ 的截面，其支集包含在 $Gamma_psi (V_(X,psi)) subset V_U$ 中。也就是说，$supp(iota(s)) subset Gamma_psi (V_(X,psi))$ 是闭子集。但 $Gamma_psi (V_(X,psi)) -> V_U -> V_X$ 是同构（其实就是 $V_X$ 上的恒等映射换了个说法），因而有限。于是 $supp(iota(s)) -> V_X$ 有限，故 $iota(s) in cal(P)$。 

  - $cal(P)$ 包含在 $f_! cal(H)$ 的像中。 

    设 $s in cal(P)(V_X) subset cal(H)(V_U)$ 且 $supp(s) -> V_U -> V_X$ 有限。要证明：对任意 $ol(v) in V_X$，存在 $ol(v)$ 的平展邻域 $W_X -> V_X$，使得 $s|_(W_X)$ 是 $f_(cPSh,!) cal(H)$ 中某个元素的像。 

    由于 $supp(s) -> V_X$ 有限，$ol(v)$ 在 $f_V: V_U -> V_X$ 下的几何纤维中，只有有限多个点落在 $supp(s)$ 的像里。设这些几何点为 ${ol(v)_1, dots.c, ol(v)_r}$。 

    取 $W_X = V_U times_(V_X) dots.c times_(V_X) V_U$ 为 $r$ 重纤维积，它在 $V_X$ 上平展，并带有 $ol(v)$ 上方的一个几何点 $ol(w) = (ol(v)_1, dots.c, ol(v)_r)$。令 $W_U = W_X times_X U = W_X times_(V_X) V_U$。于是对 $supp(s|_(W_U)) -> W_U -> W_X$，$ol(w)$ 上方有 $r$ 个几何点位于 $W_U$ 中，且都落在 $supp(s|_(W_U))$ 中；在等同 $W_U = W_X times_(V_X) V_U$ 下，这些点就是 $ol(w)_i = (ol(w), ol(v)_i) in W_U$。  
    
    第 $i$ 个投影 $W_X -> V_U$ 的图给出映射 $W_X -> W_X times_(V_X) V_U = W_X times_X U = W_U$，它是 $W_U -> W_X$ 的截面，并给出映射 $ol(w) -> ol(w)_i$。于是把底从 $(V_X, ol(v))$ 换成 $(W_X, ol(w))$ 作基变换后，可以假设： 

    - 存在截面 $psi_i: V_X -> V_U$，使得对每个 $1<=i<=r$ 都有 $psi_i (ol(v)) = ol(v)_i$。 

    对 $i!=j$，可以取 $psi_i, psi_j$ 的等化子。设 $E_(i,j)$ 是沿态射 $(psi_i, psi_j): V_X -> V_U times_(V_X) V_U$ 对对角线作拉回所得。由于 $V_U -> V_X$ 分离平展，该对角线既开又闭。因此每个 $E_(i,j)$ 在 $V_X$ 中开闭。又因 $ol(v)_i != ol(v)_j$，$ol(v)$ 不是 $E_(i,j), i!=j$ 的几何点。于是 $E_(i,j) subset V_X$ 作为 Zariski 开集不含 $v$。因此从 $V_X$ 中去掉所有 $E_(i,j)$，就得到 $v$ 附近的一个开闭子概形 $W_X subset V_X$，使得 $psi_i|_(W_X)$ 的像互不相交。 

    沿 $(W_X, ol(v)) -> (V_X, ol(v))$ 作基变换，便可假设所有 $psi_i$ 的像互不相交。 

    接下来令 $S = union.sq.big_(i=1)^r psi_i (V_X) subset V_U$。每个 $psi_i$ 作为分离平展态射 $V_U -> V_X$ 的截面都是开闭浸入，因此 $S$ 是 $V_U$ 的开闭子集。令 $C = V_U - S$，它也是 $V_U$ 的开闭子集，且不含 $v in V_X$ 上方的任何点。由于 $supp(s) -> V_X$ 有限，$supp(s) inter C$ 在 $V_X$ 中的像是闭集且不含 $v$。取其补集，得到 Zariski 开集 $v in W_X subset V_X$。于是 $union.sq.big_(i=1)^r psi_i (W_X) supset supp(s|_(W_U))$。 

    沿 $(W_X, ol(v)) -> (V_X, ol(v))$ 作基变换，可以假设 $supp(s) subset union.sq.big_(i=1)^r psi_i (V_X)$。令 $phi_i = p_2 compose psi_i: V_X -> V_U -> U$，这是平展的 $X$-态射。则 $s$ 落在下述映射的像中： 
    $
      oplus.big_(i=1)^r cal(H) (V_(X,phi_i)) -> cal(H) (V_U)
    $
    因为每个 $Gamma_(phi_i) = psi_i$，故可按 $s|_(psi_i (V_X))$ 在 $cal(H)(V_(X,phi_i))$ 中找到相应的元素。 
  
  证毕。 
]

#corollary(name: <fet-lower-star-is-lower-shriek>)[
  对有限平展态射 $f: X -> Y$，任意 $cal(F) in cAb(X_et)$ 都有典范同构 $f_! cal(F) -> f_* cal(F)$。 
]
#proof[
  上面构造的包含映射 $f_! cal(F) -> f_* cal(F)$ 给出等同： 
  $
    f_! cal(F)(V) = {s in cal(F)(X times_Y V) : supp(s) -> X times_Y V -> V #[紧合]} subset cal(F)(X times_Y V) = f_* cal(F)(V)
  $
  然而 $supp(s) -> X times_Y V$ 是闭浸入，而 $X -> Y$ 有限，故 $X times_Y V -> V$ 也有限。于是 $supp(s) -> V$ 自动有限，故 $f_! cal(F)(V) = f_* cal(F)(V)$。
]

接下来，给定互补的一对闭浸入与开浸入 $i: Z -> X$、$j: X - i(Z) -> X$，我们要定义 $i^!$。 
#lemma(name: <pushforward-by-closed-immersion>)[
  + $i^(-1) compose i_* = id$，且 $i_*$ 是全忠实函子。 

  + $cal(F) = i_* cal(G)$ 对某个 $cal(G) in cAb(Z_et)$ 成立，当且仅当 $j^(-1) cal(F) = 0$。
]
#proof[
  (1) $i^(-1) compose i_* = id$ 由前面关于 $i_* cal(F)$ 的茎的刻画得到。$i_*$ 的全忠实性则可由伴随性得到： 
  $
    Hom_(cAb(X_et)) (i_* cal(F), i_* cal(G)) = Hom_(cAb(Z_et)) (i^(-1)i_* cal(F), cal(G)) = Hom_(cAb(Z_et)) (cal(F), cal(G))
  $
  
  (2)($==>$)
  $
    (j^(-1) i_* cal(G)) (V -> U) = i_* cal(G) (V -> U) = cal(G) (V times_X Z) = cal(G)(emptyset) = 0
  $
  
  ($<==$) 有典范映射 $cal(F) -> i_* i^(-1) cal(F)$，它在 $Z$ 上方几何点处的茎上已经是同构。若 $j^(-1)cal(F) = 0$，则 $cal(F)$ 在 $U$ 上方几何点处的茎为零；而该映射是否为同构，只需在茎上检验。因此取 $cal(G) = i^(-1) cal(F)$ 即可。 
]

#construction(name: <closed-immersion-upper-shriek-constr>)[
  如下构造 $i^!$。令 $cal(F)' = ker(cal(F) -> j_* j^(-1) cal(F))$。则由 $j^(-1)$ 的正合性：
  $
    j^(-1) cal(F)' = ker(j^(-1) cal(F) overset(->, id) underbrace(j^(-1)j_*, id) j^(-1) cal(F)) = 0
  $
  于是由前一条引理，存在唯一的 $i^! cal(F) in cAb(Z_et)$ 使 $cal(F)' = i_* i^! cal(F)$。更具体地：
  $
    i^! cal(F) = i^(-1) ker(cal(F) -> j_* j^(-1) cal(F))
  $
]

#properties(name: <closed-immersion-upper-shriek-first-props>)[
  0. (带支集截面序列) 存在左正合列： #h(1fr)
    $
      0 -> i_* i^! cal(F) -> cal(F) -> j_* j^(-1) cal(F)
    $
  
  1. 存在同构：
    $
      Hom_(cAb(X_et)) (i_* cal(G), cal(F)) overset(->, tilde) Hom_(cAb(Z_et)) (cal(G), i^! cal(F))
    $
    它把 $i^!$ 等同于 $i_*$ 的右伴随。 
]
#proof[
  (0) 按定义， 
  $
    i_* i^! cal(F) = ker(cal(F) -> j_* j^(-1) cal(F))
  $
  因此该序列正合是显然的。 

  (1) 给定任意态射 $phi: i_* cal(G) -> cal(F)$，可以把它与映射 $cal(F) -> j_* j^(-1) cal(F)$ 复合。考虑复合： 
  $
    i_* cal(G) ->^phi cal(F) -> j_* j^(-1) cal(F)
  $
  由伴随性，映射 $i_* cal(G) -> j_* j^(-1) cal(F)$ 与映射 $j^(-1) i_* cal(G) -> j^(-1) cal(F)$ 一一对应。但 $j^(-1) compose i_* = 0$，故这样的映射只能是零。换言之，$i_* cal(G) ->^phi cal(F) -> j_* j^(-1) cal(F)$ 恒为零，因此 $phi$ 唯一地分解为： 
  $
    i_* cal(G) -> ker(cal(F) -> j_* j^(-1) cal(F))
  $
  由于 $i^(-1)$ 全忠实且 $i^(-1) compose i_* = id$，这样的映射唯一对应于一个映射： 
  $
    cal(G) = i^(-1) i_* cal(G) -> i^(-1) ker(cal(F) -> j_* j^(-1) cal(F)) = i^! cal(F)
  $
  证毕。 
]

最后，作为一个应用，设 $f: U -> X$ 平展。我们证明一条关于 $f^(-1) cal(G)$ 的平展上同调的引理。 

#corollary(name: <pullback-along-etale-morphism-derived>)[
  设 $f: U -> X$ 是平展态射。则对 $cal(F) in cAb(X_et)$ 与任意 $V in Et_U$，存在典范同构： 
  $
    H^q (V, cal(F)) cong H^q (V, f^(-1) cal(F))
  $
  其中 $V$ 借助 $V -> U ->^f X$ 被看作 $Et_X$ 的对象。 
]
#proof[
  $q = 0$ 的情形已由 @pullback-along-etale-morphism 处理。 

  为得到次数更高的同构，取内射消解 $0 -> cal(F) -> cal(I)^bullet$。由于 $f^(-1)$ 有正合的左伴随 $f_!$，$0 -> f^(-1) cal(F) -> f^(-1) cal(I)^bullet$ 是 $f^(-1) cal(F)$ 的内射消解。在 $V$ 上取截面，再对所得的两个链复形取上同调，最后用关于截面的结论即可完成证明。 
]
