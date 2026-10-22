#import "void-import.typ": *

== Galois 覆叠空间

接下来我们要推广两项内容：一是域上 Galois 扩张的概念，二是取 Galois 群某个子群的不动子域这一做法；随后为平展覆叠空间建立 Galois 理论。

#definition(name: <defn-galois-covering-space>)[
  若下列条件成立，则称有限平展覆叠空间 $Z in FEt_X$ 为 *Galois* 的：
  
  + $Z$ 连通；
  
  + $Aut(Z\/X)^opp$ 在 $F_(ol(x)) (Z)$ 上传递地作用。
  
  这里条件 (2) 等价于条件 (2')：$\#Aut(Z\/X)^opp = \#F_(ol(x)) (Z)$，因为由性质 (1) 可知条件 (2) 中的作用是忠实的。而对另一个几何点 $ol(x')$，我们知道 $\#F_(ol(x)) (Z) = \#F_(ol(x')) (Z)$。因此一个有限平展覆叠是否为 Galois，与基点的选取无关。 
  
  #example[
    考虑 $X = Spec(K)$ 这个例子。有限平展覆叠 $Z -> X$ 必定有 $Z = Spec(A)$，其中 $A = product_i L_i$。
    
    此时 $Spec(A)$ 满足条件 (1) 当且仅当 $A = L$ 是有限可分扩张，而条件 (2') 是：
    $
      \#Aut(L\/K) = \#Hom_K (L, ol(K))
    $
    即 $L\/K$ 正规。总之，$Spec(A) -> Spec(K)$ 是 Galois 的 $<==>$ $A = L\/K$ 是域的 Galois 扩张。
  ]
]

#lemma(name: <galois-closure-exists>)[
  （Galois 闭包的存在性）对每个位于 $(X, ol(x))$ 之上且连通的 $(Z, ol(z)) in FEt_X$，都存在 Galois 覆叠空间 $(tilde(Z), ol(tilde(z))) in FEt_X$，连同一个 $X$ 上的态射 $(tilde(Z), ol(tilde(z))) -> (Z, ol(z))$：
  // https://q.uiver.app/#r=typst&q=WzAsMyxbMCwwLCIodGlsZGUoWiksIG92ZXJsaW5lKHRpbGRlKHopKSkiXSxbMiwwLCIoWiwgb3ZlcmxpbmUoeikpIl0sWzEsMSwiKFgsb3ZlcmxpbmUoeCkpIl0sWzAsMV0sWzAsMl0sWzEsMl1d
  #align(center, diagram(
    {
      node((-1, -1), [$(tilde(Z), ol(tilde(z)))$])
      node((1, -1), [$(Z, ol(z))$])
      node((0, 0), [$(X,ol(x))$])
      edge((-1, -1), (1, -1), "->")
      edge((-1, -1), (0, 0), "->")
      edge((1, -1), (0, 0), "->")
    },
    spacing: 1.5em,
  ))
  #example[
    在 $X = Spec(K)$ 的情形，几何点 $ol(x)$ 由嵌入 $K -> K^sep$ 给出，此时连通的平展覆叠空间 $Z -> X$ 就是嵌入 $K^sep$ 中的有限可分扩张 $L/K$。
    
    设 $Hom_K (L, K^sep) = {sigma_1, dots.c, sigma_n}$，其中由可分性有 $n = [L:K]$。于是我们把 Galois 闭包构造为像：
    $
      im(underbrace(L otimes_K dots.c otimes_K L, n) -> K^sep, x_1 otimes dots.c otimes x_n |-> sigma_1 (x_1) dots.c sigma_n (x_n))
    $
    这不过是域论中定义的 $L$ 的 Galois 闭包。这个 Galois 闭包的构造，也将为该引理的证明提供思路。
  ]
]
#proof[
  记 $F_(ol(x)) (Z) = {ol(z_1), dots.c, ol(z_n)}$，其中 $ol(z) = ol(z_1)$；令 $tilde(Z)$ 是 $Z times_X dots.c times_X Z$（$n$ 份）中包含 $(ol(z_1), dots.c, ol(z_n))$ 之像的那个连通分支。于是 $FEt_X$ 中有态射：
  $
    (tilde(Z), ol(tilde(z))) -> (Z times_X dots.c times_X Z, (ol(z_1), dots.c, ol(z_n))) overset(->, "pr"_1) (Z, ol(z_1))
  $
  
  只需证明 $tilde(Z)$ 是 Galois 的。
  
  对不同的 $i$，这些映射 $tilde(Z) arrow.hook.r Z^(times_X n) overset(->, "pr"_i) Z$ 两两不同，因为它们分别把 $ol(tilde(z))$ 送到 $ol(z_i)$。由于 $tilde(Z)$ 连通，由 @fet-first-props (1)，对任意 $ol(tilde(omega)) in F_(ol(x)) (tilde(Z))$，它在上述 $n$ 个映射下的像也两两不同。
  
  因此存在置换 $sigma in S_n$，使得 $"pr"_(sigma(i)) (ol(tilde(z))) = "pr"_i (ol(tilde(omega)))$。考虑 $FEt_X$ 中的一个图表：
  // https://q.uiver.app/#r=typst&q=WzAsMyxbMCwwLCJaXih0aW1lcyBuKSJdLFsyLDAsIlpeKHRpbWVzIG4pIl0sWzEsMSwiWiJdLFswLDEsInNpZ21hIl0sWzAsMiwiXCJwclwiXyhzaWdtYShpKSkiLDJdLFsxLDIsIlwicHJcIl9pIl1d
  #align(center, diagram(
    {
      node((-1, -1), [$Z^(times n)$])
      node((1, -1), [$Z^(times n)$])
      node((0, 0), [$Z$])
      edge((-1, -1), (1, -1), [$sigma$], label-side: left, "->")
      edge((-1, -1), (0, 0), [$"pr"_(sigma(i))$], label-side: right, "->")
      edge((1, -1), (0, 0), [$"pr"_i$], label-side: left, "->")
    },
    spacing: 2.5em,
  ))
  于是 $sigma$ 把 $ol(tilde(z))$ 送到 $ol(tilde(omega)) in tilde(Z)$，因而必然保持连通分支 $tilde(Z)$ 不变。所以 $sigma$ 限制为 $tilde(Z)$ 的自同构，且 $sigma(ol(tilde(z))) = ol(tilde(omega))$。按定义，这就证明了 $Aut(tilde(Z)\/X)$ 在 $F_(ol(x)) (tilde(Z))$ 上传递地作用。
]

Galois 闭包构造完毕，接下来我们推广取不动子域的做法。 

#definition(name: <defn-quotient-by-finite-group>)[
  设 $G$ 是作用在概形 $Z$ 上的抽象有限群。 

  设 $pi: Z -> Y$ 是 $G$-不变态射（即对一切 $g in G$ 都有 $pi compose g = pi$）。若对每个 $X$ 都存在函子性同构，则称该态射为 $Z$ 对 $G$ 的*范畴商* (categorical quotient)： 
  // https://q.uiver.app/#r=typst&q=WzAsMyxbMCwwLCJIb20oWiwgWCkiXSxbMiwwLCJIb20oWixYKV5HIl0sWzEsMSwiSG9tKFksIFgpIl0sWzEsMCwiIiwwLHsic3R5bGUiOnsidGFpbCI6eyJuYW1lIjoiaG9vayIsInNpZGUiOiJ0b3AifX19XSxbMiwxLCJleGlzdHMiLDEseyJzdHlsZSI6eyJib2R5Ijp7Im5hbWUiOiJkYXNoZWQifX19XSxbMiwwLCJwaV4qIiwxXV0=
  #context align(center, diagram({
    node((-2, -1), [$Hom(Z, X)$])
    node((0, -1), [$Hom(Z,X)^G$])
    node((-1, 0), [$Hom(Y, X)$])
    edge((0, -1), (-2, -1), "hook->")
    edge((-1, 0), (0, -1), [$exists$], label-side: center, "-->")
    edge((-1, 0), (-2, -1), [$(-) compose pi$], label-side: center, "->")
  }, crossing-fill: thm-box-curr-color()))
]

#proposition(name: <affine-sch-quotient>)[
  设 $Z = Spec(B)$ 仿射，并令 $A = B^G subset B$。则映射 $pi: Z = Spec(B) -> Spec(A) = Y$ 具有以下性质： 

  + $pi$ 是整的。 

  + $pi$ 满射且闭，故 $Y$ 上的拓扑就是 $Z$ 经 $pi$ 得到的商拓扑。$pi$ 的纤维恰好是 $G$-轨道。 

  + 设 $z in Z, y = pi(z) in Y$，$G_z = {sigma in G: sigma(z) = z}$。则 $k(z)\/k(y)$ 是代数扩张且正规（即拟 Galois 的），并且下面的映射是满射： 
    $
      G_z -> Aut(k(z)\/k(y))
    $

  + $(Y, pi)$ 是 $Z$ 对 $G$ 的商。 
]
#proof[
  (1) 对任意 $b in B$，$product_(sigma in G) (X - sigma(b)) in A[X]$，故 $pi$ 是整的。 

  (2) $A subset B$ 是整扩张，故由上行性质，$Spec(B) -> Spec(A)$ 满射。对任意 $J subset B$，$A\/A ∩ J -> B\/J$ 也是整扩张，从而满射。于是 $pi(V(J)) = V(A ∩ J)$。因此 $pi$ 既满且闭。 

  假设 $frak(q), frak(q)' subset B$ 在 $pi$ 下位于同一个 $frak(p) in Spec(A)$ 之上，即 $frak(q) ∩ A = frak(q)' ∩ A$。对任意 $x in frak(q)'$，$product_(sigma in G) sigma(x) in frak(p) = frak(q)' ∩ A subset frak(q)$。因此存在 $sigma in G$ 使 $x in sigma(frak(q))$。于是 
  $
    frak(q)' subset union.big_(sigma in G) sigma(frak(q))
  $
  由素理想回避，存在 $sigma in G$ 使 $frak(q)' subset sigma(frak(q))$。又因 $frak(q)' ∩ A = frak(p) = sigma(frak(q)) ∩ A$ 且 $A subset B$ 是整扩张，故 $frak(q)' = sigma(frak(q))$。 
  
  （$frak(q)' = sigma(frak(q))$ 的理由如下：若 $A subset B$ 是整扩张，$frak(q)_1 subset frak(q)_2 in Spec(B)$ 位于同一个 $frak(p) in Spec(A)$ 之上，则过渡到 $Spec(B\/frak(q)_1) -> Spec(B) -> Spec(A)$ 中对应于 $frak(p)$ 的纤维后，可不妨设 $frak(q)_1 = 0$、$B$ 是整环且 $A$ 是域。整环若在域上整，则它本身是域，故 $frak(q)_2 = 0 = frak(q)_1$。）

  (3) 把 $Y$ 基变换到局部环 $Spec(cal(O)_(Y,y))$（这样做可行，因为取不动子环与局部化相容），可不妨设 $(A, frak(m))$ 是局部环，且 $z$ 对应着 $frak(m)$ 之上的极大理想 $frak(q) subset B$。（正如刚才所证，整扩张中位于同一个素理想之上的素理想之间不可能有包含关系。因此位于 $frak(m)$ 之上的素理想全是极大理想。）
  
  现在 $k(z) = B\/frak(q)$ 在 $k = A\/frak(m)$ 上整，因为 $B$ 在 $A$ 上是整的。对每个 $ol(b) in k(z) = B\/frak(q)$， 
  $
    product_(sigma in G) (X - ol(sigma(b))) in k[X]
  $
  而 $[b]$ 是这个多项式的根。因此 $k(z)\/k$ 由那些极小多项式在 $k$ 上完全分裂的元素生成，从而是正规扩张。 
  
  设 $k_s$ 是 $k$ 在 $k(z)$ 中的可分闭包，$k_s = k(ol(b))$，其中 $ol(b) in B\/frak(q)$。诸 ${sigma(frak(q))}_(sigma in G)$ 都是极大理想，故两两互素。于是 
  $
    B -> product_(frak(r) in Spec(B) \ exists sigma in G, frak(r) = sigma(frak(q))) B\/frak(r)
  $
  由中国剩余定理，该映射是满射。因此可以取 $b in B$ 满足：

  - $b mod frak(q) = ol(b)$； 

  - 对任意 $sigma in G - G_z$（即 $sigma(frak(q)) != frak(q)$），$b equiv 0 mod sigma^(-1)(frak(q))$，即 $sigma(b) equiv 0 mod frak(q)$。 

  考虑多项式 $product_(sigma in G) (X - sigma(b)) in A[X]$。 
  任何 $s in Aut(k(z)\/k)$ 都由 $s(ol(b)) in k(z)$ 决定。$s(ol(b))$ 是多项式 $product_(sigma in G) (X - ol(sigma(b)))$ 的根，故存在 $sigma in G$ 使 $sigma(b) mod frak(q) = s(ol(b)) != 0$。按 $b$ 的取法，这样的 $sigma$ 必有 $sigma in G_z$。于是映射 $G_z -> Aut(k(z)\/k)$ 由 $sigma |-> s$ 给出，所需的满射便得到了。 

  (4) 首先，$Z -> Y$ 显然是 $G$-不变的。其次，$(-) compose pi: Hom(Y, X) -> Hom(Z, X)$ 的像落在 $Hom(Z, X)^G$ 内，因为 $pi$ 是 $G$-不变的。这个映射是函子性的，故只需对每个单独的 $X$ 证明 
  $
    (-) compose pi: Hom(Y, X) -> Hom(Z, X)^G
  $
  是双射。$pi$ 在拓扑空间上满射、在结构层上单射，从而是概形范畴中的满态射。因此 $(-) compose pi$ 是单射，只需再证它满射。设 $f: Z -> X$ 是 $G$-不变态射，我们要把它下降到某个 $g: Y -> X$。 

  - 由于作为拓扑空间有 $Y = Z\/G$，拓扑空间层面的 $G$-不变映射 $f: Z -> X$ 下降为某个 $g: Y -> X$。 

  - 映射 $f^\#: cal(O)_X -> f_* cal(O)_Z$ 在 $G$ 对 $cal(O)_Z$ 的作用下是 $G$-不变的。因此它穿过子层 $(f_* cal(O)_Z)^G = f_* cal(O)_Z^G = g_* pi_* cal(O)_Z^G = g_* cal(O)_Y$ 分解。这就定义了结构层上的态射 $g^\#: cal(O)_X -> g_* cal(O)_Y$。 

  至此构造出了态射 $g$。
]

#definition(name: <defn-admissible-group-action>)[
  若存在满足 @affine-sch-quotient 中 (1)–(4) 的仿射 $G$-不变映射 $pi: Z -> Y$，则称 $G$ 在 $Z$ 上的作用为*可容许* (admissible)。等价地： 

  - 存在 $G$-不变仿射映射 $pi: Z -> Y$，使得 $cal(O)_Y cong (pi_* cal(O)_Z)^G$。 

  - $Z$ 是若干 $G$-不变仿射开集之并。 

  #example[
    可容许的 $pi$ 不必是平展的。看一个来自复几何的例子：$CC -> CC, z |-> z^n$，即
    $
      CC[y] -> CC[z], y |-> z^n
    $
    其中 $mu_n$ 为 $n$ 次单位根群，它按 $sigma, z |-> sigma z$ 作用在 $CC[z]$ 上。这个映射在 $y = 0 in Y$ 之上分歧，但仍然可容许（因为 $CC[z]^(mu_n) = CC[z^n]$）。 
  ]

  #construction[
    设 $Z = Spec(B)$，且 $pi: Z = Spec(B) -> Y = Spec(A)$ 可容许。则性质 (4) 给出自然的同构： 
    $
      Hom(Spec(B), X)^G cong Hom(Spec(A), X)
    $
    取 $X = Spec(C)$，得自然同构 $Hom(C, B)^G cong Hom(C, A)$；再取 $C = ZZ[T]$，得自然同构 $B^G cong A$。 

    也就是说，对带 $G$-作用的概形 $Z$，只要存在可容许的 $pi: Z -> Y$，它局部上就必须形如 $Spec(B) -> Spec(B^G)$，因而被唯一确定。于是“$Z$ 可容许”的三种定义彼此等价，可容许性因此是一种性质，而非一种结构。往后的“$Z$ 可容许”与“$pi: Z -> Y$ 可容许”这两种说法，我们混着用。 
  ]
]

#definition(name: <defn-inertia-group>)[
  给定可容许映射 $pi: Z -> Y$，对 $z in Z$，*惯性子群* (inertia group) $I_G (z)$ 定义为下面的核： 
  $
    I_G (z) = ker(G_z ->> Aut(k(z)\/k(pi(z))))
  $
]

现在我们为平展覆叠空间建立 Galois 理论： 
#theorem(name: <galois-theory-of-coverings>)[
  0. 若 $Z -> Y$ 是 $FEt_X$ 中的态射，且 $Z\/X$ 是 Galois 的，则 $Z\/Y$ 也是 Galois 的。  

  + 设 $pi: Z -> Y := Z\/G$ 可容许且有限。若对一切 $z in Z$ 都有惯性子群 $I_G (z) = {1}$，则 $pi$ 是有限平展覆叠。 

  + 设 $Z in FEt_X$ 连通，$G$ 是 $Aut(Z\/X)^opp$ 中作用在 $Z$ 上的子群。在此设定下，$Z$ 是 $G$-可容许的，$Z -> Z\/G$ 是平展覆叠空间，也是 $FEt_X$ 中满足 $G = Aut(Z\/(Z\/G))$ 的态射，并且 $Z\/G -> X$ 也是平展覆叠空间（即 $FEt_X$ 中的对象）。 

  + 取平展覆叠空间 $Z -> X$，其中 $Z,X$ 连通。则 $Z\/X$ 是 Galois 的 $<==>$ $Z\/Aut(Z\/X)^opp overset(->, tilde) X$。 

  #example[
    考虑所涉概形都是域的谱的情形。此时这三条断言化为域论中熟悉的说法： 

    + 设 $L$ 带有 $G$-作用。若 $G -> Aut(L\/L^G)$ 是同构，则 $L\/L^G$ 是有限可分扩张。 

    + 设 $L\/K$ 是有限可分扩张，$G <= Gal(L\/K)$ 是子群。则 $L\/L^G$ 是 Galois 群为 $G$ 的有限可分扩张。 

    + 有限可分扩张 $L\/K$ 是 Galois 的，当且仅当 $L^(Aut(L\/K)) = K$。 
  ]
]
#proof[
  (0) 取 $Y$ 的一个位于 $X$ 的 $ol(x)$ 之上的几何点 $ol(y)$。则对 $ol(z_1), ol(z_2) in F_(ol(y)) (Z) subset F_(ol(x)) (Z)$，由于 $Z -> X$ 是 Galois 的，存在 $g in Aut(Z\/X)$ 使 $ol(z_2) = g(ol(z_1))$。再与结构映射 $pi: Z -> Y$ 复合，得 
  $
    pi(ol(z_1)) = ol(y) = pi(ol(z_2)) = pi(g(ol(z_1))) 
  $
  由于 $pi$ 与 $pi compose g$ 在一个几何点上取值相同，由 @fet-first-props (1) 得 $pi = pi compose g$。因此 $g$ 是 $Aut(Z\/Y)$ 中的自同构。于是 $Aut(Z\/Y)$ 在 $F_(ol(y)) (Z)$ 上传递地作用。 

  (1) //这个问题本质上是局部的，故可不妨设 $Z = Spec(B) $ 仿射，$Y = Spec(A), A = B^G$。//固定位于 $frak(p) in Spec(A) $ 之上的点 $frak(q) in Spec(B) $。我们打算沿 $A -> A_(frak(p))^"sh"$ 作基变换，也就是把 $A$ 在 $frak(p) $ 处作严格 Hensel 化。 
  //记 $R = A_(frak(p))^"sh"$，$S = B otimes_A A_(frak(p))^"sh"$。 
  我们打算对 $A$ 的某个局部环作严格 Hensel 化，再沿它作基变换，以化归到 $Y = Spec(A)$ 且 $A$ 是严格 Hensel 局部环的情形。 

  #lemma[
    设 $pi: Z -> Y = Z\/G$ 可容许，$g: Y' -> Y$ 平坦。作基变换： 
    // https://q.uiver.app/#r=typst&q=WzAsNCxbMCwwLCJaJyJdLFsxLDAsIlknIl0sWzAsMSwiWiJdLFsxLDEsIlkiXSxbMiwzLCJwaSIsMl0sWzEsMywiZyJdLFswLDEsInBpJyJdLFswLDIsImcnIiwyXV0=
    #align(center, diagram({
      node((-1, -1), [$Z'$])
      node((0, -1), [$Y'$])
      node((-1, 0), [$Z$])
      node((0, 0), [$Y$])
      edge((-1, 0), (0, 0), [$pi$], label-side: right, "->")
      edge((0, -1), (0, 0), [$g$], label-side: left, "->")
      edge((-1, -1), (0, -1), [$pi'$], label-side: left, "->")
      edge((-1, -1), (-1, 0), [$g'$], label-side: right, "->")
    }, spacing: 2em))
    则 $pi': Z' -> Y'$ 仍是 $G$-可容许的，且对任意 $z' in Z'$，令 $z = g'(z')$，都有 
    $
      I_G (z') = I_G (z)
    $
  ]
  #proof[
    先证 $pi': Z' -> Y'$ 仍然 $G$-可容许。这个问题在 $Y'$ 与 $Y$ 上都是局部的，故可不妨设 $Y, Y'$ 都仿射。于是只需证明：对任意平坦的 $B^G -> C$ 都有 $(B otimes_(B^G) C)^G = C$。事实上， 
    $
      B^G = ker(B -> oplus.big_(g in G) B, b |-> (g(b) - b)_(g in G))
    $
    作为 $B^G$-模成立，而平坦基变换保持这样的核。 

    接着证明惯性子群保持不变。设 $Z = Spec(B)$，$Y = Spec(A)$，$A = B^G$；设 $A'$ 是平坦 $A$-代数，$B' = B otimes_A A'$。令 $y = pi(z), y' = pi'(z')$。 

    对任意 $sigma in I_G (z')$，按定义 $sigma in G_(z')$，且 $sigma: B'_(z') -> B'_(z')$ 模去极大理想 $z' B'_(z')$ 后是恒等映射。由于按定义 $sigma$ 与映射 $B -> B'$ 交换，且 $sigma(z') = z'$，我们有 $sigma(z) = z$，故 $sigma in G_z$。由剩余域的包含 $k(z) subset k(z')$ 以及 $sigma$ 在 $k(z')$ 上是恒等映射，可知 $sigma$ 在 $k(z)$ 上也是恒等映射。于是得到容易的那个包含关系 $I_G (z') subset I_G (z)$。 

    反之，我们要证相反的包含。设 $sigma in I_G (z)$。条件 $sigma(z) = z$ 以及 $sigma$ 在 $k(z)$ 上的恒等性，可以改写成代数条件： 
    $
      sigma(b) - b in z, forall b in B
    $
    对任意 $b' in B'$，写 $b' = sum_i b_i otimes a'_i$。则： 
    $
      sigma(b') - b' = sum_i underbrace((sigma(b_i) - b_i), in z) otimes a'_i in z B' subset z'
    $
    这里用到 $z'$ 位于 $z$ 之上。于是 $sigma in G_(z')$，且在剩余域 $k(z')$ 上是恒等映射，故 $sigma in I_G (z')$。从而 $I_G (z) subset I_G (z')$。综上 $I_G (z) = I_G (z')$。 
  ]

  假定在 $Y = Spec(A)$、$A$ 是严格 Hensel 局部环的情形下已证得 (1)。下面证明一般情形：
  #proof[
    这个问题本质上是局部的，故可不妨设 $Z = Spec(B)$ 仿射，$Y = Spec(A), A = B^G$。不过平展性只需在局部环上验证，因此只需证明 $pi: Z -> Y$ 沿 $Spec(cal(O)_(Y,y)) -> Y$ 的每次基变换都平展。由于 $Spec(cal(O)_(Y,y)) -> Y$ 平坦，$pi$ 的基变换的惯性子群仍然平凡。 
    
    因此只需考虑 $Y = Spec(A)$、$A$ 是局部环的情形。取严格 Hensel 化 $Y' = Spec(A^"sh")$，此时 $Y' -> Y$ 忠实平坦。由 @fpqc-descent-of-properties (5)，平展性沿忠实平坦基变换下降，故沿 $Y' -> Y$ 作基变换即可化归到严格 Hensel 的情形。 
  ]

  现在设 $Y = Spec(A)$，其中 $(A, frak(m))$ 是严格 Hensel 的，且 $Z = Spec(B)$。 
  
  由于 $B$ 是 $A$ 上的有限代数而 $A$ 是 Hensel 的，$B$ 只有有限多个极大理想 ${frak(n)_1, dots.c, frak(n)_r}$，它们全都位于 $frak(m)$ 之上，并且 
  $
    B = B_(frak(n)_1) times dots.c B_(frak(n)_r)
  $
  由于 $G$ 传递地作用在位于 $frak(m)$ 之上的素理想 ${frak(n)_1, dots.c, frak(n)_r}$ 上，对固定的极大理想 $frak(n) in Spec(B)$，任一元素 $b in B^G$ 在分量 $B_(frak(n))$ 上的取值决定了其余所有分量。因此 $B^G = B_(frak(n))^(G_(frak(n)))$。然而 $k(frak(m)) = A\/frak(m)$ 可分闭，故 $k(frak(n))\/k(frak(m))$ 是有限正规的纯不可分扩张，其自同构群也就是平凡的。于是 $I_G (frak(n)) = ker(G_(frak(n)) -> Aut(k(frak(n))\/k(frak(m)))) = G_(frak(n))$。 

  /*($<==$) */若所有惯性子群 $I_G (frak(n))$ 都平凡，则所有群 $G_(frak(n))$ 都平凡。于是对任意极大理想 $frak(n) in Spec(B)$ 有 $A = B^G = B_(frak(n))^(G_(frak(n))) = B_(frak(n))$。因此 $B = A times dots.c times A$ 是若干份 $A$ 的直积，而 $pi: union.sq.big_(i=1)^r Spec(A) -> Spec(A)$ 平展。 

  /*($==>$) 设 $B$ 在 $A$ 上平展。则每个局部同态 $A -> B_(frak(n))$ 都平展。于是 $B_(frak(n))\/frak(n)B_(frak(n))$ 是 $k = A\/frak(m)$ 上的有限可分扩张。但 $k$ 可分闭，故这个扩张必然是平凡的。 
  
  现在我们有一个在剩余域上是同构的局部同态 $A -> B_(frak(n))$。由平展性，$frak(m)_A B_(frak(n)) = frak(n) B_(frak(n))$，故极大理想上诱导的态射是满射。最后，$B$ 是有限 $A$-模。由一个 Nakayama 论证，$B_(frak(n)) cong A$。 

  换言之，$B = product_(frak(n)) A$ 不过是若干份 $A$ 的直积，$G$ 作用其上，而 $A -> B$ 是对角嵌入。由于 $A -> B$ 是 $G$-不变的，$G$ 在每份 $A$ 上的作用平凡，$G$ 只是置换这些 $A$ 的副本。 */

  /* 容易验证： 
  - $Z -> Z\/G$ 的构造与平坦基变换 $Y' -> Z\/G$ 交换； 

  - $G_i (z)$ 的构造与这种基变换相容。 

  于是过渡到严格 Hensel 化 $Spec(cal(O)_(Y, ol(y))^h) -> Y$ 后，可不妨设： 

  - $Y = Spec(A)$，其中 $(A,frak(m))$ 是局部环，且 $A\/frak(m)$ 可分闭； 

  - $X = Spec(B), B = product_("有限") B_(frak(n)_i)$，在 $A$ 上有限。 

  按假设 $A cong B^G$。性质 (2) 说 $G$ 传递地作用在 $π^(-1)(frak(m))$ 上，且固定其中一个 $frak(n)$ 后有 $B^G = (B_(frak(n)))^(G_(frak(n)))$，其中 $G_(frak(n))$ 是分解群。 

  按假设 $G_i (frak(n)) = {1}$。现在考虑惯性子群与分解群的正合列： 
  $
    1 -> G_i (frak(n)) -> G_(frak(n)) -> Aut(κ(frak(n))\/(A\/frak(m))) -> 1
  $
  由于 $A\/frak(m)$ 可分闭，$κ(frak(n))\/(A\/frak(m))$ 纯不可分，故自同构群 $Aut(κ(frak(n))\/(A\/frak(m)))$ 平凡。于是 $G_(frak(n)) = {1}$，从而 $B^G = B_(frak(n)) = A$。 

  此时 $Z = union.sq.big Spec(B_(frak(n_i)))$，其中每个分支不过就是 $Y = Spec(B_(frak(n))) = Spec(A)$。这不过是平凡覆叠，所以平展。 */

  (2) 由于 $Z -> X$ 有限平展且 $Z$ 连通，@fet-first-props (1) 把 $Aut(Z\/X)$ 等同于任一几何纤维的自同构群的某个子群。因此 $G$ 有限。 

  先证 $Z$ 是 $G$-可容许的： 
  
  - 若 $U = Spec(A) subset X$ 是仿射开集，则 $V = Z times_X U$ 因 $Z -> X$ 有限而仿射；它又是 $Aut(Z\/X)^opp$-不变的，因为这个作用与结构映射 $Z -> X$ 相容，从而保持“点位于 $X$ 的某个指定点或开集之上”这一性质。 
  
    这些开集覆盖 $Z$，故按可容许性定义中的不变仿射开集判据，$Z$ 是 $G$-可容许的。于是商 $pi: Z -> Z\/G$ 存在。

  其次，$pi$ 的每个惯性子群都平凡。事实上：
  
  - 设 $z in Z$，$sigma in I_G (z)$。取 $z$ 之上的几何点 $ol(z)$。由于 $sigma$ 固定 $z$ 且在 $k(z)$ 上平凡地作用，它固定 $ol(z)$（后者实际上是 $k(z)$ 到一个可分闭域中的嵌入）。$sigma$ 与 $id_Z$ 都是连通有限平展覆叠 $Z -> X$ 的 $X$-自同构，故由 @fet-first-props (1) 得 $sigma = id_Z$。因此对一切 $z$ 有 $I_G (z) = {1}$，再由 (1) 知 $pi: Z -> Z\/G$ 有限平展。 

  结构态射 $Z -> X$ 是 $G$-不变的，故由 @affine-sch-quotient (4) 的商性质，它唯一地下降为态射 $q: Z\/G -> X$，使 $Z -> Z\/G ->^q X$ 等于原来的映射 $Z -> X$。我们要证 $q$ 有限平展。 
  
  - 这个断言在 $X$ 上是局部的，故固定 $x in X$，基变换到 $X' = Spec(cal(O)_(X,x)^#[sh])$。态射 $X' -> Spec(cal(O)_(X,x))$ 忠实平坦。由上面的平坦基变换引理，$Z\/G$ 的基变换就是 $Z times_X X'$ 对 $G$ 的商。由于 $X'$ 是严格 Hensel 的，有限平展覆叠 $Z times_X X' -> X'$ 是若干份 $X'$ 的有限不交并，$G$ 通过置换这些分支作用其上。它的商因此仍是若干份 $X'$ 的有限不交并，故 $q$ 的基变换有限平展。由 @fpqc-descent-of-properties (2) 与 (5)，$q: Z\/G -> X$ 有限平展。

  于是 $Z\/G in FEt_X$，且 $pi: Z -> Z\/G$ 是 $FEt_X$ 中的态射。 

  最后，给定的作用给出包含 $G -> Aut(Z\/(Z\/G))$。反之，$Z$ 在 $Z\/G$ 上的任何自同构都保持 $pi$ 的每条纤维，而由 @affine-sch-quotient (2)，这些纤维恰好是 $G$-轨道。取 $Z\/G$ 的一个几何点 $ol(y)$，以及 $Z$ 中位于其上方的几何点 $ol(z)$。则对任意 $gamma in Aut(Z\/(Z\/G))$，存在 $g in G$ 使 $gamma(ol(z)) = g(ol(z))$。由 @fet-first-props (1) 得 $gamma = g$。因此 $G -> Aut(Z\/(Z\/G))$ 是同构。 

  (3) 令 $G = Aut(Z\/X)^opp$。由于 $Z -> X$ 是连通的有限平展态射，由 @fet-first-props (1)，$G$ 忠实地作用在每条几何纤维上。

  ($<==$) 若 $Z\/G overset(->, tilde) X$，则对任意几何点 $ol(x) -> X$，由 @affine-sch-quotient (2)，纤维 $F_(ol(x)) (Z)$ 是单条 $G$-轨道。因此 $G$ 在 $F_(ol(x)) (Z)$ 上传递地作用，故 $Z\/X$ 是 Galois 的。

  ($==>$) 设 $Z\/X$ 是 Galois 的。对 $G <= Aut(Z\/X)^opp$ 应用 (2)，商 $Z -> Z\/G$ 作为平展覆叠存在，且 $Z\/G -> X$ 落在 $FEt_X$ 中。对任意几何点 $ol(x) -> X$，@affine-sch-quotient (2) 把 $Z -> Z\/G$ 的纤维与 $F_(ol(x)) (Z)$ 中的 $G$-轨道等同起来。由于 $Z\/X$ 是 Galois 的，这个作用是传递的，故：
  $
    \#F_(ol(x)) (Z\/G) = 1
  $
  于是有限平展覆叠 $Z\/G -> X$ 的次数为 $1$。$X$ 连通，故次数为 $1$ 的有限平展覆叠是同构。因此 $Z\/Aut(Z\/X)^opp overset(->, tilde) X$。
]
