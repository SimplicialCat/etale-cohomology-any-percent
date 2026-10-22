// audit-exception: 展示公式内的方括号文字块夹有多段行内公式，审计逐个配对美元符号后会把块内散文切成伪公式段，因此翻译这些散文必然改变数学指纹；块内公式与全部数学内容均未改动。
#import "void-import.typ": *

现在，我们可以进入平展上同调中基变换定理的领域了。 

和往常一样，我们力求为引入的每一部分理论给出动机。 

平展上同调的动机，是建立一个适用于代数簇的上同调理论，它类似于 CW 复形的 Betti 上同调。 

因此，我们有好几个大定理需要建立： 

+ 关于代数闭域 $k$ 上的代数簇，$n in k^times$ 时 $H^q_et (X, ZZ\/n)$ 的基本结论。（若 $n = p = "char"(k) > 0$，这个上同调的表现相当糟糕。） 
  - 有限性
  - 消没（超过 $2 dim(X)$ 时，以及仿射情形下超过 $dim(X)$ 时）
  - 紧支上同调
  - Poincaré 对偶
  - ……

+ 平展上同调在数论中有应用：考虑代数簇 $X\/QQ$，把它基变换到 $QQ$ 的代数闭包上，即 $X_(overline(QQ)) = X times_QQ overline(QQ)$。 
  
  此时 $Gal_QQ$ 在 $H^q_et (X_(overline(QQ)), ZZ\/n)$ 上有作用；由概形的极限公式 $H^q_et (X_(overline(QQ)), ZZ\/n) = colim_(L\/QQ #[有限 Galois]) H^q_et (X_L, ZZ\/n)$，这个作用是连续的。这样就得到一个 Galois 表示： 
  $
    Gal_QQ -> End(H^q_et (X_(ol(QQ)), ZZ\/n))
  $
  这个构造是基本的：取 $n = ell, ell^2, ell^3, dots.c$ 并过渡到逆向极限，就会得到连续表示： 
  $
    Gal_QQ -> End(H^q_et (X_(ol(QQ)), ZZ_ell)), H^q_et (X_(ol(QQ)), ZZ_ell) := invlim_(n>=1) H^q_et (X_(ol(QQ)), ZZ\/ell^n)
  $
  现在 $H^q_et (X_(ol(QQ)), ZZ_ell)$ 是有限秩 $ZZ_ell$-模，把它与 $QQ_ell$ 作张量积，就得到有限维 $QQ_ell$-向量空间 $H^q_et (X_(ol(QQ)), QQ_ell) := H^q_et (X_(ol(QQ)), ZZ_ell) otimes_(ZZ_ell) QQ_ell$。这给出了概形的一个性质良好的特征 0 上同调理论，以及一个连续表示： 
  $
    Gal_QQ -> End(H^q_et (X_(ol(QQ)), QQ_ell))
  $
  即绝对 Galois 群在特征 0 域上的有限维向量空间中的表示。 

  我们怎样研究 Galois 表示 $Gal_QQ -> End(H^q_et (X_(overline(QQ)), ZZ\/n))$？对每个满足 $gcd(p, n) = 1$ 的 $p$，固定一个嵌入 $overline(QQ) -> overline(QQ_p)$，它给出嵌入 $Gal_(QQ_p) arrow.r.hook Gal_QQ$。我们希望有同构： 
 
  $
    H^q_et (X_(overline(QQ)), ZZ\/n) ->^tilde_(#[(a)]) H^q_et (X_(overline(QQ_p)), ZZ\/n)
  $
  
  其中 $Gal_QQ$ 作用在左边，$Gal_(QQ_p)$ 作用在右边，以便研究局部情形。接下来，假设 $X_(QQ_p)$ 有整模型 $X_(ZZ_p) -> Spec(ZZ_p)$，则我们有交换图表： 
  // https://q.uiver.app/#r=typst&q=WzAsNixbMSwwLCJYXyhaWl9wXnVyKSJdLFsyLDAsIlhfKG9sKEZGX3ApKSJdLFsxLDEsIlNwZWMoWlpfcF51cikiXSxbMiwxLCJTcGVjKG9sKEZGX3ApKSJdLFswLDAsIlhfKG9sKFFRX3ApKSJdLFswLDEsIlNwZWMob2woUVFfcCkpIl0sWzUsMl0sWzMsMl0sWzQsMF0sWzEsMF0sWzAsMl0sWzEsM10sWzQsNV1d
  #align(center, diagram({
    node((0, -1), [$X_(ZZ_p^#[ur])$])
    node((1, -1), [$X_(ol(FF_p))$])
    node((0, 0), [$Spec(ZZ_p^#[ur])$])
    node((1, 0), [$Spec(ol(FF_p))$])
    node((-1, -1), [$X_(ol(QQ_p))$])
    node((-1, 0), [$Spec(ol(QQ_p))$])
    edge((-1, 0), (0, 0), "->")
    edge((1, 0), (0, 0), "->")
    edge((-1, -1), (0, -1), "->")
    edge((1, -1), (0, -1), "->")
    edge((0, -1), (0, 0), "->")
    edge((1, -1), (1, 0), "->")
    edge((-1, -1), (-1, 0), "->")
  }))
  于是我们希望有同构： 
  $
    H^q_et (X_(ol(QQ_p)), ZZ\/n) ->^tilde_(#[(b)]) H^q_et (X_(ZZ_p^#[ur]), ZZ\/n) <-^tilde_(#[(c)]) H^q_et (X_(ol(FF_p)), ZZ\/n)
  $
  使得左边带 $Gal_(QQ_p)$-作用，右边带 $Gal_(FF_p)$-作用。 

  态射 (a)、(b)、(c) 都是同构，这是各种基变换定理的推论，即紧合基变换定理与光滑基变换定理。 
  
  具体地说，(a) 需要光滑基变换，(c) 需要紧合基变换，而 (b) 两者都需要。 
  
  于是，
  
  - 只要 $X_(QQ_p)$ 在 $ZZ_p$ 上有光滑紧合模型，$Gal_QQ$ 就在 $H^q_et (X_(ol(QQ)), ZZ\/n)$ 上有 Galois 作用，并且该作用在 $p$ 处非分歧，即惯性子群 $I_(QQ_p) = ker(Gal_(QQ_p) -> Gal_(FF_p))$ 的作用平凡。 


因此，基变换定理是研究与运用平展上同调的关键而一般的工具。 

#date[
  #set align(left) 
  我刻意选择了这样的证明路线：本章不使用导出范畴，以免抽象的机器掩盖其背后的具体论证。 
  
  然而，基变换态射 (base change morphism) 本质上是一个导出对象，它的自然性从导出范畴看最为明显。相反，在这种情况下坚持停留在 Abel 范畴的框架里，就需要一段冗长而乏味的论证，只会毫无意义地掩盖构造的自然性。因此，在构造基变换态射时，我会使用导出范畴。 
]

== 基本设定与证明框架

我们先来构造基变换态射： 

#construction(name: <base-change-constr>)[
  考虑交换图表：
  // https://q.uiver.app/#r=typst&q=WzAsNCxbMCwwLCJYJyJdLFsxLDAsIlknIl0sWzAsMSwiWCJdLFsxLDEsIlkiXSxbMiwzLCJmIl0sWzAsMSwiZiciXSxbMSwzLCJnIl0sWzAsMiwiZyciLDJdXQ==
  #align(center, diagram({
    node((-1, -1), [$X'$])
    node((0, -1), [$Y'$])
    node((-1, 0), [$X$])
    node((0, 0), [$Y$])
    edge((-1, 0), (0, 0), [$f$], label-side: left, "->")
    edge((-1, -1), (0, -1), [$f'$], label-side: left, "->")
    edge((0, -1), (0, 0), [$g$], label-side: left, "->")
    edge((-1, -1), (-1, 0), [$g'$], label-side: right, "->")
  }))
  注意，对 $cal(F) in cAb(X_et)$，由伴随关系可得典范映射 $cal(F) -> g'_* g'^(-1) cal(F)$。于是有典范映射：
  $
    f_* cal(F) -> f_* g'_* g'^(-1) cal(F) = g_* f'_* (g')^(-1) cal(F)
  $
  再应用伴随，得到典范映射：
  $
    g^(-1) f_* cal(F) -> f'_* g'^(-1) cal(F)
  $
  它对 $cal(F)$ 是函子性的。取内射消解 $cal(F) -> cal(I)^bullet$。此时 $R^bullet f_* cal(F) = h^bullet (0 -> f_* cal(I)^bullet)$。逆像函子正合，且与上同调交换，所以有典范映射：
  $
    g^(-1) (R^q f_* cal(F)) cong h^q (0 -> g^(-1) f_* cal(I)^bullet) -> h^q (0 -> f'_* g'^(-1) cal(I)^bullet) -> h^q (0 -> f'_* cal(J)^bullet) = R^q f'_* (g'^(-1) cal(F))
  $
  其中 $g'^(-1) cal(F) -> cal(J)^bullet$ 是内射消解，于是有上链复形的态射 $g'^(-1) cal(I)^bullet -> cal(J)^bullet$，它在上同调上诱导典范映射。总之，对每个交换方块，都存在典范态射：
  $
    g^(-1) R^q f_* cal(F) -> R^q f'_* g'^(-1) cal(F)
  $
  它对 $cal(F)$ 是函子性的。这就是所谓的*基变换态射*。 

  上面的定义看上去很不典范、很不自然。事实上，基变换态射更自然地是导出范畴中的对象。给定 $cal(K) in D(X_et)$，基变换态射： 
  $
    g^(-1) R f_* cal(K) -> R f'_* g'^(-1) cal(K)
  $
  其定义如下： 

  - 由伴随，态射 $g^(-1) R f_* cal(K) -> R f'_* g'^(-1) cal(K)$ 等价于态射： #h(1fr)
    $
      R f_* cal(K) -> R g_* R f'_* g'^(-1) cal(K) = R (g compose f')_* g'^(-1) cal(K) = R (f compose g')_* g'^(-1) cal(K) = R f_* R g'_* g'^(-1) cal(K)
    $
    我们把这个伴随单位 $cal(K) -> R g'_* g'^(-1) cal(K)$ 沿 $R f_*$ 提升，就得到这个映射。 

  换言之，基变换态射正是 @bcbc-defn 中定义的 Beck–Chevalley 基变换，对应图表： 
  // https://q.uiver.app/#r=typst&q=WzAsNCxbMCwwLCJEKFgnX2V0KSJdLFswLDEsIkQoWF9ldCkiXSxbMSwxLCJEKFlfZXQpIl0sWzEsMCwiRChZJ19ldCkiXSxbMCwzLCJSIGYnXyoiXSxbMSwyLCJSIGZfKiIsMl0sWzMsMiwiUiBnXyoiXSxbMCwxLCJSIGcnXyoiLDJdLFsxLDNdXQ==
  #align(center, diagram({
    node((-1, -1), [$D(X'_et)$])
    node((-1, 0), [$D(X_et)$])
    node((0, 0), [$D(Y_et)$])
    node((0, -1), [$D(Y'_et)$])
    edge((-1, -1), (0, -1), [$R f'_*$], label-side: left, "->")
    edge((-1, 0), (0, 0), [$R f_*$], label-side: right, "->")
    edge((0, -1), (0, 0), [$R g_*$], label-side: left, "->")
    edge((-1, -1), (-1, 0), [$R g'_*$], label-side: right, "->")
    edge((-0.7, -0.3), (-0.3, -0.7), "=>")
  }))
  其中对角的自然变换就是同构 $R f_* compose R g'_* = R (f compose g')_* = R (g compose f')_* = R g_* compose R f'_*$。 
]

基变换态射是自然的，即它与交换方块的拼接相容。 

#lemma(name: <base-change-naturality>)[
  基变换态射与交换方块的拼接相容。给定交换图表： 
  // https://q.uiver.app/#r=typst&q=WzAsOCxbMSwyLCJYIl0sWzIsMiwiWSJdLFsyLDEsIlknIl0sWzEsMSwiWCciXSxbMSwwLCJYJyciXSxbMiwwLCJZJyciXSxbMCwxLCJXJyJdLFswLDIsIlciXSxbMCwxLCJmIiwyXSxbMywyLCJmJyJdLFs0LDUsImYnJyJdLFs3LDAsImgiLDJdLFs2LDMsImgnIl0sWzIsMSwiZyJdLFszLDAsImcnIl0sWzYsNywiZycnIiwyXSxbNSwyLCJrIl0sWzQsMywiayciXV0=
  #align(center, diagram({
    node((0, 1), [$X$])
    node((1, 1), [$Y$])
    node((1, 0), [$Y'$])
    node((0, 0), [$X'$])
    node((0, -1), [$X''$])
    node((1, -1), [$Y''$])
    node((-1, 0), [$W'$])
    node((-1, 1), [$W$])
    // node((-0.7, 0.3), $cart$)
    // node((0.3, -0.7), $cart$)
    // node((0.3, 0.3), $cart$)
    edge((0, 1), (1, 1), [$f$], label-side: right, "->")
    edge((0, 0), (1, 0), [$f'$], label-side: left, "->")
    edge((0, -1), (1, -1), [$f''$], label-side: left, "->")
    edge((-1, 1), (0, 1), [$h$], label-side: right, "->")
    edge((-1, 0), (0, 0), [$h'$], label-side: left, "->")
    edge((1, 0), (1, 1), [$g$], label-side: left, "->")
    edge((0, 0), (0, 1), [$g'$], label-side: left, "->")
    edge((-1, 0), (-1, 1), [$g''$], label-side: right, "->")
    edge((1, -1), (1, 0), [$k$], label-side: left, "->")
    edge((0, -1), (0, 0), [$k'$], label-side: left, "->")
  }))
  + 基变换态射与交换方块的竖直拼接相容，即在导出范畴中，把沿两个小方块的基变换态射复合起来： 
    $
      (k compose g)^(-1) R f_* cal(K) = k^(-1) g^(-1) R f_* cal(K) -> k^(-1) R f'_* g'^(-1) cal(K) -> R f''_* k'^(-1) g'^(-1) cal(K) = R f''_* (k' compose g')^(-1) cal(K) 
    $
    恰好就是沿右侧矩形的基变换态射。 
    取上同调，把沿两个小方块的基变换态射复合起来： 
    $
      (k compose g)^(-1) R^q f_* cal(F) = k^(-1) g^(-1) R^q f_* cal(F) -> k^(-1) R^q f'_* g'^(-1) cal(F) -> R^q f''_* k'^(-1) g'^(-1) cal(F) = R^q f''_* (k' compose g')^(-1) cal(F) 
    $
    就是沿右侧矩形的基变换态射。 

  + 基变换态射与交换方块的水平拼接相容，即在导出范畴中，把沿两个小方块的基变换态射复合起来： 
    $
      g^(-1) R(f compose h)_* cal(K) = g^(-1) R f_* R h_* cal(K) -> R f'_* g'^(-1) R h_* cal(K) -> R f'_* R h'_* g''^(-1) cal(K) = R(f' compose h')_* g''^(-1) cal(K) 
    $
    恰好就是沿下方矩形的基变换态射。 

    取上同调，得到 Leray 谱序列之间的态射 $E_2^(p,q) -> tilde(E)_2^(p,q)$，其中： 
    $
      E_2^(p,q) = g^(-1) R^p f_* R^q h_* cal(F) => g^(-1) R^(p+q) (f compose h)_* cal(F) = H^(p+q) \

      tilde(E)_2^(p,q) = R^p f'_* R^q h'_* g''^(-1) cal(F) => R^(p+q) (f' compose h')_* g''^(-1) cal(F) = tilde(H)^(p+q)
    $
    这里，$E_2^(p,q) -> tilde(E)_2^(p,q)$ 是沿下方两个方块的基变换态射的复合，而 $H^n -> tilde(H)^n$ 是沿下方矩形的基变换态射。 
]
#proof[
  我们只证明导出范畴中的陈述：(1) 的 Abel 范畴陈述可由导出版本取上同调得到，(2) 的 Abel 范畴陈述则可由导出版本取与全复形相伴的谱序列得到（当然，超上同调谱序列也可以）。 

  现在，导出范畴中的基变换态射就是一个 Beck–Chevalley 基变换，这是纯范畴论的构造。因此，(1) 与 (2) 分别由 @bcbc-vertical-concat 与 @bcbc-horizontal-concat 推出。
  /*#lemma[
    Given a commutative square of functors between categories: 
    // https://q.uiver.app/#r=typst&q=WzAsNCxbMCwwLCJjYWwoQylfMSJdLFsxLDAsImNhbChDKV8yIl0sWzAsMSwiY2FsKEQpXzEiXSxbMSwxLCJjYWwoRClfMiJdLFswLDEsImYnIl0sWzIsMywiZiIsMl0sWzEsMywiZyJdLFswLDIsImcnIiwyXV0=
    #align(center, diagram({
      node((-1, -1), [$cal(C)_1$])
      node((0, -1), [$cal(C)_2$])
      node((-1, 0), [$cal(D)_1$])
      node((0, 0), [$cal(D)_2$])
      edge((-1, -1), (0, -1), [$f'$], label-side: left, "->")
      edge((-1, 0), (0, 0), [$f$], label-side: right, "->")
      edge((0, -1), (0, 0), [$g$], label-side: left, "->")
      edge((-1, -1), (-1, 0), [$g'$], label-side: right, "->")
    }))
    s.t. $g, g'$ have left adjoints $g^L, g^L '$ respectively, we define the base change map along this square to be the natural transformation: 
    $
      g^L f -> g^L f g' g'^L ->^tilde g^L g f' g'^L -> f' g'^L
    $
    where the first map is an adjunction unit, and the third is a counit. 

    Then given a commutative diagram: 
    // https://q.uiver.app/#r=typst&q=WzAsOCxbMSwyLCJjYWwoRClfMiJdLFswLDEsImNhbChDKV8xIl0sWzEsMSwiY2FsKEMpXzIiXSxbMiwxLCJjYWwoQylfMyJdLFswLDIsImNhbChEKV8xIl0sWzIsMiwiY2FsKEQpXzMiXSxbMiwwLCJjYWwoRSlfMyJdLFsxLDAsImNhbChFKV8yIl0sWzAsNSwiZiIsMl0sWzQsMCwiaCIsMl0sWzIsMywiZiciXSxbMSwyLCJoJyJdLFszLDUsImdfMyJdLFsyLDAsImdfMiJdLFsxLDQsImdfMSIsMl0sWzcsNiwiZicnIl0sWzYsMywiaF8zIl0sWzcsMiwiaF8yIl1d
    #align(center, diagram({
      node((0, 0), [$cal(D)_2$])
      node((-1, -1), [$cal(C)_1$])
      node((0, -1), [$cal(C)_2$])
      node((1, -1), [$cal(C)_3$])
      node((-1, 0), [$cal(D)_1$])
      node((1, 0), [$cal(D)_3$])
      node((1, -2), [$cal(E)_3$])
      node((0, -2), [$cal(E)_2$])
      edge((0, 0), (1, 0), [$f$], label-side: right, "->")
      edge((-1, 0), (0, 0), [$h$], label-side: right, "->")
      edge((0, -1), (1, -1), [$f'$], label-side: left, "->")
      edge((-1, -1), (0, -1), [$h'$], label-side: left, "->")
      edge((1, -1), (1, 0), [$g_3$], label-side: left, "->")
      edge((0, -1), (0, 0), [$g_2$], label-side: left, "->")
      edge((-1, -1), (-1, 0), [$g_1$], label-side: right, "->")
      edge((0, -2), (1, -2), [$f''$], label-side: left, "->")
      edge((1, -2), (1, -1), [$h_3$], label-side: left, "->")
      edge((0, -2), (0, -1), [$h_2$], label-side: left, "->")
    }))
    in which $g_i, h_i$ have left adjoints $g_i^L, h_i^L$: 

    + The composition of natural transformations: #h(1fr)
      $
        g_3^L f h -> f' g_2^L h -> f'h'g_1^L
      $
      of successive base changes along the two bottom squares is just base change along the bottom rectangle. 

    + The composition of natural transformations: 
      $
        h_3^L g_3^L f -> h_3^L f' g_2^L -> f'' h_2^L g_2^L
      $
      of successive base changes along the two right squares is just base change along the right ==rectangle. 
  ]*/
]

以上就是基变换定理的一般设定。紧合基变换定理断言： 

#theorem(name: <proper-base-change>)[
  给定拉回图表： 
  #align(center, diagram({
    node((-1, -1), [$X'$])
    node((0, -1), [$Y'$])
    node((-1, 0), [$X$])
    node((0, 0), [$Y$])
    node((-0.7, -0.7), $cart$)
    edge((-1, 0), (0, 0), [$f$], label-side: left, "->")
    edge((-1, -1), (0, -1), [$f'$], label-side: left, "->")
    edge((0, -1), (0, 0), [$g$], label-side: left, "->")
    edge((-1, -1), (-1, 0), [$g'$], label-side: right, "->")
  }))
  
  基变换态射： #h(1fr)
  $
    g^(-1) R^q f_* cal(F) -> R^q f'_* g'^(-1) cal(F)
  $
  当 $cal(F) in cAb(X_et)$ 是挠层，$f$ 紧合，$X$ 与 $Y$ 局部 Noether 时，该态射是同构。 
]
这里的局部 Noether 假设并不必要，它只是我们方法的技术性产物；只要把证明中使用的结论稍作强化，就可以去掉这个假设。不过，局部 Noether 情形的证明已经体现了证明的精神，所以我们还是沿用这一假设。 

#construction[
  我们考虑紧合基变换的如下情形：$Y = Spec(A), Y' = ol(y) = Spec(k)$，其中 $(A, frak(m), k)$ 是严格 Hensel 局部环。此时 $X -> Spec(A)$ 紧合，$X' = X_0$ 是它的特殊纤维。于是基变换态射是 $cAb(Spec(k)_et)$ 中的态射；由于 $k$ 可分闭，它实际上是茎上的态射。 
  
  换言之，此情形下的基变换态射是：
  $
    (g^(-1) R^q f_* cal(F))_(ol(y)) = (R^q f_* cal(F))_(ol(y)) = H^q (X times_A tilde(Spec(A))_(ol(y)), cal(F)|_(X times_A tilde(Spec(A))_(ol(y)))) = H^q (X, cal(F))
  $
  因为 $A$ 已经是严格 Hensel 的，故 $tilde(Spec(A))_(ol(y)) = Spec(A)$。另一方面，
  $
    (R^q f'_* g'^(-1) cal(F))_(ol(y)) = H^q (X_0, cal(F)|_(X_0))
  $
  因为我们只是在计算整体截面 $R^q f'_* g'^(-1) cal(F) (ol(y))$，而由 @struct-of-spec-omega-et (1) 与 @derived-lower-star-first-props (3)，它就是 $H^q (X_0, cal(F)|_(X_0))$。此情形下的基变换态射就是限制映射：
  $
    H^q (X, cal(F)) -> H^q (X_0, cal(F)|_(X_0))
  $
]

#notation[
  我们把各种与基变换有关的命题简记如下： 

  - $BC^q (X ->^f Y, Y' ->^g Y, cal(F))$ 表示命题： #h(1fr)
    $
      #[基变换态射 $g^(-1)R^q f_* cal(F) -> R^q f'_* g'^(-1) cal(F) $ 是同构。]
    $

  - 对严格 Hensel 局部环 $A$，$BC^q_* (X ->^f Spec(A), cal(F))$ 表示命题： 
    $
      #[限制映射 $H^q (X, cal(F)) -> H^q (X_0, cal(F)|_(X_0)) $ 是同构。]
    $
    我们也用 $BC^q_(*,#[inj]) (f, cal(F)), BC^q_(*,#[surj])$ 分别表示这个限制是单射、满射。 

  - $BC (X ->^f Y, Y' ->^g Y)$ 表示命题：
    $
      forall q>=0, forall cal(F) in cAb(X_et) #[挠], BC^q (f, g, cal(F))
    $
    即对 $f$ 与 $g$ 决定的拉回方块、对所有挠层，基变换定理成立。类似地，$BC_* (X ->^f Spec(A))$ 表示命题： 
    $
      forall q>=0, forall cal(F) in cAb(X_et) #[挠], BC^q_* (f, cal(F))
    $

  于是紧合基变换定理就是如下陈述： 
  $
    #[$BC (X ->^f Y, Y' ->^g Y) $ 对所有紧合的 $f$ 与局部 Noether 的 $Y', Y$ 成立。]
  $
]

紧合基变换的证明包含几个大步骤，每一步都需要截然不同的技术，每一步的证明也都相当长。因此，我们在这里把每一步的主要结论总结成命题。 

#notation[
  #set enum(numbering: n => ("(Seed)", "(Dev)", "(Comp)", "(Shift)", "(Reduce)", "(Finite)").at(n - 1))

  我们定义如下命题： 

  + /*For any noetherian strict henselian $A$, any $f: X -->^#[finite] PP^1_A -> Spec(A)$, #h(1fr)

    - $BC^0_* (X ->^f Spec(A), ul(ZZ\/n))$ holds, and for all $q >= 1$, $BC^q_(*,#[surj]) (X ->^f Spec(A), ul(ZZ\/n))$ holds. */
    对任意 Noether 严格 Hensel 环 $A$， #h(1fr)
    $
      forall & f: X -->^#[finite] PP^1_A -> Spec(A), forall n>=1, \
      &BC^0_* (f, ul(ZZ\/n)) and (forall q>=1, BC^q_(*,#[surj]) (f, ul(ZZ\/n)))
    $

  + /*For any noetherian strict henselian $A$, any $f: X -> Spec(A)$, if: 

    - $BC^0_* (tilde(X) ->^g Spec(A), ul(ZZ\/n))$ holds, and for all $q >= 1$, $BC^q_(*,#[surj]) (tilde(X) ->^g Spec(A), ul(ZZ\/n))$ holds for all $g: tilde(X) ->^#[finite] X ->^f A$. 

    Then: 

    - $BC^q_* (tilde(X) ->^g Spec(A), cal(F))$ holds for all $g: tilde(X) ->^#[finite] X ->^f A$, all $q >= 0$ and all torsion $cal(F) in cAb(tilde(X)_et)$. */
    $
      (&forall tilde(X) -> X #[finite], forall n >= 1, \
      & BC^0_* (tilde(X) -> X -> Spec(A), ul(ZZ\/n)) and (forall q>=1, BC^q_(*,#[surj]) (tilde(X) -> X -> Spec(A), ul(ZZ\/n)))) \
      // ==>&(&&forall tilde(X) -> X #[finite], forall cal(F) in cAb(tilde(X)_et) #[torsion], forall q>=0, \
      // &&& BC^q_(*,#[surj])(tilde(X) -> X -> Spec(A), cal(F))))
      ==>& (forall tilde(X) -> X #[finite], BC_* (tilde(X) -> Spec(A)))
    $

  + #set enum(numbering: "(1)")
    + 在逐次基变换的图表中：
      // https://q.uiver.app/#r=typst&q=WzAsNixbMCwwLCJaJyJdLFsxLDAsIlgnIl0sWzIsMCwiWSciXSxbMiwxLCJZIl0sWzEsMSwiWCJdLFswLDEsIloiXSxbMiwzLCJnIl0sWzEsNCwiZyciXSxbMCw1LCJnJyciXSxbNCwzLCJmIiwyXSxbNSw0LCJoIiwyXSxbMCwxLCJoJyJdLFsxLDIsImYnIl1d
      #align(center, diagram({
        node((-2, -1), [$Z'$])
        node((-1, -1), [$X'$])
        node((0, -1), [$Y'$])
        node((0, 0), [$Y$])
        node((-1, 0), [$X$])
        node((-2, 0), [$Z$])
        edge((0, -1), (0, 0), [$g$], label-side: left, "->")
        edge((-1, -1), (-1, 0), [$g'$], label-side: left, "->")
        edge((-2, -1), (-2, 0), [$g''$], label-side: left, "->")
        edge((-1, 0), (0, 0), [$h$], label-side: right, "->")
        edge((-2, 0), (-1, 0), [$f$], label-side: right, "->")
        edge((-2, -1), (-1, -1), [$f'$], label-side: left, "->")
        edge((-1, -1), (0, -1), [$h'$], label-side: left, "->")
      }))
      我们有：
      $
        BC (f, g) and BC (h, g') ==> BC (h compose f, g)
      $
      即若基变换定理对左右两个小方块成立，则它对大矩形也成立。 

    + 在逐次基变换的图表中：
      // https://q.uiver.app/#r=typst&q=WzAsNixbMCwxLCJYJyJdLFsxLDEsIlknIl0sWzAsMiwiWCJdLFsxLDIsIlkiXSxbMSwwLCJZJyciXSxbMCwwLCJYJyciXSxbMiwzLCJmIl0sWzAsMSwiZiciXSxbMSwzLCJnIl0sWzAsMiwiZyciLDJdLFs1LDQsImYnJyJdLFs0LDEsImgiXSxbNSwwLCJoJyciLDJdXQ==
      #align(center, diagram({
        node((0, 0), [$X'$])
        node((1, 0), [$Y'$])
        node((0, 1), [$X$])
        node((1, 1), [$Y$])
        node((1, -1), [$Y''$])
        node((0, -1), [$X''$])
        edge((0, 1), (1, 1), [$f$], label-side: left, "->")
        edge((0, 0), (1, 0), [$f'$], label-side: left, "->")
        edge((1, 0), (1, 1), [$g$], label-side: left, "->")
        edge((0, 0), (0, 1), [$g'$], label-side: right, "->")
        edge((0, -1), (1, -1), [$f''$], label-side: left, "->")
        edge((1, -1), (1, 0), [$h$], label-side: left, "->")
        edge((0, -1), (0, 0), [$h'$], label-side: right, "->")
      }))
      我们有： 
      $
        BC(f, g) and BC(f', h) ==> BC(f, g compose h)
      $
      即若基变换定理对上下两个小方块成立，则它对大矩形也成立。 

  + 在逐次基变换的图表中，若所有概形都是 Noether 的，$X', X$ 在 $Spec(A)$ 上紧合，且 $X' ->> X$ 满射：
    // https://q.uiver.app/#r=typst&q=WzAsNixbMCwxLCJYJyJdLFsxLDEsIlgiXSxbMiwxLCJTcGVjKEEpIl0sWzIsMCwiU3BlYyhrKSJdLFsxLDAsIlhfMCJdLFswLDAsIlgnXzAiXSxbMCwxLCJwaSIsMl0sWzEsMl0sWzMsMl0sWzUsNCwicGlfMCJdLFs0LDEsImkiXSxbNSwwLCJpJyIsMl0sWzQsM11d
    #align(center, diagram({
      node((-1, 0), [$X'$])
      node((0, 0), [$X$])
      node((1, 0), [$Spec(A)$])
      node((1, -1), [$Spec(k)$])
      node((0, -1), [$X_0$])
      node((-1, -1), [$X'_0$])
      edge((-1, 0), (0, 0), [$pi$], label-side: right, "->")
      edge((0, 0), (1, 0), "->")
      edge((1, -1), (1, 0), "->")
      edge((-1, -1), (0, -1), [$pi_0$], label-side: left, "->")
      edge((0, -1), (0, 0), [$i$], label-side: left, "->")
      edge((-1, -1), (-1, 0), [$i'$], label-side: right, "->")
      edge((0, -1), (1, -1), "->")
    }))
    我们有： 
    $
      & BC(pi, i) \
      ==>& (BC_* (X -> Spec(A)) <==> BC_* (X' -> Spec(A)))
    $

  + 若 $Y', Y$ 局部 Noether，则
    $
      & BC(X ->^f Y, Y' ->^g Y) \
      <==& (BC_* (X times_Y Spec(A) -> Spec(A)), forall Spec(A) -> Y, forall A #[Noether 严格 Hensel])
    $

  + 只要 $f$ 有限，$BC(X ->^f Y, Y' ->^g Y)$ 就成立。 
]

我们先陈述证明的最后一部分，以说明上面六点如何构成相关的归约步骤，以及它们如何足以证明紧合基变换。 

#theorem[
  只要上面陈述的六点 (Seed)、(Dev)、(Comp)、(Shift)、(Reduce)、(Finite) 成立，紧合基变换定理就成立。 
]
#proof[
  由 (Seed) 与 (Dev)，对任意 Noether 严格 Hensel 环 $A$，$BC_* (PP^1_A -> Spec(A))$ 成立。 

  第一步是证明：对所有 $n >= 1$ 与局部 Noether 的 $Y$，$BC(PP^n_Y -> Y, Y' ->^g Y)$ 成立，也就是说，紧合基变换对射影空间成立。由 (Reduce)，只需对所有 Noether 严格 Hensel 环 $A$ 证明 $BC_* (PP^n_A -> Spec(A))$。现在有一个有限满射：
  $
    underbrace(PP^1_A times_A dots.c times_A PP^1_A, #[$n$ 个副本]) -> PP^n_A, ((X_1:Y_1), dots.c, (X_n:Y_n)) |-> (F_0:F_1:dots.c:F_n)
  $
  其中各个 $F_i$ 由 $product_(i=1)^n (X_i T + Y_i) = sum_(i=0)^n F_i (arrow(X), arrow(Y)) T^i$ 刻画。 

  由 (Finite)，沿这个有限满射的基变换成立。再假设基变换对 $PP^1_A times_A dots.c times_A PP^1_A -> Spec(A)$ 也成立，则由 (Shift) 可知，基变换对 $PP^n_A -> Spec(A)$ 成立。 
  
  于是，只需证明：对所有 Noether 严格 Hensel 环 $A$，沿 $PP^1_A times_A dots.c times_A PP^1_A -> Spec(A)$ 的基变换成立。这个态射分解为： 
  $
    underbrace(PP^1_A times_A dots.c times_A PP^1_A, #[$n$ 个副本]) -> underbrace(PP^1_A times_A dots.c times_A PP^1_A, #[$n-1$ 个副本]) -> dots.c -> PP^1_A -> Spec(A)
  $
  其中每一步都形如 $PP^1_(tilde(Y)) -> tilde(Y)$，$tilde(Y)$ 是某个 Noether 概形。由 (Comp)，可以假定 $n = 1$，而要证的是沿 $PP^1_Y -> Y$ 的基变换成立，即 $BC(PP^1_Y -> Y, Y' ->^g Y)$。不过由 (Reduce)，只需证明对所有 Noether 严格 Hensel 环 $A$，$BC_* (PP^1_A -> Spec(A))$ 成立，而这正是我们已有的结论。

  接下来，任取射影态射 $f: X ->^i PP^n_Y -> Y$，其中 $i$ 是闭浸入。#footnote[我们所说的态射 $f: X -> Y$ 是*射影*的，是指 $f$ 分解为 $X -> PP^n_Y -> Y$，其中 $X -> PP^n_Y$ 是闭浸入。这个定义与 @cite-hartshorne-ag 中的定义一致，在 Stacks Project 中则称为 *H-射影*。]要证明基变换对 $f$ 成立，只需证明：对所有 Noether 严格 Hensel 环 $A$ 与任意闭浸入 $i: X -> PP^n_A$，$BC_* (X ->^i PP^n_A -> Spec(A))$ 成立。现在由 (Finite) 可得 $BC_* (i)$ 成立，而我们刚刚证明了 $BC_* (PP^n_A -> Spec(A))$ 成立，且所有涉及的概形都是 Noether 的，所以由 (Comp)，$BC_* (X -> Spec(A))$ 成立。因此，只要 $f$ 射影、$Y, Y'$ 局部 Noether，$BC(X ->^f Y, Y' ->^g Y)$ 就成立。 

  现在处理一般情形：$f$ 紧合时的 $BC(X ->^f Y, Y' ->^g Y)$。由 (Reduce)，只需对所有紧合的 $X -> Spec(A)$ 与所有 Noether 环 $A$ 证明 $BC_* (X -> Spec(A))$。为此我们调用周炜良引理。 

  #lemma[
    (周炜良引理) 设 $S$ 是 Noether 概形，$f: X -> S$ 是有限型且分离的态射。则存在交换图表： 
    // https://q.uiver.app/#r=typst&q=WzAsNCxbMCwwLCJYIl0sWzEsMCwiWCciXSxbMiwwLCJQUF5uX1MiXSxbMSwxLCJTIl0sWzIsM10sWzEsMl0sWzEsMCwicGkiLDJdLFswLDMsImYiLDJdLFsxLDNdXQ==
    #align(center, diagram({
      node((-1, -1), [$X$])
      node((0, -1), [$X'$])
      node((1, -1), [$PP^n_S$])
      node((0, 0), [$S$])
      edge((1, -1), (0, 0), "->")
      edge((0, -1), (1, -1), "->")
      edge((0, -1), (-1, -1), [$pi$], label-side: right, "->")
      edge((-1, -1), (0, 0), [$f$], label-side: right, "->")
      edge((0, -1), (0, 0), "->")
    }))
    其中：

    + $pi$ 射影且满射； 

    + $X' -> PP^n_S$ 是浸入； 

    + 存在稠密开子集 $U subset X$，使得 $pi: pi^(-1) (U) -> U$ 是同构。 

    特别地，当 $f$ 紧合时，$X' -> PP^n_S$ 也紧合，从而是闭浸入。换言之，$X' -> S$ 射影。 
  ]
  #proof[
    参见 #cite-stacks("0200")[Lemma 30.18.1] 与 #cite-stacks("0201")[Remark 30.18.2]。 
  ]
  现在 $X -> Spec(A)$ 分解为：
  // https://q.uiver.app/#r=typst&q=WzAsMyxbMCwwLCJYIl0sWzIsMCwiU3BlYyhBKSJdLFsxLDEsIlgnIl0sWzIsMCwicGkiXSxbMiwxXSxbMCwxXV0=
  #align(center, diagram({
    node((-1, -1), [$X$])
    node((1, -1), [$Spec(A)$])
    node((0, 0), [$X'$])
    edge((0, 0), (-1, -1), [$pi$], label-side: left, "->")
    edge((0, 0), (1, -1), "->")
    edge((-1, -1), (1, -1), "->")
  }))
  其中 $pi: X' -> X$ 满射且射影，$X' -> Spec(A)$ 射影。由于 $X$ 与 $Spec(A)$ 都是 Noether 的，由前面关于射影态射的结论，
  $
    BC (X' ->^pi X, X_0 ->^i X) #[且] BC_* (X' -> Spec(A))
  $
  成立。又因 $X, X', Spec(A)$ 都是 Noether 的，由 (Shift)，$BC_* (X -> Spec(A))$ 成立。至此证毕。 
]

因此，要证明紧合基变换定理，我们需要逐一攻克上面六点 (Seed)、(Dev)、(Comp)、(Shift)、(Reduce)、(Finite)。 

这六点之中，(Finite) 最容易证明，而且证明其他几点时也会用到它。我们现在就来证。 

#proposition(name: <pbc-finite>)[
  (Finite) 只要 $f$ 有限，基变换态射： 
  $
    g^(-1) R^q f_* cal(F) -> R^q f'_* g'^(-1) cal(F)
  $
  就是同构。 

  （注意，这里甚至不要求 $cal(F)$ 是挠层，这与紧合基变换的陈述不同。） 
]
#proof[
  $f$ 有限时 $f_*$ 正合，故 $q >= 1$ 时两边都消没。只需证明基变换态射：
  $
    g^(-1) f_* cal(F) -> f'_* g'^(-1) cal(F)
  $
  在 $f$ 有限时是同构。对任意代数闭几何点 $ol(y') in Y'$，用 @stalks-of-finite-pushforward 计算两边的茎：
  $
    (g^(-1) f_* cal(F))_(ol(y')) = (f_* cal(F))_(g(ol(y'))) = oplus.big_(ol(x) in f^(-1)(g(ol(y')))) cal(F)_(ol(x))
  $
  另一方面，
  $
    (f'_* g'^(-1) cal(F))_(ol(y')) = oplus.big_(ol(x') in f'^(-1)(ol(y'))) (g'^(-1)cal(F))_(ol(x')) = oplus.big_(ol(x') in f'^(-1)(ol(y'))) cal(F)_(g'(ol(x')))
  $
  于是只需证明：
  $
    g': f'^(-1)(ol(y')) -> f^(-1)(g(ol(y')))
  $
  是双射。事实上，若 $ol(y) = g(ol(y'))$，则由纤维积的定义，诱导映射 $g': f'^(-1)(ol(y')) -> f^(-1)(ol(y))$ 是双射。 
]
