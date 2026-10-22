#import "void-import.typ": *
== 函子性 <sect-functoriality-of-etale-topos>

本节我们要建立： 

- 对任意概形态射 $f: X -> Y$，直像 (direct image) 函子与逆像 (inverse image) 函子 $f_*: cSh(X_et) arrows.rl cSh(Y_et): f^(-1)$； 

#construction[
  设 $f: X -> Y$ 是概形态射，则有函子：
  $
    f^(-1): Et_Y -> Et_X, (V -> Y) |-> f^(-1) (V) = (X times_Y V -> X)
  $
  
  它满足以下性质： 

  - $f^(-1) (Y) = X$；

  - $f^(-1) (V_1 times_V V_2) = f^(-1) (V_1) times_(f^(-1) (V)) f^(-1) (V_2)$。 
  
  因此，若 $cal(V) = {V_i -> V}$ 是 $Y_et$ 中的覆盖，则 ${f^(-1) (V_i) -> f^(-1) (V)}$ 是 $X_et$ 中的覆盖。 
]

#definition(name: <defn-etale-direct-image>)[
  定义*直像*函子： 
  $
    f_* = f_(et,*): cPSh(X_et) -> cPSh(Y_et), cal(F) |-> (V |-> cal(F)(f^(-1) (V)) = cal(F)(X times_Y V))
  $
]
#lemma[
  $f_*$ 是函子 $cSh(X_et) -> cSh(Y_et), cPAb(X_et) -> cPAb(Y_et), cAb(X_et) -> cAb(Y_et)$。 
]
#proof[
  事实上，只需证明：若 $cal(F)$ 是层，则 $f_* cal(F)$ 也是层。具体地说，$f_* cal(F)$ 的层条件要求 
  $
    f_* cal(F) (V) -> product_i f_* cal(F)(V_i) -> product_(i,j) f_* cal(F) (V_i times_V V_j)
  $
  对 $Et_Y$ 中的每个覆盖 $cal(V) = {V_i -> V}$ 都是等化子。然而，利用前面给出的 $f^(-1)$ 的性质，这恰好化为 $cal(F)$ 关于 $Et_X$ 中覆盖 $f^(-1) (cal(V)) = {f^(-1) (V_i) -> f^(-1) (V)}$ 的层条件；而 $cal(F)$ 是层，所以该条件成立。 
]

#definition[
  定义*预层逆像* (presheaf inverse image) 函子： 
  $
    f_(cPSh)^(-1): cPSh(Y_et) -> cPSh(X_et), cPAb(Y_et) -> cPAb(X_et), cal(G) |-> (U |-> dircolim_((V,phi)) cal(G)(V))
  $
  其中滤余极限取遍所有如下形状的交换图表： 
  // https://q.uiver.app/#r=typst&q=WzAsNCxbMCwwLCJVIl0sWzEsMCwiViJdLFswLDEsIlgiXSxbMSwxLCJZIl0sWzIsMywiZiIsMl0sWzAsMSwicGhpIl0sWzEsM10sWzAsMl1d
  #align(center, diagram({
    node((-1, -1), [$U$])
    node((0, -1), [$V$])
    node((-1, 0), [$X$])
    node((0, 0), [$Y$])
    edge((-1, 0), (0, 0), [$f$], label-side: right, "->")
    edge((-1, -1), (0, -1), [$phi$], label-side: left, "->")
    edge((0, -1), (0, 0), "->")
    edge((-1, -1), (-1, 0), "->")
  }, spacing: 1.5em))
  其中 $(V -> Y) in Et_Y$。这确实是滤过系统，如下两张图表所示： 
  // https://q.uiver.app/#r=typst&q=WzAsNixbMCwxLCJWXzEiXSxbMiwxLCJWXzIiXSxbMSwwLCJVIl0sWzEsMiwiWSJdLFsxLDEsIlZfMSB0aW1lc19ZIFZfMiJdLFs0LDEsIlgiXSxbMCwzXSxbMSwzXSxbMiwwLCJwaGlfMSIsMl0sWzIsMSwicGhpXzIiXSxbNCwwXSxbNCwxXSxbMiw0XSxbNCwzXSxbMiw1XSxbNSwzLCJmIl1d
  #align(center, diagram({
    node((-1, -1), [$V_1$])
    node((1, -1), [$V_2$])
    node((0, -2), [$U$])
    node((0, 0), [$Y$])
    node((0, -1), [$V_1 times_Y V_2$])
    node((3, -1), [$X$])
    edge((-1, -1), (0, 0), "->")
    edge((1, -1), (0, 0), "->")
    edge((0, -2), (-1, -1), [$phi_1$], label-side: right, "->")
    edge((0, -2), (1, -1), [$phi_2$], label-side: left, "->", label-sep: -2pt)
    edge((0, -1), (-1, -1), "->")
    edge((0, -1), (1, -1), "->")
    edge((0, -2), (0, -1), "->")
    edge((0, -1), (0, 0), "->")
    edge((0, -2), (3, -1), "->")
    edge((3, -1), (0, 0), [$f$], label-side: left, "->")
  }))
  // https://q.uiver.app/#r=typst&q=WzAsNixbMCwxLCJVIl0sWzEsMSwiViJdLFsyLDIsIlYnIl0sWzAsMiwiWCJdLFsxLDMsIlkiXSxbMCwwLCJ0aWxkZShWKSJdLFsxLDIsInBoaV8xIiwyLHsib2Zmc2V0IjoxfV0sWzEsMiwicGhpXzIiLDAseyJvZmZzZXQiOi0xfV0sWzAsMV0sWzAsM10sWzMsNCwiZiIsMl0sWzIsNF0sWzUsMSwidGlsZGUocGhpKSJdLFswLDVdXQ==
  #align(center, {diagram({
    node((-1, -1), [$U$])
    node((0, -1), [$V$])
    node((1, 0), [$V'$])
    node((-1, 0), [$X$])
    node((0, 1), [$Y$])
    node((-1, -2), [$tilde(V)$])
    edge((0, -1), (1, 0), [$phi_1$], label-side: right, shift: -0.05, "->")
    edge((0, -1), (1, 0), [$phi_2$], label-side: left, shift: 0.05, "->")
    edge((-1, -1), (0, -1), "->")
    edge((-1, -1), (-1, 0), "->")
    edge((-1, 0), (0, 1), [$f$], label-side: right, "->")
    edge((1, 0), (0, 1), "->")
    edge((-1, -2), (0, -1), [$tilde(phi)$], label-side: left, "->")
    edge((-1, -1), (-1, -2), "->")
  })
  h(15%)
  // https://q.uiver.app/#r=typst&q=WzAsNCxbMCwwLCJ0aWxkZShWKSJdLFsyLDAsIlYiXSxbMCwyLCJWJyJdLFsyLDIsIlYnIHRpbWVzX1kgViciXSxbMCwxLCJ0aWxkZShwaGkpIl0sWzEsMywiKHBoaV8xLHBoaV8yKSJdLFsyLDMsIkRlbHRhIiwyXSxbMCwyXV0=
  diagram({
    node((-1, -1), [$tilde(V)$])
    node((1, -1), [$V$])
    node((-1, 1), [$V'$])
    node((1, 1), [$V' times_Y V'$])
    node((-0.7, -0.7), $cart$, layer: 1, snap: false)
    edge((-1, -1), (1, -1), [$tilde(phi)$], label-side: left, "->")
    edge((1, -1), (1, 1), [$(phi_1,phi_2)$], label-side: left, "->")
    edge((-1, 1), (1, 1), [$Delta$], label-side: right, "->")
    edge((-1, -1), (-1, 1), "->")
  })
  })
]

#lemma[
  在 $cPSh(X_et)$ 与 $cPAb(X_et)$ 上，$f_(cPSh)^(-1)$ 是 $f_*$ 的左伴随，即：
  $
    Hom_cPSh (f_cPSh^(-1) cal(G), cal(F)) = Hom_cPSh (cal(G), f_* cal(F))
  $
  对 $cPAb$ 而言，同样的伴随关系成立。 
]
#proof[
  我们只对 $cPSh$ 证明，$cPAb$ 的情形完全相同。这里只构造单位与余单位态射： 
  $
    alpha_(cal(F)): f^(-1)_cPSh f_* cal(F) -> cal(F), beta_(cal(G)): cal(G) -> f_* f^(-1)_cPSh cal(G)
  $

  $
    alpha_(cal(F)): f^(-1)_cPSh f_* cal(F) (U) = dirlim_((V,phi)) cal(F)(f^(-1) (V)) &-> cal(F)(U) \
    (s in cal(F) (f^(-1)(V))) &|-> s|_U
  $
  其中态射 $U -> f^(-1)(V) = V times_Y X$ 由 $U -> X$ 与 $phi: U -> V$ 给出。 

  $
    beta_(cal(G)): cal(G)(W) &-> f_* f^(-1)_cPSh cal(G) (W) = dirlim_((V,phi:f^(-1)(W)->V)) cal(G)(V) \
    s &|-> s 
  $
  其中我们把 $s$ 送到序对 $(W, f^(-1)(W) = W times_Y X -> W)$ 中的 $s$。 

  这对单位与余单位确实满足所有自然性条件，验证起来是例行公事。这一伴随关系与拓扑景上 $f^(-1)$ 与 $f_*$ 的伴随类似。 
]

#definition(name: <defn-etale-sheaf-inverse-image>)[
  定义*层逆像* (sheaf inverse image) 函子： 
  $
    f^(-1) = f_et^(-1) := (f_cPSh^(-1))^\#: cSh(Y_et) -> cSh(X_et), cAb(Y_et) -> cAb(X_et), cal(G) |-> (f^(-1)_cPSh cal(G))^\#
  $
  若 $f: X -> Y$ 在上下文中已经明确，我们也用 $cal(F)|_X$ 表示 $f^(-1) cal(F)$。 
]

#proposition(name: <pullback-first-props>)[
  + $f^(-1)$ 在 $cSh(Y_et) -> cSh(X_et)$ 与 $cAb(Y_et) -> cAb(X_et)$ 这两种情形下都是 $f_*$ 的左伴随；#footnote[
    这一对 $f_et: (f^(-1)_et, f_(et,*)): cSh(X_et) arrows.rl cSh(Y_et)$ 称为平展意象的态射 (morphism of étale topoi)。你不需要知道这是什么意思。 
  ]
  
  + $f^(-1)_cPSh$ 与 $f^(-1)$ 都与有限极限交换，因此 $f^(-1): cAb(Y_et) -> cAb(X_et)$ 正合。 

  + 对任意 $cal(F) in cPSh(Y_et)$ 或 $cPAb(Y_et)$，都存在 $cSh(X_et)$ 或 $cAb(X_et)$ 中的典范同构：$f^(-1) cal(F)^\# -> (f^(-1)_cPSh cal(F))^\#$。 
]
#proof[
  (1) 事实上： 
  $
    Hom_(cSh(X_et)) (f^(-1) cal(F), cal(G)) &= Hom_(cSh(X_et)) ((f^(-1)_cPSh cal(F))^\#, cal(G)) \
    &= Hom_(cPSh(X_et)) (f^(-1)_cPSh cal(F), cal(G)) \
    &= Hom_(cPSh(Y_et)) (cal(F), f_* cal(G)) \
    &= Hom_(cSh(Y_et)) (cal(F), f_* cal(G))
  $

  (2) $f^(-1)$ 是先取 $f^(-1)_cPSh$ 再取 $(-)^\#$ 得到的，而 $(-)^\#$ 已知保持有限极限。因此只需证明 $f^(-1)_cPSh$ 保持有限极限。这可以逐截面验证：在每个截面上，$f^(-1)_cPSh$ 的取值都是滤余极限，而滤余极限与有限极限交换。 

  于是 $f^(-1): cAb(Y_et) -> cAb(X_et)$ 左正合，因为它保持有限极限；又右正合，因为它是左伴随。故它正合。 

  (3) 注意： 
  $
    Hom_cSh (f^(-1) cal(F)^\#, cal(G)) &= Hom_cSh (cal(F)^\#, f_* cal(G)) \
    &= Hom_cPSh (cal(F), f_* cal(G)) \
    &= Hom_cPSh (f^(-1)_cPSh cal(F), cal(G)) \
    &= Hom_cSh ((f_cPSh^(-1) cal(F))^\#, cal(G))
  $
  由 Yoneda 引理即得。 
]

#corollary[
  给定常值层 $ul(M)_Y in cAb(Y_et)$，存在典范同构 $ul(M)_X cong f^(-1) ul(M)_Y$。 
]
#proof[
  由上一条命题中的 (3)，存在典范同构： 
  $
    f^(-1) ul(M)_Y = f^(-1) ul(M)_(Y,0)^\# cong (f^(-1)_cPSh ul(M)_(Y,0))^\#
  $
  不过，$f^(-1)_cPSh ul(M)_(Y,0)$ 很容易描述：用来计算其截面的那个余极限，每一项都是 $M$，因此有典范同构 $f^(-1)_cPSh ul(M)_(Y,0) cong ul(M)_(X,0)$。 
]

// 同样的构造与性质对 $cPAb, cAb$ 继续成立。 

由于 $f_*$ 是左正合函子，我们可以对它取右导出。 

#definition(name: <defn-higher-direct-image>)[
  把左正合函子 $f_*: cAb(X_et) -> cAb(Y_et)$ 的第 $q$ 个右导出函子称为第 $q$ 个*高阶直像* (higher direct image) 函子 $R^q f_*$。 
]

#properties(name: <derived-lower-star-first-props>)[
  由于 $f_*$ 有正合的左伴随 $f^(-1)$，它把内射对象送到内射对象。因此： 

  + 对 $X overset(->, f) Y overset(->, g) Z$，有： 
    $
      f^(-1) compose g^(-1) cong (g compose f)^(-1), g_* compose f_* = (g compose f)_*
    $
    过渡到 Grothendieck–Leray 谱序列： 
    $
      E_2^(p,q) = R^p g_* (R^q f_* (cal(F))) => R^(p+q) (g compose f)_* cal(F)
    $

  + （Leray 谱序列）$Gamma(Y, f_*(-)) = Gamma(f^(-1)(Y), -)$，再过渡到 Grothendieck–Leray 谱序列： 
    $
      E_2^(p,q) = H^p_et (Y, R^q f_* cal(F)) => H^(p+q)_et (X, cal(F))
    $

  + $R^q f_* (cal(F))$ 就是 $(V |-> H^q (f^(-1) (V), cal(F)))^\#$。 
]
#proof[
  (1) $g_* compose f_* = (g compose f)_*$ 很容易直接验证。$f^(-1) compose g^(-1) = (g compose f)^(-1)$ 却难以直接验证；不过 $f^(-1) compose g^(-1)$ 是 $g_* compose f_*$ 的左伴随，而 $(g compose f)^(-1)$ 也是 $(g compose f)_*$ 的左伴随，故二者一致。 

  $E_2^(p,q) = R^p g_* (R^q f_* (cal(F))) => R^(p+q) (g compose f)_* cal(F)$ 不过是把 Grothendieck–Leray 谱序列应用于 $g_*$ 与 $f_*$，其中 $f_*$ 保持内射对象。 

  (2) 不言自明。 

  (3) 取内射消解 $0 -> cal(F) -> cal(I)^bullet$，于是： 
  $
    R^q f_* cal(F) = h^q (0 -> f_* cal(I)^bullet)
  $
  现在，层的核就是预层的核，层的余核则是预层余核的层化。故 
  $
    R^q f_* cal(F) &= h^q (0 -> f_* cal(I)^bullet) \
    &= h^q (0 -> iota(f_* cal(I)^bullet))^\# 
  $
  另一方面，$h^q (0 -> iota(f_* cal(I)^bullet))$ 可以逐截面计算：它在 $V$ 上的截面正是 $h^q (0 -> iota(f_* cal(I)^bullet) (V)) = h^q (0 -> cal(I)^bullet (f^(-1)(V))) = H^q (f^(-1)(V), cal(F))$。于是 
  $
    R^q f_* cal(F) = (V |-> H^q (f^(-1) (V), cal(F)))^\#
  $
]

最后，我们证明当 $f$ 平展时，$f^(-1)$ 有一个简单的刻画： 
#lemma(name: <pullback-along-etale-morphism>)[
  若 $f: X -> Y$ 平展，则 $f^(-1) = f^(-1)_cPSh|_cSh(Y_et)$，且有如下简单刻画： 
  $
    f^(-1)_cPSh: cPSh(Y_et) &-> cPSh(X_et) \
    cal(G) &|-> ((psi: U -> X) |-> cal(G)(f compose psi))
  $
  对 $cPAb(Y_et)$ 与 $cAb(Y_et)$ 也一样。 
]
#proof[
  $f^(-1)_cPSh$ 的简单刻画可以直接由定义得到：在定义 $f^(-1)_cPSh cal(G) (psi)$ 的余极限里，指标范畴中的 $f compose psi$ 是终对象，于是该余极限退化为 $cal(G)(f compose psi)$。 

  例行验证表明：此时 $f^(-1)_cPSh$ 已经把层送到层，因此 $f^(-1)$ 就是 $f^(-1)_cPSh$ 在 $cSh(Y_et)$ 上的限制。 
  // 导出层面的陈述可以由取内射消解并计算得到，但我们需要证明：对任意内射 $cal(I) in f^(-1) $，$f^(-1) cal(I)$ 在 $X$ 上零调
]
