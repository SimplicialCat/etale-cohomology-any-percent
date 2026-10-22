#import "void-import.typ": *

#date[
  #set align(left) 
  本章及往后，我们会频繁使用导出范畴的语言，而这些用法往往不可或缺。 
]

本章我们要构造紧支上同调，也就是函子 $R Gamma_c$ 与 $R f_!$。按惯例，我们会先讲清一个概念背后的动机，再引入它。 

平展上同调当初是作为正特征下奇异上同调的类比、并为解决 Weil 猜想而引入的。为此，我们需要 Poincaré 对偶与 Lefschetz 迹公式的类比。 

我们先回忆奇异上同调中 Poincaré 对偶与 Lefschetz 迹公式的陈述，再把其中的同调全部换成上同调——因为在平展的框架里，我们只有上同调理论。 

设 $X$ 是 $n$ 维可定向流形。 

- 奇异 Poincaré 对偶说的是，自然映射：#h(1fr)
  $
    H^k_c (X) -> H_(n-k) (X)
  $
  是同构。要把同调换成上同调，我们用一个万有系数定理。于是 Poincaré 对偶可陈述为：杯积配对： 
  $
    - smile -: H^k_c (X, QQ) times H^(n-k) (X, QQ) -> H^n_c (X, QQ) ->^(tr_X) QQ
  $
  是完美配对。 

- 奇异 Lefschetz 迹公式说的是：若映射 $f: X -> X$ 的 Lefschetz 数 
  $
    Lambda_f = sum_(i=0)^n (-1)^i tr(f_*: H_i (X, QQ))
  $
  非零，则 $f$ 有不动点。要换到上同调，我们用 Poincaré 对偶，紧支上同调也就顺带登场了： 
  $
    Lambda_f = sum_(i=0)^n (-1)^i tr(f^*: H^i_c (X, QQ))
  $

因此，要为平展上同调建立 Poincaré 对偶与 Lefschetz 迹公式的类比，就必须先把 $H^q_c (X, -)$ 或 $R Gamma_c (X, -)$ 这个概念确立起来，也就是某种紧支上同调。 

我们还需要紧支上同调的相对版本，即 $R f_!$。粗略地说，$R f_!$ 之于 $R f_*$，正如 $R Gamma_c (X, -)$ 之于 $R Gamma(X, -)$。$R f_!$ 的重要性可以从下面几点看出： 

- $R f_*$ 在某种意义上是“坏”的推前。它不与任意基变换交换，也不适合用来陈述投影公式与 Künneth 公式，除非 $f$ 紧合。 
  
  另一方面，$R f_!$ 是“好”的推前：它与任意基变换交换，可以用来陈述投影公式与 Künneth 公式。 

- 把 $R f_!$ 定义在导出范畴上，就能陈述相对形式的 Poincaré 对偶。它的姊妹函子 $R f_*$ 是右伴随，$R f_!$ 则不同，它是某个函子 $R f^!$ 的左伴随。于是这一框架下的 Poincaré 对偶，就归结为在 $f$ 光滑时具体刻画 $R f^!$。 

  这六个函子： 
  $
    f^(-1), R f_* \
    R f_!, R f^! \
    - Lotimes_Lambda -, RHHom_Lambda (-, -)
  $
  现在构成三对伴随，使我们能把平展上同调总结成一组公理化的陈述。 
  
  这就是 Grothendieck 著名的*六函子形式*，与 *Verdier 对偶*的形式体系，它们让人能从更高的视角来看平展上同调。 

最后，我们为 $R Gamma_c (X, -)$（以及 $R f_!$）的构造提供一些直观解释。对流形 $X$ 的奇异上同调，$H^q_(#[sing],c) (X, Lambda)$ 是用紧支上链定义的；平展上同调则不用上链，而用导出函子来定义。 

- 若把奇异上同调看作导出函子上同调，那么 $H^q_(#[sing],c) (X, Lambda)$ 可以这样重新解释。先假设存在开浸入 $j: X -> ol(X)$，其中 $ol(X)$ 是紧流形。那么： 
  $
    H^q_(#[sing],c) (X, Lambda) &= dirlim_(K subset X #[compact]) H^q_#[sing] (X, X - K, Lambda) = dirlim_(K subset X #[compact]) H^q (ol(X), ol(X) - K, Lambda) #[由切除] \
    &= dirlim_(K subset X #[compact]) H^q (ol(X), i_K^! ul(Lambda)_K) = H^q (ol(X), dirlim_(K subset X #[compact]) i_K^! ul(Lambda)_K) = H^q (ol(X), j_! ul(Lambda)_X)
  $
  由此可见，紧支奇异上同调可以借助一个外部紧化来定义。 

在平展上同调的框架里，充当这种外部紧化的将是 Nagata 紧化（它是非典范的），从而使 $R Gamma_c$ 与 $R f_!$ 得以定义。必须指出：这两个函子虽然（当然）与紧化的选取无关，但若不先选定一个到某个“紧”的（即紧合的）外围空间的嵌入，就无法内蕴地定义它们。 

== $R f_!$ 与 $R Gamma_c$ 的构造

正如刚才所说，$R f_!$ 与 $R Gamma_c$ 是借助外部紧化定义的，这就要用到某种紧化的存在性。 

#theorem(name: <nagata-compactification>)[
  (Nagata 紧化) 设 $f: X -> Y$ 是拟紧拟分离概形之间分离、有限型的态射。则 $f$ 可分解为： 
  $
    X ->^j ol(X) ->^(ol(f)) Y
  $
  其中 $j$ 是开浸入，$ol(f)$ 紧合。 
]
#proof[
  这是代数几何中非常有名、也很标准的结果。参见 #cite-stacks("0F41")[Theorem 38.33.8]。 
]
本章的要点就是定义： 
$
  R f_! = R ol(f)_* compose j_!
$
然而紧化的选取极不唯一，也毫不典范。因此我们必须先对紧化建立一些一般性结论，才能说明由不同紧化给出的 $R ol(f)_* compose j_!$ 彼此相容。 

#definition(name: <defn-compactification>)[
  对分离、有限型的态射 $f: X -> Y$，所谓 $f$ 的*紧化*，指的是一个分解： 
  $
    X ->^j ol(X) ->^(ol(f)) Y
  $
  其中 $j$ 是开浸入，$ol(f)$ 紧合。 
  
  两个紧化 $X ->^(j_1) ol(X)_1 ->^(ol(f)_1) Y$ 与 $X ->^(j_2) ol(X)_2 ->^(ol(f)_2) Y$ 之间的态射，指的是一个态射 $h: ol(X)_1 -> ol(X)_2$，它使下图交换： 
  // https://q.uiver.app/#r=typst&q=WzAsNCxbMCwxLCJYIl0sWzEsMCwib2woWClfMSJdLFsyLDEsIlkiXSxbMSwyLCJvbChYKV8yIl0sWzAsMSwial8xIl0sWzAsMywial8yIiwyXSxbMSwyLCJvbChmKV8xIl0sWzMsMiwib2woZilfMiIsMl0sWzEsMywiaCIsMV1d
  #context align(center, diagram({
    node((-1, 0), [$X$])
    node((0, -1), [$ol(X)_1$])
    node((1, 0), [$Y$])
    node((0, 1), [$ol(X)_2$])
    edge((-1, 0), (0, -1), [$j_1$], label-side: left, "->")
    edge((-1, 0), (0, 1), [$j_2$], label-side: right, "->")
    edge((0, -1), (1, 0), [$ol(f)_1$], label-side: left, "->")
    edge((0, 1), (1, 0), [$ol(f)_2$], label-side: right, "->")
    edge((0, -1), (0, 1), [$h$], label-side: center, "->")
  }, crossing-fill: thm-box-curr-color(), spacing: (3em, 2em)))
  由于紧合态射可以消去（复合态射与其后一个因子都紧合），这样的 $h$ 必定紧合。 
]

#proposition(name: <compactification-filtered>)[
  设 $f: X -> Y$ 是拟紧拟分离概形之间分离、有限型的态射。则 $f$ 的紧化构成一个正向系统。换言之： 

  + 给定两个紧化 $X ->^(j_i) ol(X)_i ->^(ol(f)_i) Y$，存在第三个紧化 $X ->^j ol(X) ->^(ol(f)) Y$，它同时有到 $ol(X)_1$ 与 $ol(X)_2$ 的态射。 

  + 给定两个紧化 $X ->^(j_i) ol(X)_i ->^(ol(f)_i) Y$ 之间的两个态射 $h_(1,2): ol(X)_1 -> ol(X)_2$，存在第三个紧化 $X ->^j ol(X) ->^(ol(f)) Y$，以及紧化之间的态射 $g: ol(X) -> ol(X)_1$，使得 $h_1 compose g = h_2 compose g$。 
]
#proof[
  (1) 我们可以作纤维积： 
  // https://q.uiver.app/#r=typst&q=WzAsNSxbMCwxLCJYIl0sWzIsMSwib2woWClfMSB0aW1lc19ZIG9sKFgpXzIiXSxbMywxLCJZIl0sWzIsMCwib2woWClfMSJdLFsyLDIsIm9sKFgpXzIiXSxbMCwzLCJqXzEiXSxbMCw0LCJqXzIiLDJdLFszLDIsIm9sKGYpXzEiXSxbNCwyLCJvbChmKV8yIiwyXSxbMSwzLCJwXzEiLDFdLFsxLDQsInBfMiIsMV0sWzEsMiwicGhpIiwxXSxbMCwxLCJnYW1tYSIsMV1d
  #context align(center, diagram({
    node((-1, 0), [$X$])
    node((1, 0), [$ol(X)_1 times_Y ol(X)_2$])
    node((2, 0), [$Y$])
    node((1, -1), [$ol(X)_1$])
    node((1, 1), [$ol(X)_2$])
    edge((-1, 0), (1, -1), [$j_1$], label-side: left, "->")
    edge((-1, 0), (1, 1), [$j_2$], label-side: right, "->")
    edge((1, -1), (2, 0), [$ol(f)_1$], label-side: left, "->")
    edge((1, 1), (2, 0), [$ol(f)_2$], label-side: right, "->")
    edge((1, 0), (1, -1), [$p_1$], label-side: center, "->")
    edge((1, 0), (1, 1), [$p_2$], label-side: center, "->")
    edge((1, 0), (2, 0), [$phi$], label-side: center, "->")
    edge((-1, 0), (1, 0), [$gamma$], label-side: center, "->")
  }, crossing-fill: thm-box-curr-color()))

  现在考虑 $gamma: X -> ol(X)_1 times_Y ol(X)_2$。它是两个浸入的积，因此是浸入。这里所有概形都是拟紧拟分离的。由 #cite-stacks("01QV")[Lemma 29.3.2]，拟紧的浸入可分解为先一个开浸入、再一个闭浸入。于是 $gamma$ 分解为： 
  $
    X ->^j ol(X) ->^t ol(X)_1 times_Y ol(X)_2
  $
  其中 $j$ 是开浸入，$t$ 是闭浸入。于是我们有下图： 
  // https://q.uiver.app/#r=typst&q=WzAsNixbMCwxLCJYIl0sWzIsMSwib2woWClfMSB0aW1lc19ZIG9sKFgpXzIiXSxbMywxLCJZIl0sWzIsMCwib2woWClfMSJdLFsyLDIsIm9sKFgpXzIiXSxbMSwxLCJvbChYKSJdLFswLDMsImpfMSJdLFswLDQsImpfMiIsMl0sWzMsMiwib2woZilfMSJdLFs0LDIsIm9sKGYpXzIiLDJdLFsxLDMsInBfMSIsMV0sWzEsNCwicF8yIiwxXSxbMSwyLCJwaGkiLDFdLFswLDUsImoiLDFdLFs1LDEsInQiLDFdLFs1LDMsInFfMSIsMV0sWzUsNCwicV8yIiwxXV0=
  #context align(center, diagram({
    node((0, 1), [$X$])
    node((2, 1), [$ol(X)_1 times_Y ol(X)_2$])
    node((3, 1), [$Y$])
    node((2, 0), [$ol(X)_1$])
    node((2, 2), [$ol(X)_2$])
    node((1, 1), [$ol(X)$])
    edge((0, 1), (2, 0), [$j_1$], label-side: left, "->")
    edge((0, 1), (2, 2), [$j_2$], label-side: right, "->")
    edge((2, 0), (3, 1), [$ol(f)_1$], label-side: left, "->")
    edge((2, 2), (3, 1), [$ol(f)_2$], label-side: right, "->")
    edge((2, 1), (2, 0), [$p_1$], label-side: center, "->")
    edge((2, 1), (2, 2), [$p_2$], label-side: center, "->")
    edge((2, 1), (3, 1), [$phi$], label-side: center, "->")
    edge((0, 1), (1, 1), [$j$], label-side: center, "->")
    edge((1, 1), (2, 1), [$t$], label-side: center, "->")
    edge((1, 1), (2, 0), [$h_1$], label-side: center, "->")
    edge((1, 1), (2, 2), [$h_2$], label-side: center, "->")
  }, crossing-fill: thm-box-curr-color()))
  现在 $phi$ 是两个紧合态射的积，因此紧合；$t$ 是闭浸入。于是我们构造出了紧化 $X ->^j ol(X) ->^(phi compose t) Y$，它分别有到 $ol(X)_(1,2)$ 的态射 $h_(1,2)$。 

  (2) 考虑图态射： 
  $
    Gamma_(h_1), Gamma_(h_2): ol(X)_1 -> ol(X)_1 times_Y ol(X)_2
  $
  这两个态射分别是对角态射 $Delta_(ol(X)_1\/Y): ol(X)_2 -> ol(X)_2 times_Y ol(X)_2$ 沿 $h_(1,2): ol(X)_1 -> ol(X)_2$ 的基变换，因此都是闭浸入。现在作拉回方块： 
  // https://q.uiver.app/#r=typst&q=WzAsNCxbMCwwLCJXIl0sWzEsMCwib2woWClfMSJdLFswLDEsIm9sKFgpXzEiXSxbMSwxLCJvbChYKV8xIHRpbWVzX1kgb2woWClfMiJdLFswLDEsInBfMSJdLFswLDIsInBfMiIsMl0sWzEsMywiR2FtbWFfKGhfMSkiXSxbMiwzLCJHYW1tYV8oaF8yKSIsMl1d
  #align(center, diagram({
    node((-1, -1), [$W$])
    node((-0.7, -0.7), $cart$)
    node((0, -1), [$ol(X)_1$])
    node((-1, 0), [$ol(X)_1$])
    node((0, 0), [$ol(X)_1 times_Y ol(X)_2$])
    edge((-1, -1), (0, -1), [$p_1$], label-side: left, "->")
    edge((-1, -1), (-1, 0), [$p_2$], label-side: right, "->")
    edge((0, -1), (0, 0), [$Gamma_(h_1)$], label-side: left, "->")
    edge((-1, 0), (0, 0), [$Gamma_(h_2)$], label-side: right, "->")
  }))
  其中每个态射都是闭浸入。记投影为 $q: ol(X)_1 times_Y ol(X)_2 -> ol(X)_1$。注意： 
  $
    p_1 = p_1 compose Gamma_(h_1) compose q = p_2 compose Gamma_(h_2) compose q = p_2
  $
  因此我们可以记 $p = p_1 = p_2: W -> ol(X)_1$。我们断言，$p$ 是 $h_(1,2): ol(X)_1 -> ol(X)_2$ 在 $Y$-概形范畴中的等化子。事实上，一个 $Y$-态射 $k: Z -> W$ 等价于两个 $Y$-态射 $k_(1,2): Z -> ol(X)_1$，使得 $Gamma_(h_1) compose k_1 = Gamma_(h_2) compose k_2$。把两个投影作用上去，可见该条件等价于： 
  $
    k_1 = k_2, h_1 compose k_1 = h_2 compose k_2
  $
  于是 $Y$-态射 $k: Z -> W$ 无非就是一个 $Y$-态射 $k' = k_1 = k_2: Z -> ol(X)_1$，使得 $h_1 compose k' = h_2 compose k'$。 

  现在看下图： 
  // https://q.uiver.app/#r=typst&q=WzAsNSxbMCwxLCJYIl0sWzEsMSwib2woWClfMSJdLFsyLDEsIlkiXSxbMSwyLCJvbChYKV8yIl0sWzEsMCwiVyJdLFswLDQsImpfMCIsMCx7InN0eWxlIjp7ImJvZHkiOnsibmFtZSI6ImRhc2hlZCJ9fX1dLFs0LDEsImdfMCJdLFswLDEsImpfMSIsMl0sWzEsMiwib2woZl8xKSIsMl0sWzEsMywiaF8xIiwyLHsib2Zmc2V0IjoxfV0sWzEsMywiaF8yIiwwLHsib2Zmc2V0IjotMX1dLFswLDMsImpfMiIsMl0sWzMsMiwib2woZilfMiIsMl1d
  #align(center, diagram({
    node((-1, 0), [$X$])
    node((0, 0), [$ol(X)_1$])
    node((1, 0), [$Y$])
    node((0, 1), [$ol(X)_2$])
    node((0, -1), [$W$])
    edge((-1, 0), (0, -1), [$j_0$], label-side: left, "-->")
    edge((0, -1), (0, 0), [$p$], label-side: left, "->")
    edge((-1, 0), (0, 0), [$j_1$], label-side: right, "->")
    edge((0, 0), (1, 0), [$ol(f_1)$], label-side: right, "->")
    edge((0, 0), (0, 1), [$h_1$], label-side: right, shift: -0.05, "->")
    edge((0, 0), (0, 1), [$h_2$], label-side: left, shift: 0.05, "->")
    edge((-1, 0), (0, 1), [$j_2$], label-side: right, "->")
    edge((0, 1), (1, 0), [$ol(f)_2$], label-side: right, "->")
  }))
  由泛性质，存在 $Y$-态射 $j_0: X -> W$，使得 $p compose j_0 = j_1$。既然 $j_1$ 是开浸入、$p$ 是闭浸入，$j_0$ 必定是开浸入。又 $ol(f)_1 compose p$ 紧合，故： 
  $
    X ->^(j_0) W ->^(ol(f)_1 compose f) Y
  $
  这就给出了一个紧化，并带有紧化之间的态射 $p: W -> ol(X)_1$，它等化 $h_(1,2)$。 
]

#construction[
  假设有交换方块： 
  // https://q.uiver.app/#r=typst&q=WzAsNCxbMCwwLCJYXzEiXSxbMCwxLCJYXzIiXSxbMSwxLCJZXzIiXSxbMSwwLCJZXzEiXSxbMCwzLCJmXzEiXSxbMSwyLCJmXzIiLDJdLFswLDEsImpfWCIsMl0sWzMsMiwial9ZIl1d
  #align(center, diagram({
    node((-1, 0), [$X_1$])
    node((-1, 1), [$X_2$])
    node((0, 1), [$Y_2$])
    node((0, 0), [$Y_1$])
    edge((-1, 0), (0, 0), [$f_1$], label-side: left, "->")
    edge((-1, 1), (0, 1), [$f_2$], label-side: right, "->")
    edge((-1, 0), (-1, 1), [$j_X$], label-side: right, "->")
    edge((0, 0), (0, 1), [$j_Y$], label-side: left, "->")
  }))
  其中竖直态射是开浸入，水平态射紧合。 
  
  #lemma[
    沿用上述设定，基变换映射： 
    $
      j_Y^(-1) R f_(2,*) j_(X,!) -> R f_(1,*) j_X^(-1) j_(X,!) = R f_(1,*)
    $
    是同构。 
  ]
  #proof[
    作基变换 $tilde(X) = X_2 times_(Y_2) Y_1$，得到下图： 
    // https://q.uiver.app/#r=typst&q=WzAsNixbMCwyLCJYXzIiXSxbMSwyLCJZXzIiXSxbMSwxLCJZXzEiXSxbMCwxLCJ0aWxkZShYKSJdLFswLDAsIlhfMSJdLFsxLDAsIllfMSJdLFswLDEsImZfMiIsMl0sWzMsMiwidGlsZGUoZikiXSxbNCw1LCJmXzEiXSxbNCwzLCJwIiwyXSxbMywwLCJ0aWxkZShqKSIsMl0sWzIsMSwial9ZIl0sWzUsMiwiIiwwLHsic3R5bGUiOnsiYm9keSI6eyJuYW1lIjoiZG90dGVkIn19fV1d
    #align(center, diagram({
      node((-1, 1), [$X_2$])
      node((0, 1), [$Y_2$])
      node((0, 0), [$Y_1$])
      node((-1, 0), [$tilde(X)$])
      node((-1, -1), [$X_1$])
      node((0, -1), [$Y_1$])
      edge((-1, 1), (0, 1), [$f_2$], label-side: right, "->")
      edge((-1, 0), (0, 0), [$tilde(f)$], label-side: left, "->")
      edge((-1, -1), (0, -1), [$f_1$], label-side: left, "->")
      edge((-1, -1), (-1, 0), [$p$], label-side: right, "->")
      edge((-1, 0), (-1, 1), [$tilde(j)$], label-side: right, "->")
      edge((0, 0), (0, 1), [$j_Y$], label-side: left, "->")
      edge((0, -1), (0, 0), "=")
      node((-0.7, 0.3), $cart$)
    }))
    其中 $f_1, tilde(f), f_2$ 紧合，$tilde(j)$ 是开浸入。现在 $j_X = tilde(j) compose p$，而 $j_X, tilde(j)$ 都是开浸入，所以 $p$ 也是开浸入。另一方面，$f_1 = tilde(f) compose p$ 且 $f_1, tilde(f)$ 紧合，故 $p$ 紧合。于是 $p$ 是开闭浸入。 

    接下来，由基变换的自然性，基变换映射 $j_Y^(-1) R f_(2,*) j_(X,!) -> R f_(1,*) j_X^(-1) j_(X,!)$ 分解为沿两个方块的基变换： 
    $
      j_Y^(-1) R f_(2,*) j_(X,!) -> R tilde(f)_* tilde(j)^(-1) j_(X,!) -> R f_(1,*) j_X^(-1) j_(X,!)
    $
    由 @pbc-etale-bc，第一个基变换是同构。对第二个基变换，注意 $p$ 是开闭浸入，故 $R p_* = p_!$，从而 $R f_(1,*) j_X^(-1) j_(X,!)= R tilde(f)_* p_! p^(-1) tilde(j) j_(X,!)$。在这一等同下，第二个基变换不过是伴随的单位： 
    $
      R tilde(f)_* tilde(j)^(-1) j_(X,!) -> R f_(1,*) j_X^(-1) j_(X,!)= R tilde(f)_* p_! p^(-1) tilde(j)^(-1) j_(X,!)
    $
    现在单位 $id -> p_! p^(-1) = R p_* p^(-1)$ 在支集含于 $X_1$ 的复形上是同构，因此 $tilde(j)^(-1) j_(X,!) -> p_! p^(-1) tilde(j)^(-1) j_(X,!)$ 是同构。证毕。 
  ]
  
  于是有自然变换： 
  $
    j_(Y,!) R f_(1,*) -> R f_(2,*) j_(X,!)
  $
  它是函子 $D(X_(1,et), Lambda) -> D(Y_(2,et), Lambda)$ 之间的自然变换，由同构 $j_Y^(-1) R f_(2,*) j_(X,!) ->^tilde R f_(1,*)$ 的逆经伴随对应提升得到。
]

#lemma(name: <open-proper-compat-naturality>)[
  上面构造的自然变换 $j_(Y,!) R f_(1,*) -> R f_(2,*) j_(X,!)$ 与交换图的水平拼接、竖直拼接相容。 
]
#proof[
  我们将证明上述态射是一个 Beck–Chevalley 基变换，其定义见 @bcbc-defn。事实上，考虑下图： 
  // https://q.uiver.app/#r=typst&q=WzAsNCxbMCwwLCJEKFhfKDIsZXQpKSJdLFsxLDAsIkQoWV8oMixldCkpIl0sWzAsMSwiRChYXygxLGV0KSkiXSxbMSwxLCJEKFlfKDEsZXQpKSJdLFswLDEsIlIgZl8oMiwqKSJdLFsyLDMsIlIgZl8oMSwqKSIsMl0sWzAsMiwial9YXigtMSkiLDJdLFsxLDMsImpfWV4oLTEpIl1d
  #context align(center, diagram({
    node((-1, -1), [$D(X_(2,et))$])
    node((0, -1), [$D(Y_(2,et))$])
    node((-1, 0), [$D(X_(1,et))$])
    node((0, 0), [$D(Y_(1,et))$])
    edge((-1, -1), (0, -1), [$R f_(2,*)$], label-side: left, "->")
    edge((-1, 0), (0, 0), [$R f_(1,*)$], label-side: right, "->")
    edge((-1, -1), (-1, 0), [$j_X^(-1)$], label-side: right, "->")
    edge((0, -1), (0, 0), [$j_Y^(-1)$], label-side: left, "->")
    edge((-0.7, -0.3), (-0.3, -0.7), $t$, "=>", label-side: center)
  }, crossing-fill: thm-box-curr-color()))
  
  图中对角位置的自然变换 $t$ 定义如下。沿用上一条引理的设定： 
  #align(center, diagram({
    node((-1, 1), [$X_2$])
    node((0, 1), [$Y_2$])
    node((0, 0), [$Y_1$])
    node((-1, 0), [$tilde(X)$])
    node((-1, -1), [$X_1$])
    node((0, -1), [$Y_1$])
    edge((-1, 1), (0, 1), [$f_2$], label-side: right, "->")
    edge((-1, 0), (0, 0), [$tilde(f)$], label-side: left, "->")
    edge((-1, -1), (0, -1), [$f_1$], label-side: left, "->")
    edge((-1, -1), (-1, 0), [$p$], label-side: right, "->")
    edge((-1, 0), (-1, 1), [$tilde(j)$], label-side: right, "->")
    edge((0, 0), (0, 1), [$j_Y$], label-side: left, "->")
    edge((0, -1), (0, 0), "=")
    node((-0.7, 0.3), $cart$)
  }))

  定义 $t$ 为： 
  $
    t: R f_(1,*) j_X^(-1) = R tilde(f)_* p_! p^(-1) tilde(j)^(-1) -> R tilde(f)_* tilde(j)^(-1) ->^tilde j_Y^(-1) R f_(2,*)
  $
  其中第一个映射是等号给出的等同，第二个映射是伴随的余单位，第三个映射是基变换的逆。 

  注意上方方块的基变换映射是伴随的单位： 
  $
    R tilde(f)_* -> R tilde(f)_* p_! p^(-1) = R f_(1,*) p^(-1)
  $
  并且单位与余单位的复合 $p_! p^(-1) -> id -> p_! p^(-1)$ 是同构。因此上面的映射 $t$ 是基变换映射 $b: j_Y^(-1) R f_(2,*) -> R f_(1,*) j_X^(-1)$ 的一个截面。 

  - 事实上，与这个 $t$ 对应的 Beck–Chevalley 基变换是映射：#h(1fr)
    $
      j_(Y,!) R f_(1,*) = j_(Y,!) R f_(1,*) j_X^(-1) j_(X,!) ->^(j_(Y,!) t j_(X,!)) j_(Y,!) j_Y^(-1) R f_(2,*) j_(X,!) ->^#[余单位] R f_(2,*) j_(X,!)
    $
  
    在伴随对应下，它对应于由下式定义的映射 $R f_(1,*) -> j_Y^(-1) R f_(2,*) j_(X,!)$：#h(1fr)
    $
      R f_(1,*) = R f_(1,*) j_X^(-1) j_(X,!) ->^(t j_(X,!)) j_Y^(-1) R f_(2,*) j_(X,!)
    $

    由于 $t$ 是基变换的截面，上面的映射也就是基变换 $j_Y^(-1) R f_(2,*) j_(X,!) -> R f_(1,*) j_X^(-1) j_(X,!) = R f_(1,*)$ 的截面，而后者由上一条引理是同构。于是上面的态射恰是同构 $j_Y^(-1) R f_(2,*) j_(X,!) ->^tilde R f_(1,*)$ 的逆。按我们对映射 $j_(Y,!) R f_(1,*) -> R f_(2,*) j_(X,!)$ 的构造，它在伴随下对应的正是这个映射。因此 $j_(Y,!) R f_(1,*) -> R f_(2,*) j_(X,!)$ 确实就是这个 Beck–Chevalley 基变换。 

  我们断言，$t$ 是 $b$ 唯一的自然截面，即作为自然变换的唯一截面。 

  - $b$ 是两个基变换的复合：#h(1fr)
    $
      j_Y^(-1) R f_(2,*) ->^(b_1) R tilde(f)_* tilde(j)^(-1) ->^(b_2) R f_(1,*) j_X^(-1)
    $
    其中 $b_1$ 是同构。因此只需证明 $b_2$ 的截面唯一。 

    设 $u: R f_(1,*) j_X^(-1) -> R tilde(f)_* tilde(j)^(-1)$ 是 $b_2$ 的一个截面。 

  - 再取 $j_X: X_1 -> X_2$ 的补 $i: Z -> X_2$，它是闭浸入。于是对复形 $cal(K) in D(X_(2,et), Lambda)$，有特殊三角： 
    $
      j_(X,!) j_X^(-1) cal(K) -> cal(K) -> i_* i^(-1) cal(K) ->^(+1)
    $
    注意 $j_X^(-1) i_* i^(-1) cal(K) = 0$。因此 $u$ 在 $i_* i^(-1) cal(K)$ 上是 $0$，从而 $u$ 由它在形如 $j_(X,!) cal(L)$ 的对象上的作用决定，其中 $cal(L) in D(tilde(X)_(1,et), Lambda)$。 

  - 对这类对象，$b_2 j_(X,!)$ 就是基变换 $R tilde(f)_* tilde(j)^(-1) j_(X,!) -> R f_(1,*) j_X^(-1) j_(X,!) = R f_(1,*)$，上一条引理已证它是同构。换言之，$b_2$ 在形如 $j_(X,!) cal(L)$ 的对象上是同构，故 $u$ 在这些对象上的作用就是 $b_2$ 的逆，从而完全确定。 

  于是 $b$ 的截面唯一，就是 $t$。现在考虑交换方块的水平或竖直拼接：对两个小方块分别定义的自然变换 $t$，它们的复合必须等于对矩形定义的 $t$——因为由 @base-change-naturality，基变换的自然性保证它们都是大矩形基变换的截面，再由上面论证的唯一性即得相等。 

  因此，按 @bcbc-horizontal-concat 与 @bcbc-vertical-concat 中对 Beck–Chevalley 基变换所论证的一般性结论，映射 $j_(Y,!) R f_(1,*) ->^tilde R f_(2,*) j_(X,!)$ 与交换方块的水平拼接、竖直拼接相容。 
]

#proposition(name: <open-proper-compat>)[
  给定交换图： 
  // https://q.uiver.app/#r=typst&q=WzAsNCxbMCwwLCJYXzEiXSxbMCwxLCJYXzIiXSxbMSwxLCJZXzIiXSxbMSwwLCJZXzEiXSxbMCwzLCJmXzEiXSxbMSwyLCJmXzIiLDJdLFswLDEsImpfWCIsMl0sWzMsMiwial9ZIl1d
  #align(center, diagram({
    node((-1, 0), [$X_1$])
    node((-1, 1), [$X_2$])
    node((0, 1), [$Y_2$])
    node((0, 0), [$Y_1$])
    edge((-1, 0), (0, 0), [$f_1$], label-side: left, "->")
    edge((-1, 1), (0, 1), [$f_2$], label-side: right, "->")
    edge((-1, 0), (-1, 1), [$j_X$], label-side: right, "->")
    edge((0, 0), (0, 1), [$j_Y$], label-side: left, "->")
  }))
  其中水平态射紧合，竖直态射是开浸入，且所有概形都是 Noether 的。则对 $cal(K) in D_#[tor] (X_(1,et), Lambda)$，典范映射： 
  $
    j_(Y,!) R f_(1,*) cal(K) -> R f_(2,*) j_(X,!) cal(K)
  $
  是拟同构。 
]
#proof[
  按构造，沿 $j_Y$ 拉回后得到的是与基变换互逆的映射 $R f_(1,*) cal(K) -> j_Y^(-1) R f_(2,*) j_(X,!) cal(K)$： 
  $
    j_Y^(-1) R f_(2,*) j_(X,!) cal(K) -> R f_(1,*) j_X^(-1) j_(X,!) cal(K) = R f_(1,*) cal(K)
  $
  从而是同构。于是取 $j_Y: Y_1 -> Y_2$ 的补，即闭浸入 $i: Z -> Y_2$，只需证明 $j_(Y,!) R f_(1,*) cal(K) -> R f_(2,*) j_(X,!) cal(K)$ 沿 $i$ 拉回后仍是同构。 

  注意 $i^(-1) j_(Y,!) = 0$，因此 $i^(-1) j_(Y,!) R f_(1,*) cal(K) = 0$。另一方面，由 $cal(K) in D_#[tor] (X_(1,et), Lambda)$ 及 @torsion-sheaves-first-props，$j_(X,!) cal(K) in D_#[tor] (X_(2,et), Lambda)$ 是挠的。由于 $f_2$ 紧合，且涉及的概形都是 Noether 的，紧合基变换适用。用 $f_2$ 与 $i$ 作拉回方块： 
  // https://q.uiver.app/#r=typst&q=WzAsNixbMCwwLCJYXzEiXSxbMCwxLCJYXzIiXSxbMSwxLCJZXzIiXSxbMSwwLCJZXzEiXSxbMSwyLCJaIl0sWzAsMiwiVyJdLFswLDMsImZfMSJdLFsxLDIsImZfMiIsMl0sWzAsMSwial9YIiwyXSxbMywyLCJqX1kiXSxbNSw0LCJmJyIsMl0sWzQsMiwiaSIsMl0sWzUsMSwiaSciXV0=
  #align(center, diagram({
    node((0, 0), [$X_1$])
    node((0, 1), [$X_2$])
    node((1, 1), [$Y_2$])
    node((1, 0), [$Y_1$])
    node((1, 2), [$Z$])
    node((0, 2), [$W$])
    edge((0, 0), (1, 0), [$f_1$], label-side: left, "->")
    edge((0, 1), (1, 1), [$f_2$], label-side: right, "->")
    edge((0, 0), (0, 1), [$j_X$], label-side: right, "->")
    edge((1, 0), (1, 1), [$j_Y$], label-side: left, "->")
    edge((0, 2), (1, 2), [$f'$], label-side: right, "->")
    edge((1, 2), (1, 1), [$i$], label-side: right, "->")
    edge((0, 2), (0, 1), [$i'$], label-side: left, "->")
    node((0.3, 1.7), rotate(-90deg, $cart$))
  }))
  则由紧合基变换： 
  $
    i^(-1) R f_(2,*) j_(X,!) cal(K) = R f'_* i'^(-1) j_(X,!) cal(K)
  $
  然而： 
  $
    X_1 times_(X_2) W = X_1 times_(X_2) X_2 times_(Y_2) Z = X_1 times_(Y_2) Z = emptyset
  $
  因为 $X_1$ 在 $Y_2$ 中的像含于 $Y_1$，与 $Z$ 不交。因此 $i'^(-1) j_(X,!) cal(K) = 0$。 

  换言之，我们证明了 $j_(Y,!) R f_(1,*) cal(K) -> R f_(2,*) j_(X,!) cal(K)$ 沿 $j_Y$ 拉回是同构，沿 $i$ 拉回则是零对象之间的态射。因此它是同构。 
]

现在可以证明 $R f_!$ 的良定义性了。 

#theorem(name: <derived-lower-shriek-well-defined>)[
  设 $f: X -> Y$ 是 Noether 概形之间分离、有限型的态射。给定两个紧化： 
  // https://q.uiver.app/#r=typst&q=WzAsNCxbMCwxLCJYIl0sWzIsMSwiWSJdLFsxLDAsIm9sKFgpXzEiXSxbMSwyLCJvbChYKV8yIl0sWzAsMiwial8xIl0sWzAsMywial8yIiwyXSxbMiwxLCJvbChmKV8xIl0sWzMsMSwib2woZilfMiIsMl1d
  #align(center, diagram({
    node((-1, 0), [$X$])
    node((1, 0), [$Y$])
    node((0, -1), [$ol(X)_1$])
    node((0, 1), [$ol(X)_2$])
    edge((-1, 0), (0, -1), [$j_1$], label-side: left, "->")
    edge((-1, 0), (0, 1), [$j_2$], label-side: right, "->")
    edge((0, -1), (1, 0), [$ol(f)_1$], label-side: left, "->")
    edge((0, 1), (1, 0), [$ol(f)_2$], label-side: right, "->")
  }, spacing: (2em, 1.5em)))
  存在典范同构： 
  $
    R ol(f)_(1,*) j_(1,!) cal(K) -> R ol(f)_(2,*) j_(2,!) cal(K)
  $
  其中 $cal(K) in D_#[tor] (X_et, Lambda)$。 
]
#proof[
  - 第一步。当紧化之间存在态射 $phi: ol(X)_1 -> ol(X)_2$ 时，构造同构。 

    给定这样的态射 $phi$，有 $j_2 = phi compose j_1$ 与 $ol(f)_1 = ol(f)_2 compose phi$，且 $phi$ 紧合。现在： 
    $
      R ol(f)_(1,*) j_(1,!) cal(K) = R ol(f)_(2,*) R phi_* j_(1,!) cal(K)
    $

    现在考虑交换图： 
    // https://q.uiver.app/#r=typst&q=WzAsNCxbMCwwLCJYIl0sWzAsMSwib2woWClfMSJdLFsxLDEsIm9sKFgpXzIiXSxbMSwwLCJYIl0sWzEsMiwicGhpIiwyXSxbMCwxLCJqXzEiLDJdLFswLDMsIiIsMCx7InN0eWxlIjp7ImJvZHkiOnsibmFtZSI6ImRhc2hlZCJ9fX1dLFszLDIsImpfMiJdXQ==
    #align(center, diagram({
      node((0, 0), [$X$])
      node((0, 1), [$ol(X)_1$])
      node((1, 1), [$ol(X)_2$])
      node((1, 0), [$X$])
      edge((0, 1), (1, 1), [$phi$], label-side: right, "->")
      edge((0, 0), (0, 1), [$j_1$], label-side: right, "->")
      edge((0, 0), (1, 0), "=")
      edge((1, 0), (1, 1), [$j_2$], label-side: left, "->")
    }))
    其中水平态射紧合，竖直态射是开浸入。于是由 @open-proper-compat，有典范拟同构 $j_(2,!) cal(K) ->^tilde R phi_* j_(1,!) cal(K)$。与其逆复合，得到拟同构： 
    $
      R ol(f)_(1,*) j_(1,!) cal(K) = R ol(f)_(2,*) R phi_* j_(1,!) cal(K) ->^tilde R ol(f)_(2,*) j_(2,!) cal(K)
    $

  - 第二步。该构造的函子性。 

    记 $R(phi)$ 为由紧化之间的态射 $phi: ol(X)_1 -> ol(X)_2$ 诱导的同构 $R ol(f)_(1,*) j_(1,!) -> R ol(f)_(2,*) j_(2,!)$，这是函子 $D_#[tor] (X_et, Lambda) -> D(Y_et, Lambda)$ 之间的自然同构。假设有紧化之间的一串态射： 
    // https://q.uiver.app/#r=typst&q=WzAsNSxbMCwxLCJYIl0sWzIsMSwiWSJdLFsxLDAsIm9sKFgpXzEiXSxbMSwyLCJvbChYKV8zIl0sWzEsMSwib2woWClfMiJdLFswLDIsImpfMSJdLFswLDMsImpfMyIsMl0sWzIsMSwib2woZilfMSJdLFszLDEsIm9sKGYpXzMiLDJdLFswLDQsImpfMiIsMV0sWzQsMSwib2woZilfMiIsMV0sWzIsNCwicGhpIiwxXSxbNCwzLCJwc2kiLDFdXQ==
    #context align(center, diagram({
      node((0, 1), [$X$])
      node((2, 1), [$Y$])
      node((1, 0), [$ol(X)_1$])
      node((1, 2), [$ol(X)_3$])
      node((1, 1), [$ol(X)_2$])
      edge((0, 1), (1, 0), [$j_1$], label-side: left, "->")
      edge((0, 1), (1, 2), [$j_3$], label-side: right, "->")
      edge((1, 0), (2, 1), [$ol(f)_1$], label-side: left, "->")
      edge((1, 2), (2, 1), [$ol(f)_3$], label-side: right, "->")
      edge((0, 1), (1, 1), [$j_2$], label-side: center, "->")
      edge((1, 1), (2, 1), [$ol(f)_2$], label-side: center, "->")
      edge((1, 0), (1, 1), [$phi$], label-side: center, "->")
      edge((1, 1), (1, 2), [$psi$], label-side: center, "->")
    }, crossing-fill: thm-box-curr-color()))
    则我们断言： 
    $
      R(psi compose phi) = R(psi) compose R(phi): R ol(f)_(1,*) j_(1,!) -> R ol(f)_(3,*) j_(3,!)
    $

    考虑交换图： 
    // https://q.uiver.app/#r=typst&q=WzAsNixbMCwwLCJYIl0sWzAsMSwib2woWClfMSJdLFsxLDEsIm9sKFgpXzIiXSxbMSwwLCJYIl0sWzIsMSwib2woWClfMyJdLFsyLDAsIlgiXSxbMSwyLCJwaGkiLDJdLFswLDEsImpfMSIsMl0sWzAsMywiIiwwLHsic3R5bGUiOnsiYm9keSI6eyJuYW1lIjoiZGFzaGVkIn19fV0sWzMsMiwial8yIl0sWzIsNCwicHNpIiwyXSxbMyw1LCIiLDIseyJzdHlsZSI6eyJib2R5Ijp7Im5hbWUiOiJkYXNoZWQifX19XSxbNSw0LCJqXzMiXV0=
    #align(center, diagram({
      node((0, 0), [$X$])
      node((0, 1), [$ol(X)_1$])
      node((1, 1), [$ol(X)_2$])
      node((1, 0), [$X$])
      node((2, 1), [$ol(X)_3$])
      node((2, 0), [$X$])
      edge((0, 1), (1, 1), [$phi$], label-side: right, "->")
      edge((0, 0), (0, 1), [$j_1$], label-side: right, "->")
      edge((0, 0), (1, 0), "=")
      edge((1, 0), (1, 1), [$j_2$], label-side: left, "->")
      edge((1, 1), (2, 1), [$psi$], label-side: right, "->")
      edge((1, 0), (2, 0), "=")
      edge((2, 0), (2, 1), [$j_3$], label-side: left, "->")
    }))
    其中水平态射紧合，竖直态射是开浸入。 


    由 @open-proper-compat，左、右两个方块与大矩形各自诱导自然同构： 
    $
      q_1: j_(2,!) -> R phi_* j_(1,!): D_#[tor] (X_et, Lambda) -> D(ol(X)_(2,et), Lambda) \

      q_2: j_(3,!) -> R psi_* j_(2,!): D_#[tor] (X_et, Lambda) -> D(ol(X)_(3,et), Lambda) \

      q_3: j_(3,!) -> R psi_* R phi_* j_(1,!): D_#[tor] (X_et, Lambda) -> D(ol(X)_(3,et), Lambda)
    $
    由 @open-proper-compat-naturality，该构造与水平拼接相容。因此： 
    $
      q_3 = R psi_* q_1 compose q_2
    $
    
    按定义，$R(psi) compose R(phi)$ 是这样的复合： 
    $
      R ol(f)_(1,*) j_(1,!) = R ol(f)_(2,*) R phi_* j_(1,!) ->^(R ol(f)_(2,*) q_1^(-1)) R ol(f)_(2,*) j_(2,!) = R ol(f)_(3,*) R psi_* j_(2,!) ->^(R ol(f)_(3,*) q_2^(-1)) -> R ol(f)_(3,*) j_(3,!)
    $
    而 $R ol(f)_(3,*) q_2^(-1) compose R ol(f)_(2,*) q_1^(-1) = R ol(f)_(3,*) (q_2^(-1) compose R psi_* q_1^(-1)) = R ol(f)_(3,*) (R psi_* q_1 compose q_2)^(-1) = R ol(f)_(3,*) q_3^(-1) = R(psi compose phi)$，于是断言得证。 

  - 第三步。一般同构的构造。 

    对任意两个紧化 $ol(X)_1, ol(X)_2$，由 @compactification-filtered，存在第三个紧化 $ol(X)_3$ 以及紧化之间的态射 $phi_i: ol(X)_3 -> ol(X)_i, i=1,2$。我们想把典范同构构造成： 
    $
      R ol(f)_1 j_(1,!) -->^(R(phi_1)^(-1)) R ol(f)_3 j_(3,!) -->^(R(phi_2)) R ol(f)_2 j_(2,!)
    $

    然而 $ol(X)_3$ 与 $phi_(1,2)$ 的选取可能不唯一，所以这个同构目前还不是典范的。给定第四个紧化 $ol(X)_4$ 以及紧化之间的态射 $psi_i: ol(X)_4 -> ol(X)_i, i=1,2$，我们必须证明 $R(phi_1)^(-1) compose R(phi_2) = R(psi_1)^(-1) compose R(psi_2)$。 

    为此，取第五个紧化 $ol(X)_5$ 及态射 $chi'_i: ol(X)_5 -> ol(X)_i, i = 3,4$。这样我们就得到两对紧化之间的态射： 
    $
      phi_1 compose chi'_3, psi_1 compose chi'_4: ol(X)_5 -> ol(X)_1 \

      phi_2 compose chi'_3, psi_2 compose chi'_4: ol(X)_5 -> ol(X)_2
    $
    由 @compactification-filtered，可以取第六个紧化 $ol(X)_6$ 及态射 $chi: ol(X)_6 -> ol(X)_5$，使得： 
    $
      phi_1 compose chi'_3 compose chi = psi_1 compose chi'_4 compose chi: ol(X)_6 -> ol(X)_1 \

      phi_2 compose chi'_3 compose chi = psi_2 compose chi'_4 compose chi: ol(X)_6 -> ol(X)_2
    $
    取 $chi_i = chi'_i compose chi: ol(X)_6 -> ol(X)_i, i = 3,4$，便得到下面这个紧化之间的交换图： 
    // https://q.uiver.app/#r=typst&q=WzAsMTUsWzAsMywib2woWClfMSJdLFsxLDIsIm9sKFgpXzMiXSxbMyw0LCJvbChYKV80Il0sWzQsMywib2woWClfMiJdLFsyLDMsIm9sKFgpXzYiXSxbMywyLCJYIl0sWzIsMSwiWCJdLFsxLDAsIlgiXSxbMCwxLCJYIl0sWzQsMSwiWCJdLFsyLDUsIlkiXSxbMCw1LCJZIl0sWzQsNSwiWSJdLFsxLDQsIlkiXSxbMyw2LCJZIl0sWzEsMCwicGhpXzEiLDFdLFsxLDMsInBoaV8yIiwxXSxbMiwwLCJwc2lfMSIsMV0sWzIsMywicHNpXzIiLDFdLFs0LDEsImNoaV8zIiwxXSxbNCwyLCJjaGlfNCIsMV0sWzgsMCwial8xIiwxLHsibGFiZWxfcG9zaXRpb24iOjMwfV0sWzcsMSwial8zIiwxXSxbNiw0LCJqXzYiLDEseyJsYWJlbF9wb3NpdGlvbiI6MzB9XSxbNSwyLCJqIiwxLHsibGFiZWxfcG9zaXRpb24iOjIwfV0sWzksMywial8yIiwxLHsibGFiZWxfcG9zaXRpb24iOjMwfV0sWzgsNiwiIiwxLHsic3R5bGUiOnsiYm9keSI6eyJuYW1lIjoiZGFzaGVkIn19fV0sWzcsNiwiIiwxLHsic3R5bGUiOnsiYm9keSI6eyJuYW1lIjoiZGFzaGVkIn19fV0sWzYsNSwiIiwxLHsic3R5bGUiOnsiYm9keSI6eyJuYW1lIjoiZGFzaGVkIn19fV0sWzYsOSwiIiwxLHsic3R5bGUiOnsiYm9keSI6eyJuYW1lIjoiZGFzaGVkIn19fV0sWzAsMTEsIm9sKGYpXzEiLDEseyJsYWJlbF9wb3NpdGlvbiI6NzB9XSxbMSwxMywib2woZilfMyIsMSx7ImxhYmVsX3Bvc2l0aW9uIjozMH1dLFs0LDEwLCJvbChmKV82IiwxLHsibGFiZWxfcG9zaXRpb24iOjcwfV0sWzIsMTQsIm9sKGYpXzQiLDEseyJsYWJlbF9wb3NpdGlvbiI6MzB9XSxbMywxMiwib2woZilfMiIsMSx7ImxhYmVsX3Bvc2l0aW9uIjo3MH1dLFsxMywxMCwiIiwxLHsic3R5bGUiOnsiYm9keSI6eyJuYW1lIjoiZGFzaGVkIn19fV0sWzEwLDE0LCIiLDEseyJzdHlsZSI6eyJib2R5Ijp7Im5hbWUiOiJkYXNoZWQifX19XSxbMTEsMTAsIiIsMSx7InN0eWxlIjp7ImJvZHkiOnsibmFtZSI6ImRhc2hlZCJ9fX1dLFsxMCwxMiwiIiwxLHsic3R5bGUiOnsiYm9keSI6eyJuYW1lIjoiZGFzaGVkIn19fV1d
    #context align(center, diagram({
      node((-2, 0), [$ol(X)_1$])
      node((-1, -1), [$ol(X)_3$])
      node((1, 1), [$ol(X)_4$])
      node((2, 0), [$ol(X)_2$])
      node((0, 0), [$ol(X)_6$])
      node((1, -1), [$X$])
      node((0, -2), [$X$])
      node((-1, -3), [$X$])
      node((-2, -2), [$X$])
      node((2, -2), [$X$])
      node((0, 2), [$Y$])
      node((-2, 2), [$Y$])
      node((2, 2), [$Y$])
      node((-1, 1), [$Y$])
      node((1, 3), [$Y$])
      edge((-1, -1), (-2, 0), [$phi_1$], label-side: center, "->")
      edge((-1, -1), (2, 0), [$phi_2$], label-side: center, "->")
      edge((1, 1), (-2, 0), [$psi_1$], label-side: center, "->")
      edge((1, 1), (2, 0), [$psi_2$], label-side: center, "->")
      edge((0, 0), (-1, -1), [$chi_3$], label-side: center, "->")
      edge((0, 0), (1, 1), [$chi_4$], label-side: center, "->")
      edge((-2, -2), (-2, 0), [$j_1$], label-side: center, label-pos: 0.3, "->")
      edge((-1, -3), (-1, -1), [$j_3$], label-side: center, label-pos: 0.7, "->")
      edge((0, -2), (0, 0), [$j_6$], label-side: center, label-pos: 0.3, "->")
      edge((1, -1), (1, 1), [$j_4$], label-side: center, label-pos: 0.7, "->")
      edge((2, -2), (2, 0), [$j_2$], label-side: center, label-pos: 0.3, "->")
      edge((-2, -2), (0, -2), "=")
      edge((-1, -3), (0, -2), "=")
      edge((0, -2), (1, -1), "=")
      edge((0, -2), (2, -2), "=")
      edge((-2, 0), (-2, 2), [$ol(f)_1$], label-side: center, label-pos: 0.7, "->")
      edge((-1, -1), (-1, 1), [$ol(f)_3$], label-side: center, label-pos: 0.3, "->")
      edge((0, 0), (0, 2), [$ol(f)_6$], label-side: center, label-pos: 0.7, "->")
      edge((1, 1), (1, 3), [$ol(f)_4$], label-side: center, label-pos: 0.3, "->")
      edge((2, 0), (2, 2), [$ol(f)_2$], label-side: center, label-pos: 0.7, "->")
      edge((-1, 1), (0, 2), "=")
      edge((0, 2), (1, 3), "=")
      edge((-2, 2), (0, 2), "=")
      edge((0, 2), (2, 2), "=")
    }, crossing-fill: thm-box-curr-color()))
    于是由 $phi_1 compose chi_3 = psi_1 compose chi_4$，有： 
    $
      R(phi_1) compose R(chi_3) = R(psi_1) compose R(chi_4)
    $
    同理： 
    $
      R(phi_2) compose R(chi_3) = R(psi_2) compose R(chi_4)
    $
    因此 $R(phi_1)^(-1) compose R(psi_1) = R(chi_3) compose R(chi_4)^(-1) = R(phi_2)^(-1) compose R(psi_2)$，从而： 
    $
      R(phi_2) compose R(phi_1)^(-1) = R(psi_2) compose R(psi_1)^(-1)
    $
    证毕。 
]

最后，我们证明一条引理：$f$ 紧合时 $R f_*$ 保持挠复形。这样就把 $R f_!$ 这个 $D_#[tor]$ 上的函子构造出来了。 

#lemma(name: <derived-lower-shriek-preserves-torsion>)[
  设 $f: X -> Y$ 是 Noether 概形之间的紧合态射，则 $R f_*$ 把 $D_#[tor] (X_et, Lambda)$ 中的复形送到 $D_#[tor] (Y_et, Lambda)$ 中的复形。 
]
#proof[
  由 @derived-artin-grothendieck-vanishing，$R f_*$ 的上同调维数上下都有界。于是，给定复形 $cal(K) in D_#[tor] (X_et, Lambda)$ 与固定的 $q$，存在某个截断 $sigma_([a,b]) (cal(K)) in D^b_#[tor] (X_et, Lambda)$，使得 $R f_* (sigma_([a,b]) cal(K)) -> R f_* cal(K)$ 在 $h^q$ 上诱导同构。 

  因此只需证明 $R f_*$ 把 $D^b_#[tor]$ 送到 $D_#[tor]$。由截断三角，只需证明 $R f_*$ 把 $cAb_#[tor] (X_et, Lambda)$ 送到 $D_#[tor] (Y_et, Lambda)$。 
  
  记 $T_n (cal(F))$ 为层 $cal(F)$ 的 $n$-挠部分（因为记号 $cal(F)[n]$ 已被复形的平移占用）。对每个挠层 $cal(F) in cAb_#[tor] (X_et, Lambda)$，由 @relative-limit-formula-for-sheaves， 
  $
    R^q f_* cal(F) = R^q f_* (dirlim_n T_n (cal(F))) = dirlim_n R^q f_* (T_n (cal(F)))
  $
  这是一族挠层的正向极限，因此是挠的。于是 $R f_* cal(F)$ 的上同调层都是挠层，从而 $R f_* cal(F)$ 属于 $D_#[tor] (Y_et, Lambda)$。 
]

#definition(name: <defn-derived-pushforward-with-proper-support>)[
  设 $f: X -> Y$ 是 Noether 概形之间分离、有限型的态射。任取一个紧化： 
  $
    X ->^j ol(X) ->^(ol(f)) Y
  $
  定义函子 $R f_!$ 为： 
  $
    R f_!: D_#[tor] (X_et, Lambda) &-> D_#[tor] (Y_et, Lambda) \
    cal(K) &|-> R ol(f)_* j_! cal(K)
  $
  由 @derived-lower-shriek-well-defined 与 @derived-lower-shriek-preserves-torsion，这个函子良定义，且与所选紧化无关。特别地，对 $f$ 的任意紧化 $X ->^j ol(X) ->^(ol(f)) Y$，存在自然同构： 
  $
    R ol(f)_* j_! cong R f_!: D_#[tor] (X_et, Lambda) &-> D_#[tor] (Y_et, Lambda)
  $
  它与 @derived-lower-shriek-well-defined 中的那些同构相容。 

  这个函子称为导出的*紧支推前*。 
]

#definition(name: <defn-cohomology-with-proper-support>)[
  设 $X$ 是 $Spec(k)$ 上分离、有限型的概形，其中 $k$ 是可分闭域。令 $f: X -> Spec(k)$ 为结构态射。定义 $R Gamma_c (X, -)$ 为函子： 
  $
    D_#[tor] (X_et, Lambda) ->^(R f_!) D_#[tor] (Spec(k)_et, Lambda) ->^tilde D_#[tor] (Lambda)
  $

  这个函子称为*紧支上同调*。 
]

#notation(name: <proper-support-cohomology-notation>)[
  对层 $cal(F) in cAb_#[tor] (X_et, Lambda)$： 

  - 给定 Noether 概形之间分离、有限型的态射 $f: X -> Y$，记：#h(1fr)
    $
      R^q f_! cal(F) := h^q (R f_! cal(F)) \
      f_! cal(F) := h^0 (R f_! cal(F))
    $

  - 若 $X$ 是 $Spec(k)$ 上分离、有限型的概形，其中 $k$ 是可分闭域，则记： 
    $
      H^q_c (X, cal(F)) := h^q (R Gamma_c (X, cal(F))) \
      Gamma_c (X, cal(F)) := h^0 (R Gamma_c (X, cal(F)))
    $

  #remark[
    这套记号有几处微妙之处： 

    - 记号 $f_! cal(F) := h^0 (R f_! cal(F))$ 与 @etale-lower-shriek-defn 中函子 $f_!$ 的记号冲突。不过两者是相容的。我们将证明：对 Noether 概形之间分离且平展的态射 $f: X -> Y$，有#h(1fr)
      $
        R f_! = f_!: D_#[tor] (X_et, Lambda) -> D_#[tor] (Y_et, Lambda)
      $
      其中 $R f_!$ 是上面定义的紧支推前，$f_!$ 则按 @etale-lower-shriek-defn 定义。 

    - 尽管 $Gamma_c (X, -)$ 与 $f_!$ 是左正合函子，$R Gamma_c (X, -)$ 与 $R f_!$（以及 $H^q_c (X, -)$ 与 $R^q f_!$）却不是它们的导出函子。 

      因此这里有轻微的记号滥用。这一点请务必记在心里。 
  ]
]
