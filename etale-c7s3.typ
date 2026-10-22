#import "void-import.typ": *
== 投影与 Künneth 公式

本节我们证明投影公式与 Künneth 公式。这两个公式是描述 $R f_!$ 与张量积之间相互作用的关键机制。

作为应用，我们将对可分闭域 $k$ 计算 $PP^n_k$ 的上同调与 $AA^n_k$ 的紧支上同调。

首先要做的是构造投影态射 (projection morphism)。设 $f: X -> Y$ 是 Noether 概形之间有限型的分离态射，且 $cal(K) in D_#[tor] (X_et, Lambda), cal(L) in D_#[tor] (Y_et, Lambda)$。我们希望构造投影态射：
$
  R f_! cal(K) Lotimes_Lambda cal(L) -> R f_! (cal(K) Lotimes_Lambda f^(-1) cal(L))
$
它对 $cal(K)$ 与 $cal(L)$ 自然，与 $f$ 的复合相容，与 $cal(L)$ 中的张量积相容，并与基变换相容。随后我们将证明它是同构。
要建立这些相容性，最好的办法是把投影态射构造为 Beck–Chevalley 基变换。但在构造 $R f_!$ 的投影态射之前，必须先为它的各个组成部分，即 $R f_*$ 与 $j_!$，构造投影态射。

#construction[
  (对 $R f_*$ 的投影) 对一般的概形态射 $f: X -> Y$，我们可以为 $R f_*$ 构造如下形式的投影态射：
  $
    R f_* cal(K) Lotimes_Lambda cal(L) -> R f_* (cal(K) Lotimes_Lambda f^(-1) cal(L))
  $  
  考察所涉及的函子便可看出，它可以构造为下述图表的 Beck–Chevalley 基变换：
  // https://q.uiver.app/#r=typst&q=WzAsNCxbMCwwLCJEKFhfZXQsIExhbWJkYSkiXSxbMCwyLCJEKFhfZXQsIExhbWJkYSkiXSxbMiwwLCJEKFlfZXQsIExhbWJkYSkiXSxbMiwyLCJEKFlfZXQsIExhbWJkYSkiXSxbMCwxLCJSSEhvbV9MYW1iZGEgKGNhbChMKSwgLSkiLDJdLFsyLDMsIlJISG9tX0xhbWJkYSAoZl4oLTEpIGNhbChMKSwgLSkiLDJdLFsxLDMsIlIgZl8qIiwyXSxbMCwyLCJSIGZfKiJdXQ==
  #align(center, diagram({
    node((0, 0), [$D(X_et, Lambda)$])
    node((0, 2), [$D(X_et, Lambda)$])
    node((2, 0), [$D(Y_et, Lambda)$])
    node((2, 2), [$D(Y_et, Lambda)$])
    edge((0, 0), (0, 2), [$RHHom_Lambda (cal(L), -)$], label-side: right, "->")
    edge((2, 0), (2, 2), [$RHHom_Lambda (f^(-1) cal(L), -)$], label-side: left, "->")
    edge((0, 2), (2, 2), [$R f_*$], label-side: right, "->")
    edge((0, 0), (2, 0), [$R f_*$], label-side: left, "->")
    edge(..tune-2-mor-coords((0, 2), (2, 0), l: 0.8), "=>")
  }, spacing: 2.5em))
  其中对角线上的自然变换是同构：
  $
    RHHom_Lambda (cal(L), R f_* (-)) -> R f_* RHHom_Lambda (f^(-1) cal(L), -)
  $
  这由伴随得到，参见 @derived-functoriality-etale (3a)。

  - 注意 $RHHom_Lambda (cal(L), R f_* (-)) -> R f_* RHHom_Lambda (f^(-1) cal(L), -)$ 是复合起来的两个右伴随之间的态射；它诱导出的左伴随之间的态射正是幺半同构：
    $
      f^(-1) (-) Lotimes_Lambda f^(-1) cal(L) -> f^(-1) (- Lotimes_Lambda cal(L))
    $
    由 @bcbc-all-rights，投影态射可这样得到。先取态射 $f^(-1) (R f_* cal(K) Lotimes_Lambda cal(L)) cong f^(-1) R f_* cal(K) Lotimes_Lambda f^(-1) cal(L) -> cal(K) Lotimes_Lambda f^(-1) cal(L)$，再应用伴随，便得到态射 $R f_* cal(K) Lotimes_Lambda cal(L) -> R f_* (cal(K) Lotimes_Lambda f^(-1) cal(L))$。

  下面验证这个映射的各项相容性。

  - 投影态射与 $f$ 的复合相容。设另有概形态射 $g: Y -> Z$。则接连作出的两次投影：
    $
      R g_* R f_* cal(K) Lotimes_Lambda cal(L) -> R g_* (R f_* cal(K) Lotimes_Lambda g^(-1) cal(L)) -> R g_* R f_* (cal(K) Lotimes_Lambda f^(-1) g^(-1) cal(L))
    $
    就是 $g compose f$ 的投影。

    由 @bcbc-horizontal-concat，只需验证伴随同构的复合
    $
      RHHom_Lambda (cal(L), R g_* R f_* (-)) ->^tilde R g_* RHHom_Lambda (g^(-1) cal(L), R f_* (-)) ->^tilde R g_* R f_* RHHom_Lambda (f^(-1) g^(-1) cal(L), -)
    $
    就是 $f^(-1) g^(-1) tack.l R g_* R f_*$ 的伴随同构。为验证这一点，可以应用 $R Gamma(U, -)$ 化归为逐截面检查。这样就能把 $RHHom_Lambda$ 换成 $RHom_Lambda$。又因 $h^q (RHHom_Lambda (-, -)) = Hom_Lambda (-, -[q])$，还可进一步把 $RHom_Lambda$ 换成范畴意义下的 hom $Hom_Lambda$。于是这一相容性不过是关于伴随复合的标准范畴论事实。

  - 投影态射与 $cal(L)$ 中的张量积相容。也就是说，接连的投影：#h(1fr)
    $
      R f_* cal(K) Lotimes_Lambda cal(L)_1 Lotimes_Lambda cal(L)_2 -> R f_* (cal(K) Lotimes_Lambda f^(-1) cal(L)_1) Lotimes_Lambda cal(L)_2 -> R f_* (cal(K) Lotimes_Lambda f^(-1) cal(L)_1 Lotimes_Lambda f^(-1) cal(L)_2)
    $
    就是 $cal(L)_1 Lotimes_Lambda cal(L)_2$ 的投影，这里我们把 $f^(-1) (cal(L)_1 Lotimes_Lambda cal(L)_2) = f^(-1) cal(L)_1 Lotimes_Lambda f^(-1) cal(L)_2$ 等同起来。

    由 @bcbc-vertical-concat，只需验证下图交换：
    #align(center, diagram({
      node((0, 0), $RHHom_Lambda (cal(L)_1, RHHom_Lambda (cal(L)_2, R f_* (-)))$)
      node((0, 1), $RHHom_Lambda (cal(L)_1, R f_* RHHom_Lambda (f^(-1) cal(L)_2, -))$)
      node((0, 2), $R f_* RHHom_Lambda (f^(-1) cal(L)_1, RHHom_Lambda (f^(-1) cal(L)_2, -))$)
      node((2, 0), $RHHom_Lambda (cal(L)_1 Lotimes_Lambda cal(L)_2, R f_* (-))$)
      node((2, 2), $R f_* RHHom_Lambda (f^(-1) cal(L)_1 Lotimes_Lambda f^(-1) cal(L)_2, -)$)
      edge((0, 0), (0, 1), "->")
      edge((0, 1), (0, 2), "->")
      edge((2, 0), (2, 2), "->")
      edge((0, 0), (2, 0), "->")
      edge((0, 2), (2, 2), "->")
    }, spacing: (2em, 3em)))
    应用 $R Gamma$ 化归到 $RHom_Lambda$，再化归到范畴意义下的 hom 之后，我们只需验证下图交换：
    #align(center, diagram({
      node((0, 0), $Hom_Lambda (cal(L)_1, RHHom_Lambda (cal(L)_2, R f_* (-)))$)
      node((0, 1), $Hom_Lambda (cal(L)_1, R f_* RHHom_Lambda (f^(-1) cal(L)_2, -))$)
      node((0, 2), $Hom_Lambda (f^(-1) cal(L)_1, RHHom_Lambda (f^(-1) cal(L)_2, -))$)
      node((2, 0), $Hom_Lambda (cal(L)_1 Lotimes_Lambda cal(L)_2, R f_* (-))$)
      node((2, 2), $Hom_Lambda (f^(-1) cal(L)_1 Lotimes_Lambda f^(-1) cal(L)_2, -)$)
      edge((0, 0), (0, 1), "->")
      edge((0, 1), (0, 2), "->")
      edge((2, 0), (2, 2), "->")
      edge((0, 0), (2, 0), "->")
      edge((0, 2), (2, 2), "->")
    }, spacing: (2em, 3em)))
    然而，这个图表的交换性恰恰就是幺半同构 $f^(-1) (cal(L)_1 Lotimes_Lambda cal(L)_2) cong f^(-1) cal(L)_1 Lotimes_Lambda f^(-1) cal(L)_2$ 的构造。

  - 投影态射与任意基变换相容。也就是说，给定交换图：
    // https://q.uiver.app/#r=typst&q=WzAsNCxbMCwwLCJYJyJdLFswLDEsIlgiXSxbMSwwLCJZJyJdLFsxLDEsIlkiXSxbMSwzLCJmIiwyXSxbMCwyLCJmJyJdLFsyLDMsImciXSxbMCwxLCJnJyIsMl1d
    #align(center, diagram({
      node((0, 0), [$X'$])
      node((0, 1), [$X$])
      node((1, 0), [$Y'$])
      node((1, 1), [$Y$])
      edge((0, 1), (1, 1), [$f$], label-side: right, "->")
      edge((0, 0), (1, 0), [$f'$], label-side: left, "->")
      edge((1, 0), (1, 1), [$g$], label-side: left, "->")
      edge((0, 0), (0, 1), [$g'$], label-side: right, "->")
    }))
    这里 $p = g compose f' = f compose g': X' -> Y$。于是如下复合：
    $
      g^(-1) (R f_* (-) Lotimes_Lambda cal(L)) -->^M g^(-1) R f_* (-) Lotimes_Lambda g^(-1) cal(L) -->^BC R f'_* g'^(-1) (-) Lotimes_Lambda g^(-1) cal(L) -->^P R f'_* (g'^(-1) (-) Lotimes_Lambda p^(-1) cal(L))
    $
    与如下复合相同：
    $
      g^(-1) (R f_* (-) Lotimes_Lambda cal(L)) -->^P g^(-1) R f_* (- Lotimes_Lambda f^(-1) cal(L)) -->^BC R f'_* g'^(-1) (- Lotimes_Lambda f^(-1) cal(L)) -->^M R f'_* (g'^(-1) (-) Lotimes_Lambda p^(-1) cal(L))
    $
    这里 $M$ 表示拉回的幺半同构，$BC$ 表示基变换映射，$P$ 表示投影态射。

    现在逐项验证：

    - 幺半同构 $g^(-1) (- Lotimes_Lambda cal(L)) cong g^(-1) (-) Lotimes_Lambda g^(-1) cal(L)$ 来自下述同构的伴随：
      $
        RHHom_Lambda (cal(L), R g_* (-)) cong R g_* RHHom_Lambda (g^(-1) cal(L), -)
      $
      另一个幺半同构同理。

    - 基变换映射 $g^(-1) R f_* -> R f'_* g'^(-1)$ 是关于 $R f_* R g'_* = R p_* = R g_* R f'_*$ 的 Beck–Chevalley 基变换。

    - 投影态射 $R f_* (-) Lotimes_Lambda cal(L) -> R f_* (- Lotimes_Lambda f^(-1) cal(L))$ 是伴随同构 $RHHom_Lambda (cal(L), R f_* (-)) -> R f_* RHHom_Lambda (f^(-1) cal(L), -)$ 的 Beck–Chevalley 基变换。

    于是只要说明下图中从品红色函子到绿色函子的红色路径与蓝色路径相等，再由 @bcbc-vertical-concat 与 @bcbc-naturality，便得到所要的相容性：
    // https://q.uiver.app/#r=typst&q=WzAsOCxbMCwxLCJEKFknKSJdLFsyLDIsIkQoWScpIl0sWzEsMCwiRChZKSJdLFszLDEsIkQoWSkiXSxbMCw0LCJEKFgnKSJdLFsyLDUsIkQoWCcpIl0sWzEsMywiRChYKSJdLFszLDQsIkQoWCkiXSxbMCwyLCJSIGdfKiIsMV0sWzEsMywiUiBnXyoiLDFdLFs0LDYsIlIgZydfKiIsMV0sWzUsNywiUiBnJ18qIiwxXSxbMiwzLCJSSEhvbV9MYW1iZGEgKGNhbChMKSwgLSkiLDFdLFswLDEsIlJISG9tX0xhbWJkYSAoZ14oLTEpIGNhbChMKSwgLSkiLDFdLFs2LDcsIlJISG9tX0xhbWJkYSAoZl4oLTEpIGNhbChMKSwgLSkiLDFdLFs0LDUsIlJISG9tX0xhbWJkYSAocF4oLTEpIGNhbChMKSwgLSkiLDFdLFs3LDMsIlIgZl8qIiwxXSxbNSwxLCJSIGZfKiIsMSx7ImxhYmVsX3Bvc2l0aW9uIjo4MH1dLFs2LDIsIlIgZidfKiIsMSx7ImxhYmVsX3Bvc2l0aW9uIjoyMH1dLFs0LDAsIlIgZidfKiIsMV1d
    #context align(center, diagram({
      edge(..tune-2-mor-coords((2, 2), (1, 0), l: 0.6), "=>", text(fill: red)[$1$], stroke: red, label-side: center)
      edge(..tune-2-mor-coords((0, 1), (1, 3)), "=>", text(fill: red)[$2$], stroke: red, label-side: center)
      edge(..tune-2-mor-coords((1, 0), (3, 4)), "=>", text(fill: red)[$3$], stroke: red, label-side: center, label-pos: 0.75, bend: 30deg)

      edge(..tune-2-mor-coords((0, 1), (2, 5)), "=>", text(fill: blue)[$1$], stroke: blue, label-side: center, label-pos: 0.25, bend: -30deg)
      edge(..tune-2-mor-coords((2, 2), (3, 4)), "=>", text(fill: blue)[$2$], stroke: blue, label-side: center)
      edge(..tune-2-mor-coords((2, 5), (1, 3), l: 0.6), "=>", text(fill: blue)[$3$], stroke: blue, label-side: center)

      node((0, 1), [$D(Y')$])
      node((2, 2), [$D(Y')$])
      node((1, 0), [$D(Y)$])
      node((3, 1), [$D(Y)$])
      node((0, 4), [$D(X')$])
      node((2, 5), [$D(X')$])
      node((1, 3), [$D(X)$])
      node((3, 4), [$D(X)$])
      edge((3, 4), (3, 1), text(fill: green)[$R f_*$], label-side: center, "->", stroke: green)
      edge((2, 5), (2, 2), [$R f_*$], label-side: center, label-pos: 0.8, "->")
      edge((1, 3), (1, 0), [$R f'_*$], label-side: center, label-pos: 0.2, "->")
      edge((0, 4), (0, 1), text(fill: fuchsia)[$R f'_*$], label-side: center, "->", stroke: fuchsia)
      edge((0, 1), (1, 0), [$R g_*$], label-side: center, "->")
      edge((2, 2), (3, 1), text(fill: fuchsia)[$R g_*$], label-side: center, "->", stroke: fuchsia)
      edge((0, 4), (1, 3), text(fill: green)[$R g'_*$], label-side: center, "->", stroke: green)
      edge((2, 5), (3, 4), [$R g'_*$], label-side: center, "->")
      edge((1, 0), (3, 1), [$RHHom_Lambda (cal(L), -)$], label-side: center, "->")
      edge((0, 1), (2, 2), text(fill: fuchsia)[$RHHom_Lambda (g^(-1) cal(L), -)$], label-side: center, "->", label-pos: 0.7, stroke: fuchsia)
      edge((1, 3), (3, 4), text(fill: green)[$RHHom_Lambda (f^(-1) cal(L), -)$], label-side: center, "->", label-pos: 0.3, stroke: green)
      edge((0, 4), (2, 5), [$RHHom_Lambda (p^(-1) cal(L), -)$], label-side: center, "->")
    }, crossing-fill: thm-box-curr-color(), label-size: 0.8em, spacing: (2.5em, 1.6em)))
    这一等式不过是复合伴随的相容性。（这里我们把 $D_#[tor] (X_et, Lambda)$ 简记为 $D(X)$。）

  至此我们为 $R f_*$ 构造出了满足各项要求的投影态射。
]

#construction[
  (对 $f_!$ 的投影) 对平展态射 $f: X -> Y$，我们希望构造投影态射：
  $
    f_! cal(K) Lotimes_Lambda cal(L) -> f_! (cal(K) Lotimes_Lambda f^(-1) cal(L)) 
  $
  它与基变换相容。这个投影同构定义在 @derived-functoriality-etale (4b) 中，即下述同构的伴随：
  $
    RHHom_Lambda (f^(-1) (-), f^(-1) cal(L)) -->^tilde f^(-1) RHHom_Lambda (-, cal(L))
  $

  - 投影与 $f$ 的复合相容。事实上，给定另一个平展态射 $g: Y -> Z$，要说明投影的复合：#h(1fr)
    $
      g_! f_! cal(K) Lotimes_Lambda cal(L) -> g_! (f_! cal(K) Lotimes_Lambda g^(-1) cal(L)) -> g_! f_! (cal(L) Lotimes_Lambda f^(-1) g^(-1) cal(L))
    $
    就是沿 $g compose f$ 的投影，由伴随只需说明复合：
    $
      RHHom_Lambda (g^(-1) f^(-1) (-), g^(-1) f^(-1) cal(L)) -> g^(-1) RHHom_Lambda (f^(-1) (-), f^(-1) cal(L)) -> g^(-1) f^(-1) RHHom_Lambda (-, cal(L))
    $
    就是 $g compose f$ 的同一个同构。但这是自动的。

  - 投影与任意基变换相容。假设有交换图：
    // https://q.uiver.app/#r=typst&q=WzAsNCxbMCwwLCJYJyJdLFswLDEsIlgiXSxbMSwwLCJZJyJdLFsxLDEsIlkiXSxbMSwzLCJmIiwyXSxbMCwyLCJmJyJdLFsyLDMsImciXSxbMCwxLCJnJyIsMl1d
    #align(center, diagram({
      node((0, 0), [$X'$])
      node((0, 1), [$X$])
      node((1, 0), [$Y'$])
      node((1, 1), [$Y$])
      edge((0, 1), (1, 1), [$f$], label-side: right, "->")
      edge((0, 0), (1, 0), [$f'$], label-side: left, "->")
      edge((1, 0), (1, 1), [$g$], label-side: left, "->")
      edge((0, 0), (0, 1), [$g'$], label-side: right, "->")
      node((0.3, 0.3), $cart$)
    }))
    其中 $p = g compose f' = f compose g': X' -> Y$，则复合：
    $
      g^(-1) (f_! (-) Lotimes_Lambda cal(L)) -->^M g^(-1) f_! (-) Lotimes_Lambda g^(-1) cal(L) -->^(BC_!) f'_! g'^(-1) (-) Lotimes_Lambda g^(-1) cal(L) -->^P f'_! (g'^(-1) (-) Lotimes_Lambda p^(-1) cal(L))
    $
    与如下复合相同：
    $
      g^(-1) (f_! (-) Lotimes_Lambda cal(L)) -->^P g^(-1) f_! (- Lotimes_Lambda f^(-1) cal(L)) -->^(BC_!) f'_! g'^(-1) (- Lotimes_Lambda f^(-1) cal(L)) -->^M f'_! (g'^(-1) (-) Lotimes_Lambda p^(-1) cal(L))
    $
    其中 $P$ 是投影态射，$M$ 是幺半同构，$BC_!$ 是 @etale-lower-shriek-first-props (4) 中的同构。

    事实上，转到右伴随之后，只需说明下图交换：

    // https://q.uiver.app/#r=typst&q=WzAsOCxbMCwwLCJSIGcnXyogUkhIb21fTGFtYmRhIChwXigtMSkgY2FsKEwpLCAtKSJdLFsyLDAsIlIgZydfKiBSSEhvbV9MYW1iZGEgKHBeKC0xKSBjYWwoTCksIC0pIl0sWzAsMSwiUiBnJ18qIGYnXigtMSkgUkhIb21fTGFtYmRhIChnXigtMSkgY2FsKEwpLCAtKSJdLFswLDIsImZeKC0xKSBSIGdfKiBSSEhvbV9MYW1iZGEgKGdeKC0xKSBjYWwoTCksIC0pIl0sWzAsMywiZl4oLTEpIFJISG9tX0xhbWJkYSAoY2FsKEwpLCBSIGdfKiAoLSkpIl0sWzIsMSwiUkhIb21fTGFtYmRhIChmXigtMSkgY2FsKEwpLCBSIGcnXyogZideKC0xKSAoLSkpIl0sWzIsMiwiUkhIb21fTGFtYmRhIChmXigtMSkgY2FsKEwpLCBmXigtMSkgUiBnXyogKC0pKSJdLFsyLDMsImZeKC0xKSBSSEhvbV9MYW1iZGEgKGNhbChMKSwgUiBnXyogKC0pKSJdLFswLDEsIiIsMCx7InN0eWxlIjp7ImJvZHkiOnsibmFtZSI6ImRvdWJsZSBiYXJyZWQifX19XSxbMCwyXSxbMiwzXSxbMyw0XSxbMSw1XSxbNSw2XSxbNiw3XSxbNCw3LCIiLDIseyJzdHlsZSI6eyJib2R5Ijp7Im5hbWUiOiJkb3VibGUgYmFycmVkIn19fV1d
    #context align(center, diagram({
      node((0, 0), [$R g'_* RHHom_Lambda (p^(-1) cal(L), -)$])
      node((2, 0), [$R g'_* RHHom_Lambda (p^(-1) cal(L), -)$])
      node((0, 1), [$R g'_* f'^(-1) RHHom_Lambda (g^(-1) cal(L), -)$])
      node((0, 2), [$f^(-1) R g_* RHHom_Lambda (g^(-1) cal(L), -)$])
      node((0, 3), [$f^(-1) RHHom_Lambda (cal(L), R g_* (-))$])
      node((2, 1), [$RHHom_Lambda (f^(-1) cal(L), R g'_* f'^(-1) (-))$])
      node((2, 2), [$RHHom_Lambda (f^(-1) cal(L), f^(-1) R g_* (-))$])
      node((2, 3), [$f^(-1) RHHom_Lambda (cal(L), R g_* (-))$])
      edge((0, 0), (2, 0), "=")
      edge((0, 0), (0, 1), "->")
      edge((0, 1), (0, 2), "->")
      edge((0, 2), (0, 3), "->")
      edge((2, 0), (2, 1), "->")
      edge((2, 1), (2, 2), "->")
      edge((2, 2), (2, 3), "->")
      edge((0, 3), (2, 3), "=")
    }, crossing-fill: thm-box-curr-color()))
    要证该交换性，只需先对 $U in Et_X$ 应用 $R Gamma(U, -)$，再作验证。进一步不妨设 $U = X$。这是因为：对一般的 $U$ 把 $R Gamma(U, -)$ 作用于上图，所得结果与把起点从 $X -> Y$ 换成 $U -> Y$ 后再取整体截面所得的结果相同。再把 $cal(L)$ 换成 K-平坦复形、把 $(-)$ 中的复形换成 K-内射复形，便可用 @hhom-from-kflat-to-kinj-is-kinj 去掉导出函子中所有的 $R$。
    
    当 $U = X$，即取整体截面时，诸如 $f^(-1) RHHom_Lambda (-, -) cong RHHom_Lambda (f^(-1) (-), f^(-1) (-))$ 的态射都变成恒等。此时右路径变为：
    $
      Hom_Lambda (p^(-1) cal(L), f'^(-1) (-)) -> Hom_Lambda (f^(-1) cal(L), g'_* f'^(-1) (-)) -> Hom_Lambda (f^(-1) cal(L), f^(-1) g_* (-))
    $
    而左路径变为：
    $
      Hom_Lambda (p^(-1) cal(L), f'^(-1) (-)) = Gamma(X', HHom_Lambda (g^(-1) cal(L), -)) = Gamma(X, HHom_Lambda (cal(L), g_* (-))) = Hom_Lambda (f^(-1) cal(L), f^(-1) g_* (-))
    $
    直接验证即可看出这两条路径相等。

  - 投影与 $cal(L)$ 中的张量积相容。为说明投影的复合：
    $
      f_! cal(K) Lotimes_Lambda cal(L)_1 Lotimes_Lambda cal(L)_2 -> f_! (cal(K) Lotimes_Lambda f^(-1) cal(L)_1) Lotimes_Lambda cal(L)_2 -> f_! (cal(K) Lotimes_Lambda f^(-1) cal(L)_1 Lotimes_Lambda f^(-1) cal(L)_2) ->^M f_! (cal(K) Lotimes_Lambda f^(-1) (cal(L)_1 Lotimes_Lambda cal(L)_2))
    $
    就是 $cal(L)_1 Lotimes_Lambda cal(L)_2$ 的投影（其中 $M$ 是幺半同构）。
    
    本可以硬算：比较两边（看作 $cal(K)$ 的函子）的伴随。但我们打算偷懒，只在茎上验证，因为投影态射与任意基变换相容。于是不妨设 $f$ 形如 $union.sq.big_(i in I) Spec(Omega) -> Spec(Omega)$，其中 $Omega$ 是可分闭域，这时一切都只是 $Lambda$-模复形。这种情形下相容性可以直接验证。
    /*, by unfolding the definition of the monoidal isomorphism, it suffices to show that the composition: 
    $
      RHHom_Lambda (f^(-1) (cal(L)_1 Lotimes_Lambda cal(L)_2), f^(-1) (-)) -> f^(-1) RHHom_Lambda (cal(L)_1 Lotimes_Lambda cal(L)_2, R f_* f^(-1) (-)) -> 
    $*/
    #remark[
      作为这一相容性的推论，取伴随便可看出幺半同构 $f^(-1) (cal(L)_1 Lotimes_Lambda cal(L)_2) cong f^(-1) cal(L)_1 Lotimes_Lambda f^(-1) cal(L)_2$ 落在如下交换图中：
      // https://q.uiver.app/#r=typst&q=WzAsNixbMCwwLCJSSEhvbV9MYW1iZGEgKGZeKC0xKSBjYWwoTClfMSBMb3RpbWVzX0xhbWJkYSBmXigtMSkgY2FsKEwpXzIsIGZeKC0xKSAoLSkpIl0sWzEsMCwiUkhIb21fTGFtYmRhIChmXigtMSkgY2FsKEwpXzEsIFJISG9tX0xhbWJkYShmXigtMSkgY2FsKEwpXzIsIGZeKC0xKSAoLSkpKSJdLFsxLDEsIlJISG9tX0xhbWJkYSAoZl4oLTEpIGNhbChMKV8xLCBmXigtMSkgUkhIb21fTGFtYmRhKGNhbChMKV8yLCAtKSkiXSxbMSwyLCJmXigtMSkgUkhIb21fTGFtYmRhIChjYWwoTClfMSwgUkhIb21fTGFtYmRhKGNhbChMKV8yLCAtKSkiXSxbMCwyLCJmXigtMSkgUkhIb21fTGFtYmRhIChjYWwoTClfMSBMb3RpbWVzX0xhbWJkYSBjYWwoTClfMiwgLSkiXSxbMCwxLCJSSEhvbV9MYW1iZGEgKGZeKC0xKSAoY2FsKEwpXzEgTG90aW1lc19MYW1iZGEgY2FsKEwpXzIpLCBmXigtMSkgKC0pKSJdLFswLDFdLFsxLDJdLFsyLDNdLFszLDRdLFswLDUsInRpbGRlIiwyXSxbNSw0XV0=
      #align(center, diagram({
        node((0, 0), [$RHHom_Lambda (f^(-1) cal(L)_1 Lotimes_Lambda f^(-1) cal(L)_2, f^(-1) (-))$])
        node((1, 0), [$RHHom_Lambda (f^(-1) cal(L)_1, RHHom_Lambda(f^(-1) cal(L)_2, f^(-1) (-)))$])
        node((1, 1), [$RHHom_Lambda (f^(-1) cal(L)_1, f^(-1) RHHom_Lambda(cal(L)_2, -))$])
        node((1, 2), [$f^(-1) RHHom_Lambda (cal(L)_1, RHHom_Lambda(cal(L)_2, -))$])
        node((0, 2), [$f^(-1) RHHom_Lambda (cal(L)_1 Lotimes_Lambda cal(L)_2, -)$])
        node((0, 1), [$RHHom_Lambda (f^(-1) (cal(L)_1 Lotimes_Lambda cal(L)_2), f^(-1) (-))$])
        edge((0, 0), (1, 0), "->")
        edge((1, 0), (1, 1), "->")
        edge((1, 1), (1, 2), "->")
        edge((1, 2), (0, 2), "->")
        edge((0, 0), (0, 1), [$tilde$], label-side: right, "->")
        edge((0, 1), (0, 2), "->")
      }))
      若不在茎上偷懒，我们就得手动证明这一点。不过多半也不难。
    ]
]

现在可以把 $R f_*$ 与 $f_!$ 的投影态射结合起来，定义 $R f_!$ 的投影态射了。

#proposition[
  设 $f: X -> Y$ 是 Noether 概形之间有限型的分离态射。则存在自然的投影态射：
  $
    R f_! cal(K) Lotimes_Lambda cal(L) -> R f_! (cal(K) Lotimes_Lambda f^(-1) cal(L))
  $
  其中 $cal(K) in D_#[tor] (X_et), cal(L) in D_#[tor] (Y_et)$；它与 $f$ 的复合、$cal(L)$ 中的张量积以及任意基变换都相容。
]
#proof[
  取 $f$ 的一个紧化 $X ->^j ol(X) ->^(ol(f)) Y$。下面定义投影态射：
  $
    R f_! cal(K) Lotimes_Lambda cal(L) cong R ol(f)_* j_! cal(K) Lotimes_Lambda cal(L) -> R ol(f)_* (j_! cal(K) Lotimes_Lambda ol(f)^(-1) cal(L)) -> R ol(f)_* j_! (cal(K) Lotimes_Lambda j^(-1) ol(f)^(-1) cal(L)) cong R f_! (cal(K) Lotimes_Lambda f^(-1) cal(L))
  $
  其中第一步是 $R ol(f)_*$ 的投影，第二步是 $j_!$ 的投影。

  其良定义性由下面的引理给出。与 $cal(L)$ 中张量积的相容性、与任意基变换的相容性，分别来自 $R ol(f)_*$ 的投影与 $j_!$ 的投影各自的相应性质。与 $f$ 复合的相容性则来自 $R ol(f)_*$ 的投影与 $j_!$ 的投影各自的相应性质，以及下面的引理。

  #lemma[
    给定 Noether 概形的交换图：
    // https://q.uiver.app/#r=typst&q=WzAsNCxbMCwwLCJYXzEiXSxbMCwxLCJYXzIiXSxbMSwxLCJZXzIiXSxbMSwwLCJZXzEiXSxbMCwzLCJmXzEiXSxbMSwyLCJmXzIiLDJdLFswLDEsImpfWCIsMl0sWzMsMiwial9ZIl1d
    #context align(center, diagram({
      node((-1, 0), [$X_1$])
      node((-1, 1), [$X_2$])
      node((0, 1), [$Y_2$])
      node((0, 0), [$Y_1$])
      edge((-1, 0), (0, 0), [$f_1$], label-side: left, "->")
      edge((-1, 1), (0, 1), [$f_2$], label-side: right, "->")
      edge((-1, 0), (-1, 1), [$j_X$], label-side: right, "->")
      edge((0, 0), (0, 1), [$j_Y$], label-side: left, "->")
      edge((-1, 0), (0, 1), $p$, label-side: center, "->")
    }, crossing-fill: thm-box-curr-color()))
    其中水平态射紧合、竖直态射是开浸入。把 @open-proper-compat 中的同构 $j_(Y,!) R f_(1,*) -> R f_(2,*) j_(X,!)$ 记为 $T$。则复合：
    $
      j_(Y,!) R f_(1,*) (-) Lotimes_Lambda cal(L) -->^T R f_(2,*) j_(X,!) (-) Lotimes_Lambda cal(L) -->^P R f_(2,*) (j_(X,!) (-) Lotimes_Lambda f_2^(-1) cal(L)) -->^(P_!) R f_(2,*) j_(X,!) (- Lotimes_Lambda p^(-1) cal(L))
    $
    等于如下复合：
    $
      j_(Y,!) R f_(1,*) (-) Lotimes_Lambda cal(L) -->^(P_!) j_(Y,!) (R f_(1,*) (-) Lotimes_Lambda j_Y^(-1) cal(L)) -->^P j_(Y,!) R f_(1,*) (- Lotimes_Lambda p^(-1) cal(L)) -->^T R f_(2,*) j_(X,!) (- Lotimes_Lambda p^(-1) cal(L))
    $
    其中 $P$ 表示 $R f_(1,*)$ 或 $R f_(2,*)$ 的投影，$P_!$ 表示 $j_(X,!)$ 或 $j_(Y,!)$ 的投影。
  ]
  #proof[
    本可以硬算：逐一检查定义这些态射所用的各个 Beck–Chevalley 基变换中的自然变换。

    换个办法：由 @open-proper-compat-with-bc 以及我们对投影 $P$、$P_!$ 的构造，这里所有自然变换都与基变换相容。又由紧合基变换、@etale-lower-shriek-first-props (4) 以及拉回的幺半同构，各相容性中出现的基变换映射都是同构。因此只需检查茎，即把整张概形图表沿 $Y_2$ 的几何点作基变换后证明本引理。

    若沿 $Y_2$ 中不在 $Y_1$ 里的几何点作基变换，$j_(Y,!)$ 变成零，两条路径都是零。于是不妨设沿 $Y_1$ 中的几何点 $ol(y) = Spec(k) -> Y_2$ 作基变换，其中 $k$ 是代数闭域。此时在该基变换下 $j_Y$ 变成恒等态射 $Spec(k) -> Spec(k)$，交换图化为：
    // https://q.uiver.app/#r=typst&q=WzAsMyxbMCwwLCJYXzEiXSxbMCwyLCJYXzIiXSxbMiwxLCJTcGVjKGspIl0sWzAsMSwiaiIsMl0sWzAsMiwiZl8xIl0sWzEsMiwiZl8yIiwyXV0=
    #align(center, diagram({
      node((0, 0), [$X_1$])
      node((0, 2), [$X_2$])
      node((2, 1), [$Spec(k)$])
      edge((0, 0), (0, 2), [$j$], label-side: right, "->")
      edge((0, 0), (2, 1), [$f_1$], label-side: left, "->")
      edge((0, 2), (2, 1), [$f_2$], label-side: right, "->")
    }, spacing: 1.5em))
    其中 $f_1, f_2$ 紧合，$j$ 是开浸入。于是 $j$ 是紧合的开浸入，从而是开闭浸入。 //于是可以写成 $X_2 = X_1 union.sq X_3$，其中 $f_3: X_3 -> Spec(k) $ 是另一个紧合 $k$-概形。
    
    此时可以把 $j_! cong R j_*$ 等同起来。

    - 在这个等同下，自然变换 $T: R f_(1,*) -> R f_(2,*) j_!$ 就是复合 $R f_(1,*) cong R f_(2,*) R j_*$。事实上：
    
      - 按定义，$T$ 是基变换 $R f_(2,*) j_! -> R f_(1,*) j^(-1) j_! cong R f_(1,*)$ 的逆。
      
      - $R f_(1,*) cong R f_(2,*) R j_*$ 是基变换 $R f_(2,*) R j_* -> R f_(1,*) j^(-1) R j_* cong R f_(1,*)$ 的逆。这正是基变换与方块横向拼接的相容性。

      - 等同 $j_! cong R j_*$ 与等同 $j^(-1) j_! cong id cong j^(-1) R j_*$ 相容。

    - 在这个等同下，$j_!$ 的投影变成 $R j_*$ 的投影。事实上，应用 $j^(-1)$ 与幺半同构之后，
      $
        P: R j_* (-) Lotimes_Lambda cal(L) -> R j_* (- Lotimes_Lambda j^(-1) cal(L))
      $
      变成余单位 $j^(-1) R j_* (-) Lotimes_Lambda j^(-1) cal(L) -> - Lotimes_Lambda j^(-1) cal(L)$。再把 $j^(-1) R j_*$ 与恒等函子等同起来，它就变成恒等。

      另一方面，应用 $j^(-1)$ 与幺半同构之后，
      $
        P_!: j_! (-) Lotimes_Lambda cal(L) -> j_! (- Lotimes_Lambda j^(-1) cal(L))
      $
      由 $P_!$ 与基变换的相容性，它也变成 $- Lotimes_Lambda j^(-1) cal(L)$ 上的恒等。这样就验证了该断言。

    有了这两个断言，所要的等式就归结为 $R f_*$ 的投影与复合的相容性。
  ]
]

投影态射既已定义，现在就可以证明投影公式了。

#theorem(name: <projection-formula>)[
  (投影公式) 设 $f: X -> Y$ 是 Noether 概形之间有限型的分离态射，则自然的投影态射：
  $
    R f_! cal(K) Lotimes_Lambda cal(L) -> R f_! (cal(K) Lotimes_Lambda f^(-1) cal(L))
  $
  对 $cal(K) in D_#[tor] (X_et), cal(L) in D_#[tor] (Y_et)$ 是拟同构。
]
#proof[
  取 $f$ 的一个紧化 $X ->^j ol(X) ->^(ol(f)) Y$。则 $R f_!$ 的投影不过是将 $R ol(f)_*$ 的投影与 $j_!$ 的投影接起来。$j_!$ 的投影已经是同构，所以只需证明 $R ol(f)_*$ 那一部分。于是可以把 $f$ 换成 $ol(f)$，假定 $f$ 紧合。我们要证明投影：
  $
    R f_* cal(K) Lotimes_Lambda cal(L) -> R f_* (cal(K) Lotimes_Lambda f^(-1) cal(L))
  $
  是拟同构。由紧合基变换以及投影与基变换的相容性，这等价于对 $Y$ 的每个几何点 $ol(y)$ 证明投影：
  $
    R Gamma(X_(ol(y)), cal(K)|_(X_(ol(y)))) Lotimes_Lambda cal(L)_(ol(y)) -> R Gamma(X_(ol(y)), cal(K)|_(X_(ol(y))) Lotimes_Lambda ul(cal(L)_(ol(y))))
  $
  是拟同构。这由下面的引理得到：
  #lemma(name: <projection-formula-for-global-sections>)[
    (整体截面的投影公式) 设 $X$ 是可分闭域 $k$ 上的有限型概形。则对任意 $cal(K) in D(X_et, Lambda), M in D (Lambda)$，投影态射：
    $
      R Gamma(X, cal(K)) Lotimes_Lambda M -> R Gamma(X, cal(K) Lotimes_Lambda ul(M))
    $
    是拟同构。
  ]
  #proof[
    单靠 way-out 引理不足以把这个命题化归到简单情形，我们需要更强的化归手段：

    #lemma(name: <cpct-generator-of-d-lambda>)[
      设 $Lambda$ 是环，$T$ 是 $D(Lambda)$ 中对象的一个性质。若满足以下条件，则该性质对 $D(Lambda)$ 的每个对象都成立：

      #set enum(numbering: "(a)")
      + 给定一族复形 $M_i in D(Lambda)$，若对一切 $i$ 都有 $T(M_i)$ 成立，则 $T(oplus.big_i M_i)$ 成立。

      + 给定 $D(Lambda)$ 中的特殊三角 $K -> L -> M ->^(+1)$，若 $T(K), T(L), T(M)$ 中有两个成立，则第三个也成立。

      + 对一切 $k in ZZ$，$T(Lambda[k])$ 成立。
    ]
    #proof[
      这或者正是 #cite-stacks("09PB")[Remark 15.60.11]，或者来自把 @cpct-generation-of-triangulated-cat 应用于 $D(Lambda)$ 与生成对象族 ${Lambda[k]}_(k in ZZ)$。
    ]

    设 $T$ 是 $D(Lambda)$ 上的一条性质，$T(M)$ 表示如下陈述：

    - 对一切 $cal(K) in D(X_et, Lambda)$，投影态射：#h(1fr)
      $
        R Gamma(X, cal(K)) Lotimes_Lambda M -> R Gamma(X, cal(K) Lotimes_Lambda ul(M))
      $
      是拟同构。

    下面逐项验证：

    - 两边作为 $M$ 的函子都是三角函子，故由导出五引理，$T(M)$ 在平移下保持；并且若在特殊三角 $K -> L -> M ->^(+1)$ 中 $T(K), T(L)$ 成立，则 $T(M)$ 成立。

    - 对任意直和，需要用一个极限公式：

      #proposition(name: <derived-bounded-limit-formula-for-direct-sum>)[
        设 $X$ 是拟紧拟分离概形，使得 $R Gamma(X, -)$ 上有界。则对任意 $cal(K)_i in D (X_et, Lambda)$，典范映射：
        $
          oplus.big_i R Gamma(X, cal(K)_i) -> R Gamma(X, oplus.big_i cal(K)_i)
        $
        是拟同构。
      ]
      #proof[
        考虑截断 $tau_([a,b]) (cal(K)_i)$。则：
        $
          tau_([a,b]) (oplus.big_i cal(K)_i) = oplus.big_i tau_([a,b]) cal(K)_i
        $
        设 $R Gamma(X, -)$ 的上同调维数 $=d$。于是利用截断三角，典范映射：
        $
          h^q (R Gamma(X, tau_([q-d,q+1]) cal(K))) -> h^q (R Gamma(X, cal(K)))
        $
        是同构。因此为证明所要的同构，可以对每个次数分别论证，并把所有复形截断，从而不妨设每个 $cal(K)_i$ 的支集落在 $[a,b]$ 中。现在把每个 $cal(K)_i$ 换成支集落在 $[a,+oo)$ 中的内射消解 $cal(I)_i$，并注意对每个 $p$ 及一切 $q>=1$：
        $
          H^q (X, oplus.big_i cal(I)_i^p) = oplus.big_i H^q (X, cal(I)_i^p) = 0
        $
        于是 $oplus.big_i cal(K)_i$ 拟同构于由 $Gamma(X,-)$-零调层构成的下有界复形 $oplus.big_i cal(I)_i$。这个零调消解因此可用来计算 $R Gamma(X, -)$，得到：
        $
          R Gamma(X, oplus.big_i cal(K)_i) = oplus.big_i R Gamma(X, cal(K)_i)
        $
      ]
      上述命题之所以适用，是因为 $X$ 是可分闭域 $k$ 上的有限型概形，故由 Grothendieck 消没，$R Gamma(X, -)$ 上有界。又 $Lotimes_Lambda$ 是左伴随，因而与所有直和交换。于是：
      $
        R Gamma(X, cal(K)) Lotimes_Lambda (oplus.big_i M_i) = oplus.big_i (R Gamma(X, cal(K)) Lotimes_Lambda M_i)
      $
      而：
      $
        R Gamma(X, cal(K) Lotimes_Lambda ul(oplus.big_i M_i)) &= R Gamma(X, cal(K) Lotimes_Lambda (oplus.big_i ul(M_i))) \
        &= R Gamma(X, oplus.big_i (cal(K) Lotimes_Lambda ul(M_i))) \
        &= oplus.big_i R Gamma(X, cal(K) Lotimes_Lambda ul(M_i))
      $
      因此，若对一切 $i$ 有 $T(M_i)$，则 $T(oplus.big_i M_i)$ 成立。

    - 最后，对一切 $k$ 都有 $T(Lambda[k])$ 成立。事实上 $T$ 在平移下保持，故只需证明 $T(Lambda)$。但：
      $
        R Gamma(X, cal(K) Lotimes_Lambda ul(Lambda)) = R Gamma(X, cal(K)) = R Gamma(X, cal(K)) Lotimes_Lambda Lambda
      $

    由上述引理，对一切 $M in D(Lambda)$ 都有 $T(M)$ 成立。这样就完成了整体截面投影公式的证明。
    /*
    Since $Lambda$ has finite global dimension, $- Lotimes_Lambda M$ and $- Lotimes_Lambda ul(M)$ are both bounded above/below functors if $M$ is a bounded above/below complex. Further, since $X$ is finite type over an algebraically closed field $k$, $R Gamma$ is bounded. 
    
    Thus, in each of the four cases, the way-out lemma is applicable, and we may reduce to the case that $cal(K)$ is a single sheaf $cal(F) in cAb(X_et)$. 
    
    Next, having fixed $cal(K) = cal(F) in cAb(X_et, Lambda)$, both sides are bounded in $M$. By way-out lemma, we may further assume that $M = N in AMod(Lambda)$ is a $Lambda$-module. Since $Lambda$ has finite global dimension, we may find a bounded projective resolution of $M$, say $0 -> P^bullet -> M$. Now: 
    $
      R Gamma(X, cal(K)) Lotimes_Lambda M = R Gamma(X, cal(F)) otimes_Lambda P \
      R Gamma(X, cal(K) Lotimes_Lambda ul(M)) = R Gamma(X, cal(F) otimes_Lambda ul(P))
    $
    Taking an injective resolution $0 -> cal(F) -> cal(I)^bullet$, and considering the double complex: 
    $
      Gamma(X, cal(I)^bullet) otimes_Lambda P^*
    $
    we get a canonical spectral sequence that is horizontally bounded: 
    $
      E_1^(p,q) = H^q (X, cal(F)) otimes_Lambda P^p => h^(p+q) (R Gamma(X, cal(F)) otimes_Lambda P)
    $
    On the other hand, the hypercohomology spectral sequence gives another canonical horizontally bounded spectral sequence: 
    $
      tilde(E)_1^(p,q) = H^q (X, cal(F) otimes_Lambda ul(P^p)) => h^(p+q) (R Gamma(X, cal(F) otimes_Lambda ul(P)))
    $
      The projection maps give a morphism $E_1^(p,q) -> tilde(E)_1^(p,q)$ of spectral sequences. Thus, to show that $R Gamma(X, cal(F)) otimes_Lambda P -> R Gamma(X, cal(F) otimes_Lambda ul(P))$ is a quasi-isomorphism, it suffices to show that each $E_1^(p,q) -> tilde(E)_1^(p,q)$ is an isomorphism, i.e. given a projective $Lambda$-module $Q$ and any $cal(F) in cAb(X_et, Lambda)$, we have: 
    $
      H^q (X, cal(F) otimes_Lambda ul(Q)) cong H^q (X, cal(F)) otimes_Lambda Q
    $
    By Lazard's theorem (#cite-stacks("058G")[Theorem 10.81.4]), $Q = dirlim_lambda Q_lambda$ is a direct limit of finite free $Lambda$-modules $Q_lambda$'s. Since tensor product commutes with colimits as a left adjoint, by the limit formula @limit-formula-for-sheaves, it suffices to prove for each $Q_lambda$: 
    $
      H^q (X, cal(F) otimes_Lambda ul(Q_lambda)) cong H^q (X, cal(F)) otimes_Lambda Q_lambda
    $
    But each $Q_lambda cong Lambda^(oplus m_lambda)$ is a direct sum of $m_lambda$ copies of $Lambda$, so both sides are direct sums of $m_lambda$ copies of $H^q (X, cal(F))$. */
  ]
]

接下来，我们从投影公式推出 Künneth 公式。

#theorem(name: <kunneth-formula>)[
  (Künneth 公式) 给定 Noether 概形的拉回图表：
  // https://q.uiver.app/#r=typst&q=WzAsNCxbMCwwLCJYIl0sWzAsMSwiWF8xIl0sWzEsMCwiWF8yIl0sWzEsMSwiWSJdLFswLDEsInBfMSIsMl0sWzAsMiwicF8yIl0sWzEsMywiZl8xIiwyXSxbMiwzLCJmXzIiXSxbMCwzLCJmIiwxXV0=
  #context align(center, diagram({
    node((0, 0), [$X$])
    node((0, 1), [$X_2$])
    node((1, 0), [$X_1$])
    node((1, 1), [$Y$])
    edge((0, 0), (0, 1), [$p_2$], label-side: right, "->")
    edge((0, 0), (1, 0), [$p_1$], label-side: left, "->")
    edge((0, 1), (1, 1), [$f_2$], label-side: right, "->")
    edge((1, 0), (1, 1), [$f_1$], label-side: left, "->")
    edge((0, 0), (1, 1), [$f$], label-side: center, "->")
  }, crossing-fill: thm-box-curr-color()))
  则存在自然同构：
  $
    R f_! (p_1^(-1) cal(K)_1 Lotimes_Lambda p_2^(-1) cal(K)_2) cong R f_(1,!) cal(K)_1 Lotimes_Lambda R f_(2,!) cal(K)_2
  $
  其中 $cal(K)_1 in D_#[tor] ((X_1)_et, Lambda), cal(K)_2 in D_#[tor] ((X_2)_et, Lambda)$。这个同构与任意基变换相容，关于 $f_1$ 与 $f_2$ 对称，与 $3 times 3$ 拉回方块相容，并对三重积满足结合律。
]
#proof[
  先构造这个同构：
  /*$
    & R f_! (p_1^(-1) cal(K)_1 Lotimes_Lambda p_2^(-1) cal(K)_2) \
    cong& R f_(2,!) R p_(2,!) (p_1^(-1) cal(K)_1 Lotimes_Lambda p_2^(-1) cal(K)_2) \
    cong& R f_(2,!) (R p_(2,!) p_1^(-1) cal(K)_1 Lotimes_Lambda cal(K)_2) #[by projection formula] \
    cong& R f_(2,!) (f_2^(-1) R f_(1,!) cal(K)_1 Lotimes_Lambda cal(K)_2) #[by proper base change] \
    cong& R f_(1,!) cal(K)_1 Lotimes_Lambda R f_(2,!) cal(K)_2 #[by projection formula]
  $*/
  $
    & R f_(1,!) cal(K)_1 Lotimes_Lambda R f_(2,!) cal(K)_2 \
    cong& R f_(2,!) (f_2^(-1) R f_(1,!) cal(K)_1 Lotimes_Lambda cal(K)_2) #[由投影公式] \
    cong& R f_(2,!) (R p_(2,!) p_1^(-1) cal(K)_1 Lotimes_Lambda cal(K)_2) #[由紧合基变换] \
    cong& R f_(2,!) R p_(2,!) (p_1^(-1) cal(K)_1 Lotimes_Lambda p_2^(-1) cal(K)_2) #[由投影公式] \
    cong& R f_! (p_1^(-1) cal(K)_1 Lotimes_Lambda p_2^(-1) cal(K)_2)
  $
  由投影与基变换的相容性以及基变换的自然性，这个 Künneth 同构与任意基变换相容。下面证明其余的相容性陈述。

  从现在起，我们把 $Lotimes_Lambda$ 简写为 $Lotimes$，并在记号中省略 $Lambda$。为证明对称性与 $3 times 3$ 相容性这两条陈述，我们需要两个引理。我们约定：
  
  - $P(f)$ 表示 $R f_!$ 的投影态射；
  
  - $P'(f)$ 表示 $R f_!$ 在另一个变量位置上的投影态射，即 $cal(K) Lotimes R f_! cal(L) -> R f_! (f^(-1) cal(K) Lotimes cal(L))$；

  - $BC$ 表示基变换。

  第一个引理是在所有态射都紧合的情形下，对 Künneth 同构的另一描述。
  #lemma(name: <proper-kunneth-alt-desc>)[
    当 $f_1, f_2$ 都紧合时，Künneth 同构：
    $
      R f_(1,*) cal(K)_1 Lotimes R f_(2,*) cal(K)_2 -> R f_* (p_1^(-1) cal(K)_1 Lotimes p_2^(-1) cal(K)_2) 
    $
    可以这样描述：由 $R f_*$ 的伴随，它等价于映射 $f^(-1) (R f_(1,*) cal(K)_1 Lotimes R f_(2,*) cal(K)_2) -> p_1^(-1) cal(K)_1 Lotimes p_2^(-1) cal(K)_2$。这个映射是：
    $
      f^(-1) (R f_(1,*) cal(K)_1 Lotimes R f_(2,*) cal(K)_2) &cong f^(-1) R f_(1,*) cal(K)_1 Lotimes f^(-1) R f_(2,*) cal(K)_2 \
      &= p_1^(-1) f_1^(-1) R f_(1,*) cal(K)_1 Lotimes p_2^(-1) f_2^(-1) R f_(2,*) cal(K)_2 \
      &-> p_1^(-1) cal(K)_1 Lotimes p_2^(-1) cal(K)_2
    $
    其中第一个映射是幺半同构，第二个映射由两个伴随余单位组成。
  ]
  #proof[
    考虑 Künneth 映射的构造：
    $
      R f_(1,*) cal(K)_1 Lotimes R f_(2,*) cal(K)_2 &-->^(P'(f_2)) R f_(2,*) (f_2^(-1) R f_(1,*) cal(K)_1 Lotimes cal(K)_2) \
      &-->^BC R f_(2,*) (R p_(2,*) p_1^(-1) cal(K)_1 Lotimes cal(K)_2) \
      &-->^(P(p_2)) R f_(2,*) R p_(2,*) (p_1^(-1) cal(K) Lotimes p_2^(-1) cal(K)_2) 
    $
    现在逐项来看：
    
    - 在构造 $R f_*$ 的投影态射时，我们已经描述了投影态射在伴随下的样子。在伴随下，$P(f): R f_* cal(K) Lotimes cal(L) -> R f_* (cal(K) Lotimes cal(L))$ 变成：#h(1fr)
      $
        f^(-1) (R f_* cal(K) Lotimes cal(L)) -->^M f^(-1) R f_* cal(K) Lotimes f^(-1) cal(L) -->^eta cal(K) Lotimes f^(-1) cal(L)
      $
      这里 $M$ 表示幺半同构，$eta$ 表示余单位。$P'(f)$ 看起来一样，只是张量因子对调。
  
    于是 Künneth 映射在伴随下变成：
    $
      p_2^(-1) f_2^(-1) (R f_(1,*) cal(K)_1 Lotimes R f_(2,*) cal(K)_2) &-->^(M(f_2)) p_2^(-1) (f_2^(-1) R f_(1,*) cal(K)_1 Lotimes f_2^(-1) R f_(2,*) cal(K)_2) \
      &-->^(eta(f_2)) p_2^(-1) (f_2^(-1) R f_(1,*) cal(K)_1 Lotimes cal(K)_2) \
      &-->^BC p_2^(-1) (R p_(2,*) p_1^(-1) cal(K)_1 Lotimes cal(K)_2) \
      &-->^(M(p_2)) p_2^(-1) R p_(2,*) p_1^(-1) cal(K)_1 Lotimes p_2^(-1) cal(K)_2 \
      &-->^(eta(p_2)) p_1^(-1) cal(K)_1 Lotimes p_2^(-1) cal(K)_2
    $
    由自然性，可以交换最后四步的次序，把它改写成：
    $
      p_2^(-1) f_2^(-1) (R f_(1,*) cal(K)_1 Lotimes R f_(2,*) cal(K)_2) &-->^(M(f_2)) p_2^(-1) (f_2^(-1) R f_(1,*) cal(K)_1 Lotimes f_2^(-1) R f_(2,*) cal(K)_2) -->^(M(p_2)) p_2^(-1) f_2^(-1) R f_(1,*) cal(K)_1 Lotimes p_2^(-1) f_2^(-1) R f_(2,*) cal(K)_2 \
      &-->^BC p_2^(-1) R p_(2,*) p_1^(-1) cal(K)_1 Lotimes p_2^(-1) f_2^(-1) R f_(2,*) cal(K)_2 \
      &-->^(eta(p_2)) p_1^(-1) cal(K)_1 Lotimes p_2^(-1) f_2^(-1) R f_(2,*) cal(K)_2 \
      &-->^(eta(f_2)) p_2^(-1) (f_2^(-1) R f_(1,*) cal(K)_1 Lotimes cal(K)_2)
    $
    这已经与所断言的态射颇为相似，剩下只需说明复合：
    $
      p_2^(-1) f_2^(-1) R f_(1,*) cong p_1^(-1) f_1^(-1) R f_(1,*) -->^(eta(f_1)) p_1^(-1)
    $
    与下述复合相同：
    $
      p_2^(-1) f_2^(-1) R f_(1,*) -->^(BC) p_2^(-1) R p_(2,*) p_1^(-1) -->^(eta(p_2)) p_1^(-1)
    $

    - 事实上，由 @bcbc-all-rights，第二条路径是：#h(1fr)
      $
        p_2^(-1) f_2^(-1) R f_(1,*) &-->^(p_2^(-1) u(p_2) f_2^(-1) R f_(1,*)) p_2^(-1) R p_(2,*) p_2^(-1) f_2^(-1) R f_(1,*) cong p_2^(-1) R p_(2,*) p_1^(-1) f_1^(-1) R f_(1,*) \
        &-->^(p_2^(-1) R p_(2,*) p_1^(-1) eta(f_1)) p_2^(-1) R p_(2,*) p_1^(-1) -->^(eta(p_2) p_1^(-1)) p_1^(-1)
      $
      由自然性把第四个映射与第二、第三个映射交换位置，再应用一条伴随恒等式，便得到第一条路径。

    证毕。
  ]

  第二个引理说明：图中 Künneth 映射的对称性，与它对 $3 times 3$ 拉回图表的相容性之间是什么关系。

  #lemma(name: <kunneth-3x3-and-symmetry>)[
    取 Noether 概形之间有限型分离态射构成的 $3 times 3$ 拉回图表。

    // https://q.uiver.app/#r=typst&q=WzAsOSxbMCwwLCJaIl0sWzEsMCwiWl8xIl0sWzIsMCwiV18xIl0sWzAsMSwiWl8yIl0sWzEsMSwiWCJdLFsyLDEsIlhfMSJdLFswLDIsIldfMiJdLFsxLDIsIlhfMiJdLFsyLDIsIlkiXSxbNSw4LCJmXzEiLDFdLFs3LDgsImZfMiIsMV0sWzQsNSwicF8xIiwxXSxbNCw3LCJwXzIiLDFdLFsyLDUsImhfMSIsMV0sWzYsNywiaF8yIiwxXSxbMSw0LCJnXzEiLDFdLFszLDQsImdfMiIsMV0sWzEsMiwic18xIiwxXSxbMyw2LCJzXzIiLDFdLFswLDEsInFfMSIsMV0sWzAsMywicV8yIiwxXV0=
    #context align(center, diagram({
      node((0, 0), [$Z$])
      node((1, 0), [$Z_1$])
      node((2, 0), [$W_1$])
      node((0, 1), [$Z_2$])
      node((1, 1), [$X$])
      node((2, 1), [$X_1$])
      node((0, 2), [$W_2$])
      node((1, 2), [$X_2$])
      node((2, 2), [$Y$])
      edge((2, 1), (2, 2), [$f_1$], label-side: center, "->")
      edge((1, 2), (2, 2), [$f_2$], label-side: center, "->")
      edge((1, 1), (2, 1), [$p_1$], label-side: center, "->")
      edge((1, 1), (1, 2), [$p_2$], label-side: center, "->")
      edge((2, 0), (2, 1), [$h_1$], label-side: center, "->")
      edge((0, 2), (1, 2), [$h_2$], label-side: center, "->")
      edge((1, 0), (1, 1), [$g_1$], label-side: center, "->")
      edge((0, 1), (1, 1), [$g_2$], label-side: center, "->")
      edge((1, 0), (2, 0), [$s_1$], label-side: center, "->")
      edge((0, 1), (0, 2), [$s_2$], label-side: center, "->")
      edge((0, 0), (1, 0), [$q_1$], label-side: center, "->")
      edge((0, 0), (0, 1), [$q_2$], label-side: center, "->")
    }, crossing-fill: thm-box-curr-color()))

    记：
    
    - $BC_(1,2,3,4)$ 分别为左上、右上、左下、右下四个方块中的基变换，其中沿竖直映射取拉回、沿水平映射取推前；
    
    - $BC_i^T$ 是与 $BC_i$ 同一个方块中的基变换，但沿水平映射取拉回、沿竖直映射取推前；

    - $K_1, K_2$ 分别为左上与右下方块中的 Künneth 映射。
    
    设左下方块中的 Künneth 映射对称。则 Künneth 映射与这个 $3 times 3$ 方块相容。也就是说，复合：
    $
      & R f_(1,!) R h_(1,!) cal(K)_1 Lotimes R f_(2,!) R h_(2,!) cal(K)_2 \
      -->^(K_2) & R f_(2,!) R p_(2,!) (p_1^(-1) R h_(1,!) cal(K)_1 Lotimes p_2^(-1) R h_(2,!) cal(K)_2) \
      -->^(BC_2^T, BC_3) & R f_(2,!) R p_(2,!) (R g_(1,!) s_1^(-1) cal(K)_1 Lotimes R g_(2,!) s_2^(-1) cal(K)_2) \
      -->^(K_1) & R f_(2,!) R p_(2,!) R g_(2,!) R s_(q,!) (q_1^(-1) s_1^(-1) cal(K)_1 Lotimes q_2^(-1) s_2^(-1) cal(K)_2) \
      cong & R f_(2,!) R h_(2,!) R s_(2,!) R s_(q,!) (q_1^(-1) s_1^(-1) cal(K)_1 Lotimes q_2^(-1) s_2^(-1) cal(K)_2)
    $
    恰好就是大方块的 Künneth 映射。
  ]
  #proof[
    先写下路径 (1)，即两个小方块的 Künneth：
    $
      & R f_(1,!) R h_(1,!) cal(K)_1 Lotimes R f_(2,!) R h_(2,!) cal(K)_2 \
      -->^(P'(f_2)) & R f_(2,!) (f_2^(-1) R f_(1,!) R h_(1,!) cal(K)_1 Lotimes R h_(2,!) cal(K)_2) \
      -->^(BC_4^T) & R f_(2,!) (R p_(2,!) p_1^(-1) R h_(1,!) cal(K)_1 Lotimes R h_(2,!) cal(K)_2) \
      -->^(P(p_2)) & R f_(2,!) R p_(2,!) (p_1^(-1) R h_(1,!) cal(K)_1 Lotimes p_2^(-1) R h_(2,!) cal(K)_2) \
      -->^(BC_2^T, BC_3) & R f_(2,!) R p_(2,!) (R g_(1,!) s_1^(-1) cal(K)_1 Lotimes R g_(2,!) s_2^(-1) cal(K)_2) \
      -->^(P'(g_2)) & R f_(2,!) R p_(2,!) R g_(2,!) (g_2^(-1) R g_(1,!) s_1^(-1) cal(K)_1 Lotimes s_2^(-1) cal(K)_2)\
      -->^(BC_1^T) & R f_(2,!) R p_(2,!) R g_(2,!) (R q_(2,!) q_1^(-1) s_1^(-1) cal(K)_1 Lotimes s_2^(-1) cal(K)_2) & \ 
      -->^(P(q_2)) & R f_(2,!) R p_(2,!) R g_(2,!) R q_(2,!) (q_1^(-1) s_1^(-1) cal(K)_1 Lotimes q_2^(-1) s_2^(-1) cal(K)_2) \
      -->^c & R f_(2,!) R h_(2,!) R s_(2,!) R q_(2,!) (q_1^(-1) s_1^(-1) cal(K)_1 Lotimes q_2^(-1) s_2^(-1) cal(K)_2)
    $
    其中 $c$ 是同构 $R p_(2,!) R g_(2,!) -> R h_(2,!) R s_(2,!)$。而路径 (2)（即大方块的 Künneth）由投影态射与复合的相容性给出，它是如下路径：
    $
      & R f_(1,!) R h_(1,!) cal(K)_1 Lotimes R f_(2,!) R h_(2,!) cal(K)_2 \
      -->^(P'(f_2)) & R f_(2,!) (f_2^(-1) R f_(1,!) R h_(1,!) cal(K)_1 Lotimes R h_(2,!) cal(K)_2) \
      -->^(P'(h_2)) & R f_(2,!) R h_(2,!) (h_2^(-1) f_2^(-1) R f_(1,!) R h_(1,!) cal(K)_1 Lotimes cal(K)_2) \
      -->^(BC_(1,2,3,4)^T) & R f_(2,!) R h_(2,!) (R s_(2,!) R q_(2,!) q_1^(-1) s_1^(-1) cal(K)_1 Lotimes cal(K)_2) \
      -->^(P(s_2)) & R f_(2,!) R h_(2,!) R s_(2,!) (R q_(2,!) q_1^(-1) s_1^(-1) cal(K)_1 Lotimes s_2^(-1) cal(K)_2) \
      -->^(P(q_2)) & R f_(2,!) R h_(2,!) R s_(2,!) R q_(2,!) (q_1^(-1) s_1^(-1) cal(K)_1 Lotimes q_2^(-1) s_2^(-1) cal(K)_2)
    $
    由自然性，可以把 (1) 中最后两个态射由 $-->^(P(q_2)) -->^c$ 换成 $-->^c -->^(P(q_2))$。于是可以立刻从两条路径两端消去 $P'(f_2)$ 与 $P(q_2)$，再去掉每一项最外层都出现的 $R f_(2,!)$，从而只需证明路径 (2')：
    $
      & f_2^(-1) R f_(1,!) R h_(1,!) cal(K)_1 Lotimes R h_(2,!) cal(K)_2 \
      -->^(P'(h_2)) & R h_(2,!) (h_2^(-1) f_2^(-1) R f_(1,!) R h_(1,!) cal(K)_1 Lotimes cal(K)_2) \
      -->^(BC_(1,2,3,4)^T) & R h_(2,!) (R s_(2,!) R q_(2,!) q_1^(-1) s_1^(-1) cal(K)_1 Lotimes cal(K)_2) \
      -->^(P(s_2)) & R h_(2,!) R s_(2,!) (R q_(2,!) q_1^(-1) s_1^(-1) cal(K)_1 Lotimes s_2^(-1) cal(K)_2)
    $ 
    与路径 (1')：
    $
      &f_2^(-1) R f_(1,!) R h_(1,!) cal(K)_1 Lotimes R h_(2,!) cal(K)_2 \
      -->^(BC_4^T) & R p_(2,!) p_1^(-1) R h_(1,!) cal(K)_1 Lotimes R h_(2,!) cal(K)_2 \
      -->^(P(p_2)) & R p_(2,!) (p_1^(-1) R h_(1,!) cal(K)_1 Lotimes p_2^(-1) R h_(2,!) cal(K)_2) \
      -->^(BC_2^T, BC_3) & R p_(2,!) (R g_(1,!) s_1^(-1) cal(K)_1 Lotimes R g_(2,!) s_2^(-1) cal(K)_2) \
      -->^(P'(g_2)) & R p_(2,!) R g_(2,!) (g_2^(-1) R g_(1,!) s_1^(-1) cal(K)_1 Lotimes s_2^(-1) cal(K)_2)\
      -->^(BC_1^T) & R p_(2,!) R g_(2,!) (R q_(2,!) q_1^(-1) s_1^(-1) cal(K)_1 Lotimes s_2^(-1) cal(K)_2) & \ 
      -->^c & R h_(2,!) R s_(2,!) (R q_(2,!) q_1^(-1) s_1^(-1) cal(K)_1 Lotimes s_2^(-1) cal(K)_2)
    $
    接下来，在路径 (1') 中，由自然性可把末尾的 $-->^(BC_1^T) -->^c$ 换成 $-->^c -->^(BC_1^T)$，并把 $BC_2^T$ 挪到 $P(p)_2$ 左边。在路径 (2') 中，由自然性可把 $BC_2^T, BC_4^T$ 挪到 $P'(h_2)$ 左边，把 $BC_1^T$ 挪到 $P(s)_2$ 右边。总之，我们要比较的是路径 (1')：
    $
      bullet -->^(BC_4^T) bullet -->^(BC_2^T) bullet -->^(P(p_2)) bullet -->^(BC_3) bullet -->^(P'(g_2)) bullet -->^c bullet -->^(BC_1^T) bullet
    $
    与路径 (2')：
    $
      bullet -->^(BC_4^T) bullet -->^(BC_2^T) bullet -->^(P'(h_2)) bullet -->^(BC_3) bullet -->^(P(s_2)) bullet -->^(BC_1^T) bullet
    $
    现在可以消去 $BC_(1,2,4)^T$，于是只需说明路径 (1'')：
    $
      & R p_(2,!) R g_(1,!) s_1^(-1) cal(K)_1 Lotimes R h_(2,!) cal(K)_2 \
      -->^(P'(h_2)) & R h_(2,!) (h_2^(-1) R p_(2,!) R g_(1,!) s_1^(-1) cal(K)_1 Lotimes cal(K)_2) \
      -->^(BC_3^T) & R h_(2,!) (R s_(2,!) g_2^(-1) R g_(1,!) s_1^(-1) cal(K)_1 Lotimes cal(K)_2) \
      -->^(P(s_2)) & R h_(2,!) R s_(2,!) (g_2^(-1) R g_(1,!) s_1^(-1) cal(K)_1 Lotimes s_2^(-1) cal(K)_2)
    $
    与路径 (2'')：
    $
      & R p_(2,!) R g_(1,!) s_1^(-1) cal(K)_1 Lotimes R h_(2,!) cal(K)_2 \
      -->^(P(p_2)) & R p_(2,!) (R g_(1,!) s_1^(-1) cal(K)_1 Lotimes p_2^(-1) R h_(2,!) cal(K)_2) \
      -->^(BC_3) & R p_(2,!) (R g_(1,!) s_1^(-1) cal(K)_1 Lotimes R g_(2,!) s_2^(-1) cal(K)_2) \
      -->^(P'(g_2)) & R p_(2,!) R g_(2,!) (g_2^(-1) R g_(1,!) s_1^(-1) cal(K)_1 Lotimes s_2^(-1) cal(K)_2) \
      -->^(c^(-1)) & R h_(2,!) R s_(2,!) (g_2^(-1) R g_(1,!) s_1^(-1) cal(K)_1 Lotimes s_2^(-1) cal(K)_2)
    $
    然而按定义，路径 (1'') 就是把左下方块的 Künneth 映射作用于 $R g_(1,!) s_1^(-1) cal(K)_1$ 与 $cal(K)_2$，而路径 (2'') 是同一个方块的 Künneth 但转置之后的样子。二者相等，恰恰就是左下方块的 Künneth 对称的含义。
  ]

  下面开始证明对称性与 $3 times 3$ 相容性这两条陈述。

  - 第一步。设在给定的拉回图表中 $f_2$ 是开浸入。我们断言此时的 Künneth 映射对称。#h(1fr)
  
    事实上，由紧合基变换以及与任意基变换的相容性，只需沿 $Y$ 的几何点 $ol(y)$ 作基变换后证明对称性。若 $ol(y)$ 不在 $X_2$ 中，则 $R f_(1,!) cal(K)_1 Lotimes R f_(2,!) cal(K)_2 -> R f_! (p_1^(-1) cal(K)_1 Lotimes p_2^(-1) cal(K)_2)$ 两边的茎都是零，对称性自动成立。于是只需沿 $Y$ 的、落在 $X_2$ 中的几何点作基变换后证明对称性。此时基变换后的图表为：
    // https://q.uiver.app/#r=typst&q=WzAsNCxbMCwwLCJYIl0sWzEsMCwiWCJdLFswLDEsIlNwZWMoaykiXSxbMSwxLCJTcGVjKGspIl0sWzAsMSwiIiwwLHsic3R5bGUiOnsiYm9keSI6eyJuYW1lIjoiZG91YmxlIGJhcnJlZCJ9fX1dLFsyLDMsIiIsMCx7InN0eWxlIjp7ImJvZHkiOnsibmFtZSI6ImRvdWJsZSBiYXJyZWQifX19XSxbMCwyLCJmIiwyXSxbMSwzLCJmIl1d
    #align(center, diagram({
      node((0, 0), [$X$])
      node((1, 0), [$X$])
      node((0, 1), [$Spec(k)$])
      node((1, 1), [$Spec(k)$])
      edge((0, 0), (1, 0), "=")
      edge((0, 1), (1, 1), "=")
      edge((0, 0), (0, 1), [$f$], label-side: right, "->")
      edge((1, 0), (1, 1), [$f$], label-side: left, "->")
    }, spacing: (1.5em, 3em)))
    其中 $k$ 是可分闭域。此时的 Künneth 映射就是投影态射：
    $
      R f_! cal(K)_1 Lotimes cal(K)_2 -> R f_! (cal(K)_1 Lotimes f^(-1) cal(K)_2)
    $
    而转置后的 Künneth 映射按定义检查也是这个投影态射。因此对称性自动成立。

  - 第二步。一般情形下取紧化 $X_i ->^(j_i) ol(X)_i ->^(ol(f)_i) Y$，便可把原来的拉回方块拆成 $3 times 3$ 拉回图表：
    // https://q.uiver.app/#r=typst&q=WzAsOSxbMCwwLCJYIl0sWzEsMCwiWl8xIl0sWzIsMCwiWF8xIl0sWzAsMSwiWl8yIl0sWzEsMSwib2woWCkiXSxbMiwxLCJvbChYKV8xIl0sWzAsMiwiWF8yIl0sWzEsMiwib2woWClfMiJdLFsyLDIsIlkiXSxbNSw4LCJvbChmKV8xIiwxXSxbNyw4LCJvbChmKV8yIiwxXSxbNCw1LCJvbChwKV8xIiwxXSxbNCw3LCJvbChwKV8yIiwxXSxbMiw1LCJqXzEiLDFdLFs2LDcsImpfMiIsMV0sWzEsNCwiZ18xIiwxXSxbMyw0LCJnXzIiLDFdLFsxLDIsInNfMSIsMV0sWzMsNiwic18yIiwxXSxbMCwxLCJxXzEiLDFdLFswLDMsInFfMiIsMV1d
    #context align(center, diagram({
      node((0, 0), [$X$])
      node((1, 0), [$Z_1$])
      node((2, 0), [$X_1$])
      node((0, 1), [$Z_2$])
      node((1, 1), [$ol(X)$])
      node((2, 1), [$ol(X)_1$])
      node((0, 2), [$X_2$])
      node((1, 2), [$ol(X)_2$])
      node((2, 2), [$Y$])
      edge((2, 1), (2, 2), [$ol(f)_1$], label-side: center, "->")
      edge((1, 2), (2, 2), [$ol(f)_2$], label-side: center, "->")
      edge((1, 1), (2, 1), [$ol(p)_1$], label-side: center, "->")
      edge((1, 1), (1, 2), [$ol(p)_2$], label-side: center, "->")
      edge((2, 0), (2, 1), [$j_1$], label-side: center, "->")
      edge((0, 2), (1, 2), [$j_2$], label-side: center, "->")
      edge((1, 0), (1, 1), [$g_1$], label-side: center, "->")
      edge((0, 1), (1, 1), [$g_2$], label-side: center, "->")
      edge((1, 0), (2, 0), [$s_1$], label-side: center, "->")
      edge((0, 1), (0, 2), [$s_2$], label-side: center, "->")
      edge((0, 0), (1, 0), [$q_1$], label-side: center, "->")
      edge((0, 0), (0, 1), [$q_2$], label-side: center, "->")
      edge((0, 0), (1, 1), [$q$], label-side: center, "->")
      edge((1, 1), (2, 2), [$ol(f)$], label-side: center, "->")
    }, crossing-fill: thm-box-curr-color()))

    由第一步，这个图表中左下方块的 Künneth 对称。故由 @kunneth-3x3-and-symmetry，Künneth 映射与这个 $3 times 3$ 图表相容。换言之，若 $K_1, K_2$ 分别是左上与右下方块的 Künneth，则原方块的 Künneth 变成：
    $
      R f_(1,!) cal(K)_1 Lotimes R f_(2,!) cal(K)_2 &-->^(K_2) R ol(f)_! (ol(p)_1^(-1) j_(1,!) cal(K)_1 Lotimes ol(p)_2^(-1) j_(2,!) cal(K)_1) \
      &-->^BC R ol(f)_! (g_(1,!) s_1^(-1) cal(K)_1 Lotimes g_(2,!) s_2^(-1) cal(K)_1) \
      &-->^(K_1) R f_! (p_1^(-1) cal(K)_1 Lotimes p_2^(-1) cal(K)_2)
    $ 
    于是只需证明两个小方块的 Künneth 映射 $K_1, K_2$ 对称。左上方块的水平态射是开浸入，故由第一步 $K_1$ 对称。另一方面，$K_2$ 对称，因为 @proper-kunneth-alt-desc 给出了 Künneth 映射的一个对称的替代描述。

    这样就证明了 Künneth 映射总是对称的。

  - 由第二步，Künneth 映射总是对称的。因此 @kunneth-3x3-and-symmetry 表明 Künneth 映射总是与 $3 times 3$ 拉回图表相容。

  剩下要证的是对三重积的结合律。这里只给出证明梗概。@proper-kunneth-alt-desc 中的构造也是结合的，故所有态射都紧合的情形已经完成。
  
  对一般的三重积，可取紧化 $X_i ->^(j_i) ol(X)_i ->^(ol(f)_i) Y, i=1,2,3$。此后凡遇到开浸入，所需的一切都是自动的：作基变换到几何点，使该开浸入变成恒等，陈述便化为平凡情形。有了这些，$3 times 3$ 相容性以及其他相容性陈述便把证明归结到开浸入情形与紧合情形。
  
  （我不愿把这段证明完整写下来的主要原因是：它需要构造一个 $3 times 3 times 3$ 的立方图表，含 27 个顶点和 54 条边。你大概能猜到我为什么跳过这一段。）
  // - Compatibility for horizontal concatenation requires that for a Cartesian diagram: #h(1fr)
  //   // https://q.uiver.app/#r=typst&q=WzAsNixbMCwwLCJYJyJdLFswLDEsIlgnXzEiXSxbMSwwLCJYIl0sWzEsMSwiWF8xIl0sWzIsMCwiWF8yIl0sWzIsMSwiWSJdLFszLDUsImZfMSIsMl0sWzEsMywiZyIsMl0sWzIsMywicF8xIiwxXSxbMiw0LCJwXzIiXSxbNCw1LCJmXzIiXSxbMCwyLCJoXzIiXSxbMiw1LCJmIiwxXSxbMCwxLCJoXzEiLDJdLFswLDMsImgiLDFdXQ==
  //   #context align(center, diagram({
  //     node((0, 0), [$X'$])
  //     node((0, 1), [$X'_1$])
  //     node((1, 0), [$X$])
  //     node((1, 1), [$X_1$])
  //     node((2, 0), [$X_2$])
  //     node((2, 1), [$Y$])
  //     edge((1, 1), (2, 1), [$f_1$], label-side: right, "->")
  //     edge((0, 1), (1, 1), [$g$], label-side: right, "->")
  //     edge((1, 0), (1, 1), [$p_1$], label-side: center, "->")
  //     edge((1, 0), (2, 0), [$p_2$], label-side: left, "->")
  //     edge((2, 0), (2, 1), [$f_2$], label-side: left, "->")
  //     edge((0, 0), (1, 0), [$h_2$], label-side: left, "->")
  //     edge((1, 0), (2, 1), [$f$], label-side: center, "->")
  //     edge((0, 0), (0, 1), [$h_1$], label-side: right, "->")
  //     edge((0, 0), (1, 1), [$h$], label-side: center, "->")
  //   }, crossing-fill: thm-box-curr-color()))
  //   with $q: X' -> Y, q_2: X' -> X_2, g_1: X'_1 -> Y$ has the following two paths equal: 
  //   $
  //     R f_(1,!) R g_! cal(K)'_1 Lotimes_Lambda R f_(2,!) cal(K)_2 -->^K R f_! (p_1^(-1) R g_! cal(K)'_1 Lotimes_Lambda cal(K)_2) -->^BC R f_! (R h_(2,!) h_1^(-1) cal(K)'_1 Lotimes_Lambda cal(K)_2) -->^K 
  //   $
]

作为 Künneth 公式的应用，现在可以计算 $AA^d$ 与 $PP^d$ 的紧支上同调了。

#proposition(name: <cohom-with-proper-supp-of-Ad-and-Pd>)[
  设 $k$ 是可分闭域，$n in k^times$ 且为自然数。则：

  + 存在典范同构：#h(1fr)
    $
      H^q_c (AA^d_k, ZZ\/n) cong cases(
        mu_n^(otimes -d) &\, q = 2d, 
        0 &\, #[否则]
      )
    $

  + 存在典范同构：#h(1fr)
    $
      H^q (PP^d_k, ZZ\/n) cong cases(
        mu_n^(otimes -j) &\, q = 2j\, 0 <= j <= d, 
        0 &\, #[否则]
      )
    $
]
#proof[
  (1) 先计算 $H^q_c (AA^1_k, mu_n)$。由 Grothendieck 消没，只需处理 $q = 0,1,2$。
  
  设 $AA^1_k$ 的紧化为 $AA^1_k ->^j PP^1_k -> Spec(k)$，并令 $i: Spec(k) -> PP^1_k$ 是 $oo$ 的嵌入。则由零延拓三角（@rf-lower-shriek-first-props (3)），有长正合列：
  $
    0 &-> H^0_c (AA^1_k, mu_n) -> H^0 (PP^1_k, mu_n) -> H^0 (Spec(k), mu_n) \
    &-> H^1_c (AA^1_k, mu_n) -> underbrace(H^1 (PP^1_k, mu_n), 0) -> underbrace(H^1 (Spec(k), mu_n), 0) \
    &-> H^2_c (AA^1_k, mu_n) -> H^2 (PP^1_k, mu_n) -> underbrace(H^2 (Spec(k), mu_n), 0) -> 0
  $
  现在逐项计算：

  - 映射 $H^0 (PP^1_k, mu_n) -> H^0 (Spec(k), mu_n)$ 是恒等 $mu_n -> mu_n$。因此，#h(1fr)
    $
      H^0_c (AA^1_k, mu_n) = ker(H^0 (PP^1_k, mu_n) -> H^0 (Spec(k), mu_n)) = 0 \
      H^1_c (AA^1_k, mu_n) = coker(H^0 (PP^1_k, mu_n) -> H^0 (Spec(k), mu_n)) = 0
    $

  - 存在典范同构 $H^2_c (AA^1_k, mu_n) cong H^2 (PP^1_k, mu_n) cong ZZ\/n$，最后一步来自 @cohom-of-proj-curve (1)。

  于是 $H^q_c (AA^1_k, mu_n)$ 计算完毕，并得到典范同构：
  $
    R Gamma_c (AA^1_k, mu_n) cong ZZ\/n [-2]
  $
  与 $mu_n^(otimes -1)$ 作张量积并用投影公式，便得到典范同构：
  $
    R Gamma_c (AA^1_k, ul(ZZ\/n)) cong mu_n^(otimes -1)[-2]
  $
  又 $AA^d_k cong underbrace(AA^1_k times_k dots.c times_k AA^1_k, d#[ copies])$ 是 $d$ 重纤维积，投影为 $p_j: AA^d_k -> AA^1_k$，于是：
  $
    R Gamma_c (AA^d_k, ul(ZZ\/n)) &cong R Gamma_c (AA^d_k, p_1^(-1) ul(ZZ\/n) Lotimes_(ZZ\/n) dots.c Lotimes_(ZZ\/n) p_d^(-1) ul(ZZ\/n)) \
    &cong underbrace(R Gamma_c (AA^1_k, ul(ZZ\/n)) Lotimes_(ZZ\/n) dots.c Lotimes_(ZZ\/n) R Gamma_c (AA^1_k, ul(ZZ\/n)), d#[ copies]) #[由 Künneth 公式] \
    &cong underbrace(mu_n^(otimes -1)[-2] Lotimes_(ZZ\/n) dots.c Lotimes_(ZZ\/n) mu_n^(otimes -1)[-2], d#[ copies]) #[由 Künneth 公式] \
    &cong mu_n^(otimes -d)[-2d]
  $
  至此证毕。

  (2) 我们对 $d$ 归纳。$d=1$ 的情形就是 @cohom-of-proj-curve (1)。现在 $PP^d_k$ 有一对互补的开浸入与闭浸入：
  $
    j: AA^d_k -> PP^d_k, i: PP^(d-1)_k -> PP^d_k
  $
  因此有长正合列：
  $
    dots.c -> H^(q-1) (PP^(d-1)_k, ul(ZZ\/n)) -> H^q_c (AA^d_k, ul(ZZ\/n)) -> H^q (PP^d_k, ul(ZZ\/n)) -> H^q (PP^(d-1)_k, ul(ZZ\/n)) -> H^(q+1) (AA^d_k, ul(ZZ\/n)) -> dots.c
  $

  - 当 $q <= 2d-2$ 时，由 (1) 有 $H^q_c (AA^d_k, ul(ZZ\/n)) = H^(q+1)_c (AA^d_k, ul(ZZ\/n)) = 0$。于是有典范同构：
    $
      H^q (PP^d_k, ul(ZZ\/n)) cong H^q (PP^(d-1)_k, ul(ZZ\/n))
    $
    而所要的结论由关于 $PP^(d-1)_k$ 的归纳假设得到。

  - 当 $q = 2d-1$ 时，$H^(2d-1)_c (AA^d_k, ul(ZZ\/n)) = 0$ 且 $H^(2d-1) (PP^(d-1)_k, ul(ZZ\/n)) = 0$。因此，
    $
      H^(2d-1) (PP^d_k, ul(ZZ\/n)) = 0
    $

  - 当 $q = 2d$ 时，$H^(2d-1) (PP^(d-1)_k, ul(ZZ\/n)) = 0$ 且 $H^(2d) (PP^(d-1)_k, ul(ZZ\/n)) = 0$。于是有典范同构：
    $
      H^(2d) (PP^d_k, ul(ZZ\/n)) cong H^(2d)_c (AA^d_k, ul(ZZ\/n)) cong mu_n^(otimes -d)
    $

  至此证毕。
]
