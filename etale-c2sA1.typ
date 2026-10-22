#import "void-import.typ": *

== 根性态射

本节是对根性态射 (radicial) 的一段简短插叙。这类态射与平展态射有几分相反：平展态射以可分域扩张为特征，根性态射则以纯不可分域扩张为特征。

#proposition(name: <equiv-defns-of-radicial>)[
  （#cite-stacks("01S4")[Lemma 29.10.2]）设 $f: X -> Y$ 是概形态射。以下条件等价：

  + $f$ 是泛单的；

  + $f$ 是单射，且对每个满足 $f(x) = y$ 的点 $x$，$k(x)\/k(y)$ 都是纯不可分域扩张；

  + 对任意域 $K$，映射： #h(1fr)
    $
      Hom(Spec(K), X) -> Hom(Spec(K), Y)
    $
    是单射；

  + 对角映射 $Delta_(X\/Y): X -> X times_Y X$ 是满射。
]
#proof[
  (2) $<==>$(3)：
  #proof[
    显然：
    $
      Hom(Spec(K), X) = {(x, phi): x in X, phi: k(x) arrow.hook K}
    $
    因此，某个 $(y, psi) in Hom(Spec(K), Y)$ 的原像，正是那些满足 $f(x) = y$、且使复合 $k(y) -> k(x) ->^phi K$ 恰为 $psi$ 的 $(x, phi)$。

    (3) $==>$(2)：固定 $y in Y$。若不同的点 $x_(1,2) in X$ 满足 $f(x_1) = f(x_2) = y$，取一个同时包含 $k(x_1)$ 与 $k(x_2)$ 的域 $K\/k(y)$（例如 $k(x_1) otimes_(k(y)) k(x_2)$ 的某个剩余域）。于是 $k(y) -> K$ 同时穿过 $k(x_1)$ 与 $k(x_2)$ 分解，从而给出 $Hom(Spec(K), Y)$ 中同一元素的两个不同提升。矛盾。因此 $f$ 是单射。

    假设存在 $x in X$ 使 $f(x) = y$。取 $K = ol(k(x))$，则 $k(x)$ 只有唯一一种方式嵌入 $ol(k(x))$。这就迫使 $k(x)\/k(y)$ 纯不可分：否则它的可分部分会有非平凡的嵌入。

    (2) $==>$(3)：设 $(y, psi) in Hom(Spec(K), Y)$ 有两个提升 $(x_(1,2), phi_(1,2))$。由于 $f$ 是单射，$x_1 = x_2 = x$，而 $phi_(1,2)$ 是 $k(x) -> K$ 的两个嵌入，使得：
    $
      k(y) -> k(x) ->^(phi_(1,2)) K
    $
    都等于嵌入 $psi$。然而 $k(x)\/k(y)$ 纯不可分。因此相容的嵌入 $k(x) -> K$ 若存在，必定唯一。（事实上，$k(x)$ 是在 $k(y)$ 上添加若干 $p^m$ 次根得到的；在特征 $p$ 下，这样的根唯一。）
  
    #suppress-qed
  ]

  (1) $==>$(2)：
  #proof[
    按定义，$f$ 是单射。若 $f(x) = y$，沿 $k(y) -> Y$ 对 $f$ 作基变换，得到 $f: X_y -> Spec(k(y))$。$X_y$ 必定是单点，其约化为 $Spec(k(x))$。
    
    再进一步基变换到 $ol(k(y))$，则 $X_y otimes_(k(y)) ol(k(y))$ 仍是单点。$X_y$ 的约化为 $Spec(k(x))$，所以 $Spec(k(x) otimes_(k(y)) ol(k(y)))$ 是 $X_y otimes_(k(y)) ol(k(y))$ 中由幂零理想定义的闭子概形，并且与后者有相同的底空间。于是 $Spec(k(x) otimes_(k(y)) ol(k(y)))$ 是单点。
    
    这就迫使 $k(x)\/k(y)$ 纯不可分：否则 $k(x)$ 中 $k(y)$ 的可分闭包在与 $ol(k(y))$ 作张量积之后会分裂成多个 $ol(k(y))$ 的副本。

    #suppress-qed
  ]

  (3) $==>$(1)：
  #proof[
    要证 $f$ 泛单，只需证明 $f$ 的任意基变换的每个非空纤维都是单点。也就是说，对任意 $psi: Spec(K) -> Y$，我们需要证明基变换：
    $
      f_psi: X_K -> Spec(K)
    $
    中的 $X_K$ 要么为空、要么是单点。事实上，若 $X_K$ 有两个不同的点 $x_1, x_2$，可取同时包含 $k(x_1)$ 与 $k(x_2)$ 的域扩张 $L\/K$。于是由 $x_1$ 与 $x_2$ 得到两个不同的映射 $Spec(L) -> X_K -> X$。与 $f$ 复合后，它们都变成同一个映射 $Spec(L) -> Spec(K) -> Y$。这与 (3) 矛盾。
    #suppress-qed
  ]

  至此我们证明了 (1)(2)(3) 彼此等价。

  (1) $==>$(4)：由于 $f$ 泛单，投影 $p_1: X times_Y X -> X$ 作为 $f$ 的基变换也是单射。于是作为 $p_1$ 的截面，$Delta_(X\/Y)$ 是满射。

  (4) $==>$(2)：//假设 $(x_(1,2), phi_(1,2)) in Hom(Spec(K), X) $ 都被送到 $(y, psi) in Hom(Spec(K), Y) $。回忆一下：
  回忆：

  - $X times_S Y$ 的点对应四元组 $(x, y, s, frak(p))$，其中 $x in X, y in Y$ 都位于 $s in S$ 之上，且 $frak(p) in Spec(k(x) otimes_(k(s)) k(y))$。（#cite-stacks("01JT")[Lemma 26.17.5]）

  于是对角映射 $X -> X times_Y X$ 把 $x$ 送到 $(x, x, f(x), ker(k(x) otimes_(k(f(x))) k(x) -> k(x)))$。由于对角映射满射，满足 $f(x_1) = f(x_2)$ 的 $x_1, x_2$ 必定相等；并且对每个 $x in X$（记 $y = f(x)$），$k(x) otimes_(k(y)) k(x)$ 只有一个素理想。因此 $ker(k(x) otimes_(k(y)) k(x) -> k(x))$ 就是 $k(x) otimes_(k(y)) k(x)$ 的幂零根，于是每个形如 $a otimes 1 - 1 otimes a in k(x) otimes_(k(y)) k(x)$ 的元素都幂零。

  - 对每个 $a in k(x)$，若 $a$ 在 $k(y)$ 上超越，则 $k(y)(a) otimes_(k(y)) k(y)(a)$ 是 $k(y)[X, Y]$ 的局部化，从而是整环，而 $a otimes 1 - 1 otimes a$ 对应 $X - Y$，说它幂零就荒谬了。故 $a$ 在 $k(y)$ 上代数；设其极小多项式为 $p(X)$。那么：
    $
      k(y)(a) otimes_(k(y)) k(y)(a) cong (k(y)(a)[T])/((p(T)))
    $
    并且元素 $a otimes 1 - 1 otimes a$ 对应 $T - a$。由幂零性，对某个幂次 $m$ 有 $p(T) divides (T-a)^m$。因此 $p(T)$ 在 $ol(k(y))$ 中只有根 $a$。故 $a$ 在 $k(y)$ 上不可分。

  于是 $k(x)\/k(y)$ 纯不可分。
]

#definition(name: <defn-radicial-morphism>)[
  满足上述四条等价条件的态射 $f: X -> Y$ 称为*根性的*。
]

#properties(name: <radicial-morphism-first-props>)[
  0. 根性态射对基变换与复合稳定。

  1. 根性态射是分离的。

  2. 态射 $f: X -> Y$ 是泛同胚 (universal homeomorphism)，当且仅当它满射、根性且整。

  3. 态射 $f: X -> Y$ 是开浸入，当且仅当它根性且平展。
]
#proof[
  (0) 用“根性 $<==>$ 泛单”这一刻画，这是平凡的。

  (1) 对根性态射 $f: X -> Y$，对角映射 $Delta_(X\/Y): X -> X times_Y X$ 自动是浸入，并且是满射。因此它是闭浸入，从而 $f$ 分离。

  (2)($<==$) 满射性在基变换下保持，根性态射是泛单的，整态射是泛闭的。于是 $f$ 泛双射且泛闭，从而是泛同胚。

  ($==>$) 按定义，泛同胚满射且泛单（即根性），故只剩整性待验证。

  #lemma[
    若概形态射 $f: X -> Y$ 是同胚，则 $f$ 是仿射的。
  ]
  #proof[
    仿射性可在底上局部验证，故不妨设 $Y$ 仿射。

    任取 $y in Y$，令 $x = f^(-1)(y) in X$，可取仿射开集 $x in U subset X$。现在 $f(U)$ 是 $f(X)$ 中的开集，故可取函数 $u in A$ 使 $y in D(u) subset f(U)$。于是 $f^(-1) (D(u)) = D(u) times_Y U = D(u) times_Y U$ 是仿射底上两个仿射概形的纤维积，从而是仿射的。因此 $Y$ 的每个点都有一个仿射邻域，它在 $f$ 下的原像是 $X$ 的仿射开集。既然仿射性可在底上局部验证，$f$ 就是仿射的。
  ]

  于是 $f$ 仿射，而且还泛闭。接下来还需要一个引理：
  #lemma[
    仿射且泛闭的态射是整的。
  ]
  #proof[
    该性质可在底上局部验证，故不妨设 $f: X = Spec(B) -> Spec(A) = Y$ 泛闭。我们先化归到 $A, B$ 都是整环且 $A subset B$ 的情形。反设 $b in B$ 不在 $A$ 上整。那么：
    $
      "ev"_b: A[T] ->> C := A[b] subset B, p(T) |-> p(b)
    $
    它的核 $I subset A[T]$ 不含首一多项式。首一多项式构成 $A[T]$ 的乘法子集 $S$，于是 $I$ 定义了 $S^(-1) A[T]$ 的一个非单位理想。因此取 $S^(-1) A[T]$ 中含 $I$ 的素理想，便知存在 $frak(p) in Spec(A[T])$ 使 $I subset frak(p)$，且 $frak(p)$ 不含首一多项式。令 $frak(q) = frak(p)\/I in Spec(A[T]\/I) cong Spec(C)$，则 $b in C\/frak(q)$ 仍然不在 $A$ 上整，否则 $frak(p)$ 中就会出现首一多项式。现在：

    - $Spec(B) -> Spec(A)$ 泛闭，且分解为 $Spec(B) -> Spec(C) -> Spec(A)$。
    
      现在，$Spec(B) -> Spec(C)$ 的图态射 $Spec(B) -> Spec(B otimes_A C)$ 作为 $Spec(B) -> Spec(A)$ 的对角的基变换，是闭浸入，并且泛闭。$Spec(B otimes_A C) -> Spec(C)$ 是 $Spec(B) -> Spec(A)$ 的基变换，也泛闭。而 $Spec(B) -> Spec(C)$ 是二者的复合，因此也泛闭。又因 $C subset B$，它是支配的，从而是满射。

    于是可取 $frak(r) in Spec(B)$ 使 $frak(q) = C inter frak(r)$，此时有包含 $C\/frak(q) arrow.hook B\/frak(r)$。$[b] in C\/frak(q)$ 不在 $A$ 上整，故 $[b] in B\/frak(r)$ 也不在 $A$ 上整。因此，若 $B$ 为整环的情形已经证完，则 $Spec(B\/frak(r)) -> Spec(A)$ 会是整的，矛盾。

    于是不妨设 $B$ 是整环。令 $frak(p) = ker(A -> B) in Spec(A)$，则有分解 $Spec(B) -> Spec(A\/frak(p)) -> Spec(A)$。与前面处理 $Spec(B) -> Spec(C) -> Spec(A)$ 的论证相同，$Spec(B) -> Spec(A\/frak(p))$ 满射且泛闭。又只需证明 $B$ 在 $A\/frak(p)$ 上整。因此可以放心把 $A$ 换成 $A\/frak(p)$，并假定 $A, B$ 都是整环且 $A subset B$。
    
    由泛闭性的赋值判别法（#cite-stacks("01KF")[Proposition 26.20.6]），对每个以 $K$ 为分式域的赋值环 $R$，下方交换图表中虚线所示的对角映射总是存在：
    // https://q.uiver.app/#r=typst&q=WzAsNCxbMCwwLCJBIl0sWzAsMSwiQiJdLFsxLDEsIksiXSxbMSwwLCJSIl0sWzMsMiwiIiwwLHsic3R5bGUiOnsidGFpbCI6eyJuYW1lIjoiaG9vayIsInNpZGUiOiJ0b3AifX19XSxbMCwxXSxbMCwzXSxbMSwyXSxbMSwzLCIiLDEseyJzdHlsZSI6eyJib2R5Ijp7Im5hbWUiOiJkYXNoZWQifX19XV0=
    #align(center, diagram({
      node((0, 0), [$A$])
      node((0, 1), [$B$])
      node((1, 1), [$K$])
      node((1, 0), [$R$])
      edge((1, 0), (1, 1), "hook->")
      edge((0, 0), (0, 1), "->")
      edge((0, 0), (1, 0), "->")
      edge((0, 1), (1, 1), "->")
      edge((0, 1), (1, 0), "-->")
    }))
    取 $K$ 为 $Frac(B)$，并取 $B -> K$ 为自然包含映射。这时赋值判别法告诉我们：

    - 对 $K$ 中每个包含 $A$ 的赋值环 $R$，$R$ 也包含 $B$。

    这要用到下述代数事实：
    #lemma[
      （@cite-atiyah-macdonald[Corollary 5.22]）设 $A$ 是域 $K$ 的子环，则 $A$ 在 $K$ 中的整闭包恰为 $K$ 中所有包含 $A$ 的赋值环的交。
    ]

    可见 $B$ 含于 $A$ 在 $K$ 中的整闭包，从而在 $A$ 上整。
  ]

  (3)($==>$) 不难：直接验证即知开浸入既平展又根性。所以只需证明 ($<==$)。设 $f: X -> Y$ 平展且根性。平展态射是开的，故 $f(X) -> Y$ 是开浸入，而 $f: X -> f(X)$ 是满射、平展、根性的。把 $Y$ 换成 $f(X)$，于是不妨设 $f$ 还满射。这时 $f$ 泛单、满射，又因平展而泛开，从而是泛同胚，因此整。平展态射是局部有限展示的，故 $f$ 有限。又因 $f$ 平坦，这说明 $f$ 实际上是有限局部自由的。为完成证明，注意：
  $
    "rk"_(cal(O)_(Y,f(x))) (cal(O)_(X,x)) = dim_(k(f(x))) (cal(O)_(X,x)\/frak(m)_(f(x))cal(O)_(X,x)) = dim_(k(f(x))) (k(x))
  $
  这些等式由平展性给出。$k(x)\/k(f(x))$ 因平展而有限可分，又因根性而纯不可分，故必为平凡扩张。于是 $dim_(k(f(x))) (k(x)) = 1$，从而每个 $cal(O)_(Y,f(x)) -> cal(O)_(X,x)$ 都是同构。因此 $X -> Y$ 是同构。
]

#corollary(name: <adjoining-pth-root-in-char-p-is-univ-homeo>)[
  设 $A$ 是一个环，其中对某个素数 $p$ 有 $p = 0$。则对任意 $a_1, dots.c, a_t in A$ 与 $m_1, dots.c, m_t >= 1$，映射：
  $
    Spec((A[T])/((T^(p^(m_1)) - a_1, dots.c, T^(p^(m_t)) - a_t))) -> Spec(A)
  $
  是有限泛同胚。
]
#proof[
  逐个添加根，不妨设 $t = 1$；每次只开一次 $p$ 次根，不妨设 $m_1 = 1$。于是只需证明：
  $
    phi: Spec(A[T]\/(T^p - a)) -> Spec(A)
  $
  是有限泛同胚。它有限，这可以直接看出。对每个点 $frak(p) in Spec(A)$，考虑纤维：
  $
    Spec(k(frak(p))[T]\/(T^p - a)) -> Spec(k(frak(p)))
  $
  现在：

  - 若 $a$ 在 $k(frak(p))$ 中有 $p$ 次根，则： #h(1fr)
    $
      k(frak(p))[T]\/(T^p - a) cong k(frak(p))[T]\/((T - a^(1\/p))^p)
    $
    它对应单个非既约的点，剩余域为 $k(frak(p))$。否则，$k(frak(p))[T]\/(T^p - a)$ 是 $k(frak(p))$ 的纯不可分扩张。

    于是 $phi$ 的每个纤维非空，故 $phi$ 满射。$phi$ 的每个纤维还都是单点，且剩余域扩张为纯不可分，所以由 @equiv-defns-of-radicial (2) 知 $phi$ 根性。
]
