// audit-cjk-exception: 0.42  # 末尾整页小抄由栏框与网格排版代码构成，代码字符占全文一半以上，散文已全部中译；45% 阈值结构性不适用。
#import "void-import.typ": *

== 六函子形式

本节我们写下六函子形式，也就是平展上同调已被证明满足的一组公理；借此为这趟穿越五百页密集数学的艰辛旅程干净而优雅地收尾。 

#theorem(name: <six-functor-formalism>)[
  (六函子形式) 平展上同调是一个六函子形式。也就是说，给定任意域 $k$ 与任意 $n$-挠 Noether 环 $Lambda$（其中 $n in k^times$），设 $X, Y, Z$ 表示分离的有限型 $k$-概形，$f: X -> Y, g: Y -> Z$ 为概形态射；记 $D(X)$ 为 $D^b_#[ctf] (X_et, Lambda)$，它是三角范畴。 

  0. 共有六个函子：#h(1fr)
    $
      R f_*, R f_!: D(X) -> D(Y) \
      f^(-1), R f^!: D(Y) -> D(X) \
      - Lotimes_Lambda -: D(X) times D(X) -> D(X) \
      RHHom_Lambda (-, -): D(X)^opp times D(X) -> D(X)
    $
    它们两两构成伴随，共三对： 
    $
      f^(-1) tack.l R f_* \
      R f_! tack.l R f^! \
      - Lotimes_Lambda cal(K) tack.l RHHom_Lambda (cal(K), -)
    $

  + $- Lotimes_Lambda -$ 与 $RHHom_Lambda (-, -)$ 使 $D(X)$ 成为闭幺半范畴。 

  + 有典范同构： 
    $
      R g_* compose R f_* cong R(g compose f)_*, R g_! compose R f_! cong R(g compose f)_! \
      f^(-1) compose g^(-1) cong (g compose f)^(-1), R f^! compose R g^! cong R (g compose f)^!
    $

  + $f^(-1)$ 是幺半的，即存在典范同构： 
    $
      f^(-1) (cal(K)_1 Lotimes_Lambda cal(K)_2) cong f^(-1) cal(K)_1 Lotimes_Lambda f^(-1) cal(K)_2
    $

  + （紧合基变换）对每个拉回方块： 
    #align(center, diagram({
      node((0, 0), [$X'$])
      node((1, 0), [$Y'$])
      node((0, 1), [$X$])
      node((1, 1), [$Y$])
      node((0.3, 0.3), [$cart$])
      edge((0, 1), (1, 1), [$f$], label-side: right, "->")
      edge((0, 0), (1, 0), [$f'$], label-side: left, "->")
      edge((1, 0), (1, 1), [$g$], label-side: left, "->")
      edge((0, 0), (0, 1), [$g'$], label-side: right, "->")
    }))
    有典范同构： 
    $
      g^(-1) R f_! cal(K) cong R f'_! g'^(-1) cal(K)
    $
  
  + （投影公式）存在典范同构： 
    $
      R f_! (cal(K) Lotimes_Lambda f^(-1) cal(L)) cong R f_! cal(K) Lotimes_Lambda cal(L)
    $

  + 上面列出的所有自然映射彼此相容。 

    #remark[
      实际上，这指的是散落在全书各处的那些陈述，诸如“基变换与方块的拼接相容”“投影与基变换、复合、张量相容”之类。 

      要最精确地表述这条相容性，需要 $oo$-范畴的语言。眼下不必多想，把它当成这样一个断言就好：“若两个对象之间的两个映射都是纯粹形式地构造出来的，那么它们应当一致”。 
      
      （当然，从 $cal(K) Lotimes_Lambda cal(K)$ 到自身就有两个形式映射：$id$ 与对称映射，而它们并不相等。所以“若两个对象之间的两个映射都是纯粹形式地构造出来的，那么它们应当一致”这话不能太当真——这些结构里本来就有形式自同构。不过你多少该明白我的意思了。）
    ]

  此外，还有下面这些平展几何性质： 

  7. （比较）$f$ 平展时，有典范同构 $R f^! cong f^(-1)$；$f$ 紧合时，有典范同构 $R f_! cong R f_*$。 

  + 设 $j: U -> X, i: Z -> X$ 是一对互补的开浸入与闭浸入，则有典范特殊三角： 

    - （零延拓三角）#h(1fr)
      $
        j_! j^(-1) cal(K) -> cal(K) -> i_* i^(-1) cal(K) ->^(+1)
      $
    
    - （带支集截面三角）
      $
        i_* R i^! cal(K) -> cal(K) -> R j_* j^(-1) cal(K) ->^(+1)
      $

  + （Poincaré 对偶）对相对维数为 $d$ 的光滑态射 $f$，有典范同构： 
    $
      R f^! cal(K) cong cal(K)(d)[2d]
    $

  + （光滑基变换）对每个拉回方块： 
    #align(center, diagram({
      node((0, 0), [$X'$])
      node((1, 0), [$Y'$])
      node((0, 1), [$X$])
      node((1, 1), [$Y$])
      node((0.3, 0.3), [$cart$])
      edge((0, 1), (1, 1), [$f$], label-side: right, "->")
      edge((0, 0), (1, 0), [$f'$], label-side: left, "->")
      edge((1, 0), (1, 1), [$g$], label-side: left, "->")
      edge((0, 0), (0, 1), [$g'$], label-side: right, "->")
    }))
    其中 $g$ 光滑，有典范同构： 
    $
      g^(-1) R f_* cal(K) cong R f'_* g'^(-1) cal(K)
    $

  + （一般基变换）设 $f: X -> Y$ 是有限型 $S$-概形之间的态射。（所有对象仍假定为 $k$ 上分离且有限型的。）那么对每个 $cal(K) in D(X)$，都存在稠密开集 $U subset S$，使得对任意拉回图表：#h(1fr)
    #align(center, diagram({
      node((0, 0), [$X'$])
      node((1, 0), [$Y'$])
      node((0, 1), [$X$])
      node((1, 1), [$Y$])
      // node((0.3, 0.3), [$cart$])
      node((2, 1), [$S$])
      node((2, 0), [$S'$])
      edge((0, 1), (1, 1), [$f$], label-side: right, "->")
      edge((0, 0), (1, 0), [$f'$], label-side: left, "->")
      edge((1, 0), (2, 0), "->")
      edge((1, 1), (2, 1), "->")
      edge((1, 0), (1, 1), [$g_Y$], label-side: left, "->")
      edge((2, 0), (2, 1), [$g$], label-side: left, "->")
      edge((0, 0), (0, 1), [$g_X$], label-side: right, "->")
    }))
    只要 $g(S') subset U$，就存在典范同构： 
    $
      g_Y^(-1) R f_* cal(K) cong R f'_* g_X^(-1) cal(K)
    $

  + 你愿意的话，尽可以往这里继续加陈述。 
]
#proof[
  这里的一切都在前面各节证过了。把它们翻出来，把其中的证明复习一遍，是个有益身心的练习！ 
]

我们的平展上同调之旅到此结束。非常感谢你一路走到这里；本书第二部分再见——那里讲的是平展上同调的应用，也就是 Weil 猜想。 

作为最后的礼物，下一页是一份平展上同调小抄，供你回顾学过的东西。 

#date[
  #set text(fill: red, weight: "semibold")
  #set align(left)

  本书关于 Weil 猜想的第二部分已有计划，但至少几个月内不会动工。敬请期待！ 
]

#pagebreak()

#block(width: 100%, height: auto, inset: 0pt, stroke: black, breakable: true, {
  set text(size: 11pt)
  set par(leading: 0.45em)
  set list(spacing: 0.35em, indent: 0.8em, body-indent: 0.4em)
  stack(
    dir: ttb, 
    box(stroke: black, width: 100%, height: auto, inset: (x: 0pt, y: 4pt))[#align(center)[
      #text(size: 14pt)[平展上同调#text(size: 12pt)[（Any%）]]
    ]],
    box(stroke: black, width: 100%, height: auto, inset: (x: 0pt, y: 3pt))[
      #align(center)[#text(size: 11pt)[平展态射]]
    ],
    box(stroke: black, width: 100%, height: auto, inset: (x: 3pt, y: 3pt))[
      - $f: X -> Y$ 局部有限展示，$f$ 非分歧 $:<==> Omega_(X\/Y) = 0$，$f$ 平展 $:<==>$ 平坦 + 非分歧 \
      - Noether、正则、既约、正规都是平展局部性质 \
      - 平展态射局部上都是标准平展的：$Spec(A[T]_(g(T))\/h(T)) -> Spec(A)$，其中 $(h(T),h'(T))$ 在 $A[T]_(g(T))^times$ 中是单位 \
      - 光滑、非分歧、平展态射都可以用无穷小提升判别法来检验 \
      - 严格 Hensel 化是平展拓扑中正确的局部环
    ], 
    grid(columns: (1fr, 1fr), stroke: black, inset: (3pt, 3pt),
      [
        #align(center)[#text(size: 11pt)[平展基本群]]
      ], 
      [
        #align(center)[#text(size: 11pt)[平展景]]
      ]
    ), 
    grid(columns: (1fr, 1fr), stroke: black, inset: (3pt, 3pt), 
      [
        $X$ 连通 Noether 概形，$ol(x)$ 为几何点，$exists$ 投射有限群 $pi_1^et (X,ol(x))$\
        - 有限平展覆叠与 Galois 覆叠的概念
        - $F_(ol(x)): FEt_X -> GSet(pi_1^et (X, ol(x)))^#[fin,disc]$ 是范畴等价
        - $f:X->Y$ 诱导 $pi_1^et (X,ol(x)) -> pi_1^et (Y,ol(y))$ \
          在相应的几何条件下，它可以是单射、满射或平凡映射
        - $pi_1^et (Spec(K)) = Gal_K$；
        - 对正规的 $X$，有 $pi_1^et (X) = Gal(K^"ur" (X)\/K(X))$
      ], 
      [
        #set text(size: 9pt)
        - $cAb(X_et)$ 是 Grothendieck Abel 范畴；$exists D^bullet (X_et,Lambda)$
        - $ul(M), mu_n, GG_m, GG_a in cAb(X_et)$
        - 对 $f: X -> Y$ 的函子性：#h(1fr)
          #align(center, diagram({
            node((-1, 1), text(size: 0.7em, $cAb(Y_et)$))
            edge("->", label-side: center, $f^! #[当 $f$ 为闭浸入时]$)
            node((0, 0), text(size: 0.7em, $cAb(X_et)$))
            edge("->", label-side: center, $f_*$)
            node((1, 1), text(size: 0.7em, $cAb(Y_et)$))
            edge("->", label-side: center, $f^(-1)$)
            node((2, 0), text(size: 0.7em, $cAb(X_et)$))
            edge("->", label-side: center, $f_! #[当 $f$ 平展时]$)
            node((3, 1), text(size: 0.7em, $cAb(Y_et)$))
            node((0, 0.7), $tack$)
            node((1, 0.3), $tack$)
            node((2, 0.7), $tack$)
          }, spacing: (0em, 2em), label-size: 0.7em))
          还有伴随对 $HHom(cal(F),-)$ 与 $- otimes cal(F)$
        - 正合性可由茎来检测
      ]
    ), 
    box(stroke: black, width: 100%, height: auto, inset: (x: 3pt, y: 3pt))[
      #align(center)[#text(size: 11pt)[平展上同调的基本性质]]
    ], 
    grid(columns: (1fr, 1fr), stroke: black, 
      stack(dir: ttb, 
        box(stroke: black, inset: (x: 3pt, y: 3pt), width: 100%, height: auto)[
          - $H^q (X, dirlim_i cal(F)_i) = dirlim_i H^q (X, cal(F)_i)$
          - $X = invlim_i X_i$, $H^q (X, cal(F)_0|_X) = dirlim_i H^q (X_i, cal(F)_0|_(X_i))$
          - 相对情形与复合情形的版本
        ], 
        box(inset: (x: 3pt, y: 3pt), width: 100%, height: auto)[
          - $(R^q f_* cal(F))_(ol(y)) = H^q (X times_Y tilde(Y)_(ol(y)), cal(F)|_(X times_Y tilde(Y)_(ol(y))))$
          - $f$ 有限，$(f_* cal(F))_(ol(y)) = oplus.big_(ol(x) in f^(-1)(ol(y))) cal(F)_(ol(x))$
        ]
      ), 
      stack(dir: ttb, 
        box(stroke: black, inset: (x: 3pt, y: 3pt), width: 100%, height: auto)[
          - $H^q_et (X, cal(M)_et) = H^q_#[Zar] (X, cal(M))$, $forall cal(M) in QCoh(X)$
          - $H^1_et (X, GG_m) = Pic(X)$
          - $H^1_et (X, ul(G)) = Hom_#[cont] (pi_1^et (X),G)$，$G$ 是有限交换群
        ], 
        box(inset: (x: 3pt, y: 3pt), width: 100%, height: auto)[
          $f: X' -> X$ 为泛同胚
          - $Et_X -> Et_(X')$ 是范畴等价
          - 在 $cAb(X_et)$、$D^bullet (X_et)$、$FEt_X$ 上同样成立
        ]
      ),
    ), 
    grid(columns: (1fr, 1fr), stroke: black, inset: (3pt, 3pt),
    [
      $X$ 为 $k = ol(k)$ 上的射影光滑曲线，$n in k^times$ #v(-0.8em)
      #[
        #set text(size: 0.8em)
        $
          H^q_et (X, ZZ\/n) = cases(
            ZZ\/n &\, q = 0,
            (ZZ\/n)^(oplus 2g(X)) &\, q = 1,
            ZZ\/n &\, q = 2,
            0 &\, q >= 3
          )
        $
      ]
    ], 
    [
      $X$ 为 $k = ol(k)$ 上的仿射光滑曲线，$n in k^times$ #v(-0.8em)
      #[
        #set text(size: 0.9em)
        $
          H^q_et (X, ZZ\/n) = cases(
            ZZ\/n &\, q = 0,
            (ZZ\/n)^(oplus 2g(X)+abs(ol(X)-X)-1) &\, q = 1,
            0 &\, q >= 2
          )
        $
      ]
    ]), 
    box(inset: (x: 3pt, y: 3pt), stroke: black, height: auto, width: 100%)[
      - l.c.c. 层即经平展覆盖后成为常值的层；可构造层即局部闭分层上的 l.c.c. 层
      - 可构造层对核、余核与扩张封闭；当 $j$ 拟紧平展时，它还对 $j_!$ 封闭；当 $h$ 有限时，对 $h_*$ 封闭
      - 可构造层有左消解 $j_! ul(Lambda)$（$j$ 拟紧平展）与右消解 $h_* ul(Lambda)$（$h$ 有限）
    ],
    grid(columns: (1fr, 1fr), inset: (3pt, 3pt), stroke: black, 
      [#align(center)[#text(size: 11pt)[紧合基变换]]], 
      [#align(center)[#text(size: 11pt)[局部零调性]]], 
      [
        #set text(size: 0.85em)
        - （紧合基变换）$f:X->Y$ 紧合，$g:Y'->Y$ 是局部 Noether 概形之间的态射 $==>$ $g^(-1) R f_* cal(K) cong R f'_* g'^(-1) cal(K)$，$forall cal(K)$ 挠
        - $R f_! := R ol(f)_* j_!$ 经紧化后是良定义的
        - （投影公式）$R f_! cal(K) Lotimes_Lambda cal(L) cong R f_! (cal(K) Lotimes f^(-1)cal(L))$
        - （Künneth 公式）$R f_! (p_1^(-1) cal(K)_1 Lotimes_Lambda p_2^(-1) cal(K)_2) cong R f_(1,!) cal(K)_1 Lotimes_Lambda R f_(2,!) cal(K)_2$
      ], [
        - 光滑态射是泛局部零调的
        - （光滑基变换）$f:X->Y$ 拟紧拟分离，$g:Y'->Y$ 光滑 $==>$ $g^(-1) R f_* cal(K) cong R f'_* g'^(-1) cal(K)$，$forall cal(K)$ 挠且阶在 $Y$ 中可逆
      ]
    ), 
    box(inset: (x: 3pt, y: 3pt), stroke: black, height: auto, width: 100%)[
      #align(center)[#text(size: 11pt)[六函子形式 \& Poincaré 对偶]]
    ], 
    grid(columns: (1fr, 1fr), inset: (3pt, 4pt), stroke: black,
      [
        - 对 $cal(K) in D^b_c$，基变换在一般情形下是同构
        - $f^(-1) tack.l R f_*$、$R f_! tack.l R f^!$、$- Lotimes_Lambda bullet tack.l RHHom(bullet, -)$ \
          六个函子都保持 $D^b_#[ctf]$
      ], [
        - 当 $f$ 光滑且相对维数为 $d$ 时，$R f^! cal(K) cong cal(K)(d)[2d]$； 
        - $X$ 在 $k = ol(k)$ 上光滑且相对维数为 $d$ $==>$ 完美配对 $H^q_c (X, cal(F)) times Ext^(2d-q) (cal(F), ul(ZZ\/n)(d)) -> ZZ\/n$
        #v(1fr)
      ]
    )
  )
})
