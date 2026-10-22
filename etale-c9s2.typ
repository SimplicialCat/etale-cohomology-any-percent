// audit-exception: 展示公式内的 #[...] 文字块内嵌两段 $Lambda$，审计按相邻美元符号配对会把块内散文切成伪公式段；翻译该文字块必然改变数学指纹，块内公式与其余数学均未改动。
#import "void-import.typ": *

== Poincaré 对偶

本节我们证明平展上同调的 Poincaré 对偶，并顺带把纯性定理作为应用证出来。但在此之前，先要为它找到正确而尽可能一般的陈述。

#definition(name: <defn-cup-product-pairing>)[
  设 $X$ 是代数闭域 $k$ 上维数为 $d$ 的光滑概形，$Lambda$ 是 $n$-挠 Noether 环，且 $n in k^times$。对复形 $cal(K) in D(X_et, Lambda)$，
  $
    h^(2d-q) (RHom_Lambda (cal(K), ul(Lambda)(d))) = Hom_(D(X_et,Lambda)) (cal(K)[q], mu_n^(otimes d) [2d])
  $
  于是 $h^(2d-q)(RHom_Lambda (cal(K), Lambda(d)))$ 的每个元素都诱导一个态射：
  $
    R Gamma_c (X, cal(K))[q] -> R Gamma_c (X, ul(Lambda))(d)[2d] -->^(Tr_(X\/k)) Lambda
  $
  这是复形之间的态射；从而作为交换群有 $h^q (R Gamma_c (X, cal(K))) -> Lambda$。于是我们得到 $Lambda$-双线性配对：
  $
    smile: h^q (R Gamma_c (X, cal(K))) times h^(2d-q) (RHom_Lambda (cal(K), ul(Lambda)(d))) -> Lambda
  $
  称为*杯积配对*。特别地，对层 $cal(F) in cAb(X_et, Lambda)$，有*杯积配对*：
  $
    smile: H^q_c (X, cal(F)) times Ext^(2d-q)_Lambda (cal(F), ul(Lambda)(d)) -> Lambda
  $
]

特别地，若 $cal(F)$ 是 $Lambda$-模的 l.c.c. 层，则 $p>0$ 时 $EExt^p (cal(F), Lambda(d)) = 0$；于是由 Hochschild–Serre 谱序列，$Ext^(2d-q)_Lambda (cal(F), Lambda(d)) = H^(2d-q) (X, caron(cal(F))(d))$，其中 $caron(cal(F)) = HHom_Lambda (cal(F), Lambda)$。这时就得到经典的 Poincaré 对偶：
$
  smile: H^q_c (X, cal(F)) times H^(2d-q) (X, caron(cal(F))(d)) -> Lambda
$
是完美配对。

#construction(name: <constr-pd-relative-to-absolute>)[
  设 $k$ 是代数闭域，$Lambda$ 是 $n$-挠 Noether 环，满足 $n in k^times$，且 $Lambda$ 是内射 $Lambda$-模。 

  设 $X$ 是维数为 $d$ 的光滑 $k$-概形，$g: X -> Spec(k)$ 是结构态射。我们要证明：
  $
    h^(2d-q) (RHom_Lambda (cal(K), ul(Lambda)(d))) -> Hom_Lambda (h^q (R Gamma_c (X, cal(K))), Lambda)
  $
  是同构。现在：
  $
    h^(2d-q) (RHom_Lambda (cal(K), ul(Lambda)(d))) = Hom_Lambda (cal(K)[q], ul(Lambda)(d)[2d])
  $
  另一方面：
  $
    Hom_Lambda (R g_! cal(K)[q], ul(Lambda)) &= Hom_Lambda (R Gamma_c (X, cal(K))[q], Lambda) \
    &= Hom_Lambda (h^q (R Gamma_c (X, cal(K))), Lambda) #[因为 $Lambda$ 是内射 $Lambda$-模]
  $
  因此，我们真正要证明的是：下述映射是同构。
  $
    Hom_Lambda (R g_! cal(K), ul(Lambda)) cong Hom_Lambda (cal(K), ul(Lambda)(d)[2d])
  $
  这个映射由迹映射诱导：
  $
    Hom_Lambda (R g_! cal(K), ul(Lambda)) -->^(Tr_(X\/k)) Hom_Lambda (cal(K)(-d)[-2d], ul(Lambda)) = Hom_Lambda (cal(K), ul(Lambda)(d)[2d])
  $

  这个同构的形状强烈暗示：$R g_!$ 存在右伴随 $R g^!: D(Spec(k)_et, Lambda) -> D(X_et, Lambda)$，并且有一个等同：
  $
    R g^! ul(Lambda) cong ul(Lambda)(d)[2d]
  $
  它由伴随性经迹映射诱导。
]

上述构造提示我们，相对情形下 Poincaré 对偶正确而最一般的陈述应当是什么样子：

- #h(1fr)
  $
    R f^! cal(K) cong f^(-1) cal(K)(d)[2d]
  $
  它对 Noether 概形之间任意相对维数为 $d$ 的光滑态射 $f: X -> Y$ 成立，其中 $R f^!$ 是 $R f_!$ 的某个右伴随。

于是我们希望为任意 Noether 概形之间分离的有限型态射 $f: X -> Y$，找到 $R f_!$ 的右伴随 $R f^!$。构造 $R f^!$ 的核心工具是 Brown 可表示性定理 @brown-representability。

#theorem(name: <existence-of-upper-shriek>)[
  设 $Lambda$ 是任意挠环。

  对 Noether 概形之间任意分离的有限型态射 $f: X -> Y$，$R f_!: D(X_et, Lambda) -> D(Y_et, Lambda)$ 有三角右伴随 $R f^!$，并且存在典范自然同构： 

  0. 对分离的平展态射 $f: X -> Y$，
    $
      R f^! cong f^(-1)
    $
    对闭浸入 $i: Z -> X$，$R i^!$ 自然同构于 @closed-immersion-upper-shriek-constr 中定义的函子 $i^!$ 的导出函子。

  + (复合) #h(1fr)
    $
      R f^! compose R g^! cong R(g compose f)^!
    $

  + (紧合基变换的伴随) 在拉回图表中：
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
    我们有：
    $
      R f^! compose R g_* cong R g'_* compose R f'^!
    $

  + (投影公式的伴随) 对任意 $cal(L) in D(Y_et, Lambda)$：
    $
      R f^! RHHom_Lambda (cal(L), -) cong RHHom_Lambda (f^(-1) cal(L), R f^! (-))
    $

  + (内部伴随) 对任意 $cal(K) in D(X_et, Lambda), cal(L) in D(Y_et, Lambda)$： 
    $
      RHHom_Lambda (R f_! cal(K), cal(L)) cong R f_* RHHom_Lambda (cal(K), R f^! cal(L))
    $
]
#proof[
  假设已证明 $R f^!$ 存在。(1)(2)(3) 依次是复合、紧合基变换与投影公式对 $R f_!$ 的伴随形式，(0) 则来自层层面上的伴随：
  $
    f^(-1) tack.l f_* \
    i^! tack.l i_*
  $
  对 (4)，我们仿照 @derived-functoriality-etale 中 (3) 的证法：应用 $R Gamma$ 并取复形的上同调，归约到范畴里的 $Hom$。  


  因此只需证明右伴随 $R f^!$ 存在。

  为此应用 Brown 可表示性定理 @brown-representability：只要 $R f_!$ 保持任意直和，右伴随 $R f^!$ 就存在。于是只需证明 $R f_!$ 保持任意直和。设 $f$ 的纤维维数 $<=d$，从而 $R f_!$ 的上同调维数有上界 $<=2d$。任取一族复形 $cal(K)_i in D(X_et, Lambda)$。对固定的 $q$，要证：
  $
    h^q (R f_! (oplus.big_i cal(K)_i)) cong oplus.big_i h^q (R f_! cal(K)_i)
  $
  取截断：
  $
    tau_(<=q-2d-1) cal(K)_i -> cal(K)_i -> tau_(>=q-2d) cal(K)_i ->^(+1)
  $
  这给出特殊三角 $oplus.big_i tau_(<=q-2d-1) cal(K)_i -> oplus.big_i cal(K)_i -> oplus.big_i tau_(>=q-2d) cal(K)_i ->^(+1)$。现在：

  - 由于 $R f_!$ 的上同调维数有上界 $<=2d$，对任意复形 $cal(L) in D_(<=q-2d-1)$，有 $R f_! cal(L) in D_(<=q-1)$，且其 $h^q, h^(q+1)$ 消没。

  于是得到同构：
  $
    h^q (R f_! (oplus.big_i cal(K)_i)) cong h^q (R f_! (oplus.big_i tau_(>=q-2d) cal(K)_i)) \
    h^q (R f_! cal(K)_i) cong h^q (R f_! (tau_(>=q-2d) cal(K)_i))
  $
  于是把 $cal(K)_i$ 换为 $tau_(>=q-2d)$ 后，可以假定存在固定的 $a in ZZ$，使每个 $cal(K)_i in D_(>=a) (X_et, Lambda)$。同样，由于 $R f_!$ 在低于 $0$ 的次数上消没，我们可以作上方截断，并假定存在固定的 $a, b in ZZ$，使每个 $cal(K)_i in D_([a,b]) (X_et, Lambda)$。接下来，对 $cal(L) in D_([a,b]) (X_et, Lambda)$ 有截断：
  $
    tau_(<=a) cal(L) -> cal(L) -> tau_(>=a+1) cal(L) ->^(+1)
  $
  其中 $tau_(>=a+1) cal(L) in D_([a+1,b]) (X_et,Lambda)$，而 $tau_(<=a) cal(L)$ 集中在次数 $a$ 上。于是对 $b-a$ 归纳并用五引理，可以假定所有 $cal(K)_i$ 都集中在同一个次数 $a in ZZ$ 上，即都是层 $cal(F)_i in cAb(X_et, Lambda)$。这样只需证明：
  $
    R^q f_! (oplus.big_i cal(F)_i) cong oplus.big_i R^q f_! cal(F)_i
  $
  取 $f$ 的一个紧化 $X ->^j ol(X) ->^(ol(f)) Y$，使 $R^q f_! cong R^q ol(f)_* j_!$。由于 $j_!$ 是左伴随，它保持直和；而由极限公式 @relative-limit-formula-for-sheaves，$R ol(f)_*$ 保持直和。至此证毕。
]

#construction(name: <purity-map>)[
  设 $Lambda$ 是 $n$-挠 Noether 环，$f: X -> Y$ 是 Noether $ZZ[n^(-1)]$-概形之间分离、光滑、相对维数为 $d$ 的态射。则迹映射：
  $
    Tr_(X\/Y): R f_! f^(-1) cal(K)(d)[2d] -> cal(K)
  $
  经伴随性诱导出一个映射：
  $
    t_(X\/Y): f^(-1) cal(K)(d)[2d] -> R f^! cal(K)
  $
  对一切 $cal(K) in D(Y_et, Lambda)$，我们称上述映射为*纯性映射* (purity map)。纯性映射与复合相容，因为迹映射与复合相容。
]

下面说明证明 Poincaré 对偶的总体策略。我们要充分利用纯性映射与复合的相容性。对任意光滑态射 $f: X -> Y$，后文会看到：要证 $t_(X\/Y)$ 是同构，只需在 $X$ 上平展局部地处理。于是可以假定 $f$ 分解为 $f: X -> AA^d_Y ->^p Y$，其中 $X -> AA^d_Y$ 平展。平展态射的纯性映射是恒等映射，因此只需证明纯性映射：
$
  t_(AA^d_Y\/Y): p^(-1) cal(K)(d)[2d] -> R p^! cal(K)
$
是同构。再把 $AA^d_Y -> Y$ 进一步分解为：
$
  AA^d_Y -> AA^(d-1)_Y -> dots.c -> AA^1_Y -> Y
$
便可假定 $d = 1$，只需处理 $p: AA^1_Y -> Y$ 这一情形。于是 Poincaré 对偶的核心，就是证明纯性映射：
$
  t_(AA^1_Y\/Y): p^(-1) cal(K)(1)[2] -> R p^! cal(K)
$
对一切 $cal(K) in D(Y_et, Lambda)$ 都是同构。

为此，我们需要先建立 Gysin 纯性的一个特殊情形。

#lemma(name: <etale-a1-homotopy-invariance>)[
  ($AA^1$-同伦不变性) 设 $Y$ 是 Noether $ZZ[n^(-1)]$-概形，$p: AA^1_Y -> Y$。则单位映射：
  $
    ul(ZZ\/n) -> R p_* ul(ZZ\/n)
  $
  是同构。
]
#proof[
  #lemma[
    若 $k$ 是可分闭域且 $n in k^times$，则有典范同构：
    $
      H^q (AA^1_k, ul(ZZ\/n)) cong cases(
        ZZ\/n & \, q = 0,
        0 & \, q >= 1
      )
    $
  ]
  #proof[
    由 Artin 消没，只需证明 $H^1 (AA^1_k, ul(ZZ\/n)) = 0$，等价地 $H^1 (AA^1_k, mu_n) = 0$。取 Kummer 序列诱导的长正合列： 
    $
      0 -> mu_n (k) -> k[t]^times ->^((-)^n) k[t]^times -> H^1 (AA^1_k, mu_n) -> Pic(AA^1_k) ->^((-)^n) Pic(AA^1_k)
    $
    此时 $k[t]^times = k^times$，而 $k$ 可分闭且 $n in k^times$，故 $(-)^n$ 在其上满射。因此 $H^1 (AA^1_k, mu_n) = ker((-)^n: Pic(AA^1_k) -> Pic(AA^1_k))$。 

    因此只需证明 $Pic(AA^1_k) = 0$。为了搞笑，我把这部分的证明扔进了脚注。请先自己想一会儿；实在想不出来，就去读脚注，乐一乐。#footnote[$k[t]$ 是主理想整环，其上的有限模有分类。其中唯一的秩 1 局部自由 $k[t]$-模就是 $k[t]$ 本身。如果这让你笑了，你可以拿这个谜题去逗逗朋友。]
  ]

  现在 $p$ 光滑，从而关于 $ul(ZZ\/n)$ 局部零调。要证单位映射 $ul(ZZ\/n) -> R p_* ul(ZZ\/n)$ 是同构，我们引用 @loc-acyc-constancy-of-pushforward，只需证明：
  $
    ZZ\/n -> R Gamma(AA^1_(ol(y)), ul(ZZ\/n))
  $
  对 $Y$ 的所有几何点 $ol(y)$ 都是同构。这由上一个引理可得。
]

#lemma(name: <p1-section-gysin-purity>)[
  ($PP^1$-截面的 Gysin 纯性) 设 $Y$ 是 Noether $ZZ[n^(-1)]$-概形，$p: PP^1_Y -> Y$，$i: Y -> PP^1_Y$ 是零截面。 

  存在唯一的态射 $c: i_* ul(ZZ\/n)_Y -> ul(ZZ\/n)_(PP^1_Y)(1)[2]$，使得复合：
  $
    ul(ZZ\/n)_(PP^1_Y) cong R p_* i_* ul(ZZ\/n)_Y -->^(R p_* (c)) R p_* ul(ZZ\/n)_(PP^1_Y)(1)[2] -->^(Tr_(PP^1_Y\/Y)) ul(ZZ\/n)_Y
  $
  是恒等映射。它与基变换相容。
]
#proof[
  先来确定 $R p_* ul(ZZ\/n)$。考虑迹映射：
  $
    Tr_(PP^1_Y\/Y): R p_* ul(ZZ\/n) -> ul(ZZ\/n)(-1)[-2]
  $
  另一方面，有伴随单位 $ul(ZZ\/n) -> i_(oo,*) ul(ZZ\/n)$。对其作用 $R p_*$，得到自然映射：
  $
    r_oo: R p_* ul(ZZ\/n) -> ul(ZZ\/n)
  $
  它与基变换相容。

  于是得到一个与基变换相容的映射：
  $
    T = (Tr_(PP^1_Y\/Y), r_oo): Tr_(PP^1_Y\/Y): R p_* ul(ZZ\/n) -> ul(ZZ\/n)(-1)[-2] oplus ul(ZZ\/n)
  $
  我们断言 $T$ 是同构。事实上，可以基变换到一个几何点，在茎上验证，从而假定 $Y = Spec(k)$ 是代数闭域的谱。此时 $Tr$ 在 $h^2$ 上诱导同构 $H^2 (PP^1_k, ul(ZZ\/n)) cong ZZ\/n(-1)$，$r_oo$ 在 $h^0$ 上诱导同构 $H^0 (PP^1_k, ul(ZZ\/n)) cong ZZ\/n$，因此 $T$ 是同构。

  只需证明：
  $
    Phi: Hom_(ZZ\/n) (i_* ul(ZZ\/n)_Y, ul(ZZ\/n)_(PP^1_Y) (1)[2]) & -> Hom_(ZZ\/n) (ul(ZZ\/n)_Y, ul(ZZ\/n)_Y) \
                                                            gamma & |-> Tr_(PP^1_Y\/Y) compose R p_* (gamma)
  $
  是同构。取与 $i$ 互补的开浸入 $j: AA^1_Y -> PP^1_Y$，再取零延拓三角：
  $
    j_! ul(ZZ\/n)_(AA^1_Y) -> ul(ZZ\/n)_(PP^1_Y) -> i_* ul(ZZ\/n)_Y ->^(+1)
  $
  对其作用 $RHom_(ZZ\/n) (-, ul(ZZ\/n)_(PP^1_Y))$，得到特殊三角：
  $
    RHom_(ZZ\/n) (i_* ul(ZZ\/n)_Y, ul(ZZ\/n)_(PP^1_Y)) ->^Q R Gamma(PP^1_Y, ul(ZZ\/n)) ->^res R Gamma(AA^1_Y, ul(ZZ\/n)) ->^(+1)
  $
  可以作如下等同：

  - #h(1fr)
    $
      R Gamma(PP^1_Y, ul(ZZ\/n)) = R Gamma(Y, R p_* ul(ZZ\/n)) = RHom_(ZZ\/n) (ul(ZZ\/n)_Y, R p_* ul(ZZ\/n)_(PP^1_Y)) \
      R Gamma(AA^1_Y, ul(ZZ\/n)) = R Gamma(Y, R (p compose j)_* ul(ZZ\/n)) = RHom_(ZZ\/n) (ul(ZZ\/n)_Y, R (p compose j)_* ul(ZZ\/n)_(PP^1_Y))
    $
    在这些等同下，可以形式地验证：

    - $res$ 由伴随单位 $R p_* ul(ZZ\/n) -> R(p compose j)_* ul(ZZ\/n)$ 诱导。

    - $Q$ 由下式诱导：
      $
        RHom_(ZZ\/n) (i_* ul(ZZ\/n)_Y, ul(ZZ\/n)_(PP^1_Y)) -->^(R p_* (-)) RHom_(ZZ\/n) (R p_* i_* ul(ZZ\/n)_Y, R p_* ul(ZZ\/n)_(PP^1_Y)) = RHom_(ZZ\/n) (ul(ZZ\/n)_Y, R p_* ul(ZZ\/n)_(PP^1_Y))
      $

  - 现在有同构：
    $
      T: R p_* ul(ZZ\/n)_(PP^1_Y) -> ul(ZZ\/n)_Y (-1)[-2] oplus ul(ZZ\/n)_Y
    $
    如上所论证；以及：
    $
      R (p compose j)_* ul(ZZ\/n)_(AA^1_Y) -> ul(ZZ\/n)_Y
    $
    由 $AA^1$-同伦不变性 (@etale-a1-homotopy-invariance) 可得。我们断言：在这些等同下，单位映射 $R p_* ul(ZZ\/n) -> R(p compose j)_* ul(ZZ\/n)$ 与向第二个因子投影的映射 $ul(ZZ\/n)(-1)[-2] oplus ul(ZZ\/n) -> ul(ZZ\/n)$ 等同。为此需要验证下图交换：
    // https://q.uiver.app/#r=typst&q=WzAsMyxbMCwwLCJSIHFfKiB1bChaWlxcL24pXyhBQV4xX1kpIl0sWzIsMCwidWwoWlpcXC9uKV9ZIl0sWzAsMSwiUiBwXyogdWwoWlpcXC9uKV8oUFBeMV9ZKSJdLFsxLDAsInVfcSIsMl0sWzIsMCwiUiBxXyogKHVfaikiXSxbMiwxLCJSIHBfKiAodV8oaV9vbykpIiwyXV0=
    #align(center, diagram({
      node((0, 0), [$R q_* ul(ZZ\/n)_(AA^1_Y)$])
      node((2, 0), [$ul(ZZ\/n)_Y$])
      node((0, 1), [$R p_* ul(ZZ\/n)_(PP^1_Y)$])
      edge((2, 0), (0, 0), [$u_q$], label-side: right, "->")
      edge((0, 1), (0, 0), [$R q_* (u_j)$], label-side: left, "->")
      edge((0, 1), (2, 0), [$R p_* (u_(i_oo))$], label-side: right, "->")
    }))
    其中 $u_p, u_q, u_(i_oo)$ 是右伴随 $R p_*, R q_*, i_(oo,*)$ 的单位映射。这是形式性的。

  -
    $
      RHom_(ZZ\/n) (i_* ul(ZZ\/n)_Y, ul(ZZ\/n)_(PP^1_Y)) &->^Q R Gamma(PP^1_Y, ul(ZZ\/n)) cong RHom_(ZZ\/n) (ul(ZZ\/n)_Y, R p_* ul(ZZ\/n)_(PP^1_Y)) \
      &= RHom_(ZZ\/n) (ul(ZZ\/n)_Y, ul(ZZ\/n)_Y (-1)[-2] oplus ul(ZZ\/n)_Y) \
      &-> RHom_(ZZ\/n) (ul(ZZ\/n)_Y, ul(ZZ\/n)_Y (-1)[-2])
    $
    不过就是把 $Phi$ 再扭转 $(-1)[-2]$。事实上，如第一个要点所述，第一行与 $R p_* (-)$ 等同；第二、三行按定义由 $Tr_(PP^1_Y\/Y)$ 诱导。

    由特殊三角可知这个复合是同构：
    $
      RHom_(ZZ\/n) (i_* ul(ZZ\/n)_Y, ul(ZZ\/n)_(PP^1_Y)) ->^Q R Gamma(PP^1_Y, ul(ZZ\/n)) ->^res R Gamma(AA^1_Y, ul(ZZ\/n)) ->^(+1)
    $

    因此，$Phi: RHom_(ZZ\/n) (i_* ul(ZZ\/n)_Y (1)[2], ul(ZZ\/n)_(PP^1_Y)) -> RHom_(ZZ\/n) (ul(ZZ\/n)_Y, ul(ZZ\/n)_Y)$ 是同构。

  取 $h^0$，
  $
    Phi: Hom_(ZZ\/n) (i_* ul(ZZ\/n)_Y (1)[2], ul(ZZ\/n)_(PP^1_Y)) -> Hom_(ZZ\/n) (ul(ZZ\/n)_Y, ul(ZZ\/n)_Y)
  $
  是同构。取 $id$ 的原像，得到 $c: i_* ul(ZZ\/n)_Y (1)[2] -> ul(ZZ\/n)_(PP^1_Y)$。

  $Phi$ 的构造与基变换相容，因此 $c$ 的构造也与基变换相容。
  /*另外记 $i_oo: Y -> PP^1_Y$ 为无穷远截面。

  先来确定 $R p_* ul(ZZ\/n)$。考虑迹映射：
  $
    Tr_(PP^1_Y\/Y): R p_* ul(ZZ\/n) -> ul(ZZ\/n)(-1)[-2]
  $
  另一方面，有伴随单位 $ul(ZZ\/n) -> i_(oo,*) ul(ZZ\/n)$。对其作用 $R p_*$，得到自然映射：
  $
    r_oo: R p_* ul(ZZ\/n) -> ul(ZZ\/n)
  $
  它与基变换相容。

  于是得到一个与基变换相容的映射：
  $
    Phi = (Tr_(PP^1_Y\/Y), r_oo): Tr_(PP^1_Y\/Y): R p_* ul(ZZ\/n) -> ul(ZZ\/n)(-1)[-2] oplus ul(ZZ\/n)
  $
  我们断言 $Phi$ 是同构。事实上，可以基变换到一个几何点，在茎上验证，从而假定 $Y = Spec(k)$ 是代数闭域的谱。此时 $Tr$ 在 $h^2$ 上诱导同构 $H^2 (PP^1_k, ul(ZZ\/n)) cong ZZ\/n(-1)$，$r_oo$ 在 $h^0$ 上诱导同构 $H^0 (PP^1_k, ul(ZZ\/n)) cong ZZ\/n$，因此 $Phi$ 是同构。

  设 $j: AA^1_Y -> PP^1_Y$ 是包含映射，$q: AA^1_Y -> Y$ 是投影。

  写出带支集截面三角：
  $
    i_* R i^! ul(ZZ\/n) -> ul(ZZ\/n) -> R j_* ul(ZZ\/n) ->^(+1)
  $
  对其作用 $R p_*$，得到特殊三角：
  $
    R i^! ul(ZZ\/n) ->^g R p_* ul(ZZ\/n) ->^h R q_* ul(ZZ\/n) ->^s_(+1)
  $
  - 在这个三角中我们知道：#h(1fr)
    $
      R p_* ul(ZZ\/n) cong ul(ZZ\/n)(-1)[-2] oplus ul(ZZ\/n) \
    $
    如刚才所论证；以及：
    $
      R q_* ul(ZZ\/n) cong ul(ZZ\/n)
    $
    由 $AA^1$-同伦不变性 (@etale-a1-homotopy-invariance) 可得。我们断言：在这些等同下，$h$ 与向第二个因子投影的映射 $ul(ZZ\/n)(-1)[-2] oplus ul(ZZ\/n) -> ul(ZZ\/n)$ 等同。为此需要验证下图交换：
    // https://q.uiver.app/#r=typst&q=WzAsMyxbMCwwLCJSIHFfKiB1bChaWlxcL24pXyhBQV4xX1kpIl0sWzIsMCwidWwoWlpcXC9uKV9ZIl0sWzAsMSwiUiBwXyogdWwoWlpcXC9uKV8oUFBeMV9ZKSJdLFsxLDAsInVfcSIsMl0sWzIsMCwiUiBxXyogKHVfaikiXSxbMiwxLCJSIHBfKiAodV8oaV9vbykpIiwyXV0=
    #align(center, diagram({
      node((0, 0), [$R q_* ul(ZZ\/n)_(AA^1_Y)$])
      node((2, 0), [$ul(ZZ\/n)_Y$])
      node((0, 1), [$R p_* ul(ZZ\/n)_(PP^1_Y)$])
      edge((2, 0), (0, 0), [$u_q$], label-side: right, "->")
      edge((0, 1), (0, 0), [$R q_* (u_j)$], label-side: left, "->")
      edge((0, 1), (2, 0), [$R p_* (u_(i_oo))$], label-side: right, "->")
    }))
    其中 $u_p, u_q, u_(i_oo)$ 是右伴随 $R p_*, R q_*, i_(oo,*)$ 的单位映射。这是形式性的。

  于是得到典范映射：
  $
    alpha: R i^! ul(ZZ\/n) ->^g R p_* ul(ZZ\/n) cong ul(ZZ\/n)(-1)[-2] oplus ul(ZZ\/n) -> ul(ZZ\/n)(-1)[-2]
  $
  上面的特殊三角使 $alpha$ 成为同构。于是它诱导自然映射：
  $
    beta: i_* ul(ZZ\/n) -> ul(ZZ\/n)(1)[2]
  $

  下面证明这个映射在基变换下保持，并在 $Y = Spec(k)$（$k$ 为代数闭域）的情形给出它的显式描述。 */
]

#lemma(name: <a1-section-gysin-purity>)[
  ($AA^1$-截面的 Gysin 纯性) 设 $Y$ 是 Noether $ZZ[n^(-1)]$-概形，$p: AA^1_Y -> Y$，$i: Y -> AA^1_Y$ 是零截面。 

  存在唯一的态射 $c: i_* ul(ZZ\/n)_Y -> ul(ZZ\/n)_(AA^1_Y)(1)[2]$，使得复合：
  $
    ul(ZZ\/n)_(AA^1_Y) cong R p_! i_* ul(ZZ\/n)_Y -->^(R p_! (c)) R p_! ul(ZZ\/n)_(AA^1_Y)(1)[2] -->^(Tr_(AA^1_Y\/Y)) ul(ZZ\/n)_Y
  $
  是恒等映射。它与基变换相容。
]
#proof[
  与 $PP^1_Y$ 的情形类似，只需证明：
  $
    Phi: Hom_(ZZ\/n) (i_* ul(ZZ\/n)_Y, ul(ZZ\/n)_(AA^1_Y) (1)[2]) & -> Hom_(ZZ\/n) (ul(ZZ\/n)_Y, ul(ZZ\/n)_Y) \
                                                            gamma & |-> Tr_(AA^1_Y\/Y) compose R p_! (gamma)
  $
  是同构。取紧化 $AA^1_Y ->^j PP^1_Y ->^(ol(p)) Y$ 与零截面 $ol(i): Y -> PP^1_Y$，并令 $i_oo: Y -> PP^1_Y$ 是 $oo$-截面。则（利用迹映射与复合的相容性）可以验证，复合：
  $
    Hom_(ZZ\/n) (i_* ul(ZZ\/n)_Y, ul(ZZ\/n)_(AA^1_Y) (1)[2]) &-->^(j_! (-)) Hom_(ZZ\/n) (ol(i)_* ul(ZZ\/n)_Y, j_! ul(ZZ\/n)_(AA^1_Y) (1)[2]) \
    &-->^(Tr_(AA^1_Y\/PP^1_Y)) Hom_(ZZ\/n) (ol(i)_* ul(ZZ\/n)_Y, ul(ZZ\/n)_(PP^1_Y) (1)[2]) \
    &-->^Phi Hom_(ZZ\/n) (ul(ZZ\/n)_Y, ul(ZZ\/n)_Y)
  $
  正是 @p1-section-gysin-purity 中为 $PP^1$ 情形构造的 $Phi$，我们把它记作 $Phi'$。于是由 @p1-section-gysin-purity，$Phi'$ 是同构。另一方面， 

  - 由伴随性，$Hom_(ZZ\/n) (cal(K), cal(L)) -->^(j_! (-)) Hom_(ZZ\/n) (j_! cal(K), j_! cal(L))cong Hom_(ZZ\/n) (cal(K), j^(-1) j_! cal(L)) cong Hom_(ZZ\/n) (cal(K), cal(L))$，故 $j_! (-)$ 总是同构。于是第一行是同构； 

  - 对第二行，有特殊三角：
    $
      RHom_(ZZ\/n) (ol(i)_* ul(ZZ\/n)_Y, j_! ul(ZZ\/n)_(AA^1_Y) (1)[2]) -->^(Tr_(AA^1_Y\/PP^1_Y)) RHom_(ZZ\/n) (ol(i)_* ul(ZZ\/n)_Y, ul(ZZ\/n)_(PP^1_Y) (1)[2]) -> RHom_(ZZ\/n) (ol(i)_* ul(ZZ\/n)_Y, i_(oo,*) ul(ZZ\/n)_Y) ->^(+1)
    $
    但 $ol(i), i_oo$ 的像不交，故 $RHom_(ZZ\/n) (ol(i)_* ul(ZZ\/n)_Y, i_(oo,*) ul(ZZ\/n)_Y) cong RHom_(ZZ\/n) (i_oo^(-1) ol(i)_* ul(ZZ\/n)_Y, ul(ZZ\/n)_Y) = 0$。因此 $Tr_(AA^1_Y\/PP^1_Y)$ 是同构： 
    $
      RHom_(ZZ\/n) (ol(i)_* ul(ZZ\/n)_Y, j_! ul(ZZ\/n)_(AA^1_Y) (1)[2]) -> RHom_(ZZ\/n) (ol(i)_* ul(ZZ\/n)_Y, ul(ZZ\/n)_(PP^1_Y) (1)[2])
    $
    取 $h^0$ 便可以把 $RHom$ 换成 $Hom$，从而断定第二行是同构。 

  于是 $Phi$ 是同构，证毕。 
]

现在可以证明 Poincaré 对偶了。 

#theorem(name: <a1-poincare-duality>)[
  ($AA^1$ 的 Poincaré 对偶) 设 $Lambda$ 是 $n$-挠 Noether 环，$Y$ 是 Noether $ZZ[n^(-1)]$-概形，$p: AA^1_Y -> Y$。则纯性映射： 
  $
    t_(AA^1_Y\/Y): p^(-1) cal(K)(1)[2] -> R p^! cal(K)
  $
  对一切 $cal(K) in D(Y_et, Lambda)$ 都是同构。 
]
#proof[
  $R p_!$ 并不在乎复形是 $Lambda$-模层复形还是遗忘到 $ZZ\/n$-模的复形（因为下星号 $R f_*$ 本来就不在乎）。因此不妨设 $Lambda = ZZ\/n$。 

  我们直接证明伴随： 
  $
    R p_! tack.l p^(-1) (-)(1)[2]
  $
  余单位映射自然就是迹映射： 
  $
    eta_Y = Tr_(AA^1_Y\/Y): R p_! p^(-1) cal(K) (1)[2] -> cal(K)
  $
  所以需要手工构造一个单位： 
  $
    u_Y: cal(L) -> p^(-1) R p_! cal(L)(1)[2]
  $
  构造如下： 

  - 取对角态射 $Delta: AA^1_Y -> AA^2_Y$ 与投影 $q_(1,2): AA^2_Y -> AA^1_Y$。在不同坐标下，$Delta$ 同时是 $q_1$ 与 $q_2$ 的零截面。于是由 @a1-section-gysin-purity，存在唯一的映射： 
    $
      c_Y: R Delta_* ul(ZZ\/n)_(AA^1_Y) -> ul(ZZ\/n)_(AA^2_Y) (1)[2]
    $
    使得复合： 
    $
      ul(ZZ\/n)_(AA^1_Y) cong R q_(i,*) Delta_* ul(ZZ\/n)_(AA^1_Y) -->^(R q_(i,*) c) R q_(i,*) ul(ZZ\/n)_(AA^2_Y)(1)[2] -->^(Tr_(q_i:AA^2_Y\/AA^1_Y)) ul(ZZ\/n)_(AA^1_Y)
    $
    对 $i=1,2$ 都是恒等映射。 

    又因 $q_(1,2) compose Delta = id$，有： 
    $
      cal(L) &cong R q_(2,!) R Delta_* cal(L) cong R q_(2,!) R Delta_* (Delta^(-1) q_1^(-1) cal(L)) \
      &cong R q_(2,!) (q_1^(-1) cal(L) Lotimes_(ZZ\/n) R Delta_* ul(ZZ\/n)) #[由投影公式] \
      &->^(c_Y) R q_(2,!) q_1^(-1) cal(L)(1)[2] \
      &cong R p_! p^(-1) cal(L)(1)[2] #[由紧合基变换]
    $
    这就是单位映射 $u_Y$。 

  剩下要验证伴随恒等式： 
  $
    R p_! cal(L) -->^(R p_! u_Y) R p_! p^(-1) R p_! cal(L)(1)[2] -->^(eta_Y R p_!) R p_! cal(L)
  $
  $
    p^(-1) cal(K) -->^(u_Y p^(-1)) p^(-1) R p_! p^(-1) cal(K)(1)[2] -->^(p^(-1) eta_Y) p^(-1) cal(K)
  $
  
  - 为证这两条恒等式，需要一个辅助命题：令 $r: AA^2_Y -> Y$，则下图交换：#h(1fr)
    // https://q.uiver.app/#r=typst&q=WzAsNixbMCwxLCJSIHBfISBSIHFfKDIsISkgcV8xXigtMSkgY2FsKEwpIl0sWzAsMiwiUiBwXyEgcF4oLTEpIFIgcF8hIGNhbChMKSJdLFsxLDIsIlIgcF8hIGNhbChMKSgtMSlbLTJdIl0sWzEsMSwiUiBwXyEgUiBxXygxLCEpIHFfMV4oLTEpIGNhbChMKSJdLFswLDAsIlIgcl8hIHFfMV4oLTEpIGNhbChMKSJdLFsxLDAsIlIgcl8hIHFfMV4oLTEpIGNhbChMKSJdLFs0LDUsIiIsMCx7InN0eWxlIjp7ImJvZHkiOnsibmFtZSI6ImRvdWJsZSBiYXJyZWQifX19XSxbNCwwLCJ0aWxkZSIsMl0sWzUsMywidGlsZGUiXSxbMCwxLCJCQ14oLTEpIiwyXSxbMywyLCJUcl8ocV8xKSJdLFsxLDIsIlRyX3AiLDJdXQ==
    #align(center, diagram({
      node((0, 0), [$R p_! R q_(2,!) q_1^(-1) cal(L)$])
      node((0, 1), [$R p_! p^(-1) R p_! cal(L)$])
      node((1, 1), [$R p_! cal(L)(-1)[-2]$])
      node((1, 0), [$R p_! R q_(1,!) q_1^(-1) cal(L)$])
      node((0, -1), [$R r_! q_1^(-1) cal(L)$])
      node((1, -1), [$R r_! q_1^(-1) cal(L)$])
      edge((0, -1), (1, -1), "=")
      edge((0, -1), (0, 0), [$tilde$], label-side: right, "->")
      edge((1, -1), (1, 0), [$tilde$], label-side: left, "->")
      edge((0, 0), (0, 1), [$BC^(-1)$], label-side: right, "->")
      edge((1, 0), (1, 1), [$Tr_(q_1)$], label-side: left, "->")
      edge((0, 1), (1, 1), [$Tr_p$], label-side: right, "->")
    }))
    可以验证，按 Künneth 映射的定义，左下的路径是复合： 
    $
      R r_! q_1^(-1) cal(L) cong R r_! (q_1^(-1) cal(L) Lotimes_(ZZ\/n) q_2^(-1) ul(ZZ\/n)) ->^K R p_! cal(L) Lotimes_(ZZ\/n) R p_! ul(ZZ\/n) -->^(Tr_p) R p_! cal(L) Lotimes_(ZZ\/n) ul(ZZ\/n)(-1)[-2]
    $
    其中 $K$ 是 Künneth 映射。另一方面，右侧路径由下式给出： 
    $
      R r_! q_1^(-1) cal(L) ->^P R p_! (cal(L) Lotimes_Lambda R q_(1,!) ul(ZZ\/n)) ->^(Tr_(q_1)) R p_! (cal(L) Lotimes_Lambda ul(ZZ\/n)(-1)[-2]) ->^P R p_! cal(L) Lotimes_Lambda ul(ZZ\/n)(-1)[-2]
    $
    Künneth 映射是对称的，可以先向任一因子投影来定义。于是左下路径分解为： 
    $
      R r_! (q_1^(-1) cal(L) Lotimes_(ZZ\/n) q_2^(-1) ul(ZZ\/n)) &-->^P R p_! (cal(L) Lotimes_(ZZ\/n) R q_(1,!) q_2^(-1) ul(ZZ\/n)) -->^(BC^(-1)) R p_! (cal(L) Lotimes_(ZZ\/n) p^(-1) R p_! ul(ZZ\/n)) \
      &-->^P R p_! cal(L) Lotimes_(ZZ\/n) R p_! ul(ZZ\/n) -->^(Tr_p) cal(L) Lotimes_(ZZ\/n) ul(ZZ\/n)(-1)[2]
    $
    由自然性，最后两个映射可以交换为： 
    $
      dots.c -->^(Tr_p) R p_! (cal(L) Lotimes_(ZZ\/n) ul(ZZ\/n)(-1)[2]) -->^(P) cal(L) Lotimes_(ZZ\/n) ul(ZZ\/n)(-1)[2]
    $

    沿 $q_1$ 的第一次投影可以与右路径中的相应投影相消，沿 $p$ 的最后一次投影也可以相消。再去掉 $R p_!$ 与 $cal(L) Lotimes_(ZZ\/n) -$，只需验证复合： 
    $
      p^(-1) R p_! ul(ZZ\/n) ->^BC R q_(1,!) q_2^(-1) ul(ZZ\/n) = R q_(1,!) ul(ZZ\/n) ->^(Tr_(q_1)) ul(ZZ\/n)(-1)[-2]
    $
    恰好是 $Tr_p$。这不过是迹映射与基变换的相容性。由对称性，把 $q_1, q_2$ 互换后同样的关系也成立。 

  - 为验证第一条伴随恒等式，考虑下图： 
    // https://q.uiver.app/#r=typst&q=WzAsMTQsWzAsMCwiUiBwXyEgY2FsKEwpIl0sWzAsMSwiUiBwXyEgUiBxXygxLCEpIFIgRGVsdGFfKiBEZWx0YV4oLTEpIHFfMl4oLTEpIGNhbChMKSJdLFswLDIsIlIgcF8hIFIgcV8oMSwhKSAocV8yXigtMSkgY2FsKEwpIExvdGltZXNfKFpaXFwvbikgUiBEZWx0YV8qIHVsKFpaXFwvbikpIl0sWzAsMywiUiBwXyEgUiBxXygxLCEpIHFfMl4oLTEpIGNhbChMKSgxKVsyXSJdLFswLDQsIlIgcF8hIHBeKC0xKSBSIHBfISBjYWwoTCkoMSlbMl0iXSxbMCw1LCJSIHBfISBjYWwoTCkiXSxbMSwwLCJSIHBfISBjYWwoTCkiXSxbMSwxLCJSIHBfISBSIHFfKDIsISkgUiBEZWx0YV8qIERlbHRhXigtMSkgcV8yXigtMSkgY2FsKEwpIl0sWzEsMiwiUiBwXyEgUiBxXygyLCEpIChxXzJeKC0xKSBjYWwoTCkgTG90aW1lc18oWlpcXC9uKSBSIERlbHRhXyogdWwoWlpcXC9uKSkiXSxbMSwzLCJSIHBfISBSIHFfKDIsISkgcV8yXigtMSkgY2FsKEwpKDEpWzJdIl0sWzEsNSwiUiBwXyEgY2FsKEwpIl0sWzEsNCwiUiBwXyEgKGNhbChMKSBMb3RpbWVzXyhaWlxcL24pIFIgcV8oMiwhKSB1bChaWlxcL24pICgxKVsyXSkiXSxbMiwzLCJSIHBfISAoY2FsKEwpIExvdGltZXNfKFpaXFwvbikgUiBxXygyLCEpIFIgRGVsdGFfKiB1bChaWlxcL24pKSJdLFsyLDQsIlIgcF8hIGNhbChMKSBMb3RpbWVzXyhaWlxcL24pIFIgcV8oMiwhKSB1bChaWlxcL24pICgxKVsyXSJdLFswLDEsInRpbGRlIiwyXSxbMSwyLCJQIiwyXSxbMiwzLCJjIiwyXSxbMyw0LCJCQ14oLTEpIiwyXSxbNCw1LCJUcl9wIiwyXSxbNiw3LCJ0aWxkZSJdLFs3LDgsIlAiXSxbOCw5LCJjIl0sWzAsNiwiIiwwLHsic3R5bGUiOnsiYm9keSI6eyJuYW1lIjoiZG91YmxlIGJhcnJlZCJ9fX1dLFsxLDcsInRpbGRlIiwxXSxbMiw4LCJ0aWxkZSIsMV0sWzUsMTAsInRpbGRlIiwyXSxbMyw5LCJ0aWxkZSIsMV0sWzksMTEsIlAiXSxbMTEsMTAsIlRyXyhxXzIpIl0sWzgsMTIsIlAiLDFdLFs3LDEyLCJQIiwxLHsiY3VydmUiOi01fV0sWzEyLDEzLCJjIl0sWzEzLDEwLCJUciJdXQ==
    #context align(center, diagram({
      node((0, 0), [$R p_! cal(L)$])
      node((0, 1), [$R p_! R q_(2,!) R Delta_* Delta^(-1) q_1^(-1) cal(L)$])
      node((0, 2), [$R p_! R q_(2,!) (q_1^(-1) cal(L) Lotimes_(ZZ\/n) R Delta_* ul(ZZ\/n))$])
      node((0, 3), [$R p_! R q_(2,!) q_1^(-1) cal(L)(1)[2]$])
      node((0, 4), [$R p_! p^(-1) R p_! cal(L)(1)[2]$])
      node((0, 5), [$R p_! cal(L)$])
      node((1, 0), [$R p_! cal(L)$])
      node((1, 1), [$R p_! R q_(1,!) R Delta_* Delta^(-1) q_1^(-1) cal(L)$])
      node((1, 2), [$R p_! R q_(1,!) (q_1^(-1) cal(L) Lotimes_(ZZ\/n) R Delta_* ul(ZZ\/n))$])
      node((1, 3), [$R p_! R q_(1,!) q_1^(-1) cal(L)(1)[2]$])
      node((1, 5), [$R p_! cal(L)$])
      node((1, 4), [$R p_! (cal(L) Lotimes_(ZZ\/n) R q_(1,!) ul(ZZ\/n) (1)[2])$])
      node((2, 3), [$R p_! (cal(L) Lotimes_(ZZ\/n) R q_(1,!) R Delta_* ul(ZZ\/n))$])
      node((2, 4), [$R p_! cal(L) Lotimes_(ZZ\/n) R q_(1,!) ul(ZZ\/n) (1)[2]$])
      edge((0, 0), (0, 1), [$tilde$], label-side: right, "->")
      edge((0, 1), (0, 2), [$P$], label-side: right, "->")
      edge((0, 2), (0, 3), [$c$], label-side: right, "->")
      edge((0, 3), (0, 4), [$BC^(-1)$], label-side: right, "->")
      edge((0, 4), (0, 5), [$Tr_p$], label-side: right, "->")
      edge((1, 0), (1, 1), [$tilde$], label-side: left, "->")
      edge((1, 1), (1, 2), [$P$], label-side: left, "->")
      edge((1, 2), (1, 3), [$c$], label-side: left, "->")
      edge((0, 0), (1, 0), "=")
      edge((0, 1), (1, 1), [$tilde$], label-side: center, "->")
      edge((0, 2), (1, 2), [$tilde$], label-side: center, "->")
      edge((0, 5), (1, 5), label-side: right, "=")
      edge((0, 3), (1, 3), [$tilde$], label-side: center, "->")
      edge((1, 3), (1, 4), [$P$], label-side: left, "->")
      edge((1, 4), (1, 5), [$Tr_(q_1)$], label-side: left, "->")
      edge((1, 2), (2, 3), [$P$], label-side: center, "->")
      edge((1, 1), (2, 3), [$P$], label-side: center, "->", bend: 30deg)
      edge((2, 3), (2, 4), [$c$], label-side: left, "->")
      edge((2, 4), (1, 5), [$Tr_(q_1)$], label-side: left, "->")
    }, crossing-fill: thm-box-curr-color()))
    这里除左下角外，所有方块都由自然性交换；左下角则由第一个要点保证交换。于是只需验证右路径是恒等映射。事实上， 
    $
      R q_(1,!) R Delta_* ul(ZZ\/n) ->^c R q_(1,!) ul(ZZ\/n) (1)[2] -->^(Tr_(q_1)) ul(ZZ\/n)
    $
    是由 $q_1 compose Delta = id$ 诱导的自然同构 $R q_(1,!) R Delta_* ul(ZZ\/n) cong ul(ZZ\/n)$，它消去了沿 $q_1 compose Delta$ 的投影。 

  - 对第二条恒等式，使用下图： 
    // https://q.uiver.app/#r=typst&q=WzAsMTQsWzAsMCwicF4oLTEpIGNhbChLKSJdLFswLDEsIlIgcV8oMiwhKSBSIERlbHRhXyogRGVsdGFeKC0xKSBxXzFeKC0xKSBwXigtMSkgY2FsKEspIl0sWzAsMiwiUiBxXygyLCEpIChxXzFeKC0xKSBwXigtMSkgY2FsKEspIExvdGltZXNfKFpaXFwvbikgUiBEZWx0YV8qIHVsKFpaXFwvbikpIl0sWzAsMywiUiBxXygyLCEpIHFfMV4oLTEpIHBeKC0xKSBjYWwoSykgKDEpWzJdIl0sWzAsNCwicF4oLTEpIFIgcF8hIHBeKC0xKSBjYWwoSykoMSlbMl0iXSxbMCw1LCJwXigtMSkgY2FsKEspIl0sWzEsMCwicF4oLTEpIGNhbChLKSJdLFsxLDEsIlIgcV8oMiwhKSBSIERlbHRhXyogRGVsdGFeKC0xKSBxXzJeKC0xKSBwXigtMSkgY2FsKEspIl0sWzEsMiwiUiBxXygyLCEpIChxXzJeKC0xKSBwXigtMSkgY2FsKEspIExvdGltZXNfKFpaXFwvbikgUiBEZWx0YV8qIHVsKFpaXFwvbikpIl0sWzEsMywiUiBxXygyLCEpIHFfMl4oLTEpIHBeKC0xKSBjYWwoSykgKDEpWzJdIl0sWzEsNSwicF4oLTEpIGNhbChLKSJdLFsxLDQsInBeKC0xKSBjYWwoSykgTG90aW1lc18oWlpcXC9uKSBSIHFfKDIsISkgdWwoWlpcXC9uKSgxKVsyXSJdLFsyLDMsInBeKC0xKSBjYWwoSykgTG90aW1lc18oWlpcXC9uKSBSIHFfKDIsISkgUiBEZWx0YV8qIHVsKFpaXFwvbikiXSxbMiw0LCJwXigtMSkgY2FsKEspIExvdGltZXNfKFpaXFwvbikgUiBxXygyLCEpICB1bChaWlxcL24pKDEpWzJdIl0sWzAsMSwidGlsZGUiLDJdLFsxLDIsIlAiLDJdLFsyLDMsImMiLDJdLFszLDQsIkJDXigtMSkiLDJdLFs0LDUsIlRyX3AiLDJdLFs2LDcsInRpbGRlIl0sWzcsOCwiUCJdLFswLDYsIiIsMCx7InN0eWxlIjp7ImJvZHkiOnsibmFtZSI6ImRvdWJsZSBiYXJyZWQifX19XSxbMSw3LCJ0aWxkZSIsMV0sWzIsOCwidGlsZGUiLDFdLFszLDksInRpbGRlIiwxXSxbNSwxMCwiIiwyLHsic3R5bGUiOnsiYm9keSI6eyJuYW1lIjoiZG91YmxlIGJhcnJlZCJ9fX1dLFs4LDksImMiXSxbOSwxMSwiUCJdLFsxMSwxMCwiVHJfKHFfMikiXSxbOCwxMiwiUCIsMV0sWzEyLDEzLCJjIiwxXSxbMTMsMTAsIlRyXyhxXzIpIiwxXSxbNywxMiwiUCIsMSx7ImN1cnZlIjotM31dXQ==
    #context align(center, diagram({
      node((0, 0), [$p^(-1) cal(K)$])
      node((0, 1), [$R q_(2,!) R Delta_* Delta^(-1) q_1^(-1) p^(-1) cal(K)$])
      node((0, 2), [$R q_(2,!) (q_1^(-1) p^(-1) cal(K) Lotimes_(ZZ\/n) R Delta_* ul(ZZ\/n))$])
      node((0, 3), [$R q_(2,!) q_1^(-1) p^(-1) cal(K) (1)[2]$])
      node((0, 4), [$p^(-1) R p_! p^(-1) cal(K)(1)[2]$])
      node((0, 5), [$p^(-1) cal(K)$])
      node((1, 0), [$p^(-1) cal(K)$])
      node((1, 1), [$R q_(2,!) R Delta_* Delta^(-1) q_2^(-1) p^(-1) cal(K)$])
      node((1, 2), [$R q_(2,!) (q_2^(-1) p^(-1) cal(K) Lotimes_(ZZ\/n) R Delta_* ul(ZZ\/n))$])
      node((1, 3), [$R q_(2,!) q_2^(-1) p^(-1) cal(K) (1)[2]$])
      node((1, 5), [$p^(-1) cal(K)$])
      node((1, 4), [$p^(-1) cal(K) Lotimes_(ZZ\/n) R q_(2,!) ul(ZZ\/n)(1)[2]$])
      node((2, 3), [$p^(-1) cal(K) Lotimes_(ZZ\/n) R q_(2,!) R Delta_* ul(ZZ\/n)$])
      node((2, 4), [$p^(-1) cal(K) Lotimes_(ZZ\/n) R q_(2,!)  ul(ZZ\/n)(1)[2]$])
      edge((0, 0), (0, 1), [$tilde$], label-side: right, "->")
      edge((0, 1), (0, 2), [$P$], label-side: right, "->")
      edge((0, 2), (0, 3), [$c$], label-side: right, "->")
      edge((0, 3), (0, 4), [$BC^(-1)$], label-side: right, "->")
      edge((0, 4), (0, 5), [$Tr_p$], label-side: right, "->")
      edge((1, 0), (1, 1), [$tilde$], label-side: left, "->")
      edge((1, 1), (1, 2), [$P$], label-side: left, "->")
      edge((0, 0), (1, 0), "=")
      edge((0, 1), (1, 1), [$tilde$], label-side: center, "->")
      edge((0, 2), (1, 2), [$tilde$], label-side: center, "->")
      edge((0, 3), (1, 3), [$tilde$], label-side: center, "->")
      edge((0, 5), (1, 5), "=")
      edge((1, 2), (1, 3), [$c$], label-side: left, "->")
      edge((1, 3), (1, 4), [$P$], label-side: left, "->")
      edge((1, 4), (1, 5), [$Tr_(q_2)$], label-side: left, "->")
      edge((1, 2), (2, 3), [$P$], label-side: center, "->")
      edge((2, 3), (2, 4), [$c$], label-side: center, "->")
      edge((2, 4), (1, 5), [$Tr_(q_2)$], label-side: center, "->")
      edge((1, 1), (2, 3), [$P$], label-side: center, "->", bend: 30deg)
    }, crossing-fill: thm-box-curr-color()))
    除左下角外，所有方块都由自然性交换。 

    - 对左下角，为验证其交换性，注意这里的一切都与基变换相容，故在茎上检查后可以假定 $Y = Spec(k)$ 是一个几何点。此时 $D(Y_et, ZZ\/n) cong D(ZZ\/n)$ 由紧对象 (compact object) $ul(ZZ\/n)$ 生成，而这个方块的两条路径都保持任意直和。于是由 @cpct-generation-of-triangulated-cat，只需对 $cal(K) = ul(ZZ\/n)$ 验证。此时投影映射是恒等映射，需要验证： 
      $
        R q_(2,!) ul(ZZ\/n)(1)[2] -->^(BC^(-1)) p^(-1) R p_! p^(-1) ul(ZZ\/n)(1)[2] -->^(Tr_p) ul(ZZ\/n)
      $
      恰好是 $Tr_(q_2)$。这正是迹映射与基变换的相容性。 

    于是只需证明右路径是恒等映射。事实上，由 $c$ 的定义性质， 
    $
      R q_(2,!) R Delta_* ul(ZZ\/n) ->^c R q_(2,!) ul(ZZ\/n) (1)[2] -->^(Tr_(q_2)) ul(ZZ\/n)
    $
    是由 $q_2 compose Delta = id$ 诱导的自然同构 $R q_(2,!) R Delta_* ul(ZZ\/n) cong ul(ZZ\/n)$，它消去了沿 $q_2 compose Delta$ 的投影。 

  两条伴随恒等式都已证，我们就正式确认了一对伴随： 
  $
    R p_! tack.l p^(-1) (-)(1)[2]
  $
  其中迹映射是伴随的余单位。因此纯性映射： 
  $
    t_(AA^1_Y\/Y): p^(-1) cal(K) (1)[2] -> R p^! cal(K)
  $
  对一切 $cal(K) in D(Y_et, ZZ\/n)$ 都是同构。 
]

#theorem(name: <relative-poincare-duality>)[
  (相对 Poincaré 对偶) 设 $Lambda$ 是 $n$-挠 Noether 环。对 Noether $ZZ[n^(-1)]$-概形之间相对维数为 $d$ 的任意光滑态射 $f: X -> Y$，纯性映射： 
  $
    t_(X\/Y): f^(-1) cal(K)(d)[2d] -> R f^! cal(K)
  $
  对一切 $cal(K) in D(Y_et, Lambda)$ 都是同构。 
]
#proof[
  纯性映射与复合相容，意思是：对 $p_d: AA^d_Y ->^q AA^(d-1)_Y ->^(p_(d-1)) Y$，复合： 
  $
    p_d^(-1) cal(K)(d)[2d] &cong q^(-1) (p_(d-1)^(-1) cal(K)(d-1)[2d-2])(1)[2] \
    &-->^(t_q) R q^! p_(d-1)^(-1) cal(K)(d-1)[2d-2] \
    &-->^(t_(p_(d-1))) R q^! R p_(d-1)^! cal(K) cong R p_d^! cal(K)
  $
  恰好是纯性映射 $t_(p_d)$。由 @a1-poincare-duality，$t_q$ 总是同构，故对 $d$ 归纳可知，纯性映射： 
  $
    t_(AA^d_Y\/Y): p_d^(-1) cal(K)(d)[2d] -> R p_d^! cal(K) 
  $
  对 $p_d: AA^d_Y -> Y$ 总是同构。 

  现在假设（分离的）光滑态射 $f: X -> Y$ 分解为 $X ->^j AA^d_Y ->^p Y$，其中 $j$ 是（分离的）平展态射。则复合： 
  $
    f^(-1) cal(K)(d)[2d] cong j^(-1) p^(-1) cal(K)(d)[2d] cong R j^! p^(-1) cal(K)(d)[2d] -->^(t_p) R j^! R p^! cal(K) cong R f^! cal(K) 
  $
  恰好是纯性映射 $t_(X\/Y)$。由于 $t_p$ 是同构，$t_(X\/Y)$ 也是同构。 

  最后，对一般的（分离的）光滑态射 $f: X -> Y$，存在（分离的）平展覆盖 $ell: U -> X$，使 $f compose ell$ 分解为 $U ->^j AA^d_Y ->^p Y$，其中 $j$ 是（分离的）平展态射。此时纯性映射 $t_(U\/Y)$ 是同构，且等于复合： 
  $
    ell^(-1) f^(-1) cal(K)(d)[2d] ->^(ell^(-1) t_(X\/Y)) ell^(-1) R f^! cal(K) cong R ell^! R f^! cal(K)
  $
  于是 $ell^(-1) t_(X\/Y): ell^(-1) f^(-1) cal(K)(d)[2d] -> ell^(-1) R f^! cal(K)$ 是同构。又因 $ell$ 满射，由 @surjective-pullback-conservative 可知 $t_(X\/Y)$ 总是同构。证毕。 
]

#theorem(name: <absolute-poincare-duality>)[
  (绝对 Poincaré 对偶) 设 $Lambda$ 是 $n$-挠 Noether 环，且作为自身的模是内射模。设 $k$ 是代数闭域，$n in k^times$，$X$ 是纯维数 $d$ 的光滑 $k$-概形。则： 

  + 对复形 $cal(K) in D(X_et, Lambda)$，杯积配对：#h(1fr)
    $
      smile: h^q (R Gamma_c (X, cal(K))) times h^(2d-q) (RHom_Lambda (cal(K), ul(Lambda)(d))) -> Lambda
    $
    是完美配对。特别地，对层 $cal(F) in cAb(X_et, Lambda)$，杯积配对：
    $
      smile: H^q_c (X, cal(F)) times Ext^(2d-q)_Lambda (cal(F), ul(Lambda)(d)) -> Lambda
    $
    是完美配对。 

  + 对 l.c.c. 层 $cal(F) in cAb(X_et, Lambda)$，存在典范的完美双线性配对： 
    $
      smile: H^q_c (X, cal(F)) times H^(2d-q) (X, caron(cal(F))(d)) -> Lambda
    $
    其中 $cal(F)^caron = HHom_Lambda (cal(F), ul(Lambda))$。 
]
#proof[
  (1) 由 @relative-poincare-duality 以及 @constr-pd-relative-to-absolute 中的讨论可得。对 (2)，只需证明： 
  $
    Ext^(2d-q)_Lambda (cal(F), ul(Lambda)(d)) cong H^(2d-q) (X, caron(cal(F))(d))
  $
  取 Hochschild–Serre 谱序列（本质上就是导出函子复合 $R Gamma(X, RHHom_Lambda (-, -)) = RHom_Lambda (-, -)$ 的 Grothendieck–Leray 谱序列）： 
  $
    E_2^(p,q) = H^p (X, EExt^q_Lambda (cal(F), ul(Lambda)(d))) -> Ext^(p+q)_Lambda (cal(F), ul(Lambda)(d))
  $
  可以看出，只需证明：当 $q>=1$ 时， 
  $
    EExt^q_Lambda (cal(F), ul(Lambda)(d)) = 0
  $

  这由下面的引理可得： 
  #lemma(name: <lcc-and-injective-has-no-higher-ext>)[
    设 $Lambda$ 是 Noether 环，$cal(F)$ 是概形 $X$ 上 $Lambda$-模的 l.c.c. 层，$G$ 是内射 $Lambda$-模。则： 
    $
      EExt^q (cal(F), ul(G)) = 0, forall q >= 1
    $
  ]
  #proof[
    事实上，取平展覆盖 $U -> X$，使对某个有限 $Lambda$-模 $M$ 有 $cal(F)|_U = ul(M)_U$。则由 @surjective-pullback-conservative，只需证明下述层消没： 
    $
      EExt^q_Lambda (cal(F), ul(G))|_U cong EExt^q_Lambda (cal(F)|_U, ul(G)_U) cong EExt^q_Lambda (ul(M)_U, ul(G)_U)
    $
    因此需要证明 $EExt^q_Lambda (ul(M)_U, ul(G)_U) = 0$。 
    
    - 若 $M$ 是有限自由 $Lambda$-模，则只需证明 $q >= 1$ 时 $EExt^q_Lambda (ul(Lambda)_U, ul(G)_U) = 0$。此时 $HHom_Lambda (ul(Lambda)_U, -)$ 是恒等函子，故没有高阶导出函子。 

    - 一般情形，取由自由 $Lambda$-模 $L^p$ 给出的自由消解 $dots.c -> L^(-1) -> L^0 -> M -> 0$；由于 $Lambda$ 是 Noether 环，这些模可取为有限模。如上所证，$q >= 1$ 时每个 $EExt^q (ul(L^(-p))_U, ul(G)_U) = 0$，故可用这个消解计算 $EExt^q_Lambda (ul(M)_U, ul(G)_U)$。于是对 $q >= 1$： 
    $
      EExt^q_Lambda (ul(M)_U, ul(G)_U) &cong h^q (0 -> HHom_Lambda (ul(L^0), ul(G)) -> HHom_Lambda (ul(L^(-1)), ul(G)) -> dots.c) \
      &cong h^q (0 -> ul(Hom_Lambda (L^0, G)) -> ul(Hom_Lambda (L^(-1), G)) -> dots.c) \
      &cong ul(h^q (0 -> Hom_Lambda (L^0, G) -> Hom_Lambda (L^(-1), G) -> dots.c)) = 0
    $
    其中由于 $G$ 是内射 $Lambda$-模，$0 -> Hom_Lambda (L^0, G) -> Hom_Lambda (L^(-1), G) -> dots.c$ 在次数 $q$ 处正合。 
  ]

  把这条引理应用于 l.c.c. 层 $cal(F)$ 与内射 $Lambda$-模 $Lambda(d)$，即得结论。 
]

#corollary(name: <relative-purity>)[
  (相对纯性) 设 $Lambda$ 是 $n$-挠 Noether 环，且作为自身的模是内射模。设 $S$ 是 Noether $ZZ[n^(-1)]$-概形。 
  
  假设 $i: X -> Y$ 是分离光滑 $S$-概形之间的闭浸入，$X, Y$ 的相对维数分别为 $d-c$ 与 $d$。设 $f: Y -> S, f_X: X -> S$ 是结构态射。则：
  
  + 对 $cal(K) in D(S_et, Lambda)$，存在典范自然同构：#h(1fr)
    $
      R i^! f^(-1) cal(K) cong i^(-1) f^(-1) cal(K) (-c)[-2c]
    $

  + 设 $c >= 1$，$j: U -> Y$ 是与 $i$ 互补的开浸入，并令 $f_U = f compose j: U -> S$。则对任意 $cal(F) in cAb(S_et, Lambda)$，有典范同构： 
    $
      R^q j_* f_U^(-1) cal(F) = cases(
        f^(-1) cal(F) &\, q = 0, 
        i_* f_X^(-1) cal(F)(-c) &\, q = 2c-1, 
        0 &\, #[否则]
      ) 
    $
  + (Gysin 序列) 在 (2) 的设定下，存在典范长正合列： 
    $
      0 &-> R^(2c-1) f_* f^(-1) cal(F) -> R^(2c-1) f_(U,*) f_U^(-1) cal(F) -> f_(X,*) f_X^(-1) cal(F)(-c) -> dots.c \
      &-> R^(q-1) f_* f^(-1) cal(F) -> R^(q-1) f_(U,*) f_U^(-1) cal(F) -> R^(q-2c) f_(X,*) f_X^(-1) cal(F)(-c) -> dots.c 
    $
    以及典范同构： 
    $
      R^q f_* f^(-1) cal(F) cong R^q f_(U,*) f_U^(-1) cal(F), forall 0 <= q <= 2c-2
    $
]
#proof[
  (1) 取结构态射 $f: Y -> S$，它是相对维数为 $d$ 的光滑态射，故 $f compose i: X -> S$ 是相对维数为 $d-c$ 的光滑态射。 

  由相对 Poincaré 对偶， 
  $
    R i^! f^(-1) cal(K) &cong R i^! R f^! cal(K)(-d)[-2d] cong R f_X^! cal(K)(-d)[-2d] \
    &cong (f_X^(-1) cal(K)(d-c)[2(d-c)])(-d)[-2d] \
    &cong i^(-1) f^(-1) cal(K)(-c)[-2c]
  $
  证毕。 

  (2) 由带支集截面三角： 
  $
    i_* R i^! f^(-1) cal(F) -> f^(-1) cal(F) -> R j_* j^(-1) f^(-1) cal(F) ->^(+1)
  $
  结合 (1)，立即得到 $R^q j_* f_U^(-1) cal(F)$ 的公式。 
  
  (3) 取 Leray 谱序列： 
  $
    E_2^(p,q) = R^p f_* R^q j_* (f_U^(-1) cal(F)) => R^(p+q) f_(U,*) f_U^(-1) cal(F)
  $
  它只在 $q=0,2c-1$ 处非零。只有两行的这种谱序列诱导出长正合列： 
  $
    0 &-> R^(2c-1) f_* f^(-1) cal(F) -> R^(2c-1) f_(U,*) f_U^(-1) cal(F) -> f_(X,*) f_X^(-1) cal(F)(-c) -->^(d^(2c)) dots.c \
      &-> R^(q-1) f_* f^(-1) cal(F) -> R^(q-1) f_(U,*) f_U^(-1) cal(F) -> R^(q-2c) f_(X,*) f_X^(-1) cal(F)(-c) -->^(d^(2c)) dots.c 
  $
  以及同构： 
  $
    R^q f_* f^(-1) cal(F) cong R^q f_(U,*) f_U^(-1) cal(F), forall 0 <= q <= 2c-2
  $
  证毕。 
]

#example[
  (仿射光滑曲线的上同调) 现在终于可以计算仿射曲线的上同调，这在 @sect-cohom-of-curves 中没有明确算过。 
  
  设 $k$ 是代数闭域，取自然数 $n in k^times$，$X$ 是 $k$ 上的仿射光滑曲线。取 $X$ 的紧化 $ol(X)$，使 $j: X -> ol(X)$ 是开浸入，且 $ol(X)$ 是射影光滑曲线。给 $Z = ol(X) - X$ 赋予诱导的既约结构，它是 $k$ 上有限个闭点。现在 $Z, ol(X)$ 都在 $k$ 上光滑，故由 @relative-purity 得到 Gysin 序列： 
  $
    0 &-> H^1 (ol(X), ul(ZZ\/n)) -> H^1 (X, ul(ZZ\/n)) -> H^0 (Z, ul(ZZ\/n)(-1)) -> H^2 (ol(X), ul(ZZ\/n)) -> 0
  $
  其中 $H^2 (X, ul(ZZ\/n))$ 因 Artin 消没而为零。展开定义可以看出： 
  $
    H^0 (Z, ul(ZZ\/n)(-1)) cong (ZZ\/n(-1))^(oplus Z) -> ZZ\/n(-1) cong H^2 (ol(X), ul(ZZ\/n))
  $
  把以 $z in Z$ 为指标的 $ZZ\/n$ 的副本送到 $H^2 (ol(X), ul(ZZ\/n)) cong Pic(ol(X))\/n Pic(ol(X))$ 中对应的除子。于是它等同于以 $Z$ 中元素为指标、在各分量上求和的映射 $(ZZ\/n(-1))^(oplus Z) -> ZZ\/n(-1)$。因此得到短正合列： 
  $
    0 -> H^1 (ol(X), ul(ZZ\/n)) -> H^1 (X, ul(ZZ\/n)) -> (ZZ\/n (-1))^(oplus (m-1))
  $
  其中 $m = abs(Z) = abs(ol(X) - X)$ 是 $X$ 所缺的点数。存在非典范同构： 
  $
    H^1 (ol(X), ul(ZZ\/n)) cong (ZZ\/n)^(oplus 2g(ol(X)))
  $
  这由 @cohom-of-proj-curve 给出。因此存在非典范同构： 
  $
    H^1 (X, ul(ZZ\/n)) cong (ZZ\/n)^(oplus 2g(ol(X))+m-1)
  $
  至此我们算出了仿射光滑曲线的平展上同调： 
  $
    H^q (X, ul(ZZ\/n)) = cases(
      ZZ\/n &\, q = 0, 
      (ZZ\/n)^(oplus 2g(ol(X))+m-1) &\, q = 1, 
      0 &\, q >= 2
    )
  $
]
