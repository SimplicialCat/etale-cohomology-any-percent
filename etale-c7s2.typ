// audit-cjk-exception: 0.20  # 8 幅大型交换图占源码大半，散文已全部中译；45% 阈值结构性不适用。
// audit-exception: 公式中作为文字条件的 proper / is proper 文本块已译为“紧合”，其余公式逐字未动。
#import "void-import.typ": *

== $R f_!$ 的基本性质

#properties(name: <rf-lower-shriek-first-props>)[
  + （Leray 谱序列）设 $f: X -> Y, g: Y -> Z$ 是 Noether 概形之间分离的有限型态射。则有典范自然同构：
    $
      R(g compose f)_! cong R g_! compose R f_!: D_#[tor] (X_et, Lambda) -> D_#[tor] (Z_et, Lambda)
    $
    该同构与态射复合链的结合相容。

    特别地，对 $cal(F) in cAb_#[tor] (X_et, Lambda)$，有典范谱序列：
    $
      E_2^(p,q) = R^p g_! R^q f_! cal(F) => R^(p+q) (g compose f)_! cal(F)
    $

    当 $Z = Spec(k)$、$k$ 为可分闭域时，该同构特化为：
    $
      R Gamma_c (Y, R f_! (-)) cong R Gamma_c (X, -)
    $
    以及：
    $
      E_2^(p,q) = H^p_c (Y, R^q f_! cal(F)) => H^(p+q)_c (X, cal(F))
    $

  + （紧合基变换）在拉回图表中：
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
    设所有概形都是 Noether 的，$f$ 分离且有限型。则有自然同构：
    $
      g^(-1) R f_! -> R f'_! g'^(-1): D_#[tor] (X_et, Lambda) -> D_#[tor] (Y'_et, Lambda)
    $
    它与拉回方块的水平拼接、竖直拼接都相容。

    特别地，当 $Y' = ol(y)$ 是 $Y$ 的几何点时，它特化为：
    $
      (R f_! (-))_(ol(y)) cong R Gamma_c (X_(ol(y)), (-)|_(X_(ol(y))))
    $

  + （零延拓序列）设 $f: X -> Y$ 是 Noether 概形之间分离的有限型态射，$j: U -> X, i: Z -> X$ 是一对互补的开浸入与闭浸入。作：
    $
      f_U: U ->^j X ->^f Y \
      f_Z: Z ->^i X ->^f Y
    $
    则对 $cal(K) in D_#[tor] (X_et, Lambda)$，有自然的特殊三角：
    $
      R f_(U,!) j^(-1) cal(K) -> R f_! cal(K) -> R f_(Z,!) i^(-1) cal(K) ->^(+1)
    $
    它与基变换相容。特别地，当 $Y = Spec(k)$、$k$ 为可分闭域时，它特化为特殊三角：
    $
      R Gamma_c (U, j^(-1) cal(K)) -> R Gamma_c (X, cal(K)) -> R Gamma_c (Z, i^(-1) cal(K)) ->^(+1)
    $
]
#proof[
  (1) 设 $cal(K) in D_#[tor] (X_et, Lambda)$。取 $f$ 的紧化 $X ->^j ol(X) ->^(ol(f)) Y$ 与 $g$ 的紧化 $Y ->^k ol(Y) ->^(ol(g)) Z$。接着，由于 $k compose ol(f): ol(X) -> ol(Y)$ 分离且有限型，存在紧化 $ol(X) ->^ell tilde(X) ->^(tilde(f)) ol(Y)$。换言之，有交换图：
  // https://q.uiver.app/#r=typst&q=WzAsNixbMCwyLCJYIl0sWzMsMiwiWSJdLFs2LDIsIloiXSxbMiwxLCJvbChYKSJdLFs1LDEsIm9sKFkpIl0sWzQsMCwidGlsZGUoWCkiXSxbMCwxLCJmIiwxXSxbMSwyLCJnIiwxXSxbMCwzLCJqIiwxXSxbMyw1LCJlbGwiLDFdLFszLDEsIm9sKGYpIiwxXSxbMSw0LCJrIiwxXSxbNCwyLCJvbChnKSIsMV0sWzUsNCwidGlsZGUoZikiLDFdXQ==
  #context align(center, diagram({
    node((-2, 1), [$X$])
    node((1, 1), [$Y$])
    node((4, 1), [$Z$])
    node((0, 0), [$ol(X)$])
    node((3, 0), [$ol(Y)$])
    node((2, -1), [$tilde(X)$])
    edge((-2, 1), (1, 1), [$f$], label-side: center, "->")
    edge((1, 1), (4, 1), [$g$], label-side: center, "->")
    edge((-2, 1), (0, 0), [$j$], label-side: center, "->")
    edge((0, 0), (2, -1), [$ell$], label-side: center, "->")
    edge((0, 0), (1, 1), [$ol(f)$], label-side: center, "->")
    edge((1, 1), (3, 0), [$k$], label-side: center, "->")
    edge((3, 0), (4, 1), [$ol(g)$], label-side: center, "->")
    edge((2, -1), (3, 0), [$tilde(f)$], label-side: center, "->")
  }, crossing-fill: thm-box-curr-color(), spacing: 1.6em))
  其中向右下的箭头紧合、向右上的箭头是开浸入。这样的图称为 *$(f, g)$ 的紧化*。
  
  由 @open-proper-compat，存在自然拟同构：
  $
    k_! R ol(f)_* cal(K) ->^tilde R tilde(f)_* ell_! cal(K)
  $
  于是按定义，
  $
    R g_! R f_! cal(K) cong R ol(g)_* k_! R ol(f)_* j_! cal(K) cong R ol(g)_* R tilde(f)_* ell_! j_! cal(K) = R(ol(g) compose tilde(f))_* (ell compose j)_! cal(K) cong R(g compose f)_! cal(K)
  $
  其中 $X ->^(ell compose j) tilde(X) ->^(ol(g) compose tilde(f)) Z$ 是 $g compose f: X -> Z$ 的紧化。这样便构造出了一个同构。剩下要证：这个同构与 $(f, g)$ 紧化的选取无关，并且与三个态射复合的结合方式相容。

  余下的证明只是记账，可以跳过。假设已证明该同构与 $(f, g)$ 紧化的选取无关。那么给定三个态射 $X ->^f Y ->^g Z ->^h W$，我们要证明同构：
  $
    R(h compose g compose f)_! cong R h_! compose R(g compose f)_! cong R h_! compose R g_! compose R f_!
  $
  与下述同构相同：
  $
    R(h compose g compose f)_! cong R (h compose g)_! compose R f_! cong R h_! compose R g_! compose R f_!
  $
  #proof_[结合性的证明][
    作一个大交换图：
    // https://q.uiver.app/#r=typst&q=WzAsMTAsWzAsMywiWCJdLFszLDMsIlkiXSxbNiwzLCJaIl0sWzIsMiwib2woWCkiXSxbNSwyLCJvbChZKSJdLFs0LDEsIm9sKFgpJyJdLFs5LDMsIlciXSxbOCwyLCJvbChaKSJdLFs3LDEsIm9sKFkpJyJdLFs2LDAsIm9sKFgpJyciXSxbMCwxLCJmIiwxXSxbMSwyLCJnIiwxXSxbMCwzLCJqX1giLDFdLFszLDUsImonX1giLDFdLFszLDEsIm9sKGYpIiwxXSxbMSw0LCJqX1kiLDFdLFs0LDIsIm9sKGcpIiwxXSxbNSw0LCJvbChmKSciLDFdLFsyLDYsImgiLDFdLFsyLDcsImpfWiIsMV0sWzcsNiwib2woaCkiLDFdLFs0LDgsImonX1kiLDFdLFs4LDcsIm9sKGcpJyIsMV0sWzUsOSwiaicnX1giLDFdLFs5LDgsIm9sKGYpJyciLDFdXQ==
    #context align(center, diagram({
      node((-2, 1), [$X$])
      node((1, 1), [$Y$])
      node((4, 1), [$Z$])
      node((0, 0), [$ol(X)$])
      node((3, 0), [$ol(Y)$])
      node((2, -1), [$ol(X)'$])
      node((7, 1), [$W$])
      node((6, 0), [$ol(Z)$])
      node((5, -1), [$ol(Y)'$])
      node((4, -2), [$ol(X)''$])
      edge((-2, 1), (1, 1), [$f$], label-side: center, "->")
      edge((1, 1), (4, 1), [$g$], label-side: center, "->")
      edge((-2, 1), (0, 0), [$j_X$], label-side: center, "->")
      edge((0, 0), (2, -1), [$j'_X$], label-side: center, "->")
      edge((0, 0), (1, 1), [$ol(f)$], label-side: center, "->")
      edge((1, 1), (3, 0), [$j_Y$], label-side: center, "->")
      edge((3, 0), (4, 1), [$ol(g)$], label-side: center, "->")
      edge((2, -1), (3, 0), [$ol(f)'$], label-side: center, "->")
      edge((4, 1), (7, 1), [$h$], label-side: center, "->")
      edge((4, 1), (6, 0), [$j_Z$], label-side: center, "->")
      edge((6, 0), (7, 1), [$ol(h)$], label-side: center, "->")
      edge((3, 0), (5, -1), [$j'_Y$], label-side: center, "->")
      edge((5, -1), (6, 0), [$ol(g)'$], label-side: center, "->")
      edge((2, -1), (4, -2), [$j''_X$], label-side: center, "->")
      edge((4, -2), (5, -1), [$ol(f)''$], label-side: center, "->")
    }, crossing-fill: thm-box-curr-color(), spacing: 1.6em))
    其中向右下的箭头紧合、向右上的箭头是开浸入。

    把上面这张态射的交换图逐项取函子，得到函子图。这里把 $D_#[tor] (X_et, Lambda)$ 简记为 $D(X)$：
    // https://q.uiver.app/#r=typst&q=WzAsMTAsWzAsMywiRChYKSJdLFszLDMsIkQoWSkiXSxbNiwzLCJEKFopIl0sWzIsMiwiRChvbChYKSkiXSxbNSwyLCJEKG9sKFkpKSJdLFs0LDEsIkQob2woWCknKSJdLFs5LDMsIkQoVykiXSxbOCwyLCJEKG9sKFopKSJdLFs3LDEsIkQob2woWSknKSJdLFs2LDAsIkQob2woWCknJykiXSxbMCwxLCJSIGZfISIsMV0sWzEsMiwiUiBnXyEiLDFdLFswLDMsImpfKFgsISkiLDFdLFszLDUsImonXyhYLCEpIiwxXSxbMywxLCJSIG9sKGYpXyoiLDFdLFsxLDQsImpfKFksISkiLDFdLFs1LDQsIlIgb2woZiknXyoiLDFdLFsyLDYsIlIgaF8hIiwxXSxbMiw3LCJqXyhaLCEpIiwxXSxbNyw2LCJSIG9sKGgpXyoiLDFdLFs0LDgsImonXyhZLCEpIiwxXSxbOCw3LCJSIG9sKGcpJ18qIiwxXSxbNSw5LCJqJydfKFgsISkiLDFdLFs5LDgsIlIgb2woZiknJ18qIiwxXSxbNCwyLCJSIG9sKGcpXyoiLDFdXQ==
    #context align(center, diagram({
      node((-2, 1), [$D(X)$])
      node((1, 1), [$D(Y)$])
      node((4, 1), [$D(Z)$])
      node((0, 0), [$D(ol(X))$])
      node((3, 0), [$D(ol(Y))$])
      node((2, -1), [$D(ol(X)')$])
      node((7, 1), [$D(W)$])
      node((6, 0), [$D(ol(Z))$])
      node((5, -1), [$D(ol(Y)')$])
      node((4, -2), [$D(ol(X)'')$])

      edge(..tune-2-mor-coords((1, 1), (2, -1)), "=>", stroke: red)
      edge(..tune-2-mor-coords((4, 1), (4, -2)), "=>", stroke: red)
      edge(..tune-2-mor-coords((4, 1), (5, -1)), "=>", stroke: blue)
      edge(..tune-2-mor-coords((1, 1), (4, -2)), "=>", stroke: blue)

      edge((-2, 1), (1, 1), [$R f_!$], label-side: center, "->")
      edge((1, 1), (4, 1), [$R g_!$], label-side: center, "->")
      edge((-2, 1), (0, 0), [$j_(X,!)$], label-side: center, "->")
      edge((0, 0), (2, -1), [$j'_(X,!)$], label-side: center, "->")
      edge((0, 0), (1, 1), [$R ol(f)_*$], label-side: center, "->")
      edge((1, 1), (3, 0), [$j_(Y,!)$], label-side: center, "->")
      edge((2, -1), (3, 0), [$R ol(f)'_*$], label-side: center, "->")
      edge((4, 1), (7, 1), [$R h_!$], label-side: center, "->")
      edge((4, 1), (6, 0), [$j_(Z,!)$], label-side: center, "->")
      edge((6, 0), (7, 1), [$R ol(h)_*$], label-side: center, "->")
      edge((3, 0), (5, -1), [$j'_(Y,!)$], label-side: center, "->")
      edge((5, -1), (6, 0), [$R ol(g)'_*$], label-side: center, "->")
      edge((2, -1), (4, -2), [$j''_(X,!)$], label-side: center, "->")
      edge((4, -2), (5, -1), [$R ol(f)''_*$], label-side: center, "->")
      edge((3, 0), (4, 1), [$R ol(g)_*$], label-side: center, "->")
    }, crossing-fill: thm-box-curr-color(), spacing: 1.4em))
    这里底部的三个小三角交换；我们要等同的两个同构，都是从大三角的底边到两条上边的自然同构。

    那么，路径
    $
      R h_! compose R g_! compose R f_! cong R(h compose g)_! compose R f_! cong R(h compose g compose f)_!
    $
    是沿两个蓝色自然同构向上得到的；而路径：
    $
      R h_! compose R g_! compose R f_! cong R h_! compose R (g compose f)_! cong R(h compose g compose f)_!
    $
    则是沿两个红色自然同构向上得到的。所有自然同构都由 @open-proper-compat 给出。由 @open-proper-compat-naturality，这两条路径都等于沿着三个小方块诱导出的、由 @open-proper-compat 给出的自然同构逐级上行，故二者相同。
  ]
  现在证明同构 $R(g compose f)_! cong R g_! compose R f_!$ 与 $(f, g)$ 所选紧化无关。设有 $(f, g)$ 的两个紧化。先假设其中一个支配另一个，即有交换图：
  // https://q.uiver.app/#r=typst&q=WzAsMTIsWzAsMiwiWCJdLFszLDIsIlkiXSxbNiwyLCJaIl0sWzIsMSwib2woWCknIl0sWzUsMSwib2woWSknIl0sWzQsMCwidGlsZGUoWCknIl0sWzAsNiwiWCJdLFszLDYsIlkiXSxbNiw2LCJaIl0sWzIsNSwib2woWCkiXSxbNSw1LCJvbChZKSJdLFs0LDQsInRpbGRlKFgpIl0sWzAsMSwiZiIsMV0sWzEsMiwiZyIsMV0sWzAsMywiaiciLDFdLFszLDUsImVsbCciLDFdLFszLDEsIm9sKGYpJyIsMV0sWzEsNCwiayciLDFdLFs0LDIsIm9sKGcpJyIsMV0sWzUsNCwidGlsZGUoZiknIiwxXSxbNiw3LCJmIiwxXSxbNyw4LCJnIiwxXSxbNiw5LCJqIiwxXSxbOSwxMSwiZWxsIiwxXSxbOSw3LCJvbChmKSIsMV0sWzcsMTAsImsiLDFdLFsxMCw4LCJvbChnKSIsMV0sWzExLDEwLCJ0aWxkZShmKSIsMV0sWzAsNiwiIiwxLHsic3R5bGUiOnsiYm9keSI6eyJuYW1lIjoiZG91YmxlIGJhcnJlZCJ9fX1dLFsxLDcsIiIsMSx7InN0eWxlIjp7ImJvZHkiOnsibmFtZSI6ImRvdWJsZSBiYXJyZWQifX19XSxbMiw4LCIiLDEseyJzdHlsZSI6eyJib2R5Ijp7Im5hbWUiOiJkb3VibGUgYmFycmVkIn19fV0sWzMsOSwicGhpIiwxXSxbNCwxMCwicHNpIiwxXSxbNSwxMSwiY2hpIiwxLHsibGFiZWxfcG9zaXRpb24iOjgwfV1d
  #context align(center, diagram({
    node((3, -1), [$X$])
    node((6, -1), [$Y$])
    node((9, -1), [$Z$])
    node((5, -2), [$ol(X)'$])
    node((8, -2), [$ol(Y)'$])
    node((7, -3), [$tilde(X)'$])
    node((3, 3), [$X$])
    node((6, 3), [$Y$])
    node((9, 3), [$Z$])
    node((5, 2), [$ol(X)$])
    node((8, 2), [$ol(Y)$])
    node((7, 1), [$tilde(X)$])
    edge((3, -1), (3, 3), "=")
    edge((6, -1), (6, 3), "=")
    edge((9, -1), (9, 3), "=")
    edge((5, -2), (5, 2), [$phi$], label-side: center, "->")
    edge((8, -2), (8, 2), [$psi$], label-side: center, "->")
    edge((7, -3), (7, 1), [$chi$], label-side: center, label-pos: 0.8, "->")
    edge((3, -1), (6, -1), [$f$], label-side: center, "->")
    edge((6, -1), (9, -1), [$g$], label-side: center, "->")
    edge((3, -1), (5, -2), [$j'$], label-side: center, "->")
    edge((5, -2), (7, -3), [$ell'$], label-side: center, "->")
    edge((5, -2), (6, -1), [$ol(f)'$], label-side: center, "->")
    edge((6, -1), (8, -2), [$k'$], label-side: center, "->")
    edge((8, -2), (9, -1), [$ol(g)'$], label-side: center, "->")
    edge((7, -3), (8, -2), [$tilde(f)'$], label-side: center, "->")
    edge((3, 3), (6, 3), [$f$], label-side: center, "->")
    edge((6, 3), (9, 3), [$g$], label-side: center, "->")
    edge((3, 3), (5, 2), [$j$], label-side: center, "->")
    edge((5, 2), (7, 1), [$ell$], label-side: center, "->", label-pos: 0.7)
    edge((5, 2), (6, 3), [$ol(f)$], label-side: center, "->")
    edge((6, 3), (8, 2), [$k$], label-side: center, "->")
    edge((8, 2), (9, 3), [$ol(g)$], label-side: center, "->")
    edge((7, 1), (8, 2), [$tilde(f)$], label-side: center, "->")
  }, crossing-fill: thm-box-curr-color(), spacing: 1.6em))

  记 @open-proper-compat 中构造的同构为 $T(f_1, f_2, j_X, j_Y)$。再把 $R f_! = R ol(f)_* compose j_!, R g_! = R ol(g)_* compose k_!$ 与 $R(g compose f)_! = R(ol(g) compose ol(f))_* compose (ell compose j)_!$ 等同起来，则由下方紧化定义的同构 $R g_! compose R f_! -> R(g compose f)_!$ 为：
  $
    R ol(g)_* k_! R ol(f)_* j_! -->^(R ol(g)_* T(tilde(f), ol(f), ell, k) j_!) R ol(g)_* R ol(f)_* ell_! j_!
  $
  而由上方紧化定义的同构为：
  $
    R ol(g)_* k_! R ol(f)_* j_! &-->^(R ol(g)_* k_! T(phi, id_X, j', j)) R ol(g)_* k_! R ol(f)_* R phi_* j'_! = R ol(g)_* k_! R ol(f)'_* j'_! \
    &-->^(T(psi, id_Y, k', k) R ol(f)'_* j'_!) R ol(g)_* psi_* k'_! R ol(f)'_* j'_! = R ol(g)'_* k'_! R ol(f)'_* j'_! \
    &-->^(R ol(g)'_* T(tilde(f)', ol(f)', ell', k') j'_!) R ol(g)'_* R tilde(f)'_* ell'_! j'_! = R ol(g)_* R tilde(f)_* R chi_* ell'_! j'_! \
    &-->^(R ol(g)'_* R ol(f)'_* T(chi, id_X, ell' compose j', ell compose j)^(-1)) R ol(g)_* R tilde(f)_* ell_! j_!
  $
  换言之，要证明等式：
  $
    & R ol(g)'_* R ol(f)'_* T(chi, id_X, ell' compose j', ell compose j) compose R ol(g)_* T(tilde(f), ol(f), ell, k) j_! \
    =& R ol(g)'_* T(tilde(f)', ol(f)', ell', k') j'_! compose T(psi, id_Y, k', k) R ol(f)'_* j'_! compose R ol(g)_* k_! T(phi, id_X, j', j)
  $
  把 $D_#[tor] (X_et, Lambda)$ 简记为 $D(X)$，可作下图：
  // https://q.uiver.app/#r=typst&q=WzAsMTIsWzAsMiwiRChYKSJdLFszLDIsIkQoWSkiXSxbNiwyLCJEKFopIl0sWzIsMSwiRChvbChYKScpIl0sWzUsMSwiRChvbChZKScpIl0sWzQsMCwiRCh0aWxkZShYKScpIl0sWzAsNiwiRChYKSJdLFszLDYsIkQoWSkiXSxbNiw2LCJEKFopIl0sWzIsNSwiRChvbChYKSkiXSxbNSw1LCJEKG9sKFkpKSJdLFs0LDQsIkQodGlsZGUoWCkpIl0sWzAsMSwiUiBmXyEiLDFdLFsxLDIsIlIgZ18hIiwxXSxbMCwzLCJqJ18hIiwxXSxbMyw1LCJlbGwnXyEiLDFdLFszLDEsIlIgb2woZiknXyoiLDFdLFsxLDQsImsnXyEiLDFdLFs0LDIsIlIgb2woZyknXyoiLDFdLFs1LDQsIlIgdGlsZGUoZiknXyoiLDFdLFs2LDcsIlIgZl8hIiwxXSxbNyw4LCJSIGdfISIsMV0sWzYsOSwial8hIiwxXSxbOSwxMSwiZWxsXyEiLDFdLFs5LDcsIlIgb2woZilfKiIsMV0sWzcsMTAsImtfISIsMV0sWzEwLDgsIlIgb2woZylfKiIsMV0sWzExLDEwLCJSIHRpbGRlKGYpXyoiLDFdLFswLDYsIiIsMSx7InN0eWxlIjp7ImJvZHkiOnsibmFtZSI6ImRvdWJsZSBiYXJyZWQifX19XSxbMSw3LCIiLDEseyJzdHlsZSI6eyJib2R5Ijp7Im5hbWUiOiJkb3VibGUgYmFycmVkIn19fV0sWzIsOCwiIiwxLHsic3R5bGUiOnsiYm9keSI6eyJuYW1lIjoiZG91YmxlIGJhcnJlZCJ9fX1dLFszLDksInBoaSIsMV0sWzQsMTAsInBzaSIsMV0sWzUsMTEsImNoaSIsMSx7ImxhYmVsX3Bvc2l0aW9uIjo4MH1dXQ==
  #context align(center, diagram({
    edge(..tune-2-mor-coords((6, 3), (7, 1)), "=>", stroke: red, text(fill: red)[$1$], label-side: center, layer: -2)
    edge(..tune-2-mor-coords((3, 3), (5, -2)), "=>", stroke: red, text(fill: red)[$2$], label-side: center, layer: -2, bend: 20deg)
    edge(..tune-2-mor-coords((5, 2), (7, -3)), "=>", stroke: red, text(fill: red)[$3$], label-side: center, label-pos: 0.5, layer: -2, bend: -36deg)
    edge(..tune-2-mor-coords((3, 3), (5, -2)), "=>", stroke: blue, text(fill: blue)[$1$], label-side: center, layer: -2, bend: -20deg)
    edge(..tune-2-mor-coords((6, 3), (8, -2)), "=>", stroke: blue, text(fill: blue)[$2$], label-side: center, layer: -2, bend: -33deg, label-pos: 0.65)
    edge(..tune-2-mor-coords((6, -1), (7, -3)), "=>", stroke: blue, text(fill: blue)[$3$], label-side: center, layer: -2)


    node((3, -1), [$D(X)$])
    node((6, -1), [$D(Y)$])
    node((9, -1), [$D(Z)$])
    node((5, -2), [$D(ol(X)')$])
    node((8, -2), [$D(ol(Y)')$])
    node((7, -3), [$D(tilde(X)')$])
    node((3, 3), [$D(X)$])
    node((6, 3), [$D(Y)$])
    node((9, 3), [$D(Z)$])
    node((5, 2), [$D(ol(X))$])
    node((8, 2), [$D(ol(Y))$])
    node((7, 1), [$D(tilde(X))$])

    edge((3, -1), (3, 3), "=")
    edge((6, -1), (6, 3), "=")
    edge((9, -1), (9, 3), "=")
    edge((5, -2), (5, 2), [$R phi_*$], label-side: center, "->")
    edge((8, -2), (8, 2), [$R psi_*$], label-side: center, "->")
    edge((7, -3), (7, 1), [$R chi_*$], label-side: center, label-pos: 0.8, "->")
    edge((3, -1), (6, -1), [$R f_!$], label-side: center, "->")
    edge((6, -1), (9, -1), [$R g_!$], label-side: center, "->")
    edge((3, -1), (5, -2), text(fill: green)[$j'_!$], label-side: center, "->", stroke: green)
    edge((5, -2), (7, -3), text(fill: green)[$ell'_!$], label-side: center, "->", stroke: green)
    edge((5, -2), (6, -1), [$R ol(f)'_*$], label-side: center, "->")
    edge((6, -1), (8, -2), [$k'_!$], label-side: center, "->")
    edge((8, -2), (9, -1), text(fill: green)[$R ol(g)'_*$], label-side: center, "->", stroke: green)
    edge((7, -3), (8, -2), text(fill: green)[$R tilde(f)'_*$], label-side: center, "->", stroke: green)
    edge((3, 3), (6, 3), [$R f_!$], label-side: center, "->")
    edge((6, 3), (9, 3), [$R g_!$], label-side: center, "->")
    edge((3, 3), (5, 2), text(fill: fuchsia)[$j_!$], label-side: center, "->", stroke: fuchsia)
    edge((5, 2), (7, 1), [$ell_!$], label-side: center, "->", label-pos: 0.7)
    edge((5, 2), (6, 3), text(fill: fuchsia)[$R ol(f)_*$], label-side: center, "->", stroke: fuchsia)
    edge((6, 3), (8, 2), text(fill: fuchsia)[$k_!$], label-side: center, "->", stroke: fuchsia)
    edge((8, 2), (9, 3), text(fill: fuchsia)[$R ol(g)_*$], label-side: center, "->", stroke: fuchsia)
    edge((7, 1), (8, 2), [$R tilde(f)_*$], label-side: center, "->")
  }, crossing-fill: thm-box-curr-color(), node-fill: thm-box-curr-color(), node-inset: 4pt, spacing: 1.6em))
  待证等式的两边都从洋红色路径走到绿色路径。由 $T$ 的构造与方块拼接的相容性（如 @open-proper-compat-naturality 所示），有：
  $
    T(chi, id_X, ell' compose j', ell compose j) = T(chi, phi, ell', ell) j'_! compose ell_! T(phi, id_X, j', j)
  $
  换言之，待证等式左端的自然变换正是红色路径，右端的自然变换则是蓝色路径，如图所示。

  由自然性，红色路径的第 1、2 步可以按任意顺序施加。红色路径的第 2 步正是蓝色路径的第 1 步，故可将其消去。于是只需证明：红色路径的第 1 步接第 3 步，等于蓝色路径的第 2 步接第 3 步。事实上，两条路径都是借助自然变换 $T$，把中间立方体上的复合合并成一步；又因 $T$ 与方块拼接相容，二者相等：
  $
    & R tilde(f)_* T(chi, psi, ell', ell) compose T(tilde(f), ol(f), ell, k) R phi_* = T(tilde(f) compose chi, ol(f) compose phi, ell', k) \
    =& T(psi compose tilde(f)', ol(f)', ell', k) = R psi_* T(tilde(f)', ol(f)', ell', k') compose T(psi, id_Y, k', k) R ol(f)'_*
  $
  至此证明了当其中一个紧化支配另一个时，同构与 $(f, g)$ 紧化的选取无关。一般情形则由下述引理推出：

  #lemma[
    对 $(f, g)$ 的任意两个紧化，存在 $(f, g)$ 的第三个紧化同时支配它们。
  ]
  #proof[
    考虑 $(f, g)$ 的两个紧化：
    // https://q.uiver.app/#r=typst&q=WzAsNixbMCwyLCJYIl0sWzMsMiwiWSJdLFs2LDIsIloiXSxbMiwxLCJvbChYKV9pIl0sWzUsMSwib2woWSlfaSJdLFs0LDAsInRpbGRlKFgpX2kiXSxbMCwxLCJmIiwxXSxbMSwyLCJnIiwxXSxbMCwzLCJqX2kiLDFdLFszLDUsImVsbF9pIiwxXSxbMywxLCJvbChmKV9pIiwxXSxbMSw0LCJrX2kiLDFdLFs0LDIsIm9sKGcpX2kiLDFdLFs1LDQsInRpbGRlKGYpX2kiLDFdXQ==
    #context align(center, diagram({
      node((0, 2), [$X$])
      node((3, 2), [$Y$])
      node((6, 2), [$Z$])
      node((2, 1), [$ol(X)_i$])
      node((5, 1), [$ol(Y)_i$])
      node((4, 0), [$tilde(X)_i$])
      edge((0, 2), (3, 2), [$f$], label-side: center, "->")
      edge((3, 2), (6, 2), [$g$], label-side: center, "->")
      edge((0, 2), (2, 1), [$j_i$], label-side: center, "->")
      edge((2, 1), (4, 0), [$ell_i$], label-side: center, "->")
      edge((2, 1), (3, 2), [$ol(f)_i$], label-side: center, "->")
      edge((3, 2), (5, 1), [$k_i$], label-side: center, "->")
      edge((5, 1), (6, 2), [$ol(g)_i$], label-side: center, "->")
      edge((4, 0), (5, 1), [$tilde(f)_i$], label-side: center, "->")
    }, crossing-fill: thm-box-curr-color(), spacing: 1.6em))
    其中 $i = 1, 2$。由 @compactification-filtered，可以选取 $f$ 的紧化 $X ->^j ol(X) ->^(ol(f)) Y$ 与 $g$ 的紧化 $Y ->^k ol(Y) ->^(ol(g)) Z$，并取紧化之间的态射 $phi_i: ol(X) -> ol(X)_i, psi_i: ol(Y) -> ol(Y)_i$（$i=1,2$）。要得到同时支配这两个给定紧化的 $(f, g)$ 紧化，只需找到 $k compose ol(f): ol(X) -> ol(Y)$ 的紧化 $ol(X) ->^ell tilde(X) ->^(tilde(f)) ol(Y)$，以及使下图交换的态射 $chi_i: tilde(X) -> tilde(X)_i, i = 1,2$：
    // https://q.uiver.app/#r=typst&q=WzAsOSxbMCwwLCJvbChYKV8xIl0sWzEsMCwidGlsZGUoWClfMSJdLFsyLDAsIm9sKFkpXzEiXSxbMCwxLCJvbChYKSJdLFsxLDEsInRpbGRlKFgpIl0sWzIsMSwib2woWSkiXSxbMCwyLCJvbChYKV8yIl0sWzEsMiwidGlsZGUoWClfMiJdLFsyLDIsIm9sKFkpXzIiXSxbMCwxLCJlbGxfMSJdLFsxLDIsInRpbGRlKGYpXzEiXSxbMywwLCJwaGlfMSJdLFszLDYsInBoaV8yIiwyXSxbNSwyLCJwc2lfMSIsMl0sWzUsOCwicHNpXzIiXSxbNiw3LCJlbGxfMiIsMl0sWzcsOCwidGlsZGUoZilfMiIsMl0sWzMsNCwiZWxsIiwyXSxbNCw1LCJ0aWxkZShmKSIsMl0sWzQsMSwiY2hpXzEiLDJdLFs0LDcsImNoaV8yIl1d
    #align(center, diagram({
      node((-1, -1), [$ol(X)_1$])
      node((0, -1), [$tilde(X)_1$])
      node((1, -1), [$ol(Y)_1$])
      node((-1, 0), [$ol(X)$])
      node((0, 0), [$tilde(X)$])
      node((1, 0), [$ol(Y)$])
      node((-1, 1), [$ol(X)_2$])
      node((0, 1), [$tilde(X)_2$])
      node((1, 1), [$ol(Y)_2$])
      edge((-1, -1), (0, -1), [$ell_1$], label-side: left, "->")
      edge((0, -1), (1, -1), [$tilde(f)_1$], label-side: left, "->")
      edge((-1, 0), (-1, -1), [$phi_1$], label-side: left, "->")
      edge((-1, 0), (-1, 1), [$phi_2$], label-side: right, "->")
      edge((1, 0), (1, -1), [$psi_1$], label-side: right, "->")
      edge((1, 0), (1, 1), [$psi_2$], label-side: left, "->")
      edge((-1, 1), (0, 1), [$ell_2$], label-side: right, "->")
      edge((0, 1), (1, 1), [$tilde(f)_2$], label-side: right, "->")
      edge((-1, 0), (0, 0), [$ell$], label-side: right, "-->")
      edge((0, 0), (1, 0), [$tilde(f)$], label-side: right, "-->")
      edge((0, 0), (0, -1), [$chi_1$], label-side: right, "-->")
      edge((0, 0), (0, 1), [$chi_2$], label-side: left, "-->")
    }))
    对 $i = 1, 2$，作纤维积 $T_i = tilde(X)_i times_(ol(Y)_i) ol(Y)$ 与投影 $t_i: T_i -> ol(Y), s_i: T_i -> tilde(X)_1$。则 $s_i, t_i$ 紧合。考虑态射 $ell_i compose phi_i: ol(X) -> tilde(X)_i$ 与 $k compose ol(f): ol(X) -> ol(Y)$。于是：
    $
      psi_i compose k compose ol(f) = tilde(f)_i compose ell_i compose phi_i
    $
    事实上，$tilde(f)_i compose ell_i compose phi_i = k_i compose ol(f)_i compose phi_i = k_i compose ol(f) = psi_i compose k compose ol(f)$，因为 $phi_i, psi_i$ 是紧化之间的态射。因此存在态射 $q_i: ol(X) -> T_i$，使下图交换：
    // https://q.uiver.app/#r=typst&q=WzAsNixbMCwwLCJvbChYKSJdLFsxLDAsIlRfaSJdLFsyLDAsIm9sKFkpIl0sWzAsMSwib2woWClfaSJdLFsxLDEsInRpbGRlKFgpX2kiXSxbMiwxLCJvbChZKV9pIl0sWzAsMywicGhpX2kiLDJdLFsyLDUsInBzaV9pIl0sWzMsNCwiZWxsX2kiLDJdLFs0LDUsInRpbGRlKGYpX2kiLDJdLFswLDEsInFfaSJdLFsxLDIsInRfaSJdLFsxLDQsInNfMSJdXQ==
    #align(center, diagram({
      node((-1, 0), [$ol(X)$])
      node((0, 0), [$T_i$])
      node((1, 0), [$ol(Y)$])
      node((-1, 1), [$ol(X)_i$])
      node((0, 1), [$tilde(X)_i$])
      node((1, 1), [$ol(Y)_i$])
      edge((-1, 0), (-1, 1), [$phi_i$], label-side: right, "->")
      edge((1, 0), (1, 1), [$psi_i$], label-side: left, "->")
      edge((-1, 1), (0, 1), [$ell_i$], label-side: right, "->")
      edge((0, 1), (1, 1), [$tilde(f)_i$], label-side: right, "->")
      edge((-1, 0), (0, 0), [$q_i$], label-side: left, "->")
      edge((0, 0), (1, 0), [$t_i$], label-side: left, "->")
      edge((0, 0), (0, 1), [$s_i$], label-side: left, "->")
    }))
    现在 $phi_i, s_i$ 紧合，$ell_i$ 是开浸入，故 $q_i$ 是分离有限型的 $tilde(X)_i$-概形之间的态射。于是 $q_i$ 分离且有限型，可以作 $q_i$ 的紧化 $ol(X) ->^(ell'_i) tilde(X)'_i ->^(h_i) T_i$。取 $tilde(f)'_i = t_i compose h_i: tilde(X)'_i -> ol(Y)_i$ 与 $chi_i = s_i compose h_i: tilde(X)'_i -> tilde(X)_i$。由于 $t_i$ 紧合，$ol(X) ->^(ell'_i) tilde(X)'_i ->^(t_i compose h_i) ol(Y)$ 是 $k compose ol(f): ol(X) -> ol(Y)$ 的紧化，并使下图交换：
    // https://q.uiver.app/#r=typst&q=WzAsNixbMCwwLCJvbChYKSJdLFsxLDAsInRpbGRlKFgpJ19pIl0sWzIsMCwib2woWSkiXSxbMCwxLCJvbChYKV9pIl0sWzEsMSwidGlsZGUoWClfaSJdLFsyLDEsIm9sKFkpX2kiXSxbMCwzLCJwaGlfaSIsMl0sWzIsNSwicHNpX2kiXSxbMyw0LCJlbGxfaSIsMl0sWzQsNSwidGlsZGUoZilfaSIsMl0sWzAsMSwiZWxsIl0sWzEsMiwidGlsZGUoZiknX2kiXSxbMSw0LCJjaGlfaSJdXQ==
    #align(center, diagram({
      node((-1, 0), [$ol(X)$])
      node((0, 0), [$tilde(X)'_i$])
      node((1, 0), [$ol(Y)$])
      node((-1, 1), [$ol(X)_i$])
      node((0, 1), [$tilde(X)_i$])
      node((1, 1), [$ol(Y)_i$])
      edge((-1, 0), (-1, 1), [$phi_i$], label-side: right, "->")
      edge((1, 0), (1, 1), [$psi_i$], label-side: left, "->")
      edge((-1, 1), (0, 1), [$ell_i$], label-side: right, "->")
      edge((0, 1), (1, 1), [$tilde(f)_i$], label-side: right, "->")
      edge((-1, 0), (0, 0), [$ell$], label-side: left, "->")
      edge((0, 0), (1, 0), [$tilde(f)'_i$], label-side: left, "->")
      edge((0, 0), (0, 1), [$chi_i$], label-side: left, "->")
    }))
    取 $ol(X) -> ol(Y)$ 的一个紧化 $tilde(X)$，使它同时支配 $tilde(X)_1$ 与 $tilde(X)_2$，便完成了证明。
  ]

  (2) 如下构造基变换同构：取 $f$ 的紧化 $X ->^j ol(X) ->^(ol(f)) Y$，并作拉回图表：
  // https://q.uiver.app/#r=typst&q=WzAsNixbMCwxLCJYIl0sWzEsMSwib2woWCkiXSxbMiwxLCJZIl0sWzIsMCwiWSciXSxbMSwwLCJvbChYKSciXSxbMCwwLCJYJyJdLFsxLDIsIm9sKGYpIiwyXSxbMCwxLCJqIiwyXSxbNSw0LCJqJyJdLFs0LDMsIm9sKGYpJyJdLFszLDIsImciXSxbNCwxLCJvbChnKSciXSxbNSwwLCJnJyIsMl1d
  #align(center, diagram({
    node((0, 1), [$X$])
    node((1, 1), [$ol(X)$])
    node((2, 1), [$Y$])
    node((2, 0), [$Y'$])
    node((1, 0), [$ol(X)'$])
    node((0, 0), [$X'$])
    node((0.3, 0.3), $cart$)
    node((1.3, 0.3), $cart$)
    edge((1, 1), (2, 1), [$ol(f)$], label-side: right, "->")
    edge((0, 1), (1, 1), [$j$], label-side: right, "->")
    edge((0, 0), (1, 0), [$j'$], label-side: left, "->")
    edge((1, 0), (2, 0), [$ol(f)'$], label-side: left, "->")
    edge((2, 0), (2, 1), [$g$], label-side: left, "->")
    edge((1, 0), (1, 1), [$ol(g)'$], label-side: left, "->")
    edge((0, 0), (0, 1), [$g'$], label-side: right, "->")
  }))
  注意 $j'$ 是开浸入、$ol(f)'$ 紧合，故 $X' ->^(j') ol(X)' ->^(ol(f)') Y'$ 是 $f': X' -> Y'$ 的紧化。

  然后定义基变换 $g^(-1) R f_! cal(K) -> R f'_! g'^(-1) cal(K)$ 为如下复合：
  $
    g^(-1) R f_! cal(K) cong g^(-1) R ol(f)_* j_! cal(K) ->^tilde R ol(f)'_* ol(g)'^(-1) j_! cal(K) ->^tilde R ol(f)'_* j'_! g'^(-1) cal(K) cong R f'_! g'^(-1) cal(K)
  $
  其中第一个映射是 @base-change-constr 中定义的基变换映射，由紧合基变换它是同构；第二个映射是 @etale-lower-shriek-first-props (4) 中的同构。

  照例，还需证明此映射良定义且自然。这部分只是记账，建议读者跳过。简言之，要证明 @open-proper-compat 中的同构、基变换映射，以及 @etale-lower-shriek-first-props (4) 中零延拓的基变换映射三者相容。

  #lemma(name: <open-proper-compat-with-bc>)[
    记：

    - 将 @base-change-constr 中的基变换映射记为 $BC(g', g, f', f)$；

    - 将 @etale-lower-shriek-first-props (4) 中零延拓的基变换记为 $BC_! (g', g, f', f)$；

    - 将 @open-proper-compat 中的同构记为 $T(f_1, f_2, j_X, j_Y)$。

    今设有交换立方体：
    // https://q.uiver.app/#r=typst&q=WzAsOCxbMCwxLCJYJ18xIl0sWzIsMCwiWSdfMSJdLFsxLDIsIlgnXzIiXSxbMywxLCJZJ18yIl0sWzAsNCwiWF8xIl0sWzEsNSwiWF8yIl0sWzIsMywiWV8xIl0sWzMsNCwiWV8yIl0sWzQsNiwiZl8xIiwxXSxbNSw3LCJmXzIiLDFdLFs0LDUsImpfWCIsMV0sWzYsNywial9ZIiwxXSxbMCwxLCJmJ18xIiwxXSxbMiwzLCJmJ18yIiwxXSxbMCwyLCJqJ19YIiwxXSxbMSwzLCJqJ19ZIiwxXSxbMyw3LCJnXzIiLDFdLFsxLDYsImdfMSIsMSx7ImxhYmVsX3Bvc2l0aW9uIjo5MH1dLFsyLDUsImcnXzIiLDEseyJsYWJlbF9wb3NpdGlvbiI6MTB9XSxbMCw0LCJnJ18xIiwxXV0=
    #context align(center, diagram({
      node((0, 1), [$X'_1$])
      node((2, 0), [$Y'_1$])
      node((1, 2), [$X'_2$])
      node((3, 1), [$Y'_2$])
      node((0, 4), [$X_1$])
      node((1, 5), [$X_2$])
      node((2, 3), [$Y_1$])
      node((3, 4), [$Y_2$])
      edge((0, 4), (1, 5), [$j_X$], label-side: center, "->")
      edge((2, 3), (3, 4), [$j_Y$], label-side: center, "->")
      edge((0, 1), (1, 2), [$j'_X$], label-side: center, "->")
      edge((2, 0), (3, 1), [$j'_Y$], label-side: center, "->")
      edge((3, 1), (3, 4), [$g_2$], label-side: center, "->")
      edge((2, 0), (2, 3), [$g_1$], label-side: center, label-pos: 0.85, "->")
      edge((1, 2), (1, 5), [$g'_2$], label-side: center, label-pos: 0.15, "->")
      edge((0, 1), (0, 4), [$g'_1$], label-side: center, "->")
      edge((0, 4), (2, 3), [$f_1$], label-side: center, "->", label-pos: 0.3)
      edge((1, 5), (3, 4), [$f_2$], label-side: center, "->")
      edge((0, 1), (2, 0), [$f'_1$], label-side: center, "->")
      edge((1, 2), (3, 1), [$f'_2$], label-side: center, "->", label-pos: 0.7)
    }, spacing: (2.5em, 1.6em), crossing-fill: thm-box-curr-color()))
    其中 $f_1, f_2, f'_1, f'_2$ 紧合，$j_X, j_Y, j'_X, j'_Y$ 是开浸入，四个竖直面都是拉回方块。则函子 $D_#[tor] ((X_1)_et, Lambda) -> D_#[tor] ((Y'_2)_et, Lambda)$ 上的下述两个自然变换相同：
    // https://q.uiver.app/#r=typst&q=WzAsNixbMCwxLCJnXzJeKC0xKSBqXyhZLCEpIFIgZl8oMSwqKSJdLFsxLDAsImdfMl4oLTEpIFIgZl8oMiwqKSBqXyhYLCEpIl0sWzIsMCwiUiBmJ18oMiwqKSBnJ18yXigtMSkgal8oWCwhKSJdLFszLDEsIlIgZidfKDIsKikgaidfKFgsISkgZydfMV4oLTEpIl0sWzEsMiwiaidfKFksISkgZ18xXigtMSkgUiBmXygxLCopIl0sWzIsMiwiaidfKFksISkgUiBmJ18oMSwqKSBnJ18xXigtMSkiXSxbMCwxLCJnXzJeKC0xKSBUKGZfMSwgZl8yLCBqX1gsal9ZKSIsMV0sWzEsMiwiQkMoZydfMiwgZ18yLCBmJ18yLCBmXzIpIGpfKFgsISkiXSxbMiwzLCJSIGYnXygyLCopIEJDXyEgKGcnXzEsIGcnXzIsIGonX1gsIGpfWCkiLDFdLFs1LDMsIlQoZidfMSwgZidfMiwgaidfWCwgaidfWSkiLDFdLFs0LDUsImonXyhZLCEpIEJDKGcnXzEsIGdfMSwgZidfMSwgZl8xKSIsMl0sWzAsNCwiQkNfISAoZ18xLCBnXzIsIGonX1ksIGpfWSkgUiBmXygxLCopIiwyXV0=
    #context align(center, diagram({
      node((0, 1), [$g_2^(-1) j_(Y,!) R f_(1,*)$])
      node((1, 0), [$g_2^(-1) R f_(2,*) j_(X,!)$])
      node((2, 0), [$R f'_(2,*) g'_2^(-1) j_(X,!)$])
      node((3, 1), [$R f'_(2,*) j'_(X,!) g'_1^(-1)$])
      node((1, 2), [$j'_(Y,!) g_1^(-1) R f_(1,*)$])
      node((2, 2), [$j'_(Y,!) R f'_(1,*) g'_1^(-1)$])
      edge((0, 1), (1, 0), [$g_2^(-1) T(f_1, f_2, j_X,j_Y)$], label-side: center, "->")
      edge((1, 0), (2, 0), [$BC(g'_2, g_2, f'_2, f_2) j_(X,!)$], label-side: left, "->")
      edge((2, 0), (3, 1), [$R f'_(2,*) BC_! (g'_1, g'_2, j'_X, j_X)$], label-side: center, "->")
      edge((2, 2), (3, 1), [$T(f'_1, f'_2, j'_X, j'_Y) g'_1^(-1)$], label-side: center, "->")
      edge((1, 2), (2, 2), [$j'_(Y,!) BC(g'_1, g_1, f'_1, f_1)$], label-side: right, "->")
      edge((0, 1), (1, 2), [$BC_! (g_1, g_2, j'_Y, j_Y) R f_(1,*)$], label-side: center, "->")
    }, spacing: (6.5em, 4em), label-size: 0.8em, crossing-fill: thm-box-curr-color()))
  ]
  #proof[
    注意上面六边形图的所有箭头都是自然同构。设 $i'_Y: W' -> Y'_2$ 是 $j'_Y$ 的互补闭浸入。又 $i'_Y^(-1) j'_(Y,!) g_1^(-1) R f_(1,*) = 0$，故对上面的图施加 $i'_Y^(-1)$，得到一张全为零的图。因此由零延拓三角，只需证明施加 $j_Y^(-1)$ 后图表交换。

    在下述论证中，为方便起见，把 $id$ 与 $j_X^(-1) j_(X,!)$ 等同（不再追踪相应的自然同构）。

    - 先展开最神秘的 $T$ 项。检查 @open-proper-compat 的证明可知，#h(1fr)
      $
        & j'_Y^(-1) T(f'_1, f'_2, j'_X, j'_Y) g'_1^(-1) = (BC(j'_X, j'_Y, f'_1, f'_2) j'_(X,!))^(-1) g'_1^(-1)\
        :& j'_Y^(-1) R f'_(2,*) j'_(X,!) g'_1^(-1) <- R f'_(1,*) j'_X^(-1) j'_(X,!) g'_1^(-1) = R f'_(1,*) g'_1^(-1)
      $
      以及：
      $
        & j'_Y^(-1) g_2^(-1) T(f_1, f_2, j_X, j_Y) = g_1^(-1) j_Y^(-1) T(f_1, f_2, j_X, j_Y) = g_1^(-1) (BC(j_X, j_Y, f_1, f_2) j_(X,!))^(-1) \
        :& j'_Y^(-1) g_2^(-1) R f_(2,*) j_(X,!) = g_1^(-1) j_Y^(-1) R f_(2,*) j_(X,!) <- g_1^(-1) R f_(1,*) j_X^(-1) j_(X,!) = g_1^(-1) R f_(1,*) = g_1^(-1) j_Y^(-1) j_(Y,!) R f_(1,*) = j'_Y^(-1) g_2^(-1) j_(Y,!) R f_(1,*)
      $

    - 接着看左下箭头 $BC_! (g_1, g_2, j'_Y, j_Y) R f_(1,*)$。展开定义可知，这个同构为：
      $
        BC_! (g_1, g_2, j'_Y, j_Y): g_2^(-1) j_(Y,!) -> j'_(Y,!) g_1^(-1)
      $
      施加 $j'_Y^(-1)$ 后，只要把下面两式等同起来，这个同构便正是 $id_(g_1^(-1))$：
      $
        j'_Y^(-1) g_2^(-1) j_(Y,!) = g_1^(-1) j_Y^(-1) j_(Y,!) = g_1^(-1)
      $
      与 $j'_Y^(-1) j'_(Y,!) g_1^(-1) = g_1^(-1)$。

      于是，施加 $j'_Y^(-1)$ 并把此映射的两端用 $g_1^(-1) R f_(1,*)$ 等同起来之后，它便成为恒等映射。

    因此在这些等同之下，只需证明下述五边形图交换：
    // https://q.uiver.app/#r=typst&q=WzAsNSxbMCwwLCJqJ19ZXigtMSkgZ18yXigtMSkgUiBmXygyLCopIGpfKFgsISkiXSxbMCwyLCJnXzFeKC0xKSBSIGZfKDEsKikiXSxbMiwyLCJSIGYnXygxLCopIGcnXzFeKC0xKSJdLFs0LDEsImonX1leKC0xKSBSIGYnXygyLCopIGonXyhYLCEpIGcnXzFeKC0xKSJdLFsyLDAsImonX1leKC0xKSBSIGYnXygyLCopIGcnXzJeKC0xKSBqXyhYLCEpIl0sWzEsMiwiQkMoZydfMSxnXzEsZidfMSxmXzEpIiwyXSxbMCw0LCJqJ19ZXigtMSkgQkMoZydfMixnXzIsZidfMixmXzIpIGpfKFgsISkiXSxbMCwxLCJnXzFeKC0xKSBCQyhqX1gsIGpfWSwgZl8xLCBmXzIpIGpfKFgsISkiLDJdLFs0LDMsImpfWV4oLTEpIFIgZl8oMiwqKSBCQ18hIChnXzEnLCBnXzInLCBqJ19YLCBqJ19ZKSJdLFszLDIsIkJDKGonX1gsIGonX1ksIGYnXzEsIGYnXzIpIGonXyhYLCEpIGcnXzFeKC0xKSJdXQ==
    #context align(center, diagram({
      node((-2, -1), [$j'_Y^(-1) g_2^(-1) R f_(2,*) j_(X,!)$])
      node((-2, 1), [$g_1^(-1) R f_(1,*)$])
      node((0, 1), [$R f'_(1,*) g'_1^(-1)$])
      node((2, 0), [$j'_Y^(-1) R f'_(2,*) j'_(X,!) g'_1^(-1)$])
      node((0, -1), [$j'_Y^(-1) R f'_(2,*) g'_2^(-1) j_(X,!)$])
      edge((-2, 1), (0, 1), [$BC(g'_1,g_1,f'_1,f_1)$], label-side: right, "->")
      edge((-2, -1), (0, -1), [$j'_Y^(-1) BC(g'_2,g_2,f'_2,f_2) j_(X,!)$], label-side: left, "->")
      edge((-2, -1), (-2, 1), [$g_1^(-1) BC(j_X, j_Y, f_1, f_2) j_(X,!)$], label-side: center, "->")
      edge((0, -1), (2, 0), [$j_Y^(-1) R f_(2,*) BC_! (g_1', g_2', j'_X, j'_Y)$], label-side: center, "->")
      edge((2, 0), (0, 1), [$BC(j'_X, j'_Y, f'_1, f'_2) j'_(X,!) g'_1^(-1)$], label-side: center, "->")
    }, label-size: 0.8em, spacing: (3.5em, 3em), crossing-fill: thm-box-curr-color()))

    现在看最右边的两个箭头。那里的自然变换作用在函子复合的不同部分，故可应用自然性，得到交换图：
    // https://q.uiver.app/#r=typst&q=WzAsNCxbMiwyLCJSIGYnXygxLCopIGcnXzFeKC0xKSBqX1heKC0xKSBqXyhYLCEpIl0sWzQsMSwiaidfWV4oLTEpIFIgZidfKDIsKikgaidfKFgsISkgZydfMV4oLTEpIl0sWzIsMCwiaidfWV4oLTEpIFIgZidfKDIsKikgZydfMl4oLTEpIGpfKFgsISkiXSxbMCwxLCJSIGYnXygxLCopIGonX1heKC0xKSBnJ18yXigtMSkgal8oWCwhKSJdLFsyLDEsImpfWV4oLTEpIFIgZl8oMiwqKSBCQ18hIChnXzEnLCBnXzInLCBqJ19YLCBqJ19ZKSIsMV0sWzEsMCwiQkMoaidfWCwgaidfWSwgZidfMSwgZidfMikgaidfKFgsISkgZydfMV4oLTEpIiwxXSxbMiwzLCJCQyhqJ19YLCBqJ19ZLCBmJ18xLCBmJ18yKSBqJ18oWCwhKSBnJ18xXigtMSkiLDFdLFszLDAsIlIgZidfKDEsKikgaidfWF4oLTEpIEJDXyEgIChnJ18xLCBnJ18yLCBqJ19YLCBqJ19ZKSIsMV1d
    #context align(center, diagram({
      node((0, 1), [$R f'_(1,*) j'_X^(-1) j'_(X,!) g'_1^(-1)$])
      node((2, 0), [$j'_Y^(-1) R f'_(2,*) j'_(X,!) g'_1^(-1)$])
      node((0, -1), [$j'_Y^(-1) R f'_(2,*) g'_2^(-1) j_(X,!)$])
      node((-2, 0), [$R f'_(1,*) j'_X^(-1) g'_2^(-1) j_(X,!)$])
      edge((0, -1), (2, 0), [$j_Y^(-1) R f_(2,*) BC_! (g_1', g_2', j'_X, j'_Y)$], label-side: center, "->")
      edge((2, 0), (0, 1), [$BC(j'_X, j'_Y, f'_1, f'_2) j'_(X,!) g'_1^(-1)$], label-side: center, "->")
      edge((0, -1), (-2, 0), [$BC(j'_X, j'_Y, f'_1, f'_2) j'_(X,!) g'_1^(-1)$], label-side: center, "->")
      edge((-2, 0), (0, 1), [$R f'_(1,*) j'_X^(-1) BC_!  (g'_1, g'_2, j'_X, j'_Y)$], label-side: center, "->")
    }, crossing-fill: thm-box-curr-color(), label-size: 0.8em))
    如上所述，只要等同 $j'_X^(-1) g'_2^(-1) j_(X,!) = j'_X^(-1) j'_(X,!) g'_1^(-1) = g'_1^(-1)$，态射 $j'_X^(-1) BC_!  (g'_1, g'_2, j'_X, j'_Y)$ 便成为恒等映射。于是可把最右边的两个箭头换成一个箭头。在底边箭头上插入 $j_X^(-1) j_(X,!)$，便只需证明下述方块交换：
    // https://q.uiver.app/#r=typst&q=WzAsNCxbMCwwLCJqJ19ZXigtMSkgZ18yXigtMSkgUiBmXygyLCopIGpfKFgsISkiXSxbMCwyLCJnXzFeKC0xKSBSIGZfKDEsKikiXSxbMiwyLCJSIGYnXygxLCopIGcnXzFeKC0xKSJdLFsyLDAsImonX1leKC0xKSBSIGYnXygyLCopIGcnXzJeKC0xKSBqXyhYLCEpIl0sWzEsMiwiQkMoZydfMSxnXzEsZidfMSxmXzEpIGpfWF4oLTEpIGpfKFgsISkiLDJdLFswLDMsImonX1leKC0xKSBCQyhnJ18yLGdfMixmJ18yLGZfMikgal8oWCwhKSJdLFswLDEsImdfMV4oLTEpIEJDKGpfWCwgal9ZLCBmXzEsIGZfMikgal8oWCwhKSIsMV0sWzMsMiwiQkMoaidfWCwgaidfWSwgZidfMSwgZidfMikgZydfMl4oLTEpIGpfKFgsISkiLDFdXQ==
    #context align(center, diagram({
      node((0, 0), [$j'_Y^(-1) g_2^(-1) R f_(2,*) j_(X,!)$])
      node((0, 2), [$g_1^(-1) R f_(1,*)$])
      node((2, 2), [$R f'_(1,*) g'_1^(-1)$])
      node((2, 0), [$j'_Y^(-1) R f'_(2,*) g'_2^(-1) j_(X,!)$])
      edge((0, 2), (2, 2), [$BC(g'_1,g_1,f'_1,f_1) j_X^(-1) j_(X,!)$], label-side: right, "->")
      edge((0, 0), (2, 0), [$j'_Y^(-1) BC(g'_2,g_2,f'_2,f_2) j_(X,!)$], label-side: left, "->")
      edge((0, 0), (0, 2), [$g_1^(-1) BC(j_X, j_Y, f_1, f_2) j_(X,!)$], label-side: center, "->")
      edge((2, 0), (2, 2), [$BC(j'_X, j'_Y, f'_1, f'_2) g'_2^(-1) j_(X,!)$], label-side: center, "->")
    }, crossing-fill: thm-box-curr-color(), label-size: 0.8em, spacing: (3.5em, 3em)))

    换言之，只需证明：
    $
      BC(j'_X, j'_Y, f'_1, f'_2) g'_2^(-1) compose j'_Y^(-1) BC(g'_2,g_2,f'_2,f_2) = BC(g'_1,g_1,f'_1,f_1) j_X^(-1) compose g_1^(-1) BC(j_X, j_Y, f_1, f_2)
    $
    这正是基变换与竖直拼接的相容性（见 @base-change-naturality）：两端都等于：
    $
      BC(g'_2 compose j'_X, g_2 compose j'_Y, f'_1, f_2) = BC(j_X compose g'_1, j_Y compose g_1, f'_1, f_2)
    $
  ]
  现在可以证明 $R f_!$ 的基变换映射良定义且自然了。先证良定义性，即与紧化选取无关：设 $X ->^(j_i) ol(X)_i ->^(ol(f)_i) Y$ 是两个紧化，要证它们定义同一个基变换映射。由 @compactification-filtered 取同时支配二者的第三个紧化。这两个紧化与第三个紧化定义的基变换映射若相同，问题即化归为：存在紧化之间的态射 $phi: ol(X)_2 -> ol(X)_1$。作基变换：
  // https://q.uiver.app/#r=typst&q=WzAsOCxbMCwxLCJYJyJdLFsyLDAsIm9sKFgpJ18xIl0sWzEsMiwib2woWCknXzEiXSxbMywxLCJZJyJdLFswLDQsIlgiXSxbMSw1LCJvbChYKV8yIl0sWzIsMywib2woWClfMSJdLFszLDQsIlkiXSxbNCw2LCJqXzEiLDEseyJsYWJlbF9wb3NpdGlvbiI6MzB9XSxbNSw3LCJmXzIiLDFdLFs0LDUsImpfMiIsMV0sWzYsNywial9ZIiwxXSxbMCwxLCJqJ18xIiwxXSxbMiwzLCJvbChmKSdfMiIsMSx7ImxhYmVsX3Bvc2l0aW9uIjo3MH1dLFswLDIsImonXzIiLDFdLFsxLDMsIm9sKGYpJ18xIiwxXSxbMyw3LCJnIiwxXSxbMSw2LCJvbChnKV8xIiwxLHsibGFiZWxfcG9zaXRpb24iOjkwfV0sWzIsNSwib2woZylfMiIsMSx7ImxhYmVsX3Bvc2l0aW9uIjoxMH1dLFswLDQsImcnIiwxXSxbNSw2LCJwaGkiLDFdLFsyLDEsInBoaSciLDFdXQ==
  #context align(center, diagram({
    node((0, 1), [$X'$])
    node((2, 0), [$ol(X)'_1$])
    node((1, 2), [$ol(X)'_2$])
    node((3, 1), [$Y'$])
    node((0, 4), [$X$])
    node((1, 5), [$ol(X)_2$])
    node((2, 3), [$ol(X)_1$])
    node((3, 4), [$Y$])
    edge((0, 4), (2, 3), [$j_1$], label-side: center, label-pos: 0.3, "->")
    edge((1, 5), (3, 4), [$ol(f)_2$], label-side: center, "->")
    edge((0, 4), (1, 5), [$j_2$], label-side: center, "->")
    edge((2, 3), (3, 4), [$ol(f)_1$], label-side: center, "->")
    edge((0, 1), (2, 0), [$j'_1$], label-side: center, "->")
    edge((1, 2), (3, 1), [$ol(f)'_2$], label-side: center, label-pos: 0.7, "->")
    edge((0, 1), (1, 2), [$j'_2$], label-side: center, "->")
    edge((2, 0), (3, 1), [$ol(f)'_1$], label-side: center, "->")
    edge((3, 1), (3, 4), [$g$], label-side: center, "->")
    edge((2, 0), (2, 3), [$ol(g)_1$], label-side: center, label-pos: 0.85, "->")
    edge((1, 2), (1, 5), [$ol(g)_2$], label-side: center, label-pos: 0.15, "->")
    edge((0, 1), (0, 4), [$g'$], label-side: center, "->")
    edge((1, 5), (2, 3), [$phi$], label-side: center, "->")
    edge((1, 2), (2, 0), [$phi'$], label-side: center, "->")
  }, spacing: (2.5em, 1.6em), crossing-fill: thm-box-curr-color()))

  于是，$R f_!$ 与 $R f'_!$ 各自由不同紧化给出的定义之间有如下等同：
  $
    R f_(1,*) j_(1,!) -->^(R f_(1,*) T(phi, id_X, j_2, j_1)) R f_(1,*) R phi_* j_(2,!) = R f_(2,*) j_(2,!) \

    R f'_(1,*) j'_(1,!) -->^(R f'_(1,*) T(phi', id_(X'), j'_2, j'_1)) R f'_(1,*) R phi'_* j'_(2,!) = R f'_(2,*) j'_(2,!)
  $

  // 为证明与紧化选取无关，只需证明下图交换：
  照例把 $D_#[tor] (X_et, Lambda)$ 简记为 $D(X)$。利用同构 $T$，用一个自然变换 $g^(-1) R ol(f)_(1,*) j_(1,!) -> R ol(f)'_(2,*) j'_(2,!) g'^(-1)$ 把两个紧化分别定义的基变换等同起来。于是在下图中：

  // https://q.uiver.app/#r=typst&q=WzAsOCxbMCwxLCJEKFgnKSJdLFsyLDAsIkQob2woWCknXzEpIl0sWzEsMiwiRChvbChYKSdfMSkiXSxbMywxLCJEKFknKSJdLFswLDQsIkQoWCkiXSxbMSw1LCJEKG9sKFgpXzIpIl0sWzIsMywiRChvbChYKV8xKSJdLFszLDQsIkQoWSkiXSxbNCw2LCJqXygxLCEpIiwxLHsibGFiZWxfcG9zaXRpb24iOjMwfV0sWzUsNywiUiBvbChmKV8oMiwqKSIsMV0sWzQsNSwial8oMiwhKSIsMV0sWzYsNywiUiBvbChmKV8oMSwqKSIsMV0sWzAsMSwiaidfKDEsISkiLDFdLFsyLDMsIlIgb2woZiknXygyLCopIiwxLHsibGFiZWxfcG9zaXRpb24iOjcwfV0sWzAsMiwiaidfKDIsISkiLDFdLFsxLDMsIlIgb2woZiknXygxLCopIiwxXSxbNywzLCJnXigtMSkiLDFdLFs2LDEsIm9sKGcpXzFeKC0xKSIsMSx7ImxhYmVsX3Bvc2l0aW9uIjo5MH1dLFs1LDIsIm9sKGcpXzJeKC0xKSIsMSx7ImxhYmVsX3Bvc2l0aW9uIjoxMH1dLFs0LDAsImcnXigtMSkiLDFdLFs1LDYsIlIgcGhpXyoiLDFdLFsyLDEsIlIgcGhpJ18qIiwxXV0=
  #context align(center, diagram({
    edge(..tune-2-mor-coords((3, 4), (2, 0), l: 0.9), text(fill: red)[$1,BC$], "=>", label-side: center, stroke: red, bend: -30deg)
    edge(..tune-2-mor-coords((2, 3), (0, 1), l: 0.42), text(fill: red)[$2,BC_!$], "=>", label-side: center, stroke: red, bend: 36deg, label-pos: 0.7)
    edge(..tune-2-mor-coords(midpoint((0, 1), (2, 0)), (1, 2), l: 0.2), text(fill: red)[$3,T$], "=>", label-side: center, stroke: red)

    edge(..tune-2-mor-coords(midpoint((0, 4), (2, 3)), (1, 5), l: 0.2), text(fill: blue)[$1,T$], "=>", label-side: center, stroke: blue, bend: -40deg)
    edge(..tune-2-mor-coords((3, 4), (2, 0), l: 0.9), text(fill: blue)[$2, BC$], "=>", label-side: center, stroke: blue, bend: 30deg)
    edge(..tune-2-mor-coords((2, 3), (1, 2), l: 0.15), text(fill: blue)[$3, BC$], "=>", label-side: center, stroke: blue)
    edge(..tune-2-mor-coords((1, 5), (0, 1)), text(fill: blue)[$4, BC_!$], "=>", label-side: center, stroke: blue)

    node((0, 1), [$D(X')$])
    node((2, 0), [$D(ol(X)'_1)$])
    node((1, 2), [$D(ol(X)'_2)$])
    node((3, 1), [$D(Y')$])
    node((0, 4), [$D(X)$])
    node((1, 5), [$D(ol(X)_2)$])
    node((2, 3), [$D(ol(X)_1)$])
    node((3, 4), [$D(Y)$])
    edge((0, 4), (2, 3), text(fill: fuchsia)[$j_(1,!)$], label-side: center, label-pos: 0.3, "->", stroke: fuchsia)
    edge((1, 5), (3, 4), [$R ol(f)_(2,*)$], label-side: center, "->")
    edge((0, 4), (1, 5), [$j_(2,!)$], label-side: center, "->")
    edge((2, 3), (3, 4), text(fill: fuchsia)[$R ol(f)_(1,*)$], label-side: center, "->", stroke: fuchsia)
    edge((0, 1), (2, 0), [$j'_(1,!)$], label-side: center, "->")
    edge((1, 2), (3, 1), text(fill: green)[$R ol(f)'_(2,*)$], label-side: center, label-pos: 0.7, "->", stroke: green)
    edge((0, 1), (1, 2), text(fill: green)[$j'_(2,!)$], label-side: center, "->", stroke: green)
    edge((2, 0), (3, 1), [$R ol(f)'_(1,*)$], label-side: center, "->")
    edge((3, 4), (3, 1), text(fill: fuchsia)[$g^(-1)$], label-side: center, "->", stroke: fuchsia)
    edge((2, 3), (2, 0), [$ol(g)_1^(-1)$], label-side: center, label-pos: 0.15, "->")
    edge((1, 5), (1, 2), [$ol(g)_2^(-1)$], label-side: center, label-pos: 0.85, "->")
    edge((0, 4), (0, 1), text(fill: green)[$g'^(-1)$], label-side: center, "->", stroke: green)
    edge((1, 5), (2, 3), [$R phi_*$], label-side: center, "->")
    edge((1, 2), (2, 0), [$R phi'_*$], label-side: center, "->")
  }, crossing-fill: thm-box-curr-color(),  spacing: (3.125em, 2em)))
  于是，由两个紧化定义的基变换都是从洋红色函子到绿色函子的路径。红色路径是 $ol(X)_1$ 定义的基变换，蓝色路径是 $ol(X)_2$ 定义的基变换（这里用了基变换的自然性，把沿 $R ol(f)_(2,*)$ 的基变换拆成两步）。由自然性，蓝色路径的第 1、2 步可以交换，故只需把红色路径的第 2、3 步与蓝色路径的第 1、3、4 步相比较，也就是比较左三角柱上的那部分路径。而对左三角柱上的概形态射（在 $X$ 与 $X'$ 上取恒等映射）应用前一个引理，便可知这两条路径相同。

  至此证明了良定义性。至于与拉回方块拼接的相容性，竖直拼接的相容性直接来自 $R f_*$ 的同一相容性；因此只剩水平拼接。设 $Z ->^h X ->^f Y$，其中两个态射都分离且有限型，取 $(h, f)$ 的一个紧化并作基变换：
  // https://q.uiver.app/#r=typst&q=WzAsMTIsWzAsMiwiWiciXSxbMywyLCJYJyJdLFs2LDIsIlknIl0sWzIsMSwib2woWiknIl0sWzUsMSwib2woWCknIl0sWzQsMCwidGlsZGUoWiknIl0sWzAsNSwiWiJdLFszLDUsIlgiXSxbNiw1LCJZIl0sWzIsNCwib2woWikiXSxbNSw0LCJvbChYKSJdLFs0LDMsInRpbGRlKFopIl0sWzYsNywiaCIsMV0sWzcsOCwiZiIsMV0sWzYsOSwiayIsMV0sWzksMTEsImVsbCIsMSx7ImxhYmVsX3Bvc2l0aW9uIjo3MH1dLFs3LDEwLCJqIiwxXSxbOSw3LCJvbChoKSIsMV0sWzEwLDgsIm9sKGYpIiwxXSxbMTEsMTAsInRpbGRlKGgpIiwxXSxbMCwxLCJoJyIsMV0sWzEsMiwiZiciLDFdLFswLDMsImsnIiwxXSxbMyw1LCJlbGwnIiwxXSxbMSw0LCJqIiwxXSxbMywxLCJvbChoKSciLDFdLFs0LDIsIm9sKGYpJyIsMV0sWzUsNCwidGlsZGUoaCknIiwxXSxbMiw4LCJnIiwxLHsibGFiZWxfcG9zaXRpb24iOjIwfV0sWzEsNywiZyciLDEseyJsYWJlbF9wb3NpdGlvbiI6MjB9XSxbMCw2LCJnJyciLDEseyJsYWJlbF9wb3NpdGlvbiI6MjB9XSxbMyw5LCJvbChnKSciLDFdLFs0LDEwLCJvbChnKSIsMV0sWzUsMTEsInRpbGRlKGcpIiwxLHsibGFiZWxfcG9zaXRpb24iOjkwfV1d
  #context align(center, diagram({
    node((0, 2), [$Z'$])
    node((3, 2), [$X'$])
    node((6, 2), [$Y'$])
    node((2, 1), [$ol(Z)'$])
    node((5, 1), [$ol(X)'$])
    node((4, 0), [$tilde(Z)'$])
    node((0, 5), [$Z$])
    node((3, 5), [$X$])
    node((6, 5), [$Y$])
    node((2, 4), [$ol(Z)$])
    node((5, 4), [$ol(X)$])
    node((4, 3), [$tilde(Z)$])
    edge((0, 5), (3, 5), [$h$], label-side: center, "->")
    edge((3, 5), (6, 5), [$f$], label-side: center, "->")
    edge((0, 5), (2, 4), [$k$], label-side: center, "->")
    edge((2, 4), (4, 3), [$ell$], label-side: center, label-pos: 0.7, "->")
    edge((3, 5), (5, 4), [$j$], label-side: center, "->")
    edge((2, 4), (3, 5), [$ol(h)$], label-side: center, "->")
    edge((5, 4), (6, 5), [$ol(f)$], label-side: center, "->")
    edge((4, 3), (5, 4), [$tilde(h)$], label-side: center, "->")
    edge((0, 2), (3, 2), [$h'$], label-side: center, "->")
    edge((3, 2), (6, 2), [$f'$], label-side: center, "->")
    edge((0, 2), (2, 1), [$k'$], label-side: center, "->")
    edge((2, 1), (4, 0), [$ell'$], label-side: center, "->")
    edge((3, 2), (5, 1), [$j'$], label-side: center, label-pos: 0.3, "->")
    edge((2, 1), (3, 2), [$ol(h)'$], label-side: center, "->")
    edge((5, 1), (6, 2), [$ol(f)'$], label-side: center, "->")
    edge((4, 0), (5, 1), [$tilde(h)'$], label-side: center, "->")
    edge((6, 2), (6, 5), [$g$], label-side: center, label-pos: 0.2, "->")
    edge((3, 2), (3, 5), [$g'$], label-side: center, label-pos: 0.2, "->")
    edge((0, 2), (0, 5), [$g''$], label-side: center, label-pos: 0.2, "->")
    edge((2, 1), (2, 4), [$ol(g)'$], label-side: center, "->")
    edge((5, 1), (5, 4), [$ol(g)$], label-side: center, "->")
    edge((4, 0), (4, 3), [$tilde(g)$], label-side: center, label-pos: 0.9, "->")
  }, crossing-fill: thm-box-curr-color(), spacing: 1.6em))
  于是上图的顶面是 $(h', f')$ 的紧化。把分别施于 $R h_!$ 与 $R f_!$ 的基变换，以及施于 $R(f compose f)_*$ 的基变换，都写成自然变换：
  $
    g^(-1) R ol(f)_* j_! R ol(h)_* k_! -> R ol(f)'_* R tilde(h)'_* ell'_! k'_! g''^(-1)
  $
  于是可在下图中标出这两个自然变换（即红色路径与蓝色路径）：
  // https://q.uiver.app/#r=typst&q=WzAsMTIsWzAsMSwiRChaJykiXSxbMywyLCJEKFgnKSJdLFs3LDEsIlknIl0sWzIsMSwiRChvbChaKScpIl0sWzUsMSwiRChvbChYKScpIl0sWzQsMCwiRCh0aWxkZShaKScpIl0sWzAsNCwiRChaKSJdLFszLDUsIkQoWCkiXSxbNyw0LCJEKFkpIl0sWzIsNCwiRChvbChaKSkiXSxbNSw0LCJEKG9sKFgpKSJdLFs0LDMsIkQodGlsZGUoWikpIl0sWzYsOSwia18hIiwxXSxbOSwxMSwiZWxsXyEiLDEseyJsYWJlbF9wb3NpdGlvbiI6NzB9XSxbNywxMCwial8hIiwxXSxbOSw3LCJSIG9sKGgpXyoiLDFdLFsxMCw4LCJSIG9sKGYpXyoiLDFdLFsxMSwxMCwiUiB0aWxkZShoKV8qIiwxXSxbMCwzLCJrJyIsMV0sWzMsNSwiZWxsJ18hIiwxXSxbMSw0LCJqXyEiLDEseyJsYWJlbF9wb3NpdGlvbiI6MzB9XSxbMywxLCJSIG9sKGgpJ18qIiwxXSxbNCwyLCJSIG9sKGYpJ18qIiwxXSxbNSw0LCJSIHRpbGRlKGgpJ18qIiwxXSxbMiw4LCJnXigtMSkiLDFdLFsxLDcsImcnXigtMSkiLDEseyJsYWJlbF9wb3NpdGlvbiI6MjB9XSxbMCw2LCJnJydeKC0xKSIsMV0sWzMsOSwib2woZyknXigtMSkiLDFdLFs0LDEwLCJvbChnKV4oLTEpIiwxXSxbNSwxMSwidGlsZGUoZyleKC0xKSIsMSx7ImxhYmVsX3Bvc2l0aW9uIjo4MH1dXQ==
  #context align(center, diagram({
    edge(..tune-2-mor-coords((7, 4), (5, 1), l: 0.6), text(fill: red)[$1,BC$], "=>", label-side: center, stroke: red, bend: -20deg, shift: -3pt)
    edge(..tune-2-mor-coords((5, 4), (3, 2)), text(fill: red)[$2,BC_!$], "=>", label-side: center, stroke: red, bend: 50deg, label-pos: 0.35)
    edge(..tune-2-mor-coords((3, 5), (2, 1), l: 0.6), text(fill: red)[$3,BC$], "=>", label-side: center, stroke: red)
    edge(..tune-2-mor-coords((2, 4), (0, 1), l: 0.6), text(fill: red)[$4,BC_!$], "=>", label-side: center, stroke: red, bend: -20deg, shift: -3pt)
    edge(..tune-2-mor-coords((3, 2), (4, 0)), text(fill: red)[$5,T$], "=>", label-side: center, stroke: red)

    edge(..tune-2-mor-coords((3, 5), (4, 3)), text(fill: blue)[$1,T$], "=>", label-side: center, stroke: blue)
    edge(..tune-2-mor-coords((7, 4), (5, 1), l: 0.6), text(fill: blue)[$2,BC$], "=>", label-side: center, stroke: blue, bend: 20deg, shift: 3pt)
    edge(..tune-2-mor-coords((5, 4), (4, 0)), text(fill: blue)[$3,BC$], "=>", label-side: center, stroke: blue)
    edge(..tune-2-mor-coords((4, 3), (2, 1)), text(fill: blue)[$4,BC_!$], "=>", label-side: center, stroke: blue, bend: 55deg, label-pos: 0.6)
    edge(..tune-2-mor-coords((2, 4), (0, 1), l: 0.6), text(fill: blue)[$5,BC_!$], "=>", label-side: center, stroke: blue, bend: 20deg, shift: 3pt)

    node((0, 1), [$D(Z')$])
    node((3, 2), [$D(X')$])
    node((7, 1), [$Y'$])
    node((2, 1), [$D(ol(Z)')$])
    node((5, 1), [$D(ol(X)')$])
    node((4, 0), [$D(tilde(Z)')$])
    node((0, 4), [$D(Z)$])
    node((3, 5), [$D(X)$])
    node((7, 4), [$D(Y)$])
    node((2, 4), [$D(ol(Z))$])
    node((5, 4), [$D(ol(X))$])
    node((4, 3), [$D(tilde(Z))$])
    edge((0, 4), (2, 4), text(fill: fuchsia)[$k_!$], label-side: center, "->", stroke: fuchsia)
    edge((2, 4), (4, 3), [$ell_!$], label-side: center, label-pos: 0.7, "->")
    edge((3, 5), (5, 4), text(fill: fuchsia)[$j_!$], label-side: center, "->", stroke: fuchsia)
    edge((2, 4), (3, 5), text(fill: fuchsia)[$R ol(h)_*$], label-side: center, "->", stroke: fuchsia)
    edge((5, 4), (7, 4), text(fill: fuchsia)[$R ol(f)_*$], label-side: center, "->", stroke: fuchsia)
    edge((4, 3), (5, 4), [$R tilde(h)_*$], label-side: center, "->")
    edge((0, 1), (2, 1), text(fill: green)[$k'_!$], label-side: center, "->", stroke: green)
    edge((2, 1), (4, 0), text(fill: green)[$ell'_!$], label-side: center, "->", stroke: green)
    edge((3, 2), (5, 1), [$j_!$], label-side: center, label-pos: 0.3, "->")
    edge((2, 1), (3, 2), [$R ol(h)'_*$], label-side: center, "->")
    edge((5, 1), (7, 1), text(fill: green)[$R ol(f)'_*$], label-side: center, "->", stroke: green)
    edge((4, 0), (5, 1), text(fill: green)[$R tilde(h)'_*$], label-side: center, "->", stroke: green)
    edge((7, 4), (7, 1), text(fill: fuchsia)[$g^(-1)$], label-side: center, "->", stroke: fuchsia)
    edge((3, 5), (3, 2), [$g'^(-1)$], label-side: center, label-pos: 0.8, "->")
    edge((0, 4), (0, 1), text(fill: green)[$g''^(-1)$], label-side: center, "->", stroke: green)
    edge((2, 4), (2, 1), [$ol(g)'^(-1)$], label-side: center, "->")
    edge((5, 4), (5, 1), [$ol(g)^(-1)$], label-side: center, "->")
    edge((4, 3), (4, 0), [$tilde(g)^(-1)$], label-side: center, label-pos: 0.2, "->")
  }, crossing-fill: thm-box-curr-color(), spacing: 2em))
  两个自然变换都从洋红色函子到绿色函子。先施于 $R f_!$、再施于 $R h_!$ 的基变换映射是红色路径，$R(f compose h)_!$ 的基变换映射是蓝色路径。

  由自然性，蓝色路径的第 1、2 步可交换，红色路径的第 4、5 步可交换。因此只需把红色路径的第 2、3、5 步与蓝色路径的第 1、3、4 步等同起来；对中央立方体应用引理即得。

  (3) 给定一对互补的开浸入与闭浸入 $j: U -> X, i: Z -> X$，有零延拓三角：
  $
    j_! j^(-1) cal(K) -> cal(K) -> i_* i^(-1) cal(K) ->^(+1)
  $
  此三角与基变换相容，在茎上检查即可。

  现在 $j$ 是开浸入、$i$ 紧合，故 $R j_! = j_!, R i_! = i_*$。对上述三角施加 $R f_!$ 并用 (1)，便得到所要的三角：
  $
    R f_(U,!) j^(-1) cal(K) -> R f_! cal(K) -> R f_(Z,!) i^(-1) cal(K) ->^(+1)
  $
  这里 $f_U = f compose j, f_Z = f compose i$。它与基变换相容：基变换与复合相容，且 $j_! j^(-1) cal(K) -> cal(K) -> i_* i^(-1) cal(K) ->^(+1)$ 与基变换相容。
]

作为紧合基变换的推论，有 $R f_!$ 的消没结果。

#corollary(name: <grothendieck-vanishing-for-rf-lower-shriek>)[
  设 $f: X -> Y$ 是 Noether 概形之间分离的有限型态射，其纤维的维数 $<=d$。则 $R f_!$ 上有界，且其上方上同调维数 $<=2d$。
]
#proof[
  由紧合基变换，
  $
    (R f_! cal(K))_(ol(y)) = R Gamma_c (X_(ol(y)), cal(K)|_(X_(ol(y))))
  $
  现在 $X_(ol(y))$ 的维数 $<=d$，故只需处理 $Y = Spec(k)$（$k$ 为可分闭域）且 $dim(X) <= d$ 的情形。任取紧化 $X ->^j ol(X) -> Spec(k) = Y$。把 $ol(X)$ 换成 $j$ 的概形像，便可假设 $X$ 在 $ol(X)$ 中稠密。于是 $dim(ol(X)) = dim(X) <= d$。而：
  $
    R Gamma_c (X, -) = R Gamma(ol(X), j_! (-))
  $
  由 Grothendieck 消没，其上方上同调维数 $<=2d$。
]

  这里还有一点要证：我们刚定义的 $R f_!$ 与 @etale-lower-shriek-defn 中为平展态射 $f$ 定义的、作为 $f^(-1)$ 的伴随来定义的 $f_!$ 相容。

#proposition(name: <etale-and-compactified-lower-shriek-agree>)[
  设 $f: X -> Y$ 是 Noether 概形之间分离的平展态射。则有典范自然同构：
  $
    R f_! cong f_!: D_#[tor] (X_et, Lambda) -> D_#[tor] (Y_et, Lambda)
  $
  其中 $R f_!$ 用紧化定义，$f_!$ 则是 @etale-lower-shriek-defn 中作为 $f^(-1)$ 的伴随定义的。
]
#proof[
  设 $cal(F) in cAb_#[tor] (X_et, Lambda)$，$q >= 1$，$ol(y) = Spec(Omega)$ 是 $Y$ 的任意几何点。则几何纤维 $X_(ol(y)) = union.sq.big_(ol(x) in f^(-1)(ol(y))) Spec(Omega)$ 不过是若干个 $Spec(Omega)$ 的不交并。因此 $f_(ol(y)): X_(ol(y)) -> ol(y)$ 有限，没有高阶直像。由紧合基变换，
  $
    h^q (R f_! cal(F))_(ol(y)) = R^q f_(ol(y),*) cal(F) = 0
  $
  所以对一切 $q >= 1$ 都有 $h^q (R f_! cal(F)) = 0$。这表明无论向上还是向下，$R f_!$ 的上同调维数都是 0。若暂用 $R^0 f_!$ 表示 $h^0 (R f_! (-))$，则 $R^0 f_!$ 是正合函子 $cAb_#[tor] (X_et, Lambda) -> cAb_#[tor] (Y_et, Lambda)$，而 $R f_!$ 不过是逐项施加的 $R^0 f_!$。

  因此只需证明 $f_! = R^0 f_!$。任取紧化 $X ->^j ol(X) ->^(ol(f)) Y$，便有：
  $
    R^0 f_! cal(F) = ol(f)_* j_! cal(F)
  $
  由 @sep-etale-lower-shriek-alt-desc，可以如下把 $f_! cal(F) subset f_* cal(F)$ 与 $ol(f)_* j_! cal(F) subset ol(f)_* j_* cal(F) = f_* cal(F)$ 看成同一个子层。对 $U in Et_Y$，
  $
    f_! cal(F) (U) = {s in cal(F)(U times_Y X) : supp(s) -> U times_Y X -> U #[紧合]} subset cal(F)(U times_Y X) = f_* cal(F) (U) \

    ol(f)_* j_! cal(F) = {s in cal(F)(U times_Y X) : supp(s) -> U times_Y X -> U times_Y ol(X) #[紧合]} subset cal(F)(U times_Y X) = f_* cal(F) (U)
  $
  然而，由于 $U times_Y ol(X) -> U$ 紧合，$supp(s) -> U$ 紧合当且仅当 $supp(s) -> U times_Y ol(X)$ 紧合。因此这两个子层其实是 $f_* cal(F)$ 的同一个子层。于是得到自然同构：
  $
    f_! cal(F) cong ol(f)_* j_! cal(F)
  $
  要说明这个自然同构与紧化选取无关、且与复合相容，归结为下述引理以及 @sep-etale-lower-shriek-alt-desc 中映射的复合相容性：

  #lemma(name: <open-proper-compat-and-inclusion-of-lower-shriek>)[
    记：
    
    - 将 @open-proper-compat 中的同构记为 $T(f_1, f_2, j_X, j_Y)$；

    - 将 @sep-etale-lower-shriek-alt-desc 中的包含 $f_! -> f_*$ 记为 $I(f)$。

    则复合：
    $
      j_(Y,!) f_(1,*) ->^(T(f_1,f_2,j_X,j_Y)) f_(2,*) j_(X,!) ->^(f_(2,*) I(j_X)) f_(2,*) j_(X,*) = j_(Y,*) f_(1,*)
    $
    正是 $I(j_Y) f_(1,*)$。
  ]
  #proof[
    沿 $j_Y$ 的互补闭浸入拉回后，两个映射都为零。因此可以沿 $j_Y^(-1)$ 拉回后再证相等。再者，若等同 $j_Y^(-1) j_(Y,!) = j_Y^(-1) j_(Y,*) = id$，则 $j_Y^(-1) I(j_Y) = id$。于是只需证明：
    $
      j_Y^(-1) f_(2,*) j_(X,!) -->^(BC(j_X,j_Y,f_1,f_2) j_(X,!)) f_(1,*)
    $
    正是映射：
    $
      j_Y^(-1) f_(2,*) j_(X,!) -->^(j_Y^(-1) f_(2,*) I(j_X)) j_Y^(-1) f_(2,*) j_(X,*) = f_(1,*)
    $
    这正是下述方块的自然性：
    // https://q.uiver.app/#r=typst&q=WzAsNCxbMCwxLCJqX1leKC0xKSBmXygyLCopIGpfKFgsISkiXSxbMSwwLCJqXigtMSkgZl8oMiwqKSBqXyhYLCopIl0sWzIsMSwiZl8oMSwqKSBqX1heKC0xKSBqXyhYLCopIl0sWzEsMiwiZl8oMSwqKSBqX1heKC0xKSBqXyhYLCEpIl0sWzAsMSwial9ZXigtMSkgZl8oMiwqKUkoal9YKSIsMV0sWzMsMiwiZl8oMSwqKSBqX1heKC0xKSBJKGpfWCkiLDFdLFswLDMsIkJDKGpfWCxqX1ksZl8xLGZfMilqXyhYLCEpIiwxXSxbMSwyLCJCQyhqX1gsal9ZLGZfMSxmXzIpal8oWCwqKSIsMV1d
    #context align(center, diagram({
      node((-1, 0), [$j_Y^(-1) f_(2,*) j_(X,!)$])
      node((0, -1), [$j^(-1) f_(2,*) j_(X,*)$])
      node((1, 0), [$f_(1,*) j_X^(-1) j_(X,*)$])
      node((0, 1), [$f_(1,*) j_X^(-1) j_(X,!)$])
      edge((-1, 0), (0, -1), [$j_Y^(-1) f_(2,*)I(j_X)$], label-side: center, "->")
      edge((0, 1), (1, 0), [$f_(1,*) j_X^(-1) I(j_X)$], label-side: center, "->")
      edge((-1, 0), (0, 1), [$BC(j_X,j_Y,f_1,f_2)j_(X,!)$], label-side: center, "->")
      edge((0, -1), (1, 0), [$BC(j_X,j_Y,f_1,f_2)j_(X,*)$], label-side: center, "->")
    }, crossing-fill: thm-box-curr-color(), label-size: 0.8em))
    其中在等同 $j_X^(-1) j_(X,!) = j_X^(-1) j_(X,*) = id$ 之下，右边两个箭头都是恒等映射。
  ]
]

有了这个命题，我们用紧化定义的记号 $R^q f_!$ 与 $f_!$，终于与 @etale-lower-shriek-defn 中 $f_!$ 的记号一致了。

此外，对任意分离、有限型的 $f$，还可以把 $f_! cal(F)$ 等同于 $f_* cal(F)$ 的一个子层：

#lemma[
  设 $f: X -> Y$ 是 Noether 概形之间分离的有限型态射。则存在典范自然单射：
  $
    f_! cal(F) -> f_* cal(F)
  $
  其中 $cal(F) in cAb_#[tor] (X_et, Lambda)$，该单射的像由下式给出：对 $U in Et_Y$，
  $
    f_! cal(F)(U) = {s in cal(F)(U times_Y X) : supp(s) -> U times_Y X -> U #[紧合]} subset cal(F)(U times_Y X) = f_* cal(F)(U)
  $
  此包含与复合相容。
]
#proof[
  任取紧化 $X ->^j ol(X) ->^(ol(f)) Y$，便有：
  $
    R^0 f_! cal(F) = ol(f)_* j_! cal(F)
  $
  由 @sep-etale-lower-shriek-alt-desc，可以如下把 $ol(f)_* j_! cal(F) subset ol(f)_* j_* cal(F) = f_* cal(F)$ 看成一个子层。对 $U in Et_Y$，
  $
    ol(f)_* j_! cal(F) = {s in cal(F)(U times_Y X) : supp(s) -> U times_Y X -> U times_Y ol(X) #[紧合]} subset cal(F)(U times_Y X) = f_* cal(F) (U)
  $
  然而，由于 $U times_Y ol(X) -> U$ 紧合，$supp(s) -> U$ 紧合当且仅当 $supp(s) -> U times_Y ol(X)$ 紧合。因此得到等同：
  $
    f_! cal(F)(U) = {s in cal(F)(U times_Y X) : supp(s) -> U times_Y X -> U #[紧合]} subset cal(F)(U times_Y X) = f_* cal(F)(U)
  $
  上述包含 $f_! cal(F) -> f_* cal(F)$ 的构造与紧化选取无关，且与复合相容；这由 @open-proper-compat-and-inclusion-of-lower-shriek 以及 @sep-etale-lower-shriek-alt-desc 中的自然性推出。
]
