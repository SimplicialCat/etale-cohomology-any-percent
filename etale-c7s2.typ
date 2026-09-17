#import "void-import.typ": *

== First properties of $R f_!$

#properties(name: <rf-lower-shriek-first-props>)[
  + (Leray spectral sequence) Let $f: X -> Y, g: Y -> Z$ be separated morphisms of finite type between noetherian schemes. There is a canonical natural isomorphism: 
    $
      R(g compose f)_! cong R g_! compose R f_!: D_#[tor] (X_et, Lambda) -> D_#[tor] (Z_et, Lambda)
    $
    that is associative w.r.t. chains of morphism compositions. 

    In particular, for $cal(F) in cAb_#[tor] (X_et, Lambda)$, there is a canonical spectral sequence: 
    $
      E_2^(p,q) = R^p g_! R^q f_! cal(F) => R^(p+q) (g compose f)_! cal(F)
    $

    When $Z = Spec(k)$ for a separably closed field $k$, this specializes to: 
    $
      R Gamma_c (Y, R f_! (-)) cong R Gamma_c (X, -)
    $
    and: 
    $
      E_2^(p,q) = H^p_c (Y, R^q f_! cal(F)) => H^(p+q)_c (X, cal(F))
    $

  + (Proper base change) In a Cartesian diagram: 
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
    Suppose that all schemes are noetherian and $f$ is separated of finite type. Then there is a natural isomorphism: 
    $
      g^(-1) R f_! -> R f'_! g'^(-1): D_#[tor] (X_et, Lambda) -> D_#[tor] (Y'_et, Lambda)
    $
    compatible with horizontal and vertical concatenation of Cartesian squares. 

    In particular, when $Y' = ol(y)$ is a geometric point of $Y$, this specializes to: 
    $
      (R f_! (-))_(ol(y)) cong R Gamma_c (X_(ol(y)), (-)|_(X_(ol(y))))
    $

  + (Extension by zero sequence) Suppose that $f: X -> Y$ is a separated morphism of finite type between noetherian schemes, and that $j: U -> X, i: Z -> X$ is a pair of complementary open and closed immersions. Form: 
    $
      f_U: U ->^j X ->^f Y \
      f_Z: Z ->^i X ->^f Y
    $
    Then for $cal(K) in D_#[tor] (X_et, Lambda)$, there is a natural distinguished triangle: 
    $
      R f_(U,!) j^(-1) cal(K) -> R f_! cal(K) -> R f_(Z,!) i^(-1) cal(K) ->^(+1)
    $
    compatible with base change. In particular, when $Y = Spec(k)$ for a separably closed field $k$, this specializes to a distinguished triangle: 
    $
      R Gamma_c (U, j^(-1) cal(K)) -> R Gamma_c (X, cal(K)) -> R Gamma_c (Z, i^(-1) cal(K)) ->^(+1)
    $
]
#proof[
  (1) Let $cal(K) in D_#[tor] (X_et, Lambda)$. Pick compactifications $X ->^j ol(X) ->^(ol(f)) Y$ of $f$ and $Y ->^k ol(Y) ->^(ol(g)) Z$ of $g$. Next, since $k compose ol(f): ol(X) -> ol(Y)$ is separated of finite type, there exists a compactification $ol(X) ->^ell tilde(X) ->^(tilde(f)) ol(Y)$. In other words, we have a commutative diagram: 
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
  in which down-right arrows are proper and up-right arrows are open immersions. Such a diagram is called a *compactification of $(f, g)$*. 
  
  By @open-proper-compat, there is a natural quasi-isomorphism: 
  $
    k_! R ol(f)_* cal(K) ->^tilde R tilde(f)_* ell_! cal(K)
  $
  Thus, by definition, 
  $
    R g_! R f_! cal(K) cong R ol(g)_* k_! R ol(f)_* j_! cal(K) cong R ol(g)_* R tilde(f)_* ell_! j_! cal(K) = R(ol(g) compose tilde(f))_* (ell compose j)_! cal(K) cong R(g compose f)_! cal(K)
  $
  where $X ->^(ell compose j) tilde(X) ->^(ol(g) compose tilde(f)) Z$ is a compactification of $g compose f: X -> Z$. We have thus constructed an isomorphism. It remains to show that this isomorphism is independent from the choice of compactification of $(f, g)$, and is associative with composition of three morphisms. 

  The rest of this proof is bookkeeping and may be skipped. Suppose that we have proved independence from the choice of a compactification of $(f, g)$. Then given three morphisms $X ->^f Y ->^g Z ->^h W$, we aim to prove that the isomorphism: 
  $
    R(h compose g compose f)_! cong R h_! compose R(g compose f)_! cong R h_! compose R g_! compose R f_!
  $
  is the same as the isomorphism: 
  $
    R(h compose g compose f)_! cong R (h compose g)_! compose R f_! cong R h_! compose R g_! compose R f_!
  $
  #proof_[Proof of associativity][
    Form a large commutative diagram: 
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
    in which down-right arrows are proper and up-right arrows are open immersions. 

    This commutative diagram of morphisms passes to a diagram of functors. Here, we abbreviate $D_#[tor] (X_et, Lambda)$ by $D(X)$: 
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
    Here, the three small triangles on the bottom commute, and the two isomorphisms we want to identify are both natural isomorphisms from the bottom edge to the two upper edges of the large triangle. 

    Then, the path: 
    $
      R h_! compose R g_! compose R f_! cong R(h compose g)_! compose R f_! cong R(h compose g compose f)_!
    $
    is going up along the two blue natural isomorphisms, and the path: 
    $
      R h_! compose R g_! compose R f_! cong R h_! compose R (g compose f)_! cong R(h compose g compose f)_!
    $
    is going up along the two red natural isomorphisms, where all natural isomorphisms are given by @open-proper-compat. By @open-proper-compat-naturality, these two paths are both the same as going up along the natural isomorphism given by @open-proper-compat induced by the three small squares, hence the same. 
  ]
  We now prove independence of the isomorphism $R(g compose f)_! cong R g_! compose R f_!$ from the compactification of $(f, g)$ chosen. Suppose that we have two compactifications of $(f, g)$. We first assume that one dominates the other, i.e. we have a commutative diagram: 
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

  Denote by $T(f_1, f_2, j_X, j_Y)$ the isomorphism constructed in @open-proper-compat. Then identifying $R f_! = R ol(f)_* compose j_!, R g_! = R ol(g)_* compose k_!$ and $R(g compose f)_! = R(ol(g) compose ol(f))_* compose (ell compose j)_!$, the isomorphism $R g_! compose R f_! -> R(g compose f)_!$ defined by the lower compactification is: 
  $
    R ol(g)_* k_! R ol(f)_* j_! -->^(R ol(g)_* T(tilde(f), ol(f), ell, k) j_!) R ol(g)_* R ol(f)_* ell_! j_!
  $
  while the isomorphism defined by the upper compactification is: 
  $
    R ol(g)_* k_! R ol(f)_* j_! &-->^(R ol(g)_* k_! T(phi, id_X, j', j)) R ol(g)_* k_! R ol(f)_* R phi_* j'_! = R ol(g)_* k_! R ol(f)'_* j'_! \
    &-->^(T(psi, id_Y, k', k) R ol(f)'_* j'_!) R ol(g)_* psi_* k'_! R ol(f)'_* j'_! = R ol(g)'_* k'_! R ol(f)'_* j'_! \
    &-->^(R ol(g)'_* T(tilde(f)', ol(f)', ell', k') j'_!) R ol(g)'_* R tilde(f)'_* ell'_! j'_! = R ol(g)_* R tilde(f)_* R chi_* ell'_! j'_! \
    &-->^(R ol(g)'_* R ol(f)'_* T(chi, id_X, ell' compose j', ell compose j)^(-1)) R ol(g)_* R tilde(f)_* ell_! j_!
  $
  In other words, we need to prove the equality: 
  $
    & R ol(g)'_* R ol(f)'_* T(chi, id_X, ell' compose j', ell compose j) compose R ol(g)_* T(tilde(f), ol(f), ell, k) j_! \
    =& R ol(g)'_* T(tilde(f)', ol(f)', ell', k') j'_! compose T(psi, id_Y, k', k) R ol(f)'_* j'_! compose R ol(g)_* k_! T(phi, id_X, j', j)
  $
  Abbreviating $D_#[tor] (X_et, Lambda)$ by $D(X)$, we may form the following diagram: 
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
  Both sides of the desired equality go from the magenta path to the green path. By compatibility of the construction of $T$ with concatenation of squares, as in @open-proper-compat-naturality, we have: 
  $
    T(chi, id_X, ell' compose j', ell compose j) = T(chi, phi, ell', ell) j'_! compose ell_! T(phi, id_X, j', j)
  $
  In other words, the natural transformation on LHS of the desired equality is just the red path, while the natural transformation on RHS of the desired equality is the blue path, as drawn on the diagram. 

  By naturality, step 1 and 2 of the red path can be applied in either order. Now step 2 of red path is just step 1 of blue path, so we may cancel it off. We then only need to show that step 1 then 3 of red path, is the same as step 2 then 3 of the blue path. Indeed, both paths roll up the middle cube using the natural transformation $T$. They are thus equal since $T$ is compatible with concatenation of squares: 
  $
    & R tilde(f)_* T(chi, psi, ell', ell) compose T(tilde(f), ol(f), ell, k) R phi_* = T(tilde(f) compose chi, ol(f) compose phi, ell', k) \
    =& T(psi compose tilde(f)', ol(f)', ell', k) = R psi_* T(tilde(f)', ol(f)', ell', k') compose T(psi, id_Y, k', k) R ol(f)'_*
  $
  We have thus proved independence from the choice of compactification of $(f, g)$ when one dominates the other. The independence thus follows from the following lemma: 

  #lemma[
    For any two compactifications of $(f, g)$, there exists a third compactification of $(f, g)$ dominating both of them. 
  ]
  #proof[
    Consider two compactifications of $(f, g)$: 
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
    where $i = 1, 2$. By @compactification-filtered, we may pick a compactification $X ->^j ol(X) ->^(ol(f)) Y$ of $f$, and a compactification $Y ->^k ol(Y) ->^(ol(g)) Z$ of $g$, with morphisms of compactifications $phi_i: ol(X) -> ol(X)_i, psi_i: ol(Y) -> ol(Y)_i$ for $i=1,2$. Then to obtain a compactification of $(f,  g)$ dominating both given compactifications, it suffices to find a compactification $ol(X) ->^ell tilde(X) ->^(tilde(f)) ol(Y)$ of $k compose ol(f): ol(X) -> ol(Y)$, and morphisms $chi_i: tilde(X) -> tilde(X)_i, i = 1,2$ that makes the following diagram commute: 
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
    For $i = 1, 2$, form the fiber product $T_i = tilde(X)_i times_(ol(Y)_i) ol(Y)$ and projections $t_i: T_i -> ol(Y), s_i: T_i -> tilde(X)_1$. Then $s_i, t_i$ are proper. Consider the morphisms $ell_i compose phi_i: ol(X) -> tilde(X)_i$ and $k compose ol(f): ol(X) -> ol(Y)$. Then: 
    $
      psi_i compose k compose ol(f) = tilde(f)_i compose ell_i compose phi_i
    $
    Indeed, $tilde(f)_i compose ell_i compose phi_i = k_i compose ol(f)_i compose phi_i = k_i compose ol(f) = psi_i compose k compose ol(f)$ since $phi_i, psi_i$ are morphisms of compactifications. Thus, there is a morphism $q_i: ol(X) -> T_i$ fitting in the commutative diagram: 
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
    Now $phi_i, s_i$ are proper and $ell_i$ is an open immersion, so $q_i$ is a morphism between $tilde(X)_i$ schemes that are separated of finite type. Thus $q_i$ is separated of finite type, and we may form a compactification $ol(X) ->^(ell'_i) tilde(X)'_i ->^(h_i) T_i$ of $q_i$. Take $tilde(f)'_i = t_i compose h_i: tilde(X)'_i -> ol(Y)_i$ and $chi_i = s_i compose h_i: tilde(X)'_i -> tilde(X)_i$. Then since $t_i$ is proper, $ol(X) ->^(ell'_i) tilde(X)'_i ->^(t_i compose h_i) ol(Y)$ is a compactification of $k compose ol(f): ol(X) -> ol(Y)$ that fits in the commutative diagram: 
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
    Picking a compactification $tilde(X)$ of $ol(X) -> ol(Y)$ dominating both $tilde(X)_1$ and $tilde(X)_2$ concludes the proof. 
  ]

  (2) We construct a base change isomorphism as follows: Pick a compactification $X ->^j ol(X) ->^(ol(f)) Y$ of $f$, and form a Cartesian diagram: 
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
  Note that $j'$ is an open immersion and $ol(f)'$ is proper, making $X' ->^(j') ol(X)' ->^(ol(f)') Y'$ a compactification of $f': X' -> Y'$. 

  Then we define the base change $g^(-1) R f_! cal(K) -> R f'_! g'^(-1) cal(K)$ as the composition: 
  $
    g^(-1) R f_! cal(K) cong g^(-1) R ol(f)_* j_! cal(K) ->^tilde R ol(f)'_* ol(g)'^(-1) j_! cal(K) ->^tilde R ol(f)'_* j'_! g'^(-1) cal(K) cong R f'_! g'^(-1) cal(K)
  $
  where the first map is the base change map as defined in @base-change-constr, which is an isomorphism by proper base change, and the second map is the isomorphism in @etale-lower-shriek-first-props (4). 

  As usual, we still need to prove well-definedness and naturality of this map. This part is bookkeeping and we encourage the reader to skip it. In short, we need to prove the compatibility of the isomorphism as in @open-proper-compat, the base change map, and the base change map for extension by zero as in @etale-lower-shriek-first-props (4). 

  #lemma(name: <open-proper-compat-with-bc>)[
    Denote: 

    - the base change map as in @base-change-constr by $BC(g', g, f', f)$; 

    - the base change for extension by zero as in @etale-lower-shriek-first-props (4) by $BC_! (g', g, f', f)$; 

    - the isomorphism as in @open-proper-compat by $T(f_1, f_2, j_X, j_Y)$. 

    Now let there be a commutative cube: 
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
    in which $f_1, f_2, f'_1, f'_2$ are proper, $j_X, j_Y, j'_X, j'_Y$ are open immersions, and all four vertical faces are Cartesian. Then the following two natural transformations on functors $D_#[tor] ((X_1)_et, Lambda) -> D_#[tor] ((Y'_2)_et, Lambda)$ are the same: 
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
    Note that all arrows on the hexagonal diagram above are natural isomorphisms. Let $i'_Y: W' -> Y'_2$ be a complementary closed immersion to $j'_Y$. Note that $i'_Y^(-1) j'_(Y,!) g_1^(-1) R f_(1,*) = 0$, and so if we apply $i'_Y^(-1)$ to the diagram above, we get a diagram full of zeros. Hence, by the extension by zero triangle, it suffices to prove the commutativity of the diagram upon applying $j_Y^(-1)$. 

    In the argument that follows, we identify $id$ with $j_X^(-1) j_(X,!)$ (and do not track the natural isomorphism for that) for convenience. 

    - We first unfold the most mysterious $T$ terms. Upon checking the proof of @open-proper-compat, #h(1fr)
      $
        & j'_Y^(-1) T(f'_1, f'_2, j'_X, j'_Y) g'_1^(-1) = (BC(j'_X, j'_Y, f'_1, f'_2) j'_(X,!))^(-1) g'_1^(-1)\
        :& j'_Y^(-1) R f'_(2,*) j'_(X,!) g'_1^(-1) <- R f'_(1,*) j'_X^(-1) j'_(X,!) g'_1^(-1) = R f'_(1,*) g'_1^(-1)
      $
      and: 
      $
        & j'_Y^(-1) g_2^(-1) T(f_1, f_2, j_X, j_Y) = g_1^(-1) j_Y^(-1) T(f_1, f_2, j_X, j_Y) = g_1^(-1) (BC(j_X, j_Y, f_1, f_2) j_(X,!))^(-1) \
        :& j'_Y^(-1) g_2^(-1) R f_(2,*) j_(X,!) = g_1^(-1) j_Y^(-1) R f_(2,*) j_(X,!) <- g_1^(-1) R f_(1,*) j_X^(-1) j_(X,!) = g_1^(-1) R f_(1,*) = g_1^(-1) j_Y^(-1) j_(Y,!) R f_(1,*) = j'_Y^(-1) g_2^(-1) j_(Y,!) R f_(1,*)
      $

    - Next, consider the lower left arrow $BC_! (g_1, g_2, j'_Y, j_Y) R f_(1,*)$. By unfolding the definitions, the isomorphism: 
      $
        BC_! (g_1, g_2, j'_Y, j_Y): g_2^(-1) j_(Y,!) -> j'_(Y,!) g_1^(-1)
      $
      upon applying $j'_Y^(-1)$, is just $id_(g_1^(-1))$ once we identify: 
      $
        j'_Y^(-1) g_2^(-1) j_(Y,!) = g_1^(-1) j_Y^(-1) j_(Y,!) = g_1^(-1)
      $
      and $j'_Y^(-1) j'_(Y,!) g_1^(-1) = g_1^(-1)$. 

      Thus, upon applying $j'_Y^(-1)$ and identifying both sides of this map by $g_1^(-1) R f_(1,*)$, this map becomes the identity. 

    Thus, under these identifications, it suffices to prove the commutativity of the following pentagonal diagram: 
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

    Now consider the two rightmost arrows. The natural transformations there act on different parts of a composition of functors, so naturality is applicable, and we have a commutative diagram: 
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
    As argued above, once we identify $j'_X^(-1) g'_2^(-1) j_(X,!) = j'_X^(-1) j'_(X,!) g'_1^(-1) = g'_1^(-1)$, the morphism $j'_X^(-1) BC_!  (g'_1, g'_2, j'_X, j'_Y)$ becomes the identity. Hence, we may replace the two rightmost arrows by a single arrow. By inserting a $j_X^(-1) j_(X,!)$ on the bottom arrow, it suffices to prove the commutativity of the following square: 
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

    In other words, it suffices to prove: 
    $
      BC(j'_X, j'_Y, f'_1, f'_2) g'_2^(-1) compose j'_Y^(-1) BC(g'_2,g_2,f'_2,f_2) = BC(g'_1,g_1,f'_1,f_1) j_X^(-1) compose g_1^(-1) BC(j_X, j_Y, f_1, f_2)
    $
    This is just compatibility of base change with vertical concatenation, as in @base-change-naturality: Both sides are equal to: 
    $
      BC(g'_2 compose j'_X, g_2 compose j'_Y, f'_1, f_2) = BC(j_X compose g'_1, j_Y compose g_1, f'_1, f_2)
    $
  ]
  We are now ready to prove the base change map for $R f_!$ is well-defined and natural. For well-definedness, i.e. independence from the choice of compactification, let $X ->^(j_i) ol(X)_i ->^(ol(f)_i) Y$ be two compactifications. We aim to show that they define the same base change map. By picking a third compactification dominating them both by @compactification-filtered, and showing that both compactifications define the same base change map as the third one, we may assume WLOG that there exists a morphism $phi: ol(X)_2 -> ol(X)_1$ of compactifications. Form the base change: 
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

  Then we have the following identifications for $R f_!$ and $R f'_!$ defined by different compactifications: 
  $
    R f_(1,*) j_(1,!) -->^(R f_(1,*) T(phi, id_X, j_2, j_1)) R f_(1,*) R phi_* j_(2,!) = R f_(2,*) j_(2,!) \

    R f'_(1,*) j'_(1,!) -->^(R f'_(1,*) T(phi', id_(X'), j'_2, j'_1)) R f'_(1,*) R phi'_* j'_(2,!) = R f'_(2,*) j'_(2,!)
  $

  // To prove independence from the choice of a compactification, it suffices to prove the commutativity of the following diagram: 
  As usual, we abbreviate $D_#[tor] (X_et, Lambda)$ by $D(X)$. We identify base changes defined by both compactifications by a natural transformation $g^(-1) R ol(f)_(1,*) j_(1,!) -> R ol(f)'_(2,*) j'_(2,!) g'^(-1)$ using the isomorphisms $T$. Then in the following diagram: 

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
  Then base changes defined by both compactifications are paths from the magenta functor to the green functor. The red path is the base change defined by $ol(X)_1$, and the blue path is the base change defined by $ol(X)_2$ (where we used the naturality of base change here to split the base change along $R ol(f)_(2,*)$ into two steps). Now by naturality, step 1 and 2 of the blue path may be exchanged, and so it suffices to compare step 2, 3 of the red path with step 1, 3, 4 of the blue path, i.e. the part of the paths on the left triangular prism. However, applying the previous lemma to the scheme morphisms on the left triangular prism (with identity maps on $X$ and $X'$) identifies these two paths. 

  We have thus proved well-definedness. For compatibility with concatenation of Cartesian squares, the compatibility with vertical concatenation directly follows from the same compatibility for $R f_*$. Thus, it remains to prove compatibility with horizontal concatenation. Let $Z ->^h X ->^f Y$ be two separated morphisms of finite type, and pick a compactification of $(h, f)$ and form a base change: 
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
  Then the top face of the diagram above is a compactification of $(h', f')$. Identify the base changes applied separately to $R h_!$ and $R f_!$, and the base change applied to $R(f compose f)_*$ as natural transformations: 
  $
    g^(-1) R ol(f)_* j_! R ol(h)_* k_! -> R ol(f)'_* R tilde(h)'_* ell'_! k'_! g''^(-1)
  $
  Then we may denote these two natural transformations in the following diagram: 
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
  Both natural transformations go from the magenta functor to the green functor. The base change map of $R f_!$ then $R h_!$ is the red path, while the base change map of $R(f compose h)_!$ is the blue path. 

  By naturality, step 1 and 2 of the blue path may be swapped, and step 4 and 5 of the red path may be swapped. Thus, it suffices to identify step 2, 3, 5 of the red path with step 1, 3, 4 of the blue path. This follows by applying the lemma to the central cube. 

  (3) Given a pair of complementary open and closed immersions $j: U -> X, i: Z -> X$, we have the extension by zero triangle: 
  $
    j_! j^(-1) cal(K) -> cal(K) -> i_* i^(-1) cal(K) ->^(+1)
  $
  This triangle is compatible with base change as can be checked on stalks. 

  Now $j$ is an open immersion and $i$ is proper, so $R j_! = j_!, R i_! = i_*$. The desired triangle:
  $
    R f_(U,!) j^(-1) cal(K) -> R f_! cal(K) -> R f_(Z,!) i^(-1) cal(K) ->^(+1)
  $
  then follows by applying $R f_!$ to this triangle and applying (1), as $f_U = f compose j, f_Z = f compose i$. It is compatible with base change, since base change and composition are compatible, and $j_! j^(-1) cal(K) -> cal(K) -> i_* i^(-1) cal(K) ->^(+1)$ is compatible with base change. 
]

As a corollary to proper base change, we have a vanishing result for $R f_!$. 

#corollary(name: <grothendieck-vanishing-for-rf-lower-shriek>)[
  Let $f: X -> Y$ be a separated morphism of finite type between noetherian schemes, whose fibers have dimensions $<=d$. Then $R f_!$ is bounded above, with cohomological dimension above $<=2d$. 
]
#proof[
  By proper base change, 
  $
    (R f_! cal(K))_(ol(y)) = R Gamma_c (X_(ol(y)), cal(K)|_(X_(ol(y))))
  $
  Now $X_(ol(y))$ has dimension $<=d$, and so it suffices to deal with the case where $Y = Spec(k)$ for a separably closed field $k$ and $dim(X) <= d$. Pick any compactification $X ->^j ol(X) -> Spec(k) = Y$. By replacing $ol(X)$ with the schematic image of $j$, we may assume that $X$ is dense in $ol(X)$. Thus, $dim(ol(X)) = dim(X) <= d$. Now: 
  $
    R Gamma_c (X, -) = R Gamma(ol(X), j_! (-))
  $
  has cohomological dimension above $<=2d$ by Grothendieck vanishing. 
]

There is one more point to prove here, namely the compatibility of $R f_!$ we just defined, and the $f_!$ defined for an etale morphism $f$ in @etale-lower-shriek-defn as an adjoint to $f^(-1)$. 

#proposition(name: <etale-and-compactified-lower-shriek-agree>)[
  Suppose that $f: X -> Y$ is a separated etale morphism between noetherian schemes. Then there is a canonical natural isomorphism: 
  $
    R f_! cong f_!: D_#[tor] (X_et, Lambda) -> D_#[tor] (Y_et, Lambda)
  $
  where $R f_!$ is defined using compactifications, and $f_!$ is defined in @etale-lower-shriek-defn as an adjoint to $f^(-1)$. 
]
#proof[
  For a sheaf $cal(F) in cAb_#[tor] (X_et, Lambda)$ and $q >= 1$, and any geometric point $ol(y) = Spec(Omega)$ of $Y$, the geometric fiber $X_(ol(y)) = union.sq.big_(ol(x) in f^(-1)(ol(y))) Spec(Omega)$ is just a disjoint union of copies of $Spec(Omega)$. Thus $f_(ol(y)): X_(ol(y)) -> ol(y)$ is finite and has no higher direct images. By proper base change, 
  $
    h^q (R f_! cal(F))_(ol(y)) = R^q f_(ol(y),*) cal(F) = 0
  $
  Hence, $h^q (R f_! cal(F)) = 0$ for all $q >= 1$. This proves that $R f_!$ has cohomological dimension 0 both above and below. If we temporarily use $R^0 f_!$ to denote $h^0 (R f_! (-))$, then $R^0 f_!$ is an exact functor $cAb_#[tor] (X_et, Lambda) -> cAb_#[tor] (Y_et, Lambda)$, and $R f_!$ is just $R^0 f_!$ applied termwisely. 

  Thus, it suffices to prove that $f_! = R^0 f_!$. Pick any compactification $X ->^j ol(X) ->^(ol(f)) Y$, and so: 
  $
    R^0 f_! cal(F) = ol(f)_* j_! cal(F)
  $
  By @sep-etale-lower-shriek-alt-desc, we may identify $f_! cal(F) subset f_* cal(F)$ and $ol(f)_* j_! cal(F) subset ol(f)_* j_* cal(F) = f_* cal(F)$ as follows. For $U in Et_Y$, 
  $
    f_! cal(F) (U) = {s in cal(F)(U times_Y X) : supp(s) -> U times_Y X -> U #[proper]} subset cal(F)(U times_Y X) = f_* cal(F) (U) \

    ol(f)_* j_! cal(F) = {s in cal(F)(U times_Y X) : supp(s) -> U times_Y X -> U times_Y ol(X) #[proper]} subset cal(F)(U times_Y X) = f_* cal(F) (U)
  $
  However, since $U times_Y ol(X) -> U$ is proper, $supp(s) -> U$ is proper if and only if $supp(s) -> U times_Y ol(X)$ is proper. Therefore, these two sheaves are really just the same subsheaves of $f_* cal(F)$. We have thus obtained a natural isomorphism: 
  $
    f_! cal(F) cong ol(f)_* j_! cal(F)
  $
  To show that this natural isomorphism is independent from the choice of compactification and is compatible with composition, it amounts to the following lemma and the compatibility of composition of the map in @sep-etale-lower-shriek-alt-desc: 

  #lemma(name: <open-proper-compat-and-inclusion-of-lower-shriek>)[
    Denote: 
    
    - the isomorphism as in @open-proper-compat by $T(f_1, f_2, j_X, j_Y)$. 

    - the inclusion $f_! -> f_*$ as in @sep-etale-lower-shriek-alt-desc by $I(f)$. 

    Then the composition: 
    $
      j_(Y,!) f_(1,*) ->^(T(f_1,f_2,j_X,j_Y)) f_(2,*) j_(X,!) ->^(f_(2,*) I(j_X)) f_(2,*) j_(X,*) = j_(Y,*) f_(1,*)
    $
    is just $I(j_Y) f_(1,*)$. 
  ]
  #proof[
    Under pulling back along a complementary closed immersion to $j_Y$, both maps are zero. Thus, we may prove equality after pulling back along $j_Y^(-1)$. Furthermore, $j_Y^(-1) I(j_Y) = id$ if we identify $j_Y^(-1) j_(Y,!) = j_Y^(-1) j_(Y,*) = id$. Thus, it suffices to prove: 
    $
      j_Y^(-1) f_(2,*) j_(X,!) -->^(BC(j_X,j_Y,f_1,f_2) j_(X,!)) f_(1,*)
    $
    is just the map: 
    $
      j_Y^(-1) f_(2,*) j_(X,!) -->^(j_Y^(-1) f_(2,*) I(j_X)) j_Y^(-1) f_(2,*) j_(X,*) = f_(1,*)
    $
    This is the naturality of the square: 
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
    where under the identifications $j_X^(-1) j_(X,!) = j_X^(-1) j_(X,*) = id$, both arrows on the right are the identity. 
  ]
]

With this proposition proved, our notation $R^q f_!$ and $f_!$ defined using compactifications is finally consistent with the notation of $f_!$ as in @etale-lower-shriek-defn. 

Furthermore, we have an identification of $f_! cal(F)$ as a subsheaf of $f_* cal(F)$ in the case of any separated of finite type $f$: 

#lemma[
  Let $f: X -> Y$ be a separated morphism of finite type between noetherian schemes. Then there is a canonical natural injection: 
  $
    f_! cal(F) -> f_* cal(F)
  $
  for $cal(F) in cAb_#[tor] (X_et, Lambda)$ whose image is: For $U in Et_Y$, 
  $
    f_! cal(F)(U) = {s in cal(F)(U times_Y X) : supp(s) -> U times_Y X -> U #[is proper]} subset cal(F)(U times_Y X) = f_* cal(F)(U)
  $
  This inclusion is compatible with composition. 
]
#proof[
  Pick any compactification $X ->^j ol(X) ->^(ol(f)) Y$, and so: 
  $
    R^0 f_! cal(F) = ol(f)_* j_! cal(F)
  $
  By @sep-etale-lower-shriek-alt-desc, we may identify $ol(f)_* j_! cal(F) subset ol(f)_* j_* cal(F) = f_* cal(F)$ as follows. For $U in Et_Y$, 
  $
    ol(f)_* j_! cal(F) = {s in cal(F)(U times_Y X) : supp(s) -> U times_Y X -> U times_Y ol(X) #[proper]} subset cal(F)(U times_Y X) = f_* cal(F) (U)
  $
  However, since $U times_Y ol(X) -> U$ is proper, $supp(s) -> U$ is proper if and only if $supp(s) -> U times_Y ol(X)$ is proper. Therefore, we have identified: 
  $
    f_! cal(F)(U) = {s in cal(F)(U times_Y X) : supp(s) -> U times_Y X -> U #[is proper]} subset cal(F)(U times_Y X) = f_* cal(F)(U)
  $
  The independence of the inclusion $f_! cal(F) -> f_* cal(F)$ constructed above from the compactification, and its compatibility with composition, follow from @open-proper-compat-and-inclusion-of-lower-shriek and the naturality in @sep-etale-lower-shriek-alt-desc. 
]
