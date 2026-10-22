#import "void-import.typ": *

#date[
  #set align(left) 
  Throughout this chapter and onwards, we will make frequent and often essential uses of the language of the derived category. 
]

In this chapter, we want to construct compactly supported cohomology, i.e. the functors $R Gamma_c$ and $R f_!$. As usual, we will first explain the motivations behind a concept, before introducing it. 

Etale cohomology was introduced as an analog of singular cohomology in positive characteristics, and to solve the Weil conjectures. For this, we need an analog of Poincare duality, and an analog of Lefschetz trace formula. 

We recall the statements of Poincare duality and Lefschetz trace formula in singular cohomology, and replace all homologies with cohomologies since in the etale setting, we only have a cohomology theory. 

Let $X$ be an $n$-dimensional orientable manifold. 

- Singular Poincare duality says that the natural map: #h(1fr)
  $
    H^k_c (X) -> H_(n-k) (X)
  $
  is an isomorphism. To change homology into cohomology, we use a universal coefficient theorem. Then Poincare duality states that the cup product pairing: 
  $
    - smile -: H^k_c (X, QQ) times H^(n-k) (X, QQ) -> H^n_c (X, QQ) ->^(tr_X) QQ
  $
  is a perfect pairing. 

- Singular Lefschetz trace formula says that if a map $f: X -> X$ has the Lefschetz number: 
  $
    Lambda_f = sum_(i=0)^n (-1)^i tr(f_*: H_i (X, QQ))
  $
  nonzero, then $f$ has a fixed point. To convert to cohomology, we use Poincare duality, giving rise to compactly supported cohomology on the way: 
  $
    Lambda_f = sum_(i=0)^n (-1)^i tr(f^*: H^i_c (X, QQ))
  $

As such, to establish analogs of Poincare duality and Lefschetz trace formula for etale cohomology, it is essential to establish the notion of $H^q_c (X, -)$ or $R Gamma_c (X, -)$, a kind of compactly supported cohomology. 

We will also need a relative notion of compactly supported cohomology, namely $R f_!$. Briefly speaking, $R f_!$ is to $R f_*$ what $R Gamma_c (X, -)$ is to $R Gamma(X, -)$. The significance of $R f_!$ can be seen as follows: 

- $R f_*$ is in some sense the "bad" push forward. It does not commute with arbitrary base change, and is not suitable for stating the projection and Kunneth formulas, unless $f$ is proper. 
  
  On the other hand, $R f_!$ is the "good" push forward. It commutes with arbitrary base change, and can be used to state the projection and Kunneth formulas. 

- $R f_!$ defined on the derived category allows a relative form of Poincare duality to be stated. Unlike its sister $R f_*$ which is a right adjoint, $R f_!$ is left adjoint to a functor $R f^!$. Then Poincare duality in this setting amounts to an explicit description of $R f^!$ whenever $f$ is smooth. 

  The six functors: 
  $
    f^(-1), R f_* \
    R f_!, R f^! \
    - Lotimes_Lambda -, RHHom_Lambda (-, -)
  $
  now form three adjunction pairs, and allow us to summarize etale cohomology into an axiomatic list of statements. 
  
  This is Grothendieck's famous *six functor formalism* and the formalism of *Verdier duality*, allowing one to view etale cohomology from a higher perspective. 

Finally, we bring some insight to the construction of $R Gamma_c (X, -)$ (and $R f_!$). In the case of singular cohomology of a manifold $X$, $H^q_(#[sing],c) (X, Lambda)$ is defined using compactly supported cochains. Etale cohomology is not defined using cochains, but as a derived functor cohomology. 

- If we view singular cohomology from the perspective of considering it as a derived functor cohomology, $H^q_(#[sing],c) (X, Lambda)$ may be reinterpreted as follows. Suppose for now that there is an open inclusion $j: X -> ol(X)$ in which $ol(X)$ is a compact manifold. Then: 
  $
    H^q_(#[sing],c) (X, Lambda) &= dirlim_(K subset X #[compact]) H^q_#[sing] (X, X - K, Lambda) = dirlim_(K subset X #[compact]) H^q (ol(X), ol(X) - K, Lambda) #[by excision] \
    &= dirlim_(K subset X #[compact]) H^q (ol(X), i_K^! ul(Lambda)_K) = H^q (ol(X), dirlim_(K subset X #[compact]) i_K^! ul(Lambda)_K) = H^q (ol(X), j_! ul(Lambda)_X)
  $
  Therefore, we see that singular cohomology with compact support may be defined using an external compactification. 

In the settings of etale cohomology, Nagata compactification will play the role of a (non-canonical) compactification, allowing $R Gamma_c$ and $R f_!$ to be defined. One must remark that although these functors are (of course) independent from the choice of compactification, they cannot be defined intrinsically without the choice of an embedding into a "compact" (i.e. proper) ambient space. 

== Construction of $R f_!$ and $R Gamma_c$

As we've just remarked, $R f_!$ and $R Gamma_c$ are defined via an external compactification. This requires the existence of some compactification. 

#theorem(name: <nagata-compactification>)[
  (Nagata compactification) Let $f: X -> Y$ be a separated morphism of finite type between qcqs schemes. Then $f$ factors into: 
  $
    X ->^j ol(X) ->^(ol(f)) Y
  $
  in which $j$ is an open immersion and $ol(f)$ is proper. 
]
#proof[
  This is a very famous and standard result in algebraic geometry. We refer to #cite-stacks("0F41")[Theorem 38.33.8]. 
]
The upshot of this chapter would be to define: 
$
  R f_! = R ol(f)_* compose j_!
$
However, the choice of compactification is highly non-unique and non-canonical, so it is a necessity that we establish some generalities regarding compactifications in advance, so that we can establish compatibility between $R ol(f)_* compose j_!$ defined by various compactifications. 

#definition(name: <defn-compactification>)[
  For a morphism $f: X -> Y$ separated of finite type, a *compactification* of $f$ denotes a factoring: 
  $
    X ->^j ol(X) ->^(ol(f)) Y
  $
  in which $j$ is an open immersion and $ol(f)$ is proper. 
  
  A morphism between two compactifications $X ->^(j_1) ol(X)_1 ->^(ol(f)_1) Y$ and $X ->^(j_2) ol(X)_2 ->^(ol(f)_2) Y$ is a morphism $h: ol(X)_1 -> ol(X)_2$ fitting in the commutative diagram: 
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
  Since proper morphisms cancel, such $h$ is necessarily proper. 
]

#proposition(name: <compactification-filtered>)[
  Let $f: X -> Y$ be a separated morphism of finite type between qcqs schemes. Then the compactifications of $f$ form a directed system. In other words: 

  + Given two compactifications $X ->^(j_i) ol(X)_i ->^(ol(f)_i) Y$, there exists a third compactification $X ->^j ol(X) ->^(ol(f)) Y$ admitting morphisms to both $ol(X)_1$ and $ol(X)_2$. 

  + Given two morphisms $h_(1,2): ol(X)_1 -> ol(X)_2$ between two compactifications $X ->^(j_i) ol(X)_i ->^(ol(f)_i) Y$, there exists a third compactification $X ->^j ol(X) ->^(ol(f)) Y$ and a morphism $g: ol(X) -> ol(X)_1$ of compactifications s.t. $h_1 compose g = h_2 compose g$. 
]
#proof[
  (1) We may form the fiber product: 
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

  Now consider $gamma: X -> ol(X)_1 times_Y ol(X)_2$. It is the product of two immersions, hence an immersion. All schemes here are qcqs. By #cite-stacks("01QV")[Lemma 29.3.2], a quasi-compact immersion factors into an open immersion followed by a closed immersion. Thus, $gamma$ factors into: 
  $
    X ->^j ol(X) ->^t ol(X)_1 times_Y ol(X)_2
  $
  in which $j$ is an open immersion and $t$ is a closed immersion. We now have the diagram: 
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
  Now $phi$ is a product of proper morphisms, hence proper. $t$ is a closed immersion. Thus, we have constructed a compactification $X ->^j ol(X) ->^(phi compose t) Y$ admitting morphisms $h_(1,2)$ to $ol(X)_(1,2)$, respectively. 

  (2) Form the graph morphisms: 
  $
    Gamma_(h_1), Gamma_(h_2): ol(X)_1 -> ol(X)_1 times_Y ol(X)_2
  $
  These morphisms are the base changes of the diagonal $Delta_(ol(X)_1\/Y): ol(X)_2 -> ol(X)_2 times_Y ol(X)_2$ along $h_(1,2): ol(X)_1 -> ol(X)_2$ respectively, hence are closed immersions. We now form the Cartesian square: 
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
  in which every morphism is a closed immersion. Denote the projection $q: ol(X)_1 times_Y ol(X)_2 -> ol(X)_1$. Note: 
  $
    p_1 = p_1 compose Gamma_(h_1) compose q = p_2 compose Gamma_(h_2) compose q = p_2
  $
  and so we may denote $p = p_1 = p_2: W -> ol(X)_1$. We claim that $p$ is the equalizer of $h_(1,2): ol(X)_1 -> ol(X)_2$ in the category of $Y$-schemes. Indeed, a $Y$-morphism $k: Z -> W$ is equivalent to two $Y$-morphisms $k_(1,2): Z -> ol(X)_1$ s.t. $Gamma_(h_1) compose k_1 = Gamma_(h_2) compose k_2$. Applying the two projections, we see that this condition is equivalent to: 
  $
    k_1 = k_2, h_1 compose k_1 = h_2 compose k_2
  $
  and so a $Y$-morphism $k: Z -> W$ is just a $Y$-morphism $k' = k_1 = k_2: Z -> ol(X)_1$ s.t. $h_1 compose k' = h_2 compose k'$. 

  Now in the diagram: 
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
  there exists a $Y$-morphism $j_0: X -> W$ s.t. $p compose j_0 = j_1$, by the universal properties. Now that $j_1$ is an open immersion and $p$ is a closed immersion, so $j_0$ must be an open immersion. Now $ol(f)_1 compose p$ is proper, so: 
  $
    X ->^(j_0) W ->^(ol(f)_1 compose f) Y
  $
  is a compactification with a morphism $p: W -> ol(X)_1$ of compactifications equalizing $h_(1,2)$. 
]

#construction[
  Suppose that we have a commutative square: 
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
  in which vertical morphisms are open immersions and horizontal morphisms are proper. 
  
  #lemma[
    Setup as above, the base change map: 
    $
      j_Y^(-1) R f_(2,*) j_(X,!) -> R f_(1,*) j_X^(-1) j_(X,!) = R f_(1,*)
    $
    is an isomorphism. 
  ]
  #proof[
    Form the base change $tilde(X) = X_2 times_(Y_2) Y_1$, and we have a diagram: 
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
    where $f_1, tilde(f), f_2$ are proper and $tilde(j)$ is an open immersion. Now $j_X = tilde(j) compose p$ where $j_X, tilde(j)$ are open immersions, so $p$ is also an open immersion. On the other hand, since $f_1 = tilde(f) compose p$ where $f_1, tilde(f)$ is proper, $p$ is proper. As such, $p$ is an open and closed immersion. 

    Then the base change $j_Y^(-1) R f_(2,*) j_(X,!) -> R f_(1,*) j_X^(-1) j_(X,!)$ factors into base changes along the two squares, according to the naturality of base change: 
    $
      j_Y^(-1) R f_(2,*) j_(X,!) -> R tilde(f)_* tilde(j)^(-1) j_(X,!) -> R f_(1,*) j_X^(-1) j_(X,!)
    $
    Here, the first base change is an isomorphism by @pbc-etale-bc. For the second base change, note that $p$ is an open and closed immersion, so $R p_* = p_!$, and so $R f_(1,*) j_X^(-1) j_(X,!)= R tilde(f)_* p_! p^(-1) tilde(j) j_(X,!)$. Under this identification, the second base change is just the adjunction unit: 
    $
      R tilde(f)_* tilde(j)^(-1) j_(X,!) -> R f_(1,*) j_X^(-1) j_(X,!)= R tilde(f)_* p_! p^(-1) tilde(j)^(-1) j_(X,!)
    $
    Now the unit $id -> p_! p^(-1) = R p_* p^(-1)$ is an isomorphism on complexes supported on $X_1$, and so $tilde(j)^(-1) j_(X,!) -> p_! p^(-1) tilde(j)^(-1) j_(X,!)$ is an isomorphism. We are thereby done. 
  ]
  
  Then there is a natural transformation: 
  $
    j_(Y,!) R f_(1,*) -> R f_(2,*) j_(X,!)
  $
  between functors $D(X_(1,et), Lambda) -> D(Y_(2,et), Lambda)$, obtained by lifting the inverse of the isomorphism $j_Y^(-1) R f_(2,*) j_(X,!) ->^tilde R f_(1,*)$ through adjunction.
]

#lemma(name: <open-proper-compat-naturality>)[
  The natural transformation $j_(Y,!) R f_(1,*) -> R f_(2,*) j_(X,!)$ constructed above is compatible with horizontal and vertical concatenation of commutative diagrams. 
]
#proof[
  We will prove that the morphism above is a Beck-Chevalley base change, as defined in @bcbc-defn. Indeed, consider the diagram: 
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
  
  Here, the diagonal map $t$ is defined as follows. Setup as in previous lemma: 
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

  We define $t$ to be: 
  $
    t: R f_(1,*) j_X^(-1) = R tilde(f)_* p_! p^(-1) tilde(j)^(-1) -> R tilde(f)_* tilde(j)^(-1) ->^tilde j_Y^(-1) R f_(2,*)
  $
  Here, the second map is an adjunction counit, and the third map is the inverse of base change. 

  Note that the base change map of the upper square is the adjunction unit: 
  $
    R tilde(f)_* -> R tilde(f)_* p_! p^(-1) = R f_(1,*) p^(-1)
  $
  and that the composition $p_! p^(-1) -> id -> p_! p^(-1)$ of unit and counit is an isomorphism. Therefore, the map $t$ above is a section of the base change map $b: j_Y^(-1) R f_(2,*) -> R f_(1,*) j_X^(-1)$. 

  - Indeed, the Beck-Chevalley base change corresponding to this $t$ is the map: #h(1fr)
    $
      j_(Y,!) R f_(1,*) = j_(Y,!) R f_(1,*) j_X^(-1) j_(X,!) ->^(j_(Y,!) t j_(X,!)) j_(Y,!) j_Y^(-1) R f_(2,*) j_(X,!) ->^#[counit] R f_(2,*) j_(X,!)
    $
  
    This corresponds by adjunction to the map $R f_(1,*) -> j_Y^(-1) R f_(2,*) j_(X,!)$ defined by: #h(1fr)
    $
      R f_(1,*) = R f_(1,*) j_X^(-1) j_(X,!) ->^(t j_(X,!)) j_Y^(-1) R f_(2,*) j_(X,!)
    $

    Since $t$ is a section to base change, the map above is a section to the base change $j_Y^(-1) R f_(2,*) j_(X,!) -> R f_(1,*) j_X^(-1) j_(X,!) = R f_(1,*)$, which is an isomorphism by the previous lemma. Thus, the morphism above is exactly the inverse to the base change $j_Y^(-1) R f_(2,*) j_(X,!) ->^tilde R f_(1,*)$. It is thus exactly what the map $j_(Y,!) R f_(1,*) -> R f_(2,*) j_(X,!)$ corresponds to under adjunction, by our construction of this map. Thus $j_(Y,!) R f_(1,*) -> R f_(2,*) j_(X,!)$ is indeed this Beck-Chevalley base change. 

  We claim that $t$ is the unique natural section of $b$, i.e. the unique section as a natural transformation. 

  - $b$ is the composition of two base changes: #h(1fr)
    $
      j_Y^(-1) R f_(2,*) ->^(b_1) R tilde(f)_* tilde(j)^(-1) ->^(b_2) R f_(1,*) j_X^(-1)
    $
    where $b_1$ is an isomorphism. Thus, it suffices to prove that the section of $b_2$ is unique. 

    Let $u: R f_(1,*) j_X^(-1) -> R tilde(f)_* tilde(j)^(-1)$ be a section to $b_2$. 

  - Also form the complement $i: Z -> X_2$ of $j_X: X_1 -> X_2$, a closed immersion. Now for a complex $cal(K) in D(X_(2,et), Lambda)$, there is a distinguished triangle: 
    $
      j_(X,!) j_X^(-1) cal(K) -> cal(K) -> i_* i^(-1) cal(K) ->^(+1)
    $
    Note that $j_X^(-1) i_* i^(-1) cal(K) = 0$. Thus, $u$ is $0$ on $i_* i^(-1) cal(K)$, and so $u$ is determined by its action on objects of the form $j_(X,!) cal(L)$ for $cal(L) in D(tilde(X)_(1,et), Lambda)$. 

  - For such objects, $b_2 j_(X,!)$ is the base change $R tilde(f)_* tilde(j)^(-1) j_(X,!) -> R f_(1,*) j_X^(-1) j_(X,!) = R f_(1,*)$, proven to be an isomorphism by the previous lemma. In other words, $b_2$ is an isomorphism on objects of the form $j_(X,!) cal(L)$, so $u$ acts on these objects by the inverse of $b_2$ and is determined. 

  Thus, $b$ must have a unique section, which is $t$. Now for a horizontal or vertical concatenation of commutative squares, the diagonal maps $t$ defined for the two small squares must compose to $t$ defined for the rectangle, since by @base-change-naturality the naturality of base change, they are both sections to base changes of the large rectangle, hence equal by the uniqueness argued above. 

  Thus, the map $j_(Y,!) R f_(1,*) ->^tilde R f_(2,*) j_(X,!)$ is compatible with horizontal and vertical concatenation of commutative squares, by generalities argued for Beck-Chevalley base changes in @bcbc-horizontal-concat and @bcbc-vertical-concat. 
]

#proposition(name: <open-proper-compat>)[
  Given a commutative diagram: 
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
  in which horizontal morphisms are proper and vertical morphisms are open immersions, and all schemes are noetherian, for $cal(K) in D_#[tor] (X_(1,et), Lambda)$ the canonical map: 
  $
    j_(Y,!) R f_(1,*) cal(K) -> R f_(2,*) j_(X,!) cal(K)
  $
  is a quasi-isomorphism. 
]
#proof[
  According to the construction, when pulled back along $j_Y$, we get the map $R f_(1,*) cal(K) -> j_Y^(-1) R f_(2,*) j_(X,!) cal(K)$ inverse to the base change: 
  $
    j_Y^(-1) R f_(2,*) j_(X,!) cal(K) -> R f_(1,*) j_X^(-1) j_(X,!) cal(K) = R f_(1,*) cal(K)
  $
  and hence an isomorphism. Thus, take the complementary closed immersion $i: Z -> Y_2$ of $j_Y: Y_1 -> Y_2$, it suffices to show that $j_(Y,!) R f_(1,*) cal(K) -> R f_(2,*) j_(X,!) cal(K)$ when pulled back along $i$ is still an isomorphism. 

  Note that $i^(-1) j_(Y,!) = 0$, and so $i^(-1) j_(Y,!) R f_(1,*) cal(K) = 0$. On the other hand, since $cal(K) in D_#[tor] (X_(1,et), Lambda)$, by @torsion-sheaves-first-props, $j_(X,!) cal(K) in D_#[tor] (X_(2,et), Lambda)$ is torsion. Since $f_2$ is proper and all schemes involved are noetherian, proper base change is applicable. We form the Cartesian square by $f_2$ and $i$: 
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
  Then by proper base change: 
  $
    i^(-1) R f_(2,*) j_(X,!) cal(K) = R f'_* i'^(-1) j_(X,!) cal(K)
  $
  However: 
  $
    X_1 times_(X_2) W = X_1 times_(X_2) X_2 times_(Y_2) Z = X_1 times_(Y_2) Z = emptyset
  $
  since the image of $X_1$ in $Y_2$ is contained in $Y_1$ and is disjoint from $Z$. Thus, $i'^(-1) j_(X,!) cal(K) = 0$. 

  In other words, we have proved that $j_(Y,!) R f_(1,*) cal(K) -> R f_(2,*) j_(X,!) cal(K)$ is an isomorphism upon pulling back by $j_Y$, and is a morphism between two zeros upon pulling back by $i$. It is thus an isomorphism. 
]

We are now ready to prove the well-definedness of $R f_!$. 

#theorem(name: <derived-lower-shriek-well-defined>)[
  Let $f: X -> Y$ be a separated morphism of finite type between noetherian schemes. Given two compactifications: 
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
  There is a canonical isomorphism: 
  $
    R ol(f)_(1,*) j_(1,!) cal(K) -> R ol(f)_(2,*) j_(2,!) cal(K)
  $
  for $cal(K) in D_#[tor] (X_et, Lambda)$. 
]
#proof[
  - Step 1. Construction of an isomorphism when there is a morphism $phi: ol(X)_1 -> ol(X)_2$ of compactifications. 

    Given such a morphism $phi$, we have $j_2 = phi compose j_1$ and $ol(f)_1 = ol(f)_2 compose phi$, with $phi$ proper. Now: 
    $
      R ol(f)_(1,*) j_(1,!) cal(K) = R ol(f)_(2,*) R phi_* j_(1,!) cal(K)
    $

    Now consider the commutative diagram: 
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
    in which horizontal morphisms are proper and vertical morphisms are open immersions. Thus by @open-proper-compat, there is a canonical quasi-isomorphism $j_(2,!) cal(K) ->^tilde R phi_* j_(1,!) cal(K)$. Composing with its inverse, we get a quasi-isomorphism: 
    $
      R ol(f)_(1,*) j_(1,!) cal(K) = R ol(f)_(2,*) R phi_* j_(1,!) cal(K) ->^tilde R ol(f)_(2,*) j_(2,!) cal(K)
    $

  - Step 2. Functoriality of this construction. 

    Denote by $R(phi)$ the natural isomorphism $R ol(f)_(1,*) j_(1,!) -> R ol(f)_(2,*) j_(2,!)$ between functors $D_#[tor] (X_et, Lambda) -> D(Y_et, Lambda)$, which is induced by a morphism $phi: ol(X)_1 -> ol(X)_2$ of compactifications. Suppose that we have a chain of morphisms of compactifications: 
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
    Then we claim that: 
    $
      R(psi compose phi) = R(psi) compose R(phi): R ol(f)_(1,*) j_(1,!) -> R ol(f)_(3,*) j_(3,!)
    $

    Consider the commutative diagram: 
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
    with horizontal morphisms being proper, and vertical morphisms being open immersions. 


    By @open-proper-compat, the left/right squares and the large rectangle induces natural isomorphisms: 
    $
      q_1: j_(2,!) -> R phi_* j_(1,!): D_#[tor] (X_et, Lambda) -> D(ol(X)_(2,et), Lambda) \

      q_2: j_(3,!) -> R psi_* j_(2,!): D_#[tor] (X_et, Lambda) -> D(ol(X)_(3,et), Lambda) \

      q_3: j_(3,!) -> R psi_* R phi_* j_(1,!): D_#[tor] (X_et, Lambda) -> D(ol(X)_(3,et), Lambda)
    $
    By @open-proper-compat-naturality, this construction is compatible with horizontal concatenation. Therefore: 
    $
      q_3 = R psi_* q_1 compose q_2
    $
    
    By definition, $R(psi) compose R(phi)$ is the composition: 
    $
      R ol(f)_(1,*) j_(1,!) = R ol(f)_(2,*) R phi_* j_(1,!) ->^(R ol(f)_(2,*) q_1^(-1)) R ol(f)_(2,*) j_(2,!) = R ol(f)_(3,*) R psi_* j_(2,!) ->^(R ol(f)_(3,*) q_2^(-1)) -> R ol(f)_(3,*) j_(3,!)
    $
    However, $R ol(f)_(3,*) q_2^(-1) compose R ol(f)_(2,*) q_1^(-1) = R ol(f)_(3,*) (q_2^(-1) compose R psi_* q_1^(-1)) = R ol(f)_(3,*) (R psi_* q_1 compose q_2)^(-1) = R ol(f)_(3,*) q_3^(-1) = R(psi compose phi)$, so we have proved our claim. 

  - Step 3. Construction of the general isomorphism. 

    For any two compactifications $ol(X)_1, ol(X)_2$, by @compactification-filtered, there is a third compactification $ol(X)_3$ and morphisms $phi_i: ol(X)_3 -> ol(X)_i, i=1,2$ between compactifications. We intend to construct the canonical isomorphism as: 
    $
      R ol(f)_1 j_(1,!) -->^(R(phi_1)^(-1)) R ol(f)_3 j_(3,!) -->^(R(phi_2)) R ol(f)_2 j_(2,!)
    $

    However, the choice of $ol(X)_3$ and $phi_(1,2)$ might be non-unique, so currently this isomorphism is non-canonical. Given a fourth compactification $ol(X)_4$ and morphisms $psi_i: ol(X)_4 -> ol(X)_i, i=1,2$ between compactifications, we must show that $R(phi_1)^(-1) compose R(phi_2) = R(psi_1)^(-1) compose R(psi_2)$. 

    For this, we pick a fifth compactification $ol(X)_5$ with morphisms $chi'_i: ol(X)_5 -> ol(X)_i, i = 3,4$. We thus have pairs of morphisms between compactifications: 
    $
      phi_1 compose chi'_3, psi_1 compose chi'_4: ol(X)_5 -> ol(X)_1 \

      phi_2 compose chi'_3, psi_2 compose chi'_4: ol(X)_5 -> ol(X)_2
    $
    By @compactification-filtered, we may pick a sixth compactification $ol(X)_6$ and a morphism $chi: ol(X)_6 -> ol(X)_5$, s.t: 
    $
      phi_1 compose chi'_3 compose chi = psi_1 compose chi'_4 compose chi: ol(X)_6 -> ol(X)_1 \

      phi_2 compose chi'_3 compose chi = psi_2 compose chi'_4 compose chi: ol(X)_6 -> ol(X)_2
    $
    Take $chi_i = chi'_i compose chi: ol(X)_6 -> ol(X)_i, i = 3,4$, and we have the following commutative diagram of compactifications: 
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
    Then since $phi_1 compose chi_3 = psi_1 compose chi_4$, we have: 
    $
      R(phi_1) compose R(chi_3) = R(psi_1) compose R(chi_4)
    $
    Similarly: 
    $
      R(phi_2) compose R(chi_3) = R(psi_2) compose R(chi_4)
    $
    Thus, $R(phi_1)^(-1) compose R(psi_1) = R(chi_3) compose R(chi_4)^(-1) = R(phi_2)^(-1) compose R(psi_2)$, and so: 
    $
      R(phi_2) compose R(phi_1)^(-1) = R(psi_2) compose R(psi_1)^(-1)
    $
    We are thereby done. 
]

Finally, we prove a lemma stating that $R f_*$ for proper $f$ preserves torsion complexes, thus completing the construction of $R f_!$ as a functor on $D_#[tor]$. 

#lemma(name: <derived-lower-shriek-preserves-torsion>)[
  For $f: X -> Y$ proper between noetherian schemes, $R f_*$ sends complexes in $D_#[tor] (X_et, Lambda)$ to complexes in $D_#[tor] (Y_et, Lambda)$. 
]
#proof[
  By @derived-artin-grothendieck-vanishing, $R f_*$ is bounded both above and below. Thus, given a complex $cal(K) in D_#[tor] (X_et, Lambda)$ and a fixed $q$, there exists some truncation $sigma_([a,b]) (cal(K)) in D^b_#[tor] (X_et, Lambda)$ s.t. $R f_* (sigma_([a,b]) cal(K)) -> R f_* cal(K)$ induces an isomorphism on $h^q$. 

  Thus, it suffices to prove that $R f_*$ sends $D^b_#[tor]$ to $D_#[tor]$. By truncation triangles, it suffices to prove that $R f_*$ sends $cAb_#[tor] (X_et, Lambda)$ to $D_#[tor] (Y_et, Lambda)$. 
  
  Denote by $T_n (cal(F))$ the $n$-torsion of a sheaf $cal(F)$ (because the notation $cal(F)[n]$ is taken by shifts of complexes). For every torsion sheaf $cal(F) in cAb_#[tor] (X_et, Lambda)$, by @relative-limit-formula-for-sheaves, 
  $
    R^q f_* cal(F) = R^q f_* (dirlim_n T_n (cal(F))) = dirlim_n R^q f_* (T_n (cal(F)))
  $
  is a direct limit of torsion sheaves, hence torsion. Thus, the cohomology sheaves of $R f_* cal(F)$ are torsion, hence $R f_* cal(F)$ is in $D_#[tor] (Y_et, Lambda)$. 
]

#definition(name: <defn-derived-pushforward-with-proper-support>)[
  Let $f: X -> Y$ be a separated morphism of finite type between noetherian schemes. Pick any compactification: 
  $
    X ->^j ol(X) ->^(ol(f)) Y
  $
  We define the functor $R f_!$ to be: 
  $
    R f_!: D_#[tor] (X_et, Lambda) &-> D_#[tor] (Y_et, Lambda) \
    cal(K) &|-> R ol(f)_* j_! cal(K)
  $
  By @derived-lower-shriek-well-defined and @derived-lower-shriek-preserves-torsion, this functor is well-defined and independent from the compactification chosen. In particular, for any compactification $X ->^j ol(X) ->^(ol(f)) Y$ of $f$, there exists a natural isomorphism: 
  $
    R ol(f)_* j_! cong R f_!: D_#[tor] (X_et, Lambda) &-> D_#[tor] (Y_et, Lambda)
  $
  compatible with the isomorphisms in @derived-lower-shriek-well-defined. 

  This functor is called derived *pushforward with proper support*. 
]

#definition(name: <defn-cohomology-with-proper-support>)[
  Suppose that $X$ is a separated scheme of finite type over $Spec(k)$, with $k$ a separably closed field. Let $f: X -> Spec(k)$ be the structure map. $R Gamma_c (X, -)$ is defined to be the functor: 
  $
    D_#[tor] (X_et, Lambda) ->^(R f_!) D_#[tor] (Spec(k)_et, Lambda) ->^tilde D_#[tor] (Lambda)
  $

  This functor is called *cohomology with proper support*. 
]

#notation(name: <proper-support-cohomology-notation>)[
  For a sheaf $cal(F) in cAb_#[tor] (X_et, Lambda)$: 

  - Given a separated morphism $f: X -> Y$ of finite type between noetherian schemes, we denote by: #h(1fr)
    $
      R^q f_! cal(F) := h^q (R f_! cal(F)) \
      f_! cal(F) := h^0 (R f_! cal(F))
    $

  - If $X$ is a separated scheme of finite type over $Spec(k)$ for a separably closed field $k$, we denote by: 
    $
      H^q_c (X, cal(F)) := h^q (R Gamma_c (X, cal(F))) \
      Gamma_c (X, cal(F)) := h^0 (R Gamma_c (X, cal(F)))
    $

  #remark[
    There are some subtleties with this notation: 

    - The notation $f_! cal(F) := h^0 (R f_! cal(F))$ clashes with the notation for the functor $f_!$ defined in @etale-lower-shriek-defn. However, these notations are consistent. We will show that for a morphism $f: X -> Y$ that is separated and etale between noetherian schemes: #h(1fr)
      $
        R f_! = f_!: D_#[tor] (X_et, Lambda) -> D_#[tor] (Y_et, Lambda)
      $
      where $R f_!$ is pushforward with proper support defined above, and $f_!$ is as defined in @etale-lower-shriek-defn. 

    - Although $Gamma_c (X, -)$ and $f_!$ are left exact functors, $R Gamma_c (X, -)$ and $R f_!$, or $H^q_c (X, -)$ and $R^q f_!$, are not their derived functors. 

      As such, there is a slight abuse of notation. You should keep this point in mind. 
  ]
]
