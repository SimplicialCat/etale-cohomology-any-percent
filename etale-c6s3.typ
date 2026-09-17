#import "void-import.typ": *

== Devissage: proof of (Dev) and (Comp)

In this section, we use devissage arguments with constructible sheaves to prove the statements (Dev) and (Comp). 

#theorem(name: <pbc-comp>)[
  (Comp) 
  
  + In a diagram of successive base changes:
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
    We have:
    $
      BC (f, g) and BC (h, g') ==> BC (h compose f, g)
    $
    i.e. if the base change theorem holds for the left and right small squares, then it holds for the large rectangle. 

  + In a diagram of successive base changes:
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
    We have: 
    $
      BC(f, g) and BC(f', h) ==> BC(f, g compose h)
    $
    i.e. if the base change theorem holds for the upper and lower small squares, then it holds for the large rectangle. 
]
#proof[
  (1) We first show that the base change map: 
  $
    g^(-1) R^q (h compose f)_* cal(F) -> R^q (h' compose f')_* g''^(-1) cal(F)
  $
  is an isomorphism for $cal(F) in cAb(Z_et)$ where $cal(F)$ is $n$-torsion for a fixed $n >= 1$. 

  Let $cal(F) in cAb(Z_et)$ be $n$-torsion, and consider the Leray spectral sequence (@derived-lower-star-first-props (1)): 
  $
    R^p h_* (R^q f_* cal(F)) ==> R^(p+q) (h compose f)_* cal(F)
  $
  Applying the exact functor $g^(-1)$ to the spectral sequence, we obtain a new spectral sequence: 
  $
    g^(-1) (R^p h_* (R^q f_* cal(F))) ==> g^(-1) (R^(p+q) (h compose f)_* cal(F))
  $
  Meanwhile, by base change theorems along both squares on left and right: 
  $
    g^(-1) (R^p h_* (R^q f_* cal(F))) cong R^p h'_* (g'^(-1) (R^q f_* cal(F))) cong R^p h'_* (R^q f'_* (g''^(-1) cal(F)))
  $
  where since $times n: cal(F) -> cal(F)$ is zero, so are $times n: R^q f_* cal(F) -> R^q f_* cal(F)$, and so $cal(F)$ and $R^q f_* cal(F)$ are both $n$-torsion, and base change theorems are applicable. By @base-change-naturality, the Leray spectral sequence is compatible with base change maps, so this spectral sequence turns via base change isomorphisms into: 
  $
    R^p h'_* (R^q f'_* (g''^(-1) cal(F))) ==> g^(-1) (R^(p+q) (h compose f)_* cal(F))
  $
  However, by the Leray spectral sequence @derived-lower-star-first-props (1), 
  $
    R^p h'_* (R^q f'_* (g''^(-1) cal(F))) ==> R^(p+q) (h' compose f')_* (g''^(-1) cal(F))
  $
  Thus the base change map $g^(-1) (R^q (h compose f)_* cal(F)) -> R^q (h' compose f')_* (g''^(-1) cal(F))$ is an isomorphism. 

  Next, we consider general torsion sheaves $cal(F) in cAb(Z_et)$. By definition of torsion sheaves, $cal(F) = dirlim_(n>=1) cal(F)[n]$. Write $cal(F) = dirlim_i cal(F)_i$, where each $cal(F)_i$ is $n_i$-torsion for some $n_i$, and apply @relative-limit-formula-for-sheaves and the result for torsion sheaves annihilated by a fixed integer: 
  $
    & g^(-1) (R^q (h compose f)_* cal(F)) cong g^(-1) (R^q (h compose f)_* (dirlim_(i in I) cal(F)_i)) \
    cong& dirlim_(i in I) g^(-1) (R^q (h compose f)_* cal(F)_i) #[by @relative-limit-formula-for-sheaves and $g^(-1)$ being a left adjoint] \
    cong& dirlim_(i in I) R^q (h' compose f')_* (g''^(-1) cal(F)_i) #[by result for $n$-torsion sheaves] \
    cong& R^q (h' compose f')_* (g''^(-1) cal(F)) #[by @relative-limit-formula-for-sheaves and $g''^(-1)$ being a left adjoint]
  $

  (2) is very easy: By @base-change-naturality, the base change is compatible with vertical concatenation of Cartesian squares, so we may write down: 
  $
    (g compose h)^(-1) R^q f_* cal(F) cong h^(-1) g^(-1) R^q f_* cal(F) cong h^(-1) R^q f'_* (g'^(-1) cal(F)) cong R^q f''_* (h'^(-1) g'^(-1) cal(F)) cong R^q f''_* (g' compose h')^(-1) cal(F)
  $
  where since $cal(F)$ is torsion, $g'^(-1) cal(F)$ is torsion by @pullback-of-torsion-sheaf, so that base change is applicable. 
]

This argument for (Comp) is mainly done through a spectral sequence argument, that becomes almost trivial when viewed in the derived category: 
$
  g^(-1) R(h compose f)_* cal(F) cong g^(-1) (R h_* (R f_* cal(F))) cong R h'_* (g'^(-1) (R f_* cal(F))) cong R h'_* (R f'_* (g''^(-1) cal(F))) = R(h' compose f')_* (g''^(-1) cal(F))
$
where in the derived category, the Leray spectral sequence is really just $R(h compose f)_* = R h_* compose R f_*$. 

Next, we will demonstrate the power of constructible sheaves, when we perform the critical devissage required to reduce arbitrary torsion sheaves to $ul(ZZ\/n)$. 

#theorem(name: <pbc-dev>)[
  (Dev) Whenever $A$ is strict henselian noetherian and $X -> Spec(A)$ is noetherian, 
  $
      ( & forall tilde(X) -> X #[finite], forall n >= 1, \
        & BC^0_* (tilde(X) -> X -> Spec(A), ul(ZZ\/n)) and (forall q>=1, BC^q_(*,#[surj]) (tilde(X) -> X -> Spec(A), ul(ZZ\/n)))) \
    // ==>&(&&forall tilde(X) -> X #[finite], forall cal(F) in cAb(tilde(X)_et) #[torsion], forall q>=0, \
    // &&& BC^q_(*,#[surj])(tilde(X) -> X -> Spec(A), cal(F))))
    ==> & (forall tilde(X) -> X #[finite], BC_* (tilde(X) -> Spec(A)))
  $
  In plain English, given $X -> Spec(A)$ for $A$ strict henselian noetherian and $X$ noetherian, if for all finite $tilde(X) -> X$, the base change map: 
  $
    res_(ul(ZZ\/n))^(q,tilde(X)): H^q (tilde(X), ul(ZZ\/n)) -> H^q (tilde(X)_0, ul(ZZ\/n))
  $
  is bijective for $q = 0$ and surjective for all $q >= 1$, then for all finite $tilde(X) -> X$, the base change map:
  $
    res_(cal(F))^(q,tilde(X)): H^q (tilde(X), cal(F)) -> H^q (tilde(X)_0, cal(F)|_(tilde(X)_0))
  $
  is bijective for all torsion $cal(F) in cAb(tilde(X)_et)$. 
]
#proof[
  The main idea is that we perform dimension reduction along two exact sequences. 

  #lemma(name: <pbc-dev-lem1>)[
    Given any noetherian $X -> Spec(A)$ and fixed $q >= 0$, if $res_(cal(F))^(q,tilde(X))$ is injective/surjective/bijective for all constructible $cal(F) in cAb(X_et)$, the same holds for all torsion $cal(F) in cAb(X_et)$. 
  ]
  #proof[
    By @constructible-sheaves-first-props (6), every torsion $cal(F)$ can be written as a direct limit of its constructible subsheaves: 
    $
      cal(F) = dirlim_(i in I) cal(F)_i
    $
    where each $cal(F)_i$ is constructible. Now by @limit-formula-for-sheaves and the fact that pullbacks preserve colimits as left adjoints, 
    $
      H^q (X, cal(F)) = dirlim_(i in I) H^q (X, cal(F)_i) \
      H^q (X_0, cal(F)|_(X_0)) = dirlim_(i in I) H^q (X_0, cal(F)_i|_(X_0))
    $
    and so as morphisms: 
    $
      res^(q,X)_(cal(F)) = dirlim_(i in I) res^(q,X)_(cal(F)_i)
    $
    By (Ab5) of $cAb$, the injective/surjective/bijective properties of $res^(q,X)_(cal(F)_i)$ passes to $res^(q,X)_(cal(F))$. 
  ]

  #lemma(name: <pbc-dev-lem2>)[
    Given any noetherian $X -> Spec(A)$ and fixed $q >= 1$, if: 

    - For all $p < q$ and all torsion $cal(F) in cAb(X_et)$, $res^(p,X)_(cal(F))$ is bijective. 

    Then: 

    - For all torsion $cal(F) in cAb(X_et)$, $res^(q,X)_(cal(F))$ is injective. 
  ]
  #proof[
    By @pbc-dev-lem1, it suffices to prove that for all constructible $cal(F) in cAb(X_et)$, $res^(q,X)_(cal(F))$ is injective. Suppose that $cal(F)$ is $n$-torsion. Then by @acyclic-godement-resolution, there exists an $n$-torsion $Gamma(X, -)$-acyclic sheaf $cal(C)$ and an injection $cal(F) -> cal(C)$. Forming the cokernel, we have an exact sequence: 
    $
      0 -> cal(F) -> cal(C) -> cal(R) -> 0
    $
    of $n$-torsion sheaves on $X$. We thus have an exact sequence of $n$-torsion sheaves: 
    $
      0 -> cal(F)|_(X_0) -> cal(C)|_(X_0) -> cal(R)|_(X_0) -> 0
    $
    of $n$-torsion sheaves on $X_0$. Now consider the long exact sequence on cohomology, paired with naturality of base change morphisms: 
    // https://q.uiver.app/#r=typst&q=WzAsMTIsWzEsMCwiSF4ocS0xKSAoWCwgY2FsKEMpKSJdLFsyLDAsIkheKHEtMSkgKFgsIGNhbChSKSkiXSxbMywwLCJIXnEgKFgsIGNhbChGKSkiXSxbNCwwLCJvdmVyYnJhY2UoSF5xIChYLCBjYWwoQykpLCAwKSJdLFsxLDEsIkheKHEtMSkgKFhfMCwgY2FsKEMpfF8oWF8wKSkiXSxbMiwxLCJIXihxLTEpIChYXzAsIGNhbChSKXxfKFhfMCkpIl0sWzMsMSwiSF5xIChYXzAsIGNhbChGKXxfKFhfMCkpIl0sWzQsMSwiSF5xIChYXzAsIGNhbChDKXxfKFhfMCkpIl0sWzAsMCwiZG90cy5jIl0sWzAsMSwiZG90cy5jIl0sWzUsMCwiZG90cy5jIl0sWzUsMSwiZG90cy5jIl0sWzAsMV0sWzEsMl0sWzIsM10sWzQsNV0sWzUsNl0sWzYsN10sWzgsMF0sWzksNF0sWzMsMTBdLFs3LDExXSxbMCw0LCJyZXNeKHEtMSxYKV8oY2FsKEMpKSIsMCx7InN0eWxlIjp7InRhaWwiOnsibmFtZSI6Imhvb2siLCJzaWRlIjoidG9wIn0sImhlYWQiOnsibmFtZSI6ImVwaSJ9fX1dLFsxLDUsInJlc14ocS0xLFgpXyhjYWwoUikpIiwxLHsic3R5bGUiOnsidGFpbCI6eyJuYW1lIjoiaG9vayIsInNpZGUiOiJ0b3AifSwiaGVhZCI6eyJuYW1lIjoiZXBpIn19fV0sWzIsNiwicmVzXihxLFgpXyhjYWwoRikpIiwxXSxbMyw3LCJyZXNeKHEsWClfKGNhbChDKSkiLDEseyJzdHlsZSI6eyJ0YWlsIjp7Im5hbWUiOiJob29rIiwic2lkZSI6InRvcCJ9fX1dXQ==
    #align(center, diagram({
      node((-2, -1), [$H^(q-1) (X, cal(C))$])
      node((-1, -1), [$H^(q-1) (X, cal(R))$])
      node((0, -1), [$H^q (X, cal(F))$])
      node((1, -1), [$overbrace(H^q (X, cal(C)), 0)$])
      node((-2, 0), [$H^(q-1) (X_0, cal(C)|_(X_0))$])
      node((-1, 0), [$H^(q-1) (X_0, cal(R)|_(X_0))$])
      node((0, 0), [$H^q (X_0, cal(F)|_(X_0))$])
      node((1, 0), [$H^q (X_0, cal(C)|_(X_0))$])
      node((-3, -1), [$dots.c$])
      node((-3, 0), [$dots.c$])
      node((2, -1), [$dots.c$])
      node((2, 0), [$dots.c$])
      edge((-2, -1), (-1, -1), "->")
      edge((-1, -1), (0, -1), "->")
      edge((0, -1), (1, -1), "->")
      edge((-2, 0), (-1, 0), "->")
      edge((-1, 0), (0, 0), "->")
      edge((0, 0), (1, 0), "->")
      edge((-3, -1), (-2, -1), "->")
      edge((-3, 0), (-2, 0), "->")
      edge((1, -1), (2, -1), "->")
      edge((1, 0), (2, 0), "->")
      edge((-2, -1), (-2, 0), [$res^(q-1,X)_(cal(C))$], label-side: left, "hook->>")
      edge((-1, -1), (-1, 0), [$res^(q-1,X)_(cal(R))$], label-side: left, "hook->>")
      edge((0, -1), (0, 0), [$res^(q,X)_(cal(F))$], label-side: left, "->")
      edge((1, -1), (1, 0), [$res^(q,X)_(cal(C))$], label-side: left, "hook->")
    }, spacing: (2.4em, 3em)))
    where: 

    - The first two vertical arrows are bijective by inductive hypothesis, since $cal(C), cal(R)$ are $n$-torsion; 

    - The fourth vertical arrow is injective since $H^q (X, cal(C)) = 0$ due to acyclicity of $cal(C)$. 

    By the four lemma for monomorphisms, $res^(q,X)_(cal(F))$ is injective. 
  ]

  #lemma(name: <pbc-dev-lem3>)[
    Given any noetherian $X -> Spec(A)$ and fixed $q >= 0$, if: 

    - For all $p < q$, all finite $tilde(X) -> X$ and all torsion $cal(F) in cAb(tilde(X)_et)$, $res_(cal(F))^(p,tilde(X))$ is bijective. 

    - For all finite $tilde(X) -> X$, $res_(ul(ZZ\/n))^(q,tilde(X))$ is surjective, and in addition bijective when $q = 0$. 

    Then: 

    - For all finite $tilde(X) -> X$ and all torsion $cal(F) in cAb(tilde(X)_et)$, $res_(cal(F))^(q,tilde(X))$ is bijective. 
  ]
  #proof[
    By @pbc-dev-lem1, it suffices to prove when $cal(F)$ is constructible. By replacing $X$ with $tilde(X)$ we may also assume that $cal(F) in cAb(X_et)$. Now by @finite-morphisms-and-constructible-sheaves (2), there exists a finite morphism $g: tilde(X) -> X$ and an injection $cal(F) -> g_* ul(ZZ\/n)_(tilde(X))$. Forming the cokernel, we have an exact sequence of constructible sheaves: 
    $
      0 -> cal(F) -> g_* ul(ZZ\/n)_(tilde(X)) -> cal(R) -> 0
    $
    Base change $g: tilde(X) -> X$ to $g_0: tilde(X)_0 -> X_0$. Then by (Finite) (@pbc-finite), upon pulling back to $X_0$, we have an exact sequence of constructible sheaves: 
    $
      0 -> cal(F)|_(X_0) -> g_(0,*) ul(ZZ\/n)_(tilde(X)_0) -> cal(R)|_(X_0) -> 0
    $
    Now consider the long exact sequence on cohomology, paired with naturality of base change morphisms, together with @pushforward-by-finite-morphism: 

    - Case $q = 0$: We have a commutative diagram: #h(1fr)
      // https://q.uiver.app/#r=typst&q=WzAsMTAsWzAsMCwiMCJdLFswLDEsIjAiXSxbMSwwLCJIXjAgKFgsIGNhbChGKSkiXSxbMSwxLCJIXjAgKFhfMCwgY2FsKEYpfF8oWF8wKSkiXSxbMywwLCJIXjAgKFgsIGNhbChSKSkiXSxbMywxLCJIXjAgKFhfMCwgY2FsKFIpfF8oWF8wKSkiXSxbMiwwLCJIXjAgKHRpbGRlKFgpLCB1bChaWlxcL24pKSJdLFsyLDEsIkheMCAodGlsZGUoWClfMCwgdWwoWlpcXC9uKSkiXSxbNCwwLCJkb3RzLmMiXSxbNCwxLCJkb3RzLmMiXSxbMiw2LCIiLDAseyJzdHlsZSI6eyJ0YWlsIjp7Im5hbWUiOiJob29rIiwic2lkZSI6InRvcCJ9fX1dLFswLDJdLFs2LDRdLFsxLDNdLFszLDcsIiIsMCx7InN0eWxlIjp7InRhaWwiOnsibmFtZSI6Imhvb2siLCJzaWRlIjoidG9wIn19fV0sWzcsNV0sWzIsMywicmVzXigwLFgpXyhjYWwoRikpIl0sWzQsNSwicmVzXigwLFgpXyhjYWwoUikpIl0sWzYsNywicmVzXigwLHRpbGRlKFgpKV8odWwoWlpcXC9uKSkiLDAseyJzdHlsZSI6eyJ0YWlsIjp7Im5hbWUiOiJob29rIiwic2lkZSI6InRvcCJ9LCJoZWFkIjp7Im5hbWUiOiJlcGkifX19XSxbNCw4XSxbNSw5XV0=
      #align(center, diagram({
        node((-3, -1), [$0$])
        node((-3, 0), [$0$])
        node((-2, -1), [$H^0 (X, cal(F))$])
        node((-2, 0), [$H^0 (X_0, cal(F)|_(X_0))$])
        node((0, -1), [$H^0 (X, cal(R))$])
        node((0, 0), [$H^0 (X_0, cal(R)|_(X_0))$])
        node((-1, -1), [$H^0 (tilde(X), ul(ZZ\/n))$])
        node((-1, 0), [$H^0 (tilde(X)_0, ul(ZZ\/n))$])
        node((1, -1), [$dots.c$])
        node((1, 0), [$dots.c$])
        edge((-2, -1), (-1, -1), "hook->")
        edge((-3, -1), (-2, -1), "->")
        edge((-1, -1), (0, -1), "->")
        edge((-3, 0), (-2, 0), "->")
        edge((-2, 0), (-1, 0), "hook->")
        edge((-1, 0), (0, 0), "->")
        edge((-2, -1), (-2, 0), [$res^(0,X)_(cal(F))$], label-side: left, "->")
        edge((0, -1), (0, 0), [$res^(0,X)_(cal(R))$], label-side: left, "->")
        edge((-1, -1), (-1, 0), [$res^(0,tilde(X))_(ul(ZZ\/n))$], label-side: left, "hook->>")
        edge((0, -1), (1, -1), "->")
        edge((0, 0), (1, 0), "->")
      }, spacing: (2.4em, 3em)))
      
      - The first vertical arrow $res^(0,X)_(cal(F))$ is injective, since all other arrows in the first square are injective. 

      - This shows that for all constructible $cal(F) in cAb(X_et)$, $res^(0,X)_(cal(F))$ is injective. In particular, the third vertical arrow $res^(0,X)_(cal(R))$ is injective. 

      - Since the second vertical arrow $res^(0,tilde(X))_(ul(ZZ\/n))$ is surjective and the third vertical arrow $res^(0,X)_(cal(R))$ is injective, by the four lemma for epimorphisms, $res^(0,X)_(cal(F))$ is surjective. 

      We are thereby done in this case. 

    - Case $q >= 1$. In this case, the inductive hypothesis allows us to apply @pbc-dev-lem2, and conclude that: 

      - For all finite $tilde(X) -> X$ and all torsion $cal(F) in cAb(tilde(X)_et)$, $res_(cal(F))^(q,tilde(X))$ is injective. 

      Now consider the same long exact sequence: 
      // https://q.uiver.app/#r=typst&q=WzAsMTIsWzEsMCwiSF4ocS0xKSAoWCwgY2FsKFIpKSJdLFsyLDAsIkhecSAoWCwgY2FsKEYpKSJdLFszLDAsIkhecSAodGlsZGUoWCksIHVsKFpaXFwvbikpIl0sWzQsMCwiSF5xIChYLCBjYWwoUikpIl0sWzMsMSwiSF5xICh0aWxkZShYKV8wLCB1bChaWlxcL24pKSJdLFs0LDEsIkhecSAoWF8wLCBjYWwoUil8XyhYXzApKSJdLFsxLDEsIkheKHEtMSkgKFhfMCwgY2FsKFIpfF8oWF8wKSkiXSxbMiwxLCJIXnEgKFhfMCwgY2FsKEYpfF8oWF8wKSkiXSxbMCwwLCJkb3RzLmMiXSxbMCwxLCJkb3RzLmMiXSxbNSwwLCJkb3RzLmMiXSxbNSwxLCJkb3RzLmMiXSxbMCwxXSxbMSwyXSxbMiwzXSxbNiw3XSxbNyw0XSxbNCw1XSxbMiw0LCJyZXNeKHEsdGlsZGUoWCkpXyh1bChaWlxcL24pKSIsMCx7InN0eWxlIjp7InRhaWwiOnsibmFtZSI6Imhvb2siLCJzaWRlIjoidG9wIn0sImhlYWQiOnsibmFtZSI6ImVwaSJ9fX1dLFsxLDcsInJlc14ocSxYKV8oY2FsKEYpKSIsMCx7InN0eWxlIjp7InRhaWwiOnsibmFtZSI6Imhvb2siLCJzaWRlIjoidG9wIn19fV0sWzAsNiwicmVzXihxLTEsWClfKGNhbChSKSkiLDAseyJzdHlsZSI6eyJ0YWlsIjp7Im5hbWUiOiJob29rIiwic2lkZSI6InRvcCJ9LCJoZWFkIjp7Im5hbWUiOiJlcGkifX19XSxbOCwwXSxbOSw2XSxbMywxMF0sWzUsMTFdLFszLDUsInJlc14ocSxYKV8oY2FsKFIpKSIsMCx7InN0eWxlIjp7InRhaWwiOnsibmFtZSI6Imhvb2siLCJzaWRlIjoidG9wIn19fV1d
      #align(center, diagram({
        node((2, 0), [$H^(q-1) (X, cal(R))$])
        node((3, 0), [$H^q (X, cal(F))$])
        node((4, 0), [$H^q (tilde(X), ul(ZZ\/n))$])
        node((5, 0), [$H^q (X, cal(R))$])
        node((4, 1), [$H^q (tilde(X)_0, ul(ZZ\/n))$])
        node((5, 1), [$H^q (X_0, cal(R)|_(X_0))$])
        node((2, 1), [$H^(q-1) (X_0, cal(R)|_(X_0))$])
        node((3, 1), [$H^q (X_0, cal(F)|_(X_0))$])
        node((1, 0), [$dots.c$])
        node((1, 1), [$dots.c$])
        node((6, 0), [$dots.c$])
        node((6, 1), [$dots.c$])
        edge((2, 0), (3, 0), "->")
        edge((3, 0), (4, 0), "->")
        edge((4, 0), (5, 0), "->")
        edge((2, 1), (3, 1), "->")
        edge((3, 1), (4, 1), "->")
        edge((4, 1), (5, 1), "->")
        edge((4, 0), (4, 1), [$res^(q,tilde(X))_(ul(ZZ\/n))$], label-side: left, "hook->>")
        edge((3, 0), (3, 1), [$res^(q,X)_(cal(F))$], label-side: left, "hook->")
        edge((2, 0), (2, 1), [$res^(q-1,X)_(cal(R))$], label-side: left, "hook->>")
        edge((1, 0), (2, 0), "->")
        edge((1, 1), (2, 1), "->")
        edge((5, 0), (6, 0), "->")
        edge((5, 1), (6, 1), "->")
        edge((5, 0), (5, 1), [$res^(q,X)_(cal(R))$], label-side: left, "hook->")
      }, spacing: (2.4em, 3em)))
      where: 
      - The first vertical arrow is bijective by the inductive hypothesis; 

      - The second, third and fourth arrow are injective, since we have proved using @pbc-dev-lem2 that for all finite $tilde(X) -> X$ and all torsion $cal(F) in cAb(tilde(X)_et)$, $res_(cal(F))^(q,tilde(X))$ is injective. 

      - The third arrow is surjective by our hypothesis on $res^(q,tilde(X))_(ul(ZZ\/n))$. 

      By the four lemma for epimorphisms, the second vertical arrow $res^(q,X)_(cal(F))$ is surjective, hence bijective. We are thereby done. 
  ]
  After proving the three lemmas, the third lemma (@pbc-dev-lem3) and the theorem hypothesis allow us to perform induction and show that $res^(q,X)_(cal(F))$ is bijective for all $q >= 0$ and torsion $cal(F) in cAb(X_et)$. 
]
