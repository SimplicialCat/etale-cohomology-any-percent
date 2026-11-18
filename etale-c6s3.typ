#import "void-import.typ": *

== Devissage: proof of (Dev) and (Comp)

In this section, we use devissage arguments with constructible sheaves to prove the statements (Dev) and (Comp). 

#theorem(name: <pbc-comp>)[
  (Comp) 
  
  + In a diagram of successive base changes with $f$ and $h$ qcqs:
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
    we have:
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
    we have: 
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

First, we prove an abstract lemma that serves as the framework of devissage. 
#lemma(name: <abstract-devissage>)[
  (Abstract devissage) Let $cal(A), cal(B)$ be abelian categories, so that $cal(B)$ has (Ab5). 
  
  Let $S^q,T^q: cal(A) -> cal(B)$ be two $delta$-functors defined for all degrees $q in ZZ$ defined for all $cal(R)$, with a natural transformation $eta^q: S^q -> T^q$ of $delta$-functors. Suppose that: 

  - $S^q, T^q$ commute with directed limits. 

  - There exists $a in ZZ$ s.t. for all $q < a$, $S^q = T^q = 0$. 

  - Every object in $cal(A)$ can be written as a directed limit of objects in a certain subset of objects $cal(A)_0 subset cal(A)$. 

  - For every $q >= a$, every object $A in cal(A)_0$ admits embeddings $A arrow.hook C, D$ into objects $C, D in cal(A)$ so tha $eta^q_C: S^q (C) -> T^q (C)$ is injective, and $eta^q_D: S^q (D) -> T^q (D)$ is surjective. 

  Then $eta^q: S^q -> T^q$ is an natural isomorphism of $delta$-functors.

  If we may take $cal(A)_0 = cal(A)$ itself, then the requirements on commuting with directed limits and on (Ab5) may be omitted.
]
#proof[
  Let $P(n)$ denote the statement that: 

  - For all degrees $q <= n$, $eta^q: S^q -> T^q$ is a natural isomorphism. 

  Then the vanishing below degree $a$ gives the base case $P(a-1)$ automatically. We now perform induction, assuming $P(n-1)$ and aiming to prove $P(n)$. 

  - For every $A in cal(A)_0$, embed it as $A arrow.hook C$ so that $eta^q_C$ is injective, and form the cokernel $0 -> A -> C -> R -> 0$. Now consider the commutative diagram with exact rows: 
    // https://q.uiver.app/#r=typst&q=WzAsMTIsWzAsMCwiZG90cy5jIl0sWzEsMCwiU14obi0xKSAoQykiXSxbMiwwLCJTXihuLTEpIChSKSJdLFszLDAsIlNebiAoQSkiXSxbNCwwLCJTXm4gKEMpIl0sWzUsMCwiZG90cy5jIl0sWzAsMSwiZG90cy5jIl0sWzUsMSwiZG90cy5jIl0sWzEsMSwiVF4obi0xKSAoQykiXSxbMiwxLCJUXihuLTEpIChSKSJdLFszLDEsIlRebiAoQSkiXSxbNCwxLCJUXm4gKEMpIl0sWzAsMV0sWzEsMl0sWzIsM10sWzMsNF0sWzQsNV0sWzYsOF0sWzgsOV0sWzksMTBdLFsxMCwxMV0sWzExLDddLFsxLDgsImV0YV4obi0xKV9DIiwxLHsic3R5bGUiOnsidGFpbCI6eyJuYW1lIjoiaG9vayIsInNpZGUiOiJ0b3AifSwiaGVhZCI6eyJuYW1lIjoiZXBpIn19fV0sWzIsOSwiZXRhXihuLTEpX1IiLDEseyJzdHlsZSI6eyJ0YWlsIjp7Im5hbWUiOiJob29rIiwic2lkZSI6InRvcCJ9LCJoZWFkIjp7Im5hbWUiOiJlcGkifX19XSxbMywxMCwiZXRhXm5fQSIsMV0sWzQsMTEsImV0YV5uX0MiLDEseyJzdHlsZSI6eyJ0YWlsIjp7Im5hbWUiOiJob29rIiwic2lkZSI6InRvcCJ9fX1dXQ==
    #context align(center, diagram({
      node((0, 0), [$dots.c$])
      node((1, 0), [$S^(n-1) (C)$])
      node((2, 0), [$S^(n-1) (R)$])
      node((3, 0), [$S^n (A)$])
      node((4, 0), [$S^n (C)$])
      node((5, 0), [$dots.c$])
      node((0, 1), [$dots.c$])
      node((5, 1), [$dots.c$])
      node((1, 1), [$T^(n-1) (C)$])
      node((2, 1), [$T^(n-1) (R)$])
      node((3, 1), [$T^n (A)$])
      node((4, 1), [$T^n (C)$])
      edge((0, 0), (1, 0), "->")
      edge((1, 0), (2, 0), "->")
      edge((2, 0), (3, 0), "->")
      edge((3, 0), (4, 0), "->")
      edge((4, 0), (5, 0), "->")
      edge((0, 1), (1, 1), "->")
      edge((1, 1), (2, 1), "->")
      edge((2, 1), (3, 1), "->")
      edge((3, 1), (4, 1), "->")
      edge((4, 1), (5, 1), "->")
      edge((1, 0), (1, 1), [$eta^(n-1)_C$], label-side: center, "hook->>")
      edge((2, 0), (2, 1), [$eta^(n-1)_R$], label-side: center, "hook->>")
      edge((3, 0), (3, 1), [$eta^n_A$], label-side: center, "->")
      edge((4, 0), (4, 1), [$eta^n_C$], label-side: center, "hook->")
    }, crossing-fill: thm-box-curr-color()))
    By the inductive hypothesis, $eta^(n-1)_C$ and $eta^(n-1)_R$ are bijective. By assumption, $eta^n_C$ is injective. By the injective four lemma, $eta^n_A$ is injective. 
  
  - For every $A in cal(A)$, write $A = dirlim_lambda A_lambda$ for $A_lambda in cal(A)_0$. We have shown that $eta^n_(A_lambda)$ is injective for all $lambda$. Now: 
    $
      eta^n_A: S^n (A) cong dirlim_lambda S^n (A_lambda) -> T^n (A) cong dirlim_lambda T^n (A_lambda)
    $
    is the directed limit of the $eta^n_lambda$'s, which are injective maps. By (Ab5) of $cal(B)$, $eta^n_A$ is injective. 

  - For every $A in cal(A)_0$, embed it as $A arrow.hook D$ so that $eta^q_D$ is surjective, and form the cokernel $0 -> A -> D -> R -> 0$. Now consider the commutative diagram with exact rows: 
    // https://q.uiver.app/#r=typst&q=WzAsMTIsWzAsMCwiZG90cy5jIl0sWzEsMCwiU14obi0xKSAoUikiXSxbMiwwLCJTXm4gKEEpIl0sWzMsMCwiU15uIChDKSJdLFs0LDAsIlNebiAoUikiXSxbNCwxLCJTXm4gKFIpIl0sWzAsMSwiZG90cy5jIl0sWzEsMSwiVF4obi0xKSAoUikiXSxbMiwxLCJUXm4gKEEpIl0sWzMsMSwiVF5uIChDKSJdLFs1LDAsImRvdHMuYyJdLFs1LDEsImRvdHMuYyJdLFswLDFdLFsxLDJdLFsyLDNdLFszLDRdLFs2LDddLFs3LDhdLFs4LDldLFs5LDVdLFsxLDcsImV0YV4obi0xKV9SIiwxLHsic3R5bGUiOnsidGFpbCI6eyJuYW1lIjoiaG9vayIsInNpZGUiOiJ0b3AifSwiaGVhZCI6eyJuYW1lIjoiZXBpIn19fV0sWzIsOCwiZXRhXm5fQSIsMSx7InN0eWxlIjp7InRhaWwiOnsibmFtZSI6Imhvb2siLCJzaWRlIjoidG9wIn19fV0sWzMsOSwiZXRhXm5fQyIsMSx7InN0eWxlIjp7InRhaWwiOnsibmFtZSI6Imhvb2siLCJzaWRlIjoidG9wIn0sImhlYWQiOnsibmFtZSI6ImVwaSJ9fX1dLFs0LDUsImV0YV5uX1IiLDEseyJzdHlsZSI6eyJ0YWlsIjp7Im5hbWUiOiJob29rIiwic2lkZSI6InRvcCJ9fX1dLFs0LDEwXSxbNSwxMV1d
    #context align(center, diagram({
      node((1, 0), [$dots.c$])
      node((2, 0), [$S^(n-1) (R)$])
      node((3, 0), [$S^n (A)$])
      node((4, 0), [$S^n (D)$])
      node((5, 0), [$S^n (R)$])
      node((5, 1), [$S^n (R)$])
      node((1, 1), [$dots.c$])
      node((2, 1), [$T^(n-1) (R)$])
      node((3, 1), [$T^n (A)$])
      node((4, 1), [$T^n (D)$])
      node((6, 0), [$dots.c$])
      node((6, 1), [$dots.c$])
      edge((1, 0), (2, 0), "->")
      edge((2, 0), (3, 0), "->")
      edge((3, 0), (4, 0), "->")
      edge((4, 0), (5, 0), "->")
      edge((1, 1), (2, 1), "->")
      edge((2, 1), (3, 1), "->")
      edge((3, 1), (4, 1), "->")
      edge((4, 1), (5, 1), "->")
      edge((2, 0), (2, 1), [$eta^(n-1)_R$], label-side: center, "hook->>")
      edge((3, 0), (3, 1), [$eta^n_A$], label-side: center, "hook->")
      edge((4, 0), (4, 1), [$eta^n_D$], label-side: center, "hook->>")
      edge((5, 0), (5, 1), [$eta^n_R$], label-side: center, "hook->")
      edge((5, 0), (6, 0), "->")
      edge((5, 1), (6, 1), "->")
    }, crossing-fill: thm-box-curr-color()))
    As previously shown, all vertical arrows are injective. Furthermore, $eta^(n-1)_R$ is bijective by the inductive hypothesis, and $eta^n_D$ is surjective by assumption. By the surjective four lemma, $eta^n_A$ is surjective. 

  - For every $A in cal(A)$, write $A = dirlim_lambda A_lambda$ for $A_lambda in cal(A)_0$. We have shown that $eta^n_(A_lambda)$ is bijective for all $lambda$. Now: 
    $
      eta^n_A: S^n (A) cong dirlim_lambda S^n (A_lambda) -> T^n (A) cong dirlim_lambda T^n (A_lambda)
    $
    is the directed limit of the $eta^n_lambda$'s, which are bijective maps. By (Ab5) of $cal(B)$, $eta^n_A$ is bijective. 

  We have thus shown $P(n)$. We may conclude the proof by induction.

  If take $cal(A)_0 = cal(A)$, the two directed limit parts in the proof may be dropped. Thus, the assumptions on commuting with directed limits and (Ab5) of $cal(B)$ may be dropped.
]

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
  The same hypothesis holds for all finite $tilde(X)$ over $X$. Thus, we may assume that $tilde(X) = X$, and focus on sheaves over $X$. 

  Now for $h: tilde(X) -> X$ base changing to $h_0: tilde(X)_0 -> X_0$, 
  $
    H^q (X, h_* ul(ZZ\/n)) cong H^q (tilde(X), ul(ZZ\/n))
  $
  and by (Finite) (@pbc-finite), 
  $
    H^q (X_0, (h_* ul(ZZ\/n))|_(X_0)) cong H^q (X_0, h_(0,*) ul(ZZ\/n)) cong H^q (tilde(X)_0, ul(ZZ\/n))
  $
  Under these identifications, we may check that the restriction map $H^q (X, h_* ul(ZZ\/n)) -> H^q (X_0, (h_* ul(ZZ\/n))|_(X_0))$ is identified with the restriction map $H^q (tilde(X), ul(ZZ\/n)) -> H^q (X, ul(ZZ\/n))$. Thus, we may conclude that: 

  - For every finite $h: tilde(X) -> X$, the restriction maps: 
    $
      res_(h_* ul(ZZ\/n))^(q,X): H^q (X, h_* ul(ZZ\/n)) -> H^q (X_0, (h_* ul(ZZ\/n))|_(X_0))
    $
    is bijective for $q = 0$ and surjective for $q >= 1$. 

  We now apply the abstract devissage @abstract-devissage to the restriction map $res^(q,X): H^q (X, -) -> H^q (X_0, (-)|_(X_0))$, defined on torsion sheaves on $X$. 

  - By @limit-formula-for-sheaves, both functors commute with directed limits. Both functors vanishes for $q < 0$. 

  - Every torsion abelian sheaf is the directed limit of its constructible subsheaves by @constructible-sheaves-first-props (6). 

  - Let $cal(F)$ be a constructible sheaf on $X$. Then: 

    - By @finite-morphisms-and-constructible-sheaves (2), there exists $h: tilde(X) -> X$ finite and an embedding $cal(F) arrow.hook h_* ul(ZZ\/n)$. Now $res^(q,X)$ on $h_* ul(ZZ\/n)$ is bijective for $q = 0$ and surjective for $q >= 1$; 

    - Let $cal(F)$ be $n$-torsion, and embed $cal(F) arrow.hook cal(I)$ for an injective sheaf $cal(I)$ of $ZZ\/n$-modules. Then $H^q (X, cal(I)) = 0$ for $q >= 1$ by @etale-zn-sheaves-first-props (3). Thus $res^(q,X)$ is injective on $cal(I)$ for $q >= 1$. 

    This constructs the required embeddings in @abstract-devissage with injective/surjective transformations.

  Thus @abstract-devissage may be applied, and we may conclude that the base change map:
  $
    res_(cal(F))^(q,tilde(X)): H^q (tilde(X), cal(F)) -> H^q (tilde(X)_0, cal(F)|_(tilde(X)_0))
  $
  is bijective for all torsion $cal(F) in cAb(tilde(X)_et)$. 

]
