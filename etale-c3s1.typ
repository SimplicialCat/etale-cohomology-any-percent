#import "void-import.typ": *

Recall that for a scheme $X$, we have $Et_X$, the category of all etale maps ${f: Z -> X}$. We then introduced the notion of an etale #furi[recouvrement][cover]. We also have the category $FEt_X$ consisting of all finite etale maps ${f: Z -> X}$. In this setting, the notion of etale #furi[revêtement][covering] space refers to a morphism in $FEt_X$.

The etale fundamental group aims to solve the following classification problem: 
#question[
  Classify and describe $FEt_X$ in a Galois-theoretic way.
]

The intuition goes as follows. In algebraic topology, given a good#footnote[Don't ask me what good means. Maybe a CW complex.] path-connected topological space $X$, we defined its (topological) fundamental group $pi_1^"top" (X, x)$ as homotopy equivalence classes of $x$-based loops. Such a space has a universal covering space $tilde(X) ->> X$. $pi_1^"top" (X)$ can be defined as the automorphism group of $tilde(X)$ over $X$, and there is an equivalence of categories: 
$
  bold("Cov")(X) &-> GSet(pi_1^"top" (X, x)) \
  (p: X' -> X) &|-> p^(-1) (x)
$
between the covering spaces of $X$ under which the finite covering spaces corresponds to finite $pi_1^"top" (X)$-sets. 

In the same way, for a suitable scheme $X$, we hope to define the etale fundamental group $pi_1^et (X)$ as the automorphism of _something_. There is no universal etale covering space, so we need to get creative. It turns out that the finite etale covering spaces of $X$ form a filtered system. This allows us to define $pi_1^et (X)$ as the projective limit of automorphism groups of various etale covering spaces, a profinite group. 

We would then hope to obtain a classification: 
$
  FEt_X &-> GSet(pi_1^et (X, ol(x)))^"fin,cont" \
  (p: X' -> X) &|-> p^(-1)(ol(x))
$
(whatever $ol(x)$ means). This is an equivalence of categories, between the finite etale coverings of $X$, and finite $pi_1^et (X, ol(x))$-sets with a continuous group action. 

One might imagine what the group $pi_1^et (X, ol(x))$ could possibly look like. The intuition comes from the case where $X = Spec(K)$ is the spectrum of a field. 
#example(name: <pi1et-motivation-eg>)[
  When $X = Spec(K)$ is a field, any object $Z in FEt_X$ is a disjoint union $union.sq.big_i Spec(L_i)$, where $L_i\/K$ is a finite separable extension. From Galois theory, a finite separable extension $L\/K$ corresponds to the open subgroup $Gal(K^sep\/L)$ of the absolute Galois group $Gal(K^sep\/K)$. Thus, 
  $
    FEt_X &-> GSet(Gal(K^sep\/K))^#[fin,cont] \
    union.sq.big_i Spec(L_i) &|-> union.sq.big_i Gal(K^sep\/K)\/Gal(K^sep\/L_i)
  $
  is an equivalence of categories. In other words, we would expect $pi_1^et (Spec(K)) = Gal(K^sep\/K)$, to be the absolute Galois group. 
]
This example suggests that we should establish the theory of the etale fundamental group in a Galois-theoretic way, by establishing suitable generalizations of Galois theory for finite etale coverings. 

In this chapter, we assume that $X$ is a connected noetherian scheme, and all schemes appearing are assumed to be noetherian. The noetherian hypothesis is here because without it, connected components may behave pathologically. 

The theory of etale fundamental groups can still be developed in a non-noetherian context. However we try to keep this material concise and self-contained, so we won't bother. 

#notation(name: <terminology-etale-coverings>)[
  The French word for the #furi[recouvrement][cover] and the #furi[revêtement][covering] looks very different, but unfortunately they look similar in English. Try to distinguish between these notions. In this document, we will use the following notation for disambiguation:
  - An _etale cover_ refers to a jointly surjective family of etale morphisms ${f_i: Z_i -> X}$
  - A _finite etale covering space_ refers to a finite etale morphism $f: Z -> X$.
  However I am not perfect and may forget whether to use 'cover' and 'covering' every now and then. 'Finite etale covering spaces' are 4 words and I won't bother to write all 4 words in most cases. The rule of thumb is that whenever you see 'finite' or 'covering space', I am referring to the second concept. If you see 'etale cover', I am referring to the first. If you see 'etale covering' without the word 'finite' or 'space', you need to use the context to disambiguate, and you should probably contact me. 
]

== Etale covering spaces
/*#date[
  Lecture 4, 2025/10/15
  #align(left)[
    Today, we will introduce: 
    - Etale covering spaces
    - Quotient by finite group
    - Galois theory
    and introduce the etale fundamental group. 

    Warning: Be careful about left and right. 
  ]
]*/


#definition(name: <defn-geometric-points>)[
  A *geometric point* of $X$ is a morphism $ol(x) : Spec(Omega) -> X$ for a separably closed field $Omega$. We say $ol(x)$ *lies above* a usual point $x in X$, if $x$ is the image of $ol(x)$. 

  A *pointed scheme* $(X,ol(x))$ refers to simply a scheme $X$ together with a geometric point $ol(x)$ of $X$. A morphism $f: (X, ol(x)) -> (Y, ol(y))$ of pointed schemes refers to a commutative diagram: 
  // https://q.uiver.app/#r=typst&q=WzAsMyxbMSwwLCJTcGVjKE9tZWdhKSJdLFswLDIsIlgiXSxbMiwyLCJZIl0sWzAsMSwib3ZlcmxpbmUoeCkiXSxbMCwyLCJvdmVybGluZSh5KSIsMl0sWzEsMiwiZiJdXQ==
  #align(center, diagram({
    node((0, -1), [$Spec(Omega)$])
    node((-1, 1), [$X$])
    node((1, 1), [$Y$])
    edge((0, -1), (-1, 1), [$ol(x)$], label-side: right, "->")
    edge((0, -1), (1, 1), [$ol(y)$], label-side: left, "->")
    edge((-1, 1), (1, 1), [$f$], label-side: right, "->")
  }, spacing: 1.5em))
  #example[
    - For $X = Spec(K)$, a geometric point of $X$ is nothing but the choice of an inclusion $K arrow.r.hook Omega$ into a separably closed field. Usually, we take $Omega = K^sep$ or $ol(K)$ to be a separable/algebraic closure. 

    - For a general scheme $X$, a geometric point $ol(x)$ above $x in X$ is also simply an inclusion $k(x) -> Omega$ of the residue field into a separably closed field. We also usually take $Omega = k(x)^sep$ or $ol(k(x))$ to be a separable/algebraic closure. 

    It will turn out that the choice of $Omega$ is not of much importance, and simply picking $Omega = k(x)^sep$ or $ol(k(x))$ will capture all essential information. However, we will not make a precise meaning out of it until much later in the course. 
  ]
]

#definition(name: <defn-fiber-functor>)[
  For a fixed geometric point $ol(x): Spec(Omega) -> X$, we define the *fiber functor*: 
  $
    F_(ol(x)): FEt_X &-> cSet^"fin" \
    (p: Z -> X) &|-> p^(-1)(ol(x))
  $
  sending an etale covering space to the fiber of the geometric point $ol(x)$, a finite set. 
  
  In other words, this is equivalent to the set of pairs $(z, psi)$, where $z in p^(-1)(x)$ is a usual point and $psi: k(z) -> Omega$ is an inclusion compatible with $k(x) -> Omega$. In particular, 
  $
    abs(F_(ol(x)) (Z)) = dim_(k(x)) (cal(O)_(Z_x) (Z_x)) = deg(p)
  $
  is independent from $x$ since $p$ is flat. 
]

#properties(name: <fet-first-props>)[
  0. If we have a diagram: 
  // https://q.uiver.app/#r=typst&q=WzAsMyxbMCwwLCJaIl0sWzIsMCwiWiciXSxbMSwxLCJYIl0sWzAsMiwiZiJdLFsxLDIsImYnIiwyXSxbMCwxLCJnIl1d
    #align(center, diagram({
      node((-1, -1), [$Z$])
      node((1, -1), [$Z'$])
      node((0, 0), [$X$])
      edge((-1, -1), (0, 0), [$f$], label-side: right, "->")
      edge((1, -1), (0, 0), [$f'$], label-side: left, "->")
      edge((-1, -1), (1, -1), [$g$], label-side: left, "->")
    }, spacing: 1.5em))
    for $(f: Z -> X), (f': Z' -> X) in FEt_X$, then $g$ is finite etale. 
    #proof[
      $g$ being etale follows from @etale-first-props. The finiteness of $g$ is not easy to check from the definition. However we see that $g$ is proper here, and $g^(-1)(z') subset f^(-1)(f'(z'))$ is finite and so $g$ is quasi-finite. Thus $g$ is finite by Zariski's main theorem.#footnote[Zariski's main theorem is definitely not necessary here. Finiteness of $g$ can definitely be checked manually here, but I want a short proof aimed at convincing you quickly.]
    ]

  1. Suppose we have pointed schemes $(Z, ol(z)), (Z', ol(z'))$ etale over $(X, ol(x))$. If $Z$ is connected and $Z'$ is separated over $X$ (which of course holds for finite etale coverings), then there is at most one map $g: (Z, ol(z)) -> (Z', ol(z'))$ over $(X, ol(x))$. 
    #proof[
      Such a map $g$ makes the graph $Gamma_g$ fit into the diagram: 
      // https://q.uiver.app/#r=typst&q=WzAsNCxbMCwxLCJaIl0sWzIsMSwiWiB0aW1lc19YIFonIl0sWzIsMiwiWiJdLFswLDAsIlNwZWMoT21lZ2EpIl0sWzAsMSwiR2FtbWFfZyIsMV0sWzEsMiwiXCJwclwiX1oiLDFdLFswLDIsIiIsMSx7InN0eWxlIjp7ImhlYWQiOnsibmFtZSI6ImVwaSJ9fX1dLFszLDAsIm92ZXJsaW5lKHopIiwxXSxbMywxLCIob3ZlcmxpbmUoeiksIG92ZXJsaW5lKHonKSkiLDFdXQ==
      #context align(center, diagram({
        node((0, 0), [$Z$])
        node((2, 0), [$Z times_X Z'$])
        node((2, 1), [$Z$])
        node((0, -1), [$Spec(Omega)$])
        edge((0, 0), (2, 0), [$Gamma_g$], label-side: center, "->")
        edge((2, 0), (2, 1), [$"pr"_Z$], label-side: center, "->")
        edge((0, 0), (2, 1), "=")
        edge((0, -1), (0, 0), [$ol(z)$], label-side: center, "->")
        edge((0, -1), (2, 0), [$(ol(z), ol(z'))$], label-side: center, "->")
      }, crossing-fill: thm-box-curr-color()))
      $Gamma_g$ is the base change of the diagonal $Delta_(Z'\/X): Z' -> Z' times_X Z'$ along $g: Z -> Z'$, hence locally an open immersion since $Z' -> X$ is etale. Since $"pr"_Z compose Gamma_g = id_Z$, $Gamma_g$ is injective, hence it must be an open immersion. It is also a closed immersion since $Z' -> X$ is separated. 
      
      As such, $Gamma_g: Z -> Z times_X Z'$ must be the inclusion of $Z$ as a connected component of $Z times_X Z'$. There is only one connected component of $Z times_X Z'$ containing $(ol(z), ol(z'))$, so $Gamma_g$ is unique if it exists. Then $g = "pr"_(Z') compose Gamma_g$ is unique if it exists. 
    ]

  + Given finite etale coverings $(Z, ol(z))$ and $(Z', ol(z'))$ of $(X, ol(x))$, there exists a connected finite etale covering $(tilde(Z), ol(tilde(z)))$ fitting in the commutative diagram: 
    // https://q.uiver.app/#r=typst&q=WzAsNCxbMSwwLCIodGlsZGUoWiksIG92ZXJsaW5lKHRpbGRlKHopKSkiXSxbMCwxLCIoWiwgb3ZlcmxpbmUoeikpIl0sWzIsMSwiKFonLCBvdmVybGluZSh6JykpIl0sWzEsMiwiKFgsIG92ZXJsaW5lKHgpKSJdLFswLDEsImV4aXN0cyIsMV0sWzAsMiwiZXhpc3RzIiwxXSxbMSwzXSxbMiwzXV0=
    #context align(center, diagram({
      node((0, -1), [$(tilde(Z), ol(tilde(z)))$])
      node((-1, 0), [$(Z, ol(z))$])
      node((1, 0), [$(Z', ol(z'))$])
      node((0, 1), [$(X, ol(x))$])
      edge((0, -1), (-1, 0), [$exists$], label-side: center, "->")
      edge((0, -1), (1, 0), [$exists$], label-side: center, "->")
      edge((-1, 0), (0, 1), "->")
      edge((1, 0), (0, 1), "->")
    }, crossing-fill: thm-box-curr-color(), spacing: 2em))
    This is to be seen as the generalization of the existence of a composite field. 
    #proof[
      Take a connected component of $Z times_X Z'$ containing the image of $(ol(z), ol(z')))$
    ]
  
  + Fix a geometric point $ol(x)$ of $X$. For a morphism $g: Z -> Z'$ in $FEt_X$, if $F_(ol(x)) (g): F_(ol(x)) (Z) -> F_(ol(x)) (Z')$ is a bijection, then $g$ is an isomorphism. 

    #proof[
      Since $g$ is finite etale, $g$ is an isomorphism $<==>$ $deg(g) = 1$, which is equivalent to the cardinality of geometric fibers of $g$ being $1$, i.e. fibers of $F_(ol(x)) (g)$ having cardinality $1$. 
    ]
  
  + If $Z in FEt_X$ is connected, then any $X$-endomorphism $g: Z -> Z$ is an isomorphism. 
    #proof[
      Since $Z$ is connected, by (1), $F_(ol(x)) (g): F_(ol(x)) (Z) -> F_(ol(x)) (Z)$ is injective. There's a deep theorem that a map between two finite sets of the same cardinality is injective $<==>$ surjective $<==>$ bijective. Thus $F_(ol(x)) (g)$ is bijective, and by (3) $g$ is an isomorphism. 
    ]
]

#notation[
  For every $Z in FEt_X$, define the group: 
  $
    Aut(Z\/X) = {g: Z overset(->, tilde) Z "automorphism in" FEt_X}
  $
  Then $Aut(Z\/X)$ has a left action on $Z$. Consider the opposite group $Aut(Z\/X)^opp$, having a right action on $Z$. 
  
  /*Today when we see a finite abstract group $G$ acting on $Z$, we will always consider right actions. */
  #remark[
    Mentally, the reason for considering the opposite group is that: 
    $
      Aut(Spec(K^sep)\/Spec(K))^opp cong Gal(K^sep\/K)
    $
    ($K^sep$ is not _finite_ etale over $K$. However, this relation holds whenever you replace $K^sep$ with a finite Galois extension $L\/K$.) We mentally want the absolute Galois group, since in @pi1et-motivation-eg, we expect $pi_1^et (Spec(K)) = Gal(K^sep\/K)$ to be the absolute Galois group. 
  ]
]
