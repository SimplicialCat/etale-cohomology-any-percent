#import "void-import.typ": *

In this final chapter, we establish Poincare duality. We continue our analog between etale cohomology and singular cohomology. For an orientable $n$-manifold $X$, classical Poincare duality states that there exists a cup product pairing $smile$ and a trace isomorphism $Tr: H^n_c (X, QQ) ->^tilde QQ$, s.t. the following pairing is a perfect pairing: 
$
  H^q_c (X, QQ) times H^(n-q) (X, QQ) ->^smile H^n_c (X, QQ) ->^Tr QQ
$

For etale cohomology, the correct analog of an orientable $d$-manifold is a scheme $X$ smooth over $k$ of relative dimension $d$. The coefficient ring $QQ$ will be replaced by a constant torsion sheaf, say $ZZ\/n$ with $n in k^times$, since etale cohomology in non-torsion coefficients, and in coefficients with torsion not invertible in base field, are very much ill-behaved. 

But even with these seemingly natural modifications done, there is still no trace map $H^(2d)_c (X, ul(ZZ\/n)) -> ZZ\/n$ as in this shape. A hint lies in the cohomology of curves. 

- For a smooth projective curve $X$, Kummer theory gives a canonical isomorphism: #h(1fr)
  $
    H^2 (X, mu_n) cong Pic(X)\/n Pic(X) -->^deg_(tilde) ZZ\/n
  $
  By the projection formula, we have a canonical isomorphism $H^2 (X, ul(ZZ\/n)) cong mu_n^(otimes -1)$. 

  In other words, there exists no canonical isomorphism $H^2 (X, ul(ZZ\/n)) cong ZZ\/n$, as that requires an artificial choice of a primitive $n$-th root of unity in $k$. 

As such, a modification to the shape of the trace morphism is necessary. Instead of a trace morphism $Tr_(X\/k): H^(2d)_c (X, ul(ZZ\/n)) -> ZZ\/n$, the correct shape should be: 
$
  Tr_(X\/k): H^(2d)_c (X, mu_n^(otimes d)) -> ZZ\/n
$
as suggested by the curve case. In fact, the trace morphism has a relative version: Given a smooth morphism $f: X -> Y$ of relative dimension $d$ with nonempty connected geometric fibers, there exists a canonical isomorphism: 
$
  R^(2d) f_! mu_n^(otimes d) -> ul(ZZ\/n)
$
By the projection formula, this really gives a canonical isomorphism: 
$
  R f_! (cal(K) Lotimes_(ZZ\/n) mu_n^(otimes d))[2d] -> cal(K)
$
for each complex $cal(K)$. We will then prove the etale analog of classical Poincare duality, that: 
$
  H^q_c (X, mu_n^(otimes d)) times H^(2d-q) (X, ul(ZZ\/n)) ->^smile H^(2d)_c (X, mu_n^(otimes d)) ->^Tr ZZ\/n
$
is a perfect pairing, whenever $X$ is smooth of relative dimension $d$ over an algebraically closed field $k$. 

However, we will not only prove this statement. In fact, upon abstractly inspecting the desired statements, we will see evidence for a right adjoint $R f^!$ of $R f_!$ whenever $f$ is separated of finite type. We will then see that Poincare duality is implied by the following purity statement: 

- If $f: X -> Y$ is smooth of relative dimension $d$ and $n in cal(O)_Y^times$, then: #h(1fr)
  $
    R f^! ul(ZZ\/n) = mu_n^(otimes d)[2d]
  $

Not only is the functor $R f^!$ useful for Poincare duality, but its introduction allows us to put etale cohomology into a very elegant axiomatic framework, namely Grothendieck's _six functor formalism_. In later sections of this chapter, we will prove a very strong base change result called generic base change by bootstrapping a chain of reductions using Poincare duality, and then use it to devise necessary finiteness results needed to state the six functor formalism. 

== Trace map of a smooth morphism

// 0. A trace morphism on the family of all smooth maps is unique if it exists
// 1. A compatible family of trace morphism exists for smooth morphisms of relative dimension 0/1 with an etale coordinate
// 2. A compatible family of trace morphism exists for smooth morphisms with an etale coordinate
// 3. A compatible family of trace morphism exists

In this section, we intend to define a trace map. 

The trace map can be uniquely characterized axiomatically, by its compatibility with composition and base change, and its explicit description in the case of etale morphisms and curves. 

The axiomatic approach to the trace map in this section is inspired by the treatment in @cite-freitag-kiehl[Section II.1]. 

#notation[
  Suppose that $cal(S)$ is a family of separated smooth morphisms of pure relative dimension between noetherian $ZZ[n^(-1)]$-schemes, closed under composition and (noetherian) base change. 
  
  A family of *trace-like maps* is a family ${S_f = S_(X\/Y)}_((f:X->Y) in cal(S))$, where for any $f: X -> Y$ of relative dimension $d$, $S_(X\/Y)$ is of the shape: 
  $
    S_(X\/Y): R^(2d) f_! mu_(n,X)^(otimes d) -> ul(ZZ\/n)_Y
  $
  Equivalently, since $R f_! mu_(n,X)^(otimes d)$ is concentrated in degrees $[0,2d]$ by Grothendieck vanishing, a map $S_(X\/Y): R^(2d) f_! mu_(n,X)^(otimes d) -> ul(ZZ\/n)_Y$ is equivalent to a map: 
  $
    S_(X\/Y): R f_! mu_(n,X)^(otimes d)[2d] -> ul(ZZ\/n)_Y
  $

  A family of trace-like maps ${S_(X\/Y)}_((f:X->Y) in cal(S))$ is said to be: 

  - *compatible with base change*, if for every morphism $g: Y' -> Y$ with $Y'$ noetherian and a Cartesian diagram: #h(1fr)
    // https://q.uiver.app/#r=typst&q=WzAsNCxbMCwwLCJYJyJdLFsxLDAsIlknIl0sWzAsMSwiWCJdLFsxLDEsIlkiXSxbMiwzLCJmIiwyXSxbMCwxLCJmJyJdLFsxLDMsImciXSxbMCwyLCJnJyIsMl1d
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
    the following diagram of maps commutes: 
    // https://q.uiver.app/#r=typst&q=WzAsNCxbMCwwLCJnXigtMSkgUiBmXyEgbXVfbl4ob3RpbWVzIGQpWzJkXSJdLFsxLDAsInVsKFpaXFwvbikiXSxbMSwxLCJ1bChaWlxcL24pIl0sWzAsMSwiUiBmJ18hIG11X25eKG90aW1lcyBkKVsyZF0iXSxbMCwxLCJnXigtMSkgU18oWFxcL1kpIl0sWzAsMywiQkMiLDJdLFszLDIsIlNfKFgnXFwvWScpIiwyXV0=
    #align(center, diagram({
      node((0, 0), [$g^(-1) R f_! mu_n^(otimes d)[2d]$])
      node((1, 0), [$ul(ZZ\/n)$])
      node((1, 1), [$ul(ZZ\/n)$])
      node((0, 1), [$R f'_! mu_n^(otimes d)[2d]$])
      edge((0, 0), (1, 0), [$g^(-1) S_f$], label-side: left, "->")
      edge((0, 0), (0, 1), [$BC$], label-side: right, "->")
      edge((0, 1), (1, 1), [$S_(f')$], label-side: right, "->")
      edge((1, 0), (1, 1), "=")
    }))

  - *compatible with composition*, if for $f: X -> Y, g: Y -> Z$ in the family $cal(S)$, smooth of relative dimension $d,e$ respectively, the composition: 
    $
      R g_! R f_! mu_n^(otimes (d+e)) [2(d+e)] -->^P R g_! (R f_! mu_n^(otimes d)[2d] Lotimes_(ZZ\/n) mu_n^(otimes e)[2e]) -->^(S_(X\/Y)) R g_! mu_n^(otimes e)[2e] -->^(S_(Y\/Z)) ul(ZZ\/n)
    $
    is exactly $S_(X\/Z)$. (Here $P$ is a projection isomorphism.) 

    As a convenient notation, we denote by the composition above as: 
    $
      S_(Y\/Z) diamond.small S_(X\/Y)
    $
    and so compatibility with composition can be written as $S_(Y\/Z) diamond.small S_(X\/Y) = S_(X\/Z)$. 

    By naturality of the projection map, $diamond.small$ is associative. 
]

We now axiomatically characterize the uniqueness of the trace map. 

#proposition(name: <pd-trace-uniqueness>)[
  Suppose that there exists a family of trace-like maps ${Tr_(X\/Y)}$ on the family of all separated smooth morphisms of pure relative dimension between noetherian $ZZ[n^(-1)]$-schemes s.t: 

  0. ${Tr_(X\/Y)}$ is compatible with base change and composition; 

  + For $f: X -> Y$ etale (i.e. smooth of relative dimension 0), #h(1fr)
    $
      Tr_(X\/Y): f_! ul(ZZ\/n) -> ul(ZZ\/n)
    $
    is the adjunction counit. 

  + For $f: X -> Spec(k)$ a smooth projective curve over $k$ algebraically closed, $Tr_(X\/k)$ is characterized as: 
    $
      Tr_(X\/k): H^2 (X, mu_n) cong Pic(X)\/n Pic(X) ->^deg ZZ\/n 
    $
    where the canonical isomorphism $H^2 (X, mu_n) cong Pic(X)\/n Pic(X)$ is as in @cohom-of-proj-curve (1). 

  Then this family of trace-like maps is unique. 
]
#proof[
  By compatibility with composition, for $k$ algebraically closed and $f: AA^1_k -> Spec(k)$ with compactification $AA^1_k ->^j PP^1_k ->^(ol(f)) Spec(k)$, $Tr_(AA^1_k\/k)$ factors as: 
  $
    H^2_c (AA^1_k, mu_n) -->^(Tr_(AA^1_k\/PP^1_k)) H^2 (PP^1_k, mu_n) -->^(Tr_(PP^1_k\/k)) ZZ\/n
  $
  Both maps are known due to (1) and (2). Thus $Tr_(AA^1_k\/k)$ is uniquely determined. By compatibility with base change, every $Tr_(AA^1_Y\/Y)$ is uniquely determined. Thus, by compatibility with composition, every $Tr_(AA^d_Y\/Y)$ is uniquely determined. 

  Now by @equiv-defns-of-smooth (3), for every smooth morphism $f: X -> Y$ of relative dimension $d$, there exists a commutative diagram: 
  // https://q.uiver.app/#r=typst&q=WzAsNCxbMCwwLCJVIl0sWzEsMCwiQUFeZF9ZIl0sWzAsMSwiWCJdLFsxLDEsIlkiXSxbMCwyLCJnIiwyXSxbMCwxLCJmXzEiXSxbMSwzLCJwIl0sWzIsMywiZiIsMl1d
  #align(center, diagram({
    node((0, 0), [$U$])
    node((1, 0), [$AA^d_Y$])
    node((0, 1), [$X$])
    node((1, 1), [$Y$])
    edge((0, 0), (0, 1), [$g$], label-side: right, "->")
    edge((0, 0), (1, 0), [$f_1$], label-side: left, "->")
    edge((1, 0), (1, 1), [$p$], label-side: left, "->")
    edge((0, 1), (1, 1), [$f$], label-side: right, "->")
  }))
  in which $g$ is an etale cover, $f_1$ is etale, and $p$ is the projection from $AA^d$. We have seen that $Tr_(AA^d_Y\/Y)$ is uniquely determined, and so by (1) and compatibility with composition, $Tr_(U\/Y)$ is uniquely determined. Now $Tr_(U\/X)$ is the counit: 
  $
    g_! ul(ZZ\/n) -> ul(ZZ\/n)
  $
  which is surjective upon checking stalks, since $g$ is surjective etale. By Grothendieck vanishing, $R^(2d) f_!$ is right exact, so $R^(2d) f_! g_! mu_n^(otimes d) -> R^(2d) f_! mu_n^(otimes d)$ is surjective. Now the composition: 
  $
    R^(2d) f_! g_! mu_n^(otimes d) -> R^(2d) f_! mu_n^(otimes d) -->^(Tr_(X\/Y)) ul(ZZ\/n)
  $
  being $Tr_(U\/Y)$, is uniquely determined, where the first map is a uniquely determined surjection. Thus the second map $Tr_(X\/Y)$ is uniquely determined. 
]

This axiomatic characterization of the uniqueness of the trace map hints its construction: It is constructed by glueing the following three constructions using various lemmas governing their compatibility: 

- For a separated etale morphism $f: X -> Y$, the counit $Tr_(X\/Y)^compose: f_! ul(ZZ\/n) -> ul(ZZ\/n)$; 

- For a smooth curve $f: X -> Spec(k)$ with $k$ algebraically closed, the map: #h(1fr)
  $
    Tr_(X\/k)^tilde: H^2_c (X, mu_n) cong Pic(X)\/n Pic(X) ->^deg ZZ\/n 
  $

- For a projection $p: AA^d_Y -> Y$ from affine space, the map: 
  $
    Tr_(AA^d_Y\/Y)^square: R^(2d) p_! mu_n^(otimes d) -> ul(ZZ\/n)
  $
  obtained as the inverse of a canonical isomorphism $ul(ZZ\/n) -> R p_! mu_n^(otimes d)[2d]$. 

Only the third construction is not known, so we construct it first. 

#lemma(name: <pd-trace-affine-constr>)[
  Given any noetherian scheme $Y$ with affine space $p_d: AA^d_Y -> Y$, there exists a canonical isomorphism: 
  $
    Tr_(AA^d_Y\/Y)^square: R p_(d,!) mu_n^(otimes d)[2d] -> ul(ZZ\/n)
  $
  which, as a family of trace-like maps on the family: 
  $
    cal(S)^square = {AA^(d_1+d_2)_Y -> AA^(d_1)_Y #[projection onto first $d_1$ coordinates] : d_(1,2) in NN, Y #[noetherian $ZZ[n^(-1)]$-scheme]}
  $
  is compatible with base change and composition. Furthermore, for any automorphism $sigma: AA^d_Y -> AA^d_Y$ defined by permuting coordinates according to a permutation $sigma in S_d$, there is a commutative diagram: 
  // https://q.uiver.app/#r=typst&q=WzAsNCxbMCwwLCJSIHBfKGQsISkgbXVfbl4ob3RpbWVzIGQpIFsyZF0iXSxbMCwyLCJSIHBfKGQsISkgc2lnbWFfISBtdV9uXihvdGltZXMgZCkgWzJkXSJdLFsyLDAsInVsKFpaXFwvbikiXSxbMiwyLCJSIHBfKGQsISkgbXVfbl4ob3RpbWVzIGQpIFsyZF0iXSxbMCwyLCJUcl5zcXVhcmVfKHBfZCkiXSxbMSwwLCJUcl9zaWdtYV5jb21wb3NlIl0sWzEsMywidGlsZGUiLDJdLFszLDIsIlRyXnNxdWFyZV8ocF9kKSIsMl1d
  #align(center, diagram({
    node((0, 0), [$R p_(d,!) mu_n^(otimes d) [2d]$])
    node((0, 2), [$R p_(d,!) sigma_! mu_n^(otimes d) [2d]$])
    node((2, 0), [$ul(ZZ\/n)$])
    node((2, 2), [$R p_(d,!) mu_n^(otimes d) [2d]$])
    edge((0, 0), (2, 0), [$Tr^square_(p_d)$], label-side: left, "->")
    edge((0, 2), (0, 0), [$Tr_sigma^compose$], label-side: left, "->")
    edge((0, 2), (2, 2), [$tilde$], label-side: right, "->")
    edge((2, 2), (2, 0), [$Tr^square_(p_d)$], label-side: right, "->")
  }))
  where the bottom isomorphism is induced by $p_d compose sigma = p_d$, and the left map $Tr_sigma^compose$ is the counit of $sigma_! tack.l sigma^(-1)$. 
]
#proof[
  We first construct the map $Tr_(AA^1_Y\/Y)^square$. Let $p_1: AA^1_Y -> Y$ with compactification $AA^1_Y ->^j PP^1_Y ->^(ol(p_1)) Y$. Then by the Kummer sequence, there is a canonical map: 
  $
    Pic(PP^1_Y) = H^1 (PP^1_Y, GG_m) -> H^2 (PP^1_Y, mu_n)
  $
  Let $c_(1,Y) in H^2 (PP^1_Y, mu_n)$ be the image of the canonical bundle $cal(O)_(PP^1_Y) (1)$ under this map. Recall that $R^2 ol(p_1)_* mu_n = (U |-> H^2 (PP^1_U, mu_n))^\#$, so the class $c_1 in H^2 (PP^1_Y, mu_n)$ corresponds to a global section $c_Y in Gamma(PP^1_Y, R^2 ol(p_1)_* mu_n)$. This defines a map: 
  $
    alpha_Y: ul(ZZ\/n)_Y -> R^2 ol(p_1)_* mu_n
  $

  We claim that $alpha_Y$ is compatible with base change. 
  #proof_[Proof of claim][
    Indeed, for a Cartesian diagram: #h(1fr)
    // https://q.uiver.app/#r=typst&q=WzAsNixbMCwwLCJBQV4xXyhZJykiXSxbMSwwLCJQUF4xXyhZJykiXSxbMiwwLCJZJyJdLFswLDEsIkFBXjFfWSJdLFsxLDEsIlBQXjFfWSJdLFsyLDEsIlkiXSxbMyw0LCJqIiwyXSxbNCw1LCJvbChwXzEpIiwyXSxbMiw1LCJnIl0sWzAsMywiZyciLDJdLFsxLDQsIm9sKGcpJyJdLFsxLDIsIm9sKHAnXzEpIl0sWzAsMSwiaiciXV0=
    #align(center, diagram({
      node((0, 0), [$AA^1_(Y')$])
      node((1, 0), [$PP^1_(Y')$])
      node((2, 0), [$Y'$])
      node((0, 1), [$AA^1_Y$])
      node((1, 1), [$PP^1_Y$])
      node((2, 1), [$Y$])
      edge((0, 1), (1, 1), [$j$], label-side: right, "->")
      edge((1, 1), (2, 1), [$ol(p_1)$], label-side: right, "->")
      edge((2, 0), (2, 1), [$g$], label-side: left, "->")
      edge((0, 0), (0, 1), [$g'$], label-side: right, "->")
      edge((1, 0), (1, 1), [$ol(g)'$], label-side: left, "->")
      edge((1, 0), (2, 0), [$ol(p'_1)$], label-side: left, "->")
      edge((0, 0), (1, 0), [$j'$], label-side: left, "->")
    }))
    we want to show the commutativity of: 
    // https://q.uiver.app/#r=typst&q=WzAsOSxbMCwwLCJaWlxcL24iXSxbMSwwLCJQaWMoUFBeMV9ZKSJdLFswLDIsIlpaXFwvbiJdLFsxLDIsIlBpYyhQUF4xXyhZJykpIl0sWzIsMCwiSF4yIChQUF4xX1ksIG11X24pIl0sWzIsMiwiSF4yIChQUF4xXyhZJyksIG11X24pIl0sWzMsMCwiR2FtbWEoWSwgUl4yIG9sKHBfMSlfKiBtdV9uKSJdLFszLDIsIkdhbW1hKFknLCBSXjIgb2wocCdfMSlfKiBtdV9uKSJdLFszLDEsIkdhbW1hKFksIGdeKC0xKSBSXjIgb2wocF8xKV8qIG11X24pIl0sWzAsMSwiY2FsKE8pKDEpIl0sWzIsMywiY2FsKE8pKDEpIl0sWzEsNF0sWzMsNV0sWzQsNl0sWzUsN10sWzAsMiwiIiwxLHsic3R5bGUiOnsiYm9keSI6eyJuYW1lIjoiZG91YmxlIGJhcnJlZCJ9fX1dLFsxLDMsIm9sKGcpJ14oLTEpIl0sWzQsNSwicmVzIl0sWzYsOCwicmVzIl0sWzgsNywiQkMiLDFdXQ==
    #align(center, diagram({
      node((0, 0), [$ZZ\/n$])
      node((1, 0), [$Pic(PP^1_Y)$])
      node((0, 2), [$ZZ\/n$])
      node((1, 2), [$Pic(PP^1_(Y'))$])
      node((2, 0), [$H^2 (PP^1_Y, mu_n)$])
      node((2, 2), [$H^2 (PP^1_(Y'), mu_n)$])
      node((3, 0), [$Gamma(Y, R^2 ol(p_1)_* mu_n)$])
      node((3, 2), [$Gamma(Y', R^2 ol(p'_1)_* mu_n)$])
      node((3, 1), [$Gamma(Y, g^(-1) R^2 ol(p_1)_* mu_n)$])
      edge((0, 0), (1, 0), [$cal(O)(1)$], label-side: left, "->")
      edge((0, 2), (1, 2), [$cal(O)(1)$], label-side: left, "->")
      edge((1, 0), (2, 0), "->")
      edge((1, 2), (2, 2), "->")
      edge((2, 0), (3, 0), "->")
      edge((2, 2), (3, 2), "->")
      edge((0, 0), (0, 2), "=")
      edge((1, 0), (1, 2), [$ol(g)'^*$], label-side: left, "->")
      edge((2, 0), (2, 2), [$res$], label-side: left, "->")
      edge((3, 0), (3, 1), [$res$], label-side: left, "->")
      edge((3, 1), (3, 2), [$BC$], label-side: left, "->")
    }))
    
    Recall that by unfolding the definitions: 

    - For $f: X -> Y$, the map $f^*: Pic(Y) -> Pic(X)$ is identified as the map: #h(1fr)
      $
        H^1 (Y, GG_(m,X)) ->^res H^1 (X, f^(-1) GG_(m,Y)) -> H^1 (X, GG_(m,X))
      $
      where the map $f^(-1) GG_(m,Y) -> GG_(m,X)$ is induced by adjunction from $GG_(m,Y) -> GG_(m,X)$. Furthermore, there is a commutative diagram: 
      // https://q.uiver.app/#r=typst&q=WzAsMTAsWzAsMCwiMCJdLFsxLDAsImZeKC0xKSBtdV8obixZKSJdLFsyLDAsImZeKC0xKSBHR18obSxZKSJdLFszLDAsImZeKC0xKSBHR18obSxZKSJdLFs0LDAsIjAiXSxbMCwxLCIwIl0sWzEsMSwibXVfKG4sWCkiXSxbMiwxLCJHR18obSxYKSJdLFszLDEsIkdHXyhtLFgpIl0sWzQsMSwiMCJdLFswLDFdLFsxLDJdLFsyLDMsIigtKV5uIl0sWzMsNF0sWzUsNl0sWzYsN10sWzcsOCwiKC0pXm4iLDJdLFs4LDldLFsxLDYsInRpbGRlIiwxXSxbMiw3XSxbMyw4XV0=
      #context align(center, diagram({
        node((0, 0), [$0$])
        node((1, 0), [$f^(-1) mu_(n,Y)$])
        node((2, 0), [$f^(-1) GG_(m,Y)$])
        node((3, 0), [$f^(-1) GG_(m,Y)$])
        node((4, 0), [$0$])
        node((0, 1), [$0$])
        node((1, 1), [$mu_(n,X)$])
        node((2, 1), [$GG_(m,X)$])
        node((3, 1), [$GG_(m,X)$])
        node((4, 1), [$0$])
        edge((0, 0), (1, 0), "->")
        edge((1, 0), (2, 0), "->")
        edge((2, 0), (3, 0), [$(-)^n$], label-side: left, "->")
        edge((3, 0), (4, 0), "->")
        edge((0, 1), (1, 1), "->")
        edge((1, 1), (2, 1), "->")
        edge((2, 1), (3, 1), [$(-)^n$], label-side: right, "->")
        edge((3, 1), (4, 1), "->")
        edge((1, 0), (1, 1), [$tilde$], label-side: center, "->")
        edge((2, 0), (2, 1), "->")
        edge((3, 0), (3, 1), "->")
      }, crossing-fill: thm-box-curr-color()))

      (We have seen this at the end of this proof of proper base change.)
    
    Thus, the diagram that we want to prove to be commutative factors as: 
    // https://q.uiver.app/#r=typst&q=WzAsMTEsWzAsMCwiWlpcXC9uIl0sWzEsMCwiSF4xKFBQXjFfWSwgR0dfbSkiXSxbMCwyLCJaWlxcL24iXSxbMSwyLCJIXjEoUFBeMV8oWScpLCBHR19tKSJdLFsyLDAsIkheMiAoUFBeMV9ZLCBtdV9uKSJdLFsyLDIsIkheMiAoUFBeMV8oWScpLCBtdV9uKSJdLFszLDAsIkdhbW1hKFksIFJeMiBvbChwXzEpXyogbXVfbikiXSxbMywyLCJHYW1tYShZJywgUl4yIG9sKHAnXzEpXyogbXVfbikiXSxbMywxLCJHYW1tYShZLCBnXigtMSkgUl4yIG9sKHBfMSlfKiBtdV9uKSJdLFsxLDEsIkheMShQUF4xXyhZJyksIG9sKGcpJ14oLTEpIEdHX20pIl0sWzIsMSwiSF4yIChQUF4xXyhZJyksIG11X24pIl0sWzAsMSwiY2FsKE8pKDEpIl0sWzIsMywiY2FsKE8pKDEpIl0sWzEsNF0sWzMsNV0sWzQsNl0sWzUsN10sWzYsOCwicmVzIl0sWzgsNywiQkMiLDFdLFsxLDksInJlcyJdLFs5LDNdLFswLDIsIiIsMSx7InN0eWxlIjp7ImJvZHkiOnsibmFtZSI6ImRvdWJsZSBiYXJyZWQifX19XSxbNCwxMCwicmVzIl0sWzEwLDUsIiIsMCx7InN0eWxlIjp7ImJvZHkiOnsibmFtZSI6ImRvdWJsZSBiYXJyZWQifX19XSxbOSwxMF1d
    #align(center, diagram({
      node((0, 0), [$ZZ\/n$])
      node((1, 0), [$H^1(PP^1_Y, GG_m)$])
      node((0, 2), [$ZZ\/n$])
      node((1, 2), [$H^1(PP^1_(Y'), GG_m)$])
      node((2, 0), [$H^2 (PP^1_Y, mu_n)$])
      node((2, 2), [$H^2 (PP^1_(Y'), mu_n)$])
      node((3, 0), [$Gamma(Y, R^2 ol(p_1)_* mu_n)$])
      node((3, 2), [$Gamma(Y', R^2 ol(p'_1)_* mu_n)$])
      node((3, 1), [$Gamma(Y, g^(-1) R^2 ol(p_1)_* mu_n)$])
      node((1, 1), [$H^1(PP^1_(Y'), ol(g)'^(-1) GG_m)$])
      node((2, 1), [$H^2 (PP^1_(Y'),ol(g)'^(-1) mu_n)$])
      edge((0, 0), (1, 0), [$cal(O)(1)$], label-side: left, "->")
      edge((0, 2), (1, 2), [$cal(O)(1)$], label-side: left, "->")
      edge((1, 0), (2, 0), "->")
      edge((1, 2), (2, 2), "->")
      edge((2, 0), (3, 0), "->")
      edge((2, 2), (3, 2), "->")
      edge((3, 0), (3, 1), [$res$], label-side: left, "->")
      edge((3, 1), (3, 2), [$BC$], label-side: left, "->")
      edge((1, 0), (1, 1), [$res$], label-side: left, "->")
      edge((1, 1), (1, 2), "->")
      edge((0, 0), (0, 2), "=")
      edge((2, 0), (2, 1), [$res$], label-side: left, "->")
      edge((2, 1), (2, 2), "->", $tilde$)
      edge((1, 1), (2, 1), "->")
    }))

    The left square commutes since $ol(g)'^* cal(O)(1) cong cal(O)(1)$. The middle two squares commute by naturality. Thus it remains to show that the right square commutes. Factoring out a naturality square for $ol(g)'^(-1) mu_n cong mu_n$, it reduces to the following lemma: 

    #lemma[
      Given a Cartesian diagram: 
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
      for every $cal(F) in cAb(X_et)$, we have a commutative diagram of maps: 
      // https://q.uiver.app/#r=typst&q=WzAsNSxbMCwwLCJIXnEgKFgsIGNhbChGKSkiXSxbMSwwLCJHYW1tYShZLCBSXnEgZl8qIGNhbChGKSkiXSxbMCwyLCJIXnEgKFgnLCBnJ14oLTEpIGNhbChGKSkiXSxbMSwyLCJHYW1tYShZJywgUl5xIGYnXyogZydeKC0xKSBjYWwoRikpIl0sWzEsMSwiR2FtbWEoWSwgZ14oLTEpIFJecSBmXyogY2FsKEYpKSJdLFswLDFdLFsyLDNdLFswLDIsInJlcyIsMl0sWzEsNCwicmVzIl0sWzQsMywiQkMiXV0=
      #align(center, diagram({
        node((0, 0), [$H^q (X, cal(F))$])
        node((1, 0), [$Gamma(Y, R^q f_* cal(F))$])
        node((0, 2), [$H^q (X', g'^(-1) cal(F))$])
        node((1, 2), [$Gamma(Y', R^q f'_* g'^(-1) cal(F))$])
        node((1, 1), [$Gamma(Y, g^(-1) R^q f_* cal(F))$])
        edge((0, 0), (1, 0), "->")
        edge((0, 2), (1, 2), "->")
        edge((0, 0), (0, 2), [$res$], label-side: right, "->")
        edge((1, 0), (1, 1), [$res$], label-side: left, "->")
        edge((1, 1), (1, 2), [$BC$], label-side: left, "->")
      }))
    ]
    #proof[
      Both paths are natural transformations $H^q (X, -) -> Gamma(Y', R^q f'_* g'^(-1) (-))$ as $delta$-functors. Note that ${H^q (X, -)}$ is a universal $delta$-functor. Thus, to prove for general $q$, it suffices to prove assuming $q = 0$. Now everything in this diagram are global sections. Pushing every sheaf to $Y$, it suffices to show the commutativity of: 
      // https://q.uiver.app/#r=typst&q=WzAsNSxbMCwwLCJmXyogY2FsKEYpIl0sWzEsMCwiZl8qIGNhbChGKSJdLFswLDIsImZfKiBnJ18qIGcnXigtMSkiXSxbMSwyLCJnXyogZidfKiBnJ14oLTEpIl0sWzEsMSwiZ18qIGdeKC0xKSBmXyogY2FsKEYpIl0sWzAsMSwiIiwwLHsic3R5bGUiOnsiYm9keSI6eyJuYW1lIjoiZG91YmxlIGJhcnJlZCJ9fX1dLFsyLDMsInRpbGRlIiwyXSxbMCwyLCIjW3VuaXRdIiwyXSxbMSw0LCIjW3VuaXRdIl0sWzQsMywiQkMiXV0=
      #align(center, diagram({
        node((0, 0), [$f_* cal(F)$])
        node((1, 0), [$f_* cal(F)$])
        node((0, 2), [$f_* g'_* g'^(-1)$])
        node((1, 2), [$g_* f'_* g'^(-1)$])
        node((1, 1), [$g_* g^(-1) f_* cal(F)$])
        edge((0, 0), (1, 0), "=")
        edge((0, 2), (1, 2), [$tilde$], label-side: right, "->")
        edge((0, 0), (0, 2), [$#[unit]$], label-side: right, "->")
        edge((1, 0), (1, 1), [$#[unit]$], label-side: left, "->")
        edge((1, 1), (1, 2), [$BC$], label-side: left, "->")
      }))
      This is formal. 
    ]
    We have thus concluded proving that $alpha_Y: ul(ZZ\/n)_Y -> R^2 ol(p_1)_* mu_n$ is compatible with base change. 
  ]

  Let $Tr_(AA^1_Y\/Y)^square$ be the map: 
  $
    Tr_(AA^1_Y\/Y)^square: R^2 p_(1,!) mu_n -> R^2 ol(p_1)_* mu_n ->^(alpha_Y^(-1)) ul(ZZ\/n)
  $
  where the first map is induced from the extension by zero triangle (and an isomorphism as its complement is $Y ->^id Y$, whose pushforward has no $R^1$ or $R^2$). Since both the extension by zero triangle and $alpha_Y$ are compatible with base change, so is $Tr_(AA^1_Y\/Y)^square$. 

  By our computation in @cohom-with-proper-supp-of-Ad-and-Pd and proper base change, $R p_(1,!) mu_n$ is concentrated in degree 2. Thus, we have constructed an isomorphism: 
  $
    Tr_(AA^1_Y\/Y)^square: R p_(1,!) mu_n [2] -> ul(ZZ\/n)
  $
  compatible with base change. 

  We now define $Tr_(AA^d_Y\/Y)^square$. Let $q_i: AA^d_Y -> AA^1_Y, 1<=i<=d$ be projections onto various coordinates. Then we take $Tr_(AA^d_Y\/Y)^square$ to be the isomorphism defined as: 
  $
    R p_(d,!) mu_n^(otimes d)[2d] &cong R p_(d_!) (q_1^(-1) mu_n [2] Lotimes_(ZZ\/n) dots.c Lotimes_(ZZ\/n) q_d^(-1) mu_n [2]) \
    &cong underbrace(R p_(1,!) mu_n [2] Lotimes_(ZZ\/n) dots.c Lotimes_(ZZ\/n) R p_(1,!) mu_n [2], #[$d$ copies]) #[by Kunneth formula] \
    &cong ul(ZZ\/n) Lotimes_(ZZ\/n) dots.c Lotimes_(ZZ\/n) ul(ZZ\/n) #[by $d$ copies of $Tr_(AA^1_Y\/Y)^square$] \
    &cong ul(ZZ\/n)
  $
  Now: 

  - The Kunneth map is symmetric. Thus, $Tr_(AA^d_Y\/Y)^square$ is invariant under permutation of the $d$ coordinates of $AA^d_Y$. 

  - The Kunneth map is compatible with base change, and so is $Tr_(AA^1_Y\/Y)^square$. Thus, $Tr_(AA^d_Y\/Y)^square$ is compatible with base change. 

  - By inspecting the definition of the Kunneth map, we see that: 
    $
      Tr_(AA^d_Y\/Y)^square = Tr_(AA^1_Y\/Y)^square diamond.small Tr_(AA^2_Y\/AA^1_Y)^square diamond.small dots.c diamond.small Tr_(AA^d_Y\/AA^(d-1)_Y)^square
    $
    so $Tr_(AA^d_Y\/Y)^square$ is immediately compatible with composition. 

  We have thus proved all claimed properties. 
]

#notation[
  Denote the three ingredients of the trace map as follows: 

  - For a separated etale morphism $f: X -> Y$, the counit: 
    $
      Tr_(X\/Y)^compose: f_! ul(ZZ\/n) -> ul(ZZ\/n)
    $ 

  - For a smooth curve $f: X -> Spec(k)$ with $k$ algebraically closed, the map: #h(1fr)
    $
      Tr_(X\/k)^tilde: H^2_c (X, mu_n) ->^tilde H^2 (ol(X), mu_n) cong Pic(X)\/n Pic(X) ->^deg_tilde ZZ\/n 
    $
    where: 

    - $ol(X)$ is the completion of $X$, and is a projective smooth curve over $k$; 

    - The first map is induced by the extension by zero triangle, and is an isomorphism since $ol(X) - X$ is a finite set of closed points over $k$, and has no $H^1_c, H^2_c$; 

    - The isomorphism $H^2 (ol(X), mu_n) cong Pic(X)\/n Pic(X) ->^deg_tilde$ is as in @cohom-of-proj-curve. 

  - For a projection $p: AA^d_Y -> Y$ from affine space, the map: 
    $
      Tr_(AA^d_Y\/Y)^square: R^(2d) p_! mu_n^(otimes d) -> ul(ZZ\/n)
    $
    as defined in the previous lemma. 

  $Tr^compose_(X\/Y)$ is compatible with base change and composition formally, and $Tr^square_(AA^d_Y\/Y)$ is compatible with base change and composition as in the previous lemma. 
]

We now start to glue these constructions by proving compatibility lemmas. 

#lemma(name: <pd-trace-etale-curve-compat>)[
  Let $f: U -> X$ be an etale morphism between smooth curves over an algebraically closed field $k$ with $n in k^times$. Then: 
  $
    Tr_(U\/k)^tilde = Tr_(X\/k)^tilde diamond.small Tr^compose_(U\/X)
  $
]
#proof[
  Let $X -> ol(X)$ be the completion of $X$, so that $ol(X)$ is a smooth projective curve over $k$. Now by definition: 
  $
    Tr_(X\/k)^tilde diamond.small Tr^compose_(U\/X) = Tr_(ol(X)\/k)^tilde diamond.small Tr_(X\/ol(X))^compose diamond.small Tr^compose_(U\/X) = Tr_(ol(X)\/k)^tilde diamond.small Tr_(U\/ol(X))^compose
  $
  Thus, it suffices to prove the lemma in the case that $X$ is a smooth projective curve. Let $ol(U)$ be the completion of $U$. Then $f: U -> X$ extends to a finite map $ol(f): ol(U) -> X$ between curves. Let $j: U -> ol(U)$ be the inclusion. 
  
  Then we need to show the commutativity of: 
  // https://q.uiver.app/#r=typst&q=WzAsOCxbMCwwLCJIXjJfYyAoVSwgbXVfbikiXSxbMCwxLCJIXjJfYyAoVSwgbXVfbikiXSxbMSwwLCJIXjIgKG9sKFUpLCBtdV9uKSJdLFsyLDAsIlBpYyhvbChVKSlcXC9uIFBpYyhvbChVKSkiXSxbMywwLCJaWlxcL24iXSxbMywxLCJaWlxcL24iXSxbMSwxLCJIXjIgKFgsIG11X24pIl0sWzIsMSwiUGljKFgpXFwvbiBQaWMoWCkiXSxbMCwxLCIiLDAseyJzdHlsZSI6eyJib2R5Ijp7Im5hbWUiOiJkb3VibGUgYmFycmVkIn19fV0sWzQsNSwiIiwwLHsic3R5bGUiOnsiYm9keSI6eyJuYW1lIjoiZG91YmxlIGJhcnJlZCJ9fX1dLFswLDIsIlRyXyhVXFwvb2woVSkpXmNvbXBvc2UiXSxbMiwzLCJ0aWxkZSJdLFszLDQsImRlZyJdLFsxLDYsIlRyXyhVXFwvWCleY29tcG9zZSIsMl0sWzYsNywidGlsZGUiLDJdLFs3LDUsImRlZyIsMl1d
  #align(center, diagram({
    node((0, 0), [$H^2_c (U, mu_n)$])
    node((0, 1), [$H^2_c (U, mu_n)$])
    node((1, 0), [$H^2 (ol(U), mu_n)$])
    node((2, 0), [$Pic(ol(U))\/n Pic(ol(U))$])
    node((3, 0), [$ZZ\/n$])
    node((3, 1), [$ZZ\/n$])
    node((1, 1), [$H^2 (X, mu_n)$])
    node((2, 1), [$Pic(X)\/n Pic(X)$])
    edge((0, 0), (0, 1), "=")
    edge((3, 0), (3, 1), "=")
    edge((0, 0), (1, 0), [$Tr_(U\/ol(U))^compose$], label-side: left, "->")
    edge((1, 0), (2, 0), [$tilde$], label-side: left, "->")
    edge((2, 0), (3, 0), [$deg$], label-side: left, "->")
    edge((0, 1), (1, 1), [$Tr_(U\/X)^compose$], label-side: right, "->")
    edge((1, 1), (2, 1), [$tilde$], label-side: right, "->")
    edge((2, 1), (3, 1), [$deg$], label-side: right, "->")
  }))

  For this some preparation is needed. 

  #lemma[
    Let $f: X -> Y$ be a finite morphism between smooth projective curves over an algebraically closed field $k$, which is automatically flat of degree $r$. Then: 

    + $f_*: Div(X) -> Div(Y), sum_x n_x x |-> sum_x n_x f(x)$ preserves principal divisors, and induces a homomorphism: #h(1fr)
      $
        Nm_f: Pic(X) -> Pic(Y)
      $

    + For any $cal(L) in Pic(X)$, $f_* cal(L)$ is locally free of rank $r$. $Nm_f$ can be explicitly described as: 
      $
        Nm_f ([cal(L)]) = [det(f_* cal(L)) otimes det(f_* cal(O)_X)^(otimes -1)] 
      $

    + There is a morphism $Nm_f: f_* GG_(m,X) -> GG_(m,Y)$, which induces $Nm_f: Pic(X) -> Pic(Y)$ on $H^1$. 
  ]
  #proof[
    ($f: X -> Y$ is automatically flat, since for closed points $x in X, y = f(x)$, each $cal(O)_(Y,y) -> cal(O)_(X,x)$ is a morphism of DVRs, and is injective since $f$ is dominant. Thus each $cal(O)_(X,x)$ is a finite torsion-free $cal(O)_(Y,y)$-module, hence free and in particular flat.)

    (1) Suppose that $D = (s) in Div(X)$ is a principal divisor. That is, $0 != s in K(X)$ is a rational function so that $D = sum_(x in abs(X)) v_x (s) x in Div(X)$, where each $v_x$ is the valuation $K(X)^times -> ZZ$ at $x$. Take $0 != Nm_(K(X)\/K(Y)) (s)$. Then for $y in abs(Y)$, we claim that: 
    $
      v_y (Nm_(K(X)\/K(Y)) (s)) = sum_(x in f^(-1)(y)) v_x (s)
    $

    - Indeed, let $B_y$ be the integral closure of $cal(O)_(Y,y)$ in $K(X)$. Then $B_y$ is a Dedekind domain finite free over $cal(O)_(Y,y)$ with rank $r$, and has its maximal ideals corresponding to $x in f^(-1)(y)$ with local rings $cal(O)_(X,x)$. 
    
      Now for $s in B_y$, $Nm_(K(X)\/K(Y)) (s) = det_(cal(O)_(Y,y)) (times s: B_y -> B_y)$ where $B_y$ is a finite free $cal(O)_(Y,y)$-module. By taking the Smith normal form, we see that: 
      $
        v_y (Nm_(K(X)\/K(Y)) (s)) = length_(cal(O)_(Y,y)) (B_y\/s B_y) 
      $

      - For any torsion $B_y$-module $M$, there exists a length decomposition: #h(1fr)
        $
          length_(cal(O)_(Y,y)) (M) = sum_(x in f^(-1)(y)) length_(cal(O)_(X,x)) (M_x)
        $
        Since $M$ is of finite length over $cal(O)_(Y,y)$, it is of finite length over $B_y$, and so we may take replace $M$ by its $B_y$-Jordan-Holder factors. These factors are necessarily $B_y\/frak(m)_x B_y$ for some $x in f^(-1) (y)$. For them, it suffices to prove: 
        $
          length_(cal(O)_(Y,y)) (B_y\/frak(m)_x B_y) = 1
        $ 
        Now: 
        $
          length_(cal(O)_(Y,y)) (B_y\/frak(m)_x B_y) = dim_(k(y)) (B_y\/frak(m)_x B_y) = dim_(k(y)) (k(x)) = 1
        $
        since $k(x) = k(y) = 1$, and we are done. 
      
      Hence, from the length decomposition, 
      $
        v_y (Nm_(K(X)\/K(Y))(s)) &= length_(cal(O)_(Y,y)) (B_y\/s B_y) = sum_(x in f^(-1)(y)) length_(cal(O)_(X,x)) (cal(O)_(X,x)\/s cal(O)_(X,x)) \
        &= sum_(x in f^(-1)(y)) v_x (s)
      $
      Thus, 
      $
        f_* D = sum_(y in abs(Y)) (sum_(x in f^(-1)(y)) v_x (s)) y = sum_(y in abs(Y)) v_y (Nm_(K(X)\/K(Y)) (s)) y = (Nm_(K(X)\/K(Y))(s))
      $
      is a principal divisor. 

    (2) Firstly, note that for every $cal(L) in Pic(X)$, $f_* cal(L)$ is locally free of rank $r$. Indeed, each $cal(O)_(Y,y) -> cal(O)_(X,x)$ is injective, so $f_* cal(L)$ is torsion-free. Since $f$ is finite, $f_* cal(L)$ is coherent. Now the stalks of $f_* cal(L)$ are finite torsion-free modules over local rings of $Y$, which are fields or DVRs. They are thus free. Thus $f_* cal(L)$ is locally free. Finally, the generic stalk of $f_* cal(L)$ is $K(X)$, which has dimension $r = [K(X):K(Y)]$ over $K(Y)$. Thus $f_* cal(L)$ is locally free of dimension $r$. 
    
    By @cite-hartshorne-ag[Exercise II.6.11(b)], we have the following fact:

    - On a smooth curve $X$ over an algebraically closed field $k$, given a short exact sequence: #h(1fr)
      $
        0 -> cal(E) -> cal(E)' -> cal(T) -> 0
      $
      where $cal(E), cal(E)'$ are locally free of the same rank and $cal(T)$ is torsion, 
      $
        det(cal(E)') cong det(cal(E)) otimes cal(L)(sum_(x in abs(X)) length_(cal(O)_(X,x)) (cal(T)_x) x)
      $
    
    Now for an effective divisor $D in Div(X)$, consider the short exact sequence
    $
      0 -> cal(L)_X (-D) -> cal(O)_X -> cal(O)_D -> 0
    $
    Since $f$ is finite, $f_*$ is exact, and so we have a short exact sequence: 
    $
      0 -> f_* cal(L)_X (-D) -> f_* cal(O)_X -> f_* cal(O)_D -> 0
    $
    It can be directly checked that $f_* cal(O)_D = cal(O)_(f_* D)$, as: 
    $
      length_(cal(O)_(Y,y)) ((f_* cal(O)_D)_y) = sum_(x in f^(-1) (y)) length_(cal(O)_(X,x)) (cal(O)_(D,x))
    $
    by the length formula in (1). Thus by the fact listed at the beginning of this proof, 
    $
      det(f_* cal(O)_X) cong det(f_* cal(L)_X (-D)) otimes cal(L)_Y (f_* D)
    $

    Now for any divisor $E in Div(X)$, any effective divisor $D$, applying the same argument to the sequence: 
    $
      0 -> f_* cal(L)_X (E - D) -> f_* cal(L)_X (E) -> f_* cal(O)_D -> 0
    $
    we see that: 
    $
      det(f_* cal(L)_X (E)) cong det(f_* cal(L)_X (E - D)) otimes cal(L)_Y (f_* D)
    $
    Hence, for any divisor $D in Div(X)$, write $D = D_+ - D_-$ for $D_(plus.minus)$ effective, and so: 
    $
      det(f_* cal(L)_X (D)) &cong det(f_* cal(L)_X (-D_-)) otimes cal(L)_Y (f_* D_+) \
      &cong det(f_* cal(O)_X) otimes cal(L)_Y (f_* D_-)^(otimes -1) cal(L)_Y (f_* D_+) \
      &cong det(f_* cal(O)_X) otimes cal(L)_Y (f_* D)
    $
    Thus, 
    $
      cal(L)_Y (f_* D) = det(f_* cal(L)_X (D)) otimes det(f_* cal(O)_X)^(otimes -1)
    $
    and we are done. 

    (3) We first define a map on Zariski sheaves: 
    $
      Nm_f: f_* cal(O)_X^times -> cal(O)_Y^times
    $
    Note that $f_* cal(O)_X$ is a locally free sheaf of $cal(O)_Y$-modules. Thus, taking norms locally, there is a map: 
    $
      Nm_f: f_* cal(O)_X -> cal(O)_Y
    $
    It sends units to units, and so induces a map $Nm_f: f_* cal(O)_X^times -> cal(O)_Y^times$ of Zariski sheaves. 

    Next, we extend $Nm_f$ to a map $f_* GG_(m,X) -> GG_(m,Y)$ of etale sheaves. Any etale $U in Et_Y$ is regular by @etale-local-properties (2), hence a disjoint union of smooth curves over $k$. Thus, to construct $Nm_f: f_* GG_(m,X) -> GG_(m,Y)$, it suffices to construct it on sections on $U$. 
    
    Form the base change $f_U: X_U -> U$ of $f$ along $U -> Y$, so $f_U$ is finite flat of rank $r$. By the same argument as in the beginning of (2), $f_(U,*) cal(O)_(X_U)$ is locally free of rank $r$. Thus, we may define a map: 
    $
      Nm_(f_U): f_(U,*) cal(O)_(X_U)^times -> cal(O)_U^times
    $
    and its global sections give $Nm_f: f_* GG_(m,X) (U) -> GG_(m,Y) (U)$. To show that it is compatible with restriction, for $V -> U$ an etale morphism between smooth curves $V, U in Et_Y$, we need to show the commutativity of the diagram: 
    // https://q.uiver.app/#r=typst&q=WzAsNCxbMCwwLCJjYWwoTylfKFhfVikgKFhfVikiXSxbMSwwLCJjYWwoTylfViAoVikiXSxbMCwxLCJjYWwoTylfKFhfVSkgKFhfVSkiXSxbMSwxLCJjYWwoTylfVSAoVSkiXSxbMCwxLCJObV8oZl9WKSJdLFsyLDMsIk5tXyhmX1UpIl0sWzMsMV0sWzIsMF1d
    #align(center, diagram({
      node((0, 0), [$cal(O)_(X_V) (X_V)$])
      node((1, 0), [$cal(O)_V (V)$])
      node((0, 1), [$cal(O)_(X_U) (X_U)$])
      node((1, 1), [$cal(O)_U (U)$])
      edge((0, 0), (1, 0), [$Nm_(f_V)$], label-side: left, "->")
      edge((0, 1), (1, 1), [$Nm_(f_U)$], label-side: right, "->")
      edge((1, 1), (1, 0), "->")
      edge((0, 1), (0, 0), "->")
    }))
    This can be checked locally by replacing $U, V$ by their affine opens. Thus, we may assume that $U, V$ are affine. Then this reduces to showin that: Given a finite locally free $A$-algebra $B$ of rank $r$, any $A$-algebra $A'$ with $B' = B' otimes_A A'$, 
    // https://q.uiver.app/#r=typst&q=WzAsNCxbMCwwLCJCJyJdLFswLDEsIkIiXSxbMSwxLCJBIl0sWzEsMCwiQSciXSxbMSwwXSxbMiwzXSxbMSwyLCJObSIsMl0sWzAsMywiTm0iXV0=
    #align(center, diagram({
      node((0, 0), [$B'$])
      node((0, 1), [$B$])
      node((1, 1), [$A$])
      node((1, 0), [$A'$])
      edge((0, 1), (0, 0), "->")
      edge((1, 1), (1, 0), "->")
      edge((0, 1), (1, 1), [$Nm$], label-side: right, "->")
      edge((0, 0), (1, 0), [$Nm$], label-side: left, "->")
    }))
    commutes. This is evident. 

    Finally, it suffices to show that $Nm_f: f_* GG_(m,X) -> GG_(m,Y)$ induces $Nm_f: Pic(X) -> Pic(Y)$ on $H^1$. Since $H^1_et$ and $H^1_#[Zar]$ of $GG_m$ are canonically isomorphic, it suffices to show that: 
    $
      Nm_f: f_* cal(O)_X^times -> cal(O)_Y^times
    $
    induces $Nm_f: Pic(X) -> Pic(Y)$ by $H^1_#[Zar]$. 

    - Any $cal(L) in Pic(X)$ can be trivialized by a Zariski cover of $X$ coming from a Zariski cover of $Y$. 

      Indeed, for any $y in abs(Y)$, $X times_Y Spec(cal(O)_(Y,y)) = Spec(B_y)$ is a Dedekind domain and in particular a UFD, and it hence has trivial class group. Thus $cal(L)|_(X times_Y Spec(cal(O)_(Y,y)))$ as a line bundle is necessarily trivial. By spreading out, there exists a Zariski open $V subset Y$ s.t. $cal(L)|_(f^(-1)(V))$ is trivial. 

      Thus, we may take a Zariski cover ${Y_i}$ of $Y$, base changing to ${X_i}$ of $X$ with isomorphisms $phi_i: cal(L)|_(X_i) -> cal(O)_(X_i)$. We have sections $s_(i,j) in cal(O)_(X_(i,j)) (X_(i,j))^times$, defining the transition maps: 
      $
        phi_j compose phi_i^(-1): cal(O)_(X_(i,j)) -> cal(O)_(X_(i,j))
      $

    Now consider: 
    $
      Nm_f (cal(L)) = det(f_* cal(L)) otimes det(f_* cal(O)_X)^(otimes -1)
    $

    Applying $f_*$ to $phi_i$ gives an isomorphism $psi_i: f_* cal(L)|_(X_i) -> f_* cal(O)_(X_i)$, and taking determinants gives an isomorphism: 
    $
      det(psi_i): det(f_* cal(L))|_(Y_i) -> det(f_* cal(O)_X)|_(Y_i)
    $
    i.e. a trivialization: 
    $
      chi_i: Nm_f (cal(L))|_(Y_i) -> cal(O)_(Y_i)
    $
    We thus need to compare the trivialization on overlaps $Y_(i,j)$. Now by definition, 
    $
      phi_j = s_(i,j) compose phi_i: cal(L)_(X_(i,j)) -> cal(O)_(X_(i,j))
    $
    Thus applying $f_*$, 
    $
      psi_j = f_* s_(i,j) compose psi_i: cal(L)_(X_(i,j)) -> cal(O)_(X_(i,j))
    $
    and applying determinants, 
    $
      det(psi_j) = det(f_* s_(i,j)) compose det(psi_i): det(f_* cal(L))|_(Y_(i,j)) -> det(f_* cal(O)_X)|_(Y_(i,j))
    $
    Then we see that the elements $t_(i,j) in cal(O)_(Y_(i,j)) (Y_(i,j))^times$ defining the transition between the maps ${chi_i}$ are exactly those defining: 
    $
      det(f_* s_(i,j)): det(f_* cal(O)_X)|_(Y_(i,j)) -> det(f_* cal(O)_X)|_(Y_(i,j))
    $
    On $f_* cal(O)_(X_(i,j))$, $f_* s_(i,j)$ is multiplication by the element $s_(i,j)$ on the locally free $cal(O)_(Y_(i,j))$-module $f_* cal(O)_(X_(i,j))$. Thus by definition of $Nm_f$, $det(f_* s_(i,j))$ is multiplication by $Nm_f (s_(i,j))$. Thus $t_(i,j) = Nm_f (s_(i,j))$. We have thus concluded that: 
    $
      Nm_f: Pic(X) -> Pic(Y)
    $
    is induced by $Nm_f: f_* GG_(m,X) -> GG_(m,Y)$. 
  ]

  Recall that we want commutativity of: 
  #align(center, diagram({
    node((0, 0), [$H^2_c (U, mu_n)$])
    node((0, 1), [$H^2_c (U, mu_n)$])
    node((1, 0), [$H^2 (ol(U), mu_n)$])
    node((2, 0), [$Pic(ol(U))\/n Pic(ol(U))$])
    node((3, 0), [$ZZ\/n$])
    node((3, 1), [$ZZ\/n$])
    node((1, 1), [$H^2 (X, mu_n)$])
    node((2, 1), [$Pic(X)\/n Pic(X)$])
    edge((0, 0), (0, 1), "=")
    edge((3, 0), (3, 1), "=")
    edge((0, 0), (1, 0), [$Tr_(U\/ol(U))^compose$], label-side: left, "->")
    edge((1, 0), (2, 0), [$tilde$], label-side: left, "->")
    edge((2, 0), (3, 0), [$deg$], label-side: left, "->")
    edge((0, 1), (1, 1), [$Tr_(U\/X)^compose$], label-side: right, "->")
    edge((1, 1), (2, 1), [$tilde$], label-side: right, "->")
    edge((2, 1), (3, 1), [$deg$], label-side: right, "->")
  }))
  Note that using the Kummer sequence, there exists a unique $Nm_(ol(f)): ol(f)_* mu_n -> mu_n$ fitting in the commutative diagram: 
  // https://q.uiver.app/#r=typst&q=WzAsMTAsWzAsMCwiMCJdLFsxLDAsIm9sKGYpXyogbXVfKG4sb2woVSkpIl0sWzIsMCwib2woZilfKiBHR18obSxvbChVKSkiXSxbMywwLCJvbChmKV8qIEdHXyhtLG9sKFUpKSJdLFs0LDAsIjAiXSxbMCwxLCIwIl0sWzEsMSwibXVfKG4sWCkiXSxbMiwxLCJHR18obSxYKSJdLFszLDEsIkdHXyhtLFgpIl0sWzQsMSwiMCJdLFswLDFdLFsxLDJdLFsyLDMsIigtKV5uIl0sWzMsNF0sWzUsNl0sWzYsN10sWzcsOCwiKC0pXm4iLDJdLFs4LDldLFsxLDYsIk5tXyhvbChmKSkiLDJdLFsyLDcsIk5tXyhvbChmKSkiXSxbMyw4LCJObV8ob2woZikpIl1d
  #align(center, diagram({
    node((0, 0), [$0$])
    node((1, 0), [$ol(f)_* mu_(n,ol(U))$])
    node((2, 0), [$ol(f)_* GG_(m,ol(U))$])
    node((3, 0), [$ol(f)_* GG_(m,ol(U))$])
    node((4, 0), [$0$])
    node((0, 1), [$0$])
    node((1, 1), [$mu_(n,X)$])
    node((2, 1), [$GG_(m,X)$])
    node((3, 1), [$GG_(m,X)$])
    node((4, 1), [$0$])
    edge((0, 0), (1, 0), "->")
    edge((1, 0), (2, 0), "->")
    edge((2, 0), (3, 0), [$(-)^n$], label-side: left, "->")
    edge((3, 0), (4, 0), "->")
    edge((0, 1), (1, 1), "->")
    edge((1, 1), (2, 1), "->")
    edge((2, 1), (3, 1), [$(-)^n$], label-side: right, "->")
    edge((3, 1), (4, 1), "->")
    edge((1, 0), (1, 1), [$Nm_(ol(f))$], label-side: right, "->")
    edge((2, 0), (2, 1), [$Nm_(ol(f))$], label-side: left, "->")
    edge((3, 0), (3, 1), [$Nm_(ol(f))$], label-side: left, "->")
  }))

  Then the desired diagram factors as: 
  // https://q.uiver.app/#r=typst&q=WzAsOCxbMCwwLCJIXjJfYyAoVSwgbXVfbikiXSxbMCwxLCJIXjJfYyAoVSwgbXVfbikiXSxbMSwwLCJIXjIgKG9sKFUpLCBtdV9uKSJdLFsyLDAsIlBpYyhvbChVKSlcXC9uIFBpYyhvbChVKSkiXSxbMywwLCJaWlxcL24iXSxbMywxLCJaWlxcL24iXSxbMSwxLCJIXjIgKFgsIG11X24pIl0sWzIsMSwiUGljKFgpXFwvbiBQaWMoWCkiXSxbMCwxLCIiLDAseyJzdHlsZSI6eyJib2R5Ijp7Im5hbWUiOiJkb3VibGUgYmFycmVkIn19fV0sWzQsNSwiIiwwLHsic3R5bGUiOnsiYm9keSI6eyJuYW1lIjoiZG91YmxlIGJhcnJlZCJ9fX1dLFswLDIsIlRyXyhVXFwvb2woVSkpXmNvbXBvc2UiXSxbMiwzLCJ0aWxkZSJdLFszLDQsImRlZyJdLFsxLDYsIlRyXyhVXFwvWCleY29tcG9zZSIsMl0sWzYsNywidGlsZGUiLDJdLFs3LDUsImRlZyIsMl0sWzIsNiwiTm1fKG9sKGYpKSJdLFszLDcsIk5tXyhvbChmKSkiXV0=
  #align(center, diagram({
    node((0, 0), [$H^2_c (U, mu_n)$])
    node((0, 1), [$H^2_c (U, mu_n)$])
    node((1, 0), [$H^2 (ol(U), mu_n)$])
    node((2, 0), [$Pic(ol(U))\/n Pic(ol(U))$])
    node((3, 0), [$ZZ\/n$])
    node((3, 1), [$ZZ\/n$])
    node((1, 1), [$H^2 (X, mu_n)$])
    node((2, 1), [$Pic(X)\/n Pic(X)$])
    edge((0, 0), (0, 1), "=")
    edge((3, 0), (3, 1), "=")
    edge((0, 0), (1, 0), [$Tr_(U\/ol(U))^compose$], label-side: left, "->")
    edge((1, 0), (2, 0), [$tilde$], label-side: left, "->")
    edge((2, 0), (3, 0), [$deg$], label-side: left, "->")
    edge((0, 1), (1, 1), [$Tr_(U\/X)^compose$], label-side: right, "->")
    edge((1, 1), (2, 1), [$tilde$], label-side: right, "->")
    edge((2, 1), (3, 1), [$deg$], label-side: right, "->")
    edge((1, 0), (1, 1), [$Nm_(ol(f))$], label-side: left, "->")
    edge((2, 0), (2, 1), [$Nm_(ol(f))$], label-side: left, "->")
  }))

  Now: 

  - The middle square commutes by the commutative diagram of the Kummer sequence and $Nm_(ol(f))$; 

  - The right square commutes since $ol(f)_* (sum_(u in ol(U)) n_u u) = sum_(u in ol(U)) n_u ol(f)(u)$, so on the divisor level $ol(f): Div(ol(U)) -> Div(X)$ preserves degrees. Thus $Nm_(ol(f)): Pic(ol(U)) -> Pic(X)$ preserves degrees. 

  - To show that the left square commutes, it suffices to show that the composition: 
    $
      f_! mu_(n,U) cong ol(f)_* j_! mu_(n,U) -> ol(f)_* mu_(n,ol(U)) ->^(Nm_(ol(f))) mu_n
    $
    is exactly the counit map $f_! mu_(n,U) -> mu_n$. /*By checking on stalks, it suffices to show that $Nm_(ol(f)): ol(f)_* mu_(n,ol(U)) -> mu_(n,X)$ on stalks at $x in abs(X)$ is: 
    $
      oplus.big_(u in ol(f)^(-1)(x)) mu_n -> mu_n
    $
    by a product over all factors. For this, we need to show that the stalk of $Nm_(ol(f)): ol(f)_* GG_(m,ol(U)) -> GG_(m,X)$ at $x in abs(X)$ is: 
    $
      oplus.big_(u in ol(f)^(-1)(x)) (cal(O)_(ol(U),u)^#[sh])^times -> (cal(O)_(X,x)^#[sh])^times
    $ 
    a product over all factors.*/ 

    #lemma[
      Let $f: X -> Y$ be a finite morphism between smooth projective curves over an algebraically closed field $k$, which is automatically flat of degree $r$. Then $Nm_f: f_* GG_(m,X) -> GG_(m,Y)$ has its stalks at $y in abs(Y)$ identified as: 
      $
        oplus.big_(x in f^(-1)(y)) (cal(O)_(X,x)^#[sh])^times -> (cal(O)_(Y,y)^#[sh])^times, (a_x)_x |-> product_(x in f^(-1)(y)) Nm_(cal(O)_(X,x)^#[sh]\/cal(O)_(Y,y)^#[sh]) (a_x)
      $ 
      where $cal(O)_(X,x)^#[sh]\/cal(O)_(Y,y)^#[sh]$ are extensions of DVRs. (Here, the closed points of $X$ and $Y$ are algebraically closed, hence automatically geometric points.)
    ]
    #proof[
      Consider the norm map: 
      $
        Nm_f: f_* cal(O)_X -> cal(O)_Y
      $
      of the locally free sheaf $f_* cal(O)_X$ over $cal(O)_Y$. Locally this construction is $Nm_(B\/A): B -> A$ for a locally free finite $A$-algebra $B$, and is preserved under arbitrary base change in $A$ and also limits in $A$. Thus, taking a limit over all affine etale neighborhoods of $y in Y$, the stalk of $Nm_f: f_* GG_(m,X) -> GG_(m,Y)$ at $y$ is: 
      $
        Nm: Gamma(X times_Y tilde(Y)_y, cal(O)_(X times_Y tilde(Y)_y))^times -> (cal(O)_(Y,y)^#[sh])^times
      $
      By @strict-henselization-and-finite-base-change, since $f$ is finite, $X times_Y tilde(Y)_y = union.sq.big_(x in f^(-1)(y)) tilde(X)_x$, where each $cal(O)_(X,x)^#[sh]\/cal(O)_(Y,y)^#[sh]$ is an extension of DVRs. Thus the norm above is identified as: 
      $
        oplus.big_(x in f^(-1)(y)) (cal(O)_(X,x)^#[sh])^times -> (cal(O)_(Y,y)^#[sh])^times, (a_x)_x |-> product_(x in f^(-1)(y)) Nm_(cal(O)_(X,x)^#[sh]\/cal(O)_(Y,y)^#[sh]) (a_x)
      $
      and this lemma is proved. 
    ]
    Thus, by the previous lemma, $Nm_(ol(f)): ol(f)_* mu_(n,ol(U)) -> mu_(n,X)$ on stalks at $x in abs(X)$ is identified as: 
    $
      oplus.big_(u in ol(f)^(-1)(x)) mu_n -> mu_n, (a_u)_u |-> product_(u in ol(f)^(-1)(x)) a_u^(r_u)
    $
    where $r_u := "rk"_(cal(O)_(X,x)^#[sh]) (cal(O)_(ol(U),u)^#[sh])$. We now check the compostion: 
    $
      f_! mu_(n,U) cong ol(f)_* j_! mu_(n,U) -> ol(f)_* mu_(n,ol(U)) ->^(Nm_(ol(f))) mu_(n,X)
    $
    on stalks at $x in abs(X)$. It is: 
    $
      oplus.big_(u in f^(-1)(x)) mu_n cong oplus.big_(u in ol(f)^(-1)(x) \ u in U) mu_n -> oplus.big_(u in ol(f)^(-1)(x)) mu_n -> mu_n
    $
    where the first map fills the missing entries by 1, and the second map is a stalk of $Nm_(ol(f))$. Thus as described above, this composition is: 
    $
      (a_u)_(u in f^(-1)(x)) &|-> (a'_u)_(u in ol(f)^(-1)(x)) #[where] a'_u = cases(a_u &\, u in abs(U), 1 &\, u in ol(U) - U) \
      &|-> product_(u in ol(f)^(-1)(x)) (a'_u)^(r_u) \
      &= product_(u in f^(-1)(x)) a_u^(r_u) #[since $a'_u = 1$ for $u in ol(U) - U$] \
      &= product_(u in f^(-1)(x)) a_u
    $
    where in the last step, each $r_u = 1$ as $f: U -> X$ is etale, so $cal(O)_(U,u)^#[sh] = cal(O)_(X,x)^#[sh]$. This is exactly the counit $f_! mu_(n,U) -> mu_(n,X)$ on stalks. 

    Thus the left square commutes and we may conclude the proof. 
]

#lemma(name: <pd-trace-curve-affine-compat>)[
  Let $p: AA^1_k -> Spec(k)$, where $k$ is an algebraically closed field. Then: 
  $
    Tr^tilde_(AA^1_k\/k) = Tr^square_(AA^1_k\/k)
  $
]
#proof[
  By definition, $Tr^tilde_(AA^1_k\/k)$ is: 
  $
    H^2_c (AA^1_k, mu_n) ->^tilde H^2 (PP^1_k, mu_n) cong Pic(PP^1_k)\/n Pic(PP^1_k) -->^deg_tilde ZZ\/n
  $
  Note that $deg(cal(O)(1)) = 1$, so $H^2 (PP^1_k, mu_n) -> Pic(PP^1_k)\/n Pic(PP^1_k) ->^deg ZZ\/n$ is exactly the inverse of: 
  $
    alpha_k: ZZ\/n ->^(cal(O)(1)) Pic(PP^1_k)\/n Pic(PP^1_k) -> H^2 (PP^1_k, mu_n)
  $
  Hence, by definition of $Tr_(AA^1_k\/k)^square$, $Tr^tilde_(AA^1_k\/k) = Tr^square_(AA^1_k\/k)$. 
]

#lemma(name: <pd-trace-etale-affine-compat>)[
  Suppose that $f: X -> Y$ is a separated smooth morphism of relative dimension $d$. A list of global sections $s_1, dots.c, s_d in cal(O)_X (X)$ is equivalent to a map $j_(s_1,dots.c,s_d): X -> AA^d_Y$. 
  
  Suppose that two lists of global sections $s_i, s'_i in cal(O)_X (X)$ both defines etale morphisms $j_(s_1,dots.c,s_d), j_(s'_1,dots.c,s'_d): X -> AA^d_Y$. Then: 
  $
    Tr^square_(AA^d_Y\/Y) diamond.small Tr^compose_(j_(s_1,dots.c,s_d)) = Tr^square_(AA^d_Y\/Y) diamond.small Tr^compose_(j_(s'_1,dots.c,s'_d))
  $
]
#proof[
  First, note that this problem is Zariski local in $x$. 
  
  - Indeed, suppose that for any $x in X$ there is a Zariski neighborhood $U -> X$ of $x$ s.t: 
    $
      Tr^square_(AA^d_Y\/Y) diamond.small Tr^compose_(j_(s_1|_U,dots.c,s_d|_U)) = Tr^square_(AA^d_Y\/Y) diamond.small Tr^compose_(j_(s'_1|_U,dots.c,s'_d|_U))
    $
    Note that $j_(s_1|_U,dots.c,s_d|_U): U -> AA^d_k$ is just the composition: 
    $
      U -> X -->^(j_(s_1,dots.c,s_d)) AA^d_k
    $
    and the same goes for the primed variants. Since $Tr^compose$ is compatible with composition, 
    $
      Tr^square_(AA^d_Y\/Y) diamond.small Tr^compose_(j_(s_1,dots.c,s_d)) diamond.small Tr^compose_(U\/X) = Tr^square_(AA^d_Y\/Y) diamond.small Tr^compose_(j_(s'_1,dots.c,s'_d)) diamond.small Tr^compose_(U\/X)
    $
    Taking a disjoint union of an open cover obtained this way, there exists a surjective etale $ell: U -> X$ s.t. the above relation holds. Now: 
    $
      Tr_(U\/X)^compose: R^(2d) f_! ell_! mu_n^(otimes d) -> R^(2d) f_! mu_n^(otimes d) 
    $
    is surjective, since $ell_! mu_n^(otimes d) -> mu_n^(otimes d)$ is surjective and $R^(2d) f_!$ is right exact by Grothendieck vanishing. As such, $Tr_(U\/X)^compose$ may be right cancelled from $Tr^square_(AA^d_Y\/Y) diamond.small Tr^compose_(j_(s_1,dots.c,s_d)) diamond.small Tr^compose_(U\/X) = Tr^square_(AA^d_Y\/Y) diamond.small Tr^compose_(j_(s'_1,dots.c,s'_d)) diamond.small Tr^compose_(U\/X)$, yielding: 
    $
      Tr^square_(AA^d_Y\/Y) diamond.small Tr^compose_(j_(s_1,dots.c,s_d)) = Tr^square_(AA^d_Y\/Y) diamond.small Tr^compose_(j_(s'_1,dots.c,s'_d))
    $

  Next, by compatibility with base change, we may assume that $Y = Spec(k)$ for an algebraically closed field $k$. Thus, fix a closed point $x in abs(X)$, and it suffices to prove that there exists a Zariski open $x in U subset X$ s.t: 
  $
    Tr^square_(AA^d_k\/k) diamond.small Tr^compose_(j_(s_1|_U,dots.c,s_d|_U)) = Tr^square_(AA^d_k\/k) diamond.small Tr^compose_(j_(s'_1|_U,dots.c,s'_d|_U))
  $

  Observe: 

  + Note that for a permutation $sigma in S_d$, 
    $
      Tr^square_(AA^d_k\/k) diamond.small Tr^compose_(j_(s_1,dots.c,s_d)) =  Tr^square_(AA^d_k\/k) diamond.small Tr^compose_(j_(s_(sigma(1)),dots.c,s_(sigma(d))))
    $
    Indeed, regard $sigma$ as an automorphism $phi_sigma: AA^d_k -> AA^d_k, (x_1, dots.c, x_d) |-> (x_(sigma(1)), dots.c, x_(sigma(d)))$, we have: 
    $
      j_(s_1,dots.c,s_d) compose phi_sigma = j_(s_(sigma(1)),dots.c,s_(sigma(d)))
    $
    Hence, 
    $
      Tr^square_(AA^d_k\/k) diamond.small Tr^compose_(j_(s_1,dots.c,s_d)) =  Tr^square_(AA^d_k\/k) diamond.small Tr^compose_(phi_sigma) diamond.small Tr^compose_(j_(s_(sigma(1)),dots.c,s_(sigma(d))))
    $
    whereas $Tr^square_(AA^d_k\/k) = Tr^square_(AA^d_k\/k) diamond.small Tr^compose_(phi_sigma)$ as shown in @pd-trace-affine-constr. 

  + /*Note that for $c_1, dots.c, c_d in k$, #h(1fr)
    $
      Tr^square_(AA^d_k\/k) diamond.small Tr^compose_(j_(s_1,dots.c,s_d)) = Tr^square_(AA^d_k\/k) diamond.small Tr^compose_(j_(s_1-c_1,dots.c,s_d-c_d))
    $
    Indeed, by subtracting on one section at a time, we may assume that we are only replacing $s_i$ with $s_i - c_i$ for a single $i$. By the permutation invariance in the previous bullet, we may assume that $i=d$, i.e. we are modifying the last bullet. */
    Suppose that $s_i = s'_i$ for all $i!=i_0$, i.e. the two lists of sections differ only by one element. By permutation invariance as in (1), we may assume that $i_0 = d$, i.e. the two lists of sections differ only at the last element. 
    
    Now put $pi_d: AA^d_k -> AA^(d-1)_k$ be projection onto the first $(d-1)$ components, and so: 
    $
      pi_d compose j_(s_1,dots.c,s_(d-1),s_d) = j_(s_1,dots.c,s_(d-1)) = pi_d compose j_(s_1,dots.c,s_(d-1),s'_d)
    $
    Now by @pd-trace-affine-constr, 
    $
      Tr^square_(AA^d_k\/k) diamond.small Tr^compose_(j_(s_1,dots.c,s_d)) = Tr^square_(AA^(d-1)_k\/k) diamond.small Tr^square_(AA^d_k\/AA^(d-1)_k) diamond.small Tr^compose_(j_(s_1,dots.c,s_(d-1),s_d)) \
      Tr^square_(AA^d_k\/k) diamond.small Tr^compose_(j_(s_1,dots.c,s'_d)) = Tr^square_(AA^(d-1)_k\/k) diamond.small Tr^square_(AA^d_k\/AA^(d-1)_k) diamond.small Tr^compose_(j_(s_1,dots.c,s_(d-1),s'_d))
    $
    and so it suffices to prove that $Tr^square_(AA^d_k\/AA^(d-1)_k) diamond.small Tr^compose_(j_(s_1,dots.c,s_(d-1),s_d)) = Tr^square_(AA^d_k\/AA^(d-1)_k) diamond.small Tr^compose_(j_(s_1,dots.c,s_(d-1),s'_d))$. By base changing to stalks, it suffices to show that: 

    - Let $K$ be an algebraically closed field and $j, j': U -> AA^1_K$ be etale morphisms, s.t. $g = p_1 compose j = p_1 compose j': U -> Spec(K)$ for $p_1: AA^1_K -> Spec(K)$. Then: #h(1fr)
      $
        Tr^square_(AA^1_K\/K) diamond.small Tr^compose_j = Tr^square_(AA^1_K\/K) diamond.small Tr^compose_(j')
      $
      Now $U$ is separated smooth of relative dimension $1$ over $K$, hence a disjoint union of smooth curves. Replacing $U$ with a connected component, we may thus assume that $U$ is a smooth curve over $K$. Then by @pd-trace-curve-affine-compat and more importantly @pd-trace-etale-curve-compat, 
      $
        Tr^square_(AA^1_K\/K) diamond.small Tr^compose_j = Tr^tilde_(AA^1_K\/K) diamond.small Tr^compose_j = Tr^tilde_(g:U\/K) \
        
        Tr^square_(AA^1_K\/K) diamond.small Tr^compose_(j') = Tr^tilde_(AA^1_K\/K) diamond.small Tr^compose_(j') = Tr^tilde_(g:U\/K)
      $
      are equal. 

  Now by observation (2), we may replace $s_i$ by $s_i - (s_i mod frak(m)_x in k)$ to assume that every $s_i in frak(m)_x$, and the same for $s'_i$. These modifications to the sections compose $j_(s_1,dots.c,s_d)$ with a translation $AA^d_k -> AA^d_k$ and do not affect etaleness, so observation (2) is indeed applicable. 
  
  To proceed, we establish a lemma: 

  #lemma[
    Let $k$ be an algebraically closed field and $X -> Spec(k)$ be separated smooth of relative dimension $d$, or identically $X$ is regular. For a closed point $x in abs(X)$, suppose that global sections $s_1, dots.c, s_d in cal(O)_X (X)$ are in $frak(m)_x cal(O)_(X,x)$. Then the map $j_(s_1,dots.c,s_d): X -> AA^d_k$ they define, sending $x$ to $0$, is etale at $x$ if and only if: 
    $
      [s_1], dots.c, [s_d] in frak(m)_x\/frak(m)_x^2
    $ 
    form a basis for the $d$-dimensional $k$-vector space $frak(m)_x\/frak(m)_x^2$. 
  ]
  #proof[
    The given condition is equivalent to: 
    $
      frak(m)_x = (s_1, dots.c, s_d) cal(O)_(X,x)
    $
    by Nakayama's lemma. 

    ($==>$) Since $j_(s_1,dots.c,s_d)$ is etale, $frak(m)_x = frak(m)_0 cal(O)_(X,x) = (s_1, dots.c, s_d) cal(O)_(X,x)$. 

    ($<==$) In the case that: 
    $
      frak(m)_x = (s_1, dots.c, s_d) cal(O)_(X,x) = frak(m)_0 cal(O)_(X,x)
    $
    note that $x in X$ and $0 in AA^d_k$ both has residue field $k$. Thus $j_(s_1,dots.c,s_d)$ is unramified at $x$. To show that it is etale at $x$ it suffices to show flatness at $x$. By miracle flatness, it suffices to show that: 
    $
      dim(cal(O)_(X,x)) = dim(cal(O)_(AA^d_k,0)) + dim(cal(O)_(X_0,x))
    $
    Thus it suffices to show that $dim(cal(O)_(X_0,x)) = 0$, i.e. $x$ is an isolated point of its fiber. Indeed, $cal(O)_(X_0,x) = cal(O)_(X,x)\/(s_1,dots.c,s_d) cal(O)_(X,x) = cal(O)_(X,x)\/frak(m)_x = k$ is zero-dimensional. 
  ]

  Now since $j_(s_1,dots.c,s_d)$ and the primed version are etale, $[s_1], dots.c, [s_d]$ and $[s'_1], dots.c, [s'_d]$ are two bases of the $d$-dimensional $k$-vector space $frak(m)_x\/frak(m)_x^2$. From linear algebra, there exists a finite chain of bases: 
  $
    [s_1^((t))], dots.c, [s_d^((t))] in frak(m)_x\/frak(m)_x^2, 0 <= t <= T
  $
  s.t: 

  - $[s_i^((0))] = [s_i], [s_i^((T))] = [s'_i]$; 

  - For every $1<=t<=T$, $[s_1^((t-1))], dots.c, [s_d^((t-1))]$ and $[s_1^((t))], dots.c, [s_d^((t))]$ differs in exactly one element. 

  We now take lift them to sections $s_i^((t)), 0 <= t <= T + d$ as follows: 

  - Take $s_i^((0)) = s_i$; 

  - For any $1<=t<=T$ with $s_i^((t-1))$ already defined, let $i_t$ be the unique index s.t. $[s_(i_t)^((t))] != [s_(i_t)^((t-1))]$. Then take: 
    $
      s_i^((t)) = cases(
        s_i^((t-1)) &\, i != i_t, 
        #[arbitrary lift of $[s_i^((t))]$ in $frak(m)_x$] &\, i = i_t
      )
    $

  - For $t = T + alpha, 1 <= alpha <= T$, take: 
    $
      s_i^((T+alpha)) = cases(
        s_i^((T)) &\, i > alpha, 
        s'_i &\, i <= alpha
      )
    $
    so all $[s_i^((T+alpha))] = [s_i^((T))] = [s'_i]$. 

  Then this chain of lists of sections $s_i^((t)) in frak(m)_x, 0 <= t <= T+d$ has the following property: 
  
  - For every $t$, $[s_1^((t))], dots.c, [s_d^((t))] in frak(m)_x\/frak(m)_x^2$ is a basis; 

  - $s_i^((0)) = s_i, s_i^((T+d)) = s'_i$; 

  - For every $1<=t<=T$, $s_1^((t-1)), dots.c, s_d^((t-1))$ and $s_1^((t)), dots.c, s_d^((t))$ differs in at most one element. 

  By the previous lemma, each $j_(s_1^((t)), dots.c, s_d^((t))): X -> AA^d_k$ is etale at $x$. Since the etale locus is open, by replacing $X$ with a suitable Zariski open around $x$, we may assume that each $j_(s_1^((t)), dots.c, s_d^((t))): X -> AA^d_k$ is etale. Now by observation (2) and that $s_1^((t-1)), dots.c, s_d^((t-1))$ and $s_1^((t)), dots.c, s_d^((t))$ differs in at most one element, 
  $
    Tr^square_(AA^d_k\/k) diamond.small Tr^compose_(j_(s_1^((t-1)),dots.c,s_d^((t-1)))) = Tr^square_(AA^d_k\/k) diamond.small Tr^compose_(j_(s_1^((t)),dots.c,s_d^((t)))), forall 1<=t<=T+d
  $
  Chaining these equalities, we see that: 
  $
    Tr^square_(AA^d_k\/k) diamond.small Tr^compose_(j_(s_1,dots.c,s_d)) = Tr^square_(AA^d_k\/k) diamond.small Tr^compose_(j_(s'_1,dots.c,s'_d))
  $
]

As a corollary, a family of trace maps can now be defined on those separated smooth morphisms $X -> Y$ admitting a factorization $X -> AA^d_Y -> Y$ with the first map etale. 

#proposition(name: <pd-trace-1>)[
  There exists a family of trace-like maps ${Tr^((1))_(X\/Y)}$ on the family $cal(S)^((1))$ of separated smooth morphisms defined as: 
  $
    cal(S)^((1)) = {&f:X -> Y #[separated smooth of relative dimension $d$]\
    &: #[$X,Y$ noetherian $ZZ[n^(-1)]$-schemes, $f$ factors as $X ->^j AA^d_Y -> Y$ for some etale $j: X -> AA^d_Y$]}
  $
  Here the etale morphism $j$ is automatically separated. This family of trace-like maps is constructed as: 
  $
    Tr_(X\/Y)^((1)) := Tr_(AA^d_Y\/Y)^square diamond.small Tr_j^compose
  $
  for a factorization $f: X ->^j AA^d_Y -> Y$ with $j$ etale. Furthermore, 

  0. ${Tr^((1))_(X\/Y)}_((f:X->Y) in cal(S)^((1)))$ is compatible with composition and base change; 

  + For $X -> Y$ separated etale, #h(1fr)
    $
      Tr_(X\/Y)^((1)) = Tr_(X\/Y)^compose
    $
]
#proof[
  $
    Tr_(X\/Y)^((1)) := Tr_(AA^d_Y\/Y)^square diamond.small Tr_j^compose
  $
  is well-defined (i.e. independent from the factorization $X ->^j AA^d_Y -> Y$) by @pd-trace-etale-affine-compat. Now (1) is automatic from the definition, and compatibility with base change follows from that of $Tr^square$ and $Tr^compose$. 

  To show compatibility with composition, let $f: X -> Y, g: Y -> Z$ be in $cal(S)^((1))$, factoring as: 
  $
    f: X ->^j AA^d_Y -> Y, g: Y ->^ell AA^e_Z -> Z
  $
  for $j,ell$ etale. Then $g compose f$ factors as: 
  $
    X ->^q AA^(d+e)_Z -> Z
  $
  where $q: X ->^j AA^d_Y ->^(ell_d) AA^(d+e)_Z$ is etale. Thus by compatibility with composition of the constructions $Tr^square$ and $Tr^compose$: 
  $
    Tr^((1))_g diamond.small Tr^((1))_f = Tr^square_(AA^e_Z\/Z) diamond.small Tr^compose_ell diamond.small Tr^square_(AA^d_Y\/Y) diamond.small Tr^square_j \

    Tr^((1))_(g compose f) = Tr^square_(AA^e_Z\/Z) diamond.small Tr^square_(AA^(d+e)_Z\/AA^e_Z) diamond.small Tr^compose_(ell_d) diamond.small Tr^square_j
  $
  and hence, it suffices to prove: 
  $
    Tr^compose_ell diamond.small Tr^square_(AA^d_Y\/Y) = Tr^square_(AA^(d+e)_Z\/AA^e_Z) diamond.small Tr^compose_(ell_d)
  $
  where $ell: Y -> AA^e_Z$ is etale, and $ell_d: AA^d_Y -> AA^(d+e)_Z$ is its base change along $AA^(d+e)_Z -> AA^e_Z$ the projection onto first $e$ coordinates. Suppose that we are done with the case $d=1$. By factoring: 
  $
    Tr^square_(AA^d_Y\/Y) = Tr^square_(AA^d_Y\/AA^(d-1)_Y) diamond.small dots.c diamond.small Tr^square_(AA^1_Y\/Y)
  $
  and exchanging step by step according to the $d=1$ case, we are done with the general case. Thus we may assume $d=1$ and aim to prove: 
  $
    Tr^compose_ell diamond.small Tr^square_(AA^1_Y\/Y) = Tr^square_(AA^(e+1)_Z\/AA^e_Z) diamond.small Tr^compose_(ell_1)
  $
  Base changing to an algebraically closed geometric point $Spec(K) -> AA^e_Z$, and $ell: Y -> Spec(K)$ becomes a finite disjoint union of $Spec(K)$'s. Then it suffices to prove: 
  $
    Tr^compose_ell diamond.small Tr^square_(AA^1_Y\/Y) = Tr^square_(AA^1_K\/K) diamond.small Tr^compose_(Y\/K)
  $ 
  Indeed, on each connected component $Spec(K)$ of $Y$, both sides are $Tr^square_(AA^1_K\/K)$. We are thereby done. 
]

We are now ready to glue ${Tr^((1))_(X\/Y)}$ to finally obtain the trace map. 

#theorem(name: <existence-of-trace-map>)[
  There exists a unique family ${Tr_(X\/Y)}$ on the family of all separated smooth morphisms of pure relative dimension between noetherian $ZZ[n^(-1)]$-schemes s.t: 

  0. ${Tr_(X\/Y)}$ is compatible with base change and composition; 

  + For $f: X -> Y$ separated etale (i.e. smooth of relative dimension 0), #h(1fr)
    $
      Tr_(X\/Y) = Tr_(X\/Y)^compose
    $

  + For $f: X -> Spec(k)$ a smooth curve over $k$ algebraically closed, 
    $
      Tr_(X\/k) = Tr_(X\/k)^tilde
    $ 

  + For any $d$, 
    $
      Tr_(AA^d_Y\/Y) = Tr_(AA^d_Y\/Y)^square
    $

  // + If $X -> Y$ is separated smooth of relative dimension $d$ and has nonempty connected geometric fibers, then $Tr_(X\/Y): R^(2d) f_! mu_(n,X)^(otimes d) -> ul(ZZ\/n)_Y$ is an isomorphism. 
]
#proof[
  Uniqueness follows from @pd-trace-uniqueness, so we prove existence only. 

  Take any separated smooth morphism $f: X -> Y$ of relative dimension $d$ between noetherian $ZZ[n^(-1)]$-schemes. By the local structure of smooth maps, for every geometric point $ol(x)$ of $X$ there is an etale neighborhood $(U, ol(u)) -> (X, ol(x))$ (in fact, a Zariski neighborhood is possible) s.t. $U -> Y$ factors as $U ->^j AA^d_Y -> Y$ with $j$ etale. Thus, taking a finite subcover and a disjoint union over selected $U$'s, there exists a surjective etale map $q: X' -> X$ s.t. $f compose q: X' -> Y$ factors as $X' ->^j AA^d_Y -> Y$. Let $X'' = X' times_X X'$, let $q': X'' -> X$ be the induced map, and let $q_1, q_2: X'' -> X'$ be the two projections. Form the base changes: 

  Note that for any sheaf $cal(F)$ on $X$, there is a right exact sequence: 
  $
    q'_! q'^(-1) cal(F) -->^(Tr^compose_(q_1) - Tr^compose_(q_2)) q_! q^(-1) cal(F) -->^(Tr^compose_q) cal(F) -> 0
  $
  This can be checked either on stalks, or by applying $Hom(-, cal(G))$ and using Yoneda. Applying $R^(2d)f_!$ keeps its right exactness, since $R^(2d) f_!$ is right exact by Grothendieck vanishing. We now have a commutative diagram: 
  // https://q.uiver.app/#r=typst&q=WzAsOCxbMCwwLCJxJ18hIFJeKDJkKSBmXyEgbXVfbl4ob3RpbWVzIGQpIl0sWzEsMCwicV8hIFJeKDJkKSBmXyEgbXVfbl4ob3RpbWVzIGQpIl0sWzIsMCwiUl4oMmQpIGZfISBtdV9uXihvdGltZXMgZCkiXSxbMSwxLCJ1bChaWlxcL24pIl0sWzAsMSwidWwoWlpcXC9uKSJdLFsyLDEsInVsKFpaXFwvbikiXSxbMywwLCIwIl0sWzMsMSwiMCJdLFswLDEsIlRyXmNvbXBvc2VfKHFfMSkgLSBUcl5jb21wb3NlXyhxXzIpIl0sWzQsMywiMCIsMl0sWzMsNSwiIiwyLHsic3R5bGUiOnsiYm9keSI6eyJuYW1lIjoiZG91YmxlIGJhcnJlZCJ9fX1dLFs1LDddLFsxLDIsIlRyXmNvbXBvc2VfcSJdLFsyLDZdLFswLDQsIlRyXigoMSkpXyhYJydcXC9ZKSIsMl0sWzEsMywiVHJeKCgxKSlfKFgnXFwvWSkiXV0=
  #align(center, diagram({
    node((0, 0), [$R^(2d) f_! q'_! mu_n^(otimes d)$])
    node((1, 0), [$R^(2d) f_! q_! mu_n^(otimes d)$])
    node((2, 0), [$R^(2d) f_! mu_n^(otimes d)$])
    node((1, 1), [$ul(ZZ\/n)$])
    node((0, 1), [$ul(ZZ\/n)$])
    node((2, 1), [$ul(ZZ\/n)$])
    node((3, 0), [$0$])
    node((3, 1), [$0$])
    edge((0, 0), (1, 0), [$Tr^compose_(q_1) - Tr^compose_(q_2)$], label-side: left, "->")
    edge((0, 1), (1, 1), [$0$], label-side: right, "->")
    edge((1, 1), (2, 1), "=")
    edge((2, 1), (3, 1), "->")
    edge((1, 0), (2, 0), [$Tr^compose_q$], label-side: left, "->")
    edge((2, 0), (3, 0), "->")
    edge((0, 0), (0, 1), [$Tr^((1))_(X''\/Y)$], label-side: right, "->")
    edge((1, 0), (1, 1), [$Tr^((1))_(X'\/Y)$], label-side: left, "->")
  }, spacing: (4.5em, 3em)))
  where the left square commutes, since: 
  $
    Tr^((1))_(X'\/Y) diamond.small Tr^compose_(q_1) = Tr^((1))_(X''\/Y) = Tr^((1))_(X'\/Y) diamond.small Tr^compose_(q_2)
  $
  By diagram tracing, there exists a unique map $Tr^((q))_(X\/Y)$ fitting in the commutative diagram: 
  // https://q.uiver.app/#r=typst&q=WzAsOCxbMCwwLCJxJ18hIFJeKDJkKSBmXyEgbXVfbl4ob3RpbWVzIGQpIl0sWzEsMCwicV8hIFJeKDJkKSBmXyEgbXVfbl4ob3RpbWVzIGQpIl0sWzIsMCwiUl4oMmQpIGZfISBtdV9uXihvdGltZXMgZCkiXSxbMSwxLCJ1bChaWlxcL24pIl0sWzAsMSwidWwoWlpcXC9uKSJdLFsyLDEsInVsKFpaXFwvbikiXSxbMywwLCIwIl0sWzMsMSwiMCJdLFswLDEsIlRyXmNvbXBvc2VfKHFfMSkgLSBUcl5jb21wb3NlXyhxXzIpIl0sWzQsMywiMCIsMl0sWzMsNSwiIiwyLHsic3R5bGUiOnsiYm9keSI6eyJuYW1lIjoiZG91YmxlIGJhcnJlZCJ9fX1dLFs1LDddLFsxLDIsIlRyXmNvbXBvc2VfcSJdLFsyLDZdLFswLDQsIlRyXigoMSkpXyhYJydcXC9ZKSIsMl0sWzEsMywiVHJeKCgxKSlfKFgnXFwvWSkiXSxbMiw1LCJUcl4oKHEpKV8oWFxcL1kpIl1d
  #align(center, diagram({
    node((0, 0), [$R^(2d) f_! q'_! mu_n^(otimes d)$])
    node((1, 0), [$R^(2d) f_! q_! mu_n^(otimes d)$])
    node((2, 0), [$R^(2d) f_! mu_n^(otimes d)$])
    node((1, 1), [$ul(ZZ\/n)$])
    node((0, 1), [$ul(ZZ\/n)$])
    node((2, 1), [$ul(ZZ\/n)$])
    node((3, 0), [$0$])
    node((3, 1), [$0$])
    edge((0, 0), (1, 0), [$Tr^compose_(q_1) - Tr^compose_(q_2)$], label-side: left, "->")
    edge((0, 1), (1, 1), [$0$], label-side: right, "->")
    edge((1, 1), (2, 1), "=")
    edge((2, 1), (3, 1), "->")
    edge((1, 0), (2, 0), [$Tr^compose_q$], label-side: left, "->")
    edge((2, 0), (3, 0), "->")
    edge((0, 0), (0, 1), [$Tr^((1))_(X''\/Y)$], label-side: right, "->")
    edge((1, 0), (1, 1), [$Tr^((1))_(X'\/Y)$], label-side: left, "->")
    edge((2, 0), (2, 1), [$Tr^((q))_(X\/Y)$], label-side: left, "-->")
  }))
  In other words, there exists a unique trace-like map $Tr^((q))_(X\/Y)$ s.t: 
  $
    Tr^((1))_(X'\/Y) = Tr^((q))_(X\/Y) diamond.small Tr^compose_q
  $
  This map $Tr^((q))_(X\/Y)$ is independent from the choice of the etale cover $q$. Indeed: 

  - Suppose that there is another etale cover $tilde(q): tilde(X)' -> X$ refining $q: X' -> X$ as $tilde(X)' ->^r X' ->^q X$. Then $f compose tilde(q) in cal(S)^((1))$ too, and: 
    $
      Tr^((1))_(tilde(X)'\/Y) = Tr^((1))_(X'\/Y) diamond.small Tr^compose_(r:tilde(X)'\/X') = Tr^((q))_(X\/Y) diamond.small Tr^compose_q diamond.small Tr^compose_(r:tilde(X)'\/X') = Tr^((q))_(X\/Y) diamond.small Tr^compose_(tilde(q))
    $
    By uniqueness, $Tr^((q))_(X\/Y) = Tr^((tilde(q)))_(X\/Y)$. 

    Now for general different etale covers $q, tilde(q)'$, we may pick their fiber product as a common refinement, and compare $Tr^((q))_(X\/Y), Tr^((tilde(q)))_(X\/Y)$ both against this common refinement. 

  Now that $Tr^((q))_(X\/Y)$ is independent from the choice of $q$, we may define: 
  $
    Tr_(X\/Y) := Tr^((q))_(X\/Y)
  $
  By definition, $Tr_(X\/Y) = Tr^((1))_(X\/Y)$ if $(f: X -> Y) in cal(S)^((1))$. Thus, (1) and (3) are automatic. 

  - For compatibility with base change, let $g: Y' -> Y$ with $Y'$ noetherian and form a Cartesian diagram: #h(1fr)
    // https://q.uiver.app/#r=typst&q=WzAsNCxbMCwwLCJYJyJdLFsxLDAsIlknIl0sWzAsMSwiWCJdLFsxLDEsIlkiXSxbMiwzLCJmIiwyXSxbMCwxLCJmJyJdLFsxLDMsImciXSxbMCwyLCJnJyIsMl1d
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
    We intend to show that $Tr_(X'\/Y')$ is exactly the composition: 
    $
      Phi: R^(2d) f'_! mu_n^(otimes d) -->^(BC^(-1)) g^(-1) R^(2d) f_! mu_n^(otimes d) -->^(Tr_(X\/Y)) ul(ZZ\/n)
    $
    Indeed, pick an etale cover $q: Z -> X$ s.t. $f compose q in cal(S)^((1))$, and base change to $q': Z' -> X'$. Then $f' compose q' in cal(S)^((1))$ too. By base changing the equality $Tr^((1))_(Z\/Y) = Tr_(X\/Y) diamond.small Tr_q^compose$, we get: 
    $
      Tr^((1))_(Z'\/Y') = Phi diamond.small Tr_(q')^compose
    $
    By uniqueness, $Phi = Tr_(X'\/Y')$. 

  - For compatibility with composition, let $f: X -> Y, g: Y -> Z$ be separated smooth of relative dimension $d,e$ respectively. Now pick etale covers $r: tilde(X) -> X$, $q: Y' -> Y$ s.t. $f compose r, g compose q in cal(S)^((1))$. Form the following commutative diagram: 
    // https://q.uiver.app/#r=typst&q=WzAsNyxbMSwxLCJYIl0sWzIsMSwiWSJdLFszLDEsIloiXSxbMiwwLCJZJyJdLFsxLDAsIlgnIl0sWzAsMSwidGlsZGUoWCkiXSxbMCwwLCJ0aWxkZShYKSciXSxbMCwxLCJmIiwyXSxbMSwyLCJnIiwyXSxbMywxLCJxIl0sWzUsMCwiciIsMl0sWzQsMywiZiciXSxbNiw0LCJyJyJdLFs0LDAsInEnIiwyXSxbNiw1LCJ0aWxkZShxJykiLDJdXQ==
    #align(center, diagram({
      node((0, 1), [$X$])
      node((1, 1), [$Y$])
      node((2, 1), [$Z$])
      node((1, 0), [$Y'$])
      node((0, 0), [$X'$])
      node((-1, 1), [$tilde(X)$])
      node((-1, 0), [$tilde(X)'$])
      node((-0.7, 0.3), $cart$)
      node((0.3, 0.3), $cart$)
      edge((0, 1), (1, 1), [$f$], label-side: right, "->")
      edge((1, 1), (2, 1), [$g$], label-side: right, "->")
      edge((1, 0), (1, 1), [$q$], label-side: left, "->")
      edge((-1, 1), (0, 1), [$r$], label-side: right, "->")
      edge((0, 0), (1, 0), [$f'$], label-side: left, "->")
      edge((-1, 0), (0, 0), [$r'$], label-side: left, "->")
      edge((0, 0), (0, 1), [$q'$], label-side: right, "->")
      edge((-1, 0), (-1, 1), [$tilde(q')$], label-side: right, "->")
    }))
    where the two squares are Cartesian. Now since $f compose r in cal(S)^((1))$, we have $f' compose r' in cal(S)^((1))$. Also $g compose q in cal(S)^((1))$, and so: 
    $
      g compose f compose r compose tilde(q)' = g compose q compose f' compose r' in cal(S)^((1))
    $
    Hence, $r compose tilde(q'): tilde(X)' -> X$ is a suitable etale cover of $X$ for defining $Tr_(X\/Z)$. $Tr_(X\/Z)$ is the unique map in: 
    $
      Tr_(tilde(X)'\/Z)^((1)) = Tr_(X\/Z) diamond.small Tr^compose_(r compose tilde(q')) = Tr_(X\/Z) diamond.small Tr^compose_(q' compose r') = Tr_(X\/Z) diamond.small Tr^compose_(q') diamond.small Tr^compose_(r')
    $
    Meanwhile: 
    $
      Tr_(tilde(X)'\/Z)^((1)) = Tr_(Y'\/Z)^((1)) diamond.small Tr_(tilde(X)'\/Y')^((1)) = Tr_(Y\/Z) diamond.small Tr^compose_q diamond.small Tr_(X'\/Y') diamond.small Tr^compose_(r')
    $
    Thus it suffices to show that $Tr^compose_q diamond.small Tr_(X'\/Y') diamond.small Tr^compose_(r') = Tr_(X\/Y) diamond.small Tr^compose_(q') diamond.small Tr^compose_(r')$. Now: 
    $
      & Tr^compose_q diamond.small Tr_(X'\/Y') diamond.small Tr^compose_(r') \
      =& Tr^compose_q diamond.small Tr^((1))_(tilde(X)'\/Y') \
      =& Tr^((1))_(tilde(X)\/Y) diamond.small Tr^compose_(tilde(q')) \
      =& Tr_(X\/Y) diamond.small Tr^compose_r diamond.small Tr^compose_(tilde(q')) \
      =& Tr_(X\/Y) diamond.small Tr^compose_(q') diamond.small Tr^compose_(r')
    $
    We are thereby done showing compatibility with composition. 
  
  Thus (0) is verified. 

  (2) This problem is etale local on $X$. Suppose that there is an etale cover ${j_i: U_i -> X}_i$ of $X$ in which each $U_i$ is a smooth curve and $Tr_(U_i\/k) = Tr^tilde_(U_i\/k)$. Then by @pd-trace-etale-curve-compat: 
  $
    Tr^tilde_(X\/k) diamond.small Tr^compose_(U_i\/X) = Tr^tilde_(U_i\/k) = Tr_(U_i\/k) = Tr_(X\/k) diamond.small Tr^compose_(U_i\/X)
  $
  Refining to a finite subcover and taking $U = union.sq.big_i U_i$, we thus see that there exists a surjective etale $U -> X$ s.t:: 
  $
    Tr^tilde_(X\/k) diamond.small Tr^compose_(U\/X) = Tr_(X\/k) diamond.small Tr^compose_(U\/X)
  $
  As we have seen, for surjective etale $U -> X$, $Tr^compose_(U\/X)$ may be cancelled on the right of $diamond.small$'s. Thus $Tr^tilde_(X\/k) = Tr_(X\/k)$. 

  It remains to prove this etale locally on $X$. For any geometric point $ol(x)$ of $X$, pick an etale neighborhood $(U, ol(u)) -> (X, ol(x))$ s.t. $U -> Spec(k)$ is in $cal(S)^((1))$. By taking a connected component of $U$, we may assume that $U$ is a smooth curve. Now take a factorization $U ->^j AA^1_k -> Spec(k)$, and so: 
  $
    Tr_(U\/k) = Tr^((1))_(U\/k) = Tr^square_(AA^1_k\/k) diamond.small Tr^compose_(U\/AA^1_k) = Tr^tilde_(AA^1_k\/k) diamond.small Tr^compose_(U\/AA^1_k) = Tr^tilde_(U\/k)
  $
  by @pd-trace-etale-curve-compat and @pd-trace-curve-affine-compat. We are thereby done. 
]

The trace map can now be extended to arbitrary torsion coefficient rings. 

#definition(name: <defn-tate-twists>)[
  Let $Lambda$ be an $n$-torsion coefficient ring. Then as etale sheaves on some $ZZ[n^(-1)]$-scheme, we define *Tate twists* of $Lambda$ to be: 
  $
    ul(Lambda)(m) = cases(
      Lambda otimes_(ZZ\/n) mu_n^(otimes m) &\, m > 0, 
      Lambda &\, m = 0, 
      Hom_(ZZ\/n) (mu_n^(otimes -m), Lambda) &\, m < 0
    )
  $
  When the underlying scheme is over $ZZ[n^(-1),zeta_n]$ (i.e. has an $n$-th root of unity), this is a sheaf non-canonically isomorphic to $ul(Lambda)$ by an artificial choice of a primitive $n$-th root of unity. 
  
  For any complex $cal(K)$ of etale sheaves of $Lambda$-modules, define its *Tate twists*:
  $
    cal(K)(m) = cal(K) otimes_Lambda ul(Lambda)(m)
  $
  When the underlying scheme is over $ZZ[n^(-1),zeta_n]$ (i.e. has an $n$-th root of unity), they are all non-canonically isomorphic to $cal(K)$ by an artificial choice of a primitive $n$-th root of unity. 
  
  Now monoidal relations give: 
  $
    RHHom_Lambda (cal(K)(m_1), cal(L)(m_2)) = RHHom_Lambda (cal(K), cal(L))(m_2 - m_1) \
    cal(K)(m_1) Lotimes_Lambda cal(L)(m_2) = (cal(K) Lotimes_Lambda cal(L))(m_1 + m_2) \
    f^(-1) (cal(K)(m)) = (f^(-1) cal(K))(m)
  $
  and projections give: 
  $
    R f_! (cal(K)(m)) = (R f_! cal(K))(m) 
  $
  and: 
  $
    R f_* (cal(K)(m)) = (R f_* cal(K))(m)
  $
  (The formula for $R f_*$ is not really automatic. In the case that the underlying scheme $X$ has an $n$-th root of unity, this projection is an isomorphism by the non-canonical isomorphism $ul(Lambda)(m) cong ul(Lambda)$. In the general case, adjoining an $n$-th root of unity to the underlying scheme $X$ gives a finite etale covering, the Kummer covering. Then the projection pulled back along the Kummer covering is an isomorphism, so the projection is an isomorphism by @surjective-pullback-conservative.)

  Hence in an expression involving Tate twists, we always throw the Tate twists to the far right, and suppress from the notation which part of the expression the Tate twist associates to. 
]

#construction(name: <trace-map-with-coefficients>)[
  The trace map just defined is a canonical map: 
  $
    Tr_(X\/Y): R f_! ul(ZZ\/n)(d)[2d] -> ul(ZZ\/n)
  $
  Thus, for any $n$-torsion coefficient ring and any complex $cal(K) in D(Y_et, Lambda)$, applying $- Lotimes_(ZZ\/n) cal(K)$ and the projection formula to the trace map above gives a canonical map: 
  $
    Tr_(X\/Y): R f_! f^(-1) cal(K)(d)[2d] -> cal(K)
  $
  which is also called the *trace map*. This map is also compatible with base change and composition, as inherited from the trace map $R f_! ul(ZZ\/n)(d)[2d] -> ul(ZZ\/n)$. 
]
