#import "void-import.typ": *

== Proof of (Shift)

In this section, we prove (Shift), an intermediate step that allows us to transfer base change results between schemes. The method of this section comes from #cite-stacks("095S")[Section 59.91]. 

#proposition(name: <pbc-seed-precursor-0>)[
  For any noetherian henselian $A$ and proper $f: X -> Spec(A)$ and any torsion $cal(F) in cAb(X_et)$, the natural map on connected components: 
  $
    pi_0 (X_0) -> pi_0 (X)
  $
  is a bijection. 
]
#proof[
  By Stein factorization, $f: X -> Spec(A)$ factors as $f: X ->^g Y ->^h Spec(A)$, where $g$ is surjective with connected fibers and $h$ is finite. Now $f_0$ factors as $f_0: X_0 ->^(g_0) Y_0 ->^(h_0) Spec(k)$, where $g_0$ has connected fibers and $h_0$ is finite. 

  #lemma[
    If $f: X -> Y$ is a surjective closed map with connected fibers between locally connected topological spaces, then $pi_0 (f): pi_0 (X) -> pi_0 (Y)$ is a bijection. 
  ]
  #proof[
    For a connected component $C subset Y$, $f^(-1) (C)$ is open and closed in $X$, hence a disjoint union of connected components of $X$. Replacing $X -> Y$ with $f^(-1) (C) -> C$, we may assume that $Y$ is connected and aim to prove that $X$ is connected. 

    Assume the contrary that $X = X_1 union.sq X_2$ for closed and open $X_1, X_2 subset X$. Since $f$ is closed, $f(X_1), f(X_2) subset Y$ are closed. Since $f$ is surjective, $Y = f(X_1) union f(X_2)$. Had this union been disjoint, $Y$ is the disjoint union of two proper closed and open subsets, a contradiction to the connectivity of $Y$. Thus there exists $y in Y$ s.t. $y in f(X_1) ∩ f(X_2)$. Now by hypothesis, $f^(-1)(y)$ is connected. However, $f^(-1)(y) = (X_1 ∩ f^(-1)(y)) union.sq (X_2 ∩ f^(-1)(y))$ is the disjoint union of two proper open and closed subsets, a contradiction to connectivity of $f^(-1)(y)$. 
  ]

  Thus, $pi_0 (g): pi_0 (X) -> pi_0 (Y)$ and $pi_0 (g_0): pi_0 (X_0) -> pi_0 (Y_0)$ are bijective. Thus it suffices to show that $pi_0 (Y_0) -> pi_0 (Y)$ is bijective. Replacing $X$ with $Y$, we may assume that $X -> Spec(A)$ is finite, i.e. $X = Spec(B)$ for a finite $A$-algebra $B$. By @equiv-defns-of-henselian (1), since $A$ is henselian, $B = B_1 times dots.c times B_m$ is a direct product of finite local $A$-algebras, and $Spec(B) = union.sq.big_(i=1)^m Spec(B_i)$ is a connected-component decomposition. Now $X_0 = Spec(B_0), B_0 = B\/frak(m) B$, and so $B_0 = B_(1,0) times dots.c times B_(m,0)$ where each $B_(i,0) = B_i\/frak(m) B_i$ is a finite local $k$-algebra. Thus $Spec(B_0) = union.sq.big_(i=1)^m Spec(B_(i,0))$ is a connected-component decomposition, with $pi_0 (Spec(B_0)) -> pi_0 (Spec(B))$ sending $Spec(B_(i,0))$ to $Spec(B_i)$. Thus, $pi_0 (X_0) -> pi_0 (X)$ is a bijection in this case, and we are done. 
]

#lemma(name: <pbc-point-deg0>)[
  For any noetherian strict henselian $A$ and proper $X -> Spec(A)$ and any torsion $cal(F) in cAb(X_et)$, the natural restriction: 
  $
    Gamma(X, cal(F)) -> Gamma(X_0, cal(F)|_(X_0))
  $
  is bijective. In other words, proper base change along $X -> Spec(A)$ always holds in degree $0$. 
]
#proof[
  By @pbc-dev-lem3, it suffices to prove when $cal(F) = ul(ZZ\/n)$. Now: 
  $
    Gamma(X, ul(ZZ\/n)) = (ZZ\/n)^(oplus pi_0 (X)), Gamma(X_0, ul(ZZ\/n)) = (ZZ\/n)^(oplus pi_0 (X_0))
  $
  where the natural restriction is induced by the morphism $pi_0 (X_0) -> pi_0 (X)$ on connected components, which is a bijection by @pbc-seed-precursor-0. We are thereby done. 
]

#lemma(name: <pbc-and-injectives-of-ab-zn>)[
  For any noetherian strict henselian $A$ and proper $f: X -> Spec(A)$, TFAE: 
  
  - Base change holds along $X -> Spec(A)$, i.e. for all torsion $cal(F) in cAb(X_et)$, the natural restriction: 
    $
      H^q (X, cal(F)) -> H^q (X_0, cal(F)|_(X_0))
    $
    is bijective. 

  - For any injective object $cal(I) in cAb(X_et, ZZ\/n)$, $H^q (X_0, cal(I)|_(X_0)) = 0$ for $q >= 1$. 
]
#proof[
  ($==>$) is automatic by @etale-zn-sheaves-first-props (3), so it suffices to prove ($<==$). By @pbc-dev-lem1, we may assume that $cal(F)$ is constructible, hence $n$-torsion for some $n>=1$. Now pick an injective resolution: 
  $
    0 -> cal(F) -> cal(I)^bullet
  $
  of $cal(F)$ in $cAb(X_et, ZZ\/n)$. By @etale-zn-sheaves-first-props (3), each $cal(I)^i$ is $Gamma(X, -)$-acyclic, so: 
  $
    H^q (X, cal(F)) = h^q (0 -> Gamma(X, cal(I)^bullet))
  $
  Since pullback is exact, we have an exact sequence in $cAb((X_0)_et)$: 
  $
    0 -> cal(F)|_(X_0) -> cal(I)^bullet|_(X_0)
  $
  By hypothesis, each $cal(I)^bullet|_(X_0)$ is $Gamma(X_0, -)$-acyclic, and so: 
  $
    H^q (X_0, cal(F)|_(X_0)) = h^q (0 -> Gamma(X_0, cal(I)^bullet|_(X_0)))
  $
  The natural restriction $H^q (X, cal(F)) -> H^q (X_0, cal(F)|_(X_0))$ is induced by the restriction maps of cochain complexes $Gamma(X, cal(I)^bullet) -> Gamma(X_0, cal(I)^bullet|_(X_0))$. These maps are termwise isomorphisms by @pbc-point-deg0, and so the natural restriction $H^q (X, cal(F)) -> H^q (X_0, cal(F)|_(X_0))$ is an isomorphism. 
]

#theorem[
  (Shift) In a diagram of successive base changes in which all schemes are noetherian and $A$ is strict henselian with $X', X$ proper over $Spec(A)$:
  // https://q.uiver.app/#r=typst&q=WzAsNixbMCwxLCJYJyJdLFsxLDEsIlgiXSxbMiwxLCJTcGVjKEEpIl0sWzIsMCwiU3BlYyhrKSJdLFsxLDAsIlhfMCJdLFswLDAsIlgnXzAiXSxbMCwxLCJwaSIsMl0sWzEsMl0sWzMsMl0sWzUsNCwicGlfMCJdLFs0LDEsImkiXSxbNSwwLCJpJyIsMl0sWzQsM11d
  #align(center, diagram({
    node((-1, 0), [$X'$])
    node((0, 0), [$X$])
    node((1, 0), [$Spec(A)$])
    node((1, -1), [$Spec(k)$])
    node((0, -1), [$X_0$])
    node((-1, -1), [$X'_0$])
    edge((-1, 0), (0, 0), [$pi$], label-side: right, "->")
    edge((0, 0), (1, 0), "->")
    edge((1, -1), (1, 0), "->")
    edge((-1, -1), (0, -1), [$pi_0$], label-side: left, "->")
    edge((0, -1), (0, 0), [$i$], label-side: left, "->")
    edge((-1, -1), (-1, 0), [$i'$], label-side: right, "->")
    edge((0, -1), (1, -1), "->")
  }))
  We have:
  $
        & BC(pi, i) \
    ==> & (BC_* (X -> Spec(A)) <==> BC_* (X' -> Spec(A)))
  $
  In plain English, if base change holds for the left square, then it holds for the right square if and only if it holds for the large rectangle. 
]
#proof[
  We first prove a technical lemma: 
  #lemma(name: <surjection-has-injective-unit>)[
    If $f: X -> Y$ is surjective, then for all $cal(F) in cAb(Y_et)$, the unit map: 
    $
      eta_(cal(F)): cal(F) -> f_* f^(-1) cal(F)
    $
    is injective. 
  ]
  #proof[
    /*Let $cal(K) = ker(cal(F) -> f_* f^(-1) cal(F))$, and form the exact sequence: 
    $
      0 -> cal(K) -> cal(F) ->^eta f_* f^(-1) cal(F)
    $
    Applying $f^(-1)$, we get an exact sequence: 
    $
      0 -> f^(-1) cal(K) -> f^(-1) cal(F) -->^(f^(-1) eta_(cal(F))) f^(-1) f_* f^(-1) cal(F)
    $
    However, */From category theory, the counit $epsilon_(cal(G)): f^(-1) f_* cal(G) -> cal(G)$ and the unit $eta_(cal(F))$ satisfy an identity: the composition: 
    $
      f^(-1) cal(F) -->^(f^(-1) eta_(cal(F))) f^(-1) f_* f^(-1) cal(F) -->^(epsilon_(f^(-1) cal(F))) f^(-1) cal(F)
    $
    is the identity. In particular, $f^(-1) eta_(cal(F)): f^(-1) cal(F) -> f^(-1) f_* f^(-1) cal(F)$ is injective. Now from @surjective-pullback-conservative, $eta_(cal(F))$ is injective. 
  ]
  By @pbc-and-injectives-of-ab-zn, it suffices to show that for every injective object $cal(I) in cAb(X_et, ZZ\/n)$, $H^q (X_0, cal(I)|_(X_0)) = 0$ for $q >= 1$. Pick an injective map $pi^(-1) cal(I) -> cal(J)$ for an injective object $cal(J) in cAb(X'_et, ZZ\/n)$. Since $pi_*$ is left exact and the unit $cal(I) -> pi_* pi^(-1) cal(I)$ is injective by the previous lemma, the morphism from adjunction: 
  $
    cal(I) -> pi_* pi^(-1) cal(I) -> pi_* cal(J)
  $
  is an injective morphism in $cAb(X_et, ZZ\/n)$. Since $cal(I) in cAb(X_et, ZZ\/n)$ is an injective object, it is a direct summand of $pi_* cal(J)$. Thus, to prove $H^q (X_0, cal(I)|_(X_0)) = 0$ for $q>=1$, it remains to prove $H^q (X_0, pi_* cal(J)|_(X_0)) = 0$. 

  Since $cal(J)$ is $n$-torsion and base change holds for the left square, $pi_* cal(J)|_(X_0) = pi_(0,*) (cal(J)|_(X'_0))$. Thus, we need to show that: 
  $
    H^q (X_0, pi_(0,*) (cal(J)|_(X'_0))) = 0, forall q >= 1
  $
  For any $q >= 1$, 
  $
    R^q pi_(0,*) (cal(J)|_(X'_0)) cong (R^q pi_* cal(J))|_(X_0) = 0
  $
  since base change holds for the left square, and $R^q pi_* cal(J) = 0$ by @etale-zn-sheaves-first-props (3). Thus, the Leray spectral sequence (@derived-lower-star-first-props (2)): 
  $
    H^p (X_0, R^q pi_(0,*) (cal(J)|_(X'_0))) ==> H^(p+q) (X'_0, cal(J)|_(X'_0))
  $
  degenerates, inducing isomorphisms: 
  $
    H^q (X_0, pi_(0,*) (cal(J)|_(X'_0))) cong H^q (X'_0, cal(J)|_(X'_0))
  $
  which is $0$ for $q>=1$ by the second point of @pbc-and-injectives-of-ab-zn, since base change holds for the large rectangle. Thus $H^q (X_0, pi_* cal(J)|_(X_0)) = 0$ for all $q >= 1$ and we are done. 
]
// We give two essentially identical proofs of this result, one phrased using explicit resolutions and complexes, and one phrased in the derived category. The second proof is merely the first one with some details encapsulated in the mechanisms of derived categories. However, I think that we haven't used derived categories up to now, and we probably shouldn't require readers to digress to a hard categorical construction in the middle of a lengthy proof. Therefore, the manual proof will be the main line, and I will write how to abbreviate the long manual proof using derived category vocabulary in nested proof boxes. 

// This proof requires the theory/language of derived categories in an essential way. Readers should read the appendix on derived categories before reading this proof. 

// #proof[
//   ($==>$) is just (Comp) (@pbc-comp), so we only need to prove ($<==$), that if base change holds for the left square and large rectangle, it holds for the right square. 

//   // By @pbc-dev-lem1, it suffices to show that base change holds for all constructible sheaves $cal(F) in cAb(X_et)$. In particular, $cal(F)$ is $n$-torsion for some fixed $n>=1$, so by the acyclic Godement resolution (@acyclic-godement-resolution), there exists a $Gamma(X, -)$-acyclic resolution: 
//   // $
//   //   0 -> cal(F) -> cal(I)^bullet
//   // $
//   // in which every $cal(I)^p$ is $n$-torsion. 
// ]
