#import "void-import.typ": *
== Vanishing theorems in dimension 1

#lemma[
  Let $X$ be a noetherian scheme, and $E subset X$ be a subset closed under specialization. Let $cal(F) in cAb(X_et)$ be a torsion sheaf with $supp(cal(F)) subset E$. Then $cal(F)$ can be written as a directed limit: 
  $
    cal(F) = dirlim_(lambda) cal(F)_lambda
  $
  in which every $cal(F)_lambda$ is a torsion sheaf supported on a closed subset of $E$. 
]
#proof[
  By @constructible-sheaves-first-props (6), $cal(F)$ is the directed limit of its constructible subsheaves ${cal(F)_lambda}$. By @supp-of-constructible-sheaf, each: 
  $
    supp(cal(F)_lambda) subset E
  $
  is a constructible subset of $E$. The closure of a constructible set consists of all points specializing a point in it. Since $E$ is closed under specialization, $ol(supp(cal(F)_lambda)) subset E$, and we are done. 
]

#notation(name: <notation-supp-on-dim-a>)[
  Let $X$ be a finite type scheme over a field $K$. We denote the set of *points of $X$ of dimension $<=a$* by: 
  $
    E_a (X) := {x in X : dim(ol({x})) <= a}
  $
  
  For $cal(F) in cAb(X_et)$, we say that it is *supported on dimension $<=a$*, if $supp(cal(F)) subset E_a (X)$. 
]

#corollary(name: <supp-of-torsion-sheaf-dim>)[
  Let $X$ be a finite type scheme over a field $K$, and $cal(F) in cAb(X_et)$ be a torsion sheaf supported on dimension $<=a$. Then $cal(F)$ can be written as a directed limit: 
  $
    cal(F) = dirlim_(lambda) cal(F)_lambda
  $
  in which every $cal(F)_lambda$ is a torsion sheaf supported on a closed subscheme of $X$ of dimension $<=a$. 
]
#proof[
  Taking $E = E_a (X)$ in the previous lemma concludes the proof. 
]

#corollary(name: <supp-of-torsion-sheaf-dim-0>)[
  Let $X$ be a finite type scheme over a separably closed field $k$, and $cal(F) in cAb(X_et)$ be a torsion sheaf supported on dimension $<=0$. Then for all $q >= 1$, 
  $
    H^q (X_et, cal(F)) = 0
  $
]
#proof[
  By @supp-of-torsion-sheaf-dim, 
  $
    cal(F) = dirlim_lambda cal(F)_lambda
  $
  in which every $supp(cal(F)_lambda) subset Z$ for a dimension $0$ subscheme of $X$, i.e. a finite set of closed points. By @pushforward-by-closed-immersion (1), @pushforward-by-finite-morphism and @struct-of-spec-omega-et, 
  $
    H^q (X, cal(F)_lambda) = 0, forall q>=1
  $
  We may conclude the proof by the limit formula @limit-formula-for-sheaves. 
]

#proposition(name: <grothendieck-vanishing-for-curves>)[
  Let $X$ be any curve over a separably closed field $k$, and $cal(F) in cAb(X_et)$ be a torsion sheaf. Then for all $q >= 3$, 
  $
    H^q (X, cal(F)) = 0
  $
]
#proof[
  By topological invariance, since $ol(k)\/k$ is a purely inseparable extension, we may base change to $ol(k)$ and assume that $k$ is algebraically closed. 

  Let $j: eta = Spec(K(X)) -> X$ be the inclusion of the generic point. Consider the natural morphism: 
  $
    gamma: cal(F) -> j_* j^(-1) cal(F)
  $
  We claim that $gamma$ is an isomorphism on stalks at $ol(eta)$. Indeed, $tilde(X)_(ol(eta)) = Spec(cal(O)_(X,eta)^#[sh]) = Spec(K(X)^#[sh]) = Spec(K(X)^sep) = ol(eta)$, and so: 
  $
    (R^q j_* j^(-1) cal(F))_(ol(eta)) = H^q (eta times_X ol(eta), j^(-1) cal(F)|_(eta times_X ol(eta))) = H^q (ol(eta), cal(F)_(ol(eta))) = cases(
      cal(F)_(ol(eta)) &\, q = 0, 
      0 &\, q >= 1
    )
  $
  In other words, $ker(gamma)_(ol(eta)) = coker(gamma)_(ol(eta)) = 0$, and $(R^q j_* j^(-1) cal(F))_(ol(eta)) = 0$ for $q >= 1$. By @supp-of-torsion-sheaf-dim-0, 
  $
    H^p (X, ker(gamma)) = H^p (X, coker(gamma)) = 0, forall p >= 1 \
    H^p (X, R^q j_* j^(-1) cal(F)) = 0, forall p >= 1
  $
  Since $H^p (X, ker(gamma)) = H^p (X, coker(gamma)) = 0, forall p >= 1$, using short exact sequences, we see that for all $p >= 2$, 
  $
    H^p (X, cal(F)) cong H^p (X, im(gamma)) cong H^p (X, j_* j^(-1) cal(F))
  $
  and so it suffices to show for $p >= 3$, $H^p (X, j_* j^(-1) cal(F)) = 0$. For this, we use the Leray spectral sequence @derived-lower-star-first-props (2): 
  $
    E_2^(p,q) = H^p (X, R^q j_* j^(-1) cal(F)) ==> H^(p+q) (eta, j^(-1) cal(F)) 
  $
  Now for $q >= 2$ and $x in abs(X)$, 
  $
    (R^q j_* j^(-1) cal(F))_x = H^q (eta times_X tilde(X)_x, cal(F)|_(eta times_X tilde(X)_x))
  $
  As in the proof of @gm-generic-pushforward-higher-vanishing, $eta times_X tilde(X)_x = Spec(L)$, where $L$ is an extension field of $k$ of transcendence degree $1$. Thus, this cohomology is $H^q_#[cont] (Gal_L, -)$ applied to a discrete torsion $Gal_L$-module, since $cal(F)$ is torsion. By @tsen-thm-in-galois-cohom (1), a consequence of Tsen's theorem, this cohomology vanishes. Thus, $(R^q j_* j^(-1) cal(F))_x = 0$. Hence $R^q j_* j^(-1) cal(F) = 0$ for all $q >= 2$. 
  
  We also have proved $H^p (X, R^1 j_* j^(-1) cal(F)) = 0$ for $p >= 1$. Thus, in the Leray spectral sequence: 
  $
    E_2^(p,q) = H^p (X, R^q j_* j^(-1) cal(F)) ==> H^(p+q) (eta, j^(-1) cal(F)) 
  $
  the only nonzero terms on the $E_2$-page are $E_2^(p,0)$ and $E_2^(0,1)$. The only surviving differential is $d_2: E_2^(0,1) -> E_2^(2,0)$, and the spectral sequence stabilizes on the $E_3$-page. Thus for all $p >= 3$, this spectral sequence induces an isomorphism: 
  $
    H^p (X, j_* j^(-1) cal(F)) = H^p (eta, j^(-1) cal(F))
  $
  which vanishes by @tsen-thm-in-galois-cohom (1), as a consequence of Tsen's theorem, where $eta = Spec(K(X))$ is the spectrum of a transcendence degree 1 extension of $k$, and $j^(-1) cal(F)$ is a torsion $Gal_(K(X))$-module as $cal(F)$ is a torsion sheaf. 

  Thus, we have shown for $p >= 3$, 
  $
    H^p (X, cal(F)) cong H^p (X, j_* j^(-1) cal(F)) cong H^p (eta, j^(-1) cal(F)) = 0
  $
  and we are done. 
]

We are now ready to prove Grothendieck vanishing in dimension 1. 

#theorem(name: <grothendieck-vanishing-in-dim-1>)[
  Let $X$ be any finite type scheme of dimension $<=1$ over a separably closed field $k$, and $cal(F) in cAb(X_et)$ be a torsion sheaf. Then for all $q >= 3$, 
  $
    H^q (X, cal(F)) = 0
  $
]
#proof[
  We run induction on the number of irreducible components of $X$. 

  Suppose that $X$ is irreducible. By topological invariance, we may replace $X$ by its reduction and assume that $X$ is integral. Then $X$ is either a point $Spec(k)$ or a curve. The case of a point is done by @struct-of-spec-omega-et, and the case of a curve is done by the previous proposition. 

  For the inductive step, suppose that the theorem holds for all $X$ with $<n$ irreducible components, and $X$ has $n$ irreducible components. Let $Z$ be an irreducible component of $X$ equipped with reduced induced subscheme structure, and $U = X - Z$ its complement, with $n-1$ irreducible components. Let $i: Z -> X, j: U -> X$ be the inclusions. By @etale-lower-shriek-first-props (3), we have a short exact sequence: 
  $
    0 -> j_! j^(-1) cal(F) -> cal(F) -> i_* i^(-1) cal(F) -> 0
  $
  Now for $q >= 3$: 

  - $H^q (X, i_* i^(-1) cal(F)) = H^q (Z, i^(-1) cal(F)) = 0$ by the irreducible case; 

  - $supp(j_! j^(-1) cal(F)) subset U subset Y := ol(U)$. $Y$ has $n-1$ irreducible components, and we equip it with the reduced induced subscheme structure and consider the inclusion $h: Y -> X$. 

    Then $j_! j^(-1) cal(F) = h_* cal(G)$ for some $cal(G) in cAb(Y_et)$. For any $ol(y) in Y_et$, $cal(G)_(ol(y)) = (h_* cal(G))_(ol(y)) = (j_! j^(-1) cal(F))_(ol(y))$ is torsion, and so $cal(G)$ is a torsion sheaf by @torsion-sheaves-first-props. As such, 
    $
      H^q (X, j_! j^(-1) cal(F)) = H^q (Y, cal(G)) = 0
    $
    by the case of $n-1$ irreducible components. 

  Using the long exact sequence, $H^q (X, cal(F)) = 0$ for all $q >= 3$, and we are done. 
]

Next, we deal with Artin vanishing in dimension 1. 

#proposition(name: <artin-vanishing-of-zn>)[
  Let $X$ be any finite type affine scheme of dimension $<=1$ over a separably closed field $k$. Then for all $q >= 2$ and all $n >= 1$, 
  $
    H^q (X, ul(ZZ\/n)) = 0
  $
]
#proof[
  Vanishing for $q >= 3$ is given by @grothendieck-vanishing-in-dim-1, so it suffices to deal with vanishing for $q = 2$. 

  By topological invariance, since $ol(k)\/k$ is a purely inseparable extension, we may base change to $ol(k)$ and assume that $k$ is algebraically closed. We have proved this proposition for $X$ an affine smooth curve in @h2-zn-of-affine-smooth-curve. Next, when $X$ is an arbitrary affine curve, we take its normalization: 
  $
    nu: tilde(X) -> X
  $
  which is a finite map. Consider the canonical map: 
  $
    ul(ZZ\/n)_X -> nu_* ul(ZZ\/n)_(tilde(X))
  $
  Since there exists a dense open $U subset X$ s.t. $nu: nu^(-1) (U) -> U$ is an isomorphism, $ul(ZZ\/n)_X -> nu_* ul(ZZ\/n)_(tilde(X))$ is an isomorphism when restricted to $U$. Hence, its kernel and cokernel are supported on finitely many closed points, and so are acyclic.#footnote[This morphism should be injective, but we do not need this here.] Thus, using short exact sequences, 
  $
    H^2 (X, ul(ZZ\/n)) = H^2 (X, im(ul(ZZ\/n)_X -> nu_* ul(ZZ\/n)_(tilde(X)))) = H^2 (X, nu_* ul(ZZ\/n)_(tilde(X))) = H^2 (tilde(X), ul(ZZ\/n))
  $
  where the last step is due to @pushforward-by-finite-morphism. Now $tilde(X)$ is a smooth affine curve, so this cohomology vanishes and we are done. 

  Finally, for $X$ a general finite type affine scheme of dimension $<=1$ over $k$, let $Z_1, dots.c, Z_m$ be its irreducible components, equipped with the reduced induced subscheme structure. Thus, each $Z_i$ is either a curve or a point $Spec(k)$, and so $H^q (Z_i, ul(ZZ\/n)) = 0$ as proved above. Let $h_i: Z_i -> X$ be the closed immersions, and let $h: Z := union.sq.big_(i=1)^m Z_i -> X$ be the disjoint union, a finite map. Consider the canonical map: 
  $
    ul(ZZ\/n)_X -> h_* ul(ZZ\/n)_Z
  $
  The set of points in $X$ contained in exactly one irreducible component forms a dense open $U$, s.t. $h^(-1) (U) -> U$ is an isomorphism. As such, $ul(ZZ\/n)_X -> h_* ul(ZZ\/n)_Z$ is an isomorphism upon restriction to $U$, and its kernel and cokernel are supported on finitely many closed points.#footnote[This morphism should also be injective, but we do not need this here.] Similarly, 
  $
    H^2 (X, ul(ZZ\/n)) = H^2 (Z, ul(ZZ\/n)) = oplus.big_(i=1)^m H^2 (Z_i, ul(ZZ\/n)) = 0
  $
  and we are done. 
]

#theorem(name: <artin-vanishing-in-dim-1>)[
  Let $X$ be any finite type affine scheme of dimension $<=1$ over a separably closed field $k$, and $cal(F) in cAb(X_et)$ be a torsion sheaf. Then for all $q >= 2$,  
  $
    H^q (X, cal(F)) = 0
  $
]
#proof[
  The case $q >= 3$ is dealt with in @grothendieck-vanishing-in-dim-1, so we may take $q = 2$. 

  By the same induction on the number of irreducible components as in the proof of @grothendieck-vanishing-in-dim-1, we may assume that $X$ is irreducible. By replacing $X$ with its reduction according to topological invariance, we may assume that $X$ is integral, i.e. a curve. By the limit formula @limit-formula-for-sheaves, and constructible sheaf devissage @constructible-sheaves-first-props (6), we may assume that $cal(F)$ is a constructible sheaf. 

  By @constructible-sheaves-first-props (2), there exists a dense open $j: U -> X$ s.t. $cal(F)|_U$ is l.c.c. Take the complement $i: Z -> X$ where $Z$ is a finite set of closed points with reduced induced subscheme structure. Now in the exact sequence from @etale-lower-shriek-first-props (3): 
  $
    0 -> j_! (cal(F)|_U) -> cal(F) -> i_* (cal(F)|_Z) -> 0
  $
  we have $H^2 (X, i_* (cal(F)|_Z)) = H^2 (Z, cal(F)|_Z) = 0$. As such, it suffices to prove $H^2 (X, j_! (cal(F)|_U)) = 0$ to obtain the desired vanishing. 

  Since $cal(F)|_U = j^(-1) cal(F)$ is l.c.c, we may pick a finite etale covering $pi: V -> U$ s.t. $pi^(-1) j^(-1) cal(F) cong ul(G)_V$ where $G$ is a finite group. 

  #lemma[
    Let $f: X -> Y$ be surjective etale. Then the canonical morphism: 
    $
      f_! f^(-1) cal(F) -> cal(F)
    $
    given by the adjunction counit is surjective. 
  ]
  #proof[
    The adjunction unit and counit: 
    $
      epsilon_(cal(F)): f_! f^(-1) cal(F) -> cal(F) \
      eta_(cal(G)): cal(G) -> f^(-1) f_! cal(G)
    $
    satisfy an identity: the composition: 
    $
      f^(-1) cal(F) ->^(eta_(f^(-1) cal(F))) f^(-1) f_! f^(-1) cal(F) ->^(f^(-1) epsilon_(cal(F))) f^(-1) cal(F)
    $
    is the identity morphism. Thus, $f^(-1) epsilon_(cal(F))$ is surjective, and by @surjective-pullback-conservative, $epsilon_(cal(F))$ is surjective. 
  ]
  Thus, we have a surjective morphism: 
  $
    pi_* ul(G)_V = pi_* pi^(-1) j^(-1) cal(F) ->> j^(-1) cal(F)
  $
  Since $j_!$ is exact, we have a surjective morphism $j_! pi_* ul(G)_V -> j_! j^(-1) cal(F)$. Forming its kernel, we have a short exact sequence: 
  $
    0 -> cal(K) -> j_! pi_* ul(G)_V -> j_! j^(-1) cal(F) -> 0
  $
  inducing a long exact sequence: 
  $
    dots.c -> H^2 (X, j_! pi_* ul(G)_V) -> H^2 (X, j_! j^(-1) cal(F)) -> underbrace(H^3 (X, cal(K)), #[$0$ by @grothendieck-vanishing-in-dim-1]) -> dots.c
  $
  and so it suffices to prove that $H^2 (X, j_! pi_* ul(G)_V) = 0$. Now $j compose pi: V -> X$ is quasi-finite separated, so by Zariski's main theorem, we may factor it as: 
  // https://q.uiver.app/#r=typst&q=WzAsNCxbMCwwLCJWIl0sWzEsMSwiWCJdLFswLDEsIlUiXSxbMSwwLCJXIl0sWzIsMSwiaiIsMl0sWzAsMiwicGkiLDJdLFswLDMsImpfMSJdLFszLDEsInBpXzEiXV0=
  #align(center, diagram({
    node((-1, -1), [$V$])
    node((0, 0), [$X$])
    node((-1, 0), [$U$])
    node((0, -1), [$W$])
    edge((-1, 0), (0, 0), [$j$], label-side: right, "->")
    edge((-1, -1), (-1, 0), [$pi$], label-side: right, "->")
    edge((-1, -1), (0, -1), [$h$], label-side: left, "->")
    edge((0, -1), (0, 0), [$pi.alt$], label-side: left, "->")
  }))
  where $pi.alt$ is finite and $h$ is an open immersion. We claim that $j_! pi_* ul(G)_V cong pi.alt_* h_! ul(G)_V$. Indeed, a natural map $j_! pi_* ul(G)_V -> pi.alt_* h_! ul(G)_V$ may be constructed from adjunction and base change, and that it is an isomorphism can be checked on stalks according to @stalks-of-finite-pushforward and @etale-lower-shriek-first-props (2). Thus, it suffices to prove that: 
  $
    H^2 (X, j_! pi_* ul(G)_V) = H^2 (X, pi.alt_* h_! ul(G)_V) = H^2 (W, h_! ul(G)_V)
  $
  vanishes. 

  Taking $Z$ to be the schematic image of $h: V -> W$, $h$ may be factored as: 
  $
    h: V ->^g Z ->^i W
  $ 
  In which $g$ is a dominant open immersion and $i$ is a closed immersion. Now $h_! ul(G)_V = i_* g_! ul(G)_V$, as a natural map may be constructed from base change and adjunction, and it can be checked to be an isomorphism by taking stalks according to @stalks-of-finite-pushforward and @etale-lower-shriek-first-props (2). 
  
  Thus, $H^2 (W, h_! ul(G)_V) = H^2 (W, i_* g_! ul(G)_V) = H^2 (Z, g_! ul(G)_V)$. 

  Now take $g': Y := Z - V -> Z$ be the complementary closed immersion, where $Y$ is given the reduced induced subscheme structure. Since $V subset Z$ is a dense open, $Y$ is a finite set of closed points. Now consider the exact sequence: 
  $
    0 -> g_! ul(G)_V -> ul(G)_Z -> g'_* ul(G)_Y -> 0
  $
  inducing a long exact sequence: 
  $
    dots.c -> H^1 (Z, g'_* ul(G)_Y) -> H^2 (Z, g_! ul(G)_V) -> H^2 (Z, ul(G)_Z) -> dots.c
  $
  Now: 

  - $H^1 (Z, g'_* ul(G)_Y) = H^1 (Y, ul(G)_Y)$ since $Y$ is a finite set of closed points; 

  - $H^2 (Z, ul(G)_Z) = 0$ by @artin-vanishing-of-zn, since $G$ is a finite abelian group, and $Z ->^i W ->^(pi.alt) X$ is finite, making $Z$ a finite type affine scheme over $k$ of dimension $<=1$. 

  As such, $H^2 (Z, g_! ul(G)_V) = 0$, and we are done. 
]
