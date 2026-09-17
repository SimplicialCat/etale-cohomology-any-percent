#import "void-import.typ": *

== Local acyclicity

With the reductions of last section in mind, we are now ready to introduce local acyclicity. The notion of local acyclicity represents a certain compatibility between special and generic fibers of a morphism, and is the correct compatibility condition required for the relative base change map (w.r.t. a certain complex $cal(L)$) to be universally an isomorphism. 

#definition(name: <defn-local-acyclicity>)[
  Given a morphism of schemes $f: X -> S$ with geometric points $ol(x)$ of $X$ and $ol(s) = f(ol(x))$, and a geometric point $ol(t)$ of $tilde(S)_(ol(s))$ (i.e. a generalization of $ol(s)$), we define the *vanishing cycle variety* to be: 
  $
    F_(ol(x),ol(t)) := ol(t) times_(tilde(S)_(ol(s))) tilde(X)_(ol(x))
  $
  Since $tilde(X)_(ol(x))$ is strict henselian, $Gamma(tilde(X)_(ol(x)), -)$ is exact and isomorphic to $(-)_(ol(x))$. Thus $R Gamma(tilde(X)_(ol(x)), -) = (-)_(ol(x))$, and so for any complex $cal(K) in D^+ (X_et, Lambda)$, there exists a restriction morphism: 

  $
    alpha_(cal(K),ol(x),ol(t)): cal(K)_(ol(x)) -> R Gamma(F_(ol(x),ol(t)), cal(K)|_(F_(ol(x),ol(t))))
  $
  Denote: 

  - $f$ is *locally acyclic at $ol(x)$ relative to $cal(K)$*, if for any geometric point $ol(t)$ of $tilde(S)_(ol(s))$, $alpha_(cal(K),ol(x),ol(t))$ is an isomorphism. 

  - $f$ is *locally acyclic relative to $cal(K)$* if it is locally acyclic at every geometric point relative to $cal(K)$, and *locally acyclic* if for every natural number $n in cal(O)_S^times$, $f$ is locally acyclic relative to $ul(ZZ\/n)$. 

  - $f$ is *universally locally acyclic (relative to $cal(K)$)*, if every base change $f': X' -> S'$ along $g: S' -> S$ is locally acyclic (relative to $g^(-1) cal(K)$). 

  Note that: 
  
  // - By @bc-along-extension-of-sep-cl-fields, whenever $cal(K) in D^+_(#[tor]\/S) (X_et, Lambda)$, the property that $alpha_(cal(K),ol(x),ol(t))$ is independent from the choice of different geometric points $ol(t)$ above the same point of $tilde(S)_(ol(s))$. Thus, when checking local acyclicity for such complexes, we may assume that $ol(t)$ is an algebraic geometric point. 

  - Local acyclicity depends only on the map $tilde(X)_(ol(x)) -> tilde(S)_(ol(s))$. It is thus in particular an etale-local property, and is also independent of the choice of geometric point $ol(x)$ above a point $x in X$. 
]

Local acyclicity is a sort of compatibility condition between the cohomology of $cal(K)$ on the generic and special fibers, as illustrated in the following proposition. 

#proposition(name: <loc-acyc-alt-desc>)[
  For a morphism $f: X -> S$ and $cal(K) in D^+ (X_et, Lambda)$. For a geometric point $ol(s)$ of $S$, TFAE: 

  + $f: X -> S$ is locally acyclic w.r.t. $cal(K)$ at every geometric point of $X_(ol(s))$; 

  + For $ol(t)$ any geometric point of $tilde(S)_(ol(s))$, Form the Cartesian diagram: #h(1fr)
    // https://q.uiver.app/#r=typst&q=WzAsNixbMCwwLCJYXyhvbCh0KSkiXSxbMSwwLCJYIHRpbWVzX1MgdGlsZGUoUylfKG9sKHMpKSJdLFsyLDAsIlhfKG9sKHMpKSJdLFsyLDEsIm9sKHMpIl0sWzEsMSwidGlsZGUoUylfKG9sKHMpKSJdLFswLDEsIm9sKHQpIl0sWzUsNCwiaiIsMl0sWzMsNCwiaSJdLFsyLDMsImZfKG9sKHMpKSJdLFsxLDQsInRpbGRlKGYpIl0sWzAsNSwiZl8ob2wodCkpIiwyXSxbMiwxLCJpJyIsMl0sWzAsMSwiaiciXV0=
    #align(center, diagram({
      node((0, 0), [$X_(ol(t))$])
      node((1, 0), [$X times_S tilde(S)_(ol(s))$])
      node((2, 0), [$X_(ol(s))$])
      node((2, 1), [$ol(s)$])
      node((1, 1), [$tilde(S)_(ol(s))$])
      node((0, 1), [$ol(t)$])
      edge((0, 1), (1, 1), [$j$], label-side: right, "->")
      edge((2, 1), (1, 1), [$i$], label-side: left, "->")
      edge((2, 0), (2, 1), [$f_(ol(s))$], label-side: left, "->")
      edge((1, 0), (1, 1), [$tilde(f)$], label-side: left, "->")
      edge((0, 0), (0, 1), [$f_(ol(t))$], label-side: right, "->")
      edge((2, 0), (1, 0), [$i'$], label-side: right, "->")
      edge((0, 0), (1, 0), [$j'$], label-side: left, "->")
    }))
    and $tilde(cal(K)) = cal(K)|_(X times_S tilde(S)_(ol(s)))$. Then the unit:
    $
      i'^(-1) tilde(cal(K)) -> i'^(-1) R j'_* j'^(-1) tilde(cal(K))
    $
    is an isomorphism. 
]
#proof[
  We devise an equivalent formulation of condition (2). Passing to the stalk at any geometric point $ol(x)$ of $X_(ol(s))$ (which is also a geometric point of $X$), the unit map then becomes: 
  $
    cal(K)_(ol(x)) -> (R j'_* j'^(-1) tilde(cal(K)))_(i'(ol(x))) cong R Gamma(X_(ol(t)) times_(X times_S tilde(S)_(ol(s))) (X times_S tilde(S)_(ol(s)))^tilde_(i'(ol(x))), tilde(cal(K))|_(X_(ol(t)) times_(X times_S tilde(S)_(ol(s))) (X times_S tilde(S)_(ol(s)))^tilde_(i'(ol(x)))))
  $
  Note that: 
  $
    X_(ol(t)) times_(X times_S tilde(S)_(ol(s))) (X times_S tilde(S)_(ol(s)))^tilde_(i'(ol(x))) = ol(t) times_(tilde(S)_(ol(s))) (X times_S tilde(S)_(ol(s)))^tilde_(i'(ol(x)))
  $
  We claim that the canonical map $(X times_S tilde(S)_(ol(s)))^tilde_(i'(ol(x))) -> tilde(X)_(ol(x))$ defined by the projection $X times_S tilde(S)_(ol(s)) -> X$ is an isomorphism. 

  - Indeed, this is showing that: #h(1fr)
    $
      cal(O)_(X,x)^#[sh] cong (cal(O)_(X,x) otimes_(cal(O)_(S,s)) cal(O)_(S,s)^#[sh])^#[sh]_(ker(cal(O)_(X,x) otimes_(cal(O)_(S,s)) cal(O)_(S,s)^#[sh] -> k(ol(x))))
    $
    Since $cal(O)_(S,s)^#[sh]$ is a filtered colimit of quasi-finite $cal(O)_(S,s)$-algebras, @strict-henselizations-tensors-and-qfinites may be invoked, and RHS is just $cal(O)_(X,x)^#[sh] otimes_(cal(O)_(S,s)^#[sh]) cal(O)_(S,s)^#[sh] cong cal(O)_(X,x)^#[sh]$. 
    

  In summary, the unit map in question becomes: 
  $
    cal(K)_(ol(x)) = R Gamma(tilde(X)_(ol(x)), cal(K)|_(tilde(X)_(ol(x)))) -> R Gamma(ol(t) times_(tilde(S)_(ol(s))) tilde(X)_(ol(x)), cal(K)|_(ol(t) times_(tilde(S)_(ol(s))) tilde(X)_(ol(x))))
  $
  the restriction map. There is a canonical map of geometric points $f(ol(x)) -> ol(s)$, inducing a canonical isomorphism $tilde(S)_(ol(s)) cong tilde(S)_(f(ol(x)))$. Under this isomorphism, the restriction map above is: 
  $
    cal(K)_(ol(x)) = R Gamma(tilde(X)_(ol(x)), cal(K)|_(tilde(X)_(ol(x)))) -> R Gamma(F_(ol(x),ol(t)), cal(K)|_(F_(ol(x),ol(t))))
  $
  for the vanishing cycle variety $F_(ol(x),ol(t))$. This is just the map $alpha_(cal(K),ol(x),ol(t))$ in the definition of local acyclicity. 
  
  Thus, by checking stalks, condition (2) is equivalent to the statement: 

  - For any geometric point $ol(x)$ of $X_(ol(s))$ and any geometric point $ol(t)$ of $tilde(S)_(f(ol(x)))$, #h(1fr)
    $
      alpha_(cal(K),ol(x),ol(t)): cal(K)_(ol(x)) = R Gamma(tilde(X)_(ol(x)), cal(K)|_(tilde(X)_(ol(x)))) -> R Gamma(F_(ol(x),ol(t)), cal(K)|_(F_(ol(x),ol(t))))
    $
    is an isomorphism. 

  This is by definition local acyclicity at every geometric point $ol(x)$ of $X_(ol(s))$, i.e. condition (1). 
]

We are now ready to establish the relation between local acyclicity and base change. 

#theorem(name: <loc-acyc-and-base-change>)[
  Let $Lambda$ be a torsion noetherian ring. Let $g: S' -> S$ be a morphism with $S$ noetherian, and $cal(L)_S in D^b_#[ctf] (S'_et, Lambda)$. 
  
  Then among the following statements, (1)$==>$(2)$==>$(3), and (3)$==>$(1) whenever every finite $Lambda$-module embeds into a finite free $Lambda$-module. 

  + For every morphism $f: X -> Y$ of qcqs $S$-schemes, base change to the following Cartesian square: 
    $
      // http://q.uiver.app/#r=typst&q=WzAsNCxbMCwwLCJYJyJdLFsxLDAsIlknIl0sWzAsMSwiWCJdLFsxLDEsIlkiXSxbMiwzLCJmIiwyXSxbMCwxLCJmJyJdLFsxLDMsImciXSxbMCwyLCJnJyIsMl1d
      #align(center, diagram({
        node((0, 0), [$X'$])
        node((1, 0), [$Y'$])
        node((0, 1), [$X$])
        node((1, 1), [$Y$])
        node((0.3, 0.3), $cart$)
        edge((0, 1), (1, 1), [$f$], label-side: right, "->")
        edge((0, 0), (1, 0), [$f'$], label-side: left, "->")
        edge((1, 0), (1, 1), [$g_Y$], label-side: left, "->")
        edge((0, 0), (0, 1), [$g_X$], label-side: right, "->")
      }))
    $
    and put $cal(L)_X = cal(L)_S|_(X')$ and $cal(L)_Y = cal(L)_S|_(Y')$. Then the relative base change map: 
    $
      g_Y^(-1) R f_* cal(K) Lotimes_Lambda cal(L)_Y -> R f'_* (g_X^(-1) cal(K) Lotimes_Lambda cal(L)_X)
    $
    is an isomorphism for all $cal(K) in D^+ (X_et, Lambda)$. 

  + $g$ is universally locally acyclic relative to $cal(L)_S$. 

  + Let $X$ be any $S$-scheme that is the normalization of a finite type $S$-scheme in the algebraic closure of its function field with generic point $xi$. Then the base change $g_X: X' -> X$ and $cal(L)_X = cal(L)_S|_(X')$ satisfies that: 

    - For a very dense subset $E subset X'$ and a family of geometric points ${ol(x')}$ above each point of $E$, the map: 
      $
        alpha_(ol(x'),xi): (cal(L)_X)_(ol(x')) -> R Gamma(F_(ol(x'),xi), cal(L)_X|_(F_(ol(x'),xi)))
      $
      is an isomorphism. 

    In particular, this hypothesis holds if $g_X$ is locally acyclic relative to $cal(L)_X$. 
]
#proof[
  (1)$==>$(2): Suppose that we can show that $g$ is locally acyclic from (1). Note that condition (1) is preserved under qcqs base change. Thus, for every qcqs morphism $X -> S$, the base change $g_X: X' -> X$ is locally acyclic relative to $cal(L)_X$. Now let $h: X -> S$ be an arbitrary morphism. To show that $g_X: X' -> X$ is locally acyclic relative to $cal(L)_X$, we may use etale locality of local acyclicity: it suffices to show that for any affine open $U subset X$, $g_U: U' -> U$ is locally acyclic relative to $cal(L)_U$. But this has already been proved, since $U -> S$ is qcqs. 

  Thus, it suffices to prove that $g$ is locally acyclic. 

  #lemma[
    For a Cartesian diagram, 
    $
      // http://localhost:8000/#r=typst&q=WzAsNCxbMCwwLCJYJyJdLFsxLDAsIlknIl0sWzAsMSwiWCJdLFsxLDEsIlkiXSxbMiwzLCJmIiwyXSxbMCwxLCJmJyJdLFsxLDMsImciXSxbMCwyLCJnJyIsMl1d
      #align(center, diagram({
        node((0, 0), [$X'$])
        node((1, 0), [$Y'$])
        node((0, 1), [$X$])
        node((1, 1), [$Y$])
        node((0.3, 0.3), $cart$)
        edge((0, 1), (1, 1), [$f$], label-side: right, "->")
        edge((0, 0), (1, 0), [$f'$], label-side: left, "->")
        edge((1, 0), (1, 1), [$g$], label-side: left, "->")
        edge((0, 0), (0, 1), [$g'$], label-side: right, "->")
      }))
    $
    and $cal(L) in D(Y'_et, Lambda)$, the unit map $cal(L) -> R f'_* f'^(-1) cal(L)$ is the composition: 
    $
      cal(L) cong g^(-1) ul(Lambda) Lotimes_Lambda cal(L) -> g^(-1) R f_* ul(Lambda) Lotimes_Lambda cal(L) -> R f'_* (g'^(-1) ul(Lambda) Lotimes_Lambda f'^(-1) cal(L)) cong R f'_* f'^(-1) cal(L)
    $
    where the first map is a unit and the second map is a relative base change. 
  ]
  #proof[
    Under adjunction, this map is: 
    $
      f'^(-1) cal(L) cong g'^(-1) f^(-1) ul(Lambda) Lotimes_Lambda f'^(-1) cal(L) cong g'^(-1) ul(Lambda) Lotimes_Lambda f'^(-1) cal(L) cong f'^(-1) cal(L)
    $
    in which every step is the identity. We are thereby done. 
  ]

  We now prove local acyclicity. Let $ol(s)$ be any algebraic geometric point of $S$, and $ol(t)$ be any algebraic geometric point of $tilde(S)_(ol(s))$. Form the Cartesian diagram: 
  #align(center, diagram({
    node((0, 0), [$S'_(ol(t))$])
    node((1, 0), [$S' times_S tilde(S)_(ol(s))$])
    node((2, 0), [$S'_(ol(s))$])
    node((2, 1), [$ol(s)$])
    node((1, 1), [$tilde(S)_(ol(s))$])
    node((0, 1), [$ol(t)$])
    edge((0, 1), (1, 1), [$j$], label-side: right, "->")
    edge((2, 1), (1, 1), [$i$], label-side: left, "->")
    edge((2, 0), (2, 1), [$g_(ol(s))$], label-side: left, "->")
    edge((1, 0), (1, 1), [$tilde(g)$], label-side: left, "->")
    edge((0, 0), (0, 1), [$g_(ol(t))$], label-side: right, "->")
    edge((2, 0), (1, 0), [$i'$], label-side: right, "->")
    edge((0, 0), (1, 0), [$j'$], label-side: left, "->")
  }))
  and $tilde(cal(L)) = cal(L)_S|_(S' times_S tilde(S)_(ol(s)))$. By the previous lemma, the unit:
  $
    tilde(cal(L)) -> R j'_* j'^(-1) tilde(cal(L))
  $
  factors as: 
  $
    tilde(cal(L)) cong tilde(g)^(-1) ul(Lambda) Lotimes_Lambda tilde(cal(L)) -> tilde(g)^(-1) R j_* ul(Lambda) Lotimes_Lambda tilde(cal(L)) -> R j'_* (g_(ol(t))^(-1) ul(Lambda) Lotimes_Lambda j'^(-1) tilde(cal(L))) cong R j'_* j'^(-1) tilde(cal(L)) 
  $
  Now $ol(t) -> tilde(S)_(ol(s))$ is a morphism between qcqs schemes, so the second map, being a relative base change along the left square w.r.t. $cal(L)|_(S' times_S tilde(S)_(ol(s)))$ is an isomorphism. Thus, to prove that: 
  $
    i'^(-1) tilde(cal(L)) -> i'^(-1) R j'_* j'^(-1) tilde(cal(L))
  $
  is an isomorphism, it suffices to prove that $tilde(g)^(-1) ul(Lambda) Lotimes_Lambda tilde(cal(L)) -> tilde(g)^(-1) R j_* ul(Lambda) Lotimes_Lambda tilde(cal(L))$ is an isomorphism upon pulling back along $i'^(-1)$. That is, we need to show that: 
  $
    g_(ol(s))^(-1) i^(-1) ul(Lambda) -> g_(ol(s))^(-1) i^(-1) R j_* ul(Lambda)
  $
  is an isomorphism. Thus it suffices to show that $ul(Lambda) -> i^(-1) R j_* ul(Lambda)$ is an isomorphism, i.e. $(R j_* ul(Lambda))_(ol(s)) = Lambda$. Indeed, 
  $
    (R j_* ul(Lambda))_(ol(s)) = R Gamma(ol(t) times_(tilde(S)_(ol(s))) (tilde(S)_(ol(s)))^tilde_(ol(s)), ul(Lambda)) = R Gamma(ol(t) times_(tilde(S)_(ol(s))) tilde(S)_(ol(s)), ul(Lambda)) = R Gamma(ol(t), ul(Lambda)) = Lambda
  $
  and we are done showing that $i'^(-1) tilde(cal(L)) -> i'^(-1) R j'_* j'^(-1) tilde(cal(L))$ is an isomorphism. Thus by @loc-acyc-alt-desc, $g$ is locally acyclic. 

  (2)$==>$(3) is tautological. 

  (3)$==>$(1): Recall that we assumed that every finite $Lambda$-module embeds into a finite free $Lambda$-module. By @rel-bc-reductions, it suffices to show the result when $X = Spec(A)$ is the normalization of a finite type $S$-scheme in the algebraic closure of its function field $K$, and $j: xi = Spec(K) -> X$ is the inclusion of the generic point, in the Cartesian diagram: 
  // https://q.uiver.app/#r=typst&q=WzAsNCxbMCwwLCJ4aSciXSxbMCwxLCJ4aSJdLFsxLDEsIlgiXSxbMSwwLCJYJyJdLFszLDIsImdfWCJdLFswLDEsImdfeGkiLDJdLFsxLDIsImoiLDJdLFswLDMsImonIl1d
  #align(center, diagram({
    node((0, 0), [$X'_xi$])
    node((0, 1), [$xi$])
    node((1, 1), [$X$])
    node((1, 0), [$X'$])
    node((0.3, 0.3), $cart$)
    edge((1, 0), (1, 1), [$g_X$], label-side: left, "->")
    edge((0, 0), (0, 1), [$g_xi$], label-side: right, "->")
    edge((0, 1), (1, 1), [$j$], label-side: right, "->")
    edge((0, 0), (1, 0), [$j'$], label-side: left, "->")
  }))
  the relative base change: 
  $
    g_X^(-1) R j_* ul(Lambda) Lotimes_Lambda cal(L)_X -> R j'_* j'^(-1) cal(L)_X
  $
  (where $cal(L)_X = cal(L)_S|_(X')$) is an isomorphism. 

  We establish a lemma about integral normal schemes with algebraically closed function field. 

  #lemma(name: <integral-normal-affine-with-ac-func-field>)[
    Let $S = Spec(A)$ be an affine integral normal scheme with algebraically closed function field $K$. Then: 

    (1) Any monic polynomial in $A[T]$ splits completely in $A$, and the same statement holds with $A$ replaced by a local ring of $S$; 

    (2) The local rings of $S$ are integral, normal and strict henselian, with algebraically closed residue fields. 
  ]
  #proof[
    (1) Any monic polynomial in $A[T]$ splits completely in $K$, since $K$ is algebraically closed. Now that $A$ is integrally closed in $K$, the roots of this monic polynomial must lie in $A$. Thus this polynomial splits completely in $A$. 

    The same argument holds for a local ring of $S$, since these local rings are also integral normal with algebraically closed fraction field $K$. 

    (2) Let $frak(p) in Spec(A)$. Now for a monic polynomial $f_0 (T) in k(frak(p))[T]$, we may lift it to a monic polynomial $f(T) in A_(frak(p)) [T]$. By (1), $f(T)$ splits completely over $A_(frak(p))$. Reducing modulo $frak(p) A_(frak(p))$, we see that $f_0 (T)$ splits completely in $k(frak(p))$. 

    For any monic $f(T) in A_(frak(p)) [T]$ reducing to $f_0 (T) in k(frak(p))[T]$, $f(T)$ splits completely over $A_(frak(p))$, with roots reducing to roots of $f_0 (T)$. Thus Hensel's lemma trivially holds, as every root of $f_0 (T)$ trivially lifts to one of $f(T)$. Thus $A_(frak(p))$ is henselian. Since its residue field is algebraically closed (hence separably closed), $A_(frak(p))$ is strict henselian. 
  ]

  Note that by @generic-pt-pushforward-of-const-shv-on-normal-sch and by @geom-point-pushforward-exact, 
  $
    R j_* ul(Lambda) cong ul(Lambda)
  $
  and so $g_X^(-1) R j_* ul(Lambda) Lotimes_Lambda cal(L)_X cong cal(L)_X$. Thus we only need to show that the unit map: 
  $
    cal(L)_X -> R j'_* j'^(-1) cal(L)_X
  $
  is an isomorphism, where $g_X$ is locally acyclic relative to $cal(L)_X$ by (3). 

  Let $ol(x')$ be a geometric point of $X'$ above $x in X$ in the family ${ol(x')}$ above $E$, as in hypothesis, and so: 
  $
    (R j'_* j'^(-1) cal(L)_X)_(ol(x')) = R Gamma(xi times_X tilde(X')_(ol(x')), cal(L)_X|_(tilde(X')_(ol(x'))))
  $
  By @integral-normal-affine-with-ac-func-field, $x$ is always a geometric point of $X$, and:  
  $
    xi = xi times_X tilde(X)_x
  $
  Thus, 
  $
    (R j'_* j'^(-1) cal(L)_X)_(ol(x')) = R Gamma(xi times_X tilde(X')_(ol(x')), cal(L)_X|_(tilde(X')_(ol(x')))) = R Gamma(xi times_(tilde(X)_x) tilde(X')_(ol(x')), cal(L)_X|_(xi times_(tilde(X)_x) tilde(X')_(ol(x')))) = R Gamma(F_(ol(x'),xi), cal(L)_X|_(F_(ol(x'),xi)))
  $
  and so the stalk of the unit $cal(L)_X -> R j'_* j'^(-1) cal(L)_X$ is the restriction map: 
  $
    (cal(L)_X)_(ol(x')) -> R Gamma(F_(ol(x'),xi), cal(L)_X|_(F_(ol(x'),xi)))
  $
  which is an isomorphism by hypothesis. We are thereby done. 
  /*By the lemma above, every point of $X$ is a geometric point. For a point $x in X$, form the Cartesian diagram: 
  // https://q.uiver.app/#r=typst&q=WzAsNixbMCwwLCJ4aSciXSxbMCwxLCJ4aSJdLFsxLDEsInRpbGRlKFgpXyhvbCh4KSkiXSxbMSwwLCJYJyB0aW1lc19YIHRpbGRlKFgpXyhvbCh4KSkiXSxbMiwxLCJ4Il0sWzIsMCwieCciXSxbMywyLCJnX1giXSxbMCwxLCJnX3hpIiwyXSxbMSwyLCJqIiwyXSxbMCwzLCJqJyJdLFs0LDIsImkiXSxbNSw0LCJnX3giXSxbNSwzLCJpJyIsMl1d
  #align(center, diagram({
    node((0, 0), [$X'_xi$])
    node((0, 1), [$xi$])
    node((1, 1), [$tilde(X)_(x)$])
    node((1, 0), [$X' times_X tilde(X)_(x)$])
    node((2, 1), [$x$])
    node((2, 0), [$x'$])
    edge((1, 0), (1, 1), [$g_X$], label-side: left, "->")
    edge((0, 0), (0, 1), [$g_xi$], label-side: right, "->")
    edge((0, 1), (1, 1), [$j_1$], label-side: right, "->")
    edge((0, 0), (1, 0), [$tilde(j)$], label-side: left, "->")
    edge((2, 1), (1, 1), [$tilde(i)$], label-side: left, "->")
    edge((2, 0), (2, 1), [$g_x$], label-side: left, "->")
    edge((2, 0), (1, 0), [$i'$], label-side: right, "->")
  }))
  to which we may attach two more Cartesian squares at the bottom: 
  // https://q.uiver.app/#r=typst&q=WzAsOSxbMCwwLCJ4aSciXSxbMCwxLCJ4aSJdLFsxLDEsInRpbGRlKFgpX3giXSxbMSwwLCJYJyB0aW1lc19YIHRpbGRlKFgpX3giXSxbMiwxLCJ4Il0sWzIsMCwieCciXSxbMSwyLCJYIl0sWzIsMiwieCJdLFswLDIsInhpIl0sWzMsMiwidGlsZGUoZykiXSxbMCwxLCJnX3hpIiwyXSxbMSwyLCJqXzEiLDJdLFswLDMsImonIl0sWzQsMiwiaV8xIl0sWzUsNCwiZ194Il0sWzUsMywiaSciLDJdLFsyLDYsImdhbW1hIl0sWzgsNiwiaiIsMl0sWzcsNiwiaSJdLFs0LDcsIiIsMix7InN0eWxlIjp7ImJvZHkiOnsibmFtZSI6ImRvdWJsZSBiYXJyZWQifX19XSxbMSw4LCIiLDIseyJzdHlsZSI6eyJib2R5Ijp7Im5hbWUiOiJkb3VibGUgYmFycmVkIn19fV1d
  #align(center, diagram({
    node((0, 0), [$X'_xi$])
    node((0, 1), [$xi$])
    node((1, 1), [$tilde(X)_x$])
    node((1, 0), [$X' times_X tilde(X)_x$])
    node((2, 1), [$x$])
    node((2, 0), [$X'_x$])
    node((1, 2), [$X$])
    node((2, 2), [$x$])
    node((0, 2), [$xi$])
    edge((1, 0), (1, 1), [$tilde(g)$], label-side: left, "->")
    edge((0, 0), (0, 1), [$g_xi$], label-side: right, "->")
    edge((0, 1), (1, 1), [$j_1$], label-side: right, "->")
    edge((0, 0), (1, 0), [$tilde(j)$], label-side: left, "->")
    edge((2, 1), (1, 1), [$i_1$], label-side: left, "->")
    edge((2, 0), (2, 1), [$g_x$], label-side: left, "->")
    edge((2, 0), (1, 0), [$tilde(i)$], label-side: right, "->")
    edge((1, 1), (1, 2), [$gamma$], label-side: left, "->")
    edge((0, 2), (1, 2), [$j$], label-side: right, "->")
    edge((2, 2), (1, 2), [$i$], label-side: left, "->")
    edge((2, 1), (2, 2), "=")
    edge((0, 1), (0, 2), "=")
  }))
  By @loc-acyc-alt-desc, the unit: 
  $
    tilde(i)^(-1) (cal(L)_X|_(X' times_X tilde(X)_x)) -> tilde(i)^(-1) R tilde(j)_* tilde(j)^(-1) (cal(L)_X|_(X' times_X tilde(X)_x))
  $
  is an isomorphism. Taking stalk, this says
  $
    
  $*/
]

Now that we have seen the intimate connection between local acyclicity and base changes, we study the cospecialization, a construction that arises from local acyclicity, and also study the properties that allows us to manipulate local acyclicity. 

#properties(name: <loc-acyc-and-limits-of-qfinite>)[
  In a Cartesian diagram of schemes: 
  // https://q.uiver.app/#r=typst&q=WzAsNCxbMCwwLCJYJyJdLFswLDEsIlMnIl0sWzEsMCwiWCJdLFsxLDEsIlMiXSxbMSwzLCJnIiwyXSxbMCwyLCJnJyJdLFsyLDMsImYiXSxbMCwxLCJmJyIsMl1d
  #align(center, diagram({
    node((0, 0), [$X'$])
    node((0, 1), [$S'$])
    node((1, 0), [$X$])
    node((1, 1), [$S$])
    node((0.3, 0.3), $cart$)
    edge((0, 1), (1, 1), [$g$], label-side: right, "->")
    edge((0, 0), (1, 0), [$g'$], label-side: left, "->")
    edge((1, 0), (1, 1), [$f$], label-side: left, "->")
    edge((0, 0), (0, 1), [$f'$], label-side: right, "->")
  }))
  Let $ol(x')$ be a geometric point of $X'$, $ol(x) = g'(ol(x'))$. Suppose that $S'$ is a projective limit of locally quasi-finite $S$-schemes with affine transition maps. Then:
    
  - If $f$ is locally acyclic relative to $cal(K)$ at $ol(x)$, then $f'$ is locally acyclic relative to $cal(K)|_(X')$ at $ol(x')$. 
]
#proof[
  (1) Let $ol(s') = f'(ol(x')), ol(s) = f(ol(x))$. Let $ol(t')$ be a geometric point of $tilde(S')_(ol(s'))$ above $ol(t)$ of $tilde(S)_(ol(s))$. We now compare the vanishing cycle varieties: 
  $
    F_(ol(x'),ol(t')) = ol(t') times_(tilde(S')_(ol(s'))) tilde(X')_(ol(x')) 
  $
  v.s: 
  $
    F_(ol(x),ol(t)) = ol(t) times_(tilde(S)_(ol(s))) tilde(X)_(ol(x))
  $

  By applying @strict-henselizations-tensors-and-qfinites with $Omega$ being the residue field of $ol(x')$, 
  $
    cal(O)_(X,ol(x))^#[sh] otimes_(cal(O)_(s,ol(s))^#[sh]) cal(O)_(S',ol(s'))^#[sh] cong cal(O)_(X',ol(x'))
  $
  and so: 
  $
    Omega otimes_(cal(O)_(S',ol(s'))^#[sh]) cal(O)_(X',ol(x')) cong Omega otimes_(cal(O)_(s,ol(s))^#[sh]) cal(O)_(X,ol(x))^#[sh]
  $
  i.e. $F_(ol(x'),ol(t')) cong F_(ol(x),ol(t))$. Now that: 
  $
    cal(K)_(ol(x)) -> R Gamma(F_(ol(x),ol(t)), cal(K)|_(F_(ol(x),ol(t))))
  $
  is an isomorphism by local acyclicity of $f$ relative to $cal(K)$ at $ol(x)$, $cal(K)_(ol(x)) -> R Gamma(F_(ol(x'),ol(t')), cal(K)|_(F_(ol(x'),ol(t'))))$ must be an isomorphism. Thus $f'$ is locally acyclic at $ol(x')$ relative to $cal(K)|_(X')$. 
]

#construction(name: <cospecialization-map>)[
  Suppose that $f: X -> S$ is a locally acyclic morphism relative to $cal(K) in D^+ (X_et, Lambda)$. For any geometric point $ol(s)$ of $S$, any geometric point $ol(t)$ of $tilde(S)_(ol(s))$, form the Cartesian diagram: #h(1fr)
    // https://q.uiver.app/#r=typst&q=WzAsNixbMCwwLCJYXyhvbCh0KSkiXSxbMSwwLCJYIHRpbWVzX1MgdGlsZGUoUylfKG9sKHMpKSJdLFsyLDAsIlhfKG9sKHMpKSJdLFsyLDEsIm9sKHMpIl0sWzEsMSwidGlsZGUoUylfKG9sKHMpKSJdLFswLDEsIm9sKHQpIl0sWzUsNCwiaiIsMl0sWzMsNCwiaSJdLFsyLDMsImZfKG9sKHMpKSJdLFsxLDQsInRpbGRlKGYpIl0sWzAsNSwiZl8ob2wodCkpIiwyXSxbMiwxLCJpJyIsMl0sWzAsMSwiaiciXV0=
    #align(center, diagram({
      node((0, 0), [$X_(ol(t))$])
      node((1, 0), [$X times_S tilde(S)_(ol(s))$])
      node((2, 0), [$X_(ol(s))$])
      node((2, 1), [$ol(s)$])
      node((1, 1), [$tilde(S)_(ol(s))$])
      node((0, 1), [$ol(t)$])
      edge((0, 1), (1, 1), [$j$], label-side: right, "->")
      edge((2, 1), (1, 1), [$i$], label-side: left, "->")
      edge((2, 0), (2, 1), [$f_(ol(s))$], label-side: left, "->")
      edge((1, 0), (1, 1), [$tilde(f)$], label-side: left, "->")
      edge((0, 0), (0, 1), [$f_(ol(t))$], label-side: right, "->")
      edge((2, 0), (1, 0), [$i'$], label-side: right, "->")
      edge((0, 0), (1, 0), [$j'$], label-side: left, "->")
    }))
    and $tilde(cal(K)) = cal(K)|_(X times_S tilde(S)_(ol(s)))$. By @loc-acyc-alt-desc, the unit:
    $
      beta_(cal(K),ol(s),ol(t)): i'^(-1) tilde(cal(K)) -> i'^(-1) R j'_* j'^(-1) tilde(cal(K))
    $
    is an isomorphism of complexes in $D^+ ((X_(ol(s)))_et, Lambda)$. Thus, we may define a composition: 
    $
      R Gamma(X_(ol(t)), cal(K)|_(X_(ol(t)))) &= R Gamma(X_(ol(t)), j'^(-1) tilde(cal(K))) = R Gamma(X times_S tilde(S)_(ol(s)), R j'_* j'^(-1) tilde(cal(K))) \
      &-> R Gamma(X_(ol(s)), i'^(-1) R j'_* j'^(-1) tilde(cal(K))) \
      &->^(beta_(cal(K),ol(s),ol(t))^(-1)) R Gamma(X_(ol(s)), i'^(-1) tilde(cal(K))) = R Gamma(X_(ol(s)), cal(K)|_(X_(ol(s))))
    $
    Here, the first map is restriction along $i'^(-1)$ and the second map is induced by the inverse of the isomorphism $beta_(cal(K),ol(s),ol(t))$. This map is called the *cospecialization map*, and denoted: 
    $
      cosp: R Gamma(X_(ol(t)), cal(K)|_(X_(ol(t)))) -> R Gamma(X_(ol(s)), cal(K)|_(X_(ol(s))))
    $
    By construction, the cospecialization is transitive w.r.t. chains of generalizations of geometric points. 
]

#proposition(name: <loc-acyc-sp-cosp-square>)[
  Let $f: X -> S$ be a qcqs locally acyclic morphism relative to $cal(K) in D^+ (X_et, Lambda)$. Then for every geometric point $ol(s)$ of $S$, every generalization of $ol(s)$, i.e. a geometric point $ol(t)$ of $tilde(S)_(ol(s))$, the following diagram commutes: 
  // https://q.uiver.app/#r=typst&q=WzAsNCxbMCwwLCIoUiBmXyogY2FsKEspKV8ob2wocykpIl0sWzAsMSwiKFIgZl8qIGNhbChLKSlfKG9sKHQpKSJdLFsxLDAsIlIgR2FtbWEoWF8ob2wocykpLCBjYWwoSyl8XyhYXyhvbChzKSkpKSJdLFsxLDEsIlIgR2FtbWEoWF8ob2wodCkpLCBjYWwoSyl8XyhYXyhvbCh0KSkpKSJdLFswLDIsIkJDIl0sWzEsMywiQkMiLDJdLFswLDEsInNwIiwyXSxbMiwzLCJjb3NwIl1d
  #align(center, diagram({
    node((0, 0), [$(R f_* cal(K))_(ol(s))$])
    node((0, 1), [$(R f_* cal(K))_(ol(t))$])
    node((1, 0), [$R Gamma(X_(ol(s)), cal(K)|_(X_(ol(s))))$])
    node((1, 1), [$R Gamma(X_(ol(t)), cal(K)|_(X_(ol(t))))$])
    edge((0, 0), (1, 0), [$BC$], label-side: left, "->")
    edge((0, 1), (1, 1), [$BC$], label-side: right, "->")
    edge((0, 0), (0, 1), [$sp$], label-side: right, "->")
    edge((1, 1), (1, 0), [$cosp$], label-side: right, "->")
  }))
  Here, the horizontal maps are base changes, the left map is the specialization map, and the right map is the cospecialization map. 
]
#proof[
  By unfolding the definitions, we see that we may replace $f: X -> S$ with $tilde(f): tilde(X) = X times_S tilde(S)_(ol(s)) -> tilde(S)_(ol(s))$, and $cal(K)$ with $tilde(cal(K)) = cal(K)|_(X times_S tilde(S)_(ol(s)))$. Indeed, 

  - $tilde(f)$ is locally acyclic relative to $tilde(cal(K))$. Indeed, $tilde(S)_(ol(s)) -> S$ is a projective limit of etale neighborhoods of $ol(s)$ in $S$, and thus $tilde(S)_(ol(s))$ is a projective limit of quasi-finite $S$-schemes. By @loc-acyc-and-limits-of-qfinite, $tilde(f)$ is locally acyclic relative to $tilde(cal(K))$. 

  - By @derived-stalks-of-derived-pushforward, we have isomorphisms: 
    $
      (R f_* cal(K))_(ol(t)) = R Gamma(X times_S tilde(S)_(ol(t)), cal(K)|_(X times_S tilde(S)_(ol(t)))) = R Gamma(tilde(X) times_(tilde(S)_(ol(s))) (tilde(S)_(ol(s)))^tilde_(ol(t)), tilde(cal(K))|_(tilde(X) times_(tilde(S)_(ol(s))) (tilde(S)_(ol(s)))^tilde_(ol(t)))) = (R tilde(f)_* tilde(cal(K)))_(ol(t))
    $
    These isomorphisms are compatible with restrictions and base changes to a stalk (which are essentially restrictions), hence specializations (which are also essentially restrictions). Thus, the left side of the diagram passes over. 

  - The construction of $cosp$ is only dependent on the map $tilde(f): X times_S tilde(S)_(ol(s))$ and its fibers above $ol(s)$ and $ol(t)$, and so the right side of the diagram passes over. 

  Thus, we may assume that $S$ is the spectrum of a strict henselian local ring and $ol(s)$ is the closed point of $S$. 

  Form the Cartesian diagram: 
  #align(center, diagram({
    node((0, 0), [$X_(ol(t))$])
    node((1, 0), [$X$])
    node((2, 0), [$X_(ol(s))$])
    node((2, 1), [$ol(s)$])
    node((1, 1), [$S$])
    node((0, 1), [$ol(t)$])
    edge((0, 1), (1, 1), [$j$], label-side: right, "->")
    edge((2, 1), (1, 1), [$i$], label-side: left, "->")
    edge((2, 0), (2, 1), [$f_(ol(s))$], label-side: left, "->")
    edge((1, 0), (1, 1), [$f$], label-side: left, "->")
    edge((0, 0), (0, 1), [$f_(ol(t))$], label-side: right, "->")
    edge((2, 0), (1, 0), [$i'$], label-side: right, "->")
    edge((0, 0), (1, 0), [$j'$], label-side: left, "->")
  }))

  Inspecting the definition of specialization and cospecialization, we see that we need to show the commutativity of the following diagram: 

  // https://q.uiver.app/#r=typst&q=WzAsNixbMCwwLCJSIEdhbW1hKFgsIGNhbChLKSkiXSxbMSwwLCJSIEdhbW1hKFhfKG9sKHMpKSwgaSdeKC0xKSBjYWwoSykpIl0sWzAsMiwiUiBHYW1tYShYIHRpbWVzX1MgdGlsZGUoUylfKG9sKHQpKSwgY2FsKEspfF8oWCB0aW1lc19TIHRpbGRlKFMpXyhvbCh0KSkpKSJdLFsxLDIsIlIgR2FtbWEoWF8ob2wodCkpLCBqJ14oLTEpIGNhbChLKSkiXSxbMiwyLCJSIEdhbW1hKFgsIFIgaidfKiBqJ14oLTEpIGNhbChLKSkiXSxbMiwwLCJSIEdhbW1hKFhfKG9sKHMpKSwgaSdeKC0xKSBSIGonXyogaideKC0xKSBjYWwoSykpIl0sWzAsMiwicmVzIiwyXSxbMiwzLCJyZXMiLDJdLFswLDEsInJlcyJdLFszLDQsIiIsMix7InN0eWxlIjp7ImJvZHkiOnsibmFtZSI6ImRvdWJsZSBiYXJyZWQifX19XSxbMSw1LCJiZXRhIl0sWzQsNSwicmVzIiwyXV0=
  #align(center, diagram({
    node((0, 0), [$R Gamma(X, cal(K))$])
    node((1, 0), [$R Gamma(X_(ol(s)), i'^(-1) cal(K))$])
    node((0, 2), [$R Gamma(X times_S tilde(S)_(ol(t)), cal(K)|_(X times_S tilde(S)_(ol(t))))$])
    node((1, 2), [$R Gamma(X_(ol(t)), j'^(-1) cal(K))$])
    node((2, 2), [$R Gamma(X, R j'_* j'^(-1) cal(K))$])
    node((2, 0), [$R Gamma(X_(ol(s)), i'^(-1) R j'_* j'^(-1) cal(K))$])
    edge((0, 0), (0, 2), [$res$], label-side: right, "->")
    edge((0, 2), (1, 2), [$res$], label-side: right, "->")
    edge((0, 0), (1, 0), [$res$], label-side: left, "->")
    edge((1, 2), (2, 2), "=")
    edge((1, 0), (2, 0), [$beta$], label-side: left, "->")
    edge((2, 2), (2, 0), [$res$], label-side: right, "->")
  }))
  where $beta$ is the unit and the $res$'s are restrictions. The composition of the left and lower left restriction arrows is the restriction $res: R Gamma(X, cal(K)) -> R Gamma(X_(ol(t)), cal(K)|_(X_(ol(t))))$. Now under $D(Lambda) cong D(ol(s)_et, Lambda)$, we have the natural isomorphisms: 
  $
    R Gamma(X, -) cong i^(-1) R f_* (-) \
    R Gamma(X_(ol(s)), -) cong R f_(ol(s),*) \
    R Gamma(X_(ol(t)), -) cong i^(-1) R j_* R f_(ol(t),*) cong i^(-1) R f_* R j'_*
  $
  Under this identification, we only need to verify the commutativity of: 
  // https://q.uiver.app/#r=typst&q=WzAsNCxbMCwwLCJpXigtMSkgUiBmXyogY2FsKEspIl0sWzAsMSwiaV4oLTEpIFIgZl8qIFIgaidfKiBqJ14oLTEpIGNhbChLKSJdLFsxLDEsIlIgZl8ob2wocyksKikgaSdeKC0xKSBSIGonXyogaideKC0xKSBjYWwoSykiXSxbMSwwLCJSIGZfKG9sKHMpLCopIGknXigtMSkgY2FsKEspIl0sWzAsMywiQkMiXSxbMywyXSxbMCwxXSxbMSwyLCJCQyIsMl1d
  #align(center, diagram({
    node((0, 0), [$i^(-1) R f_* cal(K)$])
    node((0, 1), [$i^(-1) R f_* R j'_* j'^(-1) cal(K)$])
    node((1, 1), [$R f_(ol(s),*) i'^(-1) R j'_* j'^(-1) cal(K)$])
    node((1, 0), [$R f_(ol(s),*) i'^(-1) cal(K)$])
    edge((0, 0), (1, 0), [$BC$], label-side: left, "->")
    edge((1, 0), (1, 1), "->")
    edge((0, 0), (0, 1), "->")
    edge((0, 1), (1, 1), [$BC$], label-side: right, "->")
  }))
  which is nothing but a naturality square. 
]

#corollary(name: <proper-loc-acyc-bc>)[
  Let $f: X -> S$ be a proper morphism between locally noetherian schemes that is locally acyclic relative to $cal(K) in D^+_#[tor] (X_et, Lambda)$. Then for every geometric point $ol(s)$ of $S$, every generalization of $ol(s)$, i.e. a geometric point $ol(t)$ of $tilde(S)_(ol(s))$, the specialization and cospecialization maps: 
  $
    sp: (R f_* cal(K))_(ol(s)) -> (R f_* cal(K))_(ol(t)) \

    cosp: R Gamma(X_(ol(t)), cal(K)|_(X_(ol(t)))) -> R Gamma(X_(ol(s)), cal(K)|_(X_(ol(s))))
  $
  are both isomorphisms. 
]
#proof[
  In the commutative diagram of @loc-acyc-sp-cosp-square, the base change maps are both isomorphisms by proper base change, since $f$ is proper. Thus, it suffices to prove either of $sp$ or $cosp$ is an isomorphism. 

  We will directly prove that $cosp$ is an isomorphism. Indeed, $cosp$ is constructed as: 
  $
    R Gamma(X_(ol(t)), cal(K)|_(X_(ol(t)))) &= R Gamma(X_(ol(t)), j'^(-1) tilde(K)) = R Gamma(X times_S tilde(S)_(ol(s)), R j'_* j'^(-1) tilde(cal(K))) \
    &-> R Gamma(X_(ol(s)), i'^(-1) R j'_* j'^(-1) tilde(cal(K))) \
    &->^(beta_(cal(K),ol(s),ol(t))^(-1)) R Gamma(X_(ol(s)), i'^(-1) tilde(cal(K))) = R Gamma(X_(ol(s)), cal(K)|_(X_(ol(s))))
  $
  The second map is by definition an isomorphism. Meanwhile, the first map: 
  $
    R Gamma(X times_S tilde(S)_(ol(s)), R j'_* j'^(-1) tilde(cal(K))) -> R Gamma(X_(ol(s)), i'^(-1) R j'_* j'^(-1) tilde(cal(K)))
  $
  is the base change of the proper map $X times_S tilde(S)_(ol(s)) -> tilde(S)_(ol(s))$ along the closed geometric point $ol(s) -> tilde(S)_(ol(s))$. Here, $tilde(S)_(ol(s))$ is noetherian and $R j'_* j'^(-1) tilde(cal(K)) in D^+_#[tor]$, so proper base change is applicable. Thus this map is an isomorphism too by proper base change. We are thereby done showing that $cosp$ is an isomorphism. 
]

#properties(name: <loc-acyc-compose>)[
  Local acyclicity is compatible with composition, in the following sense. Let $X ->^f Y ->^g S$ be qcqs morphisms between locally noetherian schemes, and $cal(K) in D^b_#[ctf] (X_et, Lambda)$, with geometric points $ol(x)$ of $X$, and $ol(y) = f(ol(x))$. 
  
  If $f$ is locally acyclic relative to $cal(K)$ at every point of $tilde(X)_(ol(x))$, and $g$ is locally acyclic relative to $ul(cal(K)_(ol(x)))$ at $ol(y)$, then $g compose f$ is locally acyclic relative to $cal(K)$ at $ol(x)$. 
]
#proof[
  Put $ol(s) = g(ol(y))$. Since local acyclicity is only dependent on the strict local neighborhood, we may replace $X, Y, S$ with $tilde(X)_(ol(x)), tilde(Y)_(ol(y)), tilde(S)_(ol(s))$ and assume that: 

  - $X, Y, S$ are spectra of noetherian strict henselian local rings, and $ol(x), ol(y), ol(s)$ are above their closed points. 

  - $f$ is locally acyclic relative to $cal(K)$ and $g$ is locally acyclic at $ol(y)$ relative to $ul(cal(K)_(ol(x))) = ul(R Gamma(X, cal(K)))$. 

  Let $ol(t)$ be any geometric point of $S$. To show that $g compose f$ is locally acyclic relative to $cal(K)$ at $ol(x)$, it suffices to show that the map: 
  $
    cal(K)_(ol(x)) -> R Gamma(X_(ol(t)), cal(K)|_(X_(ol(t))))
  $
  Base change $f$ to $f_(ol(t)): X_(ol(t)) -> Y_(ol(t))$. Now by the Leray spectral sequence, 
  $
    R Gamma(X_(ol(t)), cal(K)|_(X_(ol(t)))) cong R Gamma(Y_(ol(t)), R f_(ol(t),*) (cal(K)|_(X_(ol(t)))))
  $
  There is a map $ul(cal(K)_(ol(x))) = ul(R Gamma(X, cal(K))) -> cal(K)$, hence a map $ul(cal(K)_(ol(x))) -> cal(K)|_(X_(ol(t)))$. Thus by adjunction there is a canonical map: 
  $
    ul(cal(K)_(ol(x))) -> R f_(ol(t),*) (cal(K)|_(X_(ol(t))))
  $
  Suppose that this map is an isomorphism, then: 
  $
    R Gamma(X_(ol(t)), cal(K)|_(X_(ol(t)))) cong R Gamma(Y_(ol(t)), R f_(ol(t),*) (cal(K)|_(X_(ol(t))))) cong R Gamma(Y_(ol(t)), ul(cal(K)_(ol(x)))) cong cal(K)_(ol(x))
  $
  where the last isomorphism is due to local acyclicity of $g$ relative to $ul(cal(K)_(ol(x)))$. We would thus be done. It therefore suffices to show that the canonical map $ul(cal(K)_(ol(x))) -> R f_(ol(t),*) (cal(K)|_(X_(ol(t))))$ is an isomorphism. 
  #lemma[
    Let $f: X -> S$ be a locally acyclic morphism relative to $cal(K) in D^+ (X_et, Lambda)$. Then for every geometric point $ol(t)$ of $S$, form the Cartesian diagram: 
    // https://q.uiver.app/#r=typst&q=WzAsNCxbMCwwLCJYXyhvbCh0KSkiXSxbMSwwLCJYIl0sWzEsMSwiUyJdLFswLDEsIm9sKHQpIl0sWzAsMSwiaiciXSxbMywyLCJqIiwyXSxbMSwyLCJmIl0sWzAsMywiZl8ob2wodCkpIiwyXV0=
    #align(center, diagram({
      node((0, 0), [$X_(ol(t))$])
      node((1, 0), [$X$])
      node((1, 1), [$S$])
      node((0, 1), [$ol(t)$])
      edge((0, 0), (1, 0), [$j'$], label-side: left, "->")
      edge((0, 1), (1, 1), [$j$], label-side: right, "->")
      edge((1, 0), (1, 1), [$f$], label-side: left, "->")
      edge((0, 0), (0, 1), [$f_(ol(t))$], label-side: right, "->")
    }))
    Then the relative base change map: 
    $
      cal(K) Lotimes_Lambda f^(-1) j_* ul(Lambda) -> R j'_* j'^(-1) cal(K)
    $
    is an isomorphism. 
  ]
  #proof[
    Let $ol(t)$ lie above $t in S$, and let $S'$ be the normalization of $ol({t})$, equipped with its reduced substructure, in the algebraic closure of its function field. Then: 
    $
      S' -> ol({t}) -> S
    $
    is the composition of an integral map with a closed immersion, hence integral. Thus by @loc-acyc-and-limits-of-qfinite, the base change $f': X' -> S'$ of $f: X -> S$ along $S' -> S$ is locally acyclic relative to $cal(K)|_(X')$. 

    Since relative base change is compatible with horizontal concatenation of Cartesian squares, by @finite-bc-in-the-limit, it suffices to deal with base change along $ol(t) -> S'$ and $X' -> S'$. In other words, we may assume that: 

    - $S$ is a normal integral scheme with algebraically closed function field, and $ol(t)$ is above its generic point. 

    Let $t$ be the generic point of $S$, which is an algebraic geometric point. Factor $j: ol(t) -> S$ into $ol(t) ->^q t -> S$ where $t$ is the generic point of $S$, being an algebraic geometric point. By @integral-normal-affine-with-ac-func-field, 
    $
      f^(-1) j_* ul(Lambda) = f^(-1) h_* q_* ul(Lambda) = f^(-1) h_* ul(Lambda) = f^(-1) ul(Lambda) = ul(Lambda)
    $
    Thus, it suffices to show that $cal(K) -> R j'_* j'^(-1) cal(K)$ is an isomorphism. Indeed, for a geometric point $ol(x)$ lying above $x in X$, 
    $
      (R j'_* j'^(-1) cal(K))_(ol(x)) = R Gamma(X_(ol(t)) times_X tilde(X)_(ol(x)), cal(K)|_(X_(ol(t)) times_X tilde(X)_(ol(x)))) = R Gamma(ol(t) times_S tilde(X)_(ol(x)), cal(K)|_(ol(t) times_S tilde(X)_(ol(x))))
    $

    For $s = f(x)$, $tilde(X)_(ol(x))$ is local above $Spec(cal(O)_(S,s))$, and: 
    $
      ol(t) times_S tilde(X)_(ol(x)) = ol(t) otimes_(cal(O)_(S,s)) tilde(X)_(ol(x))
    $
    However, by @integral-normal-affine-with-ac-func-field, $s$ is a geometric point of $S$, and $cal(O)_(S,s)$ is strict henselian. Thus: 
    $
      ol(t) times_S tilde(X)_(ol(x)) = ol(t) otimes_(cal(O)_(S,s)) tilde(X)_(ol(x)) = ol(t) times_(tilde(S)_s) tilde(X)_(ol(x)) = F_(ol(x),ol(t))
    $
    is a vanishing cycle variety. Thus, the map: 
    $
      cal(K)_(ol(x)) -> (R j'_* j'^(-1) cal(K))_(ol(x)) = R Gamma(F_(ol(x),ol(t)), cal(K)|_(F_(ol(x),ol(t))))
    $
    is an isomorphism by definition of local acyclicity. Hence $cal(K) -> R j'_* j'^(-1) cal(K)$ is an isomorphism. 
  ]

  #lemma[
    Let $Lambda$ be a noetherian ring s.t. every finite $Lambda$-module embeds into a finite free $Lambda$-module. Suppose that $f: X -> S$ is a qcqs locally acyclic morphism relative to $cal(K) in D^b_#[ctf] (X_et, Lambda)$, in which $S$ is locally noetherian. Suppose that $ol(s)$ is a geometric point of $S$ s.t. all cospecializations: 
    $
      R Gamma(X_(ol(t)), cal(K)|_(X_(ol(t)))) -> R Gamma(X_(ol(s)), cal(K)|_(X_(ol(s))))
    $
    are isomorphisms for geometric points $ol(t)$ of $tilde(S)_(ol(s))$. Then the base change: 
    $
      (R f_* cal(K))_(ol(s)) -> R Gamma(X_(ol(s)), cal(K)|_(X_(ol(s))))
    $
    is an isomorphism. 
  ]
  #proof[
    As in the start of the proof of @loc-acyc-sp-cosp-square, we may replace $f: X -> S$ with $X times_S tilde(S)_(ol(s)) -> tilde(S)_(ol(s))$ and $cal(K)$ with $cal(K)|_(X times_S tilde(S)_(ol(s)))$. We may thus assume that $S$ is the spectrum of a noetherian strict henselian local ring, and $ol(s)$ lies above its closed point. 

    To prove the desired result, we prove that for all sheaves $cal(F)$ of $Lambda$-modules on $S$, the base change: 
    $
      (R f_* (cal(K) Lotimes_Lambda f^(-1) cal(F)))_(ol(s)) = R Gamma(X, cal(K) Lotimes_Lambda f^(-1) cal(F)) -> R Gamma (X_(ol(s)), (cal(K) Lotimes_Lambda f^(-1) cal(F))|_(X_(ol(s))))
    $
    is an isomorphism. We will then take $cal(F) = ul(Lambda)$ to conclude the proof. 

    Firstly, suppose that $cal(F) = j_* ul(Lambda)$ for a geometric point $j: ol(t) -> S$. Form the Cartesian diagram: 
    #align(center, diagram({
      node((0, 0), [$X_(ol(t))$])
      node((1, 0), [$X$])
      node((2, 0), [$X_(ol(s))$])
      node((2, 1), [$ol(s)$])
      node((1, 1), [$S$])
      node((0, 1), [$ol(t)$])
      edge((0, 1), (1, 1), [$j$], label-side: right, "->")
      edge((2, 1), (1, 1), [$i$], label-side: left, "->")
      edge((2, 0), (2, 1), [$f_(ol(s))$], label-side: left, "->")
      edge((1, 0), (1, 1), [$f$], label-side: left, "->")
      edge((0, 0), (0, 1), [$f_(ol(t))$], label-side: right, "->")
      edge((2, 0), (1, 0), [$i'$], label-side: right, "->")
      edge((0, 0), (1, 0), [$j'$], label-side: left, "->")
    }))
    By the previous lemma, LHS is: 
    $
      R Gamma(X, cal(K) Lotimes_Lambda f^(-1) j_* ul(Lambda)) = R Gamma(X, R j'_* j'^(-1) cal(K)) = R Gamma(X_(ol(t)), j'^(-1) cal(K))
    $ 
    while on RHS: 
    $
      i'^(-1) (cal(K) Lotimes_Lambda f^(-1) j_* ul(Lambda)) = i'^(-1) cal(K) Lotimes_Lambda f_(ol(s))^(-1) i^(-1) j_* ul(Lambda)
    $
    Now $i^(-1) j_* ul(Lambda) = ul((j_* ul(Lambda))_(ol(s))) = ul(R Gamma(S, j_* ul(Lambda))) = ul(Lambda)$, and so $f_(ol(s))^(-1) i^(-1) j_* ul(Lambda) = ul(Lambda)$. Thus RHS is: 
    $
      R Gamma (X_(ol(s)), (cal(K) Lotimes_Lambda f^(-1) cal(F))|_(X_(ol(s)))) = R Gamma(X_(ol(s)), i'^(-1) cal(K))
    $
    By unfolding the definitions, it can be checked that under these identifications of LHS and RHS, the base change map becomes exactly the cospecialization: 
    $
      cosp: R Gamma(X_(ol(t)), j'^(-1) cal(K)) -> R Gamma(X_(ol(s)), i'^(-1) cal(K))
    $
    and is an isomorphism by hypothesis. In other words, we have proved that the base change: 
    $
      (R f_* (cal(K) Lotimes_Lambda f^(-1) cal(F)))_(ol(s)) -> R Gamma (X_(ol(s)), (cal(K) Lotimes_Lambda f^(-1) cal(F))|_(X_(ol(s))))
    $
    is an isomorphism whenever $cal(F) = j_* ul(Lambda)$ for a geometric point $j: ol(t) -> S$. 

    Replace $cal(K)$ by a bounded flat resolution $cal(P)^bullet$, and we have hypercohomology spectral sequences: 
    $
      E_1^(p,q) (cal(F)) := R^q f_* (cal(P)^p otimes_Lambda f^(-1) cal(F)) => h^(p+q) ((R f_* (cal(K) Lotimes_Lambda f^(-1) cal(F)))_(ol(s))) =: L^q (cal(F)) \

      tilde(E)_1^(p,q) (cal(F)) := H^q (X_(ol(s)), (cal(P)^p Lotimes_Lambda f^(-1) cal(F))|_(X_(ol(s)))) => h^(p+q) (R Gamma (X_(ol(s)), (cal(K) Lotimes_Lambda f^(-1) cal(F))|_(X_(ol(s))))) =: S^q (cal(F))
    $
    Since $f$ is qcqs, by the limit formulas @limit-formula-for-sheaves and @relative-limit-formula-for-sheaves, $E_1^(p,q)$ and $tilde(E)_1^(p,q)$ both commute with directed limits. Thus, $L^q (cal(F))$ and $S^q (cal(F))$ both commute with directed limits in $cal(F)$. 

    Suppose that for a fixed $q$, for all $r < q$, $L^r (cal(F)) -> S^r (cal(F))$ is an isomorphism for all $cal(F) in cAb(S_et, Lambda)$. Note that: 

    - $S$ is noetherian, and so every sheaf $cal(F) in cAb(S_et, Lambda)$ can be written as $cal(F) = dirlim_lambda cal(F)_lambda$ as a directed limit of constructible sheaves of $Lambda$-modules. Now $L^q (cal(F)) -> S^q (cal(F))$ is the directed limit of $L^q (cal(F)_lambda) -> S^q (cal(F)_lambda)$, and so TFAE: 

      - $L^q (cal(F)) -> S^q (cal(F))$ is injective for all $cal(F) in cAb(S_et, Lambda)$; 

      - $L^q (cal(F)) -> S^q (cal(F))$ is injective for all constructible $cal(F) in cAb(S_et, Lambda)$. 
  
    - For every constructible sheaf $cal(F)$, by @constructible-godement-resolution we may get an injection $cal(F) -> oplus.big_(i=1)^m ol(t_i)_* ul(M_i)$ for finite $Lambda$-modules $M_i$ and geometric points $ol(t_i) -> S$. Now since every finite $Lambda$-module embeds into a finite free $Lambda$-module, we may assume that every $M_i$ is finite free, and by splitting them we may assume that every $M_i = Lambda$. Form the short exact sequence: #h(1fr)
      $
        0 -> cal(F) -> cal(C) = oplus.big_(i=1)^m ol(t_i)_* ul(Lambda) -> cal(R) -> 0
      $
      Now consider the following commutative diagram with exact rows: 
      // https://q.uiver.app/#r=typst&q=WzAsMTQsWzAsMCwiZG90cy5jIl0sWzEsMCwiTF4ocS0xKSAoY2FsKEMpKSJdLFsyLDAsIkxeKHEtMSkgKGNhbChSKSkiXSxbMywwLCJMXnEgKGNhbChGKSkiXSxbNCwwLCJMXnEgKGNhbChDKSkiXSxbNSwwLCJMXnEgKGNhbChSKSkiXSxbNiwwLCJkb3RzLmMiXSxbMCwxLCJkb3RzLmMiXSxbNiwxLCJkb3RzLmMiXSxbMSwxLCJTXihxLTEpIChjYWwoQykpIl0sWzIsMSwiU14ocS0xKSAoY2FsKFIpKSJdLFszLDEsIlNecSAoY2FsKEYpKSJdLFs0LDEsIlNecSAoY2FsKEMpKSJdLFs1LDEsIlNecSAoY2FsKFIpKSJdLFswLDFdLFsxLDJdLFsyLDNdLFszLDRdLFs0LDVdLFs1LDZdLFs3LDldLFs5LDEwXSxbMTAsMTFdLFsxMSwxMl0sWzEyLDEzXSxbMTMsOF0sWzEsOV0sWzIsMTBdLFszLDExXSxbNCwxMl0sWzUsMTNdXQ==
      #align(center, diagram({
        node((0, 0), [$dots.c$])
        node((1, 0), [$L^(q-1) (cal(C))$])
        node((2, 0), [$L^(q-1) (cal(R))$])
        node((3, 0), [$L^q (cal(F))$])
        node((4, 0), [$L^q (cal(C))$])
        node((5, 0), [$L^q (cal(R))$])
        node((6, 0), [$dots.c$])
        node((0, 1), [$dots.c$])
        node((6, 1), [$dots.c$])
        node((1, 1), [$S^(q-1) (cal(C))$])
        node((2, 1), [$S^(q-1) (cal(R))$])
        node((3, 1), [$S^q (cal(F))$])
        node((4, 1), [$S^q (cal(C))$])
        node((5, 1), [$S^q (cal(R))$])
        edge((0, 0), (1, 0), "->")
        edge((1, 0), (2, 0), "->")
        edge((2, 0), (3, 0), "->")
        edge((3, 0), (4, 0), "->")
        edge((4, 0), (5, 0), "->")
        edge((5, 0), (6, 0), "->")
        edge((0, 1), (1, 1), "->")
        edge((1, 1), (2, 1), "->")
        edge((2, 1), (3, 1), "->")
        edge((3, 1), (4, 1), "->")
        edge((4, 1), (5, 1), "->")
        edge((5, 1), (6, 1), "->")
        edge((1, 0), (1, 1), "->")
        edge((2, 0), (2, 1), "->")
        edge((3, 0), (3, 1), "->")
        edge((4, 0), (4, 1), "->")
        edge((5, 0), (5, 1), "->")
      }))
      
      - By our inductive hypothesis, the first two vertical maps are isomorphisms. By the discussion above on sheaves of the shape $ul(t)_* ul(Lambda)$, the fourth vertical map is an isomorphism. 

        Thus, by the injective four lemma, the third vertical arrow is injective. Thus $L^q (cal(F)) -> S^q (cal(F))$ is injective for all constructible sheaves $cal(F)$, hence for all sheaves by the previous bullet. 

        In particular $L^q (cal(R)) -> S^q (cal(R))$, the fifth vertical arrow, is injective, so by the surjective four lemma, the third vertical arrow is surjective. Thus $L^q (cal(F)) -> S^q (cal(F))$ is bijective for all constructible sheaves $cal(F)$, hence for all sheaves $cal(F)$ by the previous bullet.

    Setting $cal(F) = ul(Lambda)$ concludes the proof.  
  ]

  #lemma(name: <loc-acyc-constancy-of-pushforward>)[
    Let $Lambda$ be a noetherian ring s.t. every finite $Lambda$-module embeds into a finite free $Lambda$-module. Let $f: X -> S$ be a qcqs morphism between locally noetherian schemes, locally acyclic relative to $cal(K) in D^b_#[ctf] (X_et, Lambda)$. 

    Suppose that we have a complex $A in D^b (Lambda)$ and a morphism $alpha: ul(A)_X -> cal(K)$, s.t. for every geometric point $ol(s)$ of $S$, the map induced by $alpha$: 
    $
      A -> R Gamma(X_(ol(s)), ul(A)) -> R Gamma(X_(ol(s)), cal(K)|_(X_(ol(s))))
    $
    is an isomorphism. Then the map: 
    $
      beta: ul(A)_S -> R f_* cal(K)
    $
    induced from $alpha$ by adjunction is an isomorphism. 
  ]
  #proof[
    By unfolding the definitions, it can be checked that the isomorphisms $A -> R Gamma(X_(ol(s)), cal(K)|_(X_(ol(s))))$ are compatible with cospecializations between different geometric fibers. Thus, all cospecializations of $f$ on $cal(K)$ are isomorphisms. 

    For every geometric point $ol(s)$ of $S$, consider the map $tilde(f)_(ol(s)): X times_S tilde(S)_(ol(s)) -> tilde(S)_(ol(s))$. $tilde(S)_(ol(s))$ is a projective limit of affine etale neighborhoods of $ol(s)$ in $S$, and is hence a projective limit of quasi-finite $S$-schemes under affine transition maps. Thus by @loc-acyc-and-limits-of-qfinite, $tilde(f)_(ol(s))$ is locally acyclic relative to $cal(K)|_(X times_S tilde(S)_(ol(s)))$. 

    Furthermore, the cospecializations of $tilde(f)_(ol(s))$ on $cal(K)|_(X times_S tilde(S)_(ol(s)))$ are exactly the same as the cospecializations of $f$ on $cal(K)$ by definition. Thus, all cospecializations of $tilde(f)_(ol(s))$ on $cal(K)|_(X times_S tilde(S)_(ol(s)))$ are isomorphisms. 

    The previous lemma is now applicable, and we have a base change isomorphism: 
    $
      R Gamma(X times_S tilde(S)_(ol(s)), cal(K)|_(X times_S tilde(S)_(ol(s)))) cong R tilde(f)_(ol(s),*) (cal(K)|_(X times_S tilde(S)_(ol(s))))_(ol(s)) cong R Gamma(X_(ol(s)), cal(K)|_(X_(ol(s))))
    $
    However, by @derived-stalks-of-derived-pushforward, $R Gamma(X times_S tilde(S)_(ol(s)), cal(K)|_(X times_S tilde(S)_(ol(s)))) cong (R f_* cal(K))_(ol(s))$. Thus, we have shown that: 
    $
      (R f_* cal(K))_(ol(s)) cong R Gamma(X_(ol(s)), cal(K)|_(X_(ol(s)))) cong A
    $
    One may check that this isomorphism is exactly the morphism $beta_(ol(x)): A -> (R f_* cal(K))_(ol(s))$. Thus $beta$ is an isomorphism. 
  ]

  Recall that we intend to show that the map $ul(cal(K)_(ol(x))) -> R f_(ol(t),*) (cal(K)|_(X_(ol(t))))$, induced from $ul(cal(K)_(ol(x))) -> cal(K)|_(X_(ol(t)))$, is an isomorphism. $ol(t) -> S$ is quasi-finite, so by @loc-acyc-and-limits-of-qfinite, $f_(ol(t))$ is locally acyclic relative to $cal(K)|_(X_(ol(t)))$. Now for a geometric point $ol(u)$ of $Y_(ol(t))$, 
  $
    R Gamma(X_(ol(t)) times_(Y_(ol(t))) ol(u), cal(K)|_(X_(ol(t)) times_(Y_(ol(t))) ol(u))) cong R Gamma(X_(ol(u)), cal(K)|_(X_(ol(u))))
  $
  However, $X_(ol(u)) = ol(u) times_Y X = ol(u) times_(tilde(Y)_(ol(y))) tilde(X)_(ol(x)) = F_(ol(x),ol(u))$ is a vanishing cycle variety for $f: X -> Y$, so $R Gamma(X_(ol(u)), cal(K)|_(X_(ol(u)))) = R Gamma(F_(ol(x),ol(u)), cal(K)|_(F_(ol(x),ol(u)))) = cal(K)_(ol(x))$ by definition of local acyclicity. Thus we have natural isomorphisms $cal(K)_(ol(x)) cong R Gamma(X_(ol(t)) times_(Y_(ol(t))) ol(u), cal(K)|_(X_(ol(t)) times_(Y_(ol(t))) ol(u)))$. The previous lemma can now be invoked to show that we have the desired isomorphism: 
  $
    ul(cal(K)_(ol(x))) cong R f_(ol(t),*) (cal(K)|_(X_(ol(t))))
  $
]

#lemma(name: <loc-acyc-pass-to-lcc-sheaves>)[
  Let $f: X -> S$ be a locally acyclic scheme morphism. Let $Lambda$ be a torsion noetherian ring whose torsion order $n in cal(O)_S^times$. 
  
  Then for any locally constant sheaf $cal(F) in cAb(X_et, Lambda)$ of $Lambda$-modules, $f$ is locally acyclic relative to $cal(F)$. 
]
#proof[
  Since local acyclicity only depends on the strict local rings, for $ol(x)$ of $X$ and $ol(s) = f(ol(x))$, to show that $f$ is locally acyclic relative to $cal(F)$ at $ol(x)$, it suffices to show that $tilde(X)_(ol(x)) -> tilde(S)_(ol(s))$ is locally acyclic relative to $cal(F)|_(tilde(X)_(ol(x)))$. Now $tilde(X)_(ol(x)) -> tilde(S)_(ol(s))$ is locally acyclic, so we may replace $f$ by it, and assume that $X, S$ are spectra of strict henselian local rings. 

  Now $cal(F)$ is an l.c.c. sheaf of $Lambda$-modules on $X$. Thus by definition there exists an etale cover $U -> X$ s.t. $cal(F)|_U$ is constant. The special fiber of $U -> X$ gives at least a section $s: X -> U$ by @equiv-defns-of-henselian (4), since $X$ is the spectrum of a strict henselian local ring, so $s^(-1) (cal(F)|_U) = cal(F)$ is constant. Thus $cal(F) = ul(M)$ for a $Lambda$-module $M$. Since $Lambda$ is $n$-torsion, $M$ is an $n$-torsion abelian group, so as abelian groups: 
  $
    M = oplus.big_i ZZ\/d_i
  $
  for some $d_i|n$. By the limit formula @limit-formula-for-sheaves, 
  $
    H^q (F_(ol(x),ol(t)), ul(M)) = H^q (F_(ol(x),ol(t)), oplus.big_i ZZ\/d_i) = oplus.big_i H^q (F_(ol(x),ol(t)), ZZ\/d_i) = cases(
      0 &\, q >= 1, 
      oplus.big_i ZZ\/d_i = M &\, q = 0
    )
  $
  where we used local acyclicity of $f$ relative to each $ZZ\/d_i$ (where $d_i | n$ is in $cal(O)_S^times$). We are thereby done showing local acyclicity of $f$ relative to $cal(F) = ul(M)$. 
]
