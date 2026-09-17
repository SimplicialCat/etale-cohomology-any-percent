#import "void-import.typ": *

== Radicial morphisms

This section is a short interlude on radicial morphisms. They are somewhat opposite to etale morphisms, in the sense that etale morphisms feature separable field extensions, while radicial morphisms feature purely inseparable field extensions. 

#proposition(name: <equiv-defns-of-radicial>)[
  (#cite-stacks("01S4")[Lemma 29.10.2]) Let $f: X -> Y$ be a scheme morphism. TFAE: 

  + $f$ is universally injective; 

  + $f$ is injective and for every $f(x) = y$, $k(x)\/k(y)$ is a purely inseparable field extension; 

  + For every field $K$, the map: #h(1fr)
    $
      Hom(Spec(K), X) -> Hom(Spec(K), Y)
    $
    is injective; 

  + The diagonal map $Delta_(X\/Y): X -> X times_Y X$ is surjective. 
]
#proof[
  (2)$<==>$(3): 
  #proof[
    It is clear that: 
    $
      Hom(Spec(K), X) = {(x, phi): x in X, phi: k(x) arrow.hook K}
    $
    Thus, the preimage of some $(y, psi) in Hom(Spec(K), Y)$ is those $(x, phi)$ s.t. $f(x) = y$ and the composition $k(y) -> k(x) ->^phi K$ is exactly $psi$. 

    (3)$==>$(2): Fix $y in Y$. If $f(x_1) = f(x_2) = y$ for different points $x_(1,2) in X$, take a field $K\/k(y)$ containing both $k(x_1)$ and $k(x_2)$ (say a residue field of $k(x_1) otimes_(k(y)) k(x_2)$). Then $k(y) -> K$ factors through both $k(x_1)$ and $k(x_2)$, giving two different lifts of $Hom(Spec(K), Y)$. This is a contradiction. Thus $f$ is injective. 

    Suppose that there exists $x in X$ s.t. $f(x) = y$. Then taking $K = ol(k(x))$, we see that $k(x)$ embeds into $ol(k(x))$ in a unique way. This forces $k(x)\/k(y)$ to be purely inseparable, since otherwise its separable component would have nontrivial embeddings. 

    (2)$==>$(3): Suppose that $(y, psi) in Hom(Spec(K), Y)$ has two lifts $(x_(1,2), phi_(1,2))$. Then since $f$ is injective, $x_1 = x_2 = x$, and $phi_(1,2)$ are two embeddings $k(x) -> K$ s.t: 
    $
      k(y) -> k(x) ->^(phi_(1,2)) K
    $
    are both the embedding $psi$. However, $k(x)\/k(y)$ is purely inseparable. Thus a compatible embedding $k(x) -> K$, if exists, must be unique. (Indeed, $k(x)$ is obtained from $k(y)$ by adjoining $p^m$-th roots. Over characteristic $p$, such roots are unique.)
  
    #suppress-qed
  ]

  (1)$==>$(2): 
  #proof[
    $f$ is tautologically injective. If $f(x) = y$, base change $f$ along $k(y) -> Y$ yields $f: X_y -> Spec(k(y))$. $X_y$ is necessarily a single point with reduction $Spec(k(x))$. 
    
    Now base change further to $ol(k(y))$, and so $X_y otimes_(k(y)) ol(k(y))$ is a single point. $X_y$ has reduction $Spec(k(x))$, so $Spec(k(x) otimes_(k(y)) ol(k(y)))$ is a closed subscheme of $X_y otimes_(k(y)) ol(k(y))$ defined by a nilpotent ideal, and shares the same underlying space. Thus $Spec(k(x) otimes_(k(y)) ol(k(y)))$ is a single point. 
    
    This forces $k(x)\/k(y)$ to be purely inseparable, since otherwise the separable closure of $k(y)$ in $k(x)$ would split into multiple copies of $ol(k(y))$ upon tensoring $ol(k(y))$. 

    #suppress-qed
  ]

  (3)$==>$(1): 
  #proof[
    To show that $f$ is universally injective, it suffices to show that every nonempty fiber of a base change of $f$ is a single point. That is, for any $psi: Spec(K) -> Y$, we need to show that the base change: 
    $
      f_psi: X_K -> Spec(K)
    $
    has $X_K$ either empty or a single point. Indeed, if $X_K$ has two distinct points $x_1, x_2$, we may pick a field extension $L\/K$ containing both $k(x_1)$ and $k(x_2)$. Then we have distinct maps $Spec(L) -> X_K -> X$ defined by $x_1$ and $x_2$. Upon composing with $f$, they both become the same map $Spec(L) -> Spec(K) -> Y$. This contradicts (3). 
    #suppress-qed
  ]

  We have thus shown that (1)(2)(3) are all equivalent. 

  (1)$==>$(4): Since $f$ is universally injective, the projection $p_1: X times_Y X -> X$, being a base change of $f$, is injective. Thus $Delta_(X\/Y)$, being a section of $p_1$, is surjective. 

  (4)$==>$(2): //Suppose that $(x_(1,2), phi_(1,2)) in Hom(Spec(K), X)$ are both sent to $(y, psi) in Hom(Spec(K), Y)$. Recall that: 
  Recall that: 

  - Points of $X times_S Y$ correspond to quadruples $(x, y, s, frak(p))$ where $x in X, y in Y$ both lie above $s in S$, and $frak(p) in Spec(k(x) otimes_(k(s)) k(y))$. (#cite-stacks("01JT")[Lemma 26.17.5])

  The diagonal $X -> X times_Y X$ then sends $x$ to $(x, x, f(x), ker(k(x) otimes_(k(f(x))) k(x) -> k(x)))$. Since the diagonal is surjective, $x_1, x_2$ with $f(x_1) = f(x_2)$ are necessarily equal, and for every $x in X$ with $y = f(x)$, $k(x) otimes_(k(y)) k(x)$ only has one prime ideal. Thus $ker(k(x) otimes_(k(y)) k(x) -> k(x))$ is the nilradical of $k(x) otimes_(k(y)) k(x)$, and so every element of the form $a otimes 1 - 1 otimes a in k(x) otimes_(k(y)) k(x)$ is nilpotent. 

  - For every $a in k(x)$, if $a$ were transcendental over $k(y)$, then $k(y)(a) otimes_(k(y)) k(y)(a)$ is a localization of $k(y)[X, Y]$ and is integral, and $a otimes 1 - 1 otimes a$ corresponds to $X - Y$. Its nilpotence is thus absurd. Thus $a$ is algebraic over $k(y)$, say with minimal polynomial $p(X)$. Then: 
    $
      k(y)(a) otimes_(k(y)) k(y)(a) cong (k(y)(a)[T])/((p(T)))
    $
    and the element $a otimes 1 - 1 otimes a$ corresponds to $T - a$. By nilpotence, $p(T) divides (T-a)^m$ for some power $m$. Thus $p(T)$ has only the root $a$ in $ol(k(y))$. Thus $a$ is inseparable over $k(y)$. 

  Thus $k(x)\/k(y)$ is purely inseparable. 
]

#definition(name: <defn-radicial-morphism>)[
  A morphism $f: X -> Y$ satisfying the four equivalent conditions above is called *radicial*. 
]

#properties(name: <radicial-morphism-first-props>)[
  0. Radicial morphisms are stable under base change and composition. 

  1. Radicial morphisms are separated. 

  2. A morphism $f: X -> Y$ is a universal homeomorphism, if and only if it is surjective, radicial and integral. 

  3. A morphism $f: X -> Y$ is an open immersion, if and only if it is radicial and etale. 
]
#proof[
  (0) This is trivial under the characterization that radicial $<==>$ universally injective. 

  (1) For a radicial morphism $f: X -> Y$, the diagonal $Delta_(X\/Y): X -> X times_Y X$, automatically known to be an immersion, is surjective. It is thus a closed immersion, hence separated. 

  (2)($<==$) Surjectivity is universal, radicial morphisms are universally injective, and integral morphisms are universally closed. Thus $f$ is universally bijective and universally closed, hence a universal homeomorphism. 

  ($==>$) Universal homeomorphisms are tautologically surjective and universally injective (i.e. radicial), so it remains to check integrality. 

  #lemma[
    If $f: X -> Y$ is a scheme morphism that is a homeomorphism, then $f$ is affine. 
  ]
  #proof[
    Affineness can be checked locally on base, so we may assume that $Y$ is affine. 

    For any $y in Y$ with $x = f^(-1)(y) in X$, we may pick an affine open $x in U subset X$. Now $f(U)$ is open in $f(X)$, so we may pick a function $u in A$ s.t. $y in D(u) subset f(U)$. Consequently, $f^(-1) (D(u)) = D(u) times_Y U = D(u) times_Y U$ is a fiber product of two affine schemes over affine base, and is hence affine. Thus every point of $Y$ has an affine neighborhood pulling back to an affine open of $X$ under $f$. Since affineness is local on base, $f$ is affine. 
  ]

  Thus $f$ is known to be affine. $f$ is also universally closed. To proceed: 
  #lemma[
    An affine universally closed morphism is integral. 
  ]
  #proof[
    We may check locally on base and assume that $f: X = Spec(B) -> Spec(A) = Y$ is universally closed. We'll reduce to the case that $A, B$ are both integral domains and $A subset B$ first. Assume for contradiction that $b in B$ is not integral over $A$. Then: 
    $
      "ev"_b: A[T] ->> C := A[b] subset B, p(T) |-> p(b)
    $
    has its kernel $I subset A[T]$ containing no monic polynomial. The monic polynomials form a multiplicative subset $S$ of $A[T]$, and so $I$ defines a non-unit ideal of $S^(-1) A[T]$. Thus by taking a prime of $S^(-1) A[T]$ containing $I$, we see that there exists $frak(p) in Spec(A[T])$ s.t. $I subset frak(p)$, and $frak(p)$ contains no monic polynomial. Let $frak(q) = frak(p)\/I in Spec(A[T]\/I) cong Spec(C)$. Then $b in C\/frak(q)$ is still not integral over $A$, otherwise a monic polynomial would be in $frak(p)$. Now: 

    - $Spec(B) -> Spec(A)$ is universally closed and factors as $Spec(B) -> Spec(C) -> Spec(A)$. 
    
      Now the graph $Spec(B) -> Spec(B otimes_A C)$ of $Spec(B) -> Spec(C)$ is a closed immersion as a base change of the diagonal of $Spec(B) -> Spec(A)$, and is universally closed. $Spec(B otimes_A C) -> Spec(C)$ is a base change of $Spec(B) -> Spec(A)$ and is universally closed. Thus, $Spec(B) -> Spec(C)$ being their composition is universally closed. It is dominant since $C subset B$, so it is surjective. 

    Hence, we may pick $frak(r) in Spec(B)$ s.t. $frak(q) = C inter frak(r)$. We then have an inclusion $C\/frak(q) arrow.hook B\/frak(r)$. Since $[b] in C\/frak(q)$ is not integral over $A$, neither is $[b] in B\/frak(r)$. Thus if we are done with the case of $B$ integral, then $Spec(B\/frak(r)) -> Spec(A)$ would be integral, raising a contradiction. 

    We may thus assume that $B$ is integral. Now let $frak(p) = ker(A -> B) in Spec(A)$. Then we have a factorization $Spec(B) -> Spec(A\/frak(p)) -> Spec(A)$. By the same argument as done previously for $Spec(B) -> Spec(C) -> Spec(A)$, $Spec(B) -> Spec(A\/frak(p))$ is surjective universally closed. Also it suffices to show that $B$ is integral over $A\/frak(p)$. Thus it is safe to replace $A$ with $A\/frak(p)$, and assume that $A, B$ are both integral, $A subset B$. 
    
    By the valuative criterion for universal closedness (#cite-stacks("01KF")[Proposition 26.20.6]), for every valuation ring $R$ with fraction field $K$, the dotted diagonal map fitting in the following commutative diagram always exists: 
    // https://q.uiver.app/#r=typst&q=WzAsNCxbMCwwLCJBIl0sWzAsMSwiQiJdLFsxLDEsIksiXSxbMSwwLCJSIl0sWzMsMiwiIiwwLHsic3R5bGUiOnsidGFpbCI6eyJuYW1lIjoiaG9vayIsInNpZGUiOiJ0b3AifX19XSxbMCwxXSxbMCwzXSxbMSwyXSxbMSwzLCIiLDEseyJzdHlsZSI6eyJib2R5Ijp7Im5hbWUiOiJkYXNoZWQifX19XV0=
    #align(center, diagram({
      node((0, 0), [$A$])
      node((0, 1), [$B$])
      node((1, 1), [$K$])
      node((1, 0), [$R$])
      edge((1, 0), (1, 1), "hook->")
      edge((0, 0), (0, 1), "->")
      edge((0, 0), (1, 0), "->")
      edge((0, 1), (1, 1), "->")
      edge((0, 1), (1, 0), "-->")
    }))
    Take $K$ to be $Frac(B)$ and $B -> K$ to be the natural inclusion. Then the valuative criterion says that: 

    - For every valuation ring $R$ of $K$ containing $A$, $R$ contains $B$ too. 

    By the following algebraic fact: 
    #lemma[
      (@cite-atiyah-macdonald[Corollary 5.22]) Let $A$ be a subring of a field $K$. Then the integral closure of $A$ in $K$ is exactly the intersection of all valuation rings of $K$ containing $A$.
    ]

    We see that $B$ is contained in the integral closure of $A$ in $K$, thus integral over $A$. 
  ]

  (3)($==>$) is easy, as it is direct to check that open immersions are etale and radicial. It suffices to prove ($<==$). Suppose that $f: X -> Y$ is etale and radicial. Since etale morphisms are open, $f(X) -> Y$ is an open immersion, and $f: X -> f(X)$ is surjective etale radicial. Replacing $Y$ with $f(X)$, we may thus assume that $f$ is additionally surjective. Thus, $f$ is universally injective, surjective, and also universally open since it is etale. Thus $f$ is a universal homeomorphism, hence integral. Etale morphisms are locally of finite presentation. Thus, $f$ is finite. Since $f$ is flat, this shows that $f$ is in fact finite locally free. To conclude the proof, note that: 
  $
    "rk"_(cal(O)_(Y,f(x))) (cal(O)_(X,x)) = dim_(k(f(x))) (cal(O)_(X,x)\/frak(m)_(f(x))cal(O)_(X,x)) = dim_(k(f(x))) (k(x))
  $
  by etaleness. Since $k(x)\/k(f(x))$ is finite separable by etaleness, and purely inseparable by radicialness, it must be trivial. Thus $dim_(k(f(x))) (k(x)) = 1$ and so every $cal(O)_(Y,f(x)) -> cal(O)_(X,x)$ is an isomorphism. Thus $X -> Y$ is an isomorphism. 
]

#corollary(name: <adjoining-pth-root-in-char-p-is-univ-homeo>)[
  Let $A$ be a ring in which $p = 0$ for a prime number $p$. Then for any $a_1, dots.c, a_t in A$ and $m_1, dots.c, m_t >= 1$, the map: 
  $
    Spec((A[T])/((T^(p^(m_1)) - a_1, dots.c, T^(p^(m_t)) - a_t))) -> Spec(A)
  $
  is a finite universal homeomorphism. 
]
#proof[
  By adjoining roots one by one, we may assume that $t = 1$. By taking roots by degree $p$ at a time, we may assume that $m_1 = 1$. Thus we need to show that: 
  $
    phi: Spec(A[T]\/(T^p - a)) -> Spec(A)
  $
  is a finite universal homeomorphism. It is finite as can be seen directly. For every point $frak(p) in Spec(A)$, consider the fiber: 
  $
    Spec(k(frak(p))[T]\/(T^p - a)) -> Spec(k(frak(p)))
  $
  Now: 

  - If $a$ has a $p$-th root in $k(frak(p))$, then: #h(1fr)
    $
      k(frak(p))[T]\/(T^p - a) cong k(frak(p))[T]\/((T - a^(1\/p))^p)
    $
    is a single nonreduced point with residue field $k(frak(p))$. Otherwise, $k(frak(p))[T]\/(T^p - a)$ is a purely inseparable extension of $k(frak(p))$. 

    Thus every fiber of $phi$ is nonempty, making $phi$ surjective. Every fiber of $phi$ also consists of a single point with purely inseparable residue field extension, so $phi$ is radicial by @equiv-defns-of-radicial (2). 
]
