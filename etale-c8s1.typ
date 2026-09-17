#import "void-import.typ": *

The sequence of reductions done in this section can be seen both in #cite-stacks("0EZQ")[Section 59.86] and @cite-lei-fu[Section 7.6]. 

The theory of local acyclicity, roughly speaking, consists of the following statements: 

+ (Smooth base change) In a Cartesian diagram: #h(1fr)
  // https://q.uiver.app/#r=typst&q=WzAsNCxbMCwxLCJYIl0sWzEsMSwiUyJdLFswLDAsIlgnIl0sWzEsMCwiUyciXSxbMywxLCJnIl0sWzIsMCwiZyciLDJdLFsyLDMsImYnIl0sWzAsMSwiZiIsMl1d
  #align(center, diagram({
    node((-1, 1), [$X$])
    node((0, 1), [$S$])
    node((-1, 0), [$X'$])
    node((0, 0), [$S'$])
    node((-0.7, 0.3), $cart$)
    edge((0, 0), (0, 1), [$g$], label-side: left, "->")
    edge((-1, 0), (-1, 1), [$g'$], label-side: right, "->")
    edge((-1, 0), (0, 0), [$f'$], label-side: left, "->")
    edge((-1, 1), (0, 1), [$f$], label-side: right, "->")
  }))
  in which $f$ is qcqs and $g$ is smooth, given any $n$-torsion abelian sheaf $cal(F)in cAb(X_et, ZZ\/n)$ on $X$ s.t. $n in cal(O)_S (S)^times$, the base change morphism: 
  $
    g^(-1) R^q f_* cal(F) -> R^q f'_* g'^(-1) cal(F)
  $
  is an isomorphism. 

+ (Local acyclicity of smooth morphisms) Given a smooth morphism $f: X -> S$ with $f(x) = s$, an algebraic geometric point $ol(x)$ above $x$, and a pair of algebraic geometric points $ol(s), ol(t)$ of $S$ where $t succ s$, 
  $
    H^q (tilde(X)_(ol(x)) times_(tilde(S)_(ol(s))) ol(t), ul(ZZ\/n)) = cases(
      ZZ\/n &\, q = 0, 
      0 &\, q>=1
    )
  $
  for any natural number $n in cal(O)_S (S)^times$. 

+ (Proper smooth base change) Suppose that $f: X -> S$ is proper and smooth between noetherian schemes. Then for any $n$-torsion l.c.c. sheaf $cal(F) in cAb(X_et, ZZ\/n)$ where $n in cal(O)_S (S)^times$, $R^q f_* cal(F)$ is l.c.c. 

+ (Finiteness of $R f_!$) Suppose that $f: X -> S$ is separated of finite type between noetherian schemes. Then for any constructible sheaf $cal(F) in cAb(X_et, ZZ\/n)$, $R^q f_! cal(F)$ is constructible. In other words, $R f_!$ is a functor $D^b_c (X_et, Lambda) -> D^b_c (S_et, Lambda)$. 

Logically, (1) smooth base change is equivalent to (2) local acyclicity of smooth morphisms, with (3) smooth proper base change and (4) finiteness of $R f_!$ depending on (1)(2). The motivation to develop this theory lies in (3) and the sheaf-theoretic result @descs-of-lcc-sheaves (a)$<==>$(b): 

- A sheaf $cal(F) in cAb(X_et)$ with finite stalks is l.c.c. if and only if for every pair $t succ s$ in $X$, the specialization map $cal(F)_(ol(t)) -> cal(F)_(ol(s))$ is an isomorphism. 

This allows us to ask the question: For a proper morphism $f: X -> S$, when is $R^q f_* ul(ZZ\/n)$ l.c.c? The finiteness of stalks may be established by some reduction to curves, so all that is required is the specialization maps to be isomorphisms. By proper base change, this amounts to an isomorphism: 
$
  H^q (X_(ol(t)), ul(ZZ\/n)) ->^tilde H^q (X_(ol(s)), ul(ZZ\/n))
$
We will see how this morphism can be expressed by embedding both geometric fibers in $X times_S tilde(S)_(ol(s))$, then translated through a vanishing cycle construction to the statement (2). Then through devissage arguments, (3) will imply (4). 

There is a final side remark regarding coefficient rings. 

#remark[
  The main application of the theory of etale cohomology is the proof of the Weil conjectures, which requires establishing the theory of $ell$-adic sheaves. That is, over a scheme $X$ with characteristic $p$, for every $ell != p$, there is a cohomology theory with coefficients in $ol(QQ_ell)$. Such a cohomology theory is established by doing it over every finite extension $E\/QQ_ell$, by passing from the ring of integers $cal(O)_E$, which is itself constructed by a limit construction from etale sheaves in coefficients $cal(O)_E\/frak(m)_E^N$. 

  Thus, the most important coefficient rings, and a class of coefficient rings enough for application, are the rings $Lambda = cal(O)_E\/frak(m)_E^N$ for a finite extension $E\/QQ_ell$ with $ell in cal(O)_X^times$. (This includes the rings $ZZ\/ell^N$.) These $Lambda$ together with $Lambda = ZZ\/n, n in cal(O)_X^times$ have the following desirable properties: 

  - $Lambda$ is a torsion ring with torsion coefficient in $cal(O)_X^times$; 

  - $Lambda$ is a finite ring, so constructible sheaves of $Lambda$-modules are just sheaves of $Lambda$-modules constructible as a sheaf of abelian groups; 

  - Every finite $Lambda$-module admits an injection into a free $Lambda$-module of finite rank; 

  - $Lambda$ is an injective $Lambda$-module. 

  Thus, whenever you see one of these seemingly arbitrary conditions in the hypotheses of a proposition, you can stay motivated and know that such conditions are satisfied in practice. 
]

Throughout this chapter, $Lambda$ is assumed to be a torsion ring. 

== General reduction on base changes

#notation(name: <constructible-finite-tor-derived-category>)[
  We use the notion $D^b_#[ctf] (X_et, Lambda)$ to denote the triangulated category of bounded complexes of etale sheaves of $Lambda$-modules on $X$ with constructible cohomology sheaves, and with finite Tor-dimension (i.e. the functor $cal(K) Lotimes_Lambda -$ is bounded above and below). Equivalently, such a complex is in $D^b_c$ and has bounded flat resolution. 

  #lemma(name: <resolution-of-ctf-complexes>)[
    (#cite-stacks("03TT")[Lemma 59.77.3]) Let $X$ be a noetherian scheme, and let $cal(K) in D^b_#[ctf] (X_et, Lambda)$ satisfy that $cal(K) Lotimes_Lambda cal(G) in D_([a,b]) (X_et, Lambda)$ for all sheaves $cal(G) in cAb(X_et, Lambda)$. Then $cal(K)$ can be represented by a complex: 
    $
      0 -> cal(F)^a -> cal(F)^(a+1) -> dots.c -> cal(F)^b -> 0
    $ 
    in which every $cal(F)^q = j_(q,!) ul(Lambda)$ is constructible and flat. 
  ]
  #proof[
    We argue by induction on $b-a$. If $a=b$, then $cal(K) = h^a (cal(K))[-a]$. The hypothesis then says that $h^a (cal(K))$ is constructible flat, so the claim follows. 
    
    Assume now that $b>a$, and represent $cal(K)$ by a K-flat complex $dots.c -> cal(K)^a -> cal(K)^(a+1) -> dots.c -> cal(K)^b -> dots.c$ consisting of flat sheaves. By constructibility, there is an etale morphism $j: U -> X$ with $U$ affine, and a surjection: 
    $
      j_! ul(Lambda) -> h^b (cal(K))
    $
    This is a global section of $h^b (cal(K))|_U$. Since $ker(cal(K)^b -> cal(K)^(b+1)) -> h^b (cal(K))$ is a surjection, there exists a further affine etale cover $U' -> U$ s.t. this section lifts to a global section of $ker(cal(K)^b -> cal(K)^(b+1))|_(U')$. Put $j': U' -> X$, and we have a map $cal(F) := j'_! ul(Lambda) -> ker(cal(K)^b -> cal(K)^(b+1))$, surjective when mapped further to $h^b (cal(K))$. Now we form a distinguished triangle:
    $
      cal(F)[-b] -> cal(K) -> cal(L) ->^(+1)
    $
    The complex $cal(L) in D^b_#[ctf] (X_et, Lambda)$, and has Tor-amplitude contained in $[a,b-1]$. Indeed, the map $cal(F) -> h^b (cal(K))$ is surjective. Thus tensoring with an arbitrary sheaf $cal(G)$, we have a long exact sequence: 
    $
      dots.c -> h^q (cal(G) Lotimes_Lambda cal(K)) -> h^q (cal(G) Lotimes_Lambda cal(L)) -> h^(q-b+1) (cal(G) Lotimes_Lambda cal(F)) -> dots.c
    $
    Now: 

    - The term $h^q (cal(G) Lotimes_Lambda cal(K))$ vanishes unless $q in [a,b]$, and the term $h^(q-b+1) (cal(G) Lotimes_Lambda cal(F))$ vanishes unless $q = b-1$ (since $cal(F)$ is constructible flat). Thus whenever $q<a$ or $q>b$, $h^q (cal(G) Lotimes_Lambda cal(L)) = 0$. 

    - For $h^b$, we have: #h(1fr)
      $
        dots.c -> cal(G) otimes_Lambda cal(F) -> h^b (cal(G) Lotimes_Lambda cal(K)) -> h^b (cal(G) Lotimes_Lambda cal(L)) -> 0
      $
      The first map factors as: 
      $
        cal(G) otimes_Lambda cal(F) -> cal(G) otimes_Lambda h^b (cal(K)) ->^tilde h^b (cal(G) Lotimes_Lambda cal(K)).
      $
      The first arrow is surjective by right exactness of tensor product. The second is the edge isomorphism of the hypercohomology spectral sequence
      $
        E_2^(p,q) = "Tor"_p^Lambda (cal(G), h^q (cal(K))) => h^(q-p)(cal(G) Lotimes_Lambda cal(K)),
      $
      where $h^q (cal(K))=0$ for $q>b$. Hence $h^b (cal(G) Lotimes_Lambda cal(L)) = 0$.

    Thus, $cal(L)$ has Tor-amplitude in $[a,b-1]$. By induction, represent $cal(L)$ by a complex: 
    $
      cal(F)^a -> dots.c -> cal(F)^(b-1)
    $
    in which every $cal(F)^q$ is constructible flat. The $+1$ morphism $cal(L) -> cal(F)[-b+1]$ is represented by a morphism $cal(F)^(b-1) -> cal(F)$ annihilating the image of $cal(F)^(b-2)$. Its cone, shifted by $-1$, represents $cal(K)$ and is precisely
    $
      0 -> cal(F)^a -> dots.c -> cal(F)^(b-1) -> cal(F) -> 0
    $
    This completes the induction.
  ]
]

#construction(name: <relative-base-change-constr>)[
  (Relative base change) For a Cartesian diagram, 
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
  and $cal(L) in D(Y'_et, Lambda)$, we define a relative base change map w.r.t. $cal(K)$: 
  $
    g^(-1) R f_* cal(K) Lotimes_Lambda cal(L) --> R f'_* g'^(-1) cal(K) Lotimes_Lambda cal(L) --> R f'_* (g'^(-1) cal(K) Lotimes_Lambda f'^(-1) cal(L))
  $
  Here, the first map is a conventional base change map, and the second map is a projection map for $R f'_*$. 

  By proper base change and the projection formula, such a relative base change map is an isomorphism whenever $f$ is proper. 

  By naturalities of base change maps and projection maps, the relative base change map enjoys the following naturality statements: 

  - For a vertical concatenation of Cartesian diagrams, #h(1fr)
    // http://localhost:8000/#r=typst&q=WzAsNixbMCwxLCJYJyJdLFsxLDEsIlknIl0sWzAsMiwiWCJdLFsxLDIsIlkiXSxbMSwwLCJZJyciXSxbMCwwLCJYJyciXSxbMiwzLCJmIiwyXSxbMCwxLCJmJyJdLFsxLDMsImciXSxbMCwyLCJnJyIsMl0sWzUsNCwiZicnIl0sWzQsMSwiaCJdLFs1LDAsImgnIiwyXV0=
    #align(center, diagram({
      node((0, 0), [$X'$])
      node((1, 0), [$Y'$])
      node((0, 1), [$X$])
      node((1, 1), [$Y$])
      node((1, -1), [$Y''$])
      node((0, -1), [$X''$])
      edge((0, 1), (1, 1), [$f$], label-side: right, "->")
      edge((0, 0), (1, 0), [$f'$], label-side: left, "->")
      edge((1, 0), (1, 1), [$g$], label-side: left, "->")
      edge((0, 0), (0, 1), [$g'$], label-side: right, "->")
      edge((0, -1), (1, -1), [$f''$], label-side: left, "->")
      edge((1, -1), (1, 0), [$h$], label-side: left, "->")
      edge((0, -1), (0, 0), [$h'$], label-side: right, "->")
    }))
    the relative base change $h^(-1) g^(-1) R f_* cal(K) Lotimes_Lambda h^(-1) cal(L) -> R f''_* (h'^(-1) g'^(-1) cal(K) Lotimes_Lambda h^(-1) f''^(-1) cal(L))$ relative to $h^(-1) cal(L)$, is the composition: 
    $
      h^(-1) g^(-1) R f_* cal(K) Lotimes_Lambda h^(-1) cal(L) &cong h^(-1) (g^(-1) R f_* cal(K) Lotimes_Lambda cal(L)) \
      &-> h^(-1) R f'_* (g'^(-1) cal(K) Lotimes_Lambda f'^(-1) cal(L)) \
      &-> R f''_* h'^(-1) (g'^(-1) cal(K) Lotimes_Lambda f'^(-1) cal(L)) \
      &cong R f''_* (h'^(-1) g'^(-1) cal(K) Lotimes_Lambda h^(-1) f''^(-1) cal(L))
    $
    of the relative base change of the lower square w.r.t. $cal(L)$, and the base change of the upper square. 

  - For a horizontal concatenation of Cartesian squares, 
    // http://localhost:8000/#r=typst&q=WzAsNixbMSwwLCJYJyJdLFsyLDAsIlknIl0sWzEsMSwiWCJdLFsyLDEsIlkiXSxbMCwxLCJaIl0sWzAsMCwiWiciXSxbMiwzLCJmIiwyXSxbMCwxLCJmJyJdLFsxLDMsImciXSxbMCwyLCJnJyIsMl0sWzQsMiwiaCIsMl0sWzUsMCwiaCciXSxbNSw0LCJnJyciLDJdXQ==
    #align(center, diagram({
      node((0, 0), [$X'$])
      node((1, 0), [$Y'$])
      node((0, 1), [$X$])
      node((1, 1), [$Y$])
      node((-1, 1), [$Z$])
      node((-1, 0), [$Z'$])
      edge((0, 1), (1, 1), [$f$], label-side: right, "->")
      edge((0, 0), (1, 0), [$f'$], label-side: left, "->")
      edge((1, 0), (1, 1), [$g$], label-side: left, "->")
      edge((0, 0), (0, 1), [$g'$], label-side: right, "->")
      edge((-1, 1), (0, 1), [$h$], label-side: right, "->")
      edge((-1, 0), (0, 0), [$h'$], label-side: left, "->")
      edge((-1, 0), (-1, 1), [$g''$], label-side: right, "->")
    }))
    the relative base change $g^(-1) R f_* R h_* cal(K) Lotimes_Lambda cal(L) -> R f'_* R h'_* (g''^(-1) cal(K) Lotimes_Lambda h'^(-1) f'^(-1) cal(L))$, is the composition: 
    $
      g^(-1) R f_* R h_* cal(K) Lotimes_Lambda cal(L) -> R f'_* (g'^(-1) R h_* cal(K) Lotimes_Lambda f'^(-1) cal(L)) -> R h'_* R f'_* (g''^(-1) cal(K) Lotimes_Lambda h'^(-1) f'^(-1) cal(L))
    $
    of the relative base change of the right square w.r.t. $cal(L)$ and the relative base change of the left square w.r.t. $f'^(-1) cal(L)$. 
]

Proper base change gives a condition on $f$ so that the relative base change map is an isomorphism, namely $f$ being proper. It is thus natural to study the problem in the $g$-aspect. That is, we want to ask for a condition on $g$, so that the relative base change map established above is an isomorphism. 

To establish the main result, we need some preliminary statements. 

#lemma(name: <constructible-godement-resolution>)[
  Let $X$ be a noetherian scheme and $cal(F) in cAb(X_et, ZZ\/n)$ be an $n$-torsion constructible sheaf. Then there exists a finite list of geometric points $ol(x_1), dots.c, ol(x_m) in X$ and an injection: 
  $
    cal(F) -> oplus.big_(i=1)^m ol(x_i)_* ul(ZZ\/n)
  $
]
#proof[
  By @finite-morphisms-and-constructible-sheaves, there exists finite $h: X' -> X$ and an injection $cal(F) -> h_* ul(ZZ\/n)$. Note that since $h$ is finite, $h_*$ is exact and by Leray spectral sequence @derived-lower-star-first-props (1), $h_* ol(x')_* ul(ZZ\/n) = (h(ol(x')))_* ul(ZZ\/n)$. Thus by replacing $X$ with $X'$, we may assume that $cal(F) = ul(ZZ\/n)$. 

  Let $x_1, dots.c, x_m in X$ be generic points of all irreducible components of $X$, and $ol(x_i)$ be a geometric point above $x_i$. We claim that the canonical map: 
  $
    ul(ZZ\/n)_X -> oplus.big_(i=1)^m ol(x_i)_* ul(ZZ\/n)
  $
  is injective. Indeed, for any connected affine $U in Et_X$, this map induces the following map on sections on $U$: 
  $
    ZZ\/n -> oplus.big_(i=1)^m (ZZ\/n)^(oplus pi_0 (U_(ol(x_i))))
  $
  This diagonal map is injective, since the image of $U$ in $X$ must contain the generic point of some irreducible component of $X$, making $U_(ol(x_i))$ nonempty, and the direct sum on RHS nonzero. We are thereby done. 
]

#proposition(name: <finite-bc-in-the-limit>)[
  For any integral morphism $f: X -> Y$, $f_*$ is exact, and in a Cartesian diagram: 
  #align(center, diagram({
    node((-1, 1), [$X$])
    node((0, 1), [$Y$])
    node((-1, 0), [$X'$])
    node((0, 0), [$Y'$])
    node((-0.7, 0.3), $cart$)
    edge((0, 0), (0, 1), [$g$], label-side: left, "->")
    edge((-1, 0), (-1, 1), [$g'$], label-side: right, "->")
    edge((-1, 0), (0, 0), [$f'$], label-side: left, "->")
    edge((-1, 1), (0, 1), [$f$], label-side: right, "->")
  }))
  in which $f: X -> Y$ is integral, the base change morphism: 
  $
    g^(-1) f_* cal(K) Lotimes_Lambda cal(L) -> f'_* (g'^(-1) cal(K) Lotimes_Lambda f'^(-1) cal(L))
  $
  is an isomorphism for all complexes $cal(K) in D(X_et, Lambda), cal(L) in D(Y'_et, Lambda)$. 
]
#proof[
  It suffices to consider this problem Zariski (or etale) locally on $Y$, by replacing $Y$ with an affine open of it and base changing the whole Cartesian diagram along its open immersion. As such, we may assume $Y = Spec(A)$ and $X = Spec(B)$ are affine, with $B$ an integral $A$-algebra. 
  
  Now we may write $B$ as a directed limit of finite $A$-algebras. In other words, we may write $X = invlim_i X_i$ as a projective limit of finite $Y$-schemes. //By limit formulas and $cal(F) = dirlim_(n>=1) cal(F)[n]$, we may assume that $cal(F)$ is $n$-torsion for a fixed $n$, and so all sheaves in question are $n$-torsion. 
  
  Denote the involved morphisms by: 
  // https://q.uiver.app/#r=typst&q=WzAsNixbMiwwLCJZJyJdLFsyLDEsIlkiXSxbMSwxLCJYX2kiXSxbMCwxLCJYIl0sWzAsMCwiWCciXSxbMSwwLCJYJ19pIl0sWzQsNSwiaCdfaSJdLFs1LDAsImYnX2kiXSxbMiwxLCJmX2kiXSxbMywyLCJoX2kiXSxbMCwxLCJnIl0sWzUsMiwiZydfaSJdLFs0LDMsImcnIiwyXV0=
  #align(center, diagram({
    node((1, -1), [$Y'$])
    node((1, 0), [$Y$])
    node((0, 0), [$X_i$])
    node((-1, 0), [$X$])
    node((-1, -1), [$X'$])
    node((0, -1), [$X'_i$])
    edge((-1, -1), (0, -1), [$h'_i$], label-side: left, "->")
    edge((0, -1), (1, -1), [$f'_i$], label-side: left, "->")
    edge((0, 0), (1, 0), [$f_i$], label-side: left, "->")
    edge((-1, 0), (0, 0), [$h_i$], label-side: left, "->")
    edge((1, -1), (1, 0), [$g$], label-side: left, "->")
    edge((0, -1), (0, 0), [$g'_i$], label-side: left, "->")
    edge((-1, -1), (-1, 0), [$g'$], label-side: right, "->")
  }))
  By @limit-formula-adjunction, $cal(F) = dirlim_i h_i^(-1) h_(i,*) cal(F)$. Denote by $cal(F)_i = h_(i,*) cal(F)$. Thus by @relative-limit-formula-composite, 
  $
    R^q f_* cal(F) = dirlim_i R^q f_(i,*) cal(F)_i
  $
  For $q >= 1$, since each $f_i$ is finite, $R^q f_(i,*) = 0$, so the colimit above is over zeroes. Hence $R^q f_* cal(F) = 0$. Thus we have proved the part about $f_*$ being exact. 

  For base change, by @pbc-finite, 
  $
    g^(-1) f_* cal(F) = dirlim_i g^(-1) f_(i,*) cal(F)_i = dirlim_i f'_(i,*) g'_i^(-1) cal(F)_i 
  $
  Finally, notice that: 
  $
    dirlim_i h'_i^(-1) g'_i^(-1) cal(F)_i = dirlim_i g'^(-1) h_i^(-1) cal(F)_i = g'^(-1) (dirlim_i h_i^(-1) cal(F)_i) = g'^(-1) cal(F) 
  $
  Thus, @relative-limit-formula-composite may be applied to the limit $dirlim_i f'_(i,*) g'_i^(-1) cal(F)_i$ to conclude that: 
  $
    g^(-1) f_* cal(F) = dirlim_i f'_(i,*) g'_i^(-1) cal(F)_i = f'_* g'^(-1) cal(F)
  $
  i.e. standard base change for an integral pushforward is an isomorphism. For a relative base change, it suffices to prove that the projection part is an isomorphism. This follows from the base change part, the compatibility of projection with base change, and @projection-formula-for-global-sections. (Here, geometric fibers of an integral morphism are finite, so the finite type hypothesis of @projection-formula-for-global-sections is satisfied.)
]

The main reduction result is now stated in the following theorem. 

#theorem(name: <rel-bc-reductions>)[
  Let $Lambda$ be a torsion noetherian ring. Suppose that $g: S' -> S$ is a morphism for $S$ noetherian, and $cal(L)_S in D^b_#[ctf] (S'_et, Lambda)$. Then TFAE: 

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

  + The above condition holds for $f: xi -> X$ when: 

    - $X$ is the normalization of a finite type affine integral $S$-scheme in the algebraic closure of its function field;
    
    - $xi$ is the generic point of $X$, which is algebraically closed; 

    and $cal(K) = ul(M)$ for a finite $Lambda$-module $M$. Furthermore, if every finite $Lambda$-module admits an injection into a finite free $Lambda$-module, then this condition is only required to hold for $cal(K) = ul(Lambda)$. 
]
#proof[
  (1)$==>$(2) is tautological, so we only prove (2)$==>$(1). The proof is essentially a sequence of reductions. Also, note that since $cal(L)_S in D^b_#[ctf] (S'_et, Lambda)$, and arbitrary pullbacks preserve flatness of sheaves of $Lambda$-modules, $cal(L)_X, cal(L)_Y$ are always in $D^b_#[ctf]$ of the respective schemes. 

  Thus, both sides of $g_Y^(-1) R f_* cal(K) Lotimes_Lambda cal(L)_Y -> R f'_* (g_X^(-1) cal(K) Lotimes_Lambda cal(L)_X)$ are bounded both above and below in $cal(K)$. By the way-out lemma, it suffices to deal with the case that $cal(K) = cal(F) in cAb(X_et, Lambda)$ is just a single sheaf. From now on we always assume $cal(K) = cal(F)$ is a single sheaf. 

  Furthermore, to use limit formulas, we need to translate statements in derived categories to statements in abelian categories. Replace $cal(L)_S$ with a bounded complex $cal(P)_S^bullet$ of flat sheaves. Then by the hypercohomology spectral sequence, for LHS of relative base change, there is a spectral sequence: 
  $
    E_1^(p,q) = g_Y^(-1) R^q f_* cal(F) otimes_Lambda cal(P)_Y^p ==> h^(p+q) (g_Y^(-1) R f_* cal(F) Lotimes_Lambda cal(L)_Y)
  $
  and for RHS, there is a spectral sequence: 
  $
    tilde(E)_1^(p,q) = R^q f'_* (g_X^(-1) cal(F) otimes_Lambda cal(P)_X^p) ==> h^(p+q) (R f'_* (g_X^(-1) cal(F) otimes_Lambda cal(L)_X))
  $
  Furthermore, the relative base change map $h^(p+q) (g_Y^(-1) R f_* cal(F) Lotimes_Lambda cal(L)_Y) -> h^(p+q) (R f'_* (g_X^(-1) cal(F) otimes_Lambda cal(L)_X))$ is induced by the relative base change maps: 
  $
    E_1^(p,q) = g_Y^(-1) R^q f_* cal(F) otimes_Lambda cal(P)_Y^p -> R^q f'_* (g_X^(-1) cal(F) otimes_Lambda cal(P)_X^p) = tilde(E)_1^(p,q)
  $

  Step 1. It suffices to deal with the case where $X -> Y$ is of finite presentation. 

  #proof_[Proof of Step 1][
    Note that $f: X -> Y$ is qcqs, and so by @relative-approx, we may write $X = invlim_lambda X_lambda$ as a projective limit of finite presentation $Y$-schemes with affine transition morphisms. We thus have a following Cartesian diagram of $S$-schemes: 
    // https://q.uiver.app/#r=typst&q=WzAsNixbMCwwLCJYJyJdLFsxLDAsIlgnX2xhbWJkYSJdLFsyLDAsIlknIl0sWzAsMSwiWCJdLFsxLDEsIlhfbGFtYmRhIl0sWzIsMSwiWSJdLFsyLDUsImciXSxbMSw0LCJnJ19sYW1iZGEiXSxbMCwzLCJnJyIsMl0sWzQsNSwiZl9sYW1iZGEiLDJdLFszLDQsImhfbGFtYmRhIiwyXSxbMCwxLCJoJ19sYW1iZGEiXSxbMSwyLCJmJ19sYW1iZGEiXV0=
    #align(center, diagram({
      node((0, 0), [$X'$])
      node((1, 0), [$X'_lambda$])
      node((2, 0), [$Y'$])
      node((0, 1), [$X$])
      node((1, 1), [$X_lambda$])
      node((2, 1), [$Y$])
      edge((2, 0), (2, 1), [$g_Y$], label-side: left, "->")
      edge((1, 0), (1, 1), [$g_lambda$], label-side: left, "->")
      edge((0, 0), (0, 1), [$g_X$], label-side: right, "->")
      edge((1, 1), (2, 1), [$f_lambda$], label-side: right, "->")
      edge((0, 1), (1, 1), [$h_lambda$], label-side: right, "->")
      edge((0, 0), (1, 0), [$h'_lambda$], label-side: left, "->")
      edge((1, 0), (2, 0), [$f'_lambda$], label-side: left, "->")
    }))
    Take $cal(F)_lambda = h_(lambda,*) cal(F)$, and take a bounded flat resolution $cal(P)^bullet$ of $cal(L)_Y$. By @limit-formula-adjunction, $cal(F) = dirlim_lambda h_lambda^(-1) cal(F)_lambda$. Now consider the two spectral sequences on LHS and RHS of relative base changes for the right square for various $lambda$: 
    $
      E_(1,lambda)^(p,q) = g_Y^(-1) R^q f_(lambda,*) cal(F)_lambda otimes_Lambda cal(P)^p => h^(p+q) (g_Y^(-1) R f_(lambda,*) cal(F)_lambda Lotimes_Lambda cal(L)_Y) \

      tilde(E)_(1,lambda)^(p,q) = R^q f'_(lambda,*) (g_lambda^(-1) cal(F)_lambda otimes_Lambda f'_lambda^(-1) cal(P)^p) => h^(p+q) (R f'_(lambda,*) (g_lambda^(-1) cal(F)_lambda Lotimes_Lambda f'_lambda^(-1) cal(L)_Y))
    $
    Taking a direct limit over $lambda$: 
    $
      dirlim_lambda (g_Y^(-1) R^q f_(lambda,*) cal(F)_lambda otimes_Lambda cal(P)^p) = g_Y^(-1) (dirlim_lambda R^q f_(lambda,*) cal(F)_lambda) otimes_Lambda cal(P)^p cong g_Y^(-1) R^q f_* cal(F) otimes_Lambda cal(P)^p
    $
    by @relative-limit-formula-for-schemes, while by the same limit formula: 
    $
      dirlim_lambda (R^q f'_(lambda,*) (g_lambda^(-1) cal(F) otimes_Lambda f'_lambda^(-1) cal(P)^p)) &cong R^q f'_* (dirlim_lambda (h'_lambda^(-1) g_lambda^(-1) cal(F)_lambda otimes_Lambda f'^(-1) cal(P)^p)) \
      &= R^q f'_* ((dirlim_lambda g_X^(-1) h_lambda^(-1) cal(F)_lambda) otimes_Lambda f'^(-1) cal(P)^p) \
      &= R^q f'_* (g_X^(-1) cal(F) otimes_Lambda f'^(-1) cal(P)^p)
    $
    Thus, we have canonical spectral sequences: 
    $
      E_1^(p,q) = g_Y^(-1) R^q f_* cal(F) otimes_Lambda cal(P)^p => dirlim_lambda h^(p+q) (g_Y^(-1) R f_(lambda,*) cal(F)_lambda Lotimes_Lambda cal(L)_Y) \
      tilde(E)_1^(p,q) = R^q f'_* (g_X^(-1) cal(F) otimes_Lambda f'^(-1) cal(P)^p) => dirlim_lambda h^(p+q) (R f'_(lambda,*) (g_lambda^(-1) cal(F)_lambda Lotimes_Lambda f'_lambda^(-1) cal(L)_Y))
    $
    However, the same canonical exact sequences converge to $h^(p+q) (g_Y^(-1) R f_* cal(F) Lotimes_Lambda cal(L)_Y)$ and $h^(p+q) (R f'_* (g_X^(-1) cal(F) Lotimes_Lambda cal(L)_X))$, respectively. More precisely, there exist two canonical morphisms of spectral sequences, each the identity on the $E_1$-page, so the limits are isomorphic. Hence, we have canonical isomorphisms: 
    $
      h^(p+q) (g_Y^(-1) R f_* cal(F) Lotimes_Lambda cal(L)_Y) cong dirlim_lambda h^(p+q) (g_Y^(-1) R f_(lambda,*) cal(F)_lambda Lotimes_Lambda cal(L)_Y) \

      h^(p+q) (R f'_* (g_X^(-1) cal(F) otimes_Lambda cal(L)_X)) cong dirlim_lambda h^(p+q) (R f'_(lambda,*) (g_lambda^(-1) cal(F)_lambda Lotimes_Lambda f'_lambda^(-1) cal(L)_Y))
    $
    The RHSs of both isomorphisms are isomorphic, since we assumed the relative base change w.r.t. $cal(L)$ to be an isomorphism for the finite presentation morphisms $f_lambda: X_lambda -> Y$. Thus the LHSs are isomorphic and we are done. 
  ]  

  Step 2. It suffices to deal with the case where $f: X -> Y$ is between finite type $S$-schemes. 

  #proof_[Proof of Step 2][
    By Step 1, we may assume that $f: X -> Y$ is of finite presentation between qcqs $S$-schemes. By @passage-to-limit-of-morphisms and @relative-approx, we may write $Y = invlim_i Y_i$ with $Y_i$ being finite type $S$-schemes for $i >= 0$, and we have a finite type morphism $f_0: X_0 -> Y_0$ whose base change along $Y -> Y_0$ is just $f: X -> Y$. Put $f_i: X_i -> Y_i$ to be the base change of $f_0$ along $Y_i -> Y_0$. 

    We now have a cube with Cartesian faces: 
    // https://q.uiver.app/#r=typst&q=WzAsOCxbMCwwLCJYJyJdLFsyLDAsIlknIl0sWzEsMSwiWCdfaSJdLFszLDEsIlknX2kiXSxbMCwyLCJYIl0sWzIsMiwiWSJdLFsxLDMsIlhfaSJdLFszLDMsIllfaSJdLFszLDcsImdfKFlfaSkiLDEseyJsYWJlbF9wb3NpdGlvbiI6MjB9XSxbMSw1LCJnX1kiLDEseyJsYWJlbF9wb3NpdGlvbiI6ODB9XSxbMiw2LCJnXyhYX2kpIiwxLHsibGFiZWxfcG9zaXRpb24iOjIwfV0sWzAsNCwiZ19YIiwxLHsibGFiZWxfcG9zaXRpb24iOjgwfV0sWzQsNSwiZiIsMSx7ImxhYmVsX3Bvc2l0aW9uIjozMH1dLFswLDEsImYnIiwxXSxbNiw3LCJmX2kiLDFdLFsyLDMsImYnX2kiLDEseyJsYWJlbF9wb3NpdGlvbiI6ODB9XSxbNSw3LCJoX2kiLDFdLFsxLDMsImgnX2kiLDFdLFs0LDYsImtfaSIsMV0sWzAsMiwiaydfaSIsMV1d
    #context align(center, diagram({
      node((0, 0), [$X'$])
      node((2, 0), [$Y'$])
      node((1, 1), [$X'_i$])
      node((3, 1), [$Y'_i$])
      node((0, 2), [$X$])
      node((2, 2), [$Y$])
      node((1, 3), [$X_i$])
      node((3, 3), [$Y_i$])
      edge((3, 1), (3, 3), [$g_(Y_i)$], label-side: center, label-pos: 0.2, "->")
      edge((2, 0), (2, 2), [$g_Y$], label-side: center, label-pos: 0.8, "->")
      edge((1, 1), (1, 3), [$g_(X_i)$], label-side: center, label-pos: 0.2, "->")
      edge((0, 0), (0, 2), [$g_X$], label-side: center, label-pos: 0.8, "->")
      edge((0, 2), (2, 2), [$f$], label-side: center, label-pos: 0.8, "->")
      edge((0, 0), (2, 0), [$f'$], label-side: center, "->")
      edge((1, 3), (3, 3), [$f_i$], label-side: center, "->")
      edge((1, 1), (3, 1), [$f'_i$], label-side: center, label-pos: 0.2, "->")
      edge((2, 2), (3, 3), [$h_i$], label-side: center, "->")
      edge((2, 0), (3, 1), [$h'_i$], label-side: center, "->")
      edge((0, 2), (1, 3), [$k_i$], label-side: center, "->")
      edge((0, 0), (1, 1), [$k'_i$], label-side: center, "->")
    }, crossing-fill: thm-box-curr-color()))
    where the vertical morphisms are base changes of $g: S' -> S$. Put $cal(L) = cal(L)_Y$ and $cal(L)_i = cal(L)_(Y_i)$, and pick flat resolutions $cal(P)^bullet, cal(P)_i^bullet$ of $cal(L), cal(L)_i$ all supported on a certain bounded interval. Put $cal(F)_i = k_(i,*) cal(F)$ so that $cal(F) = dirlim_i k_i^(-1) cal(F)_i$ by @limit-formula-adjunction. 
    
    Consider canonical spectral sequences: 
    $
      E_(1,i)^(p,q) = g_(Y_i)^(-1) R^q f_(i,*) cal(F)_i otimes_Lambda cal(P)^p_i => h^(p+q) (g_(Y_i)^(-1) R f_(i,*) cal(F)_i Lotimes_Lambda cal(L)_i) \

      tilde(E)_1^(p,q) = R^q f'_(i,*) (g_(X_i)^(-1) cal(F)_i otimes_Lambda f'_i^(-1) cal(P)^p_i) => h^(p+q) (R f'_(i,*) (g_(X_i)^(-1) cal(F)_i Lotimes_Lambda f'_i^(-1) cal(L)_i))
    $
    Take the limits $dirlim_i h'_i^(-1) E_1^(p,q)$ and $dirlim_i h'_i^(-1) tilde(E)_1^(p,q)$: 
    $
      dirlim_i h'_i^(-1) E_1^(p,q) &= dirlim_i (h'_i^(-1) g_(Y_i)^(-1) R^q f_(i,*) cal(F)_i otimes_Lambda h'_i^(-1) cal(P)^p_i) \
      &= g_Y^(-1) dirlim_i h_i^(-1) R^q f_(i,*) cal(F)_i otimes_Lambda cal(P)^p \
      &cong g_Y^(-1) R^q f_* cal(F) otimes_Lambda cal(P)^p
    $
    by @limit-formula-for-base-change. By the same limit formula, 
    $
      dirlim_i h'_i^(-1) tilde(E)_1^(p,q) &= dirlim_i h'_i^(-1) R^q f'_(i,*) (g_(X_i)^(-1) cal(F)_i otimes_Lambda f'_i^(-1) cal(P)^p_i) \
      &cong R^q f'_* (dirlim_i k'_i^(-1) (g_(X_i)^(-1) cal(F)_i otimes_Lambda f'_i^(-1) cal(P)^p_i)) \
      &= R^q f'_* (dirlim_i (g_X^(-1) k_i^(-1) cal(F)_i otimes_Lambda f'^(-1) h'_i^(-1) cal(P)^p_i)) \
      &= R^q f'_* (g_X^(-1) (dirlim_i k_i^(-1) cal(F)_i) otimes_Lambda cal(P)^p) \
      &= R^q f'_* (g_X^(-1) cal(F) otimes_Lambda cal(P)^p)
    $
    Hence, we have canonical spectral sequences: 
    $
      E_1^(p,q) = g_Y^(-1) R^q f_* cal(F) otimes_Lambda cal(P)^p => dirlim_i h'_i^(-1) h^(p+q) (g_(Y_i)^(-1) R f_(i,*) cal(F)_i Lotimes_Lambda cal(L)_i) \

      tilde(E)_1^(p,q) = R^q f'_* (g_X^(-1) cal(F) otimes_Lambda cal(P)^p) => dirlim_i h'_i^(-1) h^(p+q) (R f'_(i,*) (g_(X_i)^(-1) cal(F)_i Lotimes_Lambda f'_i^(-1) cal(L)_i))
    $
    However, the same canonical exact sequences converge to $h^(p+q) (g_Y^(-1) R f_* cal(F) Lotimes_Lambda cal(L)_Y)$ and $h^(p+q) (R f'_* (g_X^(-1) cal(F) Lotimes_Lambda cal(L)_X))$, respectively. More precisely, there exist two canonical morphisms of spectral sequences, each the identity on the $E_1$-page, so the limits are isomorphic. Hence, we have canonical isomorphisms: 
    $
      h^(p+q) (g_Y^(-1) R f_* cal(F) Lotimes_Lambda cal(L)_Y) cong dirlim_i h'_i^(-1) h^(p+q) (g_(Y_i)^(-1) R f_(i,*) cal(F)_i Lotimes_Lambda cal(L)_i) \

      h^(p+q) (R f'_* (g_X^(-1) cal(F) otimes_Lambda cal(L)_X)) cong dirlim_i h'_i^(-1) h^(p+q) (R f'_(i,*) (g_(X_i)^(-1) cal(F)_i Lotimes_Lambda f'_i^(-1) cal(L)_i))
    $
    The RHSs of both isomorphisms are isomorphic, since we assumed the relative base change w.r.t. $cal(L)_i$ to be an isomorphism for the morphisms $f_i: X_i -> Y_i$ between finite type $S$-schemes. Thus the LHSs are isomorphic and we are done. 
  ]

  Step 3. It suffices to deal with the case where $f: X -> Y$ is an open immersion where $Y$ is of finite type over $S$. 

  #proof_[Proof of Step 3][
    By Step 2, we may assume that $f: X -> Y$ is between finite type $S$-schemes. 

    Suppose that $f$ is additionally separated. Since $S$ is noetherian, so is $X$ and $Y$. Thus we may pick a compactification $X ->^j ol(X) ->^(ol(f)) Y$. Now the relative base change for $cal(L)_(ol(X))$ along $j$ is an isomorphism by hypotheses, and that for $cal(L)_Y$ along $ol(f)$ is an isomorphism by proper base change. Thus the relative base change along $f$ for $cal(L)_Y$ is an isomorphism, and we are done. 

    Since $X$ is noetherian, we may cover it by finitely many affine opens. That is, there exists an affine scheme $Z$ with $j: Z -> X$ a surjection. By the separated case, the relative base change for $cal(L)_Y$ along $j$ and $f compose j$ are isomorphisms. For a complex $cal(K)$ of the form $R j_* cal(K)_Z$, the composition: 
    $
      g_Y^(-1) R f_* R j_* cal(K)_Z Lotimes_Lambda cal(L)_Y -> R f'_* (g_X^(-1) R j_* cal(K)_Z Lotimes_Lambda cal(L)_X) -> R f'_* R j_* (g_Z^(-1) cal(K)_Z Lotimes_Lambda cal(L)_Z) 
    $
    of relative base changes for $f$ and $j$, is the same as the relative base change along $f compose j$. Hence, the composition here is an isomorphism and the second map is an isomorphism by the separated case. Thus, the first map: 
    $
      g_Y^(-1) R f_* R j_* cal(K)_Z Lotimes_Lambda cal(L)_Y -> R f'_* (g_X^(-1) R j_* cal(K)_Z Lotimes_Lambda cal(L)_X)
    $
    is always an isomorphism. 

    Suppose that $cal(L)_S$ admits a flat resolution supported on $[b_1, b_2]$. For any complex $cal(K) in D_(>=a) (X_et, Lambda)$, both sides of: 
    $
      g_Y^(-1) R f_* cal(K) Lotimes_Lambda cal(L)_Y -> R f'_* (g_X^(-1) cal(K) Lotimes_Lambda cal(L)_X)
    $
    is supported on $>=a-b_1$. Form a distinguished triangle: 
    $
      cal(K) -> R j_* j^(-1) cal(K) -> cal(R) ->^(+1) 
    $
    By the hypercohomology spectral sequence, $h^a (R j_* j^(-1) cal(K)) cong j_* j^(-1) h^a (cal(K))$. By @surjection-has-injective-unit, $h^a (cal(K)) -> h^a (R j_* j^(-1) cal(K)) cong j_* j^(-1) h^a (cal(K))$ is injective, and so its kernel $h^(a-1) (cal(R)) = 0$. Hence, $cal(R) in D_(>=a) (X_et, Lambda)$. We now form the long exact sequences: 
    
    // https://q.uiver.app/#r=typst&q=WzAsMTQsWzAsMCwiZG90cy52Il0sWzAsMSwiaF5xIChnX1heKC0xKSBSIGZfKiBSIGpfKiBqXigtMSkgY2FsKEspIExvdGltZXNfTGFtYmRhIGNhbChMKV9ZKSJdLFswLDIsImhecSAoZ19YXigtMSkgUiBmXyogY2FsKFIpIExvdGltZXNfTGFtYmRhIGNhbChMKV9ZKSJdLFswLDMsImheKHErMSkgKGdfWF4oLTEpIFIgZl8qIGNhbChLKSBMb3RpbWVzX0xhbWJkYSBjYWwoTClfWSkiXSxbMCw0LCJoXihxKzEpIChnX1heKC0xKSBSIGZfKiBSIGpfKiBqXigtMSkgY2FsKEspIExvdGltZXNfTGFtYmRhIGNhbChMKV9ZKSJdLFswLDUsImheKHErMSkgKGdfWF4oLTEpIFIgZl8qIGNhbChSKSBMb3RpbWVzX0xhbWJkYSBjYWwoTClfWSkiXSxbMCw2LCJkb3RzLnYiXSxbMiwwLCJkb3RzLnYiXSxbMiw2LCJkb3RzLnYiXSxbMiwxLCJoXnEgKFIgZidfKiAoZ19ZXigtMSkgUiBqXyogal4oLTEpIGNhbChLKSBMb3RpbWVzX0xhbWJkYSBjYWwoTClfWCkpIl0sWzIsNCwiaF4ocSsxKSAoUiBmJ18qIChnX1leKC0xKSBSIGpfKiBqXigtMSkgY2FsKEspIExvdGltZXNfTGFtYmRhIGNhbChMKV9YKSkiXSxbMiwyLCJoXnEgKFIgZidfKiAoZ19ZXigtMSkgY2FsKFIpIExvdGltZXNfTGFtYmRhIGNhbChMKV9YKSkiXSxbMiwzLCJoXihxKzEpIChSIGYnXyogKGdfWV4oLTEpIGNhbChLKSBMb3RpbWVzX0xhbWJkYSBjYWwoTClfWCkpIl0sWzIsNSwiaF4ocSsxKSAoUiBmJ18qIChnX1leKC0xKSBjYWwoUikgTG90aW1lc19MYW1iZGEgY2FsKEwpX1gpKSJdLFsxLDldLFsyLDExXSxbMywxMl0sWzQsMTBdLFs1LDEzXSxbMSwyXSxbMiwzXSxbMyw0XSxbNCw1XSxbMCwxXSxbNSw2XSxbNyw5XSxbOSwxMV0sWzExLDEyXSxbMTIsMTBdLFsxMCwxM10sWzEzLDhdXQ==
    #align(center, diagram({
      node((0, 0), [$dots.v$])
      node((0, 1), [$h^q (g_Y^(-1) R f_* R j_* j^(-1) cal(K) Lotimes_Lambda cal(L)_Y)$])
      node((0, 2), [$h^q (g_Y^(-1) R f_* cal(R) Lotimes_Lambda cal(L)_Y)$])
      node((0, 3), [$h^(q+1) (g_Y^(-1) R f_* cal(K) Lotimes_Lambda cal(L)_Y)$])
      node((0, 4), [$h^(q+1) (g_Y^(-1) R f_* R j_* j^(-1) cal(K) Lotimes_Lambda cal(L)_Y)$])
      node((0, 5), [$h^(q+1) (g_Y^(-1) R f_* cal(R) Lotimes_Lambda cal(L)_Y)$])
      node((0, 6), [$dots.v$])
      node((2, 0), [$dots.v$])
      node((2, 6), [$dots.v$])
      node((2, 1), [$h^q (R f'_* (g_X^(-1) R j_* j^(-1) cal(K) Lotimes_Lambda cal(L)_X))$])
      node((2, 4), [$h^(q+1) (R f'_* (g_X^(-1) R j_* j^(-1) cal(K) Lotimes_Lambda cal(L)_X))$])
      node((2, 2), [$h^q (R f'_* (g_X^(-1) cal(R) Lotimes_Lambda cal(L)_X))$])
      node((2, 3), [$h^(q+1) (R f'_* (g_X^(-1) cal(K) Lotimes_Lambda cal(L)_X))$])
      node((2, 5), [$h^(q+1) (R f'_* (g_X^(-1) cal(R) Lotimes_Lambda cal(L)_X))$])
      edge((0, 1), (2, 1), "->")
      edge((0, 2), (2, 2), "->")
      edge((0, 3), (2, 3), "->")
      edge((0, 4), (2, 4), "->")
      edge((0, 5), (2, 5), "->")
      edge((0, 1), (0, 2), "->")
      edge((0, 2), (0, 3), "->")
      edge((0, 3), (0, 4), "->")
      edge((0, 4), (0, 5), "->")
      edge((0, 0), (0, 1), "->")
      edge((0, 5), (0, 6), "->")
      edge((2, 0), (2, 1), "->")
      edge((2, 1), (2, 2), "->")
      edge((2, 2), (2, 3), "->")
      edge((2, 3), (2, 4), "->")
      edge((2, 4), (2, 5), "->")
      edge((2, 5), (2, 6), "->")
    }))

    This diagram has exact columns, and by the separated case, we have deduced that the first and fourth horizontal maps are isomorphisms. Suppose that for all $cal(K) in D_(>=a)$, $g_Y^(-1) R f_* cal(K) Lotimes_Lambda cal(L)_Y -> R f'_* (g_X^(-1) cal(K) Lotimes_Lambda cal(L)_X)$ is an isomorphism on $h^r$ for all $r <= q$. Then the second horizontal arrow is an isomorphism, and by the injective four lemma, the third horizontal arrow becomes injective. 

    Since $cal(K)$ can be any arbitrary complex in $D_(>=a)$ and $cal(R) in D_(>=a)$, the same argument shows that the fifth horizontal arrow is injective. Thus the third horizontal arrow is surjective by the surjective four lemma. Thus, 
    $
      g_Y^(-1) R f_* cal(K) Lotimes_Lambda cal(L)_Y -> R f'_* (g_X^(-1) cal(K) Lotimes_Lambda cal(L)_X)
    $
    being an isomorphism on $h^r$ for all $r<=q$ and for all $cal(K) in D_(>=a)$, implies the same statement but for $h^(q+1)$. Both sides are supported on $>=a-b_1$, so this map is trivially an isomorphism on $h^r$ for $r<=a-b_1-1$. By induction, this map is a quasi-isomorphism. 
  ]

  Step 4. Conclusion of proof. 

  #proof[
    Let $f: X -> Y$ be an open immersion between finite type $S$-scheme. In particular, $X, Y$ are noetherian. Suppose that $cal(F) = dirlim_lambda cal(F)_lambda$. 

    Take the spectral sequences for LHS and RHS for $cal(F)_lambda$: 
    $
      E_(1,lambda)^(p,q) = g_Y^(-1) R^q f_* cal(F)_lambda otimes_Lambda cal(P)_Y^p ==> h^(p+q) (g_Y^(-1) R f_* cal(F)_lambda Lotimes_Lambda cal(L)_Y)
    $
    and for RHS, there is a spectral sequence: 
    $
      tilde(E)_(1,lambda)^(p,q) = R^q f'_* (g_X^(-1) cal(F)_lambda otimes_Lambda cal(P)_X^p) ==> h^(p+q) (R f'_* (g_X^(-1) cal(F)_lambda otimes_Lambda cal(L)_X))
    $
    Taking limit over all $lambda$ and using @relative-limit-formula-for-sheaves yields (by similar arguments as in Step 2 and Step 3): 
    $
      dirlim_lambda h^(p+q) (g_Y^(-1) R f_* cal(F)_lambda Lotimes_Lambda cal(L)_Y) cong h^(p+q) (g_Y^(-1) R f_* cal(F) Lotimes_Lambda cal(L)_Y) \
      dirlim_lambda h^(p+q) (R f'_* (g_X^(-1) cal(F)_lambda otimes_Lambda cal(L)_X)) cong h^(p+q) (R f'_* (g_X^(-1) cal(F) otimes_Lambda cal(L)_X))
    $
    Thus, if $g_Y^(-1) R f_* cal(F)_lambda Lotimes_Lambda cal(L)_Y -> R f'_* (g_X^(-1) cal(F)_lambda otimes_Lambda cal(L)_X)$ is a quasi-isomorphism for every $cal(F)_lambda$, it is a quasi-isomorphism for $cal(F)$. By @constructible-sheaves-first-props, we may assume that $cal(F)$ is a constructible sheaf of $Lambda$-modules. 

    By @constructible-godement-resolution, there exists a finite set of algebraic geometric points $ol(x_1), dots.c, ol(x_m)$ of $X$, and an injection $cal(F) -> oplus.big_(i=1)^m ol(x_i)_* ul(M_i)$ for finite $Lambda$-modules $M_i$. By a two-stage four-lemma argument as in Step 3, applied to the exact sequence $0 -> cal(F) -> oplus.big_(i=1)^m ol(x_i)_* ul(M_i) -> cal(R) -> 0$, it suffices to prove relative base change for every summand. We may thus assume that $cal(F) = ol(x)_* ul(M)$ for a finite $Lambda$-module $M$. Form the Cartesian diagram: 
    // https://q.uiver.app/#r=typst&q=WzAsNixbMSwwLCJYJyJdLFsyLDAsIlknIl0sWzEsMSwiWCJdLFsyLDEsIlkiXSxbMCwxLCJQID0gb2woeCkiXSxbMCwwLCJQJyJdLFsyLDMsImYiLDJdLFswLDEsImYnIl0sWzEsMywiZ19YIl0sWzAsMiwiZ19ZIiwyXSxbNCwyLCJwIiwyXSxbNSw0LCJnX1AiLDJdLFs1LDAsInAnIl1d
    #align(center, diagram({
      node((0, 0), [$X'$])
      node((1, 0), [$Y'$])
      node((0, 1), [$X$])
      node((1, 1), [$Y$])
      node((-1, 1), [$P = ol(x)$])
      node((-1, 0), [$P'$])
      edge((0, 1), (1, 1), [$f$], label-side: right, "->")
      edge((0, 0), (1, 0), [$f'$], label-side: left, "->")
      edge((1, 0), (1, 1), [$g_Y$], label-side: left, "->")
      edge((0, 0), (0, 1), [$g_X$], label-side: right, "->")
      edge((-1, 1), (0, 1), [$p$], label-side: right, "->")
      edge((-1, 0), (-1, 1), [$g_P$], label-side: right, "->")
      edge((-1, 0), (0, 0), [$p'$], label-side: left, "->")
    }))
    Consider the composition of relative base changes: 
    $
      g_Y^(-1) R f_* p_* ul(M) Lotimes_Lambda cal(L)_Y -> R f'_* (g_X^(-1) p_* ul(M) Lotimes_Lambda cal(L)_X) -> R f'_* R p'_* (ul(M) Lotimes_Lambda cal(L)_P)
    $
    which is the relative base change along $f compose p: ol(x) -> Y$. We aim to prove that the first map is an isomorphism. For this, it suffices to show that the second map and the composition are isomorphisms. They are relative base changes along $p: ol(x) -> X$ and $f compose p: ol(x) -> Y$, respectively, for the sheaf $ul(M)$. Since $X -> Y$ is an open immersion, $ol(x) -> Y$ is an algebraic geometric point. Thus it remains to prove that: 

    - For every algebraic geometric point $p: ol(x) = P -> X$, the relative base change: #h(1fr)
      $
        g_X^(-1) p_* ul(M) Lotimes_Lambda cal(L)_X -> g_P^(-1) (ul(M) Lotimes_Lambda cal(L)_P)
      $
      is an isomorphism. 

    Note that this problem is Zariski local in $X$, so we may assume that $X$ is affine. 

    Suppose that $ol(x)$ lies above $x in X$ so that $ol(x) = Spec(ol(k(x)))$. Let $Z$ be the closed subscheme $ol({x})$ of $X$ equipped with the reduced substructure, so that $Z$ is integral with function field $k(x)$. Let $ol(Z)$ be the normalization of $Z$ in $ol(k(x))$, so that $ol(Z)$ is normal integral with function field $ol(k(x))$. $ol(x)$ is thus the generic point of $ol(Z)$. We now have a factorization of $ol(x) -> X$ as: 
    $
      ol(x) ->^j ol(Z) ->^nu Z ->^i X
    $
    Here, $nu$, being the normalization map, is integral, and $i$ is the closed immersion. Relative base changes along them are always isomorphisms by @finite-bc-in-the-limit. Hence, it suffices to prove that the relative base change of $ul(M)$ along $j: ol(x) -> ol(Z)$ is an isomorphism.

    Here, $ol(Z)$ is the normalization of the integral finite type $S$-scheme $Z$ in the algebraic closure of its function field, which is affine since we assumed that $X$ is affine. Thus we are done by the hypothesis. 

    Finally, in the case that every finite $Lambda$-module may be embedded into a finite free $Lambda$-module, we may further embed: 
    $
      cal(F) arrow.hook oplus.big_i ol(x_i)_* ul(M) arrow.hook oplus.big_j ol(x_j)_* ul(Lambda)
    $
    and so all $M$ above can be replaced by simply $Lambda$. Thus, the $M$ in the hypothesis may be replaced by $Lambda$. 
  ]
]
