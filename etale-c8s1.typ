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

- A sheaf $cal(F) in cAb(X_et)$ with finite stalks is l.c.c. if and only if for every pair $t succ s$ in $X$, the specialization map $cal(F)_(ol(s)) -> cal(F)_(ol(t))$ is an isomorphism. 

This allows us to ask the question: For a proper morphism $f: X -> S$, when is $R^q f_* ul(ZZ\/n)$ l.c.c? The finiteness of stalks may be established by reduction to curves, so all that is required is to establish the specialization maps as isomorphisms. By proper base change, this amounts to an isomorphism: 
$
  H^q (X_(ol(s)), ul(ZZ\/n)) ->^tilde H^q (X_(ol(t)), ul(ZZ\/n))
$
We will see how this morphism can be expressed by embedding both geometric fibers in $X times_S tilde(S)_(ol(s))$, then translated through a vanishing cycle construction to the statement (2). Then through devissage arguments, (3) will imply (4). 

There is a final side remark regarding coefficient rings. 

#remark[
  The main application of the theory of etale cohomology is the proof of the Weil conjectures, which requires establishing the theory of $ell$-adic sheaves. That is, over a scheme $X$ with characteristic $p$, for every $ell != p$, there is a cohomology theory with coefficients in $ol(QQ_ell)$. Such a cohomology theory is established by doing it over every finite extension $E\/QQ_ell$, by passing from the ring of integers $cal(O)_E$, which is itself constructed by a limit construction from etale sheaves with coefficients $cal(O)_E\/frak(m)_E^N$. 

  Thus, the most important coefficient rings, and a class of coefficient rings enough for application, are the rings $Lambda = cal(O)_E\/frak(m)_E^N$ for a finite extension $E\/QQ_ell$ with $ell in cal(O)_X^times$. (This includes the rings $ZZ\/ell^N$.) These $Lambda$ together with $Lambda = ZZ\/n, n in cal(O)_X^times$ have the following desirable properties: 

  - $Lambda$ is a torsion ring with torsion coefficient in $cal(O)_X^times$; 

  - $Lambda$ is a finite ring, so constructible sheaves of $Lambda$-modules are just sheaves of $Lambda$-modules constructible as sheaves of abelian groups; 

  - Every finite $Lambda$-module admits an injection into a free $Lambda$-module of finite rank; 

  - $Lambda$ is an injective $Lambda$-module. 

  Thus, whenever you see one of these seemingly arbitrary conditions in the hypotheses of a proposition, you can stay motivated and know that such conditions are satisfied in practice. 
]

Throughout this chapter, $Lambda$ is assumed to be a torsion ring. 

== General reduction on base changes

#definition[
  For a scheme $X$, a geometric point $ol(x)$ above $x in X$ is called an *algebraic geometric point*, if $k(ol(x))$ is an algebraic closure of $k(x)$. 
]

#definition(name: <constructible-finite-tor-derived-category>)[
  We use $D^b_#[ctf] (X_et, Lambda)$ to denote the triangulated category of bounded complexes of etale sheaves of $Lambda$-modules on $X$ with constructible cohomology sheaves, and with finite Tor-dimension (i.e. the functor $cal(K) Lotimes_Lambda -$ is bounded above and below). Equivalently, such a complex is in $D^b_c$ and has a bounded flat resolution. 

  #lemma(name: <resolution-of-ctf-complexes>)[
    (#cite-stacks("03TT")[Lemma 59.77.3]) Let $Lambda$ be noetherian and $X$ be a noetherian scheme, and let $cal(K) in D^b_#[ctf] (X_et, Lambda)$ satisfy that $cal(K) Lotimes_Lambda cal(G) in D_([a,b]) (X_et, Lambda)$ for all sheaves $cal(G) in cAb(X_et, Lambda)$. Then $cal(K)$ can be represented by a complex: 
    $
      0 -> cal(F)^a -> cal(F)^(a+1) -> dots.c -> cal(F)^b -> 0
    $ 
    in which every $cal(F)^q$ is constructible and flat. 
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
    The complex $cal(L)$ is in $D^b_#[ctf] (X_et, Lambda)$, and has Tor-amplitude contained in $[a,b-1]$. Indeed, the map $cal(F) -> h^b (cal(K))$ is surjective. Thus tensoring with an arbitrary sheaf $cal(G)$, we have a long exact sequence: 
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

  The bounded flat resolutions of complexes in $D^b_#[ctf]$ are especially useful, since tensoring with them commutes with homotopy directed limits, as stated in the following lemma. 
  #lemma(name: <dirhlim-and-bounded-flat-resln>)[
    Let $T$ be a scheme, and ${cal(M)_i}_(i in I)$ be a directed system in $D_(>=a) (T_et, Lambda)$, with compatible maps to $cal(M) in D_(>=a) (T_et, Lambda)$ s.t: 
    $
      dirhlim_(i in I) cal(M)_i cong cal(M)
    $
    Then for any bounded complex $cal(P)^bullet$ of flat sheaves on $T$:
    $
      dirhlim_(i in I) (cal(M)_i Lotimes_Lambda cal(P)^bullet) cong cal(M) Lotimes_Lambda cal(P)^bullet
    $
  ]
  #proof[
    We want to prove the statements: 
    $
      dirlim_(i in I) h^q (cal(M)_i Lotimes_Lambda cal(P)^bullet) cong h^q (cal(M) Lotimes_Lambda cal(P)^bullet)
    $

    We perform induction on the length of the flat resolution. Let $cal(P)^bullet$ be supported on $[b_1, b_2]$, and we induct on $b_2 - b_1$. The base case $b_2 - b_1 < 0$ is vacuous. Consider the stupid truncation: 
    $
      cal(P)^(b_2)[-b_2] -> cal(P)^bullet -> sigma_(<=b_2-1) cal(P)^bullet ->^(+1)
    $
    Now: 
    $
      dirlim_i h^q (cal(M)_i Lotimes_Lambda sigma_(<=b_2-1) cal(P)^bullet) cong h^q (cal(M) Lotimes_Lambda sigma_(<=b_2-1) cal(P)^bullet)
    $
    by the inductive hypothesis, and: 
    $
      dirlim_i h^q (cal(M)_i Lotimes_Lambda cal(P)^(b_2) [-b_2]) cong dirlim_i (h^(q-b_2) (cal(M)_i) otimes_Lambda cal(P)^(b_2)) cong h^(q-b_2) (cal(M)) otimes_Lambda cal(P)^(b_2) cong h^q (cal(M) Lotimes_Lambda cal(P)^(b_2) [-b_2])
    $
    by assumption. By applying five lemma to the map between the long exact sequences obtained by applying both $dirlim_i h^q (cal(M)_i Lotimes_Lambda -)$ and $h^q (cal(M) Lotimes_Lambda -)$ to the stupid truncation triangle, we may conclude that: 
    $
      dirlim_i h^q (cal(M)_i Lotimes_Lambda cal(P)^bullet) cong h^q (cal(M) Lotimes_Lambda cal(P)^bullet)
    $
    for each $q in ZZ$. 
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
    the relative base change $h^(-1) g^(-1) R f_* cal(K) Lotimes_Lambda h^(-1) cal(L) -> R f''_* (h'^(-1) g'^(-1) cal(K) Lotimes_Lambda f''^(-1) h^(-1) cal(L))$ relative to $h^(-1) cal(L)$, is the composition: 
    $
      h^(-1) g^(-1) R f_* cal(K) Lotimes_Lambda h^(-1) cal(L) &cong h^(-1) (g^(-1) R f_* cal(K) Lotimes_Lambda cal(L)) \
      &-> h^(-1) R f'_* (g'^(-1) cal(K) Lotimes_Lambda f'^(-1) cal(L)) \
      &-> R f''_* h'^(-1) (g'^(-1) cal(K) Lotimes_Lambda f'^(-1) cal(L)) \
      &cong R f''_* (h'^(-1) g'^(-1) cal(K) Lotimes_Lambda f''^(-1) h^(-1) cal(L))
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
      g^(-1) R f_* R h_* cal(K) Lotimes_Lambda cal(L) -> R f'_* (g'^(-1) R h_* cal(K) Lotimes_Lambda f'^(-1) cal(L)) -> R f'_* R h'_* (g''^(-1) cal(K) Lotimes_Lambda h'^(-1) f'^(-1) cal(L))
    $
    of the relative base change of the right square w.r.t. $cal(L)$ and the relative base change of the left square w.r.t. $f'^(-1) cal(L)$. 
]

Proper base change gives a condition on $f$ so that the relative base change map is an isomorphism, namely $f$ being proper. It is thus natural to study the problem in the $g$-aspect. That is, we want to ask for a condition on $g$, so that the relative base change map established above is an isomorphism. 

To establish the main result, we need some preliminary statements. Firstly, we need an embedding result to use for @abstract-devissage. 

#lemma(name: <constructible-godement-resolution>)[
  Let $Lambda$ be a noetherian ring, $X$ be a noetherian scheme, and $cal(F) in cAb(X_et, Lambda)$ be a constructible sheaf of $Lambda$-modules. Then there exist a finite list of algebraic geometric points $ol(x_1), dots.c, ol(x_m)$ of $X$, finite $Lambda$-modules $M_1, dots.c, M_m$, and an injection:
  $
    cal(F) -> oplus.big_(i=1)^m ol(x_i)_* ul(M_i)
  $
  If every finite $Lambda$-module embeds into a finite free $Lambda$-module, we may take every $M_i = Lambda$. 
]
#proof[
  By @finite-morphisms-and-constructible-sheaves (2), there exist a finite morphism $h: X' -> X$, a finite $Lambda$-module $M$, and an injection $cal(F) -> h_* ul(M)_(X')$.

  Since $X'$ is noetherian, it has finitely many irreducible components. Let $x'_1, dots.c, x'_m$ be their generic points, and choose an algebraic geometric point $ol(x'_i)$ above each $x'_i$. We claim that the canonical map:
  $
    ul(M)_(X') -> oplus.big_(i=1)^m ol(x'_i)_* ul(M)
  $
  is injective. The nonempty connected affine objects $U in Et_(X')$ form a basis, and on such a $U$ this is the diagonal map:
  $
    M -> oplus.big_(i=1)^m product_(pi_0 (U_(ol(x'_i)))) M.
  $
  The image of $U$ in $X'$ is nonempty and open, hence contains some $x'_i$. Thus $U_(ol(x'_i))$ is nonempty, and projection onto any corresponding coordinate recovers the original element of $M$. This proves injectivity.

  Applying $h_*$, which preserves injections and finite direct sums, and using composition of direct images gives:
  $
    cal(F) -> h_* ul(M)_(X') -> oplus.big_(i=1)^m (h compose ol(x'_i))_* ul(M).
  $
  Put $ol(x_i) = h compose ol(x'_i)$ and $M_i = M$. Since $h$ is finite, these are algebraic geometric points of $X$, proving the first assertion.

  Under the additional hypothesis, choose injections $M_i -> Lambda^(oplus r_i)$. Taking constant sheaves and pushing forward along $ol(x_i)$ preserves these injections. Splitting each finite direct sum and repeating each $ol(x_i)$ by $r_i$ times proves the last assertion.
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
  By @limit-formula-adjunction, $cal(F) = dirlim_i h_i^(-1) h_(i,*) cal(F)$. Put $cal(F)_i = h_(i,*) cal(F)$. Thus by @relative-limit-formula-composite, 
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
  i.e. standard base change for an integral pushforward is an isomorphism. For a relative base change, it suffices to prove that the projection part is an isomorphism. This follows from the base change part, the compatibility of projection with base change, and @projection-formula-for-global-sections. (Here, geometric fibers of an integral morphism are integral over a separably closed field, hence affine. Furthermore, these fibers have etale cohomological dimension $0$ by @cohom-dim-of-rings-props (2)(3). Thus, the qcqs and bounded above global sections assumptions in @projection-formula-for-global-sections are satisfied.)
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

  Thus, both sides of $g_Y^(-1) R f_* cal(K) Lotimes_Lambda cal(L)_Y -> R f'_* (g_X^(-1) cal(K) Lotimes_Lambda cal(L)_X)$ are bounded below in $cal(K)$. By the way-out lemma, it suffices to deal with the case that $cal(K) = cal(F) in cAb(X_et, Lambda)$ is just a single sheaf. From now on we always assume $cal(K) = cal(F)$ is a single sheaf. 

  Fix a bounded flat resolution $cal(P)_S^bullet$ of $cal(L)_S$ supported on $[b_1, b_2]$, and denote its pullbacks to $X'$ and $Y'$ by $cal(P)_X^bullet$ and $cal(P)_Y^bullet$. They are flat resolutions of $cal(L)_X$ and $cal(L)_Y$ respectively, supported on $[b_1, b_2]$. 

  Step 1. It suffices to deal with the case where $X -> Y$ is of finite presentation. 

  #proof_[Proof of Step 1][
    Note that $f: X -> Y$ is qcqs, and so by @relative-approx, we may write $X = invlim_lambda X_lambda$ as a projective limit of finite presentation $Y$-schemes with affine transition morphisms. We thus have the following Cartesian diagram of $S$-schemes: 
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
    Take $cal(F)_lambda = h_(lambda,*) cal(F)$, so that by @limit-formula-adjunction, $cal(F) cong dirlim_lambda h_lambda^(-1) cal(F)_lambda$. 
    
    Then: 
    
    - By @relative-limit-formula-composite, $dirhlim_lambda R f_(lambda,*) cal(F)_lambda cong R f_* cal(F)$. Thus, by exactness of pullback and @dirhlim-and-bounded-flat-resln, we have: 
      $
        dirhlim_lambda (g_Y^(-1) R f_(lambda,*) cal(F)_lambda Lotimes_Lambda cal(L)_Y) cong g_Y^(-1) R f_* cal(F) Lotimes_Lambda cal(L)_Y
      $

    - Since: 
      $
        dirhlim_lambda h'_lambda^(-1) (g_lambda^(-1) cal(F)_lambda Lotimes_Lambda f'_lambda^(-1) cal(L)_Y) cong dirhlim_lambda (g_X^(-1) h_lambda^(-1) cal(F)_lambda Lotimes_Lambda f'^(-1) cal(L)_Y)
      $
      By $dirlim_lambda h_lambda^(-1) cal(F)_lambda cong cal(F)$, exactness of $g_X^(-1)$ and @dirhlim-and-bounded-flat-resln, we may conclude that: 
      $
        dirhlim_lambda h'_lambda^(-1) (g_lambda^(-1) cal(F)_lambda Lotimes_Lambda f'_lambda^(-1) cal(L)_Y) cong g_X^(-1) cal(F) Lotimes_Lambda f'^(-1) cal(L)_Y
      $
    
      All complexes in the limit above are supported on $[b_1, b_2]$. Thus by @derived-relative-limit-formula-composite, we may conclude that: 
      $
        dirhlim_lambda R f'_(lambda,*) (g_lambda^(-1) cal(F)_lambda Lotimes_Lambda f'_lambda^(-1) cal(L)_Y) cong R f'_* (g_X^(-1) cal(F) Lotimes_Lambda cal(L)_X)
      $

    By the assumed finite presentation case, we have canonical isomorphisms:
    $
      g_Y^(-1) R f_(lambda,*) cal(F)_lambda Lotimes_Lambda cal(L)_Y cong R f'_(lambda,*) (g_lambda^(-1) cal(F)_lambda Lotimes_Lambda f'_lambda^(-1) cal(L)_Y)
    $
    Thus through the two limits, we may conclude that $g_Y^(-1) R f_* cal(F) Lotimes_Lambda cal(L)_Y cong R f'_* (g_X^(-1) cal(F) Lotimes_Lambda cal(L)_X)$. 
  ]  

  Step 2. It suffices to deal with the case where $f: X -> Y$ is between finite type $S$-schemes. 

  #proof_[Proof of Step 2][
    By Step 1, we may assume that $f: X -> Y$ is of finite presentation between qcqs $S$-schemes. By @passage-to-limit-of-morphisms and @relative-approx, we may write $Y = invlim_i Y_i$ with $Y_i$ being finite type $S$-schemes for $i >= 0$, and we have a finite type morphism $f_0: X_0 -> Y_0$ whose base change along $Y -> Y_0$ is just $f: X -> Y$. Let $f_i: X_i -> Y_i$ be the base change of $f_0$ along $Y_i -> Y_0$. 

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
    where the vertical morphisms are base changes of $g: S' -> S$. Put $cal(F)_i = k_(i,*) cal(F)$ so that $cal(F) = dirlim_i k_i^(-1) cal(F)_i$ by @limit-formula-adjunction. 
    
    - Consider: 
      $
        dirhlim_i h'_i^(-1) (g_(Y_i)^(-1) R f_(i,*) cal(F)_i Lotimes_Lambda cal(L)_(Y_i)) &cong dirhlim_i (h'_i^(-1) g_(Y_i)^(-1) R f_(i,*) cal(F)_i Lotimes_Lambda cal(L)_Y)
      $
      By @limit-formula-for-base-change, $dirhlim_i h'_i^(-1) g_(Y_i)^(-1) R f_(i,*) cal(F)_i cong g_Y^(-1) dirhlim_i h_i^(-1) R f_(i,*) cal(F)_i cong g_Y^(-1) R f_* cal(F)$. Thus by @dirhlim-and-bounded-flat-resln, 
      $
        dirhlim_i h'_i^(-1) (g_(Y_i)^(-1) R f_(i,*) cal(F)_i Lotimes_Lambda cal(L)_(Y_i)) cong g_Y^(-1) R f_* cal(F) Lotimes_Lambda cal(L)_Y
      $

    - Consider: 
      $
        dirhlim_i h'_i^(-1) R f'_(i,*) (g_(X_i)^(-1) cal(F)_i Lotimes_Lambda f'_i^(-1) cal(L)_i)
      $
      Note that: 
      $
        dirhlim_i k'_i^(-1) (g_(X_i)^(-1) cal(F)_i Lotimes_Lambda f'_i^(-1) cal(L)_i) cong dirhlim_i (g_X^(-1) k_i^(-1) cal(F)_i Lotimes_Lambda f'^(-1) cal(L)_Y)
      $
      Since $dirlim_i k_i^(-1) cal(F)_i = cal(F)$ and $g_X^(-1)$ is exact, by @dirhlim-and-bounded-flat-resln, this limit is $dirhlim_i k'_i^(-1) (g_(X_i)^(-1) cal(F)_i Lotimes_Lambda f'_i^(-1) cal(L)_i) cong g_X^(-1) cal(F) Lotimes_Lambda f'^(-1) cal(L)_Y cong g_X^(-1) cal(F) Lotimes_Lambda cal(L)_X$. Now by @derived-limit-formula-for-base-change, we may conclude that: 
      $
        dirhlim_i h'_i^(-1) R f'_(i,*) (g_(X_i)^(-1) cal(F)_i Lotimes_Lambda f'_i^(-1) cal(L)_i) cong R f'_* (g_X^(-1) cal(F) Lotimes_Lambda cal(L)_X)
      $
    By the assumed finite type over $S$ case, we have canonical isomorphisms: 
    $
      g_(Y_i)^(-1) R f_(i,*) cal(F)_i Lotimes_Lambda cal(L)_(Y_i) cong R f'_(i,*) (g_(X_i)^(-1) cal(F)_i Lotimes_Lambda f'_i^(-1) cal(L)_i)
    $
    Thus the LHSs of the two limits agree. Thus we may conclude that:
    $
      g_Y^(-1) R f_* cal(F) Lotimes_Lambda cal(L)_Y cong R f'_* (g_X^(-1) cal(F) Lotimes_Lambda cal(L)_X)
    $
  ]

  Step 3. It suffices to deal with the case where $f: X -> Y$ is an open immersion where $Y$ is of finite type over $S$. 

  #proof_[Proof of Step 3][
    By Step 2, we may assume that $f: X -> Y$ is between finite type $S$-schemes. 

    Suppose that $f$ is additionally separated. Since $S$ is noetherian, so are $X$ and $Y$. Thus we may pick a compactification $X ->^j ol(X) ->^(ol(f)) Y$. Now the relative base change for $cal(L)_(ol(X))$ along $j$ is an isomorphism by hypotheses, and that for $cal(L)_Y$ along $ol(f)$ is an isomorphism by proper base change. Thus the relative base change along $f$ for $cal(L)_Y$ is an isomorphism, and we are done. 

    For the general case, we use noetherian induction to patch together cases for affine $X$. For a closed subset $Z subset X$ equipped with the reduced substructure, let $i_Z: Z -> X$ be its inclusion, and $P(Z)$ denote the statement: 

    - For every $cal(K) in D^+ (Z_et, Lambda)$, the relative base change: 
      $
        g_Y^(-1) R f_* i_(Z,*) cal(K) Lotimes_Lambda cal(L)_Y -> R f'_* (g_X^(-1) i_(Z,*)  cal(K) Lotimes_Lambda cal(L)_X)
      $
      is an isomorphism. 

    Now the RHS above is always isomorphic to $R f'_* (i'_(Z,*) g_Z^(-1) cal(K) Lotimes_Lambda cal(L)_X)$ (where $g_Z: Z' -> Z$, $i'_Z: Z' -> X'$ are the base changes of $g_X$ and $i_Z$). Thus, the statement $P(Z)$ is equivalent to the relative base change being an isomorphism along $f compose i_Z: Z -> Y$. Hence, we may replace $X$ with $Z$, and aim to prove $P(X)$ assuming $P(Z)$ for every proper closed subset $Z subset X$. 

    Pick an affine open $U subset X$, and form the complement $Z = X - U subset X$, equipped with reduced induced substructure. Let $j: U -> X, i: Z -> X$ be the complementary immersions. Now consider the sections with support triangle @derived-functoriality-etale (6b): 
    $
      i_* R i^! cal(K) -> cal(K) -> R j_* j^(-1) cal(K) ->^(+1)
    $
    - By $P(Z)$, the relative base change $g_Y^(-1) R f_* i_* R i^! cal(K) Lotimes_Lambda cal(L)_Y -> R f'_* (g_X^(-1) i_* R i^! cal(K) Lotimes_Lambda cal(L)_X)$ is an isomorphism. 

    - Since $U$ is affine, $j: U -> X$ and $j compose f: U -> Y$ are both separated between finite type $S$-schemes. Thus by the separated case, 
      $
        g_Y^(-1) R f_* R j_* j^(-1) cal(K) Lotimes_Lambda cal(L)_Y cong R f'_* R j'_* (g_U^(-1) j^(-1) cal(K) Lotimes_Lambda cal(L)_U) cong R f'_* (g_X^(-1) R j_* j^(-1) cal(K) Lotimes_Lambda cal(L)_X) 
      $

    These two isomorphisms together with the extension by zero triangle establishes the isomorphism $g_Y^(-1) R f_* cal(K) Lotimes_Lambda cal(L)_Y cong R f'_* (g_X^(-1) cal(K) Lotimes_Lambda cal(L)_X)$.
  ]

  Step 4. It suffices to deal with the case where $f$ is replaced by $j: xi -> X$, the inclusion of the generic point of $X$, where $X$ is the normalization of a finite type integral (not necessarily affine) $S$-scheme in the algebraic closure of its function field. 

  #proof[
    Let's assume for now that every finite $Lambda$-module embeds into a finite free $Lambda$-module. 

    Let $f: X -> Y$ be an open immersion between finite type $S$-schemes. In particular, $X, Y$ are noetherian. We want to show that the relative base change: 
    $
      g_Y^(-1) R f_* cal(F) Lotimes_Lambda cal(L)_Y -> R f'_* (g_X^(-1) cal(F) Lotimes_Lambda cal(L)_X)
    $
    is an isomorphism for all $cal(F) in cAb(X_et, Lambda)$. 

    Let $j: ol(x) -> X$ be the inclusion of an algebraic geometric point $ol(x)$ above $x in X$. Let $T$ be the normalization of $ol({x}) subset X$ (equipped with its reduced induced substructure) in the algebraic closure of its function field. Then $T$ is an integral normal scheme with function field $ol(k(x)) = k(ol(x))$. Then $j$ factors as $ol(x) ->^q T ->^i X$, where $i$ is integral, and $q$ is the inclusion of the generic point of the normalization of a finite type integral $S$-scheme in the algebraic closure of its function field. By the hypothesis of the theorem, relative base change for the sheaf $ul(Lambda)$ along $q$ is an isomorphism. 

    Forming the Cartesian diagram: 
    // https://q.uiver.app/#r=typst&q=WzAsOCxbMCwwLCJQJyJdLFswLDEsIm9sKHgpIl0sWzEsMSwiVCJdLFsyLDEsIlgiXSxbMywxLCJZIl0sWzEsMCwiVCciXSxbMiwwLCJYJyJdLFszLDAsIlknIl0sWzIsMywiaSIsMl0sWzMsNCwiZiIsMl0sWzEsMiwicSIsMl0sWzAsNSwicSciXSxbNSw2LCJpJyJdLFs2LDcsImYnIl0sWzcsNCwiZ19ZIl0sWzYsMywiZ19YIl0sWzUsMiwiZ19UIl0sWzAsMSwiZ19QIiwyXV0=
    #align(center, diagram({
      node((0, 0), [$P'$])
      node((0, 1), [$ol(x)$])
      node((1, 1), [$T$])
      node((2, 1), [$X$])
      node((3, 1), [$Y$])
      node((1, 0), [$T'$])
      node((2, 0), [$X'$])
      node((3, 0), [$Y'$])
      node((0.3, 0.3), $cart$)
      node((1.3, 0.3), $cart$)
      node((2.3, 0.3), $cart$)
      edge((1, 1), (2, 1), [$i$], label-side: right, "->")
      edge((2, 1), (3, 1), [$f$], label-side: right, "->")
      edge((0, 1), (1, 1), [$q$], label-side: right, "->")
      edge((0, 0), (1, 0), [$q'$], label-side: left, "->")
      edge((1, 0), (2, 0), [$i'$], label-side: left, "->")
      edge((2, 0), (3, 0), [$f'$], label-side: left, "->")
      edge((3, 0), (3, 1), [$g_Y$], label-side: left, "->")
      edge((2, 0), (2, 1), [$g_X$], label-side: left, "->")
      edge((1, 0), (1, 1), [$g_T$], label-side: left, "->")
      edge((0, 0), (0, 1), [$g_P$], label-side: right, "->")
    }))
    Then the relative base change: 
    $
      & g_X^(-1) R j_* ul(Lambda) Lotimes_Lambda cal(L)_X cong g_X^(-1) R i_* R q_* ul(Lambda) Lotimes_Lambda cal(L)_X \
      cong& R i'_* (g_T^(-1) R q_* ul(Lambda) Lotimes_Lambda cal(L)_T) #[by @finite-bc-in-the-limit] \
      cong& R i'_* R q'_* cal(L)_P #[by the assumption] \
      cong& R j'_* cal(L)_P
    $
    is an isomorphism. Meanwhile, $f compose j: ol(x) -> Y$ is also the inclusion of an algebraic geometric point, so by the same argument, the relative base change: 
    $
      g_Y^(-1) R f_* R j_* ul(Lambda) Lotimes_Lambda cal(L)_Y -> R f'_* R j'_* cal(L)_P
    $
    is an isomorphism. Thus we have an isomorphism: 
    $
      g_Y^(-1) R f_* R j_* ul(Lambda) Lotimes_Lambda cal(L)_Y cong R f'_* R j'_* cal(L)_P cong R f'_* (g_X^(-1) R j_* ul(Lambda) Lotimes_Lambda cal(L)_X)
    $
    By the compatibility of relative base change with composition, this isomorphism is identified with the relative base change of the sheaf $R j_* ul(Lambda) = ol(x)_* ul(Lambda)$ along $cal(F)$. We may thus conclude that: 

    - The relative base change: 
      $
        g_Y^(-1) R f_* cal(F) Lotimes_Lambda cal(L)_Y -> R f'_* (g_X^(-1) cal(F) Lotimes_Lambda cal(L)_X)
      $
      is an isomorphism whenever $cal(F) = ol(x)_* ul(Lambda)$. 

    We now apply @abstract-devissage to the natural transformation of $delta$-functors: 
    $
      h^q (g_Y^(-1) R f_* (-) Lotimes_Lambda cal(L)_Y) -> h^q (R f'_* (g_X^(-1) (-) Lotimes_Lambda cal(L)_X))
    $
    on $cAb(X_et, Lambda)$. 
    - Both sides vanishes for $q < b_1$, since $cal(L)_S$ has a flat resolution supported on $[b_1,b_2]$. 

    - Both sides commutes with direct limits. Suppose $cal(F) = dirlim_lambda cal(F)_lambda$. Then:
    
      - By @relative-limit-formula-for-sheaves, $dirhlim_lambda R f_* cal(F)_lambda cong R f_* cal(F)$. Thus by @dirhlim-and-bounded-flat-resln, 
        $
          dirhlim_lambda (g_Y^(-1) R f_* cal(F)_lambda Lotimes_Lambda cal(L)_Y) cong g_Y^(-1) R f_* cal(F) Lotimes_Lambda cal(L)_Y
        $

      - By @dirhlim-and-bounded-flat-resln, $dirhlim_lambda (g_X^(-1) cal(F)_lambda Lotimes_Lambda cal(L)_X) cong g_X^(-1) cal(F) Lotimes_Lambda cal(L)_X$. Thus by @derived-relative-limit-formula-composite, 
        $
          dirhlim_lambda R f'_* (g_X^(-1) cal(F)_lambda Lotimes_Lambda cal(L)_X) cong R f'_* (g_X^(-1) cal(F) Lotimes_Lambda cal(L)_X)
        $

    - Every $cal(F) in cAb(X_et, Lambda)$ may be written as a direct limit of constructible sheaves of $Lambda$-modules. 

    - By @constructible-godement-resolution, every constructible sheaf $cal(F)$ of $Lambda$-module on $X$ admits an embedding $cal(F) arrow.hook oplus.big_(i=1)^r ol(x_i)_* ul(Lambda)$ for geometric points $ol(x_1), dots.c, ol(x_r)$, which may be taken to be algebraic. We have shown that the relative base change map is an isomorphism for sheaves of the shape $oplus.big_(i=1)^r ol(x_i)_* ul(Lambda)$. 

    Thus applying the abstract devissage @abstract-devissage concludes the proof in the case that every finite $Lambda$-module embeds into a finite free one. In case that we don't have this assumption, the proof is identical - use the same argument to show that the relative base change is an isomorphism for sheaves of the shape $ol(x)_* ul(M)$ for finite $Lambda$-modules $M$, then applying @constructible-godement-resolution for @abstract-devissage. 
  ]

  Step 5. Concluding the proof. 
  #proof[
    Let $j: xi -> X$ be the inclusion of the generic point of the normalization of an integral finite type $S$-scheme $X_0$ in the algebraic closure of its function field. We want to reduce to the case that $X_0$ is affine. Indeed, for any affine open $U_0 subset X_0$, form the Cartesian diagram: 
    // https://q.uiver.app/#r=typst&q=WzAsNixbMCwwLCJQJyJdLFswLDEsInhpIl0sWzEsMSwiVSJdLFsyLDEsIlgiXSxbMiwwLCJYJyJdLFsxLDAsIlUnIl0sWzEsMiwicSIsMl0sWzIsMywiZWxsIiwyXSxbMCw1LCJxJyJdLFs1LDQsImVsbCciXSxbNCwzLCJnX1giXSxbNSwyLCJnX1UiXSxbMCwxLCJnX1AiLDJdXQ==
    #align(center, diagram({
      node((0, 0), [$P'$])
      node((0, 1), [$xi$])
      node((1, 1), [$U$])
      node((2, 1), [$X$])
      node((2, 0), [$X'$])
      node((1, 0), [$U'$])
      node((0.3, 0.3), $cart$)
      node((1.3, 0.3), $cart$)
      edge((0, 1), (1, 1), [$q$], label-side: right, "->")
      edge((1, 1), (2, 1), [$ell$], label-side: right, "->")
      edge((0, 0), (1, 0), [$q'$], label-side: left, "->")
      edge((1, 0), (2, 0), [$ell'$], label-side: left, "->")
      edge((2, 0), (2, 1), [$g_X$], label-side: left, "->")
      edge((1, 0), (1, 1), [$g_U$], label-side: left, "->")
      edge((0, 0), (0, 1), [$g_P$], label-side: right, "->")
    }))
    Then $U$ is the normalization of $U_0$ in $k(xi)$, and by the hypothesis, relative base change is an isomorphism along $q$. 

    Now for $M = Lambda$, or for any finite $Lambda$-module $M$ if we do not assume that every finite $Lambda$-module embeds into a finite free one: 
    $
      & ell'^(-1) (g_X^(-1) R j_* ul(M) Lotimes_Lambda cal(L)_X) cong g_U^(-1) ell^(-1) R ell_* R q_* ul(M) Lotimes_Lambda ell'^(-1) cal(L)_X cong g_U^(-1) R q_* ul(M) Lotimes_Lambda cal(L)_U\
      cong & R q'_* (ul(M) Lotimes_Lambda cal(L)_P) #[by the hypothesis] \
      cong & ell'^(-1) R ell'_* R q'_* (ul(M) Lotimes_Lambda cal(L)_P) cong ell'^(-1) R j'_* (ul(M) Lotimes_Lambda cal(L)_P)
    $
    Thus the relative base change $g_X^(-1) R j_* ul(M) Lotimes_Lambda cal(L)_X -> R j'_* (ul(M) Lotimes_Lambda cal(L)_P)$ restricts to isomorphisms on an open cover ${U'}$ of $X'$, hence is an isomorphism. 
  ]
]
