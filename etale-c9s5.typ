#import "void-import.typ": *

== The six functor formalism

In this section, we write down the six functor formalism, a set of axioms that etale cohomology has been shown to satisfy, to cleanly and elegantly conclude this arduous journey through half a thousand dense pages of mathematics. 

#theorem(name: <six-functor-formalism>)[
  (The six functor formalism) Etale cohomology is a six functor formalism. That is, given any field $k$ and any $n$-torsion noetherian ring $Lambda$ with $n in k^times$, let $X, Y, Z$ denote separated finite type $k$-schemes, and let $f: X -> Y, g: Y -> Z$ be scheme morphisms. Let $D(X)$ denote $D^b_#[ctf] (X_et, Lambda)$, which is a triangulated category. 

  0. There are six functors: #h(1fr)
    $
      R f_*, R f_!: D(X) -> D(Y) \
      f^(-1), R f^!: D(Y) -> D(X) \
      - Lotimes_Lambda -: D(X) times D(X) -> D(X) \
      RHHom_Lambda (-, -): D(X)^opp times D(X) -> D(X)
    $
    making three adjoint pairs: 
    $
      f^(-1) tack.l R f_* \
      R f_! tack.l R f^! \
      - Lotimes_Lambda cal(K) tack.l RHHom_Lambda (cal(K), -)
    $

  + $- Lotimes_Lambda -$ and $RHHom_Lambda (-, -)$ equip $D(X)$ with the structure of a closed monoidal category. 

  + There are canonical isomorphisms: 
    $
      R g_* compose R f_* cong R(g compose f)_*, R g_! compose R f_! cong R(g compose f)_! \
      f^(-1) compose g^(-1) cong (g compose f)^(-1), R f^! compose R g^! cong R (g compose f)^!
    $

  + $f^(-1)$ is monoidal, that is, there are canonical isomorphisms: 
    $
      f^(-1) (cal(K)_1 Lotimes_Lambda cal(K)_2) cong f^(-1) cal(K)_1 Lotimes_Lambda f^(-1) cal(K)_2
    $

  + (Proper base change) For every Cartesian square: 
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
    there are canonical isomorphisms: 
    $
      g^(-1) R f_! cal(K) cong R f'_! g'^(-1) cal(K)
    $
  
  + (Projection formula) There are canonical isomorphisms: 
    $
      R f_! (cal(K) Lotimes_Lambda f^(-1) cal(L)) cong R f_! cal(K) Lotimes_Lambda cal(L)
    $

  + All natural maps listed above are compatible with each other. 

    #remark[
      In reality, this means those statements "base change is compatible with concatenations of squares", "projection is compatible with base change, compositions and tensors" and so on, littered all over the document. 

      The most precise formulation of this compatibility statement requires the language of $oo$-categories. For now, don't think too much about it. Just take this statement as a claim that "if you have two maps between two objects constructed purely formally, then they should agree". 
      
      (Now of course there are two formal maps from $cal(K) Lotimes_Lambda cal(K)$ to itself, namely $id$ and symmetry. They are of course not equal. Thus the statement "if you have two maps between two objects constructed purely formally, then they should agree" should not be taken too literally, as there are formal automorphisms in the structures. However you should vaguely get what I mean.)
    ]

  In addition, there are the following etale-geometric properties: 

  7. (Comparisons) When $f$ is etale, $R f^! cong f^(-1)$ canonically. When $f$ is proper, $R f_! cong R f_*$ canonically. 

  + For a pair of complementary open and closed immersions $j: U -> X, i: Z -> X$, there are canonical distinguished triangles: 

    - (Extension by zero triangle) #h(1fr)
      $
        j_! j^(-1) cal(K) -> cal(K) -> i_* i^(-1) cal(K) ->^(+1)
      $
    
    - (Sections with support triangle)
      $
        i_* R i^! cal(K) -> cal(K) -> R j_* j^(-1) cal(K) ->^(+1)
      $

  + (Poincare duality) For smooth $f$ of relative dimension $d$, there is a canonical identification: 
    $
      R f^! cal(K) cong cal(K)(d)[2d]
    $

  + (Smooth base change) For every Cartesian square: 
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
    in which $g$ is smooth, there are canonical isomorphisms: 
    $
      g^(-1) R f_* cal(K) cong R f'_* g'^(-1) cal(K)
    $

  + (Generic base change) Suppose that $f: X -> Y$ is a morphism between finite type $S$-schemes. (Everything is still assumed to be separated of finite type over $k$.) Then for every $cal(K) in D(X)$, there exists a dense open $U subset S$ s.t. for any Cartesian diagram: #h(1fr)
    #align(center, diagram({
      node((0, 0), [$X'$])
      node((1, 0), [$Y'$])
      node((0, 1), [$X$])
      node((1, 1), [$Y$])
      // node((0.3, 0.3), [$cart$])
      node((2, 1), [$S$])
      node((2, 0), [$S'$])
      edge((0, 1), (1, 1), [$f$], label-side: right, "->")
      edge((0, 0), (1, 0), [$f'$], label-side: left, "->")
      edge((1, 0), (2, 0), "->")
      edge((1, 1), (2, 1), "->")
      edge((1, 0), (1, 1), [$g_Y$], label-side: left, "->")
      edge((2, 0), (2, 1), [$g$], label-side: left, "->")
      edge((0, 0), (0, 1), [$g_X$], label-side: right, "->")
    }))
    in which $g(S') subset U$, there is a canonical isomorphism. 
    $
      g_Y^(-1) R f_* cal(K) cong R f'_* g_X^(-1) cal(K)
    $

  + Add more statements here as you wish. 
]
#proof[
  Everything here has been proved in previous sections. It is a healthy exercise for you to look them up and review their proofs! 
]

This marks the end of our journey in etale cohomology. Thank you very much for making it here, and see you in the second part of the book, dedicated to the application of etale cohomology, namely the Weil conjectures. 

As a final gift, the next page contains a cheat sheet for etale cohomology for you to look back on what you have learned. 

#date[
  #set text(fill: red, weight: "semibold")
  #set align(left)

  Second part of this book on Weil conjectures is planned, but will not be worked on at least in a few months. Stay tuned! 
]

#pagebreak()

#block(width: 100%, height: auto, inset: 0pt, stroke: black, breakable: true, {
  stack(
    dir: ttb, 
    box(stroke: black, width: 100%, height: auto, inset: (x: 0pt, y: 7.5pt))[#align(center)[
      #text(size: 17.5pt)[Etale Cohomology#text(size: 15pt)[ (Any%)]] \
      #text(size: 10pt)[a crash course for the reluctant geometer]
    ]],
    box(stroke: black, width: 100%, height: auto, inset: (x: 0pt, y: 6pt))[
      #align(center)[#text(size: 13pt)[Etale morphisms]]
    ],
    box(stroke: black, width: 100%, height: auto, inset: (x: 6pt, y: 6pt))[
      - $f: X -> Y$ loc. of fin. pres, $f$ unramified $:<==> Omega_(X\/Y) = 0$, $f$ etale $:<==>$ flat + unramified \
      - being noetherian/regular/reduced/normal are etale local properties \
      - etale morphisms are locally std. etale: $Spec(A[T]_(g(T))\/h(T)) -> Spec(A)$ for $(h(T),h'(T))$ unit in $A[T]_(g(T))^times$ \
      - smooth/unramified/etale morphisms can be tested by infinitesimal lifting criterion \
      - strict henselization is the correct local ring for the etale topology
    ], 
    grid(columns: (1fr, 1fr), stroke: black, inset: (6pt, 6pt),
      [
        #align(center)[#text(size: 13pt)[Etale fundamental group]]
      ], 
      [
        #align(center)[#text(size: 13pt)[Etale site]]
      ]
    ), 
    grid(columns: (1fr, 1fr), stroke: black, inset: (6pt, 6pt), 
      [
        $X$ conn. noe., $ol(x)$ geom. pt., $exists$profinite group $pi_1^et (X,ol(x))$\
        - notion of finite etale \& Galois coverings
        - $F_(ol(x)): FEt_X -> GSet(pi_1^et (X, ol(x)))^#[fin,disc]$ equiv. of cat.
        - $f:X->Y$ induces $pi_1^et (X,ol(x)) -> pi_1^et (Y,ol(y))$ \
          inj./surj./trivial under geometric conditions
        - $pi_1^et (Spec(K)) = Gal_K$;
        - $pi_1^et (X) = Gal(K^"ur" (X)\/K(X))$ for $X$ normal
      ], 
      [
        #set text(size: 10pt)
        - $cAb(X_et)$ is Grothendieck abelian cat; $exists D^bullet (X_et,Lambda)$
        - $ul(M), mu_n, GG_m, GG_a in cAb(X_et)$
        - Functoriality for $f: X -> Y$: #h(1fr)
          #align(center, diagram({
            node((-1, 1), text(size: 0.7em, $cAb(Y_et)$))
            edge("->", label-side: center, $f^! #[when $f$ cl.imm.]$)
            node((0, 0), text(size: 0.7em, $cAb(X_et)$))
            edge("->", label-side: center, $f_*$)
            node((1, 1), text(size: 0.7em, $cAb(Y_et)$))
            edge("->", label-side: center, $f^(-1)$)
            node((2, 0), text(size: 0.7em, $cAb(X_et)$))
            edge("->", label-side: center, $f_! #[when $f$ etale]$)
            node((3, 1), text(size: 0.7em, $cAb(Y_et)$))
            node((0, 0.7), $tack$)
            node((1, 0.3), $tack$)
            node((2, 0.7), $tack$)
          }, spacing: (0em, 2em), label-size: 0.7em))
          Also adjoint pair $HHom(cal(F),-)$ and $- otimes cal(F)$
        - Stalks detect exact sequences
      ]
    ), 
    box(stroke: black, width: 100%, height: auto, inset: (x: 6pt, y: 6pt))[
      #align(center)[#text(size: 13pt)[Basic properties of etale cohomology]]
    ], 
    grid(columns: (1fr, 1fr), stroke: black, 
      stack(dir: ttb, 
        box(stroke: black, inset: (x: 6pt, y: 6pt), width: 100%, height: auto)[
          - $H^q (X, dirlim_i cal(F)_i) = dirlim_i H^q (X, cal(F)_i)$
          - $X = invlim_i X_i$, $H^q (X, cal(F)_0|_X) = dirlim_i H^q (X_i, cal(F)_0|_(X_i))$
          - relative/composite versions
        ], 
        box(inset: (x: 6pt, y: 6pt), width: 100%, height: auto)[
          - $(R^q f_* cal(F))_(ol(y)) = H^q (X times_Y tilde(Y)_(ol(y)), cal(F)|_(X times_Y tilde(Y)_(ol(y))))$
          - $f$ finite, $(f_* cal(F))_(ol(y)) = oplus.big_(ol(x) in f^(-1)(ol(y))) cal(F)_(ol(x))$
        ]
      ), 
      stack(dir: ttb, 
        box(stroke: black, inset: (x: 6pt, y: 6pt), width: 100%, height: auto)[
          - $H^q_et (X, cal(M)_et) = H^q_#[Zar] (X, cal(M))$, $forall cal(M) in QCoh(X)$
          - $H^1_et (X, GG_m) = Pic(X)$
          - $H^1_et (X, ul(G)) = Hom_#[cont] (pi_1^et (X),G)$, $G$ fin. ab. grp.
        ], 
        box(inset: (x: 6pt, y: 6pt), width: 100%, height: auto)[
          $f: X' -> X$ univ. homeomorphism
          - $Et_X -> Et_(X')$ equiv. of cat.
          - Equiv. on $cAb(X_et)$, $D^bullet (X_et)$, $FEt_X$
        ]
      ),
    ), 
    grid(columns: (1fr, 1fr), stroke: black, inset: (6pt, 6pt),
    [
      $X$ proj. sm. curve over $k = ol(k)$, $n in k^times$ #v(-0.8em)
      #[
        #set text(size: 0.8em)
        $
          H^q_et (X, ZZ\/n) = cases(
            ZZ\/n &\, q = 0,
            (ZZ\/n)^(oplus 2g(X)) &\, q = 1,
            ZZ\/n &\, q = 2,
            0 &\, q >= 3
          )
        $
      ]
    ], 
    [
      $X$ aff. sm. curve over $k = ol(k)$, $n in k^times$ #v(-0.8em)
      #[
        #set text(size: 0.9em)
        $
          H^q_et (X, ZZ\/n) = cases(
            ZZ\/n &\, q = 0,
            (ZZ\/n)^(oplus 2g(X)+abs(ol(X)-X)-1) &\, q = 1,
            0 &\, q >= 2
          )
        $
      ]
    ]), 
    box(inset: (x: 6pt, y: 6pt), stroke: black, height: auto, width: 100%)[
      - l.c.c. sheaves = const. after etale cover, constr. sheaves = l.c.c. on loc. closed stratification
      - constr. sheaves closed under ker, coker, extensions, $j_!$ for $j$ q.c. etale, $h_*$ for $h$ finite
      - constr. sheaves resolved on the left by $j_! ul(Lambda)$ for $j$ q.c. etale, and on the right by $h_* ul(Lambda)$ for $h$ finite
    ],
    grid(columns: (1fr, 1fr), inset: (6pt, 6pt), stroke: black, 
      [#align(center)[#text(size: 13pt)[Proper base change]]], 
      [#align(center)[#text(size: 13pt)[Local acyclicity]]], 
      [
        #set text(size: 0.85em)
        - (Proper BC) $f:X->Y$ proper, $g:Y'->Y$ b/w loc. noe. sch. $==>$ $g^(-1) R f_* cal(K) cong R f'_* g'^(-1) cal(K)$, $forall cal(K)$ torsion
        - $R f_! := R ol(f)_* j_!$ via compact'n is well defined
        - (Projection) $R f_! cal(K) Lotimes_Lambda cal(L) cong R f_! (cal(K) Lotimes f^(-1)cal(L))$
        - (Kunneth) $R f_! (p_1^(-1) cal(K)_1 Lotimes_Lambda p_2^(-1) cal(K)_2) cong R f_(1,!) cal(K)_1 Lotimes_Lambda R f_(2,!) cal(K)_2$
      ], [
        - Smooth morphisms are univ. loc. acyc.
        - (Smooth BC) $f:X->Y$ qcqs, $g:Y'->Y$ smooth $==>$ $g^(-1) R f_* cal(K) cong R f'_* g'^(-1) cal(K)$, $forall cal(K)$ torsion with order invertible in $Y$
      ]
    ), 
    box(inset: (x: 6pt, y: 6pt), stroke: black, height: auto, width: 100%)[
      #align(center)[#text(size: 13pt)[Six functor formalism \& Poincare duality]]
    ], 
    grid(columns: (1fr, 1fr), inset: (6pt, 7pt), stroke: black,
      [
        - base change is generically isom. for $cal(K) in D^b_c$
        - $f^(-1) tack.l R f_*$, $R f_! tack.l R f^!$, $- Lotimes_Lambda bullet tack.l RHHom(bullet, -)$ \
          all six functors preserve $D^b_#[ctf]$
      ], [
        - $f$ sm. of rel. dim. $d$, $R f^! cal(K) cong cal(K)(d)[2d]$; 
        - $X$ sm. of rel. dim. $d$ over $k = ol(k)$ $==>$ perfect pairing $H^q_c (X, cal(F)) times Ext^(2d-q) (cal(F), ul(ZZ\/n)(d)) -> ZZ\/n$
        #v(1fr)
      ]
    )
  )
  

  v(1fr)
})
