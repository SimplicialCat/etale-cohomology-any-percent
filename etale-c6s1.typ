#import "void-import.typ": *

We are now ready to enter the realm of base change theorems in etale cohomology. 

As always, we attempt to give motivations to each piece of theory we introduce. 

The motivation of etale cohomology is a cohomology theory for algebraic varieties, analogous to Betti cohomology for CW complexes.

Thus, we have several large theorems that we need to establish:

+ Basic results on $H^q_et (X, ZZ\/n)$ for an algebraic variety over an algebraically closed field $k$ with $n in k^times$. (If $n = p = "char"(k) > 0$, this cohomology is rather ill-behaved.)
  - Finiteness
  - Vanishing (beyond $2 dim(X)$, and beyond $dim(X)$ in affine case)
  - Cohomology with compact support
  - Poincare duality
  - ...

+ Etale cohomology has applications to number theory: Consider an algebraic variety $X\/QQ$, and we may base change it to $X_(overline(QQ)) = X times_QQ overline(QQ)$, the algebraic closure of $QQ$.
  
  Now $Gal_QQ$ has an action on $H^q_et (X_(overline(QQ)), ZZ\/n)$ which is continuous by the limit formula for schemes, $H^q_et (X_(overline(QQ)), ZZ\/n) = colim_(L\/QQ #[finite Galois]) H^q_et (X_L, ZZ\/n)$. This would give a Galois representation: 
  $
    Gal_QQ -> End(H^q_et (X_(ol(QQ)), ZZ\/n))
  $
  This construction is fundamental, in the sense that taking $n = ell, ell^2, ell^3, dots.c$ and passing to a projective limit, we would have a continuous representation: 
  $
    Gal_QQ -> End(H^q_et (X_(ol(QQ)), ZZ_ell)), H^q_et (X_(ol(QQ)), ZZ_ell) := invlim_(n>=1) H^q_et (X_(ol(QQ)), ZZ\/ell^n)
  $
  Now $H^q_et (X_(ol(QQ)), ZZ_ell)$ is a finite-rank $ZZ_ell$-module, which, upon tensoring with $QQ_ell$, gives a finite-dimensional $QQ_ell$-vector space $H^q_et (X_(ol(QQ)), QQ_ell) := H^q_et (X_(ol(QQ)), ZZ_ell) otimes_(ZZ_ell) QQ_ell$. This gives a good characteristic 0 cohomology theory for a scheme, and a continuous representation: 
  $
    Gal_QQ -> End(H^q_et (X_(ol(QQ)), QQ_ell))
  $
  of the absolute Galois group on a finite-dimensional vector space over a characteristic 0 field. 

  How do we study Galois representations $Gal_QQ -> End(H^q_et (X_(overline(QQ)), ZZ\/n))$? For each $p$ s.t. $gcd(p, n) = 1$, we fix an inclusion $overline(QQ) -> overline(QQ_p)$, giving an inclusion $Gal_(QQ_p) arrow.r.hook Gal_QQ$. We want an isomorphism: 
 
  $
    H^q_et (X_(overline(QQ)), ZZ\/n) ->^tilde_(#[(a)]) H^q_et (X_(overline(QQ_p)), ZZ\/n)
  $
  
  where $Gal_QQ$ acts on the left, and $Gal_(QQ_p)$ acts on the right so that we can study the local case. Next, suppose that $X_(QQ_p)$ admits an integral model $X_(ZZ_p) -> Spec(ZZ_p)$, then we have a commutative diagram: 
  // https://q.uiver.app/#r=typst&q=WzAsNixbMSwwLCJYXyhaWl9wXnVyKSJdLFsyLDAsIlhfKG9sKEZGX3ApKSJdLFsxLDEsIlNwZWMoWlpfcF51cikiXSxbMiwxLCJTcGVjKG9sKEZGX3ApKSJdLFswLDAsIlhfKG9sKFFRX3ApKSJdLFswLDEsIlNwZWMob2woUVFfcCkpIl0sWzUsMl0sWzMsMl0sWzQsMF0sWzEsMF0sWzAsMl0sWzEsM10sWzQsNV1d
  #align(center, diagram({
    node((0, -1), [$X_(ZZ_p^#[ur])$])
    node((1, -1), [$X_(ol(FF_p))$])
    node((0, 0), [$Spec(ZZ_p^#[ur])$])
    node((1, 0), [$Spec(ol(FF_p))$])
    node((-1, -1), [$X_(ol(QQ_p))$])
    node((-1, 0), [$Spec(ol(QQ_p))$])
    edge((-1, 0), (0, 0), "->")
    edge((1, 0), (0, 0), "->")
    edge((-1, -1), (0, -1), "->")
    edge((1, -1), (0, -1), "->")
    edge((0, -1), (0, 0), "->")
    edge((1, -1), (1, 0), "->")
    edge((-1, -1), (-1, 0), "->")
  }))
  We then hope to have isomorphisms: 
  $
    H^q_et (X_(ol(QQ_p)), ZZ\/n) ->^tilde_(#[(b)]) H^q_et (X_(ZZ_p^#[ur]), ZZ\/n) <-^tilde_(#[(c)]) H^q_et (X_(ol(FF_p)), ZZ\/n)
  $
  so that LHS has a $Gal_(QQ_p)$-action, and RHS has a $Gal_(FF_p)$-action. 

  The fact that the morphisms (a), (b), and (c) are isomorphisms is a consequence of various base change theorems, namely the proper base change and smooth base change theorems. 
  
  More specifically, (a) needs smooth base change, (c) needs proper base change, and (b) needs both. 
  
  Consequently,
  
  - Whenever $X_(QQ_p)$ admits a smooth proper model over $ZZ_p$, there is a Galois action of $Gal_QQ$ on $H^q_et (X_(ol(QQ)), ZZ\/n)$, unramified at $p$ in the sense that the inertia subgroup $I_(QQ_p) = ker(Gal_(QQ_p) -> Gal_(FF_p))$ acts trivially. 


The base change theorems are thus the critical and general machinery to study and to apply etale cohomology. 

#date[
  #set align(left) 
  I have deliberately chosen the proof route to avoid the use of the derived category in this chapter, to not obfuscate the concrete arguments behind abstract machineries. 
  
  However, the base change morphism is naturally a derived object, and its naturality is most obviously seen from the derived category. In contrast, insisting on sticking to the abelian category setup in this situation would require a lengthy and uninspiring argument, which would meaninglessly obscure the naturality of the constructions. As such, I will use the derived category in the construction of the base change morphism. 
]

== Setup and proof framework

We will first construct the base change morphism: 

#construction(name: <base-change-constr>)[
  Consider a commutative diagram:
  // https://q.uiver.app/#r=typst&q=WzAsNCxbMCwwLCJYJyJdLFsxLDAsIlknIl0sWzAsMSwiWCJdLFsxLDEsIlkiXSxbMiwzLCJmIl0sWzAsMSwiZiciXSxbMSwzLCJnIl0sWzAsMiwiZyciLDJdXQ==
  #align(center, diagram({
    node((-1, -1), [$X'$])
    node((0, -1), [$Y'$])
    node((-1, 0), [$X$])
    node((0, 0), [$Y$])
    edge((-1, 0), (0, 0), [$f$], label-side: left, "->")
    edge((-1, -1), (0, -1), [$f'$], label-side: left, "->")
    edge((0, -1), (0, 0), [$g$], label-side: left, "->")
    edge((-1, -1), (-1, 0), [$g'$], label-side: right, "->")
  }))
  Note that for $cal(F) in cAb(X_et)$, we have by adjunction a canonical map $cal(F) -> g'_* g'^(-1) cal(F)$. Then we have a canonical map:
  $
    f_* cal(F) -> f_* g'_* g'^(-1) cal(F) = g_* f'_* (g')^(-1) cal(F)
  $
  Applying adjunction, we have a canonical map:
  $
    g^(-1) f_* cal(F) -> f'_* g'^(-1) cal(F)
  $
  functorial in $cal(F)$. Take an injective resolution $cal(F) -> cal(I)^bullet$. Now $R^bullet f_* cal(F) = h^bullet (0 -> f_* cal(I)^bullet)$. The inverse-image functor is exact and commutes with cohomology, so we have a canonical map:
  $
    g^(-1) (R^q f_* cal(F)) cong h^q (0 -> g^(-1) f_* cal(I)^bullet) -> h^q (0 -> f'_* g'^(-1) cal(I)^bullet) -> h^q (0 -> f'_* cal(J)^bullet) = R^q f'_* (g'^(-1) cal(F))
  $
  where $g'^(-1) cal(F) -> cal(J)^bullet$ is an injective resolution, so we have a morphism of cochain complexes $g'^(-1) cal(I)^bullet -> cal(J)^bullet$ that induces canonical maps on cohomology. In summary, for every commutative square, there exists a canonical morphism:
  $
    g^(-1) R^q f_* cal(F) -> R^q f'_* g'^(-1) cal(F)
  $
  functorial in $cal(F)$. This is called the *base change morphism*. 

  The definition above seems very non-canonical and unnatural. Indeed, the base change morphism is more naturally an object in the derived category. Given $cal(K) in D(X_et)$, the base change morphism: 
  $
    g^(-1) R f_* cal(K) -> R f'_* g'^(-1) cal(K)
  $
  is defined as follows: 

  - By adjunction, a morphism $g^(-1) R f_* cal(K) -> R f'_* g'^(-1) cal(K)$ is equivalent to a morphism: #h(1fr)
    $
      R f_* cal(K) -> R g_* R f'_* g'^(-1) cal(K) = R (g compose f')_* g'^(-1) cal(K) = R (f compose g')_* g'^(-1) cal(K) = R f_* R g'_* g'^(-1) cal(K)
    $
    and we lift the adjunction unit $cal(K) -> R g'_* g'^(-1) cal(K)$ through $R f_*$ to obtain this map. 

  In other words, the base change morphism is just the Beck-Chevalley base change defined in @bcbc-defn, corresponding to the diagram: 
  // https://q.uiver.app/#r=typst&q=WzAsNCxbMCwwLCJEKFgnX2V0KSJdLFswLDEsIkQoWF9ldCkiXSxbMSwxLCJEKFlfZXQpIl0sWzEsMCwiRChZJ19ldCkiXSxbMCwzLCJSIGYnXyoiXSxbMSwyLCJSIGZfKiIsMl0sWzMsMiwiUiBnXyoiXSxbMCwxLCJSIGcnXyoiLDJdLFsxLDNdXQ==
  #align(center, diagram({
    node((-1, -1), [$D(X'_et)$])
    node((-1, 0), [$D(X_et)$])
    node((0, 0), [$D(Y_et)$])
    node((0, -1), [$D(Y'_et)$])
    edge((-1, -1), (0, -1), [$R f'_*$], label-side: left, "->")
    edge((-1, 0), (0, 0), [$R f_*$], label-side: right, "->")
    edge((0, -1), (0, 0), [$R g_*$], label-side: left, "->")
    edge((-1, -1), (-1, 0), [$R g'_*$], label-side: right, "->")
    edge((-0.7, -0.3), (-0.3, -0.7), "=>")
  }))
  in which the diagonal natural transformation is just the isomorphism $R f_* compose R g'_* = R (f compose g')_* = R (g compose f')_* = R g_* compose R f'_*$. 
]

The base change morphism is natural, in the sense that it is compatible with concatenation of commutative squares. 

#lemma(name: <base-change-naturality>)[
  The base change morphism is compatible with concatenation of commutative squares. Given a commutative diagram: 
  // https://q.uiver.app/#r=typst&q=WzAsOCxbMSwyLCJYIl0sWzIsMiwiWSJdLFsyLDEsIlknIl0sWzEsMSwiWCciXSxbMSwwLCJYJyciXSxbMiwwLCJZJyciXSxbMCwxLCJXJyJdLFswLDIsIlciXSxbMCwxLCJmIiwyXSxbMywyLCJmJyJdLFs0LDUsImYnJyJdLFs3LDAsImgiLDJdLFs2LDMsImgnIl0sWzIsMSwiZyJdLFszLDAsImcnIl0sWzYsNywiZycnIiwyXSxbNSwyLCJrIl0sWzQsMywiayciXV0=
  #align(center, diagram({
    node((0, 1), [$X$])
    node((1, 1), [$Y$])
    node((1, 0), [$Y'$])
    node((0, 0), [$X'$])
    node((0, -1), [$X''$])
    node((1, -1), [$Y''$])
    node((-1, 0), [$W'$])
    node((-1, 1), [$W$])
    // node((-0.7, 0.3), $cart$)
    // node((0.3, -0.7), $cart$)
    // node((0.3, 0.3), $cart$)
    edge((0, 1), (1, 1), [$f$], label-side: right, "->")
    edge((0, 0), (1, 0), [$f'$], label-side: left, "->")
    edge((0, -1), (1, -1), [$f''$], label-side: left, "->")
    edge((-1, 1), (0, 1), [$h$], label-side: right, "->")
    edge((-1, 0), (0, 0), [$h'$], label-side: left, "->")
    edge((1, 0), (1, 1), [$g$], label-side: left, "->")
    edge((0, 0), (0, 1), [$g'$], label-side: left, "->")
    edge((-1, 0), (-1, 1), [$g''$], label-side: right, "->")
    edge((1, -1), (1, 0), [$k$], label-side: left, "->")
    edge((0, -1), (0, 0), [$k'$], label-side: left, "->")
  }))
  + The base change morphism is compatible with vertical concatenation of commutative squares, i.e. in the derived category, the composition: 
    $
      (k compose g)^(-1) R f_* cal(K) = k^(-1) g^(-1) R f_* cal(K) -> k^(-1) R f'_* g'^(-1) cal(K) -> R f''_* k'^(-1) g'^(-1) cal(K) = R f''_* (k' compose g')^(-1) cal(K) 
    $
    of base change morphisms along the two small squares is simply the base change morphism along the right rectangle. 
    Taking cohomologies, the composition: 
    $
      (k compose g)^(-1) R^q f_* cal(F) = k^(-1) g^(-1) R^q f_* cal(F) -> k^(-1) R^q f'_* g'^(-1) cal(F) -> R^q f''_* k'^(-1) g'^(-1) cal(F) = R^q f''_* (k' compose g')^(-1) cal(F) 
    $
    of base change morphisms along the two small squares is simply the base change morphism along the right rectangle. 

  + The base change morphism is compatible with horizontal concatenation of commutative squares, i.e. in the derived category, the composition: 
    $
      g^(-1) R(f compose h)_* cal(K) = g^(-1) R f_* R h_* cal(K) -> R f'_* g'^(-1) R h_* cal(K) -> R f'_* R h'_* g''^(-1) cal(K) = R(f' compose h')_* g''^(-1) cal(K) 
    $
    of base change morphisms along the two small squares is simply the base change morphism along the bottom rectangle. 

    Taking homologies, there is a morphism of Leray spectral sequences $E_2^(p,q) -> tilde(E)_2^(p,q)$, in which: 
    $
      E_2^(p,q) = g^(-1) R^p f_* R^q h_* cal(F) => g^(-1) R^(p+q) (f compose h)_* cal(F) = H^(p+q) \

      tilde(E)_2^(p,q) = R^p f'_* R^q h'_* g''^(-1) cal(F) => R^(p+q) (f' compose h')_* g''^(-1) cal(F) = tilde(H)^(p+q)
    $
    where the morphisms $E_2^(p,q) -> tilde(E)_2^(p,q)$ are the compositions of the two base change maps along the two bottom squares, and the morphisms $H^n -> tilde(H)^n$ are the base change maps along the bottom rectangle. 
]
#proof[
  We only prove the derived statements, since the abelian category statement of (1) follows from the derived one by taking cohomologies, and that of (2) follows from the derived one by taking the spectral sequence associated to the totalizer (or, of course, the hypercohomology spectral sequence). 

  Now, the base change map in the derived category is just a Beck-Chevalley base change, a purely category-theoretic construction. Thus, (1) and (2) follow from @bcbc-vertical-concat and @bcbc-horizontal-concat, respectively. 
  /*#lemma[
    Given a commutative square of functors between categories: 
    // https://q.uiver.app/#r=typst&q=WzAsNCxbMCwwLCJjYWwoQylfMSJdLFsxLDAsImNhbChDKV8yIl0sWzAsMSwiY2FsKEQpXzEiXSxbMSwxLCJjYWwoRClfMiJdLFswLDEsImYnIl0sWzIsMywiZiIsMl0sWzEsMywiZyJdLFswLDIsImcnIiwyXV0=
    #align(center, diagram({
      node((-1, -1), [$cal(C)_1$])
      node((0, -1), [$cal(C)_2$])
      node((-1, 0), [$cal(D)_1$])
      node((0, 0), [$cal(D)_2$])
      edge((-1, -1), (0, -1), [$f'$], label-side: left, "->")
      edge((-1, 0), (0, 0), [$f$], label-side: right, "->")
      edge((0, -1), (0, 0), [$g$], label-side: left, "->")
      edge((-1, -1), (-1, 0), [$g'$], label-side: right, "->")
    }))
    s.t. $g, g'$ have left adjoints $g^L, g^L '$ respectively, we define the base change map along this square to be the natural transformation: 
    $
      g^L f -> g^L f g' g'^L ->^tilde g^L g f' g'^L -> f' g'^L
    $
    where the first map is an adjunction unit, and the third is a counit. 

    Then given a commutative diagram: 
    // https://q.uiver.app/#r=typst&q=WzAsOCxbMSwyLCJjYWwoRClfMiJdLFswLDEsImNhbChDKV8xIl0sWzEsMSwiY2FsKEMpXzIiXSxbMiwxLCJjYWwoQylfMyJdLFswLDIsImNhbChEKV8xIl0sWzIsMiwiY2FsKEQpXzMiXSxbMiwwLCJjYWwoRSlfMyJdLFsxLDAsImNhbChFKV8yIl0sWzAsNSwiZiIsMl0sWzQsMCwiaCIsMl0sWzIsMywiZiciXSxbMSwyLCJoJyJdLFszLDUsImdfMyJdLFsyLDAsImdfMiJdLFsxLDQsImdfMSIsMl0sWzcsNiwiZicnIl0sWzYsMywiaF8zIl0sWzcsMiwiaF8yIl1d
    #align(center, diagram({
      node((0, 0), [$cal(D)_2$])
      node((-1, -1), [$cal(C)_1$])
      node((0, -1), [$cal(C)_2$])
      node((1, -1), [$cal(C)_3$])
      node((-1, 0), [$cal(D)_1$])
      node((1, 0), [$cal(D)_3$])
      node((1, -2), [$cal(E)_3$])
      node((0, -2), [$cal(E)_2$])
      edge((0, 0), (1, 0), [$f$], label-side: right, "->")
      edge((-1, 0), (0, 0), [$h$], label-side: right, "->")
      edge((0, -1), (1, -1), [$f'$], label-side: left, "->")
      edge((-1, -1), (0, -1), [$h'$], label-side: left, "->")
      edge((1, -1), (1, 0), [$g_3$], label-side: left, "->")
      edge((0, -1), (0, 0), [$g_2$], label-side: left, "->")
      edge((-1, -1), (-1, 0), [$g_1$], label-side: right, "->")
      edge((0, -2), (1, -2), [$f''$], label-side: left, "->")
      edge((1, -2), (1, -1), [$h_3$], label-side: left, "->")
      edge((0, -2), (0, -1), [$h_2$], label-side: left, "->")
    }))
    in which $g_i, h_i$ have left adjoints $g_i^L, h_i^L$: 

    + The composition of natural transformations: #h(1fr)
      $
        g_3^L f h -> f' g_2^L h -> f'h'g_1^L
      $
      of successive base changes along the two bottom squares is just base change along the bottom rectangle. 

    + The composition of natural transformations: 
      $
        h_3^L g_3^L f -> h_3^L f' g_2^L -> f'' h_2^L g_2^L
      $
      of successive base changes along the two right squares is just base change along the right ==rectangle. 
  ]*/
]

This is the general setup for base change theorems. The proper base change theorem states that: 

#theorem(name: <proper-base-change>)[
  Given a Cartesian diagram: 
  #align(center, diagram({
    node((-1, -1), [$X'$])
    node((0, -1), [$Y'$])
    node((-1, 0), [$X$])
    node((0, 0), [$Y$])
    node((-0.7, -0.7), $cart$)
    edge((-1, 0), (0, 0), [$f$], label-side: left, "->")
    edge((-1, -1), (0, -1), [$f'$], label-side: left, "->")
    edge((0, -1), (0, 0), [$g$], label-side: left, "->")
    edge((-1, -1), (-1, 0), [$g'$], label-side: right, "->")
  }))
  
  The base change morphism: #h(1fr)
  $
    g^(-1) R^q f_* cal(F) -> R^q f'_* g'^(-1) cal(F)
  $
  is an isomorphism whenever $cal(F) in cAb(X_et)$ is a torsion sheaf, $f$ is proper, and $X$, $Y$ are locally noetherian. 
]
The locally noetherian hypothesis here is not necessary, and is merely a technical artifact of our methods which can be removed upon some mild strengthening of the results used in the proof. However, the proof in the locally noetherian case captures the spirit of the proof, so we'll stick with it. 

#construction[
  We will consider the case of proper base change, where $Y = Spec(A), Y' = ol(y) = Spec(k)$, where $(A, frak(m), k)$ is a strict henselian local ring. In this case, $X -> Spec(A)$ is proper, and $X' = X_0$ is its special fiber. Then the base change morphism is a morphism in $cAb(Spec(k)_et)$, where $k$ is separably closed, so it is really a morphism on stalks. 
  
  In other words, the base change morphism in this case is: 
  $
    (g^(-1) R^q f_* cal(F))_(ol(y)) = (R^q f_* cal(F))_(ol(y)) = H^q (X times_A tilde(Spec(A))_(ol(y)), cal(F)|_(X times_A tilde(Spec(A))_(ol(y)))) = H^q (X, cal(F))
  $
  since $A$ is already strict henselian, so $tilde(Spec(A))_(ol(y)) = Spec(A)$. On the other hand, 
  $
    (R^q f'_* g'^(-1) cal(F))_(ol(y)) = H^q (X_0, cal(F)|_(X_0))
  $
  since we are just computing the global section $R^q f'_* g'^(-1) cal(F) (ol(y))$, which, by @struct-of-spec-omega-et (1) and @derived-lower-star-first-props (3), is just $H^q (X_0, cal(F)|_(X_0))$. The base change morphism in this case is just restriction: 
  $
    H^q (X, cal(F)) -> H^q (X_0, cal(F)|_(X_0))
  $
]

#notation[
  We abbreviate various base change related propositions as follows: 

  - $BC^q (X ->^f Y, Y' ->^g Y, cal(F))$ denotes the proposition: #h(1fr)
    $
      #[The base change morphism $g^(-1)R^q f_* cal(F) -> R^q f'_* g'^(-1) cal(F)$ is an isomorphism.]
    $

  - For a strict henselian local ring $A$, $BC^q_* (X ->^f Spec(A), cal(F))$ denotes the proposition: 
    $
      #[The restriction $H^q (X, cal(F)) -> H^q (X_0, cal(F)|_(X_0))$ is an isomorphism.]
    $
    We also use $BC^q_(*,#[inj]) (f, cal(F)), BC^q_(*,#[surj])$ to denote that this restriction is injective/surjective, respectively. 

  - $BC (X ->^f Y, Y' ->^g Y)$ denotes the proposition:
    $
      forall q>=0, forall cal(F) in cAb(X_et) #[torsion], BC^q (f, g, cal(F))
    $
    i.e. the base change theorem holds for the Cartesian square defined by $f$ and $g$ and all torsion sheaves. Similarly, $BC_* (X ->^f Spec(A))$ denotes the proposition: 
    $
      forall q>=0, forall cal(F) in cAb(X_et) #[torsion], BC^q_* (f, cal(F))
    $

  The proper base change theorem is thus the statement: 
  $
    #[$BC (X ->^f Y, Y' ->^g Y)$ holds for all $f$ proper and $Y', Y$ locally noetherian.]
  $
]

There are a few big steps in the proofs of proper base change, each requiring drastically different techniques and rather lengthy proofs. As such, we summarize the main results of each step as propositions here. 

#notation[
  #set enum(numbering: n => ("(Seed)", "(Dev)", "(Comp)", "(Shift)", "(Reduce)", "(Finite)").at(n - 1))

  We define the following propositions: 

  + /*For any noetherian strict henselian $A$, any $f: X -->^#[finite] PP^1_A -> Spec(A)$, #h(1fr)

    - $BC^0_* (X ->^f Spec(A), ul(ZZ\/n))$ holds, and for all $q >= 1$, $BC^q_(*,#[surj]) (X ->^f Spec(A), ul(ZZ\/n))$ holds. */
    For any noetherian strict henselian $A$, #h(1fr)
    $
      forall & f: X -->^#[finite] PP^1_A -> Spec(A), forall n>=1, \
      &BC^0_* (f, ul(ZZ\/n)) and (forall q>=1, BC^q_(*,#[surj]) (f, ul(ZZ\/n)))
    $

  + /*For any noetherian strict henselian $A$, any $f: X -> Spec(A)$, if: 

    - $BC^0_* (tilde(X) ->^g Spec(A), ul(ZZ\/n))$ holds, and for all $q >= 1$, $BC^q_(*,#[surj]) (tilde(X) ->^g Spec(A), ul(ZZ\/n))$ holds for all $g: tilde(X) ->^#[finite] X ->^f A$. 

    Then: 

    - $BC^q_* (tilde(X) ->^g Spec(A), cal(F))$ holds for all $g: tilde(X) ->^#[finite] X ->^f A$, all $q >= 0$ and all torsion $cal(F) in cAb(tilde(X)_et)$. */
    $
      (&forall tilde(X) -> X #[finite], forall n >= 1, \
      & BC^0_* (tilde(X) -> X -> Spec(A), ul(ZZ\/n)) and (forall q>=1, BC^q_(*,#[surj]) (tilde(X) -> X -> Spec(A), ul(ZZ\/n)))) \
      // ==>&(&&forall tilde(X) -> X #[finite], forall cal(F) in cAb(tilde(X)_et) #[torsion], forall q>=0, \
      // &&& BC^q_(*,#[surj])(tilde(X) -> X -> Spec(A), cal(F))))
      ==>& (forall tilde(X) -> X #[finite], BC_* (tilde(X) -> Spec(A)))
    $

  + #set enum(numbering: "(1)")
    + In a diagram of successive base changes:
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
      We have:
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
      We have: 
      $
        BC(f, g) and BC(f', h) ==> BC(f, g compose h)
      $
      i.e. if the base change theorem holds for the upper and lower small squares, then it holds for the large rectangle. 

  + In a diagram of successive base changes in which all schemes are noetherian with $X', X$ proper over $Spec(A)$ and $X' ->> X$ surjective: 
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
      ==>& (BC_* (X -> Spec(A)) <==> BC_* (X' -> Spec(A)))
    $

  + When $Y', Y$ are locally noetherian, 
    $
      & BC(X ->^f Y, Y' ->^g Y) \
      <==& (BC_* (X times_Y Spec(A) -> Spec(A)), forall Spec(A) -> Y, forall A #[noetherian strict henselian])
    $

  + $BC(X ->^f Y, Y' ->^g Y)$ holds whenever $f$ is finite. 
]

We first state the last part of the proof, to demonstrate how the six points stated above are relevant reduction steps, and how they are sufficient to prove proper base change. 

#theorem[
  The proper base change theorem holds as long as the six points (Seed)(Dev)(Comp)(Shift)(Reduce)(Finite) stated above hold. 
]
#proof[
  By (Seed) and (Dev), $BC_* (PP^1_A -> Spec(A))$ holds for any noetherian strict henselian $A$. 

  Our first step is showing that $BC(PP^n_Y -> Y, Y' ->^g Y)$ holds for all $n >= 1$ and locally noetherian $Y$. That is, proper base change holds for projective spaces. By (Reduce), it suffices to prove $BC_* (PP^n_A -> Spec(A))$ for all noetherian strict henselian $A$. Now there is a finite surjection:
  $
    underbrace(PP^1_A times_A dots.c times_A PP^1_A, #[$n$ copies]) -> PP^n_A, ((X_1:Y_1), dots.c, (X_n:Y_n)) |-> (F_0:F_1:dots.c:F_n)
  $
  where the $F_i$'s are characterized by $product_(i=1)^n (X_i T + Y_i) = sum_(i=0)^n F_i (arrow(X), arrow(Y)) T^i$. 

  Base change along this finite surjective morphism holds by (Finite). Suppose that base change holds for $PP^1_A times_A dots.c times_A PP^1_A -> Spec(A)$ too. Then by (Shift), we see that base change holds for $PP^n_A -> Spec(A)$. 
  
  Thus, it suffices to show that for all noetherian strict henselian $A$, base change holds along $PP^1_A times_A dots.c times_A PP^1_A -> Spec(A)$. This morphism factors as: 
  $
    underbrace(PP^1_A times_A dots.c times_A PP^1_A, #[$n$ copies]) -> underbrace(PP^1_A times_A dots.c times_A PP^1_A, #[$n-1$ copies]) -> dots.c -> PP^1_A -> Spec(A)
  $
  in which every step is of the shape $PP^1_(tilde(Y)) -> tilde(Y)$ for some noetherian $tilde(Y)$. By (Comp), we are allowed to assume $n = 1$ and we want to show that base change holds along $PP^1_Y -> Y$, i.e. $BC(PP^1_Y -> Y, Y' ->^g Y)$. However, by (Reduce), it suffices to show that $BC_* (PP^1_A -> Spec(A))$ holds for all noetherian strict henselian $A$, which is what we already have.

  Next, for any projective#footnote[Our notion of a morphism $f: X -> Y$ being *projective* means that $f$ factors as $X -> PP^n_Y -> Y$ where $X -> PP^n_Y$ is a closed immersion. This notion agrees with the notion in @cite-hartshorne-ag, and is referred to as *H-projective* in Stacks Project.] $f: X ->^i PP^n_Y -> Y$, where $i$ is a closed immersion, to show that base change holds for $f$, it suffices to show that for all noetherian strictly henselian $A$, any closed immersion $i: X -> PP^n_A$, $BC_* (X ->^i PP^n_A -> Spec(A))$ holds. Now $BC_* (i)$ holds from (Finite), and we just proved that $BC_* (PP^n_A -> Spec(A))$ holds, and all schemes involved are noetherian, so by (Comp) $BC_* (X -> Spec(A))$ holds. Therefore, $BC(X ->^f Y, Y' ->^g Y)$ holds whenever $f$ is projective and $Y, Y'$ are locally noetherian.

  We now deal with the general case $BC(X ->^f Y, Y' ->^g Y)$ for $f$ proper. By (Reduce), it suffices to prove $BC_* (X -> Spec(A))$ for all $X -> Spec(A)$ proper and all noetherian $A$. For this, we invoke Chow's lemma. 

  #lemma[
    (Chow's lemma) Let $S$ be a noetherian scheme, and $f: X -> S$ be separated of finite type. Then there exists a commutative diagram: 
    // https://q.uiver.app/#r=typst&q=WzAsNCxbMCwwLCJYIl0sWzEsMCwiWCciXSxbMiwwLCJQUF5uX1MiXSxbMSwxLCJTIl0sWzIsM10sWzEsMl0sWzEsMCwicGkiLDJdLFswLDMsImYiLDJdLFsxLDNdXQ==
    #align(center, diagram({
      node((-1, -1), [$X$])
      node((0, -1), [$X'$])
      node((1, -1), [$PP^n_S$])
      node((0, 0), [$S$])
      edge((1, -1), (0, 0), "->")
      edge((0, -1), (1, -1), "->")
      edge((0, -1), (-1, -1), [$pi$], label-side: right, "->")
      edge((-1, -1), (0, 0), [$f$], label-side: right, "->")
      edge((0, -1), (0, 0), "->")
    }))
    in which: 

    + $pi$ is projective and surjective; 

    + $X' -> PP^n_S$ is an immersion; 

    + There exists an open dense $U subset X$ s.t. $pi: pi^(-1) (U) -> U$ is an isomorphism. 

    In particular, when $f$ is proper, $X' -> PP^n_S$ is also proper, and hence a closed immersion. In other words, $X' -> S$ is projective. 
  ]
  #proof[
    We refer to #cite-stacks("0200")[Lemma 30.18.1] and #cite-stacks("0201")[Remark 30.18.2]. 
  ]
  Now $X -> Spec(A)$ factors as: 
  // https://q.uiver.app/#r=typst&q=WzAsMyxbMCwwLCJYIl0sWzIsMCwiU3BlYyhBKSJdLFsxLDEsIlgnIl0sWzIsMCwicGkiXSxbMiwxXSxbMCwxXV0=
  #align(center, diagram({
    node((-1, -1), [$X$])
    node((1, -1), [$Spec(A)$])
    node((0, 0), [$X'$])
    edge((0, 0), (-1, -1), [$pi$], label-side: left, "->")
    edge((0, 0), (1, -1), "->")
    edge((-1, -1), (1, -1), "->")
  }))
  with $pi: X' -> X$ surjective and projective, and $X' -> Spec(A)$ projective. Since $X$ and $Spec(A)$ are noetherian, by our previous results on projective morphisms, 
  $
    BC (X' ->^pi X, X_0 ->^i X) #[and] BC_* (X' -> Spec(A))
  $
  holds. Since $X, X', Spec(A)$ are all noetherian, by (Shift), $BC_* (X -> Spec(A))$ holds. We are thereby done. 
]

Thus, to prove the proper base change theorem, we need to take down the six points (Seed)(Dev)(Comp)(Shift)(Reduce)(Finite) one by one. 

Among these six points, (Finite) is the easiest to prove, and will be used during the proof of other points. We prove it right now. 

#proposition(name: <pbc-finite>)[
  (Finite) The base change morphism: 
  $
    g^(-1) R^q f_* cal(F) -> R^q f'_* g'^(-1) cal(F)
  $
  is an isomorphism whenever $f$ is finite. 

  (Note that this doesn't even require $cal(F)$ to be a torsion sheaf, contrary to the statement of proper base change.)
]
#proof[
  Since $f_*$ is exact when $f$ is finite, both sides vanish when $q >= 1$. It suffices to prove that the base change morphism: 
  $
    g^(-1) f_* cal(F) -> f'_* g'^(-1) cal(F)
  $
  is an isomorphism for $f$ finite. For any algebraically closed geometric point $ol(y') in Y'$, compute the stalks on both sides using @stalks-of-finite-pushforward: 
  $
    (g^(-1) f_* cal(F))_(ol(y')) = (f_* cal(F))_(g(ol(y'))) = oplus.big_(ol(x) in f^(-1)(g(ol(y')))) cal(F)_(ol(x))
  $
  while: 
  $
    (f'_* g'^(-1) cal(F))_(ol(y')) = oplus.big_(ol(x') in f'^(-1)(ol(y'))) (g'^(-1)cal(F))_(ol(x')) = oplus.big_(ol(x') in f'^(-1)(ol(y'))) cal(F)_(g'(ol(x')))
  $
  Thus, it suffices to show that: 
  $
    g': f'^(-1)(ol(y')) -> f^(-1)(g(ol(y')))
  $
  is a bijection. Indeed, if $ol(y) = g(ol(y'))$, the induced map $g': f'^(-1)(ol(y')) -> f^(-1)(ol(y))$ is a bijection by the definition of the fiber product. 
]
