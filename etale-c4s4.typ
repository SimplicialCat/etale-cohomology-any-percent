#import "void-import.typ": *
== Functoriality <sect-functoriality-of-etale-topos>

In this section, we will establish: 

- The direct and inverse image functors $f_*: cSh(X_et) arrows.rl cSh(Y_et): f^(-1)$ for any scheme morphism $f: X -> Y$; 

#construction[
  Let $f: X -> Y$ be a morphism of schemes. We then have a functor:
  $
    f^(-1): Et_Y -> Et_X, (V -> Y) |-> f^(-1) (V) = (X times_Y V -> X)
  $
  
  It has the properties: 

  - $f^(-1) (Y) = X$;

  - $f^(-1) (V_1 times_V V_2) = f^(-1) (V_1) times_(f^(-1) (V)) f^(-1) (V_2)$. 
  
  Therefore, $cal(V) = {V_i -> V}$ is a cover in $Y_et$ implies that ${f^(-1) (V_i) -> f^(-1) (V)}$ is a covering in $X_et$. 
]

#definition(name: <defn-etale-direct-image>)[
  Define the *direct image* functor: 
  $
    f_* = f_(et,*): cPSh(X_et) -> cPSh(Y_et), cal(F) |-> (V |-> cal(F)(f^(-1) (V)) = cal(F)(X times_Y V))
  $
]
#lemma[
  $f_*$ is a functor $cSh(X_et) -> cSh(Y_et), cPAb(X_et) -> cPAb(Y_et), cAb(X_et) -> cAb(Y_et)$. 
]
#proof[
  Indeed, it suffices to show that if $cal(F)$ is a sheaf, so is $f_* cal(F)$. Indeed, the sheaf condition for $f_* cal(F)$ requires that: 
  $
    f_* cal(F) (V) -> product_i f_* cal(F)(V_i) -> product_(i,j) f_* cal(F) (V_i times_V V_j)
  $
  is an equalizer for every cover $cal(V) = {V_i -> V}$ in $Et_Y$. However, using the properties of $f^(-1)$ given above, this translates to the sheaf conditions for $cal(F)$ for the cover $f^(-1) (cal(V)) = {f^(-1) (V_i) -> f^(-1) (V)}$ in $Et_X$, which holds since $cal(F)$ is a sheaf. 
]

#definition[
  Define the *presheaf inverse image* functor: 
  $
    f_(cPSh)^(-1): cPSh(Y_et) -> cPSh(X_et), cPAb(Y_et) -> cPAb(X_et), cal(G) |-> (U |-> dircolim_((V,phi)) cal(G)(V))
  $
  where the filtered colimit is taken over all commutative diagrams of the shape: 
  // https://q.uiver.app/#r=typst&q=WzAsNCxbMCwwLCJVIl0sWzEsMCwiViJdLFswLDEsIlgiXSxbMSwxLCJZIl0sWzIsMywiZiIsMl0sWzAsMSwicGhpIl0sWzEsM10sWzAsMl1d
  #align(center, diagram({
    node((-1, -1), [$U$])
    node((0, -1), [$V$])
    node((-1, 0), [$X$])
    node((0, 0), [$Y$])
    edge((-1, 0), (0, 0), [$f$], label-side: right, "->")
    edge((-1, -1), (0, -1), [$phi$], label-side: left, "->")
    edge((0, -1), (0, 0), "->")
    edge((-1, -1), (-1, 0), "->")
  }, spacing: 1.5em))
  where $(V -> Y) in Et_Y$. This is indeed a filtered system, as explained in the following two diagrams: 
  // https://q.uiver.app/#r=typst&q=WzAsNixbMCwxLCJWXzEiXSxbMiwxLCJWXzIiXSxbMSwwLCJVIl0sWzEsMiwiWSJdLFsxLDEsIlZfMSB0aW1lc19ZIFZfMiJdLFs0LDEsIlgiXSxbMCwzXSxbMSwzXSxbMiwwLCJwaGlfMSIsMl0sWzIsMSwicGhpXzIiXSxbNCwwXSxbNCwxXSxbMiw0XSxbNCwzXSxbMiw1XSxbNSwzLCJmIl1d
  #align(center, diagram({
    node((-1, -1), [$V_1$])
    node((1, -1), [$V_2$])
    node((0, -2), [$U$])
    node((0, 0), [$Y$])
    node((0, -1), [$V_1 times_Y V_2$])
    node((3, -1), [$X$])
    edge((-1, -1), (0, 0), "->")
    edge((1, -1), (0, 0), "->")
    edge((0, -2), (-1, -1), [$phi_1$], label-side: right, "->")
    edge((0, -2), (1, -1), [$phi_2$], label-side: left, "->", label-sep: -2pt)
    edge((0, -1), (-1, -1), "->")
    edge((0, -1), (1, -1), "->")
    edge((0, -2), (0, -1), "->")
    edge((0, -1), (0, 0), "->")
    edge((0, -2), (3, -1), "->")
    edge((3, -1), (0, 0), [$f$], label-side: left, "->")
  }))
  // https://q.uiver.app/#r=typst&q=WzAsNixbMCwxLCJVIl0sWzEsMSwiViJdLFsyLDIsIlYnIl0sWzAsMiwiWCJdLFsxLDMsIlkiXSxbMCwwLCJ0aWxkZShWKSJdLFsxLDIsInBoaV8xIiwyLHsib2Zmc2V0IjoxfV0sWzEsMiwicGhpXzIiLDAseyJvZmZzZXQiOi0xfV0sWzAsMV0sWzAsM10sWzMsNCwiZiIsMl0sWzIsNF0sWzUsMSwidGlsZGUocGhpKSJdLFswLDVdXQ==
  #align(center, {diagram({
    node((-1, -1), [$U$])
    node((0, -1), [$V$])
    node((1, 0), [$V'$])
    node((-1, 0), [$X$])
    node((0, 1), [$Y$])
    node((-1, -2), [$tilde(V)$])
    edge((0, -1), (1, 0), [$phi_1$], label-side: right, shift: -0.05, "->")
    edge((0, -1), (1, 0), [$phi_2$], label-side: left, shift: 0.05, "->")
    edge((-1, -1), (0, -1), "->")
    edge((-1, -1), (-1, 0), "->")
    edge((-1, 0), (0, 1), [$f$], label-side: right, "->")
    edge((1, 0), (0, 1), "->")
    edge((-1, -2), (0, -1), [$tilde(phi)$], label-side: left, "->")
    edge((-1, -1), (-1, -2), "->")
  })
  h(15%)
  // https://q.uiver.app/#r=typst&q=WzAsNCxbMCwwLCJ0aWxkZShWKSJdLFsyLDAsIlYiXSxbMCwyLCJWJyJdLFsyLDIsIlYnIHRpbWVzX1kgViciXSxbMCwxLCJ0aWxkZShwaGkpIl0sWzEsMywiKHBoaV8xLHBoaV8yKSJdLFsyLDMsIkRlbHRhIiwyXSxbMCwyXV0=
  diagram({
    node((-1, -1), [$tilde(V)$])
    node((1, -1), [$V$])
    node((-1, 1), [$V'$])
    node((1, 1), [$V' times_Y V'$])
    node((-0.7, -0.7), $cart$, layer: 1, snap: false)
    edge((-1, -1), (1, -1), [$tilde(phi)$], label-side: left, "->")
    edge((1, -1), (1, 1), [$(phi_1,phi_2)$], label-side: left, "->")
    edge((-1, 1), (1, 1), [$Delta$], label-side: right, "->")
    edge((-1, -1), (-1, 1), "->")
  })
  })
]

#lemma[
  $f_(cPSh)^(-1)$ is the left adjoint to $f_*$ on $cPSh(X_et)$ and $cPAb(X_et)$, i.e:
  $
    Hom_cPSh (f_cPSh^(-1) cal(G), cal(F)) = Hom_cPSh (cal(G), f_* cal(F))
  $
  and the same goes for $cPAb$. 
]
#proof[
  We prove for $cPSh$ since the proof for $cPAb$ is the same. We only construct the unit and counit morphisms: 
  $
    alpha_(cal(F)): f^(-1)_cPSh f_* cal(F) -> cal(F), beta_(cal(G)): cal(G) -> f_* f^(-1)_cPSh cal(G)
  $

  $
    alpha_(cal(F)): f^(-1)_cPSh f_* cal(F) (U) = dirlim_((V,phi)) cal(F)(f^(-1) (V)) &-> cal(F)(U) \
    (s in cal(F) (f^(-1)(V))) &|-> s|_U
  $
  where the morphism $U -> f^(-1)(V) = V times_Y X$ is obtained from $U -> X$ and $phi: U -> V$. 

  $
    beta_(cal(G)): cal(G)(W) &-> f_* f^(-1)_cPSh cal(G) (W) = dirlim_((V,phi:f^(-1)(W)->V)) cal(G)(V) \
    s &|-> s 
  $
  where we send $s$ to $s$ in the pair $(W, f^(-1)(W) = W times_Y X -> W)$. 

  That this pair of unit and counit indeed satisfies all natural properties is routine to check. It is analogous to the adjunction of $f^(-1)$ and $f_*$ on the topological site. 
]

#definition(name: <defn-etale-sheaf-inverse-image>)[
  Define the *sheaf inverse image* functor: 
  $
    f^(-1) = f_et^(-1) := (f_cPSh^(-1))^\#: cSh(Y_et) -> cSh(X_et), cAb(Y_et) -> cAb(X_et), cal(G) |-> (f^(-1)_cPSh cal(G))^\#
  $
  When $f: X -> Y$ is clear from the context, we also use $cal(F)|_X$ to denote $f^(-1) cal(F)$. 
]

#proposition(name: <pullback-first-props>)[
  + $f^(-1)$ is left adjoint to $f_*$ on $cSh(Y_et) -> cSh(X_et)$ and $cAb(Y_et) -> cAb(X_et)$;#footnote[
    This pair $f_et: (f^(-1)_et, f_(et,*)): cSh(X_et) arrows.rl cSh(Y_et)$ is called a morphism of etale topoi. You don't need to know what that means. 
  ]
  
  + $f^(-1)_cPSh$ and $f^(-1)$ commute with finite limits, and hence $f^(-1): cAb(Y_et) -> cAb(X_et)$ is exact. 

  + For all $cal(F) in cPSh(Y_et)$ or $cPAb(Y_et)$, there is a canonical isomorphism: $f^(-1) cal(F)^\# -> (f^(-1)_cPSh cal(F))^\#$ in $cSh(X_et)$ or $cAb(X_et)$. 
]
#proof[
  (1) Indeed: 
  $
    Hom_(cSh(X_et)) (f^(-1) cal(F), cal(G)) &= Hom_(cSh(X_et)) ((f^(-1)_cPSh cal(F))^\#, cal(G)) \
    &= Hom_(cPSh(X_et)) (f^(-1)_cPSh cal(F), cal(G)) \
    &= Hom_(cPSh(Y_et)) (cal(F), f_* cal(G)) \
    &= Hom_(cSh(Y_et)) (cal(F), f_* cal(G))
  $

  (2) $f^(-1)$ is $f^(-1)_cPSh$ followed by $(-)^\#$, where $(-)^\#$ is known to preserve finite limits. Thus, it suffices to show that $f^(-1)_cPSh$ preserves finite limits. We can check section-wise, but section-wise $f^(-1)_cPSh$ is a filtered colimit, which commutes with finite limits. 

  $f^(-1): cAb(Y_et) -> cAb(X_et)$ is thus left exact since it preserves finite limits, and right exact since it is a left adjoint. It is thus exact. 

  (3) Note that: 
  $
    Hom_cSh (f^(-1) cal(F)^\#, cal(G)) &= Hom_cSh (cal(F)^\#, f_* cal(G)) \
    &= Hom_cPSh (cal(F), f_* cal(G)) \
    &= Hom_cPSh (f^(-1)_cPSh cal(F), cal(G)) \
    &= Hom_cSh ((f_cPSh^(-1) cal(F))^\#, cal(G))
  $
  and we are done by Yoneda's lemma. 
]

#corollary[
  Given a constant sheaf $ul(M)_Y in cAb(Y_et)$, there is a canonical isomorphism $ul(M)_X cong f^(-1) ul(M)_Y$. 
]
#proof[
  By (3) of the previous properties, we see that there is a canonical isomorphism: 
  $
    f^(-1) ul(M)_Y = f^(-1) ul(M)_(Y,0)^\# cong (f^(-1)_cPSh ul(M)_(Y,0))^\#
  $
  However, $f^(-1)_cPSh ul(M)_(Y,0)$ is trivial to describe, since every term in the colimit defining its sections is $M$, and so $f^(-1)_cPSh ul(M)_(Y,0) cong ul(M)_(X,0)$ canonically. 
]

// The same constructions and properties continue to hold for $cPAb, cAb$. 

Since $f_*$ is a left exact functor, we may right derive it. 

#definition(name: <defn-higher-direct-image>)[
  Define the $q$-th *higher direct image* functor $R^q f_*$ to be the $q$-th right derived functor of the left exact functor $f_*: cAb(X_et) -> cAb(Y_et)$. 
]

#properties(name: <derived-lower-star-first-props>)[
  Since $f_*$ has an exact left adjoint $f^(-1)$, $f_*$ sends injectives to injectives. Consequently: 

  + $X overset(->, f) Y overset(->, g) Z$ has: 
    $
      f^(-1) compose g^(-1) cong (g compose f)^(-1), g_* compose f_* = (g compose f)_*
    $
    Passing to the Grothendieck-Leray spectral sequence: 
    $
      E_2^(p,q) = R^p g_* (R^q f_* (cal(F))) => R^(p+q) (g compose f)_* cal(F)
    $

  + (Leray spectral sequence) $Gamma(Y, f_*(-)) = Gamma(f^(-1)(Y), -)$, and passing to the Grothendieck-Leray spectral sequence: 
    $
      E_2^(p,q) = H^p_et (Y, R^q f_* cal(F)) => H^(p+q)_et (X, cal(F))
    $

  + $R^q f_* (cal(F))$ is simply $(V |-> H^q (f^(-1) (V), cal(F)))^\#$. 
]
#proof[
  (1) $g_* compose f_* = (g compose f)_*$ can be verified directly with ease. $f^(-1) compose g^(-1) = (g compose f)^(-1)$ is hard to verify directly, but $f^(-1) compose g^(-1)$ is the left adjoint of $g_* compose f_*$, while $(g compose f)^(-1)$ is the left adjoint of $(g compose f)_*$. 

  That $E_2^(p,q) = R^p g_* (R^q f_* (cal(F))) => R^(p+q) (g compose f)_* cal(F)$ is just the Grothendieck-Leray spectral sequence applied to $g_*$ and $f_*$, where $f_*$ preserves injectives. 

  (2) is self-explanatory. 

  (3) Take an injective resolution $0 -> cal(F) -> cal(I)^bullet$, and so: 
  $
    R^q f_* cal(F) = h^q (0 -> f_* cal(I)^bullet)
  $
  Now the sheaf kernel is just the presheaf kernel, and the sheaf cokernel is the presheaf cokernel sheafified. Thus, 
  $
    R^q f_* cal(F) &= h^q (0 -> f_* cal(I)^bullet) \
    &= h^q (0 -> iota(f_* cal(I)^bullet))^\# 
  $
  Meanwhile, $h^q (0 -> iota(f_* cal(I)^bullet))$ can be computed section-wise: Its sections on $V$ are just $h^q (0 -> iota(f_* cal(I)^bullet) (V)) = h^q (0 -> cal(I)^bullet (f^(-1)(V))) = H^q (f^(-1)(V), cal(F))$. Hence, 
  $
    R^q f_* cal(F) = (V |-> H^q (f^(-1) (V), cal(F)))^\#
  $
]

Finally, we prove a simple description of $f^(-1)$ when $f$ is etale: 
#lemma(name: <pullback-along-etale-morphism>)[
  If $f: X -> Y$ is etale, then $f^(-1) = f^(-1)_cPSh|_cSh(Y_et)$, and has the following simple description: 
  $
    f^(-1)_cPSh: cPSh(Y_et) &-> cPSh(X_et) \
    cal(G) &|-> ((psi: U -> X) |-> cal(G)(f compose psi))
  $
  The same goes for $cPAb(Y_et)$ and $cAb(Y_et)$. 
]
#proof[
  The simple description for $f^(-1)_cPSh$ follows from the definition directly, since $f compose psi$ is terminal in the indexing category of the colimit for $f^(-1)_cPSh cal(G) (psi)$. The colimit thus collapses into simply $cal(G)(f compose psi)$. 

  It is routine to check that in this case, $f^(-1)_cPSh$ already sends sheaves to sheaves, making $f^(-1)$ a restriction of $f^(-1)_cPSh$ to $cSh(Y_et)$. 
  // The derived statement follows from taking an injective resolution and computing, but we need to show that $f^(-1) cal(I)$ is acyclic on $X$ for any injective $cal(I) in f^(-1) $
]
