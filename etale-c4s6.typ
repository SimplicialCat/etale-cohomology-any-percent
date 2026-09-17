#import "void-import.typ": *

== Cech cohomology

#construction(name: <constr-cech-cohom>)[
  Let $X$ be a scheme. Given $U in Et_X$ and an etale cover $cal(U) = {U_i -> U}_(i in I)$. Denote $U_(i_0,dots.c,i_p) = U_(i_0) times_U dots.c times_U U_(i_p)$. 
  
  Given $cal(G) in cPAb(X_et)$, define the *Cech complex* of $cal(G)$ w.r.t. $cal(U)$ to be the cochain complex: 
  $
    0 -> C^0 (cal(U), cal(G)) -> dots.c -> C^p (cal(U), cal(G)) ->^d C^(p+1) (cal(U), cal(G)) -> dots.c
  $
  formed with groups: 
  $
    C^p (cal(U), cal(G)) = product_(i_0,dots.c,i_p in I) cal(G) (U_(i_0,dots.c,i_p))
  $
  and the usual differentials: 
  $
    d: C^p (cal(U), cal(G)) &-> C^(p+1) (cal(U), cal(G)) \
    (s_(i_0, dots.c, i_p))_(i_0,dots.c,i_p) &|-> (sum_(k=0)^(p+1) (-1)^k s_(i_0,dots.c,cancel(i_k),dots.c,i_(p+1))|_(U_(i_0,dots.c,i_(p+1))))_(i_0,dots.c,i_(p+1))
  $
  The $p$-th *Cech cohomology* of $cal(G)$ w.r.t. $cal(U)$ is thus defined as: 
  $
    caron(H)^p (cal(U), cal(G)) = h^p (0 -> C^bullet (cal(U), cal(G)))
  $
  As usual, given a refinement from $cal(U)$ to $cal(V)$, there exists a chain map: 
  $
    C^p (cal(U), cal(G)) &-> C^p (cal(V), cal(G)) \
    (s_(i_0,dots.c,i_p))_(i_0,dots.c,i_p) &|-> (s_(lambda(j_0),dots.c,lambda(j_p))|_(V_(j_0,dots.c,j_p)))_(j_0,dots.c,j_p)
  $
  inducing a map $caron(H)^p (cal(U), cal(G)) -> caron(H)^p (cal(V), cal(G))$. 
  #lemma[
    Given two different refinements from $cal(U)$ to $cal(V)$, they induce chain homotopic maps $C^bullet (cal(U), cal(G)) -> C^bullet (cal(V), cal(G))$, hence identical maps: 
    $
      caron(H)^p (cal(U), cal(G)) -> caron(H)^p (cal(V), cal(G))
    $
  ]
  #proof[
    // Since a cover $cal(U) = {U_i -> U}_i$ is equivalent to the cover ${U' = union.sq.big_i U_i -> U}$ by a single map, we may assume that $cal(U) = {U' ->> U}, cal(V) = {V' ->> U}$ and $V' -> U$ factors as $V' arrows.rr^(g_1)_(g_2) U' -> U$. To clarify, we use $V'_1$ and $V'_2$ to denote the $U'$-scheme $V'$ with the maps $g_1$ and $g_2$ respectively. We also define $V'_(12)$ to be the $U''$-scheme defined by $(g_1, g_2): V' -> U'' = U' times_U U'$.
    Let $cal(U) = {u_i: U_i -> U}_(i in I), cal(V) = {v_j: V_j -> U}_(j in J)$, and the two refinements be given by $mu, lambda: J -> I$ and factorings: 
    #align(center, diagram({
      node((-1, 0), $V_j$)
      node((0, -1), $U_(mu(j))$)
      node((0, 1), $U_(lambda(j))$)
      node((1, 0), $U$)
      edge((-1, 0), (0, -1), $f_j$, "->")
      edge((-1, 0), (0, 1), $g_j$, "->", label-side: right)
      edge((-1, 0), (1, 0), $v_j$, "->")
      edge((0, -1), (1, 0), $u_(mu(j))$, "->")
      edge((0, 1), (1, 0), $u_(lambda(j))$, "->", label-side: right)
    }, spacing: 2em))
    
    Now define: 
    $
      h: C^p (cal(U), cal(G)) &-> C^(p-1) (cal(V), cal(G)) \

      (s_(i_0,dots.c,i_p))_(i_0,dots.c,i_p) &|-> (sum_(k=0)^(p-1) (-1)^k s_(mu(j_0),dots.c,mu(j_k),lambda(j_k),dots.c,lambda(j_(p-1)))|_(phi_k))_(j_0,dots.c,j_(p-1))
    $
    where $phi_k$ is the etale map: 
    $
      phi_k: V_(j_0) times_U dots.c times_U V_(j_(p-1)) -> U_(mu(j_0)) times_U dots.c times_U U_(mu(j_k)) times_U U_(lambda(j_k)) times_U dots.c times_U U_(lambda(j_(p-1)))
    $
    defined as the fiber product of maps: 

    - $f_(j_s): V_(j_s) -> U_(mu(j_s))$ for $0 <= s < k$; 

    - The single map $(f_(j_k), g_(j_k)): V_(j_k) -> U_(mu(j_k)) times_U U_(lambda(j_k))$; 

    - $g_(j_s): V_(j_s) -> U_(lambda(j_s))$ for $k < s <= p-1$. 

    By the same argument as that of the simplicial identities, $h$ is a chain homotopy between the chain maps induced by the refinements $g_1$ and $g_2$. 
  ]
  The $p$-th *Cech cohomology* of $cal(G) in cPAb(X_et)$ on $U$ is then defined as: 
  $
    caron(H)^p (U, cal(G)) = dirlim_(cal(U)) caron(H)^p (cal(U), cal(G))
  $
]

#lemma[
  + The right derived functors of $caron(H)^0 (cal(U), -): cPAb(X_et) -> cAb$ are ${caron(H)^p (cal(U), -)}_(p>=0)$ for every etale cover $cal(U)$ in $X_et$; 

  + The right derived functors of $caron(H)^0 (U, -): cPAb(X_et) -> cAb$ are ${caron(H)^p (U, -)}_(p>=0)$ for every $U in Et_X$. 
]
#proof[
  (1) $caron(H)^p (cal(U), -)$ are $delta$-functors, since a short exact sequence of presheaves $0 -> cal(F) -> cal(G) -> cal(H) -> 0$ is exact on sections, hence induces a short exact sequence of chain complexes: 
  $
    0 -> C^bullet (cal(U), cal(F)) -> C^bullet (cal(U), cal(G)) -> C^bullet (cal(U), cal(H)) -> 0
  $
  and induces a long exact sequence on cohomologies. As such, to show that $caron(H)^p (cal(U), -) cong R^p caron(H)^0 (cal(U), -)$, it suffices to prove that $caron(H)^p (cal(U), cal(I)) = 0$ for every $p >= 1$ and every injective $cal(I) in cPAb(X_et)$. Suppose that $cal(U) = {U_i -> U}_(i in I)$. We then need to show the exactness of the Cech complex: 
  $
    0 -> product_(i_0 in I) cal(I) (U_(i_0)) -> dots.c -> product_(i_0,dots.c,i_p in I) cal(I) (U_(i_0,dots.c,i_p)) -> product_(i_0,dots.c,i_(p+1) in I) cal(I) (U_(i_0,dots.c,i_(p+1))) -> dots.c
  $
  is exact at every $p >= 1$. Now $cal(I)(U^((p))) = Hom_(cPAb)(ul(ZZ)_(!,U^((p)),0), cal(I))$ and $cal(I)$ is injective so $Hom_(cPAb) (-, cal(I))$ is contravariant exact. As such, it suffices to show that the sequence: 
  $
    dots.c -> product_(i_0,dots.c,i_(p+1) in I) ul(ZZ)_(!,U_(i_0,dots.c,i_(p+1)),0) ->^partial product_(i_0,dots.c,i_p in I) ul(ZZ)_(!,U_(i_0,dots.c,i_p),0)  -> dots.c -> product_(i_0 in I) ul(ZZ)_(!,U_(i_0),0)
  $
  where $d$ is: 
  $
    partial: ul(ZZ)_(!,U^((p+1)),0) (V) = oplus.big_(Hom(U^((p+1)),V)) ZZ &-> ul(ZZ)_(!,U^((p)),0) (V) = oplus.big_(Hom(U^((p)), V)) ZZ \

    (s(f))_(f in Hom(U^((p+1)), V)) &|-> (sum_(k=0)^p (-1)^k s(g compose #[pr]_(0,dots.c,cancel(k),dots.c,p)))_(g in Hom(U^((p)), V))
  $
  where $#[pr] _(0,dots.c,cancel(k),dots.c,p): U^((p+1)) -> U^((p))$ is the projection onto all but the $k$-th components of $U^((p+1))$. 

  We know this chain complex very well from topology: This is the singular chain complex of a simplex. We may thus accept that it is exact. 

  (2) follows from (1), where $caron(H)^p (U, -)$ is a $delta$-functor, by taking the direct limit of the long exact sequences for each $caron(H)^p (cal(U), -)$ and using (Ab5) of $cAb$, and for injective $cal(I) in cPAb(X_et)$, $caron(H)^p (U, cal(I)) = 0$ as a direct limit of zeroes. 
]

#theorem(name: <cech-to-derived-functor-spectral-sequence>)[
  (Cech-to-derived-functor spectral sequence / Cartan-Leray spectral sequence) 
  
  For any $cal(F) in cAb(X_et)$, define the presheaf $ul(H)^q (cal(F)): Et_X^opp -> cAb, U |-> H^q (U, cal(F))$, whose restriction maps are obtained from the restriction maps on an injective resolution of $cal(F)$. 

  For every etale cover $cal(U)$ of $U in Et_X$, there is a natural spectral sequence: 
  $
    E_2^(p,q) = caron(H)^p (cal(U), ul(H)^q (cal(F))) => H^(p+q) (U, cal(F))
  $
  and for every $U in Et_X$, there is a natural spectral sequence: 
  $
    E_2^(p,q) = caron(H)^p (U, ul(H)^q (cal(F))) => H^(p+q) (U, cal(F))
  $
]
#proof[
  Note that the forgetful functor $iota: cAb(X_et) -> cPAb(X_et)$ has the exact left adjoint $(-)^\#$, and sends injectives to injectives, and that $caron(H)^p = R^p caron(H)^0$. 
  
  We now show that $ul(H)^q = R^q iota$. Indeed, for each $cal(F) in cAb(X_et)$, take an injective resolution $0 -> cal(F) -> cal(I)^bullet$ in $cAb(X_et)$. Then: 
  $
    R^q iota(cal(F)) = h^q (0 -> iota(cal(I)^bullet))
  $
  and cohomology in $cPAb$ is taken section-wise, so this presheaf is $U |-> h^q (0 -> iota(cal(I)^bullet)(U)) = H^q (U, cal(F))$, i.e. the presheaf $ul(H)^q (cal(F))$. 
  
  The theorem then follows from the Grothendieck-Leray spectral sequences of the following two compositions: 
  // https://q.uiver.app/#r=typst&q=WzAsMyxbMiwxLCJjQWIiXSxbMCwxLCJjQWIoWF9ldCkiXSxbMSwwLCJjUEFiKFhfZXQpIl0sWzEsMiwiaW90YSJdLFsyLDAsImNhcm9uKEgpXjAgKGNhbChVKSwgLSkiXSxbMSwwLCJHYW1tYShVLCAtKSIsMl1d
  #align(center, {
  diagram({
    node((1, 0), [$cAb$])
    node((-1, 0), [$cAb(X_et)$])
    node((0, -1), [$cPAb(X_et)$])
    edge((-1, 0), (0, -1), [$iota$], label-side: left, "->")
    edge((0, -1), (1, 0), [$caron(H)^0 (cal(U), -)$], label-side: left, "->")
    edge((-1, 0), (1, 0), [$Gamma(U, -)$], label-side: right, "->")
  })
  h(10%)
  diagram({
    node((1, 0), [$cAb$])
    node((-1, 0), [$cAb(X_et)$])
    node((0, -1), [$cPAb(X_et)$])
    edge((-1, 0), (0, -1), [$iota$], label-side: left, "->")
    edge((0, -1), (1, 0), [$caron(H)^0 (U, -)$], label-side: left, "->")
    edge((-1, 0), (1, 0), [$Gamma(U, -)$], label-side: right, "->")
  })
  })
]

#proposition(name: <cech-h0-of-hq-psh-vanish>)[
  For any $q >= 1$, $cal(F) in cAb(X_et)$, $U in Et_X$ and any class $alpha in ul(H)^q (cal(F))(U) = H^q (U, cal(F))$, there exists an etale cover $V ->> U$ s.t. $alpha|_V = 0$. 

  In particular, $caron(H)^0 (U, ul(H)^q (cal(F))) = 0$ for every $U in Et_X$, i.e. $ul(H)^q (cal(F))^+ = 0$. 
]
#proof[
  Pick an injective resolution of $cal(F)$ in $cAb(X_et)$: 
  $
    0 -> cal(F) -> cal(I)^bullet
  $
  and so $alpha in h^q (0 -> cal(I)^bullet (U))$. Since $cal(I)^(q-1) -> cal(I)^q -> cal(I)^(q+1)$ is exact at $q$, 
  $
    im(cal(I)^(q-1) -> cal(I)^q) = ker(cal(I)^q -> cal(I)^(q+1))
  $
  as sheaves. Let $alpha = [alpha_0]$ where $alpha_0 in ker(cal(I)^q -> cal(I)^(q+1)) = im(cal(I)^(q-1) -> cal(I)^q)$. Since the sheaf image is the presheaf image sheafified using the plus construction once (as the presheaf image is a sub-presheaf of a sheaf and is separated), there exists an etale cover ${V_i -> U}$ s.t. $alpha_0|_(V_i) in im(cal(I)^(q-1) (V_i) -> cal(I)^q (V_i))$. Passing to the disjoint union, there exists an etale cover $V ->> U$ s.t. $alpha_0|_V in im(cal(I)^(q-1) (V) -> cal(I)^q (V))$. Therefore, $alpha|_V = 0$. 

  That $caron(H)^0 (U, ul(H)^q (cal(F))) = 0$ is evident, since for any etale cover $cal(U) = {U' -> U}$, any class $alpha in caron(H)^0 (cal(U), ul(H)^q (cal(F))) subset H^q (U', cal(F))$ vanishes after passing to a refinement $V ->> U'$, hence vanishes in the direct limit. 
]

#corollary(name: <h1-is-cech-h1>)[
  There is a natural isomorphism for every $U in Et_X, cal(F) in cAb(X_et)$: 
  $
    caron(H)^1 (U, cal(F)) ->^tilde H^1 (U, cal(F))
  $
]
#proof[
  Take the five term exact sequence of the Cech-to-derived-functor spectral sequence: 
  $
    E_2^(p,q) = caron(H)^p (U, ul(H)^q (cal(F))) => H^(p+q) (U, cal(F))
  $
  Note that $ul(H)^0 (cal(F)) = cal(F)$ for very obvious reasons, so we get: 
  $
    0 -> caron(H)^1 (U, cal(F)) -> H^1 (U, cal(F)) -> caron(H)^0 (U, ul(H)^1 (cal(F))) -> caron(H)^2 (U, cal(F)) -> H^2 (U, cal(F))
  $
  However, we have shown that $caron(H)^0 (U, ul(H)^1 (cal(F))) = 0$, so we get an isomorphism: 
  $
    caron(H)^1 (U, cal(F)) ->^tilde H^1 (U, cal(F))
  $
]

/*
#lemma[
  If $X$ is a scheme in which every finite set of points in contained in an affine open, and $cal(P) in cPAb(X_et)$ s.t. $cal(P)^+ = 0$, then for all $U in Et_X$: 
  $
    caron(H)^p (U, cal(P)) = 0, forall p >= 0
  $
]
#proof[

]

#corollary[
  If $X$ is a scheme in which every finite set of points in contained in an affine open (which holds in many cases, say whenever $X$ is quasi-projective over an affine scheme), there are natural isomorphisms for all $U in Et_X, cal(F) in cAb(X_et)$: 
  $
    caron(H)^q (U, cal(F)) ->^tilde H^q (U, cal(F)), forall q >= 0
  $
]
#proof[

]*/
