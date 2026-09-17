#import "void-import.typ": *
== Internal Hom and tensor <sect-hom-tensor>

In this section, we establish a hom-tensor duality of etale sheaves. 

#definition(name: <defn-etale-ring-and-module-sheaves>)[
  Let $X$ be a scheme. An *etale presheaf/sheaf of rings* $cal(A)$ on $X$, is an abelian etale presheaf/sheaf $cal(A) in cPAb(X_et)$ or $cAb(X_et)$ on which each $cal(A)(U)$ is equipped with the structure of a ring, compatible with the restriction morphisms, in the sense that the following diagram commutes: 
  // https://q.uiver.app/#r=typst&q=WzAsNCxbMCwwLCJjYWwoQSkoVSkgdGltZXMgY2FsKEEpKFUpIl0sWzAsMSwiY2FsKEEpKFYpIHRpbWVzIGNhbChBKShWKSJdLFsxLDAsImNhbChBKShVKSJdLFsxLDEsImNhbChBKShWKSJdLFswLDIsInRpbWVzIl0sWzEsMywidGltZXMiLDJdLFswLDEsInJlc15VX1YgdGltZXMgcmVzXlVfViIsMV0sWzIsMywicmVzXlVfViIsMV1d
  #context align(center, diagram({
    node((-1, -1), [$cal(A)(U) times cal(A)(U)$])
    node((-1, 0), [$cal(A)(V) times cal(A)(V)$])
    node((0, -1), [$cal(A)(U)$])
    node((0, 0), [$cal(A)(V)$])
    edge((-1, -1), (0, -1), [$times$], label-side: left, "->")
    edge((-1, 0), (0, 0), [$times$], label-side: right, "->")
    edge((-1, -1), (-1, 0), [$res^U_V times res^U_V$], label-side: center, "->")
    edge((0, -1), (0, 0), [$res^U_V$], label-side: center, "->")
  }, crossing-fill: thm-box-curr-color()))

  Given an etale presheaf/sheaf of rings $cal(A)$ on $X$, an *etale presheaf/sheaf of $cal(A)$-modules* $cal(M)$ is an abelian etale presheaf/sheaf $cal(M)$ on which each $cal(M)(U)$ is equipped with the structure of an $cal(A)(U)$-module, compatible with the restriction morphisms, in the sense that the following diagram commutes: 

  // https://q.uiver.app/#r=typst&q=WzAsNCxbMCwwLCJjYWwoQSkoVSkgdGltZXMgY2FsKE0pKFUpIl0sWzAsMSwiY2FsKEEpKFYpIHRpbWVzIGNhbChNKShWKSJdLFsxLDAsImNhbChNKShVKSJdLFsxLDEsImNhbChNKShWKSJdLFswLDIsInRpbWVzIl0sWzEsMywidGltZXMiLDJdLFswLDEsInJlc15VX1YgdGltZXMgcmVzXlVfViIsMV0sWzIsMywicmVzXlVfViIsMV1d
  #context align(center, diagram({
    node((0, 0), [$cal(A)(U) times cal(M)(U)$])
    node((0, 1), [$cal(A)(V) times cal(M)(V)$])
    node((1, 0), [$cal(M)(U)$])
    node((1, 1), [$cal(M)(V)$])
    edge((0, 0), (1, 0), [$times$], label-side: left, "->")
    edge((0, 1), (1, 1), [$times$], label-side: right, "->")
    edge((0, 0), (0, 1), [$res^U_V times res^U_V$], label-side: center, "->")
    edge((1, 0), (1, 1), [$res^U_V$], label-side: center, "->")
  }, crossing-fill: thm-box-curr-color()))

  The category of etale presheaves/sheaves of $cal(A)$-modules is denoted $cPAb(X_et, cal(A))$ or $cAb(X_et, cal(A))$. 
]

#example[
  - The forgetful functor $cAb(X_et, ul(ZZ)_X) -> cAb(X_et)$ from the category of sheaves of $ul(ZZ)_X$-modules is an equivalence of categories. Indeed, the quasi-inverse can be constructed, as every abelian etale sheaf $cal(F)$ can be uniquely equipped with the structure of a sheaf of $ul(ZZ)_X$-modules, by: 
    $
      ul(ZZ)_X (U) times cal(F)(U) -> cal(F)(U), f, s |-> f s
    $
    where $f in ul(ZZ)_X (U)$ is a locally constant function $U -> ZZ$, so that $f s$ is obtained by gluing $n s|_(f^(-1)(n))$ from the partition ${f^(-1)(n)}_(n in ZZ)$ of $U$. 

  - Similarly, the forgetful functor $cAb(X_et, ul(ZZ\/n)_X) -> cAb(X_et, ZZ\/n)$ from the sheaves of $ul(ZZ\/n)$-modules to the $n$-torsion sheaves is an equivalence of categories. 
]

These are actually pretty much all examples that we will use in this document. Nevertheless, it is worthwhile to state the theory of internal hom and tensors in the general setting. 

#proposition[
  Let $X$ be a scheme and $cal(A)$ be an etale sheaf of rings on $X$. Given $cal(M), cal(N) in cAb(X_et, cal(A))$, the presheaf: 
  $
    HHom_(cal(A)) (cal(M), cal(N)): Et_X^opp -> cAb, U |-> Hom_(cal(A)|_U) (cal(M)|_U, cal(N)|_U)
  $ 
  is an etale sheaf of $cal(A)$-modules. 
]
#proof[
  This argument is entirely formal and identical to that for sheaf hom of Zariski sheaves, and generalizes to all sites instead of being limited to the etale site. 

  Let $U in Et_X$ and $cal(U) = {U_i -> U}_(i in I)$ be an etale cover. 

  - Separatedness: Given $phi in Hom_(cal(A)|_U) (cal(M)|_U, cal(N)|_U)$ s.t. $phi|_(U_i) = 0$ for each $i$, and any $V in Et_U$, we have: 
    $
      phi_V (s)|_(U_i times_U V) = phi|_(U_i) (s|_(U_i times_U V)) = 0
    $
    Hence by separatedness of $cal(N)$, $phi_V (s) = 0$. Hence $phi = 0$. 

  - Gluing: Given compatible $phi_i in Hom_(cal(A)|_(U_i)) (cal(M)|_(U_i), cal(N)|_(U_i))$, and any $V in Et_U$, we define $phi in Hom_(cal(A)|_U) (cal(M)|_U, cal(N)|_U)$ by letting: 
    $
      phi_V (s)|_(U_i times_U V) = phi_i (s|_(U_i times_U V))
    $
    and gluing to get $phi_V (s)$. These sections do indeed glue since the ${phi_i}$'s are compatible, and it is routine to check that $phi|_(U_i) = phi_i$. 

  The structure of $cal(A)$-modules is natural. 
]

#definition(name: <defn-internal-hom>)[
  Let $X$ be a scheme and $cal(A)$ be an etale presheaf/sheaf of rings on $X$. Given $cal(M), cal(N) in cPAb(X_et, cal(A))$ or $cAb(X_et, cal(A))$, their *internal hom* or *presheaf/sheaf hom* $HHom_(cal(A)) (cal(M), cal(N))$ is the presheaf/sheaf of $cal(A)$-modules defined by: 
  $
    HHom_(cal(A)) (cal(M), cal(N)): Et_X^opp -> cAb, U |-> Hom_(cal(A)|_U) (cal(M)|_U, cal(N)|_U)
  $
]

We next define a tensor product, and prove hom-tensor duality: 

#definition(name: <defn-sheaf-tensor-product>)[
  Given an etale presheaf of rings $cal(A)$ on $X$ and $cal(M), cal(N) in cPAb(X_et, cal(A))$, we define their *presheaf tensor product* to be the presheaf of $cal(A)$-modules: 
  $
    cal(M) otimes_(cal(A),cPSh) cal(N): Et_X^opp -> cAb, U |-> cal(M)(U) otimes_(cal(A)(U)) cal(N)(U)
  $

  Given an etale sheaf of rings $cal(A)$ on $X$ and $cal(M), cal(N) in cAb(X_et, cal(A))$, we define their *sheaf tensor product* to be the sheaf of $cal(A)$-modules: 
  $
    cal(M) otimes_(cal(A)) cal(N) := (cal(M) otimes_(cal(A),cPSh) cal(N))^\#
  $
  to be the sheafification of the presheaf tensor product. 
]

#proposition(name: <hom-tensor-first-props>)[
  + Given a etale presheaf of rings $cal(A)$ on $X$ and $cal(N) in cPAb(X_et, cal(A))$, there is a natural isomorphism for any $cal(M), cal(P) in cPAb(X_et, cal(A))$: #h(1fr)
    $
      HHom_(cal(A)) (cal(M), HHom_(cal(A)) (cal(N), cal(P))) cong HHom_(cal(A)) (cal(M) otimes_(cal(A),cPSh) cal(N), cal(P))
    $
    In particular, taking global sections, we have: 
    $
      Hom_(cal(A)) (cal(M), HHom_(cal(A)) (cal(N), cal(P))) cong Hom_(cal(A)) (cal(M) otimes_(cal(A),cPSh) cal(N), cal(P))
    $
    and so the tensor product $- otimes_(cal(A),cPSh) cal(N)$ is the left adjoint of $HHom_(cal(A)) (cal(N), -): cPAb(X_et, cal(A)) -> cPAb(X_et, cal(A))$. 

  + Given a etale sheaf of rings $cal(A)$ on $X$ and $cal(N) in cAb(X_et, cal(A))$, there is a natural isomorphism for any $cal(M), cal(P) in cAb(X_et, cal(A))$: #h(1fr)
    $
      HHom_(cal(A)) (cal(M), HHom_(cal(A)) (cal(N), cal(P))) cong HHom_(cal(A)) (cal(M) otimes_(cal(A)) cal(N), cal(P))
    $
    In particular, taking global sections, we have: 
    $
      Hom_(cal(A)) (cal(M), HHom_(cal(A)) (cal(N), cal(P))) cong Hom_(cal(A)) (cal(M) otimes_(cal(A)) cal(N), cal(P))
    $
    and so the tensor product $- otimes_(cal(A)) cal(N)$ is the left adjoint of $HHom_(cal(A)) (cal(N), -): cAb(X_et, cal(A)) -> cAb(X_et, cal(A))$. 
]
#proof[
  The proof is, once again, formal arguments. We won't present all details: 
  
  (1) By replacing $cal(A), cal(M), cal(N), cal(P)$ with $cal(A)|_U, cal(M)|_U, cal(N)|_U, cal(P)|_U$, we see that it suffices to prove the statement: 
  $
    Hom_(cal(A)) (cal(M), HHom_(cal(A)) (cal(N), cal(P))) cong Hom_(cal(A)) (cal(M) otimes_(cal(A),cPSh) cal(N), cal(P))
  $
  Now: 
  $
    & Hom_(cal(A)) (cal(M), HHom_(cal(A)) (cal(N), cal(P))) \
    =& {{phi_U in Hom_(cal(A)(U)) (cal(M)(U), Hom_(cal(A)|_U) (cal(N)|_U, cal(P)|_U))}_(U in Et_X) #[compatible with restriction]} \
    =& {{phi_U in Hom_(cal(A)(U)) (cal(M)(U), Hom_(cal(A)(U)) (cal(N)(U), cal(P)(U)))}_(U in Et_X) #[compatible with restriction]} \
    =& {{phi_U in Hom_(cal(A)(U)) (cal(M)(U) otimes_(cal(A)(U)) cal(N)(U), cal(P)(U))}_(U in Et_X) #[compatible with restriction]} \
    =& Hom_(cal(A)) (cal(M) otimes_(cal(A),cPSh) cal(N), cal(P))
  $ 
  In this deduction, the only line needing an explanation is the third line: There is a natural map: 
  $
    & {{phi_U in Hom_(cal(A)(U)) (cal(M)(U), Hom_(cal(A)|_U) (cal(N)|_U, cal(P)|_U))}_(U in Et_X) #[compatible with restriction]} \
    ->& {{psi_U in Hom_(cal(A)(U)) (cal(M)(U), Hom_(cal(A)(U)) (cal(N)(U), cal(P)(U)))}_(U in Et_X) #[compatible with restriction]}
  $
  by taking the map on global sections. Its inverse is given as follows: Given ${psi_U in Hom_(cal(A)(U)) (cal(M)(U), Hom_(cal(A)(U)) (cal(N)(U), cal(P)(U)))}_(U in Et_X) #[compatible with restriction]$, take: 
  $
    phi_U (s in cal(M)(U)): cal(N)(V) &-> cal(P)(V), V in Et_U \
    t &|-> psi_V (s|_V) (t|_V)
  $
  It is routine and formal to see that this is an inverse. We are thereby done. 

  (2) Similarly, it suffices to prove the adjunction. However, from the adjunction in the presheaf case and the sheafification: 
  $
    Hom_(cal(A)) (cal(M), HHom_(cal(A)) (cal(N), cal(P))) &cong Hom_(cal(A)) (cal(M) otimes_(cal(A),cPSh) cal(N), cal(P)) \
    &cong Hom_(cal(A)) ((cal(M) otimes_(cal(A),cPSh) cal(N))^\#, cal(P)) \
    &= Hom_(cal(A)) (cal(M) otimes_(cal(A)) cal(N), cal(P))
  $
  and we are done. 
]

Next, we study how functors like $f_*$ and $f^(-1)$ interact with hom and tensor. 

#proposition[
  Let $f: X -> Y$ be a morphism of schemes, and $cal(A)$ be an etale sheaf of rings on $Y$. 
  
  + For any $cal(F) in cAb(X_et, f^(-1)cal(A)), cal(G) in cAb(Y_et, cal(A))$, there is a natural isomorphism: #h(1fr)
    $
      f_* HHom_(f^(-1) cal(A)) (f^(-1) cal(G), cal(F)) cong HHom_(cal(A)) (cal(G), f_* cal(F))
    $

  + For any $cal(F), cal(G) in cAb(Y_et, cal(A))$, there is a natural isomorphism: 
    $
      f^(-1) cal(F) otimes_(f^(-1) cal(A)) f^(-1) cal(G) cong f^(-1) (cal(F) otimes_(cal(A)) cal(G))
    $

  + If $f$ is etale, for any $cal(F) in cAb(X_et, f^(-1)cal(A)), cal(G) in cAb(Y_et, cal(A))$, there is a natural isomorphism: 
    $
      f_* HHom_(f^(-1) cal(A)) (cal(F), f^(-1) cal(G)) cong HHom_(cal(A)) (f_! cal(F), cal(G))
    $

  + (Projection formula) If $f$ is etale, for any $cal(F) in cAb(X_et, f^(-1) cal(A)), cal(G) in cAb(Y_et, cal(A))$, there is a natural isomorphism: 
    $
      f_! (f^(-1) cal(G) otimes_(f^(-1) cal(A)) cal(F)) cong cal(G) otimes_(cal(A)) f_! cal(F)
    $

  
]
#proof[
  (1) and (3) can be checked on sections, and really just reduces to the adjunction of $f_*$ with $f^(-1)$, and $f^(-1)$ with $f_!$. 

  (2) can be checked by Yoneda and (1): 
  $
    Hom_(f^(-1) cal(A)) (f^(-1) cal(F) otimes_(f^(-1) cal(A)) f^(-1) cal(G), cal(R)) &= Hom_(f^(-1) cal(A)) (f^(-1) cal(F), HHom_(f^(-1) cal(A)) (f^(-1) cal(G), cal(R))) \
    &= Hom_(cal(A)) (cal(F), f_* HHom_(f^(-1) cal(A)) (f^(-1) cal(G), cal(R))) \
    &= Hom_(cal(A)) (cal(F), HHom_(cal(A)) (cal(G), f_* cal(R))) \
    &= Hom_(cal(A)) (cal(F) otimes_(cal(A)) cal(G), f_* cal(R)) \
    &= Hom_(f^(-1) cal(A)) (f^(-1) (cal(F) otimes_(cal(A)) cal(G)), cal(R))
  $

  (4) There is a canonical morphism: 
  $
    f_! (f^(-1) cal(G) otimes_(f^(-1) cal(A)) cal(F)) -> cal(G) otimes_(cal(A)) f_! cal(F)
  $
  by adjunction of $f^(-1) cal(G) otimes_(f^(-1) cal(A)) cal(F) -> f^(-1) cal(G) otimes_(f^(-1) cal(A)) f^(-1) f_! cal(F) = f^(-1) (cal(G) otimes_(cal(A)) f_! cal(F))$ (where the last isomorphism is by (2)). This morphism is an isomorphism, as can be checked on stalks by (2) and @etale-lower-shriek-first-props: 
  $
    (f_! (f^(-1) cal(G) otimes_(f^(-1) cal(A)) cal(F)))_(ol(x)) &= oplus.big_(ol(u) in f^(-1)(ol(x))) (f^(-1) cal(G) otimes_(f^(-1) cal(A)) cal(F))_(ol(u)) = oplus.big_(ol(u) in f^(-1)(ol(x))) cal(G)_(f(ol(u))) otimes_(cal(A)_(f(ol(u)))) cal(F)_(ol(u)) \
    &= cal(G)_(ol(x)) otimes_(cal(A)_(ol(x))) oplus.big_(ol(u) in f^(-1)(ol(x))) cal(F)_(ol(u)) \
    &= cal(G)_(ol(x)) otimes_(cal(A)_(ol(x))) (f_! cal(F))_(ol(x)) = (cal(G) otimes_(cal(A)) f_! cal(F))_(ol(x))
  $
]

Finally, we deal with flat objects. 
#lemma[
  Let $X$ be a scheme and $cal(A)$ be an etale sheaf of rings on $X$. An object $cal(M) in cAb(X_et, cal(A))$ is flat whenever $cal(M)_(ol(x))$ is a flat $cal(A)_(ol(x))$-module for all geometric points $ol(x)$ of $X$. 
]
#proof[
  Given an injection $cal(F) -> cal(G)$ in $cAb(X_et, cal(A))$, we need to check that $cal(F) otimes_(cal(A)) cal(M) -> cal(G) otimes_(cal(A)) cal(M)$ is injective. This can be checked on stalks, where $cal(F)_(ol(x)) otimes_(cal(A)_(ol(x))) cal(M)_(ol(x)) -> cal(G)_(ol(x)) otimes_(cal(A)_(ol(x))) cal(M)_(ol(x))$ is injective since $cal(M)_(ol(x))$ is a flat $cal(A)_(ol(x))$-module. 
]

#corollary(name: <flat-resolution-of-et-sheaf>)[
  Let $X$ be a scheme and $cal(A)$ be an etale sheaf of rings on $X$. For every $(f: U -> X) in Et_X$, $f_! f^(-1) cal(A)$ is a flat object of $cAb(X_et, cal(A))$. In particular, $cAb(X_et, cal(A))$ has enough flat objects. 
]
#proof[
  We check that: 
  $
    (f_! f^(-1) cal(A))_(ol(x)) = oplus.big_(ol(u) in f^(-1)(ol(x))) (f^(-1) cal(A))_(ol(u)) = cal(A)_(ol(x))^(oplus f^(-1)(ol(x)))
  $
  is a free $cal(A)_(ol(x))$-module, hence flat. 

  For any $cal(M) in cAb(X_et, cal(A))$, it admits a surjection from a flat $cal(A)$-module by the following construction: 
  $
    oplus.big_((f: U -> X) in Et_X \ #[$U$ affine \ $exists V subset X$ affine, $f(U) subset V$]) oplus.big_(s in cal(M)(f)) f_! f^(-1) cal(A) -> cal(M)
  $
  where for each $(f, s)$ indexing this direct sum, $f_! f^(-1) cal(A) -> cal(M)$ is obtained by adjunction from $f^(-1) cal(A) -> f^(-1) cal(M)$, defined by the global section $s$ of $f^(-1) cal(M)$. $s in cal(M)(f)$ is thus in the image of this $f_! f^(-1) cal(A) -> cal(M)$. Since every object of $Et_X$ is covered by objects $f: U -> X$ of $Et_X$ s.t. $U$ is affine and $f(U)$ is contained in an affine open of $X$, this morphism is surjective, and its LHS is a direct sum of flat objects, hence flat. 

  #remark[
    The restriction on $f in Et_X$ in the direct sum is to avoid a set-theoretic difficulty, as discussed in @set-categorical-subtleties. 
  ]
]
