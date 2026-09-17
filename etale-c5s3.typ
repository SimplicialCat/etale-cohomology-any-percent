#import "void-import.typ": *

== $H^1$ of multiplicative group

#proposition[
  Let $X = Spec(A)$ be an affine scheme. There is a canonical isomorphism: 
  $
    H^1_et (X, GG_m) cong Pic(X) = H^1_#[Zar] (X, cal(O)_X^times)
  $
  This isomorphism may be explicitly identified as follows: $H^1$ on the Zariski site and etale site can both be computed by $caron(H)^1$, and we have the map: 
  $
    caron(H)^1_#[Zar] (X, cal(O)_X^times) &-> Pic(X) = caron(H)^1_et (X, GG_m) \
    (u_(i,j) in cal(O)_X^times (U_i ∩ U_j))_(i,j) &|-> (u_(i,j) in GG_m (U_i times_X U_j))_(i,j)
  $
  where every Zariski open cover is an etale cover, and we just leave the Cech cocycles verbatim. 
]
#proof[
  We directly construct a map: 
  $
    Phi: caron(H)^1_et (X, GG_m) -> Pic(X)
  $
  Since $X$ is affine hence quasi-compact, every etale cover may be refined by a finite subcover using affine schemes. Passing to the disjoint union, we see that: 
  $
    caron(H)^1_et (X, GG_m) = dirlim_(cal(U) in cal(S)) caron(H)^1_et (cal(U), GG_m)
  $
  where $cal(S)$ consists of those etale covers consisting of a single map of the shape $cal(U) = {X' = Spec(A') -> X}$. Now: 
  $
    caron(H)^1_et (cal(U), GG_m) = (ker((A'')^times -> (A''')^times, a'' |-> i_(12)(a'') i_(23)(a'') i_(13) (a'')^(-1)))/(im((A')^times -> (A'')^times, a' |-> a' otimes a'^(-1)))
  $
  where $i_(12), i_(23), i_(13): A'' -> A'''$ are the three inclusions w.r.t. various components. We now define $Phi_(cal(U)): caron(H)^1_et (cal(U), GG_m) -> Pic(X)$ as follows: 

  - Given any class $alpha in caron(H)^1_et (cal(U), GG_m)$, represented by $u in (A'')^times$, $(times u): A'' -> A''$ is an isomorphism satisfying the cocycle conditions. This is some descent datum of $A'$ to $A$. By fpqc descent, there exists a unique $A$-module $M$, with an isomorphism $phi: M' := M otimes_A A' -> A'$, identifying the canonical descent datum $eta: M' otimes_A A' -> A' otimes_A M'$ with multiplication by $u$. 

    Since local freedom descends along faithfully flat morphisms, $M$ is a locally free $A$-module of rank 1, defining an element $[M] in Pic(X)$. 

  In other words, $Phi_(cal(U)) ([u]) = [M]$, where $[M] in Pic(X)$ is the unique element for which there exists an isomorphism $phi: M' -> A'$ s.t. the canonical descent datum $eta: M' otimes_A A' -> A' otimes_A M'$ is the composition: 
  $
    M' otimes_A A' -->^(phi otimes id) A'' -->^(times u) A'' -->^(id otimes phi^(-1)) A' otimes_A M'
  $

  Now there are a few facts to check. 

  - The map $ker((A'')^times -> (A''')^times) -> Pic(X)$ defined above gives a group homomorphism. Indeed, suppose that $u_1, u_2 in (A'')^times$ are sent to $[M_1], [M_2] in Pic(X)$, and we claim that $u_1 u_2$ is sent to $[M_1 otimes_A M_2]$. Let $N = M_1 otimes_A M_2$. Indeed, take the isomorphism $psi: N' -> A'$ as $M_1 otimes_A M_2 otimes A' -->^(id otimes phi_2) M_1 otimes_A A' -->^(phi_1) A'$. 

    Now consider the commutative diagram: 
    // https://q.uiver.app/#r=typst&q=WzAsNixbMCwwLCJOJyBvdGltZXNfQSBBJyJdLFs0LDAsIkEnIG90aW1lc19BIE4nIl0sWzIsMCwiTSdfMSBvdGltZXNfQSBNJ18yIl0sWzAsMiwiQScnIl0sWzIsMiwiQScnIl0sWzQsMiwiQScnIl0sWzAsMiwiaWRfKE1fMSkgb3RpbWVzIGV0YV8yIl0sWzIsMSwiZXRhXzEgb3RpbWVzIGlkXyhNXzEpIl0sWzAsMywicHNpIG90aW1lcyBpZCIsMl0sWzIsNCwicGhpXzEgb3RpbWVzIHBoaV8yIiwyXSxbMSw1XSxbMyw0LCJ0aW1lcyB1XzIiXSxbNCw1LCJ0aW1lcyB1XzEiXV0=
    #align(center, diagram({
      node((-1, -1), [$N' otimes_A A'$])
      node((3, -1), [$A' otimes_A N'$])
      node((1, -1), [$M'_1 otimes_A M'_2$])
      node((-1, 1), [$A''$])
      node((1, 1), [$A''$])
      node((3, 1), [$A''$])
      edge((-1, -1), (1, -1), [$id_(M_1) otimes eta_2$], label-side: left, "->")
      edge((1, -1), (3, -1), [$eta_1 otimes id_(M_1)$], label-side: left, "->")
      edge((-1, -1), (-1, 1), [$psi otimes id$], label-side: right, "->")
      edge((1, -1), (1, 1), [$phi_1 otimes phi_2$], label-side: right, "->")
      edge((3, -1), (3, 1), "->", $id otimes psi$)
      edge((-1, 1), (1, 1), [$times u_2$], label-side: left, "->")
      edge((1, 1), (3, 1), [$times u_1$], label-side: left, "->")
    }))
    where the first row is the canonical descent datum for $N'$. We are thereby done showing $u_1 u_2$ is sent to $[M_1 otimes_A M_2]$. 

  - $Phi_(cal(U))$ defined above is well-defined and injective. That is, we want to show that $u in (A'')^times$ is sent to $[A] in Pic(X)$ if and only if $u$ has the form $a' otimes a'^(-1)$.
    
    ($==>$) If $u$ is sent to $[A] in Pic(X)$, there exists an isomorphism $phi: A' -> A'$ s.t. the canonical descent datum $id: A' otimes_A A' -> A' otimes_A A'$ is the composition:
    $
      A' otimes_A A' -->^(phi otimes id) A'' -->^(times u) A'' -->^(id otimes phi^(-1)) A' otimes_A A'
    $
    Let $phi$ be represented by multiplication by $a'^(-1) in (A')^times$, and we see that $u = a' otimes a'^(-1)$. 

    ($<==$) If $u = a' otimes a'^(-1)$, take $phi: A' -> A'$ to be multiplication by $a'^(-1)$, and so: 
    $
      A' otimes_A A' -->^(phi otimes id) A'' -->^(times u) A'' -->^(id otimes phi^(-1)) A' otimes_A A'
    $
    is $id: A' otimes_A A' -> A' otimes_A A'$, the canonical descent datum. Hence, $u$ is sent to $[A] in Pic(X)$. 

  - $Phi_(cal(U))$ is compatible with the direct system. 

    Suppose that $Spec(tilde(A)')$ refines $Spec(A') -> Spec(A)$ as etale covers, i.e. we have etale ring maps $A -> A' -> tilde(A)'$. Given an element $u in A''$ mapping to $tilde(u) in tilde(A)''$, we need to show that the element of $Pic(Spec(A))$ given by $u$ and $tilde(u)$ are equal. For this, suppose that $[M] in Pic(Spec(A))$ is the image of $u$. In other words, we have an isomorphism $phi: M otimes_A A' -> A'$ s.t. the canonical descent datum $eta: (M otimes_A A') otimes_A A' -> A' otimes_A (M otimes_A A')$ is given by:
    $
      (M otimes_A A') otimes_A A' -->^(phi otimes id) A' otimes_A A' -->^(times u) A' otimes_A A' -->^(id otimes phi^(-1)) A' otimes_A (M otimes_A A')
    $
    Then we have an isomorphism $tilde(phi): M otimes_A tilde(A)' -> tilde(A')$ obtained as $phi otimes_(A') id_(tilde(A)')$. We then see that the canonical descent datum $tilde(eta): (M otimes_A tilde(A)') otimes_A tilde(A)' -> tilde(A)' otimes_A (M otimes_A tilde(A)')$ is just $eta$ tensored with $tilde(A)' otimes_A tilde(A)'$ w.r.t. $A' otimes_A A'$, and is thus:
    $
      (M otimes_A tilde(A)') otimes_A tilde(A)' -->^(tilde(phi) otimes id) tilde(A)' otimes_A tilde(A)' -->^(times tilde(u)) tilde(A)' otimes_A tilde(A)' -->^(id otimes tilde(phi)^(-1)) tilde(A)' otimes_A (M otimes_A tilde(A)')
    $
    By uniqueness of descent, $[M]$ is also the image of $tilde(u)$. 

  Since injectivity is preserved by direct limits, taking the direct limit, we have constructed an injective homomorphism: 
  $
    Phi: caron(H)^1_et (X, GG_m) -> Pic(X)
  $
  Finally, we show that $Phi$ is surjective. Given any $[M] in Pic(X)$, $M$ is a locally free $A$-module of rank 1. Therefore, there exists a Zariski cover $Spec(A') ->> Spec(A)$ and an isomorphism $phi: M otimes_A A' -> A'$, obtained by taking the disjoint union of a cover of $X$ by affine opens that trivialize $M$. Let $cal(U) = {Spec(A') -> Spec(A)}$, and let $u in (A'')^times$ be the element s.t. the canonical descent datum $M' otimes_A A' -> A' otimes_A M'$ is: 
  $
    M' otimes_A A' -->^(phi otimes id) A'' -->^(times u) A'' -->^(id otimes phi^(-1)) A' otimes_A M'
  $
  Then $Phi_(cal(U)) ([u]) = [M]$. As such, $Phi$ is an isomorphism. We are thereby done. 
  
  /*Passing to the disjoint union, we may assume that we are dealing with an element: 
  $
    u in caron(H)^1_et (cal(U), GG_m), cal(U) = {X' = Spec(A') ->> X}
  $
  In particular, $A -> A'$ is faithfully flat. Expanding definitions, $u$ is represented by an element of $(A'')^times$ satisfying the cocycle condition when pulled in three ways to an automorphism of $A'''$. In other words, it determines some descent datum for the $A'$-module $A'$ to $A$. By fpqc descent, this descends to an $A$-module $M$ s.t. $M otimes_A A' cong A'$, with the isomorphism in the descent datum being multiplication by $u$. Since local freedom descends along faithfully flat ring maps, $M$ is locally free of rank 1. We then send $u$ to the element $[M] in Pic(Spec(A))$. 

  - This map is well-defined. 

    Suppose that $Spec(tilde(A)')$ refines $Spec(A') -> Spec(A)$ as etale covers, i.e. we have etale ring maps $A -> A' -> tilde(A)'$. Given an element $u in A''$ mapping to $tilde(u) in tilde(A)''$, we need to show that the element of $Pic(Spec(A))$ given by $u$ and $tilde(u)$ are equal. For this, suppose that $[M] in Pic(Spec(A))$ is the image of $u$. In other words, we have an isomorphism $phi: M otimes_A A' -> A'$ s.t. the canonical descent datum $eta: (M otimes_A A') otimes_A A' -> A' otimes_A (M otimes_A A')$ is given by: 
    $
      (M otimes_A A') otimes_A A' -->^(phi otimes id) A' otimes_A A' -->^(times u) A' otimes_A A' -->^(id otimes phi^(-1)) A' otimes_A (M otimes_A A')
    $
    Then we have an isomorphism $tilde(phi): M otimes_A tilde(A)' -> tilde(A')$ obtained as $phi otimes_(A') id_(tilde(A)')$. We then see that the canonical descent datum $tilde(eta): (M otimes_A tilde(A)') otimes_A tilde(A)' -> tilde(A)' otimes_A (M otimes_A tilde(A)')$ is just $eta$ tensored with $tilde(A)' otimes_A tilde(A)'$ w.r.t. $A' otimes_A A'$, and is thus: 
    $
      (M otimes_A tilde(A)') otimes_A tilde(A)' -->^(tilde(phi) otimes id) tilde(A)' otimes_A tilde(A)' -->^(times tilde(u)) tilde(A)' otimes_A tilde(A)' -->^(id otimes tilde(phi)^(-1)) tilde(A)' otimes_A (M otimes_A tilde(A)')
    $
    By uniqueness of descent, $[M]$ is also the image of $tilde(u)$. 

  - This map is a group homomorphism: 

    Suppose that $u_1, u_2 in A''$ are sent to $[M_1], [M_2] in Pic(Spec(A))$, respectively, with isomorphisms $phi_(1,2): M_(1,2) otimes_A A' -> A'$ relating canonical descent datum of $M_1, M_2$ with $u_1, u_2$ in the way described above. Then consider $N = M_1 otimes_A M_2$ with an isomorphism $psi: N otimes_A A' -->^(id_(M_1) otimes phi_2) M_1 otimes A' -->^(phi_1) A'$. Now the canonical descent datum for $N$ is: 
    $
      (M_1 otimes_A M_2 otimes_A A') otimes_A A' -->^(id_(M_1) otimes eta_2) (M_1 otimes_A A') otimes_A (M_2 otimes_A A') -->^(eta_1 otimes id_(M_2)) A' otimes_A (M_1 otimes_A M_2 otimes_A A')
    $
    By applying the isomorphisms $phi_1, phi_2, psi$, we then see that this descent datum is multiplication by $u_1 u_2$ under $psi$. We are thereby done. 

  - This morphism is surjective. 

    Every $[M] in Pic(Spec(A))$ has $M$ Zariski locally trivial on $Spec(A)$. As such, there exists a morphism $f: Spec(A') ->> Spec(A)$ that is a local isomorphism s.t. $M otimes A' cong A'$. The element of $(A'')^times$ giving the isomorphism of the canonical descent datum for $M otimes A'$ is thus sent to $[M]$. 

  - This morphism is injective. 

    Given $u in (A'')^times$*/
]

#theorem(name: <h1-of-gm-is-pic>)[
  Let $X$ be any scheme. There is a canonical isomorphism:
  $
    H^1_et (X, GG_m) cong Pic(X) = H^1_#[Zar] (X, cal(O)_X^times)
  $
  This isomorphism may be explicitly identified as follows: $H^1$ on the Zariski site and etale site can both be computed by $caron(H)^1$, and we have the map:
  $
    caron(H)^1_#[Zar] (X, cal(O)_X^times) & -> Pic(X) = caron(H)^1_et (X, GG_m) \
    (u_(i,j) in cal(O)_X^times (U_i ∩ U_j))_(i,j) & |-> (u_(i,j) in GG_m (U_i times_X U_j))_(i,j)
  $
  where every Zariski open cover is an etale cover, and we just leave the Cech cocycles verbatim.
]
#proof[
  As in the proof of @etale-cohom-of-qcoh-sheaf, the forgetful functor: 
  $
    epsilon: cAb(X_et) -> cAb(X_#[Zar])
  $
  fits in a spectral sequence: 
  $
    E_2^(p,q) = H^p_#[Zar] (X, R^q epsilon (GG_m)) => H^(p+q)_et (X, GG_m)
  $
  The five term exact sequence gives: 
  $
    0 -> H^1_#[Zar] (X, cal(O)_X^times) -> H^1_et (X, GG_m) -> H^0_#[Zar] (X, R^1 epsilon (GG_m)) -> dots.c
  $
  where the first map has the explicit form in the theorem statement, as can be checked by unfolding definitions. It suffices to prove that: 
  $
    R^1 epsilon (GG_m) = 0
  $
  and as proved in the proof of @etale-cohom-of-qcoh-sheaf, $R^1 epsilon (GG_m)$ is the Zariski sheafification of the presheaf $cal(R): U |-> H^1_et (U, GG_m)$. Given a point $x in X$, note that affine opens make up a neighborhood basis around $x$. Thus: 
  $
    cal(R)_x = dirlim_(x in U #[affine]) H^1_et (U, GG_m) cong dirlim_(x in U #[affine]) Pic(U)
  $
  by the previous proposition, where the transition morphisms are just restriction $Pic(U) -> Pic(V)$ for $x in V subset U$. However, for any $[cal(L)] in Pic(U)$, there exists a smaller affine neighborhood $x in V subset U$ s.t. $cal(L)|_V cong cal(O)_V$, i.e. $cal(L)$ goes to the identity upon passing to $Pic(V)$. Therefore, every element in the direct limit $dirlim_(x in U #[affine]) Pic(U)$ is zero. Thus, $cal(R)_x = 0$ for all $x in X$, and so $cal(R) = 0$. Now $R^1 epsilon (GG_m)$, as the Zariski sheafification of $cal(R)$, must be zero. 
]
