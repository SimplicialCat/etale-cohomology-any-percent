#import "void-import.typ": *

In this appendix, we prove the Brown representability theorem, a formal criterion for a triangulated functor $D(cal(A)) -> cal(D)$ to have a right adjoint. The statement is: 

- Let $cal(A)$ be a Grothendieck abelian category. Then any triangulated functor $D(cal(A)) -> cal(D)$ that preserves arbitrary direct sums must have a triangulated right adjoint. 

The proof first reduces to the module category $AMod(R)$ by the Gabriel-Popescu theorem, and then uses a compact version of Brown representability theorem to bootstrap the proof. 

#theorem(name: <gabriel-popescu>)[
  (Gabriel-Popescu theorem) Let $cal(A)$ be a Grothendieck abelian category. Then there exists a non-commutative ring $R$ and functors: 
  $
    Q: AMod(R) arrows.rl cal(A): G
  $
  with $Q$ left adjoint to $G$, $G$ fully faithful and $Q$ exact. 
]
#proof[
  Let $U in cal(A)$ be a generator and $R = End_(cal(A)) (U)$ be its ring of endomorphisms. Now put: 
  $
    G: cal(A) -> AMod(R), A |-> Hom_(cal(A)) (U, A)
  $
  Then each $G(A) = Hom_(cal(A)) (U, A)$ is a right $R$-module under composition. On the other hand, to define $Q$, for any $M in AMod(R)$ there is a canonical free resolution: 
  $
    R^(oplus K(M)) ->^A R^(oplus M) -> M -> 0
  $
  in which $K(M) = ker(R^(oplus M) -> M)$. Let $A$ be represented by a matrix $display(mat(r_(m,k))_(k in K(M),m in M))$ where $r_(m,k) in R = End_(cal(A)) (U)$ is an endomorphism of $U$. Then $A$ passes to a morphism: 
  $
    A_U: U^(oplus K(M)) -> U^(oplus M), (u_k) |-> (sum_(k in K(M)) r_(m,k)(u_k))_m
  $
  (Note: $cal(A)$ is a general abelian category and $U$ is an opaque object, so the formula above with elements of $U$ doesn't really make sense. Nevertheless $A_U$ is the unique morphism induced by $r_(m,k): U -> U$ on the respective direct summands.)

  We now define: 
  $
    Q: AMod(R) -> cal(A), M |-> coker(A_U\: U^(oplus K(M)) -> U^(oplus M))
  $
  $Q$ is a functor since the free resolution of $M$ is functorial. Now: 
  $
    Hom_(cal(A)) (Q(M), A) &= Hom_(cal(A)) (coker(A_U\: U^(oplus K(M)) -> U^(oplus M)), A) \
    &= ker(Hom_(cal(A)) (U^(oplus M), A) -> Hom_(cal(A)) (U^(oplus K(M)), A)) \
    // &= ker(product_M Hom(U, A) -> product_(K(M)) Hom(U, A)) \
    &= ker(G(A)^M -> G(A)^(K(M))) \
    &= ker(Hom_R (R^(oplus M), G(A)) -> Hom_R (R^(oplus K(M)), G(A)))\
    &= Hom_R (coker(R^(oplus K(M)) -> R^(oplus M)), G(A)) \
    &= Hom_R (M, G(A))
  $
  and so $Q$ is left adjoint to $G$. $Q$ is automatically right exact as a left adjoint. 

  - Note that: #h(1fr)
    $
      Hom_(cal(A)) (U^(oplus I), A) = G(A)^I = Hom_R (R^(oplus I), G(A))
    $
    Thus we have identifications $Q(R^(oplus I)) = U^(oplus I)$. 

  - We claim that if $i: M arrow.hook G(A)$ is injective, then the morphism $tilde(i): Q(M) arrow A$ induced by adjunction is injective. 

    Given any map $g: R^n -> M$, induce a map $Q(g): U^n -> Q(M)$ by applying $Q$ to it. Now any map $alpha: U -> U^n$ is defined by $n$ elements of $Hom_(cal(A)) (U, U) = R$, and is thus induced by some $a: R -> R^n$ via functoriality, i.e. $alpha = Q(a)$. Now we claim that: 
    $
      tilde(i) compose Q(g) compose Q(a) = 0 <==> Q(g) compose Q(a) = 0
    $
    We only need to prove $(==>)$. If $tilde(i) compose Q(g) compose Q(a) = 0$, then by adjunction $i compose g compose a: R -> M$ is zero. Since $i$ is injective, $g compose a = 0$ and so $Q(g) compose Q(a) = 0$. Thus for any map $alpha: U -> U^n$, $tilde(i) compose Q(g) compose alpha = 0 <==> Q(g) compose alpha = 0$. That is, 
    $
      Hom_(cal(A)) (U, ker(Q(g))) -> Hom_(cal(A)) (U, ker(tilde(i) compose Q(g)))
    $
    is an isomorphism. Since $U$ is a generator, $ker(Q(g)) = ker(tilde(i) compose Q(g))$. 

    Now pick any free resolution $h: R^(oplus I) -> M$. The above argument then says that for any finite subset $I' subset I$, $h_(I'): R^(oplus I')$ has: 
    $
      ker(Q(h_(I'))) = ker(tilde(i) compose Q(h_(I')))
    $
    Taking a directed limit over all finite $I' subset I$ and using (Ab5), we have: 
    $
      ker(Q(h)) = ker(tilde(i) compose Q(h))
    $
    Since $Q(h)$ is surjective (as $Q$ is right exact), this implies that $tilde(i)$ is injective. 

  Now by the claim applied to $id_(G(A))$, we see that the unit $eta_A: Q G (A) -> A$ is always injective. On the other hand, any map $U = Q(R) -> A$ can be regarded as an element of $G(A)$, and factors into $U = Q(R) -> Q G(A) -> A$, hence through $eta_A$. Thus the evaluation map $oplus.big_(phi in Hom_(cal(A)) (U,A)) U -> A$ factors through $eta_A$. The evaluation map is surjective, so $eta_A$ is surjective. Hence the counit $eta: Q G -> id$ is a natural isomorphism, or equivalently $G$ is fully faithful. 

  Finally we show that $Q$ is exact. It is already right exact, so it suffices to show that it respects injections. 

  - First suppose that we have an inclusion $K arrow.hook R^(oplus I) = G(U^(oplus I))$. The claim above then shows that $Q(K) -> Q(R^(oplus I)) = U^(oplus I)$ is injective. 

  - For a general inclusion $A arrow.hook B$ in $AMod(R)$, pick a free resolution $P -> B$ and form: 
    $
      L = ker(P -> B), K = A times_B P
    $
    We then have $L subset K subset P$ with identifications $A = K\/L, B = P\/L$. By right exactness of $Q$, 
    $
      Q(A) = Q(K)\/Q(L), Q(B) = Q(P)\/Q(L)
    $
    By the previous bullet, since $P$ is free, $Q(K) -> Q(P)$ is injective. Thus $Q(A) -> Q(B)$ is injective. 

  We are thereby done. 
]

#corollary(name: <gabriel-popescu-derived>)[
  Let $cal(A)$ be a Grothendieck abelian category. The functors $Q: AMod(R) arrows.rl cal(A): G$ defined in @gabriel-popescu pass to the unbounded derived categories: 
  $
    Q: D(R) arrows.rl D(cal(A)): R G
  $
  s.t. $Q$ is left adjoint to $R G$, and $R G$ is fully faithful. 
]
#proof[
  The Grothendieck abelian category $cal(A)$ has enough injectives. The rest is formal from @gabriel-popescu. 
]

Next, we give the bootstrapping compact case Brown representability theorem. 

#notation(name: <compact-objects-and-generators>)[
  In a triangulated category $cal(D)$, an object $G in cal(D)$ is called *compact* if $Hom_(cal(D)) (G, -): cal(D) -> cAb$ commutes with arbitrary direct sums. 

  A family of compact objects $cal(G) subset cal(D)$ is said to *generate* $cal(D)$, if: 

  - For any $X in cal(D)$, if for all $G in cal(G), n in ZZ$, #h(1fr)
    $
      Hom_(cal(D)) (G[n], X) = 0
    $
    then $X = 0$. 
]

#construction(name: <telescoping-construction>)[
  (Telescoping construction) In a triangulated category $cal(D)$ with arbitrary direct sums, suppose that we have a chain of maps $X_0 ->^(u_0) X_1 ->^(u_1) dots.c$. 

  Put $S = oplus.big_(n>=0) X_n$ with inclusions $i_n: X_n -> S$, and define a map $sigma: S -> S$ by sending $X_n -> X_(n+1)$ by $u_n$. In other words, 
  $
    sigma compose i_n = i_(n+1) compose u_n
  $
  Form a distinguished triangle: 
  $
    S -->^(1-sigma) S -->^q X_oo ->^(+1)
  $
  and set $j_n = q compose i_n: X_n -> X_oo$. Since $q compose (1 - sigma) = 0$, we have: 
  $
    j_n = q compose i_n = q compose sigma compose i_n = q compose i_(n+1) compose u_n = j_(n+1) compose u_n
  $
  Note that the choice of $X_oo$ is not canonical (i.e. unique up to unique isomorphism) as it is just an arbitrary cone for $1-sigma: S -> S$. It has the following property: 

  - For any (covariant) cohomological functor $F: cal(D) -> cal(A)$ (for some abelian category $cal(A)$) preserving direct sums, the morphisms $j_n: X_n -> X_oo$ induce an isomorphism: #h(1fr)
    $
      dirlim_(n>=0) F(X_n) cong F(X_oo)
    $
    Indeed, applying $F(-)$ to $S -->^(1-sigma) S -->^q X_oo ->^(+1)$ and using preservation of direct sums by $F$, we get a long exact sequence: 
    $
      & oplus.big_(n>=0) F(X_n) ->^D oplus.big_(n>=0) F(X_n) -> F(X_oo) -> oplus.big_(n>=0) F(X_n [1]) ->^(D') oplus.big_(n>=0) F(X_n [1])
    $
    where: 
    $
      D: oplus.big_(n>=0) F(X_n) -> oplus.big_(n>=0) F(X_n), (a_n)_n |-> (a_n - F(u_(n-1)) a_(n-1))_n \

      D': oplus.big_(n>=0) F(X_n [1]) -> oplus.big_(n>=0) F(X_n [1]), (a_n)_n |-> (a_n - F(u_(n-1) [1]) compose a_(n-1))_n
    $
    Both maps are injective. Indeed, if $(a_n)_n in ker(D)$, then: 
    $
      a_0 = 0 \
      a_n = F(u_(n-1)) a_(n-1), forall n>=1
    $
    and one can inductively show all $a_n = 0$. The same goes for $D'$. Now that $D'$ is injective, we have an identification: 
    $
      F(X_oo) cong coker(D\: oplus.big_(n>=0) F(X_n) -> oplus.big_(n>=0) F(X_n))
    $
    However by definition of $D$, this cokernel is exactly $dirlim_(n>=0) F(X_n)$. 

    In particular, for a compact object $G in cal(D)$, $Hom_(cal(D)) (G, X_oo) = dirlim_(n>=0) Hom_(cal(D)) (G, X_n)$. 

  - There is a dual statement: For any contravariant cohomological functor $H: cal(D)^opp -> cal(A)$ sending direct sums to direct products, 
    $
      H(X_oo) -> invlim_(n>=0) H(X_n) 
    $
    is surjective. 

    Indeed, apply $H$ to $S -->^(1-sigma) S -->^q X_oo ->^(+1)$ gives the exactness of: 
    $
      H(X_oo) -> product_(n>=0) H(X_n) ->^D product_(n>=0) H(X_n)
    $
    where: 
    $
      D: product_(n>=0) H(X_n) -> product_(n>=0) H(X_n), (a_n)_n |-> (a_n - H(u_(n+1)) a_(n+1))_n
    $
    By definition $invlim_(n>=0) H(X_n) = ker(D)$, so we have a surjection $H(X_oo) -> invlim_(n>=0) H(X_n)$. 
]

#lemma(name: <cpct-generation-of-triangulated-cat>)[
  Let $cal(D)$ be a triangulated category with arbitrary direct sums, and a family of compact objects $cal(G)$ generating $cal(D)$. Then the only triangulated subcategory $cal(E)$ of $cal(D)$ containing $cal(G)$ and closed under arbitrary direct sums is $cal(D)$ itself. 
]
#proof[
  We may replace $cal(G)$ by the set of all shifts of elements of $cal(G)$ and assume that it is closed under shifts. 
  
  We inductively define a chain $P_0 ->^(u_0) P_1 -> dots.c$. 
  
  - For any $X in cal(D)$, let: #h(1fr)
    $
      P_0 = oplus.big_(G in cal(G) \ h: G -> X) G
    $
    with evaluation map $p_0: P_0 -> X$. 

  - Suppose that $p_n: P_n -> X$ is already defined. Let:
    $
      Q_n = oplus.big_(G in cal(G) \ h: G -> P_n, p_n compose h = 0) G
    $
    with evaluation $e_n: Q_n -> P_n$ (that by definition has $p_n compose e_n = 0$). Complete to a distinguished triangle: 
    $
      Q_n -->^(e_n) P_n -->^(u_n) P_(n+1) ->^(+1)
    $

    Note that exactness of $Hom_(cal(D)) (P_(n+1), X) -> Hom_(cal(D)) (P_n, X) -> Hom_(cal(D)) (Q_n, X)$ and that $u_n compose e_n = 0$ gives a lift $p_(n+1): P_(n+1) -> X$ s.t. $p_(n+1) compose u_n = p_n$. 

  We now form the telescope $S_P = oplus.big_(n>=0) P_n -->^(1-sigma) S_P -->^q P_oo$ of $P_0 ->^(u_0) P_1 ->^(u_1) -> dots.c$ and put $j_n: P_n -> P_oo$. Then since $Hom_(cal(D)) (-, X)$ is a contravariant cohomological functor sending direct sums to direct products: 
  $
    Hom_(cal(D)) (P_oo, X) -> invlim_(n>=0) Hom_(cal(D)) (P_n, X)
  $
  is surjective. Thus there exists $p_oo: P_oo -> X$ s.t. $p_n = p_oo compose j_n$. 

  We claim that for all $G in cal(G)$, 
  $
    Hom_(cal(D)) (G, p_oo): Hom_(cal(D)) (G, P_oo) -> Hom_(cal(D)) (G, X)
  $
  is bijective. It is surjective, because it factors through $Hom_(cal(D)) (G, P_0) -> Hom_(cal(D)) (G, X)$ which is by definition surjective. This map is injective: Since $G$ is compact, $Hom_(cal(D)) (G, P_oo) cong dirlim_(n>=0) Hom_(cal(D)) (G, P_n)$ so we need to show that: 
  $
    dirlim_(n>=0) Hom_(cal(D)) (G, P_n) -> Hom_(cal(D)) (G, X)
  $
  is injective. Indeed, for any $h in Hom_(cal(D)) (G, P_n)$ in this kernel of this map, $p_n compose h = 0$, and so $h$ indexes a direct summand of $Q_n$. Subsequently $h: G -> P_n$ factors through $e_n: Q_n -> P_n$, and so $u_n compose h = 0$. That is, $h$ becomes $0$ in the next stage of the direct limit $dirlim_(n>=0) Hom_(cal(D)) (G, P_n)$. We have thus shown injectivity. 

  Now that we have shown that $Hom_(cal(D)) (G, P_oo) -> Hom_(cal(D)) (G, X)$ is an isomorphism, we may form the cone $P_oo -->^(p_oo) X -> C ->^(+1)$. Then: 
  $
    Hom_(cal(D)) (G, C) = 0
  $
  for all $G in cal(G)$, and so $C = 0$. Thus $p_oo$ is an isomorphism. It remains to show that $P_oo in cal(E)$. 

  Indeed: 

  - $P_0 in cal(E)$ and every $Q_n in cal(E)$, since they are direct sums of objects of $cal(G)$, and $cal(E)$ contains $cal(G)$ and is closed under arbitrary direct sums. 

  - The distinguished triangle $Q_n -> P_n -> P_(n+1) ->^(+1)$ then inductively shows that every $P_n in cal(E)$. 

  - Thus $S_P = oplus.big_(n>=0) P_n in cal(E)$ by closure under direct sums, and $P_oo in cal(E)$ by the triangle $S_P -->^(1-sigma) S_P -> P_oo ->^(+1)$. 

  We are thereby done. 
]

#lemma(name: <ptwise-brown-representability-cpct-case>)[
  (Pointwise Brown representability in compact case) Let $cal(D)$ be a triangulated category with arbitrary direct sums, and a family of compact objects $cal(G)$ generating $cal(D)$. Let $H: cal(D)^opp -> cAb$ be a contravariant cohomological functor sending direct sums to direct products. Then $H$ is representable. 
]
#proof[
  We may replace $cal(G)$ with its completion under shifts and assume that $cal(G)$ is closed under shifts. 

  An element $a in H(X)$ defines a natural transformation: 
  $
    theta_Y^a: Hom_(cal(D)) (Y, X) -> H(Y), f |-> H(f) a
  $
  We construct $X in cal(D)$ and $a in H(X)$ s.t. this $theta^a$ is a natural isomorphism. Take: 
  $
    X_0 = oplus.big_(G in cal(G) \ x in H(G)) G
  $
  Since $H$ sends direct sums to direct products, $H(X_0) = product_(G in cal(G) \ x in H(G)) H(G)$, and so we may take $a_0 = (x)_(G,x) in H(X_0)$. Then for any $G in cal(G)$ the map: 
  $
    theta_G^(a_0): Hom_(cal(D))(G, X_0) -> H(G)
  $
  is surjective by definition, since every element $x in H(G)$ is obtained from $a_0$ by projecting to the factor corresponding to $(G,x)$. 

  Suppose that we have constructed $X_n in cal(D), a_n in H(X_n)$. Then take: 
  $
    K_n = oplus.big_(G in cal(G) \ k: G -> X_n, H(k)a_n = 0) G
  $
  and let $r_n: K_n -> X_n$ be the map that is exactly $k: G -> X_n$ on the direct summand indexed by $k$. Then by definition, $H(r_n) a_n = 0 in H(K_n)$, as: 
  $
    H(K_n) = product_(G in cal(G) \ k:G -> X_n, H(k)a_n = 0) H(G)
  $
  and $H(r_n) a_n = (H(k)a_n)_(G,k) = 0$. Form the distinguished triangle: 
  $
    K_n -->^(r_n) X_n -->^(u_n) X_(n+1) ->^(+1)
  $
  Since $H$ is cohomological, $H(X_(n+1)) -> H(X_n) -> H(K_n)$ is exact. Since $H(r_n) a_n = 0$, there exists $a_(n+1) in H(X_(n+1))$ s.t. $a_n = H(u_n) a_(n+1)$. 
  
  Now form the telescope $X_oo$ of $X_0 ->^(u_0) X_1 ->^(u_1) dots.c$ with maps $j_n: X_n -> X_oo$. Then since $H$ sends direct sums to direct products, 
  $
    H(X_oo) -> invlim_(n>=0) H(X_n)
  $
  is surjective. Thus there exists $a_oo in H(X_oo)$ s.t. $a_n = H(j_n) a_oo$ for all $n$. Now we claim that: 
  $
    theta^(a_oo)_G: Hom_(cal(D)) (G, X_oo) -> H(G)
  $
  is bijective. 

  - It is surjective since it factors through $theta^(a_0)_G: Hom_(cal(D)) (G, X_0) -> H(G)$, which is surjective as we have shown. 

  - It is injective: Suppose that $f in Hom_(cal(D)) (G, X_oo)$ has $H(f)a_oo = 0$. Since $G$ is compact, 
    $
      Hom_(cal(D)) (G, X_oo) = dirlim_(n>=0) Hom_(cal(D)) (G, X_n)
    $
    and there exists $f_n: G -> X_n$ s.t. $f = j_n compose f_n$. Thus, 
    $
      H(f_n) a_n = H(f_n) H(j_n) a_oo = 0
    $
  Hence $(G, f_n)$ indexes a direct summand in $K_n$. Thus $f_n: G -> X_n$ factors through $r_n: K_n -> X_n$, and so $u_n compose f_n = 0$. Hence, 
    $
      f = j_n compose f_n = j_(n+1) compose u_n compose f_n = 0
    $
    and we are done. 

  Now let $cal(P)$ be the full subcategory of $cal(D)$ with objects: 
  $
    cal(P) = {Y in cal(D): theta^(a_oo)_Y: Hom_(cal(D)) (Y, X_oo) -> H(Y) #[is an isomorphism]}
  $
  Since $Hom_(cal(D)) (-, X_oo)$ and $H$ are both triangulated functors, $cal(P)$ is closed under shifts and distinguished triangles. Since $Hom_(cal(D)) (-, X_oo)$ and $H$ both send direct sums to direct products, $cal(P)$ is closed under arbitrary direct sums. Finally, $cal(G) subset cal(P)$ as we have proved. Thus by @cpct-generation-of-triangulated-cat, $cal(P) = cal(D)$. 

  Thus $theta^(a_oo)$ gives a natural isomorphism $H cong Hom_(cal(D)) (-, X_oo)$, thus representing $H$ with $X_oo in cal(D)$. 
]

#lemma(name: <ptwise-brown-representability>)[
  (Pointwise Brown representability) Let $cal(A)$ be a Grothendieck abelian category. Let $H: D(cal(A))^opp -> cAb$ be a contravariant cohomological functor sending direct sums to direct products. Then $H$ is representable. 
]
#proof[
  By @gabriel-popescu-derived, we may pick a non-commutative ring $R$ and a pair of triangulated adjoint functors: 
  $
    Q: D(R) -> D(cal(A)): G
  $
  where $G$ is fully faithful (i.e. the counit $eta: Q G -> id$ is a natural isomorphism). 

  Consider the functor $H compose Q: D(R)^opp -> cAb$. Since $Q$ is a left adjoint, it preserves direct sums. Thus $H compose Q$ sends direct sums to direct products too. Furthermore, the triangulated category $D(R)$ is generated by the compact objects ${R[n]}_(n in ZZ)$. Thus by @ptwise-brown-representability-cpct-case, $H compose Q$ is representable, i.e. there exists an object $L in D(R)$ and a natural isomorphism: 
  $
    H(Q(C)) cong Hom_(D(R)) (C, L)
  $
  Take the unit map $u_L: L -> G Q(L)$ and form the cone: 
  $
    M -> L ->^(u_L) G Q(L) ->^(+1)
  $
  Note that $Q(u_L): Q(L) -> Q G Q(L)$ is an isomorphism by an adjunction identity. Thus applying $Q$ to the distinguished triangle above, we see that $Q(M) = 0$, and so $Hom_(D(R)) (M, L) cong H(Q(M)) = 0$. Hence, applying $Hom_(D(R)) (-, L)$ to the distinguished triangle above, we have a surjection: 
  $
    Hom_(D(R)) (G Q(L), L) ->> Hom_(D(R)) (L, L)
  $
  Take $r_L: G Q(L) -> L$ sent to $id_L$ under this morphism, and we see that $r_L compose u_L = id_L$, i.e. $r_L$ is a retract of $L$. 

  By fully faithfulness of $G$, we now have a retract: 
  $
    H(A) cong H(Q G (A)) cong Hom_(D(R)) (G(A), L) \
    ->^(u_L compose -) Hom_(D(R)) (G(A), G Q(L)) cong Hom_(D(cal(A))) (A, Q(L))
  $
  Now $u_L compose -$ has a left inverse $r_L compose -$. Therefore, $H$ is a direct summand of $Hom_(D(cal(A))) (-, Q(L))$, a representable functor. 

  - Note that $D(cal(A))$ is idempotent complete, meaning every idempotent $e: X -> X$ in $D(cal(A))$ splits as $e: X ->^f Y ->^g X$ s.t. $f compose g = id_Y$.

    Indeed, form the telescope $Y$ of the chain $X ->^e X ->^e -> dots.c$. This is a cone: 
    $
      oplus.big_(n>=0) X ->^(1-sigma) oplus.big_(n>=0) X ->^q Y ->^(+1)
    $
    where $sigma((x_n)_n) = (e x_(n-1))_n$. 

    Put $ell: oplus.big_(n>=0) X -> oplus.big_(n>=0) X, (x_n)_n |-> (x_n - sum_(k>=n) e x_k)_n$. Then: 
    $
      ell(1-sigma)((x_n)_n) = ell((x_n - e x_(n-1))_n) = ((x_n - e x_(n-1)) - sum_(k>=n) (e x_k - e x_(k-1)))_n = (x_n)_n
    $
    Thus $ell$ is a left inverse to $1 - sigma$. Now that $1 - sigma$ has a left inverse, the triangle above is a split triangle, i.e. the $+1$ map $Y -> oplus.big_(n>=0) X[1]$ is zero, and $q$ has a right inverse. Thus we have a short exact sequence: 
    $
      0 -> Hom_(D(cal(A))) (Y, X) -> product_(n>=0) Hom_(D(cal(A))) (X, X) -> product_(n>=0) Hom_(D(cal(A))) (X, X) -> 0
    $
    Put $r: oplus.big_(n>=0) X -> X$ by $(x_n)_n |-> sum_(n>=0) e x_n$. Then $r = r compose sigma$, so $r compose (1-sigma) = 0$. Thus there exists $g: Y -> X$ s.t. $g compose q = r$. 

    Let $i_n: X -> oplus.big_(n>=0) X$ be inclusion into $n$-th direct summand. Then put $f = q compose i_0: X -> Y$. Now: 
    $
      g compose f = g compose q compose i_0 = r compose i_0 = e
    $
    and: 
    $
      f compose g compose q = f compose r
    $
    - Since $q = q compose sigma$, composing with $i_n$ gives $q compose i_n = q compose i_(n+1) compose e$. Right compose with $e$ and using idempotence, we have $q compose i_n compose e = q compose i_(n+1) compose e = q compose i_n$, and so: 
      $
        q compose i_n = q compose i_(n+1)
      $
      Thus $f = q compose i_n$ for all $n$ and $f = f compose e$. Now: 
      $
        f compose r compose i_n = f compose e = f = q compose i_n
      $
      for all $n$, and so $f compose r = q$
    Thus $f compose g compose q = q$. Since $q$ has a right inverse, $f compose g = id$. We have thus split the idempotent $e$.

  Since $H$ is a direct summand of $Hom_(D(cal(A))) (-, Q(L))$, it corresponds to an idempotent of $Q(L)$, factoring as $Q(L) ->^f T ->^g Q(L)$ with $f compose g = id$. Then $T$ represents $H$. 
]

#theorem(name: <brown-representability>)[
  (Brown representability) Let $cal(A)$ be a Grothendieck abelian category. Then any triangulated functor $D(cal(A)) -> cal(D)$ that preserves arbitrary direct sums must have a triangulated right adjoint. 
]
#proof[
  Let $F: D(cal(A)) -> cal(D)$ be a triangulated functor preserving arbitrary direct sums. For every $X in cal(D)$, the functor $Hom_(cal(D)) (F(-), X)$ sends direct sums to direct products. By @ptwise-brown-representability, each $Hom_(cal(D)) (F(-), X)$ is representable. Thus $F$ has an additive right adjoint: 
  $
    G: cal(D) -> D(cal(A))
  $
  It remains to show that $G$ is triangulated. By adjunction $G$ preserves all shifts. 

  Let $A ->^f B ->^g C ->^u_(+1)$ be a distinguished triangle in $cal(D)$, and form a distinguished triangle: 
  $
    G(A) ->^(G(f)) G(B) -> X ->^(+1)
  $
  Now $F G(A) -> F G(B) -> F(X) ->^(+1)$ is a distinguished triangle. Thus by the triangular axioms, there is a map $phi: F(X) -> C$ making the following diagram commute: 
  // https://q.uiver.app/#r=typst&q=WzAsOCxbMCwwLCJGIEcoQSkiXSxbMCwxLCJBIl0sWzEsMCwiRiBHKEIpIl0sWzIsMCwiRihYKSJdLFszLDAsIkYgRyhBKVsxXSJdLFsxLDEsIkIiXSxbMiwxLCJDIl0sWzMsMSwiQVsxXSJdLFszLDRdLFswLDJdLFsyLDNdLFsxLDUsImYiLDJdLFs1LDYsImciLDJdLFs2LDcsInUiLDJdLFswLDEsImV0YV9BIiwyXSxbMiw1LCJldGFfQiJdLFszLDYsInBoaSJdLFs0LDcsImV0YV9BIFsxXSJdXQ==
  #align(center, diagram({
    node((0, 0), [$F G(A)$])
    node((0, 1), [$A$])
    node((1, 0), [$F G(B)$])
    node((2, 0), [$F(X)$])
    node((3, 0), [$F G(A)[1]$])
    node((1, 1), [$B$])
    node((2, 1), [$C$])
    node((3, 1), [$A[1]$])
    edge((2, 0), (3, 0), "->")
    edge((0, 0), (1, 0), "->")
    edge((1, 0), (2, 0), "->")
    edge((0, 1), (1, 1), [$f$], label-side: right, "->")
    edge((1, 1), (2, 1), [$g$], label-side: right, "->")
    edge((2, 1), (3, 1), [$u$], label-side: right, "->")
    edge((0, 0), (0, 1), [$eta_A$], label-side: right, "->")
    edge((1, 0), (1, 1), [$eta_B$], label-side: left, "->")
    edge((2, 0), (2, 1), [$phi$], label-side: left, "->")
    edge((3, 0), (3, 1), [$eta_A [1]$], label-side: left, "->")
  }))
  By adjunction, we have a commutative diagram: 
  // https://q.uiver.app/#r=typst&q=WzAsOCxbMCwwLCJHKEEpIl0sWzAsMSwiRyhBKSJdLFsxLDAsIkcoQikiXSxbMiwwLCJYIl0sWzMsMCwiRyhBKVsxXSJdLFsxLDEsIkcoQikiXSxbMiwxLCJHKEMpIl0sWzMsMSwiRyhBWzFdKSJdLFszLDRdLFswLDIsIkcoZikiXSxbMiwzXSxbMSw1LCJHKGYpIiwyXSxbNSw2LCJHKGcpIiwyXSxbNiw3LCJ1IiwyXSxbMiw1LCIiLDAseyJzdHlsZSI6eyJib2R5Ijp7Im5hbWUiOiJkb3VibGUgYmFycmVkIn19fV0sWzMsNiwicHNpIl0sWzQsNywidGlsZGUiXSxbMCwxLCIiLDIseyJzdHlsZSI6eyJib2R5Ijp7Im5hbWUiOiJkb3VibGUgYmFycmVkIn19fV1d
  #align(center, diagram({
    node((0, 0), [$G(A)$])
    node((0, 1), [$G(A)$])
    node((1, 0), [$G(B)$])
    node((2, 0), [$X$])
    node((3, 0), [$G(A)[1]$])
    node((1, 1), [$G(B)$])
    node((2, 1), [$G(C)$])
    node((3, 1), [$G(A[1])$])
    edge((2, 0), (3, 0), "->")
    edge((0, 0), (1, 0), [$G(f)$], label-side: left, "->")
    edge((1, 0), (2, 0), "->")
    edge((0, 1), (1, 1), [$G(f)$], label-side: right, "->")
    edge((1, 1), (2, 1), [$G(g)$], label-side: right, "->")
    edge((2, 1), (3, 1), [$u$], label-side: right, "->")
    edge((1, 0), (1, 1), "=")
    edge((2, 0), (2, 1), [$psi$], label-side: left, "->")
    edge((3, 0), (3, 1), [$tilde$], label-side: left, "->")
    edge((0, 0), (0, 1), "=")
  }))
  By construction of the isomorphism $G(A)[1] cong G(A[1])$ from adjunctions, this passes to a morphism of triangles: 
  #align(center, diagram({
    node((0, 0), [$G(A)$])
    node((0, 1), [$G(A)$])
    node((1, 0), [$G(B)$])
    node((2, 0), [$X$])
    node((3, 0), [$G(A)[1]$])
    node((1, 1), [$G(B)$])
    node((2, 1), [$G(C)$])
    node((3, 1), [$G(A[1])$])
    edge((2, 0), (3, 0), "->")
    edge((0, 0), (1, 0), [$G(f)$], label-side: left, "->")
    edge((1, 0), (2, 0), "->")
    edge((0, 1), (1, 1), [$G(f)$], label-side: right, "->")
    edge((1, 1), (2, 1), [$G(g)$], label-side: right, "->")
    edge((2, 1), (3, 1), [$u$], label-side: right, "->")
    edge((1, 0), (1, 1), "=")
    edge((2, 0), (2, 1), [$psi$], label-side: left, "->")
    edge((3, 0), (3, 1), label-side: left, "=")
    edge((0, 0), (0, 1), "=")
  }))
  For any $W in D(cal(A))$, apply $Hom_(D(cal(A))) (W, -)$ and use the five lemma to see that $Hom_(D(cal(A))) (W, X) -> Hom_(D(cal(A))) (W, G(C))$ is an isomorphism. By Yoneda, $psi$ is an isomorphism. Thus $G(A) -> G(B) -> G(C) ->^(+1)$ is isomorphic to a distinguished triangle, hence distinguished. 
]
