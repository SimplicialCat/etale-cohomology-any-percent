#import "void-import.typ": *

== Smooth base change

The core arguments of this section come from @cite-deligne-arcata.

In this section, we incorporate the reductions and discussions on local acyclicity done in previous sections, to prove the smooth base change theorem. The main theorem of this section is: 

- Smooth morphisms are universally locally acyclic. 

We first perform some reductions. 

#notation[
  Let $(A, frak(m))$ be a strict henselian local ring. Then the notation $A{T}$ denotes the local ring: 
  $
    A{T} := A[T]_((frak(m),T))^#[h] = A[T]_((frak(m),T))^#[sh]
  $
]

#lemma(name: <loc-acyc-of-smooth-maps-reductions>)[
  Smooth morphisms are universally locally acyclic, assuming the following condition: 

  - For any $A$ obtained as the strict henselization of a normal finite type $ZZ$-algebra at a prime with $K = Frac(A)$, #h(1fr)
    $
      H^0 (Spec(ol(K) otimes_A A{T}), ul(ZZ\/n)) = ZZ\/n \
      H^1 (Spec(ol(K) otimes_A A{T}), ul(ZZ\/n)) = 0
    $
    for any natural number $n in A^times$. 
]
#proof[
  Local acyclicity is etale local on both source and target. Thus, it suffices to show that every $AA^d_S -> S$ is locally acyclic, since any smooth morphism $X -> S$ Zariski locally factors as $X ->^j AA^d_S -> S$ with $j$ etale. 

  Thus, it suffices to show that every $AA^d_(ZZ[n^(-1)]) -> Spec(ZZ[n^(-1)])$ is universally locally acyclic relative to $ul(ZZ\/n)$. By @loc-acyc-and-base-change, it suffices to show that: 

  - For every $A$ being the normalization of an integral finite type $ZZ[n^(-1)]$-algebra $A_0$ in the algebraic closure of its field of fractions, $AA^d_A -> Spec(A)$ is locally acyclic relative to $ul(ZZ\/n)$. 

  By @loc-acyc-and-limits-of-qfinite, if $AA^d_(A_0) -> Spec(A_0)$ is locally acyclic, then local acyclicity lifts along the integral base change $Spec(A) -> Spec(A_0)$, yielding local acyclicity of $AA^d_A -> Spec(A)$. Now $A_0$ is finite type over $ZZ$ and in particular noetherian, so @loc-acyc-compose may be invoked. Thus it suffices to show that: 

  - For every integral finite type $ZZ[n^(-1)]$-algebra $A_0$, $AA^1_(A_0) -> Spec(A_0)$ is locally acyclic relative to $ul(ZZ\/n)$. 

  For this it suffices to show that $AA^1_(ZZ[n^(-1)]) -> Spec(ZZ[n^(-1)])$ is universally locally acyclic relative to $ul(ZZ\/n)$. Invoking @loc-acyc-and-base-change again, it suffices to show that: 

  - For every $X = Spec(A)$ being the normalization of an affine integral finite type $ZZ[n^(-1)]$-scheme $Spec(A_0)$ in the algebraic closure of its function field $K$, with generic point $xi$, 
    $
      R Gamma(F_(ol(x'),xi), ul(ZZ\/n)) cong ZZ\/n
    $
    for a family of geometric points ${ol(x')}$ above a very dense subset of $AA^1_X$. 

  By @integral-normal-affine-with-ac-func-field, the local rings of $X$ are strict henselian with algebraically closed function field. Consider the following subset: 
  $
    E = {x' in AA^1_X : #[$x'$ lies above $x in X$ and is a closed point in the fiber $AA^1_(k(x))$]}
  $
  The closed points of each $AA^1_(k(x))$ are very dense. Thus, every nonempty locally closed subset of $AA^1_X$ must intersect some fiber $AA^1_(k(x))$ in a nonempty locally closed subset, hence contain a closed point. This shows that $E subset AA^1_X$ is very dense. We thus choose ${ol(x')}$ to be the family of algebraic geometric points above points of $E$. 
  
  Let $x in X = Spec(A)$ correspond to a prime $frak(p)$, and let $x' in E$ above $x$ be represented by a coordinate $[u] in k(x) = A_(frak(p))\/frak(p) A_(frak(p))$. $[u]$ is represented by an element $u in A_(frak(p))$, hence an element $u in A_f$ for some $f in A - frak(p)$. Now $F_(ol(x'),xi)$ is insensitive to shrinking both source and target. Thus, we may base change along $Spec(A_f) -> Spec(A)$ and assume that $u in A$. Then $x'$ is represented by the prime ideal $(frak(p), T - u) subset A[T]$. By the coordinate change $A[T] -> A[T], T |-> T + u$, we may thus assume that $x' in AA^1_A = Spec(A[T])$ is represented by the prime ideal $(frak(p), T)$. Thus, 
  $
    F_(ol(x'),xi) = Spec(K otimes_(A_(frak(p))) A_(frak(p)) {T})
  $
  and so it suffices to prove that: 
  $
    R Gamma(Spec(K otimes_(A_(frak(p))) A_(frak(p)) {T}), ul(ZZ\/n)) = ZZ\/n
  $
  Thus, it remains to show that: 

  - If $A$ is a strict henselian normal local domain with algebraically closed function field $K$, obtained as a local ring of the normalization of an integral finite type $ZZ$-algebra in the algebraic closure of its fraction field, with $n in A^times$, then: 
    $
      R Gamma(Spec(K otimes_A A{T}), ul(ZZ\/n)) = ZZ\/n
    $

  We proceed with another limit argument. 
  
  - Write $A = dirlim_lambda A_lambda^((1))$ as a limit of its finite type $ZZ[n^(-1)]$-algebras. 
  
  - Each $A_lambda^((1))$ is necessarily integral, so we may take its normalization $A_lambda^((2))$. Since $A_lambda^((1))$ is finite type over $ZZ$, $A_lambda^((2))$ is finite over it and remains finite type over $ZZ$. Since $A$ is normal, $A_lambda^((2))$ is a subalgebra of $A$ containing $A_lambda^((1))$. Thus we have: 
    $
      A = dirlim_lambda A_lambda^((2))
    $

  - Let $frak(q)_lambda in Spec(A_lambda^((2)))$ be the image of $frak(m)_A$, and put $A_lambda^((3)) = (A_lambda^((2)))_(frak(q)_lambda)$. Every element of $A_lambda^((2)) - frak(q)_lambda$ is in $A - frak(m) = A^times$, so each $(A_lambda^((2)))_(frak(q)_lambda)$ is a subalgebra of $A$. Thus we have: 
    $
      A = dirlim_lambda A_lambda^((3))
    $

  - Finally take $A_lambda = (A_lambda^((3)))^#[sh]$. Since strict henselization commutes with directed limits (@henselization-and-directed-limits), 
    $
      A = A^#[sh] = dirlim_lambda (A_lambda^((3)))^#[sh] = dirlim_lambda A_lambda
    $
    where each $A_lambda$ is the strict henselization of an integral normal finite type $ZZ[n^(-1)]$-algebra at a prime. 
    
  - Each $A_lambda -> A$ is injective by @inverting-nonzeros-in-henselization (2). Thus $A$ is the union of its subalgebras $A_lambda$, and: 
    $
      K = Frac(A) = dirlim_lambda Frac(A_lambda)
    $
    Now $K = Frac(A)$ is the algebraic closure of the fraction field of an integral finite type $ZZ$-algebra. It is thus of finite transcendence degree over $QQ$ or $FF_p$. Pick a transcendence basis $u_1, dots.c, u_t in K$ of $K$ over $QQ$ or $FF_p$, and there is a finite stage $lambda_0$ s.t. $u_1, dots.c, u_t in Frac(A_lambda)$. Truncate the directed system to $lambda >= lambda_0$, and so we may assume that $K\/Frac(A_lambda)$ is algebraic. Since $K$ is algebraically closed, $K = ol(Frac(A_lambda))$. 

  Thus, 
  $
    Frac(A) otimes_A A{T} &= Frac(A) otimes_(dirlim_lambda A_lambda) (dirlim_lambda A_lambda {T}) = dirlim_lambda Frac(A) otimes_(A_lambda) A_lambda {T} \
    &= dirlim_lambda ol(Frac(A_lambda)) otimes_(A_lambda) A_lambda {T}
  $
  and so: 
  $
    H^q (Spec(K otimes_A A{T}), ul(ZZ\/n)) = dirlim_lambda H^q (Spec(ol(Frac(A_lambda)) otimes_(A_lambda) A_lambda {T}), ul(ZZ\/n))
  $
  Thus, if we can show that each $R Gamma(Spec(ol(Frac(A_lambda)) otimes_(A_lambda) A_lambda {T}), ul(ZZ\/n)) = ZZ\/n$, then $R Gamma(Frac(A) otimes_A A{T}, ul(ZZ\/n)) = ZZ\/n$ and we are done. Hence, it suffices to show that: 

  - For $A$ the strict henselization of a finite type $ZZ[n^(-1)]$-algebra at a prime with $K = Frac(A)$, #h(1fr)
    $
      H^q (Spec(ol(K) otimes_A A{T}), ul(ZZ\/n)) = cases(
        ZZ\/n &\, q = 0, 
        0 &\, q >= 1
      )
    $

  // Now $A{T}$ is a normal local domain, so $K otimes_A A{T}$, being one of its localizations, is integral. Thus $Spec(K otimes_A A{T})$ is integral and so connected, and: 
  // $
  //   H^0 (Spec(ol(K) otimes_A A{T}), ul(ZZ\/n)) = ZZ\/n
  // $ 
  // Now the case $q = 1$ is the hypothesis, so it suffices to deal with the case $q = 2$. However, 
  The case $q = 0,1$ is the hypothesis. For $q >= 2$, $A{T}$ is a directed limit of etale $A[T]$-algebras. Thus, $ol(K) otimes_A A{T}$ is a directed limit of etale $ol(K)[T]$-algebras $B_lambda$. Then: 
  $
    H^q (Spec(ol(K) otimes_A A{T}), ul(ZZ\/n)) = dirlim_lambda H^q (Spec(B_lambda), ul(ZZ\/n))
  $
  Each $B_lambda$ is finite type over $ol(K)$ of dimension $<=1$. Thus by Artin vanishing (@artin-vanishing), every term in the limit on RHS vanishes as $q >= 2$. Thus $H^q (Spec(ol(K) otimes_A A{T}), ul(ZZ\/n)) = 0$. We are thereby done. 
]

We now start computing the desired $H^0$ and $H^1$, which boils down to connected components and finite etale coverings. 

#lemma(name: <a-braces-t-and-normalization-in-fin-sep-ext>)[
  Let $A$ be a noetherian strict henselian normal local domain with $K = Frac(A)$. Then for any finite separable extension $L\/K$, the normalization $B$ of $A$ in $L$ is finite over $A$ and remains a noetherian strict henselian normal local domain. Furthermore, 
  $
    B otimes_A A{T} cong B{T}
  $
]
#proof[
  That $B$ is finite over $A$ is due to an elementary fact that the normalization of any normal domain in a finite separable extension of its fraction field remains finite (#cite-stacks("032L")[Lemma 10.161.8]). $B$ is by definition normal, and noetherian for being finite over the noetherian ring $A$. 
  
  Since $B$ is finite over $A$, by @finite-over-henselian-is-henselian, $B$ is a product of strict henselian local $A$-algebras. However $B$ is integral, so it has to be strict henselian local itself. 

  Finally, by @strict-henselizations-tensors-and-qfinites, since $B$ is finite over $A$ and $B[T] = B otimes_A A[T]$, 
  $
    B{T} = B[T]_((frak(m)_B,T))^#[sh] = B^#[sh] otimes_(A^#[sh]) A[T]_((frak(m)_A,T))^#[sh] = B otimes_A A{T}
  $
]

We are now ready to tackle the $H^0$ case. 

#proposition(name: <sbc-core-h0>)[
  Let $A$ be a noetherian strict henselian normal local domain with $K = Frac(A)$. Then $Spec(ol(K) otimes_A A{T})$ is connected, i.e: 
  $
    H^0 (Spec(ol(K) otimes_A A{T}), ul(ZZ\/n)) = ZZ\/n
  $
]
#proof[
  For every finite separable extension $L\/K$, let $B$ be the normalization of $A$ in $L$. By @a-braces-t-and-normalization-in-fin-sep-ext, $B$ is a noetherian strict henselian normal domain, and: 
  $
    L otimes_A A{T} = L otimes_B B otimes_A A{T} cong L otimes_B B{T}
  $
  Now $B{T}$ is a normal local domain. Thus, $L otimes_B B{T}$, being $B{T}$ with the elements of $B - {0}$ inverted, must remain integral and so connected. Thus: 
  $
    H^0 (Spec(K^sep otimes_A A{T}), ul(ZZ\/n)) &= dirlim_(L\/K #[finite separable]) H^0 (Spec(L otimes_A A{T}), ul(ZZ\/n)) \
    &= dirlim_(L\/K #[finite separable]) ZZ\/n = ZZ\/n
  $
  By topological invariance, we may replace $K^sep$ with $ol(K)$ and conclude the proof. 
]

The $H^1$ case is a lot more involved, and requires a special case of the so-called Abhyankar's lemma. The core algebraic engine behind all of this is the following lemma: 

#lemma(name: <normal-hartogs>)[
  (Normal Hartogs; @cite-matsumura-ca[Theorem 38]) Let $A$ be a normal noetherian domain. Then in $Frac(A)$,
  $
    A = inter.big_(frak(p) in Spec(A) \ "ht"(frak(p)) = 1) A_(frak(p))
  $
]

We now develop some algebraic engine to spread the finite etale covering on the generic fiber to a codimension $>=2$ open subset.  

#lemma(name: <zariski-nagata-purity-in-dim-2>)[
  (Zariski-Nagata purity in dimension $2$) Let $(A, frak(m))$ be a regular local domain of dimension $2$, with an inclusion $A arrow.hook B$ for $B$ a normal finite $A$-algebra. 
  
  If $B$ is etale over the punctured spectrum $Spec(A) - {frak(m)}$, then it is etale over $A$. 
]
#proof[
  Since $A subset B$ with $A$ normal and $B$ finite over $A$, going down holds for $A -> B$ (by @cite-atiyah-macdonald[Theorem 5.16]). Now the first step is to prove that $B$ is finite free over $A$.

  - We claim that if $z in Frac(B)$ and $frak(m) z subset B$, then $z in B$. 
  
    Indeed, for any height $1$ prime $frak(q) in Spec(B)$, by going down, $frak(p) = frak(q) inter A$ has height $<=1$. Thus $frak(p) != frak(m)$ and we may pick $a in frak(m) - frak(p)$. Now $a z in B$ and $a in B_(frak(q))^times$, so $z in B_(frak(q))$. Thus, 
    $
      z in inter.big_(frak(q) in Spec(B) \ "ht"(frak(q)) = 1) B_(frak(q)) = B
    $
    by @normal-hartogs. 

  Choose a regular system of parameters $frak(m) = (x, y)$. Now: 

  - Multiplication of $y$ on $B\/x B$ is injective. Indeed, suppose that $b_1, b_2 in B$ has $b_1 y = b_2 x$. Then: #h(1fr)
    $
      z = b_1/x = b_2/y in Frac(B)
    $
    has $x z, y z in B$, so $frak(m) z subset B$. By the previous bullet, $z in B$. Thus $x divides b_1$, so $[b_1] = 0 in B\/x B$. 

  Now $A\/x A$ is a regular local ring of dimension $1$, hence a DVR with uniformizer $[y]$. $B\/x B$ is a finite $A\/x A$-module on which the multiplication of $[y]$ is injective. Thus $B\/x B$ is finite free over $A\/x A$. 

  Pick a basis $B\/x B cong (A\/x A)^(oplus r)$, and lift it arbitrarily to a map $phi: A^(oplus r) -> B$. Then $coker(phi) = x coker(phi)$, so by Nakayama, $phi$ is surjective. Next, for any $k in ker(phi)$, $phi(k) = 0$ so $k in (x A)^(oplus r)$. Put $k = x k_0$. Then $0 = phi(k) = x phi(k_0)$. $B$ is a domain and $x != 0$, so $phi(k_0) = 0$ and $k_0 in ker(phi)$. Thus $ker(phi) = x ker(phi)$, and by Nakayama again, $phi$ is injective. We have thus constructed an isomorphism $B cong A^(oplus r)$ as $A$-modules. 

  To proceed we need the following lemma: 
  #lemma[
    Let $A$ be an integral domain and $B$ be a finite free $A$-algebra with basis $e_1, dots.c, e_r in B$. Then $B\/A$ is finite etale if and only if the discriminant: 
    $
      Delta = det mat(Tr_(B\/A) (e_i e_j))_(1<=i,j<=r) in A
    $
    is an element of $A^times$. 
  ]
  #proof[
    Note that $Delta in A^times$ if and only if the trace pairing $B times B -> A, (u, v) |-> Tr_(B\/A) (u v)$ is perfect. 

    ($==>$) For any maximal ideal $frak(m) in Spec(A)$, the fiber $B\/frak(m) B$, being etale over $k(frak(m)) = A\/frak(m)$, is a finite product of finite separable extensions of $k(frak(m))$. The trace pairing of a finite separable field extension is perfect, and so is the trace pairing of $B\/frak(m) B$ over $k(frak(m))$. This shows that $Delta$ reduces to a unit in each $k(frak(m))$. Since $Delta$ is not contained in any maximal ideal, it is a unit. 

    ($<==$) Suppose that the trace pairing is perfect. Pick a basis $u_1, dots.c, u_r in B$ with dual basis $v_1, dots.c, v_r in B$, and put $e = sum_(i=1)^r u_i otimes v_i in B otimes_A B$. The element $e$ has the following property: 
    $
      (b otimes 1)e &= sum_(i=1)^n b u_i otimes v_i = sum_(i=1)^n sum_(j=1)^n Tr_(B\/A) (b u_i v_j) u_j otimes v_i \
      &= sum_(i=1)^n sum_(j=1)^n u_i otimes Tr_(B\/A) (b u_j v_i) v_j = sum_(i=1)^n u_i otimes b v_i = (1 otimes b)e
    $
    Take the multiplication map $mu: B otimes_A B -> B$. Then for every element $t in B otimes_A B$, 
    $
      t e = (mu(t) otimes 1) e = (1 otimes mu(t)) e
    $

    Meanwhile $b in B$, 
    $
      Tr_(B\/A) (b mu(e)) = sum_(i=1)^n Tr_(B\/A) (b u_i v_i) = Tr_(B\/A) (b)
    $
    and so by perfectness of the trace pairing, $mu(e) = 1$. Now let $I = ker(mu)$ and $z in I$. Then: 
    $
      z e = (mu(z) otimes 1) e = 0
    $
    and so $z = z(1-e)$. However, $mu(e) = 1$ so $1-e in I^2$. Thus $z = z(1-e) = I^2$, so $I = I^2$. Thus, 
    $
      Omega_(B\/A) cong I\/I^2 = 0
    $
    so $B$ is unramified over $A$. Since $B$ is free over $A$, it is flat, and hence etale. 
  ]

  Since $B$ is a finite free $A$-algebra, we may form the trace map $Tr_(B\/A): B -> A$. For an $A$-basis $e_1, dots.c, e_r$ of $B$, form the discriminant: 
  $
    Delta = det mat(Tr_(B\/A) (e_i e_j))_(1<=i,j<=r) in A
  $
  Since $Spec(B) -> Spec(A)$ is etale over the punctured spectrum $Spec(A) - {frak(m)}$, for any height 1 prime $frak(p) in Spec(A)$, $Spec(B_(frak(p))) -> Spec(A_(frak(p)))$ is etale. Thus, by the previous lemma, 
  $
    Delta in A_(frak(p))^times
  $
  Thus, 
  $
    Delta = inter.big_(frak(p) in Spec(A) \ "ht"(frak(p)) = 1) A_(frak(p))^times = A^times
  $
  by @normal-hartogs. Thus by the previous lemma, $B$ is an etale $A$-algebra. 
]

#lemma(name: <abhyankar-lemma-special-case>)[
  (Special case of Abhyankar's lemma) Let $R$ be a DVR with uniformizer $pi.alt$ and fraction field $K$, and let $X$ be an affine smooth $R$-scheme of relative dimension $1$. Let $eta in S = Spec(R)$ be the generic point. 

  Let $n$ be a prime number s.t. $n in R^times$, and put $R' = R[pi.alt^(1\/n)], S' = Spec(R')$. A prime on an object denotes its base change from $R$ to $R'$. Let $eta' in S'$ be the generic point. 

  Suppose that $Z_eta -> X_eta$ is an etale $ZZ\/n$-torsor. Then the base change $Z'_(eta') -> X'_(eta')$ extends to a finite etale covering $Z' -> X'$. 
]
#proof[
  /*We may assume that $X$ is affine. Indeed, pick an affine cover ${X_i}$ of $X$, and base change to an affine cover ${X'_i}$ of $X$. Then if the statement holds in the affine case, each $Z'_(i,eta') -> X'_(i,eta')$ must lift to a finite etale covering $pi_i: Z'_i -> X'_i$. To glue these lifts, we need a rigidity statement for finite etales. 

  #lemma[
    If $X$ is a normal noetherian scheme and $U subset X$ is dense open, then for any $Y, Z in FEt_X$ with base changes $Y_U, Z_U in FEt_U$, 
    $
      Hom_X (Y, Z) cong Hom_U (Y_U, Z_U)
    $
  ]
  #proof[
    By replacing $X$ with its connected components, we may assume that $X$ is integral normal. Now put $K = K(X)$, and by @p1et-of-normal-scheme, it suffices to show that for discrete finite $Gal(K^"ur" (X)\/K)$-sets $S, T$, 
    $
      Hom_(Gal(K^"ur" (X)\/K)) (S, T) = Hom_(Gal(K^"ur" (U)\/K)) (S, T)
    $
    Indeed, $Gal(K^"ur" (X)\/K)$ is a quotient of $Gal(K^"ur" (U)\/K)$, so the Hom sets are equal. 
  ]

  Now the finite etales $pi_i: Z'_i -> X'_i$ and $pi_j: Z'_j -> X'_j$ are both restrictions of $Z'_(eta') -> X'_(eta')$ upon base changing to the generic fiber $X'_eta$. Now: 

  - $X'$ is smooth over $S'$ the spectrum of a DVR, hence regular. Its connected components are thus integral regular schemes. Each of them must dominate $S'$ by openness of flat morphisms. Thus the generic point of every irreducible component of $X'$ lies above the generic point $eta' in S'$, and so $X'_(eta') subset X'$ is a dense open. 

    Consequently, for any open subset $U' subset X'$, $U'_(eta') subset U'$ is a dense open. 

  Hence, by the previous rigidity lemma, $pi_i$ and $pi_j$ agrees over $X'_(i,j)$ since they agree over $X'_(i,j,eta')$. Hence, we may glue the $pi_i$'s to a finite etale covering $pi: Z' -> X'$. */
  Since $X$ is smooth over $R$, it is regular. Thus the connected components of $X$ are integral. We may replace $X$ by its connected components and assume that $X$ is integral affine. 

  Since $X$ is integral affine, put $X = Spec(A)$. Fix notation by: 
  $
    X' &= Spec(A'), #h(2em) && A' := A otimes_R R' = A[pi.alt^(1\/n)] \
    X_eta &= Spec(A_1), && A_1 := A otimes_R K = A[pi.alt^(-1)] \
    X'_(eta') &= Spec(A'_1), && A'_1 := A' otimes_(R') Frac(R') = A[pi.alt^(1\/n), pi.alt^(-1)] \
    Z_eta &= Spec(C_1) \
    Z'_(eta') &= Spec(C'_1), && C'_1 := C_1 otimes_K Frac(R') = C_1 [pi.alt^(1\/n)]
  $
  All of these rings involved are regular for being smooth over a DVR or a field. $A$ and $A_1$ are known to be regular domains of dimension $2$. Put: 
  $
    F = Frac(A) = Frac(A_1) 
  $

  Denote the closed points of $S, S'$ by $s, s'$, having the same residue field $k$. We may assume that $X_s = X'_(s') != emptyset$, for otherwise there is nothing to prove. In this case, $X'$ is also necessarily integral: 

  - Choose a generic point $frak(p) in X_s = Spec(A\/frak(pi.alt) A)$. This fiber is smooth over a field, hence regular. Thus the local ring $A_(frak(p))\/frak(pi.alt) A_(frak(p))$ of a generic point is a field. Thus $A_(frak(p))$ is a DVR with uniformizer $pi.alt A_(frak(p))$. 

    Thus $T^n - pi.alt$ is irreducible over the DVR $A_(frak(p))$, hence over its fraction field $F$. Hence it is irreducible over $A$. Thus $A' = A[T]\/(T^n - pi.alt)$ is an integral domain. 

  Put: 
  $
    F' = Frac(A') = Frac(A'_1)
  $
  and we know that $A, A_1, A', A'_1$ are regular domains, with $A, A'$ of dimension $2$ and $A_1, A'_1$ of dimension $1$. 

  $Z'_(eta') -> X'_(eta')$ is an etale $ZZ\/n$-torsor for $n$ prime. If it is trivial, we take $Z' = union.sq.big_(i=1)^n X'$ and conclude the proof. Thus, we may assume that: 

  - $Z'_(eta') -> X'_(eta')$ and $Z_eta -> X_eta$ are nontrivial etale $ZZ\/n$-torsors. 

    $ZZ\/n$ acts transitively on the connected components of $Z'_(eta')$ and $Z_eta$. Since $n$ is a prime, they necessarily have $1$ or $n$ connected components. However, a $ZZ\/n$-torsor with $n$ connected components are trivial. Thus, $Z_eta, Z'_(eta')$ are necessarily connected, hence integral regular. Thus $C_1, C'_1$ are regular domains of dimension 1. Put: 
    $
      L = Frac(C_1), L' = Frac(C'_1)
    $
    
  The $n$ automorphisms in $Aut(C_1\/A_1)$ passes to the generic fiber. Thus $L\/F$ is a degree $n$ cyclic Galois extension. Similarly $L'\/F'$ is degree $n$ cyclic Galois. 

  Since $C'_1$ is finite over $A'_1$ and a domain, it is necessary that: 
  $
    C'_1 otimes_(A'_1) F' = L'
  $
  Also $L' = C'_1 otimes_(A'_1) F' = (C_1 otimes_(A_1) F) otimes_F F' = L otimes_F F'$. Thus as subfields of $L'$, $L' = L F'$. 

  Let $C'$ be the normalization of $A'$ in $L'$. Since $L'\/F'$ is finite separable, by #cite-stacks("032L")[Lemma 10.161.8], $C'$ is finite over $A'$. Put $Z' = Spec(C')$, and we aim to show that the finite map $Z' -> X'$ is finite etale. Furthermore, since localization commutes with normalization, 
  $
    C' otimes_(A') A'_1 = C'[pi.alt^(-1)] = C'_1
  $
  (Here $C'_1$ is normal and finite over $A'_1$, and is hence the normalization of $A'_1$ in $Frac(C'_1) = L'$.) Thus $pi': Z' -> X'$ indeed recovers $Z'_(eta') -> X'_(eta')$ on the generic fiber. In particular, $pi'$ is etale at every point above the generic fiber $X'_(eta')$. 

  We claim that $pi'$ is etale at every point above a height $<=1$ point of $X'$. Now it is already etale above the generic fiber. Meanwhile, the closed points of $X'_(s')$ are of height $2$. Thus it suffices to deal with a generic point of $X_s = X'_(s')$. 

  Let $xi in Spec(A')$ be the generic point of an irreducible component of $X'_(s') = X_s$. It is thus represented by a prime $frak(q)' in Spec(A'\/pi.alt A')$ or $frak(q) in Spec(A\/pi.alt A)$. Put: 
  $
    V  &= A_(frak(q)) = cal(O)_(X,xi) \
    V' &= A'_(frak(q')) = cal(O)_(X',xi) = V[pi.alt^(1\/n)]
  $
  They are both DVRs. Now $V\/pi.alt V = cal(O)_(X_s,xi)$ is a field, so $pi.alt$ is a uniformizer of $V$. Thus $T^n - pi.alt$ is Eisenstein over $V$, making $pi.alt^(1\/n)$ a uniformizer of $V' = V[pi.alt^(1\/n)]$. 

  Let $W$ be the normalization of $V$ in $L$. Since $L\/F$ is finite separable, by #cite-stacks("032L")[Lemma 10.161.8], $W$ is finite over $V$. Since $V -> W$ is an inclusion with $V$ a DVR, $W$ is finite free over $V$, hence flat. 
  
  Since $L\/F$ is a Galois extension, Hilbert theory applies. $Gal(L\/F) cong ZZ\/n$ acts transitively on the $g$ maximal primes of $W$, each with the same ramification index $e$ and residue degree $f$. Then $e f g = n$, and since $n$ is a prime, there are only three possibilities: 
  $
    (e, f, g) = (1, 1, n), (1, n, 1), (n, 1, 1)
  $

  - In the first two cases $e = 1$. The residue field extensions are of degree $1$ or $n$, which are coprime to residue characteristic. Hence the residue field extensions are all finite separable. 
  
    Thus $W$ is unramified over $V$. It is also finite free, so $Spec(W) -> Spec(V)$ is finite etale. Thus $D = W otimes_V V'$ is finite etale over $V'$. Meanwhile, 
    $
      Frac(D) = D otimes_(V') F' = W otimes_V F' = W otimes_V F otimes_F F' = L otimes_F F' = L'
    $
    Thus $D$ is a normal $V'$-subalgebra of $L'$ and finite over $V'$, hence the normalization of $V'$ in $L'$. Since normalization commutes with localization, 
    $
      C' otimes_(A') V' cong D
    $
    Hence, $C' otimes_(A') V'$ is finite etale over $V'$. Since localization on base does not change etaleness, $Spec(C') -> Spec(A')$ is etale at points above $xi$. 

  - In the case $(e, f, g) = (n, 1, 1)$, $W$ itself is a DVR with the same residue field as $V$, and with ramification index $n$. Pick a uniformizer $delta in W$, so that $pi.alt = delta^n u$ for $u in W^times$. Take: 
    $
      D = W[T]\/(T^n - u) = W[u^(1\/n)]
    $
    and endow $D$ with the structure of a $V'$-algebra by $V' -> D, pi.alt^(1\/n) |-> delta u^(1\/n)$. This is well-defined since $(delta u^(1\/n))^n = delta^n u = pi.alt$. $D$ is free over $W$, hence torsion free. Thus, $delta in W$ is a nonzerodivisor of $D$. Now in $D$, $u^(1\/n)$ is a unit, so $pi.alt^(1\/n) = delta u^(1\/n)$ remains a nonzerodivisor. Thus $D$ is finite and torsion free, hence finite over the DVR $V'$. We claim that $Spec(D) -> Spec(V')$ is finite etale. Indeed, 
    $
      D\/pi.alt^(1\/n) D = D\/delta D = k(W)[T]\/(T^n - u)
    $
    is finite etale over $k(W)$ as a Kummer covering, since $u in W^times$. Thus, 
    $
      Omega_(D\/V') otimes_D D\/pi.alt^(1\/n) D = 0
    $
    By Nakayama's lemma, $Omega_(D\/V') = 0$. Thus $Spec(D) -> Spec(V')$ is unramified and also finite free, thus finite etale. Finally, 
    $
      D[pi.alt^(-1\/n)] &= L[T]\/(T^n - u) \
      &= L[T]\/(T^n - pi.alt) #[by changing $T |-> delta T$] \
      &= L(pi.alt^(1\/n)) = L'
    $ 
    Thus $C' otimes_(A') V' = D$ is finite etale over $V'$. Since localization on base does not change etaleness, $Spec(C') -> Spec(A')$ is etale at points above $xi$. 

  Thus, $pi': Spec(C') -> Spec(A')$ is etale at all points above a height $<=1$ point of $Spec(A')$. For any height $2$ point $frak(p) in Spec(A')$, the finite morphism $Spec(C'_(frak(p))) -> Spec(A'_(frak(p)))$ is etale over the punctured spectrum $Spec(A'_(frak(p))) - {frak(p) A'_(frak(p))}$, with $C'_(frak(p))$ normal. By Zariski-Nagata purity in dimension $2$ (@zariski-nagata-purity-in-dim-2), $Spec(C'_(frak(p))) -> Spec(A'_(frak(p)))$ is finite etale. Since localization on base does not change etaleness, $Spec(C') -> Spec(A')$ is etale at points above $frak(p)$. Thus we have shown that $Spec(C') -> Spec(A')$ is finite etale. 
]

#proposition(name: <sbc-core-h1>)[
  Let $A$ be a noetherian strict henselian normal local domain with $K = Frac(A)$. Then $Spec(ol(K) otimes_A A{T})$ has no nontrivial finite etale covering of degree $n in A^times$. In particular, 
  $
    H^1 (Spec(ol(K) otimes_A A{T}), ul(ZZ\/n)) = 0
  $
]
#proof[
  Using the exact sequences $0 -> ul(ZZ\/n) -> ul(ZZ\/m n) -> ul(ZZ\/m) -> 0$, we may break down $n$ to its prime factors and assume that $n$ is a prime number. 

  By topological invariance, it suffices to prove that: 
  $
    H^1 (Spec(K^sep otimes_A A{T}), ul(ZZ\/n)) = 0
  $

  By @cech-h1-classifies-torsors, every class in this cohomology is represented by an etale $ZZ\/n$-torsor. Let $pi: Z -> Y := Spec(K^sep otimes_A A{T})$ be an etale $ZZ\/n$-torsor. 

  - Since: #h(1fr)
    $
      K^sep otimes_A A{T} = dirlim_(L\/K #[finite separable]) L otimes_A A{T}
    $
    by applying @passage-to-limit-of-morphisms (1) and @passage-to-limit-of-properties (2a)(3d) to $pi$, and @passage-to-limit-of-morphisms (1)(3) to the inverse of the torsor isomorphism $Z times ZZ\/n cong Z times_Y Z$, we may assume that $pi$ comes from base changing an etale $ZZ\/n$-torsor $pi^((1)): Z^((1)) -> Y^((1)) := Spec(L otimes_A A{T})$ for a finite separable extension $L\/K$. 

    By @a-braces-t-and-normalization-in-fin-sep-ext, we may safely replace $A$ with the normalization of $A$ in $L$ without affecting the schemes in question. Thus we may assume that $pi$ comes from base changing an etale $ZZ\/n$-torsor: 
    $
      pi^((1)): Z^((1)) -> Y^((1)) := Spec(K otimes_A A{T})
    $

  - Since: 
    $
      Spec(K otimes_A A{T}) = invlim_(U subset Spec(A) #[open]) U times_A Spec(A{T})
    $
    By the same limit argument, we may assume that there exists a dense open $U subset Spec(A)$ and an etale $ZZ\/n$-torsor: 
    $
      pi^((2)): Z^((2)) -> Y^((2)) := U times_A Spec(A{T})
    $
    that base changes to $pi^((1))$, hence to $pi$. 

  - Since: 
    $
      U times_A Spec(A{T}) = invlim_((Spec(B),ol(u)) -> (Spec(A[T]),Spec(K(T)^sep)) #[etale]) U times_A Spec(B)
    $
    by the same limit argument, we may assume that there exists an etale $A[T]$-algebra $B$ and an etale $ZZ\/n$-torsor: 
    $
      pi^((3)): Z^((3)) -> Y^((3)) := U times_A Spec(B)
    $
    that base changes to $pi^((2))$, hence to $pi^((1)), pi$. 

  Throughout later paragraphs, we will implicitly use the following result: If $K'\/K$ is a finite separable extension and $A'$ is the normalization of $A$ in $K'$, then $Spec(A') -> Spec(A)$ preserves height of primes. Indeed, going up holds by finiteness and going down holds by normality and finiteness. 

  - $U subset Spec(A)$ is a dense open. Thus there are only finitely many height-$1$ primes of $A$ not in $U$. Let them be $frak(p)_1, dots.c, frak(p)_t$. Since $A$ is normal, each $A_(frak(p)_i)$ is a DVR, say with uniformizer $pi.alt_i$. Put $K' = K(pi.alt_1^(1\/n), dots.c, pi.alt_t^(1\/n))$ and let $A'$ be the normalization of $A$ in $K'$, necessarily strict henselian local normal and finite over $A$ by @a-braces-t-and-normalization-in-fin-sep-ext. Let $U' subset Spec(A')$ be the base change of $U$. Base change $pi^((3)): Z^((3)) -> U times_A Spec(B)$ along $Spec(A') -> Spec(A)$ to obtain an etale $ZZ\/n$-torsor: 
    $
      pi': Z' -> U' times_(A') Spec(B')
    $ 
    where $B' = B otimes_A A'$ is an etale $A'[T]$-algebra. $pi'$ has a generic fiber: 
    $
      pi'_1: Z'_1 -> Spec(K') times_(A') Spec(B')
    $

    Let $frak(q) in Spec(A') - U'$ be a height $1$ prime. Then it necessarily lies above some $frak(p)_i in Spec(A) - U$. Now $A_(frak(p)_i) -> A'_(frak(q))$ is an extension of DVRs. Furthermore, since $pi.alt_i^(1\/n) in K'$, $A'_(frak(q))$, being a local ring of the normalization of $A_(frak(p)_i)$ in $K'$, must contain $pi.alt_i^(1\/n)$. Thus, we have extensions of DVRs: 
    $
      A_(frak(p)_i) arrow.hook A_(frak(p)_i) [pi.alt_i^(1\/n)] arrow.hook A'_(frak(q))
    $
    $B$ is a smooth $A$-algebra of relative dimension $1$. By @abhyankar-lemma-special-case, the generic fiber $Spec(K(pi.alt_i^(1\/n))) times_(U') Z'-> Spec(K(pi.alt_i^(1\/n))) times_A Spec(B)$ extends to a finite etale covering above $Spec(A_(frak(p)_i) [pi.alt_i^(1\/n)]) times_A Spec(B)$. 

    Hence, $pi'_1: Z'_1 -> Spec(K') times_(A') Spec(B')$ extends to a finite etale covering above $Spec(A'_(frak(q))) times_(A') Spec(B')$. By @passage-to-limit-of-morphisms (1), it extends to a finite etale covering above $V_(frak(q)) times_(A') Spec(B')$ for an open neighborhood $frak(q) in V_(frak(q)) subset Spec(A')$. By @passage-to-limit-of-morphisms (3), this extension agrees with $pi': Z'_1 -> U' times_(A') Spec(B')$ over the intersection $(U' inter V_(frak(q))) times_(A') Spec(B')$, upon shrinking $V_(frak(q))$ around $frak(q)$. 

    Thus, $pi': Z' -> U' times_(A') Spec(B')$ may be extended by replacing $U'$ with $U' union V_(frak(q))$, thereby removing one height-$1$ prime from $Spec(A') - U'$. Repeating this construction for the finitely many primes in $Spec(A') - U'$ yields a finite etale covering: 
    $
      pi^((4)): Z^((4)) -> V times_(A') Spec(B')
    $
    for an open subset $V subset Spec(A')$ of codimension $>=2$, s.t. $pi^((4))$ extends a base change of $pi^((3))$. Over the generic fiber, it base changes to $pi$. 

  - Replace $A$ with $A'$. Base changing $pi^((4))$ along $Spec(A{T}) -> Spec(B)$, we may replace it with a finite etale covering: 
    $
      pi^((5)): Z^((5)) -> V times_A Spec(A{T})
    $
    for $V subset Spec(A)$ a codimension $>=2$ open subset, s.t. $pi^((5))$ base changes to $pi$. 

  - Take the zero section $i: Spec(A) -> Spec(A{T})$. Base changing $pi^((5))$ along the zero section yields a finite etale covering $Z_V -> V$, where $V subset Spec(A)$ and $A$ is normal. Thus, a finite etale covering of $V$ is characterized by a discrete finite $pi_1^et (V) cong Gal(K^"ur" (V)\/K)$-set. There thus exists a finite separable extension $K'\/K$ s.t. the normalization $V'$ of $V$ in $K'$ is finite etale over $V$ and $Z_V times_V V' -> V'$ is a trivial finite etale covering. 
  
    Let $A'$ be the normalization of $A$ in $K'$. Then, since normalization is a local construction, $V' = V times_A Spec(A')$. Thus, base changing $pi^((5))$ along $Spec(A') -> Spec(A)$ gives a finite etale covering: 
    $
      pi^((6)): Z^((6)) -> V' times_(A') Spec(A'{T})
    $
    Then upon base changing along the zero section $Spec(A') -> Spec(A'{T})$, $pi^((6))$ becomes the trivial etale covering. Furthermore, $pi$ is a base change of $pi^((6))$. 

  Once we show that $pi^((6))$ is trivial, thus showing the triviality of $pi$, we have shown that every etale $ZZ\/n$-torsor over $Spec(K^sep otimes_A A{T})$ is trivial. This concludes the proof by showing that: 
  $
    H^1 (Spec(K^sep otimes_A A{T}), ul(ZZ\/n)) = 0
  $
  Now $pi^((6))$ is trivial by the following lemma. 

  #lemma[
    Let $A$ be a noetherian strict henselian normal local domain, $V subset Spec(A)$ be an open subset of codimension $>=2$, and: 
    $
      pi: Z -> V times_A Spec(A{T})
    $
    be a finite etale covering, whose base change along the zero section $i: Spec(A) -> Spec(A{T})$ is a trivial finite etale covering of $V$. Then $pi$ is trivial. 
  ]
  #proof[
    Let $n$ be the degree of $pi$. 

    Note that $A{T}\/T^m A{T} cong A[T]\/T^m A[T]$. Indeed, 
    
    - By @henselization-and-quotients, $A{T}\/T^m A{T} cong (A[T]\/T^m)^#[sh]$. However, $A[T]\/T^m$ is a local ring finite over the strict henselian local ring $A$, hence strict henselian by @finite-over-henselian-is-henselian. Thus, 
      $
        A{T}\/T^m A{T} cong A[T]\/T^m
      $

    We thus have a compatible family of closed immersions $i_m: Spec(A[T]\/T^(m+1)) -> Spec(A{T})$, in which $i_0: Spec(A) cong Spec(A[T]\/T) -> Spec(A{T})$ is the zero section. Together they induce a map $hat(i): Spec(A fps(T)) -> Spec(A{T})$. 
  
    By topological invariance, $pi: Z -> V times_A Spec(A{T})$ becomes a trivial covering upon base changing along each $i_m: Spec(A[T]\/T^(m+1)) -> Spec(A{T})$. Furthermore, the trivializations for different $m$ are compatible. 

    Fix notation via the following Cartesian diagram: 
    // https://q.uiver.app/#r=typst&q=WzAsMTEsWzIsMiwiU3BlYyhBe1R9KSJdLFsyLDMsIlNwZWMoQSkiXSxbMSwzLCJWIl0sWzEsMiwiVyJdLFsyLDAsIlNwZWMoQVtUXVxcL1ReKG0rMSkpIl0sWzIsMSwiU3BlYyhBIGZwcyhUKSkiXSxbMSwwLCJXX20iXSxbMSwxLCJoYXQoVykiXSxbMCwyLCJaIl0sWzAsMCwiWl9tIl0sWzAsMSwiaGF0KFopIl0sWzQsNSwial9tIl0sWzUsMCwiaGF0KGkpIl0sWzAsMSwiZyJdLFsyLDEsIiIsMix7InN0eWxlIjp7InRhaWwiOnsibmFtZSI6Imhvb2siLCJzaWRlIjoidG9wIn19fV0sWzMsMCwiaCIsMix7InN0eWxlIjp7InRhaWwiOnsibmFtZSI6Imhvb2siLCJzaWRlIjoidG9wIn19fV0sWzcsNSwiaGF0KGgpIiwyLHsic3R5bGUiOnsidGFpbCI6eyJuYW1lIjoiaG9vayIsInNpZGUiOiJ0b3AifX19XSxbNiw0LCJoX20iLDAseyJzdHlsZSI6eyJ0YWlsIjp7Im5hbWUiOiJob29rIiwic2lkZSI6InRvcCJ9fX1dLFs4LDMsInBpIiwyXSxbOSw2LCJwaV9tIl0sWzYsNywiaidfbSJdLFs5LDEwLCJqJydfbSIsMl0sWzEwLDcsImhhdChwaSkiLDJdLFs3LDMsImhhdChpKSciXSxbMTAsOCwiaGF0KGkpJyciLDJdLFszLDIsImcnIl1d
    #align(center, diagram({
      node((2, 2), [$Spec(A{T})$])
      node((2, 3), [$Spec(A)$])
      node((1, 3), [$V$])
      node((1, 2), [$W$])
      node((2, 0), [$Spec(A[T]\/T^(m+1))$])
      node((2, 1), [$Spec(A fps(T))$])
      node((1, 0), [$W_m$])
      node((1, 1), [$hat(W)$])
      node((0, 2), [$Z$])
      node((0, 0), [$Z_m$])
      node((0, 1), [$hat(Z)$])
      edge((2, 0), (2, 1), [$j_m$], label-side: left, "->")
      edge((2, 1), (2, 2), [$hat(i)$], label-side: left, "->")
      edge((2, 2), (2, 3), [$g$], label-side: left, "->")
      edge((1, 3), (2, 3), "hook->")
      edge((1, 2), (2, 2), [$h$], label-side: right, "hook->")
      edge((1, 1), (2, 1), [$hat(h)$], label-side: right, "hook->")
      edge((1, 0), (2, 0), [$h_m$], label-side: left, "hook->")
      edge((0, 2), (1, 2), [$pi$], label-side: right, "->")
      edge((0, 0), (1, 0), [$pi_m$], label-side: left, "->")
      edge((1, 0), (1, 1), [$j'_m$], label-side: left, "->")
      edge((0, 0), (0, 1), [$j''_m$], label-side: right, "->")
      edge((0, 1), (1, 1), [$hat(pi)$], label-side: right, "->")
      edge((1, 1), (1, 2), [$hat(i)'$], label-side: left, "->")
      edge((0, 1), (0, 2), [$hat(i)''$], label-side: right, "->")
      edge((1, 2), (1, 3), [$g'$], label-side: left, "->")
    }))
    Also put $i'_m = hat(i)' compose j'_m$ and $i''_m = hat(i)'' compose j''_m$. 

    Put $B = Gamma(Z, cal(O)_Z)$. Every morphism here is separated between noetherian schemes, and hence all pushforwards and pullbacks preserve quasi-coherent sheaves. Now $h_* pi_* cal(O)_Z in QCoh(Spec(A{T}))$, and so: 
    $
      h_* pi_* cal(O)_Z = Gamma(Spec(A{T}), h_* pi_* cal(O)_Z)^tilde = tilde(B)
    $
    and so $pi_* cal(O)_Z = h^* tilde(B)$. Since $pi$ is affine, 
    $
      Z = SPec(pi_* cal(O)_Z) = SPec(h^* tilde(B)) = W times_(A{T}) Spec(B)
    $
    Thus, it remains to show that $B cong A{T}^n$. Now $A{T} -> A fps(T)$ as a completion is faithfully flat. Thus, it suffices to show that $hat(B) := B otimes_(A{T}) A fps(T)$ is isomorphic to $A fps(T)^n$. By flat base change of quasi-coherent sheaves, 
    $
      hat(B)^tilde cong hat(i)^* h_* pi_* cal(O)_Z cong hat(h)_* hat(pi)_* cal(O)_(hat(Z))
    $
    Also since $hat(pi)$ is affine, 
    $
      hat(Z) &= SPec(hat(pi)_* cal(O)_(hat(Z))) = SPec(hat(h)^* hat(h)_* hat(pi)_* cal(O)_(hat(Z))) &= SPec(hat(h)^* hat(B)^tilde) \
      &= hat(W) times_(A fps(T)) Spec(hat(B))
    $
    Similarly, since $pi_m$ is affine, 
    $
      Z_m = W_m times_(A[T]\/T^(m+1)) Spec(Gamma(Z_m, cal(O)_(Z_m)))
    $

    Thus, taking global sections, $hat(B) cong Gamma(hat(Z), cal(O)_(hat(Z)))$. Now by restrictions of global sections, there is a canonical map: 
    $
      Phi: hat(B) cong Gamma(hat(Z), cal(O)_(hat(Z))) -> invlim_(m>=0) Gamma(Z_m, cal(O)_(Z_m))
    $
    Since $pi_m: Z_m -> W_m$ admits compatible trivializations, $Phi$ is a map: 
    $
      Phi: hat(B) -> invlim_(m>=0) Gamma(Z_m, cal(O)_(Z_m)) cong (invlim_(m>=0) Gamma(W_m, cal(O)_(W_m)))^n
    $
    To identify the projective limit on RHS, we need a version of normal Hartogs for sheaves. 

    #lemma[
      (Normal Hartogs for sheaves) Let $X = Spec(A)$ be a noetherian integral normal scheme, and $U subset X$ be a subset of codimension $>=2$. Then for any coherent sheaf $cal(F)$ on $X$ that is free over $cal(O)_X$, the restriction map: 
      $
        Gamma(X, cal(F)) -> Gamma(U, cal(F))
      $
      is an isomorphism. 
    ]
    #proof[
      Writing $cal(F) cong cal(O)_X^(oplus r)$, we may replace $cal(F)$ with $cal(O)_X$ and assume that $cal(F) = cal(O)_X$. Then from the construction of the sheaf $tilde(A) in Coh(Spec(A))$, we see that this restriction map is: 
      $
        A -> inter.big_(frak(p) in U) A_(frak(p))
      $
      where we identify both sides as subsets of $Frac(A)$. However, $U$ contains all height $1$ primes of $A$, so by @normal-hartogs, the intersection on RHS is exactly $A$ itself. 
    ]

    Now: 
    $
      Gamma(W_m, cal(O)_(W_m)) cong Gamma(V, i'_(m,*) cal(O)_(W_m)) cong Gamma(V, i_(m,*) cal(O)_(Spec(A[T]\/T^(m+1))))
    $
    Since $i_(m,*) cal(O)_(Spec(A[T]\/T^(m+1)))$ is finite free over $cal(O)_(Spec(A))$ and $V subset Spec(A)$ is of codimension $>=2$, by the previous lemma, 
    $
      Gamma(V, i_(m,*) cal(O)_(Spec(A[T]\/(T^(m+1))))) cong Gamma(Spec(A), i_(m,*) cal(O)_(Spec(A[T]\/T^(m+1)))) cong A[T]\/T^(m+1)
    $
    Thus, $Phi$ is identified as: 
    $
      Phi: hat(B) -> invlim_(m>=0) Gamma(Z_m, cal(O)_(Z_m)) cong (invlim_(m>=0) Gamma(W_m, cal(O)_(W_m)))^n cong (invlim_(m>=0) A[T]\/T^(m+1))^n = A fps(T)^n
    $
    Since we know that $hat(Z) = hat(W) times_(A fps(T)) Spec(hat(B))$, the $n$ coordinate maps $Phi_1, dots.c, Phi_n: hat(B) -> A fps(T)$ yield $n$ sections $Spec(A fps(T)) -> Spec(hat(B))$ of the structure map $Spec(hat(B)) -> Spec(A fps(T))$. They thus yield $n$ sections: 
    $
      sigma_1, dots.c, sigma_n: hat(W) -> hat(Z)
    $
    of $hat(pi)$. 

    - Modulo $T$, $Phi$ becomes: #h(1fr)
      $
        Phi_0: hat(B)\/T hat(B) = B\/T B -> Gamma(Z_0, cal(O)_(Z_0)) cong Gamma(W_0, cal(O)_(W_0))^n cong A^n
      $
      Thus the $t$-th coordinate map is the restriction $Gamma(Z_0, cal(O)_(Z_0)) -> A$ along the $t$-th component of the chosen trivialization $Z_0 cong union.sq.big_(j=1)^n W_0$. Under the identifications: 
      $
        Z_0 = W_0 times_A Spec(Gamma(Z_0, cal(O)_(Z_0)))
      $
      the $t$-th coordinate map must yield the $t$-th section $W_0 -> Z_0$ according to the given trivialization. 

      Consequently, the section $sigma_t$ becomes the $t$-th section $W_0 -> Z_0$ of the chosen trivialization upon base changing along $i_0$. In particular, all $n$ sections $sigma_1, dots.c, sigma_n$ are distinct. 

    Now that $hat(Z) -> hat(W)$ is a degree $n$ finite etale covering with $n$ sections, it is necessarily trivial. Thus, 
    $
      hat(B) cong Gamma(hat(Z), cal(O)_(hat(Z))) cong Gamma(hat(W), cal(O)_(hat(W)))^n = Gamma(hat(W), cal(O)_(Spec(A fps(T))))^n
    $
    as $A fps(T)$-algebras. Since $A -> A fps(T)$ is flat, going down holds, and a point in $Spec(A fps(T))$ has height at least the height of its image in $Spec(A)$. Thus $hat(W)$ is of codimension $>=2$ in $Spec(A fps(T))$. $A fps(T)$ is also a normal domain, so by the previous lemma: 
    $
      hat(B) cong Gamma(hat(W), cal(O)_(Spec(A fps(T))))^n cong A fps(T)^n
    $
    By fpqc descent of properties (@fpqc-descent-of-properties (2)(5)), since $hat(B)$ is a finite etale $A fps(T)$-algebra, and $A{T} -> A fps(T)$ is faithfully flat, $B$ is a finite etale $A{T}$-algebra. Since $A{T}$ is strict henselian, $Spec(A{T})$ has no nontrivial finite etale coverings, and so necessarily $B cong A{T}^n$. We are thereby done. 
  ]
]

#theorem(name: <loc-acyc-of-smooth-maps>)[
  Smooth morphisms are universally locally acyclic. 

  If $f: X -> S$ is smooth and $Lambda$ is a torsion ring whose torsion order is invertible in $S$, then $f$ is locally acyclic relative to every locally constant sheaf of $Lambda$-modules. 
]
#proof[
  By @loc-acyc-of-smooth-maps-reductions, @sbc-core-h0, @sbc-core-h1, all smooth morphisms are universally locally acyclic. The second statement on locally constant sheaves is due to @loc-acyc-pass-to-lcc-sheaves. 
]

#theorem(name: <smooth-base-change>)[
  (Smooth base change) Suppose that we have a Cartesian diagram: 
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
  in which $f$ is qcqs and $g$ is smooth. Let $Lambda$ be an $n$-torsion ring with $n in cal(O)_S^times$. Then for all $cal(K) in D^+ (X_et, Lambda)$, the base change map: 
  $
    g^(-1) R f_* cal(K) -> R f'_* g'^(-1) cal(K)
  $
  is an isomorphism. 

  In particular, for any sheaf $cal(F) in cAb(X_et, Lambda)$, the base change map: 
  $
    g^(-1) R^q f_* cal(F) -> R^q f'_* g'^(-1) cal(F)
  $
  is an isomorphism for all $q >= 0$. 
]
#proof[
  This follows from @loc-acyc-of-smooth-maps and @loc-acyc-and-base-change. 
]

As a consequence of smooth base change, we show that etale cohomology of torsion sheaves over a separably closed field, with torsion coefficients coprime to base characteristic, is inert to base change along an extension of separably closed fields. 

#corollary(name: <bc-along-extension-of-sep-cl-fields>)[
  Let $Omega\/K$ be an extension of separably closed field, $X$ be a qcqs scheme over $K$, and $X_Omega = X otimes_K Omega$. 

  Then for any complex $cal(K) in D^+_(#[tor]\/K) (X_et, Lambda)$ (i.e. a bounded below complex whose cohomology sheaves are torsion with torsion orders invertible in $K$), the restriction morphism: 
  $
    R Gamma(X, cal(K)) -> R Gamma(X_Omega, cal(K)|_(X_Omega))
  $
  is an isomorphism. 
]
#proof[
  By the way-out lemma, we may replace $cal(K)$ with a single torsion sheaf $cal(F)$ whose germs have torsion order invertible in $K$, and aim to prove that $H^q (X, cal(F)) -> H^q (X_Omega, cal(F)|_(X_Omega))$ is an isomorphism. 

  By topological invariance, it is safe to replace $Omega$ with an algebraic closure $ol(Omega)$ and $K$ with its algebraic closure $ol(K)$ in $ol(Omega)$. We may thus assume that $Omega\/K$ are both algebraically closed. 

  Writing $Omega = dirlim_(I subset Omega #[finite]) ol(K(I))$ as its algebraically closed subfields with finite transcendence degree, and using @limit-formula-for-schemes to write: 
  $
    H^q (X_Omega, cal(F)|_(X_Omega)) = dirlim_(I subset Omega #[finite]) H^q (X_(ol(K(I))), cal(F)|_(X_(ol(K(I)))))
  $
  we may replace $Omega$ with $ol(K(I))$ to assume that $Omega\/K$ is of finite transcendence degree, say $Omega = ol(K(t_1, dots.c, t_m))$. Then by induction on the transcendence degree, we may assume that $Omega = ol(K(t))$. 


  
  It suffices to show that $Omega = ol(K(t))$ is a direct limit $dirlim_lambda A_lambda$ of smooth $K$-algebras $A_lambda$. Since in that case, we may form the Cartesian diagram: 
  // https://q.uiver.app/#r=typst&q=WzAsNixbMCwyLCJYIl0sWzEsMiwiU3BlYyhLKSJdLFswLDEsIlhfKEFfbGFtYmRhKSJdLFsxLDEsIlNwZWMoQV9sYW1iZGEpIl0sWzEsMCwiU3BlYyhPbWVnYSkiXSxbMCwwLCJYX09tZWdhIl0sWzUsNCwiZl9PbWVnYSJdLFsyLDMsImZfbGFtYmRhIl0sWzAsMSwiZiJdLFs1LDIsImgnX2xhbWJkYSIsMl0sWzIsMCwiZydfbGFtYmRhIiwyXSxbNCwzLCJoX2xhbWJkYSJdLFszLDEsImdfbGFtYmRhIl1d
  #align(center, diagram({
    node((-1, 1), [$X$])
    node((0, 1), [$Spec(K)$])
    node((-1, 0), [$X_(A_lambda)$])
    node((0, 0), [$Spec(A_lambda)$])
    node((0, -1), [$Spec(Omega)$])
    node((-1, -1), [$X_Omega$])
    edge((-1, -1), (0, -1), [$f_Omega$], label-side: left, "->")
    edge((-1, 0), (0, 0), [$f_lambda$], label-side: left, "->")
    edge((-1, 1), (0, 1), [$f$], label-side: left, "->")
    edge((-1, -1), (-1, 0), [$h'_lambda$], label-side: right, "->")
    edge((-1, 0), (-1, 1), [$g'_lambda$], label-side: right, "->")
    edge((0, -1), (0, 0), [$h_lambda$], label-side: left, "->")
    edge((0, 0), (0, 1), [$g_lambda$], label-side: left, "->")
  }))
  and apply the limit formula for base change @limit-formula-for-base-change, to see that: 
  $
    R^q f_(Omega,*) (cal(F)|_(X_Omega)) &= dirlim_lambda h_lambda^(-1) R^q f_(lambda,*) (cal(F)|_(X_(A_lambda))) \
    &= dirlim_lambda h_lambda^(-1) g_lambda^(-1) R^q f_* cal(F) #[by smooth base change @smooth-base-change] \
    &= dirlim_lambda (R^q f_* cal(F))|_(Spec(Omega)) = (R^q f_* cal(F))|_(Spec(Omega))
  $
  In other words, 
  $
    H^q (X_Omega, cal(F)|_(X_Omega)) = H^q (X, cal(F))
  $
  Now it remains to prove that $ol(K(t))$ is a directed limit of smooth $K$-algebras. For any subfield $K(t) subset L subset ol(K(t))$, let $A_L$ be the normalization of $K[t]$ in $L$, so that $L = Frac(A_L)$. Then since $K[t]$ is Nagata (by @cite-matsumura-ca[Theorem 31.H]), $A_L$ is a finite $K[t]$-algebra. It is thus a finite type integral $K$-algebra of dimension $1$ that is integrally closed. Since $A_L$ has dimension $1$ and is integrally closed, all of its local rings are fields or DVRs, hence $A_L$ is regular. Recall that for an algebraically closed field $K$, a finite type $K$-scheme is smooth if and only if it is regular (by @cite-hartshorne-ag[Theorem III.10.2]). Thus, $A_L$ is a smooth $K$-algebra with $Frac(A_L) = L$.

  Now: 
  $
    ol(K(t)) = dirlim_(L\/K(t) #[finite]) Frac(A_L) = dirlim_(L\/K(t) #[finite] \ 0 != f in A_L) A_L [f^(-1)]
  $
  where $Spec(A_L [f^(-1)])$ is an affine open of $Spec(A_L)$, hence smooth over $K$. We have thus written $ol(K(t))$ as a direct limit of smooth $K$-algebras. 
]
