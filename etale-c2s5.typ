#import "void-import.typ": *

== Henselization & strict henselization

Etale morphisms mimic open subsets, in the sense that they define a finer "topology" that will later be studied and is suitable for applications. Now in Zariski topology, one important object of a scheme is its local ring at a point: 
$
  cal(O)_(X,x) = dirlim_(x in U subset X #[open]) cal(O)_U (U)
$
It is the limit of all Zariski neighborhoods of $x$. We would like to define an analogous notion for etale neighborhoods. 

Later we will see that the correct notion of a point of $X$ in the etale topology is a geometric point, i.e. a map $ol(x): Spec(Omega) -> X$ for a separably closed field $Omega$. Then the correct notion of local rings in the etale setting is: 
$
  dirlim_((U,ol(u))->(X,ol(x)) #[etale]) cal(O)_U (U)
$
It will turn out that such rings are a special type of local rings characterized by the familiar Hensel's lemma. They are called (strict) henselian local rings, and will play a critical role in the development of etale cohomology. 

#proposition(name: <equiv-defns-of-henselian>)[
  For a local ring $(A, frak(m))$ with residue field $k$, the following conditions are equivalent: 

  + Every finite $A$-algebra $B$ factors as $B = product_i B_i$, a direct product of local $A$-algebras. 

  + (Hensel's lemma) For any monic $f(T) in A[T]$ and any root $a_0 in k$ of $ol(f)$ with $ol(f)'(a_0) != 0$ (i.e. $a_0$ is not a repeated root), there exists $a in A$ s.t. $a_0 = ol(a)$ and $f(a) = 0$. 
  
  + (Strong Hensel's lemma) For any monic $f in A[T]$ and any factorization $ol(f) (T) = g_0 (T) h_0 (T) in k[T]$ with $gcd(g_0, h_0) = 1$, there exists a factorization $f(T) = g(T)h(T) in A[T]$ s.t. $ol(g) = g_0$ and $ol(h) = h_0$. 

  + For every etale morphism $alpha: X -> S = Spec(A)$, consider its base change to the special fiber $alpha_0: X_0 -> S_0 = Spec(k)$. Then the natural map: 
    $
      sec(alpha) -> sec(alpha_0), f |-> f otimes_A k
    $
    from sections of $alpha$ to sections of $alpha_0$ is bijective. 

  + For any etale $A$-algebra $R$, if $R$ has a $k$-point, then $alpha: Spec(R) -> Spec(A)$ has a section. In other words, if $sec(alpha_0)$ is nonempty, so is $sec(alpha)$. 
]
#proof[
  The following implications are tautological: (3)$==>$(2), (4)$==>$(5). 

  We first prove (5)$==>$(4): 
  #proof[
    Note that if $(A, frak(m))$ is a local ring, then the image of any map $Spec(A) -> X$ is contained in any open containing $Spec(frak(m))$. 

    Fix a $k$-point $x_0: Spec(k) -> X_0$. Then any section $x: Spec(A) -> X$ lifting $x_0$ must have image contained in any neighborhood $U$ of $x_0$. Thus it suffices to prove for a fixed arbitrary neighborhood $U$ of $x_0$ that there is a unique section $Spec(A) -> U$ lifting $x_0: Spec(k) -> U_0$. 

    Thus in (4) we may assume that $X = Spec(B)$ where $B$ is an etale $A$-algebra. We perform induction on $dim_k (B_0)$ where $B_0 = B otimes_A k$. Now: 

    - If $sec(Spec(B_0) -> Spec(k))$ is nonempty, so is $sec(Spec(B) -> Spec(A))$ by (5). Thus the separated etale morphism $Spec(B) -> Spec(A)$ has a section, which is necessarily an open and closed immersion. Thus we may write $B = A times B'$ as $A$-algebras, and $B_0 = k times B'_0$ as $k$-algebras. Now: 
      $
        sec(Spec(B) -> Spec(A)) = {*} union.sq sec(Spec(B') -> Spec(A)) \
        sec(Spec(B_0) -> Spec(k)) = {*} union.sq sec(Spec(B'_0) -> Spec(k))
      $
      so we may replace $B$ by $B'$. Now $dim_k (B'_0) = dim_k (B_0) - 1$, so by the inductive hypothesis $sec(Spec(B') -> Spec(A)) cong sec(Spec(B'_0) -> Spec(k))$. Thus $sec(Spec(B) -> Spec(A)) cong sec(Spec(B_0) -> Spec(k))$. 

    - If $sec(Spec(B_0) -> Spec(k))$ is empty, $sec(Spec(B) -> Spec(A))$ must be empty. Thus the desired bijection trivially holds. 
  ]

  (2)$==>$(4): 
  #proof[
    Note that if $(A, frak(m))$ is a local ring, then the image of any map $Spec(A) -> X$ is contained in any open containing $Spec(frak(m))$. 

    Fix a $k$-point $x_0: Spec(k) -> X_0$. Then any section $x: Spec(A) -> X$ lifting $x_0$ must have image contained in any neighborhood $U$ of $x_0$. Thus it suffices to prove for a fixed arbitrary neighborhood $U$ of $x_0$ that there is a unique section $Spec(A) -> U$ lifting $x_0: Spec(k) -> U_0$. 

    By @local-struct-of-etale-morphisms (the local structure of etale morphisms), upon shrinking $X$ around $x_0$ and $Spec(A)$ around $frak(m)$, we may make $alpha$ standard etale. Now the only open of $Spec(A)$ containing $frak(m)$ is $Spec(A)$ itself, so we only need to shrink $X$ around $x_0$. Thus we may assume that: 
    $
      X = Spec(B), B = (A[T]_(h(T)))/((g(T)))
    $
    is standard etale over $Spec(A)$, where $g(T)$ is monic and $(g(T), g'(T)) = (1) subset A[T]_(h(T))$. 

    Now sections to $X_0 -> Spec(k)$ are nothing but elements $a_0 in k$ s.t: 
    $
      ol(h)(a_0) in k^times, ol(g)(a_0) = 0
    $
    and sections to $X -> Spec(A)$ are nothing but elements $a in A$ s.t: 
    $
      h(a) in A^times, g(a) = 0
    $
    Thus we need to prove that the reduction: 
    $
      {a in A : h(a) in A^times, g(a) = 0} -> {a_0 in k: ol(h)(a_0) in k^times, ol(g)(a_0) = 0}
    $
    is bijective. Now for $a_0$ in RHS, since $(ol(g)(T), ol(g)'(T)) = (1) subset k[T]_(ol(h)(T))$, it must be that $ol(g)'(a_0) != 0$. Thus by Hensel's lemma, there exists a unique lift $a in A$ s.t. $g(a) = 0$. Such a lift necessarily has $h(a) in A^times$ (since it reduces to $ol(h)(a_0) in k^times$). We are thereby done. 
    #suppress-qed
  ]

  (4)$==>$(1): 
  #proof[
    Suppose that we know (1) for $B$ finite free over $A$. Then for a general finite $A$-algebra $B$, pick finitely many generators $b_1, dots.c, b_n in B$, each satisfying a monic relation $f_i (T) in A[T]$. Then we have a surjection: 
    $
      C = (A[T_1, dots.c, T_n])/((f_1 (T_1), dots.c, f_n (T_n))) ->> B
    $
    in which $C$ is a finite free $A$-algebra. Thus by the free case, $C$ factors as $C = product_i C_i$ a finite product of local $A$-algebras. Then as a quotient of $C$, $B$ must factor as $product_i C_i\/I_i$, also a finite product of local $A$-algebras. 

    We may now assume that $B$ is finite free over $A$. Pick a basis $B = oplus.big_(i=1)^n A e_i$, and so there are structure constants: 
    $
      e_i e_j = sum_(k=1)^n a_(i,j,k) e_k
    $
    where commutativity requires $a_(i,j,k) = a_(j,i,k)$ and associativity requires: 
    $
      (e_i e_j) e_k = sum_(s=1)^n a_(i,j,s) e_s e_k = sum_(s=1)^n sum_(t=1)^n a_(i,j,s) a_(s,k,t) e_t \
      e_i (e_j e_k) = sum_(s=1)^n a_(j,k,s) e_i e_s = sum_(s=1)^n sum_(t=1)^n a_(j,k,s) a_(i,s,t) e_t
    $
    and so for each $t$, $sum_(s=1)^n a_(i,j,s) a_(s,k,t) = sum_(s=1)^n a_(j,k,s) a_(i,s,t)$. 

    Put indeterminates $T_1, dots.c, T_n$. Then: 
    $
      (T_1 e_1 + dots.c + T_n e_n)^2 = sum_(k=1)^n (sum_(1<=i,j<=n) a_(i,j,k) T_i T_j) e_k
    $
    Put $p_k (T) = sum_(1<=i,j<=n) a_(i,j,k) T_i T_j - T_k$ and $R = A[T_1, dots.c, T_n]\/(p_1 (T), dots.c, p_n (T))$. Then: 

    - $R$ represents the idempotents of $B$. Indeed, any ring homomorphism $R -> A$ corresponds to coefficients $alpha_1, dots.c, alpha_n in A$ s.t: 
      $
        sum_(1<=i,j<=n) a_(i,j,k) alpha_i alpha_j - alpha_k = 0
      $
      for each $k$. This is equivalent to $sum_(i=1)^n alpha_i e_i in B$ being idempotent. 

      In the same way, $R_0 = R otimes_A k$ represents the idempotents of $B_0 = B otimes_A k$. 

    - $R$ is an etale $A$-algebra. Indeed, consider the Jacobian matrix. The polynomials $p_k (T)$ mimic the function $X^2 - X$, so the Jacobian matrix should mimic the derivative $2X - 1$, which should be invertible since $(2X - 1)^2 = 4 X^2 - 4 X + 1 = 1$ due to idempotence. We make this rigorous as follows. Compute: 
      $
        (partial p_j)/(partial T_i) (T) &= (partial)/(partial T_i) (sum_(1<=k,ell<=n) a_(k,ell,j) T_k T_ell) - delta_(i,j) \
        &= sum_(1<=ell<=n) a_(i,ell,j) T_ell + sum_(1<=k<=n) a_(k,i,j) T_k - delta_(i,j) \
        &= 2 sum_(k=1)^n a_(k,i,j) T_k - delta_(i,j)
      $
      
      Consider the Jacobian matrix: 
      $
        J = mat(display((partial p_j)/(partial T_i) (T)))_(i,j) = mat(display(sum_(k=1)^n 2 a_(k,i,j) T_k - delta_(i,j)))_(i,j) = 2K - I
      $
      where $K = mat(display(sum_(k=1)^n a_(k,i,j) T_k))_(i,j)$. Now to show that $J^2 = I$ over $R$, it suffices to show that $K^2 = K$ over $R$. Indeed, comparing entry $i,j$, we need to show that: 
      $
        sum_(k=1)^n a_(k,i,j) T_k = sum_(s=1)^n (sum_(k=1)^n a_(k,i,s) T_k) (sum_(ell=1)^n a_(ell,s,j) T_ell) in R
      $
      Indeed, in $R$, 
      $
        & sum_(s=1)^n (sum_(k=1)^n a_(k,i,s) T_k) (sum_(ell=1)^n a_(ell,s,j) T_ell) \
        =& sum_(k=1)^n T_k sum_(1<=ell,s<=n) a_(ell,s,j) a_(k,i,s) T_ell \
        =& sum_(k=1)^n T_k sum_(1<=ell,s<=n) a_(i,s,j) a_(k,ell,s) T_ell #[by associativity] \
        =& sum_(s=1)^n a_(s,i,j) sum_(1<=ell,k<=n) a_(k,ell,s) T_k T_ell \
        =& sum_(s=1)^n a_(s,i,j) T_s #[by the relation $p_s (T)$]
      $
      Thus $J^2 = I$ in $R$, so $J$ is invertible. Thus $R$ is an etale $A$-algebra. 

    (4) combined with these two points thus show that the reduction: 
    $
      Idem(B) -> Idem(B_0), b |-> [b]
    $
    is a bijection. Now $B_0$ is a finite $k$-algebra and is artinian, hence factors into: 
    $
      B_0 = B_(1,0) times dots.c times B_(m,0)
    $
    a product of artinian local $k$-algebras. This corresponds to a complete system of orthogonal idempotents $[e_1], dots.c, [e_m] in Idem(B_0)$. Lift them to idempotents $e_1, dots.c, e_m in Idem(B)$. Then $e_i e_j$ for $i != j$ are idempotents reducing to $0$, hence are $0$, and $sum_(i=1)^m e_i$ is an idempotent reducing to $1$, hence $1$. Thus, the factorization of $B_0$ lifts to a factorization: 
    $
      B = B_1 times dots.c times B_m
    $
    into $A$-algebras, in which $B_(i,0) = B_i otimes_A k$. Now every maximal ideal of the finite $A$-algebra $B_i$ lies above $frak(m)$ (since finite morphisms are closed), so $B_(i,0) = B_i\/frak(m) B_i$ being local implies the locality of $B_i$. We are thereby done. 
    #suppress-qed
  ]

  (1)$==>$(3): 
  #proof[
    We may assume that $g_0, h_0$ are monic by clearing leading coefficients by a unit. 

    Put $B = A[T]\/(f(T))$, which is a finite (free) $A$-algebra since $f$ is monic. By (1), 
    $
      B = B_1 times dots.c times B_m
    $
    is a product of local $A$-algebras, reducing to: 
    $
      B_0 = B_(1,0) times dots.c times B_(m,0)
    $
    modulo $frak(m)$. On the other hand, $gcd(g_0, h_0) = 1$, so $B_0 cong k[T]\/(g_0 (T)) times k[T]\/(h_0 (T))$ by Chinese remainder theorem. Thus, we may assume that: 
    $
      B_(1,0) times dots.c times B_(ell,0) cong k[T]\/(g_0 (T)) \
      B_(ell+1,0) times dots.c times B_(m,0) cong k[T]\/(h_0 (T))
    $
    Now each $B_i$ is a finite projective $A$-module, hence finite free. Put: 
    $
      g(X) = det(X id - T : B_1 times dots.c times B_ell) \
      h(X) = det(X id - T : B_(ell+1) times dots.c times B_m)
    $
    to be the characteristic polynomials of $T$ on these factors. Then $g(X) h(X) = det(X id - T : B) = f(X)$, and taking the reductions, $g_0 = g mod frak(m), h_0 = h mod frak(m)$. (In this step, we use the assumption that $g_0, h_0$ are monic.)
    #suppress-qed
  ]

  Now that we have proved (4)$<==>$(5) and (1)$==>$(3)$==>$(2)$==>$(4)$==>$(1), we are done. 
]

#definition(name: <defn-henselian-local-rings>)[
  - We say a local ring $(A, frak(m))$ is *henselian* if the equivalent conditions (1)--(5) above hold; 
  
  - We say that $A$ is *strictly henselian* if it is henselian and the residue field $k = A\/frak(m)$ is separably closed.
]

#corollary[
  Any local ring $(A,frak(m))$ that is ($frak(m)$-adically) complete is henselian. 
]
#proof[
  It is familiar that Hensel's lemma holds for complete local rings. 
]

#corollary(name: <finite-over-henselian-is-henselian>)[
  For a (strict) henselian local ring $A$, any finite local $A$-algebra $B$ must be (strict) henselian. 

  Consequently, in @equiv-defns-of-henselian (1), every finite $A$-algebra factors into a finite product of finite local (strict) henselian $A$-algebras. 
]
#proof[
  Suppose that $A$ is henselian. Any finite $B$-algebra must be a finite $A$-algebra, hence splits into a direct product of local rings. Thus @equiv-defns-of-henselian (1) is satisfied. Thus $B$ is henselian. 

  Furthermore, if $A$ is strict henselian, then note that $k(B)\/k(A)$ is a finite extension. Since $k(A)$ is separably closed, $k(B)\/k(A)$ must be purely inseparable, making $k(B)$ separably closed too. Thus $B$ is strict henselian. 
]

Now that we have characterized henselian local rings, we need to construct the henselization. 

#definition(name: <defn-henselizations>)[
  Let $(A, frak(m))$ be a local ring with residue field $k$. 

  - The *henselization* $A^#[h]$ of $A$ is defined as the filtered colimit: #h(1fr)
    $
      A^#[h] := dircolim_((Spec(B),frak(q)) -> (Spec(A),frak(m)) #[etale] \ k(frak(q)) = k) B_(frak(q))
    $
    That is, the henselization of $A$ is the filtered colimit of all local rings of etale neighborhoods of $(A, frak(m))$ that do not extend the residue field at $frak(m)$. 

  - Fix a separable closure $k arrow.r.hook k^sep$. The *strict henselization* of a local ring $(A,frak(m))$ is the filtered colimit: 
    $
      A^#[sh] := dircolim_((Spec(B),frak(q)) -> (Spec(A),frak(m)) #[etale] \ phi: k(frak(q)) arrow.hook k^sep) B_(frak(q))
    $
    Here, $phi: k(frak(q)) -> k^sep$ is required to be an inclusion compatible with the given $k -> k^sep$ under the inclusion $k -> k(frak(q))$ of residue fields. 

    That is, the strict henselization of $A$ is the filtered colimit of all local rings of etale neighborhoods of $(A, frak(m))$. 

  Now for rigor of the proofs, we need to check that the indexing category of the colimits defining $A^#[h]$ and $A^#[sh]$ are indeed filtered. 
  #proof[
    For $A^#[h]$: 

    - Suppose that $(B_1, frak(q)_1), (B_2, frak(q)_2)$ are two etale neighborhoods of $(A, frak(m))$ with $k(frak(q)_(1,2)) = k$. Take $B = B_1 otimes_A B_2$, still an etale $A$-algebra. The primes of $B$ lying above $frak(q)_(1,2)$ of $B_(1,2)$ are classified by the spectrum of the fiber: 
      $
        k(frak(q)_1) otimes_k k(frak(q)_2) = k
      $
      Thus there is a unique $frak(q) in Spec(B)$ above $frak(q)_(1,2) in Spec(B_(1,2))$ with $k(frak(q)) = k$. Thus $(B, frak(q))$ dominates both $(B_(1,2), frak(q)_(1,2))$. 

    - For two parallel arrows $g_(1,2): (Spec(C), frak(r)) -> (Spec(B), frak(q))$, take: 
      $
        g = (g_1, g_2): Spec(C) -> Spec(B otimes_A B)
      $
      Since $g_1, g_2$ both induces the morphism $k(frak(q)) -> k(frak(r))$ identified with $k cong k$ on residue fields, $g$ sends $frak(r)$ into the diagonal $Delta_(B\/A) subset Spec(B otimes_A B)$. Since $B$ is etale over $A$, $Delta_(B\/A) subset Spec(B otimes_A B)$ is open. 
      
      Thus taking an affine open $frak(r) in Spec(D) subset g^(-1) (Delta_(B\/A))$, we see that $(Spec(D), frak(r))$ is still in the indexing category, and the inclusion $(Spec(D), frak(r)) -> (Spec(C), frak(r))$ equalizes $g_(1,2)$. 

    For $A^#[sh]$: 

    - Suppose that $(B_1, frak(q)_1, phi_1), (B_2, frak(q)_2, phi_2)$ are two etale neighborhoods of $(A, frak(m))$. Take $B = B_1 otimes_A B_2$, still an etale $A$-algebra. The primes of $B$ lying above $frak(q)_(1,2)$ of $B_(1,2)$ are classified by the spectrum of the fiber: 
      $
        k(frak(q)_1) otimes_k k(frak(q)_2)
      $
      The map $k(frak(q)_1) otimes_k k(frak(q)_2) -> k^sep$, $x_1 otimes x_2 |-> phi_1 (x_1) phi_2 (x_2)$, has a maximal ideal $frak(r)$ as its kernel, corresponding to $frak(q) in Spec(B)$ lying above $frak(q)_(1,2) in Spec(B_(1,2))$. Take: 
      $
        phi: k(frak(q)) cong k(frak(q)_1) otimes_k k(frak(q)_2)\/frak(r) -> k^sep
      $
      where the last map is $[x_1 otimes x_2] |-> phi_1 (x_1) phi_2 (x_2)$. Then $phi$ is compatible with both of $phi_(1,2)$. Thus, $(Spec(B), frak(q), phi)$ dominates $(B_1, frak(q)_1, phi_1), (B_2, frak(q)_2, phi_2)$. 

    - For two parallel arrows $g_(1,2): (Spec(C), frak(r), psi) -> (Spec(B), frak(q), phi)$, consider the maps $ol(g)_(1,2): k(frak(q)) -> k(frak(r))$. By assumption, $phi = psi compose ol(g)_1 = psi compose ol(g)_2$. Since $psi$ is injective, $ol(g)_1 = ol(g)_2$. Thus $g = (g_1, g_2): Spec(C) -> Spec(B otimes_A B)$ still sends $frak(r)$ to the diagonal. The same diagonal argument as in the case of $A^#[h]$ gives a Zariski affine open of $(Spec(C), frak(r))$ that equalizes $g_(1,2)$. 

    We are thereby done. 
  ]

  As filtered colimits of local rings under local homomorphisms, $A^#[h]$ and $A^#[sh]$ are local $A$-algebras. 

  Note that open immersions are etale, so this gives ways to rewrite these filtered colimits: 
  $
    A^#[h] = dircolim_((Spec(B),frak(q)) -> (Spec(A),frak(m)) #[etale] \ k(frak(q)) = k) B \
    A^#[sh] := dircolim_((Spec(B),frak(q)) -> (Spec(A),frak(m)) #[etale] \ phi: k(frak(q)) arrow.hook k^sep) B
  $

  #remark[
    The choice of a separable closure $k -> k^sep$ is not canonical (and it is only unique up to non-canonical isomorphism). Thus strictly speaking $A^#[sh]$ is not a fully canonical construction. However in practice this is rarely an issue, so we suppress the chosen separable closure $k^sep$ from the notation. 
  ]
]

We now prove the first properties of (strict) henselizations. 

#properties[
  Let $(A, frak(m))$ be a local ring with residue field $k$. 

  + The henselization $A^#[h]$ has the following properties: 

    + $A^#[h]$ is a henselian local ring;
    + $A^#[h]$ is a filtered colimit of etale $A$-algebras;
    + $A -> A^#[h]$ is a faithfully flat local homomorphism;
    + $frak(m)_(A^#[h]) = frak(m) A^#[h]$; 
    + $k(A^#[h]) = k$; 
    + For every henselian local ring $R$, any local homomorphism $A -> R$ factors uniquely as local homomorphisms $A -> A^#[h] -> R$. 

  + (Fix a separable closure $k^sep$ and define $A^#[sh]$ with respect to this separable closure.) The strict henselization $A^#[sh]$ has the following properties: 

    + $A^#[sh]$ is a strict henselian local ring;
    + $A^#[sh]$ is a filtered colimit of etale $A$-algebras;
    + $A -> A^#[sh]$ is a faithfully flat local homomorphism;
    + $frak(m)_(A^#[sh]) = frak(m) A^#[sh]$; 
    + $k(A^#[sh]) = k^sep$; 
    + For every strict henselian local ring $R$ and a fixed inclusion $iota: k^sep -> k(R)$, any local homomorphism $A -> R$ factors uniquely as local homomorphisms $A -> A^#[sh] -> R$ with $A^#[sh] -> R$ inducing $iota$ on residue fields. 

]
#proof[
  (1b) and (2b) directly follow from the alternative limit: 
  $
    A^#[h] = dircolim_((Spec(B),frak(q)) -> (Spec(A),frak(m)) #[etale] \ k(frak(q)) = k) B \
    A^#[sh] := dircolim_((Spec(B),frak(q)) -> (Spec(A),frak(m)) #[etale] \ phi: k(frak(q)) arrow.hook k^sep) B
  $
  (1d)(2d) For any $B_(frak(q))$ in the filtered colimit defining $A^#[h]$ or $A^#[sh]$, by definition, the maximal ideal $frak(q) B_(frak(q))$ is exactly $frak(m) B_(frak(q))$. The maximal ideals of $A^#[h]$ and $A^#[sh]$ lie above the maximal ideals of each $B_(frak(q))$ and are therefore generated by $frak(m)$. Thus, 
  $
    frak(m)_(A^#[h]) = frak(m) A^#[h], frak(m)_(A^#[sh]) = frak(m) A^#[sh]
  $

  (1c)(2c) Each $B_(frak(q))$ in the definition of $A^#[h]$ or $A^#[sh]$ is a faithfully flat local $A$-algebra. Thus as a directed limit of them, $A^#[h]$ and $A^#[sh]$ are flat $A$-algebras. Now $A -> A^#[h]$ and $A -> A^#[sh]$ are flat local homomorphisms, so they are faithfully flat. (Indeed, flat morphisms are open on spectra, and local homomorphisms send the closed point to the closed point. Thus the images are open subsets of $Spec(A)$ containing the closed point, hence $Spec(A)$ itself.) 

  (1e)(2e) The residue fields can be written as: 
  $
    k(A^#[h]) = dircolim_((Spec(B),frak(q)) -> (Spec(A),frak(m)) #[etale] \ k(frak(q)) = k) k(frak(q)) \

    k(A^#[sh]) := dircolim_((Spec(B),frak(q)) -> (Spec(A),frak(m)) #[etale] \ phi: k(frak(q)) arrow.hook k^sep) k(frak(q))
  $
  In the first limit, every $k(frak(q)) = k$, so $k(A^#[h]) = k$. In the second limit, $k(A^#[sh])$ is the union of the $k(frak(q))$'s in $k^sep$. Thus, to show that $k(A^#[sh]) = k^sep$, it remains to show that every finite separable extension $L\/k$ occurs as the residue field of an etale $A$-algebra at a prime above $frak(m)$. 

  - Pick a primitive element $alpha$ so that $L = k(alpha)$, and $alpha$ has monic minimal polynomial $ol(p)(T) in k[T]$. Lift $ol(p)(T)$ arbitrarily to a monic $p(T) in A[T]$ of the same degree. Now since $ol(p)(T) in k[T]$ is separable, we may pick $ol(a_0)(T), ol(a_1)(T) in k[T]$ s.t: 
    $
      ol(p)(T) ol(a_0)(T) + ol(p)'(T) ol(a_1) (T) = 1 in k[T]
    $
    Arbitrarily lift $ol(a_(0,1))(T)$ to $a_(0,1)(T) in A[T]$, and so: 
    $
      p(T) a_0 (T) + p'(T) a_1 (T) = h(T) in 1 + frak(m)[T]
    $
    Now consider: 
    $
      B = (A[T]_(h(T)))/((p(T)))
    $
    Then the formula above gives $(p(T), p'(T)) = (1) subset A[T]_(h(T))$. $B$ is thus standard etale over $A$. Now: 
    $
      B\/frak(m) B &cong (k[T]_(ol(h)(T)))/((ol(p)(T))) \
      &cong k[T]\/(ol(p)(T)) #[since $ol(h)(T) = 1$] \
      &cong k(alpha) = L
    $
    Thus $frak(m) B$ is a maximal ideal of the etale $A$-algebra $B$ lying above $frak(m)$ s.t. $k(frak(m) B) = L$. 

  With those easier properties proved, it suffices to prove (a) and (f). 

  (1a) To prove henselianity of $A^#[h]$, consider an etale $A^#[h]$-algebra $R$ with a prime $frak(q)$ above $frak(m)A^#[h]$ s.t. $k(frak(q)) = k$. $R$ is necessarily of finite presentation over $A^#[h]$. Now our passage to limit theorems are stated using directed sets, so we need an abstract categorical lemma to change filtered categories into directed sets. This is the Artin-Mazur construction: 

  #lemma(name: <artin-mazur-construction>)[
    (Artin-Mazur construction, #cite-stacks("0032", [Lemma 4.21.5])) Let $J$ be a cofiltered category/* with a final object*/. Then there exists a directed poset $P$ /*with a minimum element, */with a cofinal functor $P -> J^opp$. 
  ]

  Now by @passage-to-limit-of-morphisms and @passage-to-limit-of-properties (3d), there exists an etale neighborhood $(B, frak(q)) -> (A, frak(m))$ with $k(frak(q)) = k$, and an etale $B$-algebra $C$ s.t. $R = C otimes_B A^#[h]$. Since $R\/A^#[h]$ has a $k$-point, so does $C\/B$. Thus there exists $frak(r) in Spec(C)$ lying above $frak(q)$ s.t. $k(frak(r)) = k$. Thus, $(Spec(C), frak(r)) -> (Spec(B), frak(q)) -> (Spec(A), frak(m))$ is a chain of etale neighborhoods. 

  Now base change $Spec(C) -> Spec(B)$ along itself, and the projection $p_1: Spec(C otimes_B C) -> Spec(C)$ admits the diagonal map as a section. Thus base changing further to $A^#[h]$, $Spec(R) -> Spec(A^#[h])$ admits a section. Thus $A^#[h]$ is henselian by @equiv-defns-of-henselian (5). 

  (2a) Similarly, for any etale $A^#[sh]$-algebra $R$ with a prime $frak(q)$ above $frak(m) A^#[sh]$, by @passage-to-limit-of-morphisms and @passage-to-limit-of-properties (3d), there exists an etale neighborhood $(B, frak(q)) -> (A, frak(m))$ and a compatible inclusion $phi: k(frak(q)) -> k^sep$ and an etale $B$-algebra $C$ s.t. $R = C otimes_B A^#[sh]$. There also exists a prime $frak(r) in Spec(C)$ above $frak(q)$. 
  
  Now base change $Spec(C) -> Spec(B)$ along itself, and the projection $p_1: Spec(C otimes_B C) -> Spec(C)$ admits the diagonal map as a section. Furthermore, we may arbitrarily choose a compatible inclusion $psi: k(frak(r)) -> k^sep$, making $(C, frak(r), psi)$ a stage in the direct limit defining $A^#[sh]$ that dominates $(B, frak(q), phi)$. Thus base changing $Spec(C) -> Spec(B)$ to this stage gives a section, so further base changing to $Spec(R) -> Spec(A^#[sh])$ also has a section. 

  (1f)(2f) For these universal properties, we need the following lemma. 

  #lemma[
    Let $(R, frak(n))$ be a henselian local ring. Then for any local homomorphism: 
    $
      phi: (A, frak(m)) -> (R, frak(n))
    $
    and any etale neighborhood $(Spec(B), frak(q)) -> (Spec(A), frak(m))$, given any inclusion $iota: k(frak(q)) -> k(R)$ compatible with the inclusion $k(A) -> k(R)$, there is a unique local homomorphism $(B_(frak(q)), frak(q) B_(frak(q))) -> (R, frak(n))$ inducing $iota$. 
  ]
  #proof[
    Put $C = B otimes_A R$, being an etale $R$-algebra, and define a $k(R)$-point of $C$ as: 
    $
      sigma: C = B otimes_A R -> k(R), b otimes r |-> iota([b]) dot [r]
    $
    By @equiv-defns-of-henselian (4), this map lifts uniquely to a section $C -> R$. Composing with $B -> C$ yields a map $B -> R$ sending $frak(n) |-> frak(q)$ on spectra, hence a local homomorphism $(B_(frak(q)), frak(q) B_(frak(q))) -> (R, frak(n))$. Conversely, for any lift $theta: (B_(frak(q)), frak(q) B_(frak(q))) -> (R, frak(n))$, 
    $
      C = B otimes_A R -> R, b otimes r |-> theta(b) r
    $
    must reduce to $sigma$. Thus such a lift $theta$ is unique. 
  ]

  This lemma in either case uniquely lifts $A -> R$ to local homomorphisms $B_(frak(q)) -> R$ for every $B_(frak(q))$ in the directed limit defining $A^#[h]$ or $A^#[sh]$, thus inducing unique lifts $A^#[h] -> R$ and $A^#[sh] -> R$. 
]

An important feature of (strict) henselization is permanence of various desirable properties. 

#proposition(name: <permanence-of-properties-under-henselization>)[
  Let $(A, frak(m))$ be a local ring. Then any of the following properties holds for $A$, if and only if the same property holds for $A^#[h]$ or $A^#[sh]$. 

  0. noetherian, in which case $dim(A) = dim(A^#[h]) = dim(A^#[sh])$; 
  + regular;
  + reduced; 
  + normal;
  + being a DVR. 
]
#proof[
  It suffices to prove equivalences between these properties for $A$ and $A^#[sh]$ only, because $(A^#[h])^#[sh] cong A^#[sh]$. 

  (0) $A -> A^#[sh]$ is faithfully flat, so if $A^#[sh]$ is noetherian, $A$ is noetherian by @noetherianity-normality-descends-along-faithfully-flat-map (1). Conversely, suppose that $A$ is noetherian. Consider the graded rings: 
  $
    G = "gr"_(frak(m)) (A) := oplus.big_(n>=0) frak(m)^n\/frak(m)^(n+1) \
    G' = "gr"_(frak(m) A^#[sh]) (A^#[sh]) := oplus.big_(n>=0) frak(m)^n A^#[sh]\/frak(m)^(n+1) A^#[sh]
  $
  By faithful flatness, 
  $
    G' = G otimes_k k^sep
  $
  Since $A$ is noetherian, $G$ is a finite type $k$-algebra. Thus $G'$ is a finite type $k^sep$-algebra. 

  Now: 

  - $A^#[sh]$ is $frak(m) A^#[sh]$-adically separated. Indeed, if $x in inter.big_(n>=0) frak(m)^n A^#[sh]$, we may assume that $x in B_(frak(q))$ for some $B_(frak(q))$ in the directed limit defining $A^#[sh]$. Note that $A^#[sh]$ is faithfully flat over $B_(frak(q))$ (since $A^#[sh] cong (B_(frak(q)))^#[sh]$ by checking the directed limits). Thus, 
    $
      x in inter.big_(n>=0) (B_(frak(q)) inter frak(m)^n A^#[sh]) = inter.big_(n>=0) frak(m)^n B_(frak(q))
    $
    Since $A$ is noetherian and $B$ is an etale $A$-algebra, $B_(frak(q))$ is noetherian. Thus the intersection above is zero, and $x = 0$. 

  - Since $A^#[sh]$ is $frak(m) A^#[sh]$-adically separated, every nonzero element $f in A^#[sh]$ is in $frak(m)^N A^#[sh] - frak(m)^(N+1) A^#[sh]$ for a unique $N >= 0$. Put $N = "ord"_(frak(m) A^#[sh]) (f)$. Define the initial-form function:
    $
      "in"_(frak(m) A^#[sh]): A^#[sh] &-> G' = oplus.big_(n>=0) frak(m)^n A^#[sh]\/frak(m)^(n+1) A^#[sh] \
      (f in frak(m)^N A^#[sh] - frak(m)^(N+1) A^#[sh]) &|-> ([f] in frak(m)^N A^#[sh]\/frak(m)^(N+1) A^#[sh])
    $
    with $"in"_(frak(m) A^#[sh]) (0) = 0$.

  - For any ideal $I subset A^#[sh]$, define its initial ideal:
    $
      "in"_(frak(m) A^#[sh]) (I) := ({"in"_(frak(m) A^#[sh]) (f) : f in I}) subset G'.
    $
    This is a homogeneous ideal. If $I = 0$, it is already finitely generated, so assume that $I != 0$. Since $"in"_(frak(m) A^#[sh]) (I)$ is generated by initial forms and $G'$ is noetherian, finitely many of those initial forms generate it. Thus, there exist nonzero $f_1, dots.c, f_s in I$ such that:
    $
      "in"_(frak(m) A^#[sh]) (I) = ("in"_(frak(m) A^#[sh]) (f_1), dots.c, "in"_(frak(m) A^#[sh]) (f_s)).
    $
    Now let $0 != f in I$, and put:
    $
      d = "ord"_(frak(m) A^#[sh]) (f), quad d_i = "ord"_(frak(m) A^#[sh]) (f_i).
    $
    Taking the homogeneous degree-$d$ part, there exist homogeneous elements $g_i in G'$ such that:
    $
      "in"_(frak(m) A^#[sh]) (f) = sum_(i=1)^s g_i "in"_(frak(m) A^#[sh]) (f_i) in G',
    $
    where $g_i = 0$ if $d_i > d$, and otherwise $g_i$ has degree $d-d_i$. For each $i$ with $d_i <= d$, pick $a_i in frak(m)^(d-d_i) A^#[sh]$ lifting $g_i$, and set $a_i = 0$ when $d_i > d$. The displayed equality then translates to:
    $
      f - sum_(i=1)^s a_i f_i in I inter frak(m)^(d+1) A^#[sh].
    $
    Put $K = (f_1, dots.c, f_s) A^#[sh] subset I$. Repeating this order-raising step finitely many times, stopping if the remainder becomes zero and otherwise continuing only until any prescribed order $M$ is reached, gives:
    $
      I = K + (I inter frak(m)^M A^#[sh])
    $
    for every $M >= 0$.

  - Now fix $x in I$. Choose one stage $B_(frak(q))$ in the directed limit defining $A^#[sh]$ which contains $x, f_1, dots.c, f_s$, and put:
    $
      K_B = (f_1, dots.c, f_s) B_(frak(q)).
    $
    Thus $K = K_B A^#[sh]$. For every $M >= 0$, the preceding equality gives:
    $
      x in K + (I inter frak(m)^M A^#[sh]) subset K + frak(m)^M A^#[sh] = (K_B + frak(m)^M B_(frak(q))) A^#[sh].
    $
    As noted above, $A^#[sh] cong (B_(frak(q)))^#[sh]$ is faithfully flat over $B_(frak(q))$, so contraction yields:
    $
      x in K_B + frak(m)^M B_(frak(q))
    $
    for every $M >= 0$. The ring $B_(frak(q))$ is noetherian and local, and $frak(m) B_(frak(q))$ is its maximal ideal. Hence Krull's intersection theorem (#cite-stacks("00IP")[Lemma 10.51.4]), applied to $B_(frak(q))\/K_B$, gives:
    $
      inter.big_(M>=0) (K_B + frak(m)^M B_(frak(q))) = K_B.
    $
    Therefore $x in K_B subset K$. Since $x in I$ was arbitrary and $K subset I$, we have $I = K$.

  Thus every ideal of $A^#[sh]$ is finitely generated, so $A^#[sh]$ is noetherian. For dimensions, by #cite-stacks("00ON")[Lemma 10.112.7],
  $
    dim(A^#[sh]) = dim(A) + underbrace(dim(A^#[sh]\/frak(m) A^#[sh]), = dim(k^sep) = 0) = dim(A)
  $

  (1) By (0) we may assume that $A, A^#[sh]$ are both noetherian. Since $frak(m)_(A^#[sh]) = frak(m) A^#[sh]$, flatness gives:
  $
    frak(m) A^#[sh]\/frak(m)^2 A^#[sh] cong frak(m)\/frak(m)^2 otimes_k k^sep.
  $
  Thus the maximal ideals of $A$ and $A^#[sh]$ have the same minimal number of generators. By (0), $dim(A) = dim(A^#[sh])$ as well. Therefore, $A$ is regular if and only if $A^#[sh]$ is.

  (2) If $A^#[sh]$ is reduced, since $A -> A^#[sh]$ is injective, $A$ must be reduced. Conversely, by @etale-local-properties (4), each $B_(frak(q))$ in the directed limit defining $A^#[sh]$ is reduced, so $A^#[sh]$ is reduced. 

  (3) If $A^#[sh]$ is normal, since $A -> A^#[sh]$ is faithfully flat, @noetherianity-normality-descends-along-faithfully-flat-map (2) implies that $A$ is normal. Conversely, by @etale-local-properties (5), each $B_(frak(q))$ in the directed limit defining $A^#[sh]$ is normal, so $A^#[sh]$ is normal. 
  
  (4) A local ring is a DVR if and only if it is noetherian $1$-dimensional and regular. Thus (4) follows from (0)(1). 
]

Next, we prove some miscellaneous properties on henselizations and strict henselizations. They will be used from time to time throughout this document. 

#proposition(name: <henselization-and-directed-limits>)[
  Henselization and strict henselization commute with directed limits: Let $(A_lambda, frak(m)_lambda)$ be a directed system of local rings with transition maps being local homomorphisms. Then the natural maps: 
  $
    dirlim_lambda A_lambda^#[h] -> (dirlim_lambda A_lambda)^#[h]  \
     dirlim_lambda A_lambda^#[sh] -> (dirlim_lambda A_lambda)^#[sh]
  $
  are isomorphisms. (Technically, for strict henselizations, a compatible system of inclusions of separable closures of residue fields must be chosen.)
]
#proof[
  This is formal from the universal properties of henselian local rings. Indeed, for any henselian local ring $(R, frak(n))$, 
  $
    &{dirlim_lambda A_lambda^#[h] -> R #[local homomorphism]} \
    =& invlim_lambda {A_lambda^#[h] -> R #[local homomorphism]} \
    =& invlim_lambda {A_lambda -> R #[local homomorphism]} #[by universal property]\
    =& {dirlim_lambda A_lambda -> R #[local homomorphism]}
  $
  so $dirlim_lambda A_lambda^#[h]$ has the universal property of $(dirlim_lambda A_lambda)^#[h]$. It is also henselian since Hensel's lemma for every polynomial can be checked at a finite stage $A_lambda^#[h]$. Thus we have a natural isomorphism: 
  $
    dirlim_lambda A_lambda^#[h] ->^tilde (dirlim_lambda A_lambda)^#[h]
  $ 
  A similar argument holds for strict henselization. 
]

#lemma(name: <henselization-and-quotients>)[
  (Strict) henselization commutes with taking quotients. For a local ring $(A, frak(m))$ and an ideal $I subset frak(m)$, 
  $
    (A\/I)^#[h] cong A^#[h]\/I A^#[h] \
    (A\/I)^#[sh] cong A^#[sh]\/I A^#[sh]
  $
]
#proof[
  This is formal from the universal properties. Indeed, $A^#[h]\/I A^#[h]$ remains henselian since every finite $A^#[h]\/I A^#[h]$-algebra is a finite $A^#[h]$-algebra, thus splits into a finite product of local rings. Now for a henselian local ring $R$, 
  $
    & {A\/I -> R #[local homomorphism]} \
    =& {A -> R #[local homomorphism killing $I$]} \
    =& {A^#[h] -> R #[local homomorphism killing $I$]} \
    =& {A^#[h]\/I A^#[h] -> R #[local homomorphism]}
  $
  and so $(A\/I)^#[h] cong A^#[h]\/I A^#[h]$ by the universal property of henselization. The same formal argument holds for strict henselization. 
]

#lemma[
  For any local ring $(A, frak(m))$ with residue field $k$, the natural map: 
  $
    (A^#[h])^#[sh] -> A^#[sh]
  $
  is an isomorphism (with the choice of $k arrow.hook k^sep$ fixed). 
]
#proof[
  This is formal. For any strict henselian local ring $(R, frak(n))$ and a fixed inclusion $iota: k^sep -> k(R)$: 
  $
    &{(A^#[h])^#[sh] -> R #[local homomorphism compatible with] iota} \
    =& {A^#[h] -> R #[local homomorphism]} \
    =& {A -> R #[local homomorphism]} \
    =& {A^#[sh] -> R #[local homomorphism compatible with] iota}
  $
  Both $(A^#[h])^#[sh]$ and $A^#[sh]$ are strict henselian. Thus $(A^#[h])^#[sh] cong A^#[sh]$. 
]

#lemma[
  For any local ring $(A, frak(m))$, the natural maps: 
  $
    A\/frak(m)^N -> A^#[h]\/frak(m)^N A^#[h]
  $
  are isomorphisms for all $N >= 1$. Consequently, the natural map between completions: 
  $
    hat(A) -> hat(A^#[h])
  $
  is an isomorphism. 
]
#proof[
  Indeed, 
  $
    A^#[h]\/frak(m)^N A^#[h] &cong dircolim_((Spec(B),frak(q)) -> (Spec(A),frak(m)) #[etale] \ k(frak(q)) = k) B_(frak(q))\/frak(m)^N B_(frak(q)) \
    &cong dircolim_((Spec(B),frak(q)) -> (Spec(A),frak(m)) #[etale] \ k(frak(q)) = k) A\/frak(m)^N #[by @etale-map-with-stable-residue-field-preserves-completions]\
    &cong A\/frak(m)^N
  $
]

#lemma(name: <inverting-nonzeros-in-henselization>)[
  + Let $A$ be a normal local domain and $S = A - {0}$. Then: #h(1fr)
    $
      S^(-1) A^#[h] = dircolim_((Spec(B),frak(q)) -> (Spec(A),frak(m)) #[etale] \ k(frak(q)) = k) Frac(B_(frak(q))) = Frac(A^#[h]) \
      S^(-1) A^#[sh] = dircolim_((Spec(B),frak(q)) -> (Spec(A),frak(m)) #[etale] \ phi: k(frak(q)) arrow.hook k^sep) Frac(B_(frak(q))) = Frac(A^#[sh])
    $
    In particular, both of these rings are fields. 

  + Let $A arrow.hook B$ be an inclusion of normal local domains. Then the induced maps: 
    $
      A^#[h] -> B^#[h], A^#[sh] -> B^#[sh]
    $
    are both inclusions. 
]
#proof[
  (1) Since localization commutes with directed limits, for the limit part, it suffices to show that $S^(-1) B_(frak(q)) = Frac(B_(frak(q)))$ for every pointed etale $(Spec(B), frak(q)) -> (Spec(A), frak(m))$. 

  Indeed, $S^(-1) B$ is an etale $S^(-1) A = Frac(A)$-algebra. It is thus necessarily a finite product of finite separable extensions of $S^(-1) A$. Thus $S^(-1) B_(frak(q))$, as a localization of $S^(-1) B$, is a finite product of fields. However $B_(frak(q))$ is integral, and so $S^(-1) B_(frak(q))$ is integral. Thus $S^(-1) B_(frak(q))$ is necessarily a field. Now we apply the following fact: 

  - If $A$ is an integral domain and $S subset A - {0}$ a multiplicative subset s.t. $S^(-1) A$ is a field, then $S^(-1) A = Frac(A)$. 

    Indeed, every element $0 != a in A subset S^(-1) A$ has an inverse in $S^(-1) A$. Thus $a^(-1) in S^(-1) A$, and so $S^(-1) A$ contains all of $Frac(A)$. 

  Hence, $S^(-1) B_(frak(q)) = Frac(B_(frak(q)))$ and both limit statements are proved. Now $S^(-1) A^#[h], S^(-1) A^#[sh]$ are both fields, so applying the fact above again, they are $Frac(A^#[h]), Frac(A^#[sh])$ respectively. 

  (2) Put $S = A - {0}$. Note that $S^(-1) A^#[h] -> S^(-1) B^#[h]$ is injective since $S^(-1) A^#[h] = Frac(A^#[h])$ is a field. Since $A$ is a domain, $A^#[h] -> S^(-1) A^#[h]$ is injective. Thus the map: 
  $
    A^#[h] -> S^(-1) B^#[h]
  $
  is injective. Hence $A^#[h] -> B^#[h]$ is injective. The same argument holds for strict henselizations. 
]

#lemma(name: <henselization-and-finite-base-change>)[
  Let $(A, frak(m))$ be a local ring with residue field $k$, and $B$ be a finite $A$-algebra. Let $frak(q)_1, dots.c, frak(q)_m in Spec(B)$ be the primes of $B$ lying above $frak(m) in Spec(A)$. Then: 
  $
    B otimes_A A^#[h] cong product_(i=1)^m B_(frak(q)_i)^#[h]
  $
]
#proof[
  Put $C = B otimes_A A^#[h]$. Then:
  
  - By @equiv-defns-of-henselian (1), points of $Spec(C\/frak(m) C)$ correspond bijectively to connected components of $Spec(C)$; 

  - By definition, $C\/frak(m) C cong B\/frak(m) B$. Let $frak(n)_1, dots.c, frak(n)_m in Spec(C)$ lie above $frak(q)_1, dots.c, frak(q)_m$. 

  Then: 
  $
    C cong C_(frak(n)_1) times dots.c times C_(frak(n)_m)
  $
  with every factor henselian. We have natural maps $B_(frak(q)_i) -> C_(frak(n)_i)$ from $Spec(C) -> Spec(B)$, hence by the universal property of henselization, natural maps: 
  $
    B_(frak(q)_i)^#[h] -> C_(frak(n)_i)
  $
  Conversely, by the universal property of henselization, there is a local map $A^#[h] -> B_(frak(q)_i)^#[h]$. Hence we have maps: 
  $
    C = B otimes_A A^#[h] -> B_(frak(q)_i)^#[h] otimes_A B_(frak(q)_i)^#[h] -> B_(frak(q)_i)^#[h]
  $
  One may check that $frak(n)_i$ lies above the maximal ideal. Thus it induces a map $C_(frak(n)_i) -> B_(frak(q)_i)^#[h]$. It is formal by the universal properties to check that this map inverts the map $B_(frak(q)_i)^#[h] -> C_(frak(n)_i)$ constructed above. 
]

#lemma(name: <strict-henselization-and-finite-base-change>)[
  Let $(A, frak(m))$ be a local ring with residue field $k$, and $B$ be a finite $A$-algebra. Let $frak(q)_1, dots.c, frak(q)_m in Spec(B)$ be the primes of $B$ lying above $frak(m) in Spec(A)$. 
  
  Let $k -> Omega$ be the inclusion of $k$ into an algebraically closed field. For each $frak(q)_i$, let $phi_(i,j): k(frak(q)_i) -> Omega$ be all inclusions compatible with $k -> Omega$. Let: 

  - $A^#[sh]$ be the strict henselization of $A$ relative to the inclusion $k -> k^sep$ where $k^sep$ is the subfield of $Omega$ consisting of all separable algebraic elements over $k$; 

  - $B_(frak(q)_i)^(#[sh],j)$ be the strict henselization of $B_(frak(q)_i)$ relative to the inclusion $k(frak(q)_i) -> k(frak(q)_i)^sep -> Omega$ where $k(frak(q)_i)^sep$ is the subfield of $Omega$ consisting of all separable algebraic elements over $k(frak(q)_i)$. 

  Then: 
  $
    B otimes_A A^#[sh] cong product_(i,j) B_(frak(q)_i)^(#[sh],j)
  $
]
#proof[
  Put $C = B otimes_A A^#[sh]$. Its special fiber is: 
  $
    C\/frak(m) C cong B otimes_A k^sep.
  $
  The points of this fiber are naturally indexed by the pairs $(i,j)$: the point corresponding to $(i,j)$ is the kernel of the map induced by $phi_(i,j)$,
  $
    k(frak(q)_i) otimes_k k^sep -> Omega.
  $
  Let $frak(n)_(i,j)$ be the corresponding primes of $C$. Since $A^#[sh]$ is henselian, @equiv-defns-of-henselian (1) gives: 
  $
    C cong product_(i,j) C_(frak(n)_(i,j)).
  $
  Every factor is henselian, and its residue field is the composite field $phi_(i,j)(k(frak(q)_i)) k^sep subset Omega$. This is a purely inseparable extension of the separably closed field $k^sep$, hence is separably closed. Thus every $C_(frak(n)_(i,j))$ is strictly henselian.

  The natural local map $B_(frak(q)_i) -> C_(frak(n)_(i,j))$ is compatible with the chosen embedding into $Omega$, so the universal property of strict henselization gives a map: 
  $
    B_(frak(q)_i)^(#[sh],j) -> C_(frak(n)_(i,j)).
  $

  Conversely, the chosen inclusions $k^sep subset k(frak(q)_i)^sep subset
  Omega$ give a local map $A^#[sh] -> B_(frak(q)_i)^(#[sh],j)$. Together with
  $B -> B_(frak(q)_i)^(#[sh],j)$ it induces: 
  $
    C = B otimes_A A^#[sh] -> B_(frak(q)_i)^(#[sh],j),
  $
  which localizes at $frak(n)_(i,j)$. By the two universal properties, the resulting maps are inverse. Taking their product proves the claim.
]
