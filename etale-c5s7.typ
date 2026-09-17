#import "void-import.typ": *

== Etale cohomology of curves <sect-cohom-of-curves>
#let Jac = math.op[Jac]
In this section, we use the word "curve" to denote an integral, separated scheme of finite type and dimension $1$ over a field $k$. We do not assume that a curve is necessarily nonsingular (i.e. smooth over $k$), and will use the word "smooth curve" when we make that assumption. However, we always assume that a curve is integral, hence connected. 

In this section, we are finally ready to explicitly compute the first nontrivial example of etale cohomology: the etale cohomology of a smooth curve. Specifically, a curve is either projective or affine, and we will establish the following results: 

- $H^q_et (X, ZZ\/n) = 0$ for any curve $X$ over an algebraically closed field $k$ and any natural number $n >= 1$, whenever $q >= 3$. 

- If $X$ is a projective smooth curve over an algebraically closed field $k$ and $"char"(k) divides.not n$ (which includes the case $"char"(k) = 0$), then: #h(1fr)
  $
    H^q_et (X, ZZ\/n) cong cases(
      ZZ\/n &\, q = 0, 
      (ZZ\/n)^(oplus 2g(X)) &\, q = 1, 
      ZZ\/n &\, q = 2, 
      0 &\, q >= 3
    )
  $

- If $p = "char"(k) > 0$ and $X$ is a smooth curve (whether affine or projective) over an algebraically closed field $k$, then: 
  $
    H^2_et (X, ZZ\/p) = 0
  $

- If $X$ is an affine curve over an algebraically closed field $k$, then for any $n >= 1$, 
  $
    H^2_et (X, ZZ\/n) = 0
  $

We start with the cohomology of $GG_m$, and the vanishing of cohomology of $ZZ\/n$ in degree $>=3$ first. 

#proposition(name: <divisor-exact-sequence>)[
  (Divisor sequence) Let $X$ be a smooth curve over an algebraically closed field $k$, with $j: eta = Spec(K) -> X$, where $eta$ is the generic point of $X$, and $K$ its function field. Then there is an exact sequence: 
  $
    0 -> GG_m -> j_* GG_(m,eta) ->^#[div] oplus.big_(x in abs(X)) x_* ul(ZZ) -> 0
  $
]
#proof[
  Since $X$ is noetherian, every $U in Et_X$ is locally noetherian, hence locally connected. It is thus the disjoint union of its connected components, so it suffices to define this sequence for any connected $U in Et_X$. 
  
  Such $U$ is smooth of relative dimension $1$ over $k$, hence nonsingular. Since it is connected, it is integral. The theory of Weil divisors thus holds on $U$. Furthermore, $U -> X$ is of finite type over $k$, so it sends closed points to closed points. Thus, the fiber of the generic point $eta in X$ in $U$ is the generic point $eta_U$ of $U$, and so $j_* GG_(m,eta) (U) = GG_(m,eta) (eta_U) = cal(O)_(U,eta_U)^times = K(U)^times$. 
  
  We define the morphisms by: 
  $
    0 -> cal(O)_U (U)^times arrow.r.hook K(U)^times ->^#[div] oplus.big_(u in abs(U)) ZZ 
  $
  where the first map is just inclusion of functors, and the second map is evaluation of a function in $K(U)^times$ at the valuations associated with closed points of $U$. From the theory of Weil divisors, this sequence is left exact. Exactness in the middle is more or less the following algebraic fact: 
  #fact[
    Let $A$ be a noetherian integrally closed domain. Then: 
    $
      A = inter.big_(frak(p) in Spec(A) \ "ht"(frak(p)) = 1) A_(frak(p))
    $
    where the intersection is taken in $Frac(A)$. 
  ]
  
  As such, we have obtained a left exact sequence: 
  $
    0 -> GG_m -> j_* GG_(m,eta) ->^#[div] oplus.big_(x in abs(X)) x_* ul(ZZ)
  $
  It remains to prove that it is right exact, i.e. a divisor $d in oplus.big_(u in abs(U)) ZZ$ comes from a function $K(U)^times$ etale locally in $U$. But this holds Zariski locally in $U$, as $U$ is nonsingular, hence locally factorial, and so every Weil divisor on $U$ is Zariski locally principal. 
]

// #lemma[
//   Let $X$ be a scheme of finite type over an algebraically closed field $k$. Then: 
  
//   + If $x in abs(X)$ is a closed point, then the skyscraper sheaf $x_* M$ satisfies: #h(1fr)
//     $
//       (x_* M)_(ol(y)) = cases(
//         M &\, y = x, 
//         0 &\, y != x
//       )
//     $
//     for any geometric point $ol(y)$ lying above $y in X$. 

//   + If any $cal(F)_(ol(x)) $
// ]

#proposition[
  Let $X$ be a smooth curve over an algebraically closed field $k$. Then there are canonical isomorphisms: 
  $
    H^q_et (X, GG_m) cong cases(
      cal(O)_X (X)^times &\, q = 0, 
      Pic(X) &\, q = 1, 
      0 &\, q >= 2
    )
  $
]
#proof[
  The $q = 0$ case is just global sections, and the $q = 1$ case is @h1-of-gm-is-pic. As such, it suffices to prove vanishing in degrees $q >= 2$. 

  We then consider the divisor exact sequence: 
  $
    0 -> GG_m -> j_* GG_(m,eta) ->^#[div] oplus.big_(x in abs(X)) x_* ul(ZZ) -> 0
  $
  giving a long exact sequence: 
  $
    dots.c -> H^(q-1) (X, oplus.big_(x in abs(X)) x_* ul(ZZ)) -> H^q (X, GG_m) -> H^q (X, j_* GG_(m,eta)) -> dots.c
  $
  Thus, to show that $H^q (X, GG_m) = 0$, it suffices to show that: 
  
  - $H^(q-1) (X, oplus.big_(x in abs(X)) x_* ul(ZZ)) = 0$; 

  - $H^q (X, j_* GG_(m,eta)) = 0$. 

  The first point is easy: 
  $
    & H^(q-1) (X, oplus.big_(x in abs(X)) x_* ul(ZZ)) = oplus.big_(x in abs(X)) H^(q-1) (X, x_* ul(ZZ)) \
    =& oplus.big_(x in abs(X)) H^(q-1) (x, ul(ZZ)) #[by @pushforward-by-finite-morphism, since the inclusion $x: x -> X$ is a closed immersion, hence finite] \
    =& 0 #[since each $x = Spec(k(x))$ where $k(x) = k$ is algebraically closed, and $q - 1 >= 1$]
  $
  so it remains to prove that $H^q (X, j_* GG_(m,eta)) = 0$. 

  #lemma(name: <gm-generic-pushforward-higher-vanishing>)[
    $R^q j_* GG_(m,eta) = 0$ for all $q >= 1$. 
  ]
  #proof[
    Since $X$ is finite type over a field $k$, its closed points are very dense. As such, it suffices to show that for all closed points $x in abs(X)$, 
    $
      (R^q j_* GG_(m,eta))_x = 0
    $
    By @stalks-of-derived-lowerstar, this is equivalent to: 
    $
      H^q (eta times_X tilde(X)_x, GG_(m,eta)|_(eta times_X tilde(X)_x)) = 0
    $
    By our arguments in @divisor-exact-sequence, every connected $U in Et_X$ is nonsingular of dimension $1$, and $eta times_X U = eta_U = Spec(K(U))$ the generic point of $U$ (by @inverting-nonzeros-in-henselization (1)). Such $U$ are also cofinal among etale neighborhoods of $(X, x)$. As such, 
    $
      eta times_X tilde(X)_x &= lim_((U,ol(u)) -> (X,x) \ #[connected]) eta times_X U = lim_((U,ol(u)) -> (X,x) \ #[connected]) Spec(K(U)) \
      &= Spec(dircolim_((U,ol(u)) -> (X,x) \ #[connected])K(U))
    $
    Take $L = dircolim_((U,ol(u)) -> (X,x) \ #[connected]) K(U)$. Each $K(U)$ is a field of transcendence degree $1$ over $k$, and so $L$ is a field of transcendence degree $1$ over $k$. Furthermore, each $K(U)\/K(X)$ is finite separable by definition of unramifiedness. Therefore, $L\/K(X)$ is an algebraic separable extension. It remains to prove that: 
    $
      H^q (Spec(L), GG_(m,eta)|_(Spec(L))) = 0
    $

    #lemma[
      Given a separable algebraic extension $L\/K$, we have a canonical isomorphism: 
      $
        GG_(m,Spec(K))|_(Spec(L)) = GG_(m,Spec(L))
      $
    ]
    #proof[
      Taking stalks at $Spec(L^sep) = Spec(K^sep)$, both sides result in the $Gal_L$-module $(K^sep)^times$. We are thereby done by @struct-of-spec-k-et. 
    ]

    Since $L\/K(X)$ is algebraic separable, 
    $
      H^q (Spec(L), GG_(m,eta)|_(Spec(L))) = H^q (Spec(L), GG_(m,Spec(L))) = H^q_#[cont] (Gal_L, (L^sep)^times)
    $
    vanishes since $L$ is of transcendence degree $1$ over the algebraically closed field $k$, by @tsen-thm-in-galois-cohom (2) as a consequence of Tsen's theorem. 
  ]

  Since $R^q j_* GG_(m,eta) = 0$ for all $q >= 1$, the Leray spectral sequence: 
  $
    E_2^(p,q) = H^p (X, R^q j_* GG_(m,eta)) ==> H^(p+q) (eta, GG_(m,eta))
  $
  degenerates, giving isomorphisms: 
  $
    H^p (X, j_* GG_(m,eta)) cong H^p (eta, GG_(m,eta))
  $
  for all $p$. Thus, for $q >= 1$, 
  $
    H^q (X, j_* GG_(m,eta)) cong H^q (eta, GG_(m,eta)) = H^q_#[cont] (Gal_(K(X)), (K(X)^sep)^times) = 0
  $
  since $K(X)$ is of transcendence degree $1$ over the algebraically closed field $k$, by @tsen-thm-in-galois-cohom (2), as a consequence of Tsen's theorem. 
]

#corollary(name: <cohom-of-gm-on-general-curve>)[
  Let $X$ be any curve over an algebraically closed field $k$. Then there are canonical isomorphisms:
  $
    H^q_et (X, GG_m) cong cases(
      cal(O)_X (X)^times & \, q = 0,
      Pic(X) & \, q = 1,
      0 & \, q >= 2
    )
  $
]
#proof[
  The $q = 0$ case is just global sections, and the $q = 1$ case is @h1-of-gm-is-pic. As such, it suffices to prove vanishing in degrees $q >= 2$. Consider the normalization: 
  $
    nu: tilde(X) -> X
  $
  where $nu$ is finite surjective, $tilde(X)$ is a smooth curve over $k$, and there exists a nonempty open set $V subset X$ (the nonsingular locus of $X$) s.t. $nu: nu^(-1) (V) -> V$ is an isomorphism. Consider the morphism: 
  $
    GG_m -> nu_* GG_(m,tilde(X))
  $
  defined on slices as $cal(O)_U (U)^times -> cal(O)_(tilde(U)) (tilde(U))^times$ for any $U in Et_X, tilde(U) = U times_X tilde(X)$. This map is injective for the following reason: We have a morphism $cal(O)_X -> nu_* cal(O)_(tilde(X))$, injective by construction of the normalization. Since $f: U -> X$ is etale, hence flat, the map $f^* cal(O)_X -> f^* nu_* cal(O)_(tilde(X))$ is injective. Since we may base change quasi-coherent sheaves along flat morphisms, $f^* nu_* cal(O)_(tilde(X)) cong nu'_* f'^* cal(O)_(tilde(X))$ canonically, where $f': tilde(U) -> tilde(X), nu': tilde(U) -> U$. In other words, the morphism $cal(O)_U -> nu'_* cal(O)_(tilde(U))$ is injective, and so $cal(O)_U (U) -> cal(O)_(tilde(U)) (tilde(U))$ is injective. Thus the morphism on units is injective. 

  We form the cokernel of $GG_m -> nu_* GG_(m,tilde(X))$: 
  $
    0 -> GG_m -> nu_* GG_(m,tilde(X)) -> cal(R) -> 0
  $
  Since $nu$ induces an isomorphism $nu^(-1) (V) -> V$, $GG_m -> nu_* GG_(m,tilde(X))$ is an isomorphism on all sections on $U in Et_X$ whose image lies in $V$. Thus, passing to the stalks, $GG_m -> nu_* GG_(m,tilde(X))$ is an isomorphism on all geometric points above $V$. In other words, $cal(R)$ has zero stalks on all geometric points above $V$, so its pullback to $V$ is zero. Take $Z = X - V$, a finite set of closed points, and the closed immersion $i: Z -> X$. Then by @pushforward-by-closed-immersion (1), there exists $cal(R)_0 in cAb(Z_et)$ s.t: 
  $
    cal(R) cong i_* cal(R)_0
  $
  Now from the normalization sequence, we have a long exact sequence: 
  $
    dots.c -> H^(q-1) (X, cal(R)) -> H^q (X, GG_m) -> H^q (X, nu_* GG_(m,tilde(X))) -> dots.c
  $
  For $q >= 2$, 

  - By @pushforward-by-finite-morphism, $H^(q-1) (X, cal(R)) = H^(q-1) (X, i_* cal(R)_0) = H^(q-1) (Z, cal(R)_0) = 0$, as $q - 1 >= 1$, and $Z$ is a disjoint union of $Spec(k)$ where $k$ is algebraically closed. 

  - By @pushforward-by-finite-morphism, since the normalization $nu$ is finite, $H^q (X, nu_* GG_(m,tilde(X))) = H^q (tilde(X), GG_(m,tilde(X)))$, which is $0$ by our result for smooth curves. 

  Therefore, $H^q (X, GG_m) = 0$. 
]

#lemma(name: <mu-n-is-zn>)[
  Let $X$ be a scheme over a strict henselian local ring $(A, frak(m), k)$, and $n>=1$ be a natural number s.t. $n in k^times$. Then for any choice of a primitive $n$-th root of unity $zeta in k$, there is an isomorphism: 
  $
    mu_n cong ul(ZZ\/n) in cAb(X_et)
  $
]
#proof[
  Since $n in k^times$ and $k$ is separably closed, $k$ has $n$ distinct $n$-th roots of unity. By Hensel's lemma, $A$ also has $n$ distinct $n$-th roots of unity. Fix a primitive $n$-th root of unity $zeta in A$. 

  We now define a presheaf morphism: 
  $
    ul(ZZ\/n)_0 -> mu_n
  $
  by sending $ZZ\/n -> mu_n (U), [m] |-> zeta^m$ for all $U in Et_X$, where $mu_n (k) subset mu_n (U)$. This presheaf morphism is injective on the section level, hence injective. Passing to the sheafification, we have an injective sheaf morphism: 
  $
    ul(ZZ\/n) -> mu_n
  $
  Thus, it suffices to prove that this morphism is surjective. For any geometric point $ol(x)$ of $X$, 
  $
    (mu_n)_(ol(x)) &= dircolim_((U,ol(u)) -> (X,ol(x))) mu_n (cal(O)_U (U)) \
    &= mu_n (dircolim_((U,ol(u)) -> (X,ol(x))) cal(O)_U (U)) #[as can be checked elementarily] \
    &= mu_n (cal(O)_(X,ol(x)))
  $
  can be expressed using the strict local ring at $X$. 

  #lemma[
    Let $(A, frak(m), k)$ be a henselian local ring with $k$ containing $n$ distinct $n$-th roots of unity, and $(R, frak(n))$ be a local $A$-algebra. Then: 
    $
      mu_n (R) = mu_n (A) cong ZZ\/n
    $
  ]
  #proof[
    Let $1, zeta, dots.c, zeta^(n-1) in A^times$ be the $n$ distinct $n$-th roots of unity in $A$. If $r in R$ satisfies $r^n = 1 in R$, then: 
    $
      product_(j=0)^(n-1) (r - zeta^j) = 0 in R
    $
    and so there exists some $0 <= j < n$ s.t. $r - zeta^j in frak(n)$. If for another $0 <= i < n$, $r - zeta^i in frak(n)$ too, then $zeta^i - zeta^j in frak(n)$ is not a unit of $R$. However, this element has nonzero image in $k^times$, hence is in $A^times$ and so $R^times$, a contradiction. 

    As such, for all $0 <= i < n$ with $i != j$, $r - zeta^i in R - frak(n) = R^times$. Cancelling away these elements, we see $r = zeta^j$. 
  ]
  Thus, $(mu_n)_(ol(x)) cong ZZ\/n$ abstractly. Now the morphism $ul(ZZ\/n) -> mu_n$ induces injective morphisms $ZZ\/n -> (mu_n)_(ol(x)) cong ZZ\/n$ on stalks. Since $ZZ\/n$ is finite, such a morphism is surjective. As such, we have constructed a non-canonical isomorphism: 
  $
    mu_n cong ul(ZZ\/n)
  $
]

#theorem(name: <cohom-of-general-curve>)[
  Let $X$ be any curve over an algebraically closed field $k$. 

  + For any natural number $n in k^times$, we have canonical isomorphisms: #h(1fr)
    $
      H^q_et (X, mu_n) = cases(
        mu_n (k) &\, q = 0, 
        Pic(X)\/n Pic(X) &\, q = 2, 
        0&\, q >= 3
      )
    $

  + If $p = "char"(k) > 0$, then: 
    $
      H^q_et (X, ZZ\/p) = cases(
        ZZ\/p &\, q = 0, 
        0 &\, q >= 3
      ) 
    $

  + For all natural numbers $n >= 1$, whenever $q >= 3$, 
    $
      H^q_et (X, ZZ\/n) = 0
    $
]
#proof[
  (1) Consider the Kummer sequence: 
  $
    0 -> mu_n -> GG_m ->^((-)^n) GG_m -> 0
  $
  inducing a long exact sequence. In low degrees, using $H^1_et (X, GG_m) = Pic(X)$, this is: 
  $
    0 &-> H^0_et (X, mu_n) -> cal(O)_X (X)^times ->^((-)^n) cal(O)_X (X)^times \
    &-> H^1_et (X, mu_n) -> Pic(X) ->^((-)^(otimes n)) Pic(X) \
    &-> H^2_et (X, mu_n) -> H^2_et (X, GG_m) = 0
  $
  This identifies: 
  $
    H^0_et (X, mu_n) = mu_n (k) \
    H^2_et (X, mu_n) = coker(Pic(X) ->^((-)^(otimes n)) Pic(X)) = Pic(X)\/n Pic(X)
  $
  For degree $q >= 3$, the long exact sequence gives: 
  $
    dots.c -> underbrace(H^(q-1) (X, GG_m), 0) -> H^q (X, mu_n) -> underbrace(H^q (X, GG_m), 0) -> dots.c
  $
  identifying $H^q (X, mu_n) = 0$. 

  (2) Consider the Artin-Schreier sequence:
  $
    0 -> ul(ZZ\/p) -> GG_a -->^(x |-> x^p - x) GG_a -> 0
  $
  In degree $0$, we have $H^0_et (X, ZZ\/p) = ZZ\/p$ by global sections. In degrees $q >= 3$, we have: 
  $
    dots.c -> H^(q-1)_et (X, GG_a) -> H^q_et (X, ZZ\/p) -> H^q_et (X, GG_a) -> dots.c
  $
  However, for $r >= 2$, 
  $
    H^r_et (X, GG_a) = H^r_#[Zar] (X, cal(O)_X) = 0
  $
  since $dim(X) = 1$ and Zariski cohomology vanishes beyond the dimension. Thus, whenever $q >= 3$, $H^(q-1)_et (X, GG_a) = H^q_et (X, GG_a) = 0$, and so: 
  $
    H^q_et (X, ZZ\/p) = 0
  $

  (3) By (1)(2) and the previous lemma, 
  $
    H^q_et (X, ZZ\/p) = 0
  $
  for all primes $p$ and degrees $q >= 3$. We may then conclude using the exact sequence $0 -> ZZ\/n -> ZZ\/m n -> ZZ\/m -> 0$, inducing exact: 
  $
    dots.c -> H^q_et (X, ZZ\/n) -> H^q_et (X, ZZ\/m n) -> H^q_et (X, ZZ\/m) -> dots.c
  $
]

Next, we explicitly compute the cohomology for a projective smooth curve. 

#theorem(name: <cohom-of-proj-curve>)[
  If $X$ is a projective curve over an algebraically closed field $k$ and $"char"(k) divides.not n$ (which includes the case $"char"(k) = 0$), then: #h(1fr)

  + There are canonical isomorphisms: #h(1fr)
    $
      H^q_et (X, mu_n) cong cases(
        mu_n (k) & \, q = 0,
        Pic(X)[n] & \, q = 1,
        Pic(X)\/n Pic(X) ->^deg_tilde ZZ\/n & \, q = 2,
        0 & \, q >= 3
      )
    $
    and whenever $X$ is smooth, non-canonical isomorphisms: 
    $
      H^q_et (X, ZZ\/n) cong cases(
        ZZ\/n & \, q = 0,
        (ZZ\/n)^(oplus 2g(X)) & \, q = 1,
        ZZ\/n & \, q = 2,
        0 & \, q >= 3
      )
    $

  + If $p = "char"(k) > 0$, then there are non-canonical isomorphisms:
    $
      H^q_et (X, ZZ\/p) cong cases(
        ZZ\/p &\, q = 0, 
        (ZZ\/p)^(oplus gamma(X)) &\, q = 1, 
        0 &\, q >= 2
      )
    $
    for an invariant $0 <= gamma(X) <= g(X)$, called the *Hasse-Witt invariant* associated with the curve $X$. 

  + If $p = "char"(k) > 0$, then $H^q_et (X, ZZ\/p^a) = 0$ for all $q >= 2$. 
]
#proof[
  (1) Since $X$ is projective, $cal(O)_X^times = k^times$. Indeed, $cal(O)_X (X) = k$:
  
  - The reason is that $cal(O)_X (X)$ is a reduced finite-dimensional $k$-algebra, hence a product of copies of $k$. If it is a product of more than one copy of $k$, then an idempotent splits $X$ into two closed and open sets, which is impossible since $X$ is connected. 
  
  Consider the long exact sequence in low degrees, induced by the Kummer sequence: 
  $
     0 & -> H^0_et (X, mu_n) -> k^times ->^((-)^n) k^times \
       & -> H^1_et (X, mu_n) -> Pic(X) ->^((-)^(otimes n)) Pic(X) \
       & -> H^2_et (X, mu_n) -> 0
  $
  $k^times ->^((-)^n) k^times$ is surjective, since $k$ is algebraically closed. As such, the connecting morphism $k^times -> H^1_et (X, mu_n)$ is zero. Thus, 
  $
    H^1_et (X, mu_n) = ker(Pic(X) ->^((-)^(otimes n)) Pic(X)) = Pic(X)[n]
  $
  and: 
  $
    H^2_et (X, mu_n) = coker(Pic(X) ->^((-)^(otimes n)) Pic(X)) = Pic(X)\/n Pic(X)
  $
  From the theory of abelian varieties: 
  #fact[
    If $X$ is a smooth projective curve over an algebraically closed field $k$, there exists an exact sequence: 
    $
      0 -> Pic^0 (X) -> Pic(X) ->^deg ZZ -> 0
    $
    and an abelian variety $Jac(X)$ over $k$ so that $Pic^0 (X) cong Jac(X)(k)$ is identified with the $k$-points of $Jac(X)$. Furthermore, $times n: Jac(X)(k) -> Jac(X)(k)$ is surjective with kernel isomorphic to $(ZZ\/n)^(oplus 2g(X))$. 
  ]
  Using this fact, 
  $
    H^1_et (X, mu_n) = Pic(X)[n] cong Pic^0 (X)[n] cong (ZZ\/n)^(oplus 2g(X))
  $
  $
    H^2_et (X, mu_n) = Pic(X)\/n Pic(X) cong ZZ\/n
  $
  and we are done. 

  (2) From the Artin-Schreier sequence:
  $
    0 -> ul(ZZ\/p) -> GG_a ->^(wp) GG_a -> 0 
  $
  where $wp: x |-> x^p - x$, we get an exact sequence: 
  $
    0 &-> ZZ\/p -> k ->^wp k \
    &-> H^1_et (X, ZZ\/p) -> H^1_et (X, GG_a) -->^(H^1 (wp)) H^1_et (X, GG_a) \
    &-> H^2_et (X, ZZ\/p) -> 0
  $
  Since $k$ is algebraically closed, $wp: k -> k$ is surjective (as every equation $X^p - X = c$ for $c in k$ has a root in $k$), so the connecting morphism $k -> H^1_et (X, ZZ\/p)$ is zero. Furthermore, $H^1_et (X, GG_a) = H^1_#[Zar] (X, cal(O)_X)$. As such, 
  $
    H^1_et (X, ZZ\/p) = ker(H^1 (wp): H^1_#[Zar] (X, cal(O)_X) -> H^1_#[Zar] (X, cal(O)_X)) \
    H^2_et (X, ZZ\/p) = coker(H^1 (wp): H^1_#[Zar] (X, cal(O)_X) -> H^1_#[Zar] (X, cal(O)_X))
  $
  Since $X$ is projective over $k$, $V = H^1_#[Zar] (X, cal(O)_X)$ is a finite-dimensional $k$-vector space. The Frobenius $F: cal(O)_X -> cal(O)_X, x |-> x^p$ satisfies $F(c x) = c^p F(x)$ and $wp = F - id$. Therefore, the morphism $wp := H^1 (wp): V -> V$ can be written as $wp = F - id$ for some additive $F: V -> V$ satisfying $F(c x) = c^p F(x)$. 

  #lemma[
    Let $k$ be an algebraically closed field of characteristic $p$, $V$ be a finite-dimensional $k$-vector space, and: 
    $
      F: V -> V
    $
    be a $p$-linear map, i.e. an $FF_p$-linear map satisfying $F(c v) = c^p F(v)$ for all $c in k, v in V$. Then there exists a decomposition: 
    $
      V = V_#[ss] oplus V_#[nil]
    $
    into $F$-stable $k$-linear subspaces, such that: 

    - $V_#[ss]$ is spanned by fixed points of $F$, and $F: V_#[ss] -> V_#[ss]$ is bijective. 

    - $F: V_#[nil] -> V_#[nil]$ is nilpotent. 
  ]
  #proof[
    Since each $F^m$ is $p^m$-linear, the subsets $im(F^m)$ and $ker(F^m)$ are in fact $k$-linear subspaces of $V$. Indeed, if $v = F^m w in im(F^m)$, then $c v = F^m (c^(1\/p^m) w) in im(F^m)$. If $v in ker(F^m)$, then $F^m (c v) = c^(p^m) F^m(v) = 0$ and so $c v in ker(F^m)$. 

    Take: 
    $
      V_#[ss] = inter.big_(m>=0) im(F^m), V_#[nil] = union.big_(m>=0) ker(F^m)
    $
    These subspaces are by definition $F$-stable. Since $V$ is finite-dimensional, the descending chain ${im(F^m)}_(m>=0)$ and ascending chain ${ker(F^m)}_(m>=0)$ of subspaces must eventually stabilize, say at stage $N$. 

    We now show that $V = V_#[ss] oplus V_#[nil]$. By the first isomorphism theorem, we have a $p^m$-linear bijection $V\/ker(F^m) -> im(F^m)$ of $k$-vector spaces. 

    We claim that if there is a $p^m$-linear bijection $phi: U -> W$ between finite-dimensional $k$-vector spaces, then $dim_k (U) = dim_k (W)$. 

      - Indeed, take a $k$-basis $u_1, dots.c, u_d$ of $U$, and we need to show that $phi(u_1), dots.c, phi(u_d)$ is a $k$-basis of $W$. 

      - Given any $w in W$, since $phi$ is surjective, take $u = sum_i c_i u_i in U$ s.t. $phi(u) = w$. Then: #h(1fr)
        $
          w = phi (sum_i c_i u_i) = sum_i c_i^(p^m) phi(u_i)
        $
        is spanned by ${phi(u_i)}$. 

      - If $sum_i c_i phi(u_i) = 0$, then: 
        $
          phi (sum_i c_i^(1\/p^m) u_i) = 0
        $
        Since $phi$ is injective, $sum_i c_i^(1\/p^m) u_i = 0$, and so each $c_i^(1\/p^m) = 0$. Thus each $c_i = 0$. 

    Therefore, we see that: 
    $
      dim_k (ker(F^m)) + dim_k (im(F^m)) = dim_k (V)
    $
    Setting $m = N$, we see that: 
    $
      dim_k (V_#[ss]) + dim_k (V_#[nil]) = dim_k (V)
    $
    Furthermore, if $v in V_#[ss] ∩ V_#[nil]$, then $v in im(F^N)$ and so $v = F^N x$ for some $x$. Since $v in ker(F^N)$, $F^(2N) x = F^N v = 0$. Thus $x in ker(F^(2N)) = ker(F^N)$ (since ${ker(F^m)}$ stablizes after stage $N$) and so $v = F^N x = 0$. Therefore, $V_#[ss] ∩ V_#[nil] = 0$. Combined with the equation on dimensions above, we see that: 
    $
      V = V_#[ss] oplus V_#[nil]
    $
    On $V_#[nil]$ we already have $F^N = 0$. On $V_#[ss]$, $F$ is surjective by definition, so we have a $p$-linear isomorphism $V_#[ss]\/ker(F|_(V_#[ss])) -> V_#[ss]$. By our claim this gives $dim_k (ker(F|_(V_#[ss]))) = 0$, so $F$ is injective on $V_#[ss]$ too. Since all fixed points of $F$ are obviously in $V_#[ss]$, it remains to show that $V_#[ss]$ is spanned by the fixed points of $F$. 

    For this, we replace $V$ with $V_#[ss]$ and $F$ with $F|_(V_#[ss])$, and assume that $F$ is bijective. Let $n = dim(V_#[ss])$. Pick an arbitrary basis $e_1, dots.c, e_n in V$, and suppose $F e_j = sum_(i=1)^n m_(i,j) e_i$, and form the matrix $M = mat(m_(i,j))_(i,j) in GL_n (k)$. Then: 
    $
      F(sum_i x_i e_j) = sum_(i,j) m_(i,j) x_j^p e_i
    $
    Therefore, to find fixed points of $F$, it suffices to solve the system of equations: 
    $
      x_i = sum_(j=1)^n m_(i,j) x_j^p, forall 1<=i<=n
    $
    They correspond bijectively to the closed points of $Spec(A)$, where: 
    $
      A = k[X_1, dots.c, X_n]/(({X_i - sum_(j=1)^n m_(i,j) X_j^p, forall 1<=i<=n}))
    $
    Since $M$ is an invertible matrix, these equations are equivalent to writing each $x_i^p$ as a linear combination of the $x_i$'s. Thus, $A$ is a $p^n$-dimensional finite $k$-algebra. Now: 
    $
      Omega_(A\/k) = (oplus.big_(i=1)^n k[X_1, dots.c, X_n] d X_i)/(({d(X_i - sum_(j=1)^n m_(i,j) X_j^p), forall 1<=i<=n}))
    $
    However, $d(X_i - sum_(j=1)^n m_(i,j) X_j^p) = d X_i$ by characteristic $p$, so the submodule on the denominator is really just $(d X_1, dots.c, d X_n)$, i.e. the whole $oplus.big_(i=1)^n k[X_1, dots.c, X_n] d X_i$. In other words, $Omega_(A\/k) = 0$, so $A$ is an etale $k$-algebra. Since $k$ is algebraically closed, $A$ is a direct product of copies of $k$, which must be $p^n$ copies since $dim_k (A) = p^n$. Thus, $Spec(A)$ has $p^n$ closed points, or $F$ has $p^n$ fixed points. 

    Let $V^F$ denote the fixed points of $F$. Since $F$ is $FF_p$-linear, $V^F$ is an $FF_p$-vector space of cardinality $p^n$, hence dimension $n$. Now pick $v_1, dots.c, v_n in V^F$ to be an $FF_p$-basis of $V^F$. We claim that these vectors are indeed $k$-linear independent. If not, pick a smallest $1<=m<=n$ s.t. $v_1, dots.c, v_m$ admits a nontrivial linear relation over $k$. The coefficient of $v_m$ must be nonzero, since otherwise we have a nontrivial linear relation of $v_1, dots.c, v_(m-1)$. Normalize this coefficient to be $1$, we obtain a linear relation: 
    $
      v_m = sum_(i=1)^(m-1) c_i v_i
    $
    Applying $F$ and using the fact that each $v_i$ is $F$-fixed, we see: 
    $
      v_m = sum_(i=1)^(m-1) c_i^p v_i
    $
    and so $sum_(i=1)^(m-1) (c_i^p - c_i) v_i = 0$. Since $v_1, dots.c, v_(m-1)$ are linearly independent, every $c_i^p - c_i = 0$, i.e. $c_i in FF_p$. In other words, we actually have a linear relation between $v_1, dots.c, v_m$ over $FF_p$, a contradiction. 

    Thus, $v_1, dots.c, v_n$ is a basis of $V$ consisting of fixed points of $F$. 
  ]
  We now study $wp = F - id: V = H^1_#[Zar] (X, cal(O)_X) -> V$, with $F$ being $p$-linear. By the previous lemma, we decompose: 
  $
    V = V_#[ss] oplus V_#[nil]
  $
  w.r.t. $F$, and take $gamma = gamma(X) := dim_k (V_#[ss])$. Now: 

  - On $V_#[nil]$, $F$ is nilpotent, say $F^N = 0$. Then $wp = F - id$ has an inverse, namely: #h(1fr)
    $
      wp^(-1) = - sum_(i=0)^(N-1) F^i
    $
    Thus, $wp$ has no kernel or cokernel on $V_#[nil]$. 

  - On $V_#[ss]$, we may pick a basis $v_1, dots.c, v_gamma$ of $V_#[ss]$ consisting of $F$-fixed vectors. Then: 
    $
      wp(sum_(i=1)^gamma x_i v_i) = sum_(i=1)^gamma (x_i^p - x_i) v_i
    $
    Since $k$ is algebraically closed, every equation of the shape $X^p - X - c, c in k$ has a root in $k$. Thus, $wp$ is surjective on $V_#[ss]$. The kernel consists of those coefficients $x_i$ s.t. $x_i^p - x_i = 0$, i.e. $x_i in FF_p$. In other words, $ker(wp)$ is a $gamma$-dimensional $FF_p$-vector space. 

  As such, 
  $
    H^1_et (X, ZZ\/p) = ker(wp\: V -> V) cong (ZZ\/p)^(oplus gamma(X)) \
    H^2_et (X, ZZ\/p) = coker(wp\: V -> V) = 0
  $
  Combined with vanishing in degrees $>=3$, we are done. 

  (3) This follows from the exact sequence $0 -> ZZ\/n -> ZZ\/m n -> ZZ\/m -> 0$ and the vanishing $H^q_et (X, ZZ\/p) = 0$ for $q >= 2$. 
]

Next, we prove vanishing for an affine smooth curve: 

#theorem(name: <h2-zn-of-affine-smooth-curve>)[
  Let $X$ be an affine smooth curve over an algebraically closed field $k$. Then: 
  $
    H^q_et (X, ZZ\/n) = 0
  $
  for all $q >= 2$ and all natural numbers $n$. 
]
#proof[
  Since we already have vanishing for $q >= 3$, it suffices to prove $H^2_et (X, ZZ\/n) = 0$ for all $n$. 

  When $n = p = "char"(k)$, we proceed by the Artin-Schreier sequence: 
  $
    dots.c -> H^1_et (X, GG_a) -> H^2_et (X, ZZ\/p) -> H^2_et (X, GG_a) -> dots.c
  $
  where $H^q_et (X, GG_a) = H^q_#[Zar] (X, cal(O)_X) = 0$, if $q >= 1$, since $X$ is affine. Hence $H^2_et (X, ZZ\/p) = 0$. 

  Next, suppose $n in k^times$. We have shown that: 
  $
    H^2_et (X, ZZ\/n) = Pic(X)\/n Pic(X)
  $
  Take a projective completion $ol(X)$ of $X$, which is a smooth projective curve. From the theory of divisors, we have a right exact sequence: 
  $
    oplus.big_(z in ol(X)-X) ZZ -> Pic(ol(X)) -> Pic(X) -> 0
  $
  By picking a point $z in ol(X)-X$, a divisor $D$ in $Pic(ol(X))$ may be shifted by $-deg(D)z$ to have degree $0$, while keeping its image in $Pic(X)$ unchanged. In other words, we have a surjection $Pic^0 (ol(X)) -> Pic(X)$. 
  // https://q.uiver.app/#r=typst&q=WzAsNCxbMCwwLCJQaWMob2woWCkpXjAiXSxbMSwwLCJQaWMoWCkiXSxbMSwxLCJQaWMoWCkiXSxbMCwxLCJQaWMob2woWCkpXjAiXSxbMCwxLCIiLDAseyJzdHlsZSI6eyJoZWFkIjp7Im5hbWUiOiJlcGkifX19XSxbMywyLCIiLDAseyJzdHlsZSI6eyJoZWFkIjp7Im5hbWUiOiJlcGkifX19XSxbMCwzLCJ0aW1lcyBuIiwxXSxbMSwyLCJ0aW1lcyBuIiwxXV0=
  #context align(center, diagram({
    node((-1, -1), [$Pic^0 (ol(X))$])
    node((0, -1), [$Pic(X)$])
    node((0, 0), [$Pic(X)$])
    node((-1, 0), [$Pic^0 (ol(X))$])
    edge((-1, -1), (0, -1), "->>")
    edge((-1, 0), (0, 0), "->>")
    edge((-1, -1), (-1, 0), [$times n$], label-side: center, "->>")
    edge((0, -1), (0, 0), [$times n$], label-side: center, "->")
  }, crossing-fill: thm-box-curr-color()))
  where the left arrow is surjective by our discussion of projective curves. Thus, $times n: Pic(X) -> Pic(X)$ is surjective, and so: 
  $
    H^2_et (X, ZZ\/n) = Pic(X)\/n Pic(X) = 0
  $
  We may then conclude the proof by using the $n$ and $p$ case, together with the exact sequence $0 -> ZZ\/n -> ZZ\/m n -> ZZ\/m -> 0$. 
]

With explicit computations involving constant sheaves done, we dedicate the remainder of this section to higher vanishing of general torsion sheaves. 

#remark(name: <remark-on-vanishing>)[
  The example of etale cohomology of a curve demonstrates vanishing theorems. 

  There is a comparison theorem (@cite-SGA4[Expos\'e XI, Th\'eor\`eme 4.4]) saying that for a variety $X$ over $CC$, there is a canonical isomorphism:
  $
    H^q_et (X, ul(ZZ\/ell)) cong H^q_#[sing] (X(CC), ZZ\/ell)
  $
  Now if $X$ has dimension $n$, then $X(CC)$ has real dimension $2n$. As such, RHS vanishes for $q > 2n$. We would expect LHS to vanish for $q > 2n$ too. This gives the expectation of a vanishing theorem: 

  - (Grothendieck vanishing) Let $X$ be a scheme of finite type of dimension $d$ over a separably closed field $k$. Then $H^q_et (X, cal(F)) = 0$ for $q > 2d$ for all torsion $cal(F) in cAb(X_et)$. 

  This is demonstrated in the case of a curve, that we just showed to have vanishing cohomology beyond degree $2$. 

  We also saw that affine smooth curves have vanishing cohomology beyond degree $1$. This is an example of a stronger vanishing theorem for affine schemes: 

  - (Artin vanishing) Let $X$ be an affine scheme of finite type of dimension $d$ over a separably closed field $k$. Then $H^q_et (X, cal(F)) = 0$ for $q > d$ for all torsion $cal(F) in cAb(X_et)$. 
]

/*
We now prove Grothendieck vanishing for curves. 

#lemma[
  Let $X$ be an irreducible noetherian scheme of dimension 1 over a separably closed field $k$, with generic point $eta$. Suppose that $cal(R) in cAb(X_et)$ satisfies $cal(R)_(ol(eta)) = 0$. Then there is a natural isomorphism: 
  $
    cal(R) cong oplus.big_(x in abs(X)) x_* cal(R)_x
  $
  In particular, 
  $
    H^q (X, cal(R)) = 0, forall q >= 1
  $
]
#proof[
  Consider the canonical morphism defined by adjunction: 
  $
    gamma: cal(R) -> product_(x in abs(X)) x_* cal(R)_x
  $
  For each qcqs $(f: U -> X) in Et_X$, $U$ is etale hence quasi-finite over $X$, hence must also be noetherian of dimension 1 over $K$. Now for each closed point $x in abs(X)$ and any $u in f^(-1)(x)$, $k(u)\/k(x)$ is a finite separable extension, hence a finite extension of $K$. As such, $u$ is a closed point. In other words, all generic points $eta_1, dots.c, eta_n in U$ of irreducible components of $U$ must lie over $eta in X$. 

  Thus, for each section $s in cal(R)(U)$, $s_(ol(eta)_i) in cal(R)_(ol(eta)) = 0$. Thus by @vanishing-stalks-spreads-out, there exists a Zariski open $V subset U$ containing all $eta_1, dots.c, eta_n$ s.t. $s|_V = 0$. Since $V$ contains all generic points of irreducible components of $U$, $V$ is a dense open, and so $Z = U - V$ is a finite set of closed points of $U$. Therefore: 
  $
    gamma(s) in product_(x in abs(X)) x_* cal(R)_(x) (U) = product_(x in abs(X)) product_(ol(u) in f^(-1)(x)) cal(R)_(x)
  $
  is the element $(s_(ol(u)))_(x,ol(u))$, whose components $s_(ol(u)) = 0$ outside a finite set of $ol(u)$. Thus, $gamma(s)$ in fact lies in: 
  $
    gamma(s) in oplus.big_(x in abs(X)) oplus.big_(ol(u) in f^(-1)(x)) cal(R)_(x) = (oplus.big_(x in abs(X)) x_* cal(R)_(x)) (U)
  $
  where the last equality is due to @limit-formula-for-sheaves. In other words, $gamma(cal(R))$, a priori a subsheaf of $product_(x in abs(X)) x_* cal(R)_(x)$, is a subsheaf of $oplus.big_(x in abs(X)) x_* cal(R)_(x)$. We thus have a natural map: 
  $
    gamma: cal(R) -> oplus.big_(x in abs(X)) x_* cal(R)_(x)
  $
  Now stalks commutes with direct sums, which, combined with @stalks-of-skyscraper-sheaves and @stalks-of-finite-pushforward, gives: 
  $
    (oplus.big_(x in abs(X)) x_* cal(R)_(x))_(ol(y)) = cases(
      cal(R)_y &\, y in abs(X), 
      0 &\, y = eta
    ) = cal(R)_(ol(y))
  $
  Thus, $gamma: cal(R) -> oplus.big_(x in abs(X)) x_* cal(R)_(x)$ is an isomorphism. Furthermore, by @limit-formula-for-sheaves and @pushforward-by-finite-morphism, 
  $
    H^q (X, cal(R)) = oplus.big_(x in abs(X)) H^q (X, x_* cal(R)_(ol(x))) = oplus.big_(x in abs(X)) H^q (x, cal(R)_(ol(x))) = 0
  $
  for all $q >= 1$. 
]

#theorem(name: <grothendieck-vanishing-for-curve>)[
  Let $X$ be any curve over a separably closed field, and $cal(F) in cAb(X_et)$ be a torsion sheaf. Then for all $q >= 3$, 
  $
    H^q (X, cal(F)) = 0
  $
]
#proof[
  Let $j: eta = Spec(K(X)) -> X$ be the inclusion of the generic point. Consider the natural morphism: 
  $
    gamma: cal(F) -> j_* j^(-1) cal(F)
  $
  We claim that $gamma$ is an isomorphism on stalks at $ol(eta)$. Indeed, $tilde(X)_(ol(eta)) = Spec(cal(O)_(X,eta)^#[sh]) = Spec(K(X)^#[sh]) = Spec(K(X)^sep) = ol(eta)$, and so: 
  $
    (R^q j_* j^(-1) cal(F))_(ol(eta)) = H^q (eta times_X ol(eta), j^(-1) cal(F)|_(eta times_X ol(eta))) = H^q (ol(eta), cal(F)_(ol(eta))) = cases(
      cal(F)_(ol(eta)) &\, q = 0, 
      0 &\, q >= 1
    )
  $
  In other words, $ker(gamma)_(ol(eta)) = coker(gamma)_(ol(eta)) = 0$, and $(R^q j_* j^(-1) cal(F))_(ol(eta)) = 0$ for $q >= 1$. By the previous lemma, 
  $
    H^p (X, ker(gamma)) = H^p (X, coker(gamma)) = 0, forall p >= 1 \
    H^p (X, R^q j_* j^(-1) cal(F)) = 0, forall p >= 1
  $
  Since $H^p (X, ker(gamma)) = H^p (X, coker(gamma)) = 0, forall p >= 1$, using short exact sequences, we see that for all $p >= 2$, 
  $
    H^p (X, cal(F)) cong H^p (X, im(gamma)) cong H^p (X, j_* j^(-1) cal(F))
  $
  and so it suffices to show for $p >= 3$, $H^p (X, j_* j^(-1) cal(F)) = 0$. For this, we use the Leray spectral sequence @derived-lower-star-first-props (2): 
  $
    E_2^(p,q) = H^p (X, R^q j_* j^(-1) cal(F)) ==> H^(p+q) (eta, j^(-1) cal(F)) 
  $
  Now for $q >= 2$ and $x in abs(X)$, 
  $
    (R^q j_* j^(-1) cal(F))_x = H^q (eta times_X tilde(X)_x, cal(F)|_(eta times_X tilde(X)_x))
  $
  As in the proof of @gm-generic-pushforward-higher-vanishing, $eta times_X tilde(X)_x = Spec(L)$, where $L$ is an extension field of $k$ of transcendence degree $1$. Thus, this cohomology is $H^q_#[cont] (Gal_L, -)$ applied to a discrete torsion $Gal_L$-module, since $cal(F)$ is torsion. By @tsen-thm-in-galois-cohom (1), a consequence of Tsen's theorem, this cohomology vanishes. Thus, $(R^q j_* j^(-1) cal(F))_x = 0$. Hence $R^q j_* j^(-1) cal(F) = 0$ for all $q >= 2$. 
  
  We also have proved $H^p (X, R^1 j_* j^(-1) cal(F)) = 0$ for $p >= 1$. Thus, in the Leray spectral sequence: 
  $
    E_2^(p,q) = H^p (X, R^q j_* j^(-1) cal(F)) ==> H^(p+q) (eta, j^(-1) cal(F)) 
  $
  the only nonzero terms on the $E_2$-page are $E_2^(p,0)$ and $E_2^(0,1)$. The only surviving differential is $d_2: E_2^(0,1) -> E_2^(2,0)$, and the spectral sequence stablizes on the $E_3$-page. Thus for all $p >= 3$, this spectral sequence induces an isomorphism: 
  $
    H^p (X, j_* j^(-1) cal(F)) = H^p (eta, j^(-1) cal(F))
  $
  which vanishes by @tsen-thm-in-galois-cohom (1), as a consequence of Tsen's theorem, where $eta = Spec(K(X))$ is the spectrum of a transcendence degree 1 extension of $k$, and $j^(-1) cal(F)$ is a torsion $Gal_(K(X))$-module as $cal(F)$ is a torsion sheaf. 

  Thus, we have shown for $p >= 3$, 
  $
    H^p (X, cal(F)) cong H^p (X, j_* j^(-1) cal(F)) cong H^p (eta, j^(-1) cal(F)) = 0
  $
  and we are done. 
]
*/
