#import "void-import.typ": *

(Note: Tsen here refers to the Chinese mathematician 曾炯 (1898–1940), who was a student of Emmy Noether. Apparently, noetherian people at the time did a lot of algebra.)

Tsen's theorem describes the algebraic properties of the function field of a curve, i.e. a finite extension of $k(t)$ for an algebraically closed field $k$. This provides critical input to computing the cohomology of curves. 
#let inf = math.op(limits: false)[inf]
#definition(name: <defn-c1-field>)[
  A field $K$ is called *$C_1$/quasi-algebraically closed*, if for all $1 <= d < n$, every non-constant homogeneous polynomial $f(x_1, dots.c, x_n) in K[x_1, dots.c, x_n]$ of degree $d$ has a nontrivial solution.
]

#proposition(name: <brauer-grp-of-c1-field-trivial>)[
  If $K$ is $C_1$, then the Brauer group $"Br"(K) := H^2_"cont" (Gal_K, (K^sep)^times) = 0$.
]
#proof[
  (You should refer to a course on algebraic number theory for basics on Brauer groups.)
  
  It suffices to prove that if $D$ is a central division algebra over $K$, then $D cong K$.
  
  Consider the reduced norm $"Nrd": D -> K$, a multiplicative map. (It is defined as follows: There exists $L\/K$ finite Galois s.t. $D_L overset(cong, alpha) "Mat"_r (L)$ as $L$-algebras. Consider the map $D_L overset(->, alpha) "Mat"_r (L) overset(->, det) L$. Then by Skolem-Noether, any two such $alpha$'s differ by inner conjugation. Thus this norm is $Gal(L\/K)$-invariant and descends to a map $"Nrd": D -> K$.)
  
  Observe that $D$ is a division algebra and $"Nrd"$ is multiplicative, so $"Nrd"(x) = 0 <==> x = 0$.
  
  Now take a $K$-basis $e_1, dots.c, e_(r^2)$ of $D$, and set:
  $
    f(x_1, dots.c, x_(r^2)) := "Nrd"(x_1 e_1 + dots.c + x_(r^2) e_(r^2))
  $
  This is a homogeneous polynomial of degree $r$, since after base changing to $L$, $f$ is just the determinant, a homogeneous polynomial of degree $r$.
  
  Now $f$ only has trivial zeros as $"Nrd"(x) = 0 <==> x = 0$. By the $C_1$ condition, this gives $r >= r^2$. Thus $r = 1$ and $D = K$.
]

#lemma(name: <finite-ext-of-c1-field-is-c1>)[
  If $K$ is a $C_1$ field, then so is $L$ for any finite extension $L\/K$. 
]
#proof[
  We may assume that $L\/K$ is a finite extension of degree $s$.
  
  Take:
  $
    f(x_1, dots.c, x_n) = sum_(i=(i_1,dots.c,i_n) \ i_1+dots.c+i_n = d) a_i arrow(x)^i, a_i in L
  $
  Fix a $K$-basis $e_1, dots.c, e_s$ of $L$, and consider the $n s$ indeterminates $y_(j,k), 1<=j<=n, 1<=k<=s$, and write $x_j (arrow(y)) = y_(j,1) e_1 + dots.c + y_(j,s) e_s$. Consider:
  $
    g(arrow(y)) = Nm_(L\/K) (f(arrow(x)(arrow(y))))
  $
  Then this is homogeneous of degree $d s$ in $n s$ variables, so by Step 1, $g$ has a nonzero solution of $arrow(y)$ in $K$. This gives a nonzero solution of $arrow(x)$ in $L$. 
]

#theorem(name: <tsen-theorem>)[
  (Tsen) If $K$ is a field extension of an algebraically closed field of transcendence degree $1$, then $K$ is $C_1$. In particular,
  $
    H^2_et (Spec(K), GG_m) = H^2_"cont" (Gal_K, (K^sep)^times) = "Br"(K) = 0
  $
]
#proof[
  Step 1: We first consider the case $K = k(t)$ is simply a function field. Suppose that $d < n$, and:
  $
    f(x_1, dots.c, x_n) = sum_(i=(i_1,dots.c,i_n) \ i_1+dots.c+i_n = d) a_i arrow(x)^i
  $
  (where we put $x^i = x_1^(i_1) dots.c x_n^(i_n)$.) We want to find a nonzero solution to $f$. We may assume that each $a_i in k[t] subset K$, and that $delta = max_i (deg(a_i))$.
  
  For a fixed $N$, consider indeterminates $y_(j,k), 1<=j<=n, 0<=k<=N$. Let $x_j (arrow(y)) = y_(j,N) t^N + dots.c + y_(j,1) t + y_(j,0)$. Now consider:
  $
    g(arrow(y)) = f(x_1 (arrow(y)), dots.c, x_n (arrow(y))) in k[t, y_(1,0), dots.c, y_(n,N)]
  $
  where $deg_t (g) <= delta + d N$.
  
  Consider the equation $g(arrow(y)) = 0$. This is equivalent to all coefficients of $t^ell, 0 <= ell <= d N + delta$ being zero. Thus, we have $(delta + d N + 1)$ equations in the variables $arrow(y)$, which is $n(N+1)$ variables. Since $n>d$ by assumption, for sufficiently large $N$, we have nonzero solutions for $arrow(y)$, hence a nonzero (i.e. nontrivial) solution for $f(arrow(x)) = 0$ by taking $arrow(x) = arrow(x)(arrow(y))$.
  
  Step 2: We now consider the general case. Pick a transcendental element $t in K$ over $k$, and then $K$ is a union of finite extensions of $k(t)$.
  
    To find a root of a homogeneous polynomial, we may first take its coefficients, which generate a finitely generated subfield of $K$ and are hence contained in a finite extension $L$ of $k(t)$. Since $L$ is $C_1$ as a finite extension of $k(t)$ by the previous lemma, we may find a nontrivial solution of this equation in $L$, hence in $K$. 
]

We now apply Tsen's theorem to get consequences of cohomology:

#theorem(name: <tsen-thm-in-galois-cohom>)[
  Suppose that $K$ is a $C_1$ field (or in particular, any extension of an algebraically closed field $k$ of transcendence degree $1$). 
  
  + For any discrete torsion $Gal_K$-module $M$, $H^q_"cont" (Gal_K, M) = 0, forall q >= 2$
  
  + $H^q_"cont" (Gal_K, (K^sep)^times) = 0, forall q >= 1$.
]
#proof[
  (1) We want to perform devissage on $M$. 

  Step 1. For $n >= 1$ and any finite separable extension $L\/K$, 
  $
    H^2_#[cont] (Gal_L, ZZ\/n) = 0
  $
  #proof[
    Since $L$ is also $C_1$ by @finite-ext-of-c1-field-is-c1, we may assume that $L = K$. 

    Using the exact sequences $0 -> ZZ\/m -> ZZ\/m n -> ZZ\/n -> 0$, we see that it suffices to prove this for all $n = p$ prime. 

    Case 1. $p != "char"(K)$. Consider the Kummer sequence: 
    $
      0 -> mu_p (K^sep) -> (K^sep)^times -> (K^sep)^times -> 0
    $
    of discrete $Gal_K$-modules, so we have an exact sequence: 
    $
      dots.c -> H^1_#[cont] (Gal_K, (K^sep)^times) -> H^2_#[cont] (Gal_K, mu_p (K^sep)) -> H^2_#[cont] (Gal_K, (K^sep)^times) -> dots.c
    $
    Now $H^1_#[cont] (Gal_K, (K^sep)^times) = 0$ by Hilbert 90, and $H^2_#[cont] (Gal_K, (K^sep)^times) = 0$ by @brauer-grp-of-c1-field-trivial. As such, $H^2_#[cont] (Gal_K, mu_p (K^sep)) = 0$. 

    However, it does not necessarily hold that $mu_p (K^sep) cong ZZ\/p$ as $Gal_K$-modules, since $K$ might not contain all $p$-th roots of unity. For this, let $L = K(zeta_p)$ be $K$ with one (or equivalently, every) $p$-th root of unity adjoined, and consider the restriction-corestriction composition: 
    $
      H^2 (Gal_K, ZZ\/p) ->^#[res] H^2 (Gal_L, ZZ\/p) ->^#[cores] H^2 (Gal_K, ZZ\/p)
    $
    This is simply multiplication by $[L:K]$ from the theory of group cohomology. Note that $H^2 (Gal_K, ZZ\/p)$ is $p$-torsion, while $gcd(p, [L:K]) = 1$. Therefore, this composition is an isomorphism, and so restriction $H^2 (Gal_K, ZZ\/p) ->^#[res] H^2 (Gal_L, ZZ\/p)$ is injective. It thus suffices to prove that $H^2 (Gal_L, ZZ\/p) = 0$. However, $L$ is a finite extension of $K$, hence $C_1$ by @finite-ext-of-c1-field-is-c1. As such, $H^2 (Gal_L, mu_p (K^sep)) = 0$. $L$ does contain all $p$-th roots of unity, so $mu_p (K^sep) cong ZZ\/p$ as $Gal_L$-modules, and we are done. 

    Case 2. $p = "char"(K) > 0$. Consider the Artin-Schreier sequence: 
    $
      0 -> ZZ\/p -> K^sep -->^(x |-> x^p - x) --> K^sep -> 0
    $
    of $Gal_K$-modules. We have an exact sequence:
    $
      dots.c -> H^1_#[cont] (Gal_K, K^sep) -> H^2_#[cont] (Gal_K, ZZ\/p) -> H^2_#[cont] (Gal_K, K^sep) -> dots.c
    $
    However, by the additive version of Hilbert 90, $H^q_#[cont] (Gal_K, K^sep) = 0$ for $q >= 1$. (One may also view this from the etale point of view: $H^q_#[cont] (Gal_K, K^sep) = H^q_et (Spec(K), cal(O)_(Spec(K))) = H^q_#[Zar] (Spec(K), cal(O)_(Spec(K))) = 0$ for $q >= 1$, but that's overkill.) As such, 
    $
      H^2_#[cont] (Gal_K, ZZ\/p) = 0
    $
    #suppress-qed
  ]

  Step 2. Suppose that for a fixed $q >= 2$ and all finite separable $L\/K$, 
  $
    H^q_#[cont] (Gal_L, ZZ\/n) = 0
  $
  for all $n >= 1$. Then for all finite separable $L\/K$ and all discrete torsion $Gal_L$-module $M$, $H^q_#[cont] (Gal_L, M) = 0$. 

  #proof[
    Any finite separable extension of $L$ is a finite separable extension of $K$, so we may replace $L$ with $K$ to assume $L = K$. 
    
    For any $x in M$, since $M$ is a discrete space with a continuous $Gal_K$-action, there exists a finite Galois extension $E\/K$ s.t. $x$ is fixed by the open normal subgroup $Gal_E <= Gal_K$. Then the finitely many torsion elements ${g x: [g] in Gal(E\/K) = Gal_K\/Gal_E}$ generate a $Gal_K$-stable finite submodule of $M$ containing $x$. As such: 
    $
      M = dirlim_(N <= M #[finite submodule]) N
    $
    as abstract $Gal_K$-modules. One may verify that the topology on the RHS is also discrete, so they are isomorphic as continuous $Gal_K$-modules. By the limit formula for modules (@galois-cohom-props (1a)), it suffices to prove that: 
    $
      H^q_#[cont] (Gal_K, M) = 0
    $
    for all finite discrete $Gal_K$-module $M$. Now for each prime $p$, the $p^oo$-torsion part of $M$ is $Gal_K$-stable, so $M$ is the direct sum of its $p^oo$-torsion parts. Since: 
    $
      H^q_#[cont] (Gal_K, M) = dirlim_(E\/K #[finite Galois] \ M = M^(Gal_E)) H^q (Gal(E\/K), M)
    $
    with transition morphisms being inflation, it suffices to show that any class $alpha_E in H^q (Gal(E\/K), M)$ for a finite Galois $E\/K$ so that $Gal_E$ acts trivially on $M$ inflates to zero when passed to a larger Galois extension. 

    Let $G = Gal(E\/K)$, which is a finite group. It admits a Sylow $p$-subgroup $P$, a finite $p$-group corresponding to an intermediate field extension $E\/F\/K$, i.e. $P = Gal(E\/F)$. We will first show that $res^G_P (alpha_E) in H^q (P, M)$ is zero when passed to a larger Galois extension of $F$. 

    Indeed, a finite $p$-group $P$ acts on the finite abelian $p$-group $M$. Each $P$-orbit in $M$ has order a power of $p$, and these numbers sum to $abs(M)$, a number divisible by $p$. Since $0$ is always fixed by $P$, the number $1$ appears once in the orbit sizes, so it must appear more than once. In other words, $M^P subset M$ is nontrivial, so we may pick $M_1 subset M^P subset M$ isomorphic to $ZZ\/p$ as an abelian group. By inductively applying this construction to $M\/M_1$, we may obtain a finite filtration: 
    $
      0 = M_0 subset M_1 subset dots.c subset M_k = M
    $
    of $P$-modules, so that each $M_j\/M_(j-1)$ is a $P$-fixed submodule of $M\/M_(j-1)$ isomorphic to $ZZ\/p$ as an abelian group, i.e. isomorphic to $ZZ\/p$ as a $P$-module (by $P$-fixness). 

    We claim that:
    
    - For each $0 <= j <= k$, any Galois extension $T\/F$ containing $E$, every class $beta_j in H^q (Gal(T\/F), M_j)$ may be killed upon inflation to $Gal(L\/F)$ for a sufficiently large finite Galois extension $L\/F$ containing $T$. 

    The base case $j = 0$ is automatic. Suppose that we are done with the case $j-1$ and are dealing with the case $j$. Consider the exact sequence: 
    $
      0 -> M_(j-1) -> M_j -> M_j\/M_(j-1) cong ZZ\/p -> 0
    $
    of $Gal_F$-modules, inducing an exact sequence: 
    $
      dots.c -> H^q (Gal(T\/F), M_(j-1)) ->^u H^q (Gal(T\/F), M_j) ->^v H^q (Gal(T\/F), ZZ\/p) -> dots.c
    $
    However, $H^q (Gal_F, ZZ\/p) = 0$ by hypothesis, so there exists a finite Galois extension $L\/F$ containing $T$ such that $inf_(Gal(T\/F))^(Gal(L\/F)) (v(beta_j)) = 0$. Since functoriality and inflation are compatible, we have a commutative diagram: 
    // https://q.uiver.app/#r=typst&q=WzAsMTAsWzAsMCwiZG90cy5jIl0sWzAsMSwiZG90cy5jIl0sWzQsMCwiZG90cy5jIl0sWzQsMSwiZG90cy5jIl0sWzEsMCwiSF5xIChQLCBNXyhqLTEpKSJdLFsyLDAsIkhecSAoUCwgTV9qKSJdLFszLDAsIkhecSAoUCxaWlxcL3ApIl0sWzEsMSwiSF5xIChHYWwoTFxcL0YpLCBNXyhqLTEpKSJdLFsyLDEsIkhecSAoR2FsKExcXC9GKSwgTV9qKSJdLFszLDEsIkhecSAoR2FsKExcXC9GKSwgWlpcXC9wKSJdLFswLDRdLFs0LDUsInUiXSxbNSw2LCJ2Il0sWzYsMl0sWzEsN10sWzcsOCwidV9MIl0sWzgsOSwidl9MIl0sWzksM10sWzQsNywiaW5mX1BeKEdhbChMXFwvRikpIiwxXSxbNSw4LCJpbmZfUF4oR2FsKExcXC9GKSkiLDFdLFs2LDksImluZl9QXihHYWwoTFxcL0YpKSIsMV1d
    #context align(center, diagram({
      node((-2, -1), [$dots.c$])
      node((-2, 0), [$dots.c$])
      node((2, -1), [$dots.c$])
      node((2, 0), [$dots.c$])
      node((-1, -1), [$H^q (Gal(T\/F), M_(j-1))$])
      node((0, -1), [$H^q (Gal(T\/F), M_j)$])
      node((1, -1), [$H^q (Gal(T\/F),ZZ\/p)$])
      node((-1, 0), [$H^q (Gal(L\/F), M_(j-1))$])
      node((0, 0), [$H^q (Gal(L\/F), M_j)$])
      node((1, 0), [$H^q (Gal(L\/F), ZZ\/p)$])
      edge((-2, -1), (-1, -1), "->")
      edge((-1, -1), (0, -1), [$u$], label-side: left, "->")
      edge((0, -1), (1, -1), [$v$], label-side: left, "->")
      edge((1, -1), (2, -1), "->")
      edge((-2, 0), (-1, 0), "->")
      edge((-1, 0), (0, 0), [$u_L$], label-side: left, "->")
      edge((0, 0), (1, 0), [$v_L$], label-side: left, "->")
      edge((1, 0), (2, 0), "->")
      edge((-1, -1), (-1, 0), [$inf_(Gal(T\/F))^(Gal(L\/F))$], label-side: center, "->")
      edge((0, -1), (0, 0), [$inf_(Gal(T\/F))^(Gal(L\/F))$], label-side: center, "->")
      edge((1, -1), (1, 0), [$inf_(Gal(T\/F))^(Gal(L\/F))$], label-side: center, "->")
    }, crossing-fill: thm-box-curr-color()))
    and so: 
    $
      v_L (inf_(Gal(T\/F))^(Gal(L\/F)) (beta_j)) = 0
    $
    By exactness of the second row, there exists $gamma_(j-1) in H^q (Gal(L\/F), M_(j-1))$ s.t. $u_L (gamma_(j-1)) = inf_(Gal(T\/F))^(Gal(L\/F)) (beta_j)$. Next, by the inductive hypothesis, there exists a Galois extension $L'\/F$ containing $L$ s.t. $inf_(Gal(L\/F))^(Gal(L'\/F)) (gamma_(j-1)) = 0$. Applying $inf_(Gal(L\/F))^(Gal(L'\/F))$ further to $u_L (gamma_(j-1)) = inf_(Gal(T\/F))^(Gal(L\/F)) (beta_j)$ and using compatibility, we see: 
    $
      inf_(Gal(T\/F))^(Gal(L'\/F)) (beta_j) = inf_(Gal(L\/F))^(Gal(L'\/F)) (u_L (gamma_(j-1))) = u_(L') (inf_(Gal(L\/F))^(Gal(L'\/F)) (gamma_(j-1))) = u_(L') (0) = 0
    $
    and we are thereby done. 

    In other words, we have shown: 

    - For every class $beta in H^q (P, M)$, there exists a finite Galois extension $L\/F$ containing $E$ s.t. $inf_P^(Gal(L\/F)) (beta) = 0$. 

    Applying this to the class $res^G_P (alpha_E)$, we see that: 
    $
      inf_P^(Gal(L\/F)) (res^G_P (alpha_E)) = 0
    $
    for some finite Galois extension $L\/F$ containing $E$. Take $L'$ to be the Galois closure of $L$ over $K$, and so upon a further inflation: 
    $
      inf_(Gal(E\/F))^(Gal(L'\/F)) (res^(Gal(E\/K))_(Gal(E\/F)) (alpha_E)) = 0
    $

    From group cohomology, we have the following compatibility of inflation and restriction: 
    #fact[
      Let $G$ be a finite group, $N <= G$ be a normal subgroup and $H <= G$ be a subgroup containing $N$. Then: 
      $
        inf_(H\/N)^H compose res^(G\/N)_(H\/N) = res^G_H compose inf^G_(G\/N)
      $
    ]
    Applying this fact to the situation above, with $N = Gal(L'\/E), G = Gal(L'\/K), H = Gal(L'\/F)$ in the notations of the fact, we see: 
    $
      res^(Gal(L'\/K))_(Gal(L'\/F)) (inf_(Gal(E\/K))^(Gal(L'\/K)) (alpha_E)) = inf_(Gal(E\/F))^(Gal(L'\/F)) (res^(Gal(E\/K))_(Gal(E\/F)) (alpha_E)) = 0
    $
    However, consider the restriction-inflation composition: 
    $
      H^q (Gal(L'\/K), M) ->^(res^(Gal(L'\/K))_(Gal(L'\/F))) H^q (Gal(L'\/F), M) -> H^q (Gal(L'\/K), M)
    $
    which is just multiplication by $[Gal(L'\/K) : Gal(L'\/F)] = [F : K] = [G : P]$, a number coprime to $p$. Since $H^q (Gal(L'\/K), M)$ is $p^k$-torsion for $p^k = abs(M)$, this composition is an isomorphism. Therefore, $res^(Gal(L'\/K))_(Gal(L'\/F)): H^q (Gal(L'\/K), M) -> H^q (Gal(L'\/F), M)$ is injective. We thus see that: 
    $
      inf_(Gal(E\/K))^(Gal(L'\/K)) (alpha_E) = 0
    $
    #suppress-qed
  ]

  Step 3. For each fixed $q >= 3$, if for all primes $2 <= r < q$ we have $H^r_#[cont] (Gal_K, M) = 0$ for any discrete torsion $M$, then: 
  $
    H^q (Gal_K, ZZ\/n) = 0
  $
  for all $n >= 1$. 

  #proof[
    We will use an exact sequence: 
    $
      0 -> ZZ\/n -> coInd_1^(Gal_K) (ZZ\/n) -> R -> 0
    $
    of $Gal_K$. Here, the co-induced module $coInd_1^(Gal_K) (ZZ\/n)$ is: 
    $
      coInd_1^(Gal_K) (ZZ\/n) = dirlim_(L\/K #[finite Galois]) coInd_1^(Gal(L\/K)) (ZZ\/n) = dirlim_(L\/K #[finite Galois]) C(Gal(L\/K), ZZ\/n) = C(Gal_K, ZZ\/n)
    $
    is the module of all locally constant functions $Gal_K -> ZZ\/n$ with left regular $Gal_K$-action, and is of course $n$-torsion. Furthermore, the topology on this module is discrete as can be checked from the direct limit. 
    
    The quotient $R$ is thus $n$-torsion and discrete. By Shapiro's lemma, $H^(q-1)_#[cont] (Gal_K, coInd_1^(Gal_K) (ZZ\/n)) = H^q_#[cont] (Gal_K, coInd_1^(Gal_K) (ZZ\/n)) = 0$. Thus, from the exact sequence of the derived functor, we have: 
    $
      H^q_#[cont] (Gal_K, ZZ\/n) cong H^(q-1)_#[cont] (Gal_K, R) = 0
    $
    by the inductive hypothesis. 
    #suppress-qed
  ]

  Step 3 may be applied to $Gal_L$ for any finite separable extension of $K$. As such, we have proved: 

  - For $n >= 1$ and any finite separable extension $L\/K$, $H^2_#[cont] (Gal_L, ZZ\/n) = 0$. #h(1fr)

  - Suppose that for a fixed $q >= 2$ and all finite separable $L\/K$,
    $
      H^q_#[cont] (Gal_L, ZZ\/n) = 0
    $
    for all $n >= 1$. Then for all finite separable $L\/K$ and all discrete torsion $Gal_L$-module $M$, $H^q_#[cont] (Gal_L, M) = 0$. 

  - For each finite separable $L\/K$, and each fixed $q >= 3$, if for all primes $2 <= r < q$ we have $H^r_#[cont] (Gal_L, M) = 0$ for any discrete torsion $M$, then:
    $
      H^q (Gal_L, ZZ\/n) = 0
    $
    for all $n >= 1$. 

  These three results are sufficient to conclude the proof by induction. 

  (2) The case $q = 1$ is Hilbert 90, $q = 2$ is Proposition @brauer-grp-of-c1-field-trivial, so we may assume $q >= 3$. For any prime $ell != "char"(K)$, consider the Kummer sequence: 
  $
    0 -> mu_ell (K^sep) -> (K^sep)^times ->^((-)^ell) (K^sep)^times -> 0
  $
  inducing a long exact sequence: 
  $
    dots.c -> H^q_#[cont] (Gal_K, mu_ell (K^sep)) -> H^q_#[cont] (Gal_K, (K^sep)^times) ->^(times ell) H^q_#[cont] (Gal_K, (K^sep)^times) -> H^(q+1)_#[cont] (Gal_K, mu_ell (K^sep)) -> dots.c
  $
  By (1), $H^q_#[cont] (Gal_K, mu_ell (K^sep)) = H^(q+1)_#[cont] (Gal_K, mu_ell (K^sep)) = 0$. As such, multiplication by $ell$: 
  $
    times ell: H^q_#[cont] (Gal_K, (K^sep)^times) -> H^q_#[cont] (Gal_K, (K^sep)^times)
  $
  is an isomorphism. 

  If $p = "char"(K) > 0$, note that $(-)^p: (K^sep)^times -> (K^sep)^times$ is injective, giving an exact sequence: 
  $
    0 -> (K^sep)^times ->^((-)^p) (K^sep)^times -> Q -> 0
  $
  of $Gal_K$-modules. Since $(K^sep)^times$ is discrete as a $Gal_K$-module, $Q$ is discrete. By definition $Q$ is $p$-torsion, making (1) applicable to $Q$. As such, we have a long exact sequence: 
  $
    dots.c -> H^(q-1)_#[cont] (Gal_K, Q) -> H^q_#[cont] (Gal_K, (K^sep)^times) ->^(times p) H^q_#[cont] (Gal_K, (K^sep)^times) -> H^q_#[cont] (Gal_K, Q) -> dots.c
  $
  Since $q >= 3$, by (1) $H^(q-1)_#[cont] (Gal_K, Q) = H^q_#[cont] (Gal_K, Q) = 0$. As such, 
  $
    times p: H^q_#[cont] (Gal_K, (K^sep)^times) -> H^q_#[cont] (Gal_K, (K^sep)^times)
  $
  Combining the two results above, for any natural number $n >= 1$, multiplication: 
  $
    times n: H^q_#[cont] (Gal_K, (K^sep)^times) -> H^q_#[cont] (Gal_K, (K^sep)^times)
  $
  is always an isomorphism. However, 
  $
    H^q_#[cont] (Gal_K, (K^sep)^times) = dirlim_(L\/K #[finite Galois]) H^q (Gal(L\/K), L^times)
  $
  is torsion. This forces $H^q_#[cont] (Gal_K, (K^sep)^times) = 0$. 
]
