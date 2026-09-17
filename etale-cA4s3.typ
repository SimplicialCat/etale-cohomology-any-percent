#import "void-import.typ": *

== Weierstrass divisibility induction

We are now ready to conclude the proof in an induction. First, we need some final preparations to utilize the determinant condition we obtained through Neron smoothing. 

The following lemma is attributed in @cite-Art69 to Tougeron.

#lemma[
  Let $(A, frak(m))$ be a henselian local ring, let $f_1, dots.c, f_(m-d) in A[Y_1,dots.c,Y_m]$ and let $arrow(y^0) in A^m$. Write: 
  $
    J = J_f (arrow(y^0)): A^m -> A^(m-d), e_i |-> sum_(j=1)^(m-d) (partial f_j)/(partial Y_i) e_j
  $
  so $J in MM_((m-d) times m) (A)$. 

  Let $Delta = (d_1, dots.c, d_s)$ be a finitely generated ideal contained in the annihilator $"ann"_A (coker(J))$. If: 
  $
    f_1 (arrow(y^0)), dots.c, f_(m-d) (arrow(y^0)) in Delta^2 frak(m)
  $
  Then there exists $arrow(y) in A^m$ s.t: 
  $
    f_1 (arrow(y)) = dots.c = f_(m-d) (arrow(y)) = 0 \

    arrow(y) - arrow(y^0) in Delta frak(m) dot A^m
  $
]
#proof[
  For each $i$, multiplication by $d_i$ on $A^(m-d)$ factors through $J$. Thus there exists $N_i in MM_(m times (m-d)) (A)$ s.t: 
  $
    J N_i = d_i I_(m-d)
  $
  Write $arrow(f)(arrow(y^0)) = sum_(i,j) d_i d_j arrow(epsilon)_(i,j)$ for $arrow(epsilon)_(i,j) in frak(m) dot A^(m-d)$. 

  Introduce a matrix of indeterminates $U = display(mat(U_(i,j))_(i<=m,j<=s))$. Put $arrow(d) = (d_1,dots.c,d_s) in A^s$. Now by the Taylor expansion: 
  $
    arrow(f)(arrow(y^0) + U arrow(d)) = arrow(f)(arrow(y^0)) + J U arrow(d) + sum_(i,j) d_i d_j arrow(Q)_(i,j) (U)
  $
  where each monomial in $arrow(Q)_(i,j) (U)$ has degree $>=2$. Rewrite using $arrow(f)(arrow(y^0)) = sum_(i,j) d_i d_j arrow(epsilon)_(i,j)$ and $J N_i = d_i I_(m-d)$, we have: 
  $
    arrow(f)(arrow(y^0) + U arrow(d)) = sum_(i=1)^s d_i J (underbrace(mat(U_(1,i); dots.v; U_(m,i)), arrow(U)_i) + sum_(j=1)^s N_j (arrow(Q)_(i,j) (U) + arrow(epsilon)_(i,j)))
  $
  Thus, to find the solution $arrow(y)$, it suffices to solve the system $arrow(Phi)(U) = 0$, where: 
  $
    arrow(Phi)_i (U) := arrow(U)_i + sum_(j=1)^s N_j (arrow(Q)_(i,j) (U) + arrow(epsilon)_(i,j))
  $
  Consider the polynomial map: 
  $
    Phi: MM_(m times s) (A) -> MM_(m times s) (A), U |-> mat(arrow(Phi)_1 (U), dots.c, arrow(Phi)_s (U))
  $
  Then $arrow(Phi)_i (0) = sum_(j=1)^s N_j arrow(epsilon)_(i,j)$ has all coefficients in $frak(m)$. Furthermore, the differential $d Phi(0) = id$ since $arrow(Q)_(i,j)$ has every term of degree $>=2$. It remains to invoke the following lemma: 

  #lemma[
    Let $(A, frak(m))$ be a henselian local ring, and: 
    $
      Phi: A^n -> A^n
    $
    be a polynomial map s.t. $Phi(0) in frak(m) dot A^n$ and $d Phi(0) = id$. Then $Phi$ has a solution in $frak(m) dot A^n$. 
  ]
  #proof[
    Take: 
    $
      R = (A[T_1, dots.c, T_n])/((Phi_1 (T_1, dots.c, T_n), dots.c, Phi_n (T_1, dots.c, T_n)))
    $
    Since $d Phi(0) = id$, the Jacobian matrix $J = display(mat(nabla Phi_1, dots.c, nabla Phi_n))$ is $I_n + K$ for some $K in (T_1, dots.c, T_n) dot MM_(n times n) (A[T_1, dots.c, T_n])$. It is thus invertible when localized at $(frak(m), T_1, dots.c, T_n)$. Hence, there exists $h in A[T_1, dots.c, T_n] - (frak(m), T_1, dots.c, T_n)$ s.t: 
    $
      R_h = (A[T_1, dots.c, T_n]_h)/((Phi_1 (T_1, dots.c, T_n), dots.c, Phi_n (T_1, dots.c, T_n)))
    $
    is an etale $A$-algebra, by @jacobian-criterion-for-etaleness. Now $Phi(0) in frak(m) dot A^n$ says that the zero section is a section $Spec(k) -> Spec(R_h\/frak(m) R_h)$. By @equiv-defns-of-henselian (4), this section lifts to a section $Spec(A) -> Spec(R_h)$, which is a solution to $Phi = 0$ that reduces to $0$ modulo $frak(m)$.  
  ]
]

#corollary(name: <jacobian-correction>)[
  Let $(A, frak(m))$ be a noetherian henselian local ring, let $f_1, dots.c, f_(m-d) in A[Y_1,dots.c,Y_m]$ and let $arrow(y^0) in A^m$. Write: 
  $
    J = J_f (arrow(y^0)): A^m -> A^(m-d), e_i |-> sum_(j=1)^(m-d) (partial f_j)/(partial Y_i) e_j
  $
  so $J in MM_((m-d) times m) (A)$. Let $d_0 in A$ be the determinant of the first $m-d$ columns of $J$. If for $N >= 0$: 
  $
    f_1 (arrow(y^0)), dots.c, f_(m-d) (arrow(y^0)) in d_0^2 frak(m)^(2N+1)
  $
  Then there exists $arrow(y) in A^m$ s.t: 
  $
    f_1 (arrow(y)) = dots.c = f_(m-d) (arrow(y)) = 0 \

    arrow(y) - arrow(y^0) in d_0 frak(m)^(N+1) dot A^m
  $
]
#proof[
  We want to apply the previous lemma with $Delta = d_0 frak(m)^N$; it suffices to show that $d_0$ annihilates $coker(J)$. Indeed, let $M$ be the first $m-d$ columns of $J$ and $M^*$ be its adjugate matrix. Pad $M^*$ with $d$ zero rows to get $N$, and then: 
  $
    J N = d_0 I_(m-d)
  $
]

#lemma(name: <jacobian-improvement>)[
  Setup as in @artin-approx-smoothing-reduction-2 (2). Put: 
  $
    d_0 = "ord"_(frak(m)_n) (delta(arrow(X), hat(y))) < +oo
  $
  If $N >= 2d_0 + 1$ and $arrow(y^0) in A_n^m$ s.t. $arrow(y^0) = hat(y) mod frak(m)_n^N hat(A_n)$, and: 
  $
    arrow(f) (arrow(X), arrow(y^0)) in delta(arrow(X), arrow(y^0))^2 dot A_n^r
  $
  then: 
  $
    arrow(f) (arrow(X), arrow(y^0)) in delta(arrow(X), arrow(y^0))^2 frak(m)_n^(N-2d_0) dot A_n^r
  $
]
#proof[
  Since $N > d_0$, $delta(arrow(X), hat(y)) mod frak(m)_n^N = delta(arrow(X), arrow(y^0)) mod frak(m)_n^N$ and so $"ord"_(frak(m)_n) (delta(arrow(X), arrow(y^0))) = d_0$. 

  Similarly, since $arrow(f)(arrow(X), hat(y)) = 0$, we have $arrow(f) (arrow(X), arrow(y^0)) in frak(m)_n^N dot A_n^r$. 

  Since $A_n$ is a regular local ring, its graded algebra is a polynomial ring over $k(A_n) = k$ by #cite-stacks("061P")[Definition 10.69.1] and #cite-stacks("00LN")[Lemma 10.69.2]. Thus, $frak(m)_n$-adic order is additive on products. Put $f_i (arrow(X), arrow(y^0)) = delta(arrow(X), arrow(y^0))^2 q_i$. Then: 
  $
    "ord"_(frak(m)_n) (q_i) = "ord"_(frak(m)_n) (f_i (arrow(X), arrow(y^0))) - 2 d_0 >= N - 2d_0
  $
]

We are now ready to perform the induction. The following lemma is Artin's Lemma 5.12. 

#lemma(name: <weierstrass-divisibility-induction>)[
  (Weierstrass divisibility) Assume Artin approximation for $A_i$ for all $i < n$. Let: 
  $
    g, f_1, dots.c, f_r in R[X_1, dots.c, X_n, Y_1, dots.c, Y_m]
  $
  so that $hat(y) in hat(A_n)^m$ satisfies: 
  $
    g(arrow(X), hat(y)) in hat(A_n) - pi.alt hat(A_n) \

    f_i (arrow(X), hat(y)) in g(arrow(X), hat(y)) hat(A_n), forall 1 <= i <= r
  $
  Then for every $N >= 1$, there exists $arrow(y) in A_n^m$ agreeing with $hat(y)$ modulo $frak(m)_n^N$ s.t: 
  $
    f_i (arrow(X), arrow(y)) in g(arrow(X), arrow(y)) A_n, forall 1 <= i <= r
  $
]
#proof[
  Put $H = g(arrow(X), hat(y)) in hat(A_n)$. If $H$ is a unit in $hat(A_n)$, any sufficiently close $arrow(y)$ makes $g(arrow(X), arrow(y)) in A_n^times$, and then the desired condition is vacuous. In particular this holds if $n = 0$. Thus we may assume $n >= 1$ and $H in frak(m)_n hat(A_n) - pi.alt hat(A_n)$. 

  Put $arrow(X)' = (X_1, dots.c, X_(n-1))$ and $T = X_n$. 

  - The reduction $ol(H) in k fps(arrow(X)'\, T)$ is nonzero. We claim that there exists some $e_1, dots.c, e_(n-1) in NN$ s.t. after applying the automorphism:
    $
      T |-> T, X_i |-> X_i + T^(e_i), i < n
    $
    we have $ol(H)(0, dots.c, 0, T) != 0$. In other words, we want $ol(H)(T^(e_1), dots.c, T^(e_(n-1)), T) != 0$. Put: 
    $
      ol(H)(arrow(X)) = sum_(alpha in NN^n) c_alpha arrow(X)^alpha
    $
    Let $S = {alpha in NN^n : c_alpha != 0}$, and let $alpha_0 = (a_1, dots.c, a_n)$ be its lexicographically least
    element, where the coordinates are compared in the order
    $X_1, dots.c, X_(n-1), T$. Put $e_n = 1$ and recursively set:
    $
      e_i = 1 + sum_(j=i+1)^n e_j a_j,
      quad i = n-1, dots.c, 1.
    $
    Put:
    $
      w(alpha) = sum_(i=1)^n e_i alpha_i.
    $
    We claim that $alpha_0$ is the unique element of $S$ of minimum weight. Indeed, if $beta in S$ and $beta != alpha_0$, let $i$ be the first index s.t. $beta_i != a_i$. By the choice of $alpha_0$, we have $beta_i > a_i$, and hence:
    $
      w(beta) - w(alpha_0)
      = sum_(j=i)^n e_j (beta_j - a_j) >= e_i - sum_(j=i+1)^n e_j a_j = 1.
    $
    Since every $e_i$ is positive, the indicated formal substitution
    is well-defined. Consequently:
    $
      ol(H)(T^(e_1), dots.c, T^(e_(n-1)), T)
      = c_(alpha_0) T^(w(alpha_0))
        + O(T^(w(alpha_0) + 1))
      != 0.
    $

  The triangular automorphism $T |-> T, X_i |-> X_i + T^(e_i)$ fixes $(pi.alt, X_1, dots.c, X_(n-1), T)$. Thus it fixes $frak(m)_n$ and $frak(m)_n hat(A_n)$. Thus, after applying such a triangular automorphism on the system and solutions, and undoing it on the solutions at the end, we may assume that $ol(H)(0, dots.c, 0, T) != 0$. 

  Put: 
  $
    B = hat(A_(n-1)) = hat(R) fps(X_1\, dots.c\, X_(n-1)) \
    frak(b) = (pi.alt, X_1, dots.c, X_(n-1)) B
  $
  and so $hat(A_n) = B fps(T)$ and $B\/frak(b) cong k$. Since $ol(H)(0, dots.c, 0, T) != 0$, we precisely know that $H != 0 in B\/frak(b) fps(T)$. 
  #lemma[
    (Formal Weierstrass preparation) Let $(A, frak(m))$ be a complete local ring and let $H(T) in A fps(T)$ be s.t. $H(T) mod frak(m) in k fps(T)$ is nonzero. Then there exist $d in NN$, $a_0, dots.c, a_(d-1) in frak(m)$ and $u in A fps(T)^times$ s.t: 
    $
      H(T) = u(T) (T^d + a_(d-1) T^(d-1) + dots.c + a_0)
    $
  ]
  #proof[
    Let $d$ be the $T$-order of $H(T) mod frak(m) in k fps(T)$, which is known to be nonzero. Then: 
    $
      H(T) = sum_(j>=0) h_j T^j
    $
    with: 
    $
      h_0, dots.c, h_(d-1) in frak(m), h_d in A^times
    $
    Set $G(T) = sum_(j>=d) h_j T^(j-d)$. Since $h_d in A^times$, we have $G(T) in A fps(T)^times$. Thus, 
    $
      H(T) = G(T) dot (T^d + G(T)^(-1) sum_(j=0)^(d-1) h_j T^j)
    $
    Here, each $h_j in frak(m)$, so $r(T) = G(T)^(-1) sum_(j=0)^(d-1) h_j T^j in frak(m) fps(T)$. It suffices to perform the same factorization for $r(T)$. 
    
    For every $f = sum_(j>=0) f_j T^j in A fps(T)$, denote: 
    $
      pi(f) = sum_(j=0)^(d-1) f_j T^j, sigma(f) = sum_(j>=d) f_j T^j
    $
    Put $D = A[T]_(<d)$ be the $A$-module of polynomials in $A$ of degree $<d$. We now aim to find $q in frak(m) A fps(T), a in frak(m) D$ s.t: 
    $
      T^d + r(T) = (1 + q(T))(T^d + a(T))
    $
    i.e. $r(T) = T^d q(T) + a(T) + a(T) q(T)$. That is, we need to solve: 
    $
      a = pi(r - a q), q = sigma(r - a q)
    $
    Put $Phi(a, q) = (pi(r - a q), sigma(r - a q))$ for $q in frak(m) A fps(T), a in frak(m) D$. Then $Phi$ is $frak(m)$-adically contracting on $frak(m) D times frak(m) A fps(T)$: 

    - If $(a, q) equiv (a', q') mod frak(m)^N$, then: #h(1fr)
      $
        a q - a' q' = a(q - q') + (a - a')q' in frak(m)^(N+1) A fps(T)
      $
      Thus $(r - a q) - (r - a' q') in frak(m)^(N+1) A fps(T)$, and so: 
      $
        pi(r - a q) - pi(r - a' q') in frak(m)^(N+1) D \
        sigma(r - a q) - sigma(r - a' q') in frak(m)^(N+1) A fps(T)
      $

    By Banach-Picard fixed point iteration, $Phi$ has a fixed point, and we are done. 
  ]

  By this lemma, we may factor: 
  $
    H = hat(u) hat(a) \
    hat(u) in hat(A_n)^times \
    hat(a) = T^d + sum_(i=0)^(d-1) hat(a)_i (arrow(X')) T^i, hat(a)_i in frak(b)
  $

  Now perform long division on each component of $hat(y) in hat(A_n) = B fps(T)$ by the monic polynomial $hat(a)$: 
  $
    hat(y)_i (T) = hat(a) (T) hat(q)_i (T) + hat(y)_i^* (T), hat(y)_i^* (T) = sum_(s=0)^(d-1) hat(y)_(i,s) T^s
  $

  - Introduce indeterminates $A_0, dots.c, A_(d-1)$ and $Z_(i,s)$, and set: #h(1fr)
    $
      P(T) = T^d + sum_(s=0)^(d-1) A_s T^s \
      Z^*_i (T) = sum_(s=0)^(d-1) Z_(i,s) T^s
    $
    We may perform long division by the monic polynomial $P(T)$ in the ring $R[arrow(X'), T, arrow(A), arrow(Z)]$. Thus we may write: 
    $
      g(arrow(X'), T, Z^*_1 (T), dots.c, Z^*_m (T)) = P Q_g + sum_(s=0)^(d-1) G_s T^s \

      f_i (arrow(X'), T, Z^*_1 (T), dots.c, Z^*_m (T)) = P Q_i + sum_(s=0)^(d-1) F_(i,s) T^s
    $
    where $Q_g, Q_i in R[arrow(X'), T, arrow(A), arrow(Z)]$ and $G_s, F_(i,s) in R[arrow(X'), arrow(A), arrow(Z)]$. 

  - Now evaluate at $A_s = hat(a)_s, Z_(i,s) = hat(y)^*_(i,s)$. Then the relations become: 
    $
      g(arrow(X'), T, hat(y)^*_1, dots.c, hat(y)^*_m) = hat(a) Q_g (arrow(X'), {hat(a)_s}, {hat(y)^*_(i,s)}) + sum_(s=0)^(d-1) G_s (arrow(X'), {hat(a)_s}, {hat(y)^*_(i,s)}) T^s \
      f_i (arrow(X'), T, hat(y)^*_1, dots.c, hat(y)^*_m) = hat(a) Q_i (arrow(X'), {hat(a)_s}, {hat(y)^*_(i,s)}) + sum_(s=0)^(d-1) F_(i,s) (arrow(X'), {hat(a)_s}, {hat(y)^*_(i,s)}) T^s
    $
    Meanwhile, $hat(y)_i equiv hat(y)_i^* mod hat(a)$. Thus, since $hat(a) divides H = g(arrow(X), hat(y)) divides f_i (arrow(X), hat(y))$
    $
      g(arrow(X), hat(y)) equiv f_i (arrow(X), hat(y)) equiv 0 mod hat(a)
    $
    and so calculating in $hat(A_n)\/hat(a)$, we have: 
    $
      g(arrow(X), hat(y)^*) equiv f_i (arrow(X), hat(y)^*) equiv 0 mod hat(a)
    $
    Thus, uniqueness of long division by the monic polynomial $hat(a)$ implies: 
    $
      G_s (arrow(X'), {hat(a)_s}, {hat(y)^*_(i,s)}) = F_(i,s) (arrow(X'), {hat(a)_s}, {hat(y)^*_(i,s)}) = 0
    $
    where $hat(a)_s, hat(y)^*_(i,s) in hat(A_(n-1))$. 

  - By the inductive hypothesis, for every $N >= 1$, there exist actual solutions $a_s, y^*_(i,s) in A_(n-1)$ agreeing with the formal solutions $hat(a)_s, hat(y)^*_(i,s)$ modulo $frak(m)_(n-1)^N$ s.t: 
    $
      G_s (arrow(X'), {a_s}, {y^*_(i,s)}) = F_(i,s) (arrow(X'), {a_s}, {y^*_(i,s)}) = 0
    $
    In particular, $a_s in frak(m)_(n-1)$. Put: 
    $
      a(T) = T^d + sum_(s=0)^(d-1) a_s T^s in A_(n-1) [T] subset A_n \

      y_i^* (T) = sum_(s=0)^(d-1) y^*_(i,s) T^s in A_(n-1) [T] subset A_n
    $
    By density, we may pick $q_i in A_n$ s.t. $q_i equiv hat(q)_i mod frak(m)_n^N$. Now put: 
    $
      y_i = a q_i + y_i^*
    $
    Then: 
    $
      y_i - hat(y)_i = a (q_i - hat(q)_i) + (a - hat(a)) hat(q)_i + (y_i^* - hat(y)_i^*) in frak(m)_n^N hat(A_n)
    $
    and so $arrow(y) - hat(y) in frak(m)_n^N dot (hat(A_n))^m$. 

  - Because: 
    $
      G_s (arrow(X'), {a_s}, {y^*_(i,s)}) = F_(i,s) (arrow(X'), {a_s}, {y^*_(i,s)}) = 0
    $
    By evaluating the remainder equations at $A_s = a_s, Z_(i,s) = y^*_(i,s)$, we see: 
    $
      g(arrow(X), arrow(y)) in a A_n \
      f_i (arrow(X), arrow(y)) in a A_n
    $

  - Write $g(arrow(X), arrow(y)) = a v$ for $v in A_n$. Then $y equiv hat(y) mod frak(m)_n^N$, 
    $
      g(arrow(X), arrow(y)) - g(arrow(X), hat(y)) in frak(m)_n^N hat(A_n)
    $
    Reduce under the map $rho: hat(A_n) -> k fps(T)$ that kills $pi.alt$ and $arrow(X')$. Then $frak(m)_n^N$ is sent to $(T^N)$. Thus whenever $N > d = "ord"_T (rho(g(arrow(X'), hat(y))))$, 
    $
      "ord"_T (rho(g(arrow(X), arrow(y)))) = d
    $
    Meanwhile, $a$ is monic in $T$ of degree $d$, so $"ord"_T (rho(a)) = d$. Now use $g(arrow(X), arrow(y)) = a v$, and so: 
    $
      "ord"_T (rho(v)) = "ord"_T (rho(g(arrow(X), arrow(y)))) - "ord"_T (rho(a)) = d - d = 0
    $
    Thus $v in A_n$ does not lie in its maximal ideal, so $v in A_n^times$. Hence $(g(arrow(X), arrow(y))) = (a) subset A_n$. Thus $f_i (arrow(X), arrow(y)) in a A_n$ gives the desired divisibility. 
]

#proposition(name: <artin-approx-core-conclusion>)[
  In the setup of @artin-approx-smoothing-reduction-2 (2), Artin approximation holds for the system $f_1, dots.c, f_(m-d)$ and the solution $hat(y)$. 
]
#proof[
  Fix the desired approximation order $N$, and set: 
  $
    d_0 = "ord"_(frak(m)_n) (delta(arrow(X), hat(y)))
  $
  Put $g(arrow(X), arrow(Y)) = delta(arrow(X), arrow(Y))^2$. Then: 
  $
    g(arrow(X), hat(y)) in hat(A_n) - pi.alt hat(A_n) \
    f_i (arrow(X), hat(y)) = 0 in g(arrow(X), hat(y)) hat(A_n)
  $
  Thus by @weierstrass-divisibility-induction, there exists $arrow(y^0) in A_n^m$ agreeing with $hat(y)$ modulo $frak(m)_n^(2N+2d_0+10)$ s.t: 
  $
    f_i (arrow(X), arrow(y^0)) in delta(arrow(X), arrow(y^0))^2 A_n
  $
  Then by @jacobian-improvement, 
  $
    f_i (arrow(X), arrow(y^0)) in delta(arrow(X), arrow(y^0))^2 frak(m)_n^(2N+1) A_n
  $
  and so by @jacobian-correction, there exists $arrow(y) in A_n^m$ agreeing with $arrow(y^0)$, hence $hat(y)$ modulo $frak(m)_n^(N+1)$, s.t: 
  $
    f_i (arrow(X), arrow(y)) = 0
  $
  We have thus found an approximation to order $N+1$. We are thereby done. 
]

We have thus completed the proof of Artin approximation theorem. 

#theorem(name: <artin-approximation-theorem>)[
  (Artin approximation theorem) Let $A$ be the henselization of a finite type algebra over any field or excellent DVR at any prime. Then: 

  + Given polynomial equations $f_1, dots.c, f_r in A[Y_1, dots.c, Y_m]$, suppose that there exist formal solutions $hat(y)_1, dots.c, hat(y)_m in hat(A)$, i.e. 
    $
      f_1 (hat(y)_1, dots.c, hat(y)_m) = dots.c = f_r (hat(y)_1, dots.c, hat(y)_m) = 0
    $
    Then for each $N >= 1$, there exist actual solutions $y_1, dots.c, y_m in A$ s.t: 
    $
      f_1 (y_1, dots.c, y_m) = dots.c = f_r (y_1, dots.c, y_m) = 0
    $
    and each $hat(y)_i equiv y_i (mod frak(m)^N)$. 

  + For any functor $F: AAlg(A) -> cSet$ commuting with direct limits, any $N >= 1$ and any element $hat(xi) in F(hat(A))$, there exists an element $xi in F(A)$ s.t. $hat(xi)$ and $xi$ share the same image in $F(A\/frak(m)^N)$. 
]
#proof[
  The result follows by combining @artin-approx-and-finitely-presented-functors, @artin-approx-reduce-to-std, @artin-approx-smoothing-reduction-2, and @artin-approx-core-conclusion. 
]
