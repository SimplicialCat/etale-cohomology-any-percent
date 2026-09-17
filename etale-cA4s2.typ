#import "void-import.typ": *

== Neron smoothing

We first introduce the setup of this section. 

#notation(name: <situation-neron-smoothing>)[
  Throughout this section, we assume that $V subset V'$ is an extension of DVRs, s.t. a uniformizer $pi.alt in V$ remains a uniformizer in $V'$. 

  $V -> V'$ will factor as: 
  $
    V arrow.hook D ->^phi V'
  $
  for some finite type flat $V$-algebra $D$. Let: 
  $
    frak(q) = ker(phi) in Spec(D) \
    frak(p) = phi^(-1) (pi.alt V') in Spec(D)
  $
  be the images of the generic and special point of $Spec(V')$ in $Spec(D)$. 
]

#definition(name: <defn-affine-neron-blowup>)[
  The *affine Neron blowup* of $D$ along $phi$ is defined to be the algebra: 
  $
    D^+ := D[pi.alt^(-1) frak(p)] subset D[pi.alt^(-1)]
  $
  Equivalently, for generators $(pi.alt, g_1, dots.c, g_t)$ of $frak(p)$, $D^+$ is isomorphic to $D[Z_1,dots.c,Z_t]\/(pi.alt Z_1 - g_1, dots.c, pi.alt Z_t - g_t)$ with all $pi.alt^oo$-torsion killed. 

  We have a commutative diagram: 
  // https://q.uiver.app/#r=typst&q=WzAsNCxbMCwxLCJWIl0sWzEsMCwiRCJdLFsxLDIsIkReKyJdLFsyLDEsIlYnIl0sWzEsMl0sWzAsMSwiIiwwLHsic3R5bGUiOnsidGFpbCI6eyJuYW1lIjoiaG9vayIsInNpZGUiOiJ0b3AifX19XSxbMCwyLCIiLDIseyJzdHlsZSI6eyJ0YWlsIjp7Im5hbWUiOiJob29rIiwic2lkZSI6InRvcCJ9fX1dLFsxLDMsInBoaSJdLFsyLDMsInBoaV4rIl1d
  #align(center, diagram({
    node((0, 0), [$V$])
    node((1, -1), [$D$])
    node((1, 1), [$D^+$])
    node((2, 0), [$V'$])
    edge((1, -1), (1, 1), "->")
    edge((0, 0), (1, -1), "hook->")
    edge((0, 0), (1, 1), "hook->")
    edge((1, -1), (2, 0), [$phi$], label-side: left, "->")
    edge((1, 1), (2, 0), [$phi^+$], label-side: right, "->")
  }, spacing: (3em, 2em)))
  Here, $phi^+$ is defined by sending $Z_i |-> pi.alt^(-1) phi(g_i)$. It is easy to check that this definition is independent of the choice of generators of $frak(p)$. We may then take: 
  $
    frak(q)^+ = ker(phi^+), frak(p)^+ = (phi^+)^(-1) (pi.alt V')
  $
]

#properties(name: <neron-blowup-first-props>)[
  The affine Neron blowup satisfies: 

  + $D[pi.alt^(-1)] cong D^+ [pi.alt^(-1)]$; 

  + For any $f in D - frak(p)$, $phi(f) in.not pi.alt V'$, hence is invertible in $V'$. Thus there is a natural map $phi_f: D_f -> V'$. Then: #h(1fr)
    $
      (D^+)_f cong (D_f)^+
    $
  
  + Given a surjection $rho: (E, psi) ->> (D, phi)$ where $(E, psi)$ is also a factorization of $V -> V'$ as in @situation-neron-smoothing, with $J = ker(rho) subset E$, 
    $
      D^+ cong E^+/((J E^+ : pi.alt^oo)) cong (E^+\/J E^+)/(T_(pi.alt^oo) (E^+\/J E^+))
    $
    Here, $(J : pi.alt^oo)$ is the $pi.alt^oo$-saturation of $J$, and $T_(pi.alt^oo)$ denotes taking $pi.alt^oo$-torsion. 
]
#proof[
  (1) 
  $
    D^+ [pi.alt^(-1)] &cong D[Z_1,dots.c,Z_t,pi.alt^(-1)]/((pi.alt Z_1 - g_1, dots.c, pi.alt Z_t - g_t))\ 
    &cong D[pi.alt^(-1)]
  $
  since each $Z_i$ is identified with $pi.alt^(-1) g_i$. 

  (2) As subsets of $D[f^(-1), pi.alt^(-1)]$, 
  $
    (D_f)^+ = (D^+)_f = D[f^(-1), pi.alt^(-1) frak(p)]
  $

  (3) We may identify $D = E\/J$. Now pick generators $(pi.alt, g_1, dots.c, g_t) = frak(p)_E$. Then: 
  $
    frak(p)_D = (pi.alt, g_1, dots.c, g_t)\/J
  $
  has the same set of generators. Now: 
  $
    E^+ cong E[Z_1,dots.c,Z_t]/(((pi.alt Z_1 - g_1, dots.c, pi.alt Z_t - g_t) : pi.alt^oo)) \

    D^+ cong D[Z_1,dots.c,Z_t]/(((pi.alt Z_1 - g_1, dots.c, pi.alt Z_t - g_t) : pi.alt^oo)) cong E[Z_1,dots.c,Z_t]/((J + (pi.alt Z_1 - g_1, dots.c, pi.alt Z_t - g_t) : pi.alt^oo))
  $
  so by ideal manipulation, 
  $
    D^+ cong E^+/((J E^+ : pi.alt^oo))
  $
]

The purpose of the affine Neron blowup is that, after finitely many Neron blowups, we can make $D$ smooth over $V$ at $frak(p)$. To this end, we show that each blowup strictly decreases a defect measure taking values in the natural numbers. 

#construction[
  Assume that $D$ is smooth of relative dimension $d$ over $V$ at $frak(q)$. Now $Omega_(D\/V)$ is a finite $D$-module. Thus $Omega_(D\/V) otimes_D V'$ is a finite $V'$-module, and hence has a free part and a $pi.alt^oo$-torsion part. Put $Q_D = Omega_(D\/V) otimes_D V'$ and define: 
  $
    e(D, phi) := length_(V') (T_(pi.alt^oo) (Q_D))
  $
  
  Choose a presentation: 
  $
    rho: E = V[T_1,dots.c,T_n] ->> D
  $
  of $D$ as a $V$-algebra, and let $J = ker(rho)$. Then by the second exact sequence: 
  $
    e(D, phi) = length_(V') (coker(J\/J^2 otimes_E V' -> Omega_(E\/V) otimes_E V'))
  $

  For $x in Spec(D)$ over $y in Spec(V)$, put: 
  $
    rho(x) = dim_(k(x)) (Omega_(D\/V) otimes_D k(x)) \
    tau(x) = dim(cal(O)_(D_y,x)) + trd_(k(y))(k(x))
  $
  By #cite-stacks("02FZ")[Lemma 29.29.4], $tau$ is upper semicontinuous, so $tau(frak(p)) >= tau(frak(q))$. 

  Now by @equiv-defns-of-smooth (1), the condition that $D$ is smooth at $frak(q)$ translates to $d = rho(frak(q)) = tau(frak(q))$. Now: 
  $
    Omega_(D\/V) otimes_D k(frak(q)) otimes_(k(frak(q))) Frac(V') &cong Q_D otimes_(V') Frac(V') \
    Omega_(D\/V) otimes_D k(frak(p)) otimes_(k(frak(p))) k(V') &cong Q_D otimes_(V') k(V') \
  $ 
  Thus, 
  $
    rho(frak(q)) = d = "rk"_(V') (Q_D\/T_(pi.alt^oo) (Q_D))
  $
  is also the free rank of $Q_D$, and: 
  $
    rho(frak(p)) = d + e(D, phi)
  $
]

#lemma(name: <zero-defect-implies-smooth>)[
  If $D$ is smooth at $frak(q)$ and $e(D, phi) = 0$, then $D$ is smooth at $frak(p)$. 
]
#proof[
  Since $rho(frak(p)) = d + e(D, phi)$, $e(D, phi) = 0$ gives $rho(frak(p)) = d$. Now: 
  $
    rho(frak(p)) = d = tau(frak(q)) <= tau(frak(p))
  $
  so by @equiv-defns-of-smooth (1), $D$ is smooth at $frak(p)$ with the inequality an equality. 
]

#proposition(name: <neron-smoothing-smoothness-pass>)[
  + If $D$ is smooth of relative dimension $d$ over $V$ at $frak(q)$, then $D^+$ is smooth of relative dimension $d$ over $V$ at $frak(q)^+$; 

  + If $D$ is smooth of relative dimension $d$ over $V$ at $frak(p)$ and $k(V')\/k(V)$ is a separable#footnote[Separability for a non-algebraic field extension is defined as in #cite-stacks("030O")[Definition 10.42.1].] field extension, then $D^+$ is smooth of relative dimension $d$ over $V$ at $frak(p)^+$. 

  + In the setup of (2), assume that $D cong V[T_1,dots.c,T_r]_s$ is a localization of a polynomial ring over $V$. Then, after potentially increasing $s$ in $V[T_1,dots.c,T_r] - frak(p)$, 
    $
      Q_D &= Omega_(D\/V) otimes_D V' \
      Q_(D^+) &= Omega_(D^+\/V) otimes_(D^+) V'
    $
    Then both $Q_D, Q_(D^+)$ are free of rank $r$ over $V'$, and the canonical map $Q_D -> Q_(D^+)$ induced by the first exact sequence has matrix presentation: 
    $
      "diag"(pi.alt I_c, I_(r-c))
    $
    under a suitable choice of basis, where $c = dim_(k(frak(p))) (D_(frak(p))\/pi.alt D_(frak(p)))$. 
    
    Consequently, we may identify $pi.alt Q_(D^+) subset Q_D subset Q_(D^+)$ and $Q_(D^+)\/Q_D cong k(V')^(oplus c)$. 
]
#proof[
  (1) Using @equiv-defns-of-smooth (2), we see that smoothness depends only on the chosen fiber. Now $D[pi.alt^(-1)] = D^+ [pi.alt^(-1)]$, so $Spec(D)$ and $Spec(D^+)$ share the same generic fiber over $Spec(V)$. Thus $D$ being smooth at $frak(q)$ implies $D^+$ being smooth at $frak(q)^+$. 

  (2) By @neron-blowup-first-props, we may replace $D$ with a suitable localization at an element of $D - frak(p)$. 

  Put $ol(frak(p)) = frak(p)\/pi.alt D in Spec(D\/pi.alt D)$. Since smoothness is stable under base change, $D\/pi.alt D$ is smooth over $k(V)$ at $ol(frak(p))$. Thus by @equiv-defns-of-smooth (2), $(D\/pi.alt D)_(ol(frak(p)))$ is a regular local ring. 

  Choose $g_1, dots.c, g_c in frak(p)$ mapping to a regular system of parameters in $(D\/pi.alt D)_(ol(frak(p))) = D_(frak(p))\/pi.alt D_(frak(p))$. Then up to shrinking $D$ around $frak(p)$, we have $frak(p) = (pi.alt, g_1, dots.c, g_c)$. By flatness, $pi.alt$ is a nonzerodivisor in $D_(frak(p))$. Thus $pi.alt, g_1, dots.c, g_c$ is a regular sequence in $D_(frak(p))$. By shrinking $D$ around $frak(p)$, we may thus assume that $pi.alt, g_1, dots.c, g_c$ is a regular sequence in $D$. 

  By applying the following lemma inductively: 
  #lemma[
    If $a$ is a nonzerodivisor in $A$ and $b in A$ is a nonzerodivisor in $A\/a$, then $a$ is a nonzerodivisor in $A[Z]\/(a Z - b)$. 
  ]
  #proof[
    If $a f(Z) = (a Z - b) g(Z)$ for some $f(Z), g(Z) in A[Z]$, then reducing modulo $a$ gives $b g(Z) = 0 in A\/a [Z]$. Since $b in A\/a$ is a nonzerodivisor, $g(Z) = 0 in A\/a [Z]$. Thus there exists $h(Z) in A[Z]$ s.t. $g(Z) = a h(Z)$. Now: 
    $
      a f(Z) = a (a Z - b) h(Z) 
    $
    and since $a in A$ is a nonzerodivisor, $f(Z) = (a Z - b) h(Z)$. Thus $f(Z) = 0 in A[Z]\/(a Z - b)$. 
  ]
  We see that $pi.alt Z_1 - g_1, dots.c, pi.alt Z_c - g_c$ is a regular sequence in $D[Z_1,dots.c,Z_c]$, and $pi.alt$ is a nonzerodivisor in $D[Z_1,dots.c,Z_c]\/(pi.alt Z_1 - g_1, dots.c, pi.alt Z_c - g_c)$. Thus, 
  $
    D^+ = D[Z_1,dots.c,Z_c]/((pi.alt Z_1 - g_1, dots.c, pi.alt Z_c - g_c))
  $
  Put $I = (pi.alt Z_1 - g_1, dots.c, pi.alt Z_c - g_c) subset D[Z_1,dots.c,Z_c]$. Then: 
  
  - Consider the second exact sequence: #h(1fr)
    $
      ol(frak(p))(D\/pi.alt D)_(ol(frak(p)))\/ol(frak(p))^2(D\/pi.alt D)_(ol(frak(p))) -> Omega_((D\/pi.alt D)\/k(V)) otimes_D k(frak(p)) -> Omega_(k(frak(p))\/k(V)) -> 0
    $
    We have: 

    - By regularity, $dim_(k(frak(p))) (ol(frak(p))(D\/pi.alt D)_(ol(frak(p)))\/ol(frak(p))^2 (D\/pi.alt D)_(ol(frak(p)))) = dim((D\/pi.alt D)_(ol(frak(p))))$; 

    - By smoothness and @equiv-defns-of-smooth (1), #h(1fr)
      $
        dim_(k(frak(p))) (Omega_((D\/pi.alt D)\/k(V)) otimes_D k(frak(p))) = dim((D\/pi.alt D)_(ol(frak(p)))) + trd_(k(V)) (k(frak(p)))
      $

    - $k(frak(p))\/k(V)$ is a finitely generated intermediate field of $k(V')\/k(V)$, a separable extension. Thus it is separably generated, and by @cite-matsumura-ca[Theorem 59],
      $
        dim_(k(frak(p))) (Omega_(k(frak(p))\/k(V))) = trd_(k(V)) (k(frak(p)))
      $

    Thus, by comparing dimensions, this sequence is short exact. Hence $d g_1, dots.c, d g_c$ are linearly independent in $Omega_((D\/pi.alt D)\/k(V)) otimes_D k(frak(p))$. 

  - Now consider another second exact sequence: 
    $
      (I\/I^2)_(frak(p)^+) -> (Omega_(D[Z_1,dots.c,Z_c]\/V))_(frak(p)^+) -> (Omega_(D^+\/V))_(frak(p)^+) -> 0
    $
    By splitting a first exact sequence, we may identify: 
    $
      Omega_(D[Z_1,dots.c,Z_c]\/V) cong (Omega_(D\/V) otimes_D D[Z_1,dots.c,Z_c]) oplus oplus.big_(b=1)^c D[Z_1,dots.c,Z_c] d Z_b
    $
    Thus the second exact sequence becomes: 
    $
      (I\/I^2)_(frak(p)^+) -> (Omega_(D\/V) otimes_D D^+_(frak(p)^+)) oplus oplus.big_(b=1)^c D^+_(frak(p)^+) d Z_b -> (Omega_(D^+\/V))_(frak(p)^+) -> 0
    $
    
    - The relation classes are sent to $pi.alt d Z_b - d g_b$. They reduce to $- d g_b$ modulo the maximal ideal at $frak(p)^+$ and become linearly independent. Thus, this sequence is short exact after reduction modulo the maximal ideal. 

    - By smoothness, the middle term is free. By #cite-stacks("061P")[Definition 10.69.1] and #cite-stacks("00LN")[Lemma 10.69.2], since $I = (pi.alt Z_1 - g_1, dots.c, pi.alt Z_c - g_c)$ is generated by a regular sequence, $I\/I^2 cong (D[Z_1,dots.c,Z_c]\/I)^(oplus c)$ with basis $pi.alt Z_1 - g_1, dots.c, pi.alt Z_c - g_c$. 

    In summary, this right exact sequence has the first term free of rank $c$, the second term free of rank $c + d$, and is exact upon reducing modulo the maximal ideal at $frak(p)^+$. 

    Thus, the matrix of the first map has a $c times c$ minor that is invertible in $k(frak(p)^+)$. This minor is thus invertible in $D^+_(frak(p)^+)$. Thus this right exact sequence is split exact, and so $D^+$ is smooth at $frak(p)^+$ by @equiv-defns-of-smooth (5). 

  (3) Continue as in the setup for (2). We have seen that $d g_1, dots.c, d g_c in Omega_((D\/pi.alt D)\/k(V)) otimes_D k(frak(p)) cong Omega_(D\/V) otimes_D k(frak(p))$. Write: 
  $
    d g_i = sum_(j=1)^r a_(i,j) d T_j
  $
  Then some $c times c$ minor $Delta$ of the matrix $display(mat(a_(i,j))_(i<=c,j<=r))$ is invertible in $k(frak(p))$. After reordering $T_j$, we may assume that: 
  $
    Delta = mat(a_(i,j))_(i,j<=c) in MM_(c times c) (D)
  $
  has $det(Delta) in k(frak(p))^times$. Thus $det(Delta) in D_(frak(p))^times$. Thus, shrinking $D$ around $frak(p)$, we may assume that $det(Delta) in D^times$. 

  Then $d g_1, dots.c, d g_c, d T_(c+1), dots.c, d T_r$ is a basis of $Omega_(D\/V)$, i.e: 
  $
    Omega_(D\/V) = oplus.big_(i=1)^c D d g_i oplus oplus.big_(i=c+1)^r D d T_i
  $
  Meanwhile, recall: 
  $
    Omega_(D^+\/V) cong ((Omega_(D\/V) otimes_D D^+) oplus oplus.big_(i=1)^c D^+ d Z_i)/((pi.alt d Z_1 - d g_1, dots.c, pi.alt d Z_c - d g_c)) cong (oplus.big_(i=1)^c D^+ d g_i oplus oplus.big_(i=c+1)^r D^+ d T_i oplus oplus.big_(i=1)^c D^+ d Z_i)/((pi.alt d Z_1 - d g_1, dots.c, pi.alt d Z_c - d g_c))
  $
  It is thus free with basis $d Z_1, dots.c, d Z_c, d T_(c+1), dots.c, d T_r$, and the map $Omega_(D\/V) otimes_D D^+ -> Omega_(D^+\/V)$ sends: 
  $
    d g_i |-> pi.alt d Z_i, d T_i |-> d T_i
  $
  It thus has matrix $"diag"(pi.alt I_c, I_(r-c))$ under these two bases. 
]


#proposition(name: <neron-blowup-defect-drop>)[
  Assume that $D$ is smooth at $frak(q)$, and that the residue field extension $k(V')\/k(V)$ is separable. That is, every finitely generated intermediate field is separably generated. If $D$ is not smooth at $frak(p)$, then: 
  $
    e(D^+, phi^+) < e(D, phi)
  $
  with $D^+$ remaining smooth at $frak(q)^+$. 
]
#proof[
  Choose a presentation: 
  $
    0 -> J arrow.hook E ->> D -> 0 
  $
  of $D$ as a $V$-algebra, where $E$ is a polynomial algebra over $V$. 

  Note that for $e(D_([q])^+, phi_([q])^+) = e(D^+, phi^+)$, since $Q_(D_([q])^+) cong Omega_(D\/V) otimes_D D_([q]) otimes_(D_([q])) V' cong Q_(D^+)$. Thus, it is safe to localize $E$ and $D$ at an element $q in E - frak(p)_E$. By @neron-smoothing-smoothness-pass, we may thus localize $E$ so that $E$ is smooth of relative dimension $d$ over $V$, s.t. the map: 
  $
    Q_E -> Q_(E^+)
  $ 
  has matrix presentation $"diag"(pi.alt I_c, I_(r-c))$. 

  Put $J^+ = ker(E^+ ->> D^+) = (J E^+ : pi.alt^oo)$. Now put: 
  $
    M = Q_E = Omega_(E\/V) otimes_E V, N = im(J\/J^2 otimes_D V' -> M) \
    M^+ = Q_(E^+) = Omega_(E^+\/V) otimes_(E^+) V, N^+ = im(J^+\/(J^+)^2 otimes_(D^+) V' -> M^+)
  $
  The second exact sequence identifies $Q := M\/N cong Q_D$ and $Q^+ := M^+\/N^+ cong Q_(D^+)$. By @neron-smoothing-smoothness-pass (3), 
  $
    pi.alt M^+ subset M subset M^+
  $
  with $M, M^+$ free of rank $r$ over $V'$. 

  Put $K = Frac(V), K' = Frac(V')$. Now: 

  - If $h in J$, then $h in frak(p)_E$ and so $pi.alt^(-1) h in pi.alt^(-1) frak(p)_E subset E^+$. Also $pi.alt^(-1) h in (J E^+: pi.alt^oo) in J^+$. Furthermore, $d(pi.alt^(-1) h) = pi.alt^(-1) d h$. Thus, we have shown that $N subset pi.alt N^+$, and in particular: 
    $
      N_(K') = N^+_(K')
    $
    where we already know $M_(K') = M^+_(K')$. 

  Both $N$ and $N^+$ are free of rank $r-d$. Then $Q$ and $Q^+$ have free rank $d$, so $d$ is the relative dimension of $D$ at $frak(q)$. 
  
  Set $W = N_(K') = N^+_(K') subset M^+_(K')$ and intersect: 
  $
    tilde(N) = W inter M, tilde(N)^+ = W inter M^+
  $
  where the intersections are performed in $M^+_(K')$. Then: 
  $
    T_(pi.alt^oo) (Q) = tilde(N)\/N, T_(pi.alt^oo) (Q^+) = tilde(N)^+\/N^+
  $
  and so: 
  $
    e(D, phi) - e(D^+, phi^+) &= length_(V') (tilde(N)\/N) - length_(V') (tilde(N)^+\/N^+) \
    &= length_(V') (N^+\/N) - length_(V') (tilde(N)^+\/tilde(N))
  $
  The inclusion $pi.alt M^+ subset M$ gives $pi.alt tilde(N)^+ subset tilde(N)$, and so $length_(V') (tilde(N)^+\/tilde(N)) <= r - d$. Meanwhile, $N subset pi.alt N^+$ shows that $length_(V') (N^+\/N) >= r-d$. Thus, 
  $
    e(D, phi) - e(D^+, phi^+) = length_(V') (N^+\/N) - length_(V') (tilde(N)^+\/tilde(N)) >= 0
  $
  We need to show that this quantity is strictly $>0$. Assuming equality, we must have: 
  $
    tilde(N) = pi.alt tilde(N)^+, N = pi.alt N^+
  $
  Because $D$ is not smooth at $frak(p)$, by @zero-defect-implies-smooth, $e(D, phi) > 0$. Thus by arguments in its proof, 
  $
    s := dim_(k(frak(p))) (Omega_(D\/V) otimes_D k(frak(p))) > d
  $
  Thus, for the following second exact sequence: 
  $
    J\/J^2 otimes_D k(frak(p)) -> oplus.big_(i=1)^r k(frak(p)) d T_i -> Omega_(D\/V) otimes_D k(frak(p)) -> 0
  $
  the first map has image of dimension $r-s$. We may thus pick a set of generators $J = (h_1, dots.c, h_t)$ s.t. $d h_1, dots.c, d h_(r-s)$ is a basis of this image, and $d h_(r-s+1), dots.c,  d h_t = 0 in oplus.big_(i=1)^r k(frak(p)) d T_i$. 
  
  On the other hand, choose a set of generators $frak(p)_E = (pi.alt, g_1, dots.c, g_c)$ as in the proof of @neron-smoothing-smoothness-pass (2). Then since $d g_1, dots.c, d g_c in Omega_(E\/V) otimes_E k(frak(p)_E)$ are linearly independent and $d pi.alt = 0$, 
  $
    ker(frak(p)_E E_(frak(p)_E)\/frak(p)_E^2 E_(frak(p)_E) -> Omega_(E\/V) otimes_E k(frak(p)_E)) = k(frak(p)_E) [pi.alt]
  $
  Thus for $i>r-s$, since the image of $d h_i$ vanishes in $oplus.big_(i=1)^r k(frak(p)) d T_i$, $d h_i$ must vanish in $Omega_(E\/V) otimes_E k(frak(p)_E)$. Thus, 
  $
    h_i = pi.alt b_i + u_i, b_i in E_(frak(p)), u_i in frak(p)_E^2 E_(frak(p)_E)
  $
  By shrinking $E$ around $frak(p)_E$, we may assume $b_i in E, u_i in frak(p)_E^2 E$. Now $h_i$ maps to $0$ in $V'$, and $u_i$ maps to an element of $pi.alt^2 V'$. Thus $b_i$ maps to an element of $pi.alt V'$, and so $b_i in frak(p)_E$ too. 

  Now $N$ is generated by $d h_1, dots.c, d h_t$, but $dim_(k(V)) (N\/pi.alt N) = r - d > r - s$. Thus, there exists some $i > r - s$ s.t. $d h_i in.not pi.alt N$. For this $i$: 

  - $pi.alt^(-2) h_i = pi.alt^(-1) b_i + pi.alt^(-2) u_i in E[pi.alt^(-1) frak(p)_E] = E^+$ and is in $(J E^+ : pi.alt^oo) = J^+$. Consequently, #h(1fr)
    $
      d(pi.alt^(-2) h_i) in N^+
    $
    and so $d h_i in pi.alt^2 N^+$. But $N = pi.alt N^+$, so: 
    $
      d h_i in pi.alt^2 N^+ = pi.alt N
    $
    a contradiction. 

  Thus, equality cannot hold, and so $e(D, phi) > e(D^+, phi^+)$. 
]

#theorem(name: <classical-neron-smoothing>)[
  (Classical Neron smoothing) Let $(D, phi)$ be as in @situation-neron-smoothing. Then assuming: 

  - $D$ is smooth at $frak(q)$; 

  - $k(V')\/k(V)$ is separable. 

  Then after applying finitely many Neron blowups to $D$ to obtain an algebra $E$, $E$ is smooth at $frak(p)_E$. 
]
#proof[
  We apply Neron blowups to $D$ consecutively: 
  $
    D = D_0 -> D_1 -> dots.c -> D_m -> D_(m+1) -> dots.c -> V'
  $
  where $D_(m+1) := D_m^+$. If none of $D_m$ is smooth at $frak(p)_m$, @neron-blowup-defect-drop may be applied indefinitely, giving a strictly descending chain of natural numbers: 
  $
    e(D_0, phi_0) > e(D_1, phi_1) > dots.c > e(D_m, phi_m) > e(D_(m+1), phi_(m+1)) > dots.c
  $
  which is absurd. Thus, some $D_m$ is smooth at $frak(p)_m$. 
]

#proposition(name: <artin-approx-smoothing-reduction>)[
  TFAE: 

  + For any excellent DVR $R$, let $A_n = R{X_1, dots.c, X_n}$. For any $N >= 1$, if a system of polynomial equations $f_1, dots.c, f_r in R[Y_1, dots.c, Y_m]$ has a formal solution $hat(y)_1, dots.c, hat(y)_m in hat(A_n)$, where $hat(A_n) = hat(R) fps(X_1\, dots.c\, X_n)$: 
    $
      f_1 (hat(y)_1, dots.c, hat(y)_m) = dots.c = f_r (hat(y)_1, dots.c, hat(y)_m) = 0
    $
    then there exists a solution $y_1, dots.c, y_m in A_n$ agreeing with $hat(y)_1, dots.c, hat(y)_m in hat(A_n)$ modulo $frak(m)_n^N$: 
    $
      f_1 (y_1, dots.c, y_m) = dots.c = f_r (y_1, dots.c, y_m) = 0
    $

    That is, Artin approximation holds for the ring $A_n = R{X_1, dots.c, X_n}$ for polynomial systems in $R[X_1,dots.c,X_n,Y_1,dots.c,Y_m]$. 

  + Setup as in (1), but with the additional assumption that for: 
    $
      phi: R[arrow(X), arrow(Y)] -> hat(A_n), Y_i |-> hat(y)_i
    $
    we have: 
    $
      (f_1, dots.c, f_r) = ker(phi)
    $
    and that $D = R[arrow(X), arrow(Y)]\/ker(phi) = im(phi)$ is smooth over $R[arrow(X)]$ at the prime $phi^(-1) (pi.alt hat(A_n)) in Spec(D)$. 
]
#proof[
  (1)$==>$(2) is tautological, so we only prove (2)$==>$(1). Firstly, we may harmlessly add finitely many equations to the system, so that: 
  $
    (f_1, dots.c, f_r) = ker(phi)
  $

  Put $D = im(phi)$. Then $Frac(D)$ is an intermediate finitely generated extension in $Frac(hat(A_n))\/Frac(R)(arrow(X))$. 
  
  Since $R[arrow(X)]_((pi,arrow(X)))$ is excellent, the generic fiber $Spec(Frac(hat(A_n))) -> Spec(Frac(R)(arrow(X)))$ is regular. By #cite-stacks("07EQ")[Lemma 15.42.6], $Frac(hat(A_n))\/Frac(R)(arrow(X))$ is a separable extension. 
  
  Thus $Frac(D)\/Frac(R)(arrow(X))$ is separably generated, and so by #cite-stacks("07EQ")[Lemma 15.42.6], $Frac(hat(A_n))\/Frac(R)(arrow(X))$ again, the map $Spec(D) -> Spec(R[arrow(X)])$ has the generic point of the generic fiber geometrically regular. Thus by @equiv-defns-of-smooth (2), $Spec(D)$ is smooth over $Spec(R[arrow(X)])$ in a dense open set. 

  Now put $V = R[arrow(X)]_((pi.alt)), V' = (hat(A_n))_(pi.alt hat(A_n))$. Then $V -> V'$ is an extension of DVRs with the same uniformizer $pi.alt$. The residue fields are: 
  $
    k(V') = Frac(k fps(arrow(X))), k(V) = k(arrow(X))
  $
  where $k = k(R)$. Thus $k(V')\/k(V)$ is separable since $k[arrow(X)]_((arrow(X)))$ is excellent. We aim to apply Neron blowups to $D otimes_(R[arrow(X)]) R[arrow(X)]_((pi.alt))$, and expect only harmless modifications to our system. 

  #construction[
    Suppose that: 
    $
      C = R[arrow(X), arrow(Y)]\/frak(q), frak(q) = (f_1, dots.c, f_r)
    $
    is a finite type $R[arrow(X)]$-algebra, that is a $R[arrow(X)]$-subalgebra of $hat(A_n)$. We also assume that $Spec(C) -> Spec(R[arrow(X)])$ is smooth on a dense open. 
    
    Put $frak(p) = pi.alt hat(A_n) inter C in Spec(C)$, and denote: 
    $
      C' := C[pi.alt^(-1) frak(p)] subset C[pi.alt^(-1)] subset hat(A_n)[pi.alt^(-1)]
    $
    $C'$ is in fact a subalgebra of $hat(A_n)$, since by definition $pi.alt^(-1) frak(p) subset hat(A_n)$. Choose generators $frak(p) = (pi.alt, g_1, dots.c, g_t)$, and then we have an isomorphism: 
    $
      C' cong C[Z_1,dots.c,Z_t]/(((pi.alt Z_1 - g_1, dots.c, pi.alt Z_t - g_t) : pi.alt^oo))
    $
    Let: 
    $
      J_0 = (f_1 (arrow(X), arrow(Y)), dots.c, f_r (arrow(X), arrow(Y)), pi.alt Z_1 - g_1 (arrow(X), arrow(Y)), dots.c, pi.alt Z_t - g_t (arrow(X), arrow(Y))) subset R[arrow(X), arrow(Y), arrow(Z)]
    $
    Then $J = (J_0 : pi.alt^oo)$ is obtained by adjoining finitely many new equations, say: 
    $
      J = J_0 + (h_1 (arrow(X), arrow(Y), arrow(Z)), dots.c, h_s (arrow(X), arrow(Y), arrow(Z)))
    $
    and then $J$ satisfies: 
    $
      C' cong R[arrow(X), arrow(Y), arrow(Z)]\/J
    $
    Now for the given solution $hat(y) in hat(A_n)^m$, by definition $g_i (X, hat(y)) in pi.alt hat(A_n)$, so we may take $hat(z)_i = pi.alt^(-1) g_i (X, hat(y))$. Then the formal solution $hat(y), hat(z)$ satisfies the equations for $J_0$: 
    $
      f_i (X, hat(y)) = 0 \
      pi.alt hat(z)_i - g_i (X, hat(y)) = 0
    $
    Furthermore, for any $h_i$, there exists some $M$ s.t. $pi.alt^M h_i in J_0$. Thus $pi.alt^M h_i (X, hat(y), hat(z)) = 0 in hat(A_n)$. However $hat(A_n)$ is a domain, so $h_i (X, hat(y), hat(z)) = 0$. In other words: 

    - The formal solution $hat(y) in hat(A_n)^m$ for $(f_1, dots.c, f_r) subset R[arrow(X), arrow(Y)]$ induces a formal solution $(hat(y), hat(z)) in hat(A_n)^(m+t)$ for $J subset R[arrow(X), arrow(Y), arrow(Z)]$. 

      Thus if the system $f_i, pi.alt Z_i - g_i, h_i$ defining $J$ has an approximating solution $(y, z) in A_n^(m+t)$ agreeing with $(hat(y), hat(z))$ modulo $frak(m)_n^N$, then $y in A_n^m$ would be an approximating solution to $(f_1,dots.c,f_r)$ agreeing with $hat(y)$ modulo $frak(m)_n^N$. 

    Therefore, we may harmlessly replace the original system of equations in $arrow(Y)$ defining $C$ by a new system of equations in $arrow(Y), arrow(Z)$ defining $C'$. 
    
    Now put $C_V := C otimes_(R[arrow(X)]) R[arrow(X)]_((pi.alt)) = C otimes_(R[arrow(X)]) V$, a finite type $V$-algebra. It is flat since $C$ as a subring of $hat(A_n)$ is free of $pi.alt$-torsion. 
    
    We have the local evaluation map:  
    $
      phi_V: C_V -> V', c otimes v |-> c v
    $
    This map is $C_V -> hat(A_n) otimes_(R[arrow(X)]) V$ the base change of $phi$, followed by the map $(hat(A_n))_(pi.alt R[arrow(X)]) = hat(A_n) otimes_(R[arrow(X)]) V -> V' = (hat(A_n))_(pi.alt hat(A_n))$. The second map is a localization of domains, hence injective. The first map is a localization of an injection, hence injective. Thus $phi_V$ is injective. 

    - If $c in C, f in R[arrow(X)] - pi.alt R[arrow(X)]$ has $c\/f in pi.alt V'$, then: #h(1fr)
      $
        c in pi.alt f V' inter C subset (pi.alt V' inter hat(A_n)) inter C = pi.alt hat(A_n) inter C = frak(p)
      $
      Conversely, if $c in frak(p), f in R[arrow(X)] - pi.alt R[arrow(X)]$, then $c in pi.alt hat(A_n)$ and $f in V' - pi.alt V' = (V')^times$, and so $c\/f in pi.alt V'$. 

      Therefore, $phi_V^(-1) (pi.alt V') = frak(p) otimes_(R[arrow(X)]) V$ is the extension of $frak(p)$. It is thus generated by $(pi.alt, g_1, dots.c, g_t)$ too. 

      Thus, 
      $
        C_V^+ = (C_V [Z_1, dots.c, Z_t])/((pi.alt Z_1 - g_1, dots.c, pi.alt Z_t - g_t : pi.alt^oo)) = C' otimes_(R[arrow(X)]) V
      $

    - $Spec(C) -> Spec(R[arrow(X)])$ is smooth on a dense open. Thus $Spec(C_V) -> Spec(V)$, as a localization of this map, is also generically smooth. Since $ker(phi_V) = 0$, the "smooth at $frak(q)$" assumption of @classical-neron-smoothing is satisfied. 
  ]

  Summarizing the discussion above, we may apply $C |-> C'$ finitely many times with only harmless extensions to the polynomial system. By @classical-neron-smoothing and the discussion above, we may assume that $Spec(D_V) -> Spec(V)$ is smooth at $frak(p)_V = phi^(-1) (pi.alt hat(A_n)) otimes_(R[arrow(X)]) V$. Now $(D_V)_(frak(p)_V) cong D_(phi^(-1) (pi.alt hat(A_n)))$ by comparing localizations, so $Spec(D) -> Spec(R[arrow(X)])$ is smooth at $phi^(-1) (pi.alt hat(A_n))$. We've thus reduced to the hypothesis. 
]

We continue the setup to turn @artin-approx-smoothing-reduction to a more usable form. 

#construction[
  Let $f_1, dots.c, f_r in R[arrow(X), arrow(Y)]$ be a system with a formal solution $hat(y) in hat(A_n)^m$ as in the setup of @artin-approx-smoothing-reduction (2). That is, for: 
  $
    phi: R[arrow(X), arrow(Y)] -> hat(A_n), Y_i |-> hat(y)_i
  $
  we have: 
  $
    frak(p) = ker(phi) = (f_1, dots.c, f_r)
  $
  and $D = im(phi)$ is smooth over $R[arrow(X)]$ at $frak(r) = phi^(-1) (pi.alt hat(A_n))$. Let $d$ be the relative dimension of smoothness at this point. @equiv-defns-of-smooth (4) gives a second exact sequence: 
  $
    frak(p)\/frak(p)^2 -> oplus.big_(i=1)^m D d Y_i -> Omega_(D\/R[arrow(X)]) -> 0
  $
  split exact at $ol(frak(r)) = frak(r)\/frak(p) in Spec(D)$. Thus, up to reordering the equations and the indeterminates $Y_i$, this splitting shows that: 
  $
    delta(arrow(X), arrow(Y)) = det mat(display((partial f_i)/(partial Y_j)))_(i,j <= m-d) in D_(ol(frak(r)))^times
  $
  Equivalently, 
  $
    delta(arrow(X), hat(y)) = det mat(display((partial f_i)/(partial Y_j)) (arrow(X), hat(y)))_(i,j <= m-d) in hat(A_n) - pi.alt hat(A_n)
  $
  We claim that it is safe to replace the equations $(f_1, dots.c, f_r)$ by just $(f_1, dots.c, f_(m-d))$. We aim to find $h in R[arrow(X), arrow(Y)] - frak(r)$ s.t. $h frak(p) subset (f_1, dots.c, f_(m-d))$. 

  - Take the local ring $C = R[arrow(X), arrow(Y)]_(frak(r))$. Then $C$ is regular, and by smoothness of $D = R[arrow(X), arrow(Y)]\/frak(p)$ at $ol(frak(r))$, $C\/frak(p) C$ is regular. 

    Since $R[arrow(X), arrow(Y)]$ is smooth over $R[arrow(X)]$ of relative dimension $m$, and $D$ is smooth over $R[arrow(X)]$ at $ol(frak(r))$ of relative dimension $d$, 
    $
      m = dim(C) + trd_(k(arrow(X))) (C\/frak(r) C) \

      d = dim(C\/frak(p) C) + trd_(k(arrow(X))) (C\/frak(r) C)
    $
    Thus $dim(C) - dim(C\/frak(p) C) = m - d$. Thus, $frak(p) C = (a_1, dots.c, a_(m-d))$ for a regular sequence $a_1, dots.c, a_(m-d)$ in $C$. By #cite-stacks("061P")[Definition 10.69.1] and #cite-stacks("00LN")[Lemma 10.69.2], $frak(p)C\/frak(p)^2 C$ is a free $C\/frak(p)$-module of rank $m-d$. 

    Then the invertible minor $delta(arrow(X), arrow(Y))$ shows that $f_1, dots.c, f_(m-d) in frak(p)$, when reduced to $frak(p)C\/frak(p)^2 C$, forms a basis. By Nakayama's lemma, 
    $
      frak(p) C = (f_1, dots.c, f_(m-d)) + frak(p)^2 C
    $
    and by Nakayama again, $frak(p) C = (f_1, dots.c, f_(m-d))$. Thus for every generator $f_i in frak(p)$, there exists $g_i in C = R[arrow(X), arrow(Y)]_(frak(r))$ s.t. $f_i in g_i (f_1, dots.c, f_(m-d)) subset C$. Clearing finitely many denominators in $R[arrow(X), arrow(Y)] - frak(r)$, we have constructed $h in R[arrow(X), arrow(Y)] - frak(r)$ s.t: 
    $
      h frak(p) subset (f_1, dots.c, f_(m-d))
    $

  Let $M = "ord"_(frak(m)_n) (h(arrow(X), hat(y)))$. Then: 

  - If we have $arrow(y) in A_n^m$ agreeing with $hat(y)$ modulo $frak(m)_n^N$ s.t. $N > M$, then: #h(1fr)
    $
      h(arrow(X), arrow(y)) mod frak(m)_n^N = h(arrow(X), hat(y)) mod frak(m)_n^N != 0
    $
    and so in particular $h(arrow(X), arrow(y)) != 0$. Now since $h frak(p) subset (f_1, dots.c, f_(m-d))$, for each $i<=r$, 
    $
      h(arrow(X), arrow(y)) f_i (arrow(X), arrow(y)) = 0
    $
    where $h(arrow(X), arrow(y)) != 0$. Since $A_n$ is a domain, each $f_i (arrow(X), arrow(y)) = 0$. 

  In summary, if we can approximate $hat(y)$ as a solution to $(f_1, dots.c, f_(m-d))$ to an arbitrary order, then we can approximate $hat(y)$ as a solution to $(f_1, dots.c, f_r)$ to an arbitrary order. 
]

Following this discussion and @artin-approx-smoothing-reduction, we have: 

#proposition(name: <artin-approx-smoothing-reduction-2>)[
  TFAE: 

  + For any excellent DVR $R$, let $A_n = R{X_1, dots.c, X_n}$. For any $N >= 1$, if a system of polynomial equations $f_1, dots.c, f_r in R[Y_1, dots.c, Y_m]$ has a formal solution $hat(y)_1, dots.c, hat(y)_m in hat(A_n)$, where $hat(A_n) = hat(R) fps(X_1\, dots.c\, X_n)$: 
    $
      f_1 (hat(y)_1, dots.c, hat(y)_m) = dots.c = f_r (hat(y)_1, dots.c, hat(y)_m) = 0
    $
    then there exists a solution $y_1, dots.c, y_m in A_n$ agreeing with $hat(y)_1, dots.c, hat(y)_m in hat(A_n)$ modulo $frak(m)_n^N$: 
    $
      f_1 (y_1, dots.c, y_m) = dots.c = f_r (y_1, dots.c, y_m) = 0
    $

    That is, Artin approximation holds for the ring $A_n = R{X_1, dots.c, X_n}$ for polynomial systems in $R[X_1,dots.c,X_n,Y_1,dots.c,Y_m]$. 

  + In the setup of (1), assume in addition that $r = m - d <= m$ and that the Jacobian determinant satisfies: 
    $
      delta(arrow(X), hat(y)) = det mat(display((partial f_i)/(partial Y_j)) (arrow(X), hat(y)))_(i,j <= m-d) in hat(A_n) - pi.alt hat(A_n)
    $
]
