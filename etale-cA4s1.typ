#import "void-import.typ": *

In this appendix, we prove the Artin approximation theorem, a critical input to the proof of the proper base change theorem. It states that: 

- Let $A$ be the henselization at a prime ideal of a finite type algebra over a field or an excellent DVR, and $hat(A)$ the completion of $A$ w.r.t. its maximal ideal $frak(m)$. 

  Given polynomial equations $f_1, dots.c, f_m in A[Y_1, dots.c, Y_n]$, suppose that there exist formal solutions $hat(a)_1, dots.c, hat(a)_n in hat(A)$, i.e: 
  $
    f_1 (hat(a)_1, dots.c, hat(a)_n) = dots.c = f_m (hat(a)_1, dots.c, hat(a)_n) = 0
  $
  Then for each $N >= 1$, there exist actual solutions $a_1, dots.c, a_n in A$ s.t: 
  $
    f_1 (a_1, dots.c, a_n) = dots.c = f_m (a_1, dots.c, a_n) = 0
  $
  and each $hat(a)_i equiv a_i (mod frak(m)^N)$. 

The proof method that we shall adopt is that of @cite-Art69, instead of the more modern proof adopted by Stacks Project based on Popescu's theorem. This is to make the proof more self-contained. The proof is very lengthy and technical, so we divided this appendix into three sections.

== Preliminary reductions

#notation[
  For a noetherian henselian local ring $(A, frak(m))$, we say *Artin approximation holds* for $A$ if, for every system of polynomial equations $f_1, dots.c, f_m in A[Y_1, dots.c, Y_n]$, there exist formal solutions $hat(a)_1, dots.c, hat(a)_n in hat(A)$, i.e: 
  $
    f_1 (hat(a)_1, dots.c, hat(a)_n) = dots.c = f_m (hat(a)_1, dots.c, hat(a)_n) = 0
  $
  Then for each $N >= 1$, there exist actual solutions $a_1, dots.c, a_n in A$ s.t: 
  $
    f_1 (a_1, dots.c, a_n) = dots.c = f_m (a_1, dots.c, a_n) = 0
  $
  and each $hat(a)_i equiv a_i (mod frak(m)^N)$. 
]

#notation[
  For a local ring $(A, frak(m))$, we denote: 
  $
    A{T_1, dots.c, T_n} = A[T_1, dots.c, T_n]_((frak(m),T_1,dots.c,T_n))^#[h]
  $
]

#proposition(name: <artin-approx-and-finitely-presented-functors>)[
  Fix a noetherian local ring $(A, frak(m))$. TFAE: 

  + Artin approximation holds for $A$; 

  + For any functor $F: AAlg(A) -> cSet$ commuting with direct limits, any $N >= 1$ and any element $hat(xi) in F(hat(A))$, there exists an element $xi in F(A)$ s.t. $hat(xi)$ and $xi$ share the same image in $F(A\/frak(m)^N)$. 
]
#proof[
  ($==>$) Write $hat(A) = dirlim_lambda A_lambda$ as the directed limit of its finite type $A$-subalgebras. Then: 
  $
    F(hat(A)) = dirlim_lambda F(A_lambda)
  $
  Let $hat(xi) in F(hat(A))$ be represented by $xi_lambda in F(A_lambda)$. 

  Let $A_lambda$ have a presentation $A[Y_1,dots.c,Y_m]\/(f_1,dots.c,f_r)$. Then the inclusion $A_lambda -> hat(A)$ is a formal solution $hat(a) in hat(A)^m$ to $arrow(f)(arrow(Y)) = 0$. There is thus a solution $a in A^m$ agreeing with $hat(a)$ modulo $frak(m)^N$. In other words, we have a section: 
  $
    phi: A_lambda -> A
  $
  of the structure map that agrees with $A_lambda -> hat(A)$ upon reducing modulo $frak(m)^N$. 

  Put $xi = F(phi) xi_lambda in F(A)$. Then $hat(xi)$ and $xi$ agree upon reducing modulo $frak(m)^N$. 

  ($<==$) 
  #notation[
    For a system $f_1, dots.c, f_r in A[Y_1,dots.c,Y_m]$ of polynomial equations, define the solution functor:
    $
      F_(arrow(f)): AAlg(A) &-> cSet \
      B &|-> {arrow(b) in B^m : arrow(f)(arrow(b)) = 0}
    $
  ]
  It can be directly checked that $F_(arrow(f))$ commutes with directed limits. Thus formal solutions to $arrow(f)$ may be approximated.  
]

#proposition(name: <artin-approx-reduce-to-std>)[
  TFAE: 

  + Artin approximation holds for the henselization of any finite type algebra $A$ over a field or an excellent DVR $R$ at a prime; 

  + For any excellent DVR $R$, let $A = R{X_1, dots.c, X_n}$. For any $N >= 1$, if a system of polynomial equations $f_1, dots.c, f_r in R[Y_1, dots.c, Y_m]$ has a formal solution $hat(a)_1, dots.c, hat(a)_m in hat(A)$, where $hat(A) = hat(R) fps(X_1\, dots.c\, X_n)$: 
    $
      f_1 (hat(a)_1, dots.c, hat(a)_m) = dots.c = f_r (hat(a)_1, dots.c, hat(a)_m) = 0
    $
    then there exists a solution $a_1, dots.c, a_m in A$ agreeing with $hat(a)_1, dots.c, hat(a)_m in hat(A)$ modulo $frak(m)_A^N$: 
    $
      f_1 (a_1, dots.c, a_m) = dots.c = f_r (a_1, dots.c, a_m) = 0
    $

    That is, Artin approximation holds for the ring $R{X_1, dots.c, X_n}$ for polynomial systems in $R[X_1,dots.c,X_n,Y_1,dots.c,Y_m]$ (i.e. over $R[X_1,dots.c,X_n]$). 
]
#proof[
  (1)$==>$(2) is formal, so we only prove (2)$==>$(1). 

  If $R$ is a DVR and $frak(m)_A in Spec(A)$ lies above the generic point of $Spec(R)$, we may replace $R$ by $Frac(R)$. Now if $R$ is a field, we replace $R$ by $R fps(T)$ and let $T$ act by zero on $A$. By these reductions, we may assume that $R$ is a DVR and $A$ lies above the closed point $(pi.alt)$ of $R$. 

  Next, we claim that we may assume that $k(A)\/k(R)$ is a finite field extension. Indeed: 
  
  - Assuming this case, we consider the general case. $k(A)\/k(R)$ is a finitely generated field extension, so we may pick $z_1, dots.c, z_d in A$ whose residues in $k(A)$ form a transcendence basis of $k(A)\/k(R)$. They induce a local map: 
    $
      R[T_1,dots.c,T_d]_((pi.alt)) -> A, T_i |-> z_i
    $
    (This map is well-defined. Indeed, for any polynomial $f(T_1,dots.c,T_d) in R[T_1,dots.c,T_d]$ not divisible by $pi.alt$, $[f(z_1, dots.c, z_d)] in k(A)$ is a nonzero polynomial in $[z_1], dot.c, [z_d]$. By algebraic independence, $[f(z_1, dots.c, z_d)] in k(A)^times$.)

    Thus $A$ is a henselian local ring above $R' = R[T_1,dots.c,T_d]_((pi.alt))$. Since $A$ is a henselization of a finite type $R$-algebra at a prime, it is a henselization of a finite type $R'$-algebra at a prime. $R'$ is an excellent DVR, so we may replace $R$ with $R'$. Now the residue field extension is $k(A)$ over $k(R') = k(R)(z_1, dots.c, z_d)$, which is finite. 

  Now choose a finite type $R$-algebra $C_0$ and $frak(m)_0 in Spec(C_0)$ s.t. $A = C_(0,frak(m)_0)^#[h]$. $frak(m)_0$ necessarily lies above $(pi.alt) in Spec(R)$. Since the residue field $k(A) = k(C_0)$ is finite over $k(R)$, by Hilbert's nullstellensatz, $frak(m)_0$ is a closed point of $Spec(C_0\/pi.alt C_0)$, hence a maximal ideal of $C_0$. 

  Pick a set of generators $C_0 = R[z_1, dots.c, z_n]$. Now $[z_i] in k(C_0)$ admits a monic polynomial relation over $k(R)$. Lift this relation arbitrarily to $P_i [T] in R[T]$, so that $x_i = P_i (z_i) in frak(m)_0$. Define a map: 
  $
    R[X_1,dots.c,X_n] -> C_0, X_i |-> x_i
  $
  Now every generator $z_i in C_0$ has $P_i (z_i) = x_i$, so $C_0$ is integral hence finite over $R[X_1,dots.c,X_n]$. Furthermore, the pullback of $frak(m)_0$ contains the maximal ideal $(pi.alt, X_1, dots.c, X_n)$ since $pi.alt in frak(m)_0$ and $x_i in frak(m)_0$. Thus, $frak(m)_0$ lies above $(pi.alt, X_1, dots.c, X_n)$, giving a finite map: 
  $
    R[X_1,dots.c,X_n]_((pi.alt, X_1, dots.c, X_n)) -> C_(0,frak(m)_0)
  $
  By @henselization-and-finite-base-change, $A = C_(0,frak(m)_0)^#[h]$ is a factor of $C_0 otimes_(R[X_1,dots.c,X_n]) R{X_1,dots.c,X_n}$. It is thus finite local over $R{X_1,dots.c,X_n}$. 

  #notation[
    Throughout the rest of the appendix, we denote by: 
    $
      A_n := R{X_1, dots.c, X_n}
    $
    for $R$ an excellent DVR clear from the context. Denote $frak(m)_n = (pi.alt, X_1, dots.c, X_n) A_n$ the maximal ideal of $A_n$. 
  ]

  Now $A\/frak(m)_n A$ is a finite local algebra over the field $k(R)$. It is thus a local artinian ring. This shows that $sqrt(frak(m)_n A) = frak(m)_A$, and so the $frak(m)_n A$-adic and $frak(m)_A$-adic topologies on $A$ are equivalent. In other words, 
  $
    hat(A) cong A otimes_(A_n) hat(A_n)
  $
  Now for every polynomial system $f_1, dots.c, f_r in A[Y_1,dots.c,Y_m]$, define the functor: 
  $
    G: AAlg(A_n) -> cSet, B |-> F_(arrow(f)) (A otimes_(A_n) B)
  $
  This functor commutes with directed limits, since $F_(arrow(f))$ and tensor products do. If we assume Artin approximation for $A_n$, then points in $G(hat(A_n))$ may be approximated by points in $G(A_n)$. That is, points of $F_(arrow(f)) (hat(A))$ may be approximated by points of $F_(arrow(f)) (A)$. That is, formal solutions of $arrow(f)$ may be approximated. 

  In summary, it suffices to prove Artin approximation for the ring $A_n$. We already assumed Artin approximation on $A_n$ for those systems over $R[X_1,dots.c,X_n]$, so it suffices to reduce to such systems. 

  Let $f_1,dots.c,f_r in A_n [Y_1,dots.c,Y_m]$ be a system over $A_n$ with solution $hat(y) in hat(A_n)$. Enlarge the system so that $(f_1,dots.c,f_r)$ generates: 
  $
    frak(p) = ker(A_n [arrow(Y)], Y_i |-> hat(y)_i) in Spec(A_n [arrow(Y)])
  $
  Put $B_n = R[X_1,dots.c,X_n]_((pi.alt,X_1,dots.c,X_n))$ so that $A_n = B_n^#[h]$. Put $frak(p)_0 = frak(p) inter B_n [arrow(Y)] in Spec(B_n [arrow(Y)])$. Now: 

  - $A_n [arrow(Y)]\/frak(p)_0 A_n [arrow(Y)]$ is a filtered limit of etale $B_n [arrow(Y)]\/frak(p)_0$-algebras, each reduced by @etale-local-properties (4). Thus $A_n [arrow(Y)]\/frak(p)_0 A_n [arrow(Y)]$ is reduced. 

    That is, $frak(p)_0 A_n [arrow(Y)]$ is a radical ideal of $A_n [arrow(Y)]$. 

  - $frak(p)$ is one of the minimal prime ideals of $A_n [arrow(Y)]$ above $frak(p)_0 A_n [arrow(Y)]$. Indeed, the map $Spec(A_n [arrow(Y)]) -> Spec(B_n [arrow(Y)])$ is a projective limit of affine etale maps. Thus its fiber over $frak(p)_0$ is a discrete set, so no prime above $frak(p)_0$ can strictly specialize $frak(p)$. 

  Let $frak(q)_1 = frak(p), dots.c, frak(q)_e in Spec(A_n [arrow(Y)])$ be the minimal primes above $frak(p)_0 A_n [arrow(Y)]$. Then, by radicality: 
  $
    frak(p)_0 A_n [arrow(Y)] = frak(p) inter frak(q)_2 inter dots.c inter frak(q)_e
  $
  Pick $g_i in frak(q)_i - frak(p)$ for $2<=i<=e$. Put $g = product_(i=2)^e g_i in frak(q)_2 dots.c frak(q)_e - frak(p)$. Then: 

  - $g(hat(y)) != 0$ since $g in.not frak(p)$; 

  - $g frak(p) subset frak(p) frak(q)_2 dots.c frak(q)_e subset frak(p)_0 A_n [arrow(Y)]$. 

  Choose generators of $frak(p)_0 subset B_n [arrow(Y)]$ and clear their denominators, which are elements of $R[arrow(X)] - (pi.alt, arrow(X))$. Thus we have polynomials $phi_1, dots.c, phi_t in R[arrow(X), arrow(Y)]$ s.t. $frak(p)_0 = (phi_1, dots.c, phi_t)$. Then: 

  - $arrow(phi)(hat(y)) = 0$, so by approximation for systems in $R[arrow(X), arrow(Y)]$, we may pick an approximation $y in A_n^m$ modulo $frak(m)_n^N$ for a sufficiently large $N$. 

  - Whenever $N > "ord"_(frak(m)_n) (g(hat(y)))$, $0 != g(hat(y)) mod frak(m)_n^N = g(y) mod frak(m)_n^N$, and so $g(y) != 0$. 

  Now for every original equation $f_i$, we have $g f_i in frak(p)_0 A_n [arrow(Y)]$, so $g(y) f_i (y) = 0$. But $g(y) != 0$, so $f_i (y) = 0$. Thus we have obtained an approximating solution $y in A_n^m$ of $hat(y)$. 
]
