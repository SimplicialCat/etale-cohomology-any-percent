#import "void-import.typ": *

== Higher vanishing of $R^q f_*$ and $H^q$

In this section, we apply proper base change to prove higher vanishing of cohomology, with both relative statements (i.e. statements on $R^q f_*$) and absolute statements (i.e. statements on $H^q$), under mild assumptions. 

We will justify our remarks in @remark-on-vanishing, that $H^q (X, cal(F))$ for a torsion sheaf $cal(F)$ vanishes for $q > 2dim(X)$ whenever $X$ is of finite type over an algebraically closed field $k$, and for $q > dim(X)$ under the additional assumption that $X$ is affine. This is important for both a formal reason and a rigorous motivational reason: 

- Establishing this will pave our way for transitioning statements on the abelian categories $cAb(X_et)$ to its derived category $D^bullet (X_et)$, by showing that certain triangulated functors like $R f_*$ and $R Gamma$ are bounded both above and below, allowing for their definition on the bounded above derived category $D^- (X_et)$, and unbounded derived categories $D(X_et)$, allowing statements like the projection formula and Kunneth formula to be stated. 

- Once we have established vanishing of $H^q (X, -)$ for $q > 2d$ for $d = dim(X)$, we see that $H^(2d) (X, -): cAb(X_et, ZZ\/n) -> cAb$ is now right exact. 

  We will eventually state and prove Poincare duality, which, for now, you can understand as a duality between $H^q (X, cal(F))$ and $H^(2d-q) (X, caron(cal(F)))$ (modulo Tate twist) whenever $X$ is proper smooth over an algebraically closed field $k$ and $cal(F)$ satisfies certain conditions. Now that we believe a posteriori $H^(2d)$ is dual to $H^0$, it has to be right exact. 
  
  Not only does this give us a reason to believe that Poincare duality is at least reasonable, but it reveals the following point of view: that Poincare duality could even possibly hold is entirely dependent on the vanishing of etale cohomology beyond twice the dimension. If we do not establish this vanishing right now, it would be unreasonable for us to be able to proceed to Poincare duality. 

There is also a historical reason for Artin vanishing, for it to hold a natural place in the theory of etale cohomology: 

- We have been making analogies between singular cohomology and etale cohomology. In 1959, @cite-andreotti-frankel showed that a smooth affine complex variety has the homotopy type of a CW complex of its complex dimension. In particular, its singular cohomology vanishes beyond that dimension, as opposed to the _real_ dimension suggested by higher vanishing of singular cohomology of a manifold.

  In 1963-1964, during the legendary seminar of Grothendieck that gave birth to etale cohomology, whose lecture notes were later known as @cite-SGA4, Artin vanishing for etale cohomology was stated and proved. As such, from a historical point of view, Artin vanishing for etale cohomology was formalized and established naturally, as an analog of this singular-cohomology vanishing.

// As in most results in etale cohomology, Artin vanishing is proved by induction on dimension. In our case, all that's needed to bootstrap the induction is one seemingly innocent invocation of proper base change, and some vanishing results in dimension 1. 

#lemma(name: <relative-grothendieck-vanishing-in-dim-1>)[
  Let $f: X -> Y$ be a proper morphism whose fibers have dimension $<=1$. Then for all torsion $cal(F) in cAb(X_et)$ and all $q>2$, $R^q f_* cal(F) = 0$. 
]
#proof[
  For every geometric point $ol(y) = Spec(k(y)^sep)$ of $Y$, 
  $
    (R^q f_* cal(F))_(ol(y)) cong H^q (X_(ol(y)), cal(F)|_(X_(ol(y))))
  $
  by proper base change, since $f$ is proper. $cal(F)|_(X_(ol(y))) in cAb((X_(ol(y)))_et)$ is torsion by @pullback-of-torsion-sheaf, and $X_(ol(y))$ is proper of dimension 1 over the separably closed field $k(y)^sep$. Thus by @grothendieck-vanishing-in-dim-1, $H^q (X_(ol(y)), cal(F)|_(X_(ol(y)))) = 0$ for $q >= 3$. Thus $R^q f_* cal(F)$ has all stalks being zero, and so: 
  $
    R^q f_* cal(F) = 0, forall q>=3
  $
]

#notation(name: <etale-cohomological-dimension>)[
  Let $X$ be a scheme. We denote by: 
  $
    cd(X) := min({d >= 0 : forall cal(F) in cAb(X_et) #[torsion], forall q > d, H^q (X, cal(F)) = 0}) in NN union {oo}
  $
  to be its *etale cohomological dimension*. For a ring $A$, we use $cd(A)$ to denote $cd(Spec(A))$. 
]

#lemma(name: <cohom-dim-of-rings-props>)[
  + Let $K$ be a field and $A$ be a 1-dimensional finite type $K$-algebra. Then: #h(1fr)
    $
      cd(A) <= cd(K) + 1
    $
  
  + Let $A = dircolim_i A_i$ be a filtered colimit of rings. Then: 
    $
      cd(A) <= sup_i cd(A_i)
    $

  + Let $L\/K$ be a field extension of transcendence degree $d$. Then: 
    $
      cd(L) <= cd(K) + d
    $
]
#proof[
  When proving these results, we will use $cal(F) = dirlim_(n>=1) cal(F)[n!]$ for a torsion sheaf $cal(F)$ by definition, and limit formula @limit-formula-for-sheaves, to reduce to the case of $cal(F)$ being $n$-torsion for a fixed $n$. In this case, any sheaf obtained by applying an additive functor to $cal(F)$ is still $n$-torsion, so we can avoid justifying why the sheaves involved are torsion. We will be using this trick implicitly throughout this proof and will not state it at a use site. 

  (1) Let $X = Spec(A)$ and $ol(X) = X otimes_K K^sep$. Let $f: X -> Spec(K)$ be the structure map, and $ol(k): Spec(K^sep) -> Spec(K)$ be a geometric point. Then for $cal(F) in cAb(X_et, ZZ\/n)$, by @stalks-of-derived-lowerstar, since $tilde(Spec(K))_(ol(k)) = Spec(K^sep)$:  
  $
    (R^q f_* cal(F))_(ol(k)) = H^q (X otimes_K K^sep, cal(F)|_(X otimes_K K^sep)) = H^q (ol(X), cal(F)|_(ol(X)))
  $
  Since $ol(X)$ is an affine scheme finite type over $K^sep$ of dimension 1, by @artin-vanishing-in-dim-1, $cd(ol(X)) <= 1$. Thus, $H^q (ol(X), cal(F)|_(ol(X))) = 0$ for $q >= 2$, and so $R^q f_* cal(F) = 0$ for $q >= 2$. Now consider the Leray spectral sequence @derived-lower-star-first-props (2): 
  $
    E_2^(p,q) = H^p (Spec(K), R^q f_* cal(F)) => H^(p+q) (X, cal(F))
  $
  By definition of cohomological dimension and our arguments above, the $E_2$-page is supported on $p <= cd(K), q <= 1$. Thus, $H^n (X, cal(F))$ is supported on $n <= cd(K) + 1$, i.e: 
  $
    cd(A) = cd(X) <= cd(K) + 1
  $

  (2) By @artin-mazur-construction, the Artin-Mazur construction, we may assume that $A = dirlim_i A_i$ is a direct limit. Take $X = Spec(A), X_i = Spec(A_i)$ and so:
  $
    X = invlim_i X_i
  $
  is a projective limit of affine schemes. Denote the projections by $v_i: X -> X_i$. For $cal(F) in cAb(X_et, ZZ\/n)$, by the limit formula @limit-formula-adjunction, 
  $
    H^q (X, cal(F)) = dirlim_i H^q (X_i, v_(i,*) cal(F)) = 0
  $
  whenever $q > sup_i cd(A_i)$, since each $H^q (X_i, v_(i,*) cal(F)) = 0$ individually. Thus: 
  $
    cd(A) = cd(X) <= sup_i cd(A_i)
  $

  (3) We may pick a chain of field extensions $L = L_d\/L_(d-1)\/dots.c\/L_0 = K$ in which each step is of transcendence degree 1. If we are done with the degree 1 case, we may apply it inductively to obtain the general case. Thus, we may assume $d = 1$ and $L\/K$ is of transcendence degree 1. Now: 
  $
    L = dirlim_lambda A_lambda
  $
  is the direct limit of its finite type $K$-subalgebras ${A_lambda}$. Since $L\/K$ is of transcendence degree $1$, each $Frac(A_lambda)\/K$ is of transcendence degree $<=1$, and so $dim(A_lambda) <= 1$. Thus by (1), each $cd(A_lambda) <= cd(K) + 1$. By (2), 
  $
    cd(L) <= sup_i cd(A_lambda) <= cd(K) + 1
  $
  and we are done. 
]

The technical engine of Artin vanishing is the following proposition: 

#proposition(name: <artin-vanishing-engine>)[
  Let $K$ be a field, and $X$ be a finite type scheme over $K$ of dimension $d$. Let $x in X$ with $a = dim(ol({x}))$. Then there exists a finite type scheme $Y$ of dimension $<=d-a$ over $K(t_1, dots.c, t_a)^sep$ and over $X$, and a closed point $y in Y$ lying above $x in X$, s.t. there is a $K$-algebra isomorphism: 
  $
    cal(O)_(X,x)^#[sh] cong cal(O)_(Y,y)^#[sh]
  $
  Furthermore, if $X$ is regular around $x$, we may take $Y$ to be regular. 
]
#proof[
  Since this problem is local in $X$, we may assume that $X = Spec(A)$ is affine. Since the transcendence degree $trd_K (k(x)) = a$, we may pick $c_1, dots.c, c_a in A$ whose image in $k(x)$ are algebraically independent, defining a morphism: 
  $
    f: X -> AA^a_K
  $
  sending $x$ to the generic point $eta in AA^a_K$. Now consider the generic fiber $f_eta: X_eta -> eta = Spec(K(t_1, dots.c, t_a))$, which is of finite type. For any $z in X_eta subset X$, 
  $
    trd_(K(t_1, dots.c, t_a)) (k(z)) = trd_K (k(z)) - a
  $
  and so $X_eta$ has dimension $d-a$. Furthermore, $trd_(K(t_1, dots.c, t_a)) (k(x)) = trd_K (k(x)) - a = a - a = 0$, so $x in X_eta$ is a closed point. Finally, 
  $
    cal(O)_(X_eta,x) = cal(O)_(X,x)\/frak(m)_(AA^a_K,eta) cal(O)_(X,x) = cal(O)_(X,x)
  $
  Next, consider the geometric point $ol(eta): Spec(K(t_1,dots.c,t_a)^sep) -> eta -> X$, corresponding to a fixed separable closure of $K(t_1, dots.c, t_a)$. Take $Y = X_(ol(eta))$, and $y in Y$ any point above $x in X_eta$. Since $Y = X_eta times_eta ol(eta)$, we see that $dim(Y) = d - a$ and $y$ is a closed point. Now: 

  #lemma[
    Let $K$ be a field and $X$ be a scheme over $K$. Fix a separable closure $K -> K^sep$. Let $x in X$, and take $ol(x) in ol(X) = X otimes_K K^sep$ be a point above $x in X$. Then there exists an isomorphism of $K$-algebras: 
    $
      cal(O)_(X,x)^#[sh] cong cal(O)_(ol(X),ol(x))^#[sh]
    $
  ]
  #proof[
    For every finite separable extension $L\/K$, take $X_L = X otimes_K L$, and $x_L in X_L$ be the image of $ol(x)$. This gives a compatible system of points ${x_L in X_L}$. Since $ol(X) = invlim_(L\/K #[finite separable]) X_L$, we have: 
    $
      cal(O)_(ol(X),ol(x)) = dirlim_(L\/K #[finite separable]) cal(O)_(X_L,x_L)
    $
    Since strict henselization commute with direct limits, 
    $
      cal(O)_(ol(X),ol(x))^#[sh] = dirlim_(L\/K #[finite separable]) cal(O)_(X_L,x_L)^#[sh]
    $
    However, each $X_L$ is etale over $X$, so there is a natural isomorphism $cal(O)_(X_L,x_L)^#[sh] cong cal(O)_(X,x)^#[sh]$. Thus, we have obtained an isomorphism: 
    $
      cal(O)_(ol(X),ol(x))^#[sh] cong cal(O)_(X,x)^#[sh]
    $
  ]
  By this lemma, 
  $
    cal(O)_(Y,y)^#[sh] cong cal(O)_(X_eta,x)^#[sh] cong cal(O)_(X,x)^#[sh]
  $
  as $K$-algebras. 
  
  Finally, for the regular part, by @permanence-of-properties-under-henselization (1), a noetherian local ring $A$ is regular if and only if $A^#[sh]$ is. Thus if $X$ is regular near $x$, $cal(O)_(X,x)$ is regular, and so is $cal(O)_(Y,y)^#[sh] cong cal(O)_(X,x)^#[sh]$. Thus $cal(O)_(Y,y)$ is regular. Since the regular locus of a finite type scheme over a field is open (say, by #cite-stacks("07R5")[Lemma 29.19.3]), $Y$ is regular near $y$. By shrinking $Y$ suitably, we may take $Y$ to be regular. 
]

We are now ready to start the induction required to prove Artin vanishing. We will use the notation "supported on dimension $<=a$" from @notation-supp-on-dim-a. 

#theorem(name: <artin-vanishing>)[
  (Artin vanishing) Let $K$ be a field, and $X$ be an affine scheme of finite type over $K$ of dimension $d$. Then: 
  $
    cd(X) <= cd(K) + d
  $
]
#proof[
  The case $d = 0$ is dealt with in @cohom-dim-of-rings-props (3) applied to a finite extension, and the case $d = 1$ is dealt with in @cohom-dim-of-rings-props (1). We thus assume that $d >= 2$, and Artin vanishing already holds in dimensions $<= d - 1$. 

  #lemma[
    Suppose that Artin vanishing holds in dimensions $<= d - 1$. 

    Let $K$ be a field, and $j: U -> X$ be an open immersion of regular varieties over $K$ of dimension $d$, whose complement $D = X - U$ is the support of an effective Cartier divisor on $X$. Then for any torsion sheaf $cal(F) in cAb(U_et)$, $R^q j_* cal(F)$ is supported on dimension $<= d - q$. 
  ]
  #proof[
    When $q = 0$, this result is automatic. We may thus assume $q >= 1$, and since $j$ is an isomorphism on $U$, $R^q j_* cal(F)|_U = 0$. Thus, it suffices to show that for $x in D$ s.t. $dim(ol({x})) = a > d - q$, we have $(R^q j_* cal(F))_(ol(x)) = 0$. 

    By @pbc-etale-bc, this problem is local in $X$. Since $D$ is the support of an effective Cartier divisor, we may assume that $j$ is the open immersion $Spec(A[f^(-1)]) = U -> X = Spec(A)$ for a regular integral domain $A$ and for some $0 != f in A$. Now by @stalks-of-derived-lowerstar: 
    $
    (R^q j_* cal(F))_(ol(x)) &= H^q (Spec(cal(O)_(X,x)^#[sh] otimes_A A[f^(-1)]), cal(F)|_(Spec(cal(O)_(X,x)^#[sh] otimes_A A[f^(-1)]))) \
    &= H^q (Spec(cal(O)_(X,x)^#[sh] [f^(-1)]), cal(F)|_(Spec(cal(O)_(X,x)^#[sh] [f^(-1)])))
    $
    By @artin-vanishing-engine, there exists a finite type regular scheme $Y$ over $K(t_1, dots.c, t_a)^sep$ of dimension $<=d-a$ that is also an $X$-scheme, and a closed point $y in Y$ lying above $x in X$ s.t. $cal(O)_(Y,y)^#[sh] cong cal(O)_(X,x)^#[sh]$ as $K$-algebras. 

    #lemma[
      Let $k$ be a separably closed field, $Y = Spec(A)$ be a finite type affine regular scheme over $k$ of dimension $d$, and $y in Y$ be a point. 
      
      Then for $f in frak(p)_y$, $cal(O)_(Y,y)^#[sh] [f^(-1)]$ is a directed limit of finite type $k(s)$-algebras of dimension $<=d-1$. 
    ]
    #proof[
      By taking a connected component of $Y$, we may assume that $Y$ is integral. Since the problem is local in $y$, by shrinking $Y$, we may assume that $Y = Spec(A), f in frak(p)_y subset A$ where $frak(p)_y$ is the prime ideal of $A$ corresponding to $y in Spec(A)$. 
      
      Consider: 
      $
        cal(O)_(Y,y)^#[sh] = dircolim_((U,ol(u)) -> (Y,ol(y)) #[etale] \ U #[affine]) cal(O)_(U,u)
      $
      We have: 
      $
        cal(O)_(Y,y)^#[sh] [f^(-1)] = dircolim_((U,ol(u)) -> (Y,ol(y)) #[etale] \ U=Spec(B) #[affine]) cal(O)_(U,u) [f^(-1)]
      $
      For each affine etale neighborhood $Spec(B) = U -> Y$, since $Y$ is regular, $U$ is regular by @etale-local-properties (1). By taking $U$ to be connected, we may assume that $U$ is integral. We will soon compare transcendence degree of fraction fields. Now for each such $U$, there is a natural morphism: 
      $
        k[s] -> cal(O)_(U,u), s |-> f in frak(m)_u
      $
      This morphism sends every polynomial $h(s) in k[s]$ with $h(0) in k^times$ to $h(f) in h(0) + f cal(O)_(U,u) subset h(0) + frak(m)_u subset cal(O)_(U,u)^times$, a unit in $cal(O)_(U,u)$. Upon inverting $f$ in $cal(O)_(U,u)$, every nonzero $h(s) in k[s]$ will thus have $h(f) in cal(O)_(U,u) [f^(-1)]^times$. Thus, this natural morphism induces a morphism: 
      $
        k(s) -> cal(O)_(U,u) [f^(-1)]
      $
      equipping each $cal(O)_(U,u) [f^(-1)]$ with the structure of a $k(s)$-algebra compatibly. Now: 
      $
        Frac(cal(O)_(Y,y)^#[sh] [f^(-1)]) = union.big_((U,ol(u)) -> (Y,ol(y)) #[etale] \ U=Spec(B) #[affine integral]) Frac(cal(O)_(U,u) [f^(-1)]) = union.big_((U,ol(u)) -> (Y,ol(y)) #[etale] \ U=Spec(B) #[affine integral]) Frac(B)
      $
      as field extensions of $k(s)$. For any integral $U$ in the limit, since $U$ is quasi-finite over $Y$, $dim(U) <= d$. Thus, 
      $
        trd_(k(s)) (Frac(B)) + 1 = trd_k (Frac(B)) <= d
      $
      and so $trd_(k(s)) (Frac(B)) <= d - 1$. Thus, 
      $
        trd_(k(s)) (Frac(cal(O)_(Y,y)^#[sh] [f^(-1)])) <= d - 1
      $
      Now $cal(O)_(Y,y)^#[sh] [f^(-1)]$ is the directed limit of its finite type $k(s)$-subalgebras ${A_lambda}$. For each such $A_lambda$, $Frac(A_lambda) subset Frac(cal(O)_(Y,y)^#[sh] [f^(-1)])$ has transcendence degree $<= d - 1$ over $k(s)$, and so $dim(A_lambda) <= d - 1$. We are thereby done. 
    ]
    We now apply the lemma just proved to the vanishing of $R^q j_* cal(F)$. Recall: 
    $
      (R^q j_* cal(F))_(ol(x)) &= H^q (Spec(cal(O)_(X,x)^#[sh] [f^(-1)]), cal(F)|_(Spec(cal(O)_(X,x)^#[sh] [f^(-1)]))) \
      &cong H^q (Spec(cal(O)_(Y,y)^#[sh] [f^(-1)]), cal(G))
    $
    for some torsion sheaf $cal(G)$, where $f$ may be regarded as an element of $frak(p)_y$ since $y$ lies above $x$. We may thus apply the lemma to write: 
    $
      cal(O)_(Y,y)^#[sh] [f^(-1)] = dirlim_lambda A_lambda
    $
    as a direct limit of finite type $k(t_1, dots.c, t_a)^sep (s)$-algebras of dimension $<= d - a - 1$. Since Artin vanishing holds in dimension $<= d - 1$, 
    $
      cd(A_lambda) <= d - a - 1 + cd(k(t_1, dots.c, t_a)^sep (s)) <= d - a
    $
    where the last inequality is due to @cohom-dim-of-rings-props (3). By @cohom-dim-of-rings-props (2), 
    $
      cd(cal(O)_(Y,y)^#[sh] [f^(-1)]) <= sup_lambda cd(A_lambda) <= d - a
    $
    Thus, whenever $q > d - a$ (i.e. $a = dim(ol({x})) > d - q$), $(R^q j_* cal(F))_(ol(x)) = 0$. 
  ]
  We are now ready to prove Artin vanishing. Let $X$ be an affine scheme of finite type over $K$ of dimension $d$. By Noether normalization, there exists a finite morphism: 
  $
    pi: X -> AA^d_K
  $
  Since $H^q (X, cal(F)) = H^q (X, pi_* cal(F))$ by @pushforward-by-finite-morphism, it suffices to prove $cd(AA^d_K) <= cd(K) + d$. We may thus assume $X = AA^d_K$. 
  
  By limit formula @limit-formula-for-sheaves, it suffices to deal with $cal(F) in cAb((AA^d_K)_et, ZZ\/n)$. Take the projection $f: AA^d_K -> AA^(d-1)_(K)$, factored as: 
  // https://q.uiver.app/#r=typst&q=WzAsMyxbMCwxLCJBQV5kX0siXSxbMiwxLCJBQV4oZC0xKV9LIl0sWzEsMCwiQUFeKGQtMSlfSyB0aW1lc19LIFBQXjFfSyJdLFswLDIsImoiXSxbMiwxLCJvbChmKSJdLFswLDEsImYiLDJdXQ==
  #align(center, diagram({
    node((-1, 0), [$AA^d_K$])
    node((1, 0), [$AA^(d-1)_K$])
    node((0, -1), [$AA^(d-1)_K times_K PP^1_K$])
    edge((-1, 0), (0, -1), [$j$], label-side: left, "->")
    edge((0, -1), (1, 0), [$ol(f)$], label-side: left, "->")
    edge((-1, 0), (1, 0), [$f$], label-side: right, "->")
  }))
  where $ol(f)$ is projection onto the first coordinate. This gives a Leray spectral sequence: 
  $
    E_2^(p,q) = R^p ol(f)_* (R^q j_* cal(F)) => R^(p+q) f_* cal(F)
  $
  $j$ is an open immersion whose complement is an effective Cartier divisor $D = AA^(d-1)_K times_K {oo}$. Thus, for $q >= 1$, $R^q j_* cal(F)$ is supported on $D$. Writing the closed immersion $i: D -> AA^(d-1)_K times_K PP^1_K$, we have: 
  $
    R^p ol(f)_* (R^q j_* cal(F)) = R^p ol(f)_* i_* (i^(-1) R^q j_* cal(F)) = R^p (ol(f) compose i)_* (i^(-1) R^q j_* cal(F)) = 0
  $
  for $p >= 1$, since $ol(f) compose i: D -> AA^(d-1)_K$ is an isomorphism. Thus, the $E_2$-page of this spectral sequence is supported on $p = 0$ or $q = 0$. Furthermore, by @relative-grothendieck-vanishing-in-dim-1, since $ol(f)$ is proper with fiber dimension $1$, $R^p ol(f)_* (R^q j_* cal(F)) = 0$ for $p > 2$. In other words, the $E_2$-page of this Leray spectral sequence is supported on $p = 0, q >= 0$ or $(p,q) = (1,0), (2,0)$. 
  
  This gives an isomorphism for $q >= 3$: 
  $
    ol(f)_* (R^q j_* cal(F)) cong R^q f_* cal(F)
  $

  We now claim that for all $q$, $R^q f_* cal(F) in cAb((AA^(d-1)_K)_et, ZZ\/n)$ is supported on dimension $<= d - q$. 

  - For $q <= 1$, this is automatic. 

  - For $q = 2$, it suffices to show that for the generic point $xi in AA^(d-1)_K$, $(R^2 f_* cal(F))_(ol(xi)) = 0$. Indeed, $(tilde(AA^(d-1)_K))_(ol(xi)) = Spec(K(t_1,dots.c,t_(d-1))^sep) = ol(xi)$, and so: 
    $
      (R^2 f_* cal(F))_(ol(xi)) &= H^2 (AA^d_K times_(AA^(d-1)_K) ol(xi), cal(F)|_(AA^d_K times_(AA^(d-1)_K) ol(xi))) \
      &= H^2 (AA^1_(ol(xi)), cal(F)|_(AA^1_(ol(xi)))) = 0
    $
    by @artin-vanishing-in-dim-1. 

  - For $q >= 3$ and $x in AA^(d-1)_K$ with $a := dim(ol({x})) > d - q$, 
    $
      (R^q f_* cal(F))_(ol(x)) &cong (ol(f)_* (R^q j_* cal(F)))_(ol(x)) \
      &cong ol(f)_(ol(x),*) (R^q j_* cal(F)|_(PP^1_(ol(x))))
    $
    for $ol(f)_(ol(x)): PP^1_(ol(x)) -> ol(x)$, a base change of $ol(f)$. Since $j$ is an open immersion of regular varieties of dimension $d$ whose complement is the support of an effective Cartier divisor, by the previous lemma, $R^q j_* cal(F)$ is supported in dimension $<= d - q$. For any point $y in AA^(d-1)_K times_K PP^1_K$ lying above $x$, $dim(ol({y})) >= dim(ol({x})) > d - q$, and so $(R^q j_* cal(F))_(ol(y)) = 0$. Thus, $R^q j_* cal(F)|_(PP^1_x) = 0$, and hence, 
    $
      R^q j_* cal(F)|_(PP^1_(ol(x))) = 0
    $
    Therefore, $(R^q f_* cal(F))_(ol(x)) = 0$. 

  Now that our claim is verified, we consider another Leray spectral sequence: 
  $
    E_2^(p,q) = H^p (AA^(d-1)_K, R^q f_* cal(F)) => H^(p+q) (AA^d_K, cal(F))
  $
  Since $R^q f_* cal(F)$ is supported in dimension $<= d - q$, by @supp-of-torsion-sheaf-dim, $R^q f_* cal(F) = dirlim_lambda cal(G)_lambda$ where each $cal(G)_lambda$ is a torsion sheaf supported on $Z_lambda$, a closed subscheme of $AA^(d-1)_K$ of dimension $<=d- max(1,q)$. Thus, 
  $
    H^p (AA^(d-1)_K, R^q f_* cal(F)) = dirlim_lambda H^p (AA^(d-1)_K, cal(G)_lambda) = dirlim_lambda H^p (Z_lambda, cal(G)_lambda|_(Z_lambda)) = 0
  $
  for $p > cd(K) + d - q$, since each $dim(Z_lambda) <= d - max(1, q)$ and Artin vanishing holds in dimension $<= d - 1$ by inductive hypothesis. In other words, the $E_2$-page of the Leray spectral sequence $E_2^(p,q) = H^p (AA^(d-1)_K, R^q f_* cal(F)) => H^(p+q) (AA^d_K, cal(F))$ vanishes whenever $p + q > cd(K) + d$. Thus, 
  $
    H^m (AA^d_K, cal(F)) = 0, forall m > cd(K) + d
  $
  Thus $cd(AA^d_K) <= cd(K) + d$ and we are done. 
]

Once we are done with Artin vanishing, Grothendieck vanishing is merely a formal consequence. 

#theorem(name: <grothendieck-vanishing>)[
  (Grothendieck vanishing) Let $K$ be a field, and $X$ be any scheme of finite type over $K$ of dimension $d$. Then: 
  $
    cd(X) <= cd(K) + 2d
  $
]
#proof[
  Consider the forgetful functor $epsilon: cAb(X_et) -> cAb(X_#[Zar])$ from etale sheaves to Zariski sheaves. Take $cal(F) in cAb(X_et)$ to be a torsion sheaf. As in the proof of @etale-cohom-of-qcoh-sheaf, there is a spectral sequence: 
  $
    E_2^(p,q) = H^p_#[Zar] (X, R^q epsilon (cal(F))) => H^(p+q)_et (X, cal(F))
  $
  with $R^q epsilon (cal(F))$ being the Zariski sheafification of the presheaf $U |-> H^q_et (U, cal(F)|_U)$. Thus, for any $x in X$, 
  $
    (R^q epsilon (cal(F)))_x = dirlim_(x in U subset X \ U #[affine open]) H^q_et (U, cal(F)|_U) = 0
  $
  for all $q > cd(K) + d$, since each $U$ is an affine scheme of dimension $d$ of finite type over $K$, making Artin vanishing @artin-vanishing applicable. In other words, $R^q epsilon (cal(F)) = 0$ whenever $q > cd(K) + d$. Furthermore, $H^p_#[Zar] (X, R^q epsilon (cal(F))) = 0$ for $p > d$, since Zariski cohomology vanishes above the dimension. 

  Therefore, the spectral sequence above is supported on $0 <= p <= d, 0 <= q <= cd(K) + d$. Hence, 
  $
    H^(m)_et (X, cal(F)) = 0, forall m > cd(K) + 2d
  $
  i.e. $cd(X) <= cd(K) + 2d$. 
]

#corollary[
  For any scheme $X$ with dimension $d$ of finite type over a separably closed field $k$: 
  
  + $cd(X) <= 2d$. That is, for any torsion sheaf $cal(F) in cAb(X_et)$, #h(1fr)
    $
      H^q (X, cal(F)) = 0, forall q > 2d
    $

  + If we additionally assume that $X$ is affine, then $cd(X) <= d$. That is, for any torsion sheaf $cal(F) in cAb(X_et)$, 
    $
      H^q (X, cal(F)) = 0, forall q > d
    $
]
#proof[
  This is just Artin vanishing (@artin-vanishing) and Grothendieck vanishing (@grothendieck-vanishing) applied to the case where the base field is separably closed. 
]

Finally, we prove a relative version of Grothendieck and Artin vanishing. 
#proposition(name: <relative-artin-grothendieck-vanishing>)[
  + (Relative Artin vanishing)
  
    If $f: X -> Y$ is an affine morphism between finite type $K$-schemes and $cal(F) in cAb(X_et)$ is a torsion sheaf supported on dimension $<=m$, then $R^q f_* cal(F)$ is supported on dimension $<=m-q$. 

    In particular, for any torsion sheaf $cal(F) in cAb(X_et)$, $R^q f_* cal(F) = 0$ for $q > dim(X)$; 

  + (Relative Grothendieck vanishing)

    If $f: X -> Y$ is any morphism between finite type $K$-schemes and $cal(F) in cAb(X_et)$ is a torsion sheaf supported on dimension $<=m$, then $R^q f_* cal(F)$ is supported on dimension $<=m - ceil(q\/2)$. 

    In particular, for any torsion sheaf $cal(F) in cAb(X_et)$, $R^q f_* cal(F) = 0$ for $q > 2dim(X)$; 

  + (Fiberwise Grothendieck vanishing)

    If $f: X -> Y$ is any proper morphism between schemes whose fibers have dimension $<=d$, then for any torsion sheaf $cal(F) in cAb(X_et)$, $R^q f_* cal(F) = 0$ for $q > 2d$. 
]
#proof[
  In (1)(2), if $cal(F)$ is supported on dimensions $<=m$, by @supp-of-torsion-sheaf-dim, $cal(F) = dirlim_lambda cal(F)_lambda$ in which every $cal(F)_lambda$ is supported on a closed subscheme of $X$ of dimension $<=m$. By @relative-limit-formula-for-sheaves, $R^q f_* cal(F) = dirlim_lambda R^q f_* cal(F)_lambda$, and stalks commute with direct limits, so it suffices to prove the desired vanishing for each $cal(F)_lambda$. Replacing $cal(F)$ with $cal(F)_lambda$, we may assume that $cal(F)$ is supported on a closed subscheme $Z subset X$ of dimension $<=m$. Now: 
  $
    R^q f_* cal(F) = R^q f_* (i_* i^(-1) cal(F)) = R^q (f compose i)_* (i^(-1) cal(F))
  $
  Thus, replacing $f$ with $f compose i$ and $X$ with $Z$, we may assume that $m = dim(X)$ and drop the conditions on the support of $cal(F)$. 

  Let $y in Y$ with $dim(ol({y})) = a$, and let $dim(Y) = d$. By the proof of @artin-vanishing-engine, there exists an affine morphism $Y -> AA^a_K$ sending $y$ to the generic point $eta in AA^a_K$. Base changing along the geometric point $ol(eta) = Spec(K(t_1, dots.c, t_a)^sep)$, we get a Cartesian diagram: 
  // https://q.uiver.app/#r=typst&q=WzAsNixbMSwxLCJZIl0sWzEsMCwiWSciXSxbMCwxLCJYIl0sWzAsMCwiWCciXSxbMiwxLCJBQV5hX0siXSxbMiwwLCJvbChldGEpIl0sWzMsMSwiZiciXSxbMSwwLCJnIl0sWzEsNV0sWzAsNF0sWzUsNF0sWzIsMCwiZiIsMl0sWzMsMiwiZyciLDJdXQ==
  #align(center, diagram({
    node((0, 0), [$Y$])
    node((0, -1), [$Y'$])
    node((0.3, -0.7), $cart$)
    node((-1, 0), [$X$])
    node((-1, -1), [$X'$])
    node((-0.7, -0.7), $cart$)
    node((1, 0), [$AA^a_K$])
    node((1, -1), [$ol(eta)$])
    edge((-1, -1), (0, -1), [$f'$], label-side: left, "->")
    edge((0, -1), (0, 0), [$g$], label-side: left, "->")
    edge((0, -1), (1, -1), "->")
    edge((0, 0), (1, 0), "->")
    edge((1, -1), (1, 0), "->")
    edge((-1, 0), (0, 0), [$f$], label-side: right, "->")
    edge((-1, -1), (-1, 0), [$g'$], label-side: right, "->")
  }))
  and a closed point $y' in Y'$ s.t. $g(y') = y$, and the local morphism $cal(O)_(Y,y) -> cal(O)_(Y',y')$ induces an isomorphism: 
  $
    cal(O)_(Y,y)^#[sh] cong cal(O)_(Y',y')^#[sh]
  $
  Now: 
  $
    (R^q f_* cal(F))_(ol(y)) &cong H^q (X times_Y Spec(cal(O)_(Y,y)^#[sh]), cal(F)|_(X times_Y Spec(cal(O)_(Y,y)^#[sh]))) \
    &cong H^q (X' times_(Y') Spec(cal(O)_(Y,y)^#[sh]), cal(F)|_(X' times_(Y') Spec(cal(O)_(Y,y)^#[sh]))) \
    &cong H^q (X' times_(Y') Spec(cal(O)_(Y',y')^#[sh]), cal(F)|_(X' times_(Y') Spec(cal(O)_(Y',y')^#[sh]))) \
    &cong (R^q f'_* (cal(F)|_(X')))_(ol(y'))
  $
  Now $f': X' -> Y'$ is a morphism between finite type $K(t_1,dots.c,t_a)^sep$-schemes, that is affine if $f$ is affine. Furthermore, for any $x' in X'$, $x'$ lies over $x in X$, which lies over the generic point $eta in AA^a_K$. Thus, 
  $
    cal(O)_(X_eta,x) = cal(O)_(X,x)
  $
  and so: 
  $
    dim(ol({x})_(X_eta)) &= trd_(K(t_1,dots.c,t_a)) (k_(X_eta) (x)) = trd_(K(t_1,dots.c,t_a)) (k_X (x)) = trd_K (k_X (x)) - a = dim(ol({x})_X) - a \
    &<= m - a
  $
  and so $dim(X_eta) <= m - a$. $X' = X_(ol(eta))$ being a base field extension $X_eta times_eta ol(eta)$ of $X_eta$, thus has dimension $dim(X') <= m - a$. Thus, we may use the isomorphism: 
  $
    (R^q f_* cal(F))_(ol(y)) cong (R^q f'_* (cal(F)|_(X')))_(ol(y'))
  $

  obtained above, together with the fact that $a > m - q$ (or $a > m - ceil(q\/2)$, respectively) implies $0 > m - a - q >= dim(X') - q$ (or $0 > m - a - ceil(q\/2) >= dim(X') - ceil(q\/2)$, respectively). Thus, replacing $f: X -> Y$ with $f': X' -> Y'$ and $y in Y$ with $y' in Y'$, we may assume that $a = 0$, i.e. $y in Y$ is a closed point. Furthermore, $X', Y'$ are finite type over $K(t_1, dots.c, t_a)^sep$, a separably closed field, so we may assume that $K$ is separably closed. 
  
  In other words, in (1)(2), it suffices to prove the final vanishing statements for separably closed $K$, i.e. vanishing for $q > m$ (or $q > 2m$, respectively). Indeed, by @derived-lower-star-first-props (3), 
  $
    R^q f_* cal(F) = (V |-> H^q (X times_Y V, cal(F)))^\#
  $
  For any affine $V in Et_Y$, $V$ is finite type over $Y$, hence over $K$. Thus $X times_Y V$ is finite type over $K$. Since $X times_Y V -> X$ is etale, hence quasi-finite, $dim(X times_Y V) <= dim(X) = m$. Furthermore, since $V$ is affine, if $f$ is affine, then $X times_Y V$ is affine. Thus, 
  $
    H^q (X times_Y V, cal(F)) = 0
  $
  for $q > 2m$, or for $q > m$ when $f$ is affine. Now for every qcqs $V in Et_Y$, every etale cover of $V$ is refined by one consisting of finitely many affine schemes $V_i in Et_V$. Thus $caron(H)^0 (V, -)$ can be computed entirely using those affine $V_i in Et_Y$, so our results above imply: 
  $
    R^q f_* cal(F) (V) = 0
  $
  for $q > 2m$, or for $q > m$ when $f$ is affine, for all qcqs $V in Et_Y$. Since every object of $Et_Y$ is covered by qcqs objects, $R^q f_* cal(F) = 0$ for $q > 2m$, or for $q > m$ when $f$ is affine. 

  (3) For $q > 2d$ and a geometric point $ol(y) = Spec(k(y)^sep)$ above $y in Y$, by proper base change, 
  $
    (R^q f_* cal(F))_(ol(y)) = H^q (X_(ol(y)), cal(F)|_(X_(ol(y))))
  $
  where $cal(F)|_(X_(ol(y)))$ is a torsion sheaf on $X_(ol(y))$, a finite type scheme of dimension $<=d$ over the separably closed field $k(y)^sep$. By absolute Grothendieck vanishing, this vanishes for $q>2d$. Thus for $q>2d$, $R^q f_* cal(F) = 0$. 
]
