#import "void-import.typ": *

Last chapter, we introduced the etale site and etale sheaves, and established fundamental operations on sheaves. 

As discussed earlier, etale cohomology, as defined by right deriving the global section functor on etale sheaves, is the central object to our study. 

In this chapter, we will establish basic results of etale cohomology, and explore first examples. We will introduce: 

- Limit formulas: They are formulas allowing us to compute: #h(1fr)
  $
    H^q (X, dirlim_i cal(F)_i) #[#h(10%) and #h(10%)] H^q (invlim_i X_i, u_(i_0)^(-1) cal(F))
  $
  from cohomology of its parts. Limit formulas are of theoretic importance, in the sense that they allow for _devissage_ on torsion sheaves. One will observe later, that a torsion sheaf is always a filtered colimit of a certain type of sheaves called constructible sheaves, which are in turn reduced to $ul(ZZ\/n)$. This allows us to reduce statements on general torsion sheaves to statements on $ul(ZZ\/n)$. 

- Cohomology of $cal(M)_et$, and first cohomology of $GG_m$ and $ul(M)$: 

  - For $cal(M) in QCoh(X)$, etale cohomology of $cal(M)_et$ is just Zariski cohomology of $cal(M)$: #h(1fr)
    $
      H^q (X_et, cal(M)_et) cong H^q (X_#[top], cal(M))
    $
    This tells us that etale sheaves coming from quasi-coherent sheaves are of little interest to etale cohomology theory, and they yield no new cohomological invariant. 

  - For the multiplicative group $GG_m$: 
    $
      H^1 (X_et, GG_m) cong Pic(X)
    $
    This is crucial in further developments of theory, as it allows for computation of cohomology of $ul(ZZ\/n)$ on curves, when combined with the Kummer and Artin-Schreier sequence. They will, in turn, prove to be critical input to very general results like proper base change. 

  - For a constant sheaf $ul(M)$: 
    $
      H^1 (X_et, ul(M)) cong Hom_#[cont] (pi_1^et (X), M)
    $
    where $M$ is given the discrete topology. This relates the theory of cohomology with that of fundamental groups that we have established and ultimately with finite etale coverings, and will also prove to be useful to further theory like proper base change. 

- Cohomology of curves: 

  We will explicitly compute $H^q_et (X, ul(ZZ\/n))$ for a nonsingular curve $X$ over an algebraically closed field $k$. This is of both theoretic and pedagogical significance. The cohomology of curves will be the motivating example of many future results, such as vanishing theorems and Poincare duality. It will also be a key input to proper base change. 

== Limit formulas <sect-limit-formulas>

We first discuss the limit formula for sheaves on a fixed scheme. 

#theorem(name: <limit-formula-for-sheaves>)[
  (Limit formula for sheaves) For $X$ #furi[quasi-compact quasi-separated][qcqs], and for a filtered colimit of sheaves $cal(F) = dircolim_i cal(F)_i$ in $cAb(X_et)$, we have a natural isomorphism: 
  $
    H^q (U, cal(F)) cong dircolim_i H^q (U, cal(F)_i)
  $
  for every qcqs $U in Et_X$. 
]
#proof[
  We prove this theorem in 4 steps. 

  Step 1. Proof for $H^0$. We claim that: 
  $
    Gamma(X, cal(F)) cong dircolim_i Gamma(X, cal(F)_i)
  $
  #proof[
    Consider the presheaf colimit: 
    $
      cal(P) = dircolim_(i,cPSh) cal(F)_i in cPAb(X_et), U |-> dircolim_i cal(F)_i (U)
    $
    so that $cal(F) = cal(P)^\#$. We thus intend to show that $cal(P)^\# (U) = cal(P)(U)$ for $U in Et_X$ qcqs. 

    We claim that for each $U in Et_X$ quasi-compact, the canonical map $cal(P)(U) -> cal(P)^+ (U)$ is an isomorphism. Indeed, when $U$ is quasi-compact, every etale cover of $U$ can be refined by a cover $cal(U) = {U_i -> U}_(1<=i<=n)$ consisting of finitely many maps in which every $U_i$ is affine. Denote by $cal(S)$ the collection of such etale covers, and so: 
    $
      caron(H)^0 (U, cal(P)) = dirlim_(cal(U)) caron(H)^0 (cal(U), cal(P)) = dirlim_(cal(U) in cal(S)) caron(H)^0 (cal(U), cal(P))
    $
    and we claim that for each $cal(U) in cal(S)$, the morphism $cal(P)(U) -> caron(H)^0 (cal(U), cal(P))$ is an isomorphism. Indeed, from the sheaf conditions for each $cal(F)_i$, we have exact sequences: 
    $
      0 -> cal(F)_i (U) -> product_(1<=j<=n) cal(F)_i (U_j) -> product_(1<=j,k<=n) cal(F)_i (U_j times_U U_k)
    $
    Taking the filtered colimit w.r.t. $I$ and using (Ab5) for $cAb$, we get: 
    $
      0 -> dircolim_i cal(F)_i (U) -> dircolim_i product_(1<=j<=n) cal(F)_i (U_j) -> dircolim_i product_(1<=j,k<=n) cal(F)_i (U_j times_U U_k)
    $
    However, filtered colimits commute with finite limits, so this sequence is just: 
    $
      0 -> dircolim_i cal(F)_i (U) -> product_(1<=j<=n) dircolim_i cal(F)_i (U_j) -> product_(1<=j,k<=n) dircolim_i cal(F)_i (U_j times_U U_k)
    $
    i.e. 
    $
      0 -> cal(P) (U) -> product_(1<=j<=n) cal(P) (U_j) -> product_(1<=j,k<=n) cal(P) (U_j times_U U_k)
    $
    In other words, $cal(P)$ satisfies the sheaf conditions for $cal(U)$, and $caron(H)^0 (cal(U), cal(P)) = cal(P)(U)$. We have thus succeeded in proving that $cal(P)^+ (U) = cal(P) (U)$ for all quasi-compact $U in Et_X$. 

    Next, we prove that $cal(P)^\# (U) = cal(P)^+ (U) = cal(P)(U)$ for qcqs $U in Et_X$. Similarly, the directed system of etale covers of $U$ has a cofinal subsystem $cal(S)$ consisting of etale covers of the form ${U_i -> U}_(1<=i<=n)$ with finitely many maps in which each $U_i$ is affine. Now for each $cal(U) in cal(S)$, we have an exact sequence: 
    $
      0 -> caron(H)^0 (cal(U), cal(P)^+) -> product_(1<=j<=n) cal(P)^+ (U_j) -> product_(1<=j,k<=n) cal(P)^+ (U_j times_U U_k) -> 0
    $
    Since $U$ is quasi-separated, each $U_j times_U U_k$ is quasi-compact. Each $U_j$ is itself quasi-compact, so by our result that $cal(P)^+ (U) = cal(P) (U)$ whenever $U$ is quasi-compact, this sequence is just: 
    $
      0 -> caron(H)^0 (cal(U), cal(P)^+) -> product_(1<=j<=n) cal(P) (U_j) -> product_(1<=j,k<=n) cal(P) (U_j times_U U_k) -> 0
    $
    i.e. $caron(H)^0 (cal(U), cal(P)^+) = caron(H)^0 (cal(U), cal(P)) = cal(P)(U)$. Hence, 
    $
      cal(P)^\# (U) = dircolim_(cal(U) in cal(S)) caron(H)^0 (cal(U), cal(P)^+) = cal(P)(U)
    $
    #suppress-qed
  ]

  Step 2. Proof for Cech cohomology. We claim that for every $p >= 0$, every qcqs $U in Et_X$, 
  $
    caron(H)^p (U, cal(F)) cong dircolim_i caron(H)^p (U, cal(F)_i)
  $

  #proof[
    As usual, the directed system of etale covers of $U$ has a cofinal subsystem $cal(S)$ consisting of etale covers of the form ${U_i -> U}_(1<=i<=n)$ with finitely many maps in which each $U_i$ is affine. For each such $cal(U) = {U_i -> U}_(1<=i<=n) in cal(S)$, $U$ is qcqs and every $U_i$ is affine, each: 
    $
      U_(i_0,dots.c,i_p) = U_(i_0) times_U dots.c times_U U_(i_p)
    $
    is qcqs. In other words, Step 1 is applicable to each $U_(i_0,dots.c,i_p)$. As such, 
    $
      C^p (cal(U), cal(F)) &= product_(1<=i_0,dots.c,i_p<=n) cal(F) (U_(i_0,dots.c,i_p)) \
      &= product_(1<=i_0,dots.c,i_p<=n) dircolim_i cal(F)_i (U_(i_0,dots.c,i_p)) #[by Step 1] \
      &= dircolim_i product_(1<=i_0,dots.c,i_p<=n) cal(F)_i (U_(i_0,dots.c,i_p)) #[since finite limits commute with filtered colimits] \
      &= dircolim_i C^p (cal(U), cal(F)_i)
    $
    In other words, the Cech complex $0 -> C^bullet (cal(U), cal(F))$ is the filtered colimit $0 -> dircolim_i C^bullet (cal(U), cal(F)_i)$ of Cech complexes for each $cal(F)_i$. By (Ab5) for $cAb$, taking cohomology commutes with filtered colimits, so: 
    $
      caron(H)^p (cal(U), cal(F)) = dircolim_i caron(H)^p (cal(U), cal(F)_i)
    $
    Taking a direct limit w.r.t. $cal(U) in cal(S)$ and commute two colimits on RHS, we get: 
    $
      caron(H)^p (U, cal(F)) = dircolim_i caron(H)^p (U, cal(F)_i)
    $
    #suppress-qed
  ]
  Step 3. Proof for injectives. We claim that for a filtered colimit of ${cal(I)_i}$ in which every $cal(I)_i in cAb(X_et)$ is injective, $cal(I) = dircolim_i cal(I)_i$ satisfies: 
  $
    H^q (U, cal(I)) = 0, forall q >= 1
  $
  for every qcqs $U in Et_X$. In other words, although $cal(I)$ is not necessarily injective, it is necessarily acyclic for computing $H^q (U, -)$. 
  #proof[
    We perform induction on $q$. For the base case $q = 1$, we use the canonical isomorphism $H^1 (U, -) cong caron(H)^1 (U, -)$ by @h1-is-cech-h1. Thus, 
    $
      H^1 (U, cal(I)) &= caron(H)^1 (U, cal(I)) \
      &= dircolim_i caron(H)^1 (U, cal(I)_i) #[by Step 2] \
      &= dircolim_i H^1 (U, cal(I)_i) \
      &= 0 #[since each $cal(I)_i$ is injective]
    $
    Suppose that we have proved the claim for all $1 <= q < n$, and we want to prove that $H^n (U, cal(I)) = 0$. For this, we use the Cech-to-derived-functor spectral sequence: 
    $
      E_2^(p,q) = caron(H)^p (U, ul(H)^q (cal(I))) => H^(p+q) (U, cal(I))
    $
    By the inductive hypothesis, for $0 < q < n$ and any qcqs $U in Et_X$, $ul(H)^q (cal(I))(U) = H^q (U, cal(I)) = 0$. As usual, the directed system of etale covers of $U$ has a cofinal subsystem $cal(S)$ consisting of etale covers of the form ${U_i -> U}_(1<=i<=n)$ with finitely many maps in which each $U_i$ is affine. For each such $cal(U) = {U_i -> U}_(1<=i<=n) in cal(S)$, $U$ is qcqs and every $U_i$ is affine, each:
    $
      U_(i_0,dots.c,i_p) = U_(i_0) times_U dots.c times_U U_(i_p)
    $
    is qcqs. Hence for each $cal(U) in cal(S)$, the whole Cech complex $0 -> C^bullet (cal(U), ul(H)^q (cal(I)))$ is zero, and so $caron(H)^p (cal(U), ul(H)^q (cal(I))) = 0$. Taking a direct limit w.r.t. $cal(U) in cal(S)$, 
    $
      caron(H)^p (U, ul(H)^q (cal(I))) = 0, forall 0<q<n
    $
    In other words, the Cech-to-derived-functor spectral sequence has a horizontal vanishing strip. We use the following cohomological lemma: 
    #lemma[
      Let $E_2^(p,q) => H^(p+q)$ be a first quadrant spectral sequence with a horizontal vanishing strip. Then there exists a modified five term exact sequence: 
      $
        0 -> E_2^(n,0) -> H^n -> E_2^(0,n) -> E_2^(n+1,0) -> H^(n+1)
      $
    ]
    By this modified five term exact sequence, we get an exact sequence: 
    $
      0 -> caron(H)^n (U, cal(I)) -> H^n (U, cal(I)) -> caron(H)^0 (U, ul(H)^n (cal(I))) -> dots.c
    $
    However, $caron(H)^n (U, cal(I)) = dircolim_i caron(H)^n (U, cal(I)_i) = 0$ by Step 2, and $caron(H)^0 (U, ul(H)^n (cal(I))) = 0$ by @cech-h0-of-hq-psh-vanish. As such, $H^n (U, cal(I))$, being sandwiched in two zeros in an exact sequence, must be $0$. 
    #suppress-qed
  ]

  Step 4. Proof for general case. Fix a set of geometric points ${ol(x)}_(x in X)$ above each point of $X$. For each $cal(F)_i$, we may then construct the Godement resolution: 
  $
    0 -> cal(F)_i -> cal(I)_i^bullet
  $
  // However, for each $p$, ${cal(I)_i^p}$ generally does not necessarily form a filtered colimit, because the maps induced between them by homological algebra are only unique up to isomorphism, and are 
  Now by functoriality of the Godement resolution, for each $p$, ${cal(I)^p_i}_i$ form a filtered colimit, and by (Ab5) of $cAb(X_et)$, we have an exact sequence: 
  $
    0 -> cal(F) -> dircolim_i cal(I)_i^bullet
  $
  However, for every qcqs $U in Et_X$, by Step 3, each $dircolim_i cal(I)_i^p$ is acyclic w.r.t. ${H^q (U, -)}_(q>=0)$. In other words, we have an acyclic resolution of $cal(F)$ that can be used to compute its cohomology: 
  $
    H^q (U, cal(F)) &= h^q (0 -> (dircolim_i cal(I)_i^bullet)(U)) \
    &= h^q (0 -> dircolim_i cal(I)_i^bullet (U)) #[by Step 1] \
    &= dircolim_i h^q (0 -> cal(I)_i^bullet (U)) #[by (Ab5) of $cAb$] \
    &= dircolim_i H^q (U, cal(F)_i) #[by definition]
  $
  #remark[
    The functoriality of the Godement resolution plays a crucial role here. Without a functorial choice of an injective resolution, we would not necessarily have ${cal(I)^p_i}_i$ forming a filtered colimit, as the morphisms between injective resolutions given by homological algebra are only unique up to chain homotopy and in general do not form a functor $I -> cAb(X_et)$. 
  ]
]

Next, we deal with limit formula for schemes. 

#theorem(name: <limit-formula-for-schemes-0>)[
  (Limit formula for schemes) Let ${Z_i}_(i in I)$ be a projective system of qcqs schemes, with all transition maps affine, with a final object $0 in I$. 
  
  Let: 
  $
    Z = invlim_(i in I) Z_i
  $
  with maps $v_i: Z -> Z_i, u_i: Z_i -> Z_0$. 
  
  Take any $cal(F)_0 in cAb((Z_0)_et)$, and any qcqs $U in Et_Z$. Then there exists $k in I$ s.t. $U$ is the base change of $U_k in Et_(Z_k)$. Then the canonical map induced by the pullbacks $H^q (Z_j, u_j^(-1) cal(F)_0) -> H^q (Z, v_0^(-1) cal(F)_0)$ along $v_j$:
  $
    dirlim_(j>=k) H^q (U_j, u_j^(-1) cal(F)_0) -> H^q (U, v_0^(-1) cal(F)_0) 
  $
  is an isomorphism. In particular, there is a canonical isomorphism: 
  $
    dirlim_(i in I) H^q (Z_i, u_i^(-1) cal(F)_0) -> H^q (Z, v_0^(-1) cal(F)_0)
  $
]
#proof[
  // We first use a general categorical construction to reduce from a general cofiltered limit to a projective limit. 
  // #lemma[
  //   (Artin-Mazur construction) Let $I$ be a cofiltered category with a final object. Then there exists a directed poset $P$ with a minimum element, with a cofinal functor $P -> I^opp$. 
  // ]
  // #proof[
  //   This is mostly just #cite-stacks("0032", [Lemma 4.21.5]), where we additionally truncate $P$ to elements $>=$ some element to guarantee the existence of a minimum element. 
  // ]
  // This construction tells us that we may replace the cofiltered limit $I$ with the projective limit over $P$. We may thus assume that the cofiltered category $I$ is actually a directed poset with a minimum element $0$, and we are dealing with a projective limit of schemes. 

  #lemma[
    + Any $U in Et_Z$ of finite presentation over $Z$ comes from base changing a $U_j in Et_(Z_j)$ of finite presentation over $Z_j$ for some $j in I$. 

    + Every etale cover of any $U in Et_Z$ of finite presentation over $Z$ is refined by one in the subsystem $cal(S)$ of etale covers defined below: 
    
      Suppose that $U$ is obtained by base changing $U_j in Et_(Z_j)$. Then $cal(S)$ consists of etale covers $cal(U) = {U_alpha -> U}$ with finitely many maps, so that there exists some $k in I$ and an etale cover $cal(U)_k = {U_(alpha,k) -> U_k}$ in $Et_(Z_k)$, whose base change to $Z$ is $cal(U)$, and where each $U_(alpha,k)$ is affine, and of finite presentation (i.e. qcqs, since we already have locally of finite presentation from etaleness) over $U_k$. 
  ]
  #proof[
    (1) follows from Theorem @passage-to-limit-of-morphisms and @passage-to-limit-of-properties. 

    (2) Since $U$ is of finite presentation over the qcqs scheme $Z$, it is itself qcqs. Given any etale cover $cal(U) = {U_alpha -> U}$, we may first refine it by a cover in which every $U_alpha$ is affine. Since $U$ is quasi-compact, we may further refine by a finite subcover, so the index set for $alpha$'s is finite. 
    
    Since $U_alpha$ and $U$ are both qcqs, the morphism $U_alpha -> U$ is qcqs. Since it is also etale (and so locally of finite presentation), it is of finite presentation. By @passage-to-limit-of-morphisms and @passage-to-limit-of-properties, for each $alpha$, there exists some $j <= i_alpha in I$ s.t. $U_alpha -> U$ comes from base changing a morphism $U_(alpha,i_alpha) -> U_(i_alpha)$ in $Et_(Z_(i_alpha))$. By picking a common upper bound for all $alpha$'s, there exists some $j <= k in I$ and morphisms ${U_(alpha,k) -> U_k}_alpha$ in $Et_(Z_k)$ whose base change to $Z$ is ${U_alpha -> U}$. Since $union.sq.big_alpha U_alpha -> U$ is surjective, up to replacing $k$ with some further stage, we may assume that $union.sq.big_alpha U_(alpha,k) -> U$ is surjective, and so ${U_(alpha,k) -> U_k}_alpha$ is jointly surjective, hence an affine cover. We are thereby done. 
  ]

  We now prove the result in 3 steps: For $H^0$, for Cech cohomology, and with the Cech-to-derived-functor spectral sequence, analogous to the proof for the limit formula for sheaves. 

  Step 1. Proof for $q = 0$. Write $cal(F)_i = u_i^(-1) cal(F)_0$ and $cal(F) = v_0^(-1) cal(F)_0$. We claim that there exists a canonical identification: 
  $
    cal(F) (U) = dirlim_(j >= k) cal(F)_j (U_j)
  $
  for any $U in Et_Z$ obtained from base changing some qcqs (i.e. of finite presentation over $Z_k$) $U_k in Et_(Z_k)$, whenever $U$ is qcqs. (Such $U_k$ always exists by previous lemma.)

  #proof[
    We first prove a lemma: 
    #lemma(name: <limit-formula-for-schemes-pab>)[
      Let ${Z_i}_(i in I)$ be a projective system of qcqs schemes, with all transition maps affine, with a final object $0 in I$.
      
      Let:
      $
        Z = invlim_(i in I) Z_i
      $
      with maps $v_i: Z -> Z_i, u_i: Z_i -> Z_0$. Take any $cal(F)_0 in cPAb((Z_0)_et)$. Then for any qcqs $U in Et_Z$ obtained from base changing some qcqs (i.e. of finite presentation over $Z_k$) $U_k in Et_(Z_k)$: 
      $
        v_(0,cPSh)^(-1) cal(F)_0 (U) = dirlim_(j>=k) u_(j,cPSh)^(-1) cal(F)_0 (U_j)
      $
    ]
    #proof[
      Recall that for any $U in Et_Z$:
      $
        v_(0,cPSh)^(-1) cal(F)_0 (U) = dircolim_((V_0,phi)) cal(F)_0 (V_0)
      $
      where the filtered colimit is over all diagrams of the shape:
      // https://q.uiver.app/#r=typst&q=WzAsNCxbMCwxLCJaIl0sWzEsMSwiWl8wIl0sWzEsMCwiVl8wIl0sWzAsMCwiVSJdLFszLDIsInBoaSJdLFswLDFdLFszLDBdLFsyLDFdXQ==
      #align(center, diagram({
        node((-1, 0), [$Z$])
        node((0, 0), [$Z_0$])
        node((0, -1), [$V_0$])
        node((-1, -1), [$U$])
        edge((-1, -1), (0, -1), [$phi$], label-side: left, "->")
        edge((-1, 0), (0, 0), "->")
        edge((-1, -1), (-1, 0), "->")
        edge((0, -1), (0, 0), "->")
      }))
      with $V_0 in Et_(Z_0)$. In other words, we are dealing with a filtered colimit: 
      $
        v_(0,cPSh)^(-1) cal(F)_0 (U) = dircolim_(V_0 in Et_(Z_0) \ phi in Hom_Z (U, Z times_(Z_0) V_0)) cal(F)_0 (V_0)
      $
      Similarly, 
      $
        dirlim_(j>=k) u_(i,cPSh)^(-1) cal(F)_0 (U_j) = dirlim_(j>=k) dircolim_(V_0 in Et_(Z_0) \ phi_j in Hom_(Z_j) (U_j, Z_j times_(Z_0) V_0)) cal(F)_0 (V_0)
      $

      However, by @passage-to-limit-of-morphisms, 
      $
        Hom_Z (U, Z times_(Z_0) V_0) = dirlim_(j>=k) Hom_(Z_j) (U_j, Z_j times_(Z_0) V_0)
      $
      so $(j, V_0, phi_j) |-> (V_0, Z times_(Z_j) phi_j)$ is a cofinal functor between the index categories between the two filtered colimits. Thus, the natural map: 
      $
        dirlim_(j>=k) dircolim_(V_0 in Et_(Z_0) \ phi_j in Hom_(Z_j) (U_j, Z_j times_(Z_0) V_0)) cal(F)_0 (V_0) -> dircolim_(V_0 in Et_(Z_0) \ phi in Hom_Z (U, Z times_(Z_0) V_0)) cal(F)_0 (V_0)
      $
      is an isomorphism. 
      /*
      However, $U -> Z$ is the base change of $U_k -> Z_k$. By @passage-to-limit-of-morphisms (2) and @passage-to-limit-of-properties, the morphism $U -> V := V times_(Z_0) Z_k$ over $Z$ is the base change of some $U_j -> V_j := V_0 times_(Z_0) Z_j$ over $Z_j$, i.e. a morphism $U_j -> V_0$ over $Z_0$. By picking $j >= k$, $U_j -> Z_j$ is also etale. In other words, the diagram above factors as:
      // https://q.uiver.app/#r=typst&q=WzAsNixbMCwxLCJaIl0sWzEsMSwiWl9rIl0sWzEsMCwiVV9rIl0sWzAsMCwiVSJdLFsyLDAsIlZfMCJdLFsyLDEsIlpfMCJdLFszLDJdLFswLDFdLFszLDBdLFsyLDFdLFsxLDVdLFsyLDQsInBoaV9rIl0sWzQsNV1d
      #align(center, diagram({
        node((-1, 0), [$Z$])
        node((0, 0), [$Z_k$])
        node((0, -1), [$U_k$])
        node((-1, -1), [$U$])
        node((-0.7, -0.7), [$cart$])
        node((1, -1), [$V_0$])
        node((1, 0), [$Z_0$])
        edge((-1, -1), (0, -1), "->")
        edge((-1, 0), (0, 0), "->", $v_k$, label-side: right)
        edge((-1, -1), (-1, 0), "->")
        edge((0, -1), (0, 0), "->")
        edge((0, 0), (1, 0), "->", $u_k$, label-side: right)
        edge((0, -1), (1, -1), [$phi_k$], label-side: left, "->")
        edge((1, -1), (1, 0), "->")
      }))
      
      Using abstract categorical arguments, the filtered colimit can thus be taken over $(j, V_0, phi_j)$ where $j>=k, V_0 in Et_(Z_0)$ and $phi_j: U_j -> V_0$, fitting in the diagram above. As such,
      $
        v_(0,cPSh)^(-1) cal(F)_0 (U) &= dircolim_((V_0,phi)) cal(F)_0 (V_0) = dircolim_((j,V_0,phi_j) \ j>=k) cal(F)_0 (V_0) = dirlim_(j>=k) dircolim_((V_0,phi_j)) cal(F_0) (V_0) \
        &= dirlim_(j>=k) u_j^(-1) cal(F)_0 (U_k) = dirlim_(j>=k) cal(F)_k (U_k)
      $
      for all $U in Et_Z$ qcqs. */
    ]

    We now prove that for all $U in Et_Z$ qcqs, $cal(F)(U) = v_(0,cPSh)^(-1) cal(F)_0 (U)$. Let $cal(S)$ be the subsystem of etale covers of $U$ as in the previous lemma. We now compute $caron(H)^0 (cal(U), v_(0,cPSh)^(-1) cal(F)_0)$ for some $cal(U) = {U_alpha -> U} in cal(S)$, base changed from $cal(U)_(k') = {U_(alpha,k') -> U_(k')}$ for $k' >= k$, an etale cover in $Et_(Z_(k'))$. Consider:
    $
      & caron(H)^0 (cal(U), v_(0,cPSh)^(-1) cal(F)_0) \
      =& ker(product_alpha v_(0,cPSh)^(-1) cal(F)_0 (U_alpha) -> product_(alpha,beta) v_(0,cPSh)^(-1) cal(F)_0 (U_alpha times_U U_beta)) #[by definition]\
      =& ker(product_alpha dirlim_(j>=k') u_(j,cPSh)^(-1) cal(F)_0 (U_(alpha,j)) -> product_(alpha,beta) dirlim_(j>=k') u_(j,cPSh)^(-1) cal(F)_0 (U_(alpha,j) times_(U_j) U_(beta,j))) \
      & #[by our description of $v_(0,cPSh)^(-1) cal(F)_0$] \
      =& ker(dirlim_(j>=k') product_alpha u_(j,cPSh)^(-1) cal(F)_0 (U_(alpha,j)) -> dirlim_(j>=k') product_(alpha,beta) u_(j,cPSh)^(-1) cal(F)_0 (U_(alpha,j) times_(U_j) U_(beta,j))) \
      & #[as finite lims commutes with filtered colims] \
      =& dirlim_(j>=k') ker(product_alpha u_(j,cPSh)^(-1) cal(F)_0 (U_(alpha,j)) -> product_(alpha,beta) u_(j,cPSh)^(-1) cal(F)_0 (U_(alpha,j) times_(U_j) U_(beta,j))) #[by (Ab5) of $cAb$] \
      =& dirlim_(j>=k') caron(H)^0 (cal(U), u_(j,cPSh)^(-1) cal(F)_0)
    $
    Taking a directed limit over all $cal(U) in cal(S)$, we see that:
    $
      caron(H)^0 (U, v_(0,cPSh)^(-1) cal(F)_0) = dirlim_(j>=k) caron(H)^0 (U_j, u_(j,cPSh)^(-1) cal(F)_0)
    $
    for all qcqs $U in Et_Z$. In other words,
    $
      (v_(0,cPSh)^(-1) cal(F)_0)^+ (U) = dirlim_(j>=k) (u_(j,cPSh)^(-1) cal(F)_0)^+ (U_j)
    $
    for all $U in Et_Z$ qcqs. Next, we repeat the argument above again for computing $caron(H)^0 (U, (v_(0,cPSh)^(-1) cal(F)_0)^+)$, where every etale cover is refined by one in $cal(S)$, which has all etale opens and their fiber products being qcqs. We then see that:
    $
      cal(F) (U) = (v_(0,cPSh)^(-1) cal(F)_0)^\# (U) = dirlim_(j>=k) (u_(j,cPSh)^(-1) cal(F)_0)^\# (U_j) = dirlim_(j>=k) cal(F)_j (U_j)
    $
    #suppress-qed
  ]

  Step 2. Proof for Cech cohomology. We claim that the canonical map: 
  $
    dirlim_(j>=k) caron(H)^p (U_j, cal(F)_j) -> caron(H)^p (U, cal(F)) 
  $
  is an isomorphism for all qcqs $U in Et_Z$, coming from a qcqs $U_k in Et_(Z_k)$. 

  #proof[
    Given any $cal(U) in cal(S)$, say $cal(U) = {U_alpha -> U}$ coming from $cal(U)_(k') = {U_(alpha,k') -> U_(k')}$ for $k' >= k$, an etale cover in $Et_(Z_(k'))$. Consider the Cech complex: 
    $
      C^p (cal(U), cal(F)) &= product_(alpha_0,dots.c,alpha_p) cal(F)(U_(alpha_0,dots.c,alpha_p)) #[by definition] \
      &= product_(alpha_0,dots.c,alpha_p) dirlim_(j>=k') cal(F)_j (U_(j,alpha_0,dots.c,alpha_p)) #[by Step 1] \
      &= dirlim_(j>=k') product_(alpha_0,dots.c,alpha_p) cal(F)_j (U_(j,alpha_0,dots.c,alpha_p)) #[by commuting finite lims and filtered colims] \
      &= dirlim_(j>=k') C^p (cal(U)_j, cal(F)_j)
    $
    In other words, the Cech complex for $cal(F)$ w.r.t. $cal(U)$ is the direct limit of the Cech complexes for those $cal(F)_j$ w.r.t. $cal(U)_j$ for $j >= k'$. By (Ab5) of $cAb$, taking cohomologies commutes with filtered colimits, so: 
    $
      caron(H)^p (cal(U), cal(F)) = dirlim_(j>=k') caron(H)^p (cal(U)_j, cal(F)_j)
    $
    Next, we would like to take the direct limit w.r.t. $cal(U) in cal(S)$ and commute two direct limits. However, $k'$ depends on $cal(U)$ and there's some categorical subtleties: We get an isomorphism
    $
      caron(H)^p (U, cal(F)) = dirlim_(cal(U)) dirlim_(j>=k') caron(H)^p (cal(U)_j, cal(F)_j) = dirlim_((k', cal(U),j) \ j>=k'>=k) caron(H)^p (cal(U)_j, cal(F)_j) = dirlim_(j>=k) caron(H)^p (U_j, cal(F)_j)
    $
    where the last two equalities follow by abstract categorical arguments. 
  ]

  Step 3. Proof for general case. The case $q = 0$ is Step 1, and the case $q = 1$ follows from Step 2 and $caron(H)^1 = H^1$. Suppose that the theorem holds whenever $q < n$, and we want to deal with degree $n$ cohomology. 
  
  Take the Cech-to-derived-functor spectral sequence for each $cal(F)_j$: 
  $
    E_(2,j)^(p,q) = caron(H)^p (U_j, ul(H)^q (cal(F)_j)) => H^(p+q) (U_j, cal(F)_j) 
  $
  Passing to the direct limit (which is exact), we obtain a new spectral sequence, 
  $
    tilde(E)_2^(p,q) = dirlim_(j>=k) caron(H)^p (U_j, ul(H)^q (cal(F)_j)) => dirlim_(j>=k) H^(p+q) (U_j, cal(F)_j)
  $
  On the other hand, we have the Cech-to-derived-functor spectral sequence for $cal(F)$: 
  $
    E_2^(p,q) = caron(H)^p (U, ul(H)^q (cal(F))) => H^(p+q) (U, cal(F))
  $
  The filtered system induces a canonical morphism $Phi: tilde(E)_2^(p,q) -> E_2^(p,q)$ of spectral sequences. 

  Since $U$ is qcqs, its Cech cohomologies may be computed using covers in $cal(S)$, involving only qcqs objects of $Et_Z$. As such, computing $caron(H)^p (U, ul(H)^q (cal(F)))$ only involves evaluating $ul(H)^q (cal(F))$ on qcqs objects, on which the inductive hypothesis may be applied. Since covers in $cal(S)$ involves only finitely many maps, for any $cal(U) in cal(S)$ and any $0 <= q < n$, we have: 
  $
    caron(H)^p (cal(U), ul(H)^q (cal(F))) &= h^p (0 -> C^bullet (cal(U), ul(H)^q (cal(F)))) \
    &= h^p (dirlim_(j>=k') (0 -> C^bullet (cal(U)_j, ul(H)^q (cal(F)_j)))) #[by commuting finite lims and filtered colims] \
    &= dirlim_(j>=k') caron(H)^p (cal(U)_j, ul(H)^q (cal(F)_j))
  $
  Passing to the direct limit over $cal(U) in cal(S)$, and resolving categorical subtleties as in Step 2, we see that: 
  $
    caron(H)^p (U, ul(H)^q (cal(F))) = dirlim_(j>=k) caron(H)^p (U_j, ul(H)^q (cal(F)_j))
  $
  In other words, $Phi: tilde(E)_2^(p,q) -> E_2^(p,q)$, as a morphism of spectral sequences, induces isomorphisms on the region $0 <= q < n$. 

  Consider a bi-degree $(p, q)$ so that $p + q = n$. For a differential on page $r >= 2$ involving bi-degree $(p, q)$: 

  - If $q = n$, note that by @cech-h0-of-hq-psh-vanish, $E_2^(0,n) = caron(H)^0 (U, ul(H)^n (cal(F))) = 0$, and $tilde(E)_2^(0,n) = 0$ for the same reason. As such, all differentials involving the bi-degree $(0, n)$ are zero, and $Phi$ induces an isomorphism $tilde(E)_oo^(0,n) -> E_oo^(0,n)$, both of whose terms are $0$. 

  - Assume $q < n$. 

    - If this differential fires from $(p, q)$, its signature is $d^r: E_2^(p,q) -> E_2^(p+r,q-r+1)$. Then $q - r + 1 < q < n$, so this differential is in the region $0 <= q < n$, so it is isomorphic to $tilde(d)^r: tilde(E)_2^(p,q) -> tilde(E)_2^(p+r,q-r+1)$. 

    - If this differential fires into $(p, q)$, its signature is $d^r: E_2^(p-r,q+r-1) -> E_2^(p,q)$. Since we have a first quadrant spectral sequence, for this differential to be nonzero, it is required that $r <= p$, and so $q + r - 1 <= q + p - 1 = n - 1$. As such, this differential is in the region $0 <= q < n$, so it is isomorphic to $tilde(d)^r: tilde(E)_2^(p-r,q+r-1) -> tilde(E)_2^(p,q)$. 

    As such, $Phi$ induces isomorphisms on all differentials involving the bi-degree $(p, q)$, and induces an isomorphism $tilde(E)_oo^(p,q) -> E_oo^(p,q)$. 

  Finally, there exist filtrations: 
  $
    0 = tilde(F)_(n+1) subset tilde(F)_n subset dots.c subset tilde(F)_0 = tilde(H)^n = dirlim_(j>=k) H^n (U_j, cal(F)_j)
  $
  and: 
  $
    0 = F_(n+1) subset F_n subset dots.c subset F_0 = H^n = H^n (U, cal(F))
  $
  so that $Phi$ induces morphisms compatible with these filtrations. Furthermore, we have commutative diagrams: 
  // https://q.uiver.app/#r=typst&q=WzAsMTAsWzAsMCwiMCJdLFsxLDAsInRpbGRlKEYpXihwKzEpIl0sWzIsMCwidGlsZGUoRilecCJdLFszLDAsInRpbGRlKEUpX29vXihwLG4tcCkiXSxbNCwwLCIwIl0sWzAsMSwiMCJdLFsxLDEsIkZeKHArMSkiXSxbMiwxLCJGXnAiXSxbMywxLCJFX29vXihwLG4tcCkiXSxbNCwxLCIwIl0sWzAsMV0sWzEsMl0sWzIsM10sWzMsNF0sWzUsNl0sWzYsN10sWzcsOF0sWzgsOV0sWzEsNiwiUGhpIl0sWzIsNywiUGhpIl0sWzMsOCwiUGhpIl1d
  #align(center, diagram({
    node((-2, -1), [$0$])
    node((-1, -1), [$tilde(F)^(p+1)$])
    node((0, -1), [$tilde(F)^p$])
    node((1, -1), [$tilde(E)_oo^(p,n-p)$])
    node((2, -1), [$0$])
    node((-2, 0), [$0$])
    node((-1, 0), [$F^(p+1)$])
    node((0, 0), [$F^p$])
    node((1, 0), [$E_oo^(p,n-p)$])
    node((2, 0), [$0$])
    edge((-2, -1), (-1, -1), "->")
    edge((-1, -1), (0, -1), "->")
    edge((0, -1), (1, -1), "->")
    edge((1, -1), (2, -1), "->")
    edge((-2, 0), (-1, 0), "->")
    edge((-1, 0), (0, 0), "->")
    edge((0, 0), (1, 0), "->")
    edge((1, 0), (2, 0), "->")
    edge((-1, -1), (-1, 0), [$Phi$], label-side: left, "->")
    edge((0, -1), (0, 0), [$Phi$], label-side: left, "->")
    edge((1, -1), (1, 0), [$Phi$], label-side: left, "->")
  }))
  for each $0 <= p <= n$. By five lemma, since $Phi$ induces isomorphisms $tilde(E)^(p,n-p)_oo -> E^(p,n-p)_oo$, we see that: 
  $
    Phi: tilde(F)^(p+1) ->^tilde F^(p+1) ==> Phi: tilde(F)^p ->^tilde F^p
  $
  We may thus proceed inductively to show that $Phi$ induces an isomorphism $tilde(F)^0 -> F^0$. In other words, we have obtained the canonical isomorphism: 
  $
    dirlim_(j>=k) H^q (U_j, u_j^(-1) cal(F)_0) ->^tilde H^q (U, v_0^(-1) cal(F)_0) 
  $
]

We apply these limit formulas to compute stalks of push forwards of etale sheaves, by characterizing the limit of etale neighborhoods via the strict henselization. This is the most important application of the strict henselization, and shows that strict henselization defines the correct local ring for the etale topology. 

#construction(name: <strict-local-ring-and-localization>)[
  Given a scheme $X$ and a geometric point $ol(x): Spec(Omega) -> X$ of $X$, the *strict local ring* of $X$ at $ol(x)$ is defined as the strict henselization: 
  $
    cal(O)_(X,ol(x)) := cal(O)_(X,x)^#[sh] 
  $
  where the strict henselization is taken w.r.t. the inclusion $k(x) -> k(x)^sep subset Omega$, where $k(x)^sep$ is the separable closure of $k(x)$ within $Omega$.
  
  Now consider the directed limit: 
  $
    dirlim_((Spec(C),ol(u)) -> (X,ol(x)) #[etale]) C = dirlim_((Spec(C),ol(u)) -> (X,ol(x)) #[etale]) cal(O)_(Spec(C),u)
  $
  of etale neighborhoods of $(X, ol(x))$. 
  
  For any etale neighborhood $(Spec(B), frak(q)) -> (cal(O)_(X,x), frak(m)_x)$ with inclusion $phi: k(frak(q)) -> k(x)^sep$, defining a stage $B_(frak(q))$ in the directed limit defining $A^#[sh]$, by @passage-to-limit-of-morphisms (1) and @passage-to-limit-of-properties (3d), $(Spec(B), frak(q)) -> (cal(O)_(X,x), frak(m)_x)$ comes from base changing an etale map $(Spec(C), frak(r)) -> (Spec(A), frak(m)_x)$ for an affine neighborhood $x in Spec(A) subset X$. Furthermore, the compatible inclusion $k(frak(q)) -> k(x)^sep$ uniquely defines a geometric point of $Spec(C)$ above $frak(r)$ lying above $ol(x)$. Thus, 
  $
    cal(O)_(X,ol(x)) = cal(O)_(X,x)^#[sh] = dirlim_((Spec(B),frak(q),phi)) B_(frak(q)) = dirlim_((Spec(C),ol(u)) -> (X,ol(x)) #[etale]) cal(O)_(Spec(C),u) = dirlim_((Spec(C),ol(u)) -> (X,ol(x)) #[etale]) C
  $  

  Denote: 
  $
    tilde(X)_(ol(x)) = Spec(cal(O)_(X,ol(x)))
  $
  and then: 
  $
    tilde(X)_(ol(x)) = lim_((Spec(C),ol(u)) -> (X,ol(x)) #[etale]) Spec(C)
  $
  is an inverse limit of a cofinal system of etale neighborhoods of $(X, ol(x))$ under affine transition morphisms. 

  In other words, the strict henselization of the local ring at $x$ is the limit of etale neighborhoods of $(X, ol(x))$. It is to the etale topology what the local ring is to the Zariski topology. 
]

#theorem(name: <limit-formula-for-schemes>)[
  (Limit formula for schemes) Let ${Z_i}_(i in I)$ be a cofiltered system of qcqs schemes, with all transition maps affine, with a final object $0 in I$.
  
  Let:
  $
    Z = lim_(i in I) Z_i
  $
  be the cofiltered limit with maps $v_i: Z -> Z_i, u_i: Z_i -> Z_0$.
  /*Take any $cal(F)_0 in cAb((Z_0)_et)$, and any qcqs $U in Et_Z$. Then there exists $k in I$ s.t. $U$ is the base change of $U_k in Et_(Z_k)$. Then the canonical map induced by the pullbacks $H^q (Z_j, u_j^(-1) cal(F)_0) -> H^q (Z, v_0^(-1) cal(F)_0)$ by $v_j$:
  $
    dircolim_(j->k) H^q (U_j, u_j^(-1) cal(F)_0) -> H^q (U, v_0^(-1) cal(F)_0)
  $
  is an isomorphism. */Then there is a canonical isomorphism:
  $
    dircolim_(i in I) H^q (Z_i, u_i^(-1) cal(F)_0) -> H^q (Z, v_0^(-1) cal(F)_0)
  $
]
#proof[
  The case when $I$ is a directed set is proved above. For the case where $I$ is a general cofiltered category, we use the Artin-Mazur construction @artin-mazur-construction. 

  Thus there exists a directed set $P$ and a cofinal functor $F: P -> I^opp$. Up to replacing $P$ with $P_(>=0_P)$ for some element $0_P$, we may assume that $P$ admits a minimum element $0_P$. Now: 
  $
    Z = lim_(i in I) Z_i = invlim_(p in P) Z_(F(p))
  $
  Let $cal(F)_i = u_i^(-1) cal(F)_0, cal(F) = v_0^(-1) cal(F)_0$. Given $p in P$, the transition morphism $tilde(u)_p: Z_(F(p)) -> Z_(F(0_P))$ is a morphism satisfying $u_(F(0_P)) compose tilde(u)_p = u_(F(p))$. In particular, 
  $
    cal(F)_(F(p)) = tilde(u)_p^(-1) cal(F)_(F(0_P))
  $
  Similarly, let $tilde(v)_p: Z -> Z_(F(p))$, and so $u_(F(0_P)) compose tilde(v)_(0_P) = v_0$. As such, 
  $
    cal(F) = tilde(v)_(0_P)^(-1) cal(F)_(F(0_P))
  $
  Hence, applying the previous theorem to the directed set $P$ and the schemes ${Z_(F(p))}_(p in P)$, we see that: 
  $
    dircolim_(i in I) H^q (Z_i, cal(F)_i) = dirlim_(p in P) H^q (Z_(F(p)), cal(F)_(F(p))) = H^q (Z, cal(F))
  $
]

#theorem(name: <stalks-of-derived-lowerstar>)[
  Let $f: X -> Y$ be a qcqs morphism between schemes. Then for any $cal(F) in cAb(X_et)$ and geometric point $ol(y)$ of $Y$, there is a natural isomorphism:
  $
    (R^q f_* cal(F))_(ol(y)) = H^q (X times_Y tilde(Y)_(ol(y)), cal(F)|_(X times_Y tilde(Y)_(ol(y))))
  $
]
#proof[
  Recall that $R^q f_* cal(F)$ is the sheafification of $U |-> H^q (X times_Y U, cal(F))$ by @derived-lower-star-first-props, i.e. $U |-> H^q (X times_Y U, cal(F)|_(X times_Y U))$ by @pullback-along-etale-morphism-derived. Also the stalks may be computed by taking the filtered colimit on the presheaf level by @pullback-first-props (3), so:
  $
    (R^q f_* cal(F))_(ol(y)) &= dircolim_((U,ol(u)) -> (Y,ol(y)) \ #[etale nbhds]) H^q (X times_Y U, cal(F)|_(X times_Y U)) \
    &= dircolim_((U,ol(u)) -> (Y,ol(y)) \ #[affine etale nbhds]) H^q (X times_Y U, cal(F)|_(X times_Y U))
  $
  However, note that:
  $
    lim_((U,ol(u)) -> (Y,ol(y)) \ #[affine etale nbhds]) X times_Y U = X times_Y lim_((U,ol(u)) -> (Y,ol(y)) \ #[affine etale nbhds]) U = X times_Y tilde(Y)_(ol(y))
  $
  with transition morphisms all affine, and each $X times_Y U$ qcqs over the affine scheme $U$, hence qcqs. As such, limit formula of schemes (@limit-formula-for-schemes) may be applied, and we see that:
  $
    (R^q f_* cal(F))_(ol(y)) = H^q (X times_Y tilde(Y)_(ol(y)), cal(F)|_(X times_Y tilde(Y)_(ol(y))))
  $
]

#corollary(name: <stalks-of-finite-pushforward>)[
  If $f: X -> Y$ is a finite morphism, then there exists a canonical isomorphism for any $cal(F) in cAb(X_et)$ and any algebraically closed geometric point $ol(y)$ of $Y$:
  $
    (f_* cal(F))_(ol(y)) = oplus.big_(ol(x) in f^(-1)(ol(y))) cal(F)_(ol(x))
  $
  In particular, $f_*$ is exact.
]
#proof[
  By @strict-henselization-and-finite-base-change,
  $
    X times_Y tilde(Y)_(ol(y)) = product_(ol(x) in f^(-1)(ol(y))) tilde(X)_(ol(x))
  $
  Hence,
  $
    (f_* cal(F))_(ol(y)) &= Gamma(X times_Y tilde(Y)_(ol(y)), cal(F)|_(X times_Y tilde(Y)_(ol(y)))) = Gamma(product_(ol(x) in f^(-1)(ol(y))) tilde(X)_(ol(x)), cal(F)|_(product_(ol(x) in f^(-1)(ol(y))) tilde(X)_(ol(x)))) \
    &= oplus.big_(ol(x) in f^(-1)(ol(y))) Gamma(tilde(X)_(ol(x)), cal(F)|_(tilde(X)_(ol(x)))) = oplus.big_(ol(x) in f^(-1)(ol(y))) cal(F)_(ol(x))
  $
]

#corollary(name: <pushforward-by-finite-morphism>)[
  If $f: X -> Y$ is a finite morphism, then for any $cal(F) in cAb(X_et)$, there is a canonical isomorphism: 
  $
    H^q (X, cal(F)) cong H^q (Y, f_* cal(F))
  $
]
#proof[
  Consider the Leray spectral sequence: 
  $
    E_2^(p,q) = H^p (Y, R^q f_* cal(F)) => H^(p+q) (X, cal(F))
  $
  Since $f_*$ is exact, $R^q f_* = 0$ for $q >= 1$, and so the Leray spectral sequence degenerates, giving a canonical isomorphism: 
  $
    H^q (Y, f_* cal(F)) ->^tilde H^q (X, cal(F))
  $
]

Combining the limit formulas for sheaves and schemes, we have a composite limit formula: 

#theorem(name: <limit-formula-composite>)[
  (Composite limit formula) Let ${X_i}_(i in I)$ be a projective system of qcqs schemes, with all transition maps $u_(i,j): X_i -> X_j$ for $i>=j$ affine. Let: 
  $
    X = invlim_(i in I) X_i
  $
  with projections $v_i: X -> X_i$. $(cal(F)_i, psi_(i,j))$ is called a *system of sheaves* for the projective system ${X_i}$, if: 

  - Each $cal(F)_i in cAb((X_i)_et)$ is an abelian etale sheaf on $X_i$. 

  - For any $i>=j$, $psi_(i,j): u_(i,j)^(-1) cal(F)_j -> cal(F)_i$ is a sheaf morphism satisfying for $i>=j>=k$: #h(1fr)
    $
      psi_(i,k) = psi_(i,j) compose u_(i,j)^(-1) psi_(j,k)
    $

  The *limit sheaf* of this system of sheaves is defined as: 
  $
    cal(F) := dirlim_(i in I) v_i^(-1) cal(F)_i
  $
  where for $i>=j$, the transition morphism $v_j^(-1) cal(F)_j -> v_i^(-1) cal(F)_i$ is the morphism $v_i^(-1) psi_(i,j)$. Then any qcqs $U in Et_X$ comes from base changing a qcqs $U_k in Et_(X_k)$ for some $k$, and the canonical morphism: 
  $
    dirlim_(i>=k) H^q (U_i, cal(F)_i) -> H^q (U, cal(F))
  $
  is an isomorphism. 
]
#proof[
  We combine the limit formula for sheaves (@limit-formula-for-sheaves) and the limit formula for schemes (@limit-formula-for-schemes). From the limit formula for sheaves: 
  $
    H^q (U, cal(F)) = H^q (U, dirlim_(j in I) v_j^(-1) cal(F)_j) = dirlim_(j in I) H^q (U, v_j^(-1) cal(F)_j) = dirlim_(j >=k) H^q (U, v_j^(-1) cal(F)_j)
  $
  Now for each $j>=k$, we apply the limit formula for schemes: 
  $
    H^q (U, v_j^(-1) cal(F)_j) = dirlim_(i>=j) H^q (U_i, u_(i,j)^(-1) cal(F)_j)
  $
  Thus, we have a double directed limit: 
  $
    H^q (U, cal(F)) = dirlim_(j>=k) dirlim_(i>=j) H^q (U_i, u_(i,j)^(-1) cal(F)_j)
  $
  Since $I$ is a directed set, every pair $(j,i)$ in this double limit is dominated by $(i,i)$. In other words, the objects corresponding to $i = j >= k$ are cofinal in the index category of this colimit. Thus, 
  $
    H^q (U, cal(F)) = dirlim_(j>=k) dirlim_(i>=j) H^q (U_i, u_(i,j)^(-1) cal(F)_j) = dirlim_(i>=k) H^q (U_i, cal(F)_i)
  $
  and we are done. 
]

This has a corollary, as a limit formula stated directly in terms of a sheaf on the limit scheme. 

#corollary(name: <limit-formula-adjunction>)[
  Let ${X_i}_(i in I)$ be a projective system of qcqs schemes, with all transition maps $u_(i,j): X_i -> X_j$ for $i>=j$ affine. Let: 
  $
    X = invlim_(i in I) X_i
  $
  with projections $v_i: X -> X_i$. For any $cal(F) in cAb(X_et)$, ${v_(i,*) cal(F)}_(i in I)$, together with the transition morphisms: 
  $
    psi_(i,j): u_(i,j)^(-1) v_(j,*) cal(F) -> v_(i,*) cal(F)
  $
  defined as adjunctions of the identity morphism $v_(j,*) cal(F) -> u_(i,j,*) v_(i,*) cal(F) = v_(j,*) cal(F)$, makes a system of sheaves for ${X_i}$ with limit sheaf $cal(F)$. In other words, the canonical map: 
  $
    dirlim_(i in I) v_i^(-1) v_(i,*) cal(F) -> cal(F)
  $
  is an isomorphism. In particular, by @limit-formula-composite: 
  $
    H^q (X, cal(F)) = dirlim_(i in I) H^q (X_i, v_(i,*) cal(F))
  $
]
#proof[
  To show that $dirlim_(i in I) v_i^(-1) v_(i,*) cal(F) cong cal(F)$, it suffices to check section-wise. For qcqs $U in Et_X$ coming from qcqs $U_k in Et_(X_k)$, 
  $
    (dirlim_(i in I) v_i^(-1) v_(i,*) cal(F))(U) &= dirlim_(i>=k) v_(i,*) cal(F) (U_i) #[by @limit-formula-composite] \
    &= dirlim_(i>=k) cal(F)(U) = cal(F)(U)
  $
  Since every $U in Et_X$ is covered by qcqs objects, we have shown $dirlim_(i in I) v_i^(-1) v_(i,*) cal(F) cong cal(F)$. 
]

We also have relative versions of limit formulas: 

#proposition(name: <relative-limit-formula-for-sheaves>)[
  Let $f: X -> S$ be a morphism between qcqs schemes, and ${cal(F)_i}_(i in I)$ be a directed system of sheaves in $cAb(X_et)$, and: 
  $
    cal(F) = dirlim_(i in I) cal(F)_i
  $
  Then the natural map: 
  $
    dirlim_(i in I) R^q f_* cal(F)_i -> R^q f_* cal(F)
  $
  is an isomorphism. 
]
#proof[
  For a geometric point $ol(s)$ of $S$, since stalks commute with colimits as a left adjoint: 
  $
    (dirlim_(i in I) R^q f_* cal(F)_i)_(ol(s)) = dirlim_(i in I) H^q (X times_S tilde(S)_(ol(s)), cal(F)_i|_(X times_S tilde(S)_(ol(s)))) = H^q (X times_S tilde(S)_(ol(s)), dirlim_(i in I) cal(F)_i|_(X times_S tilde(S)_(ol(s))))
  $
  by @limit-formula-for-sheaves, while: 
  $
    (R^q f_* cal(F))_(ol(s)) = H^q (X times_S tilde(S)_(ol(s)), cal(F)|_(X times_S tilde(S)_(ol(s))))
  $
  Meanwhile, pullbacks commute with colimits as left adjoints, so: 
  $
    cal(F)|_(X times_S tilde(S)_(ol(s))) = dirlim_(i in I) cal(F)_i|_(X times_S tilde(S)_(ol(s)))
  $
  and we are done. 
]

#proposition(name: <relative-limit-formula-for-schemes>)[
  Let $S$ be a qcqs scheme, and $X = invlim_(i in I) X_i$ be a projective limit of qcqs $S$-schemes with affine transition morphisms and a final object $0 in I$, with structure maps $g: X -> S$ and $g_i: X_i -> S$. 

  Let $cal(F)_0 in cAb((X_0)_et)$, and take $cal(F)_i = cal(F)_0|_(X_i), cal(F) = cal(F)_0|_X$. Then the natural map: 
  $
    dirlim_(i in I) R^q g_(i,*) cal(F)_i -> R^q g_* cal(F)
  $
  is an isomorphism. 
]
#proof[
  For a geometric point $ol(s)$ of $S$, since stalks commute with colimits as a left adjoint: 
  $
    (dirlim_(i in I) R^q g_(i,*) cal(F)_i)_(ol(s)) = dirlim_(i in I) (R^q g_(i,*) cal(F)_i)_(ol(s)) = dirlim_(i in I) H^q (X_i times_S tilde(S)_(ol(s)), cal(F)_i|_(X_i times_S tilde(S)_(ol(s))))
  $
  and: 
  $
    (R^q g_* cal(F))_(ol(s)) = H^q (X times_S tilde(S)_(ol(s)), cal(F)|_(X times_S tilde(S)_(ol(s))))
  $
  by @stalks-of-derived-lowerstar. Now $X_i times_S tilde(S)_(ol(s))$ are qcqs, 
  $
    cal(F)_i|_(X_i times_S tilde(S)_(ol(s))) = cal(F)_0|_(X_i)|_(X_i times_S tilde(S)_(ol(s))) = cal(F)_0|_(X_0 times_S tilde(S)_(ol(s)))|_(X_i times_S tilde(S)_(ol(s)))
  $
  and the same holds with $i$ omitted. Thus, we may apply @limit-formula-for-schemes to see that: 
  $
    dirlim_(i in I) H^q (X_i times_S tilde(S)_(ol(s)), cal(F)_i|_(X_i times_S tilde(S)_(ol(s)))) -> H^q (X times_S tilde(S)_(ol(s)), cal(F)|_(X times_S tilde(S)_(ol(s))))
  $
  is an isomorphism. We are thereby done since $dirlim_(i in I) R^q g_(i,*) cal(F)_i -> R^q g_* cal(F)$ is an isomorphism. 
  /*
  For every qcqs $U in Et_X$, 
  $
    dirlim_(i in I) H^q (U times_S X_i, cal(F)_i) -> H^q (U times_S X, cal(F))
  $
  is an isomorphism by @limit-formula-for-schemes. Now $R^q g_* cal(F)$ is the sheafification of $rho^q (g, cal(F)) := (U |-> H^q (U times_S X_i, cal(F)))$ by @derived-lower-star-first-props (3). 

  Thus, the natural presheaf morphism: 
  $
    dirlim_(i in I) rho^q (g_i, cal(F)_i) -> rho^q (g, cal(F))
  $
  are isomorphisms on sections on qcqs $U in Et_X$. Since colimits of sheaves may be computed by computing as colimits of presheaves, then sheafify, and that for $U in Et_X$ qcqs, $caron(H)^0 (U, -)$ may be computed using qcqs sections only, we have: 
  $
    R^q g_(i,*) cal(F)_i -> R^q g_* cal(F)
  $
  being an isomorphism on all $U in Et_X$ qcqs. Every $U in Et_X$ is covered by qcqs objects of $Et_X$, so this morphism is a sheaf isomorphism. */
]

#proposition(name: <relative-limit-formula-composite>)[
  Let $S$ be a qcqs scheme. Let ${X_i}_(i in I)$ be a projective system of qcqs $S$-schemes, with all transition maps $u_(i,j): X_i -> X_j$ for $i>=j$ affine. Let: 
  $
    X = invlim_(i in I) X_i
  $
  with projections $v_i: X -> X_i$ and structure maps $g_i: X_i -> S$. 
  
  Given a system of sheaves $(cal(F)_i, psi_(i,j))$ for the projective system ${X_i}$, with limit sheaf $cal(F)$, the canonical map: 
  $
    dirlim_(i in I) R^q g_(i,*) cal(F)_i -> R^q g_* cal(F)
  $
  is an isomorphism. 
]
#proof[
  We combine the relative limit formula for sheaves (@relative-limit-formula-for-sheaves) and for schemes (@relative-limit-formula-for-schemes): 
  $
    R^q g_* cal(F) &= R^q g_* (dirlim_(j in I) v_j^(-1) cal(F)_j) = dirlim_(j in I) R^q g_* v_j^(-1) cal(F)_j \
    &= dirlim_(j in I) dirlim_(i>=j) R^q g_(i,*) u_(i,j)^(-1) cal(F)_j \
    &= dirlim_(i in I) R^q g_(i,*) cal(F)_i #[since the diagonal $(i,i)$ is cofinal]
  $
]

Finally, we state @stalks-of-derived-lowerstar in the derived category. 

#proposition(name: <derived-stalks-of-derived-pushforward>)[
  For $cal(K) in D^+ (X_et, Lambda)$ and a qcqs morphism $f: X -> Y$ between schemes, there exists a canonical quasi-isomorphism: 
  $
    (R f_* cal(K))_(ol(y)) cong R Gamma(X times_Y tilde(Y)_(ol(y)), cal(K)|_(X times_Y tilde(Y)_(ol(y))))
  $
  This quasi-isomorphism holds for all $cal(K) in D(X_et, Lambda)$ if $R f_*$ and $R Gamma (X times_Y tilde(Y)_(ol(y)), -)$ are bounded above. 
]
#proof[
  We apply @stalks-of-derived-lowerstar and way-out lemma. 
]
