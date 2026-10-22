#import "void-import.typ": *
== $cAb(X_et)$ as an abelian category <sect-ab-x-et-as-abelian-cat>

/*
#date[Lecture 6, 2025/10/29
  #set align(left)
  The first problem set is available on Web Learning. Please read the instructions and keep in mind that it will be graded as in refereeing a paper. 

  Today we'll consider: 
  - $cAb(X_et)$; 
  - Functoriality; 
  - Stalks; 
  - Etale site of a field. 
]

Let $X$ be a scheme. Then we have associated to $X$ an etale site $X_et$, on which we have categories of presheaves/sheaves of sets/abelian groups: 
$
  iota: cSh(X_et) arrow.r.hook cPSh(X_et), cAb(X_et) arrow.r.hook cPAb(X_et)
$
Last time, we showed that the forgetful functor $iota$ admits a right adjoint $cal(G) |-> cal(G)^\#$, The construction is like: 
*/

As we stated at the beginning of the previous section, we will develop different methods of obtaining etale sheaves over the next few sections. This section corresponds to the second of these methods: using the abelian category structure of $cAb(X_et)$. 

As such, to establish $cAb(X_et)$ as a well-behaved abelian category, our goal is to establish the following constructions and results: 

- Sheafification; 
- $cAb(X_et)$ being an abelian category (a.k.a. defining kernels, cokernels and images); 
- $cAb(X_et)$ having enough injectives. 

Our first goal is the sheafification. 

#construction(name: <constr-zeroth-cech-cohom>)[
  Given any etale cover $cal(U) = {U_i -> U}_i$ in $Et_X$ and $cal(G) in cPSh(X_et)$, we define the *zeroth Cech cohomology* of $cal(G)$ w.r.t. $cal(U)$, denoted $caron(H)^0 (cal(U), cal(G))$ to be the equalizer: 
  $
    caron(H)^0 (cal(U), cal(G)) -> product_i cal(G)(U_i) arrows.rr product_(i,j) cal(G)(U_i times_U U_j)
  $
  In other words, elements of $caron(H)^0 (cal(U), cal(G))$ are collections of sections ${s_i in cal(G)(U_i)}$ that agree on intersections (i.e. fiber products) of the ${U_i}$'s. 

  Given an etale cover $cal(U) = {U_i -> U}_(i in I)$, a refinement of $cal(U)$ is an etale cover $cal(V) = {V_j -> U}_(j in J)$, a map on indices $lambda: J -> I$ and a factoring $V_j -> U_(lambda(j)) -> U$ for each $j in J$. Given a refinement $cal(V)$ of $cal(U)$, there are natural morphisms $product_i cal(G)(U_i) -> product_j cal(G)(V_j), (s_i) |-> (s_(lambda(j))|_(V_j))_j$, and similarly morphisms $product_(i,i') cal(G)(U_i times_U U_(i')) -> product_(j,j') cal(G)(V_j times_V V_(j'))$. This induces natural morphisms: 
  $
    caron(H)^0 (cal(U), cal(G)) -> caron(H)^0 (cal(V), cal(G))
  $
  #lemma[
    The morphism: 
    $
      caron(H)^0 (cal(U), cal(G)) -> caron(H)^0 (cal(V), cal(G))
    $
    induced by two different refinements of $cal(U)$ to $cal(V)$ is the same. 
  ]
  #proof[
    Given two refinements of $cal(U)$ by $cal(V)$ with maps on indices $lambda, lambda': J -> I$, we need to show for each $s = (s_i) in caron(H)^0 (cal(U), cal(G))$: 
    $
      s_(lambda(j))|_(V_j) = s_(lambda'(j))|_(V_j)
    $
    for each $j$. However, since $s in caron(H)^0 (cal(U), cal(G))$, 
    $
      s_(lambda(j))|_(U_(lambda(j)) times_U U_(lambda'(j))) = s_(lambda'(j))|_(U_(lambda(j)) times_U U_(lambda'(j)))
    $
    Meanwhile, from the two refinements, we have factorizations $V_j -> U_(lambda(j)) -> U$ and $V_j -> U_(lambda'(j)) -> U$ of $V_j -> U$ in $Et_X$. We may thus pass to the fiber product and obtain a factorization $V_j -> U_(lambda(j)) times_U U_(lambda'(j)) -> U$. Restricting the relation above further to $V_j$ thus concludes the proof. 
  ]
  
  We define the *zeroth Cech cohomology* of $cal(G)$ on $U$ to be the directed limit: 
  $
    caron(H)^0 (U, cal(G)) = dirlim_(cal(U)) caron(H)^0 (cal(U), cal(G))
  $
  taken over the directed set of all etale covers $cal(U)$ of $U$, where $cal(U) <= cal(V)$ iff there exists a refinement from $cal(U)$ to $cal(V)$. The transition maps are defined using refinements above, and are well-defined since they are independent from the specific refinement. 

  #remark(name: <set-categorical-subtleties>)[
    There are at least two subtleties in this definition:#footnote[I wasn't aware of either of these difficulties initially. The category-theoretic subtlety occurred to me when I was writing the next section on stalks and realized that it is possible that two refinements cannot be equalized, under some AI assistance. I later found out that it is documented in @cite-lei-fu. The set-theoretic subtlety was informed to me by Irisu, when I brought up the category-theoretic subtlety up in a group discussion.]

    - A category-theoretic subtlety: 
    
      If you naively define $caron(H)^0 (U, cal(G)) = colim_(cal(U)) caron(H)^0 (cal(U), cal(G))$ where the colimit is taken over the category of etale covers of $U$ where morphisms are refinements, this colimit is not filtered. This is because given two refinements between a pair of covers, it is not always possible to equalize them with a further refinement. 

      We eventually need to use that $caron(H)^0 (U, cal(G))$ is defined as a filtered colimit to show that sheafification commutes with finite limits and is exact. As such, had we defined $caron(H)^0$ using refinements as morphisms in the index category, at that point we will need to justify this arbitrary colimit as a directed limit, by repeating the lemma that two different refinements between the same pair of covers induces the same transition morphisms. In other words, the previous lemma is an essential part of this theory. 

      As such, it is just better that we define $caron(H)^0 (U, cal(G))$ here as a directed limit over etale covers where morphisms are refinement _as a property_, instead of refinement _as a structure_. 

    - A set-theoretic subtlety: 

      Suppose that our ambient Grothendieck universe is $cal(W)$, where#footnote[We use $cal(W)$ instead of the customary $cal(U)$ since $cal(U)$ has been used to denote an etale cover in this context.] our sets are $cal(W)$-sets and schemes are $cal(W)$-schemes, etc. Then in general, the set of all etale covers of $U$ (indexed by a $cal(W)$-set using $cal(W)$-schemes, of course) has the same cardinality as $cal(W)$, and is not a $cal(W)$-set. As such, there is a priori a concern that the directed limit above might not exist as a $cal(W)$-set. 

      We may solve this set-theoretic issue by considering the following subfamily $cal(S)$ of etale covers: 

      - Etale covers $cal(U) = {U_i -> U}$ in which every $U_i$ is affine, has image contained in an affine open of $U$, and in which no two morphisms in $cal(U)$ are isomorphic. 

      By picking sufficiently small affine opens and then removing duplicates, it is evident that every etale cover of $U$ may be refined by one in $cal(S)$. On the other hand, the affine opens of $U$ form a $cal(W)$-set, and for each affine open $Spec(A) subset U$, any etale $A$-algebra is finite type over $A$, hence isomorphic to a quotient of some $A[x_1, dots.c, x_k]$. There are thus at most $max(aleph_0, abs(A))$, hence a $cal(W)$-set of them. In other words, every cover in $cal(S)$ has its morphisms chosen among a $cal(W)$-set. $cal(S)$ is thus a $cal(W)$-set. 

      Now that every etale cover of $U$ may be refined by one in $cal(S)$, the directed limit: 
      $
        dirlim_(cal(U)) caron(H)^0 (cal(U), cal(G)) = dirlim_(cal(U) in cal(S)) caron(H)^0 (cal(U), cal(G))
      $
      exists as a $cal(W)$-set. 
  ]
]

#definition[
  We say that a presheaf $cal(G)$ is *separated* if for any etale cover $cal(U) = {U_i -> U}$,
  $
    cal(G)(U) -> caron(H)^0 (cal(U), cal(G))
  $
  is injective.
  
  One may see that $cal(G)^+$ is separated, and if $cal(G)$ is separated, then $cal(G) arrow.r.hook cal(G)^+$ and $cal(G)^+$ is already a sheaf.
]

#lemma[
  The *Grothendieck plus construction*: 
  $
    (-)^+: cPSh(X_et) -> cPSh(X_et), cal(G) |-> (cal(G)^+: Z |-> caron(H)^0 (Z, cal(G)))
  $
  satisfies: 

  + For any $cal(G) in cPSh(X_et)$, $cal(G)^+$ is separated; 

  + For any separated $cal(G) in cPSh(X_et)$, $cal(G)^+$ is a sheaf. 
]
#proof[
  (1) We must show that given any etale cover $cal(U) = {U_i -> U}_(i in I)$ and any $s, t in cal(G)^+ (U) = caron(H)^0 (U, cal(G))$ s.t. $s|_(U_i) = t|_(U_i), forall i in I$, we have $s = t$. 

  By construction, $s$ comes from $caron(H)^0 (cal(V), cal(G))$ for some etale cover $cal(V)$ of $U$. By taking a common refinement of the etale covers for $s,t$ as well as $cal(U)$, we may assume that $s, t$ come from $caron(H)^0 (cal(V), cal(G))$, where $cal(V) = {V_j -> U}_(j in J)$ refines $cal(U)$. That is, $s = (s_j)$ where $s_j in cal(G) (V_j)$, and the same goes for $t$.

  We unfold the definition for the condition $s|_(U_i) = t|_(U_i)$. These sections come from $caron(H)^0 (cal(V) times_U U_i, cal(G))$ in the direct limit, so there exists a refinement $cal(W)_i = {W_(i,k) -> U_i}_(k in K_i)$ of $cal(V) times_U U_i$ with a map $lambda_i: K_i -> J$ on indices. Then the condition $s|_(U_i) = t|_(U_i)$ unfolds to: 
  $
    s_(lambda_i (k))|_(W_(i,k)) = t_(lambda_i (k))|_(W_(i,k)) in cal(G)(W_(i,k)), forall k in K_i
  $
  Let $K = union.sq.big_(i in I) K_i$. Then $cal(W) = {W_(i,k) -> U_i -> U}_(k in K)$ refines $cal(V)$ (with map $lambda = union.sq.big_(i in I) lambda_i : K -> J$ on indices). By the unfolded condition above, passing from $cal(V)$ to $cal(W)$ shows that $s = t in caron(H)^0 (U, cal(G))$. 

  (2) Note that there exists a natural map $cal(G)(U) -> cal(G)^+ (U)$, hence a natural presheaf morphism: 
  $
    theta: cal(G) -> cal(G)^+
  $
  $cal(G)$ being separated means that $theta$ is injective, i.e. injective on sections. 
  
  Since separatedness is shown in (1), it suffices to show that sections can be glued for $cal(G)^+$. 

  Let $cal(U) = {U_i -> U}$ be an etale cover, and ${s_i in cal(G)^+ (U_i)}$ be a family of sections compatible for $cal(G)^+$. 
  
  By definition, for each $i$, there exists an etale cover $cal(U)_i = {U_(i,j) -> U_i}$ s.t. $s_i$ is given by a family of sections ${s_(i,j) in cal(G)(U_(i,j))}_j$ compatible for $cal(G)$. 

  We claim that the family ${s_(i,j) in cal(G)(U_(i,j))}_(i,j)$ defines an element of $caron(H)^0 (cal(U)', cal(G))$, where $cal(U)' = {U_(i,j) -> U_i -> U}_(i,j)$ is the joined etale cover. 

  For this, we must show that $s_(i,j)$ and $s_(i',j')$ are compatible on $U_(i,j) times_U U_(i',j')$. Since $theta$ is injective, it suffices to show that $theta(s_(i,j)) = theta(s_(i',j'))$ when restricted to an element of $cal(G)^+ (U_(i,j) times_U U_(i',j'))$. 

  However, by assumption $s_i = s_(i')$ when restricted to $cal(G)^+ (U_i times_U U_(i'))$. By unfolding the definitions, $theta(s_(i,j)) = s_i|_(U_(i,j))$ and the same goes for the primed version. We are thereby done showing compatibility. As such, there exists a well-defined section $s in cal(G)^+ (U)$ s.t. $s|_(U_(i,j)) = s_(i,j) = s_i|_(U_(i,j))$. By separatedness, $s|_(U_i) = s_i$, and gluing is verified. 
]

By the previous lemma, $(cal(G)^+)^+$ is always a sheaf for any presheaf $cal(G)$. We may thus define sheafification.

#definition(name: <defn-sheafification>)[
  The *sheafification* functor is defined as: 
  $
    (-)^\#: cPSh(X_et) -> cSh(X_et), cPAb(X_et) -> cAb(X_et), cal(G) |-> cal(G)^\# := (cal(G)^+)^+
  $
]

#proposition[
  // The forgetful functor $iota: cSh(X_et) -> cPSh(X_et)$ admits a left adjoint $(-)^\#$ called *sheafification*.
  The sheafification $(-)^\#$ is the left adjoint to the forgetful functor $iota: cSh(X_et) -> cPSh(X_et)$. 
]
#proof[
  $cSh(X_et)$ is a full subcategory of $cPSh(X_et)$. As such, it suffices to show that the natural map $cal(F) -> cal(F)^\#$ induces a natural isomorphism: 
  $
    Hom_(cPSh) (cal(F)^\#, cal(G)) -> Hom_(cPSh) (cal(F), cal(G))
  $
  for any _sheaf_ $cal(G) in cSh(X_et)$. 

  Since $(-)^\#$ is $(-)^+$ applied twice, it suffices to show that: 
  $
    Hom_(cPSh) (cal(F)^+, cal(G)) -> Hom_(cPSh) (cal(F), cal(G))
  $
  induced by $theta: cal(F) -> cal(F)^+$ is an isomorphism. 

  We first prove injectivity: Given morphisms $f, g: cal(F)^+ -> cal(G)$ s.t. $f compose theta = g compose theta$, then for any $s in cal(F)^+ (U)$ represented by ${s_i in cal(F)(U_i)}$, 
  $
    f(s)|_(U_i) = f(s|_(U_i)) = f(theta(s_i)) = g(theta(s_i)) = g(s)|_(U_i)
  $
  and so by the sheaf conditions on $cal(G)$, $f(s) = g(s)$. Hence $f = g$. 

  We then prove surjectivity, i.e. any morphism $f': cal(F) -> cal(G)$ factors through $theta$. Indeed, given any $s in cal(F)^+ (U)$ represented by ${s_i in cal(F)(U_i)}$, the sections ${f'(s_i) in cal(G)(U_i)}$ are compatible on each $U_i times_U U_j$, since $f'$ is compatible with restrictions and the ${s_i}$'s are compatible. Thus, ${f'(s_i)}_i$ glue to a section $t in cal(G)(U)$. We then define $f(s) = t$. It is easy to check that $f$ is a morphism between sheaves and $f' = f compose theta$. 
]

#let Fun = math.op[Fun]
#lemma[
  For any category $cal(C)$, the category $Fun(cal(C), cAb)$ is an abelian category with enough injectives, and kernels, cokernels and images in this category are taken pointwise. Limits and colimits are also taken pointwise. 
]
#proof[
  This argument is purely formal. 
]

#corollary[
  $cPAb(X_et)$ is an abelian category with enough injectives, with kernels, cokernels, images taken section-wise. Limits and colimits are also taken section-wise. 
]
#proof[
  Take $cal(C) = Et_X^opp$ in the previous lemma. 
]

#lemma[
  $(-)^+, (-)^\#$ commute with finite limits, i.e. are left exact when considering presheaves of abelian groups. 
]
#proof[
  It suffices to show that $(-)^+$ commutes with finite limits since $(-)^\#$ is just $(-)^+$ applied twice. 

  However, we consider the two steps taken in the construction of $(-)^+$. Since limits and colimits in $cPSh(X_et)$ and $cPAb(X_et)$ are taken section-wise, it suffices to consider on a fixed $U in Et_X$. Now: 
  
  - $caron(H)^0 (cal(U), cal(F)) = ker(product_i cal(F)(U_i) -> product_(i,j) cal(F)(U_i times_U U_j))$ is an equalizer, which is a limit. Of course it commutes with any limits. 

  - $cal(F)^+ (U) = dirlim_(cal(U)) caron(H)^0 (cal(U), cal(F))$ is a filtered colimit, and it commutes with finite limits. 
]

#example(name: <detection-and-const-sheaf>)[
  From sheafification, we may construct more etale sheaves: 

  + For $V in X_et$, define $ul(ZZ)_(!,V,0) in cPAb(X_et)$ by $U |-> oplus.big_(Hom_X (U, V)) ZZ$. Then for $cal(G) in cPAb(X_et)$, we have an isomorphism:
    $
      Hom_(cPAb) (ul(ZZ)_(!,V,0), cal(G)) overset(->, tilde) cal(G)(V), (f: ZZ_V -> cal(G)) |-> f_V (1_(id_V))
    $
    Thus, the sheafification $ul(ZZ)_(!,V) = ul(ZZ)_(!,V,0)^\# in cAb(X_et)$ would satisfy that for $cal(F) in cAb(X_et)$,
    $
      Hom_(cAb(X_et)) (ul(ZZ)_(!,V), cal(F)) = Hom_(cPAb(X_et)) (ul(ZZ)_(!,V,0), cal(F)) = cal(F)(V)
    $
    
    In other words, morphisms from $ul(ZZ)_(!,V)$ detect sections on $V$. This construction has mild importance in the general theory. 

  + For any abelian group $M$, we define the *constant sheaf* $ul(M)_X$ associated with $M$ on $X$ to be the sheafification of the presheaf sending every nonempty $U$ to $M$. 

    /*
    #lemma[
      $ul(M)_X (U) cong M$ naturally for every connected $U in Et_X$. As a corollary, for those $U in Et_X$ that can be expressed as the disjoint union of its connected components#footnote[In the non-noetherian case this does not automatically hold.], 
      $
        ul(M)_X (U) cong product_(pi_0 (U)) M
      $
      from the sheaf conditions. 
    ]
    #proof[
      Since the constant presheaf $ul(M)_(X,0): U |-> M$ whenever $U != emptyset$ is already separated, $ul(M)_X = ul(M)_(X,0)^\# = ul(M)_(X,0)^+$. 

      Given any etale cover $cal(U) = {f_i: U_i -> U}_i$, we need to compute $caron(H)^0 (cal(U), ul(M)_(X,0))$: 
      $
        caron(H)^0 (cal(U), ul(M)_(X,0)) = ker(product_i ul(M)_(X,0) (U_i) -> product_(i,j) ul(M)_(X,0) (U_i times_U U_j))
      $
      consists of elements $(s_i) in product_i M$ in which $s_i = s_j$ whenever $U_i times_U U_j$ is nonempty. In particular, $s_i = s_j$ whenever $V_i ∩ V_j$ is nonempty where $V_i = f_i (U_i)$ is an open set of $U$. 

      For each fixed $i$, let $I_i = {j in I: exists k_0, k_1, dots.c, k_n in I, k_0 = i, k_n = j, V_(k_m) ∩ V_(k_(m+1)) != emptyset}$. Now define: 
      $
        W_i = union.big_(j in I_i) V_j
      $
      Then $W_i$ is an open set of $U$. Furthermore, $W_i^c$ is also an open set of $U$. Indeed, for any $x in W_i^c$, by joint surjectivity there exists $k in I$ s.t. $x in V_k$. If $V_k$ intersects $W_i$, then it must intersect $V_j$ for some $j in I_i$. Then by extending the chain of $j$ in the definition of $I_i$ by $k$, we see that $k in I_i$ and so $x in V_k subset W_i$, a contradiction. Thus $V_k subset W_i^c$. Now that $W_i$ is a nonempty closed and open subset of $U$, by connectivity, $W_i = U$. Thus for every $k in I$, $V_k$ intersects $W_i$, hence $V_j$ for some $j in I_i$. Thus $k in I_i$ as well. Thus $I_i = I$, and in other words, every $j in I$ is reachable from $i$ by a chain $k_0, dots.c, k_n$ in which every $V_(k_m) ∩ V_(k_(m+1)) != emptyset$. Thus $s_i = s_j, forall j in I$. 

      In other words, 
      $
        ul(M)_X (U) = dirlim_(cal(U)) caron(H)^0 (cal(U), ul(M)_(X,0)) = dirlim_(cal(U)) M = M
      $
    ]*/

    #lemma[
      For any $U in Et_X$, there is a natural isomorphism: 
      $
        ul(M)_X (U) cong C(U; M_#[disc]) = {#[locally constant functions] f: U -> M}
      $
      Under this isomorphism, if a sheaf morphism $phi: ul(M)_X -> cal(G)$ is induced by a presheaf morphism $phi_0: ul(M)_(X,0) -> cal(G)$, i.e. a compatible family of morphisms ${M -> cal(G)(U)}_(U in Et_X)$, then $phi$ is: 
      $
        ul(M)_X (U) = C(U; M_#[disc]) &-> cal(G)(U) \
        f &|-> (phi_0 (x) in cal(G)(f^(-1)(x))) in cal(G)(U) = cal(G)(union.sq.big_(x in M) f^(-1)(x)) = product_(x in M) cal(G)(f^(-1) (x))
      $
    ]
    #proof[
      Since $ul(M)_(X,0)$ is a separated presheaf, $ul(M)_X = ul(M)_(X,0)^+$, i.e. we only need to apply the plus construction once. 

      For an etale cover $cal(U) = {f_i: U_i -> U}$, 
      $
        caron(H)^0 (cal(U), ul(M)_(X,0)) = ker(product_i M -> product_(i,j) ul(M)_(X,0) (U_i times_U U_j))
      $
      where $ul(M)_(X,0) (U_i times_U U_j) = 0$ if $f_i (U_i) ∩ f_j (U_j) = emptyset$, and $M$ otherwise. As such, 
      $
        caron(H)^0 (cal(U), ul(M)_(X,0)) = {(m_i) in M^I : m_i = m_j #[if] f_i (U_i) ∩ f_j (U_j) != emptyset} subset M^I
      $
      Given an element $mu = (m_i) in caron(H)^0 (cal(U), ul(M)_(X,0))$, we may define sets for each $x in M$: 
      $
        U_(mu,x) = union.big_(i in I \ m_i = x) f_i (U_i) subset U
      $
      They are open sets for each $x$, and are disjoint for different $x$ since $m_i != m_j$ implies $f_i (U_i) ∩ f_j (U_j) = emptyset$. Furthermore, they cover $U$ since $cal(U)$ is jointly surjective. In other words, we have a partition $U = union.sq.big_(x in M) U_(mu,x)$ by closed and open subsets. We then define: 
      $
        f_mu = sum_(x in M) x bold(1)_(U_(mu,x)) in C(U; M_#[disc])
      $
      This gives a natural morphism $caron(H)^0 (cal(U), ul(M)_(X,0)) -> C(U; M_#[disc])$, easily seen to be compatible with the morphisms within the directed system. Thus, we have a natural morphism: 
      $
        ul(M)_X(U) = dirlim_(cal(U)) caron(H)^0 (cal(U), ul(M)_(X,0)) -> C(U; M_#[disc])
      $
      This morphism is surjective, since given any $f in C(U; ul(M)_#[disc])$, the Zariski covering $cal(U)_f = {f^(-1)(x) -> U}_(x in M)$ sends $(x)_x in caron(H)^0 (cal(U)_f, ul(M)_(X,0))$ to $f$. It is injective, since if $mu = (m_i)_(i in I) in caron(H)^0 (cal(U), ul(M)_(X,0))$ is sent to $0$, this means that $U_(mu,x) = emptyset$ for all $0 != x in M$, i.e. every $m_i = 0$. We are thereby done. The result on induced morphisms is just unfolding the definition of the adjunction isomorphism for sheafification. 
    ]
]

#theorem(name: <ab-x-et-the-abelian-cat>)[
  // + $cPAb(X_et)$ is an abelian category with enough injectives. $cal(F) -> cal(G)$ is a monomorphism/epimorphism (i.e. injective/surjective) $<==>$ $cal(F)(U) -> cal(G)(U)$ is injective/surjective for all $U in X_et$. The same goes for exact sequences, kernels, cokernels etc. 

  + $cAb(X_et)$ is an abelian category. More precisely, for $f: cal(F) -> cal(G)$, its kernel, cokernel and image may be computed as: 
    $
      ker(f) = (U |-> ker(f_U\: cal(F)(U) -> cal(G)(U))) \

      coker(f) = (U |-> coker(f_U\: cal(F)(U) -> cal(G)(U)))^\# \

      im(f) cong op("coim")(f) = 
      coker(ker(f)) = (U |-> im(f_U\: cal(F)(U) -> cal(G)(U)))^\#
    $
    In other words, the kernel is just the presheaf kernel, while cokernel/image is the sheafification of the presheaf cokernel/image. 

  + For $f: cal(F) -> cal(G)$ in $cAb(X_et)$, $f$ is a monomorphism (injective) $<==>$ $f_U: cal(F)(U) -> cal(G)(U)$ is injective for each $U in X_et$. 
  
    Meanwhile, $f$ is an epimorphism (surjective) $<==>$ for all $U in X_et, s in cal(G)(U)$, there exists an etale cover ${U_i -> U}$ s.t. $s|_(U_i) in im(f_(U_i))$ for all $i$. 

  + To compute limits and colimits in $cAb(X_et)$: 
    $
      lim_(i in I) cal(F)_i = lim_(i in I) iota(cal(F)_i) , colim_(i in I) cal(F)_i = (colim_(i in I) iota(cal(F)_i))^\#
    $
    i.e. limits of sheaves are just their limits as presheaves, while colimits are presheaf colimits sheafified. 

  + $cAb(X_et)$ has enough injectives. 

  0. $(-)^\#: cPAb(X_et) -> cAb(X_et)$, the sheafification functor, is exact. 

//   #remark[
//   All of (1)-(4) continue to hold for any site $cal(C)$, while (3) holds for $cSh(X_et), cSh(X_et)$. 
// ]
]
#proof[
  (0) Suppose that we have established (1), that $cAb(X_et)$ is an abelian category. Then we have shown that sheafification commutes with finite limits (hence left exact), and is a left adjoint (hence right exact), so it is exact. 

  (1) For the kernel, the forgetful functor $iota: cAb(X_et) -> cPAb(X_et)$ is a right adjoint and preserves all limits. In particular, it preserves kernels, and so the kernel in $cPAb$ is simply the kernel in $cAb$. 

  For the cokernel, let $cal(F) ->^f cal(G) -> cal(P)$ be the cokernel in $cPAb$, and we need to show that $cal(P)^\#$ is the cokernel in $cAb$. Indeed, since the composition $cal(F) ->^f cal(G) -> cal(P)$ is already zero, $cal(F) ->^f cal(G) -> cal(P)^\#$ is zero. For any $cal(H) in cAb(X_et)$ s.t. $cal(F) ->^f cal(G) ->^g cal(H)$ composes to zero, from the universal property of the presheaf cokernel, $g$ factors as: 
  $
    cal(G) -> cal(P) -> cal(H)
  $
  However since $cal(H)$ is a sheaf, from the adjoint pair involving the sheafification, $g$ further factors into: 
  $
    cal(G) -> cal(P) -> cal(P)^\# -> cal(H)
  $
  and thus factors through $cal(G) -> cal(P)^\#$. Hence $cal(G) -> cal(P)^\#$ is the cokernel of $f$ in $cAb(X_et)$. (Note that this argument is also purely categorical and abstract.)

  To show that $cAb(X_et)$ is an abelian category, and that the image is given by the formula above, all that remains to prove is that the kernel of cokernel is the cokernel of kernel in $cAb(X_et)$. We use a subscript $cPAb$ and $cAb$ to distinguish between the presheaf and sheaf cokernel, and do not distinguish for the kernel (since the kernel is the same for presheaves and sheaves). Then: 
  $
    coker_(cAb)(ker(f)) &= coker_(cPAb) (ker(f))^\# \
    &= ker(coker_(cPAb)(f))^\# #[since $cPAb(X_et)$ is an abelian category] \
    &= ker(coker_(cPAb)(f)^\#) #[since $(-)^\#$ commutes with finite limits] \
    &= ker(coker_(cAb)(f))
  $
  The formula for image is then obtained as the cokernel of kernel. 

  (2) follows from the formulas in (1). 

  (3) Since $iota: cAb(X_et) -> cPAb(X_et)$ is a right adjoint, it commutes with all limits, and so limits in $cAb$ may be computed in $cPAb$. For colimits, we use a similar abstract proof showing that the sheaf cokernel is the presheaf cokernel sheafified. 

  Given any diagram $cal(F): I -> cAb(X_et)$ and any morphism from the diagram $cal(F)$ to an object $cal(G) in cAb(X_et)$, there is a unique morphism $colim_(i in I) iota(cal(F)_i) -> iota(cal(G))$, by sending the diagram via $iota$ into $cPAb(X_et)$. By adjunction, there is a unique morphism $(colim_(i in I) iota(cal(F)_i))^\# -> cal(G)$. Hence by definition, 
  $
    (colim_(i in I) iota(cal(F)_i))^\# = colim_(i in I) cal(F)_i
  $

  (4) 
  #remark[
    To show that the category of etale sheaves has enough injectives, there are at least two routes: 

    + Use @cite-grothendieck-tohoku to obtain injectives abstractly;

    + Use the Godement resolution. 

    The Godement resolution, option (2), has the advantage of being an explicit construction that is explicitly functorial. However, it requires defining stalks of etale sheaves on geometric points. We will thus introduce it in a later section. 
    
    Meanwhile, albeit being abstract, (1) is in fact also a functorial construction, and has the advantage of working on not only the etale site, but also sites like fppf, fpqc and crystalline#footnote[...whatever that means.] sites, in which there are not enough points. We are going with (1) for now, and discuss (2) when we introduce stalks. 
  ]

  We use the following theorem from @cite-grothendieck-tohoku:
  #theorem[
    Suppose that $cal(A)$ is an abelian category satisfying: 

    + (Ab5) condition: $cal(A)$ has arbitrary coproducts, and filtered colimits are exact. 

    + $cal(A)$ has a generator $G$, i.e. there exists an object $G in cal(A)$ s.t. $Hom(G, -): cal(A) -> cAb$ is faithful. 

    Then $cal(A)$ has enough injective objects, and in fact has functorial injective resolutions. 
  ]

  We thus need to show that $cAb(X_et)$ satisfies (Ab5) and has a generator. 

  (Ab5): 
  #proof[
    Arbitrary direct sums of sheaves may be formed section-wise. Furthermore, $cPAb(X_et)$ satisfies (Ab5), as checked section-wise (and thus passed to $cAb$). 

    Suppose that ${0 -> cal(F)_i -> cal(G)_i -> cal(H)_i -> 0}_i$ is a directed system of exact sequences in $cAb(X_et)$. Since the functor $iota$ is left exact, we have left exact sequences: 
    $
      0 -> iota(cal(F)_i) -> iota(cal(G)_i) -> iota(cal(H)_i) 
    $
    in $cPAb(X_et)$. Taking a cokernel, we may extend to a four-term exact sequence: 
    $
      0 -> iota(cal(F)_i) -> iota(cal(G)_i) -> iota(cal(H)_i) -> cal(R)_i -> 0
    $
    Next, we sheafify this sequence. Since the sheafification functor $(-)^\#$ is exact, we obtain an exact sequence: 
    $
      0 -> cal(F)_i -> cal(G)_i -> cal(H)_i -> cal(R)_i^\# ->  0
    $
    and so $cal(R)_i^\# = 0$ for each $i$. 

    Next, we take the directed colimit of the sequence $0 -> iota(cal(F)_i) -> iota(cal(G)_i) -> iota(cal(H)_i) -> cal(R)_i -> 0$ and use (Ab5) for $cPAb(X_et)$ to obtain an exact sequence: 
    $
      0 -> dircolim_i iota(cal(F)_i) -> dircolim_i iota(cal(G)_i) -> dircolim_i iota(cal(H)_i) -> dircolim_i cal(R)_i -> 0
    $
    Taking the sheafification (which is exact) and using the characterization $dircolim_i cal(F)_i = (dircolim_i iota(cal(F)_i))^\#$, we get an exact sequence: 
    $
      0 -> dircolim_i cal(F)_i -> dircolim_i cal(G)_i -> dircolim_i cal(H)_i -> (dircolim_i cal(R)_i)^\# -> 0
    $
    Since sheafification is a left adjoint, it preserves all colimits, hence $(dircolim_i cal(R)_i)^\# = dircolim_i cal(R)_i^\# = 0$ (as each $cal(R)_i^\# = 0$). We thus obtain the exact sequence $0 -> dircolim_i cal(F)_i -> dircolim_i cal(G)_i -> dircolim_i cal(H)_i -> 0$. 
    #suppress-qed
  ]

  Existence of generator: 
  #proof[
    We would like to take the generator $G = oplus.big_(U in Et_X) ul(ZZ)_(!,U)$. However this doesn't work due to set-theoretic difficulties: 

    - When we talk about sets, schemes etc, we have an ambient fixed Grothendieck universe $cal(U)$, and we are really talking about $cal(U)$-sets and $cal(U)$-schemes (schemes where the involved structures are sets in $cal(U)$). A direct sum thus must be indexed by a $cal(U)$-set, but in general $Et_X$, the category of $cal(U)$-schemes etale over $X$, may contain schemes that are disjoint unions of etale schemes over $X$ indexed by any $cal(U)$-set, and has the same cardinality as $cal(U)$. 

    Instead, we take a basis of the etale topology on $X$. Let $X$ be covered by affine opens ${Spec(A_i)}_(i in I)$, where $I$ is a $cal(U)$-set, and each $A_i$ is a $cal(U)$-ring. Let $cal(S)_i$ be the set of isomorphism classes of etale $A_i$-algebras. Since etale $A_i$-algebras are finite type over $A_i$, they are isomorphic to quotients of $A_i [x_1, dots.c, x_k]$ for some $k$, and so there are at most $max(aleph_0, abs(A_i))$ isomorphism classes of them. As such, each $cal(S)_i$ is a $cal(U)$-set, and so the disjoint union $cal(S) = union.sq.big_(i in I) cal(S)_i$ is a $cal(U)$-set. 

    We claim that a morphism $f: cal(F) -> cal(G)$ in $cAb(X_et)$ vanishes if it vanishes on sections on the etale opens $Spec(B_i) -> Spec(A_i) -> X$ for every $B_i in cal(S)_i$ and every $i$. Indeed, for any $U in Et_X$, we may cover $U$ by affine opens whose image in $X$ is contained in one of the $Spec(A_i)$'s, i.e. $U = union.big_(i,j) Spec(C_(i,j))$ where $C_(i,j)$ is (isomorphic to a ring) in $cal(S)_i$. Since $f$ vanishes on sections on each $C_(i,j)$, by the sheaf conditions, $f$ vanishes on sections on $U$. Thus $f = 0$. 

    In other words, the following direct sum indexed over a $cal(U)$-set $cal(S)$: 
    $
      G = oplus.big_(B_i in cal(S)) ul(ZZ)_(!,Spec(B_i))
    $
    has the property that $Hom(G, -): cAb(X_et) -> cAb$ is faithful, and is hence a generator. 

    #suppress-qed
  ]

  By invoking @cite-grothendieck-tohoku, we see that $cAb(X_et)$ has enough injectives.

  // (2) One may check directly that $ker(f), coker(f)$ are given by the formulas. To see that $cAb(X_et)$ is an abelian category, it suffices to prove that: 
  // $
  //   coker(ker(f) -> cal(F)) = op("coim")(f) -> im(f) = ker(cal(G) -> coker(f))
  // $
  // is an isomorphism. That is, 
  // $
  //   (im^(cPSh(X_et)) (f))^\# -> ker(cal(G) -> coker(f))
  // $
  // is an isomorphism. Consider the diagram in $cPAb(X_et)$: 
  // // https://q.uiver.app/#r=typst&q=WzAsMTAsWzAsMCwiMCJdLFs0LDAsIjAiXSxbMSwwLCJpbV4oY1BTaCkoZikiXSxbMiwwLCJjYWwoRykiXSxbMywwLCJjb2tlcl4oY1BTaCkgKGYpIl0sWzAsMSwiMCJdLFsxLDEsIihpbV4oY1BTaCkoZikpXlxcIyJdLFsyLDEsImNhbChHKV5cXCMiXSxbMywxLCIoY29rZXJeKGNQU2gpIChmKSleXFwjIl0sWzQsMSwiMCJdLFswLDJdLFsyLDNdLFszLDRdLFs0LDFdLFs1LDZdLFs2LDddLFs3LDhdLFs4LDldLFsyLDYsIiIsMSx7InN0eWxlIjp7InRhaWwiOnsibmFtZSI6Imhvb2siLCJzaWRlIjoiYm90dG9tIn19fV0sWzMsNywidGlsZGUiLDFdLFs0LDhdXQ==
  // #context align(center, diagram({
  //   node((-2, -1), [$0$])
  //   node((2, -1), [$0$])
  //   node((-1, -1), [$im^(cPSh)(f)$])
  //   node((0, -1), [$cal(G)$])
  //   node((1, -1), [$coker^(cPSh) (f)$])
  //   node((-2, 0), [$0$])
  //   node((-1, 0), [$(im^(cPSh)(f))^\#$])
  //   node((0, 0), [$cal(G)^\#$])
  //   node((1, 0), [$(coker^(cPSh) (f))^\#$])
  //   node((2, 0), [$0$])
  //   edge((-2, -1), (-1, -1), "->")
  //   edge((-1, -1), (0, -1), "->")
  //   edge((0, -1), (1, -1), "->")
  //   edge((1, -1), (2, -1), "->")
  //   edge((-2, 0), (-1, 0), "->")
  //   edge((-1, 0), (0, 0), "->")
  //   edge((0, 0), (1, 0), "->")
  //   edge((1, 0), (2, 0), "->")
  //   edge((-1, -1), (-1, 0), "hook'->")
  //   edge((0, -1), (0, 0), [$tilde$], label-side: center, "->")
  //   edge((1, -1), (1, 0), "->")
  // }, crossing-fill: thm-box-curr-color()))
  // The first row is exact is $cPAb(X_et)$, and the first vertical arrow is injective since $im^(cPSh)(f)$ is separated. It is left as an exercise to prove that the second row is exact in $cPAb(X_et)$. 

  // That $cPAb(X_et), cAb(X_et)$ have enough injectives is due to the following theorem by Grothendieck: 
  // #theorem[
  //   (Grothendieck in Touhoku) If $cal(C)$ is an abelian category satisfying the (Ab5) axiom having a family of generators, then $cal(C)$ has enough injectives. 
  // ]

  // - We'll just accept that $cPAb(X_et), cAb(X_et)$ satisfies (Ab5). We won't explain what (Ab5) means. 

  // - $(ZZ_V^\#)_(V in X_et)$ form a family of generators for $cAb(X_et)$. That is to say, given $cal(F) subset.neq cal(G)$, we may pick $V$ s.t. $cal(F)(V) subset.neq cal(G)(V)$. Then taking $s in cal(G)(V) - cal(F)(V)$ gives a morphism $ZZ_V^\# -> cal(G)$ not factoring through $cal(F)$. 

  // (3) follows from (2), and (4) is claimed to be easy. 
]

// By (3), for a short exact sequence $0 -> cal(F) -> cal(G) -> cal(H) -> 0$ in $cAb(X_et)$, we have a right exact sequence: 
// $
//   0 -> cal(F)(U) -> cal(G)(U) -> cal(H)(U)
// $
// In particular, the section functor $Gamma(U, -): cAb(X_et) -> cAb$ is left exact. 


#corollary(name: <sections-left-exact>)[
  The section functor $Gamma(U, -): cAb(X_et) -> cAb$, being isomorphic to the hom-functor $Hom(ul(ZZ)_(!,U), -)$, is left exact.
]

#corollary[
  If $cal(F) -> cal(G)$ is injective where $cal(F) in cPAb(X_et), cal(G) in cAb(X_et)$, then $cal(F)^\# -> cal(G)$ induced by adjunction is injective. 
]
#proof[
  This follows from exactness of $(-)^\#$. 
]

After establishing the abelian category $cAb(X_et)$ with enough injectives, and the left exact functor $Gamma(U, -)$, we are finally able to introduce the central object of this course: 

#definition(name: <defn-etale-cohomology>)[
  We define the $n$-th *etale cohomology* functor $H^n (U, -)$ to be the $n$-th right derived functor of the left exact functor $Gamma(U, -): cAb(X_et) -> cAb$. 

  #notation[
    $X in X_et$ is the final object of $Et_X$. We then additionally denote the cohomology of the etale site to be:
    $
      H^n_et (X, -) := H^n (X_et, -) := H^n (X, -): cAb(X_et) -> cAb
    $
  ]
]
