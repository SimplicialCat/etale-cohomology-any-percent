#import "void-import.typ": *

== $Spec(K)_et$

In this short section, we will establish the structure of $cSh(X_et)$ and $cAb(X_et)$ when $X = Spec(K)$ is the spectrum of a field $K$. 

#theorem(name: <struct-of-spec-k-et>)[
  The stalk at $overline(x)$, i.e. $cal(F) |-> cal(F)_(overline(x)) = dirlim_(L\/K #[finite Galois]) cal(F)(Spec(L))$ induces an equivalence of categories: 
  $
    (-)_(ol(x)): cSh(Spec(K)_et) overset(->, tilde) GSet(Gal_K)^("disc,cont"), cAb(Spec(K)_et) overset(->, tilde) AMod(Gal_K)^("disc,cont")
  $
  where the disc,cont superscript means that these $Gal_K$-sets/modules are equipped with the discrete topology s.t. $Gal_K$ acts continuously on them. 
  
  Here, $sigma in Gal_K$ acts on $cal(F)_(overline(x)) = dirlim_(L\/K #[finite Galois]) cal(F)(Spec(L))$, by acting on $cal(F)(Spec(L))$ via restriction along the image of $sigma$ in $Gal(L\/K)$. 
]
#proof[
  We first classify $Et_(Spec(K))$. 

  Let $X -> Spec(K)$ be etale. For any point $x in X$, $k(x)\/K$ is a finite separable field extension by definition of unramifiedness. Pick an affine open $Spec(A) subset X$ around $x$, so $A$ is a finite type $K$-algebra. Since $k(x)\/K$ is finite, $x$ is a closed point of $Spec(A)$. Thus, every point of $Spec(A)$ is a closed point. Hence $A$ is $0$-dimensional noetherian, hence artinian. Thus $Spec(A)$ has only finitely many points, all of which are closed and open. Also by @etale-local-properties (4), $X$ is reduced. 
  
  In summary, 
  $
    X = union.sq.big_(x in X) Spec(k(x))
  $
  in which every $k(x)\/K$ is a finite separable extension. Conversely, every scheme of this shape is etale over $Spec(K)$, so we have classified $Et_(Spec(K))$. 

  To show that $(-)_(ol(x)): cSh(Spec(K)_et) -> GSet(Gal_K)^("disc,cont")$ is an equivalence, we directly construct its quasi-inverse: 
  $
    Phi: GSet(Gal_K)^#[disc,cont] -> cSh(Spec(K)_et), M |-> (Phi(M): union.sq.big_i Spec(L_i) |-> union.sq.big_i M^(Gal_L))
  $

  To show that $Phi_M$ is a sheaf, since it respects disjoint unions, it suffices to verify the sheaf conditions on every ${Spec(L) -> Spec(K)}$. If $N\/L\/K$ is the Galois closure of $L\/K$, then we have a refinement $Spec(N) -> Spec(K)$ of $Spec(L) -> Spec(K)$. 

  By nine lemma diagram tracing like in the proof of @etale-cover-equiv-conds, it suffices to verify the sheaf conditions for those $N\/K$. Now: 
  $
    N otimes_K N = product_(sigma in Gal(N\/K)) N
  $
  Let the factor corresponding to $sigma$ be denoted $N_sigma$. Then the two projections: 
  $
    p_(1,2): N otimes_K N -> N
  $
  have $p_1$ sending $N_sigma -> N$ by the identity, and $p_2$ sending $N_sigma -> N$ by $sigma$. Hence, 
  $
    ker(M^(Gal_N) -> product_(sigma in Gal(N\/K)) M^(Gal_N)) = inter.big_(sigma in Gal(N\/K)) (M^(Gal_N))^sigma = M^(Gal_K)
  $
  Hence, the sheaf conditions are verified for $Phi(M)$. It now remains to show that $Phi$ and $(-)_(ol(x))$ are quasi-inverses: 

  - #h(1fr)
    $
      (Phi(M))_(ol(x)) = dirlim_(L\/K #[finite separable]) M^(Gal_L) = M
    $
    since every element of $M$ is fixed by some $Gal_L$ for some finite separable $L\/K$. 

  - By the sheaf conditions, for any $cal(F) in cSh(Spec(K)_et)$, $cal(F)$ is determined by the $cal(F)(Spec(L))$'s. Furthermore, for a Galois extension $N\/L$, $cal(F)(Spec(L)) = cal(F)(Spec(N))^(Gal(N\/L))$. In particular $cal(F)(Spec(L)) -> cal(F)(Spec(N))$ is injective. By taking Galois closures, $cal(F)$ has injective restriction maps. Now consider: 
    $
      M = cal(F)_(ol(x)) = dirlim_(L\/K #[finite separable]) cal(F)(Spec(L))
    $
    Since all restriction maps are injective, we may regard $cal(F)(Spec(L)) subset M$ as subsets. Now for a fixed finite separable $T\/K$: 
    $
      M^(Gal_T) &= union.big_(L\/T #[finite separable]) cal(F)(Spec(L))^(Gal_T) = union.big_(L\/T #[finite Galois]) cal(F)(Spec(L))^(Gal_T) \
      &= union.big_(L\/T #[finite Galois]) cal(F)(Spec(L))^(Gal(L\/T)) = cal(F)(Spec(T))
    $
    We are thereby done showing $cal(F) cong Phi(M)$. 

  We are thus done with the sheaf of sets case. For abelian group, the quasi-inverse is given by: 
  $
    Phi: AMod(Gal_K)^#[disc,cont] -> cAb(Spec(K)_et), M |-> (Phi(M): union.sq.big_i Spec(L_i) |-> product_i M^(Gal_(L_i)))
  $
  and the arguments work identically. 
]

#corollary[
  We have a commutative diagram of categories: 
  // https://q.uiver.app/#r=typst&q=WzAsMyxbMCwwLCJjQWIoU3BlYyhLKV9ldCkiXSxbMiwwLCJHTW9kKEcpXlwiZGlzYyxjb250XCIiXSxbMSwyLCJjQWIiXSxbMCwyLCJHYW1tYShTcGVjKEspLCAtKSIsMl0sWzEsMiwiVCB8LT4gVF5HIl0sWzAsMSwidGlsZGUiXV0=
  #align(center, diagram({
    node((-1, -1), [$cAb(Spec(K)_et)$])
    node((1, -1), [$AMod(G)^"disc,cont"$])
    node((0, 0), [$cAb$])
    edge((-1, -1), (0, 0), [$Gamma(Spec(K), -)$], label-side: right, "->")
    edge((1, -1), (0, 0), [$T |-> T^G$], label-side: left, "->")
    edge((-1, -1), (1, -1), [$tilde$], label-side: left, "->")
  }))

  Hence an isomorphism of $delta$-functors: 
  $
    H^q_et (Spec(K), cal(F)) cong H^q_"cont" (G, cal(F)_(overline(x)))// =: H^q (K, cal(F)_(overline(x)))
  $
  // where $H^n (K, cal(F)_(overline(x)))$ is called Galois cohomology. Here, $H^n_"cont"$ denotes the continuous group cohomology. 
  between etale cohomology and continuous group cohomology. 
]

From facts on etale cohomology, we may derive facts on continuous Galois cohomology: 

#corollary(name: <galois-cohom-props>)[
  0. /*Recall that for $M in AMod(G)^"disc,cont"$, we have: 
    $
      M = union.big_(K^sep\/L\/K "fin") M^(Gal(K^sep\/L))
    $
    Thus, we have an*/ There is a natural isomorphism for any discrete $Gal_K$-module $M$: #h(1fr)
    $
      H^q (Gal_K, M) cong dirlim_(L\/K #[finite Galois]) H^q (Gal(L\/K), M^(Gal(K^sep\/L)))
    $
  
  + (Limit formulas)
    + For a $G$-stable colimit $M = colim_i M_i$, there is an isomorphism: 
      $
        colim_i H^q_"cont" (G, M_i) overset(->, tilde) H^q_"cont" (G, M)
      $

    + For a separable algebraic extension $K\/K_0$, $Gal_K$ is a closed subgroup of $Gal_(K_0) = Gal(K^sep\/K_0)$, and for $N in AMod(Gal(K^sep\/K_0))$, we have: 
      $
        colim_(K\/K_i\/K_0 \ K_i\/K_0 #[finite]) H^q_"cont" (Gal(K^sep\/K_i), N) overset(->, tilde) H^q_"cont" (Gal_K, N)
      $
  
  + (Hilbert 90) #h(1fr)
  
    // $G = Gal(K^sep\/K)$ acts on $(K^sep)^times, K^sep$, and: 
    // + (Hilbert 90) $H^1_"cont" (G, (K^sep)^times) = 0$ and $H^2_"cont" (G, (K^sep)^times) = "Br"(K)$ the (absolute) Brauer group. 

    // + 
    //   $
    //   H^n_"cont" (G, K^sep) = cases(K &\, n = 0 , 0 &\, n >= 1)
    //   $

    + (Additive Hilbert 90 / Cohomology of $GG_a = cal(O)_(Spec(K),et)$) #h(1fr)
      $
        H^q_#[cont] (Gal_K, K^sep) = 0, forall q >= 1
      $

    + (Multiplicative Hilbert 90 / $H^1$ of $GG_m$)
      $
        H^1_#[cont] (Gal_K, (K^sep)^times) = 0// = Pic(Spec(K)) = 0
      $
      // (as it is $H^1_et (Spec(K), GG_m) = Pic(Spec(K)) = 0$)

  + ($H^1$ of constant sheaf) If $G$ acts on $M$ trivially, then: 
    $
      H^1_"cont" (Gal_K, M) = Hom_"cont" (Gal_K, M)
    $
]

// In the next section, we will discuss generalization of (1)(2)(3). 
