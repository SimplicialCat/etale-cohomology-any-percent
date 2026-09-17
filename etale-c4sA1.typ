#import "void-import.typ": *

== Derived category statements

The notion of derived categories is an abstract mechanism, that makes the notion of derived functors more natural. Derived categories are, in some sense, the natural categories in which derived functors belong. 

In later sections and onwards, we will cover: 

- Proper base change
- Push forward with proper support
- Local acyclicity
- Projection formula and Kunneth formula
- Poincare duality

They all make extensive and sometimes essential use of the derived category in their statements. As such, a brief introduction to the derived category, alongside translations of some of our previous results in this chapter into derived statements, is unavoidable. Such is the role of this interlude section. 

We won't construct homotopy and derived categories, abstract triangulated categories, derived functors and t-structures. We invite the reader to read standard material on the definition of derived categories and derived functors, such as: 

- Chapter I of @cite-hartshorne-rd;
- Chapter 10 of @cite-Wei94;
- Chapter I of @cite-Lip60.

We will mostly give soft discussions on necessary constructions for the translation, instead of stating long rigorous proofs. 

However, there is an important lemma that we will constantly use, and thus state right now: 

#definition(name: <defn-cohomological-dimension>)[
  A triangulated functor $F: cal(D) -> cal(C)$ between two triangulated categories with t-structures is called: 

  - *bounded above*, if there exists $m$ s.t. $F(cal(D)_(<=n)) subset cal(C)_(<=n+m)$; 

  - *bounded below*, if there exists $m$ s.t. $F(cal(D)_(>=n)) subset cal(C)_(>=n-m)$. 

  In these cases, the *cohomological dimension above/below* of $F$ is defined as the smallest integer $m$ satisfying these properties. 
]

#lemma[
  (Way-out lemma) Let $cal(A), cal(B)$ be two abelian categories, $cal(A)'$ a thick subcategory of $cal(A)$, and let $D^bullet_(cal(A)') (cal(A))$ be the triangulated subcategory of $D^bullet (cal(A))$ consisting of complexes whose cohomologies are objects of $cal(A)'$, where $bullet in {#`blank`, +, -, b}$. Suppose that we have two triangulated functors: 
  $
    F, G: D^bullet_(cal(A)') (cal(A)) -> D(cal(B))
  $
  and a natural transformation $eta: F -> G$. Suppose that $eta_X: F(X) -> G(X)$ is an isomorphism for all objects $X in cal(A)'$ regarded as an object of $D^bullet_(cal(A)') (cal(A))$, and one of the following holds: 

  + $bullet = b$; 
  + $bullet = +$ and $F,G$ are bounded below; 
  + $bullet = -$ and $F,G$ are bounded above; 
  + $bullet = #`blank`$ and $F,G$ are bounded above and below. 

  Then $eta$ is a natural isomorphism. 
]

We begin by defining the derived categories of etale sheaves. 

#notation(name: <derived-categories-of-etale-sheaves>)[
  Let $Lambda$ be a ring. Then the category $cAb(X_et, Lambda)$ of etale sheaves of $Lambda$-modules is a Grothendieck category, i.e. an abelian category with (Ab5) and a generator. 

  In @ab-x-et-the-abelian-cat, we have shown that $cAb(X_et)$ has (Ab5) and a generator $G$. 
  
  - Since the forgetful functor $cAb(X_et, Lambda) -> cAb(X_et)$ is exact and conservative (which really just says that a sequence of sheaves of $Lambda$-modules is exact if and only if it is exact as a sequence of abelian sheaves), $cAb(X_et, Lambda)$ has (Ab5). 
  
  - Take a generator $G$ of $cAb(X_et)$, and by hom-tensor adjunction: 
    $
      Hom_Lambda (G otimes_ZZ Lambda, -) = Hom_ZZ (G, -): cAb(X_et, Lambda) -> cAb
    $
    is faithful since $G$ is a generator of $cAb(X_et, Lambda)$. Thus $G otimes_ZZ Lambda$ is a generator of $cAb(X_et, Lambda)$. 
  
  Thus $cAb(X_et, Lambda)$ is indeed a Grothendieck category. 

  We define the triangulated categories: 

  - $D^bullet (X_et, Lambda)$ for $bullet in {#`blank`, -, +, b}$, as the derived category of $cAb(X_et, Lambda)$ consisting of all/bounded above/bounded below/bounded complexes, respectively. 

  The torsion sheaves give rise to a thick subcategory of $cAb(X_et, Lambda)$. Given an extension of sheaves: 
  $
    cal(F) -> cal(G) -> cal(H)
  $
  we see that if $cal(F)$ and $cal(H)$ are torsion, then so is $cal(G)$ by @torsion-sheaves-first-props (3). 

  Thus, $cAb_#[tor] (X_et, Lambda)$, consisting of all torsion sheaves in $cAb(X_et, Lambda)$, defines a thick subcategory of $cAb(X_et, Lambda)$: 

  Thus, $D^bullet_#[tor] (X_et, Lambda)$ are triangulated subcategories of $D^bullet (X_et, Lambda)$ for $bullet in {#`blank`, -, +, b}$. 

  Recall that we have argued that $cAb(X_et, Lambda)$ is a Grothendieck category. Thus, every complex in the unbounded derived category $D(X_et, Lambda)$ admits a quasi-isomorphism to a K-injective complex of injective objects. (See #cite-stacks("079P", [Theorem 19.12.6]).) This allows right derived functors of any left exact functor from $cAb(X_et, Lambda)$ to be defined, not only on the bounded below derived category $D^+ (X_et, Lambda)$, but also on the unbounded derived category $D(X_et, Lambda)$.#footnote[This generalization is essential when we eventually state the projection and Kunneth formula, which involves a (right) derived push forward together with a (left) derived tensor. The tensor is defined for $D^-$, so it is absolutely necessary that we are able to apply a right derived functor to a complex in $D^-$.]

  /*We thus have functors: 
  $
    R Gamma(U, -): D(X_et, Lambda) -> D(Lambda) \
    R f_*: D(X_et, Lambda) -> D(Y_et, Lambda) \
    RHom_Lambda (-, -): D(X_et, Lambda)^opp times D(X_et, Lambda) -> D(Lambda) \
    RHHom_Lambda (-, -): D(X_et, Lambda)^opp times D(X_et, Lambda) -> D(X_et, Lambda)
  $
  obtained as derived functors. 

  There is one functor that needs to be left derived: the tensor product. The category of sheaves do not have enough projectives, but it does have enough flat objects (see @flat-resolution-of-et-sheaf). This allows a left derived tensor product to be derived on the bounded above derived category: 
  $
    - Lotimes_Lambda -: D^- (X_et, Lambda) times D^- (X_et, Lambda) -> D^- (X_et, Lambda)
  $
  To define it on the unbounded derived category, one need to use K-flat complexes, complexes whose tensor product with an exact complex remain exact. The existence of K-flat resolutions is due to #cite-stacks("06YS")[Lemma 21.17.11]. */
]

/*
To proceed, we make one more general abstract remark: 
#remark[
  One extra abstract construction that we will make frequent use of is the translation of the Grothendieck-Leray spectral sequence. Recall for left exact functors: 
  $
    cal(A) ->^F cal(B) ->^G cal(C)
  $
  between abelian categories in which $cal(A)$ and $cal(B)$ has enough injectives, s.t. $F$ sends injectives in $cal(A)$ to $G$-acyclics in $cal(B)$. Then the Grothendieck-Leray spectral sequence gives a natural spectral sequence: 
  $
    E_2^(p,q) = R^p G (R^q F (X)) ==> R^(p+q) (G compose F) (X)
  $
  In the derived category, the statement has a much cleaner form. It is just: 
  $
    R G compose R F cong R (G compose F): D^+ (cal(A)) -> D^+ (cal(C))
  $
  Now assuming that $cal(A), cal(B)$ are Grothendieck categories, so that every complex in $D(cal(A)), D(cal(B))$ may be (functorially) resolved by a K-injective complex, and so right derived functors are defined on the unbounded derived categories. In this case, that $F$ sends injectives to $G$-acyclics is no longer enough to guarantee: 
  $
    R G compose R F cong R (G compose F): D(cal(A)) -> D(cal(C))
  $
  Instead, it is required that applying $F$ termwise sends K-injective complexes to K-$G$-acyclic complexes. 

  The case that is most important to our study is the case that $F$ has an exact left adjoint $L$. In that case, for any K-injective complex $M^bullet in K(cal(A))$, any exact complex $N^bullet in K(cal(B))$: 
  $
    Hom_(K(cal(B))) (N^bullet, F(M^bullet)) = Hom_(K(cal(A))) (L(N^bullet), M^bullet) = 0
  $
  since $L(N^bullet)$ is exact by exactness of $L$ and $N^bullet$, and $M^bullet$ is K-injective. Thus $F(M^bullet)$ is K-injective, and so $F$ preserves K-injective complexes. 
]*/

We now start by translating results from @sect-ab-x-et-as-abelian-cat, @sect-functoriality-of-etale-topos, @sect-open-closed and @sect-hom-tensor, regarding the various functors that we have constructed. 

#properties(name: <derived-functoriality-etale>)[
  (Derived functoriality of etale topos)

  Let $X, Y, Z$ denote schemes and $f: X -> Y, g: Y -> Z$ denote scheme morphisms. Let $Lambda$ denote a coefficient ring. Then: 

  + (Functoriality) There are triangulated functors: #h(1fr)
    $
      R f_*: D(X_et, Lambda) -> D(Y_et, Lambda) \
      f^(-1): D(Y_et, Lambda) -> D(X_et, Lambda) \
      - Lotimes_Lambda -: D(X_et, Lambda) times D(X_et, Lambda) -> D(X_et, Lambda) \
      RHom_Lambda (-, -): D(X_et, Lambda)^opp times D(X_et, Lambda) -> D(Lambda) \
      RHHom_Lambda (-, -): D(X_et, Lambda)^opp times D(X_et, Lambda) -> D(X_et, Lambda) \
      R Gamma(U, -): D(X_et, Lambda) -> D(Lambda), forall U in Et_X
    $
    in which $f^(-1)$ is applied termwise, $Lotimes_Lambda$ is the left derived functor of $otimes_Lambda$ (and is symmetric monoidal), and the rest are right derived functors. 

    For $j: U -> X$ etale and $i: Z -> X$ closed immersion, there are also triangulated functors: 
    $
      j_!: D(U_et, Lambda) -> D(X_et, Lambda) \
      R i^!: D(X_et, Lambda) -> D(Z_et, Lambda)
    $
    where $j_!$ is applied termwise and $R i^!$ is right derived. 

  + (Adjunctions) These functors enjoy adjunctions: 

    + #h(1fr)
      $
        f^(-1) tack.l R f_*
      $
    
    + For $j$ etale and $i$ closed immersion: 
      $
        j_! tack.l j^(-1) \
        i_* tack.l R i^!
      $

    + (hom-tensor duality) For all $cal(K) in D(X_et, Lambda)$: 
      $
        - Lotimes_Lambda cal(K) tack.l RHHom_Lambda (cal(K), -) 
      $

  + (Internal adjunctions) There are canonical quasi-isomorphisms: 

    + #h(1fr)
      $
        RHHom_Lambda (cal(K), R f_* cal(L)) ->^tilde R f_* RHHom_Lambda (f^(-1) cal(K), cal(L))
      $

    + 
      $
        RHHom_Lambda (cal(K) Lotimes_Lambda cal(L), cal(M)) ->^tilde RHHom_Lambda (cal(K), RHHom_Lambda (cal(L), cal(M)))
      $

    + For $j: U -> X$ etale, $i: Z -> X$ closed immersion: 
      $
        RHHom_Lambda (j_! cal(K), cal(L)) ->^tilde R j_* RHHom_Lambda (cal(K), j^(-1) cal(L)) \

        RHHom_Lambda (i_* cal(K), cal(L)) ->^tilde i_* RHHom_Lambda (cal(K), R i^! cal(L))
      $
    
    All these quasi-isomorphisms hold whenever the outermost $RHHom_Lambda$ (or $R f_* RHHom_Lambda$) is replaced by $RHom_Lambda$. 

  + (Monoidal identities) There are canonical quasi-isomorphisms: 

    + ($f^(-1)$ is monoidal) #h(1fr)
      $
        f^(-1) cal(K) Lotimes_Lambda f^(-1) cal(L) ->^tilde f^(-1) (cal(K) Lotimes_Lambda cal(L))
      $

    + (Projection formula) If $f$ is etale,
      $
        f_! (f^(-1) cal(L) Lotimes_Lambda cal(K)) ->^tilde cal(L) Lotimes_Lambda f_! cal(K)
      $

  + (Composition of derived functors)
    
    + (Leray spectral sequence) #h(1fr)
      $
        R g_* compose R f_* cong R(g compose f)_*
      $
      For $V in Et_Y$, 
      $
        R Gamma(V, R f_* (-)) cong R Gamma(V times_Y X, -)
      $

    + 
      $
        f^(-1) compose g^(-1) cong (g compose f)^(-1)
      $

    + For $U ->^j V ->^f X$ etale morphisms, $W ->^i Z ->^k X$ closed immersions, 
      $
        (f compose j)_! = f_! compose j_!, R(k compose i)^! = R i^! compose R k^!
      $
    
    + On $D(X_et)$, 
      $
        RHom_Lambda (-, -) cong R Gamma(X, RHHom_Lambda (-, -))
      $

  + (Open-closed triangle) For a closed immersion $i: Z -> X$ and a complementary open immersion $j: U -> X$, there are canonical distinguished triangles: 
    + (Extension by zero triangle) #h(1fr)
      $
        j_! j^(-1) cal(K) -> cal(K) -> i_* i^(-1) cal(K) ->^(+1) \
      $
    + (Sections with support triangle) #h(1fr)
      $
        i_* R i^! cal(K) -> cal(K) -> R j_* j^(-1) cal(K) ->^(+1)
      $
]
#proof[
  (1) Among these functors, $R f_*, RHom_Lambda, RHHom_Lambda, R Gamma(U, -), R i^!$ can be defined as right derived functors using K-injective resolutions, as we have discussed. $j_!$ and $f^(-1)$ are exact and so can be applied termwise. The only functor requiring some explanation is $Lotimes_Lambda$. For this, we need to show that every possibly unbounded complex in $D(X_et, Lambda)$ can be replaced by a K-flat complex. This is done through a limit with its bounded above truncations, see: #cite-stacks("06YS")[Lemma 21.17.11], which tells us that every complex in $D(X_et, Lambda)$ admits a termwise surjective quasi-isomorphism from a K-flat complex consisting of flat objects. 

  (2) The adjunctions follow from their respective counterparts on abelian categories, namely: 

  - $f^(-1) tack.l f_*$: @pullback-first-props (1); 
  - $j_! tack.l j^(-1)$: @etale-lower-shriek-first-props (1); 
  - $i_* tack.l i^!$: @closed-immersion-upper-shriek-first-props (1); 
  // - hom-tensor: @hom-tensor-first-props (1); 

  together with an abstract result on how derived functors interact with adjoints: #cite-stacks("09T5")[Lemma 13.30.3]. 

  For hom-tensor, we need to be slightly more careful. 

  #lemma(name: <hhom-from-kflat-to-kinj-is-kinj>)[
    Let $cal(P) in K(X_et, Lambda)$ be K-flat and $cal(I) in K(X_et, Lambda)$ be K-injective. Then $RHHom_Lambda (cal(P), cal(I)) in K(X_et, Lambda)$ is K-injective. 
  ]
  #proof[
    Let $cal(K) in K(X_et, Lambda)$ be any exact complex. Now: 
    $
      Hom_K (cal(K), RHHom_Lambda (cal(P), cal(I))) = Hom_K (cal(K) otimes_Lambda cal(P), cal(I)) = 0
    $
    where $cal(K) otimes_Lambda cal(P)$ is exact since $cal(K)$ is exact and $cal(P)$ is K-flat, and the last hom is zero since $cal(I)$ is K-injective. 
  ]

  Now to show that: 
  $
    Hom_D (cal(K) Lotimes_Lambda cal(L), cal(M)) = Hom_D (cal(K), RHHom_Lambda (cal(L), cal(M)))
  $
  we replace $cal(L)$ with a quasi-isomorphic K-flat complex $cal(P)$, and $cal(M)$ with a quasi-isomorphic K-injective complex $cal(I)$. We thus need to show: 
  $
    Hom_D (cal(K) otimes_Lambda cal(P), cal(I)) = Hom_D (cal(K), HHom_Lambda (cal(P), cal(I)))
  $
  However, $cal(I)$ and $HHom_Lambda (cal(P), cal(I))$ are both K-injective by the previous lemma, and $Hom_D (-, cal(I)) = Hom_K (-, cal(I))$ for K-injective $cal(I)$. Thus it suffices to prove: 
  $
    Hom_K (cal(K) otimes_Lambda cal(P), cal(I)) = Hom_K (cal(K), HHom_Lambda (cal(P), cal(I)))
  $
  However, this just follows from hom-tensor duality. 

  (5)
  #remark[
    Recall for left exact functors: 
    $
      cal(A) ->^F cal(B) ->^G cal(C)
    $
    between abelian categories in which $cal(A)$ and $cal(B)$ has enough injectives, s.t. $F$ sends injectives in $cal(A)$ to $G$-acyclics in $cal(B)$. Then the Grothendieck-Leray spectral sequence gives a natural spectral sequence: 
    $
      E_2^(p,q) = R^p G (R^q F (X)) ==> R^(p+q) (G compose F) (X)
    $
    In the derived category, the statement has a much cleaner form. It is just: 
    $
      R G compose R F cong R (G compose F): D^+ (cal(A)) -> D^+ (cal(C))
    $
    Now assuming that $cal(A), cal(B)$ are Grothendieck categories, so that every complex in $D(cal(A)), D(cal(B))$ may be (functorially) resolved by a K-injective complex, and so right derived functors are defined on the unbounded derived categories. In this case, that $F$ sends injectives to $G$-acyclics is no longer enough to guarantee: 
    $
      R G compose R F cong R (G compose F): D(cal(A)) -> D(cal(C))
    $
    Instead, it is required that applying $F$ termwise sends K-injective complexes to K-$G$-acyclic complexes. 

    The case that is most important to our study is the case that $F$ has an exact left adjoint $L$. In that case, for any K-injective complex $M^bullet in K(cal(A))$, any exact complex $N^bullet in K(cal(B))$: 
    $
      Hom_(K(cal(B))) (N^bullet, F(M^bullet)) = Hom_(K(cal(A))) (L(N^bullet), M^bullet) = 0
    $
    since $L(N^bullet)$ is exact by exactness of $L$ and $N^bullet$, and $M^bullet$ is K-injective. Thus $F(M^bullet)$ is K-injective, and so $F$ preserves K-injective complexes. 
  ]

  The case of this remark applies to most of (5), namely to $f_*$ (with exact left adjoint $f^(-1)$) and $i^!$ (with exact left adjoint $i_*$). The identities in (5) with exact functors are obtained by termwise application. Thus we immediately obtain (5a)(5b)(5c). For (5d), to show that: 
  $
    RHom_Lambda (cal(K), cal(L)) = R Gamma(X, RHHom_Lambda (cal(K), cal(L)))
  $
  we replace $cal(K)$ with a quasi-isomorphic K-flat complex $cal(P)$, and $cal(L)$ with a quasi-isomorphic K-injective complex $cal(I)$. Now: 
  $
    R Gamma(X, RHHom_Lambda (cal(K), cal(L))) &= R Gamma(X, HHom_Lambda (cal(P), cal(I))) \
    &= Gamma(X, HHom_Lambda (cal(P), cal(I))) #[since $HHom_Lambda (cal(P), cal(I))$ is K-injective] \
    &= Hom_Lambda (cal(P), cal(I)) = RHom_Lambda (cal(K), cal(L))
  $

  For (3), we only need to prove the $RHHom$ versions, since the $RHom$ versions follow by applying $R Gamma(X, -)$ and using (5a)(5d). 

  (3b) is proved in the same way as (2c): we replace $cal(L)$ with a quasi-isomorphic K-flat complex $cal(P)$, and $cal(M)$ with a quasi-isomorphic K-injective complex $cal(I)$, and: 
  $
    RHHom_Lambda (cal(K) Lotimes_Lambda cal(L), cal(M)) &= HHom_Lambda (cal(K) otimes_Lambda cal(P), cal(I)) = HHom_Lambda (cal(K), HHom_Lambda (cal(P), cal(I))) \
    &= RHHom_Lambda (cal(K), HHom_Lambda (cal(P), cal(I))) #[since $HHom_Lambda (cal(P), cal(I))$ is K-injective] \
    &= RHHom_Lambda (cal(K), RHHom_Lambda (cal(L), cal(M)))
  $

  For (3a) and (3c), note: 

  #lemma[
    Let $cal(K) -> cal(L)$ be a morphism in $D(X_et, Lambda)$. It is a quasi-isomorphism if and only if, for all $U in Et_X$, 
    $
      R Gamma(U, cal(K)) -> R Gamma(U, cal(L))
    $
    is a quasi-isomorphism. 
  ]
  #proof[
    The forward implication is immediate. Conversely, suppose the displayed morphism is a quasi-isomorphism for all $U$. Pick quasi-isomorphic K-injective resolutions $cal(K) -> cal(I), cal(L) -> cal(J)$. Now $Hom_K (cal(K), cal(J)) = Hom_K (cal(I), cal(J))$ since $cal(J)$ is K-injective, so $cal(K) -> cal(L)$ lifts to a morphism $cal(I) -> cal(J)$. Then the morphisms 
    $
      Gamma(U, cal(I)) -> Gamma(U, cal(J))
    $
    i.e. $h^q (R Gamma(U, cal(I))) ->^tilde h^q (R Gamma(U, cal(J)))$, i.e. $Gamma(U, h^q (cal(I))) ->^tilde Gamma(U, h^q (cal(J)))$. Thus, the morphisms $h^q (cal(I)) -> h^q (cal(J))$ are isomorphisms, i.e. $cal(I) -> cal(J)$ is a quasi-isomorphism. 
  ]
  Note that $R f_*, j_!, R i^!$ and $RHHom$ all commute with etale base change. By (5d), $R Gamma(U, RHHom_Lambda (cal(K), cal(L))) = RHom_Lambda (cal(K)|_U, cal(L)|_U)$. Thus, it suffices to prove the $RHom$ version of (3a)(3c). Now: 
  $
    h^q (RHom_Lambda (cal(K), cal(L))) = Hom_(D(X_et,Lambda)) (cal(K), cal(L)[q])
  $
  so to prove these quasi-isomorphisms, we may replace $RHom_Lambda$ by $Hom_D$. Then we may conclude by (1). 

  (4) is formal from (3). Indeed, for (4a): 
  $
    Hom_D (f^(-1) cal(K) Lotimes_Lambda f^(-1) cal(L), cal(M)) &= Hom_D (f^(-1) cal(K), RHHom(f^(-1) cal(L), cal(M))) \
    &= Hom_D (cal(K), R f_* RHHom(f^(-1) cal(L), cal(M))) \
    &= Hom_D (cal(K), RHHom(cal(L), R f_* cal(M))) #[by (3a)] \
    &= Hom_D (cal(K) Lotimes_Lambda cal(L), R f_* cal(M)) \
    &= Hom_D (f^(-1) (cal(K) Lotimes_Lambda cal(L)), cal(M))
  $

  For (4b): 
  $
    Hom_D (f_! (cal(K) Lotimes_Lambda f^(-1) cal(L)), cal(M)) &= Hom_D (cal(K) Lotimes_Lambda f^(-1) cal(L), f^(-1) cal(M)) \
    &= Hom_D (f^(-1) cal(L), RHHom_Lambda (cal(K), f^(-1) cal(M))) \
    &= Hom_D (cal(L), R f_* RHHom_Lambda (cal(K), f^(-1) cal(M))) \
    &= Hom_D (cal(L), RHHom_Lambda (f_! cal(K), cal(M))) \
    &= Hom_D (f_! cal(K) Lotimes_Lambda cal(L), cal(M))
  $

  (6) For (6a) the extension by zero triangle: 
  $
    j_! j^(-1) cal(K) -> cal(K) -> i_* i^(-1) cal(K) ->^(+1)
  $
  since all functors in question are applied termwise, we conclude by @etale-lower-shriek-first-props (3). For (6b), we replace $cal(K)$ with a quasi-isomorphic K-injective complex $cal(I)$ with injective objects, and we want to prove that there exists a distinguished triangle: 
  $
    i_* i^! cal(I) -> cal(I) -> j_* j^(-1) cal(I) ->^(+1)
  $
  For this, it suffices to prove that for any injective object $cal(J) in cAb(X_et, Lambda)$, we have an exact sequence: 
  $
    0 -> i_* i^! cal(J) -> cal(J) -> j_* j^(-1) cal(J) -> 0
  $
  This sequence is left exact by @closed-immersion-upper-shriek-first-props (0), so it suffices to prove that $cal(J) -> j_* j^(-1) cal(J)$ is surjective. Thus it suffices to prove $cal(J)(V) -> cal(J)(U times_X V)$ is surjective for all $V in Et_X$. Let $g: V -> X$ and $g_U: U times_X V -> U -> X$, and so $g_(U,!) ul(Lambda) -> g_! ul(Lambda)$ is injective. Since $cal(J) in cAb(X_et, Lambda)$ is an injective object, 
  $
    Hom_Lambda (g_! ul(Lambda), cal(J)) ->> Hom_Lambda (g_(U,!) ul(Lambda), cal(J))
  $
  is surjective, i.e. $cal(J)(V) -> cal(J)(U times_X V)$ is surjective. We are thereby done. 
]

#remark[
  There is one more compatibility result that has to be established. There are two ways to define $R f_*$ and $R Gamma(U, -)$. We take $R f_*$ as an example: 

  - As right derived functors to $f_*: cAb(X_et, Lambda) -> cAb(Y_et, Lambda)$; 

  - By first forgetting to sheaves of abelian groups, then right deriving $f_*: cAb(X_et) -> cAb(Y_et)$, and finally equip with a $Lambda$-module structure by functoriality. 

  Why do these two approaches commute? In other words, why do we have diagrams 
  // https://q.uiver.app/#r=typst&q=WzAsNCxbMCwwLCJEKFhfZXQsIExhbWJkYSkiXSxbMCwxLCJEKFhfZXQpIl0sWzEsMCwiRChMYW1iZGEpIl0sWzEsMSwiRChaWikiXSxbMSwzLCJSIEdhbW1hXlpaIChVLCAtKSIsMl0sWzAsMiwiUiBHYW1tYV5MYW1iZGEgKFUsIC0pIl0sWzAsMSwiaW90YSIsMl0sWzIsMywiaW90YSJdXQ==
  #align(center, diagram({
    node((-1, -1), [$D(X_et, Lambda)$])
    node((-1, 0), [$D(X_et)$])
    node((0, -1), [$D(Lambda)$])
    node((0, 0), [$D(ZZ)$])
    edge((-1, 0), (0, 0), [$R Gamma^ZZ (U, -)$], label-side: right, "->")
    edge((-1, -1), (0, -1), [$R Gamma^Lambda (U, -)$], label-side: left, "->")
    edge((-1, -1), (-1, 0), [$iota$], label-side: right, "->")
    edge((0, -1), (0, 0), [$iota$], label-side: left, "->")
  }))
  and: 
  // https://q.uiver.app/#r=typst&q=WzAsNCxbMCwwLCJEKFhfZXQsIExhbWJkYSkiXSxbMCwxLCJEKFhfZXQpIl0sWzEsMCwiRChZX2V0LCBMYW1iZGEpIl0sWzEsMSwiRChZX2V0KSJdLFsxLDMsIlIgZl5aWl8qIiwyXSxbMCwyLCJSIGZfKl5MYW1iZGEiXSxbMCwxLCJpb3RhIiwyXSxbMiwzLCJpb3RhIl1d
  #align(center, diagram({
    node((-1, -1), [$D(X_et, Lambda)$])
    node((-1, 0), [$D(X_et)$])
    node((0, -1), [$D(Y_et, Lambda)$])
    node((0, 0), [$D(Y_et)$])
    edge((-1, 0), (0, 0), [$R f^ZZ_*$], label-side: right, "->")
    edge((-1, -1), (0, -1), [$R f_*^Lambda$], label-side: left, "->")
    edge((-1, -1), (-1, 0), [$iota$], label-side: right, "->")
    edge((0, -1), (0, 0), [$iota$], label-side: left, "->")
  }))
  that commute, where $iota$ is the forgetful functor? 

  The forgetful functor $iota$ has the left adjoint $ul(Lambda) Lotimes_ZZ -$. Thus, 
  $
    iota compose R f^Lambda_* tack ul(Lambda) Lotimes_ZZ f_ZZ^(-1) (-)
  $
  while: 
  $
    R f_*^ZZ compose iota tack f_ZZ^(-1) (ul(Lambda) Lotimes_ZZ -)
  $
  These two left adjoints are identical by @derived-functoriality-etale (4a). Thus, we have a natural isomorphism $iota compose R f^Lambda_* cong R f_*^ZZ compose iota$. 

  Similarly, let $g: U -> X$, and $R Gamma(U, -): D(X_et, Lambda) -> D(Lambda)$ has the left adjoint $g_! compose a_X$, where $a_X: D(Lambda) -> D(X_et, Lambda)$ is the constant sheaf functor. Thus, 
  $
    iota compose R Gamma^Lambda (U, -) tack g_! a_X (Lambda Lotimes_ZZ -)
  $
  while: 
  $
    R Gamma^ZZ (U, -) compose iota tack ul(Lambda) Lotimes_ZZ g_! a_X (-)
  $
  The two left adjoints are identical by @derived-functoriality-etale (4b). Thus, we have a natural isomorphism $iota compose R Gamma^Lambda (U, -) cong R Gamma^ZZ (U, -) compose iota$. 
]

Therefore, we may safely port the various properties for derived functors on abelian sheaves to derived categories with coefficients. /*First comes $Gamma, f_*$ and $f^(-1)$, defined in @sect-functoriality-of-etale-topos: 

#construction[
  Let $f: X -> Y$ be a morphism of schemes. 

  + $f^(-1): cAb(Y_et, Lambda) -> cAb(X_et, Lambda)$ lifts to a triangulated functor: #h(1fr)
    $
      f^(-1): D^bullet (Y_et, Lambda) -> D^bullet (X_et, Lambda)
    $
    for $bullet in {#`blank`, -, +, b}$, by applying $f^(-1)$ to complexes termwise. 

  + $f_*: cAb(X_et, Lambda) -> cAb(Y_et, Lambda)$ lifts to a triangulated functor: #h(1fr)
    $
      R f_*: D^bullet (X_et, Lambda) -> D^bullet (Y_et, Lambda)
    $
    for $bullet in {#`blank`, +}$, as a derived functor of $f_*$. 

    Furthermore, $f^(-1): D^bullet (Y_et, Lambda) arrows.rl D^bullet (X_et, Lambda)$ forms an adjunction pair. 

  + For $U in Et_X$, $Gamma(U, -): cAb(X_et, Lambda) -> AMod(Lambda)$ lifts to a triangulated functor: #h(1fr)
    $
      R Gamma(U, -): D^bullet (X_et, Lambda) -> D^bullet (Lambda)
    $
    for $bullet in {#`blank`, +}$, as a derived functor of $Gamma(U, -)$. 

  #properties[
    For morphisms of schemes $X ->^f Y ->^g Z$, there are natural isomorphisms of triangulated functors: 
    $
      R(g compose f)_* = R g_* compose R f_*: D^bullet (X_et, Lambda) -> D^bullet (Z_et, Lambda)
    $
    and: 
    $
      R Gamma(Y, -) compose R f_* = R Gamma(X, -): D^bullet (X_et, Lambda) -> D^bullet (Lambda)
    $
    for $bullet in {#`blank`, +}$. 
  ]
]*/

Next, we translate @sect-stalks, the theory of stalks. 

#properties[
  For any geometric point $ol(x)$ of $X$, taking stalks termwise on complexes gives rise to a triangulated functor: 
  $
    (-)_(ol(x)): D(X_et, Lambda) -> D (Lambda)
  $
  Furthermore, the following are equivalent: 
  #[
    #set enum(numbering: "(a)")
    + #h(1fr)
      $
        cal(K) -> cal(L)
      $
      is a quasi-isomorphism in $D(X_et, Lambda)$. 

    + For all geometric points $ol(x)$ of $X$, 
      $
        cal(K)_(ol(x)) -> cal(L)_(ol(x))
      $
      is a quasi-isomorphism in $D(Lambda)$. 

    + There exists a subset $E subset X$ intersecting every nonempty locally closed subset of $X$, and for each $x in E$ some geometric point $ol(x)$ of $X$ lying above $x$ s.t: 
      $
        cal(K)_(ol(x)) -> cal(L)_(ol(x))
      $
      is a quasi-isomorphism in $D(Lambda)$. 
  ]
]
#proof[
  Just apply @stalks-detects-properties to the morphism on cohomology groups. 
]

Next,
