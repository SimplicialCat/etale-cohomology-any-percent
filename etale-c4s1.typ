#import "void-import.typ": *
#let topp = math.op[top]
#let LIsom = math.op[LIsom]
#let Open = math.op[Open]
/*
#date[Lecture 3, 2025/10/11
  #align(left)[
    Recall that we have introduced etale morphisms and studied their properties. Etale morphisms is the equivalent of local homeomorphisms in scheme theory. 

    Today, we will introduce etale sites and fpqc descent. 
  ]
]*/
Last chapter, we defined the etale fundamental group $pi_1^et (X)$. From the motivations given in Chapter 1, and from the analogy with algebraic topology, our next task is to establish a satisfactory theory of cohomology on schemes. 

In algebraic topology, a cohomology theory is defined using sheaf cohomology. A sheaf on a topological space $X$ is a functor $Open_X^opp -> cAb$, i.e. a contravariant functor from the open sets of $X$ to abelian groups, that satisfies certain "sheaf axioms". The sheaf cohomology is then obtained by right deriving the global section functor $Gamma(X, -): cAb(X) -> cAb$, and our familiar notion of singular cohomology with coefficients $H^p (X, Lambda)$ can then be defined as the sheaf cohomology of a constant sheaf $underline(Lambda)$. 

However, this does not provide a satisfactory cohomology theory for schemes. On a typical scheme, say an irreducible one, a constant sheaf is flasque, and all of its higher cohomologies vanish. 

It turns out that, it is to blame that the Zariski topology is too coarse. The correct way to solve this problem is to generalize the notion of a sheaf, by replacing the category of open sets $Open_X$ in $Open_X^opp -> cAb$ with $Et_X$, the category of etale morphisms over $X$. Intuitively, every open immersion is etale, so etale neighborhoods are finer in the way that they capture more information about the scheme. 

It is thus up to us to generalize what $Open_X$ and $Et_X$ has in common to establish an abstract notion of sites and sheaves, define the etale site and etale sheaves, and introduce the basic sheaf operations to etale sheaves. 

== Sites and the etale site

Before we start our exposition on the etale site, we will define the general notion of an abstract site. 

#definition(name: <defn-site>)[
  A *site* $cal(T)$ is a category $cal(C)$ together with a distinguished set of sets of morphisms ${X_i -> X}$ associated with each object $X in cal(C)$, called the *covers* of $X$ in $cal(T)$, satisfying the following axioms: 

  + A single isomorphism ${V ->^tilde U}$ is a cover of $U$ in $cal(T)$; 

  + For any cover ${U_i -> U}_(i in I)$ of $U$ in $cal(T)$ and any morphism $V -> U$ in $cal(C)$, the fiber products $U_i times_U V$ exists in $cal(C)$, and ${U_i times_U V -> V}_(i in I)$ is a cover of $V$ in $cal(T)$; 

  + If: 
    - ${U_i -> U}_(i in I)$ is a cover of $U$ in $cal(T)$;

    - for each $i$, ${U_(i,j) -> U_i}_(j in J_i)$ is a cover of $U_i$ in $cal(T)$;
    then ${U_(i,j) -> U}_(i in I, j in J_i)$ is a cover of $U$ in $cal(T)$. 
  
  Then we may define $cPSh(cal(C)), cPAb(cal(C))$ and $cSh(cal(C)), cAb(cal(C))$ in the same way.
  
  For example, for a topological space $X$, the site $X_topp = (Open(X), "open covers")$ gives the usual notation of sheaves on $X$.
]

#definition(name: <defn-presheaves-and-sheaves-on-sites>)[
  Given a site $cal(T)$ with underlying category $cal(C)$, we define: 

  - *A presheaf of sets/abelian groups on $cal(T)$* is defined to be a functor $cal(C)^opp -> cSet$ (or $cal(C)^opp -> cAb$ respectively). 
  
    A morphism between presheaves is defined as a natural transformation between them as contravariant functors. The categories of presheaves of sets/abelian groups on $cal(T)$ is denoted $cPSh(cal(T))$ and $cPAb(cal(T))$, respectively. 

  - *A sheaf of sets/abelian groups on $cal(T)$* is a presheaf $cal(F)$ of sets/abelian groups (resp.) on $cal(T)$, satisfying the following sheaf axiom: 

    - Given any $X in cal(C)$, any cover ${U_i -> X}_(i in I)$, we have an equalizer of sets: #h(1fr)
      $
        cal(F)(X) ->^(u |-> (u|_(U_i))_i) product_(i in I) cal(F)(U_i) arrows.rr^((u_i)_i |-> (u_i|_(U_i times_X U_j))_(i,j))_((u_i)_i |-> (u_j|_(U_i times_X U_j))_(i,j)) product_(i,j in I) cal(F)(U_i times_X U_j) 
      $
      In other words, every family of sections $(u_i)_(i in I) in product_(i in I) cal(F)(U_i)$ compatible on every $U_i times_X U_j$ glues to a unique section $u in cal(F)(U)$. 

    A morphism between sheaves of sets/abelian groups is just a morphism between them as presheaves. The category of sheaves of sets/abelian groups on $cal(T)$ is denoted $cSh(cal(T))$ and $cAb(cal(T))$, respectively. 
]

#example[
  The prototypical example of a site is the *topological site* $X_topp$. Let $Open_X$ be the category whose objects are open sets of $X$, and whose morphisms are inclusions of open sets. Then $X_topp = (Open_X, #[open covers])$ is a site. (The fiber product is just intersections of open sets. Open covers are stable under intersections and are transitive.)

  In this case, a presheaf $cal(F)$ (of abelian groups) on $X$ is nothing but a functor $Open_X^opp -> cAb$, where $Open_X$ is the category whose objects are open sets of $X$ and morphisms are inclusions of open sets. The sheaf condition is that given $U subset X$ and an open cover ${U_i}$, we have an exact sequence:
  $
    0 -> cal(F) (U) -> product_i cal(F)(U_i) -> product_(i,j) cal(F)(U_i ∩ U_j)
  $
  where the morphisms are your familiar ones. 

  A slight variant of $X_#[top]$ is to take $LIsom_X$ to be the category of local homeomorphisms $f: Y -> X$, and we say a family of morphisms ${h_i: Y_i -> X}$ is a covering if $X = union.big_i h_i (Y_i)$. Then fiber products exist in $LIsom_X$, and $Open_X$ embeds fully faithfully into $LIsom_X$. We denote this site by $X_LIsom$. 
  
  A presheaf on $LIsom_X$ is a contravariant functor $cal(G): LIsom_X^opp -> cSet$. We say $cal(G)$ is a sheaf if given any covering ${h_i: Y_i -> Y}$,
  $
    cal(G) (Y) -> product_(i) cal(G) (Y_i) arrows.rr product_(i,j) cal(G) (Y_i times_Y Y_j)
  $
  is an equalizer. 

  #fact[
    This generalization from open covers to covers by local homeomorphisms does not really introduce anything new. To put it rigorously, there are natural equivalences of categories: 
    $
      cSh(X_topp) cong cSh(X_LIsom), cAb(X_topp) cong cAb(X_LIsom)
    $
  ]

  Thus $X_LIsom$ is really just a new perspective of $X_topp$. One new feature is that we can glue sheaves w.r.t. coverings in $LIsom_X$. Let ${g_i : X_i -> X}$ be a covering of $id: X -> X$ in $LIsom_X$. Given $cal(F)_i in cSh(LIsom_(X_i))$ and isomorphisms $eta_(i,j) : p_1^* cal(F)_i -> p_2^* cal(F)_j$ of sheaves on $LIsom_(X_i times_X X_j)$ s.t. the cocycle condition:
  $
    p_(13)^* eta_(i,k) = p_(23)^* eta_(j,k) compose p_(12)^* eta_(i,j)
  $
  holds on $LIsom_(X_i times_X X_j times_X X_k)$. Then there exists a unique $cal(F) in cSh(LIsom_X)$ and an isomorphism $cal(F)|_(X_i) cong cal(F)_i$ compatible with $eta_(i,j)$. In other words, there is an equivalence of categories
  $
    cSh(X_topp) cong cSh(X_LIsom) cong "DD"(g_i) = {(cal(F)_i, eta_(i,j)) "s.t." dots.c}
  $
  where RHS is the category of descent data. 
]

/*
#example[
  The motivation is that, on a topological space $X$, we may consider the sheaf cohomologies $H^bullet (X, cal(F)), cal(F) in cAb(X)$. 

  In this case, a presheaf $cal(F)$ on $X$ is nothing but a functor $Open_X^opp -> cAb$, where $Open_X$ is the category whose objects are oepn sets of $X$ and morphisms are inclusion of open sets. The sheaf conditions is that given $U subset X$ and an open cover ${U_i}$, we have exact sequences: 
  $
    0 -> cal(F) (U) -> product_i cal(F)(U_i) -> product_(i,j) cal(F)(U_i ∩ U_j) -> 0
  $
  where the morphisms are #furi[first 2 maps in the Cech complex][your familiar ones]. 

  A variant of this construction is that take $LIsom_X$ to be the category of local homeomorphisms $f: Y -> X$, and we say a family of morphisms ${h_i: Y_i -> X}$ is a covering if $X = union.big_i h_i (Y_i)$. Then fiber products exist in $LIsom_X$, and $Open_X$ embeds fully faithfully into $LIsom_X$. A presheaf on $LIsom_X$ is a contravariant functor $cal(G): LIsom_X^opp -> cSet$. We say $cal(G)$ is a sheaf if given any covering ${h_i: Y_i -> Y}$, 
  $
    cal(G) (Y) -> product_(i) cal(G) (Y_i) arrows.rr product_(i,j) cal(G) (Y_i times_Y Y_j)
  $

  #exercise[
    We have an equivalence of categories: 
    $
      cSh(Open_X) & tilde.eq cSh(LIsom_X) \
      cal(F) &|-> ((g: Y -> X) |-> (g^(-1) cal(F))(Y)) \
      cal(G)|_(Open_X^opp) &#scale(x: -100%)[$|->$] cal(G)
    $
  ]
  
  So this new formulation is really just a new perspective. One new feature is that we can glue sheaves w.r.t. coverings in $LIsom_X$. Let ${g_i : X_i -> X}$ be a covering of $id: X -> X$ in $LIsom_X$. Given $cal(F)_i in cSh(LIsom_(X_i))$ and isomorphisms $eta_(i,j) : p_1^* cal(F)_i -> p_2^* cal(F)_j$ of sheaves on $LIsom_(X_i times_X X_j)$ s.t. the cocycle condition: 
  $
    p_(13)^* eta_(i,k) = p_(23)^* eta_(j,k) compose p_(12)^* eta_(i,j)
  $
  holds on $LIsom_(X_i times_X X_j times_X X_k)$. Then there exists a unique $cal(F) in cSh(LIsom_X)$ and isomorphism $cal(F)|_(X_i) cong cal(F)_i$ compatible with $eta_(i,j)$. 

  #exercise[
    $
      cSh(LIsom_X) tilde.eq "DD"(g_i) = {(cal(F)_i, eta_(i,j)) "s.t." dots.c}
    $
    where RHS is the category of descent data. 
  ]

  #remark[
    This construction is very easy if one of the $g_i: X_i -> X$ admits a section $s_i: X -> X$, in which case $X$ can almost be regarded as an open of $X_i$, and we may pick $cal(F) = s^(-1) cal(F)_i$. 
  ]

  This setup is an example of sites. More formally, a site is some category together with some notion of covering in this category, satisfying certain axioms. 
]*/

Although the general notion of sites, and #furi[toposes][sheaves on a general site] are of considerable importance to some mathematicians, as a first course in etale cohomology we won't need this point of view. There will be few occurrences of the word "site" outside the phrase "etale site" in the rest of this document. You can forget about most of the abstract notions we introduced in the last 2 pages as we proceed to introduce the etale site. 

// We are now ready to define $Et_X$, the etale site category: 
#definition(name: <defn-etale-site>)[
  The *etale site* $X_et$ on a scheme $X$ is the category defined by the following data: 

  - The base category of $X_et$ is the category $Et_X$, defined as the full subcategory of $cSch_X$ consisting of morphisms $f: Y -> X$ that are etale. 
  
    The morphisms in this category are a priori arbitrary morphisms $h: Y -> Z$ that commute with $Y -> X$ and $Z -> X$, but they are necessarily etale by properties of etale morphisms. 

  - Given $(h: Y -> X) in Et_X$, a family of morphisms ${h_i: Y_i -> Y}_(i in I)$ in $Et_X$ is called a *covering* of $Y$ if $Y = union.big_i h_i (Y_i)$. This condition is called *jointly surjective*. 

  The category $Et_X$ has fiber products given by base changes; compositions of etale morphisms are etale; isomorphisms are surjective; and joint surjectivity is stable under base change and transitive. Therefore, 
  $
    X_et = (Et_X, #[jointly surjective families of etale morphisms])
  $ 
  is a site. 

  Note that notationally, we use $X_et$ to denote this site, and use $Et_X$ to denote its underlying category. 

  An *etale presheaf/sheaf of sets/abelian groups* on $X$, is just a presheaf/sheaf of sets/abelian groups on $X_et$ as we defined for a general site. These categories are denoted $cPSh(X_et)$, $cSh(X_et)$, $cPAb(X_et)$, $cAb(X_et)$, as in the general case. 
]