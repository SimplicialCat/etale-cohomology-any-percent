#import "void-import.typ": *
== Torsion sheaves

In this section, we introduce the notion of torsion sheaves and establish some preliminary properties. 

#definition(name: <defn-torsion-sheaf>)[
  An abelian sheaf $cal(F) in cAb(X_et)$ is called a *torsion sheaf*, if: 
  $
    cal(F) = dirlim_(n>=1) cal(F)[n!]
  $
  where $cal(F)[n!]$ denotes the $n!$-torsion subsheaf of $cal(F)$. 
]

#proposition(name: <torsion-sheaves-first-props>)[
  Given $cal(F) in cAb(X_et)$, TFAE: 

  + $cal(F)$ is a torsion sheaf; 

  + Given any $U in Et_X$, any section $s in cal(F)(U)$, there exists an etale cover $cal(U) = {U_i -> U}_i$ s.t. each $s|_(U_i)$ is a torsion element of $cal(F)(U_i)$; 

  + For any geometric point $ol(x)$ of $X$, $cal(F)_(ol(x))$ is a torsion abelian group. 
]
#proof[
  (1)$==>$(2): Let $cal(P) = dirlim_(n>=1,cPAb) cal(F)[n!]$ be the sub-presheaf of $cal(F)$ consisting of torsion sections. Then by definition of torsion abelian sheaves and @ab-x-et-the-abelian-cat (3), 
  $
    cal(P)^\# = cal(F)
  $
  Since $cal(P)$ is a sub-presheaf of a sheaf $cal(F)$, it is separated, and so $cal(P)^\# = cal(P)^+$. Thus, 
  $
    cal(F)(U) = dirlim_(cal(U) = {U_i -> U}_i) ker(product_i cal(P)(U_i) -> product_(i,j) cal(P)(U_i times_U U_j))
  $
  and so every section $s in cal(F)(U)$ admits an etale cover $cal(U) = {U_i -> U}_i$ s.t. each $s|_(U_i) in cal(P)(U_i)$. We are thereby done. 

  (2)$==>$(3): Recall: 
  $
    cal(F)_(ol(x)) = dircolim_((U,ol(u)) -> (X,ol(x)) #[etale]) cal(F)(U)
  $
  Now every $[s] in cal(F)_(ol(x))$ is represented by some $s in cal(F)(U)$. By (b), there exists some etale $(V, ol(v)) -> (U, ol(u))$ s.t. $s|_V in cal(F)(V)$ is torsion, say $n(s|_V) = 0$. In other words, $n[s] = n[s|_V] = [n(s|_V)] = 0 in cal(F)_(ol(x))$, and we are done. 

  (3)$==>$(1): Since taking stalks is a left adjoint, it commutes with colimits, so: 
  $
    (dirlim_(n>=1) cal(F)[n!])_(ol(x)) = dirlim_(n>=1) cal(F)_(ol(x))[n!] = cal(F)_(ol(x))
  $
  since $cal(F)_(ol(x))$ is a torsion abelian group. Now by @stalks-detects-properties, 
  $
    dirlim_(n>=1) cal(F)[n!] = cal(F)
  $
]

#corollary(name: <pullback-of-torsion-sheaf>)[
  Given any scheme morphism $f: X -> Y$ and any torsion sheaf $cal(G) in cAb(Y_et)$, $f^(-1) cal(G)$ is torsion. 
]
#proof[
  We use equivalent condition (c) of @torsion-sheaves-first-props, and observe that every $(f^(-1) cal(G))_(ol(x)) = cal(G)_(f(ol(x)))$ is a torsion abelian group. 
]

We also need a short discussion about the category of $n$-torsion sheaves for a fixed $n>=1$, which will eventually be used in the proof of proper base change. 

#definition(name: <defn-zn-module-sheaf>)[
  Given a natural number $n>=1$, an abelian presheaf/sheaf $cal(F)$ is called a *presheaf/sheaf of $ZZ\/n$-modules*, if it is $n$-torsion.
  
  The category of presheaves/sheaves of $ZZ\/n$ on $X$, denoted $cPAb(X_et, ZZ\/n)$ and $cAb(X_et, ZZ\/n)$, is the full subcategory of $cPAb(X_et)$ and $cAb(X_et)$ consisting of presheaves/sheaves of $ZZ\/n$-modules.
]

#properties(name: <etale-zn-sheaves-first-props>)[
  + Any additive functor between a category of etale sheaves/presheaves preserves the subcategory of $ZZ\/n$-modules.
    
    In particular, the functors $R^q f_*, f^(-1)_cPSh, f^(-1), (-)^\#, f_!, i^!$ preserve the subcategory of $ZZ\/n$-modules.
  
  + $cAb(X_et, ZZ\/n)$ is an abelian category satisfying (Ab5) having enough injectives.
  
  + Any injective object $cal(I) in cAb(X_et, ZZ\/n)$ is acyclic w.r.t. $Gamma(U, -)$ for any $U in Et_X$, and $f_*$ for any $f: X -> Y$.
]
#proof[
  (1) Any additive functor sends the morphism $times n$ to $times n$, hence preserves objects on which $times n$ is the zero morphism.
  
  (2) All but enough injectives follow from the corresponding properties on $cAb(X_et)$. Now consider the $n$-torsion functor:
  $
    [n]: cAb(X_et) -> cAb(X_et, ZZ\/n), cal(F) |-> cal(F)[n]
  $
  taking the $n$-torsion part of a sheaf. Now for any $cal(G) in cAb(X_et, ZZ\/n)$,
  $
    Hom_cAb (cal(G), cal(F)) = Hom_cAb (cal(G), cal(F)[n])
  $
  since $cal(G)$ is $n$-torsion, hence having $n$-torsion image. In other words, $[n]$ has the forgetful functor $cAb(X_et, ZZ\/n) -> cAb(X_et)$ as its left adjoint. Since this left adjoint is exact, $[n]$ preserves injective objects.
  
  Now for any $cal(G) in cAb(X_et, ZZ\/n)$, $cal(G) arrow.hook cal(I)$ embeds into an injective $cal(I) in cAb(X_et)$. Now $cal(G) arrow.hook cal(I)[n]$ embeds into the $n$-torsion part of $cal(I)$, with $cal(I)[n] in cAb(X_et, ZZ\/n)$ being an injective object.
  
  (3) Pick an injective $cal(J) in cAb(X_et)$ with an embedding $cal(I) arrow.hook cal(J)$. Since $cal(I)$ is $n$-torsion, there is an embedding $cal(I) arrow.hook cal(J)[n]$ in $cAb(X_et, ZZ\/n)$. Since $cal(I)$ is injective in $cAb(X_et, ZZ\/n)$, $cal(I)$ is a direct summand of $cal(J)[n]$. It suffices to prove the acyclicity of $cal(J)[n]$.
  
  Since $cal(J)$ is an injective etale sheaf, and any $times n: ul(ZZ)_(!,U) -> ul(ZZ)_(!,U)$ for $U in Et_X$ is injective, $times n: cal(J)(U) -> cal(J)(U)$ must be surjective. In other words, $times n: cal(J) -> cal(J)$ is surjective, given an injective resolution of $cal(J)[n]$:
  $
    0 -> cal(J)[n] -> cal(J) ->^(times n) cal(J) -> 0
  $
  This makes $R^q F (cal(J)[n]) = 0$ for $q >= 2$, and $R^1 F(cal(J)[n]) = coker(times n: F(cal(J)) -> F(cal(J)))$ for any left exact additive functor $F$ defined on $cAb(X_et)$, such as $Gamma(U, -)$ or $f_*$. Thus $H^q (U, cal(J)[n]) = 0$ and $R^q f_* (cal(J)[n]) = 0$ automatically for all $q >= 2$. For $q = 1$,
  $
    H^1 (U, cal(J)[n]) = coker(times n: cal(J)(U) -> cal(J)(U)) = 0
  $
  as verified above. Since $times n: f_* cal(J) -> f_* cal(J)$ when viewed on sections is just $times n$ on sections of $cal(J)$, it is also surjective. Hence $R^1 f_* (cal(J)[n]) = 0$. We are thereby done.
]
