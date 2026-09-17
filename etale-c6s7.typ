#import "void-import.typ": *

== Proof of (Seed)

The last remaining point of the six points we stated at the beginning of this chapter is (Seed). It is a statement regarding properties of the restriction $H^q (X, ul(ZZ\/n)) -> H^q (X_0, ul(ZZ\/n))$ whenever $X -> PP^1_A$ is finite, for a noetherian strict henselian local ring $A$. 

In other words, all that remains to be proved to obtain the general proper base change theorem is a statement on the very concrete case of a projective $1$-dimensional space. 

To prove necessary results, our proof will be largely arranged in two steps: 

+ Pass from an object on $X_0 = X otimes_A k$ to $X_n = X otimes_A A\/frak(m)^(n+1)$ via topological invariance, then pass to the limit and get an object on $hat(X) = X otimes_A hat(A)$. 

+ Pass an object from the completion $hat(A)$ to the henselian local ring $A$. 

This corresponds to two results from algebraic geometry. They are interesting on their own, and their proofs are largely technical. The first step is governed by the Grothendieck existence theorem, and the second step is governed by the Artin approximation theorem. 

The proof for (Seed) in this section is inspired by the proof in @cite-lei-fu, but with Artin approximation used in a different flavor.

#theorem(name: <grothendieck-existence-thm>)[
  (Grothendieck existence theorem + Theorem on formal functions) 

  #definition[
    Given a noetherian scheme $X$, let $cal(I) subset cal(O)_X$ be a coherent sheaf of ideals. We define the category $Coh(X, cal(I))$ to be the category of projective systems of coherent $cal(O)_X$-modules ${cal(F)_n}_(n>=1)$ s.t:
    
    + $cal(I)^n cal(F)_n = 0$ for each $n$;
    
    + The transition maps $cal(F)_(n+1) -> cal(F)_n$ induce an isomorphism $cal(F)_(n+1)\/cal(I)^n cal(F)_(n+1) -> cal(F)_n$.
    
    In other words, we may regard $cal(F)_n in Coh(X_n)$ where $X_n := SPec(cal(O)_X\/cal(I)^n)$, equipped with isomorphisms $phi_n: i_n^* cal(F)_(n+1) cong cal(F)_n$ along the directed system:
    $
      X_1 -> dots.c -> X_n ->^(i_n) X_(n+1) -> dots.c
    $
  ]
  Given a noetherian ring $A$ and an ideal $I$ with respect to which $A$ is complete, and a scheme $X$ proper over $Spec(A)$, there is an equivalence of categories: 
  $
    hat: Coh(X) &-> Coh(X, I cal(O)_X) \
    cal(F) &|-> {cal(F)\/I^n cal(F)}_(n>=1)
  $
  Furthermore, this induces a canonical isomorphism: 
  $
    H^q (X, cal(F)) = invlim_(n>=1) H^q (X_n, cal(F)\/cal(I)^n cal(F))
  $
]
#proof[
  We invite the reader to read #cite-stacks("088C")[Proposition 30.25.4]. 

  To reduce the burden of a depth-first context search when unfolding the proof of a result in Stacks Project, we suggest that the reader should read #cite-stacks("0EHN,087V,0886")[Section 30.23\~30.25] sequentially. 

  The statement on cohomology is the theorem on formal functions, which can be found as #cite-stacks("02OC")[Theorem 30.20.5]. 
]

A statement of Artin approximation is @artin-approximation-theorem, with proof in @appendix-artin-approximation. 

We now prove precursors for degree 0, 1 and 2 of (Seed) separately, since we expect vanishing in degrees $>=3$ by @cohom-of-general-curve. The case for degree 0 has already been dealt with in @pbc-seed-precursor-0. We now deal with degree 1. 

#proposition(name: <pbc-seed-precursor-1>)[
  Let $(A, frak(m), k)$ be a noetherian henselian local ring, and $X -> Spec(A)$ be proper. Then the base change: 
  $
    FEt_X -> FEt_(X_0), Y |-> Y_0 := Y times_X X_0
  $
  is an equivalence of categories. In particular, the induced map:
    $
      pi_1^et (X_0, ol(x)) -> pi_1^et (X, ol(x))
    $
    is an isomorphism for any geometric point $ol(x)$ of $X_0$. 
]
#proof[
  We first prove fully faithfulness directly. Fix a geometric point $ol(x)$ of $X_0$. Then for $Y, Z in FEt_X$: 
  $
    Hom_X (Y, Z) cong Hom_(pi_1^et (X, ol(x))) (F_(ol(x)) (Y), F_(ol(x)) (Z)) \
    Hom_(X_0) (Y_0, Z_0) cong Hom_(pi_1^et (X_0, ol(x))) (F_(ol(x)) (Y_0), F_(ol(x)) (Z_0))
  $
  Now the fiber sets $F_(ol(x)) (Y) cong F_(ol(x)) (Y_0), F_(ol(x)) (Z) cong F_(ol(x)) (Z_0)$. Thus if we can prove that: 
  $
    pi_1^et (X_0, ol(x)) -> pi_1^et (X, ol(x))
  $
  is surjective, identifying $pi_1^et (X, ol(x))$ as a quotient of $pi_1^et (X_0, ol(x))$, we would be done. By @pi1et-mor-props, it suffices to show that for any $Y in FEt_X$ connected, $Y_0$ is connected. This is just @pbc-seed-precursor-0. 

  It only remains to prove essential surjectivity. We first do a limit argument: 

  - Write $A$ as a directed limit of its finite type $ZZ$-subalgebras: $A = dirlim_i A_i$. Now since $A$ is local and localization commutes with direct limits,
    $
      A = A_(frak(m)) = dirlim_i (A_i)_(frak(p)_i)
    $
    for $frak(p)_i = frak(m) ∩ A_i$. This writes $A$ as a directed limit of subalgebras that are localizations of finite type $ZZ$-algebras at prime ideals. Finally, since henselization commutes with direct limits by @henselization-and-directed-limits:
    $
      A = A^#[h] = dirlim_i (A_i)_(frak(p)_i)^#[h]
    $
  is a directed colimit of henselizations of finite type $ZZ$-algebras at prime ideals, with local transition maps. 

    We rename this directed limit as $A = dirlim_lambda A_lambda$. 
    
    By @passage-to-limit-of-morphisms (1) and @passage-to-limit-of-properties (2e), up to truncating the directed set ${lambda}$, we may assume that $X -> Spec(A)$ is obtained by base changing from some proper $X_lambda -> Spec(A_lambda)$. We denote by $X_mu = X_lambda otimes_(A_lambda) A_mu$ for $mu >= lambda$, and $X_(mu,0)$ its base change to the closed point of $Spec(A_mu)$. 

    By @passage-to-limit-of-properties (2a)(3d), 
    $
      FEt_X cong dirlim_(mu>=lambda) FEt_(X_mu) \
      FEt_(X_0) cong dirlim_(mu>=lambda) FEt_(X_(mu,0))
    $
    Thus it suffices to show that each $FEt_(X_mu) -> FEt_(X_(mu,0))$ is an equivalence of categories. 

  Thus, we may assume that $A$ is the henselization of a finite type $ZZ$-algebra at a prime. Denote by $hat(A)$ the completion of $A$ and $hat(X) = X otimes_A hat(A)$. We first claim that: 
  $
    FEt_(hat(X)) -> FEt_(X_0)
  $
  is essentially surjective. 

  - Denote by $X_m = X otimes_A A\/frak(m)^(m+1)$ for each $m>=0$. #h(1fr)
  
    Fix any $Y_0 in FEt_(X_0)$. By topological invariance (@top-invariance-sheaves (3)), there exists $Y_m in FEt_(X_m)$ s.t. $Y_m cong Y_(m+1) times_(X_(m+1)) X_m$ compatibly. Let $phi_m: Y_m -> X_m$ be the structure maps, and $cal(F)_m = phi_(m,*) cal(O)_(Y_m)$. 

    Then each $cal(F)_m$ is a coherent sheaf of $cal(O)_(X_m)$-algebras, satisfying $cal(F)_(m+1) otimes_(A\/frak(m)^(m+2)) A\/frak(m)^(m+1) cong cal(F)_m$. By @grothendieck-existence-thm, there exists a coherent sheaf $hat(cal(F))$ of $cal(O)_(hat(X))$-modules s.t:
    $
      cal(F)_m cong hat(cal(F)) otimes_(hat(A)) A\/frak(m)^(m+1)
    $
    Now by the theorem on formal functions (as in @grothendieck-existence-thm), 
    $
      Hom_(cal(O)_(hat(X))) (hat(cal(F)) otimes_(cal(O)_(hat(X))) hat(cal(F)), hat(cal(F))) cong invlim_(m>=0) Hom_(cal(O)_(X_m)) (cal(F)_m otimes_(cal(O)_(X_m)) cal(F)_m, cal(F)_m)
    $
    so the multiplication on each $cal(F)_m$ lifts to $hat(cal(F))$. Associativity, commutativity and the unit follows from lifting the corresponding relations from each $X_m$ via the theorem on formal functions. For example, commutativity is checked by lifting the symmetric isomorphism through: 
    $
      & Hom_(cal(O)_(hat(X))) (HHom_(cal(O)_(hat(X))) (hat(cal(F)) otimes_(cal(O)_(hat(X))) hat(cal(F)), hat(cal(F))), HHom_(cal(O)_(hat(X))) (hat(cal(F)) otimes_(cal(O)_(hat(X))) hat(cal(F)), hat(cal(F)))) \
      cong& invlim_(m>=0) Hom_(cal(O)_(X_m)) (HHom_(cal(O)_(X_m)) (cal(F)_m otimes_(cal(O)_(X_m)) cal(F)_m, cal(F)_m), HHom_(cal(O)_(X_m)) (cal(F)_m otimes_(cal(O)_(X_m)) cal(F)_m, cal(F)_m))
    $
    We won't check other ring axioms as that is just routine. Thus $hat(cal(F))$ is identified as a coherent sheaf of $cal(O)_(hat(X))$-algebras s.t. $cal(F)_m cong hat(cal(F)) otimes_(hat(A)) A\/frak(m)^(m+1)$. Put $hat(Y) = SPec(hat(cal(F)))$, and so $hat(phi): hat(Y) -> hat(X)$ is a finite map, base changing to every $phi_m$. Etaleness is governed by the following lemma and we are done.  
    #lemma[
      If $(A, frak(m))$ is a noetherian complete local ring and $f: X -> Y$ is a morphism between finite $A$-schemes, s.t. for all $m>=0$ the base change $f_m: X_m -> Y_m$ along $Spec(A\/frak(m)^(m+1)) -> Spec(A)$ is etale. Then $f$ is finite etale. 
    ]
    #proof[
      We may check etaleness locally on target, so we may assume that $X = Spec(C), Y = Spec(B)$ with $B, C$ finite $A$-algebras. Put $X_m = Spec(C_m), Y_m = Spec(B_m)$. 
      
      $f$ is unramified, since: 
      $
        Omega_(C\/B) otimes_A A\/frak(m) cong Omega_(C_0\/B_0) = 0
      $
      and so $Omega_(C\/B) = frak(m) Omega_(C\/B)$. By Nakayama $Omega_(C\/B) = 0$. 

      For any maximal ideal $frak(q) in Spec(B)$, we aim to show that $C_(frak(q))$ is free over $B_(frak(q))$. Since $B$ is finite over $A$, $frak(q)$ lies above the maximal ideal $frak(m) in Spec(A)$, i.e. $frak(q) B_(frak(q)) supset frak(m) B_(frak(q))$. 

      Since each $f_m$ is finite flat, each $B_(frak(q))\/frak(m)^(m+1) B_(frak(q)) -> C_(frak(q))\/frak(m)^(m+1) C_(frak(q))$ is finite flat. It is thus free since $B_(frak(q))\/frak(m)^(m+1) B_(frak(q))$ is local. They all have common rank $r$. 

      Pick a basis $[c_1], dots.c, [c_r]$ of $C_(frak(q))\/frak(m) C_(frak(q))$ over $B_(frak(q))\/frak(m) B_(frak(q))$, and lift them arbitrarily to $c_1, dots.c, c_r$. Then: 
      $
        C_(frak(q)) = sum_(i=1)^r B_(frak(q)) c_i + frak(m) C_(frak(q))
      $
      Now $C_(frak(q))$ is a finite $B_(frak(q))$-module and $frak(m) B_(frak(q)) subset frak(q) B_(frak(q))$ the maximal ideal. Thus by Nakayama, $C_(frak(q)) = sum_(i=1)^r B_(frak(q)) c_i$. Thus, 
      $
        phi: B_(frak(q))^(oplus r) -> C_(frak(q))
      $
      defined by $c_1, dots.c, c_r$ is a surjection. Modulo each $frak(m)^(m+1)$, it is a surjection between two free modules of the same rank, and is a bijection. In other words, 
      $
        ker(phi) subset inter.big_(m>=0) frak(m)^(m+1) B_(frak(q))^(oplus r)
      $
      By Krull's intersection theorem, this kernel is zero and $phi$ is a bijection. 
    ]

  Now that $FEt_(hat(X)) -> FEt_(X_0)$ is essentially surjective, we are ready to complete the proof by Artin approximation. Consider the functor: 
  $
    F: AAlg(A) -> cSet, B |-> FEt_(X otimes_A B)\/cong
  $
  sending $B$ to the isomorphism classes of finite etale coverings of $X otimes_A B$. By @passage-to-limit-of-morphisms (2)(3) and @passage-to-limit-of-properties (2a)(3d), $F$ commutes with directed limits. Since $FEt_(hat(X)) -> FEt_(X_0)$ is essentially surjective, any $Y_0 in F(A\/frak(m))$ lifts to some $hat(Y) in F(hat(A))$. 
  
  Now $A$ is the henselization of a finite type $ZZ$-algebra at a prime, so it is the henselization of a finite type algebra over either $QQ$ or $ZZ_((p))$ at a prime, depending on which prime of $ZZ$ the maximal ideal of $A$ lies above. Now $QQ$ is a field and $ZZ_((p))$ is an excellent DVR, so Artin approximation applies. 
  
  By Artin approximation (@artin-approximation-theorem (2)), there exists $Y in F(A)$ s.t. $Y$ and $hat(Y)$ agree upon passing to $F(A\/frak(m))$. That is to say, $Y otimes_A A\/frak(m) cong hat(Y) otimes_(hat(A)) A\/frak(m) cong Y_0$. We have thus proved essential surjectivity. 
]

Next, we deal with degree 2. 
#proposition(name: <pbc-seed-precursor-2>)[
  Let $(A, frak(m), k)$ be a noetherian henselian local ring, and $X -> Spec(A)$ be proper. If the special fiber $X_0$ of $X$ satisfies $dim(X_0) <= 1$, then the base change map: 
  $
    Pic(X) -> Pic(X_0)
  $
  is surjective. 
]
#proof[
  Similar to the proof of claim in the proof of @pbc-seed-precursor-1, we may write $A = dirlim_lambda A_lambda$ where $A_lambda$ is the henselization of a finite type $ZZ$-algebra at a prime ideal, with all transition maps local. Let $X -> Spec(A)$ come from some proper $X_lambda -> Spec(A_lambda)$ by @passage-to-limit-of-morphisms (2) and @passage-to-limit-of-properties (2e). 

  #lemma[
    Let $X = invlim_lambda X_lambda$ be a projective limit of qcqs schemes with affine transition maps. Then: 
    $
      Pic(X) cong dirlim_lambda Pic(X_lambda)
    $
  ]
  #proof[
    @passage-to-limit-of-sheaves (1)(2)(3) really says that: 
    $
      Coh(X)/cong cong dirlim_lambda Coh(X_lambda)/cong
    $
    That is, isomorphism classes of finitely presented sheaves of $cal(O)_X$-modules are the same as the direct limit of isomorphism classes of finitely presented sheaves of $cal(O)_(X_lambda)$-modules. The transition maps are also monoidal, i.e. respect tensor products. Thus the same limit formula holds for invertible elements, and so: 
    $
      Pic(X) cong dirlim_lambda Pic(X_lambda)
    $
  ]
  By the previous lemma, 
  $
    Pic(X) = dirlim_lambda Pic(X_lambda) \
    Pic(X_0) = dirlim_lambda Pic(X_(lambda,0))
  $
  Thus, it remains to show that each $Pic(X_lambda) -> Pic(X_(lambda,0))$ is surjective. Hence, we may assume that $A$ is the henselization of a finite type $ZZ$-algebra. 

  Let $hat(A)$ be the completion of $A$ and $hat(X) = X otimes_A hat(A)$. We claim that $Pic(hat(X)) -> Pic(X_0)$ is surjective. 

  - Let $X_n = X otimes_A A\/frak(m)^(n+1)$, which shares the same underlying topological space as $X_0$. Now consider the exact sequence of Zariski sheaves on $X_0$ for $n>=0$: 
    $
      0 -> frak(m)^(n+1) cal(O)_X -->^(gamma |-> 1+gamma) (cal(O)_X\/frak(m)^(n+2) cal(O)_X)^times -> (cal(O)_X\/frak(m)^(n+1) cal(O)_X)^times -> 0
    $
    Taking the long exact sequence on cohomology, we get: 
    $
      dots.c -> H^1_#[Zar] (X_0, (cal(O)_X\/frak(m)^(n+2) cal(O)_X)^times) -> H^1_#[Zar] (X_0, (cal(O)_X\/frak(m)^(n+1) cal(O)_X)^times) -> H^2_#[Zar] (X_0, frak(m)^(n+1) cal(O)_X) -> dots.c
    $
    i.e: 
    $
      dots.c -> Pic(X_(n+1)) -> Pic(X_n) -> H^2_#[Zar] (X_0, frak(m)^(n+1)) -> dots.c
    $
    Since $dim(X_0) <= 1$ and Zariski cohomology vanishes beyond the dimension, $H^2_#[Zar] (X_0, frak(m)^(n+1)) = 0$, and so each $Pic(X_(n+1)) -> Pic(X_n)$ is surjective. 
  
    We claim that $Pic(hat(X)) = invlim_(n>=0) Pic(X_n)$. 
    #proof_[Proof of claim][
      By Grothendieck existence theorem (@grothendieck-existence-thm), as sets, 
      $
        {cal(L) in Coh(hat(X)): j_n^* cal(L) in Pic(X_n)}/cong = invlim_(n>=0) Pic(X_n)
      $
      for $j_n: X_n -> hat(X)$. Now if $cal(L) in Coh(hat(X))$ s.t. each $j_n^* cal(L)$ is invertible. Let $cal(M)_n = (j_n^* cal(L))^(otimes (-1))$. Then for $i_n: X_n -> X_(n+1)$, 
      $
        i_n^* cal(M)_(n+1) cong (i_n^* j_(n+1)^* cal(L))^(otimes (-1)) cong (j_n^* cal(L))^(otimes (-1)) cong cal(M)_n
      $
      Thus by @grothendieck-existence-thm, ${cal(M)_n}$ form an object of $Coh(hat(X), frak(m) cal(O)_(hat(X)))$ and come from a sheaf $cal(M) in Coh(hat(X))$. Then $j_n^* (cal(L) otimes cal(M)) cong cal(O)_(X_n)$ for every $n$, and so by @grothendieck-existence-thm, $cal(L) otimes cal(M) cong cal(O)_(hat(X))$. 
      #suppress-qed
    ]
    Now that $Pic(hat(X)) = invlim_(n>=0) Pic(X_n)$, and every $Pic(X_(n+1)) -> Pic(X_n)$ is surjective, $Pic(hat(X)) -> Pic(X_0)$ must be surjective. 
  
  Now $A$ is the henselization of a finite type $ZZ$-algebra at a prime, so it is the henselization of a finite type algebra over either $QQ$ or $ZZ_((p))$ at a prime, depending on which prime of $ZZ$ the maximal ideal of $A$ lies above. Now $QQ$ is a field and $ZZ_((p))$ is an excellent DVR, so Artin approximation applies over $A$. Consider the functor: 
  $
    F: AAlg(A) -> cSet, B |-> Pic(X otimes_A B)
  $ 
  We have shown that it commutes with directed limits. Thus for any $cal(L)_0 in Pic(X_0)$, lift it to $hat(cal(L)) in Pic(hat(X))$. Then by Artin approximation (@artin-approximation-theorem (2)), there exists $cal(L) in Pic(X)$ that agrees with $hat(cal(L))$ upon pulling back to $X_0$. That is, $cal(L)$ becomes $cal(L)_0$ upon pulling back to $X_0$. Thus $Pic(X) -> Pic(X_0)$ is surjective. 
]

Finally, we deal with degree $>=3$, which boils down to a vanishing result. 
#proposition(name: <pbc-seed-precursor-3>)[
  Let $k$ be a separably closed field, and $X_0$ be proper over $k$ with $dim(X_0) <= 1$. Then: 

  + #h(1fr)
    $
      H^q_et (X_0, ul(ZZ\/n)) = 0
    $
    for all $q>=3$, and for $q=2$ if $n = p^a$ and $p = "char"(k) > 0$. 

  + $
      H^q_et (X_0, GG_m) = 0
    $
    for all $q>=2$. 
]
#proof[
  Let $ol(k)$ be the algebraic closure of $k$, so that $ol(k)\/k$ is a purely inseparable algebraic extension. Now $dim(X_0 otimes_k ol(k)) = dim(X_0) <= 1$. By topological invariance, we may replace $X_0$ with $X_0 otimes_k ol(k)$ and then with its reduction, to assume that $k$ is algebraically closed and $X_0$ is reduced. 

  For the $q>=3$ part of (1), we are done by @grothendieck-vanishing-in-dim-1. Thus for part (1), it suffices to prove that $H^2 (X_0, ul(ZZ\/p^a)) = 0$. If $X_0$ is integral, we are done: (1) is solved by @cohom-of-proj-curve (3), and (2) is solved by @cohom-of-gm-on-general-curve. 
  
  In the general case, let $X_1, dots.c, X_s$ be the irreducible components of $X_0$, equipped with reduced induced subscheme structure. Let $U = X_0 - union.big_(1<=i<j<=s) (X_i inter X_j)$ be the set of points of $X_0$ contained in only one irreducible component. Then $U$ is an open set of $X_0$, and $Z = X_0 - U$ is a finite set of closed points of $X_0$, equipped with reduced induced subscheme structure. Since $k$ is algebraically closed, $Z = union.sq.big_(z in Z) Spec(k)$. We also take $U_i = X_i ∩ U$ to be the set of points of $X_i$ not in any other irreducible component. We use $f_i: X_i -> X_0$ to denote the inclusions. 

  Given a sheaf $cal(F) in cAb(X_et)$, consider the natural map $cal(F) -> oplus.big_(i=1)^s f_(i,*) f_i^(-1) cal(F)$. On stalks, it is the diagonal embedding: 
  $
    cal(F)_(ol(x)) |-> oplus.big_(i: x in X_i) cal(F)_(ol(x))
  $
  which is injective for all $x in X$, and bijective when $x in U$. Thus, taking the cokernel, we have an exact sequence: 
  $
    0 -> cal(F) -> oplus.big_(i=1)^s f_(i,*) f_i^(-1) cal(F) -> cal(R) -> 0
  $
  where $cal(R)|_U = 0$. Let $j: Z -> X$ be the inclusion, and then by @pushforward-by-closed-immersion (2), $cal(R) = j_* cal(G)$ for some $cal(G) in cAb(Z_et)$. Now form the long exact sequence and use @pushforward-by-finite-morphism: 
  $
    dots.c -> H^(q-1) (Z, cal(G)) -> oplus.big_(i=1)^s H^q (X_i, f_i^(-1) cal(F)) -> H^q (X, cal(F)) -> H^q (Z, cal(G)) -> dots.c
  $
  Since $Z = union.sq.big_(z in Z) Spec(k)$, whenever $q>=2$ and so $q-1>=1$, by @struct-of-spec-omega-et, $H^(q-1) (Z, cal(G)) = H^q (Z, cal(G)) = 0$. Thus, 
  $
    H^q (X, cal(F)) cong oplus.big_(i=1)^s H^q (X_i, f_i^(-1) cal(F)), q >= 2
  $

  (1) Take $cal(F) = ul(ZZ\/p^a)$ and applying the result on each $X_i$ (which is integral) concludes the proof. 

  (2) From the argument above, we have: 
  $
    H^q (X, GG_m) cong oplus.big_(i=1)^s H^q (X_i, f_i^(-1) GG_m), q >= 2
  $
  Now consider the canonical map $phi: f_i^(-1) GG_(m,X) -> GG_(m,X_i)$. Since $f_i|_(U ∩ X_i): U ∩ X_i -> U$ is an isomorphism, we see that $phi: f_i^(-1) GG_(m,X) -> GG_(m,X_i)$ is an isomorphism upon restriction to $U ∩ X_i$. Now form the kernel and cokernel: 
  $
    0 -> cal(K) -> f_i^(-1) GG_(m,X) ->^phi GG_(m,X_i) -> cal(R) -> 0
  $
  where $cal(K)|_(U∩X_i) = cal(R)|_(U∩X_i) = 0$. By @pushforward-by-closed-immersion (2), $cal(K), cal(R)$ are pushforwards from sheaves on $Z ∩ X_i = union.sq.big_(z in Z ∩ X_i) Spec(k)$, a set of closed points with residue field $k$. By @pushforward-by-finite-morphism and @struct-of-spec-omega-et, we see that $H^q (X_i, cal(K)) = H^q (X_i, cal(R)) = 0$ for all $q >= 1$. Thus, whenever $q >= 2$, using the long exact sequence: 
  $
    H^q (X_i, f_i^(-1) GG_(m,X)) cong H^q (X_i, im(phi)) cong H^q (X_i, GG_m) = 0
  $
  by applying the result for cohomology of $GG_m$ on $X_i$, which is integral. 
]

We are finally ready to prove (Seed). 

#theorem[
  (Seed) Let $(A, frak(m), k)$ be a strict henselian local ring and $X -> PP^1_A$ be finite. Let $X_0 = X otimes_A k$. Then for all natural numbers $n>=1$, the restriction: 
  $
    H^q (X, ul(ZZ\/n)) -> H^q (X_0, ul(ZZ\/n))
  $
  is an isomorphism for $q = 0$, and surjective for $q >= 1$. 
]
#proof[
  We prove for each degree separately. 

  - Case $q = 0$ is solved by @pbc-point-deg0. 

  - Case $q = 1$: 
    Using @pbc-seed-precursor-0, we may assume that $X$ and $X_0$ are connected. Now by @h1-of-const-sheaf, the restriction morphism $H^1 (X, ul(ZZ\/n)) -> H^1 (X_0, ul(ZZ\/n))$ is just: 
    $
      Hom_#[cont] (pi_1^et (X, ol(x)), ZZ\/n) -> Hom_#[cont] (pi_1^et (X_0, ol(x)), ZZ\/n)
    $
    induced by the morphism $pi_1^et (X_0, ol(x)) -> pi_1^et (X, ol(x))$, induced by $X_0 -> X$. By @pbc-seed-precursor-1, $pi_1^et (X_0, ol(x)) -> pi_1^et (X, ol(x))$ is a continuous isomorphism, and so $Hom_#[cont] (pi_1^et (X, ol(x)), ZZ\/n) -> Hom_#[cont] (pi_1^et (X_0, ol(x)), ZZ\/n)$ is an isomorphism. 

  - Case $q = 2$: 
    By @pbc-seed-precursor-3, $H^2 (X_0, ZZ\/p^a) = 0$ whenever $p = "char"(k) > 0$. We may thus assume $n in k^times$ by splitting out the $p$-part in a direct sum. Since $A$ is local, the inverse of $n in k^times$ lifts to $A$, and so $n in A^times$. 

    Fix a primitive $n$-th root of unity $zeta in k^times$, lifted to a primitive $n$-th root of unity $zeta in A^times$. By @mu-n-is-zn, $zeta$ induces isomorphisms: 
    $
      mu_(n,X) cong ul(ZZ\/n)_X \
      mu_(n,X_0) cong ul(ZZ\/n)_(X_0)
    $
    compatible with pullback. Thus, it suffices to show that the restriction $H^2 (X, mu_n) -> H^2 (X_0, mu_n)$ is surjective. Let $i: X_0 -> X$ be the inclusion, and consider the Kummer sequence: 
    $
      0 -> mu_(n,X) -> GG_(m,X) ->^((-)^n) GG_(m,X) -> 0
    $
    Pulling back along $i$, we get another exact sequence: 
    $
      0 -> i^(-1) mu_(n,X) -> i^(-1) GG_(m,X) ->^((-)^n) i^(-1) GG_(m,X) -> 0
    $
    We claim that the canonical isomorphism $i^(-1) mu_(n,X) cong mu_n$ (established using the identification with constant sheaves above) and the canonical morphism $i^(-1) GG_(m,X) -> GG_(m,X_0)$ fit in a commutative diagram: 
    // https://q.uiver.app/#r=typst&q=WzAsMTAsWzAsMCwiMCJdLFsxLDAsImleKC0xKSBtdV8obixYKSJdLFsyLDAsImleKC0xKSBHR18obSxYKSJdLFszLDAsImleKC0xKSBHR18obSxYKSJdLFs0LDAsIjAiXSxbMCwxLCIwIl0sWzEsMSwibXVfKG4sWF8wKSJdLFsyLDEsIkdHXyhtLFhfMCkiXSxbMywxLCJHR18obSxYXzApIl0sWzQsMSwiMCJdLFswLDFdLFsxLDJdLFsyLDMsIigtKV5uIl0sWzMsNF0sWzUsNl0sWzYsN10sWzcsOCwiKC0pXm4iLDJdLFs4LDldLFsxLDZdLFsyLDddLFszLDhdXQ==
    #align(center, diagram({
      node((-1, -1), [$0$])
      node((0, -1), [$i^(-1) mu_(n,X)$])
      node((1, -1), [$i^(-1) GG_(m,X)$])
      node((2, -1), [$i^(-1) GG_(m,X)$])
      node((3, -1), [$0$])
      node((-1, 0), [$0$])
      node((0, 0), [$mu_(n,X_0)$])
      node((1, 0), [$GG_(m,X_0)$])
      node((2, 0), [$GG_(m,X_0)$])
      node((3, 0), [$0$])
      edge((-1, -1), (0, -1), "->")
      edge((0, -1), (1, -1), "->")
      edge((1, -1), (2, -1), [$(-)^n$], label-side: left, "->")
      edge((2, -1), (3, -1), "->")
      edge((-1, 0), (0, 0), "->")
      edge((0, 0), (1, 0), "->")
      edge((1, 0), (2, 0), [$(-)^n$], label-side: right, "->")
      edge((2, 0), (3, 0), "->")
      edge((0, -1), (0, 0), "->")
      edge((1, -1), (1, 0), "->")
      edge((2, -1), (2, 0), "->")
    }))
    The right square of course commutes, since multiplication by $n$ commutes with anything. For the left square, using adjunction, we only need to show that the square: 
    // https://q.uiver.app/#r=typst&q=WzAsNCxbMCwwLCJtdV8obixYKSJdLFswLDEsImlfKiBtdV8obixYKSJdLFsxLDAsIkdHXyhtLFgpIl0sWzEsMSwiaV8qIEdHXyhtLFgpIl0sWzAsMiwiIiwwLHsic3R5bGUiOnsidGFpbCI6eyJuYW1lIjoiaG9vayIsInNpZGUiOiJ0b3AifX19XSxbMCwxXSxbMiwzXSxbMSwzLCIiLDIseyJzdHlsZSI6eyJ0YWlsIjp7Im5hbWUiOiJob29rIiwic2lkZSI6InRvcCJ9fX1dXQ==
    #align(center, diagram({
      node((0, -1), [$mu_(n,X)$])
      node((0, 0), [$i_* mu_(n,X_0)$])
      node((1, -1), [$GG_(m,X)$])
      node((1, 0), [$i_* GG_(m,X_0)$])
      edge((0, -1), (1, -1), "hook->")
      edge((0, -1), (0, 0), "->")
      edge((1, -1), (1, 0), "->")
      edge((0, 0), (1, 0), "hook->")
    }))
    commutes. Indeed, the morphism $GG_(m,X) -> i_* GG_(m,X_0)$ is $cal(O)_X(U)^times -> cal(O)_(X_0)(U_0)^times$ on sections, induced by the structure maps $U_0 -> U$, and the same goes for $mu_(n,X) -> i_* mu_(n,X_0)$. Passing to long exact sequences, we get a commutative diagram: 
    // https://q.uiver.app/#r=typst&q=WzAsMTUsWzAsMCwiZG90cy5jIl0sWzQsMCwiZG90cy5jIl0sWzEsMCwiSF4xIChYLCBHR19tKSJdLFsyLDAsIkheMiAoWCwgbXVfbikiXSxbMywwLCJIXjIgKFgsIEdHX20pIl0sWzAsMSwiZG90cy5jIl0sWzAsMiwiZG90cy5jIl0sWzQsMSwiZG90cy5jIl0sWzQsMiwiZG90cy5jIl0sWzEsMSwiSF4xIChYXzAsIGleKC0xKSBHR19tKSJdLFsyLDEsIkheMiAoWF8wLCBtdV9uKSJdLFszLDEsIkheMiAoWF8wLCBpXigtMSkgR0dfbSkiXSxbMSwyLCJIXjEgKFhfMCwgR0dfbSkiXSxbMywyLCJIXjIgKFhfMCwgR0dfbSkiXSxbMiwyLCJIXjIgKFhfMCwgbXVfbikiXSxbMCwyXSxbMiwzXSxbMyw0XSxbNCwxXSxbNSw5XSxbOSwxMF0sWzEwLDExXSxbMTEsN10sWzYsMTJdLFsxMiwxNF0sWzE0LDEzXSxbMTMsOF0sWzIsOV0sWzksMTJdLFszLDEwXSxbMTAsMTQsIiIsMSx7InN0eWxlIjp7ImhlYWQiOnsibmFtZSI6ImVwaSJ9fX1dLFs0LDExXSxbMTEsMTNdXQ==
    #align(center, diagram({
      node((-2, -1), [$dots.c$])
      node((2, -1), [$dots.c$])
      node((-1, -1), [$H^1 (X, GG_m)$])
      node((0, -1), [$H^2 (X, mu_n)$])
      node((1, -1), [$H^2 (X, GG_m)$])
      node((-2, 0), [$dots.c$])
      node((-2, 1), [$dots.c$])
      node((2, 0), [$dots.c$])
      node((2, 1), [$dots.c$])
      node((-1, 0), [$H^1 (X_0, i^(-1) GG_m)$])
      node((0, 0), [$H^2 (X_0, mu_n)$])
      node((1, 0), [$H^2 (X_0, i^(-1) GG_m)$])
      node((-1, 1), [$H^1 (X_0, GG_m)$])
      node((1, 1), [$H^2 (X_0, GG_m)$])
      node((0, 1), [$H^2 (X_0, mu_n)$])
      edge((-2, -1), (-1, -1), "->")
      edge((-1, -1), (0, -1), "->")
      edge((0, -1), (1, -1), "->")
      edge((1, -1), (2, -1), "->")
      edge((-2, 0), (-1, 0), "->")
      edge((-1, 0), (0, 0), "->")
      edge((0, 0), (1, 0), "->")
      edge((1, 0), (2, 0), "->")
      edge((-2, 1), (-1, 1), "->")
      edge((-1, 1), (0, 1), "->")
      edge((0, 1), (1, 1), "->")
      edge((1, 1), (2, 1), "->")
      edge((-1, -1), (-1, 0), "->")
      edge((-1, 0), (-1, 1), "->")
      edge((0, -1), (0, 0), "->")
      edge((0, 0), (0, 1), "=")
      edge((1, -1), (1, 0), "->")
      edge((1, 0), (1, 1), "->")
    }))
    with the first row of vertical arrows being restrictions, and the second row induced by our commutative diagram of short exact sequences established above. Now using @h1-of-gm-is-pic and unfolding the definitions, we see that the first column of vertical arrows is just $Pic(X) -> Pic(X_0)$, surjective by @pbc-seed-precursor-2. Also by @pbc-seed-precursor-3, $H^2 (X_0, GG_m) = 0$. Thus, we have a commutative diagram: 
    // https://q.uiver.app/#r=typst&q=WzAsOSxbMCwwLCJkb3RzLmMiXSxbMSwwLCJQaWMoWCkiXSxbMiwwLCJIXjIgKFgsIG11X24pIl0sWzMsMCwiSF4yIChYLCBHR19tKSJdLFs0LDAsImRvdHMuYyJdLFszLDEsIjAiXSxbMCwxLCJkb3RzLmMiXSxbMSwxLCJQaWMoWF8wKSJdLFsyLDEsIkheMiAoWF8wLCBtdV9uKSJdLFswLDFdLFsxLDJdLFsyLDNdLFszLDRdLFs2LDddLFs3LDgsIiIsMCx7InN0eWxlIjp7ImhlYWQiOnsibmFtZSI6ImVwaSJ9fX1dLFs4LDVdLFsxLDcsIiIsMSx7InN0eWxlIjp7ImhlYWQiOnsibmFtZSI6ImVwaSJ9fX1dLFsyLDhdXQ==
    #align(center, diagram({
      node((-2, -1), [$dots.c$])
      node((-1, -1), [$Pic(X)$])
      node((0, -1), [$H^2 (X, mu_n)$])
      node((1, -1), [$H^2 (X, GG_m)$])
      node((2, -1), [$dots.c$])
      node((1, 0), [$0$])
      node((-2, 0), [$dots.c$])
      node((-1, 0), [$Pic(X_0)$])
      node((0, 0), [$H^2 (X_0, mu_n)$])
      edge((-2, -1), (-1, -1), "->")
      edge((-1, -1), (0, -1), "->")
      edge((0, -1), (1, -1), "->")
      edge((1, -1), (2, -1), "->")
      edge((-2, 0), (-1, 0), "->")
      edge((-1, 0), (0, 0), "->>")
      edge((0, 0), (1, 0), "->")
      edge((-1, -1), (-1, 0), "->>")
      edge((0, -1), (0, 0), "->")
    }))
    Hence the restriction $H^2 (X, mu_n) -> H^2 (X_0, mu_n)$ is surjective, and we are done. 

  - Case $q >= 3$: $H^q (X_0, ul(ZZ\/n)) = 0$ by @pbc-seed-precursor-3, so the restriction $H^q (X, ul(ZZ\/n)) -> H^q (X_0, ul(ZZ\/n))$ is automatically surjective. 
]

With (Seed) verified, every step in the proof of the proper base change theorem has been established. As such, we have fully proved the proper base change theorem (@proper-base-change, up to a locally noetherian assumption): 

- Consider a Cartesian diagram: #h(1fr)
  // https://q.uiver.app/#r=typst&q=WzAsNCxbMCwwLCJYJyJdLFsxLDAsIlknIl0sWzAsMSwiWCJdLFsxLDEsIlkiXSxbMiwzLCJmIl0sWzAsMSwiZiciXSxbMSwzLCJnIl0sWzAsMiwiZyciLDJdXQ==
  #align(center, diagram({
    node((-1, -1), [$X'$])
    node((0, -1), [$Y'$])
    node((-1, 0), [$X$])
    node((0, 0), [$Y$])
    node((-0.7, -0.7), $cart$)
    edge((-1, 0), (0, 0), [$f$], label-side: left, "->")
    edge((-1, -1), (0, -1), [$f'$], label-side: left, "->")
    edge((0, -1), (0, 0), [$g$], label-side: left, "->")
    edge((-1, -1), (-1, 0), [$g'$], label-side: right, "->")
  }))
  If $f$ is proper and $Y, Y'$ are locally noetherian, then for all torsion sheaves $cal(F) in cAb(X_et)$, the base change morphism: 
  $
    g^(-1) R^q f_* cal(F) -> R^q f'_* g'^(-1) cal(F)
  $
  is an isomorphism. 
