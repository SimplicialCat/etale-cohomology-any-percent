#import "void-import.typ": *

== Finiteness of $R f_!$

In this section, we establish the smooth proper base change theorem and finiteness of $R f_!$, that: 

- $R f_*$ for $f$ proper smooth preserves l.c.c. sheaves; 

- $R f_!$ for $f$ separated of finite type preserves constructible sheaves. 

The heavy workload of the proof will be done via an application of local acyclicity, in an elegant round of interplay between proper base change, local acyclicity, and constructible sheaf devissage. 

The proofs for proper smooth base change and for finiteness of $R f_!$ intertwine, so we prove a lemma for dimension $1$ to bootstrap the induction. 

#lemma(name: <proper-smooth-base-change-bootstrap>)[
  (Proper smooth base change for dimension $1$) Let $f: X -> Y$ be a proper morphism with fiber dimensions $<=1$. Then, for any natural number $n in cal(O)_Y^times$, the sheaves $R^q f_* ul(ZZ\/n)$ are l.c.c. for all $q>=0$. 
]
#proof[
  We first show that $R^q f_* ul(ZZ\/n)$ has finite stalks. By proper base change $(R^q f_* ul(ZZ\/n))_(ol(y)) = H^q (X_(ol(y)), ul(ZZ\/n))$. These stalks are finite abelian groups by the following lemma: 
  
  #lemma[
    For any finite type scheme $X$ of dimension $<=1$ proper over an algebraically closed field $k$, the groups $H^q (X, ul(ZZ\/n))$ are finite.  
  ]
  #proof[
    By Grothendieck vanishing, it suffices to deal with $q = 0,1,2$. $H^0 (X, ul(ZZ\/n)) = (ZZ\/n)^(pi_0 (X))$ is finite because $X$ has only finitely many irreducible components, so it suffices to deal with $q = 1,2$. 

    Let $X_1, dots.c, X_m$ be the irreducible components of $X$ equipped with the reduced substructure, with inclusions $i_j: X_j -> X$. We have a short exact sequence: 
    $
      0 -> ul(ZZ\/n)_X -> oplus.big_(j=1)^m i_(j,*) ul(ZZ\/n) -> cal(R) -> 0
    $
    Here, $cal(R)$ is supported on a finite set of closed points, and so $H^q (X, cal(R)) = 0$ for all $q >= 1$. We thus have an exact sequence: 
    $
      dots.c -> H^0 (X, cal(R)) -> H^1 (X, ul(ZZ\/n)) -> oplus.big_(j=1)^m H^1 (X_j, ul(ZZ\/n)) -> 0
    $
    and an isomorphism $H^2 (X, ul(ZZ\/n)) cong oplus.big_(j=1)^m H^2 (X_j, ul(ZZ\/n))$. $H^0$ is finite as argued above. Thus, it suffices to prove that $H^q (X_j, ul(ZZ\/n))$ are finite for $q=1,2$, and so we may assume that $X$ is integral by replacing $X$ with $X_j$. 

    Now consider the normalization $nu: X' -> X$. Then $nu$ is finite surjective and $X'$ is a smooth projective curve. Since $nu$ is surjective, $ul(ZZ\/n) -> nu_* ul(ZZ\/n)$ is injective by @surjection-has-injective-unit. Thus we may form a short exact sequence: 
    $
      0 -> ul(ZZ\/n) -> nu_* ul(ZZ\/n) -> cal(R) -> 0
    $
    $nu$ is an isomorphism on a dense open $U -> X$, and so $ul(ZZ\/n) -> nu_* ul(ZZ\/n)$ is an isomorphism on a dense open $U -> X$. Thus $cal(R)$ is supported on a finite set of closed points. Similarly we have an exact sequence: 
    $
      dots.c -> H^0 (X, cal(R)) -> H^1 (X, ul(ZZ\/n)) -> H^1 (X', ul(ZZ\/n)) -> dots.c
    $
    and an isomorphism $H^2 (X', ul(ZZ\/n)) cong H^2 (X, ul(ZZ\/n))$. Thus, we may replace $X$ with $X'$ and assume that $X$ is a smooth projective curve. Now $H^q (X, ul(ZZ\/n))$ are finite abelian groups by @cohom-of-proj-curve. 
  ]

  Now that $R^q f_* ul(ZZ\/n)$ has finite stalks, to show that these sheaves are l.c.c, it suffices to show that all specialization maps are isomorphisms by @descs-of-lcc-sheaves. This follows from @loc-acyc-of-smooth-maps (local acyclicity of smooth morphisms) and @proper-loc-acyc-bc. 
]

#theorem(name: <finiteness-of-lower-shriek>)[
  (Finiteness of $R f_!$) Let $f: X -> Y$ be a separated morphism of finite type between noetherian schemes, and let $Lambda$ be an $n$-torsion noetherian ring s.t. $n in cal(O)_Y^times$. 
  
  Then for any constructible sheaf $cal(F)$ of $Lambda$-modules on $X$, $R^q f_! cal(F)$ are constructible sheaves of $Lambda$-modules on $Y$. Together with Grothendieck vanishing, this gives the derived statement, that $R f_!: D(X_et, Lambda) -> D(Y_et, Lambda)$ restricts to a functor: 
  $
    R f_!: D^b_c (X_et, Lambda) -> D^b_c (Y_et, Lambda)
  $
  i.e. $R f_!$ preserves $D^b_c$. 
]
#proof[
  We will first assume that $Lambda = ZZ\/n$. //For any constructible sheaf $cal(F) in cAb_c (X_et, ZZ\/n)$, consider: 
  // $
  //   cal(S) = {Z subset Y #[closed] : (R^q f_! cal(F))|_Z #[is not constructible for some $q$]}
  // $
  // Suppose that $cal(S) != emptyset$. By noetherian induction, $cal(S)$ has a minimal element $Z$. Suppose for contradiction that $(R^q f_! cal(F))|_Z$ is not constructible, but $Z$ is not irreducible with irreducible components $Z_1, dots.c, Z_m$. Then by minimality, each $(R^q f_! cal(F))|_(Z_i)$ is constructible. For every irreducible closed subset $W subset Z$, $W subset Z_i$ for some $Z_i$, and so according to @constructible-sheaves-first-props (2), by constructibility of $(R^q f_! cal(F))|_(Z_i)$, there exists a nonempty open $U subset W$ s.t. $(R^q f_! cal(F))|_W$ is l.c.c. Thus by @constructible-sheaves-first-props (2), $(R^q f_! cal(F))|_Z$ is constructible, a contradiction to $Z in cal(S)$. 

  // Thus, $Z$ has to be irreducible. Equip $Z$ with the reduced substructure, we may assume that $Z$ is integral. By proper base change $(R^q f_! cal(F))|_Z = R^q f_(Z,!) (cal(F)|_(X_Z))$ where $f_Z: X_Z -> Z$ is the base change of $f$ along $Z -> Y$. $cal(F)|_(X_Z)$ is constructible, so by replacing $f$ with $f_Z$, we may assume that: 

  // - $X$ is integral; 

  // - For all proper closed subscheme $Z subset.neq X$ and all $q>=0$, $(R^q f_! cal(F))|_Z$ is constructible. 

  // Now pick an affine open $j: U -> Y$ with complementary closed immersion $i: Z -> Y$. We have an extension by zero triangle: 
  // $
  //   j_! (R f_! cal(F)|_U) -> R f_! cal(F) -> i_* (R f_! cal(F)|_Z) ->^(+1)
  // $
  // Since we assumed $R f_! cal(F)|_Z in D^b_c (Z_et, ZZ\/n)$, we have $i_* (R f_! cal(F)|_Z) in D^b_c (Y_et, ZZ\/n)$. Thus, to show that $R f_! cal(F) in D^b_c (X_et, ZZ\/n)$, it suffices to show
  
  // Form a Cartesian diagram: 
  // // // https://q.uiver.app/#r=typst&q=WzAsNixbMCwwLCJYX1UiXSxbMCwxLCJVIl0sWzEsMSwiWSJdLFsyLDEsIloiXSxbMSwwLCJYIl0sWzIsMCwiWF9aIl0sWzEsMiwiaiIsMl0sWzMsMiwiaSJdLFswLDQsImonIl0sWzUsNCwiaSciLDJdLFs0LDIsImYiXSxbNSwzLCJmX1oiXSxbMCwxLCJmX1UiLDJdXQ==
  // // #align(center, diagram({
  // //   node((0, 0), [$X_U$])
  // //   node((0, 1), [$U$])
  // //   node((1, 1), [$Y$])
  // //   node((2, 1), [$Z$])
  // //   node((1, 0), [$X$])
  // //   node((2, 0), [$X_Z$])
  // //   edge((0, 1), (1, 1), [$j$], label-side: right, "->")
  // //   edge((2, 1), (1, 1), [$i$], label-side: left, "->")
  // //   edge((0, 0), (1, 0), [$j'$], label-side: left, "->")
  // //   edge((2, 0), (1, 0), [$i'$], label-side: right, "->")
  // //   edge((1, 0), (1, 1), [$f$], label-side: left, "->")
  // //   edge((2, 0), (2, 1), [$f_Z$], label-side: left, "->")
  // //   edge((0, 0), (0, 1), [$f_U$], label-side: right, "->")
  // // }))
  // // Now have the extension by zero triangle: 
  // // $
  // //   R(f compose j')_! j'^(-1) cal(F) -> R f_! cal(F) -> R(f compose i')_! i'^(-1) cal(F) ->^(+1)
  // // $
  
  First, we may show that the sheaf statement and the derived statement are equivalent. Indeed, the derived statement is clearly stronger. Suppose we have the sheaf statement. Then for $cal(K) in D^b_c (X_et, ZZ\/n)$, we have a hypercohomology spectral sequence: 
  $
    E_1^(p,q) = R^q f_! (h^p (cal(K))) => h^(p+q) (R f_! cal(K))
  $
  The sheaf statement would imply that each $E_1^(p,q)$ is constructible. By Grothendieck vanishing, $E_1^(p,q)$ is supported in a bounded rectangle. Thus every $h^(p+q) (R f_! cal(K))$ is an extension of finitely many constructible sheaves, hence constructible. Thus $R f_! cal(K) in D^b_c (Y_et, ZZ\/n)$. We now focus on the sheaf statement. 

  By @constructible-sheaves-first-props (2), it suffices to show that for every irreducible closed subset $Z subset Y$ (with reduced substructure), there exists a nonempty open $V subset Z$ of $Z$ s.t. $(R^q f_! cal(F))|_V$ is constructible. 

  Pick $V$ to be any affine open of $Z$, and form the base change $f_V: X_V -> V$ of $f$ along $V -> Y$. Then: 
  $
    (R^q f_! cal(F))|_V = R^q f_(V,!) (cal(F)|_(X_V))
  $
  Since $cal(F)|_(X_V)$ is constructible, we may replace $f$ by $f_V$. We may thus assume that: 

  - $Y$ is an integral affine scheme. 

  Suppose that we have shown that every $R^q f_!$ preserves constructible sheaves under the additional assumption that $X$ is affine. Then in the general case, let $X = union.big_(i=1)^k X_i$ be covered by $k$ affine opens. Let $j_1: X_1 -> X$ be the open immersion, and $i_1: Z_1 = X - X_1 -> X$ be the complementary closed immersion. We then have an extension by zero triangle: 
  $
    R(f compose j_1)_! j_1^(-1) cal(F) -> R f_! cal(F) -> R(f compose i_1)_! i_1^(-1) cal(F) ->^(+1)
  $
  By the case when $X$ is affine, $R(f compose j_1)_! j_1^(-1) cal(F) in D^b_c (Y_et, ZZ\/n)$. Thus, to show that $R f_! cal(F) in D^b_c (Y_et, ZZ\/n)$, it suffices to show that $R(f compose i_1)_! i_1^(-1) cal(F) in D^b_c (Y_et, ZZ\/n)$. Now $Z_1 = union.big_(i=2)^k (X_i inter Z_1)$. Each $X_i inter Z_1$ is a closed subscheme of the affine scheme $X_i$, hence affine. Thus, $Z_1$ is covered by at most $(k-1)$ open affines. Performing induction on the minimum number of open affines necessary to cover $X$ allows us to assume $R(f compose i_1)_! i_1^(-1) cal(F) in D^b_c (Y_et, ZZ\/n)$, concluding the proof for the general case. 

  We may thus assume further that: 

  - $Y = Spec(A)$ is affine integral, and $X = Spec(B)$ is affine. 

  Since $X -> Y$ is of finite type, $B$ is a finite type $A$-algebra. Thus, writing $B = A[x_1, dots.c, x_d]\/I$, we may factor $f$ into: 
  $
    X ->^i AA^d_Y ->^(p_d) AA^(d-1)_Y ->^(p_(d-1)) dots.c -> AA^1_Y ->^(p_1) Y
  $
  where the first map is a closed immersion, and all subsequent maps are projections of the shape $AA^1_S -> S$. 
  
  By @finite-morphisms-and-constructible-sheaves, $i_* cal(F)$ is constructible. If we can prove that each $p_j$ has $R p_(j,!)$ preserving $D^b_c$, then: 
  $
    R f_! cal(F) = R p_(1,!) dots.c R p_(d,!) i_* cal(F) in D^b_c (Y_et, ZZ\/n)
  $
  and that would conclude the proof. Thus, by replacing $f$ with one of the projections $p_j$, we may assume that: 

  - $Y = Spec(A)$ is affine integral, and $X = AA^1_Y$, with $f: AA^1_Y -> Y$ the projection. 

  For a constructible sheaf $cal(F) in cAb(X_et, ZZ\/n)$, by @constructible-sheaves-first-props (4), there exists a quasi-compact etale morphism $j: U -> X$ and a surjection $j_! ul(ZZ\/n) -> cal(F)$. Covering $U$ by affine opens $j_i: U_i -> U$, we may replace $U$ with $union.sq.big_i U_i$ and use the surjection $oplus.big_i j_! j_(i,!) ul(ZZ\/n) -> j_! ul(ZZ\/n)$ to assume that $j$ is affine. Repeating this resolution process, we may find a resolution: 
  $
    dots.c -> cal(P)^(-1) -> cal(P)^0 -> cal(F) -> 0
  $
  of $cal(F)$ s.t. each $cal(P)^(-p) = j_(p,!) ul(ZZ\/n)$ for an affine etale $j_p: U_p -> X$. Then $R f_! cal(F) = R f_! cal(P)^bullet$, and we have a hypercohomology spectral sequence: 
  $
    E_1^(p,q) = R^q f_! cal(P)^p => R^(p+q) f_! cal(F)
  $
  which is bounded in $q$. Thus, if we can show that every $E_1^(p,q)$ is constructible, then every $R^q f_! cal(F)$ is an extension of finitely many constructible sheaves, hence constructible. 

  Thus, it suffices to show that every $R^q f_! j_(p,!) ul(ZZ\/n) = R^q (f compose j_p)_! ul(ZZ\/n)$ is constructible. Fix an affine etale $j: U -> X = AA^1_Y$, and it remains to show that: 
  $
    R^q f_! j_! ul(ZZ\/n)
  $
  are all constructible. For every integral closed subscheme $Z subset Y$, $(R^q f_! j_! ul(ZZ\/n))|_Z = R^q f_(Z,!) j_(Z,!) ul(ZZ\/n)$ by proper base change, where $f_Z: AA^1_Z -> Z$, and $j_Z: U_Z -> AA^1_Z$ remains affine etale. Thus by @constructible-sheaves-first-props (2), (upon replacing $f, j$ with $f_Z, j_Z$,) we only need to show that there exists an affine open $V subset Y$ s.t: 
  $
    (R^q f_! j_! ul(ZZ\/n))|_V = R^q f_(V,!) j_(V,!) ul(ZZ\/n)
  $
  is constructible. Put $g = f compose j: U -> Y$. 

  Let $K$ be the function field of $Y$, and let $L\/K$ be the perfect closure of $K$. (That is, $L$ is the subfield of $ol(K)$ obtained by adjoining all $p^m$-th roots of elements of $K$ for all $m$, if $"char"(K) = p$. For $"char"(K) = 0$, $L = K$.) In particular, $L$ is a perfect field. Then base changing $f$ and $j$, we get: 
  $
    g_L: U_L ->^(j_L) AA^1_L ->^(f_L) Spec(L)
  $
  which is an affine smooth morphism of relative dimension 1. 
  
  #lemma[
    Let $K$ be a perfect field, and $f: X -> Spec(K)$ be smooth of relative dimension 1 for an integral affine scheme $X$. Then $f$ admits a compactification: 
    $
      X ->^j ol(X) ->^(ol(f)) Spec(K)
    $
    in which $ol(f): ol(X) -> Spec(K)$ is proper and smooth, and $ol(X) - X$ is finite over $Spec(K)$ (i.e. a finite set of closed points). 
  ]
  #proof[
    Pick an arbitrary affine embedding $X -> AA^d_K$, giving a projective closure $X_1 -> PP^d_K$. This gives a compactification: 
    $
      X ->^h X_1 ->^(f_1) Spec(K)
    $
    in which $f_1$ is projective and $X_1$ is integral. $X$ is dense in its projective closure $X_1$, so $X_1$ is of dimension 1 and $X_1 - X$ has a smaller dimension, i.e. dimension 0. Thus $X_1 - X$ is a finite set of points. 

    Let $nu: ol(X) -> X_1$ be the normalization of $X_1$, which is a finite map. Now $X$ is normal for being smooth over a field, and $h: X -> X_1$ is dominant. Thus by the universal property of normalization, $h$ factors uniquely as $X ->^j ol(X) ->^nu X_1$. $nu$ is an isomorphism above the normal locus of $X_1$, and since $X$ is normal, $nu$ is in particular an isomorphism above the image $h(X)$. Thus, $j: X -> ol(X)$ is an open immersion. This gives a compactification: 
    $
      X ->^j ol(X) ->^(ol(f)) Spec(K)
    $
    in which $ol(X)$ is normal and of dimension 1. Now for every finite field extension $L\/K$, since $K$ is perfect, $L\/K$ is separable, and $Spec(L) -> Spec(K)$ is etale. Thus the base change $ol(X)_L -> ol(X)$ is etale. Since $ol(X)$ is normal, by @etale-local-properties (5), $ol(X)_L$ is normal. Since $ol(X)_L$ is of dimension 1, it must be regular. Hence we have shown that $ol(X)$ is geometrically regular over $K$, thus smooth over $K$. Hence $ol(f)$ is proper smooth. Furthermore, $ol(X) - X$ is finite over $X_1 - X$ since $nu$ is finite. Thus $ol(X) - X$ is finite over $K$. 
  ]

  By the previous lemma, $g_L$ has a compactification: 
  $
    g_L: U_L ->^(h_L) U'_L ->^(r_L) Spec(L)
  $
  in which $U'_L - h_L (U_L)$ is finite over $L$, and $r_L$ is proper smooth. 

  Recall $L$ is $K$ with every $p^m$-th root adjoined when $"char"(K) = p$, and $L = K$ when $"char"(K) = 0$. Now: 

  - When $"char"(K) = p$, every element $x in L$ is in $K(x_1^(p^(-m_1)), dots.c, x_s^(p^(-m_s)))$ for some finite set $x_1, dots.c, x_s in K$ and powers $m_1, dots.c, m_s >= 1$. Write $x = display((alpha(x_1^(p^(-m_1)), dots.c, x_s^(p^(-m_s))))/(beta(x_1^(p^(-m_1)), dots.c, x_s^(p^(-m_s)))))$ for polynomials $alpha, beta$, and $0 != beta_0 = beta(x_1^(p^(-m_1)), dots.c, x_s^(p^(-m_s))) in L$. Thus there exists some $m_0$ s.t. $x_0 = beta_0^(p^(m_0)) in K$. Thus $x in K[x_1^(p^(-m_1)), dots.c, x_s^(p^(-m_s)), x_0^(p^(-m_0))]$. Now the coefficients of a polynomial representation of $x$ must lie in $A_u$ for some fixed $u in A^times$, so: 
    $
      x in A_u [x_0^(p^(-m_0)), dots.c, x_s^(p^(-m_s))]
    $
    for some fixed $u in A^times$, some $x_0, dots.c, x_s in A_u$, and some powers $m_0, dots.c, m_s >= 0$. 

    For these algebras, $Spec(A_u) -> Spec(A)$ is a principal affine open, and $Spec(A_u [x_0^(p^(-m_0)), dots.c, x_s^(p^(-m_s))]) -> Spec(A_u)$ is a finite universal homeomorphism by @adjoining-pth-root-in-char-p-is-univ-homeo. 

    In other words, $L = dirlim_R R$ where each $R$ is a finite surjective radicial $A_u$-algebra for some $u in A^times$. 

  - When $"char"(K) = 0$, $L = K = dirlim_(u in A^times) A_u$, so the same conclusion as in characteristic $p$ still holds. 

  Applying @passage-to-limit-of-morphisms and @passage-to-limit-of-properties (2e)(3f), we see that there exists $u in A^times$ and a finite surjective radicial $A_u$-algebra $R$ s.t. $g_R: U_R -> Spec(R)$ admits a compactification: 
  $
    g_R: U_R ->^(h_R) U'_R ->^(r_R) Spec(R)
  $
  in which $r_R$ is proper smooth, and $U'_R - h_R (U_R)$ is finite over $Spec(R)$. In particular, every fiber of $U'_R -> Spec(R)$ differs from the corresponding fiber of $U_R$ by finitely many closed points, and hence has dimension $<=1$. Now: 
  $
    (R g_! ul(ZZ\/n))|_(Spec(R)) = R g_(R,!) ul(ZZ\/n) = R r_(R,*) h_(R,!) ul(ZZ\/n) 
  $
  Let $ell_R: Z_R = U'_R - h_R (U_R) -> U'_R$ be the complementary closed immersion to $h_R$, and so $r_R compose ell_R$ is finite. Then we have an extension by zero triangle: 
  $
    R r_(R,*) h_(R,!) ul(ZZ\/n) -> R r_(R,*) ul(ZZ\/n) -> R r_(R,*) ell_(R,*) ul(ZZ\/n)
  $
  Now: 

  - By the bootstrap lemma @proper-smooth-base-change-bootstrap, since $r_R$ is proper smooth with fiber dimensions $<=1$, the sheaves $R^q r_(R,*) ul(ZZ\/n)$ are all l.c.c. Thus, 
    $
      R r_(R,*) ul(ZZ\/n) in D^b_c (Spec(R)_et, ZZ\/n)
    $

  - $R r_(R,*) ell_(R,*) ul(ZZ\/n) = R(r_R compose ell_R)_* ul(ZZ\/n) in D^b_c (Spec(R)_et, ZZ\/n)$ by @finite-morphisms-and-constructible-sheaves. 

  Hence, $(R g_! ul(ZZ\/n))|_(Spec(R)) = R r_(R,*) h_(R,!) ul(ZZ\/n) in D^b_c (Spec(R)_et, ZZ\/n)$, and so every: 
  $
    (R^q g_! ul(ZZ\/n))|_(Spec(R))
  $
  is constructible. $Spec(R) -> Spec(A_u)$ is finite surjective radicial, hence a universal homeomorphism. Thus by topological invariance, $(R^q g_! ul(ZZ\/n))|_(Spec(A_u))$ is constructible. 
  
  We are thereby done. This concludes the proof for $Lambda = ZZ\/n$. 

  For general $n$-torsion noetherian $Lambda$, the same argument as in $Lambda = ZZ\/n$ allows us to assume $cal(F) = ul(Lambda)$. Then by the projection formula, 
  $
    R f_! ul(Lambda) = R f_! ul(ZZ\/n) Lotimes_(ZZ\/n) ul(Lambda)
  $
  By truncation triangles, it suffices to show that each $R^q f_! ul(ZZ\/n) Lotimes_(ZZ\/n) ul(Lambda) in D^b_c (Y_et, Lambda)$. Since $R^q f_! ul(ZZ\/n)$ is constructible, we may resolve it as $dots.c -> cal(P)^(-1) -> cal(P)^0 -> R^q f_! ul(ZZ\/n)$ in which every $cal(P)^p = j_(-p,!) ul(ZZ\/n)$ for quasi-compact etale $j_p: U_p -> Y$. Now each $cal(P)^p$ is flat as a sheaf of $ul(ZZ\/n)$-modules, so: 
  $
    h^p (R^q f_! ul(ZZ\/n) Lotimes_(ZZ\/n) ul(Lambda)) = h^p (cal(P)^bullet otimes_(ZZ\/n) ul(Lambda))
  $
  Each $cal(P)^p otimes_(ZZ\/n) ul(Lambda) = j_(-p,!) ul(Lambda)$ is a constructible sheaf of $Lambda$-modules, so each $h^p (R^q f_! ul(ZZ\/n) Lotimes_(ZZ\/n) ul(Lambda))$ is a constructible sheaf of $Lambda$-modules. We are thus done with the general coefficient case. 
]

#theorem[
  (Proper smooth base change) Let $f: X -> Y$ be a smooth proper morphism between noetherian schemes, and $Lambda$ be an $n$-torsion noetherian ring s.t. $n in cal(O)_Y^times$. Let $cal(F) in cAb(X_et, Lambda)$ be a l.c.c. sheaf of $Lambda$-modules on $X$. Then every $R^q f_* cal(F)$ is an l.c.c. sheaf of $Lambda$-modules on $Y$. 
]
#proof[
  By @loc-acyc-of-smooth-maps, $f$ is locally acyclic relative to $cal(F)$ as a smooth map. Thus by @proper-loc-acyc-bc, the sheaves $R^q f_* cal(F)$ have all specialization maps being isomorphisms. By @finiteness-of-lower-shriek, the $R^q f_* cal(F)$ are constructible sheaves of $Lambda$-modules, hence have finite $Lambda$-module stalks. Thus by @descs-of-lcc-sheaves, the $R^q f_* cal(F)$ are all l.c.c. sheaves. 
]
