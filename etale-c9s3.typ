#import "void-import.typ": *

== Generic base change and finiteness

In this section, we establish the generic base change theorem, that for $f$ a morphism between finite type schemes over a base, the formation of $R f_*$ preserves $D^b_c$ and is compatible with base change, up to shrinking the base to a dense open. As an application, we establish the projection and Kunneth formulas - not for $R f_!$, but for $R f_*$. In its proof, Poincare duality will be used to bootstrap the last step, after a chain of reductions. 

The proof method used in this section closely follows that of @cite-lei-fu[Section 9.3] with order rearrangements and minor variations. It is ultimately the method of @cite-SGA4half. 

#theorem(name: <generic-base-change>)[
  (Generic finiteness and base change) Let $Lambda$ be an $n$-torsion noetherian ring. Let $S$ be a noetherian $ZZ[n^(-1)]$-scheme and $f: X -> Y$ be a morphism between finite type $S$-schemes. Then for any $cal(K) in D^b_c (X_et, Lambda)$, there exists a dense open $U subset S$ s.t: 

  - $R f_(U,*) (cal(K)|_(X_U)) in D^b_c ((Y_U)_et, Lambda)$, where $f_U: X_U -> Y_U$ is the base change of $f$ along $U -> S$; 

  - For any Cartesian diagram: #h(1fr)
    #align(center, diagram({
      node((0, 0), [$X'$])
      node((1, 0), [$Y'$])
      node((0, 1), [$X$])
      node((1, 1), [$Y$])
      // node((0.3, 0.3), [$cart$])
      node((2, 1), [$S$])
      node((2, 0), [$S'$])
      edge((0, 1), (1, 1), [$f$], label-side: right, "->")
      edge((0, 0), (1, 0), [$f'$], label-side: left, "->")
      edge((1, 0), (2, 0), "->")
      edge((1, 1), (2, 1), "->")
      edge((1, 0), (1, 1), [$g_Y$], label-side: left, "->")
      edge((2, 0), (2, 1), [$g$], label-side: left, "->")
      edge((0, 0), (0, 1), [$g_X$], label-side: right, "->")
    }))
    in which $g(S') subset U$, 
    $
      g_Y^(-1) R f_* cal(K) -> R f'_* g_X^(-1) cal(K)
    $
    is an isomorphism. 
]
#proof[
  #notation[
    An open subset $U subset S$ for which the theorem above holds will be called an *$(f, cal(K), S)$-good* open for the duration of this proof. It can be seen that: 

    - When $f$ is proper, $S$ itself is $(f, cal(K), S)$-good. (This is due to proper base change and finiteness of $R f_*$ (@finiteness-of-lower-shriek).)

    - For $X ->^f Y ->^g Z$, if $U subset S$ is $(f, cal(K), S)$ good, then $U$ is $(g_U, R f_(U,*) (cal(K)|_(X_U)), S)$-good if and only if it is $(g compose f, cal(K), S)$-good. One can check this from the definition. 

      // Conversely, if $U subset S$ is $(g compose f, cal(K))$-good and $(f, cal(K))$-good, then it is also $(g, R f_(U,*) (cal(K)|_(X_U)))$-good. 

    - Given a distinguished triangle $cal(K)_1 -> cal(K)_2 -> cal(K)_3 ->^(+1)$ in $D^b_c (X_et, Lambda)$, if $U subset S$ is $(f, cal(K)_i, S)$-good for $i=1,2$, then it is also $(f, cal(K)_3, S)$-good. 
  ]

  Note that: 

  - Let $S$ have irreducible components $S_1, dots.c, S_m$, and let $U = S - union.big_(i<j) (S_i inter S_j)$. Then $U$ is a dense open of $S$ that is a disjoint union of its irreducible components. By shrinking $S$ to $U$ we may argue on each irreducible component separately, and thus assume that $S$ is irreducible. Base change to the reduction of $S$ and use topological invariance, we may thus from now on assume that $S$ is integral with generic point $sigma = Spec(K(S))$. By shrinking $S$ to any affine open, we may also assume that $S$ is affine. 

  - This problem is local in $Y$. Indeed, for an affine cover ${Y_i}$ of $Y$ consisting of finitely many opens, base change $f$ to $f_i: X_i -> Y_i$ and $cal(K)_i := cal(K)|_(X_i)$. Then if dense opens $U_i subset S$ are $(f_i, cal(K)_i, S)$-good, one can easily check that $inter.big_i U_i$ is $(f, cal(K), S)$-good. Hence, we may base change $f$ to an affine open of $Y$ whenever necessary. 

  #lemma[
    TFAE: 

    - For every morphism $f: X -> Y$ of finite type $S$-schemes in which $dim(X_sigma) <= d$ and every $cal(K) in D^b_c (X_et, Lambda)$, there is an $(f, cal(K), S)$-good open dense of $S$; 

    - For every open immersion $f: X -> Y$ of finite type $S$-schemes in which $dim(X_sigma) <= d$, $Y$ is affine and $f$ dominant, and every $cal(K) in D^b_c (X_et, Lambda)$, there is an $(f, cal(K), S)$-good open dense of $S$. 
  ]
  #proof[
    ($==>$) is tautological, so we only prove ($<==$). 
    We reduce to the case that $X$ is affine first. Suppose that the case where $X$ and $Y$ are both affine has been dealt with, and so has the case where $f$ is an open immersion. Put: 
    $
      cal(S) = {Z subset X #[closed]: #[there exists an $(f, i_(Z,*) cal(K)_Z, S)$-good open dense of $S$ for all $cal(K)_Z in D^b_c (Z_et, Lambda)$]}
    $
    where $i_Z: Z -> X$ is the closed immersion where $Z$ is given the reduced substructure. We want to perform noetherian induction with $cal(S)$ to show that $X in cal(S)$. Suppose that $Z subset X$ is closed and for any proper closed $W subset.neq Z$, $W in cal(S)$. We aim to show that $Z in cal(S)$ as well. 
    
    - Note that an $(f, i_(Z,*) cal(K)_Z, S)$-good open of $S$ is just an $(f compose i_Z, cal(K)_Z, S)$-good open dense. Thus we may assume that $Z = X$ itself by replacing $f$ with $f compose i_Z$. Take an affine open $V subset X$ with complementary closed $W subset X$, and immersions $j: V -> X, i: W -> X$. For $cal(K) in D^b_c (X_et, Lambda)$, consider the sections with support triangle: 
      $
        i_* R i^! cal(K) -> cal(K) -> R j_* j^(-1) cal(K) ->^(+1)
      $
      Now: 

      - $j$ is an open immersion and $j^(-1) cal(K) in D^b_c (V_et, Lambda)$. Now $dim(V_sigma) <= dim(X_sigma) <= d$. Thus by the open immersion case, there exists a $(j, j^(-1) cal(K), S)$-good dense open $U subset S$. Shrinking $S$ to this open, we may thus assume that $S$ is $(j, j^(-1) cal(K), S)$-good, and in particular $R j_* j^(-1) cal(K) in D^b_c (X_et, Lambda)$. 

      - Now $i_* R i^! cal(K) in D^b_c (X_et, Lambda)$, so by @finite-morphisms-and-constructible-sheaves, $R i^! cal(K) in D^b_c (W_et, Lambda)$. Thus since $W in cal(S)$, there exists an $(f, i_* R i^! cal(K), S)$-good dense open $U subset S$. Shrink $S$ to this open as well. 

      - Since $f compose j: V -> Y$ is from an affine scheme $V$ and $dim(V_sigma) <= dim(X_sigma) <= d$, by the affine case, there exists an $(f compose j, j^(-1) cal(K), S)$-good dense open $U subset S$. Since $S$ is already $(j, j^(-1) cal(K), S)$-good, we see that $U$ is $(f, R j_* j^(-1) cal(K), S)$-good. 

      Now from the triangle, we see that $U$ is $(f, cal(K), S)$-good. Thus $X in cal(S)$. 
    
    Hence, it suffices to deal with the cases: 

    - $f: X -> Y$ is an open immersion with $dim(X_sigma) <= d$; 

    - $f: X -> Y$ has $X$ affine and $dim(X_sigma) <= d$. 

    Assume the first case. Then in the second case, $f$ is separated of finite type, so $f$ has a compactification $X ->^j ol(X) ->^(ol(f)) Y$ with $j$ open immersion and $ol(f)$ proper. Since $ol(f)$ is proper, $S$ is $(ol(f), cal(L), S)$-good for all $cal(L) in D^b_c (ol(X)_et, Lambda)$. Now $dim(X_sigma) <= d$, so the first open immersion case may be applied and there exists a dense open $U subset S$ that is $(j, cal(K), S)$-good. Then $U$ is $(ol(f) compose j, cal(K), S)$-good and we are done. 

    Thus it remains to deal with the case that $f: X -> Y$ is an open immersion with $dim(X_sigma) <= d$. By locality of the problem in $Y$, we may further assume that $Y$ is affine. 

    Finally, factor the open immersion $f$ through its schematic image, we may factor it into an open immersion with dense image, and a closed immersion. The closed immersion is dealt with by proper base change, so we may assume that $f$ has dense image. This reduces to the hypothesis. 
  ]

  Hence, by induction on $d$, we may assume that: 

  - $f: X -> Y$ is an open immersion between finite type $S$-schemes with $dim(X_sigma) = d$, $Y$ affine and $f$ dominant; 

  - For every general $f: X -> Y$ between finite type $S$-schemes with $dim(X_sigma) <= d-1$, every complex $cal(K) in D^b_c (X_et, Lambda)$ admits an $(f, cal(K), S)$-good dense open of $S$. 

  In the $d <= 0$ case, we claim that $X_sigma = Y_sigma$. 
  
  - Indeed, generic points of $Y_sigma$ correspond to generic points of $Y$ of those irreducible components that dominate $S$, and are thus contained in $X$ since $X -> Y$ is dominant. Thus, the inclusion $X_sigma -> Y_sigma$ is dominant. But $dim(X_sigma) = 0$, so $X_sigma$ must be finitely many closed points of $Y_sigma$; hence $Y_sigma = X_sigma$. 

  Now applying @passage-to-limit-of-morphisms (3), we see that there exists a dense open $U subset S$ s.t. $X_U = Y_U$. Shrinking $S$ to this dense open, $f$ becomes $id$ and the problem becomes trivial. 

  The base step is now dealt with, and we may assume $d >= 1$ and we are in a genuine inductive step. We claim that it suffices to deal with the case that $X$ has a dense open that is smooth over $S$. 

  #proof_[Proof of claim][
    Let $L$ be the perfect closure of $K = K(S)$ the function field of $S$. 
  
    Now consider the base change $f_L: X_L -> Y_L$ of $f$ along $Spec(L) -> S$. Now the reduction $(X_L)_#[red]$ is of finite type over a field $L$, so its regular locus is open. Since $X'_L = (X_L)_#[red]$ is reduced, all of its generic points have local rings being fields, and so the regular locus of $X'_L$ is dense. Thus there exists a dominant open immersion $W_L -> X'_L$. Now $W_L$ is regular over the perfect field $L$, hence smooth over $Spec(L)$. That is, $W_L -> X'_L -> Spec(L)$ is smooth. 

    Then as in the proof of @finiteness-of-lower-shriek, we may write: 
    $
      Spec(L) = dirlim_lambda T_lambda
    $
    where each $T_lambda$ is an integral affine $S$-scheme s.t. there exists a principal affine open $S_lambda subset S$ s.t. $T_lambda -> S_lambda$ is finite surjective radicial, hence a universal homeomorphism. Now the morphisms: 
    $
      W_L -> X'_L -> X_L -> Y_L -> Spec(L)
    $
    of $L$-schemes must come from base changing: 
    $
      W_lambda -> X'_lambda -> X_lambda -> Y_lambda -> T_lambda
    $
    along $Spec(L) -> T_lambda$ for some stage $lambda$. By increasing $lambda$, we may assume that: 

    - $X_lambda -> Y_lambda -> T_lambda$ is exactly the base change of $X ->^f Y -> S$, by @passage-to-limit-of-morphisms (3). 

    - $W_lambda -> T_lambda$ is smooth, by @passage-to-limit-of-properties (3c). 

    - $W_lambda -> X'_lambda$ is an open immersion by @passage-to-limit-of-properties (3f). 

    - $X'_lambda -> X_lambda$ is a surjective closed immersion, in particular a universal homeomorphism by @passage-to-limit-of-properties (2b)(3g). 

    - Finally, $W_lambda -> X'_lambda$ can also be taken to be dominant. Indeed, take its schematic image $W_lambda -> ol(W_lambda) -> X'_lambda$. Now since $W_L -> X'_L$ is dominant, by base changing to $L$ we see that $(ol(W)_lambda)_L -> (X'_lambda)_L$ is the identity. Now $L\/Frac(T_lambda)$ is a purely inseparable extension and defines a universal homeomorphism, so $ol(W_lambda) -> X'_lambda$ is dominant on generic fiber over $T_lambda$. Thus there exists a principal affine open $T_mu subset T_lambda$ (also being a scheme in the family ${T_lambda}$) s.t. $(ol(W)_lambda) times_(T_lambda) T_mu -> X'_mu$ is the identity. However this closed immersion is exactly the schematic image of $W_mu -> X'_mu$, so $W_mu -> X'_mu$ must be dominant. 

    Now shrinking $S$ to $S_lambda$, we may assume that $T_lambda -> S$ is surjective. It is also finite radicial, hence a universal homeomorphism. By topological invariance, we may further base change $S$ to $T_lambda$ and replace $X_lambda$ with $X'_lambda$ without changing the problem. That is, we replace $S$ with $T_lambda$ and $f: X -> Y$ with $X'_lambda -> Y'_lambda$ (and note that $W_lambda$ is a dense open of $X'_lambda$ smooth over $T_lambda$), and we are done. 
  ]
  Let $W subset X$ be a dense open s.t. $W -> S$ is smooth. Let $cal(K) in D^b_c (X_et, Lambda)$ and we aim to find an $(f, cal(K), S)$-good open dense of $S$. By truncating $cal(K)$, it suffices to show that for any constructible sheaf $cal(F)$ of $Lambda$-modules on $X$, there is an $(f, cal(F), S)$-good open dense of $S$. 

  By shrinking $W$ further, we may assume that $W subset X$ is a dense open s.t. $cal(F)|_W$ is locally constant. (This can be done, say, by picking an open around every generic point on each stratum of $X$ over which $cal(F)$ is l.c.c.) Thus there exists an etale cover $pi: W_1 -> W$ s.t. $cal(F)|_(W_1)$ is constant on each connected component. 

  The local ring at every generic point of $W$ is an artinian local ring, hence has its reduction a field. Every quasi-compact etale map to a field is finite etale, so by topological invariance (@top-invariance-sheaves (3)), $W_1 -> W$ has finite etale fibers over generic points of $W$. Thus by @passage-to-limit-of-properties (2a), upon replacing $W$ with a dense open, we may assume that $pi: W_1 -> W$ is a finite etale covering. 

  Let $j: W -> X$ be the open immersion and $i: X - W -> X$ be the complementary closed immersion, and take the sections with support triangle: 
  $
    i_* R i^! cal(F) -> cal(F) -> R j_* j^(-1) cal(F) ->^(+1)
  $
  Suppose that there exists a dense open of $S$ that is both $(j, j^(-1) cal(F), S)$-good and $(f compose j, j^(-1) cal(F), S)$-good. By shrinking $S$ to this dense open, we may assume that $S$ is $(f compose j, j^(-1) cal(F), S)$-good. In particular $R j_* j^(-1) cal(F) in D^b_c (X_et, Lambda)$, and so $i_* R i^! cal(F) in D^b_c (X_et, Lambda)$. Hence by @finite-morphisms-and-constructible-sheaves, $R i^! cal(F) in D^b_c ((X - W)_et, Lambda)$. 
  
  Now $f compose i: X - W -> Y$ is a map between finite type $S$-schemes. Generic points of $X_sigma$ are generic points of $X$ above $sigma$ and are contained in $W$, and so $W_sigma$ is dense in $X_sigma$. Thus $dim((X - W)_sigma) < dim(X_sigma) = d$. By the inductive hypothesis, there exists an $(f compose i, R i^! cal(F), S)$-good dense open $U subset S$. Thus: 
  
  - $U$ is $(f, i_* R i^! cal(F), S)$-good; 

  - $S$ is $(j, j^(-1) cal(F), S)$-good and $(f compose j, j^(-1) cal(F), S)$-good, hence $(f, R j_* j^(-1) cal(F), S)$-good. 

  Using the sections with support triangle, $U$ is $(f, cal(F), S)$-good and we are done. Thus, it remains to show that: 

  - There exists a dense open of $S$ that is both $(j, j^(-1) cal(F), S)$-good and $(f compose j, j^(-1) cal(F), S)$-good. 

  Now $j: W -> X$ and $f compose j: W -> Y$ are both dominant open immersions in which $dim(W_sigma) <= d$, $W$ is smooth over $S$ and there exists a finite etale covering $pi: W_1 -> W$ s.t. $cal(F)|_(W_1)$ is constant on each connected component. Thus, it suffices to prove that: 

  - For any dominant open immersion $f: X -> Y$ and l.c.c. $cal(F) in cAb(X_et, Lambda)$ s.t. $dim(X_sigma) <= d$, $X$ is smooth over $S$ and there exists a finite etale covering $pi: X_1 -> X$ s.t. $cal(F)|_(X_1)$ is constant on each connected component, there exists an $(f, cal(F), S)$-good dense open of $S$. 

  We claim that we may assume that $Y$ is proper over $S$, i.e. it suffices to show that:

  - For any dominant open immersion $f: X -> Y$ and l.c.c. $cal(F) in cAb(X_et, Lambda)$ s.t. $dim(X_sigma) <= d$, $X$ is smooth over $S$, $Y$ is proper over $S$ and there exists a finite etale covering $pi: X_1 -> X$ s.t. $cal(F)|_(X_1)$ is constant on each connected component, there exists an $(f, cal(F), S)$-good dense open of $S$. 

  Indeed, assume this case, and for the general case by locality on $Y$ we may assume that $Y$ is affine, and so $Y -> S$ is separated of finite type. Then pick a compactification $Y ->^j ol(Y) -> S$, in which $j$ can be assumed dominant (by passing to a schematic image). Now by the proper case, we may assume that $S$ is $(j compose f, cal(F), S)$-good upon shrinking $S$. Now: 
    
  - $R j_* R f_* cal(F) in D^b_c (ol(Y)_et, Lambda)$. Applying $j^(-1)$ shows that $R f_* cal(F) in D^b_c (Y_et, Lambda)$. 

  - For any Cartesian diagram: #h(1fr)
    // https://q.uiver.app/#r=typst&q=WzAsOCxbMCwxLCJYIl0sWzEsMSwiWSJdLFsyLDEsIm9sKFkpIl0sWzMsMSwiUyJdLFszLDAsIlMnIl0sWzIsMCwib2woWSknIl0sWzEsMCwiWSJdLFswLDAsIlgiXSxbMCwxLCJmIiwyXSxbMSwyLCJqIiwyXSxbMiwzXSxbNyw2LCJmJyJdLFs2LDUsImonIl0sWzUsNF0sWzQsMywiZyJdLFs1LDIsIm9sKGcpJyJdLFs2LDEsImcnIl0sWzcsMCwiZycnIiwyXV0=
    #align(center, diagram({
      node((0, 1), [$X$])
      node((1, 1), [$Y$])
      node((2, 1), [$ol(Y)$])
      node((3, 1), [$S$])
      node((3, 0), [$S'$])
      node((2, 0), [$ol(Y)'$])
      node((1, 0), [$Y$])
      node((0, 0), [$X$])
      edge((0, 1), (1, 1), [$f$], label-side: right, "->")
      edge((1, 1), (2, 1), [$j$], label-side: right, "->")
      edge((2, 1), (3, 1), "->")
      edge((0, 0), (1, 0), [$f'$], label-side: left, "->")
      edge((1, 0), (2, 0), [$j'$], label-side: left, "->")
      edge((2, 0), (3, 0), "->")
      edge((3, 0), (3, 1), [$g$], label-side: left, "->")
      edge((2, 0), (2, 1), [$ol(g)'$], label-side: left, "->")
      edge((1, 0), (1, 1), [$g'$], label-side: left, "->")
      edge((0, 0), (0, 1), [$g''$], label-side: right, "->")
    }))
    We have: 
    $
      ol(g)'^(-1) R j_* R f_* cal(F) cong R j'_* R f'_* g''^(-1) cal(F)
    $
    Apply $j'^(-1)$, and: 
    $
      j'^(-1) ol(g)'^(-1) R j_* R f_* cal(F) cong g'^(-1) j^(-1) R j_* R f_* cal(F) cong g'^(-1) R f_* cal(F)
    $
    while $j'^(-1) R j'_* R f'_* g''^(-1) cal(F) cong R f'_* g''^(-1) cal(F)$. Hence we have obtained an isomorphism $ol(g)'^(-1) R j_* R f_* cal(F) cong g'^(-1) R f_* cal(F)$, which can be checked to be the base change map by naturality. Thus $S$ is $(f, cal(F), S)$-good. 

  Thus, we may in addition assume that $Y$ is proper over $S$. To proceed in the induction, we need the following lemma: 
  
  #lemma[
    Let $f: X -> Y$ be a dominant open immersion between finite type $S$-schemes s.t. $dim(X_sigma) <= d$, and let $cal(K) in D^b_c (X_et, Lambda)$. Then up to shrinking $S$ to a dense open, there exists an open subset $V subset Y$ s.t: 

    - $Y - V -> S$ is finite; 

    - $S$ is $(f_V, cal(K)|_(X_V), S)$-good for $f_V: X_V -> V$ the base change of $f$ to $V$. 
  ]
  #proof[
    Assume for now that $Y$ is affine. Since $Y -> S$ is finite type between affine schemes, we may choose a closed immersion $i: Y -> AA^m_S$ (by any finite presentation of $cal(O)_Y (Y)$ over $cal(O)_S (S)$). Let $pi_j: AA^m_S -> AA^1_S, 1<=j<=m$ be the projections onto each coordinate. Then consider $g_j = pi_j compose i compose f: X -> AA^1_S$. Let $x in X_sigma$ be any point, and let $K = K(S)$ be the function field of $S$. Then: 
    $
      trd_(K) (k(x)) <= dim(X_sigma) <= d
    $
    Let $tau = Spec(K(t))$ be the generic point of $AA^1_S$. Thus suppose that $x in g_j^(-1) (tau)$, then: 
    $
      trd_(K(t)) (k(x)) = trd_K (k(x)) - trd_K (K(t)) <= d - 1
    $
    Thus the dimension of the generic fiber of $g_j$ satisfies $dim(g_j^(-1) (tau)) <= d-1$. The inductive hypothesis may thus be applied to $g_j$ and so:
    
    - There exists a dense $(i_j compose f_j, cal(K), AA^1_S)$-good open $U_j subset AA^1_S$ for each $j$. 

      Put $V_j = i^(-1) (pi_j^(-1) (U_j)) subset Y$, and base change $X ->^f Y ->^i AA^m_S ->^(pi_j) AA^1_S$ along $U_j -> AA^1_S$ to get: #h(1fr)
      $
        X_j ->^(f_j) V_j ->^(i_j) AA^(m-1)_(U_j) ->^(tilde(pi)_j) U_j
      $

      Then: 
      $
        i_(j,*) R f_(j,*) (cal(K)|_(X_j)) in D^b_c ((U_j)_et, Lambda)
      $
      By @finite-morphisms-and-constructible-sheaves, $R f_(j,*) (cal(K)|_(X_j)) in D^b_c ((V_j)_et, Lambda)$. Furthermore, for any $g: S' -> S$, form the Cartesian diagram: 
      // https://q.uiver.app/#r=typst&q=WzAsMTAsWzAsMSwiWF9qIl0sWzEsMSwiVl9qIl0sWzIsMSwicGlfal4oLTEpIChVX2opIl0sWzMsMSwiVV9qIl0sWzQsMSwiUyJdLFs0LDAsIlMnIl0sWzMsMCwiVSdfaiJdLFsyLDAsInBpJ19qIChVJ19qKSJdLFsxLDAsIlYnX2oiXSxbMCwwLCJYJ19qIl0sWzUsNCwiZyJdLFs2LDMsImcnX2oiXSxbNywyLCJnJydfaiJdLFs4LDEsImdfKFZfaikiXSxbOSwwLCJnXyhYX2opIiwyXSxbMCwxLCJmX2oiLDJdLFsxLDIsImkiLDJdLFsyLDMsInBpX2oiLDJdLFszLDRdLFs5LDgsImYnX2oiXSxbOCw3LCJpJyJdLFs3LDYsInBpJ19qIl0sWzYsNV1d
      #align(center, diagram({
        node((0, 1), [$X_j$])
        node((1, 1), [$V_j$])
        node((2, 1), [$pi_j^(-1) (U_j)$])
        node((3, 1), [$U_j$])
        node((4, 1), [$S$])
        node((4, 0), [$S'$])
        node((3, 0), [$U'_j$])
        node((2, 0), [$pi'_j (U'_j)$])
        node((1, 0), [$V'_j$])
        node((0, 0), [$X'_j$])
        edge((4, 0), (4, 1), [$g$], label-side: left, "->")
        edge((3, 0), (3, 1), [$g'_j$], label-side: left, "->")
        edge((2, 0), (2, 1), [$g''_j$], label-side: left, "->")
        edge((1, 0), (1, 1), [$g_(V_j)$], label-side: left, "->")
        edge((0, 0), (0, 1), [$g_(X_j)$], label-side: right, "->")
        edge((0, 1), (1, 1), [$f_j$], label-side: right, "->")
        edge((1, 1), (2, 1), [$i$], label-side: right, "->")
        edge((2, 1), (3, 1), [$pi_j$], label-side: right, "->")
        edge((3, 1), (4, 1), "->")
        edge((0, 0), (1, 0), [$f'_j$], label-side: left, "->")
        edge((1, 0), (2, 0), [$i'$], label-side: left, "->")
        edge((2, 0), (3, 0), [$pi'_j$], label-side: left, "->")
        edge((3, 0), (4, 0), "->")
      }))
      Then $g''_j$ is the base change of the morphism $g'_j: U'_j -> U_j$, so by $(f_j, cal(K)|_(X_j), AA^1_S)$-goodness of $U_j$, we have a base change isomorphism:
      $
        g''_j^(-1) i_* R f_(j,*) (cal(K)|_(X_j)) cong i'_* R f'_(j,*) g_(X_j)^(-1) (cal(K)|_(X_j))
      $
      Now the base change map $g''_j^(-1) i_* -> i'_* g_(V_j)^(-1)$ is an isomorphism, so we have an isomorphism: 
      $
        i'_* g_(V_j)^(-1) R f_(j,*) (cal(K)|_(X_j)) -> i'_* R f'_(j,*) g_(X_j)^(-1) (cal(K)|_(X_j))
      $
      and by applying $i'^(-1)$ we see that the base change $g_(V_j)^(-1) R f_(j,*) (cal(K)|_(X_j)) -> R f'_(j,*) g_(X_j)^(-1) (cal(K)|_(X_j))$ is an isomorphism. This says that $S$ is $(f_j, cal(K)|_(X_j), S)$-good. 

    - Now put: 
      $
        V = union.big_(j=1)^m V_j
      $
      and let $f_V: X_V -> V$ be the base change of $f$ to $V$. 

      Since for each $j$, $S$ is $(f_j, cal(K)|_(X_j), S)$-good, we have that $S$ is $(f_V, cal(K)|_(X_V), S)$-good. Further: 
      $
        Y - V &= Y - i^(-1) (union.big_(j=1)^m pi_j^(-1) (U_j)) \
        &= i^(-1) (AA^m_S - union.big_(j=1)^m pi_j^(-1) (U_j)) #[since $i$ is an immersion] \
        &= i^(-1)((AA^1_S - U_1) times_S dots.c times_S (AA^1_S - U_m)) subset Y
      $
      For each $j$, the generic point $tau in AA^1_S$ is contained in $U_j$, so the generic fiber $(U_j)_sigma in AA^1_K$ contains the generic point of $AA^1_K$. Thus its complement is a finite set of closed points. In other words, $AA^1_S - U_j -> AA^1_S -> S$ is finite when base changed to the generic point $sigma in S$. By @passage-to-limit-of-properties (2a), upon replacing $S$ by a dense affine open, we may assume $AA^1_S - U_j -> S$ is finite. Hence by shrinking $S$ to a dense affine open finitely many times, we may assume that $AA^1_S - U_j -> S$ is finite for all $j$. Then by the formula above, $Y - V$ is finite over $S$. 

    We are now done with the case that $Y$ is affine. In general, cover $Y$ with finitely many affine opens ${Y_i}$ and base change to $f_i: X_i -> Y_i$. Now for each $Y_i$ there exists an open $V_i subset Y_i$ s.t: 

    - $S$ is $(f_(V_i), cal(K)|_(X_(V_i)), S)$-good; 

    - $Y_i - V_i -> S$ is finite. 

    Put $V = union.big_i V_i$. Now: 

    - $Y_sigma - V_sigma = union.big_i ((Y_i)_sigma - (V_i)_sigma)$ is a finite set, since each $Y_i - V_i -> S$ is finite. Thus by @passage-to-limit-of-properties (2a), upon shrinking $S$ we may assume that $Y - V -> S$ is finite; 

    - By checking locally, $S$ is $(f_V, cal(K)|_(X_V), S)$-good. 

    We are thereby done. 
  ]

  Now let: 

  - $f: X -> Y$ be a dominant open immersion of finite type $S$-schemes in which $X$ is smooth over $S$ with $dim(X_sigma) <= d$ and $Y$ is proper over $S$. 

  - $cal(F) in cAb(X_et, Lambda)$ is an l.c.c. sheaf of $Lambda$-modules with a finite etale covering $pi: X_1 -> X$ s.t. $cal(F)|_(X_1)$ is constant on each connected component of $X_1$. 

  We aim to show that there exists an $(f, cal(F), S)$-good dense open of $S$. By the previous lemma, choose an open $V subset Y$ with complementary immersions $j: V -> Y, i: W = Y - V -> Y$. Form the commutative diagram: 
  // https://q.uiver.app/#r=typst&q=WzAsNixbMCwxLCJYIl0sWzEsMSwiWSJdLFsxLDAsIlYiXSxbMSwyLCJTIl0sWzIsMSwiVi1ZIl0sWzAsMCwiWF9WIl0sWzIsMSwiaiJdLFs0LDEsImkiLDJdLFswLDEsImYiXSxbMCwzLCJhIiwyXSxbMSwzLCJiIiwxXSxbNCwzLCJjIl0sWzUsMiwiZl9WIl0sWzUsMCwiaiciLDJdXQ==
  #context align(center, diagram({
    node((0, 1), [$X$])
    node((1, 1), [$Y$])
    node((1, 0), [$V$])
    node((1, 2), [$S$])
    node((2, 1), [$W = Y-V$])
    node((0, 0), [$X_V$])
    edge((1, 0), (1, 1), [$j$], label-side: left, "->")
    edge((2, 1), (1, 1), [$i$], label-side: right, "->")
    edge((0, 1), (1, 1), [$f$], label-side: left, "->")
    edge((0, 1), (1, 2), [$a$], label-side: right, "->")
    edge((1, 1), (1, 2), [$b$], label-side: center, "->")
    edge((2, 1), (1, 2), [$c$], label-side: left, "->")
    edge((0, 0), (1, 0), [$f_V$], label-side: left, "->")
    edge((0, 0), (0, 1), [$j_X$], label-side: right, "->")
  }, crossing-fill: thm-box-curr-color()))
  with upper left square Cartesian. Then by our assumptions and the choice of $V$, after suitably shrinking $S$ to an affine open: 

  - $a$ is smooth, $b$ is proper, $c$ is finite; 

  - $S$ is $(f_V, cal(F)|_(X_V), S)$-good. 

  We prove that there exists an $(f, cal(F), S)$-good dense open of $S$ under the following additional assumption: 

  - There is a dense open of $S$ that is $(a, cal(F), S)$-good. 

  By shrinking $S$, we may assume that $S$ is $(a, cal(F), S)$-good. Consider the extension by zero triangle: 
  $
    underbrace(j_! j^(-1) R f_* cal(F), j_! R f_(V,*) (cal(F)|_(X_V))) -> R f_* cal(F) -> i_* i^(-1) R f_* cal(F) ->^(+1)
  $
  which, upon applying $R b_*$, yields a distinguished triangle: 
  $
    R b_* j_! R f_(V,*) (cal(F)|_(X_V)) -> R a_* cal(F) -> c_* i^(-1) R f_* cal(F) ->^(+1)
  $
  Now: 

  - Since $S$ is $(a, cal(F), S)$-good, we have $R a_* cal(F) in D^b_c (S_et, Lambda)$. 

    Since $S$ is $(f_V, cal(F)|_(X_V), S)$-good, we have $R f_(V,*) (cal(F)|_(X_V)) in D^b_c (V_et, Lambda)$. Since $b$ is proper, by the finiteness of $R(b compose j)_!$ (according to @finiteness-of-lower-shriek), $R b_* j_! R f_(V,*) (cal(F)|_(X_V)) in D^b_c (S_et, Lambda)$. 

    Thus, from the distinguished triangle, $c_* i^(-1) R f_* cal(F) in D^b_c (S_et, Lambda)$. By @finite-morphisms-and-constructible-sheaves, $i^(-1) R f_* cal(F) in D^b_c (W_et, Lambda)$ and hence $i_* R f_* cal(F) in D^b_c (Y_et, Lambda)$. Meanwhile $j_! j^(-1) R f_* cal(F) = j_! R f_(V,*) (cal(F)|_(X_V)) in D^b_c (Y_et, Lambda)$, so by the extension by zero triangle: 
    $
      R f_* cal(F) in D^b_c (Y_et, Lambda)
    $

  - For any $g: S' -> S$, base change the diagram along $g$ to: 
    // https://q.uiver.app/#r=typst&q=WzAsMTIsWzEsNSwiWCJdLFszLDQsIlkiXSxbNSwzLCJXIl0sWzIsMywiViJdLFswLDQsIlhfViJdLFs0LDUsIlMiXSxbMSwyLCJYJyJdLFs0LDIsIlMnIl0sWzIsMCwiViciXSxbMywxLCJZJyJdLFswLDEsIlhfKFYnKSJdLFs1LDAsIlcnIl0sWzAsMSwiZiIsMV0sWzIsMSwiaSIsMV0sWzMsMSwiaiIsMV0sWzQsMywiZl9WIiwxXSxbNCwwLCJqX1giLDFdLFswLDUsImEiLDFdLFsxLDUsImIiLDFdLFsyLDUsImMiLDFdLFs2LDksImYnIiwxXSxbMTEsOSwiaSciLDFdLFs4LDksImonIiwxXSxbMTAsOCwiZidfViIsMV0sWzEwLDYsImonX1giLDFdLFs2LDcsImEnIiwxXSxbOSw3LCJiJyIsMV0sWzExLDcsImMnIiwxXSxbMTAsNCwiZ18oWF9WKSIsMV0sWzYsMCwiZ19YIiwxLHsibGFiZWxfcG9zaXRpb24iOjIwfV0sWzgsMywiZ19WIiwxLHsibGFiZWxfcG9zaXRpb24iOjgwfV0sWzksMSwiZ19ZIiwxXSxbNyw1LCJnIiwxLHsibGFiZWxfcG9zaXRpb24iOjIwfV0sWzExLDIsImdfVyIsMSx7ImxhYmVsX3Bvc2l0aW9uIjo4MH1dXQ==
    #context align(center, diagram({
      node((0, 1), [$X$])
      node((2, 0), [$Y$])
      node((4, -1), [$W$])
      node((1, -1), [$V$])
      node((-1, 0), [$X_V$])
      node((3, 1), [$S$])
      node((0, -2), [$X'$])
      node((3, -2), [$S'$])
      node((1, -4), [$V'$])
      node((2, -3), [$Y'$])
      node((-1, -3), [$X'_(V)$])
      node((4, -4), [$W'$])
      edge((0, 1), (2, 0), [$f$], label-side: center, "->")
      edge((4, -1), (2, 0), [$i$], label-side: center, "->", layer: 1, label-pos: 0.7)
      edge((1, -1), (2, 0), [$j$], label-side: center, "->")
      edge((-1, 0), (1, -1), [$f_V$], label-side: center, "->", layer: 1, label-pos: 0.7)
      edge((-1, 0), (0, 1), [$j_X$], label-side: center, "->")
      edge((0, 1), (3, 1), [$a$], label-side: center, "->")
      edge((2, 0), (3, 1), [$b$], label-side: center, "->")
      edge((4, -1), (3, 1), [$c$], label-side: center, "->")
      edge((0, -2), (2, -3), [$f'$], label-side: center, "->", layer: 1, label-pos: 0.7)
      edge((4, -4), (2, -3), [$i'$], label-side: center, "->")
      edge((1, -4), (2, -3), [$j'$], label-side: center, "->")
      edge((-1, -3), (1, -4), [$f'_V$], label-side: center, "->")
      edge((-1, -3), (0, -2), [$j'_X$], label-side: center, "->")
      edge((0, -2), (3, -2), [$a'$], label-side: center, "->")
      edge((2, -3), (3, -2), [$b'$], label-side: center, "->")
      edge((4, -4), (3, -2), [$c'$], label-side: center, "->")
      edge((-1, -3), (-1, 0), [$g_(X_V)$], label-side: center, "->")
      edge((0, -2), (0, 1), [$g_X$], label-side: center, label-pos: 0.15, "->")
      edge((1, -4), (1, -1), [$g_V$], label-side: center, label-pos: 0.85, "->")
      edge((2, -3), (2, 0), [$g_Y$], label-side: center, "->")
      edge((3, -2), (3, 1), [$g$], label-side: center, label-pos: 0.15, "->")
      edge((4, -4), (4, -1), [$g_W$], label-side: center, label-pos: 0.85, "->")
    }, crossing-fill: thm-box-curr-color(), spacing: 2em))
    
    We aim to show that the base change $g_Y^(-1) R f_* cal(F) -> R f'_* g_X^(-1) cal(F)$ is an isomorphism. Put $cal(F)' = cal(F)|_(X')$. Consider the distinguished triangle: 
    $
      R b_* j_! R f_(V,*) (cal(F)|_(X_V)) -> R a_* cal(F) -> c_* i^(-1) R f_* cal(F) ->^(+1)
    $
    and the same triangle for the base changed maps: 
    $
      R b'_* j'_! R f'_(V,*) (cal(F)'|_(X_V)) -> R a'_* cal(F)' -> c'_* i'^(-1) R f'_* cal(F)' ->^(+1)
    $
    Now apply $g^(-1)$ to the first triangle: 

    - Since $S$ is $(a, cal(F), S)$-good, the base change $g^(-1) R a_* cal(F) -> R a'_* cal(F)'$ is an isomorphism; 

    - For the first term: #h(1fr)
      $
        g^(-1) R b_* j_! R f_(V,*) (cal(F)|_(X_V)) &cong R b'_* j'_! g_V^(-1) R f_(V,*) (cal(F)|_(X_V)) #[by proper base change] \
        &cong R b'_* j'_! R f'_(V,*) (cal(F')|_(X'_V)) #[since $S$ is $(f_V, cal(F)|_(X_V), S)$-good] 
      $
    
    Thus using the two distinguished triangles, the base change map on the third term must be an isomorphism since the one on the first and second term is. That is, the base change map: 
    $
      g^(-1) c_* i^(-1) R f_* cal(F) -> c'_* i'^(-1) R f'_* cal(F)'
    $
    is an isomorphism. Now $c$ is finite, so $g^(-1) c_* cong c'_* g_W^(-1)$, and in other words, 
    $
      c'_* g_W^(-1) i^(-1) R f_* cal(F) -> c'_* i'^(-1) R f'_* cal(F)'
    $ 
    is an isomorphism. Now $c'$ is finite, so by checking stalks, $g_W^(-1) i^(-1) R f_* cal(F) -> i'^(-1) R f'_* cal(F)'$ is an isomorphism. Applying $i'_*$ and use base change for $i_*$ shows that the base change: 
    $
      g_Y^(-1) i_* i^(-1) R f_* cal(F) -> i'_* i'^(-1) R f'_* cal(F)'
    $
    is an isomorphism. 

    Furthermore, we have seen that: 
    $
      g_Y^(-1) j_! R f_(V,*) (cal(F)|_(X_V)) cong j'_! g_V^(-1) R f_(V,*) (cal(F)|_(X_V)) cong j'_! R f'_(V,*) (cal(F)'|_(X'_V))
    $
    since $S$ is $(f_V, cal(F)|_(X_V), S)$-good. Now take the extension by zero triangles: 
    $
      j_! R f_(V,*) (cal(F)|_(X_V)) -> R f_* cal(F) -> i_* i^(-1) R f_* cal(F) ->^(+1)
    $
    and: 
    $
      j'_! R f'_(V,*) (cal(F)'|_(X'_V)) -> R f'_* cal(F)' -> i'_* i'^(-1) R f'_* cal(F)' ->^(+1)
    $
    Applying $g_Y^(-1)$ to the first triangle gives it a base change map to the second triangle, which we have shown to be an isomorphism on the first and third position. Thus it is an isomorphism on the second position, i.e: 
    $
      g_Y^(-1) R f_* cal(F) cong R f'_* cal(F)'
    $
    by base change. 

  These two arguments together show that $S$ is $(f, cal(F), S)$-good and we are done. The only assumption remaining to be shown is that up to shrinking $S$, $S$ is $(a, cal(F), S)$-good. In other words, it remains to prove that: 

  - If $f: X -> S$ is a separated smooth morphism, and $cal(F) in cAb(X_et, Lambda)$ is an l.c.c. sheaf of $Lambda$-modules trivialized by a finite etale covering $pi: X_1 -> X$, then there exists an $(f, cal(F), S)$-good dense open of $S$. 

  By taking each connected component of $X$, we may assume that $X$ is connected. Then any connected component of $X_1$ maps surjectively to $X$, so we may take $X_1$ to be surjective as well. By taking a Galois closure, we may assume that $pi: X_1 -> X$ is a Galois covering. Since $X$ is assumed to be connected, the smooth map $X -> S$ is of some pure relative dimension $d$ (being the rank of the locally free coherent sheaf $Omega_(X\/S)$ on $X$). 

  By the filtrations $0 -> ell cal(F) -> cal(F) -> cal(F)\/ell cal(F) -> 0$, we see that it suffices to show for those $cal(F)$ that are $ell$-torsion for a prime number $ell in cal(O)_S^times$. By replacing $Lambda$ with $Lambda\/ell Lambda$, we may assume that $Lambda$ is $ell$-torsion too. Now by @finiteness-of-lower-shriek, $R f_! ul(ZZ\/ell) in D^b_c (S_et, Lambda)$. Thus by shrinking $S$, we may further assume that: 

  - Every $R^q f_(1,!) ul(ZZ\/ell)$ is a l.c.c. sheaf of $ZZ\/ell$-modules. 

  We claim that in this case $S$ is $(f_1, ul(ZZ\/ell), S)$-good and every $R^q f_* ul(ZZ\/ell)$ is l.c.c. 

  #proof_[Proof of claim][
    Replace $f$ with $f_1$ and we may assume that every $R^q f_! ul(ZZ\/ell)$ is l.c.c. Now $f$ remains smooth of relative dimension $d$. 

    By Poincare duality (@relative-poincare-duality), $R f^! ul(ZZ\/ell) cong ul(ZZ\/ell)(d)[2d]$ canonically. Thus by internal adjunction we have a canonical isomorphism: 
    $
      R f_* ul(ZZ\/ell)(d)[2d] cong R f_* RHHom_(ZZ\/ell) (ul(ZZ\/ell), ul(ZZ\/ell)(d)[2d]) cong RHHom_(ZZ\/ell) (R f_! ul(ZZ\/ell), ul(ZZ\/ell))
    $
    i.e. a canonical isomorphism: 
    $
      R f_* ul(ZZ\/ell) cong RHHom_(ZZ\/ell) (R f_! ul(ZZ\/ell), ul(ZZ\/ell))(-d)[-2d]
    $

    - Note that $RHHom_(ZZ\/ell) (R f_! ul(ZZ\/ell), ul(ZZ\/ell)) = HHom_(ZZ\/ell) (R f_! ul(ZZ\/ell), ul(ZZ\/ell))$. Indeed, for a single l.c.c. sheaf $cal(G)$ of $ul(ZZ\/ell)$-modules, by @lcc-and-injective-has-no-higher-ext, $RHHom_(ZZ\/ell) (cal(G), ul(ZZ\/ell)) = HHom_(ZZ\/ell) (cal(G), ul(ZZ\/ell))$. Thus using truncations, we have: 
      $
        RHHom_(ZZ\/ell) (R f_! ul(ZZ\/ell), ul(ZZ\/ell)) = HHom_(ZZ\/ell) (R f_! ul(ZZ\/ell), ul(ZZ\/ell))
      $
      by gluing degree by degree. 

    Hence, we have canonical isomorphisms: 
    $
      R^q f_* ul(ZZ\/ell) cong HHom_(ZZ\/ell)(R^(2d-q) f_! ul(ZZ\/ell), ul(ZZ\/ell)) (-d)
    $
    Thus $R^q f_* ul(ZZ\/ell)$ vanishes unless $0<=q<=2d$, and is l.c.c. (since $R^(2d-q) f_! ul(ZZ\/ell)$ is l.c.c, so any etale cover trivializing $R^(2d-q) f_! ul(ZZ\/ell)$ also trivializes $R^q f_* ul(ZZ\/ell)$). Furthermore, for any $g: S' -> S$, the canonical map $g^(-1) HHom_(ZZ\/ell) (R^(2d-q) f_! ul(ZZ\/ell), ul(ZZ\/ell)) -> HHom_(ZZ\/ell) (g^(-1) R^(2d-q) f_! ul(ZZ\/ell), ul(ZZ\/ell))$ is an isomorphism. (This is not in general true, but in this case we can check by pulling back along a trivializing etale cover, after which everything is constant, and then apply @surjective-pullback-conservative.) Thus the base change map: 
    $
      g^(-1) R f_* ul(ZZ\/ell) -> R f'_* ul(ZZ\/ell)
    $
    is induced by the base change map: 
    $
      g^(-1) R f_! ul(ZZ\/ell) -> R f'_! ul(ZZ\/ell)
    $
    which is an isomorphism by proper base change. Thus the formation of $R f_* ul(ZZ\/ell)$ is compatible with base change. That is, we have shown that $S$ is $(f, ul(ZZ\/ell), S)$-good. 
  ]
  Now put $f_1: X_1 ->^pi X -> S$, and let $pi^(-1) cal(F) = ul(M)$ for a finite $Lambda$-module $M$. Then we have a projection map (where since $ZZ\/ell$ is a field, tensors are exact and don't need to be left derived): 
  $
    R f_(1,*) pi^(-1) cal(F) = R f_(1,*) (ul(ZZ\/ell) otimes_(ZZ\/ell) ul(M)) -> R f_(1,*) ul(ZZ\/ell) otimes_(ZZ\/ell) ul(M)
  $
  This projection map is an isomorphism. /*Indeed, by picking a basis we may assume that $ul(M) = ul(ZZ\/ell)^(oplus I)$. Then by @limit-formula-for-sheaves, 
  $
    R^q f_(1,*) ul(M) cong (R^q f_(1,*) ul(ZZ\/ell))^(oplus I) cong R^q f_(1,*) ul(ZZ\/ell) otimes_(ZZ\/ell) ul(M)
  $*/Indeed, $id$ is universally locally acyclic relative to $ul(M)$ (say by @loc-acyc-of-smooth-maps), and the desired projection isomorphism follows from @loc-acyc-and-base-change. 


  However, $R^q f_(1,*) ul(ZZ\/ell)$ are l.c.c. sheaves of $ul(ZZ\/ell)$-modules. Hence $R^q f_(1,*) ul(M)$ are l.c.c. sheaves of $Lambda$-modules, trivialized by the same finite etale coverings of $S$ trivializing $R^q f_(1,*) ul(ZZ\/ell)$. Base change compatibility of $R^q f_(1,*) ul(ZZ\/ell)$ also passes to $R^q f_(1,*) ul(M)$. Hence, we conclude that: 

  - $S$ is $(f_1, ul(M), S)$-good with $R^q f_(1,*) ul(M) = R^q f_* pi_* pi^(-1) cal(F)$ being l.c.c. sheaves of $Lambda$-modules. 

  That is, in a fully self-contained statement: 
  
  - Suppose that $f: X -> S$ is a separated smooth morphism of pure relative dimension with $X$ connected, and $Lambda$ is an $ell$-torsion noetherian ring for a prime number $ell$. Suppose that we have a Galois etale covering space $pi: X_1 -> X$, with $f_1: X_1 ->^pi X -> S$. 
  
    Then after shrinking $S$ so that every $R^q f_(1,!) ul(ZZ\/ell)$ is l.c.c, for any $cal(F) in cAb(X_et, Lambda)$ a l.c.c. sheaf of $Lambda$-modules trivialized by $pi$, $S$ is $(f_1, pi^(-1) cal(F), S)$-good. 

  To proceed, we essentially need to use a sort of group cohomology for the group $Aut(X_1\/X)$ on etale sheaves. I don't want to write a long construction for that, so I replaced it with a janky four lemma induction that you have seen multiple times. 

  Take the exact sequence: 
  $
    0 -> cal(F) -> pi_* pi^(-1) cal(F) -> cal(R) -> 0
  $
  Now $cal(F)$ and $pi_* pi^(-1) cal(F)$ are both l.c.c. sheaves of $Lambda$-modules both trivialized by $pi$, hence so is $cal(R)$. Denote by: 

  - $T(q)$ the proposition: For every l.c.c. sheaf $cal(F)$ of $Lambda$-modules on $X$ trivialized by $pi$:
  
    - $R^p f_* cal(F)$ is constructible for all $p<=q$; 
    
    - For every Cartesian diagram: #h(1fr)
      #align(center, diagram({
        node((0, 0), [$X'$])
        node((1, 0), [$S'$])
        node((0, 1), [$X$])
        node((1, 1), [$S$])
        node((0.3, 0.3), [$cart$])
        edge((0, 1), (1, 1), [$f$], label-side: right, "->")
        edge((0, 0), (1, 0), [$f'$], label-side: left, "->")
        edge((1, 0), (1, 1), [$g$], label-side: left, "->")
        edge((0, 0), (0, 1), [$g'$], label-side: right, "->")
      }))
      the base change $g^(-1) R^p f_* cal(F) -> R^p f'_* g'^(-1) cal(F)$ is an isomorphism for every $0<=p<=q$. 
    

  - $T'(q)$ the proposition $T(q)$, but with $g^(-1) R^p f_* cal(F) -> R^p f'_* g'^(-1) cal(F)$ only required to be injective when $p=q$. 

  Assume $T(q-1)$. Take any arbitrary l.c.c. sheaf $cal(F) in cAb(X_et, Lambda)$ trivialized by $pi$. Now: 

  - We have a long exact sequence involving $dots.c -> R^(q-1) f_* cal(R) -> R^q f_* cal(F) -> R^q f_(1,*) pi^(-1) cal(F) -> dots.c$. By $T(q-1)$ and previous arguments, $R^q f_* cal(F)$ is sandwiched between two constructible sheaves, hence constructible. 

  - Take any $g: S' -> S$ and form the usual Cartesian diagram. Now consider the commutative diagram with exact rows: 
    // https://q.uiver.app/#r=typst&q=WzAsMTQsWzAsMCwiZG90cy5jIl0sWzAsMSwiZG90cy5jIl0sWzEsMCwiZ14oLTEpIFJeKHEtMSkgZl8oMSwqKSBwaV4oLTEpIGNhbChGKSJdLFsyLDAsImdeKC0xKSBSXihxLTEpIGZfKiBjYWwoUikiXSxbMywwLCJnXigtMSkgUl5xIGZfKiBjYWwoRikiXSxbNCwwLCJnXigtMSkgUl5xIGZfKDEsKikgcGleKC0xKSBjYWwoRikiXSxbNSwwLCJnXigtMSkgUl5xIGZfKiBjYWwoUikiXSxbNiwwLCJkb3RzLmMiXSxbMSwxLCJSXihxLTEpIGYnXygxLCopIHBpJ14oLTEpIGcnXigtMSkgY2FsKEYpIl0sWzQsMSwiUl5xIGYnXygxLCopIHBpJ14oLTEpIGcnXigtMSkgY2FsKEYpIl0sWzIsMSwiUl4ocS0xKSBmJ18qIGcnXigtMSkgY2FsKFIpIl0sWzUsMSwiUl5xIGYnXyogZydeKC0xKSBjYWwoUikiXSxbMywxLCJSXnEgZidfKiBnJ14oLTEpIGNhbChGKSJdLFs2LDEsImRvdHMuYyJdLFswLDJdLFsyLDNdLFszLDRdLFs0LDVdLFs1LDZdLFs2LDddLFsxLDhdLFs4LDEwXSxbMTAsMTJdLFsxMiw5XSxbOSwxMV0sWzExLDEzXSxbMiw4XSxbMywxMF0sWzQsMTJdLFs1LDldLFs2LDExXV0=
    #align(center, diagram({
      node((0, 0), [$dots.c$])
      node((0, 1), [$dots.c$])
      node((1, 0), [$g^(-1) R^(q-1) f_(1,*) pi^(-1) cal(F)$])
      node((2, 0), [$g^(-1) R^(q-1) f_* cal(R)$])
      node((3, 0), [$g^(-1) R^q f_* cal(F)$])
      node((4, 0), [$g^(-1) R^q f_(1,*) pi^(-1) cal(F)$])
      node((5, 0), [$g^(-1) R^q f_* cal(R)$])
      node((6, 0), [$dots.c$])
      node((1, 1), [$R^(q-1) f'_(1,*) pi'^(-1) g'^(-1) cal(F)$])
      node((4, 1), [$R^q f'_(1,*) pi'^(-1) g'^(-1) cal(F)$])
      node((2, 1), [$R^(q-1) f'_* g'^(-1) cal(R)$])
      node((5, 1), [$R^q f'_* g'^(-1) cal(R)$])
      node((3, 1), [$R^q f'_* g'^(-1) cal(F)$])
      node((6, 1), [$dots.c$])
      edge((0, 0), (1, 0), "->")
      edge((1, 0), (2, 0), "->")
      edge((2, 0), (3, 0), "->")
      edge((3, 0), (4, 0), "->")
      edge((4, 0), (5, 0), "->")
      edge((5, 0), (6, 0), "->")
      edge((0, 1), (1, 1), "->")
      edge((1, 1), (2, 1), "->")
      edge((2, 1), (3, 1), "->")
      edge((3, 1), (4, 1), "->")
      edge((4, 1), (5, 1), "->")
      edge((5, 1), (6, 1), "->")
      edge((1, 0), (1, 1), "->")
      edge((2, 0), (2, 1), "->")
      edge((3, 0), (3, 1), "->")
      edge((4, 0), (4, 1), "->")
      edge((5, 0), (5, 1), "->")
    }, spacing: 1.3em, label-size: 0.7em))

    By $T(q-1)$, the first two vertical arrows are bijective. By previous arguments, the fourth vertical arrow is bijective. 

    - By the injective four lemma, the third arrow is injective. Since $cal(F)$ is arbitrary, this proves $T'(q)$; 

    - By $T'(q)$, the fifth arrow is injective. Now by the surjective four lemma, the third arrow is bijective. Since $cal(F)$ is arbitrary, this proves $T(q)$. 

  Now start with $T(-1)$ and perform induction, we have all $T(q)$ verified. Now suppose that $f$ has fiber dimensions $<=d$. Then for any l.c.c. sheaf $cal(F) in cAb(X_et, Lambda)$ trivialized by $pi$, any $s in S$, by compatibility with base change, 
  $
    s^(-1) R^q f_* cal(F) = R^q f_(s,*) s^(-1) cal(F) = 0 
  $
  whenever $q > 2dim(X_s)$, by @relative-artin-grothendieck-vanishing (2). In this case, for any geometric point $ol(s)$ above $s$, $(R^q f_* cal(F))_(ol(s)) = 0$. Hence, if we take $q > 2d$, we have $(R^q f_* cal(F))_(ol(s)) = 0$ for every geometric point $ol(s)$ of $S$, hence $R^q f_* cal(F) = 0$. 

  Summarizing the discussion above, this shows that: 

  - Suppose that $f: X -> S$ is a separated smooth morphism of pure relative dimension with $X$ connected, and $Lambda$ is an $ell$-torsion noetherian ring for a prime number $ell$. Suppose that we have a Galois etale covering space $pi: X_1 -> X$, with $f_1: X_1 ->^pi X -> S$. 
  
    Then after shrinking $S$ so that every $R^q f_(1,!) ul(ZZ\/ell)$ is l.c.c, for any $cal(F) in cAb(X_et, Lambda)$ a l.c.c. sheaf of $Lambda$-modules trivialized by $pi$, $S$ is $(f, cal(F), S)$-good. 

  This concludes the proof. 
]

The generic base change theorem has profound implications. 

#corollary(name: <finiteness-of-rf-lower-star>)[
  (Finiteness of $R f_*$) Let $k$ be any field, and $f: X -> Y$ be a morphism of finite type $k$-schemes. Let $Lambda$ be an $n$-torsion noetherian ring with $n in k^times$. Then: 
  
  + (Finiteness) $R f_*: D(X_et, Lambda) -> D(Y_et, Lambda)$ has finite cohomological dimension above, and sends $D^b_c (X_et, Lambda)$ to $D^b_c (Y_et, Lambda)$. 

  + (Base change) For any Cartesian diagram: #h(1fr)
    #align(center, diagram({
      node((0, 0), [$X'$])
      node((1, 0), [$Y'$])
      node((0, 1), [$X$])
      node((1, 1), [$Y$])
      // node((0.3, 0.3), [$cart$])
      node((2, 1), [$Spec(k)$])
      node((2, 0), [$S'$])
      edge((0, 1), (1, 1), [$f$], label-side: right, "->")
      edge((0, 0), (1, 0), [$f'$], label-side: left, "->")
      edge((1, 0), (2, 0), "->")
      edge((1, 1), (2, 1), "->")
      edge((1, 0), (1, 1), [$g_Y$], label-side: left, "->")
      edge((2, 0), (2, 1), [$g$], label-side: left, "->")
      edge((0, 0), (0, 1), [$g_X$], label-side: right, "->")
    }))
    $
      g_Y^(-1) R f_* cal(K) -> R f'_* g_X^(-1) cal(K)
    $
    is an isomorphism for all $cal(K) in D^b_c (X_et, Lambda)$. 

  // + Setup as in (2), and assume that every finite $Lambda$-module embeds into a finite free $Lambda$-module. Also assume that  Then we have an isomorphism of relative base change for all $cal(K) in D^b_c (X_et, Lambda), cal(L) in D^b_#[ctf] (S'_et, Lambda)$: 
  //   $
  //     g_Y^(-1) R f_* cal(K) Lotimes_Lambda cal(L)|_(Y') -> R f'_* (g_X^(-1) cal(K) Lotimes_Lambda cal(L)|_(X'))
  //   $
]
#proof[
  Finite cohomological dimension of $R f_*$ follows from @relative-artin-grothendieck-vanishing. The rest of statements (1) and the plain base change in statement (2) follow from generic base change applied to $S = Spec(k)$, where since $S$ is a single point, its only dense open is itself. 

  // (3) By truncation, we may assume that $cal(K) = cal(F)$ is a constructible sheaf. Fix $a$, and we perform induction on the following statement $T(r)$: 

  // - For all $cal(L) in D^b_#[ctf] (S'_et, Lambda)$ s.t. $cal(L) Lotimes_Lambda (-)$ has cohomological dimension below $<=a$, #h(1fr)
  //   $
  //     h^q (g_Y^(-1) R f_* cal(F) Lotimes_Lambda cal(L)|_(Y')) -> h^q (R f'_* (g_X^(-1) cal(F) Lotimes_Lambda cal(L)|_(X')))
  //   $
  //   is an isomorphism for all $q <= r$. 

  // Now for any $cal(L) in D^b_#[ctf] (S'_et, Lambda)$ with $$
]

#corollary[
  (Generic universal local acyclicity) Let $k$ be any field and $g: S -> Spec(k)$ be any finite type morphism. Let $Lambda$ be an $n$-torsion noetherian ring with $n in k^times$. Then $g$ is universally locally acyclic relative to every $cal(K) in D^b_#[ctf] (S_et, Lambda)$. 
]
#proof[
  By @loc-acyc-and-base-change, and Step 3 and the early half of Step 4 in the proof of @rel-bc-reductions, it suffices to show that for every Cartesian diagram: 
  #align(center, diagram({
    node((0, 0), [$X$])
    node((1, 0), [$Y$])
    node((0, 1), [$X_0$])
    node((1, 1), [$Y_0$])
    node((2, 1), [$Spec(k)$])
    node((2, 0), [$S$])
    edge((0, 1), (1, 1), [$f_0$], label-side: right, "->")
    edge((0, 0), (1, 0), [$f$], label-side: left, "->")
    edge((1, 0), (2, 0), "->")
    edge((1, 1), (2, 1), "->")
    edge((1, 0), (1, 1), [$g_Y$], label-side: left, "->")
    edge((2, 0), (2, 1), [$g$], label-side: left, "->")
    edge((0, 0), (0, 1), [$g_X$], label-side: right, "->")
  }))
  in which $X_0 -> Y_0$ is an open immersion of finite type $k$-schemes, and every constructible sheaf $cal(F) in cAb((X_0)_et, Lambda)$, with $cal(K)_Y = cal(K)|_Y$, the relative base change: 
  $
    g_Y^(-1) R f_(0,*) cal(F) Lotimes_Lambda cal(K)_Y -> R f_* (g_X^(-1) cal(F) Lotimes_Lambda f^(-1) cal(K)_Y)
  $
  is an isomorphism. 

  For this, we intend to use a generation argument such as @cpct-generation-of-triangulated-cat. Unfortunately $D^b_c$ does not have arbitrary direct sums, so we need to relax the conditions to $cal(K) in D(S_et, Lambda)$ to be any complex. Now by (2) of the previous corollary, every pushforward in question here is compatible with changing the base field from $k$ to its algebraic closure $ol(k)$. Thus by base changing to $ol(k)$, we may assume that $k$ is algebraically closed. Now: 
  
  - In $g_Y^(-1) R f_(0,*) cal(F) Lotimes_Lambda cal(K)_Y -> R f_* (g_X^(-1) cal(F) Lotimes_Lambda f^(-1) cal(K)_Y)$, both sides are triangulated functors in $cal(K)$; 

  - For any family $cal(K)_i in D(S_et, Lambda)$, #h(1fr)
    $
      g_Y^(-1) R f_(0,*) cal(F) Lotimes_Lambda (oplus.big_i cal(K)_(i,Y)) cong oplus.big_i (g_Y^(-1) R f_(0,*) cal(F) Lotimes_Lambda cal(K)_(i,Y))
    $
    since tensor is a left adjoint, while: 
    $
      R f_* (g_X^(-1) cal(F) Lotimes_Lambda f^(-1) (oplus.big_i cal(K)_(i,Y))) &cong R f_* (oplus.big_i g_X^(-1) cal(F) Lotimes_Lambda f^(-1) cal(K)_(i,Y)) \
      &cong oplus.big_i R f_* (g_X^(-1) cal(F) Lotimes_Lambda f^(-1) cal(K)_(i,Y))
    $
    Here, the last step is due to @relative-limit-formula-for-sheaves and the boundedness of $R f_*$. The argument is truncation then applying limit formula that is pretty much the same as the proof of @derived-bounded-limit-formula-for-direct-sum. 

    Hence, both sides of $g_Y^(-1) R f_(0,*) cal(F) Lotimes_Lambda cal(K)_Y -> R f_* (g_X^(-1) cal(F) Lotimes_Lambda f^(-1) cal(K)_Y)$ are compatible with direct sums in $cal(K) in D(S_et, Lambda)$. 

  - Consider the family of objects ${j_! ul(Lambda)}$ of $D(S_et, Lambda)$ for $j: U -> S$ etale with $U$ affine. Then: 

    - If $cal(K) in D(S_et, Lambda)$ has $Hom_Lambda (j_! ul(Lambda)[q], cal(K)) = 0$ for all $j: U -> S$ etale with $U$ affine and all $q in ZZ$, then upon replacing $cal(K)$ with a K-injective resolution $cal(I)^bullet$, we see that $Gamma(U, h^q (cal(I))) = 0$ for all affine $U in Et_S$. Every object of $Et_S$ can be covered with affines, so this shows that $h^q (cal(I)) = 0$ for all $q$, and so $cal(K) = 0$. 

    - Each $j_! ul(Lambda)$ is a compact object. Indeed, for $j: U -> S$ etale with $U$ affine, 
      $
        Hom_Lambda (j_! ul(Lambda), oplus.big_i cal(K)_i) &cong h^0 (R Gamma(U, oplus.big_i cal(K)_i)) \
        &cong h^0 (oplus.big_i R Gamma(U, cal(K)_i)) \
        &cong oplus.big_i h^0 (R Gamma(U, cal(K)_i))
      $
      where the second step is due to @derived-bounded-limit-formula-for-direct-sum. Here $S$ is finite type over the algebraically closed field $k$, and so is $U$, which gives $R Gamma(U, -)$ finite cohomological dimension above. 

  Hence, invoking @cpct-generation-of-triangulated-cat, it suffices to prove for all affine etale $j: U -> S$ that: 
  $
    g_Y^(-1) R f_(0,*) cal(F) Lotimes_Lambda cal(K)_Y -> R f_* (g_X^(-1) cal(F) Lotimes_Lambda f^(-1) cal(K)_Y)
  $
  is an isomorphism when $cal(K) = j_! ul(Lambda)$. Now by Zariski's main theorem, we may pick a compactification $j: U ->^ell ol(U) ->^pi S$ with $pi$ finite. Take the complementary closed immersion $i: Z -> ol(U)$ of $ell$ and put $pi' = pi compose i$, and by the extension by zero triangle and @etale-and-compactified-lower-shriek-agree, we have an exact sequence: 
  $
    0 -> j_! ul(Lambda) -> pi_* ul(Lambda) -> pi'_* ul(Lambda) -> 0
  $
  Hence, it suffices to prove for all $cal(K) = pi_* ul(Lambda)$ for $pi: S' -> S$ finite. Form the Cartesian diagram: 
  #align(center, diagram({
    node((0, 0), [$X$])
    node((1, 0), [$Y$])
    node((0, 1), [$X_0$])
    node((1, 1), [$Y_0$])
    node((0, -1), [$X'$])
    node((1, -1), [$Y'$])
    node((2, -1), [$S'$])
    node((2, 1), [$Spec(k)$])
    node((2, 0), [$S$])
    edge((0, 1), (1, 1), [$f_0$], label-side: right, "->")
    edge((0, 0), (1, 0), [$f$], label-side: left, "->")
    edge((1, 0), (2, 0), "->")
    edge((1, 1), (2, 1), "->")
    edge((1, 0), (1, 1), [$g_Y$], label-side: left, "->")
    edge((2, 0), (2, 1), [$g$], label-side: left, "->")
    edge((0, 0), (0, 1), [$g_X$], label-side: right, "->")
    edge((0, -1), (1, -1), $f'$, "->")
    edge((1, -1), (2, -1), "->")
    edge((2, -1), (2, 0), $pi$, label-side: left, "->")
    edge((1, -1), (1, 0), $pi_Y$, label-side: left, "->")
    edge((0, -1), (0, 0), $pi_X$, "->")
  }))
  and note $cal(K)_Y cong pi_(Y,*) ul(Lambda), f^(-1) cal(K)_Y cong pi_(X,*) ul(Lambda)$. Compute: 
  $
    g_Y^(-1) R f_(0,*) cal(F) Lotimes_Lambda pi_(Y,*) ul(Lambda) &cong pi_(Y,*) pi_Y^(-1) g_Y^(-1) R f_(0,*) cal(F) #[by projection formula] \
    &cong pi_(Y,*) R f'_* pi_X^(-1) g_X^(-1) cal(F) #[by generic base change as in (2) of previous corollary] \
    &cong R f_* pi_(X,*) pi_X^(-1) g_X^(-1) cal(F) \
    &cong R f_* (g_X^(-1) cal(F) Lotimes_Lambda pi_(X,*) ul(Lambda)) #[by projection formula]
  $
  We are thereby done. 
]

We also establish a sort of generic base change for $R f^!$. 

#proposition[
  Let $S$ be a noetherian $ZZ[n^(-1)]$-scheme, $Lambda$ be an $n$-torsion noetherian ring, $f: X -> Y$ be a separated morphism of finite type $S$-schemes, and $cal(K) in D^b_c (Y_et, Lambda)$. Then there exists a dense open $U$ of $S$ s.t for any Cartesian diagram: 
  #align(center, diagram({
    node((0, 0), [$X'$])
    node((1, 0), [$Y'$])
    node((0, 1), [$X$])
    node((1, 1), [$Y$])
    // node((0.3, 0.3), [$cart$])
    node((2, 1), [$S$])
    node((2, 0), [$S'$])
    edge((0, 1), (1, 1), [$f$], label-side: right, "->")
    edge((0, 0), (1, 0), [$f'$], label-side: left, "->")
    edge((1, 0), (2, 0), "->")
    edge((1, 1), (2, 1), "->")
    edge((1, 0), (1, 1), [$g_Y$], label-side: left, "->")
    edge((2, 0), (2, 1), [$g$], label-side: left, "->")
    edge((0, 0), (0, 1), [$g_X$], label-side: right, "->")
  }))
  in which $g(S') subset U$, the base change map
  $
    g_X^(-1) R f^! cal(K) -> R f'^! g_Y^(-1) cal(K)
  $
  (induced by the transposed Beck-Chevalley base change along the proper base change map $R f'_! g_X^(-1) cong g_Y^(-1) R f_!$) is an isomorphism. 
]
#proof[
  It is easy to check from @bcbc-horizontal-concat and @bcbc-vertical-concat that this base change map for $R f^!$ is compatible with horizontal and vertical concatenation of Cartesian squares. 

  For the duration of this proof, we denote by an $(f, cal(K), S)$-good open of $S$ an open $U subset S$ for which the statement of this proposition holds. 

  This problem is Zariski local in $Y$. Pick an affine cover ${j_(Y,i): Y_i -> Y}$ and base change $f$ to $f_i: X_i -> Y_i$. Then suppose that $U$ is $(f_i, cal(K)|_(Y_i), S)$ good for all $i$. Then: 
  $
    g_(X_i)^(-1) R f_i^! (cal(K)|_(Y_i)) cong R f'_i^! g_(Y_i)^(-1) (cal(K)|_(Y_i))
  $
  which is saying $(g_X^(-1) R f^! cal(K))|_(X'_i) cong (R f'^! g_Y^(-1) cal(K))|_(X'_i)$. Thus $g_X^(-1) R f^! cal(K) cong R f'^! g_Y^(-1) cal(K)$ by @surjective-pullback-conservative. 

  Hence, we may assume that $Y$ is affine. Now pick an affine cover ${j_i: X_i -> Y}$ of $X$. Then suppose that $U$ is $(f compose j_i, cal(K), S)$-good for all $i$. Then this is saying that for $g: S' -> S$ with $g(S') subset U$, 
  $
    j'_i^(-1) g_X^(-1) R f^! cal(K) cong g_(X_i)^(-1) j_i^(-1) R f^! cal(K) cong j'_i^(-1) R f'^! g_Y^(-1) cal(K)
  $
  for all $i$. Thus $g_X^(-1) R f^! cal(K) cong R f'^! g_Y^(-1) cal(K)$ by @surjective-pullback-conservative, and so $U$ is $(f, cal(K), S)$-good. Thus we may argue Zariski locally on $X$ and assume that $X$ is affine with image contained in an affine open of $Y$. Thus we may assume that $X$ is affine too. We may thus factor $f$ into $X ->^i AA^m_Y ->^p Y$ for a closed immersion $i$. Now: 
  $
    g_X^(-1) R f^! cal(K) cong g_X^(-1) R i^! p^(-1) cal(K)(m)[2m] \
    R f'^! g_Y^(-1) cal(K) cong R i'^! p'^(-1) g_Y^(-1) cal(K)(m)[2m] cong R i'^! g_(AA^m_Y)^(-1) p^(-1) cal(K)(m)[2m]
  $
  by relative Poincare duality. Hence, replacing $f$ with $i$ and $cal(K)$ with $p^(-1) cal(K)(m)[2m]$, we may assume that $f=i$ is a closed immersion. Now take the complementary open immersion $j: U -> Y$ use the sections with support triangle: 
  $
    R i^! cal(K) -> i^(-1) cal(K) -> i^(-1) R j_* j^(-1) cal(K) ->^(+1)
  $
  By generic base change, we may shrink $S$ so that the formation of $R j_* j^(-1) cal(K)$ commutes with arbitrary base change. Now the second and third term of the triangle is compatible with base change, and so is the first. We are thereby done. 
]

Finally, as an application, we prove the preservation of $D^b_#[ctf]$ under the six fundamental constructions on etale sheaves we have defined, known as _Grothedieck's six functors_. 

#theorem(name: <finiteness-of-six-functors>)[
  (Finiteness of six functors) Let $f: X -> Y$ be a morphism between separated $k$-schemes for a field $k$, and $Lambda$ be an $n$-torsion noetherian ring with $n in k^times$. Then the functors: 
  $
    R f_*, R f_! : D(X_et, Lambda) -> D(Y_et, Lambda) \
    f^(-1), R f^!: D(Y_et, Lambda) -> D(X_et, Lambda) \
    - Lotimes_Lambda -: D(X_et, Lambda) times D(X_et, Lambda) -> D(X_et, Lambda) \
    RHHom_Lambda (-, -): D(X_et, Lambda)^opp times D(X_et, Lambda) -> D(X_et, Lambda)
  $
  all sends $D^b_#[ctf]$ to $D^b_#[ctf]$, with the first four being bounded above and below. 
]
#proof[
  Three of these statements are already known: 

  - $f^(-1)$ preserves $D^b_c$ by @constructible-sheaves-first-props (1), and preserves finite Tor-amplitude by checking stalks; 

  - $R f_!$ preserves $D^b_c$ by @finiteness-of-lower-shriek, and is bounded by Grothendieck vanishing. It preserves $D^b_#[ctf]$ by the projection formula: #h(1fr)
    $
      R f_! cal(K) Lotimes_Lambda cal(L) cong R f_! (cal(K) Lotimes_Lambda f^(-1) cal(L))
    $
    Indeed, suppose that $cal(K)$ has Tor-amplitude in $[a,b]$, and $cal(L)$ is concentrated in $[a',b']$. Then $cal(K) Lotimes_Lambda f^(-1) cal(L)$ is concentrated in $[a+a', b+b']$, and so $R f_! (cal(K) Lotimes_Lambda f^(-1) cal(L))$ is concentrated in $[a+a', b+b'+2d]$, where $d$ is the maximum fiber dimension of $f$. Hence, $R f_! cal(K)$ is Tor-amplitude in $[a, b+2d]$. 

  - $- Lotimes_Lambda -$ preserves $D^b_#[ctf]$. Indeed, for $cal(K)_(1,2) in D^b_#[ctf] (X_et, Lambda)$, we may pick bounded flat resolutions $cal(P)_(1,2)^bullet$ of them by @resolution-of-ctf-complexes, in which every term $cal(P)^q_(1,2)$ is constructible and flat. Then $Lotimes$ may be computed termwise: 
    $
      cal(K)_1 Lotimes_Lambda cal(K)_2 cong cal(P)^bullet_1 otimes_Lambda cal(P)^bullet_2
    $
    Now tensors of constructible sheaves are still constructible sheaves (by checking on a stratification), and tensors of flat sheaves are flat (formally). Hence every term in the complex $cal(P)^bullet_1 otimes_Lambda cal(P)^bullet_2$, being a finite direct sum of tensors of constructible and flat sheaves, is constructible and flat. Thus $cal(K)_1 Lotimes_Lambda cal(K)_2 in D^b_#[ctf] (X_et, Lambda)$. 

  The next functor to deal with is $R f_*$. 

  - By @finiteness-of-rf-lower-star, $R f_*$ preserves $D^b_c$ and is bounded above. It thus suffices to prove preservation of finite Tor-amplitude. #h(1fr)

    For this, we claim that for any complex $M in D(Lambda)$, the projection map identifies
    $
      R f_* cal(K) Lotimes_Lambda ul(M)_Y cong R f_* (cal(K) Lotimes_Lambda ul(M)_X)
    $
    Indeed, this property on $M$ is invariant under shifts and completion of distinguished triangles, since both sides are triangulated functors in $M$. Furthermore, both sides commute with arbitrary direct sums in $M$. This follows from the same truncation argument as in @derived-bounded-limit-formula-for-direct-sum, this time using the boundedness of $R f_*$ instead of $R Gamma$. Finally, when $M = Lambda$, both sides are $R f_* cal(K)$ and the projection is an isomorphism. Our claim is thus verified by @cpct-generator-of-d-lambda. 

    In particular, let $d$ be the cohomological dimension above of $R f_*$, and $[a,b]$ be the Tor-amplitude of $cal(K)$. Then we have shown that for every geometric point $ol(y)$ of $Y$, every complex $M$ of $Lambda$-modules supported on $[a',b']$
    $
      h^q ((R f_* cal(K))_(ol(y)) Lotimes_Lambda M) = 0, forall q in.not [a+a',b+b'+d]
    $
    Thus by checking stalks, for every complex $cal(L) in D(Y_et, Lambda)$ supported on $[a',b']$, $h^q (R f_* cal(K) Lotimes_Lambda cal(L)) = 0$ for all $q in.not [a+a',b+b'+d]$. Thus $R f_* cal(K)$ has Tor-amplitude in $[a,b+d]$. 

  Next, $R f^!$ is formal from $R f_!$. 

  - For a closed immersion $i: Z -> X$ with complementary open immersion $j: U -> X$, we have the section with support triangle: 
    $
      i_* R i^! cal(K) -> cal(K) -> R j_* j^(-1) cal(K) ->^(+1)
    $
    Now: 
    
    - Since $R j_*$ is bounded, so is $i_* R i^!$. Applying $i^(-1)$ thus shows that $R i^!$ is bounded; 

    - Since $R j_* j^(-1)$ preserves $D^b_#[ctf]$ as argued above, so does $i_* R i^!$. Applying $i^(-1)$ thus shows that $R i^!$ preserves $D^b_#[ctf]$. 

  - For a general separated morphism $f: X -> Y$ of finite type, cover $X$ by finitely many affine opens ${X_i}$, each lying over an affine open of $Y$. Take $X' = union.big_i X_i$ and take the local isomorphism $j: X' -> X$. Then $f compose j$ factors as $X ->^i AA^d_Y ->^p Y$ for a closed immersion $i$. Thus, 
    $
      j^(-1) R f^! cal(K) cong R i^! R p^! cal(K)
    $
    By relative Poincare duality, $R p^! cal(K) cong cal(K)(d)[2d]$. Thus $j^(-1) R f^! cal(K) cong R i^! R p^! cal(K) cong R i^! cal(K) (d)[2d]$. Since $R i^!$ is bounded and preserves $D^b_#[ctf]$, so does $j^(-1) R f^! cal(K)$. 

    Now constructiblity can be checked locally, so $R f^!$ preserves $D^b_c$. By checking stalks, $R f^!$ preserves $D^b_#[ctf]$. 

  The last functor to check is $RHHom_Lambda (-, -)$. 

  - To show that $RHHom_Lambda (-, -)$ preserves $D^b_#[ctf]$, by truncations and @resolution-of-ctf-complexes, it suffices to prove that for any flat constructible sheaves $cal(F), cal(G) in cAb(X_et, Lambda)$, $RHHom_Lambda (cal(F), cal(G)) in D^b_#[ctf] (X_et, Lambda)$. 
    
    Let: 
    $
      cal(S)_X = {Z subset X #[closed]:& RHHom_Lambda (cal(F), cal(G)) in D^b_#[ctf] #[for any flat constructible sheaves $cal(F), cal(G) in cAb(X_et, Lambda)$ \
      $&$whenever $supp(cal(F)) subset Z$]}
    $

    We intend to perform noetherian induction on $cal(S)_X$. Note that: 

    - Let $i: Z -> X$ be a closed subscheme. For any flat constructible sheaves $cal(F), cal(G) in cAb(X_et, Lambda)$ with $supp(cal(F)) subset Z$, we may write $cal(F) = i_* cal(F)_Z$ for a flat constructible sheaf $cal(F)_Z$ on $Z$. Now: 
      $
        RHHom_Lambda (i_* cal(F)_Z, cal(G)) cong i_* RHHom_Lambda (cal(F)_Z, R i^! cal(G))
      $
      Now $R i^! cal(G) in D^b_#[ctf] (Z_et, Lambda)$ as argued before, so suppose that $Z in cal(S)_Z$, and then truncations show that $RHHom_Lambda (cal(F)_Z, R i^! cal(G)) in D^b_#[ctf] (Z_et, Lambda)$. Applying $i_*$ preserves $D^b_#[ctf]$, and this proves that $Z in cal(S)_X$. 

      On the other hand, for constructible flat $cal(F)_Z, cal(G)_Z in cAb(Z_et, Lambda)$, 
      $
        RHHom_Lambda (cal(F)_Z, cal(G)_Z) cong i^(-1) RHHom(i_* cal(F)_Z, i_* cal(G)_Z)
      $
      and so $Z in cal(S)_X$ implies $Z in cal(S)_Z$. 
    
    Thus, $Z in cal(S)_X$ if and only if $Z in cal(S)_Z$. Thus to perform noetherian induction, it suffices to check that: 

    - If every proper closed subset $Z subset.neq X$ is in $cal(S)_X$, then $X in cal(S)_X$. 

    We now start to check this point. For any flat constructible sheaf $cal(F), cal(G) in cAb(X_et, Lambda)$, pick a nonempty open $U subset X$ s.t. $cal(F)|_U$ is constant. Take the complementary immersions $j: U -> X$ and $i: Z = X - U -> X$, and we have the extension by zero triangle: 
    $
      j_! j^(-1) cal(F) -> cal(F) -> i_* i^(-1) cal(F) ->^(+1)
    $ 
    Now $supp(i_* i^(-1) cal(F)) subset Z in cal(S)_X$, so $RHHom_Lambda (i_* i^(-1) cal(F), cal(G)) in D^b_#[ctf]$. Thus, it remains to check that $RHHom_Lambda (j_! j^(-1) cal(F), cal(G)) in D^b_#[ctf]$. Indeed, 
    $
      RHHom_Lambda (j_! j^(-1) cal(F), cal(G)) cong R j_* RHHom_Lambda (j^(-1) cal(F), j^(-1) cal(G))
    $
    Now $R j_*$ preserves $D^b_#[ctf]$, so it suffices to prove that $RHHom_Lambda (j^(-1) cal(F), j^(-1) cal(G)) in D^b_#[ctf]$. Now $j^(-1) cal(F)$ is locally constant, so replacing $X$ with $U$, it remains to prove that: 

    - If $cal(F), cal(G) in cAb(X_et, Lambda)$ are constructible flat with $cal(F)$ l.c.c, then $RHHom_Lambda (cal(F), cal(G)) in D^b_#[ctf]$. 

    Pick an etale cover $j: U -> X$ with $U$ affine s.t. $j^(-1) cal(F)$ is constant. Now suppose that we can show that $j^(-1) RHHom_Lambda (cal(F), cal(G)) in D^b_#[ctf]$. Then: 

    - $j^(-1) EExt^q_Lambda (cal(F), cal(G))$ are constructible and vanishes outside finitely many values of $q$. 

      Since $j$ is surjective, by @surjective-pullback-conservative, $EExt^q_Lambda (cal(F), cal(G))$ vanishes outside finitely many values of $q$. Furthermore, $cal(H) -> j_! j^(-1) cal(H)$ is injective for all $cal(H)$, and so $EExt^q_Lambda (cal(F), cal(G))$ are all constructible. 

      Thus, $RHHom_Lambda (cal(F), cal(G)) in D^b_c$. 

    - By checking stalks, we may upgrade to $RHHom_Lambda (cal(F), cal(G)) in D^b_#[ctf]$. 

    Now $j^(-1) RHHom_Lambda (cal(F), cal(G)) in D^b_#[ctf] cong RHHom_Lambda (j^(-1) cal(F), j^(-1) cal(G))$, so replacing $X$ with $U$ and noting that $j^(-1) cal(F)$ is constant, it remains to show that: 

    - If $cal(G) in cAb(X_et, Lambda)$ is constructible flat, and $M$ is a finite flat $Lambda$-module, then $RHHom_Lambda (ul(M), cal(G)) in D^b_#[ctf]$. 

    Any finite flat module over a noetherian ring is necessarily projective and locally free. Thus $M$ is a projective locally free $Lambda$-module. 
    
    #lemma[
      Suppose that $Lambda$ is a noetherian ring, $M$ is a finite $Lambda$-module and $N$ is any $Lambda$-module. Then for any scheme $X$, 
      $
        EExt^q_Lambda (ul(M)_X, ul(N)_X) = ul(Ext^q_Lambda (M, N))
      $
    ]
    #proof[
      We first prove for $N$ injective. That is, we need to show that for all $q >= 1$, $EExt^q_Lambda (ul(M)_X, ul(N)_X) = 0$. Pick a resolution $dots.c -> P^(-1) -> P^0 -> M -> 0$ by finite free $Lambda$-modules. Then $HHom_Lambda (ul(P^(-p)), -)$ is exact, and so $EExt^q_Lambda (ul(M)_X, -)$ may be computed as: 
      $
        EExt^q_Lambda (ul(M)_X, -) &cong h^q (0 -> HHom_Lambda (ul(P^0)_X, ul(N)_X) -> HHom_Lambda (ul(P^(-1))_X, ul(N)_X) -> dots.c) \
        &cong h^q (0 -> ul(Hom_Lambda (P^0, N))_X -> ul(Hom_Lambda (P^(-1), N))_X -> dots.c) \
        &cong ul(h^q (0 -> Hom_Lambda (P^0, N) -> Hom_Lambda (P^(-1), N) -> dots.c))_X \
        &= 0
      $ 
      where the final vanishing is due to $N$ being an injective $Lambda$-module. Now in the general case, pick an injective resolution $0 -> N -> I^0 -> I^1 -> dots.c$ of $N$. Since $EExt^p_Lambda (ul(M)_X, ul(I^q)_X)$ vanishes for all $p>=1$, this resolution can be used to compute $EExt^p_Lambda (ul(M)_X, ul(N)_X)$: 
      $
        EExt^p_Lambda (ul(M)_X, ul(N)_X) &cong h^p (0 -> HHom_Lambda (ul(M)_X, ul(I^0)_X) -> HHom_Lambda (ul(M)_X, ul(I^1)_X) -> dots.c) \
        &cong ul(h^p (0 -> Hom_Lambda (M, I^0) -> Hom_Lambda (M, I^1) -> dots.c))_X \
        &cong ul(Ext^p_Lambda (M, N))
      $
      We are thereby done. 
    ]

    By @finite-morphisms-and-constructible-sheaves, we may pick a resolution of $cal(G)$ by: 
    $
      0 -> cal(G) -> r_(0,*) ul(N^0) -> r_(1,*) ul(N^1) -> dots.c
    $
    for $N^q$ finite $Lambda$-modules and $r_q: X_q -> X$ finite. Now: 
    $
      EExt^q_Lambda (ul(M), r_(p,*) ul(N^p)) = r_(p,*) EExt^q_Lambda (ul(M)_(X_q), ul(N^p)_(X_q)) 
    $
    which vanishes for $q>=1$ by the previous lemma, since $M$ is a projective $Lambda$-module. Therefore, the resolution of $cal(G)$ above is suitable for computing $EExt^q_Lambda (ul(M), cal(G))$, and: 

    $
      EExt^q_Lambda (ul(M), cal(G)) cong h^q (dots.c -> HHom_Lambda (ul(M), r_(q-1,*) ul(N^(q-1))) -> HHom_Lambda (ul(M), r_(q,*) ul(N^q)) -> HHom_Lambda (ul(M), r_(q+1,*) ul(N^(q+1))) -> dots.c)
    $
    // By our choice of resolution, it is possible to take it so that each $r^q: X_q -> X$ factors as $X_q ->^(g^q) X_(q-1) ->^(r^(q-1)) X$. Thus, 
    // $
    //   EExt^q_Lambda (ul(M), cal(G)) cong r^(q-1)_* h^q (ul(Hom_Lambda (M, N^(q-1))) -> g^(q-1)_* ul(Hom_Lambda (M, N^q)) -> g^(q-1)_* g^q_*)
    // $
    Taking stalks this is the cohomology of: 
    $
      dots.c -> Hom_Lambda (M, oplus.big_(ol(x_(q-1)) in r_(q-1)^(-1) (ol(x))) N^(q-1)) -> Hom_Lambda (M, oplus.big_(ol(x_(q)) in r_(q)^(-1) (ol(x))) N^(q)) -> Hom_Lambda (M, oplus.big_(ol(x_(q+1)) in r_(q+1)^(-1) (ol(x))) N^(q+1)) -> dots.c
    $
    For $q >= 1$, $oplus.big_(ol(x_(q-1)) in r_(q-1)^(-1) (ol(x))) N^(q-1) -> oplus.big_(ol(x_(q)) in r_(q)^(-1) (ol(x))) N^(q) -> oplus.big_(ol(x_(q+1)) in r_(q+1)^(-1) (ol(x))) N^(q+1)$ is exact as the stalks of the resolution of $cal(G)$. Since $M$ is projective, the complex above is thus exact at $q$. This proves that: 
    $
      RHHom_Lambda (ul(M), cal(G)) = HHom_Lambda (ul(M), cal(G)) = ker(r_(0,*) Hom_Lambda (M, N^0) -> r_(1,*) Hom_Lambda (M, N^1))
    $
    is constructible. Checking stalks as above, we see that: 
    $
      HHom_Lambda (ul(M), cal(G))_(ol(x)) cong Hom_Lambda (M, cal(G)_(ol(x)))
    $
    Since $M$ is locally free, $M$ is dualizable with dual $caron(M)$ locally free too. Thus $Hom_Lambda (M, cal(G)_(ol(x))) cong caron(M) otimes_Lambda cal(G)_(ol(x))$ is flat. 

    In summary, $RHHom_Lambda (ul(M), cal(G)) = Hom_Lambda (ul(M), cal(G))$ is constructible flat, and we are done. 
]
