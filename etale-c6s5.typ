#import "void-import.typ": *
== Proof of (Reduce)

In this section, we prove (Reduce), another important step in the proof of proper base change. It allows us to reduce base change in a general Cartesian square to base change along $X -> Spec(A)$ and the special point of $Spec(A)$, for $A$ a strict henselian local ring. 

The proof of (Reduce) is a highly technical reduction argument, involving reducing Zariski/etale locally, passage to limits and topological invariance. 

We first need a lemma to establish the etale locality of base change: 

#lemma(name: <pbc-etale-bc>)[
  In a Cartesian square: 
  // https://q.uiver.app/#r=typst&q=WzAsNCxbMCwwLCJYJyJdLFsxLDAsIlknIl0sWzAsMSwiWCJdLFsxLDEsIlkiXSxbMiwzLCJmIl0sWzAsMSwiZiciXSxbMSwzLCJnIl0sWzAsMiwiZyciLDJdXQ==
  #align(center, diagram({
    node((-1, -1), [$X'$])
    node((0, -1), [$Y'$])
    node((-1, 0), [$X$])
    node((0, 0), [$Y$])
    edge((-1, 0), (0, 0), [$f$], label-side: left, "->")
    edge((-1, -1), (0, -1), [$f'$], label-side: left, "->")
    edge((0, -1), (0, 0), [$g$], label-side: left, "->")
    edge((-1, -1), (-1, 0), [$g'$], label-side: right, "->")
  }))
  in which $g$ is etale, the base change map: 
  $
    g^(-1) R^q f_* cal(F) -> R^q f'_* g'^(-1) cal(F)
  $
  is an isomorphism for all $cal(F) in cAb(X_et)$. 
]
#proof[
  We will use @pullback-along-etale-morphism-derived. For all $V' in Et_(Y')$ 
  $
    g^(-1) R^q f_* cal(F) (V') = R^q f_* cal(F) (V') = (V |-> H^q (f^(-1) (V), cal(F)))^\# (V')
  $
  where $(V |-> H^q (f^(-1) (V), cal(F))) in cPAb(Y_et)$, while: 
  $
    R^q f'_* g'^(-1) cal(F) (V') = (V' |-> H^q (f'^(-1) (V'), g'^(-1) cal(F)))^\# (V')
  $
  where $(V' |-> H^q (f^(-1) (V'), g'^(-1) cal(F))) in cPAb(Y'_et)$. Thus, it suffices to prove that: 
  $
    g^(-1) ((V |-> H^q (f^(-1) (V), cal(F)))^\#) = (V' |-> H^q (f^(-1) (V'), g'^(-1) cal(F)))^\# in cAb(Y'_et)
  $ 
  Note that: 
  $
    g^(-1)_cPSh (V |-> H^q (f^(-1) (V), cal(F))) = (V' |-> H^q (f'^(-1) (V'), g'^(-1) cal(F)))
  $
  by @pullback-along-etale-morphism-derived. The result then follows from @pullback-first-props (3). 
]

We also need to establish a limit formula for a later passage to limit argument. 

Firstly, we establish a version of the composite limit formula @limit-formula-composite for presheaves: 

#lemma(name: <limit-formula-composite-pab>)[
  Let ${X_i}_(i in I)$ be a projective system of qcqs schemes, with all transition maps $u_(i,j): X_i -> X_j$ for $i>=j$ affine. Let:
  $
    X = invlim_(i in I) X_i
  $
  with projections $v_i: X -> X_i$. $(cal(P)_i, psi_(i,j))$ is called a *system of presheaves* for the projective system ${X_i}$, if:
  
  - Each $cal(P)_i in cPAb((X_i)_et)$ is an abelian etale presheaf on $X_i$.
  
  - For any $i>=j$, $psi_(i,j): u_(i,j,cPSh)^(-1) cal(P)_j -> cal(P)_i$ is a presheaf morphism satisfying for $i>=j>=k$: #h(1fr)
    $
      psi_(i,k) = psi_(i,j) compose u_(i,j,cPSh)^(-1) psi_(j,k)
    $
  
  The *limit presheaf* of this system of presheaves is defined as:
  $
    cal(P) := dirlim_(i in I) v_(i,cPSh)^(-1) cal(P)_i
  $
  where for $i>=j$, the transition morphism $v_(j,cPSh)^(-1) cal(P)_j -> v_(i,cPSh)^(-1) cal(P)_i$ is induced by $v_(i,cPSh)^(-1) psi_(i,j)$. Then any qcqs $U in Et_X$ comes from base changing a qcqs $U_k in Et_(X_k)$ for some $k$, and the canonical morphism:
  $
    dirlim_(i>=k) cal(P)_i (U_i) -> cal(P)(U)
  $
  is an isomorphism. 
]
#proof[
  The proof will be similar to @limit-formula-composite, where we use both a limit formula on presheaves and one for schemes. The limit formula for presheaves is not a proposition, but rather the fact that colimits in the category of presheaves are computed section-wise. 

  Now: 
  $
    cal(P)(U) = dirlim_(j in I) v_(j,cPSh)^(-1) cal(P)_j (U) = dirlim_(j>=k) v_(j,cPSh)^(-1) cal(P)_j (U)
  $
  By @limit-formula-for-schemes-pab, which should be seen as a limit formula for schemes on presheaves: 
  $
    v_(j,cPSh)^(-1) cal(P)_j (U) = dirlim_(i>=j) u_(i,j,cPSh)^(-1) cal(P)_j (U_i)
  $
  Hence, 
  $
    cal(P)(U) = dirlim_(j>=k) dirlim_(i>=j) u_(i,j,cPSh)^(-1) cal(P)_j (U_i)
  $
  Since $I$ is a directed set, every pair $(j,i)$ in this double limit is dominated by $(i,i)$. In other words, the objects corresponding to $i = j >= k$ are cofinal in the index category of this colimit. Thus, 
  $
    cal(P)(U) = dirlim_(j>=k) dirlim_(i>=j) u_(i,j,cPSh)^(-1) cal(P)_j (U_i) = dirlim_(i>=k) cal(P)_i (U_i)
  $
  and we are done. 
]

Next, we establish a limit formula for base change, involving passage to limit of base changes. 

#proposition(name: <limit-formula-for-base-change>)[
  (Limit formula for base change) Let: 
  $
    X = invlim_(i in I) X_i, S = invlim_(i in I) S_i
  $
  be projective limits of qcqs schemes with affine transition morphisms $f_(i,j): X_i -> X_j$ and $h_(i,j): S_i -> S_j$ for $i>=j$. Denote the projections $f_i: X -> X_i, h_i: S -> S_i$. 

  Suppose that we are given morphisms $g_i: X_i -> S_i$ and $g: X -> S$ s.t. the diagram: 
  // https://q.uiver.app/#r=typst&q=WzAsNixbMCwxLCJYX2kiXSxbMSwxLCJTX2kiXSxbMCwyLCJYX2oiXSxbMSwyLCJTX2oiXSxbMCwwLCJYIl0sWzEsMCwiUyJdLFswLDEsImdfaSJdLFsyLDMsImdfaiIsMl0sWzAsMiwiZl8oaSxqKSIsMl0sWzEsMywiaF8oaSxqKSJdLFs0LDUsImciXSxbNSwxLCJoX2kiXSxbNCwwLCJmX2kiLDJdXQ==
  #align(center, diagram({
    node((-1, -1), [$X_i$])
    node((0, -1), [$S_i$])
    node((-1, 0), [$X_j$])
    node((0, 0), [$S_j$])
    node((-1, -2), [$X$])
    node((0, -2), [$S$])
    node((-0.7, -1.7), $cart$)
    node((-0.7, -0.7), $cart$)
    edge((-1, -1), (0, -1), [$g_i$], label-side: left, "->")
    edge((-1, 0), (0, 0), [$g_j$], label-side: right, "->")
    edge((-1, -1), (-1, 0), [$f_(i,j)$], label-side: right, "->")
    edge((0, -1), (0, 0), [$h_(i,j)$], label-side: left, "->")
    edge((-1, -2), (0, -2), [$g$], label-side: left, "->")
    edge((0, -2), (0, -1), [$h_i$], label-side: left, "->")
    edge((-1, -2), (-1, -1), [$f_i$], label-side: right, "->")
  }))
  has Cartesian squares. Then given a system of sheaves (as in @limit-formula-composite) $(cal(F)_i, psi_(i,j))$ for ${X_i}$, there is a canonical isomorphism: 
  $
    dirlim_(i in I) h_i^(-1) R^q g_(i,*) cal(F)_i -> R^q g_* cal(F)
  $
  where the transition morphisms $h_j^(-1) R^q g_(j,*) cal(F)_j -> h_i^(-1) R^q g_(i,*) cal(F)_i$ is the composition: 
  $
    h_j^(-1) R^q g_(j,*) cal(F)_j = h_i^(-1) h_(i,j)^(-1) R^q g_(j,*) cal(F)_j ->^BC h_i^(-1) R^q g_(i,*) f_(i,j)^(-1) cal(F)_j ->^(h_i^(-1) R^q g_(i,*) psi_(i,j)) h_i^(-1) R^q g_(i,*) cal(F)_i
  $
  where $BC$ denotes the base change map. Similarly, this map starting from the directed limit is constructed via: 
  $
    h_i^(-1) R^q g_(i,*) cal(F)_i ->^BC R^q g_* f_i^(-1) cal(F)_i ->^(R^q g_* psi_i) R^q g_* cal(F)
  $
]
#proof[
  Take: 
  $
    cal(P)_i = (V_i |-> H^q (X_i times_(S_i) V_i, cal(F)_i)) in cPAb((S_i)_et) \
    cal(P) = (V |-> H^q (X times_S V, cal(F))) in cPAb(S_et)
  $
  so that: 
  $
    R^q g_(i,*) cal(F)_i = cal(P)_i^\#, R^q g_* cal(F) = cal(P)^\#
  $
  Now: 
  $
    dirlim_(i in I) h_i^(-1) R^q g_(i,*) cal(F)_i = dirlim_(i in I) h_i^(-1) cal(P)_i^\# = (dirlim_(i in I \ cPAb) h_(i,cPSh)^(-1) cal(P)_i)^\#
  $
  by @pullback-first-props (3) and the fact that colimits commute with $(-)^\#$, which is a left adjoint. Now to show that: 
  $
    (dirlim_(i in I \ cPAb) h_(i,cPSh)^(-1) cal(P)_i)^\# = cal(P)^\#
  $
  since $S$ is qcqs, it suffices to show that the sections of these two sheaves agree on qcqs $V in Et_S$. Now $caron(H)^0 (V, -)$ is computed using qcqs objects of $Et_S$ only (as in the cofinal system $cal(S)$ in the proof of @limit-formula-for-schemes-0), so it suffices to prove that for qcqs $V in Et_S$, 
  $
    (dirlim_(i in I \ cPAb) h_(i,cPSh)^(-1) cal(P)_i)(V) = cal(P)(V)
  $
  LHS may be computed by @limit-formula-composite-pab: Suppose that $V in Et_S$ is base changed from qcqs $V_k in Et_(S_k)$, then: 
  $
    (dirlim_(i in I \ cPAb) h_(i,cPSh)^(-1) cal(P)_i)(V) = dirlim_(i>=k) cal(P)_i (V_i) = dirlim_(i>=k) H^q (X_i times_(S_i) V_i, cal(F)_i)
  $
  while $cal(P)(V) = H^q (X times_S V, cal(F))$. Now note that $S_i times_(S_k) (X_k times_(S_k) V_k) = X_i times_(S_i) V_i$ and the same goes with the subscript $i$ dropped, so by @limit-formula-composite, the composite limit formula, 
  $
    dirlim_(i>=k) H^q (X_i times_(S_i) V_i, cal(F)_i) = H^q (X times_S V, cal(F))
  $
  We are thereby done. 
]

#theorem(name: <pbc-reduce>)[
  (Reduce) When $Y', Y$ are locally noetherian,
  $
        & BC(X ->^f Y, Y' ->^g Y) \
    <== & (BC_* (X times_Y Spec(A) -> Spec(A)), forall Spec(A) -> Y, forall A #[noetherian strict henselian])
  $
  In plain English, base change holds for the Cartesian square: 
  // https://q.uiver.app/#r=typst&q=WzAsNCxbMCwwLCJYJyJdLFsxLDAsIlknIl0sWzAsMSwiWCJdLFsxLDEsIlkiXSxbMiwzLCJmIl0sWzAsMSwiZiciXSxbMSwzLCJnIl0sWzAsMiwiZyciLDJdXQ==
  #align(center, diagram({
    node((-1, -1), [$X'$])
    node((0, -1), [$Y'$])
    node((-1, 0), [$X$])
    node((0, 0), [$Y$])
    edge((-1, 0), (0, 0), [$f$], label-side: left, "->")
    edge((-1, -1), (0, -1), [$f'$], label-side: left, "->")
    edge((0, -1), (0, 0), [$g$], label-side: left, "->")
    edge((-1, -1), (-1, 0), [$g'$], label-side: right, "->")
  }))
  whenever it holds along $X times_Y Spec(A) -> Spec(A)$ and the special point of $Spec(A)$ for every morphism $Spec(A) -> Y$ where $A$ is noetherian strict henselian.  
]
#proof[
  #lemma(name: <pbc-reduce-etale-local>)[
    Base change is etale local in $Y'$. In other words, consider a diagram of successive base changes: 
    // https://q.uiver.app/#r=typst&q=WzAsNixbMCwxLCJYJyJdLFsxLDEsIlknIl0sWzAsMiwiWCJdLFsxLDIsIlkiXSxbMSwwLCJZJyciXSxbMCwwLCJYJyciXSxbMiwzLCJmIl0sWzAsMSwiZiciXSxbMSwzLCJnIl0sWzAsMiwiZyciLDJdLFs1LDQsImYnJyJdLFs0LDEsImgiXSxbNSwwLCJoJyciLDJdXQ==
    #align(center, diagram({
      node((0, 0), [$X'$])
      node((1, 0), [$Y'$])
      node((0, 1), [$X$])
      node((1, 1), [$Y$])
      node((1, -1), [$Y''$])
      node((0, -1), [$X''$])
      edge((0, 1), (1, 1), [$f$], label-side: left, "->")
      edge((0, 0), (1, 0), [$f'$], label-side: left, "->")
      edge((1, 0), (1, 1), [$g$], label-side: left, "->")
      edge((0, 0), (0, 1), [$g'$], label-side: right, "->")
      edge((0, -1), (1, -1), [$f''$], label-side: left, "->")
      edge((1, -1), (1, 0), [$h$], label-side: left, "->")
      edge((0, -1), (0, 0), [$h'$], label-side: right, "->")
    }))
    in which $h: Y'' -> Y'$ is surjective etale. Then base change holds for the lower square if and only if it holds for the whole rectangle. 
  ]
  #proof[
    ($==>$) is just (Comp) @pbc-comp (2), so it suffices to show ($<==$). For any torsion $cal(F) in cAb(X_et)$, we need to show that the base change map: 
    $
      g^(-1) R^q f_* cal(F) -> R^q f'_* g'^(-1) cal(F)
    $
    is an isomorphism. By @surjective-pullback-conservative, it suffices to show that: 
    $
      h^(-1) g^(-1) R^q f_* cal(F) -> h^(-1) R^q f'_* g'^(-1) cal(F)
    $
    is an isomorphism. Now by @pbc-etale-bc, the base change morphism $h^(-1) R^q f'_* g'^(-1) cal(F) -> R^q f''_* h'^(-1) g^(-1) cal(F)$ is an isomorphism (where $g'^(-1) cal(F)$ is torsion by @pullback-of-torsion-sheaf). By naturality of the base change morphism, composing this isomorphism with the morphism above gives: 
    $
      h^(-1) g^(-1) R^q f_* cal(F) -> h^(-1) R^q f'_* g'^(-1) cal(F) ->^tilde R^q f''_* h'^(-1) g^(-1) cal(F)
    $
    which is the base change morphism for the torsion sheaf $cal(F)$ along the large rectangle, hence an isomorphism. Thus $h^(-1) g^(-1) R^q f_* cal(F) -> h^(-1) R^q f'_* g'^(-1) cal(F)$ is an isomorphism and we are done. 
  ]
  Now pick a cover ${Y''_i}$ of $Y'$ by affine opens $Y''_i$ whose image in $Y'$ is contained in some affine open of $Y'$. Taking $Y'' = union.sq.big_i Y''_i$, and by the previous lemma, we may replace $g: Y' -> Y$ with $Y'' -> Y$. From the disjoint union structure, it suffices to show that base change holds along $f: X -> Y$ and $Y''_i -> Y$ for each $i$. In other words, we are free to assume that $Y'$ is affine with image in $Y$ contained in an affine open $Y_1$. Now $g: Y' -> Y$ factors as $Y' ->^(g_1) Y_1 ->^i Y$. Consider the diagram of successive base changes: 
  // https://q.uiver.app/#r=typst&q=WzAsNixbMCwxLCJYXzEiXSxbMSwxLCJZXzEiXSxbMCwyLCJYIl0sWzEsMiwiWSJdLFsxLDAsIlknIl0sWzAsMCwiWCciXSxbMiwzLCJmIl0sWzAsMSwiZiciXSxbMSwzLCJpIl0sWzAsMiwiaSciLDJdLFs1LDQsImYnJyJdLFs0LDEsImdfMSJdLFs1LDAsImcnXzEiLDJdXQ==
  #align(center, diagram({
    node((0, 1), [$X_1$])
    node((1, 1), [$Y_1$])
    node((0, 2), [$X$])
    node((1, 2), [$Y$])
    node((1, 0), [$Y'$])
    node((0, 0), [$X'$])
    edge((0, 2), (1, 2), [$f$], label-side: left, "->")
    edge((0, 1), (1, 1), [$f_1$], label-side: left, "->")
    edge((1, 1), (1, 2), [$i$], label-side: left, "->")
    edge((0, 1), (0, 2), [$i'$], label-side: right, "->")
    edge((0, 0), (1, 0), [$f'$], label-side: left, "->")
    edge((1, 0), (1, 1), [$g_1$], label-side: left, "->")
    edge((0, 0), (0, 1), [$g'_1$], label-side: right, "->")
  }))

  By @pbc-etale-bc, base change holds for the lower square since $i$ is an open immersion, hence etale. Thus, by (Comp) @pbc-comp (2), it suffices to show that base change holds for the upper square. Since $f_1$ is a base change of $f$, every base change of $f_1$ along some $Spec(A) -> Y_1$, $A$ noetherian strict henselian, is also the base change of $f$ along $Spec(A) -> Y_1 -> Y$. Therefore, the hypothesis still holds for $f_1$. Thus, replacing $f$ with $f_1$, $g$ with $g_1$, we may assume that: 

  - $Y' = Spec(B'), Y = Spec(B)$ are affine, so that $B'$ is a $B$-algebra, and that $B, B'$ are noetherian (since originally $Y, Y'$ are noetherian). 

  We claim that if (Reduce) holds whenever $g: Spec(B') = Y' -> Y = Spec(B)$ is of finite type, then (Reduce) holds in the general case. 

  #proof_[Proof of claim][
    By our arguments above, we may assume that $g: Spec(B') = Y' -> Y = Spec(B)$ is already between two affine schemes. Now write: 
    $
      B' = union.big_lambda B'_lambda = dirlim_(lambda) B'_lambda 
    $
    where ${B'_lambda}$ runs over all finite type $B$-subalgebras of $B'$, ordered under inclusion. This makes: 
    $
      Y' = invlim_lambda Y'_lambda, Y'_lambda = Spec(B'_lambda)
    $
    We thus have a passage to limit of base changes: 
    // https://q.uiver.app/#r=typst&q=WzAsOCxbMCwwLCJYJyJdLFsxLDAsIlknIl0sWzAsMSwiWCdfbGFtYmRhIl0sWzEsMSwiWSdfbGFtYmRhIl0sWzAsMiwiWCdfbXUiXSxbMSwyLCJZJ19tdSJdLFsxLDMsIlkiXSxbMCwzLCJYIl0sWzcsNiwiZiIsMl0sWzQsNSwiZidfbXUiXSxbMiwzLCJmJ19sYW1iZGEiXSxbMCwxLCJmJyJdLFsxLDMsImhfbGFtYmRhIl0sWzMsNSwiZ18obGFtYmRhLG11KSJdLFs1LDYsImdfbXUiXSxbNCw3LCJnJ19tdSIsMl0sWzIsNCwiZydfKGxhbWJkYSxtdSkiLDJdLFswLDIsImgnX2xhbWJkYSIsMl1d
    #align(center, diagram({
      node((0, -2), [$X'$])
      node((1, -2), [$Y'$])
      node((0, -1), [$X'_lambda$])
      node((1, -1), [$Y'_lambda$])
      node((0, 0), [$X'_mu$])
      node((1, 0), [$Y'_mu$])
      node((1, 1), [$Y$])
      node((0, 1), [$X$])
      node((0.3, -1.7), $cart$)
      node((0.3, -0.7), $cart$)
      node((0.3, 0.3), $cart$)
      edge((0, 1), (1, 1), [$f$], label-side: right, "->")
      edge((0, 0), (1, 0), [$f'_mu$], label-side: left, "->")
      edge((0, -1), (1, -1), [$f'_lambda$], label-side: left, "->")
      edge((0, -2), (1, -2), [$f'$], label-side: left, "->")
      edge((1, -2), (1, -1), [$h_lambda$], label-side: left, "->")
      edge((1, -1), (1, 0), [$g_(lambda,mu)$], label-side: left, "->")
      edge((1, 0), (1, 1), [$g_mu$], label-side: left, "->")
      edge((0, 0), (0, 1), [$g'_mu$], label-side: right, "->")
      edge((0, -1), (0, 0), [$g'_(lambda,mu)$], label-side: right, "->")
      edge((0, -2), (0, -1), [$h'_lambda$], label-side: right, "->")
    }))
    where each $g_mu$ is finite type. Since (Reduce) holds when $g$ is finite type, we see that base change along $f$ and $g_mu$, i.e. along the bottom square in the diagram above holds. We now invoke the limit formula for base change (@limit-formula-for-base-change): 
    $
      R^q f'_* g'^(-1) cal(F) &= dirlim_lambda h_lambda^(-1) R^q f'_(lambda,*) g'^(-1)_lambda cal(F) #[by limit formula for base change] \
      &= dirlim_lambda h_lambda^(-1) g_lambda^(-1) R^q f_* cal(F) \
      & #[since base change holds along $f$ and $g_lambda$, and $g'^(-1)_lambda cal(F)$ is torsion by @pullback-of-torsion-sheaf] \
      &= dirlim_lambda g^(-1) R^q f_* cal(F) = g^(-1) R^q f_* cal(F)
    $
    Hence base change holds along $f$ and $g$. 
    #suppress-qed
  ]
  We may thus assume that $g$ is of finite type. By @stalks-detects-properties and @very-dense-sets-of-pts, it suffices to prove that for any finite type point $y' in Y'$, the base change map $g^(-1) R^q f_* cal(F) -> R^q f'_* g'^(-1) cal(F)$ for torsion $cal(F)$ is an isomorphism at $ol(y') = Spec(k(y')^sep)$ where $k(y')^sep$ is a fixed separable closure of $k(y')$. Let $y = g(y')$, and $ol(y) = Spec(k(y)^sep)$ where $k(y)^sep$ is the separable closure of $k(y)$ in $k(y')^sep$. (This explicit choice is so that the stalk of $R^q f_* cal(F)$ at $g(ol(y'))$ is explicitly computed using the strict henselization of $cal(O)_(Y,g(y))$ w.r.t. $k(y) -> k(y)^sep$.)

  Now compute: 
  $
    (g^(-1) R^q f_* cal(F))_(ol(y')) &= (R^q f_* cal(F))_(g(ol(y'))) = H^q (X times_Y tilde(Y)_(ol(y)), cal(F)|_(X times_Y tilde(Y)_(ol(y)))) \
    &= H^q (X times_Y ol(y), cal(F)|_(X times_Y ol(y)))
  $
  since $tilde(Y)_(ol(y)) = Spec(cal(O)_(Y,y)^#[sh])$ is the spectrum of a strict henselian local ring, which is noetherian by @permanence-of-properties-under-henselization (0) since $Y$ is noetherian, and so by hypothesis, the restriction $H^q (X times_Y tilde(Y)_(ol(y)), cal(F)|_(X times_Y tilde(Y)_(ol(y)))) -> H^q (X times_Y ol(y), cal(F)|_(X times_Y ol(y)))$ is an isomorphism. Similarly, 
  $
    (R^q f'_* g'^(-1) cal(F))_(ol(y')) &= H^q (X' times_(Y') tilde(Y')_(ol(y')), cal(F)|_(X' times_(Y') tilde(Y')_(ol(y')))) = H^q (X times_Y tilde(Y')_(ol(y')), cal(F)|_(X times_Y tilde(Y')_(ol(y')))) \
    &= H^q (X times_Y ol(y'), cal(F)|_(X times_Y ol(y')))
  $
  by our strict henselian hypothesis. 
  
  Finally, note that since $y'$ is a finite type point, $y': Spec(k(y')) -> Y'$ is finite type. Since $g$ is finite type, $Spec(k(y')) -> Y' ->^g Y$ is finite type. Now taking the fiber at $y in Y$, we see that $Spec(k(y')) -> Spec(k(y))$ is finite type. In other words, $k(y')\/k(y)$ is a field extension that is finite type as a ring extension. By Hilbert's strong nullstellensatz, $k(y')\/k(y)$ is a finite extension. Hence, $k(y')^sep\/k(y)^sep$ is a purely inseparable algebraic extension. Therefore, $ol(y') -> ol(y)$ is a universal homeomorphism, and so: 
  $
    (g^(-1) R^q f_* cal(F))_(ol(y')) = H^q (X times_Y ol(y), cal(F)|_(X times_Y ol(y))) = H^q (X times_Y ol(y'), cal(F)|_(X times_Y ol(y'))) = (R^q f'_* g'^(-1) cal(F))_(ol(y'))
  $
  by topological invariance. We are thereby done. 
]
