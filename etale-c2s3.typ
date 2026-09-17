#import "void-import.typ": *

== Infinitesimal lifting criterion

The shape of the statements in @etale-first-props might remind you of something: the behavior of unramified/etale morphisms under composition, base change, and cancellation resembles that of separated/proper morphisms, although they are geometrically totally different types of morphisms. Now separated/proper morphisms can be detected using the valuative criterion, so it is not that surprising that a similar criterion exists for unramified/etale morphisms. Indeed, that is the infinitesimal lifting criterion. 

#definition(name: <defn-formal-morphisms>)[
  Let $f: X -> Y$ be a morphism of schemes. For any ring $A$ and any ideal $I subset A$ with $I^2 = 0$, and any diagram in which the outer square commutes: 
  // https://q.uiver.app/#r=typst&q=WzAsNCxbMSwwLCJYIl0sWzEsMSwiWSJdLFswLDAsIlNwZWMoQVxcL0kpIl0sWzAsMSwiU3BlYyhBKSJdLFswLDEsImYiXSxbMiwzXSxbMywxXSxbMiwwXSxbMywwLCIiLDEseyJzdHlsZSI6eyJib2R5Ijp7Im5hbWUiOiJkYXNoZWQifX19XV0=
  #align(center, diagram({
    node((1, 0), [$X$])
    node((1, 1), [$Y$])
    node((0, 0), [$Spec(A\/I)$])
    node((0, 1), [$Spec(A)$])
    edge((1, 0), (1, 1), [$f$], label-side: left, "->")
    edge((0, 0), (0, 1), "->")
    edge((0, 1), (1, 1), "->")
    edge((0, 0), (1, 0), "->")
    edge((0, 1), (1, 0), "-->")
  }))
  we question the existence and the uniqueness of the dashed arrow fitting in the commutative diagram. 

  - $f$ is called *formally smooth*, if such a dashed arrow always exists; 

  - $f$ is called *formally unramified*, if such a dashed arrow is unique if it exists; 

  - $f$ is called *formally etale*, if such a dashed arrow always exists and is unique. 
]

The infinitesimal lifting criterion states that, whenever $f$ is locally of finite presentation, formally smooth/unramified/etale morphisms are exactly smooth/unramified/etale morphisms. To establish this theorem, we first need some general discussions on possible lifts. 

#lemma(name: <classifying-diff-of-infinitesimal-lifts>)[
  Let $f: X -> Y$ be a morphism of schemes. Let $T$ be a scheme and $T_0$ be a closed subscheme of $T$ defined by a sheaf of ideals $cal(I) subset cal(O)_T$ with $cal(I)^2 = 0$. Consider a commutative square: 
  // https://q.uiver.app/#r=typst&q=WzAsNCxbMSwwLCJYIl0sWzEsMSwiWSJdLFswLDAsIlNwZWMoQVxcL0kpIl0sWzAsMSwiU3BlYyhBKSJdLFswLDEsImYiXSxbMiwzXSxbMywxXSxbMiwwLCJ1XzAiXV0=
  #align(center, diagram({
    node((1, 0), [$X$])
    node((1, 1), [$Y$])
    node((0, 0), [$T_0$])
    node((0, 1), [$T$])
    edge((1, 0), (1, 1), [$f$], label-side: left, "->")
    edge((0, 0), (0, 1), "->", $i$)
    edge((0, 1), (1, 1), "->", $v$, label-side: right)
    edge((0, 0), (1, 0), [$u_0$], label-side: left, "->")
  }))
  Let $cal(L)$ be the topological sheaf of sets on $T$ defined by: 
  $
    cal(L)(U) = {u: U -> X: u compose i|_(U_0) = u_0|_(U_0), f compose u = v|_U}
  $ 
  Then there is a canonical action: 
  $
    HHom_(cal(O)_(T_0)) (u_0^* Omega_(X\/Y), cal(I)) times cal(L) -> cal(L)
  $
  that is simply transitive on sections on an open $U$ whenever $cal(L)(U) != emptyset$. 
]
#proof[
  We construct this sheaf action locally. Let $U = Spec(A) subset T$ be an affine open s.t. $v(U)$ is contained in an affine open $Spec(B)$ of $Y$, and $u_0 (U_0)$ is contained in an affine open $Spec(C)$ of $X$. Then on $U$, the sections $cal(L)(U)$ of lifts are exactly those lifts fitting in the following commutative diagram: 
  // https://q.uiver.app/#r=typst&q=WzAsNCxbMCwwLCJTcGVjKEFcXC9JKSJdLFswLDEsIlNwZWMoQSkiXSxbMSwwLCJTcGVjKEMpIl0sWzEsMSwiU3BlYyhCKSJdLFswLDIsInVfMCJdLFsyLDMsImYiXSxbMSwzLCJ2IiwyXSxbMCwxXSxbMSwyLCIiLDEseyJzdHlsZSI6eyJib2R5Ijp7Im5hbWUiOiJkYXNoZWQifX19XV0=
  #align(center, diagram({
    node((0, 0), [$Spec(A\/I)$])
    node((0, 1), [$Spec(A)$])
    node((1, 0), [$Spec(C)$])
    node((1, 1), [$Spec(B)$])
    edge((0, 0), (1, 0), [$u_0$], label-side: left, "->")
    edge((1, 0), (1, 1), [$f$], label-side: left, "->")
    edge((0, 1), (1, 1), [$v$], label-side: right, "->")
    edge((0, 0), (0, 1), "->")
    edge((0, 1), (1, 0), "-->")
  }))
  where $tilde(I) = cal(I)|_(Spec(A))$. For two such lifts $u_(1,2): Spec(A) -> Spec(C)$ induced from maps $u_(1,2)^\#: C -> A$, by definition: 
  $
    u_1^\# compose f^\# = v^\# = u_2^\# compose f^\#: B -> A
  $
  and $u_(1,2)^\#$ agrees after reduction to $A\/I$. Thus $delta = u_2^\# - u_1^\#: C -> A$ has its image in $I$. We claim that $delta$ is a $B$-derivation. Indeed, 
  $
    delta(f^\# (b)) = u_2^\# (f(b)) - u_1^\# (f(b)) = 0
  $
  and: 
  $
    delta(c_1 c_2) &= u_2^\# (c_1) u_2^\# (c_2) - u_1^\# (c_1) u_1^\# (c_2) \
    &= u_2^\# (c_1) delta(c_2) + u_1^\# (c_2) delta(c_1) \
    &= u_0^\# (c_1) delta(c_2) + u_0^\# (c_2) delta(c_1) #[since $I^2 = 0$]
  $
  Thus, $delta: C -> I$ is a $B$-derivation, i.e. an $C$-linear map $Omega_(C\/B) -> I$. Conversely, if $delta$ is such a derivation, then by the computation above, given any $u_1^\#: C -> A$ inducing a lift, $u_1^\# + delta$ also induces a lift. Thus we have constructed a simply transitive action: 
  $
    Hom_C (Omega_(C\/B), I) times cal(L)(U) -> cal(L)(U)
  $
  Now: 
  $
    Hom_C (Omega_(C\/B), I) cong Hom_(A\/I) (Omega_(C\/B) otimes_C A\/I, I) cong Gamma(U, HHom_(cal(O)_(T_0)) (u_0^* Omega_(X\/Y), cal(I)))
  $
  Thus we have constructed a simply transitive action: 
  $
    Gamma(U, HHom_(cal(O)_(T_0)) (u_0^* Omega_(X\/Y), cal(I))) times cal(L)(U) -> cal(L)(U)
  $
  This action is defined on those sufficiently small affine opens $U subset T$. It is routine to check that they are compatible with restrictions from $Spec(A)$ to $Spec(A_f)$. Now the intersection of any two affine opens can be covered by affine opens principal on both sides (#cite-stacks("01IW")[Lemma 26.11.5]). Thus these actions glue compatibly to a sheaf action: 
  $
    HHom_(cal(O)_(T_0)) (u_0^* Omega_(X\/Y), cal(I)) times cal(L) -> cal(L)
  $
  simply transitive on sections on an open $U$ whenever $cal(L)(U) != emptyset$. 
]

#lemma[
  For morphisms locally of finite presentation, smoothness is Zariski local on source. That is, for every open cover ${X_i}$ of $X$, a morphism $f: X -> Y$ locally of finite presentation is formally smooth if and only if $f|_(X_i): X_i -> Y$ is formally smooth. 
]
#proof[
  ($==>$) is easy, so we only prove ($<==$). For any commutative diagram: 
  // https://q.uiver.app/#r=typst&q=WzAsNCxbMCwwLCJTcGVjKEFcXC9JKSJdLFswLDEsIlNwZWMoQSkiXSxbMSwxLCJZIl0sWzEsMCwiWCJdLFszLDIsImYiXSxbMCwxXSxbMSwyLCJ2IiwyXSxbMCwzLCJ1XzAiXV0=
  #align(center, diagram({
    node((0, 0), [$Spec(A\/I)$])
    node((0, 1), [$Spec(A)$])
    node((1, 1), [$Y$])
    node((1, 0), [$X$])
    edge((1, 0), (1, 1), [$f$], label-side: left, "->")
    edge((0, 0), (0, 1), "->")
    edge((0, 1), (1, 1), [$v$], label-side: right, "->")
    edge((0, 0), (1, 0), [$u_0$], label-side: left, "->")
  }))
  where $I^2 = 0$. Let ${X_i}$ be an open cover of $X$ with each $f_i = f|_(X_i): X_i -> Y$ formally smooth. Each $u_0^(-1) (X_i)$ is open in $Spec(A\/I)$ which is homeomorphic to $Spec(A)$. Thus we may pick elements $f_(i,j) in A$ s.t. $u_0^(-1) (X_i) = union.big_j Spec(A_(f_(i,j))\/I_(f_(i,j)))$. Consider the following commutative diagram: 
  // https://q.uiver.app/#r=typst&q=WzAsNCxbMCwwLCJTcGVjKEFfKGZfKGksaikpXFwvSV8oZl8oaSxqKSkpIl0sWzAsMSwiU3BlYyhBXyhmXyhpLGopKSkiXSxbMSwxLCJZIl0sWzEsMCwiWF9pIl0sWzMsMiwiZl9pIl0sWzAsMV0sWzEsMiwidiIsMl0sWzAsMywidV8wIl0sWzEsMywidV9pIiwxLHsic3R5bGUiOnsiYm9keSI6eyJuYW1lIjoiZGFzaGVkIn19fV1d
  #context align(center, diagram({
    node((0, 0), [$Spec(A_(f_(i,j))\/I_(f_(i,j)))$])
    node((0, 1), [$Spec(A_(f_(i,j)))$])
    node((1, 1), [$Y$])
    node((1, 0), [$X_i$])
    edge((1, 0), (1, 1), [$f_i$], label-side: left, "->")
    edge((0, 0), (0, 1), "->")
    edge((0, 1), (1, 1), [$v$], label-side: right, "->")
    edge((0, 0), (1, 0), [$u_0$], label-side: left, "->")
    edge((0, 1), (1, 0), [$u_i$], label-side: center, "-->")
  }, crossing-fill: thm-box-curr-color()))
  By formal smoothness of $f_i$, the dotted lift $u_i$ exists. Now $u_i: Spec(A_(f_(i,j))) ->^(u_i) X_i -> X$ lifts $u_0: Spec(A_(f_(i,j))\/I_(f_(i,j))) -> X_i$. Thus, let $cal(L)$ be the sheaf of lifts as in the previous lemma, 
  $
    cal(L)(Spec(A_(f_(i,j)))) != emptyset
  $
  
  In other words, we have obtained an open cover ${U_alpha}$ of $Spec(A)$ by principal affines, s.t. each $cal(L)(U_alpha) != emptyset$. Let $cal(H) = HHom_(cal(O)_(Spec(A\/I))) (u_0^* Omega_(X\/Y), tilde(I))$ with the simply transitive action: 
  $
    Phi: cal(H) times cal(L) -> cal(L)
  $
  as indicated in the previous lemma. Now: 

  - There exists a unique $h_(alpha,beta) in cal(H)(U_(alpha,beta))$ s.t. $u_alpha|_(U_(alpha,beta)) = Phi(h_(alpha,beta)) (u_beta|_(U_(alpha,beta)))$. They formally satisfy the cocycle condition, thus defining a Cech cocycle: 
    $
      (h_(alpha,beta)) in caron(H)^1_#[Zar] ({U_alpha}, cal(H))
    $

  - Now $Spec(A)$ is an affine scheme, ${U_alpha}$ is an affine cover. Since $f$ is locally of finite presentation, $Omega_(X\/Y)$ is a quasi-coherent sheaf on $X$ of finite presentation. Thus: 
    $
      cal(H) = HHom_(cal(O)_(Spec(A\/I))) (u_0^* Omega_(X\/Y), tilde(I))
    $
    is a quasi-coherent sheaf on $Spec(A)$. Thus, 
    $
      caron(H)^1_#[Zar] ({U_alpha}, cal(H)) cong H^1_#[Zar] (Spec(A), cal(H)) = 0
    $
  
  - Hence, there exist sections ${h_alpha in cal(H)(U_alpha)}$ s.t. $h_(alpha,beta) = h_(beta)|_(U_(alpha,beta)) - h_(alpha)|_(U_(alpha,beta))$. Put $u'_alpha = Phi(h_alpha) u_alpha$. Then on $U_(alpha,beta)$, 
    $
      u'_beta = Phi(h_beta) u_beta = Phi(h_alpha) Phi(h_(alpha,beta)) u_beta = Phi(h_alpha) u_alpha = u'_alpha
    $
    Thus the lifts $u'_alpha: U_alpha -> X$ are compatible and glue to a global lift $Spec(A) -> X$. 
]

#theorem(name: <infinitesimal-lifting-criterion>)[
  Let $f: X -> Y$ be a morphism locally of finite presentation. Then: 

  + $f$ is smooth if and only if it is formally smooth; 

  + $f$ is unramified if and only if it is formally unramified; 

  + $f$ is etale if and only if it is formally etale. 
]
#proof[
  (3) is formal from (1) and (2), since (formal) etaleness is just (formal) unramifiedness and smoothness. Thus we only need to prove (1) and (2). 
  
  (1)($==>$) 
  #proof[
    Since formal smoothness has been shown to be local on source, it suffices to prove that standard smooth morphisms are formally smooth. Now for $AA^d_Y -> Y$, 
    // https://q.uiver.app/#r=typst&q=WzAsNCxbMCwwLCJTcGVjKEFcXC9JKSJdLFswLDEsIlNwZWMoQSkiXSxbMSwxLCJZIl0sWzEsMCwiQUFeZF9ZIl0sWzMsMiwicCJdLFswLDFdLFsxLDIsInYiLDJdLFswLDMsInVfMCJdXQ==
    #align(center, diagram({
      node((0, 0), [$Spec(A\/I)$])
      node((0, 1), [$Spec(A)$])
      node((1, 1), [$Y$])
      node((1, 0), [$AA^d_Y$])
      edge((1, 0), (1, 1), [$p$], label-side: left, "->")
      edge((0, 0), (0, 1), "->")
      edge((0, 1), (1, 1), [$v$], label-side: right, "->")
      edge((0, 0), (1, 0), [$u_0$], label-side: left, "->")
    }))
    a lift $u: Spec(A) -> AA^d_Y$ is equivalent to $d$ sections $a_1, dots.c, a_d in A$ reducing to the $d$ functions in $A\/I$ defining $u_0$. Thus we may lift them arbitrarily. Since formal smoothness is formally known to be compatible with composition, it suffices to prove that etale morphisms are formally smooth. By locality on source again, we may assume that $X = Spec(C), Y = Spec(B)$, and: 
    $
      C = (B[T]_(h(T)))/((g(T)))
    $
    s.t. $(g(T), g'(T)) = (1)$ as ideals of $B[T]_(h(T))$. Consider a commutative diagram: 
    // https://q.uiver.app/#r=typst&q=WzAsNCxbMCwwLCJBXFwvSSJdLFswLDEsIkEiXSxbMSwwLCJDIl0sWzEsMSwiQiJdLFszLDIsImciLDJdLFsxLDBdLFsyLDAsInVfMCIsMl0sWzMsMSwidiJdXQ==
    #align(center, diagram({
      node((0, 0), [$A\/I$])
      node((0, 1), [$A$])
      node((1, 0), [$C$])
      node((1, 1), [$B$])
      edge((1, 1), (1, 0), [$phi$], label-side: right, "->")
      edge((0, 1), (0, 0), "->")
      edge((1, 0), (0, 0), [$alpha_0$], label-side: right, "->")
      edge((1, 1), (0, 1), [$beta$], label-side: left, "->")
    }))
    Put $g_beta, h_beta in A[T]$ be $g,h$ with $beta$ applied on coefficients. Then $alpha_0$ is defined by a section $[a] in A\/I$ s.t. $g_beta ([a]) = 0 in A\/I, h_beta ([a]) in (A\/I)^times$. All we need to do is to construct a section $a in A$ s.t. $g_beta (a) = 0, h_beta (a) in A^times$. 
    
    Pick an arbitrary lift $a in A$ of the class $[a]$, so $g_beta (a) in I$. Note that since $I^2 = 0$, $[h_beta (a)] in (A\/I)^times$ implies $h_beta (a) in A^times$. Then for $epsilon in I$, since $epsilon^2 = 0$: 
    $
      g_beta (a + epsilon) = g_beta (a) + g'_beta (a) epsilon
    $
    Since $(g(T), g'(T)) = (1)$ as ideals of $B[T]_(h(T))$, we may choose polynomials $p_0 (T), p_1 (T) in B[T]$ s.t: 
    $
      p_0 (T) g(T) + p_1 (T) g'(T) = h(T)^N
    $
    Thus, 
    $
      p_(0,beta) (a) g_beta (a) + p_(1,beta) (a) g'_beta (a) = h_beta (a)^N
    $
    Put $epsilon = -h_beta (a)^(-N) p_(1,beta) (a) dot g_beta (a) in I$. Now: 
    $
      g_beta (a + epsilon) &= g_beta (a) + g'_beta (a) epsilon = g_beta (a) (1 - h_beta (a)^(-N) p_(1,beta) (a) g'_beta (a)) \
      &= g_beta (a)^2 h_beta (a)^(-N) p_(0,beta) (a) in I^2 = 0
    $
    and $h_beta (a+epsilon)$ reduces to a unit in $A\/I$, hence is a unit in $A^times$. Thus the representative $a+epsilon$ would work. 
    #suppress-qed
  ]

  ($<==$)
  #proof[
    For every $x in X$, it suffices to check smoothness locally. Thus (by locality of formal smoothness), shrinking $X$ around $x$ and $Y$ around $f(x)$, we may assume that $X = Spec(C), Y = Spec(B)$ are affine. Choose a presentation: 
    $
      C = (B[T_1, dots.c, T_n])/((f_1, dots.c, f_m)) = P\/I
    $
    with $P = B[T_1, dots.c, T_n], I = (f_1, dots.c, f_m) subset P$. Consider the diagram: 
    // https://q.uiver.app/#r=typst&q=WzAsNCxbMCwwLCJQXFwvSyJdLFswLDEsIlBcXC9LXjIiXSxbMSwwLCJDID0gUFxcL0siXSxbMSwxLCJCIl0sWzEsMF0sWzIsMCwiIiwyLHsic3R5bGUiOnsiYm9keSI6eyJuYW1lIjoiZG91YmxlIGJhcnJlZCJ9fX1dLFszLDJdLFszLDFdXQ==
    #align(center, diagram({
      node((0, 0), [$P\/I$])
      node((0, 1), [$P\/I^2$])
      node((1, 0), [$C = P\/I$])
      node((1, 1), [$B$])
      edge((0, 1), (0, 0), "->")
      edge((1, 0), (0, 0), "=")
      edge((1, 1), (1, 0), "->")
      edge((1, 1), (0, 1), "->")
    }))
    By formal smoothness, the quotient $P\/I^2 -> P\/I$ has a section $sigma: C = P\/I -> P\/I^2$. Define: 
    $
      delta: P -> I\/I^2, F |-> [F mod I^2] - sigma([F mod I])
    $
    Then: 

    - #h(1fr)
      $
        delta(p_1 p_2) &= [p_1 mod I^2][p_2 mod I^2] - sigma([p_1 mod I])sigma([p_2 mod I]) \
        &= [p_1 mod I^2] delta(p_2) + sigma([p_2 mod I]) delta(p_1) = p_1 delta(p_2) + p_2 delta(p_1)
      $
    
    - For $b in B$, 
      $
        delta(b) = [b mod I^2] - sigma([b mod I]) = 0
      $
      since every morphism here is a $B$-algebra homomorphism. 

    Thus $delta$ is a $B$-derivation, thus defining a $P$-linear map $rho: Omega_(P\/B) -> I\/I^2$ s.t. $rho(d F) = [F mod I^2] - sigma([F mod I])$. We thus have a $C$-linear map: 
    $
      rho: Omega_(P\/B) otimes_P C -> I\/I^2, d F |-> [F mod I^2]
    $
    since $C = P\/I$ and so the $sigma([F mod I])$ term vanishes. In the second exact sequence: 
    $
      I\/I^2 -> Omega_(P\/B) otimes_P C -> Omega_(C\/B) -> 0
    $
    the first map sends $[F mod I^2] |-> d F$. Thus $rho$ retracts this map, making this right exact sequence split exact. 

    By @equiv-defns-of-smooth (5), $f$ is a smooth morphism. 
    
    #suppress-qed
  ]

  (2)($==>$) If $f$ is unramified, $Omega_(X\/Y) = 0$ and so the sheaf $HHom_(cal(O)_(T_0)) (u_0^* Omega_(X\/Y), cal(I))$ in @classifying-diff-of-infinitesimal-lifts  always vanishes. Thus an infinitesimal lift is unique if any exists. 

  ($<==$) Suppose that $f$ is formally unramified. It is formal to check that we can verify locally, so we may assume that $X = Spec(C), Y = Spec(B)$ are affine. For any $C$-module $M$, take the square-zero algebra $C_M = C oplus M$ (with multiplication $(c_1,m_1) times (c_2, m_2) := (c_1 c_2, c_1 m_2 + c_2 m_1)$). Then $M subset C_M$ is a square-zero ideal and $C_M\/M cong C$. Thus in the following diagram: 
  // https://q.uiver.app/#r=typst&q=WzAsNCxbMSwwLCJDIl0sWzEsMSwiQiJdLFswLDEsIkNfTSJdLFswLDAsIkMiXSxbMiwzXSxbMSwwXSxbMSwyXSxbMCwzLCIiLDEseyJzdHlsZSI6eyJib2R5Ijp7Im5hbWUiOiJkb3VibGUgYmFycmVkIn19fV0sWzAsMiwiIiwxLHsic3R5bGUiOnsiYm9keSI6eyJuYW1lIjoiZGFzaGVkIn19fV1d
  #align(center, diagram({
    node((1, 0), [$C$])
    node((1, 1), [$B$])
    node((0, 1), [$C_M$])
    node((0, 0), [$C$])
    edge((0, 1), (0, 0), "->")
    edge((1, 1), (1, 0), "->")
    edge((1, 1), (0, 1), "->")
    edge((1, 0), (0, 0), "=")
    edge((1, 0), (0, 1), "-->")
  }))
  if a lift exists, then it is unique. However, $B$-linear sections to $C_M -> C$ are classified by $B$-derivations $C -> M$. The zero derivation always exists, so every other derivation is equal to that one. That is: 
  $
    Hom_C (Omega_(C\/B), M) = 0
  $
  for every $C$-module $M$. Thus $Omega_(C\/B) = 0$ and so $Spec(C) -> Spec(B)$ is unramified. 
]

#corollary(name: <etale-map-with-stable-residue-field-preserves-completions>)[
  Let $f: X -> Y$ be a morphism etale at $x$ with $y = f(x)$, and suppose that $k(x) = k(y)$. Then the natural maps: 
  $
    cal(O)_(Y,y)\/frak(m)_y^N -> cal(O)_(X,x)\/frak(m)_x^N
  $
  are all isomorphisms, and consequently, the natural map: 
  $
    hat(cal(O)_(Y,y)) -> hat(cal(O)_(X,x))
  $
  on the completions of the local rings is an isomorphism. 
]
#proof[
  Since $k(x) = k(y)$, we have a map $s_0: Spec(k(y)) = Spec(cal(O)_(Y,y)\/frak(m)_y) -> X$ by including $x$ to $X$. Now for $N >= 1$, each $Spec(cal(O)_(Y,y)\/frak(m)_y^N) -> Spec(cal(O)_(Y,y)\/frak(m)_y^(N+1))$ is a square-zero closed immersion, so by formal smoothness, there is a unique lift $s_N$ fitting in the following commutative diagram: 
  // https://q.uiver.app/#r=typst&q=WzAsNCxbMCwwLCJTcGVjKGNhbChPKV8oWSx5KVxcL2ZyYWsobSlfeV5OKSJdLFsxLDAsIlgiXSxbMSwxLCJZIl0sWzAsMSwiU3BlYyhjYWwoTylfKFkseSlcXC9mcmFrKG0pX3leKE4rMSkpIl0sWzAsMSwic18oTi0xKSJdLFsxLDIsImYiXSxbMywyXSxbMCwzXSxbMywxLCJzX04iLDFdXQ==
  #context align(center, diagram({
    node((0, 0), [$Spec(cal(O)_(Y,y)\/frak(m)_y^N)$])
    node((1, 0), [$X$])
    node((1, 1), [$Y$])
    node((0, 1), [$Spec(cal(O)_(Y,y)\/frak(m)_y^(N+1))$])
    edge((0, 0), (1, 0), [$s_(N-1)$], label-side: left, "->")
    edge((1, 0), (1, 1), [$f$], label-side: left, "->")
    edge((0, 1), (1, 1), "->")
    edge((0, 0), (0, 1), "->")
    edge((0, 1), (1, 0), [$s_N$], label-side: center, "->")
  }, crossing-fill: thm-box-curr-color()))

  The unique point of $Spec(cal(O)_(Y,y)\/frak(m)_y^(N+1))$ is sent to $x$ under $s_N$, so $s_N$ is induced by a local homomorphism $phi_N: cal(O)_(X,x) -> cal(O)_(Y,y)\/frak(m)_y^(N+1)$, all of them being compatible. 

  Its reduction mod $frak(m)_x = frak(m)_y cal(O)_(X,x)$ is the residue map $k(x) = k(y)$, and so $phi_N (frak(m)_x) subset frak(m)_y\/frak(m)_y^(N+1)$. Thus $phi_N$ kills $frak(m)_x^(N+1)$, inducing a map $psi_N: cal(O)_(X,x)\/frak(m)_x^(N+1) -> cal(O)_(Y,y)\/frak(m)_y^(N+1)$. Everything here is a $cal(O)_(Y,y)$-algebra homomorphism, so for the structure map $g_N: cal(O)_(Y,y)\/frak(m)_y^(N+1) -> cal(O)_(X,x)\/frak(m)_x^(N+1)$, at least we have $psi_N compose g_N = id$. 

  It remains to verify that the composition in the other direction is the identity. $g_0 compose psi_0$ is the identity since $k(x) = k(y)$. Suppose that we have already shown that $g_(N-1) compose psi_(N-1) = id$. Compare the two $cal(O)_(Y,y)$-algebra homomorphisms: The reduction: 
  $
    cal(O)_(X,x) -> cal(O)_(X,x)\/frak(m)_x^(N+1)
  $
  versus: 
  $
    cal(O)_(X,x) -->^(phi_N) cal(O)_(Y,y)\/frak(m)_y^(N+1) -->^(g_N) cal(O)_(X,x)\/frak(m)_x^(N+1)
  $
  By construction of $s_N$, after reduction mod $frak(m)_x^N\/frak(m)_x^(N+1)$, the second map becomes $cal(O)_(X,x) -->^(phi_(N-1)) cal(O)_(Y,y)\/frak(m)_y^N -->^(g_(N-1)) cal(O)_(X,x)\/frak(m)_x^N$, which is equal to the plain reduction by the inductive hypothesis. Thus, the two maps $cal(O)_(X,x) -> cal(O)_(X,x)\/frak(m)_x^(N+1)$ are both lifts in: 
  // https://q.uiver.app/#r=typst&q=WzAsNCxbMCwwLCJTcGVjKGNhbChPKV8oWCx4KVxcL2ZyYWsobSlfeF5OKSJdLFsxLDAsIlgiXSxbMSwxLCJZIl0sWzAsMSwiU3BlYyhjYWwoTylfKFgseClcXC9mcmFrKG0pX3heKE4rMSkpIl0sWzAsMV0sWzEsMiwiZiJdLFszLDJdLFswLDNdLFszLDEsIiIsMSx7InN0eWxlIjp7ImJvZHkiOnsibmFtZSI6ImRhc2hlZCJ9fX1dXQ==
  #align(center, diagram({
    node((0, 0), [$Spec(cal(O)_(X,x)\/frak(m)_x^N)$])
    node((1, 0), [$X$])
    node((1, 1), [$Y$])
    node((0, 1), [$Spec(cal(O)_(X,x)\/frak(m)_x^(N+1))$])
    edge((0, 0), (1, 0), "->")
    edge((1, 0), (1, 1), [$f$], label-side: left, "->")
    edge((0, 1), (1, 1), "->")
    edge((0, 0), (0, 1), "->")
    edge((0, 1), (1, 0), "-->")
  }))
  They are thus equal by formal unramifiedness. Hence $g_N compose psi_N = id$, and we have constructed the inverse for each $g_N$. Thus every $g_N$ is an isomorphism and we are done. 
]
