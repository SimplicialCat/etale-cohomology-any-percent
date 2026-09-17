#import "void-import.typ": *

== Topological invariance <sect-topological-invariance>

In this section, we prove topological invariance of the etale site, that the etale site is insensitive to universal homeomorphisms, such as nilpotent thickenings and inseparable extensions of base fields. 

// #definition[
//   A scheme morphism $f: X' -> X$ is called a *universal homeomorphism*, if it induces a homeomorphism on underlying topological spaces upon any base change. 
// ]

Throughout this section, you should keep in mind that a universal homeomorphism is equivalent to an integral surjective radicial morphism, by @radicial-morphism-first-props (2). We will use this statement implicitly throughout this section. 

The statement of topological invariance is: 

- Given a universal homeomorphism $f: X' -> X$, the induced functor: #h(1fr)
  $
    Et_X -> Et_(X'), U |-> U' = U times_X X'
  $
  on etale sites is an equivalence of categories. 

Now that the underlying sites are equivalent, the notions of etale sheaves on $X$ and $X'$ are also equivalent, in the sense that $f_*: cAb(X'_et) arrows.rl cAb(X_et): f^(-1)$ are equivalences of categories and quasi-inverses to each other. 

The proof strategy of topological invariance is an induction on dimension. The induction is carried out through a preliminary limit argument to finite universal homeomorphisms between finite type $ZZ$-schemes, then through induction via the statement: 

- Topological invariance holds for $f: X' -> X$ if for any geometric point $ol(x)$ of $X$, topological invariance holds for $X' times_X tilde(X)_(ol(x)) -> tilde(X)_(ol(x))$. 

It will turn out that a universal homeomorphism $Spec(A') -> Spec(A)$ in which $A$ is strict henselian must have $A'$ strict henselian. Now by properties of strict henselian local rings, for any etale $A$-algebra $B$, the $k(A)$-points of $B$ correspond to direct factors $A$ of $B$. These factors may be trivially dropped, leaving us to prove topological invariance for the punctured spectra $U' = Spec(A') - frak(m)_(A') -> U = Spec(A) - frak(m)_A$. However, the local rings of $U$ have dimensions $< dim(A)$ because the closed point was removed. This allows an induction on dimension to be performed. 

This method is independently come up with by myself, but upon reference checking, it resembles the method of @cite-SGA1. 

We now start the proof. We first prove a lemma for limit arguments. 

#lemma(name: <passage-of-limit-of-univ-homeo>)[
  Let $X' = Spec(A') -> Spec(A) = X$ be a universal homeomorphism. Then: 
  
  + We may write $A' = dirlim_lambda A'_lambda$ as a directed limit of finite $A$-algebras in which every $Spec(A'_lambda) -> Spec(A)$ is a universal homeomorphism. 

  + If $A'$ is finite over $A$, we may write $A' = dirlim_lambda A'_lambda$ as a directed limit of finite $A$-algebras of finite presentation in which every $Spec(A'_lambda) -> Spec(A)$ is a universal homeomorphism. 
]
#proof[
  We claim that if the composition $X -> Y -> Z$ is a universal homeomorphism with $X -> Y$ surjective and both morphisms affine, then $X -> Y$ and $Y -> Z$ are both universal homeomorphism. 

  - Since $X$ is integral over $Z$ with $X -> Y -> Z$ both affine, $X$ is integral over $Y$. Since $X -> Z$ is injective, so is $X -> Y$. Now let $x in X$ lie above $y in Y$ and $z in Z$. Since $X -> Z$ is radicial, $k(x)\/k(z)$ is purely inseparable, and so $k(x)\/k(y)$ is also purely inseparable. Now by @equiv-defns-of-radicial (2), $X -> Y$ is radicial. Thus it is integral surjective radicial, hence a universal homeomorphism. 

    Since $X -> Y$ and $X -> Z$ are both universal homeomorphisms, so is $Y -> Z$. 

  (1) We may write $A' = dirlim_lambda A'_lambda$ as a directed limit of its finite type $A$-subalgebras, necessarily finite over $A$ since $A'$ is integral over $A$. Now consider $Spec(A') -> Spec(A'_lambda) -> Spec(A)$. 

  - Since $A'_lambda -> A'$ is an inclusion, $Spec(A') -> Spec(A'_lambda)$ is dominant. It is also closed by integrality, hence surjective. By definition $A -> A'_lambda$ is finite type and integral, hence finite. 

  Thus by claim, each $Spec(A'_lambda) -> Spec(A)$ is a universal homeomorphism. 

  (2) Pick $t_1, dots.c, t_n in A'$ s.t. $A' = A[t_1, dots.c, t_n]$, so that we may write $A' = A[T_1,dots.c,T_n]\/I$ for an ideal $I$. By finiteness, for each $i$ there is a monic polynomial $p_i (T_i) in I$. Now let $K_0 = (p_1 (T_1), dots.c, p_n (T_n))$, and put $A'_0 = A[T_1,dots.c,T_n]\/K_0$, a finite free $A$-algebra. Then $A'_0 ->> A'$ is a surjection with kernel $J$, and put: 
  $
    A' = dirlim_(K_lambda subset J \ #[finitely generated ideal]) A'_0\/K_lambda
  $
  Denote $A'_lambda = A'_0\/K_lambda$, and consider $Spec(A') -> Spec(A'_lambda) -> Spec(A)$. By claim, it suffices to prove that for sufficiently large $lambda$, $Spec(A') -> Spec(A'_lambda)$ is surjective. It suffices to show that $Spec(A'_0) - V(J)$ is quasi-compact. Indeed: 

  - If $Spec(A'_0) - V(J)$ is quasi-compact, there exists finitely many $f_1, dots.c, f_m in J$ s.t. $V(J) = V(f_1, dots.c, f_m)$. Thus $sqrt(J) = sqrt((f_1, dots.c, f_m))$. Thus, whenever $K_lambda supset (f_1, dots.c, f_m)$, we have $Spec(A'_0\/J) = Spec(A') -> Spec(A'_lambda) = Spec(A'_0\/K_lambda)$ a closed immersion defined by a nil ideal, hence surjective. 

  To establish this quasi-compactness, we use the universal homeomorphisms. Since $Spec(A') -> Spec(A)$ is a universal homeomorphism, so is $p: Spec(A' otimes_A A'_0) -> Spec(A'_0)$. 
  
  Consider $s: Spec(A') -> Spec(A' otimes_A A'_0)$ defined by the multiplication map: 
  $
    phi: A' otimes_A A'_0 -> A'
  $
  It is elementary to check that its kernel is $([T_1] otimes 1 - 1 otimes [T_1], dots.c, [T_n] otimes 1 - 1 otimes [T_n])$, a finitely generated ideal. Thus, 
  $
    s(Spec(A')) = V(ker(phi))
  $
  has quasi-compact complement. We claim that $p^(-1) (V(J)) = s(Spec(A'))$ on underlying set. Indeed, $p compose s: Spec(A') -> Spec(A'_0)$ is the structure map, identifying $Spec(A')$ with $V(J)$. Thus since $p$ is a homeomorphism, $p^(-1) (V(J)) = s(Spec(A'))$. 
  
  Thus $p^(-1) (V(J))$ has quasi-compact complement, and so does $V(J)$ since $p$ is a homeomorphism. Thus, truncating the directed system to those $J supset K_lambda supset (f_1, dots.c, f_m)$ concludes the proof. 
]

#theorem(name: <top-invariance>)[
  For any universal homeomorphism $f: X' -> X$, the induced functor: #h(1fr)
  $
    Et_X -> Et_(X'), U |-> U' = U times_X X'
  $
  on etale sites is an equivalence of categories. 
]
#proof[
  We denote by "topological invariance holds for $f: X' -> X$" for the statement that the induced map: 
  $
    f: Et_X -> Et_(X'), U |-> U' = U times_X X'
  $
  on etale sites is an equivalence of categories. 

  // The first few steps are reductions through limit arguments. Firstly, note that by @passage-to-limit-of-properties (3d), given a projective limit $S = invlim_i S_i$ of qcqs schemes under affine transition maps, 
  // $
  //   Et_S^#[qcqs] cong dirlim_i Et_(S_i)^#[qcqs]
  // $
  // where $Et_S^#[qcqs]$ denotes the full subcategory of $Et_S$ consisting of qcqs schemes. 
  
  #lemma[
    For every universal homeomorphism $f: X' -> X$, $Et_X -> Et_(X')$ is faithful. 
  ]
  #proof[
    Given $Y, Z in Et_X$ and $u, v in Hom_X (Y, Z)$ giving rise to $u',v' in Hom_(X') (Y', Z')$. Form the graphs $Gamma_u, Gamma_v: Y -> Y times_X Z$. These graphs, since $Z -> X$ is etale, are open immersions. Furthermore, it is purely formal that they base change to the graphs: 
    $
      Gamma_(u'), Gamma_(v'): Y' -> Y' times_(X') Z'
    $
    along $X' -> X$. Suppose that $u' = v'$. Then $Gamma_(u') (Y') = Gamma_(v') (Y')$. Since $Y' times_(X') Z' -> Y times_X Z$ is a homeomorphism, $Gamma_u (Y) = Gamma_v (Y)$. Thus, as open immersions, $Gamma_u = Gamma_v$, and upon projecting along $Y times_X Z -> Z$, we see that $u = v$. 
  ]

  Thus, we may assume faithfulness and only prove fullness and essential surjectivity. 

  Step 1. Topological invariance holds for all universal homeomorphisms, if it holds for all universal homeomorphisms between affine schemes. 

  #proof_[Proof of Step 1][
    Assume topological invariance for universal homeomorphisms between affine schemes. Let $f: X' -> X$ be a general universal homeomorphism. Cover $X$ by affine opens ${X_i}$, take $X_(i,j) = X_i inter X_j$, and form the base changes $f_i: X'_i -> X_i, f_(i,j): X'_(i,j) -> X_(i,j)$ of $f$. Each $f_i$ is a universal homeomorphism between affine schemes(, where $X'_i$ is affine since $f_i$ is integral and $X_i$ is affine). 

    We first prove full faithfulness. For etale $X$-schemes $Y, Z$, form the base changes $Y_i, Z_i$ and $Y_(i,j), Z_(i,j)$. Scheme morphisms glue on open covers, so we have equalizers: 
    $
      Hom_X (Y, Z) -> product_i Hom_(X_i) (Y_i, Z_i) arrows.rr product_(i,j) Hom_(X_(i,j)) (Y_(i,j), Z_(i,j))
    $
    and: 
    $
      Hom_(X') (Y', Z') -> product_i Hom_(X'_i) (Y'_i, Z'_i) arrows.rr product_(i,j) Hom_(X'_(i,j)) (Y'_(i,j), Z'_(i,j))
    $
    We now have a diagram: 
    // https://q.uiver.app/#r=typst&q=WzAsNixbMCwwLCJIb21fWCAoWSwgWikiXSxbMSwwLCJwcm9kdWN0X2kgSG9tXyhYX2kpIChZX2ksIFpfaSkiXSxbMiwwLCJwcm9kdWN0XyhpLGopIEhvbV8oWF8oaSxqKSkgKFlfKGksaiksIFpfKGksaikpIl0sWzAsMSwiSG9tXyhYJykgKFknLCBaJykiXSxbMSwxLCJwcm9kdWN0X2kgSG9tXyhYJ19pKSAoWSdfaSwgWidfaSkiXSxbMiwxLCJwcm9kdWN0XyhpLGopIEhvbV8oWCdfKGksaikpIChZJ18oaSxqKSwgWidfKGksaikpIl0sWzAsM10sWzEsNF0sWzIsNV0sWzAsMV0sWzEsMiwiIiwxLHsib2Zmc2V0IjoxfV0sWzEsMiwiIiwxLHsib2Zmc2V0IjotMX1dLFs0LDUsIiIsMSx7Im9mZnNldCI6LTF9XSxbNCw1LCIiLDEseyJvZmZzZXQiOjF9XSxbMyw0XV0=
    #align(center, diagram({
      node((0, 0), [$Hom_X (Y, Z)$])
      node((1, 0), [$product_i Hom_(X_i) (Y_i, Z_i)$])
      node((2, 0), [$product_(i,j) Hom_(X_(i,j)) (Y_(i,j), Z_(i,j))$])
      node((0, 1), [$Hom_(X') (Y', Z')$])
      node((1, 1), [$product_i Hom_(X'_i) (Y'_i, Z'_i)$])
      node((2, 1), [$product_(i,j) Hom_(X'_(i,j)) (Y'_(i,j), Z'_(i,j))$])
      edge((0, 0), (0, 1), "->")
      edge((1, 0), (1, 1), "->")
      edge((2, 0), (2, 1), "->")
      edge((0, 0), (1, 0), "->")
      edge((1, 0), (2, 0 - 0.12), "->")
      edge((1, 0), (2, 0 + 0.12), "->")
      edge((1, 1), (2, 1 - 0.12), "->")
      edge((1, 1), (2, 1 + 0.12), "->")
      edge((0, 1), (1, 1), "->")
    }))
    with commuting parallelograms and equalizer rows. 

    - By our assumption on topological invariance for universal homeomorphisms between affine schemes, the middle vertical arrow is bijective. We have already proved faithfulness, so all vertical arrows are injective. 

      By diagram tracing, the first arrow is surjective, so we have full faithfulness. 

    Next, we prove essential surjectivity. For any etale $X'$-scheme $Y'$, form $Y'_i = Y' times_(X') X'_i$. By the affine case, each $Y'_i$ descends to an etale $X_i$-scheme $Y_i$. By full faithfulness, there are compatible isomorphisms $Y_i times_(X_i) X_(i,j) cong Y_j times_(X_j) X_(i,j)$. They thus glue to an etale $X$-scheme $Y$ s.t. $Y' cong Y times_X X'$. 
  ]

  To proceed, we prove a lemma that allows us to replace $Et_(Spec(A))$ with the category of etale $A$-algebras, thus introducing necessary qcqs conditions. 

  #lemma(name: <top-invariance-et-to-et-aff>)[
    Let $f: X' = Spec(A') -> X = Spec(A)$ be a universal homeomorphism, and denote by $Et_S^#[aff]$ the full category of $Et_S$ consisting of affine schemes. Then topological invariance holds for $f$ (i.e. $Et_X -> Et_(X')$ is an equivalence), if and only if $Et_X^#[aff] -> Et_(X')^#[aff]$ is an equivalence. 
  ]
  #proof[
    Note that $Y in Et_X$ is affine if and only if $Y' = Y times_X X'$ is affine. Indeed, if $Y$ is affine then $Y'$ is obviously affine. Conversely, if $Y'$ is affine, note that $Y' -> Y$ is integral and surjective. By @passage-to-limit-of-morphisms, we may write $Y' = invlim_i Y'_i -> Y$ where $Y'_i$ are finite $Y$-schemes of finite presentation. Each $Y'_i -> Y$ is surjective, and by #cite-stacks("01Z6")[Lemma 32.4.13], $Y'_i$ is affine for sufficiently large $i$. Thus $Y$ admits a finite surjection from an affine scheme, and is affine by Chevalley's theorem. This immediately gives the ($==>$) direction. We now focus on the ($<==$) direction and assume that $Et_X^#[aff] -> Et_(X')^#[aff]$ is an equivalence. 
 
    We first demonstrate full faithfulness. Faithfulness is known, so it suffices to prove fullness. Indeed, let $Y, Z in Et_X$ and let $u' in Hom_(X') (Y', Z')$, cover $Z'$ by affine opens ${Z'_i}$, and $Y'$ by affine opens ${Y'_j}$ s.t. $u'(Y'_j) subset Z'_(alpha(j))$ for some index $alpha(j)$. We may now restrict to maps $u'_j: Y'_j -> Z'_(alpha(j))$. 

    By essential surjectivity in the affine case, $Y'_j, Z'_i in Et_(X')$ descend to $Y_j, Z_i in Et_X$. Then by full faithfulness in the affine case, there exist maps $u_j: Y_j -> Z_(alpha(j))$ base changing to $u'_j$. By faithfulness, the maps $Y_j ->^(u_j) Z_(alpha(j)) -> Z$ are compatible on $Y_j inter Y_(j')$, and thus glue to a map $u: Y -> Z$ base changing to $u'$. We thus obtain fullness. 

    Finally, for essential surjectivity, take any $Y' in Et_(X')$. Cover $Y'$ by affine opens ${Y'_i}$ and by the affine case, $Y'_i = Y_i times_X X'$ for some affine $Y_i in Et_X$. Let $Y'_(i,j) = Y'_i inter Y'_j$ descend to opens $Y^((1))_(i,j) subset Y_i, Y^((2))_(i,j) subset Y_j$, and then by full faithfulness, there are compatible isomorphisms $Y_(i,j)^((1)) cong Y_(i,j)^((2))$, allowing us to glue ${Y_i}$ to $Y in Et_X$ that base changes to $Y'$. This concludes the proof. 
  ]

  We will use the above lemma implicitly throughout the rest of the proof. 

  To proceed, we use limit arguments. Let $S = invlim_i S_i$ be a projective limit of affine schemes. Then by @passage-to-limit-of-morphisms and @passage-to-limit-of-properties (1a)(3d), 
  $
    Et_S^#[aff] cong dirlim_i Et_(S_i)^#[aff]
  $ 

  Step 2. Topological invariance holds for all universal homeomorphisms, if it holds for all finite universal homeomorphisms of finite presentation between affine schemes. 
  #proof[
    By Step 1, it suffices to deal with a universal homeomorphism $f: Spec(A') = X' -> X = Spec(A)$ between affine schemes. By @passage-of-limit-of-univ-homeo (1), we may write $X' = invlim_i X'_i$ as a projective limit of finite $X$-schemes, in which each $f_i: Spec(A'_i) = X'_i -> X$ is a universal homeomorphism. By @passage-of-limit-of-univ-homeo (2), we may write each $X'_i = invlim_j X'_(i,j)$ as a projective limit of finite $X$-schemes of finite presentation, in which each $f_(i,j): X'_(i,j) -> X$ is a universal homeomorphism. 

    Now that each $f_(i,j)$ is a finite universal homeomorphism of finite presentation, by this assumed case of topological invariance, we have $Et_X cong Et_(X'_(i,j))$. Now, 
    $
      Et_(X'_i)^#[aff] cong dirlim_j Et_(X'_(i,j))^#[aff] cong dirlim_j Et_X^#[aff] cong Et_X^#[aff]
    $
    and so: 
    $
      Et_(X')^#[aff] cong dirlim_i Et_(X'_i)^#[aff] cong dirlim_i Et_X^#[aff] cong Et_X^#[aff]
    $
    and we are done. 
  ]

  Step 3. Topological invariance holds for all universal homeomorphisms, if it holds for all finite universal homeomorphisms between finite type affine $ZZ$-schemes. 

  #proof[
    By Step 2, it suffices to deal with a finite universal homeomorphism of finite type $f: Spec(A') = X' -> X = Spec(A)$ between affine schemes. Writing $A = dirlim_i A_i$ as a directed limit of finite type $ZZ$-algebras. Let $X_i = Spec(A_i)$, and by @passage-to-limit-of-morphisms, there exists a finite stage $i_0$ and $f_(i_0): X'_(i_0) -> X_(i_0)$ whose base change along $X -> X_(i_0)$ is $f: X' -> X$. Base change $f_(i_0)$ to $f_i: X'_i -> X_i$ at stages $i>=i_0$, and by @passage-to-limit-of-properties (2a)(3g) and (3g) applied to the diagonal, upon enlarging $i_0$, we have all $f_i$ being finite universal homeomorphisms. Thus each $f_i$ is a finite universal homeomorphism between finite type $ZZ$-schemes, so by the assumed case $Et_(X'_i) cong Et_(X_i)$. Thus, 
    $
      Et_(X')^#[aff] cong dirlim_i Et_(X'_i)^#[aff] cong dirlim_i Et_(X_i)^#[aff] cong Et_X^#[aff]
    $
    and we are done. 
  ]

  After this limit argument, we are ready to perform the induction. We prove the key lemma first: 

  #lemma[
    Let $f: Spec(A') = X' -> X = Spec(A)$ be a finite universal homeomorphism between affine schemes. 

    Topological invariance holds for $f$, if for every geometric point $ol(x)$ of $X$, topological invariance holds for the base change $tilde(f)_(ol(x)): tilde(X)_(ol(x)) times_X X' -> tilde(X)_(ol(x))$. 
  ]
  #proof[
    (Fully faithfulness) Faithfulness is already known, so we only deal with fullness. Let $Y, Z in Et_X^#[aff]$ and $u' in Hom_(X') (Y', Z')$. For every point $x in X$, let $ol(x)$ be a geometric point above $x$. Topological invariance holds for $tilde(f)_(ol(x)): tilde(X)_(ol(x)) times_X X' -> tilde(X)_(ol(x))$. Thus, the base change $tilde(u)'_(ol(x)) in Hom_(X' times_X tilde(X)_(ol(x))) (Y' times_X tilde(X)_(ol(x)), Z' times_X tilde(X)_(ol(x)))$ is base changed from a morphism $tilde(u)_(ol(x)) in Hom_(tilde(X)_(ol(x))) (Y times_X tilde(X)_(ol(x)), Z times_X tilde(X)_(ol(x)))$. 

    By @passage-to-limit-of-morphisms (1), there exists an etale neighborhood $(V, ol(v)) -> (X, ol(x))$ and a morphism $u_V: Y times_X V -> Z times_X V$ that base changes to $tilde(u)_(ol(x))$. By @passage-to-limit-of-morphisms (3), up to shrinking $(V, ol(v))$, we may assume that the base change $u'_V: Y' times_X V -> Z' times_X V$ is the base change of $u'$ along $V -> X$. By shrinking $V$ further, we may assume that $V$ is affine. 

    Repeat this process for every point $x in X$ and picking a finite subcover, we see that there exists a surjective etale $V -> X$ and a morphism $u_V: Y times_X V -> Z times_X V$, satisfying: 

    - The base change $u'_V: Y' times_X V -> Z' times_X V$ along $X' -> X$, is exactly the same as the base change of $u'$ along $V -> X$. 

    Put $V_2 = V times_X V$, and $V' = X' times_X V, V'_2 = X' times_X V_2$. By fpqc descent of morphisms, we have a diagram: 
    // https://q.uiver.app/#r=typst&q=WzAsNixbMCwwLCJIb21fWCAoWSwgWikiXSxbMCwxLCJIb21fKFgnKSAoWScsIFonKSJdLFsxLDAsIkhvbV9WIChZIHRpbWVzX1ggViwgWiB0aW1lc19YIFYpIl0sWzIsMCwiSG9tXyhWXzIpIChZIHRpbWVzX1ggVl8yLCBaIHRpbWVzX1ggVl8yKSJdLFsxLDEsIkhvbV8oVicpIChZJyB0aW1lc18oWCcpIFYnLCBaJyB0aW1lc18oWCcpIFYnKSJdLFsyLDEsIkhvbV8oVidfMikgKFknIHRpbWVzXyhYJykgVidfMiwgWicgdGltZXNfKFgnKSBWJ18yKSJdLFswLDJdLFsxLDRdLFswLDFdLFsyLDRdLFszLDVdXQ==
    #align(center, diagram({
      node((0, 0), [$Hom_X (Y, Z)$])
      node((0, 1), [$Hom_(X') (Y', Z')$])
      node((1, 0), [$Hom_V (Y times_X V, Z times_X V)$])
      node((2, 0), [$Hom_(V_2) (Y times_X V_2, Z times_X V_2)$])
      node((1, 1), [$Hom_(V') (Y' times_(X') V', Z' times_(X') V')$])
      node((2, 1), [$Hom_(V'_2) (Y' times_(X') V'_2, Z' times_(X') V'_2)$])
      edge((0, 0), (1, 0), "->", $alpha_1$)
      edge((0, 1), (1, 1), "->", $alpha_2$, label-side: right)
      edge((0, 0), (0, 1), "->", $g_1$)
      edge((1, 0), (1, 1), "->", $g_2$)
      edge((2, 0), (2, 1), "->", $g_3$, label-side: left)
      edge((1, 0), (2, 0 + 0.12), "->", $beta_(1,2)$, label-side: right)
      edge((1, 0), (2, 0 - 0.12), "->", $beta_(1,1)$, label-side: left)
      edge((1, 1), (2, 1 + 0.12), "->", $beta_(2,2)$, label-side: right)
      edge((1, 1), (2, 1 - 0.12), "->", $beta_(2,1)$, label-side: left)
    }))
    in which the rows are equalizers and every diagram commutes. The maps $g_(1,2,3)$ are injective by faithfulness, and we have $g_2 (u_V) = u'_V = alpha_2 (u')$. Now: 
    $
      g_3 (beta_(1,1) (u_V)) = beta_(2,1) (g_2 (u_V)) = beta_(2,1) (alpha_2 (u')) = beta_(2,2) (alpha_2 (u')) = beta_(2,2) (g_2 (u_V)) = g_3 (beta_(1,2) (u_V))
    $
    Since $g_3$ is injective, $beta_(1,1) (u_V) = beta_(1,2) (u_V)$, and since the first row is an equalizer, there exists $u in Hom_X (Y, Z)$ s.t. $alpha_1 (u) = u_V$. Now: 
    $
      alpha_2 (u') = g_2 (u_V) = g_2 (alpha_1 (u)) = alpha_2 (g_1 (u))
    $
    and so $u' = g_1 (u)$. Thus $u'$ is in the image of $Hom_X (Y, Z) -> Hom_(X') (Y', Z')$, concluding the proof of fully faithfulness. 

    (Essential surjectivity) Let $Y' in Et_(X')^#[aff]$. For every point $x in X$, let $ol(x)$ be a geometric point above $x$. Topological invariance holds for $tilde(f)_(ol(x)): tilde(X)_(ol(x)) times_X X' -> tilde(X)_(ol(x))$. Thus, there exists some $tilde(Y)_(ol(x)) in Et_(tilde(X)_(ol(x)))$ s.t. $X' times_X tilde(Y)_(ol(x)) cong tilde(X)_(ol(x)) times_X Y'$. By @passage-to-limit-of-properties (1a)(3d), there exists an affine etale neighborhood $(V, ol(v)) -> (X, ol(x))$ and an affine etale $Y_V in Et_V^#[aff]$ s.t. $tilde(Y)_(ol(x)) = tilde(X)_(ol(x)) times_V Y_V$. Let $Y'_V = X' times_X Y_V$. Then, 
    $
      tilde(X)_(ol(x)) times_X Y'_V cong tilde(X)_(ol(x)) times X' times_X Y_V cong X' times_X tilde(Y)_(ol(x)) cong tilde(X)_(ol(x)) times_X Y'
    $
    Hence, by @passage-to-limit-of-morphisms (3), upon shrinking $V$, we may assume $V times_X Y' cong Y'_V := X' times_X Y_V$. 

    Repeat this process for every point $x in X$ and pick a finite subcover. We see that there exists a surjective affine etale $V ->> X$ and an affine etale $Y_V in Et_V^#[aff]$ s.t: 
    $
      X' times_X Y_V cong V times_X Y' 
    $

    Write $V = Spec(A_1)$ so $A_1$ is a surjective etale $A$-algebra, and $A'_1 = A_1 otimes_A A'$. Write $Y' = Spec(B')$. Then our condition translates to: 

    - We have an etale $A_1$-algebra $B_1$ and an isomorphism: #h(1fr)
      $
        phi: B_1 otimes_A A' -> B' otimes_A A_1
      $

    We now define an isomorphism $eta: B_1 otimes_A A_1 -> A_1 otimes_A B_1$ as follows. A morphism $s$ suffixed by a permutation will denote a permutation of tensor factors. A suffix to a morphism denotes the tensor factors it acts on. We first define it up to tensoring with $A'$: 
    $
      eta': B_1 otimes_A A_1 otimes_A A' &->^(phi_(1,3)) B' otimes_A A_1 otimes_A A_1 ->^(s_((1,2))) A_1 otimes_A B' otimes_A A_1 ->^(phi_(2,3)^(-1)) A_1 otimes_A B_1 otimes_A A'
    $
    Now $B_1 otimes_A A_1$ and $A_1 otimes_A B_1$ are etale $A$-algebras. Thus, by fully faithfulness, $eta'$ descends to an isomorphism: 
    $
      eta: B_1 otimes_A A_1 -> A_1 otimes_A B_1
    $
    We now verify the cocycle condition. 

    - By fully faithfulness, it suffices to verify the cocycle conditions tensoring $A'$. Expanding, we need to show that the following composition is exactly $eta'_(1,3,4)$: 
      $
        B_1 otimes_A A_1 otimes_A A_1 otimes_A A' &-->^(phi_(1,4)) B' otimes_A A_1 otimes_A A_1 otimes_A A_1 -->^(s_((1,2))) A_1 otimes_A B' otimes_A A_1 otimes_A A_1 \
        &-->^(phi_(2,4)^(-1)) A_1 otimes_A B_1 otimes_A A_1 otimes_A A' -->^(phi_(2,4)) A_1 otimes_A B' otimes_A A_1 otimes_A A_1 \
        &-->^(s_((2,3))) A_1 otimes_A A_1 otimes_A B' otimes_A A_1 -->^(phi_(3,4)^(-1)) A_1 otimes_A A_1 otimes_A B_1 otimes_A A'
      $
      We may cancel $phi_(2,4)^(-1)$ and $phi_(2,4)$, and then fuse $s_((2,3)) compose s_((1,2)) = s_((1,3))$. Then the composition becomes: 
      $
        B_1 otimes_A A_1 otimes_A A_1 otimes_A A' &-->^(phi_(1,4)) B' otimes_A A_1 otimes_A A_1 otimes_A A_1 -->^(s_((1,3))) A_1 otimes_A A_1 otimes_A B' otimes_A A_1 \
        &-->^(phi_(3,4)^(-1)) A_1 otimes_A A_1 otimes_A B_1 otimes_A A'
      $
      which is just $eta_(1,3,4)$. 

    Thus, by fpqc descent, there exists an $A$-module $B$ and an isomorphism $delta: B otimes_A A_1 cong B_1$. Furthermore, by descending the multiplication map on $B_1 otimes_(A_1) B_1 -> B_1$ to a map $B otimes_A B -> B$, we may equip $B$ with the structure of an $A$-algebra, making $delta$ a ring homomorphism. Now we have isomorphisms: 
    $
      B otimes_A A' otimes_A A_1 ->^(delta_(1,3)) B_1 otimes_A A' ->^phi B' otimes_A A_1 
    $
    Since $A -> A_1$ is faithfully flat, this gives an isomorphism $B otimes_A A' cong B'$, thus descending $B'$ to an $A$-algebra $B$. It remains to show that $B$ is an etale $A$-algebra. Indeed, $B otimes_A A_1 cong B_1$ is an etale $A_1$-algebra, and by faithfully flat descent of etaleness (@fpqc-descent-of-properties (5)), $B$ is an etale $A$-algebra. Taking $Y = Spec(B) in Et_X$, we have $Y' cong X' times_X Y$ and we are done. 
  ]

  Next, observe that: 

  - Suppose that $Spec(A') = X' -> X = Spec(A)$ is a finite universal homeomorphism in which $A$ is a strict henselian local ring. Then $A'$ is a finite $A$-algebra. By @finite-over-henselian-is-henselian, $A'$ is a direct product of strict henselian local $A$-algebras. However, since $Spec(A')$ is homeomorphic to $Spec(A)$, it only has one closed point. Thus $A'$ itself is local. It is thus strict henselian too. 

  We are now ready to perform the induction. 
  #lemma[
    Topological invariance holds for any finite universal homeomorphism $f: X' -> X$ between noetherian schemes of finite dimension. 
  ]
  #proof[
    Perform induction on $d = dim(X) = dim(X')$. Assume as the inductive hypothesis that topological invariance holds for any finite universal homeomorphism between noetherian schemes of dimension $<=d-1$. 

    By the same argument as in Step 1, to show that topological invariance holds for $f$, it suffices to show that it holds for $f_i: f^(-1) (X_i) -> X_i$ for every affine open $X_i subset X$. Now $dim(X_i) <= dim(X) = d$, so we may replace $f$ with $f_i$ and assume that $X', X$ are affine. Now by the previous lemma, it suffices to show that for any geometric point $ol(x)$ of $X$, topological invariance holds for $tilde(f)_(ol(x)): X' times_X tilde(X)_(ol(x)) -> tilde(X)_(ol(x))$. Note that $dim(tilde(X)_(ol(x))) = dim(cal(O)_(X,x)) <= dim(X) <= d$. 

    Thus, replacing $f$ with $tilde(f)_(ol(x))$, we may assume that $f: Spec(A') = X' -> X = Spec(A)$ is a finite universal homeomorphism in which $A$ is a strict henselian local ring with $dim(A) <= d$. As observed above, $A'$ is also a strict henselian local ring. Take $U = Spec(A) - frak(m)_A, U' = Spec(A') - frak(m)_(A')$ to be the punctured spectra, so $f_U: U' -> U$ is another universal homeomorphism. 
    
    Note that as a punctured spectrum, $dim(U) = dim(X) - 1 <= d - 1$. Hence, the inductive hypothesis gives topological invariance for $f_U$. 

    Now: 

    - For any etale $A$-algebra $B$, points of $Spec(B\/frak(m)_A B)$ correspond bijectively to sections $B -> A$. These sections $Spec(A) -> Spec(B)$ are closed immersions as sections of a separated morphism, and are open immersions as sections of an etale morphism. Thus, every $k(A)$-point of $Spec(B)$ corresponds to a connected component of $Spec(B)$ isomorphic to $Spec(A)$. Thus $B$ has a direct product decomposition: 
      $
        B = A^(Spec(B\/frak(m)_A B)) times B_1
      $ 
      where $B_1$ has image above $U$, thus $Spec(B_1) in Et_U$. 

      The same decomposition:
      $
        B' = A'^(Spec(B'\/frak(m)_(A')B')) times B'_1
      $
      exists for any etale $A'$-algebra $B'$. 

    - Now for $Spec(B), Spec(C) in Et_(Spec(A))^#[aff]$, decompose: 
      $
        B = A^(Spec(B\/frak(m)_A B)) times B_1, C = A^(Spec(C\/frak(m)_A C)) times C_1
      $
      for $Spec(B_1), Spec(C_1) in Et_U$. Then the base changes $B', C'$ decomposes as: 
      $
        B' = A'^(Spec(B'\/frak(m)_(A') B')) times B'_1, C' = A'^(Spec(C'\/frak(m)_(A') C')) times C'_1
      $
      where $Spec(B'_1), Spec(C'_1) in Et_(U')$ are base changes of $B_1, C_1$. 
      
      For a morphism $Spec(B) -> Spec(C)$, any $Spec(A)$-component in $Spec(B)$ must map isomorphically to a $Spec(A)$-component in $Spec(C)$. Meanwhile, $Spec(B_1)$ maps into the part of $Spec(C)$ above $U$, i.e. $union.sq.big_(Spec(C\/frak(m)_A C)) U union.sq Spec(C_1)$. Thus, 
      $
        Hom_X (Spec(B), Spec(C)) = Spec(C\/frak(m)_A C)^(Spec(B\/frak(m)_A B)) times Hom_U (Spec(B_1), union.sq.big_(Spec(C\/frak(m)_A C)) U union.sq Spec(C_1))
      $
      and similarly, 
      $
        Hom_(X') (Spec(B'), Spec(C')) = Spec(C\/frak(m)_A C)^(Spec(B\/frak(m)_A B)) times Hom_(U') (Spec(B'_1), union.sq.big_(Spec(C\/frak(m)_A C)) U' union.sq Spec(C'_1))
      $
      Now the base change map $Hom_X (Spec(B), Spec(C)) -> Hom_(X') (Spec(B'), Spec(C'))$ is the identity on the first factor $Spec(C\/frak(m)_A C)^(Spec(B\/frak(m)_A B))$, which is a finite set. It is the base change map on the second factor: 
      $
        Hom_U (Spec(B_1), union.sq.big_(Spec(C\/frak(m)_A C)) U union.sq Spec(C_1)) -> Hom_(U') (Spec(B'_1), union.sq.big_(Spec(C\/frak(m)_A C)) U' union.sq Spec(C'_1))
      $
      Thus, this component is also an isomorphism, by topological invariance for $f_U: U' -> U$. We have thus shown that $Et_X^#[aff] -> Et_(X')^#[aff]$ is fully faithful. 

    - For essential surjectivity, let $Y' = Spec(B') in Et_(X')^#[aff]$. We may decompose: 
      $
        B' = A'^r times B'_1
      $
      for some $Spec(B'_1) in Et_(U')$. By topological invariance for $U' -> U$, there exists $Y_1 in Et_U$ s.t. $Spec(B'_1) cong U' times_U Y_1$. Now take: 
      $
        Y = union.sq.big_(i=1)^r Spec(A) union.sq Y_1
      $
      and so we have $Y' cong X' times_X Y$. Now $Y' -> Y$ is finite surjective with $Y'$ affine, so $Y$ is affine by Chevalley's theorem. We have thus shown that $Et_X^#[aff] -> Et_(X')^#[aff]$ is essentially surjective. 

    By @top-invariance-et-to-et-aff, $Et_X -> Et_(X')$ is an equivalence, and we are done. 
  ]

  Recall from Step 3 that we only need to prove topological invariance for finite universal homeomorphisms between finite type $ZZ$-schemes. By the previous lemma, topological invariance does hold in this case, and so we are done. 
]

#corollary(name: <top-invariance-sheaves>)[
  Let $f: X' -> X$ be a universal homeomorphism between schemes. Then:
  
  0. The base change: 
    $
      f^(-1): Et_X -> Et_(X')
    $
    is an equivalence of categories. $cal(U) = {U_i -> U}$ is an etale cover in $Et_X$ if and only if $f^(-1)(cal(U))$ is an etale cover in $Et_(X')$. 
  
  1. For any $cal(F) in cAb(X_et)$, every $V in Et_(X')$ is $U times_X X'$ for some $U in Et_X$, and we have a canonical isomorphism: 
    $
      (f^(-1) cal(F))(V) = cal(F)(U)
    $
    The functors: 
    $
      f_*: cAb(X'_et, Lambda) arrows.rl cAb(X_et, Lambda): f^(-1)
    $
    are quasi-inverses to each other, and induce an equivalence of categories $cAb(X'_et, Lambda) cong cAb(X_et, Lambda)$. 

    As a derived category statement, the functors: 
    $
      f^(-1): D(X_et, Lambda) arrows.rl D(X'_et, Lambda): R f_*
    $
    are quasi-inverses to each other, and induce an equivalence of categories $D(X_et, Lambda) cong D(X'_et, Lambda)$. 

  2. There are canonical isomorphisms: 
    $
      H^q (U, f_* cal(F)) = H^q (U times_X X', cal(F)) \

      H^q (U, cal(G)) = H^q (U times_X X', f^(-1) cal(G))
    $
    for any $U in Et_X, cal(F) in cAb(X'_et), cal(G) in cAb(X_et)$. 

  3. Suppose that $X, X'$ are noetherian. The base change: 
    $
      f^(-1): FEt_X -> FEt_(X')
    $
    is also an equivalence of categories. 
    
    As a corollary, when $X, X'$ are also connected, for geometric points $ol(x) = f(ol(x'))$: 
    $
      f_*: pi_1^et (X', ol(x')) -> pi_1^et (X, ol(x))
    $
    is an isomorphism. 
]
#proof[
  (1) and (2) are obvious consequences of (0). For (0), that $f^(-1)$ is an equivalence of categories is already proved. That $cal(U)$ is jointly surjective if and only if $f^(-1)(cal(U))$ is, is a consequence of $f$ being a universal homeomorphism. 

  (3) Fully faithfulness follows from that of $Et_X -> Et_(X')$ directly, so it suffices to show essential surjectivity. If we can prove essential surjectivity whenever $X$ (and also $X'$) is affine, then we may glue the descended finite etale coverings of $X$ by fully faithfulness, and prove the general case. Thus we may assume that $X, X'$ are affine.

  Let $Y' in FEt_(X')$ come from base changing $Y in Et_X$. By @fet-trivializes-fet-locally, there exists a finite etale covering $U' -> X'$ s.t: 
  $
    Y' times_(X') U' cong union.sq.big_(i=1)^m U'
  $
  as $U'$-schemes. 
  
  Now by essential surjectivity let $U' -> X'$ come from base changing an etale cover $U -> X$. By fully faithfulness: 
  $
    Y times_X U cong union.sq.big_(i=1)^m U
  $
  Thus $Y times_X U -> U$ is finite. $U$ is quasi-compact since it is homeomorphic to the affine scheme $U'$. Thus $U -> X$ is fpqc, and by @fpqc-descent-of-properties (2), $Y -> X$ is finite. Thus $Y in FEt_X$. 
]
