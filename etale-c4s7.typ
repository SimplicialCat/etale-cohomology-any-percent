#import "void-import.typ": *
== Open and closed immersions <sect-open-closed>

// Recall that for $f: X -> Y$, we have an adjoint pair $cAb(X_et) overset(underset(arrows.lr, f_*), f^(-1)) cAb(Y_et)$, i.e. $f^(-1)$ is the left adjoint to $f_*$, whereas $f^(-1)cal(G)$ is the sheafification of $(U -> X) |-> dirlim cal(G)(V)$, where the limit is taken over all diagrams: // https://q.uiver.app/#r=typst&q=WzAsNCxbMCwwLCJVIl0sWzEsMCwiViJdLFswLDEsIlgiXSxbMSwxLCJZIl0sWzIsMywiZiJdLFswLDFdLFswLDJdLFsxLDNdXQ==
// #align(center, diagram({
//   node((0, -1), [$U$])
//   node((1, -1), [$V$])
//   node((0, 0), [$X$])
//   node((1, 0), [$Y$])
//   edge((0, 0), (1, 0), [$f$], label-side: left, "->")
//   edge((0, -1), (1, -1), "->")
//   edge((0, -1), (0, 0), "->")
//   edge((1, -1), (1, 0), "->")
// }))

// Note that if $f$ is etale, then $f^(-1)cal(G) (U) = cal(G)(U)$, since $id: U -> U$ is initial among diagrams of the shape above.

Let $i: Z arrow.r.hook X$ be a closed immersion, and $j: U = X - Z arrow.r.hook X$ be the complementary open immersion. We want to define $j_!$ left adjoint to $j^(-1)$, and $i^!$ right adjoint to $i_*$:
// https://q.uiver.app/#r=typst&q=WzAsMyxbMCwwLCJjQWIoVV9ldCkiXSxbMiwwLCJjQWIoWF9ldCkiXSxbNCwwLCJjQWIoWl9ldCkiXSxbMSwwLCJqXigtMSkiLDFdLFsyLDEsImlfKiIsMV0sWzAsMSwial8qIiwxLHsiY3VydmUiOjN9XSxbMiwxLCJpXiEiLDEseyJjdXJ2ZSI6LTMsInN0eWxlIjp7ImJvZHkiOnsibmFtZSI6ImRhc2hlZCJ9fX1dLFswLDEsImpfISIsMSx7ImN1cnZlIjotMywic3R5bGUiOnsiYm9keSI6eyJuYW1lIjoiZGFzaGVkIn19fV0sWzEsMiwiaV4oLTEpIiwxLHsiY3VydmUiOi0zfV1d
#context align(center, diagram(
  {
    node((-1, 0), [$cAb(U_et)$])
    node((1, 0), [$cAb(X_et)$])
    node((3, 0), [$cAb(Z_et)$])
    edge((1, 0), (-1, 0), [$j^(-1)$], label-side: center, "->")
    edge((3, 0), (1, 0), [$i_*$], label-side: center, "->")
    edge((-1, 0), (1, 0), [$j_*$], label-side: center, "->", bend: -54deg)
    edge((3, 0), (1, 0), [$i^!$], label-side: center, "-->", bend: 54deg)
    edge((-1, 0), (1, 0), [$j_!$], label-side: center, "-->", bend: 54deg)
    edge((1, 0), (3, 0), [$i^(-1)$], label-side: center, "->", bend: 54deg)
  },
  crossing-fill: thm-box-curr-color(),
))

// #remark[
//   A closed immersion $i$ is always finite, so:
//   $
//     (i_* cal(G))_(overline(x)) = cases(cal(G)_(overline(x)) &\, "if" overline(x) -> Z, 0 &\, "otherwise")
//   $
// ]

#construction(name: <etale-lower-shriek-defn>)[
  Let $f: U -> X$ be a etale morphism. For any $cal(H) in cAb(U_et)$, define $f_! cal(H)$ to be the sheafification of the presheaf: 
  $
    f_(cPSh,!) cal(H): Et_X^opp &-> cAb \
    V &|-> oplus.big_(psi in Hom_X (V, U)) cal(H)(psi: V -> U)
  $
  where the restriction is defined as follows: For $W ->^phi V$ a morphism in $Et_X$, we have a restriction: 
  $
    oplus.big_(psi in Hom_X (V,U)) cal(H)(psi) -> oplus.big_(chi in Hom_X (W,U)) cal(H)(chi)
  $
  sending a section in $cal(H)(psi)$ to a section in $cal(H)(psi compose phi)$ by restricting along $phi$. 
  // or simply as a kernel:
  // $
  //   ker(j_* cal(F) -> i_* i^(-1) j_* cal(F))
  // $
  // One may check that these two constructions are equivalent.
]

#properties(name: <etale-lower-shriek-first-props>)[
  0. If $j$ is an open immersion, $j^(-1) compose j_! = id$. #h(1fr)
  
  1. There is a natural isomorphism: 
    $
      Hom_(cAb(X_et)) (f_! cal(H), cal(F)) -> Hom_(cAb(U_et)) (cal(H), f^(-1)cal(F))
    $
    identifying $f_!$ as the left adjoint to $f^(-1)$. This map is simply functoriality of $f^(-1)$, if $f$ is an open immersion. 
    
    Furthermore, $f_!: cAb(U_et) -> cAb(X_et)$ is exact. 
  
  2. For a geometric point $ol(x)$ of $X$, there is a natural isomorphism: 
    $
      (f_! cal(H))_(ol(x)) = oplus.big_(ol(u) in f^(-1)(ol(x))) cal(H)_(ol(u))
    $
    (where the geometric fiber $U_(ol(x))$ is etale over $ol(x)$, hence a discrete set $f^(-1)(ol(x))$ of geometric points.)
  
  3. (Extension by zero sequence) Let $i: Z -> X$ be a closed immersion, and $j: U = X - i(Z) -> X$ be the complementary open immersion. For all $cal(F) in cAb(X_et)$, the sequence: 
    $
      0 -> j_! j^(-1) cal(F) -> cal(F) -> i_* i^(-1) cal(F) -> 0
    $
    is exact.

  4. (Base change) The formation of $f_!$ commutes with arbitrary base change. In other words, in a Cartesian square: 
    // https://q.uiver.app/#r=typst&q=WzAsNCxbMSwxLCJYIl0sWzAsMSwiVSJdLFswLDAsIlUnIl0sWzEsMCwiWCciXSxbMywwLCJnIl0sWzEsMCwiZiIsMl0sWzIsMywiZiciXSxbMiwxLCJnJyIsMl1d
    #align(center, diagram({
      node((0, 0), [$X$])
      node((-1, 0), [$U$])
      node((-1, -1), [$U'$])
      node((0, -1), [$X'$])
      edge((0, -1), (0, 0), [$g$], label-side: left, "->")
      edge((-1, 0), (0, 0), [$f$], label-side: right, "->")
      edge((-1, -1), (0, -1), [$f'$], label-side: left, "->")
      edge((-1, -1), (-1, 0), [$g'$], label-side: right, "->")
    }))
    We have natural isomorphisms: 
    $
      g^(-1) f_! cal(H) cong f'_! g'^(-1) cal(H), forall cal(H) in cAb(U_et)
    $
]
#proof[
  (1) It suffices to check that: 
  $
    Hom_(cPAb(X_et)) (f_(cPSh,!) cal(H), cal(F)) cong Hom_(cPAb(U_et)) (cal(H), f^(-1) cal(F))
  $
  However, one may check: 
  $
    & Hom_(cPAb(X_et)) (f_(cPSh,!) cal(H), cal(F)) \
    =& {#[morphisms $(phi_V: oplus.big_(psi in Hom_X (V,U)) cal(H)(psi) -> cal(F)(V))_(V in Et_X)$ compatible with restrictions]} \
    cong& {#[morphism $(phi_V: cal(H)(V) -> cal(F)(V))_(V in Et_U)$ compatible with restrictions]} \
    =& Hom_(cPAb(U_et)) (cal(H), f^(-1) cal(F))
  $
  where the third line is due to the universal properties of direct sums and by rearranging indices, and the fourth line is due to @pullback-along-etale-morphism. 

  As a left adjoint, $f_!$ is right exact. Since the sections of $f_(cPSh,!) cal(H)$ are just direct sums of sections of $cal(H)$, and injective morphisms on sheaves may be checked section-wise, $f_(cPSh,!)$ preserves injective morphisms. Thus the sheafification $f_!$ preserves injective morphisms. Since it is already right exact, it is exact. 
  
  (4) follows from Yoneda's lemma. For any $cal(F)' in cAb(X'_et)$, we have natural isomorphisms by adjunction:
  $
    Hom_(X') (g^(-1) f_! cal(H), cal(F)') cong Hom_X (f_! cal(H), g_* cal(F)') cong Hom_U (cal(H), f^(-1) g_* cal(F)')
  $
  and:
  $
    Hom_(X') (f'_! g'^(-1) cal(H), cal(F)') cong Hom_(U') (g'^(-1) cal(H), f'^(-1) cal(F)') cong Hom_U (cal(H), g'_* f'^(-1) cal(F)')
  $
  Thus, it suffices to prove that there is a natural isomorphism $f^(-1) g_* cal(F)' cong g'_* f'^(-1) cal(F)'$. Indeed, given $V in Et_U$, by @pullback-along-etale-morphism, the sections of both LHS and RHS on $V$ are naturally identified with $cal(F)'(V times_X X')$, and we are done. 

  (2) follows from (4). By base changing along the inclusion of a geometric point, we see that if we form the base change $f_(ol(x)): f^(-1) (ol(x)) -> ol(x)$, then: 
  $
    (f_! cal(H))_(ol(x)) = f_(ol(x),!) (cal(H)|_(f^(-1)(ol(x))))
  $
  However, $f^(-1) (ol(x))$ is a disjoint union $union.sq.big_(ol(u) in f^(-1)(ol(x))) ol(u)$, and so trivially: 
  $
    f_(ol(x),!) (cal(H)|_(f^(-1)(ol(x)))) = oplus.big_(ol(u) in f^(-1)(ol(x))) cal(H)_(ol(u))
  $
  /*(2) We try to apply Yoneda's lemma. For an abelian group $A in cAb$, 
  $
    Hom_cAb ((f_! cal(H))_(ol(x)), A) &= Hom_(cAb(X_et)) (f_! cal(H), ol(x)_* A) \
    &= Hom_(cAb(U_et)) (cal(H), f^(-1) ol(x)_* A)
  $
  #lemma[
    For $f: U -> X$ etale, there exists a canonical isomorphism: 
    $
      f^(-1) ol(x_*) A cong product_(ol(u) in f^(-1)(ol(x))) ol(u)_* A
    $
  ]
  #proof[
    This isomorphism can be directly constructed section-wise. Given $phi: V -> U$ in $Et_U$, 
    $
      f^(-1) ol(x)_* A (phi) = ol(x)_* A (f compose phi = product_(ol(v) in (f compose phi)^(-1) (ol(x))) A
    $
    while: 
    $
      (product_(ol(u) in f^(-1)(ol(x))) ol(u)_* A)(phi) = product_(ol(u) in f^(-1)(ol(x))) ol(u)_* A(phi) = product_(ol(u) in f^(-1)(ol(x))) product_(ol(v) in phi^(-1)(ol(u))) A
    $
    These two groups are obviously canonically isomorphic, since: 
    $
      (f compose phi)^(-1) (ol(x)) = union.sq.big_(ol(u) in f^(-1) (ol(x))) phi^(-1)(ol(u))
    $
  ]

    As such,
    $
      Hom_cAb ((f_! cal(H))_(ol(x)), A) & = Hom_(cAb(X_et)) (f_! cal(H), ol(x)_* A) \
      & = Hom_(cAb(U_et)) (cal(H), f^(-1) ol(x)_* A) \
      & = Hom_(cAb(U_et)) (cal(H), product_(ol(u) in f^(-1)(ol(x))) ol(u)_* A) \
      & = product_(ol(u) in f^(-1)(ol(x))) Hom_(cAb(U_et)) (cal(H), ol(u)_* A) \
      & = product_(ol(u) in f^(-1)(ol(x))) Hom_(cAb) (cal(H)_(ol(u)), A) \
      & = Hom_cAb (oplus.big_(ol(u) in f^(-1)(ol(x))) cal(H)_(ol(u)), A)
    $
    We are thereby done. */

  (0) follows from (2) as well. Indeed, the natural morphism: 
  $
    cal(H) -> j^(-1) j_! cal(H) 
  $
  given by adjunction is of type $cal(H)_(ol(u)) -> (j^(-1) j_! cal(H))_(ol(u)) = (j_! cal(H))_(ol(u)) = cal(H)_(ol(u))$ by (2), and is the identity map by unfolding definitions. It is thus an isomorphism.  

  (3) also follows from (2), once we establish a lemma about the stalks of $i_*$. 
  #lemma[
    Let $i: Z -> X$ be a closed immersion. Then for any geometric point $ol(x)$ of $X$ lying above $x$: 
    $
      (i_* cal(F))_(ol(x)) = cases(
        cal(F)_(ol(z)) &\, x in i(Z), 
        0 &\, x in.not i(Z)
      )
    $
    where since $i$ is a closed immersion, $k(z) = k(i(z))$, and so if $x = i(z)$, there exists a unique geometric point $ol(z)$ above $z$ s.t. $i(ol(z)) = ol(x)$.     
  ]
  #proof_[Proof placeholder][
    We will prove a generalization of this lemma in a later section, in @stalks-of-finite-pushforward, when we establish the relationship between stalks and strict henselizations. 
  ]
  // #proof[
  //   We prove the two cases separately. If $x in.not i(Z)$, 
  //   $
  //     (i_* cal(F))_(ol(x)) = dircolim_((U,ol(u)) -> (X,ol(x))) cal(F)(Z times_X U)
  //   $
  //   However, every etale neighborhood $phi: (U, ol(u)) -> (X, ol(x))$ can be refined by its Zariski open $phi^(-1) (X - i(Z))$, whose fiber product with $Z$ is empty. As such, the filtered colimit above has a cofinal subsystem in which the groups in the colimit are zero. As such, the colimit above is zero. 

  //   If $x = i(z)$ for some $z in Z$, so that $ol(x) = i(ol(z))$, we want to prove that there exists a canonical isomorphism: 
  //   $
  //     dircolim_((U,ol(u)) -> (X,ol(x))) cal(F)(U times_X Z) cong dircolim_((V,ol(v)) -> (Z,ol(z))) cal(F)(V)
  //   $
  //   Note that every $U times_X Z$ is an etale neighborhood of $Z$, so there is a natural morphism $dircolim_((U,ol(u)) -> (X,ol(x))) cal(F)(U times_X Z) -> dircolim_((V,ol(v)) -> (Z,ol(z))) cal(F)(V)$. To show that it is an isomorphism, we thus only have to show that there is a cofinal subsystem of etale neighborhoods of $(Z, ol(z))$ that can be written in the form $U times_X Z$ for etale neighborhoods $U$ of $(X, ol(x))$. 

  //   For this, recall the local structure of etale morphisms. We then see that every etale neighborhood of $(Z, ol(z))$ may be refined by one of the shape: 
  //   $
  //     Spec(((C[t])/((f(t))))_(g(t))) -> Spec(C) -> Z
  //   $
  //   where $f(t) in C[t]$ is monic s.t. $f'(t)$ is invertible in $(C[t]\/f(t))_(g(t))$, where $Spec(C)$ is an affine open of $Z$, coming from an affine open $Spec(B)$ of $X$ s.t. $C = B\/I$. 

  //   Now we arbitrarily lift monic $f(t) in C[t]$ to some $tilde(f)(t) in B[t]$, and $g(t) in C[t]$ to some $tilde(g)[t] in B[t]$. We claim that $tilde(f)'(t)$ is invertible in $(B[t]\/tilde(f)(t))_(tilde(g)(t))$. Indeed, if we take the quotient of the ring by the ideal $I[t]$ generated by $I$, we obtain the element $f'(t) in (C[t]\/f(t))_(g(t))$, which is invertible. 
  // ]
  The result then follows from (2) by taking stalks. Indeed, for a geometric point $ol(x)$ of $X$: 

  - If $x in U$, the sequence on stalks is: #h(1fr)
    $
      0 -> cal(F)_(ol(x)) -> cal(F)_(ol(x)) -> 0 -> 0
    $

  - If $x in Z$, the sequence on stalks is: 
    $
      0 -> 0 -> cal(F)_(ol(x)) -> cal(F)_(ol(x)) -> 0
    $

  Both of these sequences are exact. 
]

#example[
  The sheaf $ul(ZZ)_(!,V)$ defined in @detection-and-const-sheaf, satisfying $Hom_cAb (ul(ZZ)_(!,V), cal(F)) = cal(F)(V)$ is simply $i_(V,!) ul(ZZ)_V$ where $i_V: V -> X$ is the structure map, which can be checked either by Yoneda or by checking definitions directly.#footnote[Hence the notation $ul(ZZ)_(!,V)$. I need to distinguish this sheaf between the constant sheaf $ul(ZZ)_V in cAb(V_et)$, so I added a shriek in the subscript, since this sheaf is just $i_(V,!) ul(ZZ)_V$.]
]

Furthermore, for a separated etale morphism $f$, we may identify $f_! cal(H)$ with a subsheaf of $f_* cal(H)$: 

#proposition(name: <sep-etale-lower-shriek-alt-desc>)[
  Given a quasi-compact separated etale morphism $f: U -> X$, there is a canonical injection: 
  $
    f_! cal(H) -> f_* cal(H)
  $
  identifying $f_! cal(H)$ with the following subsheaf of $f_* cal(H)$: For $V_X in Et_X$ form $V_U = U times_X V_X in Et_U$, and: 
  $
    f_! cal(H)(V_X) = {s in cal(H)(V_U) : supp(s) -> V_U -> V_X #[is proper]} subset cal(H)(V_U) = f_* cal(H)(V_X)
  $
  Here, $supp(s)$ is equipped with the reduced subscheme structure but any closed subscheme structure makes no difference, and the word "proper" may be replaced by "finite". This inclusion is compatible with composition of etale maps. 
]
#proof[
  We directly define the map $f_! cal(H) -> f_* cal(H)$. Let $(g: V_X -> X) in Et_X$ form $V_U = U times_X V_X in Et_U$, we define a map: 
  $
    f_(cPSh,!) cal(H) (V_X) = oplus.big_(psi in Hom_X (V_X,U)) cal(H) (V_(X,psi)) -> f_* cal(H)(V_X) = cal(H)(V_U)
  $
  Here, $V_(X,psi)$ is just $V_X$ but considered as an etale $U$-scheme under $psi$. Consider $V_X ->^psi U ->^f X$ which composes to the structure map $g$. We now form its graph: 
  $
    Gamma_psi: V_(X,psi) -> V_X times_X U = V_U
  $
  which is a $U$-morphism, where $V_(X,psi)$ is a $U$-scheme by $psi$, and $V_X times_X U$ is a $U$-scheme by the second projection. 

  Note that $Gamma_psi$ is a base change of the diagonal $U -> U times_X U$. Since $f: U -> X$ is separated etale, this diagonal is an open and closed immersion. Thus, $Gamma_psi$ is an open and closed immersion, and so as etale $U$-schemes, $V_U$ has a decomposition $V_U = Gamma_psi (V_(X,psi)) union.sq W_psi$. We now define a map $cal(H)(V_(X,psi)) -> cal(H)(V_U)$, sending a section $s in cal(H)(V_(X,psi))$ to the section $t in cal(H)(V_U)$ s.t. $t|_(V_(X,psi)) = s$ and $t|_(W_psi) = 0$. We then pass from the map for individual $psi$ to the direct sum. 

  It is routine to verify that this construction is compatible with restriction, hence a morphism of presheaves. Furthermore, it is injective. Upon sheafification, we now have a morphism of sheaves: 
  $
    f_! cal(H) -> f_* cal(H)
  $
  To verify that this morphism is injective, we need to show that for any $s in f_(cPSh,!) cal(H) (V_X)$ sent to zero, $s$ is etale locally zero. By definition of $f_(cPSh,!)$, we may write $s = sum_i [psi_i, s_i]$ a finite sum, for some $psi_i in Hom_X (V_X, U)$ and $s_i in cal(H)(V_(X,psi_i))$. 

  For two $psi_i, psi_j$, we may form the equalizer: 
  $
    V_(i,j) = {v in V_X : psi_i (v) = psi_j (v)}
  $
  of $psi_i$ and $psi_j$. This equalizer is the inverse image of the diagonal under $(psi_i, psi_j): V_X -> U times_X U$. Since the diagonal in $U times_X U$ is both open and closed, $V_(i,j) subset V_X$ is an open and closed subset. 

  Now by partitioning $V_X$ into finitely many open and closed subsets according to ${V_(i,j)}$, we may assume that on each piece, $psi_i, psi_j$ are either equal or have disjoint image. Thus replacing $V_X$ with these open and closed pieces and merging sections corresponding to the same element of $Hom_X (V_X,U)$, we may assume that the $psi_i$'s all have disjoint image. Then the $Gamma_(psi_i) (V_(X,psi_i))$'s as constructed above are all disjoint, so the vanishing of the image of $s$ gives $s_i = 0$ for all $i$. We have thereby proved injectivity. 

  Next, we want to characterize the image of $iota: f_! cal(H) -> f_* cal(H)$. We claim that: 
  $
    f_! cal(H)(V_X) = {s in cal(H)(V_U) : supp(s) -> V_U -> V_X #[is proper]} subset cal(H)(V_U) = f_* cal(H)(V_X)
  $
  /*The choice of the closed subscheme structure on $supp(s)$ here is irrelevant. Indeed, $f$ being a quasi-compact separated etale morphism is separated of finite type. Now $supp(s) -> V_U$ is a closed immersion and $V_U -> V_X$ is separated of finite type. Thus, $supp(s) -> V_X$ is automatically separated of finite type, so we may replace "proper" in the condition above by "universally closed". Now any closed subscheme structure on $supp(s)$ differs from the reduced one by a nilpotent thickening, which is a universal homeomorphism, which does not affect universal closedness. */Note that $supp(s) -> V_U$ is a closed immersion. Since $U -> X$ is quasi-compact etale, so is $V_U -> V_X$. Thus, $V_U -> V_X$ has finite fibers. Thus, $supp(s) -> V_U$ always have finite fibers. By #cite-stacks("02LS")[Lemma 37.44.1], a morphism of schemes is finite if and only if it is proper and has finite fibers. Thus, the word "proper" in the condition may be replaced with "finite". This condition is also independent from the closed subscheme structure on $supp(s)$, since finiteness is not affected by a nilpotent thickening. 

  Furthermore, the proposed condition is local in $V_X$. Indeed, suppose that $phi_X: W_X -> V_X$ is etale and base change to $phi_U: W_U -> V_U$. Then for $s in cal(H)(V_U)$: 
  $
    (s|_(W_U))_(ol(w)) = s_(phi_U (ol(w)))
  $
  and hence as sets, $supp(s|_(W_U)) = phi_U^(-1)(supp(s))$. Equip $supp(s)$ with the reduced subscheme structure, and then $supp(s|_(W_U))$ is the underlying subset of $supp(s) times_(V_U) W_U = supp(s) times_(V_X) W_X$. Thus: 

  - The property that $supp(s) -> V_X$ is finite passes to etale covers, since finiteness is preserved under base change. 

  - The property that $supp(s) -> V_X$ is finite descends from etale covers. Indeed, finiteness may be checked Zariski locally, allowing us to replace $V_X$ by an affine open. Then we may refine the given etale cover by a cover consisting of finitely many affine schemes, and finally notice that finiteness is preserved under fpqc descent by @fpqc-descent-of-properties (2). 

  Furthermore, $supp(s+t) subset supp(s) union supp(t)$ is a closed subset. Suppose that $supp(s) -> V_X, supp(t) -> V_X$ is proper. Then the composition: 
  $
    supp(s) union.sq supp(t) -> supp(s) union supp(t) -> V_X
  $
  is proper, where the first arrow is surjective finite. $supp(s) union supp(t) -> V_X$ is naturally separated of finite type, being the composition of a closed immersion and a quasi-compact separated etale morphism. Thus, we only need to prove that it is universally closed. This follows from the lemma below: 
  #lemma[
    Given morphism of schemes $X ->^q X' ->^(f') Y$ in which $q$ is surjective and the composition $f = f' compose q$ is universally closed, $f'$ is universally closed. 
  ]
  #proof[
    Note that base changing the composition preserves the property that $q$ is surjective and $f$ is universally closed. Thus, it suffices to show that $f'$ is closed. Given $C subset X'$ closed, $q^(-1) (C)$ is closed. Then since $f$ is closed, $f(q^(-1)(C))$ is closed, i.e. $f'(q(q^(-1)(C)))$ is closed. However $q$ is surjective and so $q(q^(-1) (C)) = C$. Hence $f'(C)$ is closed. 
  ]

  We have thus shown that: 
  $
    {s in cal(H)(V_U) : supp(s) -> V_U -> V_X #[is finite]} subset cal(H)(V_U) = f_* cal(H)(V_X)
  $  
  indeed defines a subsheaf $cal(P)$ of $f_* cal(H)$. 

  - The image of $f_! cal(H)$ is contained in $cal(P)$. Indeed, since $cal(P)$ is a subsheaf, it suffices to show that the image of any section in $f_(cPSh,!) cal(H)$ is in $cal(P)$. 

    Given a section $s in f_(cPSh,!) cal(H) (V_X)$, we may write $s = sum_i [psi_i, s_i]$ as a finite sum, where $psi_i in Hom_X (V_X,U), s in cal(H)(V_(X,psi_i))$. Thus it suffices to show that for a fixed $psi in Hom_X (V_X, U)$ and $s in cal(H)(V_(X,psi))$, $iota(s) in cal(P)$. Indeed, $iota(s) in f_* cal(H)(V_X) = cal(H)(V_U)$ is supported on $Gamma_psi (V_(X,psi)) subset V_U$ as a section of $cal(H)$. That is, $supp(iota(s)) subset Gamma_psi (V_(X,psi))$ is a closed subset. But $Gamma_psi (V_(X,psi)) -> V_U -> V_X$ is an isomorphism (and is just the identity on $V_X$ in disguise), and so it is finite. Thus $supp(iota(s)) -> V_X$ is finite and $iota(s) in cal(P)$. 

  - $cal(P)$ is contained in the image of $f_! cal(H)$. 

    Suppose that $s in cal(P)(V_X) subset cal(H)(V_U)$ s.t. $supp(s) -> V_U -> V_X$ is finite. We need to show that for any $ol(v) in V_X$ there is an etale neighborhood $W_X -> V_X$ of $ol(v)$ s.t. $s|_(W_X)$ is the image of an element of $f_(cPSh,!) cal(H)$. 

    Since $supp(s) -> V_X$ is finite, the geometric fiber $ol(v)$ under $f_V: V_U -> V_X$ has only finitely many points in the image of $supp(s)$. Let these geometric points be ${ol(v)_1, dots.c, ol(v)_r}$. 

    Take $W_X = V_U times_(V_X) dots.c times_(V_X) V_U$ to be an $r$-fold fiber product, which is etale over $V_X$ with a geometric point $ol(w) = (ol(v)_1, dots.c, ol(v)_r)$ above $ol(v)$. Form $W_U = W_X times_X U = W_X times_(V_X) V_U$. Then in $supp(s|_(W_U)) -> W_U -> W_X$, $ol(w)$ has $r$ geometric points lying above it in $W_U$ that is in the image of $supp(s|_(W_U))$, namely $ol(w)_i = (ol(w), ol(v)_i) in W_U$ under the identifcation $W_U = W_X times_(V_X) V_U$.  
    
    The graph of the $i$-th projection $W_X -> V_U$ defines a map $W_X -> W_X times_(V_X) V_U = W_X times_X U = W_U$, which is a section of $W_U -> W_X$ sending $ol(w) -> ol(w)_i$. Thus, upon base changing from $(V_X, ol(v))$ to $(W_X, ol(w))$, we may assume that: 

    - There are sections $psi_i: V_X -> V_U$ s.t. for each $1<=i<=r$ we have $psi_i (ol(v)) = ol(v)_i$. 

    We may form the equalizer of $psi_i, psi_j$ for $i!=j$. Let $E_(i,j)$ be the pullback of the diagonal under $(psi_i, psi_j): V_X -> V_U times_(V_X) V_U$. Since $V_U -> V_X$ is separated etale, this diagonal is open and closed. Hence, each $E_(i,j)$ is open and closed in $V_X$. Furthermore, $ol(v)$ is not a geometric point of $E_(i,j), i!=j$ since $ol(v)_i != ol(v)_j$. Therefore, as a Zariski open, $E_(i,j) subset V_X$ does not contain $v$. Thus, by removing all $E_(i,j)$ from $V_X$, there exists an open and closed subscheme $W_X subset V_X$ around $v$ s.t. $psi_i|_(W_X)$ have disjoint images. 

    Base changing along $(W_X, ol(v)) -> (V_X, ol(v))$, we may assume that all $psi_i$ have disjoint images. 

    Next, put $S = union.sq.big_(i=1)^r psi_i (V_X) subset V_U$. Each $psi_i$ as a section of the separated etale morphism $V_U -> V_X$ is an open and closed immersion. Thus $S$ is an open and closed subset of $V_U$. Put $C = V_U - S$ which is another open and closed subset of $V_U$ which does not contain any point above $v in V_X$. Since $supp(s) -> V_X$ is finite, the image of $supp(s) inter C$ in $V_X$ is a closed subset not containing $v$. Take its complement $v in W_X subset V_X$, a Zariski open. Then $union.sq.big_(i=1)^r psi_i (W_X) supset supp(s|_(W_U))$. 

    Base changing along $(W_X, ol(v)) -> (V_X, ol(v))$, we may assume that $supp(s) subset union.sq.big_(i=1)^r psi_i (V_X)$. Put $phi_i = p_2 compose psi_i: V_X -> V_U -> U$ an etale $X$-morphism. Then $s$ is in the image of: 
    $
      oplus.big_(i=1)^r cal(H) (V_(X,phi_i)) -> cal(H) (V_U)
    $
    since each $Gamma_(phi_i) = psi_i$ and so we may find the correct element in $cal(H)(V_(X,phi_i))$ according to $s|_(psi_i (V_X))$. 
  
  We are thereby done. 
]

#corollary(name: <fet-lower-star-is-lower-shriek>)[
  For finite etale $f: X -> Y$, there is a canonical isomorphism $f_! cal(F) -> f_* cal(F)$ for all $cal(F) in cAb(X_et)$. 
]
#proof[
  The inclusion $f_! cal(F) -> f_* cal(F)$ constructed above identifies: 
  $
    f_! cal(F)(V) = {s in cal(F)(X times_Y V) : supp(s) -> X times_Y V -> V #[is proper]} subset cal(F)(X times_Y V) = f_* cal(F)(V)
  $
  However, $supp(s) -> X times_Y V$ is a closed immersion, and $X times_Y V -> V$ is finite since $X -> Y$ is finite. Thus $supp(s) -> V$ is automatically finite, so $f_! cal(F)(V) = f_* cal(F)(V)$
]

Next, given a pair $i: Z -> X$ and $j: X - i(Z) -> X$ of complementary closed and open immersions, we want to define $i^!$. 
#lemma(name: <pushforward-by-closed-immersion>)[
  + $i^(-1) compose i_* = id$, and $i_*$ is a fully faithful functor. 

  + $cal(F) = i_* cal(G)$ for some $cal(G) in cAb(Z_et)$ if and only if $j^(-1) cal(F) = 0$.
]
#proof[
  (1) That $i^(-1) compose i_* = id$ follows from the previous description of the stalks of $i_* cal(F)$. Full faithfulness of $i_*$ then follows from adjunction: 
  $
    Hom_(cAb(X_et)) (i_* cal(F), i_* cal(G)) = Hom_(cAb(Z_et)) (i^(-1)i_* cal(F), cal(G)) = Hom_(cAb(Z_et)) (cal(F), cal(G))
  $
  
  (2)($==>$)
  $
    (j^(-1) i_* cal(G)) (V -> U) = i_* cal(G) (V -> U) = cal(G) (V times_X Z) = cal(G)(emptyset) = 0
  $
  
  ($<==$) We have a canonical map $cal(F) -> i_* i^(-1) cal(F)$. It is already an isomorphism on stalks on geometric points above $Z$. If $j^(-1)cal(F) = 0$, $cal(F)$ has zero stalks on geometric points above $U$, and that this map is an isomorphism can be checked by taking stalks. Thus taking $cal(G) = i^(-1) cal(F)$ works. 
]

#construction(name: <closed-immersion-upper-shriek-constr>)[
  We construct $i^!$ as follows. Let $cal(F)' = ker(cal(F) -> j_* j^(-1) cal(F))$. Then by exactness of $j^(-1)$:
  $
    j^(-1) cal(F)' = ker(j^(-1) cal(F) overset(->, id) underbrace(j^(-1)j_*, id) j^(-1) cal(F)) = 0
  $
  so by the previous lemma, there exists a unique $i^! cal(F) in cAb(Z_et)$ s.t. $cal(F)' = i_* i^! cal(F)$. More explicitly:
  $
    i^! cal(F) = i^(-1) ker(cal(F) -> j_* j^(-1) cal(F))
  $
]

#properties(name: <closed-immersion-upper-shriek-first-props>)[
  0. (Sections with support sequence) There is a left exact sequence: #h(1fr)
    $
      0 -> i_* i^! cal(F) -> cal(F) -> j_* j^(-1) cal(F)
    $
  
  1. There is an isomorphism:
    $
      Hom_(cAb(X_et)) (i_* cal(G), cal(F)) overset(->, tilde) Hom_(cAb(Z_et)) (cal(G), i^! cal(F))
    $
    identifying $i^!$ as the right adjoint of $i_*$. 
]
#proof[
  (0) By definition, 
  $
    i_* i^! cal(F) = ker(cal(F) -> j_* j^(-1) cal(F))
  $
  so this exact sequence is immediate. 

  (1) Given any morphism $phi: i_* cal(G) -> cal(F)$, we may compose it with the map $cal(F) -> j_* j^(-1) cal(F)$. Consider the composition: 
  $
    i_* cal(G) ->^phi cal(F) -> j_* j^(-1) cal(F)
  $
  By adjunction, maps $i_* cal(G) -> j_* j^(-1) cal(F)$ are in bijective correspondence with maps $j^(-1) i_* cal(G) -> j^(-1) cal(F)$. But $j^(-1) compose i_* = 0$, so such a map can only be zero. In other words, $i_* cal(G) ->^phi cal(F) -> j_* j^(-1) cal(F)$ is always zero, so $phi$ factors uniquely as: 
  $
    i_* cal(G) -> ker(cal(F) -> j_* j^(-1) cal(F))
  $
  Since $i^(-1)$ is fully faithful and $i^(-1) compose i_* = id$, such a map corresponds uniquely to a map: 
  $
    cal(G) = i^(-1) i_* cal(G) -> i^(-1) ker(cal(F) -> j_* j^(-1) cal(F)) = i^! cal(F)
  $
  and we are thereby done. 
]

Finally, as an application, we prove a lemma about etale cohomology of $f^(-1) cal(G)$ if $f: U -> X$ is etale. 

#corollary(name: <pullback-along-etale-morphism-derived>)[
  Let $f: U -> X$ be a etale morphism. Then for $cal(F) in cAb(X_et)$ and any $V in Et_U$, there exists a canonical isomorphism: 
  $
    H^q (V, cal(F)) cong H^q (V, f^(-1) cal(F))
  $
  where $V$ is regarded as an object of $Et_X$ by $V -> U ->^f X$. 
]
#proof[
  The case $q = 0$ is already done by @pullback-along-etale-morphism. 

  To obtain the higher degree isomorphisms, we take an injective resolution: $0 -> cal(F) -> cal(I)^bullet$. Since $f^(-1)$ has the exact left adjoint $f_!$, $0 -> f^(-1) cal(F) -> f^(-1) cal(I)^bullet$ is an injective resolution of $f^(-1) cal(F)$. Taking sections on $V$, then cohomology on both resolutions, then using the result on sections concludes the proof. 
]
