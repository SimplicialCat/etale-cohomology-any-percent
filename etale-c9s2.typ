#import "void-import.typ": *

== Poincare duality

In this section, we prove Poincare duality for etale cohomology, and also prove purity theorems as an application. But first, we need to devise a correct and most general statement for it.

#definition(name: <defn-cup-product-pairing>)[
  Let $X$ be smooth of dimension $d$ over an algebraically closed field $k$, and $Lambda$ be an $n$-torsion noetherian ring s.t. $n in k^times$. For a complex $cal(K) in D(X_et, Lambda)$,
  $
    h^(2d-q) (RHom_Lambda (cal(K), ul(Lambda)(d))) = Hom_(D(X_et,Lambda)) (cal(K)[q], mu_n^(otimes d) [2d])
  $
  Thus every element of $h^(2d-q)(RHom_Lambda (cal(K), Lambda(d)))$ induces a morphism:
  $
    R Gamma_c (X, cal(K))[q] -> R Gamma_c (X, ul(Lambda))(d)[2d] -->^(Tr_(X\/k)) Lambda
  $
  as complexes, and hence $h^q (R Gamma_c (X, cal(K))) -> Lambda$ as abelian groups. We thus have a $Lambda$-bilinear pairing:
  $
    smile: h^q (R Gamma_c (X, cal(K))) times h^(2d-q) (RHom_Lambda (cal(K), ul(Lambda)(d))) -> Lambda
  $
  called the *cup product pairing*. In particular, for a sheaf $cal(F) in cAb(X_et, Lambda)$, we have a *cup product pairing*:
  $
    smile: H^q_c (X, cal(F)) times Ext^(2d-q)_Lambda (cal(F), ul(Lambda)(d)) -> Lambda
  $
]

In particular, when $cal(F)$ is a l.c.c. sheaf of $Lambda$-modules, we will see that $EExt^p (cal(F), Lambda(d)) = 0$ for $p>0$ and so by the Hochschild-Serre spectral sequence, $Ext^(2d-q)_Lambda (cal(F), Lambda(d)) = H^(2d-q) (X, caron(cal(F))(d))$ where $caron(cal(F)) = HHom_Lambda (cal(F), Lambda)$. We will then have the classical Poincare duality, that:
$
  smile: H^q_c (X, cal(F)) times H^(2d-q) (X, caron(cal(F))(d)) -> Lambda
$
is a perfect pairing.

#construction(name: <constr-pd-relative-to-absolute>)[
  Let $k$ be an algebraically closed field and $Lambda$ be an $n$-torsion noetherian ring s.t. $n in k^times$ and $Lambda$ is an injective $Lambda$-module. 

  Let $X$ be a smooth $k$-scheme of dimension $d$, and $g: X -> Spec(k)$ be the structure map. We then aim to prove that:
  $
    h^(2d-q) (RHom_Lambda (cal(K), ul(Lambda)(d))) -> Hom_Lambda (h^q (R Gamma_c (X, cal(K))), Lambda)
  $
  is an isomorphism. Now:
  $
    h^(2d-q) (RHom_Lambda (cal(K), ul(Lambda)(d))) = Hom_Lambda (cal(K)[q], ul(Lambda)(d)[2d])
  $
  Meanwhile:
  $
    Hom_Lambda (R g_! cal(K)[q], ul(Lambda)) &= Hom_Lambda (R Gamma_c (X, cal(K))[q], Lambda) \
    &= Hom_Lambda (h^q (R Gamma_c (X, cal(K))), Lambda) #[since $Lambda$ is an injective $Lambda$-module]
  $
  Therefore, what we are really trying to prove is that the map:
  $
    Hom_Lambda (R g_! cal(K), ul(Lambda)) cong Hom_Lambda (cal(K), ul(Lambda)(d)[2d])
  $
  induced by the trace:
  $
    Hom_Lambda (R g_! cal(K), ul(Lambda)) -->^(Tr_(X\/k)) Hom_Lambda (cal(K)(-d)[-2d], ul(Lambda)) = Hom_Lambda (cal(K), ul(Lambda)(d)[2d])
  $
  is an isomorphism.

  The shape of this isomorphism strongly hints the existence of a right adjoint $R g^!: D(Spec(k)_et, Lambda) -> D(X_et, Lambda)$ of $R g_!$, and an identification:
  $
    R g^! ul(Lambda) cong ul(Lambda)(d)[2d]
  $
  induced from adjunction by the trace map.
]

The construction above gives a hint on what the correct most general statement of Poincare duality in a relative setting should look like:

- #h(1fr)
  $
    R f^! cal(K) cong f^(-1) cal(K)(d)[2d]
  $
  for any $f: X -> Y$ smooth of relative dimension $d$ between noetherian schemes, where $R f^!$ is some right adjoint of $R f_!$.

We are now motivated to find a right adjoint $R f^!$ to $R f_!$ for any $f: X -> Y$ separated of finite type between noetherian schemes. The core engine of the construction of $R f^!$ is the Brown representability theorem @brown-representability.

#theorem(name: <existence-of-upper-shriek>)[
  Let $Lambda$ be any torsion ring.

  For any separated morphism of finite type $f: X -> Y$ between noetherian schemes, $R f_!: D(X_et, Lambda) -> D(Y_et, Lambda)$ has a triangulated right adjoint $R f^!$. There are canonical natural isomorphisms: 

  0. For separated etale $f: X -> Y$,
    $
      R f^! cong f^(-1)
    $
    For a closed immersion $i: Z -> X$, $R i^!$ is naturally isomorphic to the derived functor of the functor $i^!$ defined in @closed-immersion-upper-shriek-constr.

  + (Composition) #h(1fr)
    $
      R f^! compose R g^! cong R(g compose f)^!
    $

  + (Adjoint to proper base change) In a Cartesian diagram:
    #align(center, diagram({
      node((0, 0), [$X'$])
      node((1, 0), [$Y'$])
      node((0, 1), [$X$])
      node((1, 1), [$Y$])
      node((0.3, 0.3), [$cart$])
      edge((0, 1), (1, 1), [$f$], label-side: right, "->")
      edge((0, 0), (1, 0), [$f'$], label-side: left, "->")
      edge((1, 0), (1, 1), [$g$], label-side: left, "->")
      edge((0, 0), (0, 1), [$g'$], label-side: right, "->")
    }))
    We have:
    $
      R f^! compose R g_* cong R g'_* compose R f'^!
    $

  + (Adjoint to projection formula) For any $cal(L) in D(Y_et, Lambda)$:
    $
      R f^! RHHom_Lambda (cal(L), -) cong RHHom_Lambda (f^(-1) cal(L), R f^! (-))
    $

  + (Internal adjunction) For any $cal(K) in D(X_et, Lambda), cal(L) in D(Y_et, Lambda)$: 
    $
      RHHom_Lambda (R f_! cal(K), cal(L)) cong R f_* RHHom_Lambda (cal(K), R f^! cal(L))
    $
]
#proof[
  Suppose that we have shown that $R f^!$ exists. (1)(2)(3) are adjoint to composition of $R f_!$, proper base change and projection formula respectively. (0) comes from the sheaf-level adjunctions:
  $
    f^(-1) tack.l f_* \
    i^! tack.l i_*
  $
  For (4), we prove it the same way as in @derived-functoriality-etale (3), by applying $R Gamma$ and taking cohomology of complexes to reduce to the categorical $Hom$.  


  Thus it suffices to show that the right adjoint $R f^!$ exists.

  For this, we use the Brown representability theorem @brown-representability and see that the right adjoint $R f^!$ exists whenever $R f_!$ preserves arbitrary direct sums. We thus aim to show that $R f_!$ preserves arbitrary direct sums. Let $f$ have fiber dimensions $<=d$, and so $R f_!$ has cohomological dimension above $<=2d$. Take an arbitrary family of complexes $cal(K)_i in D(X_et, Lambda)$. For fixed $q$, we need to show that:
  $
    h^q (R f_! (oplus.big_i cal(K)_i)) cong oplus.big_i h^q (R f_! cal(K)_i)
  $
  Take the truncations:
  $
    tau_(<=q-2d-1) cal(K)_i -> cal(K)_i -> tau_(>=q-2d) cal(K)_i ->^(+1)
  $
  which makes a distinguished triangle $oplus.big_i tau_(<=q-2d-1) cal(K)_i -> oplus.big_i cal(K)_i -> oplus.big_i tau_(>=q-2d) cal(K)_i ->^(+1)$. Now:

  - Since $R f_!$ has cohomological dimension above $<=2d$, for any complex $cal(L) in D_(<=q-2d-1)$, $R f_! cal(L) in D_(<=q-1)$ and has vanishing $h^q, h^(q+1)$.

  Thus, we have isomorphisms:
  $
    h^q (R f_! (oplus.big_i cal(K)_i)) cong h^q (R f_! (oplus.big_i tau_(>=q-2d) cal(K)_i)) \
    h^q (R f_! cal(K)_i) cong h^q (R f_! (tau_(>=q-2d) cal(K)_i))
  $
  Thus replacing $cal(K)_i$ with $tau_(>=q-2d)$, we may assume that there exists a fixed $a in ZZ$ s.t. every $cal(K)_i in D_(>=a) (X_et, Lambda)$. Similarly, since $R f_!$ has cohomological dimension below $0$, we may perform upper truncations and assume that there are fixed $a, b in ZZ$ s.t. every $cal(K)_i in D_([a,b]) (X_et, Lambda)$. Next, for $cal(L) in D_([a,b]) (X_et, Lambda)$ we have truncations:
  $
    tau_(<=a) cal(L) -> cal(L) -> tau_(>=a+1) cal(L) ->^(+1)
  $
  where $tau_(>=a+1) cal(L) in D_([a+1,b]) (X_et,Lambda)$ and $tau_(<=a) cal(L)$ is concentrated in degree $a$. Thus by induction on $b-a$ and the five lemma, we may assume that all $cal(K)_i$ are supported on the same single degree $a in ZZ$, i.e. are sheaves $cal(F)_i in cAb(X_et, Lambda)$. Thus we only need to prove that:
  $
    R^q f_! (oplus.big_i cal(F)_i) cong oplus.big_i R^q f_! cal(F)_i
  $
  Pick a compactification $X ->^j ol(X) ->^(ol(f)) Y$ of $f$ so that $R^q f_! cong R^q ol(f)_* j_!$. Now $j_!$ preserves direct sums as a left adjoint, and $R ol(f)_*$ preserves direct sums by the limit formula @relative-limit-formula-for-sheaves. We are thereby done.
]

#construction(name: <purity-map>)[
  Let $Lambda$ be an $n$-torsion noetherian ring. Let $f: X -> Y$ be separated smooth of relative dimension $d$ between noetherian $ZZ[n^(-1)]$-schemes. Then the trace map:
  $
    Tr_(X\/Y): R f_! f^(-1) cal(K)(d)[2d] -> cal(K)
  $
  induces by adjunction a map:
  $
    t_(X\/Y): f^(-1) cal(K)(d)[2d] -> R f^! cal(K)
  $
  for all $cal(K) in D(Y_et, Lambda)$, which we call the *purity map*. The purity map is compatible with compositions, since the trace map is.
]

We now state the general strategy for proving Poincare duality. We are going to fully exploit compatibility with composition of the purity map. For any smooth morphism $f: X -> Y$, we'll see that to show that $t_(X\/Y)$ is an isomorphism, it suffices to work etale locally on $X$. Thus we may assume that $f$ factors as $f: X -> AA^d_Y ->^p Y$ with $X -> AA^d_Y$ etale. The purity map for an etale morphism is the identity, so it suffices to show that the purity map:
$
  t_(AA^d_Y\/Y): p^(-1) cal(K)(d)[2d] -> R p^! cal(K)
$
is an isomorphism. By factoring $AA^d_Y -> Y$ further as:
$
  AA^d_Y -> AA^(d-1)_Y -> dots.c -> AA^1_Y -> Y
$
we may assume $d = 1$ and only deal with the case of $p: AA^1_Y -> Y$. Thus, the core of Poincare duality is to prove that the purity map:
$
  t_(AA^1_Y\/Y): p^(-1) cal(K)(1)[2] -> R p^! cal(K)
$
is an isomorphism for all $cal(K) in D(Y_et, Lambda)$.

For this, it turns out that we need to establish a special case Gysin purity statement.

#lemma(name: <etale-a1-homotopy-invariance>)[
  ($AA^1$-homotopy invariance) Let $Y$ be a noetherian $ZZ[n^(-1)]$-scheme and $p: AA^1_Y -> Y$. Then the unit:
  $
    ul(ZZ\/n) -> R p_* ul(ZZ\/n)
  $
  is an isomorphism.
]
#proof[
  #lemma[
    If $k$ is a separably closed field and $n in k^times$, there are canonical isomorphisms:
    $
      H^q (AA^1_k, ul(ZZ\/n)) cong cases(
        ZZ\/n & \, q = 0,
        0 & \, q >= 1
      )
    $
  ]
  #proof[
    By Artin vanishing it suffices to prove $H^1 (AA^1_k, ul(ZZ\/n)) = 0$, or equivalently $H^1 (AA^1_k, mu_n) = 0$. Take the long exact sequence induced by the Kummer sequence: 
    $
      0 -> mu_n (k) -> k[t]^times ->^((-)^n) k[t]^times -> H^1 (AA^1_k, mu_n) -> Pic(AA^1_k) ->^((-)^n) Pic(AA^1_k)
    $
    Now $k[t]^times = k^times$ and $(-)^n$ is surjective on it since $k$ is separably closed and $n in k^times$. Thus, $H^1 (AA^1_k, mu_n) = ker((-)^n: Pic(AA^1_k) -> Pic(AA^1_k))$. 

    Thus it suffices to show that $Pic(AA^1_k) = 0$. For comedic reasons I've put the proof of this part into a footnote. Please think about it for a moment, and if you can't figure it out, please read the footnote for a good laugh.#footnote[$k[t]$ is a PID and finite modules over it has a classification. The only locally free $k[t]$-modules of rank 1 among them is $k[t]$ itself. If this gave you a good laugh, you can try mess with your friends with this puzzle.]
  ]

  Now $p$ is smooth, hence locally acyclic relative to $ul(ZZ\/n)$. To prove that the unit $ul(ZZ\/n) -> R p_* ul(ZZ\/n)$ is an isomorphism, we invoke @loc-acyc-constancy-of-pushforward and see that it suffices to show that:
  $
    ZZ\/n -> R Gamma(AA^1_(ol(y)), ul(ZZ\/n))
  $
  is an isomorphism for all geometric points $ol(y)$ of $Y$. This follows from the previous lemma.
]

#lemma(name: <p1-section-gysin-purity>)[
  (Gysin purity for $PP^1$-section) Let $Y$ be a noetherian $ZZ[n^(-1)]$-scheme and $p: PP^1_Y -> Y$. Let $i: Y -> PP^1_Y$ be the zero section. 

  There is a unique morphism $c: i_* ul(ZZ\/n)_Y -> ul(ZZ\/n)_(PP^1_Y)(1)[2]$ s.t. the composition:
  $
    ul(ZZ\/n)_(PP^1_Y) cong R p_* i_* ul(ZZ\/n)_Y -->^(R p_* (c)) R p_* ul(ZZ\/n)_(PP^1_Y)(1)[2] -->^(Tr_(PP^1_Y\/Y)) ul(ZZ\/n)_Y
  $
  is the identity. It is compatible with base change.
]
#proof[
  We first identify $R p_* ul(ZZ\/n)$. Consider the trace map:
  $
    Tr_(PP^1_Y\/Y): R p_* ul(ZZ\/n) -> ul(ZZ\/n)(-1)[-2]
  $
  On the other hand, we have an adjunction unit $ul(ZZ\/n) -> i_(oo,*) ul(ZZ\/n)$. Applying $R p_*$ to it gives a natural map:
  $
    r_oo: R p_* ul(ZZ\/n) -> ul(ZZ\/n)
  $
  which is compatible with base change.

  Thus we have a map compatible with base change:
  $
    T = (Tr_(PP^1_Y\/Y), r_oo): Tr_(PP^1_Y\/Y): R p_* ul(ZZ\/n) -> ul(ZZ\/n)(-1)[-2] oplus ul(ZZ\/n)
  $
  We claim that $T$ is an isomorphism. Indeed, we may check on stalks by base changing to a geometric point and assume that $Y = Spec(k)$ is the spectrum of an algebraically closed field. Then in this case, $Tr$ induces the isomorphism $H^2 (PP^1_k, ul(ZZ\/n)) cong ZZ\/n(-1)$ on $h^2$, and $r_oo$ induces the isomorphism $H^0 (PP^1_k, ul(ZZ\/n)) cong ZZ\/n$ on $h^0$, and so $T$ is an isomorphism.

  It suffices to prove that:
  $
    Phi: Hom_(ZZ\/n) (i_* ul(ZZ\/n)_Y, ul(ZZ\/n)_(PP^1_Y) (1)[2]) & -> Hom_(ZZ\/n) (ul(ZZ\/n)_Y, ul(ZZ\/n)_Y) \
                                                            gamma & |-> Tr_(PP^1_Y\/Y) compose R p_* (gamma)
  $
  is an isomorphism. Take the complementary open immersion $j: AA^1_Y -> PP^1_Y$ of $i$. Then take the extension by zero triangle:
  $
    j_! ul(ZZ\/n)_(AA^1_Y) -> ul(ZZ\/n)_(PP^1_Y) -> i_* ul(ZZ\/n)_Y ->^(+1)
  $
  and apply $RHom_(ZZ\/n) (-, ul(ZZ\/n)_(PP^1_Y))$ to get a distinguished triangle:
  $
    RHom_(ZZ\/n) (i_* ul(ZZ\/n)_Y, ul(ZZ\/n)_(PP^1_Y)) ->^Q R Gamma(PP^1_Y, ul(ZZ\/n)) ->^res R Gamma(AA^1_Y, ul(ZZ\/n)) ->^(+1)
  $
  We may identify:

  - #h(1fr)
    $
      R Gamma(PP^1_Y, ul(ZZ\/n)) = R Gamma(Y, R p_* ul(ZZ\/n)) = RHom_(ZZ\/n) (ul(ZZ\/n)_Y, R p_* ul(ZZ\/n)_(PP^1_Y)) \
      R Gamma(AA^1_Y, ul(ZZ\/n)) = R Gamma(Y, R (p compose j)_* ul(ZZ\/n)) = RHom_(ZZ\/n) (ul(ZZ\/n)_Y, R (p compose j)_* ul(ZZ\/n)_(PP^1_Y))
    $
    Under these identifications, one can check formally that:

    - $res$ is induced by the adjunction unit $R p_* ul(ZZ\/n) -> R(p compose j)_* ul(ZZ\/n)$.

    - $Q$ is induced by:
      $
        RHom_(ZZ\/n) (i_* ul(ZZ\/n)_Y, ul(ZZ\/n)_(PP^1_Y)) -->^(R p_* (-)) RHom_(ZZ\/n) (R p_* i_* ul(ZZ\/n)_Y, R p_* ul(ZZ\/n)_(PP^1_Y)) = RHom_(ZZ\/n) (ul(ZZ\/n)_Y, R p_* ul(ZZ\/n)_(PP^1_Y))
      $

  - Now we have isomorphisms:
    $
      T: R p_* ul(ZZ\/n)_(PP^1_Y) -> ul(ZZ\/n)_Y (-1)[-2] oplus ul(ZZ\/n)_Y
    $
    as argued above, and:
    $
      R (p compose j)_* ul(ZZ\/n)_(AA^1_Y) -> ul(ZZ\/n)_Y
    $
    by $AA^1$-homotopy invariance (@etale-a1-homotopy-invariance). We claim that under these identifications, the unit $R p_* ul(ZZ\/n) -> R(p compose j)_* ul(ZZ\/n)$ is identified with the projection $ul(ZZ\/n)(-1)[-2] oplus ul(ZZ\/n) -> ul(ZZ\/n)$ onto second factor. For this we need to show the commutativity of:
    // https://q.uiver.app/#r=typst&q=WzAsMyxbMCwwLCJSIHFfKiB1bChaWlxcL24pXyhBQV4xX1kpIl0sWzIsMCwidWwoWlpcXC9uKV9ZIl0sWzAsMSwiUiBwXyogdWwoWlpcXC9uKV8oUFBeMV9ZKSJdLFsxLDAsInVfcSIsMl0sWzIsMCwiUiBxXyogKHVfaikiXSxbMiwxLCJSIHBfKiAodV8oaV9vbykpIiwyXV0=
    #align(center, diagram({
      node((0, 0), [$R q_* ul(ZZ\/n)_(AA^1_Y)$])
      node((2, 0), [$ul(ZZ\/n)_Y$])
      node((0, 1), [$R p_* ul(ZZ\/n)_(PP^1_Y)$])
      edge((2, 0), (0, 0), [$u_q$], label-side: right, "->")
      edge((0, 1), (0, 0), [$R q_* (u_j)$], label-side: left, "->")
      edge((0, 1), (2, 0), [$R p_* (u_(i_oo))$], label-side: right, "->")
    }))
    where $u_p, u_q, u_(i_oo)$ are unit maps for the right adjoints $R p_*, R q_*, i_(oo,*)$. This is formal.

  -
    $
      RHom_(ZZ\/n) (i_* ul(ZZ\/n)_Y, ul(ZZ\/n)_(PP^1_Y)) &->^Q R Gamma(PP^1_Y, ul(ZZ\/n)) cong RHom_(ZZ\/n) (ul(ZZ\/n)_Y, R p_* ul(ZZ\/n)_(PP^1_Y)) \
      &= RHom_(ZZ\/n) (ul(ZZ\/n)_Y, ul(ZZ\/n)_Y (-1)[-2] oplus ul(ZZ\/n)_Y) \
      &-> RHom_(ZZ\/n) (ul(ZZ\/n)_Y, ul(ZZ\/n)_Y (-1)[-2])
    $
    is just $Phi$ twisted by $(-1)[-2]$. Indeed, the first line is identified with $R p_* (-)$ as argued in the first bullet, and the second and third line is induced by $Tr_(PP^1_Y\/Y)$ by definition.

    This composition is an isomorphism due to the distinguished triangle:
    $
      RHom_(ZZ\/n) (i_* ul(ZZ\/n)_Y, ul(ZZ\/n)_(PP^1_Y)) ->^Q R Gamma(PP^1_Y, ul(ZZ\/n)) ->^res R Gamma(AA^1_Y, ul(ZZ\/n)) ->^(+1)
    $

    Thus, $Phi: RHom_(ZZ\/n) (i_* ul(ZZ\/n)_Y (1)[2], ul(ZZ\/n)_(PP^1_Y)) -> RHom_(ZZ\/n) (ul(ZZ\/n)_Y, ul(ZZ\/n)_Y)$ is an isomorphism.

  Taking $h^0$,
  $
    Phi: Hom_(ZZ\/n) (i_* ul(ZZ\/n)_Y (1)[2], ul(ZZ\/n)_(PP^1_Y)) -> Hom_(ZZ\/n) (ul(ZZ\/n)_Y, ul(ZZ\/n)_Y)
  $
  is an isomorphism. Taking the inverse image of $id$ yields $c: i_* ul(ZZ\/n)_Y (1)[2] -> ul(ZZ\/n)_(PP^1_Y)$.

  The construction of $Phi$ is compatible with base change, so the formation of $c$ is compatible with base change.
  /*Also denote $i_oo: Y -> PP^1_Y$ the infinity section.

  We first identify $R p_* ul(ZZ\/n)$. Consider the trace map:
  $
    Tr_(PP^1_Y\/Y): R p_* ul(ZZ\/n) -> ul(ZZ\/n)(-1)[-2]
  $
  On the other hand, we have an adjunction unit $ul(ZZ\/n) -> i_(oo,*) ul(ZZ\/n)$. Applying $R p_*$ to it gives a natural map:
  $
    r_oo: R p_* ul(ZZ\/n) -> ul(ZZ\/n)
  $
  which is compatible with base change.

  Thus we have a map compatible with base change:
  $
    Phi = (Tr_(PP^1_Y\/Y), r_oo): Tr_(PP^1_Y\/Y): R p_* ul(ZZ\/n) -> ul(ZZ\/n)(-1)[-2] oplus ul(ZZ\/n)
  $
  We claim that $Phi$ is an isomorphism. Indeed, we may check on stalks by base changing to a geometric point and assume that $Y = Spec(k)$ is the spectrum of an algebraically closed field. Then in this case, $Tr$ induces the isomorphism $H^2 (PP^1_k, ul(ZZ\/n)) cong ZZ\/n(-1)$ on $h^2$, and $r_oo$ induces the isomorphism $H^0 (PP^1_k, ul(ZZ\/n)) cong ZZ\/n$ on $h^0$, and so $Phi$ is an isomorphism.

  Let $j: AA^1_Y -> PP^1_Y$ be the inclusion and $q: AA^1_Y -> Y$ be the projection.

  Proceed by writing down the section with support triangle:
  $
    i_* R i^! ul(ZZ\/n) -> ul(ZZ\/n) -> R j_* ul(ZZ\/n) ->^(+1)
  $
  and apply $R p_*$ to get a distinguished triangle:
  $
    R i^! ul(ZZ\/n) ->^g R p_* ul(ZZ\/n) ->^h R q_* ul(ZZ\/n) ->^s_(+1)
  $
  - In this triangle we know: #h(1fr)
    $
      R p_* ul(ZZ\/n) cong ul(ZZ\/n)(-1)[-2] oplus ul(ZZ\/n) \
    $
    as just argued, and:
    $
      R q_* ul(ZZ\/n) cong ul(ZZ\/n)
    $
    by $AA^1$-homotopy invariance (@etale-a1-homotopy-invariance). We claim that under these identifications, $h$ is identified with the projection $ul(ZZ\/n)(-1)[-2] oplus ul(ZZ\/n) -> ul(ZZ\/n)$ onto second factor. For this we need to show the commutativity of:
    // https://q.uiver.app/#r=typst&q=WzAsMyxbMCwwLCJSIHFfKiB1bChaWlxcL24pXyhBQV4xX1kpIl0sWzIsMCwidWwoWlpcXC9uKV9ZIl0sWzAsMSwiUiBwXyogdWwoWlpcXC9uKV8oUFBeMV9ZKSJdLFsxLDAsInVfcSIsMl0sWzIsMCwiUiBxXyogKHVfaikiXSxbMiwxLCJSIHBfKiAodV8oaV9vbykpIiwyXV0=
    #align(center, diagram({
      node((0, 0), [$R q_* ul(ZZ\/n)_(AA^1_Y)$])
      node((2, 0), [$ul(ZZ\/n)_Y$])
      node((0, 1), [$R p_* ul(ZZ\/n)_(PP^1_Y)$])
      edge((2, 0), (0, 0), [$u_q$], label-side: right, "->")
      edge((0, 1), (0, 0), [$R q_* (u_j)$], label-side: left, "->")
      edge((0, 1), (2, 0), [$R p_* (u_(i_oo))$], label-side: right, "->")
    }))
    where $u_p, u_q, u_(i_oo)$ are unit maps for the right adjoints $R p_*, R q_*, i_(oo,*)$. This is formal.

  Thus we have a canonical map:
  $
    alpha: R i^! ul(ZZ\/n) ->^g R p_* ul(ZZ\/n) cong ul(ZZ\/n)(-1)[-2] oplus ul(ZZ\/n) -> ul(ZZ\/n)(-1)[-2]
  $
  and the distinguished triangle above makes $alpha$ an isomorphism. It thus induces a natural map:
  $
    beta: i_* ul(ZZ\/n) -> ul(ZZ\/n)(1)[2]
  $

  We now prove that this map is preserved under base change, and give it an explicit description in the case that $Y = Spec(k)$ for an algebraically closed field $k$. */
]

#lemma(name: <a1-section-gysin-purity>)[
  (Gysin purity for $AA^1$-section) Let $Y$ be a noetherian $ZZ[n^(-1)]$-scheme and $p: AA^1_Y -> Y$. Let $i: Y -> AA^1_Y$ be the zero section. 

  There is a unique morphism $c: i_* ul(ZZ\/n)_Y -> ul(ZZ\/n)_(AA^1_Y)(1)[2]$ s.t. the composition:
  $
    ul(ZZ\/n)_(AA^1_Y) cong R p_! i_* ul(ZZ\/n)_Y -->^(R p_! (c)) R p_! ul(ZZ\/n)_(AA^1_Y)(1)[2] -->^(Tr_(AA^1_Y\/Y)) ul(ZZ\/n)_Y
  $
  is the identity. It is compatible with base change.
]
#proof[
  Similar to the $PP^1_Y$-case, it suffices to prove that:
  $
    Phi: Hom_(ZZ\/n) (i_* ul(ZZ\/n)_Y, ul(ZZ\/n)_(AA^1_Y) (1)[2]) & -> Hom_(ZZ\/n) (ul(ZZ\/n)_Y, ul(ZZ\/n)_Y) \
                                                            gamma & |-> Tr_(AA^1_Y\/Y) compose R p_! (gamma)
  $
  is an isomorphism. Take the compactification $AA^1_Y ->^j PP^1_Y ->^(ol(p)) Y$ and the zero section $ol(i): Y -> PP^1_Y$. Also let $i_oo: Y -> PP^1_Y$ be the $oo$-section. Then it can be checked (using compatibility of the trace map with composition) that the composition:
  $
    Hom_(ZZ\/n) (i_* ul(ZZ\/n)_Y, ul(ZZ\/n)_(AA^1_Y) (1)[2]) &-->^(j_! (-)) Hom_(ZZ\/n) (ol(i)_* ul(ZZ\/n)_Y, j_! ul(ZZ\/n)_(AA^1_Y) (1)[2]) \
    &-->^(Tr_(AA^1_Y\/PP^1_Y)) Hom_(ZZ\/n) (ol(i)_* ul(ZZ\/n)_Y, ul(ZZ\/n)_(PP^1_Y) (1)[2]) \
    &-->^Phi Hom_(ZZ\/n) (ul(ZZ\/n)_Y, ul(ZZ\/n)_Y)
  $
  is exactly the $Phi$ constructed in @p1-section-gysin-purity for the $PP^1$-case, which we shall denote by $Phi'$. Thus by @p1-section-gysin-purity, $Phi'$ is an isomorphism. On the other hand, 

  - $Hom_(ZZ\/n) (cal(K), cal(L)) -->^(j_! (-)) Hom_(ZZ\/n) (j_! cal(K), j_! cal(L))cong Hom_(ZZ\/n) (cal(K), j^(-1) j_! cal(L)) cong Hom_(ZZ\/n) (cal(K), cal(L))$ by adjunction, hence $j_! (-)$ is always an isomorphism. Thus the first line is an isomorphism; 

  - For the second line, we have a distinguished triangle:
    $
      RHom_(ZZ\/n) (ol(i)_* ul(ZZ\/n)_Y, j_! ul(ZZ\/n)_(AA^1_Y) (1)[2]) -->^(Tr_(AA^1_Y\/PP^1_Y)) RHom_(ZZ\/n) (ol(i)_* ul(ZZ\/n)_Y, ul(ZZ\/n)_(PP^1_Y) (1)[2]) -> RHom_(ZZ\/n) (ol(i)_* ul(ZZ\/n)_Y, i_(oo,*) ul(ZZ\/n)_Y) ->^(+1)
    $
    but $RHom_(ZZ\/n) (ol(i)_* ul(ZZ\/n)_Y, i_(oo,*) ul(ZZ\/n)_Y) cong RHom_(ZZ\/n) (i_oo^(-1) ol(i)_* ul(ZZ\/n)_Y, ul(ZZ\/n)_Y) = 0$ since $ol(i), i_oo$ has disjoint image. Thus $Tr_(AA^1_Y\/PP^1_Y)$ is an isomorphism: 
    $
      RHom_(ZZ\/n) (ol(i)_* ul(ZZ\/n)_Y, j_! ul(ZZ\/n)_(AA^1_Y) (1)[2]) -> RHom_(ZZ\/n) (ol(i)_* ul(ZZ\/n)_Y, ul(ZZ\/n)_(PP^1_Y) (1)[2])
    $
    Taking $h^0$ allows us to replace $RHom$ by $Hom$ and conclude that the second line is an isomorphism. 

  $Phi$ is thus an isomorphism, and we are thereby done. 
]

We are now ready to prove Poincare duality. 

#theorem(name: <a1-poincare-duality>)[
  (Poincare duality for $AA^1$) Let $Lambda$ be an $n$-torsion noetherian ring. Let $Y$ be a noetherian $ZZ[n^(-1)]$-scheme and $p: AA^1_Y -> Y$. Then the purity map: 
  $
    t_(AA^1_Y\/Y): p^(-1) cal(K)(1)[2] -> R p^! cal(K)
  $
  is an isomorphism for all $cal(K) in D(Y_et, Lambda)$. 
]
#proof[
  $R p_!$ does not care if the complex is a complex of sheaves of $Lambda$-modules or forgotten to $ZZ\/n$-modules (since lower star doesn't). Thus, we may assume $Lambda = ZZ\/n$. 

  We directly prove the adjunction: 
  $
    R p_! tack.l p^(-1) (-)(1)[2]
  $
  The counit map is of course the trace: 
  $
    eta_Y = Tr_(AA^1_Y\/Y): R p_! p^(-1) cal(K) (1)[2] -> cal(K)
  $
  so we need to manually construct a unit: 
  $
    u_Y: cal(L) -> p^(-1) R p_! cal(L)(1)[2]
  $
  The construction is as follows: 

  - Take the diagonal $Delta: AA^1_Y -> AA^2_Y$ and projections $q_(1,2): AA^2_Y -> AA^1_Y$. $Delta$ is the zero section of both $q_1$ and $q_2$ under different coordinates. Thus by @a1-section-gysin-purity, there is a unique map: 
    $
      c_Y: R Delta_* ul(ZZ\/n)_(AA^1_Y) -> ul(ZZ\/n)_(AA^2_Y) (1)[2]
    $
    s.t the composition: 
    $
      ul(ZZ\/n)_(AA^1_Y) cong R q_(i,*) Delta_* ul(ZZ\/n)_(AA^1_Y) -->^(R q_(i,*) c) R q_(i,*) ul(ZZ\/n)_(AA^2_Y)(1)[2] -->^(Tr_(q_i:AA^2_Y\/AA^1_Y)) ul(ZZ\/n)_(AA^1_Y)
    $
    is the identity for both $i=1,2$. 

    Then since $q_(1,2) compose Delta = id$, we have: 
    $
      cal(L) &cong R q_(2,!) R Delta_* cal(L) cong R q_(2,!) R Delta_* (Delta^(-1) q_1^(-1) cal(L)) \
      &cong R q_(2,!) (q_1^(-1) cal(L) Lotimes_(ZZ\/n) R Delta_* ul(ZZ\/n)) #[by projection formula] \
      &->^(c_Y) R q_(2,!) q_1^(-1) cal(L)(1)[2] \
      &cong R p_! p^(-1) cal(L)(1)[2] #[by proper base change]
    $
    This is the unit map $u_Y$. 

  It remains to verify the adjunction identities that: 
  $
    R p_! cal(L) -->^(R p_! u_Y) R p_! p^(-1) R p_! cal(L)(1)[2] -->^(eta_Y R p_!) R p_! cal(L)
  $
  $
    p^(-1) cal(K) -->^(u_Y p^(-1)) p^(-1) R p_! p^(-1) cal(K)(1)[2] -->^(p^(-1) eta_Y) p^(-1) cal(K)
  $
  
  - We need an auxiliary statement for these two identities: Put $r: AA^2_Y -> Y$, and the following diagram commutes: #h(1fr)
    // https://q.uiver.app/#r=typst&q=WzAsNixbMCwxLCJSIHBfISBSIHFfKDIsISkgcV8xXigtMSkgY2FsKEwpIl0sWzAsMiwiUiBwXyEgcF4oLTEpIFIgcF8hIGNhbChMKSJdLFsxLDIsIlIgcF8hIGNhbChMKSgtMSlbLTJdIl0sWzEsMSwiUiBwXyEgUiBxXygxLCEpIHFfMV4oLTEpIGNhbChMKSJdLFswLDAsIlIgcl8hIHFfMV4oLTEpIGNhbChMKSJdLFsxLDAsIlIgcl8hIHFfMV4oLTEpIGNhbChMKSJdLFs0LDUsIiIsMCx7InN0eWxlIjp7ImJvZHkiOnsibmFtZSI6ImRvdWJsZSBiYXJyZWQifX19XSxbNCwwLCJ0aWxkZSIsMl0sWzUsMywidGlsZGUiXSxbMCwxLCJCQ14oLTEpIiwyXSxbMywyLCJUcl8ocV8xKSJdLFsxLDIsIlRyX3AiLDJdXQ==
    #align(center, diagram({
      node((0, 0), [$R p_! R q_(2,!) q_1^(-1) cal(L)$])
      node((0, 1), [$R p_! p^(-1) R p_! cal(L)$])
      node((1, 1), [$R p_! cal(L)(-1)[-2]$])
      node((1, 0), [$R p_! R q_(1,!) q_1^(-1) cal(L)$])
      node((0, -1), [$R r_! q_1^(-1) cal(L)$])
      node((1, -1), [$R r_! q_1^(-1) cal(L)$])
      edge((0, -1), (1, -1), "=")
      edge((0, -1), (0, 0), [$tilde$], label-side: right, "->")
      edge((1, -1), (1, 0), [$tilde$], label-side: left, "->")
      edge((0, 0), (0, 1), [$BC^(-1)$], label-side: right, "->")
      edge((1, 0), (1, 1), [$Tr_(q_1)$], label-side: left, "->")
      edge((0, 1), (1, 1), [$Tr_p$], label-side: right, "->")
    }))
    It can be checked that by definition of the Kunneth map, the lower left path is the composition: 
    $
      R r_! q_1^(-1) cal(L) cong R r_! (q_1^(-1) cal(L) Lotimes_(ZZ\/n) q_2^(-1) ul(ZZ\/n)) ->^K R p_! cal(L) Lotimes_(ZZ\/n) R p_! ul(ZZ\/n) -->^(Tr_p) R p_! cal(L) Lotimes_(ZZ\/n) ul(ZZ\/n)(-1)[-2]
    $
    where $K$ is the Kunneth map. On the other hand, the right path is given by: 
    $
      R r_! q_1^(-1) cal(L) ->^P R p_! (cal(L) Lotimes_Lambda R q_(1,!) ul(ZZ\/n)) ->^(Tr_(q_1)) R p_! (cal(L) Lotimes_Lambda ul(ZZ\/n)(-1)[-2]) ->^P R p_! cal(L) Lotimes_Lambda ul(ZZ\/n)(-1)[-2]
    $
    Since the Kunneth map is symmetric, it can be defined by projecting onto either factor first. Thus the lower left path factors as: 
    $
      R r_! (q_1^(-1) cal(L) Lotimes_(ZZ\/n) q_2^(-1) ul(ZZ\/n)) &-->^P R p_! (cal(L) Lotimes_(ZZ\/n) R q_(1,!) q_2^(-1) ul(ZZ\/n)) -->^(BC^(-1)) R p_! (cal(L) Lotimes_(ZZ\/n) p^(-1) R p_! ul(ZZ\/n)) \
      &-->^P R p_! cal(L) Lotimes_(ZZ\/n) R p_! ul(ZZ\/n) -->^(Tr_p) cal(L) Lotimes_(ZZ\/n) ul(ZZ\/n)(-1)[2]
    $
    The last two maps may be swapped by naturality to: 
    $
      dots.c -->^(Tr_p) R p_! (cal(L) Lotimes_(ZZ\/n) ul(ZZ\/n)(-1)[2]) -->^(P) cal(L) Lotimes_(ZZ\/n) ul(ZZ\/n)(-1)[2]
    $

    The first projection along $q_1$ may be cancelled with that of the right path, and the last projection along $p$ may also be cancelled. Then also peeling off $R p_!$ and $cal(L) Lotimes_(ZZ\/n) -$ it suffices to check that the composition: 
    $
      p^(-1) R p_! ul(ZZ\/n) ->^BC R q_(1,!) q_2^(-1) ul(ZZ\/n) = R q_(1,!) ul(ZZ\/n) ->^(Tr_(q_1)) ul(ZZ\/n)(-1)[-2]
    $
    is exactly $Tr_p$. This is just compatibility of the trace map with base change. Also the same relation holds with $q_1, q_2$ swapped by symmetry. 

  - To verify the first adjunction identity we consider the following diagram: 
    // https://q.uiver.app/#r=typst&q=WzAsMTQsWzAsMCwiUiBwXyEgY2FsKEwpIl0sWzAsMSwiUiBwXyEgUiBxXygxLCEpIFIgRGVsdGFfKiBEZWx0YV4oLTEpIHFfMl4oLTEpIGNhbChMKSJdLFswLDIsIlIgcF8hIFIgcV8oMSwhKSAocV8yXigtMSkgY2FsKEwpIExvdGltZXNfKFpaXFwvbikgUiBEZWx0YV8qIHVsKFpaXFwvbikpIl0sWzAsMywiUiBwXyEgUiBxXygxLCEpIHFfMl4oLTEpIGNhbChMKSgxKVsyXSJdLFswLDQsIlIgcF8hIHBeKC0xKSBSIHBfISBjYWwoTCkoMSlbMl0iXSxbMCw1LCJSIHBfISBjYWwoTCkiXSxbMSwwLCJSIHBfISBjYWwoTCkiXSxbMSwxLCJSIHBfISBSIHFfKDIsISkgUiBEZWx0YV8qIERlbHRhXigtMSkgcV8yXigtMSkgY2FsKEwpIl0sWzEsMiwiUiBwXyEgUiBxXygyLCEpIChxXzJeKC0xKSBjYWwoTCkgTG90aW1lc18oWlpcXC9uKSBSIERlbHRhXyogdWwoWlpcXC9uKSkiXSxbMSwzLCJSIHBfISBSIHFfKDIsISkgcV8yXigtMSkgY2FsKEwpKDEpWzJdIl0sWzEsNSwiUiBwXyEgY2FsKEwpIl0sWzEsNCwiUiBwXyEgKGNhbChMKSBMb3RpbWVzXyhaWlxcL24pIFIgcV8oMiwhKSB1bChaWlxcL24pICgxKVsyXSkiXSxbMiwzLCJSIHBfISAoY2FsKEwpIExvdGltZXNfKFpaXFwvbikgUiBxXygyLCEpIFIgRGVsdGFfKiB1bChaWlxcL24pKSJdLFsyLDQsIlIgcF8hIGNhbChMKSBMb3RpbWVzXyhaWlxcL24pIFIgcV8oMiwhKSB1bChaWlxcL24pICgxKVsyXSJdLFswLDEsInRpbGRlIiwyXSxbMSwyLCJQIiwyXSxbMiwzLCJjIiwyXSxbMyw0LCJCQ14oLTEpIiwyXSxbNCw1LCJUcl9wIiwyXSxbNiw3LCJ0aWxkZSJdLFs3LDgsIlAiXSxbOCw5LCJjIl0sWzAsNiwiIiwwLHsic3R5bGUiOnsiYm9keSI6eyJuYW1lIjoiZG91YmxlIGJhcnJlZCJ9fX1dLFsxLDcsInRpbGRlIiwxXSxbMiw4LCJ0aWxkZSIsMV0sWzUsMTAsInRpbGRlIiwyXSxbMyw5LCJ0aWxkZSIsMV0sWzksMTEsIlAiXSxbMTEsMTAsIlRyXyhxXzIpIl0sWzgsMTIsIlAiLDFdLFs3LDEyLCJQIiwxLHsiY3VydmUiOi01fV0sWzEyLDEzLCJjIl0sWzEzLDEwLCJUciJdXQ==
    #context align(center, diagram({
      node((0, 0), [$R p_! cal(L)$])
      node((0, 1), [$R p_! R q_(2,!) R Delta_* Delta^(-1) q_1^(-1) cal(L)$])
      node((0, 2), [$R p_! R q_(2,!) (q_1^(-1) cal(L) Lotimes_(ZZ\/n) R Delta_* ul(ZZ\/n))$])
      node((0, 3), [$R p_! R q_(2,!) q_1^(-1) cal(L)(1)[2]$])
      node((0, 4), [$R p_! p^(-1) R p_! cal(L)(1)[2]$])
      node((0, 5), [$R p_! cal(L)$])
      node((1, 0), [$R p_! cal(L)$])
      node((1, 1), [$R p_! R q_(1,!) R Delta_* Delta^(-1) q_1^(-1) cal(L)$])
      node((1, 2), [$R p_! R q_(1,!) (q_1^(-1) cal(L) Lotimes_(ZZ\/n) R Delta_* ul(ZZ\/n))$])
      node((1, 3), [$R p_! R q_(1,!) q_1^(-1) cal(L)(1)[2]$])
      node((1, 5), [$R p_! cal(L)$])
      node((1, 4), [$R p_! (cal(L) Lotimes_(ZZ\/n) R q_(1,!) ul(ZZ\/n) (1)[2])$])
      node((2, 3), [$R p_! (cal(L) Lotimes_(ZZ\/n) R q_(1,!) R Delta_* ul(ZZ\/n))$])
      node((2, 4), [$R p_! cal(L) Lotimes_(ZZ\/n) R q_(1,!) ul(ZZ\/n) (1)[2]$])
      edge((0, 0), (0, 1), [$tilde$], label-side: right, "->")
      edge((0, 1), (0, 2), [$P$], label-side: right, "->")
      edge((0, 2), (0, 3), [$c$], label-side: right, "->")
      edge((0, 3), (0, 4), [$BC^(-1)$], label-side: right, "->")
      edge((0, 4), (0, 5), [$Tr_p$], label-side: right, "->")
      edge((1, 0), (1, 1), [$tilde$], label-side: left, "->")
      edge((1, 1), (1, 2), [$P$], label-side: left, "->")
      edge((1, 2), (1, 3), [$c$], label-side: left, "->")
      edge((0, 0), (1, 0), "=")
      edge((0, 1), (1, 1), [$tilde$], label-side: center, "->")
      edge((0, 2), (1, 2), [$tilde$], label-side: center, "->")
      edge((0, 5), (1, 5), label-side: right, "=")
      edge((0, 3), (1, 3), [$tilde$], label-side: center, "->")
      edge((1, 3), (1, 4), [$P$], label-side: left, "->")
      edge((1, 4), (1, 5), [$Tr_(q_1)$], label-side: left, "->")
      edge((1, 2), (2, 3), [$P$], label-side: center, "->")
      edge((1, 1), (2, 3), [$P$], label-side: center, "->", bend: 30deg)
      edge((2, 3), (2, 4), [$c$], label-side: left, "->")
      edge((2, 4), (1, 5), [$Tr_(q_1)$], label-side: left, "->")
    }, crossing-fill: thm-box-curr-color()))
    Here all cells except for the lower left one commute by naturality, and the lower left cell commutes by the first bullet. Thus it suffices to verify that the right path is the identity. Indeed, 
    $
      R q_(1,!) R Delta_* ul(ZZ\/n) ->^c R q_(1,!) ul(ZZ\/n) (1)[2] -->^(Tr_(q_1)) ul(ZZ\/n)
    $
    is the natural isomorphism $R q_(1,!) R Delta_* ul(ZZ\/n) cong ul(ZZ\/n)$ induced by $q_1 compose Delta = id$, and it cancels the projection along $q_1 compose Delta$. 

  - For the second identity, we use the following diagram: 
    // https://q.uiver.app/#r=typst&q=WzAsMTQsWzAsMCwicF4oLTEpIGNhbChLKSJdLFswLDEsIlIgcV8oMiwhKSBSIERlbHRhXyogRGVsdGFeKC0xKSBxXzFeKC0xKSBwXigtMSkgY2FsKEspIl0sWzAsMiwiUiBxXygyLCEpIChxXzFeKC0xKSBwXigtMSkgY2FsKEspIExvdGltZXNfKFpaXFwvbikgUiBEZWx0YV8qIHVsKFpaXFwvbikpIl0sWzAsMywiUiBxXygyLCEpIHFfMV4oLTEpIHBeKC0xKSBjYWwoSykgKDEpWzJdIl0sWzAsNCwicF4oLTEpIFIgcF8hIHBeKC0xKSBjYWwoSykoMSlbMl0iXSxbMCw1LCJwXigtMSkgY2FsKEspIl0sWzEsMCwicF4oLTEpIGNhbChLKSJdLFsxLDEsIlIgcV8oMiwhKSBSIERlbHRhXyogRGVsdGFeKC0xKSBxXzJeKC0xKSBwXigtMSkgY2FsKEspIl0sWzEsMiwiUiBxXygyLCEpIChxXzJeKC0xKSBwXigtMSkgY2FsKEspIExvdGltZXNfKFpaXFwvbikgUiBEZWx0YV8qIHVsKFpaXFwvbikpIl0sWzEsMywiUiBxXygyLCEpIHFfMl4oLTEpIHBeKC0xKSBjYWwoSykgKDEpWzJdIl0sWzEsNSwicF4oLTEpIGNhbChLKSJdLFsxLDQsInBeKC0xKSBjYWwoSykgTG90aW1lc18oWlpcXC9uKSBSIHFfKDIsISkgdWwoWlpcXC9uKSgxKVsyXSJdLFsyLDMsInBeKC0xKSBjYWwoSykgTG90aW1lc18oWlpcXC9uKSBSIHFfKDIsISkgUiBEZWx0YV8qIHVsKFpaXFwvbikiXSxbMiw0LCJwXigtMSkgY2FsKEspIExvdGltZXNfKFpaXFwvbikgUiBxXygyLCEpICB1bChaWlxcL24pKDEpWzJdIl0sWzAsMSwidGlsZGUiLDJdLFsxLDIsIlAiLDJdLFsyLDMsImMiLDJdLFszLDQsIkJDXigtMSkiLDJdLFs0LDUsIlRyX3AiLDJdLFs2LDcsInRpbGRlIl0sWzcsOCwiUCJdLFswLDYsIiIsMCx7InN0eWxlIjp7ImJvZHkiOnsibmFtZSI6ImRvdWJsZSBiYXJyZWQifX19XSxbMSw3LCJ0aWxkZSIsMV0sWzIsOCwidGlsZGUiLDFdLFszLDksInRpbGRlIiwxXSxbNSwxMCwiIiwyLHsic3R5bGUiOnsiYm9keSI6eyJuYW1lIjoiZG91YmxlIGJhcnJlZCJ9fX1dLFs4LDksImMiXSxbOSwxMSwiUCJdLFsxMSwxMCwiVHJfKHFfMikiXSxbOCwxMiwiUCIsMV0sWzEyLDEzLCJjIiwxXSxbMTMsMTAsIlRyXyhxXzIpIiwxXSxbNywxMiwiUCIsMSx7ImN1cnZlIjotM31dXQ==
    #context align(center, diagram({
      node((0, 0), [$p^(-1) cal(K)$])
      node((0, 1), [$R q_(2,!) R Delta_* Delta^(-1) q_1^(-1) p^(-1) cal(K)$])
      node((0, 2), [$R q_(2,!) (q_1^(-1) p^(-1) cal(K) Lotimes_(ZZ\/n) R Delta_* ul(ZZ\/n))$])
      node((0, 3), [$R q_(2,!) q_1^(-1) p^(-1) cal(K) (1)[2]$])
      node((0, 4), [$p^(-1) R p_! p^(-1) cal(K)(1)[2]$])
      node((0, 5), [$p^(-1) cal(K)$])
      node((1, 0), [$p^(-1) cal(K)$])
      node((1, 1), [$R q_(2,!) R Delta_* Delta^(-1) q_2^(-1) p^(-1) cal(K)$])
      node((1, 2), [$R q_(2,!) (q_2^(-1) p^(-1) cal(K) Lotimes_(ZZ\/n) R Delta_* ul(ZZ\/n))$])
      node((1, 3), [$R q_(2,!) q_2^(-1) p^(-1) cal(K) (1)[2]$])
      node((1, 5), [$p^(-1) cal(K)$])
      node((1, 4), [$p^(-1) cal(K) Lotimes_(ZZ\/n) R q_(2,!) ul(ZZ\/n)(1)[2]$])
      node((2, 3), [$p^(-1) cal(K) Lotimes_(ZZ\/n) R q_(2,!) R Delta_* ul(ZZ\/n)$])
      node((2, 4), [$p^(-1) cal(K) Lotimes_(ZZ\/n) R q_(2,!)  ul(ZZ\/n)(1)[2]$])
      edge((0, 0), (0, 1), [$tilde$], label-side: right, "->")
      edge((0, 1), (0, 2), [$P$], label-side: right, "->")
      edge((0, 2), (0, 3), [$c$], label-side: right, "->")
      edge((0, 3), (0, 4), [$BC^(-1)$], label-side: right, "->")
      edge((0, 4), (0, 5), [$Tr_p$], label-side: right, "->")
      edge((1, 0), (1, 1), [$tilde$], label-side: left, "->")
      edge((1, 1), (1, 2), [$P$], label-side: left, "->")
      edge((0, 0), (1, 0), "=")
      edge((0, 1), (1, 1), [$tilde$], label-side: center, "->")
      edge((0, 2), (1, 2), [$tilde$], label-side: center, "->")
      edge((0, 3), (1, 3), [$tilde$], label-side: center, "->")
      edge((0, 5), (1, 5), "=")
      edge((1, 2), (1, 3), [$c$], label-side: left, "->")
      edge((1, 3), (1, 4), [$P$], label-side: left, "->")
      edge((1, 4), (1, 5), [$Tr_(q_2)$], label-side: left, "->")
      edge((1, 2), (2, 3), [$P$], label-side: center, "->")
      edge((2, 3), (2, 4), [$c$], label-side: center, "->")
      edge((2, 4), (1, 5), [$Tr_(q_2)$], label-side: center, "->")
      edge((1, 1), (2, 3), [$P$], label-side: center, "->", bend: 30deg)
    }, crossing-fill: thm-box-curr-color()))
    All cells except for the lower left one commute by naturality. 

    - For the lower left one, to verify its commutativity, note that everything here is compatible with base change, and so by checking on stalks we may assume that $Y = Spec(k)$ is a geometric point. Now $D(Y_et, ZZ\/n) cong D(ZZ\/n)$ is generated by the compact object $ul(ZZ\/n)$, and both paths of this square preserve arbitrary direct sums. Thus by @cpct-generation-of-triangulated-cat it suffices to check for $cal(K) = ul(ZZ\/n)$. In this case the projection map is the identity, and we need to check that: 
      $
        R q_(2,!) ul(ZZ\/n)(1)[2] -->^(BC^(-1)) p^(-1) R p_! p^(-1) ul(ZZ\/n)(1)[2] -->^(Tr_p) ul(ZZ\/n)
      $
      is just $Tr_(q_2)$. This is compatibility with base change of the trace map. 

    Thus it suffices to prove that the right path is the identity. Indeed, by defining properties of $c$, 
    $
      R q_(2,!) R Delta_* ul(ZZ\/n) ->^c R q_(2,!) ul(ZZ\/n) (1)[2] -->^(Tr_(q_2)) ul(ZZ\/n)
    $
    is the natural isomorphism $R q_(2,!) R Delta_* ul(ZZ\/n) cong ul(ZZ\/n)$ induced by $q_2 compose Delta = id$, and it cancels the projection along $q_2 compose Delta$. 

  With both adjunction identities proved, we have officially identified an adjoint pair: 
  $
    R p_! tack.l p^(-1) (-)(1)[2]
  $
  with the trace map as the adjunction counit. Thus the purity map: 
  $
    t_(AA^1_Y\/Y): p^(-1) cal(K) (1)[2] -> R p^! cal(K)
  $
  is an isomorphism for all $cal(K) in D(Y_et, ZZ\/n)$. 
]

#theorem(name: <relative-poincare-duality>)[
  (Relative Poincare duality) Let $Lambda$ be an $n$-torsion noetherian ring. For any smooth morphism $f: X -> Y$ of relative dimension $d$ between noetherian $ZZ[n^(-1)]$-schemes, the purity map: 
  $
    t_(X\/Y): f^(-1) cal(K)(d)[2d] -> R f^! cal(K)
  $
  is an isomorphism for all $cal(K) in D(Y_et, Lambda)$. 
]
#proof[
  The purity map is compatible with composition, in the sense that for $p_d: AA^d_Y ->^q AA^(d-1)_Y ->^(p_(d-1)) Y$, the composition: 
  $
    p_d^(-1) cal(K)(d)[2d] &cong q^(-1) (p_(d-1)^(-1) cal(K)(d-1)[2d-2])(1)[2] \
    &-->^(t_q) R q^! p_(d-1)^(-1) cal(K)(d-1)[2d-2] \
    &-->^(t_(p_(d-1))) R q^! R p_(d-1)^! cal(K) cong R p_d^! cal(K)
  $
  is exactly the purity map $t_(p_d)$. Now $t_q$ is always an isomorphism by @a1-poincare-duality, so by induction on $d$, we may conclude that the purity map: 
  $
    t_(AA^d_Y\/Y): p_d^(-1) cal(K)(d)[2d] -> R p_d^! cal(K) 
  $
  is always an isomorphism for $p_d: AA^d_Y -> Y$. 

  Now suppose that a (separated) smooth morphism $f: X -> Y$ factors as $X ->^j AA^d_Y ->^p Y$ for $j$ (separated) etale. Then the composition: 
  $
    f^(-1) cal(K)(d)[2d] cong j^(-1) p^(-1) cal(K)(d)[2d] cong R j^! p^(-1) cal(K)(d)[2d] -->^(t_p) R j^! R p^! cal(K) cong R f^! cal(K) 
  $
  is exactly the purity map $t_(X\/Y)$. Since $t_p$ is an isomorphism, so is $t_(X\/Y)$. 

  Finally, for a general (separated) smooth morphism $f: X -> Y$ there exists a (separated) etale cover $ell: U -> X$ s.t. $f compose ell$ factors as $U ->^j AA^d_Y ->^p Y$ for $j$ (separated) etale. Then the purity map $t_(U\/Y)$ is an isomorphism, and is the composition: 
  $
    ell^(-1) f^(-1) cal(K)(d)[2d] ->^(ell^(-1) t_(X\/Y)) ell^(-1) R f^! cal(K) cong R ell^! R f^! cal(K)
  $
  Thus $ell^(-1) t_(X\/Y): ell^(-1) f^(-1) cal(K)(d)[2d] -> ell^(-1) R f^! cal(K)$ is an isomorphism. Then since $ell$ is surjective, by @surjective-pullback-conservative, $t_(X\/Y)$ is always an isomorphism. We are thereby done. 
]

#theorem(name: <absolute-poincare-duality>)[
  (Absolute Poincare duality) Let $Lambda$ be an $n$-torsion noetherian ring that is an injective module over itself. Let $k$ be an algebraically closed field s.t. $n in k^times$, and $X$ be a smooth $k$-scheme of pure dimension $d$. Then: 

  + For a complex $cal(K) in D(X_et, Lambda)$, the cup product pairing: #h(1fr)
    $
      smile: h^q (R Gamma_c (X, cal(K))) times h^(2d-q) (RHom_Lambda (cal(K), ul(Lambda)(d))) -> Lambda
    $
    is perfect. In particular, for a sheaf $cal(F) in cAb(X_et, Lambda)$, the cup product pairing:
    $
      smile: H^q_c (X, cal(F)) times Ext^(2d-q)_Lambda (cal(F), ul(Lambda)(d)) -> Lambda
    $
    is perfect. 

  + For a l.c.c. sheaf $cal(F) in cAb(X_et, Lambda)$, there exists a canonical perfect bilinear pairing: 
    $
      smile: H^q_c (X, cal(F)) times H^(2d-q) (X, caron(cal(F))(d)) -> Lambda
    $
    where $cal(F)^caron = HHom_Lambda (cal(F), ul(Lambda))$. 
]
#proof[
  (1) follows from @relative-poincare-duality and the discussion in @constr-pd-relative-to-absolute. For (2), it suffices to prove that: 
  $
    Ext^(2d-q)_Lambda (cal(F), ul(Lambda)(d)) cong H^(2d-q) (X, caron(cal(F))(d))
  $
  Take the Hochschild-Serre spectral sequence (essentially the Grothendieck-Leray spectral sequence of the composition of derived functors $R Gamma(X, RHHom_Lambda (-, -)) = RHom_Lambda (-, -)$): 
  $
    E_2^(p,q) = H^p (X, EExt^q_Lambda (cal(F), ul(Lambda)(d))) -> Ext^(p+q)_Lambda (cal(F), ul(Lambda)(d))
  $
  we see that it suffices to show that whenever $q>=1$, 
  $
    EExt^q_Lambda (cal(F), ul(Lambda)(d)) = 0
  $

  This follows from the following lemma: 
  #lemma(name: <lcc-and-injective-has-no-higher-ext>)[
    Let $Lambda$ be a noetherian ring and $cal(F)$ be an l.c.c. sheaf of $Lambda$-modules on a scheme $X$, and $G$ be an injective $Lambda$-module. Then: 
    $
      EExt^q (cal(F), ul(G)) = 0, forall q >= 1
    $
  ]
  #proof[
    Indeed, take an etale cover $U -> X$ s.t. $cal(F)|_U = ul(M)_U$ for some finite $Lambda$-module $M$. Then by @surjective-pullback-conservative it suffices to prove the vanishing of the following sheaf: 
    $
      EExt^q_Lambda (cal(F), ul(G))|_U cong EExt^q_Lambda (cal(F)|_U, ul(G)_U) cong EExt^q_Lambda (ul(M)_U, ul(G)_U)
    $
    so we need to show that $EExt^q_Lambda (ul(M)_U, ul(G)_U) = 0$. 
    
    - In the case that $M$ is a finite free $Lambda$-module, it suffices to prove that $EExt^q_Lambda (ul(Lambda)_U, ul(G)_U) = 0$ for $q >= 1$. Now $HHom_Lambda (ul(Lambda)_U, -)$ is the identity functor, so it has no higher derived functors. 

    - In the general case, pick a free resolution $dots.c -> L^(-1) -> L^0 -> M -> 0$ by free $Lambda$-modules $L^p$ that can be taken to be finite since $Lambda$ is noetherian. Since each $EExt^q (ul(L^(-p))_U, ul(G)_U) = 0$ for $q >= 1$ as argued above, $EExt^q_Lambda (ul(M)_U, ul(G)_U)$ can be computed using this resolution. Then for $q >= 1$: 
    $
      EExt^q_Lambda (ul(M)_U, ul(G)_U) &cong h^q (0 -> HHom_Lambda (ul(L^0), ul(G)) -> HHom_Lambda (ul(L^(-1)), ul(G)) -> dots.c) \
      &cong h^q (0 -> ul(Hom_Lambda (L^0, G)) -> ul(Hom_Lambda (L^(-1), G)) -> dots.c) \
      &cong ul(h^q (0 -> Hom_Lambda (L^0, G) -> Hom_Lambda (L^(-1), G) -> dots.c)) = 0
    $
    where $0 -> Hom_Lambda (L^0, G) -> Hom_Lambda (L^(-1), G) -> dots.c$ is exact at degree $q$ since $G$ is an injective $Lambda$-module. 
  ]

  Applying this lemma to the l.c.c. sheaf $cal(F)$ and the injective $Lambda$-module $Lambda(d)$ concludes the proof. 
]

#corollary(name: <relative-purity>)[
  (Relative purity) Let $Lambda$ be an $n$-torsion noetherian ring that is an injective module over itself. Let $S$ be a noetherian $ZZ[n^(-1)]$-scheme. 
  
  Suppose that $i: X -> Y$ is a closed immersion between separated smooth $S$-schemes $X, Y$ of relative dimension $d-c$ and $d$ respectively. Let $f: Y -> S, f_X: X -> S$ be the structure maps. Then:
  
  + For $cal(K) in D(S_et, Lambda)$ there is a canonical natural isomorphism: #h(1fr)
    $
      R i^! f^(-1) cal(K) cong i^(-1) f^(-1) cal(K) (-c)[-2c]
    $

  + Let $c >= 1$ and $j: U -> Y$ be the complementary open immersion to $i$, and let $f_U = f compose j: U -> S$. Then for any $cal(F) in cAb(S_et, Lambda)$, there are canonical isomorphisms: 
    $
      R^q j_* f_U^(-1) cal(F) = cases(
        f^(-1) cal(F) &\, q = 0, 
        i_* f_X^(-1) cal(F)(-c) &\, q = 2c-1, 
        0 &\, #[otherwise]
      ) 
    $
  + (Gysin sequence) In the settings of (2), there is a canonical long exact sequence: 
    $
      0 &-> R^(2c-1) f_* f^(-1) cal(F) -> R^(2c-1) f_(U,*) f_U^(-1) cal(F) -> f_(X,*) f_X^(-1) cal(F)(-c) -> dots.c \
      &-> R^(q-1) f_* f^(-1) cal(F) -> R^(q-1) f_(U,*) f_U^(-1) cal(F) -> R^(q-2c) f_(X,*) f_X^(-1) cal(F)(-c) -> dots.c 
    $
    and canonical isomorphisms: 
    $
      R^q f_* f^(-1) cal(F) cong R^q f_(U,*) f_U^(-1) cal(F), forall 0 <= q <= 2c-2
    $
]
#proof[
  (1) Take the structure map $f: Y -> S$ smooth of relative dimension $d$, so $f compose i: X -> S$ is smooth of relative dimension $d-c$. 

  By relative Poincare duality, 
  $
    R i^! f^(-1) cal(K) &cong R i^! R f^! cal(K)(-d)[-2d] cong R f_X^! cal(K)(-d)[-2d] \
    &cong (f_X^(-1) cal(K)(d-c)[2(d-c)])(-d)[-2d] \
    &cong i^(-1) f^(-1) cal(K)(-c)[-2c]
  $
  We are thereby done. 

  (2) From the sections with support triangle: 
  $
    i_* R i^! f^(-1) cal(F) -> f^(-1) cal(F) -> R j_* j^(-1) f^(-1) cal(F) ->^(+1)
  $
  and (1), we obtain the formula for $R^q j_* f_U^(-1) cal(F)$ immediately. 
  
  (3) Take the Leray spectral sequence: 
  $
    E_2^(p,q) = R^p f_* R^q j_* (f_U^(-1) cal(F)) => R^(p+q) f_(U,*) f_U^(-1) cal(F)
  $
  which is supported on $q=0,2c-1$. Such a spectral sequence with only two rows induces a long exact sequence: 
  $
    0 &-> R^(2c-1) f_* f^(-1) cal(F) -> R^(2c-1) f_(U,*) f_U^(-1) cal(F) -> f_(X,*) f_X^(-1) cal(F)(-c) -->^(d^(2c)) dots.c \
      &-> R^(q-1) f_* f^(-1) cal(F) -> R^(q-1) f_(U,*) f_U^(-1) cal(F) -> R^(q-2c) f_(X,*) f_X^(-1) cal(F)(-c) -->^(d^(2c)) dots.c 
  $
  and isomorphisms: 
  $
    R^q f_* f^(-1) cal(F) cong R^q f_(U,*) f_U^(-1) cal(F), forall 0 <= q <= 2c-2
  $
  and we are done. 
]

#example[
  (Cohomology of affine smooth curve) We may finally compute the cohomology of an affine curve, not explicitly computed in @sect-cohom-of-curves. 
  
  Suppose that $k$ is an algebraically closed field, $n in k^times$ a natural number, and $X$ is an affine smooth curve over $k$. Then pick the completion $ol(X)$ of $X$, so $j: X -> ol(X)$ is an open immersion where $ol(X)$ is a projective smooth curve. Let $Z = ol(X) - X$ be equipped with the reduced induced structure, thus being a finite set of closed points over $k$. Now $Z, ol(X)$ are both smooth over $k$, so by @relative-purity, we have a Gysin sequence: 
  $
    0 &-> H^1 (ol(X), ul(ZZ\/n)) -> H^1 (X, ul(ZZ\/n)) -> H^0 (Z, ul(ZZ\/n)(-1)) -> H^2 (ol(X), ul(ZZ\/n)) -> 0
  $
  where $H^2 (X, ul(ZZ\/n))$ is killed by Artin vanishing. By unfolding the definitions, one can see that: 
  $
    H^0 (Z, ul(ZZ\/n)(-1)) cong (ZZ\/n(-1))^(oplus Z) -> ZZ\/n(-1) cong H^2 (ol(X), ul(ZZ\/n))
  $
  sends a copy of $ZZ\/n$ indexed by a point $z in Z$ to the corresponding divisor in $H^2 (ol(X), ul(ZZ\/n)) cong Pic(ol(X))\/n Pic(ol(X))$. It is thus identified with $(ZZ\/n(-1))^(oplus Z) -> ZZ\/n(-1)$ a sum over components indexed by $Z$. Thus, we have a short exact sequence: 
  $
    0 -> H^1 (ol(X), ul(ZZ\/n)) -> H^1 (X, ul(ZZ\/n)) -> (ZZ\/n (-1))^(oplus (m-1))
  $
  where $m = abs(Z) = abs(ol(X) - X)$ is the number of missing points in $X$. There is a non-canonical isomorphism: 
  $
    H^1 (ol(X), ul(ZZ\/n)) cong (ZZ\/n)^(oplus 2g(ol(X)))
  $
  by @cohom-of-proj-curve. Thus, there is a non-canonical isomorphism: 
  $
    H^1 (X, ul(ZZ\/n)) cong (ZZ\/n)^(oplus 2g(ol(X))+m-1)
  $
  We have thus computed the etale cohomology of an affine smooth curve: 
  $
    H^q (X, ul(ZZ\/n)) = cases(
      ZZ\/n &\, q = 0, 
      (ZZ\/n)^(oplus 2g(ol(X))+m-1) &\, q = 1, 
      0 &\, q >= 2
    )
  $
]
