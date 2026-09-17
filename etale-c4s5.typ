#import "void-import.typ": *

== Stalks <sect-stalks>

Let $Omega$ be a separably closed field. 

#lemma(name: <struct-of-spec-omega-et>)[
  0. There is an equivalence of categories: 
    $
      cSet -> Et_(Spec(Omega)), I |-> union.sq.big_(i in I) Spec(Omega)
    $

  + For any $cal(G) in cPSh(Spec(Omega)_et)$, #h(1fr)
    $
      cal(G) (Spec(Omega)) = cal(G)^\# (Spec(Omega))
    $
    and $cal(G)^\# (Spec(Omega))$ is the constant sheaf associated with $cal(G)(Spec(Omega))$. 

  + Taking global sections $Gamma (Spec(Omega), -)$ induces an equivalence of categories: 
    $
      cSh(Spec(Omega)_et) overset(->, tilde) cSet , cAb(Spec(Omega)_et) overset(->, tilde) cAb
    $
]
#proof[
  (0) Full faithfulness is evident, so we only prove essential surjectivity, i.e. every etale $X -> Spec(Omega)$ is a disjoint union of copies of $Spec(Omega)$. 
  
  For any etale $X -> Spec(Omega)$ and any point $x in X$, by definition $k(x)\/Omega$ is a finite separable extension. Since $Omega$ is separably closed, it can only be that $k(x) = Omega$. Thus, the inclusion $Spec(k(x)) -> X -> Spec(Omega)$ is an isomorphism, and so $Spec(k(x)) -> X$ is a closed immersion. Thus $x$ is a closed point of $X$ with residue field $Omega$. 

  On the other hand, fix $x in X$, let $U = Spec(A) subset X$ be any affine open around $x$. Then $U$ has only closed points. Since $A\/Omega$ is finite type, $A$ is noetherian. This combined with that $U$ has only closed points shows that $A$ is artinian. Thus $U$ is a finite discrete scheme, and so ${x}$ is an open subset of $U$, hence an open subset of $X$. 

  In other words, every point of $X$ is open and closed, and has residue field $Omega$. Thus, 
  $
    X cong union.sq.big_(x in X) Spec(Omega)
  $

  (1) By (0), any etale cover $cal(U) = {U_i -> Spec(Omega)}$ is (non-canonically) refined by the single etale cover $id: Spec(Omega) -> Spec(Omega)$, by factoring $Spec(Omega)$ through an arbitrary connected component $Spec(Omega)$ of an arbitrary $U_i$. In other words, the direct limit: 
  $
    cal(G)^+ (Spec(Omega)) = dircolim_(cal(U)) caron(H)^0 (cal(U), cal(G))
  $
  is taken over a directed system with a maximum object. There is thus a canonical isomorphism: 
  $
    cal(G)^+ (Spec(Omega)) cong caron(H)^0 ({id}, cal(G)) = cal(G) (Spec(Omega))
  $
  Taking $(-)^+$ twice, we see that $cal(G)^\# (Spec(Omega)) = cal(G) (Spec(Omega))$. 

  (2) From (0), we see that every etale sheaf $cal(G)$ over $Spec(Omega)$ is determined by its sections on $Spec(Omega)$, since its sections on $union.sq.big_(i in I) Spec(Omega)$ is just $product_(i in I) Gamma(Spec(Omega), cal(G))$. In other words, every etale sheaf on $Spec(Omega)$ is a constant sheaf. The equivalence of categories is thus evident. 
]

#definition(name: <defn-etale-stalk>)[
  For a geometric point $overline(x): Spec(Omega) -> X$, we define the *stalk* at $overline(x)$ to be: 
  $
    (-)_(overline(x)): cSh(X_et) &overset(->, overline(x)^(-1)) cSh(Spec(Omega)_et) overset(->, tilde) cSet, cAb(X_et) overset(->, overline(x)^(-1)) cAb(Spec(Omega)_et) overset(->, tilde) cAb \
    
    cal(F) &|-> cal(F)_(overline(x)) := (overline(x)^(-1) cal(F)) (Spec(Omega))
  $
  #remark[
    The notion of points and stalks may be defined over arbitrary sites. However, the etale site has enough points, and injectivity/surjectivity can be detected by stalks, which is a phenomenon that doesn't happen in an arbitrary site. 
  ]
]

#properties(name: <stalks-first-props>)[
  + $(-)_(overline(x))$ commutes with finite limits. Consequently, $(-)_(overline(x)): cAb(X_et) -> cAb$ is exact. 

  + $cal(F)_(ol(x))$ may be expressed as a filtered colimit: #h(1fr)
    $
      cal(F)_(overline(x)) = dircolim_(phi: (U, ol(u)) -> (X, ol(x))) cal(F)(U)
    $
    taken over $U in Et_X$ with a geometric point $ol(u)$ mapping to $ol(x)$, i.e. an *etale neighborhood* of $ol(x)$. 

  + Given a pointed morphism $f: (X, overline(x)) -> (Y, overline(y))$, there is a canonical isomorphism $(f^(-1) cal(G))_(overline(x)) cong cal(G)_(overline(y))$. 
]
#proof[
  (1) This follows from corresponding properties for $ol(x)^(-1)$. 

  (2) This follows from directly unfolding the definition of $ol(x)^(-1)_cPSh$, where to compute $ol(x)^(-1)_cPSh cal(F) (Spec(Omega))$, we have a filtered colimit taken over all diagrams of the shape: 
  // https://q.uiver.app/#r=typst&q=WzAsNCxbMCwwLCJTcGVjKE9tZWdhKSJdLFswLDEsIlNwZWMoT21lZ2EpIl0sWzEsMCwiVSJdLFsxLDEsIlgiXSxbMSwzLCJvbCh4KSIsMl0sWzAsMiwib2wodSkiXSxbMiwzXSxbMCwxXV0=
  #align(center, diagram({
    node((-1, -1), [$Spec(Omega)$])
    node((-1, 0), [$Spec(Omega)$])
    node((0, -1), [$U$])
    node((0, 0), [$X$])
    edge((-1, 0), (0, 0), [$ol(x)$], label-side: right, "->")
    edge((-1, -1), (0, -1), [$ol(u)$], label-side: left, "->")
    edge((0, -1), (0, 0), "->")
    edge((-1, -1), (-1, 0), "=")
  }, spacing: 2em))
  which is just over all etale neighborhoods of $(X, ol(x))$. Now, 
  $
    ol(x)^(-1) cal(F) (Spec(Omega)) = (ol(x)^(-1)_cPSh cal(F))^\# (Spec(Omega)) = ol(x)^(-1)_cPSh cal(F) (Spec(Omega))
  $
  as proved before. 

  (3) This follows from $ol(x)^(-1) compose f^(-1) = (f compose ol(x))^(-1) = ol(y)^(-1)$. 
]

#definition(name: <defn-germs-and-support>)[
  Let $cal(F) in cSh(X_et)$, $U in Et_X$ and $ol(u)$ be a geometric point of $U$. Then $(U, ol(u))$ is an etale neighborhood of $(X, ol(u))$, thus inducing a natural morphism: 
  $
    (-)_(ol(u)): cal(F)(U) -> cal(F)_(ol(u))
  $
  For a section $s in cal(F)(U)$, $s_(ol(u))$ is called the *germ* of $s$ at $ol(u)$. It is evident that this construction is compatible with restriction (by unfolding the definition of the filtered colimit for $cal(F)_(ol(u))$). 

  The *support* of $s in cal(F)(U)$ is defined to be the set: 
  $
    supp(s) := {u in U: exists#[a geometric point $ol(u)$ above $u$ s.t. $s_(ol(u)) != 0$]}
  $
]

We state the rest of this section in terms of $cAb(X_et)$ only. You should keep in mind that analogs of these results exist for $cSh(X_et)$, but in this course we mainly deal with sheaves of abelian groups. 

#lemma(name: <vanishing-stalks-spreads-out>)[
  Let $cal(F) in cAb(X_et)$, $s in cal(F)(U)$ and $ol(u)$ be a geometric point of $U$ lying above $u in U$ s.t. $s_(ol(u)) = 0$. Then there exists a Zariski neighborhood $u in V subset U$ s.t. $s|_V = 0$. 

  In particular, 
  $
    supp(s) &= {u in U: exists#[a geometric point $ol(u)$ above $u$ s.t. $s_(ol(u)) != 0$]} \
    &= {u in U: forall#[geometric points $ol(u)$ above $u$, $s_(ol(u)) != 0$]} subset U
  $
  is a closed subset of $U$. 
  // Consequently, if there exists a subset $E subset U$ intersecting every nonempty closed subset of $U$
]
#proof[
  Since $cal(F)_(ol(u))$ has the filtered colimit structure: 
  $
    cal(F)_(ol(u)) = dircolim_((V,ol(v)) -> (X,ol(u))) cal(F)(V)
  $
  The image of $s in cal(F)(U)$ in this filtered colimit is $0$ means that there exists an etale neighborhood $phi: (W, ol(w)) -> (U, ol(u))$ s.t. $s|_W = 0$. Now $phi(W)$ is an open subset of $U$ containing $u$, and $phi: W -> phi(W)$ is surjective etale, hence an etale cover of $phi(W)$. Thus, 
  $
    s|_W = (s|_(phi(W)))|_W = 0
  $
  and so by the sheaf conditions, $s|_(phi(W)) = 0$. Taking $V = phi(W)$ concludes the proof. 

  For the condition on $supp(s)$, note that if $u in U - supp(s)$, then $s|_V = 0$ for a Zariski neighborhood $V$ of $u in U$. Thus for all geometric points $ol(v)$ above a point of $V$, $s_(ol(v)) = 0$. Hence, the existential quantifier on $ol(u)$ in the definition of $supp(s)$ may be replaced by the universal quantifier, and $V subset U - supp(s)$. Thus $U - supp(s)$ is an open subset of $U$, making $supp(s) subset U$ closed.  
]

#proposition(name: <stalks-detects-properties>)[
  0. Given $cal(F) in cAb(X_et)$ and two geometric points $ol(x)_1, ol(x)_2$ of $X$ lying above the same point $x in X$, there exists a non-canonical isomorphism: 
    $
      cal(F)_(ol(x)_1) cong cal(F)_(ol(x)_2)
    $

  + Given $cal(F) in cAb(X_et)$, the following are equivalent: 
    + $cal(F) = 0$; 
    + $cal(F)_(ol(x)) = 0$ for every geometric point $ol(x)$ of $X$; 
    + There exists a subset $E subset X$ intersecting every nonempty locally closed subset of $X$, and for each $x in E$ some geometric point $ol(x)$ of $X$ lying above $x$ s.t. $cal(F)_(ol(x)) = 0$. 

  + Taking stalks commutes with kernels, cokernels and images. 

  + The following are equivalent: 
    + A morphism $cal(F) -> cal(G)$ of etale sheaves on $X$ is injective/surjective/isomorphism/zero, or $cal(F) -> cal(G) -> cal(H)$ is exact in the middle. 
    + The same condition holds for $cal(F)_(ol(x)) -> cal(G)_(ol(x))$ or $cal(F)_(ol(x)) -> cal(G)_(ol(x)) -> cal(H)_(ol(x))$ for every geometric point $ol(x)$ of $X$; 
    + There exists a subset $E subset X$ intersecting every nonempty locally closed subset of $X$, and for each $x in E$ some geometric point $ol(x)$ of $X$ lying above $x$ s.t. the same condition holds for $cal(F)_(ol(x)) -> cal(G)_(ol(x))$ or $cal(F)_(ol(x)) -> cal(G)_(ol(x)) -> cal(H)_(ol(x))$. 
]
#proof[
  (0) Let $ol(x) = Spec(k(x)^sep)$ be a separable closure of $k(x)$ as a geometric point above $x$. It suffices to show that $cal(F)_(ol(x)) cong cal(F)_(ol(x)_1)$. 

  Indeed, let $ol(x)_1: Spec(Omega) -> X$. Since $Omega$ contains $k(x)$ and is separably closed, we may choose a non-canonical embedding $k(x)^sep -> Omega$ over $k(x)$. This gives a factorization $ol(x)_1: Spec(Omega) ->^(ol(xi)) Spec(k(x)^sep) ->^(ol(x)) X$. Now: 
  $
    (ol(x)^(-1) cal(F))_(ol(xi)) = cal(F)_(ol(x_1))
  $
  while $ol(x)^(-1) cal(F)$ is the constant sheaf associated with $cal(F)_(ol(x))$, hence has stalk $cal(F)_(ol(x))$ at any geometric point. 

  (2) follows from exactness of $(-)_(ol(x))$. Consider a map $f: cal(F) -> cal(G)$. We may then form an exact sequence: 
  $
    0 -> ker(f) -> cal(F) ->^f cal(G) -> coker(f) -> 0
  $
  Taking stalks at $ol(x)$, we then get an exact sequence: 
  $
    0 -> ker(f)_(ol(x)) -> cal(F)_(ol(x)) ->^(f_(ol(x))) cal(G)_(ol(x)) -> coker(f)_(ol(x)) -> 0
  $
  This shows that $ker(f)_(ol(x)) = ker(f_(ol(x)))$ and $coker(f)_(ol(x)) = coker(f_(ol(x)))$. The image is the kernel of cokernel, and hence also commutes with taking stalks. 

  (1) (a)$==>$(b)$==>$(c) is obvious, so we only prove that (c)$==>$(a). 

  Given any $(f: U -> X) in Et_X$ and any section $s in cal(F)(U)$, we would like to prove that $s = 0$. We additionally assume that $U$ is affine and $f(U)$ is contained in an affine open of $X$. Suppose that $s != 0$. Let $Z = supp(s) subset U$, which is a closed subset of $U$. Since $s != 0$, $Z$ must be nonempty. 

  Let $X_0$ be an affine open of $X$ containing $f(U)$, so that $f$ factors as $f: U ->^(f_0) X_0 -> X$. Now $f_0$ is affine (hence quasi-compact), and of finite presentation. By Chevalley's theorem (say the version in #cite-stacks("054K", [Theorem 29.22.3])), $f(Z)$ is a nonempty constructible subset of $X_0$. It thus contains a nonempty locally closed subset of $X_0$, hence a nonempty locally closed subset of $X$. 

  By our assumption on $E$, there exists $x in E$ s.t. $x in f(Z)$. Pick any geometric point $ol(x)$ above $x$ and (by (0)) $cal(F)_(ol(x)) = 0$, and any $z in Z$ s.t. $x = f(z)$. Since $f$ is etale, there exists a geometric point $ol(z)$ above $z$ s.t. $ol(x) = f(ol(z))$. Then $s_(ol(z)) != 0$ is an element of $cal(F)_(ol(x)) = 0$, a contradiction. 

  In other words, for any affine $U in Et_X$ whose image in $X$ is contained in an affine open, $cal(F)(U) = 0$. Since any $U in Et_X$ can be covered by sufficiently small affine opens satisfying this condition, using the sheaf conditions, $cal(F)(U) = 0$ for all $U in Et_X$. Hence $cal(F) = 0$. 

  (3) is simply (1) and (2) combined. 
]
#remark(name: <very-dense-sets-of-pts>)[
  The condition of a subset $E subset X$ intersecting with every nonempty locally closed subset is called *very dense*. Common examples of very dense subsets include: 

  + Trivially, $E = X$; 

  + A point $x in X$ is *of finite type* if $x: Spec(k(x)) -> X$ is a morphism of finite type. The subset of finite type points of $X$ is always very dense in $X$. (#cite-stacks("02J4", [Lemma 29.16.7]))

  + A scheme is called *Jacobson* if its closed points are very dense, or equivalently every finite type point is closed. (#cite-stacks("01TB", [Lemma 29.16.8])) In a Jacobson scheme, taking $E$ to be the set of closed points would work. 

    Common examples of Jacobson schemes include schemes of finite type over a field or over a 1-dimensional noetherian domain with infinitely many primes (such as the ring of integers of a number field, in particular $ZZ$). (#cite-stacks("02J6", [Lemma 29.16.10])) 
    
    A famous non-example of a Jacobson scheme is the spectrum of a DVR. 
]

#corollary[
  A chain complex $0 -> cal(F) -> cal(G) -> cal(H)$ in $cAb(X_et)$ is left exact, if and only if for every $U in Et_X$, 
  $
    0 -> cal(F)(U) -> cal(G)(U) -> cal(H)(U)
  $
  is left exact. Furthermore, one can check this only for affine $U in Et_X$ whose image is contained in an affine open of $X$. 
]
#proof[
  ($==>$) is left exactness of $Gamma(U, -)$, which we proved in @sections-left-exact. 

  For ($<==$), we only need to prove that for every geometric point $ol(x)$, the sequence on stalks: 
  $
    0 -> cal(F)_(ol(x)) -> cal(G)_(ol(x)) -> cal(H)_(ol(x))
  $
  is left exact. Writing stalks as filtered colimits, this is: 
  $
    0 -> dircolim_((U,ol(u)) -> (X, ol(x))) cal(F)(U) -> dircolim_((U,ol(u)) -> (X, ol(x))) cal(G)(U) -> dircolim_((U,ol(u)) -> (X, ol(x))) cal(H)(U)
  $
  which is a filtered colimit of the left exact sequences $0 -> cal(F)(U) -> cal(G)(U) -> cal(H)(U)$. However, $cAb$ satisfies the (Ab5) condition that filtered colimits are exact, so we are done. 

  Since every etale neighborhood of $(X, ol(x))$ is refined by some $(V, ol(v))$ s.t. $V$ is affine and has image in $X$ contained in an affine open of $X$, our further statement is justified. 
]

#corollary(name: <surjective-pullback-conservative>)[
  For any surjective morphism $f: X -> Y$ of schemes, $f^(-1): cAb(Y_et) -> cAb(X_et)$ is a conservative functor. That is, any morphism $phi: cal(F) -> cal(G)$ in $cAb(Y_et)$ is injective/surjective/isomorphism/zero, if and only if the same holds for $f^(-1) phi: f^(-1) cal(F) -> f^(-1) cal(G)$. 
]
#proof[
  ($==>$) is exactness of $f^(-1)$, so we verify ($<==$) only. It suffices to show that for every $y in Y$, there exists a geometric point $ol(y)$ above $y$ s.t. $cal(F)_(ol(y)) -> cal(G)_(ol(y))$ is injective/surjective/isomorphism/zero. Since $f$ is surjective, we may pick $x in X$ s.t. $f(x) = y$. Pick any geometric point $ol(x)$ above $x$, and take $ol(y) = f(ol(x))$ to be a geometric point above $y$. Since $f^(-1) phi: f^(-1) cal(F) -> f^(-1) cal(G)$ is injective/surjective/isomorphism/zero, the same property holds for $(f^(-1) cal(F))_(ol(x)) -> (f^(-1) cal(G))_(ol(x))$, which is just $cal(F)_(ol(y)) -> cal(G)_(ol(y))$ by @stalks-first-props (3). We are thereby done. 
]

#example[
  There are two important exact sequences of etale sheaves on a scheme $X$: 

  - If a positive integer $n in cal(O)_X (X)^times$, one has the *Kummer sequence*: #h(1fr)
    $
      0 -> mu_n arrow.r.hook GG_m -->^(x |-> x^n) GG_m -> 0
    $
    Recall that $mu_n (U) = mu_n (cal(O)_U (U))$ are the $n$-th roots of unity in $cal(O)_U (U)$, and $GG_m (U) = cal(O)_U (U)^times$ are the units of $cal(O)_U (U)$. This sequence is left exact, since it is evidently left exact on sections: 
    $
      0 -> mu_n (cal(O)_U (U)) -> cal(O)_U (U)^times -->^(x |-> x^n) cal(O)_U (U)^times 
    $
    It remains to show that $GG_m -->^(x |-> x^n) GG_m$ is surjective, a result specific to etale sheaves that fails for Zariski sheaves. We need to show that for any $s in cal(O)_U (U)^times$, there exists an etale cover of $U$ s.t. $s$ has an $n$-th root in each piece. For this, we take the *Kummer covering*: 
    $
      U' = SPec((cal(O)_U [T])/((T^n - s)))
    $
    which is a finite etale covering of $U$. Recall that it is etale, since $(T^n - s)' = n T^(n-1)$ where $n in cal(O)_X^times$ and so $n in cal(O)_U^times$, and so $gcd(T^n - s, n T^(n-1)) = 1$. 

    Now $s|_(U') = T^n$, and we are done. 

  - If $p$ is a prime and $X$ is a scheme over $FF_p$, we have the Artin-Schreier sequence: 
    $
      0 -> ul(ZZ\/p) arrow.r.hook GG_a -->^(x |-> x^p - x) GG_a -> 0 
    $
    The morphism $ul(ZZ\/p) -> GG_a$ here is obtained by sheafifying the presheaf morphism defined by the inclusions $FF_p arrow.r.hook cal(O)_U (U)$ for each $U in Et_X$. It is thus injective since sheafification is exact. For each affine $U = Spec(A) in Et_X$, the left part of the sequence on sections on $U$ is: 
    $
      0 -> C(U; ZZ\/p) -> A -->^(x |-> x^p - x) A 
    $
    By unfolding the definitions, the first morphism is defined in the following way: Given a locally constant function $f: U -> ZZ\/p$, $f^(-1)(a)$ for $a in FF_p$ partitions $U = Spec(A)$ into $p$ closed and open sets. This corresponds to a system ${e_a}_(a in FF_p)$ of orthogonal idempotents of $A$. This morphism is then: 
    $
      C(U; ZZ\/p) -> A, f |-> sum_(a in FF_p) e_a a
    $
    Suppose that $x in A$ s.t. $x^p - x = 0$, i.e. $product_(a in FF_p) (x-a) = 0$. Now ${x-a}_(a in FF_p)$ are pairwise coprime with product $0$, so by Chinese remainder theorem, we have an isomorphism: 
    $
      A cong product_(a in FF_p) A\/(x-a)
    $
    In other words, there is a system of orthogonal idempotents ${e_a}_(a in FF_p)$ s.t. $e_a = 1 mod (x-a)$ and $0 mod (x-b)$ for $a != b in FF_p$. Now $x$ corresponds to $a$ on $A\/(x-a)$, so $x$ is sent to $(0, 1, dots.c, p-1)$ under this isomorphism, and hence $x = sum_(a in FF_p) e_a a$ comes from an element of $C(U; ZZ\/p)$. 

    In other words, $0 -> C(U; ZZ\/p) -> A -->^(x |-> x^p - x) A$ is left exact. Hence, $0 -> ul(ZZ\/p) arrow.r.hook GG_a -->^(x |-> x^p - x) GG_a$ is left exact, and it remains to show that $GG_a -->^(x |-> x^p - x) GG_a$ is surjective. 

    For this, we use the same strategy as in the Kummer sequence, but in this case, for $s in cal(O)_U (U)$, we use the *Artin-Schreier* covering, a finite etale covering: 
    $
      U' = Spec((cal(O)_U [T])/((T^p - T - s)))
    $
]

Finally, there is this alternative method of proving that $cAb(X_et)$ has enough injectives, that we promised earlier. 

#example[
  Let $ol(x)$ be a geometric point of $X$, and $M in cAb$. We may regard $M$ as a constant sheaf in $cAb(ol(x)_et)$, and push it forward to $ol(x)_* M in cAb(X_et)$. This sheaf is called the *skyscraper sheaf* associated with $M$ at $ol(x)$. //It is easy to check that the canonical map $ol(x)^(-1) ol(x)_* M -> M$ is an isomorphism, i.e. $(ol(x)_* M)_(ol(x)) = M$.

  The stalks of a skyscraper sheaf can be hard to compute explicitly, but at least we know where it vanishes: 
  #lemma(name: <stalks-of-skyscraper-sheaves>)[
    Let $ol(y)$ be a geometric point of $X$. Then if $x$ does not generalize $y$, then $(ol(x)_* M)_(ol(y)) = 0$. 
  ]
  #proof[
    If $x$ does not generalize $y$, pick a Zariski open $V subset X$ s.t. $y in V, x in.not V$. For any etale neighborhood $(U, ol(u)) -> (X, ol(y))$, if the image of $U$ in $X$ does not contain $x$, then $ol(x)_* M (U) = ul(M)_(ol(x)) (U_(ol(x))) = 0$. However, any etale neighborhood $(U, ol(u)) -> (X, ol(y))$ is refined by $(U times_X V, ol(u))$, whose image in $X$ does not contain $x$, so the filtered colimit defining the stalk is $0$. 
  ]
  
  Given any sheaf $cal(F) in cAb(X_et)$, given a morphism $cal(F)_(ol(x)) -> M$, i.e. a morphism $ol(x)^(-1) cal(F) -> M$, there exists a unique morphism $cal(F) -> ol(x)_* M$ inducing this morphism by adjunction. 
]

#construction(name: <injective-godement-resolution>)[
  (Injective Godement resolution) There is another way of proving that $cAb(X_et)$ has enough injectives, that does not use Grothendieck's Tohoku theorem, that has the advantage of being explicit and functorial. This is the Godement resolution. 

  Firstly, we recall that in $cAb$, an arbitrary object may be embedded into an injective object via: 
  $
    M -> I(M) := product_(chi in Hom(M, QQ\/ZZ)) QQ\/ZZ, x |-> (chi(x))_chi
  $
  and this construction is functorial in $M$. 

  For each $x in X$, choose a geometric point $ol(x)$ above $x$. //Now $ol(x)^(-1)cal(F)$ is just $cal(F)_(ol(x)) in cAb cong cAb(ol(x)_et)$, and thus embeds into $I(cal(F)_(ol(x))) in cAb cong cAb(ol(x)_et)$. This defines a morphism $ol(x)^(-1) cal(F) -> I(cal(F)_(ol(x)))$, hence a morphism $cal(F) -> ol(x)_* I(cal(F)_(ol(x)))$ by adjunction. 
  From the inclusions $cal(F)_(ol(x)) -> I(cal(F)_(ol(x)))$, we obtain morphisms $cal(F) -> ol(x)_* I(cal(F)_(ol(x)))$ to the skyscraper sheaf. 

  Passing to the direct product, this defines a morphism: 
  $
    gamma: cal(F) -> product_(x in X) ol(x)_* I(cal(F)_(ol(x)))
  $

  // On each geometric point $ol(x)$, $gamma$ induces a morphism $cal(F)_(ol(x)) -> I(cal(F)_(ol(x))) times dots.c$ on stalks, and is injective. Thus, $gamma$ is an injective morphism. $ol(x)_*$ has an exact left adjoint and hence preserves injectives, so $product_(x in X) ol(x)_* I(cal(F)_(ol(x)))$ is a direct product of injective objects, and is hence injective. 

  // This constructs an explicit embedding of $cal(F)$ into an injective object. This construction is functorial, and is canonical except for a choice#footnote[...which is not a big deal as long as you accept the axiom of choice.] of geometric points ${ol(x)}_(x in X)$.

  We claim that this morphism is injective. Indeed, given any $(f: U -> X) in Et_X$, we want to show that: 
  $
    cal(F)(U) -> product_(x in X) (ol(x)_* I (cal(F)_(ol(x))))(U) = product_(x in X) product_(ol(u) in f^(-1)(ol(x))) cal(F)_(ol(x))
  $
  is injective. If $s in cal(F)(U)$ is sent to zero, then for every $ol(u) in f^(-1)(ol(x))$, the germ $s_(ol(u)) = 0$. Every point of $U$ has a geometric point $ol(u)$ of this shape lying above it, so by @vanishing-stalks-spreads-out, $s = 0$. Thus, $gamma$ is injective. 
]

Other than this injective Godement resolution, there is in fact an acyclic Godement resolution: 

#lemma(name: <geom-point-pushforward-exact>)[
  Let $ol(x): Spec(Omega) -> X$ be a geometric point. Then $ol(x)_*$ is an exact functor.
]
#proof[
  Recall that $cAb(Spec(Omega)_et) cong cAb$ by @struct-of-spec-omega-et. Now given an exact sequence of abelian groups:
  $
    0 -> A -> B -> C -> 0
  $
  consider the sequence after $ol(x)_*$:
  $
    0 -> ol(x)_* A -> ol(x)_* B -> ol(x)_* C -> 0
  $
  When viewed on sections on $(f: U -> X) in Et_X$, this is:
  $
    0 -> product_(ol(u) in f^(-1)(ol(x))) A -> product_(ol(u) in f^(-1)(ol(x))) B -> product_(ol(u) in f^(-1)(ol(x))) C -> 0
  $
  which is exact, as a direct product of exact sequences $0 -> A -> B -> C -> 0$. Thus $0 -> ol(x)_* A -> ol(x)_* B -> ol(x)_* C -> 0$ is exact.
]

#proposition(name: <acyclic-godement-resolution>)[
  For any scheme $X$, fix a system of geometric points ${ol(x)}$ above each $x in X$. For any $cal(F) in cAb(X_et)$,
  $
    cal(C)^0 (cal(F)) := product_(x in X) ol(x)_* cal(F)_(ol(x))
  $
  satisfies that the canonical map $cal(F) -> cal(C)^0 (cal(F))$ induced by adjunction between $ol(x)_*$ and $ol(x)^(-1)$ is injective, and is acyclic in the sense that:
  $
    H^q (X, cal(C)^0 (cal(F))) = 0, forall q >= 1
  $
  Thus, taking $cal(C)^1 (cal(F)) = cal(C)^0 (coker(cal(F) -> cal(C)^0 (cal(F))))$ and so on, we have inductively constructed an acyclic resolution:
  $
    0 -> cal(F) -> cal(C)^0 (cal(F)) -> cal(C)^1 (cal(F)) -> dots.c -> cal(C)^p (cal(F)) -> dots.c
  $
  functorial in $cal(F)$.
]
#proof[
  For acyclicity, we use the Leray spectral sequence @derived-lower-star-first-props (2) and exactness of $ol(x)_*$ proved above. Since $R^q ol(x)_* = 0$ for $q >= 1$ by exactness of $ol(x)_*$, the spectral sequence:
  $
    H^p (X, R^q ol(x)_* A) ==> H^(p+q) (ol(x), A)
  $
  degenerates, giving isomorphisms:
  $
    H^q (X, ol(x)_* A) cong H^q (ol(x), A) = 0
  $
  for all $q >= 1$. Thus, $cal(C)^0 (cal(F))$ as a direct product of sheaves of the shape $ol(x)_* A$ is acyclic.
  
  Next, we show that the natural map:
  $
    gamma: cal(F) -> cal(C)^0 (cal(F)) = product_(x in X) ol(x)_* cal(F)_(ol(x))
  $
  is injective. This is the same proof as in @injective-godement-resolution. Indeed, given any $(f: U -> X) in Et_X$, we want to show that:
  $
    cal(F)(U) -> product_(x in X) (ol(x)_* cal(F)_(ol(x)))(U) = product_(x in X) product_(ol(u) in f^(-1)(ol(x))) cal(F)_(ol(x))
  $
  is injective. If $s in cal(F)(U)$ is sent to zero, then for every $ol(u) in f^(-1)(ol(x))$, the germ $s_(ol(u)) = 0$. Every point of $U$ has a geometric point $ol(u)$ of this shape lying above it, so by @vanishing-stalks-spreads-out, $s = 0$. Thus, $gamma$ is injective.
]

The advantage of this acyclic Godement resolution is that, if $cal(F)$ is $n$-torsion, then so are its stalks, and so $cal(C)^0 (cal(F))$ is $n$-torsion. This may make some results that only work for torsion sheaves applicable.
