#import "void-import.typ": *

== Constructible sheaves

In this section, we introduce constructible sheaves. Constructible sheaves are a suitable class of torsion sheaves whose structure is mild and whose study is more tractable than that of arbitrary torsion sheaves, which might vary wildly. In a sense, being constructible is a reasonable finiteness condition on a sheaf: an intermediate layer between a constant sheaf $ul(ZZ\/n)$ and an arbitrary torsion sheaf. Much of the further theory of etale cohomology is centered on constructible sheaves (and a more restricted class of them, namely local systems). 

The mechanism of constructible sheaves will debut in the proof of proper base change, demonstrating their power through a devissage argument, by reducing general torsion sheaves to them via limit formula for sheaves, and by reducing them to constant sheaves $ul(ZZ\/n)$ up to a finite morphism, effectively reducing results on general torsion sheaves to results on $ul(ZZ\/n)$. 

For simplicity, in this section, we assume that $X$ is a noetherian scheme. $Lambda$ will denote a coefficient ring, which is always noetherian. 

/*
#definition[
  Given a $X$-scheme $X'$, recall that there exists an etale sheaf in $cSh(X_et)$ defined by: 
  $
    Et_X -> cSet, U |-> Hom_X (U, X')
  $
  according to @examples-of-etale-sheaves. If $X'$ is additionally equipped with the structure of an abelian group scheme over $X$, this defines an abelian sheaf in $cAb(X_et)$. 

  This sheaf is denoted by $h_(X')$ or $tilde(X')$. 
]

#example[
  For a finite abelian group $G$, we denote:
  $
    G_X = union.big_(g in G) X
  $
  to be a finite etale $X$-group scheme. Then it represents the constant sheaf $ul(G)$ on $X_et$. Indeed, it sends $U in Et_X$ to $Hom_X (U, G_X)$, which is the space of continuous (i.e. locally constant) functions $X -> G$. This is compatible with our characterization of $ul(G)$. We write: 
  $
    ul(G) = tilde(G_X)
  $
  to denote this. 
]*/

#definition(name: <defn-locally-constant-and-lcc-sheaves>)[
  An etale sheaf $cal(F)$ of abelian groups (resp. sets; resp. $Lambda$-modules) on a noetherian scheme $X$ is called *locally constant*, if there exists an etale cover $cal(U) = {U_i -> X}$ s.t. each $cal(F)|_(U_i)$ is a constant sheaf. 

  An etale sheaf $cal(F)$ of $Lambda$-modules (resp. sets; resp. abelian groups) is called #furi[locally constant constructible][*l.c.c.*] if $cal(F)$ is locally constant, and its stalks are finite $Lambda$-modules (resp. finite sets; resp. finite abelian groups). 

  In other words, a l.c.c. etale sheaf of abelian groups is an l.c.c. etale sheaf of $ZZ$-modules that is a torsion sheaf, or equivalently an l.c.c. etale sheaf of $ZZ\/n$-modules for some $n$. 

  When we simply say a *l.c.c. sheaf*, we refer to a l.c.c. sheaf of abelian groups. 
]

#definition(name: <defn-specialization-morphism>)[
  Given a geometric point $ol(x)$ of $X$, a *generalization* of $ol(x)$ is a geometric point $ol(eta)$ of $tilde(X)_(ol(x))$. We also denote by $ol(eta)$ the image of $ol(eta)$ under $tilde(X)_(ol(x)) -> X$. 

  Let $cal(F) in cAb(X_et)$ or $cSh(X_et)$. Given $ol(eta)$ generalizing $ol(x)$, the *specialization morphism* is defined as the morphism: 
  $
    sp_(ol(x),ol(eta)): cal(F)_(ol(x)) = Gamma(tilde(X)_(ol(x)), cal(F)|_(tilde(X)_(ol(x)))) -> Gamma(tilde(X)_(ol(eta)), cal(F)|_(tilde(X)_(ol(eta)))) = cal(F)_(ol(eta))
  $
  identified as the restriction of global sections, where $tilde(X)_(ol(eta)) = (tilde(X)_(ol(x)))^tilde_(ol(eta)) -> tilde(X)_(ol(x))$. 

  #remark[
    By unfolding the definitions and the isomorphisms in limit formulas, we see that: 

    - $ol(eta) -> tilde(X)_(ol(x))$ induces functorially for every etale neighborhood $(U, ol(u))$ a geometric point $ol(v)$ of $U$, lying above $ol(eta) -> X$. This gives a functor: 
      $
        (U, ol(u)) |-> (U, ol(v))
      $
      from pointed etale neighborhoods of $ol(x)$ to those of $ol(eta)$. 

    The specialization map can thus be constructed from the limits: 
    $
      cal(F)_(ol(x)) = dirlim_((U,ol(u)) -> (X,ol(x))\ #[etale]) cal(F)(U) -> dirlim_((U,ol(v)) -> (X,ol(eta))\ #[etale]) cal(F)(U) = cal(F)_(ol(eta))
    $
    sending each $cal(F)(U)$ for $(U,ol(u))$ to the $cal(F)(U)$ for the respective $(U,ol(v))$. 
  ]
]

#notation(name: <representable-etale-sheaf>)[
  Recall that for every $X$-scheme $Y$, there is a sheaf of sets represented by $Y$: 
  $
    Et_X^opp -> cSet, Z |-> Hom_X (Z, Y)
  $
  This sheaf is denoted by $h_Y$. 

  For example, for a set $G$, the constant sheaf $ul(G)$ is represented by $X times G = union.big_(g in G) X$, the disjoint union of copies of $X$ indexed by $G$. Thus, we may write: 
  $
    ul(G)_X cong h_(X times G)
  $
]

#lemma(name: <descs-of-lcc-sheaves-of-sets>)[
  #set enum(numbering: "(a)")
  For $cal(F) in cSh(X_et)$ a sheaf of sets, TFAE:
  
  + $cal(F) cong h_Y$ is represented by a finite etale covering $Y in Et_X$;
  
  + $cal(F)$ is l.c.c; //There exists an etale cover ${U_i -> X}_i$ s.t. $cal(F)|_(U_i) cong h_(U_i times G_i) = ul(G_i)_(U_i)$ for some finite sets $G_i$.
  
  + For each connected component $X_0$ of $X$, there exists a finite etale covering space $U_0 -> X_0$ and a finite set $G$ s.t. $cal(F)|_(U_0) cong ul(G)_(U_0)$.
]
#proof[
  By arguing on each connected component of $X$, we may assume that $X$ is connected. 

  (c)$==>$(b) is tautological.
  
  (b)$==>$(a): //We may assume that $X$ is affine (for we can cover general $X$ by open affines ${V_i}$. If for each $i$, we may find $V'_i -> V_i$ representing $cal(F)$, then since $cal(F)|_(V_i)|_(V_i ∩ V_j) cong cal(F)|_(V_j)|_(V_i ∩ V_j)$ canonically, the representing schemes $V'_i, V'_j$ glues.), that $X$ is connected, and assume that ${U_i -> X}$ is a finite family with each $U_i$ affine connected. Then $U = union.sq.big_(i \ "finite") U_i -> X$ is an fpqc cover.
  //
  //By our assumption, $cal(F)|_U = tilde(G_U)$. Now consider $p_(1,2): U times_X U arrows.rr U$, with isomorphism $p_2^(-1) (cal(F)|_U) cong cal(F)|_(U times_X U) cong p_1^(-1) (cal(F)|_U)$ gives $eta: p_2^(-1) G_U -> p_1^(-1) G_U$ on $U times_X U$, satisfying the cocycle conditions. Thus it descneds to the desired etale covering $X' -> X$. (Finiteness and etaleness is preserved by fpqc descent.)
  On each $U_i$, $cal(F)|_(U_i) cong h_(G_i times U_i)$. Now we have isomorphisms $cal(F)|_(U_i)|_(U_(i,j)) cong cal(F)|_(U_j)|_(U_(i,j))$ for $U_(i,j) = U_i times_X U_j$, hence isomorphisms of finite etale coverings of $U_(i,j)$:
  $
    U_(i,j) times G_i cong U_(i,j) times G_j
  $
  satisfying the cocycle condition. 

  In other words, $union.sq.big_i (U_i times G_i)$ is a finite etale coverings over $union.sq.big_i U_i -> X$, equipped with a transition isomorphism satisfying the cocycle condition. By fpqc descent of relatively affine schemes (@fpqc-descent-of-relatively-affine-schemes), it comes from base changing a scheme $X' -> X$ along $union.sq.big_i U_i -> X$, which is finite and etale by @fpqc-descent-of-properties (2)(5). 

  Now that we have compatible isomorphisms $cal(F)|_(U_i) cong h_(X' times_X U_i)$, we have obtained an isomorphism: 
  $
    cal(F) cong h_(X')
  $
  
  (a)$==>$(c): Suppose that $cal(F) = h_(X')$ for a finite etale covering $X'$. Note that for any $U in Et_X$: 

  $
    h_(X')|_(U)(Y) = Hom_X (Y, X') = Hom_U (Y, X' times_X U)
  $
  In other words, $h_(X')|_U = h_(X' times_X U)$. Thus, it suffices to find a finite etale covering $Z -> X$ s.t. $X' times_X Z$ is a trivial covering of $Z$. We are done by @fet-trivializes-fet-locally. 
]

#lemma(name: <descs-of-lcc-sheaves>)[
  #set enum(numbering: "(a)")
  Let $Lambda$ be a noetherian ring. For an etale sheaf $cal(F)$ of $Lambda$-modules (resp. abelian groups) whose stalks are finite $Lambda$-modules (resp. finite abelian groups), TFAE:
  
  + $cal(F)$ is locally constant, hence l.c.c;

  + All specialization morphisms of $cal(F)$ are isomorphisms; 
  
  // + There exists an etale cover ${U_i -> X}_i$ s.t. $cal(F)|_(U_i) cong tilde((G_i)_(U_i)) = ul(G_i)_(U_i)$ for some finite abelian groups $G_i$.
  
  If $Lambda$ is finite as a set, then these two points are additionally equivalent to: 

  3. For every connected component $X_0$ of $X$, there exists a finite etale covering space $U_0 ->> X_0$ and a finite $Lambda$-module (resp. abelian group) $G$ s.t. $cal(F)|_(U_0) cong /*tilde(G_U) =*/ ul(G)_(U_0)$.
]
#proof[
  We will only deal with the case of $Lambda$-modules, since in the abelian group case, l.c.c. sheaves of abelian groups are l.c.c. sheaves of $ZZ\/n$-modules for some $n$, and it is easy to check that under any of (a)(b)(c), $cal(F)$ is $n$-torsion for some $n$. 

  (c)$==>$(a) is by definition tautological. 

  (a)$==>$(b): We need to show that specialization is compatible with pullbacks: 

  #lemma[
    Let $f: X -> Y$ be a morphism of schemes, $ol(x)$ be a geometric point of $X$, $ol(y) = f(ol(x))$, $ol(xi) -> tilde(X)_(ol(x))$ be a geometric point generalizing $ol(x)$, and $ol(eta) = ol(xi) -> tilde(X)_(ol(x)) -> tilde(Y)_(ol(y))$ be a geometric point generalizing $ol(y)$. Then the following diagram commutes: 
    // https://q.uiver.app/#r=typst&q=WzAsNCxbMCwwLCJjYWwoRilfKG9sKHgpKSJdLFswLDEsImNhbChGKV8ob2woeGkpKSJdLFsxLDAsIihmXigtMSkgY2FsKEYpKV8ob2woeSkpIl0sWzEsMSwiKGZeKC0xKSBjYWwoRikpXyhvbChldGEpKSJdLFswLDIsIiIsMCx7InN0eWxlIjp7InRhaWwiOnsibmFtZSI6Im1hcHMgdG8ifX19XSxbMSwzLCIiLDAseyJzdHlsZSI6eyJ0YWlsIjp7Im5hbWUiOiJtYXBzIHRvIn19fV0sWzAsMSwic3BfKG9sKHhpKSxvbCh4KSkiLDJdLFsyLDMsInNwXyhvbChldGEpLG9sKHkpKSJdXQ==
    #align(center, diagram({
      node((-1, -1), [$(f^(-1) cal(F))_(ol(x))$])
      node((-1, 0), [$(f^(-1) cal(F))_(ol(xi))$])
      node((0, -1), [$cal(F)_(ol(y))$])
      node((0, 0), [$cal(F)_(ol(eta))$])
      edge((-1, -1), (0, -1), "=")
      edge((-1, 0), (0, 0), "=")
      edge((-1, -1), (-1, 0), [$sp_(ol(xi),ol(x))$], label-side: right, "->")
      edge((0, -1), (0, 0), [$sp_(ol(eta),ol(y))$], label-side: left, "->")
    }))
  ]
  #proof[
    This diagram really consists of restriction maps: 
    // https://q.uiver.app/#r=typst&q=WzAsNCxbMCwwLCJHYW1tYSh0aWxkZShYKV8ob2woeCkpLCBjYWwoRil8Xyh0aWxkZShYKV8ob2woeCkpKSkiXSxbMCwxLCJHYW1tYSh0aWxkZShYKV8ob2woeGkpKSwgY2FsKEYpfF8odGlsZGUoWClfKG9sKHhpKSkpKSJdLFsxLDAsIkdhbW1hKHRpbGRlKFkpXyhvbCh5KSksIGNhbChGKXxfKHRpbGRlKFkpXyhvbCh5KSkpKSJdLFsxLDEsIkdhbW1hKHRpbGRlKFkpXyhvbChldGEpKSwgY2FsKEYpfF8odGlsZGUoWSlfKG9sKGV0YSkpKSkiXSxbMCwxXSxbMiwzXSxbMiwwXSxbMywxXV0=
    #align(center, diagram({
      node((-1, -1), [$Gamma(tilde(X)_(ol(x)), cal(F)|_(tilde(X)_(ol(x))))$])
      node((-1, 0), [$Gamma(tilde(X)_(ol(xi)), cal(F)|_(tilde(X)_(ol(xi))))$])
      node((0, -1), [$Gamma(tilde(Y)_(ol(y)), cal(F)|_(tilde(Y)_(ol(y))))$])
      node((0, 0), [$Gamma(tilde(Y)_(ol(eta)), cal(F)|_(tilde(Y)_(ol(eta))))$])
      edge((-1, -1), (-1, 0), "->")
      edge((0, -1), (0, 0), "->")
      edge((0, -1), (-1, -1), "->")
      edge((0, 0), (-1, 0), "->")
    }))
    and hence commutes. 
  ]

  Thus, given a pair of geometric points $(ol(x),ol(xi))$ of $X$ s.t. $ol(xi)$ generalizes $ol(x)$, we pick any etale neighborhood $(U, ol(u)) -> (X, ol(x))$ s.t. $cal(F)|_U$ is constant. Since $ol(xi)$ is a geometric point of $tilde(X)_(ol(x))$, it lifts canonically to a geometric point $ol(v)$ of $U$, lying above $ol(xi)$. Thus, the specialization map: 
  $
    sp_(ol(xi),ol(x)): cal(F)_(ol(x)) -> cal(F)_(ol(xi))
  $
  is really just the specialization: 
  $
    sp_(ol(v),ol(u)): (cal(F)|_U)_(ol(u)) -> (cal(F)|_U)_(ol(v))
  $
  However, $cal(F)|_U$ is a constant sheaf, and the specialization map in a constant sheaf is always an isomorphism. We are thereby done. 

  (b)$==>$(a): For a geometric point $ol(x)$ of $X$, we need to find an etale neighborhood $(U, ol(u)) -> (X, ol(x))$ s.t. $cal(F)|_U cong ul(M)_U$ for a finite $Lambda$-module $M$. Put $M = cal(F)_(ol(x))$ which is known to be a finite $Lambda$-module. Since $Lambda$ is noetherian, we may choose a presentation: 
  $
    Lambda^r ->^A Lambda^m -> M -> 0
  $
  of $M$. Let the generators of $M$ corresponding to $Lambda^r ->> M$ be $s_1, dots.c, s_m in M = cal(F)_(ol(x))$. By definition of a stalk, each $s_i$ comes from a section in $cal(F)(U_i)$ for an etale neighborhood $(U_i, ol(u)_i) -> (X, ol(x))$. Picking a common etale neighborhood $(U, ol(u))$ of all $u_i$, we may assume that each $s_i in cal(F)_(ol(x))$ comes from $s_i in cal(F)(U)$. 

  By shrinking the etale neighborhood further, we may assume that the $s_i$'s satisfy all $r$ relations between the $m$ generators of $M$. Indeed, for a relation, $s_i$'s satisfy this relation in $cal(F)_(ol(x))$, and so they satisfy this relation in some small etale neighborhood. 
  
  Thus, the sections $s_i in cal(F)(U)$ define a map: 
  $
    ul(Lambda^r)_U ->^A ul(Lambda^m)_U ->^({s_i}) cal(F)|_U -> 0
  $
  i.e. a map $phi: ul(M)_U -> cal(F)|_U$. By definition, $phi_(ol(u))$ is an isomorphism. Finally, we shrink $U$ around $ol(u)$ by replacing it with an affine open, and then the connected component of $ol(u)$, so that $U$ is noetherian and connected. 
  
  Let: 
  $
    E = {v in U : exists#[geometric point $ol(v)$ above $v$ s.t. $phi_(ol(v)): M -> (cal(F)|_U)_(ol(v))$ is an isomorphism]}
  $
  By @stalks-detects-properties (0), the property defining $E$ is independent from the choice of a geometric point above $v$. Furthermore, for $v, w in U$ s.t. $w$ generalizes $v$, pick a geometric point $ol(v)$ above $v$, and we may arbitrarily lift $w$ to a geometric point $ol(w)$ of $tilde(U)_(ol(v))$. 

  Since the specialization maps of $cal(F)$ are isomorphisms, so are those of $cal(F)|_U$. We now have a commutative diagram by naturality of specialization: 
  // https://q.uiver.app/#r=typst&q=WzAsNCxbMCwwLCJNIl0sWzAsMSwiTSJdLFsxLDAsIihjYWwoRil8X1UpXyhvbCh2KSkiXSxbMSwxLCIoY2FsKEYpfF9VKV8ob2wodykpIl0sWzIsMywic3AiXSxbMCwxLCIiLDAseyJzdHlsZSI6eyJib2R5Ijp7Im5hbWUiOiJkb3VibGUgYmFycmVkIn19fV0sWzAsMiwicGhpXyhvbCh2KSkiXSxbMSwzLCJwaGlfKG9sKHcpKSIsMV1d
  #align(center, diagram({
    node((0, 0), [$M$])
    node((0, 1), [$M$])
    node((1, 0), [$(cal(F)|_U)_(ol(v))$])
    node((1, 1), [$(cal(F)|_U)_(ol(w))$])
    edge((1, 0), (1, 1), [$sp$], label-side: left, "->")
    edge((0, 0), (0, 1), "=")
    edge((0, 0), (1, 0), [$phi_(ol(v))$], label-side: left, "->")
    edge((0, 1), (1, 1), [$phi_(ol(w))$], label-side: right, "->")
  }))
  in which $sp$ is an isomorphism. As such, $phi_(ol(v))$ is an isomorphism if and only if $phi_(ol(w))$ is. In other words, $E$ is closed under both generalization and specialization. Therefore, $E$ is a disjoint union of irreducible components of $U$. Since $U$ is noetherian and connected, its irreducible components form a connected graph under intersection. Thus $E$ is either empty or the whole $U$. Since $u in E$, it must be that $E = U$, and so $phi: ul(M)_U -> cal(F)|_U$ is an isomorphism. 

  (a)$==>$(c) when $Lambda$ is a finite ring: We may work one connected component at a time, so assume that $X$ is connected. By definition of an l.c.c. sheaf, there exists an etale cover ${U_i -> X}$ s.t. each $cal(F)|_(U_i)$ is constant. Thus, the stalks at all geometric points of $X$ are isomorphic as $Lambda$-modules. Let this finite $Lambda$-module be $G$. 
  
  Consider the following sheaf of sets: 
  $
    cal(J): Et_X^opp -> cSet, U |-> "Isom"(ul(G)_U, cal(F)|_U) = {#[isomorphisms $phi: ul(G)_U -> cal(F)|_U$]}
  $

  For every etale open $U -> X$ s.t. $cal(F)|_U cong ul(G)_U$, we have: 
  $
    cal(J)|_U: Et_U^opp -> cSet, V |-> "Isom"(ul(G)_V, ul(G)_V) = Aut_(Lambda)(G)^(pi_0 (V))
  $
  In other words, $cal(J)|_U cong ul(Aut_Lambda (G))_U$ is constant. Thus, $cal(J)$ is a locally constant sheaf of sets. Furthermore, $Lambda$ is a finite ring and $G$ is a finite $Lambda$-module. Thus, $Aut_Lambda (G)$ is finite as a set, and so $cal(J)$ is a l.c.c. sheaf of sets. By @descs-of-lcc-sheaves-of-sets, there exists a finite etale covering $U ->> X$ s.t. $cal(J)|_U cong ul(Aut_Lambda (G))_U$. Taking the global section corresponding to the identity $id in Aut_Lambda (G)$ gives an isomorphism $cal(F)|_U cong ul(G)_U$. 
]

#definition(name: <defn-constructible-sheaf>)[
  An etale sheaf $cal(F)$ on $X$ of $Lambda$-modules (resp. abelian groups) is called a *constructible sheaf* if there exists a stratification $X = union.sq.big_i X_i$ by finitely many locally closed subschemes $X_i subset X$ s.t. each $cal(F)|_(X_i)$ is a l.c.c. sheaf of $Lambda$-modules (resp. abelian groups) for each $i$. 

  When we simply say a *constructible sheaf*, we refer to a constructible sheaf of abelian groups. 
]

#properties(name: <constructible-sheaves-first-props>)[
  Let $Lambda$ be a noetherian ring and $cal(F)$ denote a sheaf of $Lambda$-modules on $X$. 

  + If $cal(F)$ is l.c.c./constructible, then $g^(-1) cal(F)$ is l.c.c./constructible for any $g: X' -> X$ with $X'$ noetherian.
    
  
  + TFAE: 
    + $cal(F)$ is constructible; 
    
    + For any $Y subset X$ an irreducible closed subset with the reduced subscheme structure, there exists $emptyset != V subset Y$ open with $cal(F)|_V$ l.c.c; 

    + For any $Y subset X$ an irreducible closed subset with the reduced subscheme structure, there exists $emptyset != V subset Y$ open with $cal(F)|_V$ constructible. 
  
  + If $f: U -> X$ is etale quasi-compact, then:
    - $f_! ul(Lambda)$ is a constructible sheaf of $Lambda$-modules. 
    - $f_! ul(ZZ\/n)$ is a constructible sheaf of abelian groups. 

  + For a sheaf $cal(F)$ of $Lambda$-modules, TFAE:
    + $cal(F)$ is constructible;
    + $cal(F)$ is /*torsion and */noetherian (i.e. any ascending chain of abelian subsheaves $0 = cal(F)_0 subset cal(F)_1 subset dots.c subset cal(F)$ eventually stabilizes).
    + There exists etale quasi-compact maps $f: U -> X$, $f': U' -> X$ and a right exact sequence:
      $
        f'_! ul(Lambda)_(U') -> f_! ul(Lambda)_U -> cal(F) -> 0
      $

    For a sheaf $cal(F)$ of abelian groups, TFAE: 
    + $cal(F)$ is constructible;
    + $cal(F)$ is torsion and noetherian; 
    + There exists etale quasi-compact maps $f: U -> X$, $f': U' -> X$ and a right exact sequence:
      $
        f'_! ul(ZZ\/n)_(U') -> f_! ul(ZZ\/n)_U -> cal(F) -> 0
      $
      for some $n >= 1$. 

  
  + Any subsheaf or quotient sheaf of a constructible sheaf of $Lambda$-modules (resp. abelian groups) is constructible. Any extension of constructible sheaves of $Lambda$-modules (resp. abelian groups) is constructible. The constructible sheaves of $Lambda$-modules (resp. abelian groups) on $X$ forms an abelian category.
  
  + 
    - Every sheaf $cal(F)$ of $Lambda$-modules is the direct limit of its constructible subsheaves ordered under inclusion. 
    - Every torsion abelian sheaf $cal(F)$ is the direct limit of its constructible subsheaves ordered under inclusion.
]
#proof[
  One can easily see that all statements here for abelian groups follow from statements for $Lambda$-modules, by taking $Lambda = ZZ\/n$ for a suitable $n$. (6) is slightly nontrivial: for every torsion abelian sheaf $cal(F)$, one can write $cal(F) = dirlim_n cal(F)[n]$, and then write each $cal(F)[n]$ as the directed limit of its constructible subsheaves of $ZZ\/n$-modules. Arguments starting at (5b) are also slightly nontrivial, for one needs to argue that if $cal(F)$ is torsion and noetherian, then since $cal(F) = dirlim_n cal(F)[n!]$, we have $cal(F) = cal(F)[n!]$ for some $n$. Thus $cal(F)$ is a sheaf of $ZZ\/n$-modules for some $n$. 

  (1)
  #proof[
    Pick a stratification $X = union.sq.big_i X_i$ by locally closed subschemes s.t. $cal(F)|_(X_i)$ is l.c.c. Then $X' = union.sq.big X'_i$ where $X'_i = X_i times_X X'$ is a stratification of $X'$ by locally closed subschemes. As such, it suffices to show that each $cal(F)|_(X'_i)$ is l.c.c, i.e. to prove the statement for l.c.c. sheaves.
    
    Suppose that for some etale cover $f: U -> X$, $f^(-1) cal(F) cong ul(G)_U$ for a finite $Lambda$-module $G$. Form the base change:
    // https://q.uiver.app/#r=typst&q=WzAsNCxbMSwxLCJYIl0sWzEsMCwiVSJdLFswLDEsIlgnIl0sWzAsMCwiVSciXSxbMiwwLCJnIiwyXSxbMSwwLCJmIl0sWzMsMSwiZyciXSxbMywyLCJmJyIsMl1d
    #align(center, diagram(
      {
        node((0, 0), [$X$])
        node((0, -1), [$U$])
        node((-1, 0), [$X'$])
        node((-1, -1), [$U'$])
        edge((-1, 0), (0, 0), [$g$], label-side: right, "->")
        edge((0, -1), (0, 0), [$f$], label-side: left, "->")
        edge((-1, -1), (0, -1), [$g'$], label-side: left, "->")
        edge((-1, -1), (-1, 0), [$f'$], label-side: right, "->")
      },
      spacing: 1.5em,
    ))
    so that $f': U' -> X'$ is an etale cover of $X'$. Then:
    $
      f'^(-1)g^(-1) cal(F) cong g'^(-1)f^(-1) cal(F) cong g'^(-1) ul(G)_U cong ul(G)_(U')
    $
    Hence, $g^(-1) cal(F)$ is l.c.c.
  ]

  (2)
  #proof[
    (a)$==>$(b): By (1), $cal(F)|_Z$ is constructible. In the locally closed stratification $Z = union.sq.big_i Z_i$, pick the stratum containing the generic point of $Z$, say $Z_1$. Then $Z_1$ is a nonempty open of $Z$ s.t. $cal(F)|_(Z_1)$ is l.c.c.
    
    (b)$==>$(a): By noetherian induction, there exists a maximal open subset $U subset X$ s.t. $cal(F)|_U$ is constructible. If $U != X$, we may take an irreducible component $Z$ of the nonempty closed subset $X - U$. By hypothesis, there exists an open subset $V subset Z$ s.t. $cal(F)|_V$ is l.c.c. $V$ is a locally closed subset of $X$. Pick a finite stratification $U = union.sq.big_i U_i$ s.t. each $cal(F)|_(U_i)$ is l.c.c. Then $U union V = (Z - V)^c$ is an open subset of $X$ with a finite locally closed stratification $(union.sq.big_i U_i) union.sq V$, s.t. $cal(F)$ restricted to each stratum is l.c.c. Thus, $cal(F)|_(U union V)$ is constructible, a contradiction to the maximality of $U$. Thus $U = X$ and $cal(F)$ is constructible. 

    (b)$==>$(c) is tautological. 
    
    (c)$==>$(b): For any irreducible closed $Y subset X$, there exists a dense open $V subset Y$ s.t. $cal(F)|_V$ is constructible by assumption. Now by (a)$==>$(b), there exists a dense open $W subset V$ s.t. $cal(F)|_W$ is l.c.c. Now $W subset Y$ is a dense open in $Y$, and so we are done. 
  ]

  (3)
  #proof[
    By (2) and that $f_!$ commutes with base change (@etale-lower-shriek-first-props (4)), we may assume that $X$ is integral with generic point $eta$//, and that $U times_X eta -> Spec(k(eta))$ is finite etale. (Etale over a field is always finite etale.) Then by a limit argument, there exists $eta in V subset X$ open s.t. $f^(-1) (V) -> V$ is finite etale. Then it is easy to check that:
    // $
    //   (f_! underline(ZZ\/n))|_V = (f|_(f^(-1)(U)))_! underline(ZZ\/n)
    // $
    // is l.c.c.
    and we need to prove that $f_! ul(Lambda)$ is l.c.c. when restricted to a nonempty open of $X$.
    
    Since $f$ is etale quasi-compact, it is of finite presentation. Now the morphism $U_eta -> eta = Spec(k(eta))$ is etale of finite presentation over a field, hence finite etale by the structure discussed in @struct-of-spec-k-et. Consider:
    $
      Spec(k(eta)) = invlim_(eta in V subset X \ V #[affine open]) V
    $
    as a projective limit of schemes with affine transition morphisms. By passage of limit of properties of morphisms (@passage-to-limit-of-properties), there exists an affine open $eta in V subset X$ s.t. $f|_(f^(-1)(V)): f^(-1)(V) -> V$ is finite etale. Now:
    $
      (f_! ul(Lambda))|_V cong (f|_(f^(-1)(V)))_! (ul(Lambda)|_(f^(-1)(V))) = (f|_(f^(-1)(V)))_! ul(Lambda)
    $
    by @etale-lower-shriek-first-props (4). Thus, it suffices to prove the following lemma:
    #lemma[
      If $X$ is connected noetherian and $f: U -> X$ is a finite etale covering, then $f_! ul(Lambda)$ is a l.c.c sheaf of $Lambda$-modules.
    ]
    #proof[
      By @fet-trivializes-fet-locally, we may pick a connected $Z in FEt_X$ s.t. the finite etale covering $f_Z: U times_X Z -> Z$ is trivial. Now:
      $
        (f_! ul(Lambda))|_Z cong f_(Z,!) (ul(Lambda)|_(U times_X Z)) cong f_(Z,!) ul(Lambda)
      $
      by @etale-lower-shriek-first-props (4). Meanwhile, since $f_Z$ is a trivial etale covering space, say of degree $d$, we see that $f_(Z,!) ul(Lambda) cong ul((Lambda)^(oplus d))$ is constant. By @descs-of-lcc-sheaves (c)$==>$(a), $f_! ul(Lambda)$ is l.c.c.
    ]
  ]

  (4)
  #proof[
    (a)$==>$(b): /*We first show that $cal(F)$ is torsion. Pick a finite stratification $X = union.sq.big_i X_i$ by locally closed subschemes s.t. each $cal(F)|_(X_i)$ is l.c.c. By definition, l.c.c. sheaves are torsion, so we may take some $n$ s.t. every $cal(F)|_(X_i)$ is $n$-torsion. For every point $x in X$ with a geometric point $ol(x)$ above $x$ s.t. $x in X_i$, since $X_i -> X$ preserves residue fields as an immersion, $ol(x)$ lifts uniquely to a geometric point $ol(x)$ of $X_i$. Now $(cal(F)|_(X_i))_(ol(x)) = cal(F)_(ol(x))$, and $times n$ is zero on $(cal(F)|_(X_i))_(ol(x))$. In other words, every $cal(F)_(ol(x))$ is $n$-torsion. Thus, $times n: cal(F) -> cal(F)$ is zero on all stalks, hence the zero morphism.*/
    To prove that $cal(F)$ is noetherian, take any ascending chain $0 = cal(F)_0 subset cal(F)_1 subset dots.c subset cal(F)$, and take:
    $
      cal(S) = {emptyset != Y subset X "closed": 0 = cal(F)_0|_Y subset cal(F)_1|_Y subset dots.c subset cal(F)|_Y "is not stationary"}
    $
    We want to show $cal(S) = emptyset$. Otherwise, since $X$ is noetherian, there exists $Y in cal(S)$ minimal. By pulling back the chain of inclusions $0 = cal(F)_0 subset cal(F)_1 subset dots.c subset cal(F)$ along the closed immersion $Y -> X$ (where $Y$ is given the reduced induced subscheme structure) and using (1) and exactness of inverse images, we may assume that:
    
    - $X$ is a reduced noetherian scheme, $0 = cal(F)_0 subset cal(F)_1 subset dots.c subset cal(F)$ does not stabilize on $X$ but does stabilize when pulled back to any proper closed subscheme of $X$.
    
    Suppose that $X$ is not irreducible. Since $X$ is noetherian, it has finitely many irreducible components $Z_1, dots.c, Z_m subset X$, which are proper closed subschemes of $X$ (equipped with reduced induced subscheme structure). Thus, each:
    $
      0 = cal(F)_0|_(Z_i) subset cal(F)_1|_(Z_i) subset dots.c subset cal(F)|_(Z_i)
    $
    does stabilize, say after stage $N_i$. Taking $N = max(N_1, dots.c, N_m)$. Now for all $n > N$. Consider the inclusion $cal(F)_N arrow.hook cal(F)_n$. It is an isomorphism when pulled back along $union.sq.big_(i=1)^m Z_i -> X$ by our hypothesis. Thus $cal(F)_N -> cal(F)_n$ is an isomorphism by @surjective-pullback-conservative.
    
    As such, we may assume that $X$ is irreducible, hence integral. By (2), there exists a nonempty open $V subset X$ s.t. $cal(F)|_V$ is l.c.c, hence an etale cover $U -> V$ s.t. $cal(F)|_U cong ul(G)_U$ for some finite $Lambda$-module $G$. Pulling back the chain of inclusions to $U$:
    $
      0 = cal(F)_0|_U subset cal(F)_1|_U subset dots.c subset ul(G)_U
    $
    We want to show that this chain eventually stabilizes.
    
    #lemma[
      Let $X$ be a noetherian scheme and $G$ be a finite $Lambda$-module. Then every chain of inclusions:
      $
        0 = cal(G)_0 subset cal(G)_1 subset dots.c subset ul(G)_X
      $
      of subsheaves of $Lambda$-modules must eventually stabilize.
    ]
    #proof[
      Repeating the same noetherian induction argument performed at the start of the proof for (a)$==>$(b) of property (4), we may assume that $X$ is integral and this lemma holds for all proper subschemes of $X$. Let $eta in X$ be the generic point, and:
      $
        H = union.big_(m>=0) (cal(G)_m)_(ol(eta)) <= G
      $
      $H <= G$ is a submodule of a finite $Lambda$-module. Since $Lambda$ is noetherian, $H$ is a finite $Lambda$-module and is noetherian. Thus there exists some finite stage $N$ s.t. $(cal(G)_N)_(ol(eta)) = H$. Consider:
      $
        (cal(G)_m)_(ol(eta)) = dircolim_((U,ol(u)) -> (X,ol(eta)) #[etale]) cal(G)_m (U) = dircolim_((U,ol(u)) -> (X,ol(eta)) #[etale] \ U #[connected]) cal(G)_m (U)
      $
      where connected etale neighborhoods are cofinal since $X$ is noetherian. However, on connected etale opens of $X$, the constant sheaf $ul(G)_X$ evaluates to $G$, with restriction maps being identity. Thus each $cal(G)_m$, as a subsheaf of $ul(G)_X$, has injective restriction maps between connected etale opens. Thus, for $m >= N$, the isomorphism:
      $
        dircolim_((U,ol(u)) -> (X,ol(eta)) #[etale] \ U #[connected]) cal(G)_m (U) -> H
      $
      has LHS being a filtered colimit with injective transition morphisms. Thus each $cal(G)_m (U) -> dircolim_((U,ol(u)) -> (X,ol(eta)) #[etale] \ U #[connected]) cal(G)_m (U) -> H$ is injective.
      
      - Taking $m = N$, and since $H$ is a finite $Lambda$-module, there exists a fixed connected etale open $U$ s.t. $cal(G)_N (U) = H$ (by finding a common etale neighborhoods of representative sections of a finite set of generators of $(cal(G)_N)_(ol(eta)) = H$).
      
      - For every $m >= N$ and every refinement $V -> U$ of connected etale opens, we have a composition of injective morphisms:
        $
          H = cal(G)_N (U) arrow.hook cal(G)_m (U) arrow.hook cal(G)_m (V) arrow.hook (cal(G)_m)_(ol(eta)) = H
        $
        whose composition is bijective. Thus every step in this chain is bijective, and in particular $cal(G)_N (U) -> cal(G)_m (V)$ is bijective. Taking $m = N$, $cal(G)_N (U) -> cal(G)_N (V)$ is also bijective. As such, for all such $V$, $cal(G)_N (V) -> cal(G)_m (V)$ is bijective.
      
      As such, there exists a nonempty etale open $phi: U -> X$ s.t. for all $m >= N$, $cal(G)_N|_U -> cal(G)_m|_U$ is an isomorphism. Let $Z = X - phi(U)$, a closed subscheme of $X$ equipped with reduced induced subscheme structure. Now by the inductive hypothesis, upon enlarging $N$ if necessary, for all $m >= N$, $cal(G)_N|_U -> cal(G)_m|_U$ and $cal(G)_N|_Z -> cal(G)_m|_Z$ are both isomorphisms. Applying @surjective-pullback-conservative to $U union.sq Z -> X$, we see that the chain of inclusions stabilizes at stage $N$.
    ]
    By the lemma, our chain $0 = cal(F)_0|_U subset cal(F)_1|_U subset dots.c subset ul(G)_U$ stabilizes at some stage $N$. Enlarging $N$ if necessary, by the inductive hypothesis, $0 = cal(F)_0|_Z subset cal(F)_1|_Z subset dots.c subset cal(F)|_Z$ stabilizes at stage $N$ for $Z = X - V$. Now applying @surjective-pullback-conservative to $U union.sq Z -> X$, we see that $0 = cal(F)_0 subset cal(F)_1 subset dots.c subset cal(F)$ stabilizes at stage $N$.
    
    (b)$==>$(c): Assume that $cal(F)$ is noetherian. /*Since $cal(F) = union.big_(n>=1) cal(F)[n!]$ is the union of its $n!$-torsion, there exists $n$ s.t. $n cal(F) = 0$. */Now consider the canonical map:
    $
      gamma: oplus.big_(f_alpha: U_alpha -> X "etale" \ U_alpha "affine" \ f_alpha (U_alpha) subset "some affine open" subset X) oplus.big_(s_alpha in cal(F)(U_alpha)) f_(alpha,!) underline(Lambda) -> cal(F)
    $
    where the morphism $f_(alpha,!) underline(Lambda) -> cal(F)$ corresponding to $f_alpha, s_alpha$ is obtained by adjunction from $underline(Lambda) -> f_alpha^(-1) cal(F)$, sending $1 |-> s_alpha$. By unfolding definitions, this morphism contains $s_alpha$ in its image. Thus by construction, $gamma$ is surjective.
    
    #remark[
      The weird range of the first direct sum $oplus.big_(f_alpha: U_alpha -> X "etale" \ U_alpha "affine" \ f_alpha (U_alpha) subset "some affine open" subset X)$ is to avoid a set-theoretic issue, in the same way as in @set-categorical-subtleties.
    ]
    
    Since $cal(F)$ is noetherian, the direct sum on LHS of $gamma$ over all $f_alpha, s_alpha$ can be replaced with a finite one and still be surjective. We thus obtain a surjection:
    $
      gamma_0: oplus.big_(i=1)^N f_(i,!) ul(Lambda) -> cal(F)
    $
    for some $f_i: U_i -> X$ etale quasi-compact. Take:
    $
      f: U = union.sq.big_(i=1)^N U_i -> X
    $
    which is etale quasi-compact. We then have a surjection $gamma_0: f_! ul(Lambda) ->> cal(F)$, from a constructible sheaf to a noetherian sheaf.
    
    By (a)$==>$(b), $f_! ul(Lambda)$ is noetherian, so $ker(gamma_0)$ is noetherian too. We may thus perform the same construction again to get $f': U' -> X$ etale quasi-compact, with a right exact sequence:
    $
      f'_! underline(Lambda) -> f_! underline(Lambda) -> cal(F) -> 0
    $
    
    (c)$==>$(a):
    
    #lemma[
      The cokernel of a morphism between constructible sheaves of $Lambda$-modules on a noetherian scheme $X$ is constructible.
    ]
    #proof[
      Consider a right exact sequence of sheaves on $X$:
      $
        cal(F) -> cal(G) -> cal(H) -> 0
      $
      in which $cal(F), cal(G)$ are constructible. By (2), it suffices to show that for every irreducible closed subscheme $Z subset X$, $cal(H)|_Z$ is l.c.c. when pulled back to some nonempty open of $Z$.
      
      By (1), we may assume that $X$ is integral, and only aim to prove that $cal(H)|_U$ is l.c.c. when pulled back to some nonempty open of $X$.
      
      Since $cal(F), cal(G)$ are both constructible, there exists some nonempty open $U subset X$ s.t. $cal(F)|_U, cal(G)|_U$ are both l.c.c. By @descs-of-lcc-sheaves (c), there exists a common etale cover $V -> U$ s.t. $cal(F)|_V cong ul(F)_V, cal(G)|_V cong ul(G)_V$ for finite $Lambda$-modules $F, G$. Restricting to $V$, we get an exact sequence:
      $
        ul(F)_V -> ul(G)_V -> cal(H)|_V -> 0
      $
      This gives a morphism $phi: F -> G$, and identifies $cal(H)|_V cong ul(coker(phi))_V$, the constant sheaf associated with a finite $Lambda$-module. Thus $cal(H)|_U$ is l.c.c. by @descs-of-lcc-sheaves (c), and we are done.
    ]
    
    Take a right exact sequence:
    $
      f'_! underline(Lambda) -> f_! underline(Lambda) -> cal(F) -> 0
    $
    i.e. $cal(F) = coker(f'_! underline(Lambda) -> f_! underline(Lambda))$. By (3) and the previous lemma we conclude the proof.
  ]

  (5)
  #proof[
    Use (4) that constructible = noetherian.
  ]

  (6)
  #proof[
    Every $s in cal(F)(U)$ for $U -> X$ quasi-compact defines a morphism $gamma_s: f_! underline(Lambda) -> cal(F)$, which has constructible image that contains the section $s$.
    
    Consider the injective morphism:
    $
      dirlim_(cal(G) subset cal(F) #[constructible]) cal(G) -> cal(F)
    $
    and we need to show that it is surjective. For this, we need to show that it is surjective on stalks. Now for every geometric point $ol(x)$ of $X$, $(-)_(ol(x))$ preserves colimits as a left adjoint. Thus, it suffices to show that:
    $
      dirlim_(cal(G) subset cal(F) #[constructible]) cal(G)_(ol(x)) -> cal(F)_(ol(x))
    $
    is surjective, i.e.
    $
      dirlim_(cal(G) subset cal(F) #[constructible]) dircolim_((U,ol(u)) -> (X,ol(x)) #[etale]) cal(G)(U) -> dircolim_((U,ol(u)) -> (X,ol(x)) #[etale]) cal(F)(U)
    $
    is surjective. Since $X$ is noetherian, the noetherian etale neighborhoods of $(U, ol(u))$ are cofinal. Thus, it suffices to show that:
    $
      dirlim_(cal(G) subset cal(F) #[constructible]) dircolim_((U,ol(u)) -> (X,ol(x)) #[etale] \ U #[noetherian]) cal(G)(U) -> dircolim_((U,ol(u)) -> (X,ol(x)) #[etale] \ U #[noetherian]) cal(F)(U)
    $
    is surjective. However, every etale $U -> X$ for $U$ noetherian is of course quasi-compact, so every section in $cal(F)(U)$ is in $cal(G)(U)$ for some constructible subsheaf $cal(G) subset cal(F)$, as we argued above. We are thereby done.
  ]
]

#proposition(name: <supp-of-constructible-sheaf>)[
  Let $Lambda$ be a noetherian ring. For a constructible sheaf $cal(F)$ on $X$ of $Lambda$-modules or abelian groups, 
  $
    supp(cal(F)) = {x in X : cal(F)_(ol(x)) != 0 #[for some geometric point $ol(x)$ above $x$]}
  $
  is a constructible subset of $X$. 
]
#proof[
  It suffices to show that for any irreducible closed subset $Z subset X$ with reduced induced subscheme structure, and with generic point $eta in Z$, if $eta in supp(cal(F))$, then there exists a nonempty open $V subset Z$ s.t. $V subset supp(cal(F))$. Since constructibility is preserved under pullback and $supp(cal(F)|_Z) = supp(cal(F)) ∩ Z$, we may replace $cal(F)$ with $cal(F)|_Z$ and $X$ with $Z$, to assume that $X$ is integral and $Z = X$. 

  Since $cal(F)$ is constructible on integral $X$, there exists a nonempty open $eta in U subset X$ s.t. $cal(F)|_U$ is l.c.c. Thus, there exists an etale cover $pi: V ->> U$ s.t. $pi^(-1) (cal(F)|_U) cong ul(G)_V$ for some finite $Lambda$-module $G$. Thus, for all geometric points $ol(u)$ lying above $u in U$, with $ol(v) in pi^(-1) (ol(u))$, 
  $
    cal(F)_(ol(u)) = (pi^(-1) (cal(F)|_U))_(ol(v)) cong (ul(G)_V)_(ol(v)) = G
  $
  Thus, $G != 0$ since $G cong cal(F)_(ol(eta)) != 0$, and so for all $ol(u)$ lying above $u in U$, $cal(F)_(ol(u)) cong G != 0$. Thus $U subset supp(cal(F))$. 
]

#theorem(name: <finite-morphisms-and-constructible-sheaves>)[
  Let $Lambda$ be a noetherian ring. 

  + Let $f: X -> Y$ be a finite morphism of noetherian schemes. Then an etale sheaf of $Lambda$-modules or abelian groups $cal(F)$ is constructible if and only if $f_* cal(F)$ is constructible.
  
  + 
    - If $cal(F)$ is a constructible sheaf of $Lambda$-modules, then there exists a finite morphism $g: Z -> X$ and an injection $cal(F) arrow.r.hook g_* ul(M)$ for a finite $Lambda$-module $M$. 

    - If $cal(F)$ is a constructible sheaf of abelian groups s.t. $n cal(F) = 0$, then there exists a finite morphism $g: Z -> X$ and an injection $cal(F) arrow.r.hook g_* ul(ZZ\/n)$. 
]
#proof[
  (1) ($<==$) holds since the adjunction map $f^(-1)f_* cal(F) -> cal(F)$ is surjective for $f$ finite, by checking stalks using @stalks-of-finite-pushforward.
  
  ($==>$) We may check for $Lambda$-modules only, since if $cal(F)$ is a constructible sheaf of abelian groups, it is a constructible sheaf of $ZZ\/n$-modules for some $n$. 
  
  We want to invoke @constructible-sheaves-first-props (2). Let $Y' subset Y$ be an irreducible closed subscheme of $Y$ equipped with reduced induced subscheme structure, and we want to show that $(f_* cal(F))|_(Y')$ is l.c.c. on an open subset of $Y'$. Now $(f_* cal(F))|_(Y') = f'_* (cal(F)|_(X'))$ by (Finite) (@pbc-finite), which says that base change holds along finite morphisms, where we form the Cartesian square: 
  // https://q.uiver.app/#r=typst&q=WzAsNCxbMCwxLCJYIl0sWzEsMSwiWSJdLFsxLDAsIlknIl0sWzAsMCwiWCciXSxbMCwxLCJmIiwyXSxbMywyLCJmJyJdLFsyLDFdLFszLDBdXQ==
  #align(center, diagram({
    node((-1, 0), [$X$])
    node((0, 0), [$Y$])
    node((0, -1), [$Y'$])
    node((-1, -1), [$X'$])
    edge((-1, 0), (0, 0), [$f$], label-side: right, "->")
    edge((-1, -1), (0, -1), [$f'$], label-side: left, "->")
    edge((0, -1), (0, 0), "->")
    edge((-1, -1), (-1, 0), "->")
  }))
  Since $cal(F)|_(X')$ is constructible and $f'$ is finite, we may assume that $Y$ is integral with generic point $eta$, and check that $f_* cal(F)$ is l.c.c. on an open subset of $Y$. 
  
  By generic flatness (see @generic-flatness) and using (Finite) (@pbc-finite) in the same way as above, we may assume that $f$ is finite flat, upon passing to an open subset of $Y$. By topological invariance, we may assume that $X$ is reduced by passing to its reduction. Now let $eta in Y$ be the generic point, and consider the generic fiber $X_eta -> eta = Spec(K(Y))$, which is finite with $X_eta$ reduced. This forces $X_eta = Spec(A)$, where $A = product_(i=1)^m L_i$, each $L_i\/K(Y)$ is a finite field extension. Now for each $i$, $L_i\/K(Y)$ factors as $L_i\/L'_i\/K(Y)$, with $L_i\/L'_i$ purely inseparable and $L'_i\/K(Y)$ etale. Thus, taking $A' = product_(i=1)^m L'_i$, $f_eta: X_eta -> eta$ factors as: 
  $
    underbrace(X_eta, Spec(A)) ->^(g_eta) underbrace(X'_eta, Spec(A')) ->^(h_eta) underbrace(eta, Spec(K(Y)))
  $
  where $g_eta$ is finite surjective radicial and $h_eta$ is finite etale. By @passage-to-limit-of-morphisms and @passage-to-limit-of-properties (where radicial also descends along the limit, since radicial = diagonal being surjective, and surjectivity descends along the limit) applied at $eta = invlim_(emptyset != V subset Y #[affine]) V$, we see that there exists a nonempty open $V subset Y$ s.t. $f_V: f^(-1)(V) -> V$ factors as: 
  $
    f_V: f^(-1)(V) ->^(g_V) V' ->^(h_V) V
  $
  where $g_V$ is finite surjective radicial and $h_V$ is finite etale. 

  By performing one more base change along $V -> Y$ and using (Finite) (@pbc-finite) again, we may further assume that $f: X -> Y$ factors as $f: X ->^g X' ->^h Y$ with $g$ finite surjective radicial, and $h$ a finite etale covering. Now $f_* cal(F) = h_* g_* cal(F)$. 

  - Since $g$ is finite surjective radicial, it is a universal homeomorphism. By topological invariance, $cal(G) = g_* cal(F)$ is constructible (as it is noetherian as described in @constructible-sheaves-first-props (4), say). 

  - Since $h$ is finite etale, by @fet-lower-star-is-lower-shriek, $h_* = h_!$. By @constructible-sheaves-first-props (4), we may find some etale quasi-compact $phi: V -> X'$ and a surjection $phi_! ul(Lambda) ->> cal(G)$. Since $h_! = h_*$ is exact, we have a surjection $(h compose phi)_! ul(Lambda) ->> h_* cal(G)$. Now $h compose phi$ is etale quasi-compact, so $(h compose phi)_! ul(Lambda)$ is constructible by @constructible-sheaves-first-props (3). Thus by @constructible-sheaves-first-props (5), $h_* cal(G)$ is constructible as a quotient of $(h compose phi)_! ul(Lambda)$. 

  As such, $f_* cal(F)$ is now constructible, hence l.c.c. when restricted to some nonempty open of $V$. We are thereby done.  
  
  (2) The abelian group case follows from the $Lambda$-module case, by first resolving $cal(F) arrow.r.hook g_* ul(M)$ for a finite $ZZ\/n$-module $M$, and then note that every finite $ZZ\/n$-module $M$ can be embedded into some $(ZZ\/n)^(oplus m)$. We first claim that: 

  - If for each geometric point $ol(x)$ of $X$, we can find a finite $Lambda$-module $G$, a finite morphism $g: Z -> X$ and a morphism $phi: cal(F) -> g_* ul(G)_Z$ s.t. $phi$ induces an injection on stalks $cal(F)_(ol(x)) -> (g_* ul(G)_Z)_(ol(x))$ at $x$, then we are done. 

  #proof_[Proof of claim][
    Fix a finite stratification by locally closed subschemes $X = union.sq.big_i X_i$ s.t. each $cal(F)|_(X_i)$ is l.c.c, and for each stratum $X_i$ there are finitely many irreducible components, with finitely many generic points $eta_(i,j)$. Now for each $eta_(i,j)$, pick: 
    $
      phi_(i,j): cal(F) -> g_(i,j,*) ul(G_(i,j))_Z
    $
    for some $G_(i,j)$ finite abelian, s.t. $phi_(i,j)$ is injective on stalks at $ol(eta_(i,j))$. Now form the direct sum: 
    $
      phi = oplus.big_(i,j) phi_(i,j): cal(F) -> oplus.big_(i,j) g_(i,j,*) ul(G_(i,j))_Z
    $
    and so $ker(phi)_(ol(eta_(i,j))) = 0$ for each $i,j$. Furthermore, $ker(phi) subset cal(F)$ and so $ker(phi)|_(X_i) subset cal(F)|_(X_i)$. 

    #lemma[
      Let $X$ be a noetherian scheme, $cal(F) in cAb(X_et, Lambda)$ be a l.c.c sheaf of $Lambda$-modules, and $cal(G) subset cal(F)$ be a subsheaf s.t. $cal(G)_(ol(eta)) = 0$ for all $eta in X$ being the generic point of an irreducible component of $X$. Then $cal(G) = 0$. 
    ]
    #proof[
      For any geometric point $ol(x)$ of $X$, pick $eta$ the generic point of some irreducible component of $X$ containing $x$, and $ol(eta)$ any geometric point above $eta$ generalizing $ol(x)$. We have a commutative diagram: 
      // https://q.uiver.app/#r=typst&q=WzAsNCxbMCwwLCJjYWwoRilfKG9sKHgpKSJdLFsxLDAsImNhbChGKV8ob2woZXRhKSkiXSxbMSwxLCJjYWwoRylfKG9sKGV0YSkpIl0sWzAsMSwiY2FsKEcpXyhvbCh4KSkiXSxbMCwxLCJzcCJdLFszLDAsIiIsMix7InN0eWxlIjp7InRhaWwiOnsibmFtZSI6Imhvb2siLCJzaWRlIjoiYm90dG9tIn19fV0sWzIsMSwiIiwyLHsic3R5bGUiOnsidGFpbCI6eyJuYW1lIjoiaG9vayIsInNpZGUiOiJib3R0b20ifX19XSxbMywyLCJzcCIsMl1d
      #align(center, diagram({
        node((0, 0), [$cal(F)_(ol(x))$])
        node((1, 0), [$cal(F)_(ol(eta))$])
        node((1, 1), [$cal(G)_(ol(eta))$])
        node((0, 1), [$cal(G)_(ol(x))$])
        edge((0, 0), (1, 0), [$sp$], label-side: left, "->")
        edge((0, 1), (0, 0), "hook'->")
        edge((1, 1), (1, 0), "hook'->")
        edge((0, 1), (1, 1), [$sp$], label-side: right, "->")
      }))
      Since $cal(F)$ is l.c.c, $sp: cal(F)_(ol(x)) -> cal(F)_(ol(eta))$ is an isomorphism. Thus $cal(G)_(ol(x)) -> cal(G)_(ol(eta))$ is injective. But $cal(G)_(ol(eta)) = 0$, so $cal(G)_(ol(x)) = 0$, and this concludes the proof that $cal(G) = 0$. 
      /*
      Let $X$ have irreducible components $X_1, dots.c, X_m$ equipped with reduced substructure. Each $cal(F)|_(X_i)$ is l.c.c. with vanishing stalks on the generic point. If we can prove that each $cal(G)|_(X_i) = 0$, we may conclude by @surjective-pullback-conservative applied to $union.sq.big_(i=1)^m X_i -> X$. 

      Thus, replacing $X$ with $X_i$, $cal(F)$ with $cal(F)|_(X_i)$, $cal(G)$ with $cal(G)|_(X_i)$, we may assume that $X$ is integral with generic point $eta$. Now pick an etale cover $U ->> X$ s.t. $cal(F)|_U cong ul(G)_U$. We may refine $U$ to be noetherian since $X$ is noetherian. Note that all generic points $u$ of $U$ are sent to $eta in X$, so $(cal(G)|_U)_(ol(u)) = cal(G)|_(ol(eta))$. By applying @surjective-pullback-conservative, and replacing $X$ with irreducible components of $U$, we may assume that: 

      - $X$ is integral noetherian and $cal(F) = ul(G)_X$ for a finite $Lambda$-module $G$. 

      For any $U in Et_X$, since $X$ is noetherian, $U$ is locally noetherian and so a disjoint union of its connected components which are noetherian. To show that $cal(G) = 0$, it suffices to prove that every $s in cal(G)(U)$ vanishes for connected $U in Et_X$. However, $cal(G)(U) subset ul(G)_X (U) = G$, and for a point $u in U$ lying above $eta in X$, taking stalks: 
      $
        (-)_(ol(u)): G = cal(F)(U) -> cal(F)_(ol(eta)) = G
      $
      is just the identity. Thus, since $s_(ol(u)) in cal(G)_(ol(eta)) = 0$, $s = 0$. */
    ]
    By lemma, $ker(phi)|_(X_i) = 0$ for each $i$. Applying @surjective-pullback-conservative to $union.sq.big_i X_i -> X$ concludes that $ker(phi) = 0$ and $phi$ is injective. /*Finally, we embed each finite group $G_(i,j)$ into a finite direct sum $(ZZ\/n)^(oplus m_(i,j))$ for some uniform $n$, we replace $G_(i,j)$ with $ZZ\/n$, and we have found finitely many finite morphisms $g_k: Z_k -> X$ and an injection $cal(F) arrow.r.hook oplus.big_k g_(k,*) ul(ZZ\/n)$. Finally, we form the disjoint union $g: Z := union.sq.big_k Z_k -> X$, and so we have an injection $cal(F) -> g_* ul(ZZ\/n)$. */Finally, we take $M = oplus.big_(i,j) G_(i,j)$ and so we have found a finite $Lambda$-module $M$, and finitely many finite morphisms $g_k: Z_k -> X$, with an injection: 
    $
      cal(F) arrow.r.hook oplus.big_k g_(k,*) ul(M)
    $
    Finally, we form the disjoint union $g: Z := union.sq.big_k Z_k -> X$, and so we have an injection $cal(F) -> g_* ul(M)$.  
  ]

  For each geometric point $ol(x)$ of $X$, it remains to find a finite $Lambda$-module $G$, a finite morphism $g: Z -> X$ and a morphism $phi: cal(F) -> g_* ul(G)_Z$ s.t. $phi$ induces an injection on stalks $cal(F)_(ol(x)) -> (g_* ul(G)_Z)_(ol(x))$ at $x$. 

  Let $Z = ol({x}) subset X$ equipped with the reduced induced subscheme structure, which makes $Z$ an integral scheme with generic point $x$ and function field $K := K(Z) = k(x)$. Now $cal(F)_(ol(x))$ is a finite $Lambda$-module under a $Gal_K$-action, so there exists a finite Galois extension $L\/K$ s.t. $Gal_L$ acts trivially on $cal(F)_(ol(x))$ (by intersecting the stabilizers of a finite set of generators). 

  Take the normalization $nu: Y -> Z$ where $Y$ is the normalization of $Z$ in $L$, making $Y$ a normal integral scheme and $nu$ an integral morphism. Since $L\/K$ is finite, $L = K(Y)$ (by checking on affine opens). Let $y in Y$ be the generic point of $Y$, with $k(y) = L$, and we have $nu(y) = x$. Now $cal(F)|_y$ is the constant sheaf $ul(G)_y$ since $Gal_L$ acts trivially on the finite abelian group $cal(F)_(ol(x))$. From adjunction, the isomorphism $cal(F)|_y -> ul(G)_y$ gives a morphism $cal(F)|_Y -> y_* ul(G)_y$, hence a morphism $phi: cal(F) -> f_* y_* ul(G)_y$, where $f: Y ->^nu Z arrow.r.hook X$. 

  #lemma(name: <generic-pt-pushforward-of-const-shv-on-normal-sch>)[
    Let $X$ be a integral normal scheme with function field $K$. Then the inclusion of the generic point $eta: eta = Spec(K) -> X$ satisfies: 
    $
      eta_* ul(G)_eta cong ul(G)_X
    $
  ]
  #proof[
    A canonical map $ul(G)_X -> eta_* ul(G)_eta$ is obtained from adjunction $eta^(-1) ul(G)_X cong ul(G)_eta$. On the other hand, for any geometric point $ol(x)$ of $X$, 
    $
      (eta_* ul(G)_eta)_(ol(x)) = Gamma(eta times_X tilde(X)_(ol(x)), ul(G)_eta|_(eta times_X tilde(X)_(ol(x)))) =  Gamma(eta times_X tilde(X)_(ol(x)), ul(G)_(eta times_X tilde(X)_(ol(x))))
    $
    Since $cal(O)_(X,x)$ is a normal local domain, so is the strict henselization $cal(O)_(X,x)^#[sh]$ by @permanence-of-properties-under-henselization (3). Thus $eta times_X Spec(cal(O)_(X,x)^#[sh])$ is the spectrum of a localization of $cal(O)_(X,x)^#[sh]$ by checking locally, i.e. the spectrum of an integral domain, which is irreducible. Thus $Gamma(eta times_X tilde(X)_(ol(x)), ul(G)_(eta times_X tilde(X)_(ol(x)))) = G$, and so the canonical map $ul(G)_X -> eta_* ul(G)_eta$ is an isomorphism. 
  ]
  As such, we have defined a morphism $phi: cal(F) -> f_* ul(G)_Y$, where $f: Y ->^nu Z arrow.r.hook X$ is integral. This is our desired morphism, since taking stalks at $ol(x)$, we get a commutative diagram by unfolding the adjunction: 
  // https://q.uiver.app/#r=typst&q=WzAsNCxbMCwwLCJjYWwoRilfKG9sKHgpKSJdLFsxLDAsIihjYWwoRil8X1kpXyhvbCh4KSkiXSxbMSwxLCIodWwoRylfWSlfKG9sKHkpKSJdLFswLDEsIihmXyp1bChHKSlfKG9sKHgpKSJdLFswLDNdLFszLDJdLFswLDFdLFsxLDJdXQ==
  #align(center, diagram({
    node((-1, -1), [$cal(F)_(ol(x))$])
    node((0, -1), [$(cal(F)|_Y)_(ol(x))$])
    node((0, 0), [$(ul(G)_Y)_(ol(y))$])
    node((-1, 0), [$(f_*ul(G))_(ol(x))$])
    edge((-1, -1), (-1, 0), "->", $phi_(ol(x))$)
    edge((-1, 0), (0, 0), "->")
    edge((-1, -1), (0, -1), "=")
    edge((0, -1), (0, 0), "=")
  }))
  and so $phi_(ol(x))$ is injective. 

  Had $f$ been finite, we would have been done. However, in general $f$ would only be integral. Note that $Y = invlim_i Y_i$ is the projective limit of $Y_i = SPec(cal(A)_i)$, $cal(A)_i$ being the directed system of finite coherent $cal(O)_Z$-subalgebras of $nu_* cal(O)_Y$. Now each $Y_i$ is integral, and $f_i: Y_i -> Z -> X$ is finite. By @relative-limit-formula-for-schemes,
  $
    f_* ul(G)_Y = dirlim_i f_(i,*) ul(G)_(Y_i)
  $
  so we have a morphism $phi: cal(F) -> dirlim_i f_(i,*) ul(G)_(Y_i)$ injective on stalks at $ol(x)$.

  #lemma[
    Let $cal(F) in cAb(X_et, Lambda)$ be a constructible sheaf, and ${cal(G)_i}_(i in I)$ be a directed system of sheaves of $Lambda$-modules. Then: 
    $
      Hom_(cAb(X_et,Lambda)) (cal(F), dirlim_(i in I) cal(G)_i) = dirlim_(i in I) Hom_(cAb(X_et,Lambda)) (cal(F), cal(G)_i)
    $ 
  ]
  #proof[
    We first show that for quasi-compact etale $f: U -> X$ and $cal(F) = f_! ul(Lambda)$, this result holds. Indeed, by adjunction, this is equivalent to giving a morphism: 
    $
      ul(Lambda) -> f^(-1) (dirlim_(i in I) cal(G)_i) = dirlim_(i in I) f^(-1) cal(G)_i
    $
    i.e. every section of $dirlim_(i in I) f^(-1) cal(G)_i$ comes from one of the $f^(-1)cal(G)_i$'s. Now by @limit-formula-for-sheaves, 
    $
      Gamma(U, dirlim_(i in I) f^(-1) cal(G)_i) = dirlim_(i in I) Gamma(U, f^(-1) cal(G)_i)
    $
    /*and taking $n$-torsion (being a kernel, i.e. a finite limit) commutes with directed limits, we have: */
    We thus have: 
    $
      Hom(ul(Lambda), dirlim_(i in I) f^(-1) cal(G)_i) = dirlim_(i in I) Hom(ul(Lambda), f^(-1) cal(G)_i)
    $ 
    and we are done. 

    Now we return to the general case. Pick quasi-compact etale $f: U -> X$ and $g: V -> X$ with an exact sequence: 
    $
      g_! ul(Lambda) -> f_! ul(Lambda) -> cal(F) -> 0
    $
    according to @constructible-sheaves-first-props (4). Now the rest is an abstract categorical argument: 
    $
      & Hom (cal(F), dirlim_(i in I) cal(G)_i) = Hom(coker(g_! ul(Lambda) -> f_! ul(Lambda)), dirlim_(i in I) cal(G)_i) \
      =& ker(Hom(f_! ul(Lambda), dirlim_(i in I) cal(G)_i) -> Hom(g_! ul(Lambda), dirlim_(i in I) cal(G)_i)) \
      =& ker(dirlim_(i in I) Hom(f_! ul(Lambda), cal(G)_i) -> dirlim_(i in I) Hom(g_! ul(Lambda), cal(G)_i)) #[by results for $f_! ul(Lambda)$] \
      =& dirlim_(i in I) ker(Hom(f_! ul(Lambda), cal(G)_i) ->Hom(g_! ul(Lambda), cal(G)_i)) \
      =& dirlim_(i in I) Hom(cal(F), cal(G)_i)
    $
  ]
  Thus, $phi: cal(F) -> dirlim_i f_(i,*) ul(G)_(Y_i)$ factors into some $phi_i: cal(F) -> f_(i,*) ul(G)_(Y_i)$. Furthermore, $phi$ is injective on stalks at $ol(x)$ and $cal(F)_(ol(x))$ is a finite group, so $phi_i$ is injective on stalks at $ol(x)$ up to enlarging the stage $i$. Taking $phi_i$ would suffice. 
]

Finally, we note that the constructible sheaves define a thick subcategory of $cAb(X_et, Lambda)$, hence triangulated subcategories of $D^bullet (X_et, Lambda)$: 

#construction(name: <constructible-derived-categories>)[
  Let $X$ be a noetherian scheme and $Lambda$ be a noetherian ring. By @constructible-sheaves-first-props (5), the full subcategory $cAb_c (X_et, Lambda)$ of $cAb(X_et, Lambda)$ consisting of constructible sheaves of $Lambda$-modules, and the full subcategory $cAb_c (X_et)$ of $cAb(X_et)$ consisting of constructible sheaves of abelian groups, are thick subcategories. Thus, for $bullet in {#`blank`, -, +, b}$, we have: 

  - $D^bullet_c (X_et, Lambda)$ is a triangulated subcategory of $D^bullet (X_et, Lambda)$; 

  - $D^bullet_c (X_et)$ is a triangulated subcategory of $D^bullet (X_et)$. 
]
