#import "void-import.typ": *

== Etale fundamental group $pi_1^et (X)$

Mimicking the topological case, we define the etale fundamental group: 

#definition(name: <defn-etale-fundamental-group>)[
  The *etale fundamental group* of $X$ w.r.t. base point $ol(x)$ is defined as:
  $
    pi_1^et (X, ol(x)) := Aut(F_(ol(x)))
  $
  which is the automorphism group of the fiber functor $F_(ol(x)) : FEt_X -> cSet^"fin"$. That is, it is the group of natural isomorphisms $gamma: F_(ol(x)) -> F_(ol(x))$. 
]

#lemma(name: <galois-grp-exact-seq>)[
  Let $f: Z -> Y$ be a morphism in $FEt_X$ where $Y, Z$ are both finite. Assuming $Z\/X$ and $Y\/X$ are both Galois, $Z\/Y$ must also be Galois with a natural exact sequence: 
  $
    1 -> Aut(Z\/Y) -> Aut(Z\/X) -> Aut(Y\/X) -> 1
  $
]
#proof[
  We first construct the morphism $Phi: Aut(Z\/X) -> Aut(Y\/X)$. Pick compatible geometric points $ol(z)$ of $Z$, $ol(y)$ of $Y$ and $ol(x)$ of $X$. For any fixed $sigma in Aut(Z\/X)$, consider the geometric point $f(sigma(ol(z)))$ of $Y$. This geometric point lies above $ol(x)$ and $Aut(Y\/X)$ acts faithfully and transitively on the fiber $F_(ol(x)) (Y)$ since $Y\/X$ is Galois. Therefore, there exists a unique $tau in Aut(Y\/X)$ s.t. $tau(ol(y)) = f(sigma(ol(z)))$. We then define $Phi(sigma) = tau$. 

  In other words, $tau = Phi(sigma)$ is the unique element of $Aut(Y\/X)$ s.t. $tau(f(ol(z))) = f(sigma(ol(z)))$. Since $Z$ is connected, any $X$-morphism $Z -> Y$ agreeing on a single geometric point must be equal, so this condition is equivalent to $tau compose f = f compose sigma$. In particular, $Phi$ is independent from the choice of $ol(z),ol(y),ol(x)$. Furthermore, $Phi$ is indeed a group homomorphism: 
  $
    f compose sigma_1 compose sigma_2 = Phi(sigma_1) compose f compose sigma_2 = Phi(sigma_1) compose Phi(sigma_2) compose f
  $
  and so $Phi(sigma_1 compose sigma_2) = Phi(sigma_1) compose Phi(sigma_2)$. We now consider the kernel of $Phi$. $sigma in Aut(Z\/X)$ is in $ker(Phi)$ if and only if $f = f compose sigma$, i.e. when $sigma$ is an $Y$-morphism. In other words, we have obtained an exact sequence: 
  $
    1 -> Aut(Z\/Y) -> Aut(Z\/X) ->^Phi Aut(Y\/X)
  $
  We then prove right exactness and that $Z\/Y$ is Galois simultaneously. First note that $abs(F_(ol(x))(Z)) = abs(F_(ol(x))(Y)) abs(F_(ol(y))(Z))$, since for any other geometric point $ol(y')$ of $Y$ above $ol(x)$, $abs(F_(ol(y'))(Z)) = abs(F_(ol(y))(Z))$ by flatness. Now: 
  $
    abs(F_(ol(x))(Y)) = abs(Aut(Y\/X)) >= abs(im(Phi)) = (abs(Aut(Z\/X)))/(abs(Aut(Z\/Y))) = (abs(F_(ol(x))(Z)))/(abs(Aut(Z\/Y)))
  $
  and so $abs(Aut(Z\/Y)) >= abs(F_(ol(x))(Z))\/abs(F_(ol(x))(Y)) = abs(F_(ol(y))(Z))$. Meanwhile, $<=$ holds automatically since $Aut(Z\/Y)$ acts faithfully on $F_(ol(y))(Z)$. Thus equality holds, $Z\/Y$ is Galois and $im(Phi) = Aut(Y\/X)$. We then see that $Z\/Y$ is Galois and also get the exact sequence: 
  $
    1 -> Aut(Z\/Y) -> Aut(Z\/X) ->^Phi Aut(Y\/X) -> 1
  $
]

#theorem(name: <pi1et-as-invlim>)[
  The etale fundamental group is the limit of a projective system of Galois groups. More explicitly, let $I$ be the directed set of pointed Galois covering spaces $(X_i, ol(x_i)) -> (X, ol(x))$. Then:
  $
    pi_1^et (X, ol(x)) = invlim_(i in I) Aut(X_i\/X)^opp
  $
  is a projective limit under the transition maps given by @galois-grp-exact-seq. 

  In particular, this equips $pi_1^et (X, ol(x))$ with the structure of a profinite group. 
  
  #example[
    In the example $X = Spec(K)$, $I$ is the category of all intermediate Galois extensions $K subset L subset K^sep$. We then see that:
    $
      pi_1^et (Spec(K), Spec(K^sep)) = invlim_(i in I) Gal(L\/K) = Gal(K^sep\/K)
    $
    is the absolute Galois group of $K$.
  ]
]
#proof[
  We first show that this projective limit is well-defined. The index category $I$ is cofiltered.

  For every Galois covering space $(X_i, ol(x_i))$, its automorphism group $Aut(X_i\/X)$ acts on $F_(ol(x)) (X_i)$ transitively and faithfully. Thus there exists an isomorphism: 
  $
    eta_i: Aut(X_i\/X) -> F_(ol(x)) (X_i), g |-> g(ol(x_i))
  $

  We construct a map: 
  $
    Psi: pi_1^et (X, ol(x)) = Aut(F_(ol(x))) &-> invlim_(i in I) Aut(X_i\/X)^opp \

    gamma &|-> (eta_i^(-1) (gamma(ol(x_i))))_(i in I)
  $
  In other words, for each $X_i$, we send $gamma$ to the unique $sigma_i in Aut(X_i\/X)$ s.t. $sigma_i (ol(x_i)) = gamma(ol(x_i))$. 
  
  Each $pi_1^et (X, ol(x)) -> Aut(X_i\/X)^opp, gamma |-> eta_i^(-1) (gamma(ol(x_i)))$ is a group homomorphism. Indeed, given $gamma, delta in pi_1^et (X, ol(x))$ with images $sigma_gamma, sigma_delta$ under this map, 
  $
    sigma_gamma sigma_delta (ol(x_i)) = sigma_gamma (delta(ol(x_i))) = delta (sigma_gamma (ol(x_i))) = delta(gamma(ol(x_i)))
  $
  (Note that the order of $gamma$ and $delta$ is reversed. This is the purpose of the opposite group in $Aut(X_i\/X)^opp$.)
  
  They are compatible with the projective system $I$. Indeed, given a morphism $f: (X_j, ol(x_j)) -> (X_i, ol(x_i))$. Let $sigma_i (ol(x_i)) = gamma(ol(x_i))$ and $sigma_j (ol(x_j)) = gamma(ol(x_j))$. Then: 
  $
    sigma_i (f(ol(x_j))) = sigma_i (ol(x_i)) = gamma(ol(x_i)) = gamma(f(ol(x_j))) = f(gamma(ol(x_j))) = f(sigma_j (ol(x_j)))
  $
  where $gamma(f(ol(x_j))) = f(gamma(ol(x_j)))$ by naturality of $gamma$. Thus $sigma_j |-> sigma_i$ under the map $Aut(X_j\/X) -> Aut(X_i\/X)$. 
  
  It suffices to show that $Psi$ is injective and surjective. For injectivity, if $gamma in ker(Psi)$, then it is sent to $id_(X_i)$ for each $i$, i.e. $gamma(ol(x_i)) = ol(x_i)$ for each $i$. Then for every pointed etale covering space $(Y, ol(y)) -> (X, ol(x))$, we may form its Galois closure, which is one of the $X_i$'s: 
  $
    (X_i, ol(x_i)) ->^f (Y, ol(y)) -> (X, ol(x))
  $
  and then $gamma(ol(y)) = gamma(f(ol(x_i))) = f(gamma(ol(x_i))) = f(ol(x_i)) = ol(y)$. That is, $gamma(ol(y)) = ol(y)$ for every $Y in FEt_X$ and every $ol(y) in F_(ol(x)) (Y)$. Thus $gamma$ as a natural automorphism of $F_(ol(x))$ is the identity morphism. 

  It remains to prove surjectivity. Fix an element $(sigma_i)_(i in I) in invlim_(i in I) Aut(X_i\/X)^opp$. We define a candidate $gamma in Aut(F_(ol(x)))$ as follows: For every $Y in FEt_X$ and every $ol(y) in F_(ol(x)) (Y)$, pick a Galois covering space $X_i$ with a covering $(X_i, ol(x_i)) ->^f (Y, ol(y)) -> (X, ol(x))$. We then define $gamma(ol(y)) := f(sigma_i (ol(x_i)))$. This construction is independent from the choice of $i$. Indeed, for two choices $i,j$, there exists a third $k in I$ with a commutative diagram: 
  // https://q.uiver.app/#r=typst&q=WzAsNSxbMCwxLCIoWF9rLG9sKHhfaykpIl0sWzEsMCwiKFhfaSxvbCh4X2kpKSJdLFsxLDIsIihYX2osb2woeF9qKSkiXSxbMiwxLCIoWSxvbCh5KSkiXSxbMywxLCIoWCxvbCh4KSkiXSxbMCwxLCJnX2kiXSxbMCwyLCJnX2oiLDJdLFsxLDMsImZfaSJdLFsyLDMsImZfaiIsMl0sWzMsNF1d
  #context align(center, diagram({
    node((-2, 0), [$(X_k,ol(x_k))$])
    node((-1, -1), [$(X_i,ol(x_i))$])
    node((-1, 1), [$(X_j,ol(x_j))$])
    node((0, 0), [$(Y,ol(y))$])
    node((1, 0), [$(X,ol(x))$])
    edge((-2, 0), (-1, -1), [$g_i$], label-side: left, "->")
    edge((-2, 0), (-1, 1), [$g_j$], label-side: right, "->")
    edge((-1, -1), (0, 0), [$f_i$], label-side: left, "->")
    edge((-1, 1), (0, 0), [$f_j$], label-side: right, "->")
    edge((0, 0), (1, 0), "->")
    edge((-2, 0), (0, 0), "->", [$f_k$], label-side: center)
  }, crossing-fill: thm-box-curr-color()))
  Thus to prove that $gamma(ol(y))$ defined with $i$ and $j$ agrees, it suffices to prove that the definition with $i$ and $k$ agrees. Indeed, 
  $
    f_k (sigma_k (ol(x_k))) &= f_i (g_i (sigma_k (ol(x_k)))) \
    &= f_i (sigma_i (g_i (ol(x_k)))) #[by definition of the transition morphisms] \
    &= f_i (sigma_i (ol(x_i)))
  $
  It then remains to prove that $gamma$ defined this way, a priori a set map $F_(ol(x)) (Y) -> F_(ol(x)) (Y)$ for every $Y in FEt_X$, is a natural automorphism of $F_(ol(x))$. For every morphism $f: (Z, ol(z)) -> (Y, ol(y))$ in $FEt_X$, we aim to show that $f(gamma(ol(z))) = gamma(ol(y)) = gamma(f(ol(z)))$. Indeed, pick a Galois closure $(X_i, ol(x_i)) -> (Y, ol(y))$, and then pick by existence of composite covering space (@fet-first-props (2)) and existence of Galois closure (@galois-closure-exists) some $(X_j, ol(x_j))$ fitting in a commutative diagram: 
  // https://q.uiver.app/#r=typst&q=WzAsNCxbMCwwLCIoWF9qLG9sKHhfaikpIl0sWzIsMCwiKFhfaSxvbCh4X2kpKSJdLFswLDIsIihaLCBvbCh6KSkiXSxbMiwyLCIoWSwgb2woeSkpIl0sWzIsMywiZiIsMl0sWzEsMywiZl9pIl0sWzAsMSwiZyJdLFswLDIsImZfaiIsMl1d
  #align(center, diagram({
    node((-1, -1), [$(X_j,ol(x_j))$])
    node((1, -1), [$(X_i,ol(x_i))$])
    node((-1, 1), [$(Z, ol(z))$])
    node((1, 1), [$(Y, ol(y))$])
    edge((-1, 1), (1, 1), [$f$], label-side: right, "->")
    edge((1, -1), (1, 1), [$f_i$], label-side: left, "->")
    edge((-1, -1), (1, -1), [$g$], label-side: left, "->")
    edge((-1, -1), (-1, 1), [$f_j$], label-side: right, "->")
  }))
  Now: 
  $
    gamma(ol(y)) &= f_i (sigma_i (ol(x_i))) #[by definition of $gamma$] \
    &= f_i (sigma_i (g(ol(x_j)))) \
    &= f_i (g(sigma_j (ol(x_j)))) #[by definition of the transition morphisms] \
    &= f(f_j (sigma_j (ol(x_j)))) \
    &= f(gamma(ol(z))) #[by definition of $gamma$]
  $
  We are thereby done showing that $Psi$ is surjective. In summary, we have constructed a canonical isomorphism: 
  $
    Psi: pi_1^et (X, ol(x)) &-> invlim_(i in I) Aut(X_i\/X)^opp \
    gamma &|-> (sigma_i)_(i in I) #[where] sigma_i (ol(x_i)) = gamma(ol(x_i))
  $
]

#corollary[
  Under the profinite topology on $pi_1^et (X, ol(x))$ given by:
  $
    pi_1^et (X, ol(x)) = invlim_(i in I) Aut(X_i\/X)^opp
  $
  For every $Z in FEt_X$, the action of $pi_1^et (X, ol(x))$ on $F_(ol(x)) (Z)$ is continuous. This defines a functor: 
  $
    F_(ol(x)): FEt_X -> GSet(pi_1^et (X, ol(x)))^#[fin,cont]
  $
  from $FEt_X$ to the category of finite sets with a continuous $pi_1^et (X, ol(x))$-action. 
]
#proof[
  The only thing left to show is that $pi_1^et (X, ol(x))$ acts continuously on $F_(ol(x)) (Z)$. Indeed, pick any Galois closure $X_i -> Z$ and by construction of the isomorphism $pi_1^et (X, ol(x)) = invlim_(i in I) Aut(X_i\/X)^opp$, the action of an element $(sigma_i)_(i in I) in pi_1^et (X, ol(x))$ on $F_(ol(x)) (Z)$ is determined by $sigma_i$. Thus a normal subgroup of $pi_1^et (X, ol(x))$ of finite index fixes $F_(ol(x))(Z)$. 
]

#theorem[
  $
    F_(ol(x)): FEt_X -> GSet(pi_1^et (X, ol(x)))^#[fin,cont]
  $
  defines an equivalence of categories, fitting in the diagram: 
  // https://q.uiver.app/#r=typst&q=WzAsMyxbMCwwLCJGRXRfWCJdLFsyLDAsIkdTZXQocGlfMV5ldCAoWCwgb2woeCkpKV4jW2Zpbixjb250XSJdLFsxLDIsImNTZXReI1tmaW5dIl0sWzAsMSwiRl8ob2woeCkpIl0sWzAsMiwiRl8ob2woeCkpIiwyXSxbMSwyLCIjW2ZvcmdldF0iXV0=
  #align(center, diagram({
    node((-1, -1), [$FEt_X$])
    node((1, -1), [$GSet(pi_1^et (X, ol(x)))^#[fin,cont]$])
    node((0, 1), [$cSet^#[fin]$])
    edge((-1, -1), (1, -1), [$F_(ol(x))$], label-side: left, "->")
    edge((-1, -1), (1, -1), [$tilde$], label-side: right)
    edge((-1, -1), (0, 1), [$F_(ol(x))$], label-side: right, "->")
    edge((1, -1), (0, 1), [$#[forget]$], label-side: left, "->")
  }, spacing: 2em))
]
#proof[
  For essential surjectivity: 
  #proof[
    Let $T$ be a finite set with a continuous $pi_1^et (X, ol(x))$-action. We may decompose $T$ into its $pi_1^et (X, ol(x))$-orbits ${T_s}$. If for each $T_s$ we may find some $Z_s in FEt_X$ s.t. $F_(ol(x)) (Z_s) cong T_s$ as $pi_1^et (X, ol(x))$-sets, then $F_(ol(x)) (union.sq.big_s Z_s) cong T$ as $pi_1^et (X, ol(x))$-sets. Thus, we are reduced to the case that $T$ is transitive under the action. 

    Since $G = pi_1^et (X, ol(x))$ is profinite and acts transitively on $T$, $T cong G\/H$ as $G$-sets for some finite index subgroup $H <= G$. By the construction of $G$ as a projective limit, there exists some $i$ and a normal subgroup $N$ of $G$ s.t. $N <= H$ and $G\/N = Aut(X_i\/X)$. Let $ol(H)$ be the image of $H$ in $G\/N = Aut(X_i\/X)$. Then as $G$-sets, $T cong G\/H cong Aut(X_i\/X)\/ol(H)$. 

    We may take $Z = X_i\/ol(H)$, constructed according to @galois-theory-of-coverings (2). By @affine-sch-quotient (2), the fibers of $X_i -> Z$ are precisely $ol(H)$-orbits, i.e. $Spec(k(z)) = (X_i)_z\/ol(H)$. Then passing to the geometric fiber is a flat base change and preserves the quotient, so $F_(ol(x))(Z) cong F_(ol(x))(X_i)\/ol(H) cong Aut(X_i\/X)\/ol(H) cong T$ as $Aut(X_i\/X)$-sets, hence as $G$-sets. 

    #suppress-qed
  ]

  For full faithfulness:
  #proof[
    For any $Z, Y in FEt_X$, consider: 
    $
      F_(ol(x)): Hom_X (Z, Y) -> Hom_(pi_1^et (X, ol(x))) (F_(ol(x)) (Z), F_(ol(x)) (Y))
    $
    We want to show that this map is bijective. Write $Z, Y$ as a union of their connected components: $Z = union.sq.big_t Z_t, Y = union.sq.big_s Y_s$, and then we will be dealing with: 
    $
      Hom_X (Z, Y) = product_t union.sq.big_s Hom_X (Z_t, Y_s) -> Hom_(pi_1^et (X, ol(x))) (F_(ol(x)) (Z), F_(ol(x)) (Y)) = product_t union.sq.big_s Hom_(pi_1^et (X, ol(x))) (F_(ol(x)) (Z_t), F_(ol(x)) (Y_s))
    $
    Thus, we are reduced to proving bijectivity for each $Z_t$ and $Y_s$, and are reduced to the case where $Z, Y$ are connected. 

    - Injectivity: Suppose that two maps $f,g: Z -> Y$ have $F_(ol(x)) (f) = F_(ol(x)) (g)$. Pick some $ol(z) in F_(ol(x)) (Z)$. Since $f(ol(z)) = g(ol(z))$ and $Z$ is connected, by @fet-first-props (1), $f = g$. 

    - Surjectivity: By the universal property of the fiber product, we have: 
      $
        F_(ol(x)) (Y times_X Z) = F_(ol(x)) (Y) times F_(ol(x)) (Z)
      $
      Given any element $phi in Hom_(pi_1^et (X, ol(x))) (F_(ol(x)) (Z), F_(ol(x)) (Y))$, consider its graph $Gamma_phi subset F_(ol(x)) (Y) times F_(ol(x)) (Z) = F_(ol(x)) (Y times_X Z)$. Since $phi$ is $pi_1^et (X, ol(x))$-equivariant, the subset $Gamma_phi$ is $pi_1^et (X, ol(x))$-invariant. From the construction for essential surjectivity, there exists an open-and-closed subscheme $W subset Y times_X Z$ s.t. $F_(ol(x)) (W) cong Gamma_phi$ as $pi_1^et (X, ol(x))$-sets. 

      Consider the projection map $p_Z: W -> Z$. Then by definition, $F_(ol(x)) (p_Z): Gamma_phi -> F_(ol(x)) (Z)$ is projection of a graph to the second factor, hence a bijection. By @fet-first-props (4), $p_Z$ is an isomorphism. Then the morphism: 
      $
        Z -->^(p_Z^(-1)) W -->^(p_Y) Y
      $
      is a morphism in $FEt_X$, and induces the map $F_(ol(x)) (Z) -> Gamma_phi -> F_(ol(x)) (Y)$ on fibers, which is just the map $phi$. 

    #suppress-qed
  ]
  With full faithfulness and essential surjectivity proved, we have seen that $F_(ol(x)): FEt_X -> GSet(pi_1^et (X, ol(x)))^#[fin,cont]$ is indeed an equivalence of categories. 
]

We have thus obtained the full analog of the statement for the topological fundamental group, that $bold("Cov")(X) -> GSet(pi_1^"top" (X, x)), 
(p: X' -> X) |-> p^(-1) (x)$ is an equivalence of categories. We have established Galois theory for schemes and classified $FEt_X$ using the group $pi_1^et (X, ol(x))$. 

#corollary(name: <fet-trivializes-fet-locally>)[
  Every finite etale covering $X' -> X$ is finite etale locally trivial. 
]
#proof[
  There are a few options for this proof, but the fastest way is through the etale fundamental group. 
  Assume that $X$ is connected, since we can trivialize $X'$ separately over each connected component of $X$. Fixing a base point $ol(x)$ of $X$, and from the theory of etale fundamental groups, $X'$ corresponds to an object: 
  $
    S in GSet(pi_1^et (X, ol(x)))^#[fin,cont]
  $
  The action of $pi_1^et (X, ol(x))$ thus factors through a finite quotient, corresponding to a Galois $(Z, ol(z)) in FEt_X$. In other words, $pi_1^et (Z, ol(z))$ acts trivially on $S$. Now $S$, as a $pi_1^et (Z, ol(z))$-set, corresponds to the base change $X' times_X Z -> Z$ in $FEt_Z$, so $X' times_X Z -> Z$ is a trivial covering space, i.e. $X' times_X Z$ is a disjoint union of copies of $Z$. 
]

/*
#date[
  Lecture 5, 2025/10/22
  #set align(left)

  /*
  Recall that last lecture, we introduced $pi_1^et (X, ol(x))$, the etale fundamental group. Let $X$ be a connected noetherian scheme, and fix a geometric point $ol(x): Spec(Omega) -> X$. We then have a functor $FEt_X -> cSet^"fin", (f: Z -> X) |-> f^(-1)(ol(x))$. We equipped $pi_1^et (X, ol(x))$ with a topology by:
  $
    pi_1^et (X, ol(x)) := Aut(F_(ol(x))) < product_(Z in FEt_X) Aut(F_(ol(x)) (Z))
  $
  by the subspace topology of the product topology on the product on the right.
  
  We also concluded that:
  #theorem[
    (Galois theory for $(X, ol(x))$) There is a natural equivalence of categories of $FEt_X$ with $pi_1^et (X, ol(X))"-"cSet^("fin,cont")$, finite sets equipped with a continuous action of $pi_1^et (X, ol(X))$, compatible with $F_(ol(x)) : FEt_X -> cSet^"fin"$ and the forgetful functor $pi_1^et (X, ol(X))"-"cSet^("fin,cont")-> cSet^"fin"$.
  ]
  
  We also gave another description of $pi_1^et$ via Galois covers. Recall that $(f: Z -> X) in FEt_X$ connected is called Galois $:<==> \#Aut(Z\/X) = \#F_(ol(x)) (Z) <==> Z\/Aut(Z\/X)^opp cong X$. Then consider:
  $
    I = {(X_i, ol(x_i)) "pointed Galois coverings over" (X, ol(x))}
  $
  and proved that:
  $
    dirlim_(i in I) Hom_X (X_i, Z) cong F_(ol(x)) (Z) \
    pi_1^et (X, ol(x)) cong invlim_(i in I) Aut(X_i\/X)^opp
  $
  #example[
    Let $X = Spec(K)$, and fix a separable closure $K^sep\/K$. Then:
    $
      pi_1^et (Spec(K), Spec(K^sep)) cong invlim_(L\/K "fin Galois") Gal(L\/K) cong Gal(K^sep\/K)
    $
    is the absolute Galois group.
  ]*/
  
  The key to this description is that:
  
  + Given connected $(Z, ol(z)), (Z', ol(z'))$ pointed etale covering spaces over $(X, ol(x))$, there is at most one map between them compatible with the covering.
  
  + Let $Z$ be a connected etale covering space over $X$, and $G <= Aut(Z\/X)^opp$ be a finite subgroup. Then $Z -> Z\/G$ is a Galois covering with $G cong Aut(Z\/(Z\/G))^opp$.
  
  To see etaleness of $Z -> Z\/G$. We need to check that for any $z in Z$, the inertia subgroup:
  $
    G_i (z) := {g in G: g(z) = z, g "acts by the identity on" κ(z)}
  $
  is trivial. But indeed,
  $
    G_i (z) & = {g in G: g dot ol(z) = ol(z) "where" ol(z) = Spec(κ(z)^sep) -> {z} subset Z}
  $
  can only have a single element by (1).
  
  The point (2) is useful in showing that $FEt_X -> pi_1^et (X, ol(X))"-"cSet^("fin,cont")$ is essentially surjective. Indeed, for any $pi_1^et$-set $T$, we may perform an orbit decomposition. We must then associate an etale covering space with any transitive $pi_1^et$-set $T$. Let $S$ be the stablizer of a point, and $N$ be a finite index normal subgroup of $pi_1^et$ s.t. $N <= S <= pi_1^et$. Then $pi_1^et\/N$ corresponds to a Galois covering $X_i$, and $pi_1^et\/S$ corresponds to the covering $X_i -> X_i\/(S\/N)$.
]*/
