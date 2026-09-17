#import "void-import.typ": *

== Galois covering spaces

We now want to generalize the notion of a Galois extension of fields, and the action of taking the fixed subfield of a subgroup of the Galois group, and establish Galois theory for etale covering spaces.

#definition(name: <defn-galois-covering-space>)[
  A finite etale covering space $Z in FEt_X$ is called *Galois* if:
  
  + $Z$ is connected;
  
  + $Aut(Z\/X)^opp$ acts on $F_(ol(x)) (Z)$ transitively.
  
  Here, the condition (2) is equivalent to condition (2') that $\#Aut(Z\/X)^opp = \#F_(ol(x)) (Z)$, since the same action is known to be faithful by Properties (1). Now for another geometric point $ol(x')$, we know that $\#F_(ol(x)) (Z) = \#F_(ol(x')) (Z)$. Thus the notion of a finite etale covering being Galois is independent from the choice of base point. 
  
  #example[
    Considering the example of $X = Spec(K)$. A finite etale covering $Z -> X$ must have $Z = Spec(A)$ for $A = product_i L_i$.
    
    Then condition (1) for $Spec(A)$ is equivalent to $A = L$ a finite separable extension, and condition (2') is:
    $
      \#Aut(L\/K) = \#Hom_K (L, ol(K))
    $
    i.e. $L\/K$ being normal. In summary, $Spec(A) -> Spec(K)$ is Galois $<==>$ $A = L\/K$ is a Galois extension of fields.
  ]
]

#lemma(name: <galois-closure-exists>)[
  (Existence of Galois closure) For every connected $(Z, ol(z)) in FEt_X$ above $(X, ol(x))$, there exists a Galois covering space $(tilde(Z), ol(tilde(z))) in FEt_X$ together with a morphism $(tilde(Z), ol(tilde(z))) -> (Z, ol(z))$ over $X$:
  // https://q.uiver.app/#r=typst&q=WzAsMyxbMCwwLCIodGlsZGUoWiksIG92ZXJsaW5lKHRpbGRlKHopKSkiXSxbMiwwLCIoWiwgb3ZlcmxpbmUoeikpIl0sWzEsMSwiKFgsb3ZlcmxpbmUoeCkpIl0sWzAsMV0sWzAsMl0sWzEsMl1d
  #align(center, diagram(
    {
      node((-1, -1), [$(tilde(Z), ol(tilde(z)))$])
      node((1, -1), [$(Z, ol(z))$])
      node((0, 0), [$(X,ol(x))$])
      edge((-1, -1), (1, -1), "->")
      edge((-1, -1), (0, 0), "->")
      edge((1, -1), (0, 0), "->")
    },
    spacing: 1.5em,
  ))
  #example[
    In the $X = Spec(K)$ case with geometric point $ol(x)$ given by the embedding $K -> K^sep$, a connected etale covering space $Z -> X$ is a finite separable extension $L/K$ embedded in $K^sep$.
    
    Let $Hom_K (L, K^sep) = {sigma_1, dots.c, sigma_n}$ where $n = [L:K]$ by separability. We then construct the Galois closure as the image:
    $
      im(underbrace(L otimes_K dots.c otimes_K L, n) -> K^sep, x_1 otimes dots.c otimes x_n |-> sigma_1 (x_1) dots.c sigma_n (x_n))
    $
    This is simply the Galois closure of $L$, as defined in field theory. This construction of Galois closure will also motivate the proof of this lemma.
  ]
]
#proof[
  Write $F_(ol(x)) (Z) = {ol(z_1), dots.c, ol(z_n)}$ where $ol(z) = ol(z_1)$, and let $tilde(Z)$ be the connected component of $Z times_X dots.c times_X Z$ ($n$-copies) containing the image of $(ol(z_1), dots.c, ol(z_n))$. Now we have a morphism in $FEt_X$:
  $
    (tilde(Z), ol(tilde(z))) -> (Z times_X dots.c times_X Z, (ol(z_1), dots.c, ol(z_n))) overset(->, "pr"_1) (Z, ol(z_1))
  $
  
  It suffices to prove that $tilde(Z)$ is Galois.
  
  The maps $tilde(Z) arrow.hook.r Z^(times_X n) overset(->, "pr"_i) Z$ are distinct when varying $i$ because they send $ol(tilde(z))$ to $ol(z_i)$ respectively. Since $tilde(Z)$ is connected, by @fet-first-props (1), for any $ol(tilde(omega)) in F_(ol(x)) (tilde(Z))$, its images under these $n$ maps are distinct.
  
  Thus, there exists a permutation $sigma in S_n$ s.t. $"pr"_(sigma(i)) (ol(tilde(z))) = "pr"_i (ol(tilde(omega)))$. Consider a diagram in $FEt_X$:
  // https://q.uiver.app/#r=typst&q=WzAsMyxbMCwwLCJaXih0aW1lcyBuKSJdLFsyLDAsIlpeKHRpbWVzIG4pIl0sWzEsMSwiWiJdLFswLDEsInNpZ21hIl0sWzAsMiwiXCJwclwiXyhzaWdtYShpKSkiLDJdLFsxLDIsIlwicHJcIl9pIl1d
  #align(center, diagram(
    {
      node((-1, -1), [$Z^(times n)$])
      node((1, -1), [$Z^(times n)$])
      node((0, 0), [$Z$])
      edge((-1, -1), (1, -1), [$sigma$], label-side: left, "->")
      edge((-1, -1), (0, 0), [$"pr"_(sigma(i))$], label-side: right, "->")
      edge((1, -1), (0, 0), [$"pr"_i$], label-side: left, "->")
    },
    spacing: 2.5em,
  ))
  Then $sigma$ sends $ol(tilde(z))$ to $ol(tilde(omega)) in tilde(Z)$ and must therefore preserve the connected component $tilde(Z)$. Thus, $sigma$ restricts to an automorphism of $tilde(Z)$ with $sigma(ol(tilde(z))) = ol(tilde(omega))$. We have thus proved by definition that $Aut(tilde(Z)\/X)$ acts transitively on $F_(ol(x)) (tilde(Z))$.
]

With the Galois closure construction done, we now generalize the construction of taking the fixed subfield. 

#definition(name: <defn-quotient-by-finite-group>)[
  Let $G$ be an abstract finite group acting on a scheme $Z$. 

  A $G$-invariant morphism $pi: Z -> Y$ (i.e. $pi compose g = pi$ for all $g in G$) is the (categorical) *quotient of $Z$ by $G$* if there exists a functorial isomorphism for every $X$: 
  // https://q.uiver.app/#r=typst&q=WzAsMyxbMCwwLCJIb20oWiwgWCkiXSxbMiwwLCJIb20oWixYKV5HIl0sWzEsMSwiSG9tKFksIFgpIl0sWzEsMCwiIiwwLHsic3R5bGUiOnsidGFpbCI6eyJuYW1lIjoiaG9vayIsInNpZGUiOiJ0b3AifX19XSxbMiwxLCJleGlzdHMiLDEseyJzdHlsZSI6eyJib2R5Ijp7Im5hbWUiOiJkYXNoZWQifX19XSxbMiwwLCJwaV4qIiwxXV0=
  #context align(center, diagram({
    node((-2, -1), [$Hom(Z, X)$])
    node((0, -1), [$Hom(Z,X)^G$])
    node((-1, 0), [$Hom(Y, X)$])
    edge((0, -1), (-2, -1), "hook->")
    edge((-1, 0), (0, -1), [$exists$], label-side: center, "-->")
    edge((-1, 0), (-2, -1), [$(-) compose pi$], label-side: center, "->")
  }, crossing-fill: thm-box-curr-color()))
]

#proposition(name: <affine-sch-quotient>)[
  Assume that $Z = Spec(B)$ is affine, and set $A = B^G subset B$. Then the map $pi: Z = Spec(B) -> Spec(A) = Y$ has the following properties: 

  + $pi$ is integral. 

  + $pi$ is surjective and closed, so the topology on $Y$ is the quotient topology from $Z$ by $pi$. Fibers of $pi$ are exactly $G$-orbits. 

  + Let $z in Z, y = pi(z) in Y$, and $G_z = {sigma in G: sigma(z) = z}$. Then $k(z)\/k(y)$ is algebraic and normal (i.e. quasi-Galois), and: 
    $
      G_z -> Aut(k(z)\/k(y))
    $
    is surjective. 

  + $(Y, pi)$ is the quotient of $Z$ by $G$. 
]
#proof[
  (1) For any $b in B$, $product_(sigma in G) (X - sigma(b)) in A[X]$, so $pi$ is integral. 

  (2) $A subset B$ is an integral ring extension, so $Spec(B) -> Spec(A)$ is surjective by going-up. For any $J subset B$, $A\/A ∩ J -> B\/J$ is also an integral ring extension, hence surjective. Thus $pi(V(J)) = V(A ∩ J)$. Therefore $pi$ is surjective and closed. 

  Assume that $frak(q), frak(q)' subset B$ lie above the same $frak(p) in Spec(A)$ under $pi$, i.e. $frak(q) ∩ A = frak(q)' ∩ A$. For any $x in frak(q)'$, $product_(sigma in G) sigma(x) in frak(p) = frak(q)' ∩ A subset frak(q)$. Therefore, there exists $sigma in G$ s.t. $x in sigma(frak(q))$. Hence, 
  $
    frak(q)' subset union.big_(sigma in G) sigma(frak(q))
  $
  and by prime avoidance, there exists $sigma in G$ such that $frak(q)' subset sigma(frak(q))$. Since $frak(q)' ∩ A = frak(p) = sigma(frak(q)) ∩ A$ and $A subset B$ is integral, $frak(q)' = sigma(frak(q))$. 
  
  (The reason for $frak(q)' = sigma(frak(q))$ goes as follows: If $A subset B$ is integral, $frak(q)_1 subset frak(q)_2 in Spec(B)$ lies above the same $frak(p) in Spec(A)$, then by passing to the fiber of $Spec(B\/frak(q)_1) -> Spec(B) -> Spec(A)$ corresponding to $frak(p)$, we may assume that $frak(q)_1 = 0$, $B$ is integral and $A$ is a field. An integral domain integral over a field is a field, so $frak(q)_2 = 0 = frak(q)_1$.)

  (3) Base changing $Y$ to the local ring $Spec(cal(O)_(Y,y))$ (which is possible since taking fixed subring is compatible with localization), we may assume that $(A, frak(m))$ is a local ring, and $z$ corresponds to a maximal ideal $frak(q) subset B$ above $frak(m)$. (Primes lying above a given primes in an integral extension cannot have containment relations, as just proved. Thus the primes above $frak(m)$ are all maximal.)
  
  Now $k(z) = B\/frak(q)$ is integral over $k = A\/frak(m)$ since $B$ is. For every $ol(b) in k(z) = B\/frak(q)$, 
  $
    product_(sigma in G) (X - ol(sigma(b))) in k[X]
  $
  and $[b]$ solves this polynomial. Therefore, $k(z)\/k$ is generated by elements whose minimal polynomials split completely over $k$, and is a normal extension. 
  
  Let $k_s$ be the separable closure of $k$ in $k(z)$, with $k_s = k(ol(b))$, $ol(b) in B\/frak(q)$. The elements ${sigma(frak(q))}_(sigma in G)$ are maximal ideals, hence pairwise coprime. Thus, 
  $
    B -> product_(frak(r) in Spec(B) \ exists sigma in G, frak(r) = sigma(frak(q))) B\/frak(r)
  $
  is surjective by Chinese remainder theorem. Thus, we may take $b in B$ satisfying:

  - $b mod frak(q) = ol(b)$; 

  - For any $sigma in G - G_z$, i.e. $sigma(frak(q)) != frak(q)$, $b equiv 0 mod sigma^(-1)(frak(q))$, i.e. $sigma(b) equiv 0 mod frak(q)$. 

  Consider the polynomial $product_(sigma in G) (X - sigma(b)) in A[X]$. 
  Any $s in Aut(k(z)\/k)$ is determined by $s(ol(b)) in k(z)$. $s(ol(b))$ solves the polynomial $product_(sigma in G) (X - ol(sigma(b)))$, and so there exists $sigma in G$ s.t. $sigma(b) mod frak(q) = s(ol(b)) != 0$. By our choice of $b$, such $sigma$ must have $sigma in G_z$. Thus, $sigma |-> s$ under $G_z -> Aut(k(z)\/k)$, and we have the desired surjection. 

  (4) Firstly, $Z -> Y$ is obviously $G$-invariant. Next, $(-) compose pi: Hom(Y, X) -> Hom(Z, X)$ has image in $Hom(Z, X)^G$, since $pi$ is $G$-invariant. This map is functorial, so it suffices to prove that for each individual $X$, 
  $
    (-) compose pi: Hom(Y, X) -> Hom(Z, X)^G
  $
  is bijective. $pi$ is surjective on topological spaces and injective on structure sheaf, hence an epimorphism in the category of schemes. Thus $(-) compose pi$ is injective, and we only need to prove its surjectivity. Let $f: Z -> X$ be a $G$-invariant morphism, and we need to descend it to some $g: Y -> X$. 

  - Since $Y = Z\/G$ as topological spaces, the $G$-invariant map $f: Z -> X$ on topological spaces descends to some $g: Y -> X$. 

  - The map $f^\#: cal(O)_X -> f_* cal(O)_Z$ is $G$-invariant under the action of $G$ on $cal(O)_Z$. Thus, it factors through the subsheaf $(f_* cal(O)_Z)^G = f_* cal(O)_Z^G = g_* pi_* cal(O)_Z^G = g_* cal(O)_Y$. This defines the morphism $g^\#: cal(O)_X -> g_* cal(O)_Y$ on structure sheaves. 

  This constructs the morphisms $g$.
]

#definition(name: <defn-admissible-group-action>)[
  An action of $G$ on $Z$ is called *admissible* if there exists an affine $G$-invariant map $pi: Z -> Y$, satisfying (1)-(4) in @affine-sch-quotient. Equivalently: 

  - There exists a $G$-invariant affine map $pi: Z -> Y$ s.t. $cal(O)_Y cong (pi_* cal(O)_Z)^G$. 

  - $Z$ is a union of $G$-invariant affine opens. 

  #example[
    An admissible $pi$ doesn't need to be etale. Consider the example from complex geometry: $CC -> CC, z |-> z^n$, i.e.
    $
      CC[y] -> CC[z], y |-> z^n
    $
    under the action of $mu_n$, the group of $n$-th roots of unity, on $CC[z]$ defined by $sigma, z |-> sigma z$. Then this map ramifies above $y = 0 in Y$ but is still admissible (as $CC[z]^(mu_n) = CC[z^n]$). 
  ]

  #construction[
    Suppose that $Z = Spec(B)$ and $pi: Z = Spec(B) -> Y = Spec(A)$ is admissible. Then property (4) implies that: 
    $
      Hom(Spec(B), X)^G cong Hom(Spec(A), X)
    $
    naturally. Taking $X = Spec(C)$ gives a natural isomorphism $Hom(C, B)^G cong Hom(C, A)$, and taking $C = ZZ[T]$ gives a natural isomorphism $B^G cong A$. 

    That is, for a scheme $Z$ with a $G$-action, if an admissible $pi: Z -> Y$ exists, it has to locally look like $Spec(B) -> Spec(B^G)$, and is hence uniquely determined. The equivalence of the three definitions of $Z$ being admissible is thus equivalent, and admissibility is hence a property, not a structure. We will use the phrases '$Z$ is admissible' and '$pi: Z -> Y$ is admissible' interchangeably. 
  ]
]

#definition(name: <defn-inertia-group>)[
  Given an admissible map $pi: Z -> Y$, the *inertia group* $I_G (z)$ at $z in Z$ is defined to be the kernel: 
  $
    I_G (z) = ker(G_z ->> Aut(k(z)\/k(pi(z))))
  $
]

We now establish Galois theory for etale covering spaces: 
#theorem(name: <galois-theory-of-coverings>)[
  0. If $Z -> Y$ is a morphism in $FEt_X$ so that $Z\/X$ is Galois, then $Z\/Y$ is also Galois.  

  + Let $pi: Z -> Y := Z\/G$ be admissible and finite. Then $pi$ is a finite etale covering whenever the group of inertia $I_G (z) = {1}$ for all $z in Z$. 

  + Assume that $Z in FEt_X$ is connected and $G$ is a subgroup of $Aut(Z\/X)^opp$ that acts on $Z$. In this setup, $Z$ is $G$-admissible, $Z -> Z\/G$ is an etale covering space and a morphism in $FEt_X$ with $G = Aut(Z\/(Z\/G))$, and $Z\/G -> X$ is also an etale covering space (i.e. an object in $FEt_X$). 

  + Take an etale covering space $Z -> X$ with $Z,X$ connected. Then $Z\/X$ is Galois $<==>$ $Z\/Aut(Z\/X)^opp overset(->, tilde) X$. 

  #example[
    Consider the cases where the schemes in question are spectra of fields. Then these three statements specialize to familiar statements from field theory: 

    + A finite field extension $L\/L^G$ where $L$ has a $G$-action is separable if $G -> Aut(L\/L^G)$ is an isomorphism. 

    + Suppose that $L\/K$ is a finite separable extension and $G <= Gal(L\/K)$ is a subgroup. Then $L\/L^G$ is a finite separable extension of Galois group $G$. 

    + A finite separable extension $L\/K$ is Galois if and only if $L^(Aut(L\/K)) = K$. 
  ]
]
#proof[
  (0) Pick a geometric point $ol(y)$ of $Y$ lying above $ol(x)$ of $X$. Then for $ol(z_1), ol(z_2) in F_(ol(y)) (Z) subset F_(ol(x)) (Z)$, there exists $g in Aut(Z\/X)$ s.t. $ol(z_2) = g(ol(z_1))$, since $Z -> X$ is Galois. Now compose with the structure map $pi: Z -> Y$, and: 
  $
    pi(ol(z_1)) = ol(y) = pi(ol(z_2)) = pi(g(ol(z_1))) 
  $
  Since $pi$ and $pi compose g$ agrees on a geometric point, by @fet-first-props (1), $pi = pi compose g$. Thus $g$ is an automorphism in $Aut(Z\/Y)$. Hence $Aut(Z\/Y)$ acts transitively on $F_(ol(y)) (Z)$. 

  (1) //This question is local in nature, so we may assume that $Z = Spec(B)$ is affine and $Y = Spec(A), A = B^G$. //Fix a point $frak(q) in Spec(B)$ lying above $frak(p) in Spec(A)$. We intend to perform a base change along $A -> A_(frak(p))^"sh"$, the strict henselization of $A$ at $frak(p)$. 
  //Denote $R = A_(frak(p))^"sh"$ and $S = B otimes_A A_(frak(p))^"sh"$. 
  We intend to perform a base change to a strict henselization of a local ring of $A$ to reduce to the case that $Y = Spec(A)$ with $A$ a strict henselian local ring. 

  #lemma[
    Let $pi: Z -> Y = Z\/G$ be admissible, and $g: Y' -> Y$ be flat. We perform a base change: 
    // https://q.uiver.app/#r=typst&q=WzAsNCxbMCwwLCJaJyJdLFsxLDAsIlknIl0sWzAsMSwiWiJdLFsxLDEsIlkiXSxbMiwzLCJwaSIsMl0sWzEsMywiZyJdLFswLDEsInBpJyJdLFswLDIsImcnIiwyXV0=
    #align(center, diagram({
      node((-1, -1), [$Z'$])
      node((0, -1), [$Y'$])
      node((-1, 0), [$Z$])
      node((0, 0), [$Y$])
      edge((-1, 0), (0, 0), [$pi$], label-side: right, "->")
      edge((0, -1), (0, 0), [$g$], label-side: left, "->")
      edge((-1, -1), (0, -1), [$pi'$], label-side: left, "->")
      edge((-1, -1), (-1, 0), [$g'$], label-side: right, "->")
    }, spacing: 2em))
    Then $pi': Z' -> Y'$ remains admissible w.r.t. $G$, and for any $z' in Z'$ with $z = g'(z')$, 
    $
      I_G (z') = I_G (z)
    $
  ]
  #proof[
    We first prove that $pi': Z' -> Y'$ remains $G$-admissible. This problem is local on both $Y'$ and $Y$, so we may assume that $Y, Y'$ are both affine. Then it suffices to show that $(B otimes_(B^G) C)^G = C$ for any flat $B^G -> C$. Indeed, 
    $
      B^G = ker(B -> oplus.big_(g in G) B, b |-> (g(b) - b)_(g in G))
    $
    as $B^G$-modules, and flat base change preserves such a kernel. 

    We then prove the preservation of the inertia subgroup. Let $Z = Spec(B)$, $Y = Spec(A)$ with $A = B^G$, $A'$ be a flat $A$-algebra and $B' = B otimes_A A'$. Let $y = pi(z), y' = pi'(z')$. 

    For any $sigma in I_G (z')$, by definition $sigma in G_(z')$ and $sigma: B'_(z') -> B'_(z')$ is the identity mod the maximal ideal $z' B'_(z')$. Since $sigma$ commutes with the map $B -> B'$ by definition and $sigma(z') = z'$, we have $sigma(z) = z$ and so $sigma in G_z$. From the inclusion of residue fields $k(z) subset k(z')$ and that $sigma$ is the identity on $k(z')$, we see that $sigma$ is the identity on $k(z)$. Thus, we have the easy inclusion $I_G (z') subset I_G (z)$. 

    Conversely, we want to prove the opposite inclusion. Let $sigma in I_G (z)$. That $sigma(z) = z$ and $sigma$ is the identity on $k(z)$ translates to the algebraic condition: 
    $
      sigma(b) - b in z, forall b in B
    $
    For any $b' in B'$, write $b' = sum_i b_i otimes a'_i$. Then: 
    $
      sigma(b') - b' = sum_i underbrace((sigma(b_i) - b_i), in z) otimes a'_i in z B' subset z'
    $
    since $z'$ lies above $z$. Thus $sigma in G_(z')$ and is identity on the residue field $k(z')$ and so $sigma in I_G (z')$. Hence $I_G (z) subset I_G (z')$. We now have $I_G (z) = I_G (z')$. 
  ]

  Suppose that we have (1) proved for the case where $Y = Spec(A)$ where $A$ is a strict henselian local ring. We then prove the general case:
  #proof[
    This question is local in nature, so we may assume that $Z = Spec(B)$ is affine and $Y = Spec(A), A = B^G$. However, etaleness can be checked on the local rings only, so it suffices to show that every base change of $pi: Z -> Y$ along $Spec(cal(O)_(Y,y)) -> Y$ is etale. Since $Spec(cal(O)_(Y,y)) -> Y$ is flat, the base change of $pi$ still has trivial inertia groups. 
    
    As such, it suffices to consider the case where $Y = Spec(A)$ where $A$ is local. Take the strict henselization $Y' = Spec(A^"sh")$ and then $Y' -> Y$ is faithfully flat. Etaleness descends along faithfully flat base change by @fpqc-descent-of-properties (5), so by base changing along $Y' -> Y$ we are reduced to the strict henselian case. 
  ]

  Now assume that $Y = Spec(A)$ with $(A, frak(m))$ strict henselian, and $Z = Spec(B)$. 
  
  Since $B$ is a finite $A$-algebra with $A$ henselian, $B$ has finitely many maximal ideals ${frak(n)_1, dots.c, frak(n)_r}$ all lying above $frak(m)$, s.t. 
  $
    B = B_(frak(n)_1) times dots.c B_(frak(n)_r)
  $
  Since $G$ acts on the primes ${frak(n)_1, dots.c, frak(n)_r}$ lying above $frak(m)$ transitively, for a fixed maximal $frak(n) in Spec(B)$, the value of an element $b in B^G$ on the component $B_(frak(n))$ determines all other components. As such, $B^G = B_(frak(n))^(G_(frak(n)))$. However, $k(frak(m)) = A\/frak(m)$ is separably closed, and so $k(frak(n))\/k(frak(m))$ is a purely inseparable finite normal extension. It thus has trivial automorphism group. Thus, $I_G (frak(n)) = ker(G_(frak(n)) -> Aut(k(frak(n))\/k(frak(m)))) = G_(frak(n))$. 

  /*($<==$) */If all inertia groups $I_G (frak(n))$ are trivial, then all groups $G_(frak(n))$ are trivial. Hence $A = B^G = B_(frak(n))^(G_(frak(n))) = B_(frak(n))$ for any maximal $frak(n) in Spec(B)$. Thus, $B = A times dots.c times A$ is the direct product of some copies of $A$, and $pi: union.sq.big_(i=1)^r Spec(A) -> Spec(A)$ is etale. 

  /*($==>$) Suppose that $B$ is etale over $A$. Then each local homomorphism $A -> B_(frak(n))$ is etale. Thus $B_(frak(n))\/frak(n)B_(frak(n))$ is a finite separable extension over $k = A\/frak(m)$. However $k$ is separably closed, so this extension must be trivial. 
  
  Now that we have a local homomorphism $A -> B_(frak(n))$ that is an isomorphism on residue fields. By etaleness $frak(m)_A B_(frak(n)) = frak(n) B_(frak(n))$, so the induced morphism on maximal ideals is surjective. Finally $B$ is a finite $A$-module. By a Nakayama argument, $B_(frak(n)) cong A$. 

  In other words, $B = product_(frak(n)) A$ is just a direct product of $A$'s on which $G$ acts, and $A -> B$ is the diagonal embedding. The action of $G$ on each $A$ is trivial since $A -> B$ is $G$-invariant, and $G$ merely permute the copies of $A$. */

  /* It is easy to check that: 
  - The formaltion of $Z -> Z\/G$ commutes with flat base change $Y' -> Z\/G$; 

  - The formation of $G_i (z)$ is compatible with such base change. 

  Thus by passing to the strict henselization $Spec(cal(O)_(Y, ol(y))^h) -> Y$, we may assume that: 

  - $Y = Spec(A)$, where $(A,frak(m))$ is local and $A\/frak(m)$ is separably closed; 

  - $X = Spec(B), B = product_("finite") B_(frak(n)_i)$ finite over $A$. 

  By assumption, $A cong B^G$. Property (2) states that $G$ acts transitively on $π^(-1)(frak(m))$, and fixing one such $frak(n)$, $B^G = (B_(frak(n)))^(G_(frak(n)))$ where $G_(frak(n))$ is a decomposition group. 

  By assumption, $G_i (frak(n)) = {1}$. Now consider the exact sequence of inertia and decomposition groups: 
  $
    1 -> G_i (frak(n)) -> G_(frak(n)) -> Aut(κ(frak(n))\/(A\/frak(m))) -> 1
  $
  Since $A\/frak(m)$ is separably closed, $κ(frak(n))\/(A\/frak(m))$ is purely inseparable, and so the automorphism group $Aut(κ(frak(n))\/(A\/frak(m)))$ is trivial. Thus $G_(frak(n)) = {1}$, and so $B^G = B_(frak(n)) = A$. 

  Now that $Z = union.sq.big Spec(B_(frak(n_i)))$, where each component is just $Y = Spec(B_(frak(n))) = Spec(A)$. This is just the trivial covering, so it is etale. */

  (2) Since $Z -> X$ is finite etale and $Z$ is connected, @fet-first-props (1) identifies $Aut(Z\/X)$ with a subgroup of the automorphism group of any geometric fiber. Thus $G$ is finite. 

  We first show that $Z$ is $G$-admissible: 
  
  - If $U = Spec(A) subset X$ is affine, then $V = Z times_X U$ is affine since $Z -> X$ is finite, and it is $Aut(Z\/X)^opp$-invariant since the action is compatible with the structure map $Z -> X$, hence preserves the property of a point lying over a particular point or open of $X$. 
  
    These opens cover $Z$, so by the invariant affine open criterion in the definition of admissibility, $Z$ is $G$-admissible. Hence the quotient $pi: Z -> Z\/G$ exists.

  Next, every inertia group for $pi$ is trivial. Indeed:
  
  - Let $z in Z$ and $sigma in I_G (z)$. Choose a geometric point $ol(z)$ over $z$. Since $sigma$ fixes $z$ and acts trivially on $k(z)$, it fixes $ol(z)$ (which is really an embedding of $k(z)$ into a separably closed field). As $sigma$ and $id_Z$ are both $X$-automorphisms of the connected finite etale cover $Z -> X$, @fet-first-props (1) gives $sigma = id_Z$. Thus $I_G (z) = {1}$ for all $z$, and (1) implies that $pi: Z -> Z\/G$ is finite etale. 

  The structure morphism $Z -> X$ is $G$-invariant, so by the quotient property of @affine-sch-quotient (4), it descends uniquely to a morphism $q: Z\/G -> X$ with $Z -> Z\/G ->^q X$ equal to the original map $Z -> X$. We aim to show that $q$ is finite etale. 
  
  - Since the claim is local on $X$, fix $x in X$ and base change to $X' = Spec(cal(O)_(X,x)^#[sh])$. The morphism $X' -> Spec(cal(O)_(X,x))$ is faithfully flat. By the flat base-change lemma above, the base change of $Z\/G$ is the quotient of $Z times_X X'$ by $G$. Since $X'$ is strict henselian, the finite etale covering $Z times_X X' -> X'$ is a finite disjoint union of copies of $X'$, on which $G$ acts by permuting the components. Its quotient is therefore again a finite disjoint union of copies of $X'$, so the base change of $q$ is finite etale. By @fpqc-descent-of-properties (2) and (5), $q: Z\/G -> X$ is finite etale.

  Thus, $Z\/G in FEt_X$ and $pi: Z -> Z\/G$ is a morphism in $FEt_X$. 

  Finally, the given action defines an inclusion $G -> Aut(Z\/(Z\/G))$. Conversely, any automorphism of $Z$ over $Z\/G$ preserves every fiber of $pi$, and by @affine-sch-quotient (2) these fibers are exactly the $G$-orbits. Pick a geometric point $ol(y)$ of $Z\/G$ and a geometric point $ol(z)$ of $Z$ above it. Then for any $gamma in Aut(Z\/(Z\/G))$, $gamma(ol(z)) = g(ol(z))$ for some $g in G$. By @fet-first-props (1), $gamma = g$. Thus $G -> Aut(Z\/(Z\/G))$ is an isomorphism. 

  (3) Let $G = Aut(Z\/X)^opp$. Since $Z -> X$ is connected finite etale, $G$ acts faithfully on every geometric fiber by @fet-first-props (1).

  ($<==$) If $Z\/G overset(->, tilde) X$, then for any geometric point $ol(x) -> X$, the fiber $F_(ol(x)) (Z)$ is a single $G$-orbit by @affine-sch-quotient (2). Thus $G$ acts transitively on $F_(ol(x)) (Z)$, so $Z\/X$ is Galois.

  ($==>$) Suppose that $Z\/X$ is Galois. By (2) applied to $G <= Aut(Z\/X)^opp$, the quotient $Z -> Z\/G$ exists as an etale covering and $Z\/G -> X$ lies in $FEt_X$. For any geometric point $ol(x) -> X$, @affine-sch-quotient (2) identifies the fibers of $Z -> Z\/G$ with the $G$-orbits in $F_(ol(x)) (Z)$. Since $Z\/X$ is Galois, this action is transitive, so:
  $
    \#F_(ol(x)) (Z\/G) = 1
  $
  Hence the finite etale cover $Z\/G -> X$ has degree $1$. As $X$ is connected, a degree $1$ finite etale covering is an isomorphism. Thus $Z\/Aut(Z\/X)^opp overset(->, tilde) X$.
]
