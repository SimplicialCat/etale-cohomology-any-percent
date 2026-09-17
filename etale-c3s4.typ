#import "void-import.typ": *
== First properties of $pi_1^et$ and examples

We now introduce first properties of etale fundamental groups.

#properties[
  + (Dependency on $ol(x)$) For another geometric point $ol(x'): Spec(Omega') -> X$, there exists a natural isomorphism (i.e. a path) $eta: F_(ol(x)) -> F_(ol(x'))$ inducing a continuous isomorphism:
    $
      pi_1^et (X, ol(x)) cong pi_1^et (X, ol(x'))
    $
    The choice of the path $eta$ is not unique, but the isomorphisms $pi_1^et (X, ol(x)) cong pi_1^et (X, ol(x'))$ obtained this way differ only by conjugation (i.e. inner automorphisms of $pi_1^et (X, ol(x))$). 
    #proof[
      That for different choices of $eta$, the isomorphisms constructed differ by an inner automorphism is entirely a formal consequence: Suppose that we are given different paths $eta, eta': F_(ol(x)) -> F_(ol(x'))$. Then $gamma := eta^(-1) compose eta' in Aut(F_(ol(x))) = pi_1^et (X, ol(x))$. Now for any element $delta$ of $pi_1^et (X, ol(x))$, the isomorphism defined by $eta'$ sends it to: 
      $
        eta' compose delta compose (eta')^(-1) = eta compose (gamma delta gamma^(-1)) compose eta^(-1)
      $
      differs from the one defined by $eta$ by an inner automorphism of $pi_1^et (X, ol(x))$. 

      It remains to show that there indeed exists a path, i.e. a natural isomorphism $eta: F_(ol(x)) -> F_(ol(x'))$. We first construct $eta$ on the full subcategory of $FEt_X$ consisting of the Galois covering spaces. 
      
      Let ${(X_i, ol(x_i))}_(i in I)$ be the directed system of pointed Galois coverings of $(X, ol(x))$. Suppose that we are given a system of geometric points ${ol(x'_i) in F_(ol(x'))(X_i)}_(i in I)$. We are then able to define maps: 
      $
        eta_i: F_(ol(x)) (X_i) -> F_(ol(x')) (X_i), sigma(ol(x_i)) |-> sigma(ol(x'_i)), forall sigma in Aut(X_i\/X)
      $
      Since $Aut(X_i\/X)$ maps bijectively to $F_(ol(x)) (X_i)$ and $F_(ol(x')) (X_i)$ by acting on $ol(x_i)$ and $ol(x'_i)$ respectively, this map constructed for each individual $i$ is a bijection. 

      We then study what requirements should be imposed on ${ol(x'_i)}_(i in I)$ to make the maps ${eta_i}_(i in I)$ natural (w.r.t. morphisms between pointed Galois coverings of $(X, ol(x))$). For every morphism $f_(i,j): (X_j, ol(x_j)) -> (X_i, ol(x_i))$, we require that: 
      $
        eta_i (f_(i,j) (ol(y))) = f_(i,j) (eta_j (ol(y))), forall ol(y) in F_(ol(x)) (X_j)
      $
      or equivalently, 
      $
        eta_i (f_(i,j) (sigma_j (ol(x_j)))) = f_(i,j) (eta_j (sigma_j (ol(x_j)))), forall sigma_j in Aut(X_j\/X)
      $
      Let $sigma_j |-> sigma_i$ under $Aut(X_j\/X) -> Aut(X_i\/X)$ induced by $f_(i,j)$.  Now for RHS $f_(i,j) (eta_j (sigma_j (ol(x_j)))) = f_(i,j) (sigma_j (ol(x'_j))) = sigma_i (f_(i,j) (ol(x'_j)))$, and for LHS, $eta_i (f_(i,j) (sigma_j (ol(x_j)))) = eta_i (sigma_i (ol(x_i))) = sigma_i (ol(x'_i))$. In other words, the naturality condition above for all $i<=j$ is equivalent to: 
      $
        f_(i,j) (ol(x'_j)) = ol(x'_i), forall i <= j
      $
      i.e. 
      $
        (ol(x'_i))_(i in I) in invlim_(i in I) F_(ol(x')) (X_i)
      $
      where the maps in this inverse system are induced by $f_(i,j): X_j -> X_i$. We claim that such a compatible system of points $(ol(x'_i))_(i in I)$ exists, i.e. the projective limit $invlim_(i in I) F_(ol(x')) (X_i)$ is not empty. This is due to the following set-theoretic fact: 
      #lemma[
        A projective limit of nonempty finite sets with surjective transition maps must be nonempty. 
      ]
      #proof[
        Let ${X_i}_(i in I)$ be a projective limit of nonempty finite sets with transition maps $f_(i,j): X_j -> X_i$. The projective limit is the subset: 
        $
          invlim_(i in I) X_i = {(x_i)_(i in I) in product_(i in I) X_i : f_(i,j)(x_j) = x_i, forall i<=j} = inter.big_(i<=j) C_(i,j)
        $
        where: 
        $
          C_(i,j) = {(x_i)_(i in I) in product_(i in I) X_i : f_(i,j)(x_j) = x_i}
        $
        Equip each $X_i$ with the discrete topology and $product_(i in I) X_i$ with the product topology. Then by Tychonoff's theorem, since each $X_i$ is compact (by finiteness), $product_(i in I) X_i$ must be compact. $C_(i,j)$ is the preimage of the diagonal of $X_i times X_i$ under the map $product_(i in I) X_i -> X_i times X_i, (x_i)_(i in I) |-> (x_i, f_(i,j) (x_j))$. Since $X_i times X_i$ is discrete, the diagonal is closed, so $C_(i,j)$ is closed in $product_(i in I) X_i$. 

        Now that $product_(i in I) X_i$ is compact, to show that the intersection of the closed sets $C_(i,j)$ is nonempty, it suffices to show that the intersection of every finite collection of them is nonempty. Let $i_1 <= j_1, dots.c, i_t <= j_t$ be finitely such pairs, and pick an upper bound $k$ of $j_1, dots.c, j_t$. Since $X_k$ is nonempty, pick any $x_k in X_k$, and pick $(x_i)_(i in I)$ so that $x_i = f_(i,k)(x_k)$ whenever $i<=k$ (and pick $x_i$ arbitrarily otherwise). Then one may easily see that $(x_i)_(i in I) in inter.big_(s=1)^t C_(i_s,j_s)$. We are thereby done. 
        #suppress-qed
      ]
      Since each $F_(ol(x')) (X_i)$ is nonempty, such a compatible choice $(ol(x'_i))_(i in I)$ exists. In other words, we have constructed natural bijections: 
      $
        eta_i : F_(ol(x)) (X_i) -> F_(ol(x')) (X_i)
      $
      Let $Z in FEt_X$ be a Galois cover. Suppose that $Z cong X_i$ over $X$, forgetting about the pointed structure of $X_i$. Then we define $eta_Z : F_(ol(x)) (X_i) -> F_(ol(x')) (X_i)$ to be $eta_i$. This definition is independent of the choice of $i$: another choice $j$ corresponds to an isomorphism $(X_i, ol(x_i)) -> (X_j, ol(x_j))$, and naturality of ${eta_i}$ gives the same definition of $eta_Z$. The naturality of ${eta_Z}$ follows from that of ${eta_i}$. We have thus defined $eta$ on the full subcategory of $FEt_X$ consisting of Galois coverings. 

      The rest of the proof that passes from Galois coverings to general coverings is identical to the last part of the proof for @pi1et-as-invlim. As such, you can skip the rest of the proof if you want. 

      Finally, for an arbitrary covering $Y in FEt_X$, pick a Galois covering $f: Z -> Y$. Then we define: 
      $
        eta_Y: F_(ol(x)) (Y) -> F_(ol(x')) (Y), f(ol(z)) |-> f(eta_Z (ol(z)))
      $

      - $eta_Y$ is well-defined: Suppose that $ol(y) in F_(ol(x))(Y)$ is written as $ol(y) = f(ol(z_1)) = f(ol(z_2))$ where $ol(z_1), ol(z_2) in F_(ol(y))(Z) subset F_(ol(x))(Z)$. Then since $Z\/X$ is Galois, by @galois-theory-of-coverings (0) so is $Z\/Y$, and there exists $sigma in Aut(Z\/Y)$ s.t. $ol(z_2) = sigma(ol(z_1))$. Now: 
        $
          f(eta_Z (ol(z_2))) &= f(eta_Z (sigma(ol(z_1)))) \
          &= f(sigma(eta_Z (ol(z_1)))) #[by definition or naturality of $eta$] \
          &= f(eta_Z (ol(z_1))) #[since $sigma in Aut(Z\/Y)$]
        $
        We must also show that $eta_Y$ is independent from the choice of Galois covering $Z$. By passing to the Galois closure of the composite covering, we are reduced to showing that $eta_Y$ defined using Galois coverings $W$ and $Z$ are the same when given $W ->^g Z ->^f Y -> X$. Under the definition with $W$, 
        $
          f(g(ol(w))) |-> f(g(eta_W (ol(w))))
        $
        while under the definition with $Z$, 
        $
          f(g(ol(w))) |-> f(eta_Z (g(ol(w))))
        $
        By naturality of ${eta_Z}$ among the Galois coverings, $g(eta_W (ol(w))) = eta_Z (g(ol(w)))$ and we are done.         

      - $eta_Y$ is bijective: Since $eta_Z$ is bijective, the image of $eta_Y$ contains all points of the form $f(ol(z'))$ where $ol(z') in F_(ol(x'))(Z)$. However $F_(ol(x')) (Z) -> F_(ol(x')) (Y)$ is surjective, so $eta_Y$ is surjective. 

        Now we could prove $eta_Y$ is injective by hand. But instead let's just invoke the very deep theorem that a surjective map between finite sets of the same size is bijective and call it a day. 

      - ${eta_Y}$ is natural: Given a morphism $g: Y_1 -> Y$ in $FEt_X$, there exists a common Galois covering $Z$: 
        // https://q.uiver.app/#r=typst&q=WzAsNCxbMSwwLCJZIl0sWzIsMSwiWCJdLFsxLDIsIllfMSJdLFswLDEsIloiXSxbMywwLCJmIl0sWzMsMiwiZl8xIiwyXSxbMCwxXSxbMiwxXV0=
        #context align(center, diagram({
          node((0, -1), [$Y$])
          node((1, 0), [$X$])
          node((0, 1), [$Y_1$])
          node((-1, 0), [$Z$])
          edge((-1, 0), (0, -1), [$f$], label-side: left, "->")
          edge((-1, 0), (0, 1), [$f_1$], label-side: right, "->")
          edge((0, 1), (0, -1), [$g$], "->", label-side: center)
          edge((0, -1), (1, 0), "->")
          edge((0, 1), (1, 0), "->")
        }, spacing: 2em, crossing-fill: thm-box-curr-color()))
        Then for any $ol(y_1) = f_1 (ol(z)) in F_(ol(x)) (Y_1)$, 
        $
          g(eta_(Y_1) (ol(y_1))) &= g(eta_(Y_1) (f_1 (ol(z)))) \
          &= g(f_1 (eta_Z (ol(z)))) #[by definition of $eta_(Y_1)$] \
          &= f(eta_Z (ol(z))) \
          &= eta_Y (f(ol(z))) #[by definition of $eta_(Y)$] \
          &= eta_Y (g(ol(y_1)))
        $
        and naturality is verified. 

      Finally, we need to verify continuity of the isomorphism $pi_1^et (X, ol(x)) -> pi_1^et (X, ol(x'))$ arising from such $eta$. However, our construction of $eta$ realized ${(X_i, ol(x'_i))}_(i in I)$ as the directed system of pointed Galois coverings of $(X, ol(x'))$, so the isomorphism constructed is essentially: 
      $
        pi_1^et (X, ol(x)) cong invlim_(i in I) Aut(X_i\/X)^opp cong pi_1^et (X, ol(x')) 
      $
      In other words, by Theorem @pi1et-as-invlim, the topologies on $pi_1^et (X, ol(x))$ and $pi_1^et (X, ol(x'))$ are both defined by $invlim_(i in I) Aut(X_i\/X)^opp$. This gives the continuity of the isomorphism. 
    ]
  
  + (Functoriality) Given $alpha: (X, ol(x)) -> (Y, ol(y))$ a morphism between pointed connected noetherian schemes, there is a canonical continuous group homomorphism:
    $
      alpha_*: pi_1^et (X, ol(x)) -> pi_1^et (Y, ol(y))
    $
    making:
    // https://q.uiver.app/#r=typst&q=WzAsNCxbMCwwLCJGRXRfWSJdLFsyLDAsIkZFdF9YIl0sWzAsMiwicGlfMSAoWSwgb3ZlcmxpbmUoeSkpXCItXCJjU2V0XlwiZi5jXCIiXSxbMiwyLCJwaV8xIChYLCBvdmVybGluZSh4KSlcIi1cImNTZXReXCJmLmNcIiJdLFswLDEsImFscGhhXigtMSkiXSxbMCwyLCJ0aWxkZSIsMl0sWzEsMywidGlsZGUiXSxbMiwzLCIoLSkgY29tcG9zZSBhbHBoYV8qIiwyXV0=
    #align(center, diagram({
      node((-1, -1), [$FEt_Y$])
      node((1, -1), [$FEt_X$])
      node((-1, 1), [$GSet(pi_1 (Y, ol(y)))^#[fin,cont]$])
      node((1, 1), [$GSet(pi_1 (X, ol(x)))^#[fin,cont]$])
      edge((-1, -1), (1, -1), [$alpha^(-1)$], label-side: left, "->")
      edge((-1, -1), (-1, 1), [$tilde$], label-side: right, "->")
      edge((1, -1), (1, 1), [$tilde$], label-side: left, "->")
      edge((-1, 1), (1, 1), [$(-) compose alpha_*$], label-side: right, "->")
    }, spacing: 2em))
    commutative, where $alpha^(-1)$ sends $Y' -> Y$ to $X times_Y Y' -> X$.
    #proof[
      By universal property of the fiber product, for any $Y' in FEt_Y$,
      $
        F_(ol(x)) (X times_Y Y') = F_(ol(y)) (Y')
      $
      /*
      from the commutative diagram:
      // https://q.uiver.app/#r=typst&q=WzAsNixbMiwwLCJYIHRpbWVzX1kgWSciXSxbNCwwLCJZJyJdLFsyLDIsIlgiXSxbNCwyLCJZIl0sWzAsMiwiU3BlYyhPbWVnYSkiXSxbMCwwLCJGXyhvdmVybGluZSh4KSkgKFggdGltZXNfWSBZJykiXSxbNSwwXSxbNSw0XSxbNCwyLCJvdmVybGluZSh4KSIsMl0sWzIsMywiYWxwaGEiLDJdLFs0LDMsIm92ZXJsaW5lKHkpIiwyLHsiY3VydmUiOjR9XSxbMCwxXSxbMSwzXSxbMCwyXV0=
      #align(center, diagram(
        {
          node((0, -1), [$X times_Y Y'$])
          node((2, -1), [$Y'$])
          node((0, 1), [$X$])
          node((2, 1), [$Y$])
          node((-2, 1), [$Spec(Omega)$])
          node((-2, -1), [$F_(ol(x)) (X times_Y Y')$])
          edge((-2, -1), (0, -1), "->")
          edge((-2, -1), (-2, 1), "->")
          edge((-2, 1), (0, 1), [$ol(x)$], label-side: right, "->")
          edge((0, 1), (2, 1), [$alpha$], label-side: right, "->")
          edge((-2, 1), (2, 1), [$ol(y)$], label-side: right, "->", bend: -36deg)
          edge((0, -1), (2, -1), "->")
          edge((2, -1), (2, 1), "->")
          edge((0, -1), (0, 1), "->")
        },
        spacing: (2em, 2em),
      ))*/
      This induces a natural homomorphism: 
      $
        alpha_*: Aut(F_(ol(x))) &-> Aut(F_(ol(y))) \
        gamma &|-> (gamma_(X times_Y Y'): F_(ol(y)) (Y') -> F_(ol(y)) (Y'))_(Y' in FEt_Y)
      $
      The commutative diagram in the statement is immediate from this construction. 
      
      Continuity is also easy: For every pointed Galois covering $(Z, ol(z)) -> (Y, ol(y))$, we need to prove that: 
      $
        pi_1^et (X, ol(x)) ->^(alpha_*) pi_1^et (Y, ol(y)) ->> Aut(Z\/Y)
      $
      has kernel containing an open subgroup of $pi_1^et (X, ol(x))$. From our construction of $alpha_*$, the kernel consists of elements $sigma in pi_1^et (X, ol(x))$ acting trivially on $F_(ol(x)) (Z times_Y X) in GSet(pi_1^et (X, ol(x)))^#[fin,cont]$. It must contain an open normal subgroup of $pi_1^et (X, ol(x))$ immediately from the equivalence $FEt_X cong GSet(pi_1^et (X, ol(x)))^#[fin,cont]$. 
    ]
]

Next, we answer the question: 

- How much information about $alpha_*: pi_1^et (X, ol(x)) -> pi_1^et (Y, ol(y))$ can be read off from $alpha^(-1): FEt_Y -> FEt_X$? 

Note that $FEt_X cong GSet(pi_1^et (X, ol(X)))^#[fin,cont]$. As such, this is really asking what information about a group homomorphism can be read off from its induced morphism on the category of finite sets under group actions. 

#construction[
  Let $alpha: G -> H$ be a homomorphism between finite groups. Then we may construct the map $alpha^(-1): GSet(H)^#[fin] -> GSet(G)^#[fin]$. Then from elementary arguments:
  $
    alpha #[surjective]
    & <==> #[$G$ acts on $H$ transitively] \
    & <==> #[$alpha^(-1)$ sends transitive $H$-sets to transitive $G$-sets]
  $
  and: 
  $
    alpha #[trivial]
    & <==> #[$alpha^(-1)$ sends every $H$-set to a $G$-set with trivial $G$-action]
  $
  and: 
  $
    & alpha #[injective] <==> #[there exists a $G$-equivariant map $G\/ker(alpha) -> G$] \
    <==>& #[$forall T in GSet(G)^#[fin]$,  $exists S in GSet(H)^#[fin]$ and a $G$-equivariant map $S_0 -> T$ where $S_0$ is a $G$-orbit of $alpha^(-1)(S)$]
  $
]

With this toy example in mind, we propose the following results on profinite groups: 
#lemma(name: <profin-grp-action-props>)[
  Let $G, H$ be profinite groups and $alpha: G -> H$ be a continuous homomorphism inducing a functor $alpha^(-1): GSet(H)^#[fin,cont] -> GSet(G)^#[fin,cont]$. Then: 

  + $alpha$ is surjective if and only if $alpha^(-1)$ sends transitive $H$-sets to transitive $G$-sets; 

  + $alpha$ is trivial if and only if $alpha^(-1)$ sends every $H$-set to a $G$-set with trivial action; 

  + $alpha$ is injective if and only if $forall T in GSet(G)^#[fin,cont]$,  $exists S in GSet(H)^#[fin,cont]$ and a $G$-equivariant map $S_0 -> T$ where $S_0$ is a $G$-orbit of $alpha^(-1)(S)$. 

  + Consider a third profinite group $K$ and a continuous surjective homomorphism $beta: H -> K$. Then:
  $
    G -> H -> K -> 1
  $
    is exact in the middle, if and only if for every transitive $S in GSet(H)^#[fin,cont]$, $alpha^(-1)(S) in GSet(G)^#[fin,cont]$ has a point fixed by all of $G$ $<==>$ there exists $Q in GSet(K)^#[fin,cont]$ s.t. $S cong beta^(-1)(Q)$. 
]
#proof[
  The proof is completely elementary and analogous to the finite group case. We only prove (3)(4) for demonstration, since the statements for (3)(4) are the longest. 

  (4) Let $I = im(alpha)$ and $H_0 = ker(beta)$. For an object $T in GSet(G)^#[fin,cont]$, we use the notation $rho_T$ to denote the continuous homomorphism $G -> Sym(T)$, where $Sym(T)$ is the permutation group on $T$, a finite group. 

  Then we may translate the proposed equivalent condition into conditions on $rho$. Given a transitive $S in GSet(H)^#[fin,cont]$, we'll assume that $S cong H\/H_1$ where $H_1$ is an open subgroup of $H$: 

  - $alpha^(-1) (S)$ having a fixed point $h H_1$ means that $h^(-1) I h subset H_1$. 

  - We claim that the existence of $Q in GSet(K)^#[fin,cont]$ s.t. $S cong beta^(-1) (Q)$ is equivalent to $H_0 subset ker(rho_S)$. Indeed, for $S cong beta^(-1) (Q)$, $Q$ must be bijective to $S$ as a set. Then the existence of a $K$-action on $S$ compatible with its given $H$-action is equivalent to $rho_S: H -> Sym(S)$ factoring through $beta: H -> K$. 

    If $rho_S$ factors as $H ->^beta K -> Sym(S)$, then $H_0 = ker(beta) subset ker(rho_S)$. Conversely, if $H_0 subset ker(rho_S)$, since $beta: H ->> K$ is surjective, we may identify $K cong H\/H_0$, and then $rho_S$ factors through $beta$ from the first isomorphism theorem. 

  In other words, the equivalent condition can be restated as: For every open subgroup $H_1 <= H$, 
  $
    exists h, I subset h^(-1)H_1 h <==> H_0 subset ker(H -> Sym(H\/H_1)) = inter.big_(h in H) h^(-1)H_1 h
  $
  Since $H_0 = ker(beta)$ is a normal subgroup, $H_0 subset inter.big_(h in H) h^(-1)H_1 h$ is just equivalent to $H_0 subset H_1$. Thus the equivalent condition can be rewritten as: 
  $
    exists h, I subset h^(-1)H_1 h <==> H_0 subset H_1
  $
  When $I = H_0$, $I$ is automatically normal, so $exists h, I subset h^(-1)H_1 h$ is equivalent to $I subset H_1$, and this condition automatically holds. 

  Conversely, suppose that this condition holds. Then in particular $I subset H_1 ==> H_0 subset H_1$. Now $I$ and $H_0$ are closed subgroups of $H$, and any closed subgroup of a profinite group is the intersection of the open subgroups containing it. As such, $I supset H_0$. 
  
  Next, we may restrict the view to open normal subgroups $H_1$. Then we have the condition that for any open normal subgroup $H_1$ of $H$, $H_0 subset H_1 ==> I subset H_1$. In a profinite group, a closed normal subgroup is the intersection of the open normal subgroups containing it. Thus taking an intersection yields $H_0 supset I$. 

  (3)($==>$) Suppose that $alpha$ is injective, identifying $G$ as a closed subgroup of $H$ (equipped with the subspace topology). For every $T in GSet(G)^#[fin,cont]$, we'll replace $T$ with a $G$-orbit to assume that $T$ is transitive under $G$. Then picking the stabilizer of an element of $T$, we may assume that $T cong G\/G_0$ as $G$-sets, where $G_0$ is a subgroup of $G$ of finite index, hence an open and closed subgroup. 

  Since $G_0 <= G$ is open and closed, there exists an open and closed subgroup $H_0 <= H$ s.t. $G_0 = H_0 ∩ G$. $H_0$ is necessarily of finite index, so we may pick the $H$-set $S = H\/H_0 in GSet(H)^#[fin,cont]$. Consider the $G$-orbit of the class $[1] in S = H\/H_0$, and by the second isomorphism theorem, 
  $
    im(G -> H\/H_0) cong G\/(G ∩ H_0) = G\/G_0 cong T
  $
  as $G$-sets. We are thereby done. 

  ($<==$) Suppose that $ker(alpha) != {1}$, say with an element $1 != g in ker(alpha)$. From the profinite topology, there exists a finite index normal subgroup $N$ of $G$ s.t. $g in.not N$. Let $T = G\/N in GSet(G)^#[fin,cont]$. 
  
  By hypothesis, there exists a finite continuous $H$-set $S$ with a $G$-orbit $S_0$ and a $G$-equivariant morphism: 
  $
    phi: S_0 -> T = G\/N
  $
  Since $G\/N$ is a transitive $G$-set, $phi(S_0)$, being a $G$-invariant subset of $G\/N$, must be $G\/N$ itself. That is, $phi$ is surjective. On the other hand, $g in ker(alpha)$, so $g$ acts as $alpha(g) = 1 in H$ on $S_0$, i.e. $g$ acts on $S_0$ trivially. Thus, $g$ acts on $phi(S_0) = G\/N$ trivially by $G$-equivariance of $phi$. In particular, $g N = N$, i.e. $g in N$, a contradiction. 

]

By translating these algebraic results into the language of etale covering spaces, we then obtain the following results; compare @cite-lei-fu[Proposition 3.3.4]:

#properties(name: <pi1et-mor-props>)[
  Let $alpha: (X, ol(x)) -> (Y, ol(y))$ be a morphism between geometrically pointed connected noetherian schemes. 

  + $alpha_*$ is surjective if and only if for any $Y' in FEt_Y$ connected, $X times_Y Y' in FEt_X$ is connected.
  
  + $alpha_*$ is trivial if and only if for all $Y' in FEt_Y$, $X times_Y Y' in FEt_X$ is the disjoint union of some copies of $X$.
  
  + $alpha_*$ is injective if and only if for any $(Z -> X) in FEt_X$, there exists a $(W -> Y) in FEt_Y$ and a morphism in $FEt_X$ from a connected component of $X times_Y W$ to $Z$. 

  + Given a third scheme $(Z, ol(z))$ with $beta: (Y, ol(y)) -> (Z, ol(z))$ s.t. $beta_*$ is surjective, 
    $
      pi_1^et (X, ol(x)) ->^(alpha_*) pi_1^et (Y, ol(y)) ->^(beta_*) pi_1^et (Z, ol(z)) -> 1
    $
    is exact if and only if for every connected $Y' in FEt_Y$, $Y'$ is the base change of some $Z' in FEt_Z$ if and only if $X' = Y' times_Y X in FEt_X$ has a connected component that is just $X$. 
  /*
  + $alpha_*$ is surjective if and only if $alpha^(-1)$ sends transitive $pi_1 (Y)$-sets to transitive $pi_1 (X)$-sets, if and only if $Y' in FEt_Y$ connected $==>$ $X times_Y Y' in FEt_X$ connected.
  
  + $alpha_*$ is trivial if and only if for all $Y' in FEt_Y$, $X times_Y Y' in FEt_X$ is the disjoint union of some copies of $X$.
  
  + $alpha_*$ is injective if and only if for any $T in GSet(pi_1 (X))^"f.c"$, there exists $S in GSet(pi_1 (Y))^"f.c"$ transitive, and a $pi_1 (X)$-equivariant map from a $pi_1 (X)$-orbit in $alpha_*^(-1) (S) -> T$. This is equivalent to for any $(Z -> X) in FEt_X$, there exists a connected $(W -> Y) in FEt_Y$ and a morphism in $FEt_X$ from a connected component of $X times_Y W$ to $Z$.*/
]
#proof[
  This is a simple translation of @profin-grp-action-props (1)(2)(3)(4), where finite continuous $pi_1^et (X, ol(x))$-sets are translated into elements of $FEt_X$ under the equivalence $F_(ol(x)): FEt_X -> GSet(pi_1^et (X, ol(x)))^#[fin,cont]$. The translations are: 

  - $Z in FEt_X$ is connected if and only if $F_(ol(x)) (Z)$ is transitive; 

  - $Z in FEt_X$ is trivial (i.e. a disjoint union of copies of $X$) if and only if $F_(ol(x)) (Z)$ has a trivial $pi_1^et (X, ol(x))$-action; 

  - Taking a connected component of $Z in FEt_X$ is equivalent to taking a $pi_1^et (X, ol(x))$-orbit of $F_(ol(x)) (Z)$. 
]

Using the functoriality for $pi_1^et$, we may obtain various methods to obtain information on $pi_1^et$ for various types of schemes. The first case we'll deal with is base changes that separably closes the base field. 

#corollary[
  Let $k$ be a field, and fix a separable closure $k^sep$. Let $X$ be a geometrically connected#footnote[The equivalence of the two statements for geometric connectivity is an exercise in @cite-hartshorne-ag[Section II.4].] (i.e. $X_(k^sep) = X otimes_k k^sep$ connected, or $X_L = X otimes_k L$ connected for every field extension $L\/k$) scheme of finite type over $k$.
  
  Fix a geometric point $ol(x): Spec(k^sep) -> X_(k^sep) -> X -> Spec(k)$. Then the morphisms $X_(k^sep) -> X -> Spec(k)$ induce an exact sequence: 
  $
    1 -> pi_1^et (X_(k^sep), ol(x)) -> pi_1^et (X, ol(x)) -> underbrace(Gal(k^sep\/k), pi_1^et (Spec(k), Spec(k^sep))) -> 1
  $
]
#proof[
  Exactness on the right:
  #proof[
    To show that $pi_1^et (X, ol(x)) -> Gal(k^sep\/k)$ is surjective, we use @pi1et-mor-props (1). A connected etale covering space of $Spec(k)$ is $Spec(L)$ for a finite separable extension $L\/k$, and $X_L = X otimes_k L$ is connected by geometric connectivity. Thus the conditions for @pi1et-mor-props (1) are verified.
    #suppress-qed
  ]

  Exactness in the middle: 
  #proof[
    Since we have exactness on the right, we may use @pi1et-mor-props (4). 

    Given $Spec(L) in FEt_(Spec(k))$, i.e. $L\/k$ a finite separable extension, the base change $X_L times_X X_(k^sep) cong X times_k Spec(L) times_k Spec(k^sep) = X times_k union.sq.big_([L:k]) Spec(k^sep) = union.sq.big_([L:k]) X_(k^sep)$ is just a disjoint union of copies of $X_(k^sep)$. 

    Conversely, suppose that $X' in FEt_X$ is connected, such that $X'_(k^sep) = X' otimes_k k^sep = X' times_X X_(k^sep) in FEt_(X_(k^sep))$ has a connected component that is just $X_(k^sep)$. 

    Let $C$ be such a connected component of $X'_(k^sep)$, so $C cong X_(k^sep)$ over $X_(k^sep)$. The natural action of $Gal(k^sep\/k)$ on $X'_(k^sep)$ permutes its connected components, and since $X'$ is connected, this action is transitive. Hence every connected component of $X'_(k^sep)$ is again a copy of $X_(k^sep)$ over $X_(k^sep)$.

    Let $H <= Gal(k^sep\/k)$ be the stabilizer of $C$. Since there are only finitely many connected components, $H$ is open, so $L := (k^sep)^H$ is a finite separable extension of $k$. We claim that $X' cong X_L$ over $X$. Indeed, 
    $
      X' otimes_k k^sep = X'_(k^sep) = union.sq.big_(Gal(k^sep\/k)\/H) X_(k^sep) cong X_L otimes_k k^sep
    $
    Furthermore, the descent datum from $X_(k^sep)$ to $X$ for both $X'$ and $X_L$ agrees, as can be checked directly. Thus by @fpqc-descent-of-morphisms, $X' cong X_L$. 

    #suppress-qed
  ]

  To show that $pi_1^et (X_(k^sep), ol(x)) -> pi_1^et (X, ol(x))$ is injective, we use @pi1et-mor-props (3). We may check (3) for only connected covering spaces $Z in FEt_(X_(k^sep))$. We then need to show that there exists some $W in FEt_X$ and a connected component $V$ of $X_(k^sep) times_X W$, with a morphism $V -> Z$. 
   
  Since $Z -> X_(k^sep)$ is finite etale, hence of finite presentation, it descends to some finite separable extension $L\/k$ inside $k^sep$: there exists $Z_L in FEt_(X_L)$ such that
  $
    Z cong Z_L times_(X_L) X_(k^sep)
  $
  over $X_(k^sep)$. Let $W$ be $Z_L$ regarded as a finite etale covering of $X$ via $Z_L -> X_L -> X$. Then
  $
    X_(k^sep) times_X W = Z_L otimes_k k^sep.
  $
  Since $L otimes_k k^sep cong union.sq.big_(Hom_k(L, k^sep)) k^sep$, this is a disjoint union of the conjugates of $Z$, and the component corresponding to the chosen embedding $L subset k^sep$ is exactly $Z$. Taking this component as $V$ gives the required morphism $V cong Z -> Z$.
]

#remark[
  In the exact sequence: 
  $
    1 -> pi_1^et (X_(k^sep), ol(x)) -> pi_1^et (X, ol(x)) ->^q underbrace(Gal(k^sep\/k), pi_1^et (Spec(k), Spec(k^sep))) -> 1
  $
  If $y in X(k)$ is a $k$-point of $X$, then $y_*: Gal(k^sep\/k) -> pi_1^et (X, ol(x))$ is a section of $q$ compatible with $pi_1$-conjugation.
  
  There is a conjecture that if $X$ is so-called "hyperbolic", then this is the only way to get sections of $q$. This is called Grothendieck's section conjecture.
]

The next case we'll deal with is computing $pi_1^et$ for a normal scheme. 

#proposition(name: <p1et-of-normal-scheme>)[
  Let $X$ be a connected noetherian normal scheme. Let $K$ be the function field $K(X)$ of $X$, and:
  $
    ol(eta): Spec(K^sep) -> Spec(K) ->^eta X
  $
  be the generic point. Then the induced morphism:
  $
    eta_*: underbrace(Gal(K^sep\/K), pi_1^et (Spec(K), Spec(K^sep))) -> pi_1^et (X, ol(eta))
  $
  is surjective with kernel $Gal(K^sep\/K^"ur" (X))$. Here $K^sep\/K^"ur" (X)\/K$ is an intermediate field characterized by two equivalent ways: 

  - $K^"ur" (X)$ is the union of all finite separable $L\/K$ s.t. the normalization $X_L$ of $X$ in $L$ (a priori finite over $X$ due to #cite-stacks("032L")[Lemma 10.161.8]) is etale over $X$; 

  - $K^"ur" (X)$ is the largest separable algebraic extension of $K$ s.t. for every finite subextension $L\/K$ of $K^"ur" (X)$, the normalization $X_L$ of $X$ in $L$ is etale over $X$. 
  
  In other words, $eta_*$ identifies: 
  $
    pi_1^et (X, ol(eta)) cong Gal(K^"ur" (X)\/K)
  $
]
This proposition gives a method to compute $pi_1^et (X)$ in principle, but often $K$ is a large complicated field of large transcendence degree over a familiar field (such as a finite field or a number field) and it is hard to compute $K^"ur" (X)$. Nevertheless, this proposition works in the prototypical case where $X$ is the spectrum of the integer ring of a local field or a global field.    
#proof[
  $eta_*$ is surjective by @pi1et-mor-props (1): For any $Z in FEt_X$ connected, since $X$ is normal and $Z\/X$ is etale, $Z$ is normal (by @etale-local-properties (5)). Since $Z$ is normal and connected, $Z$ is integral. Then the generic fiber $Z_K := Z times_X Spec(K)$ of $Z$ over $X$ is also integral, hence connected. In this case since $Z_K$ is also etale over $Spec(K)$, it must be that $Z_K = Spec(L)$ for $L = K(Z)\/K$ a finite separable extension. 

  Next, we prove that the two characterizations of $K^"ur" (X)$ are equivalent. It suffices to show that if $M\/L\/K$ are finite separable extensions s.t. $X_M -> X$ is finite etale, $X_L -> X$ is necessarily finite etale. 

  - Let $N$ be the Galois closure of $M$. If we can show that $X_N -> X$ is finite etale, then $X_L = X_N\/Gal(N\/L)$, and so by @galois-theory-of-coverings (2), $X_L -> X$ is finite etale. 
  
    Let $M_1, dots, M_r$ be the Galois conjugates of $M$ in $K^sep$. Each $X_(M_i)$ is isomorphic over $X$ to $X_M$, hence is finite etale over $X$. Therefore $X_(M_1) times_X dots times_X X_(M_r)$ is finite etale over $X$. Since $N = M_1 dots.c M_r$ as subfields of $K^sep$, $N$ is a quotient of $M_1 otimes_K dots.c otimes_K M_r$, which is artinian. 
    
    Now $M_1 otimes_K dots.c otimes_K M_r$ is reduced. Indeed, tensoring it with $N$ yields: 
    $
      (M_1 otimes_K N) otimes_N dots.c otimes_N (M_r otimes_K N)
    $
    Each $M_i otimes_K N cong N^([M:K])$, so this ring is a direct product of copies of $N$, and is reduced. Now $Spec(N) -> Spec(K)$ is etale, so this ring is etale over $M_1 otimes_K dots.c otimes_K M_r$. Thus by @etale-local-properties (4), $M_1 otimes_K dots.c otimes_K M_r$ is reduced. Thus, $Spec(N)$ is a connected component of $Spec(M_1 otimes_K dots.c otimes_K M_r)$. Hence $X_N$ is a connected component of $X_(M_1) times_X dots times_X X_(M_r)$, and is finite etale over $X$. 

  Now we consider the sequence: 
  $
    Gal(K^sep\/K^"ur" (X)) -> Gal(K^sep\/K) ->^(eta_*) pi_1^et (X, ol(eta)) -> 1
  $
  By @pi1et-mor-props (4), it suffices to prove that for a finite separable extension $L\/K$, $L = K(Z)$ for some $Z in FEt_X$ if and only if $L otimes_K K^"ur" (X)$ is a direct product of fields with a factor $K^"ur" (X)$. Now this condition is equivalent to $L subset K^"ur" (X)$. 

  ($<==$) If $L subset K^"ur" (X)$, the normalization $X_L$ is known to be finite over $X$, and etale by definition of $K^"ur" (X)$. Thus $L = K(X_L)$.

  ($==>$) If $L = K(Z)$ for some connected $Z in FEt_X$, then $Z$ is normal by @etale-local-properties (5). Since $Z -> X$ is finite, $Z$ is the normalization of $X$ in $K(Z)$. By definition of $K^"ur" (X)$, $K(Z) subset K^"ur" (X)$.  
]

#example[
  // The morphism:
  // $
  //   Gal(QQ_p^sep\/QQ_p) ->> Gal(QQ_p^"ur"\/QQ_p) cong pi_1^et (Spec(ZZ_p))
  // $
  // can be obtained this way.
  Let $K$ be a local field and $cal(O)_K$ its ring of integers. From the previous proposition, we see that: 
  $
    pi_1^et (Spec(cal(O)_K)) cong Gal(K^"ur"\/K)
  $
  However, let $k$ be the residue field of $K$, which is a finite field. Then the finite unramified extensions of $K$ are entirely classified by the finite extensions of $k$, so: 
  $
    pi_1^et (Spec(cal(O)_K)) cong Gal(K^"ur"\/K) cong Gal(ol(k)\/k) cong hat(ZZ)
  $
]

#example[
  Suppose that $U subset Spec(cal(O)_K)$ is an open subset of the ring of integers of a global field $K$. Then by the previous proposition, we see that: 
  $
    pi_1^et (U) cong Gal(K_U^"ur"\/K)
  $
  where $K_U^"ur"$ is the maximal unramified extension of $K$ relative to points (i.e. places) in $U$.
  
  #example[
    Minkowski's bound from number fields: 
    $
      (4/pi)^(s_2) (n!)/(n^n) sqrt(abs("disc"(K))) >= 1
    $
    implies that $abs("disc"(K)) > 1$ for any number field $K != QQ$. Thus for any number field $K != QQ$, there is some prime of $ZZ$ ramified in $K$. This implies that:
    $
      pi_1^et (Spec(ZZ)) = 1
    $
    is trivial. 
  ]
]

Finally, we consider one more case: the etale fundamental group of the two simplest curves, namely $PP^1$ and elliptic curves. These cases are solved directly from the definitions. 

#example[
  Let $k$ be an algebraically closed field. Recall that for a finite dominant morphism $f: X -> Y$ between smooth projective curves over $k$ such that $K(X)\/K(Y)$ is separable, we have an injective morphism:
  $
    f^* Omega_(Y\/k) arrow.r.hook Omega_(X\/k)
  $
  that is an isomorphism on the stalk at the generic point. Thus, $cal(F) = Omega_(X\/k)\/f^* Omega_(Y\/k)$ is supported on a finite set. This sheaf is called the ramification divisor. 
  
  The Riemann-Hurwitz theorem states that, for $n = [K(X):K(Y)]$ the degree of $f$:
  $
    2 - 2g(X) = n (2 - 2g(Y)) - deg(cal(F)),
  $
  where $deg(cal(F))$ is the degree of the ramification divisor.

  In the case of a connected finite etale covering $Z -> X$ where $X$ is a nonsingular curve over $k$, $Z$ is automatically a nonsingular curve (since normality is etale local). Etale morphisms are unramified, so Riemann-Hurwitz is applicable here with: 
  $
    2 - 2g(Z) = n (2 - 2g(X))
  $

  - In the case $X = PP^1_k$ is a projective line, $g(X) = 0$. Then $2 - 2g(Z) = 2n > 0$, so $g(Z) = 0$ and $n = 1$. In other words, the only connected finite etale covering of $PP^1_k$ is itself. Thus, 
    $
      pi_1^et (PP^1_k) = 1
    $
    is trivial. 

  - Assume additionally that $k$ has characteristic $0$ for simplicity, and let $X = E$ be an elliptic curve. Then $g(X) = 1$, so $2 - 2g(Z) = 0$ and $g(Z) = 1$. Choose a point $z in Z(k)$ above the origin $0 in E(k)$. Taking $z$ as the origin makes $Z$ an elliptic curve, and the covering $Z -> E$, being a pointed morphism of elliptic curves, is a homomorphism. Thus every connected finite etale covering of $E$ is a finite etale isogeny. Conversely, every finite etale isogeny with target $E$ is such a covering.

    Since $"char"(k) = 0$, every multiplication map $[n]: E -> E$ is finite etale. These maps, indexed by the positive integers ordered by divisibility, form a cofinal system of pointed Galois coverings of $(E, 0)$. Indeed, let $f: (Z, z) -> (E, 0)$ be a finite etale isogeny of degree $d$. Its dual isogeny $hat(f): (E, 0) -> (Z, z)$ satisfies:
    $
      f compose hat(f) = [d]: E -> E,
    $
    so $[d]$ dominates $f$.

    The deck transformations of $[n]$ are translations by points of $E[n](k)$. If $m = n s$, the morphism from $[m]$ to $[n]$ is $[s]: E -> E$, and the induced transition map $E[m](k) -> E[n](k)$ is multiplication by $s$. Therefore, @pi1et-as-invlim gives a canonical isomorphism:
    $
      pi_1^et (E, 0) cong invlim_(n>=1) E[n](k) cong product_(ell) T_ell (E),
    $
    where $ell$ ranges over the primes and:
    $
      T_ell (E) := invlim_(r>=1) E[ell^r](k).
    $
    is the Tate module. Since $k$ has characteristic $0$, each $T_ell (E)$ is (non-canonically) a free $ZZ_ell$-module of rank $2$. Hence, non-canonically:
    $
      pi_1^et (E, 0) cong product_(ell) ZZ_ell^2 cong hat(ZZ)^2.
    $
]
