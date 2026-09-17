#import "void-import.typ": *

== $H^1$ of constant sheaf

In this section, we will prove the following result, relating $H^1$ of a constant sheaf with the etale fundamental group. 

- For a connected noetherian scheme $X$ and a finite abelian group $G$, #h(1fr)
  $
    H^1_et (X, ul(G)) cong Hom_#[cont] (pi_1^et (X, ol(x)), G)
  $
  canonically. 

This will eventually be a central theoretical tool to reduce abstract cohomological statements to concrete geometry on finite etale coverings. 

This statement is proved through a two step classification, bridging through the notion of etale $G$-torsors. We will establish the isomorphism by showing that: 

- $Hom_#[cont] (pi_1^et (X, ol(x)), G)$ classifies etale $G$-torsors; 

- $H^1_et (X, ul(G))$ also classifies etale $G$-torsors. 

#definition(name: <defn-etale-g-torsor>)[
  Let $G$ be a finite group. An *etale $G$-torsor* over $X$ is a surjective etale $Y ->> X$ equipped with a simply transitive right $G$-action. That is, given the group scheme $X_G = union.sq.big_(g in G) X$ over $X$, there is an isomorphism: 
  $
    Y times_X X_G -> Y times_X Y, (y, g) |-> (y, y g)
  $
  // #lemma[
  //   For a finite group $G$, an etale torsor $Y$ of $G$ over $X$ must be etale locally trivial, in the sense that there exists 
  // ]
  In particular, $Y -> X$ is a finite etale covering, since $Y times_X Y -> Y times_X X_G -> Y$ is finite, and finiteness descends along faithfully flat base change by $Y -> X$ itself. 

  A *pointed etale $G$-torsor* over $X$ relative to a geometric point $ol(x)$ of $X$ is a pair $(Y, ol(y))$ where $Y$ is an etale $G$-torsor over $X$ and $ol(y) in F_(ol(x)) (Y)$ is a geometric point of $Y$ above $ol(x)$. 
]

We first classify etale $G$-torsors over $X$ by $Hom_#[cont] (pi_1^et (X, ol(x)), G)$: 

#proposition[
  For a connected noetherian scheme $X$ and a finite group $G$, there is a canonical bijection: 
  $
    {#[pointed etale $G$-torsor $(Y, ol(y))$ over $X$ relative to $ol(x)$]}/cong -> Hom_#[cont] (pi_1^et (X, ol(x)), G)
  $
  from isomorphism classes of pointed etale $G$-torsors over $X$ relative to $ol(x)$, to continuous homomorphisms $pi_1^et (X, ol(x)) -> G$. 
]
#proof[
  Step 1. Construction of the map. 

  Suppose that we have a pointed etale $G$-torsor $(Y, ol(y))$ over $X$ relative to $ol(x)$. We define a representation $rho_(Y,ol(y)): pi_1^et (X, ol(x)) -> G$ as follows. Consider the isomorphism: 
  $
    Y times G -> Y times_X Y, (y, g) |-> (y, y g)
  $
  Taking the fiber over $ol(x)$, we have a bijection of sets: 
  $
    F_(ol(x)) (Y) times G -> F_(ol(x)) (Y) times F_(ol(x)) (Y), (ol(u), g) |-> (ol(u), ol(u) g)
  $
  Thus, $G$ acts on the right of $F_(ol(x)) (Y)$-simply transitively. The base point $ol(y)$ thus defines a bijection $q_(Y,ol(y)): G -> F_(ol(x)) (Y), g |-> ol(y) g$. 
  
  Also, note that the right $G$-action on $F_(ol(x)) (Y)$ is compatible with the left $pi_1^et (X, ol(x))$-action. Each $g in G$ induces an automorphism $Y -> Y$, and so by functoriality of any $gamma in pi_1^et (X, ol(x))$, we have $gamma (ol(u) g) = (gamma ol(u)) g$. 

  For an element $gamma in pi_1^et (X, ol(x))$, it induces an automorphism on $F_(ol(x)) (Y)$. We now define: 
  $
    rho_(Y,ol(y)) (gamma) = q_(Y,ol(y))^(-1) (gamma ol(y)) in G
  $
  That is, $rho_(Y,ol(y)) (gamma) in G$ is the unique element satisfying $gamma ol(y) = ol(y) rho_(Y,ol(y)) (gamma)$. 

  - For $gamma, delta in pi_1^et (X, ol(x))$, #h(1fr)
    $
      gamma delta ol(y) = gamma (ol(y) rho_(Y,ol(y)) (delta)) = (gamma ol(y)) rho_(Y,ol(y)) (delta) = ol(y) rho_(Y,ol(y)) (gamma) rho_(Y,ol(y)) (delta)
    $
    Thus $rho_(Y,ol(y)) (gamma) rho_(Y,ol(y)) (delta) = rho_(Y,ol(y)) (gamma delta)$, and so $rho_(Y,ol(y))$ is a group homomorphism; 

  - Pick a Galois closure $tilde(Y) -> X$ of the finite etale cover $Y -> X$, so that $Aut(tilde(Y)\/X)$ is a finite quotient of $pi_1^et (X, ol(x))$. If $gamma in pi_1^et (X, ol(x))$ maps to $id in Aut(tilde(Y)\/X)$, then $gamma(ol(y)) = ol(y)$ and so $rho_(Y,ol(y)) (gamma) = 1_G in G$. Hence, $rho_(Y,ol(y))$ factors through a finite quotient of $pi_1^et (X, ol(x))$, so its kernel is open. It is thus continuous. 

  Step 2. Inverse construction. 

  Given $rho: pi_1^et (X, ol(x)) -> G$ a continuous homomorphism, we now construct a pointed torsor $(Y_(rho), ol(y)_rho)$. Indeed, $rho$ makes $G$ into a discrete finite set $G_rho$ with a continuous left $pi_1^et (X, ol(x))$-action via $(gamma, g) |-> rho(gamma) g$. 
  
  There is thus a finite etale covering $Y_rho -> X$ and an isomorphism $F_(ol(x)) (Y_rho) cong G_rho$. Take the distinguished point $ol(y)_rho in F_(ol(x)) (Y_rho)$ to correspond to the element $1_G in G_rho$. Now: 

  - $F_(ol(x)) (Y_rho) cong G_rho$ admits a simply transitive right $G$-action, compatible with the left $pi_1^et (X, ol(x))$-action. We thus have an isomorphism of finite discrete $pi_1^et (X, ol(x))$-sets: 
    $
      F_(ol(x)) (Y_rho) times G -> F_(ol(x)) (Y_rho) times F_(ol(x)) (Y_rho)
    $
    identified with $(u, g) |-> (u, u g)$ via $F_(ol(x)) (Y_rho) cong G$. This thus induces an isomorphism of finite etale coverings of $X$: 
    $
      Y_rho times_X X_G -> Y_rho times_X Y_rho
    $
    since finite etale coverings of $X$ are equivalent to finite discrete $pi_1^et (X, ol(x))$-sets. 

    It can be checked that this map $Y_rho times_X X_G -> Y_rho times_X Y_rho$ is a right $G$-action (by checking under $F_(ol(x))$). Therefore, $(Y_rho, ol(y)_rho)$ has the structure of a pointed etale $G$-torsor. 

  Step 3. These two constructions invert each other. 

  - Fix $rho in Hom_#[cont] (pi_1^et (X, ol(x)), G)$. For $gamma in pi_1^et (X, ol(x))$, $rho_(Y_rho,ol(y)_rho) (gamma) in G$ is the unique element satisfying: 
    $
      gamma ol(y)_rho = ol(y)_rho rho_(Y_rho,ol(y)_rho) (gamma)
    $
    However, under the identification $F_(ol(x)) (Y_rho) cong G_rho$, $ol(y)_rho |-> 1_G$, and $gamma$ acts by left multiplication by $rho(gamma)$. Thus, sending the equality above through $F_(ol(x)) (Y_rho) cong G_rho$, we have: 
    $
      rho(gamma) = rho_(Y_rho,ol(y)_rho) (gamma)
    $
    Thus $rho = rho_(Y_rho,ol(y)_rho)$. 
  
  - Fix a pointed etale $G$-torsor $(Y, ol(y))$, and let $rho = rho_(Y,ol(y))$. We aim to show that $(Y, ol(y)) cong (Y_rho, ol(y)_rho)$ as etale $G$-torsors. Indeed, we have a bijection: 
    $
      G_rho cong F_(ol(x)) (Y_rho) -> F_(ol(x)) (Y), g |-> ol(y) g
    $
    For $gamma in pi_1^et (X, ol(x))$, $gamma$ acts on the left by sending $g$ to $rho(gamma) g$. Then this element is sent to $ol(y) rho(gamma) g = gamma ol(y) g$ by definition of $rho$. Thus, the bijection above is $pi_1^et (X, ol(x))$-equivariant. It sends $1_G in G$ (i.e. $ol(y)_rho in F_(ol(x)) (Y_rho)$) to $ol(y)$ by definition. 

    Since finite etale coverings of $X$ are equivalent to finite discrete $pi_1^et (X, ol(x))$-sets, the map above induces an isomorphism $(Y_rho, ol(y)_rho) -> (Y, ol(y))$ as pointed etale covers. 

    Finally, note that the isomorphism $G_rho -> F_(ol(x)) (Y), g |-> ol(y) g$ above is right $G$-equivariant. Thus, the isomorphism $(Y_rho, ol(y)_rho) -> (Y, ol(y))$ is right $G$-equivariant, hence an isomorphism as etale $G$-torsors. 

  We have thus completed this classification. 
]

#corollary(name: <hom-from-pi1-classifies-torsors>)[
  For a connected noetherian scheme $X$ and a finite group $G$, there is a canonical bijection: 
  $
    {#[etale $G$-torsor $Y$ over $X$]}/cong -> (Hom_#[cont] (pi_1^et (X, ol(x)), G))/(#[conjugation in $G$])
  $
  from isomorphism classes of etale $G$-torsors over $X$, to classes of continuous homomorphisms $pi_1^et (X, ol(x)) -> G$ modulo conjugation in $G$. 

  #remark[
    Note that the LHS is independent of the base point $ol(x)$, but the RHS formally depends on $ol(x)$. However, the RHS is in fact independent of $ol(x)$. Indeed, for any other base point $ol(x')$, we have an isomorphism $pi_1^et (X, ol(x)) cong pi_1^et (X, ol(x'))$ unique up to conjugation. Thus, 
    $
      (Hom_#[cont] (pi_1^et (X, ol(x)), G))/(#[conjugation in $G$]) cong (Hom_#[cont] (pi_1^et (X, ol(x')), G))/(#[conjugation in $G$])
    $
    is a canonical bijection, independent from the choice of isomorphism $pi_1^et (X, ol(x)) cong pi_1^et (X, ol(x'))$, since the ambiguity of a conjugation is quotiented out. 
  ]
]
#proof[
  Fix a pointed etale $G$-torsor $(Y, ol(y))$ over $(X, ol(x))$. Then as discussed in the previous proposition, $F_(ol(x)) (Y) = ol(y) G$, and so the pointed etale $G$-torsors over $(X, ol(x))$ sharing the same torsor as $(Y, ol(y))$ are exactly ${(Y, ol(y) h)}_(h in G)$. Now for $gamma in pi_1^et (X, ol(x))$,  
  $
    ol(y) h rho_(Y,ol(y) h) (gamma) = gamma ol(y) h = ol(y) rho_(Y,ol(y)) (gamma) h
  $
  i.e. $h rho_(Y,ol(y) h) (gamma) = rho_(Y,ol(y)) (gamma) h$. Thus $rho_(Y,ol(y) h) (gamma) = h^(-1) rho_(Y,ol(y)) (gamma) h$, and so $rho_(Y,ol(y)h)$ is a conjugate of $rho_(Y,ol(y))$ by $h$. 

  Hence, forgetting the distinguished points from pointed etale torsors on LHS of the classification, is exactly the same as quotienting out conjugations in $G$ on RHS of the classification. We are thereby done. 
]

Next, we classify etale $G$-torsors over $X$ by $caron(H)^1_et (X, ul(G))$. 

#proposition(name: <cech-h1-classifies-torsors>)[
  For a connected noetherian scheme $X$ and a finite abelian group $G$, there is a canonical bijection: 
  $
    {#[etale $G$-torsor $Y$ over $X$]}/cong -> caron(H)^1_et (X, ul(G)) cong H^1_et (X, ul(G))
  $
]
#proof[
  Step 1. Construction of the forward map. 

  Let $p: Y -> X$ be an etale $G$-torsor with trivialization $Y times_X X_G -> Y times_X Y$. By @fet-trivializes-fet-locally, $Y -> X$ is etale locally trivial. Thus, there is an etale cover $cal(U) = {U_i -> X}$ and sections $s_i: U_i -> Y_i = U_i times_X Y$ of $p_i: Y_i -> U_i$. The sections $s_i$ trivialize the torsor via: 
  $
    psi_i: U_i times G -> Y_i, (u_i, g) |-> s_i (u_i) g 
  $
  This is an isomorphism, for given a fixed geometric point $ol(u_i)$ of $U_i$ above $ol(x)$ of $X$, upon applying $F_(ol(u_i))$, this map is: 
  $
    G -> F_(ol(u_i)) (Y_i) cong F_(ol(x)) (Y), g |-> s_i (ol(u_i)) g
  $ 
  which is bijective by the torsor condition. 

  Now on each intersection $U_(i,j) = U_i times_X U_j$, we have restrictions: 
  $
    psi^((1))_(i,j) = psi_i|_(U_(i,j) times G): U_(i,j) times G cong Y_(i,j) \
    psi^((2))_(i,j) = psi_j|_(U_(i,j) times G): U_(i,j) times G cong Y_(i,j)
  $
  Now $(psi_(i,j)^((2)))^(-1) compose psi_(i,j)^((1)): U_(i,j) times G -> U_(i,j) times G$ is a $G$-equivariant $U_(i,j)$-morphism. It is thus right action (i.e. addition) by a locally constant function $U_(i,j) -> G$, i.e. a section $alpha_(i,j) in ul(G)(U_(i,j))$. 

  - ${alpha_(i,j)}$ satisfies the cocycle conditions. Indeed, let $psi_(i,j,k)^((1,2,3))$ be the restriction of $psi_i, psi_j, psi_k$ to $U_(i,j,k) times G -> Y_(i,j,k)$. Then: 

    - $alpha_(i,j)|_(U_(i,j,k)) + alpha_(j,k)|_(U_(i,j,k))$ corresponds to the map: #h(1fr)
      $
        (psi_(j,k)^((2)))^(-1)|_(U_(i,j,k) times G) compose psi_(j,k)^((1))|_(U_(i,j,k) times G) compose (psi_(i,j)^((2)))^(-1)|_(U_(i,j,k) times G) compose psi_(i,j)^((1))|_(U_(i,j,k) times G)
      $
      which is: 
      $
        (psi_(i,j,k)^((3)))^(-1) compose psi_(i,j,k)^((2)) compose (psi_(i,j,k)^((2)))^(-1) compose psi_(i,j,k)^((1)) = (psi_(i,j,k)^((3)))^(-1)  compose psi_(i,j,k)^((1))
      $
      which is just $(psi_(i,k)^((2)))^(-1)|_(U_(i,j,k) times G) compose psi_(i,k)^((1))|_(U_(i,j,k) times G)$, corresponding to $alpha_(i,k)|_(U_(i,j,k))$. 

      Hence, we have the cocycle conditions: 
      $
        alpha_(i,j)|_(U_(i,j,k)) + alpha_(j,k)|_(U_(i,j,k)) = alpha_(i,k)|_(U_(i,j,k))
      $
  
  Thus, $(alpha_(i,j))$ defines a Cech 1-cycle, hence a class in $caron(H)^1 (cal(U), ul(G))$. Thus we have a class $alpha in caron(H)^1 (X, ul(G))$. 

  - $alpha$ is independent from the choice of sections $s_i$. Given another set of sections $s'_i: U_i -> Y_i$, defining trivializations: 
    $
      psi'_i: U_i times G -> Y_i
    $
    we have $chi_i = psi'_i^(-1) compose psi_i: U_i times G -> U_i times G$ a $G$-equivariant $U_i$-morphism. It is thus defined by right action (i.e. addition) of a locally constant function $U_i -> G$, i.e. a section $h_i in ul(G)(U_i)$. 

    Then: 
    $
      (psi'_(i,j)^((2)))^(-1) compose psi'_(i,j)^((1)) = chi_j|_(U_(i,j) times G) compose (psi_(i,j)^((2)))^(-1) compose psi_(i,j)^((1)) compose chi_i^(-1)|_(U_(i,j) times G)
    $
    and the $alpha'_(i,j) in ul(G)(U_(i,j))$ defined by the sections ${s'_i}$ satisfies: 
    $
      alpha'_(i,j) = alpha_(i,j) + h_j - h_i
    $
    Thus $(alpha'_(i,j)) - (alpha_(i,j)) = (h_j - h_i)_(i,j)$ is a Cech 1-boundary, and so $(alpha'_(i,j))$ induces the same class in $caron(H)^1 (cal(U), ul(G))$ as $(alpha_(i,j))$. 

  - For a refinement $cal(V) = {V_j -> X}$ of $cal(U)$ by $V_j -> U_(lambda(j))$, we have sections $t_j: V_j -> Y'_j = V_j times_X Y$ to $Y'_j -> V_j$, obtained by base changing $s_(lambda(j))$. They induce trivializations: 
    $
      phi_j: V_j times G -> Y'_j
    $
    Then $(phi_(j_1,j_2)^((2)))^(-1) compose phi_(j_1,j_2)^((1))$ is a base change of $(psi_(lambda(j_1),lambda(j_2))^((2)))^(-1) compose psi_(lambda(j_1),lambda(j_2))^((1))$. Thus, the $(beta_(j_1,j_2))$ defined by the sections $t_j$ satisfies: 
    $
      alpha_(lambda(j_1), lambda(j_2))|_(V_(j_1,j_2)) = beta_(j_1,j_2)
    $
    Hence, $alpha in caron(H)^1 (cal(U), ul(G))$ and $beta in caron(H)^1 (cal(V), ul(G))$ induce the same class in the directed limit defining $caron(H)^1 (X, ul(G))$. 

    By comparing any two etale covers against a new etale cover admitting refinements to both, we see that the construction of the class $alpha in caron(H)^1 (X, ul(G))$ is independent from the choice of trivializing cover. 

  Denote by this class $alpha = alpha(Y) in caron(H)^1 (X, ul(G))$. We have now defined the forward map: 
  $
    {#[etale $G$-torsor $Y$ over $X$]}/cong -> caron(H)^1_et (X, ul(G)), Y |-> alpha(Y)
  $

  Step 2. Construction of the backward map. 

  - Since $X$ is noetherian, every etale cover $cal(U)$ may be refined by an etale cover using finitely many maps from noetherian affine etale $X$-schemes. Replacing these schemes with their disjoint union does not change $caron(H)^1 (cal(U), ul(G))$ due to the sheaf conditions. Thus, 
    $
      caron(H)^1 (X, ul(G)) = dirlim_(X' ->> X #[etale] \ X' #[noetherian]) caron(H)^1 ({X'}, ul(G))
    $

  Given a class $alpha in caron(H)^1 (X, ul(G))$, we may represent it by an element:
  $
    [alpha_(X')] in caron(H)^1 ({X'}, ul(G)) = (ker(ul(G)(X'') -> ul(G)(X''')))/(im(ul(G)(X') -> ul(G)(X'')))
  $
  for $alpha_(X') in ul(G)(X'')$. 

  Put $X'' = X' times_X X', X''' = X' times_X X' times_X X'$. We have projections: 
  $
    p_(12), p_(23), p_(13): X''' -> X''
  $
  We now define an etale $G$-torsor $Y$ over $X$ as follows. Take the trivial $G$-torsor $X'_G = X' times G$. We now define an isomorphism: 
  $
    eta: X'_G times_X X' -> X' times_X X'_G
  $
  as follows. Identify both sides as $X''_G$, and define an isomorphism $X''_G -> X''_G$ by right action (i.e. addition) by the locally constant function $alpha_(X'): X'' -> G$. Then: 
  $
    alpha_(X')|_(p_(12)) + alpha_(X')|_(p_(23)) = alpha_(X')|_(p_(13))
  $
  is exactly the cocycle condition for $eta$. Thus, by fpqc descent of relatively affine schemes, and by preservation of finiteness and etaleness under fpqc descent, there exists a finite etale $Y -> X$, with an isomorphism $X' times_X Y cong X' times G$ with canonical descent datum identified with $eta$. 

  Note that $eta$ is $G$-equivariant. By fpqc descent of morphisms, $Y$ carries a right $G$-action. Furthermore, $Y times_X X_G -> Y times_X Y$ is an isomorphism upon base changing to $X'$, hence an isomorphism. Thus, $Y$ is an etale $G$-torsor over $X$, which we shall denote by $Y_alpha$. 

  - The isomorphism class of $Y_alpha$ is independent from the representative $[alpha_(X')] in caron(H)^1 ({X'}, ul(G))$. Indeed, for another representative $tilde(alpha)_(X')$, $tilde(alpha)_(X') - alpha_(X') = beta|_(p_2) - beta|_(p_1)$ for some $beta in ul(G)(X')$. 

    $beta$ induces an automorphism $psi: X'_G -> X'_G$ by addition of $beta$. Then $tilde(alpha)_(X') - alpha_(X') = beta|_(p_2) - beta|_(p_1)$ gives a commutative diagram: 
    // https://q.uiver.app/#r=typst&q=WzAsNCxbMCwwLCJYJ19HIHRpbWVzX1ggWCciXSxbMCwxLCJYJ19HIHRpbWVzX1ggWCciXSxbMSwwLCJYJyB0aW1lc19YIFgnX0ciXSxbMSwxLCJYJyB0aW1lc19YIFgnX0ciXSxbMCwyLCJldGEiXSxbMSwzLCJ0aWxkZShldGEpIiwyXSxbMCwxLCJiZXRhIiwyXSxbMiwzLCJiZXRhIl1d
    #align(center, diagram({
      node((0, 0), [$X'_G times_X X'$])
      node((0, 1), [$X'_G times_X X'$])
      node((1, 0), [$X' times_X X'_G$])
      node((1, 1), [$X' times_X X'_G$])
      edge((0, 0), (1, 0), [$eta$], label-side: left, "->")
      edge((0, 1), (1, 1), [$tilde(eta)$], label-side: right, "->")
      edge((0, 0), (0, 1), [$beta$], label-side: right, "->")
      edge((1, 0), (1, 1), [$beta$], label-side: left, "->")
    }))
    That is, $beta$ intertwines the descent map $eta, tilde(eta): X'_G times_X X' -> X' times_X X'_G$ defined by $alpha_(X'), tilde(alpha)_(X')$. 
    
    By fpqc descent, $beta$ descends to an isomorphism $Y -> tilde(Y)$ between the two etale $G$-torsors over $X$ defined by $alpha_(X'), tilde(alpha)_(X')$. Since $beta$ is $G$-equivariant, the isomorphism $Y -> tilde(Y)$ is $G$-equivariant, thus is an isomorphism of $G$-torsors. 

  - The isomorphism class of $Y_alpha$ is independent from the chosen $X'$. Indeed, for another etale cover $tilde(X)' -> X$ with $tilde(X)'$ noetherian, and a refinement $tilde(X)' -> X'$, we claim that the etale $G$-torsor $Y$ defined by $alpha_(X')$ is the same as the one defined by $alpha_(tilde(X)') = alpha_(X')|_(tilde(X)'')$. 

    Indeed, by definition, the map defined by $alpha_(X')$: 
    $
      eta: X'_G times_X X' -> X' times_X X'_G
    $
    base changes to the map defined by $alpha_(tilde(X)')$: 
    $
      tilde(eta): tilde(X)'_G times_X tilde(X)' -> tilde(X)' times_X tilde(X)'_G
    $
    along $tilde(X)'' -> X''$. Thus, $Y$ defined by $eta$ induces the same descent datum as $tilde(eta)$, and so $Y cong tilde(Y)$. 

  We have now constructed a well-defined isomorphism class $Y_alpha$ of etale $G$-torsor over $X$ from $alpha in caron(H)^1 (X, ul(G))$. 

  Step 3. These two constructions invert each other. 

  - Fix $alpha in caron(H)^1 (X, ul(G))$, and we need to prove $alpha(Y_alpha) = alpha$. 

    Suppose that $alpha$ is represented by $alpha_(X') in caron(H)^1 ({X'}, ul(G))$ for an etale cover $X' ->> X$ with $X'$ noetherian. Then by definition, $Y_alpha$ has a trivialization: 
    $
      psi: X' times G cong X' times_X Y_alpha
    $
    Picking the component corresponding to $1_G in G$ gives a section $s: X' -> X' times_X Y_alpha$, which directly gives the trivialization $psi$. Then: 
    $
      (psi|_(p_2))^(-1) compose psi|_(p_1): X''_G -> X''_G
    $
    is identified with the descent datum $eta: X'_G times_X X' -> X' times_X X'_G$, and is hence addition of $alpha_(X') in ul(G)(X'')$. Thus $alpha(Y_alpha) = [alpha_(X')] = alpha$ by definition. 

  - For a torsor $Y$, by refining a trivializing cover, we may assume that $Y$ is trivialized by an etale cover $X' ->> X$ for $X'$ noetherian, giving $psi: X' times_X Y cong X' times G$. The map: 
    $
      (psi|_(p_2))^(-1) compose psi|_(p_1): X''_G -> X''_G
    $
    is represented by a locally constant function $alpha_(X') in ul(G)(X'')$. In other words, the canonical descent datum for $Y$ w.r.t. $X' -> X$ is isomorphic to: 
    $
      eta: X'_G times_X X' -> X' times_X X'_G
    $
    constructed by addition of $alpha_(X')$. Hence by fpqc descent, $Y cong Y_([alpha_(X')]) = Y_(alpha(Y))$. 

  We are thereby done with the classification. The isomorphism from $caron(H)^1_et$ to $H^1_et$ is due to @h1-is-cech-h1. 
]

#theorem(name: <h1-of-const-sheaf>)[
  Let $X$ be a connected noetherian scheme. For any finite abelian group $G$, there exists a canonical isomorphism: 
  $
    H^1_et (X, ul(G)) cong Hom_#[cont] (pi_1^et (X, ol(x)), G)
  $
]
#proof[
  Note that $G$ has trivial conjugation as an abelian group. Thus by @hom-from-pi1-classifies-torsors and @cech-h1-classifies-torsors, we have a bijection: 
  $
    Hom_#[cont] (pi_1^et (X, ol(x)), G) ->^tilde {#[etale $G$-torsor $Y$ over $X$]}/cong ->^tilde caron(H)^1 (X, ul(G)), rho |-> c_rho
  $
  We still need to show that this is an abelian group homomorphism. For this, we devise an explicit description of this map. 

  - Take $rho in Hom_#[cont] (pi_1^et (X, ol(x)), G)$, let $N <= pi_1^et (X, ol(x))$ be a finite index open subgroup contained in $ker(rho)$. Then $N$ corresponds to a Galois covering $(X', ol(x')) -> (X, ol(x))$ so that $rho$ factors through the finite quotient $Q = Aut(X'\/X)$ as $rho_Q: Q -> G$. 

    On the other hand, let $Y_rho$ be the $G$-torsor to which $rho$ corresponds. By construction, $F_(ol(x)) (Y_rho) cong G_rho$ has left $pi_1^et (X, ol(x))$-action by $rho$, and right regular $G$-action. 

    Now $X' -> X$ trivializes $Y_rho$. Indeed, 
    $
      F_(ol(x)) (X' times_X Y) cong F_(ol(x)) (X') times F_(ol(x)) (Y) cong Q times G_rho = union.sq.big_(g in G) {(q, rho_Q (q) + g)}
    $
    partitions into left $Q$-orbits (i.e. $pi_1^et (X,ol(x))$-orbits) isomorphic to $Q$, inducing a trivialization: 
    $
      phi: X' times G -> X' times_X Y
    $
    which, on $F_(ol(x))$, is: 
    $
      Q times G -> Q times G_rho, (q, g) |-> (q, rho_Q (q) + g)
    $

    Let $p_(1,2): X'' -> X'$ be the projections. Then we need to consider the locally constant function represented by 
    $
      (phi|_(p_2))^(-1) compose phi|_(p_1): X'' times G -> X'' times G
    $
    On $F_(ol(x))$, this map is: 
    $
      Q times Q times G &-> Q times Q times G \
      (q_1, q_2, g) &|-> (q_1, q_2, g + rho_Q (q_1)) |-> (q_1, q_2, g + rho_Q (q_1) - rho_Q (q_2))
    $
    is addition by the element $rho_Q (q_1) - rho_Q (q_2) in G$. Thus, for $q_1, q_2 in Q$, $c_rho in caron(H)^1 (X, ul(G))$ is represented by the class $alpha_rho in ul(G)(X'')$, which is a locally constant function $alpha_rho: X'' = X' times_X X' -> G$ characterized by: 
    $
      alpha_rho (q_1 ol(x'), q_2 ol(x')) = rho_Q (q_1) - rho_Q (q_2)
    $
    This equation uniquely characterizes $alpha_rho: X'' = X' times_X X' -> G$, since every connected component of $X''$ contains a geometric point above $ol(x)$. 

    In summary: 

    - The class $c_rho$ is represented by $alpha_rho in ul(G)(X'')$, i.e. a locally constant function $alpha_rho: X' times_X X' -> G$, uniquely characterized by: 
      $
        alpha_rho (q_1 ol(x'), q_2 ol(x')) = rho_Q (q_1) - rho_Q (q_2)
      $

    Now to show that $rho |-> c_rho$ is additive, given $rho_(1,2)$, pick a finite index subgroup $N subset ker(rho_1) inter ker(rho_2)$, and the characterization above immediately gives additivity. 

  We thus have constructed an abelian group isomorphism: 
  $
    Hom_#[cont] (pi_1^et (X, ol(x)), G) ->^tilde caron(H)^1 (X, ul(G))
  $
  Composing with the isomorphism $caron(H)^1 (X, ul(G)) cong H^1_et (X, ul(G))$ of @h1-is-cech-h1 concludes the proof. 
]
