#import "void-import.typ": *

== Fpqc descent
#let DD = math.op[DD]

In this section, we will establish an important technical tool called fpqc descent. It is the critical algebraic engine behind the construction of etale sheaves, and will also be used in a few other places to descend various structures like line bundles and etale torsors. 

To put it simply, descent theory answers the following questions. Given a morphism $f: S' -> S$: 

- When does $cal(G) in QCoh(S')$ come from the pullback of some $cal(F) in QCoh(S)$, and how natural is this construction? 

- When does a morphism $S' -> X$ lift to a morphism $S -> X$, and how natural this construction is? 

It turns out that when $S' -> S$ is fpqc, both questions have satisfactory answers. 

#definition(name: <defn-faithfully-flat-and-fpqc-morphisms>)[
  A scheme morphism $f: S' -> S$ is called *faithfully flat*, if it is flat and surjective. A ring morphism $A -> B$ is called *faithfully flat*, if $Spec(B) -> Spec(A)$ is faithfully flat. 
  
  A scheme morphism $f: S' -> S$ is called *fpqc*, if it is #furi[fidelement plat][faithfully flat] and quasi-compact. 
]

#notation(name: <descent-notation>)[
  Let $f: S' -> S$ be a morphism between schemes. We will denote $S'' = S' times_S S'$, and $S''' = S' times_S S' times_S S'$. We then have projections: 
  $
    p_(12), p_(13), p_(23): S''' -> S''
  $
  onto components $(1,2),(1,3),(2,3)$ respectively, and projections: 
  $
    p_1, p_2: S'' -> S'
  $
  onto either component. 

  For any object $X$ over $S$, we will use $X', X'', X'''$ to denote its base change to $S', S'', S'''$ respectively. 
]

#construction(name: <descent-data>)[
  Let $cal(F) in QCoh(S)$ and $cal(F)' = f^* cal(F)$. Then one has a canonical isomorphism: 
  $
    eta: p_1^* cal(F)' -> p_2^* cal(F)'
  $
  as quasi-coherent sheaves on $S''$. Locally, this isomorphism should be viewed as: 
  $
    (M otimes_A A') otimes_A A' -> A' otimes (M otimes_A A'), (m otimes a'_1) otimes a'_2 |-> a'_1 otimes (m otimes a'_2)
  $
  for an $A$-algebra $A'$ and an $A$-module $M$. $eta$ naturally satisfies the cocycle condition: 
  $
    p_(13)^* eta = p_(23)^* eta compose p_(12)^* eta
  $
  We call the pair $(cal(F)', eta)$ the *canonical descent datum* for $cal(F)'$. 

  Mimicking this construction, a *descent datum* for $S' -> S$ is a pair $(cal(F)', eta)$, where $cal(F)' in QCoh(S')$, and $eta: p_1^* cal(F)' -> p_2^* cal(F)'$ satisfies the cocycle condition $p_(13)^* eta = p_(23)^* eta compose p_(12)^* eta$. A morphism between descent data is a morphism between their underlying sheaves, compatible with the isomorphisms $eta$. 
  
  The category of descent datum for $f: S' -> S$ is denoted $DD(f)$. Then the construction of the canonical descent datum gives a functor: 
  $
    QCoh(S) -> DD(f), cal(F) |-> (cal(F)', eta)
  $
  We want to answer the question whether this functor is an equivalence of categories. 
]

#lemma[
  Let $f: S' -> S$ be faithfully flat and $(cal(G), eta) in DD(f)$ be any descent datum. Then $eta$ satisfies the counit condition: 
  $
    Delta^* eta = id_(Delta^* cal(G))
  $
]
#proof[
  Consider the cocycle condition: 
  $
    p_(13)^* eta = p_(23)^* eta compose p_(12)^* eta
  $
  Take the morphism $D: S'' -> S''', (x, y) |-> (x, x, y)$, i.e. the fiber product of $(p_1, p_1, p_2)$. Applying $D^*$ to the relation above, we see: 
  $
    (p_(13) compose D)^* eta = (p_(23) compose D)^* eta compose (p_(12) compose D)^* eta
  $
  i.e. 
  $
    eta = eta compose (Delta compose p_1)^* eta
  $
  Since $eta$ is an isomorphism, we may cancel it to get $p_1^* Delta^* eta = id_(p_1^* Delta^* cal(G))$. $p_1$ is a base change of $f$, and is hence faithfully flat. Thus $p_1^*$ is faithful on morphisms, and so $Delta^* eta = id_(Delta^* cal(G))$. 
]

#lemma(name: <amitsur-complex-exact>)[
  (Amitsur sequence) Given $A -> A'$ faithfully flat, let $A^((n))$ be the tensor product of $n$ copies of $A'$ over $A$. For any $M in AMod(A)$, denote $M^((n)) = M otimes_A A^((n))$. Then the sequence: 
  $
    0 -> M -> M' -> dots.c -> M^((n)) &-> M^((n+1)) -> dots.c \
    m otimes a_1 otimes dots.c otimes a_n &|-> m otimes (sum_(i=0)^n (-1)^i (dots.c otimes a_(i-1) otimes 1 otimes a_i otimes dots.c))
  $
  is exact. In particular, we have a left exact sequence: 
  $
    0 -> M &-> M' &&-> M'' \
     m &|-> m otimes 1 #killcol \
     && #killcol m otimes a' &|-> m otimes (1 otimes a' - a' otimes 1) 
  $
  for every $M in AMod(A)$. 
]
#proof[
  One can check directly that the Amitsur sequence is a chain complex. (You should have seen this combinatorial argument once, in algebraic topology when proving that the singular complex is indeed a chain complex.)

  Since $A -> A'$ is faithfully flat, to prove that the Amitsur sequence is exact, it suffices to show that its base change to $A'$ is exact. Put $N^((n)) = A' otimes_A M^((n))$ and reorder the tensor factors to identify: 
  $
    N^((n)) = M otimes_A A' otimes_A A^((n))
  $
  where the first $A'$ is the distinguished tensor factor coming from $A' otimes_A -$. Now for the base changed complex, the differential is: 
  $
    d^n: N^((n)) &-> N^((n+1)) \
    m otimes a_0 otimes a_1 otimes dots.c otimes a_n &|-> m otimes a_0 otimes (sum_(i=0)^n (-1)^i (dots.c otimes a_(i-1) otimes 1 otimes a_i otimes dots.c))
  $
  which leaves the distinguished factor $a_0$ untouched. Let:
  $
    delta^n_i (m otimes a_0 otimes a_1 otimes dots.c otimes a_n) = m otimes a_0 otimes dots.c otimes a_(i-1) otimes 1 otimes a_i otimes dots.c
  $
  be the $i$-th coface map in the sum defining $d^n$, so $d^n = sum_(i=0)^n (-1)^i delta^n_i$. We now define: 
  $
    phi^n: N^((n+1)) &-> N^((n)) \
    m otimes a_0 otimes a_1 otimes dots.c otimes a_n &|-> m otimes a_0 a_1 otimes a_2 otimes dots.c otimes a_n
  $
  Then: 

  - $delta^n_0$ inserts $1$ at position $1$, so $phi^n compose delta^n_0$ sends $m otimes a_0 otimes dots.c |-> m otimes a_0 otimes 1 otimes dots.c |-> m otimes a_0 otimes dots.c $ and is the identity: 
    $
      phi^n compose delta^n_0 = id_(N^((n)))
    $

  - For $i >= 1$, $delta^n_i$ inserts $1$ at position $i+1>=2$. Thus $phi^n$ would multiply the old $0$th and $1$st tensor factor, leaving the inserted $1$ at position $i$. Thus: 
    $
      phi^n compose delta^n_i = delta^(n-1)_(i-1) compose phi^(n-1)
    $

  Thus, 
  $
    phi^n compose d^n = sum_(i=0)^n (-1)^i phi^n compose delta^n_i = id_(N^((n))) - sum_(i=0)^(n-1) (-1)^i delta_i^(n-1) compose phi^(n-1) = id_(N^((n))) - d^(n-1) compose phi^(n-1)
  $
  Thus $phi^n$ defines a chain homotopy from $id_(N^((bullet)))$ to $0$, and so the chain complex $0 -> N^((bullet))$ is exact. 
]

#proposition[
  (Affine case of fpqc descent) Let $f: A -> A'$ be faithfully flat. Then: 
  
  + For any $M, N in AMod(A)$, the sequence: #h(1fr)
    $
      0 -> Hom_A (M, N) -->^(f^*) Hom_(A') (M', N') -->^(p_1^* - p_2^*) Hom_(A'') (M'', N'')
    $
    is left exact, where $p_1, p_2: A' -> A'' = A' otimes_A A'$ are the natural maps into the two components of $A''$. In other words, 
    $
      QCoh(Spec(A)) -> DD(Spec(A') -> Spec(A))
    $
    is fully faithful. 

  + Given a module $N' in AMod(A')$ and an $A''$-isomorphism $eta: N' otimes_A A' -> A' otimes_A N'$ satisfying the cocycle condition $p_(13)^* eta = p_(23)^* eta compose p_(12)^* eta$ (where $p_(12), p_(13), p_(23): A'' -> A'''$ are the natural maps into all three choices of two components), there exists a module $N in AMod(A)$ and an isomorphism $N' cong N otimes_A A'$ under which the natural isomorphism $(N otimes_A A') otimes_A A' -> A' otimes_A (N otimes_A A')$ is compatible with $eta$. 

    In other words, 
    $
      QCoh(Spec(A)) -> DD(Spec(A') -> Spec(A))
    $
    is essentially surjective. 
]
#proof[
  (1) That $f^*$ is injective is a feature of faithfully flatness, and this sequence is a chain complex naturally since $p_1 compose f = p_2 compose f$. It suffices to show that any morphism $phi in Hom_(A') (M', N')$ satisfying $p_1^* phi = p_2^* phi$, or equivalently, after expanding the definitions: 
  $
    phi(m otimes a'_1) otimes a'_2 = a'_1 otimes phi(m otimes a'_2)
  $
  is obtained by lifting some $psi in Hom_A (M, N)$. For each fixed $m in M$, consider $phi(m otimes 1) in N'$. Then: 
  $
    phi(m otimes 1) otimes 1 = 1 otimes phi(m otimes 1)
  $
  from the condition above. From the Amitsur sequence, there exists a unique $n in N$ s.t. $n otimes 1 = phi(m otimes 1)$. We then define $psi(m) := n$. Since the choice of $n$ is unique, we see easily that $psi$ is $A$-linear, and so $phi$ is the base change of $psi$. 

  (2) Set: 
  $
    N = {x in N': eta(x otimes 1) = 1 otimes x in A' otimes_A N'}
  $
  Then $N$ is an $A$-module fitting in the exact sequence: 
  $
    0 -> N arrow.r.hook^i N' ->^(gamma - delta) A' otimes_A N'
  $
  where $gamma, delta: N' -> A' otimes_A N'$, $gamma(x) := 1 otimes x$, and $delta(x) := eta(x otimes 1)$. Consider the diagram: 
  #align(center, diagram({
    node((-1, 0), $0$)
    edge("->")
    node((0, 0), $N otimes_A A'$)
    edge("hook->")
    node((1, 0), $N' otimes_A A'$)
    edge("->", $(gamma - delta) otimes id_(A')$)
    node((2, 0), $A' otimes_A N' otimes_A A'$)

    node((-1, 1), $0$)
    edge("->")
    node((0, 1), $N'$)
    edge("hook->", label-side: right/*, $x |-> x otimes 1$*/)
    node((1, 1), $A' otimes_A N'$)
    edge("->", label-side: right/*, $x otimes a' |-> x otimes (1 otimes a' - a' otimes 1)$*/)
    node((2, 1), $A' otimes A' otimes N'$)
    edge((1, 0), (1, 1), "->", $eta$)
    edge((2, 0), (2, 1), "->", $p_(23)^* eta$)
  }, spacing: 4.5em))
  where the first row is the sequence $0 -> N arrow.r.hook^i N' ->^(gamma - delta) A' otimes_A N'$ tensored by $A'$ and is exact, and the second row is the Amitsur sequence. We claim that the right square commutes. Indeed, letting $eta(x otimes 1) = sum_i a'_i otimes x_i$, 
  #align(center, diagram({
    node((0, 0), $x otimes a'$)
    edge("|->", $(gamma-delta) otimes id_(A')$)
    node((1, -1), $(1 otimes x - sum_i a'_i otimes x_i) otimes a'$)
    edge("|->", $p_(23)^* eta$)
    node((2, -1), $1 otimes eta(x otimes a') - sum_i a'_i otimes eta(x_i otimes a')$)
    edge((0, 0), (1, 1), "|->", $eta$)
    node((1, 1), $sum_i a'_i otimes a' x_i$)
    edge("|->", [Amitsur])
    node((2, 1), $sum_i 1 otimes a'_i otimes a' x_i - sum_i a'_i otimes 1 otimes a' x_i$)
  }))
  Now $eta(x otimes a') = sum_i a'_i otimes a' x_i$ by linearity. Thus, to show that the right square commutes, it suffices to prove: 
  $
    sum_i a'_i otimes eta(x_i otimes a') = sum_i a'_i otimes 1 otimes a' x_i
  $
  This is just the cocycle condition: 
  #align(center, diagram({
    node((0, 0), $x otimes 1 otimes a'$)
    edge("|->", $p_(12)^* eta$)
    node((0, 1), $sum_i a'_i otimes x_i otimes a'$)
    edge("|->", $p_(23)^* eta$)
    node((1, 1), $sum_i a'_i otimes eta(x_i otimes a')$)
    edge("=")
    node((1, 0), $sum_i a'_i otimes 1 otimes a' x_i$)
    edge((0, 0), (1, 0), "|->", $p_(13)^* eta$)
  }))
  In other words, in the commutative diagram: 
  #align(center, diagram(
    {
      node((-1, 0), $0$)
      edge("->")
      node((0, 0), $N otimes_A A'$)
      edge("hook->")
      node((1, 0), $N' otimes_A A'$)
      edge("->", $(gamma - delta) otimes id_(A')$)
      node((2, 0), $A' otimes_A N' otimes_A A'$)
      
      node((-1, 1), $0$)
      edge("->")
      node((0, 1), $N'$)
      edge("hook->", label-side: right /*, $x |-> x otimes 1$*/)
      node((1, 1), $A' otimes_A N'$)
      edge("->", label-side: right /*, $x otimes a' |-> x otimes (1 otimes a' - a' otimes 1)$*/)
      node((2, 1), $A' otimes A' otimes N'$)
      edge((1, 0), (1, 1), "->", $eta$)
      edge((2, 0), (2, 1), "->", $p_(23)^* eta$)
      edge((0, 0), (0, 1), "-->", $q$)
    },
    spacing: 4.5em,
  ))
  the rows are exact and $eta, p_(23)^* eta$ are isomorphisms. Thus there exists an isomorphism $q: N otimes_A A' -> N'$ fitting in the dashed arrow, identifying the kernels of two essentially identical morphisms. In other words, the isomorphism $q$ satisfies: 
  $
    1 otimes q(n otimes 1) = eta(n otimes 1) = 1 otimes n, forall n in N
  $
  and so $q(n otimes 1) = n, forall n in N$. We now check that the following diagram commutes: 
  #align(center, diagram({
    node((0, 0), $(N otimes_A A') otimes_A A'$)
    edge("->"/*, $(x otimes a'_1) otimes a'_2 |-> a'_1 otimes (x otimes a'_2)$*/)
    node((1, 0), $A' otimes_A (N otimes_A A')$)
    edge((0, 0), (0, 1), "->", $q otimes id_(A')$)
    node((0, 1), $N' otimes_A A'$)
    edge("->", $eta$)
    node((1, 1), $A' otimes_A N'$)
    edge((1, 0), (1, 1), "->", $id_(A') otimes q$)
  }, spacing: 4em))
  Indeed, from linearity, it suffices to verify commutativity for all elements of the form $(n otimes 1) otimes 1$ in this diagram: 
  #align(center, diagram({
      node((0, 0), $(n otimes 1) otimes 1$)
      edge("|->" /*, $(x otimes a'_1) otimes a'_2 |-> a'_1 otimes (x otimes a'_2)$*/)
      node((1, 0), $1 otimes (n otimes 1)$)
      edge((0, 0), (0, 1), "|->", $q otimes id_(A')$)
      node((0, 1), $n otimes 1$)
      edge("|->", $eta$)
      node((1, 1), $1 otimes n$)
      edge((1, 0), (1, 1), "|->", $id_(A') otimes q$)
  }, spacing: 4em))
  We are thereby done. 
]

#theorem(name: <fpqc-descent-of-sheaves>)[
  (Fpqc descent of quasi-coherent sheaves) Let $f: S' -> S$ be fpqc. Then the functor: 
  $
    QCoh(S) -> DD(f), cal(F) |-> (cal(F)', eta)
  $
  associating a quasi-coherent sheaf $cal(F)$ on $S$ with its canonical descent datum along $f: S' -> S$ is an equivalence of categories. 
]
#proof[
  The previous proposition is just this theorem in the case that $S', S$ are affine. This reduction to the affine case is not very central, so I will skip some details. 

  Cover $S$ by affine opens ${S_i}$, and for each $S_i$, pick finitely many affine opens ${S'_(i,j)}$ covering $f^(-1) (S_i)$, and take $S'_i = union.sq.big_j S'_(i,j)$. Since $S'_i$ is a _finite disjoint_ union of affine schemes, it is affine. In other words, we have jointly surjective local isomorphisms ${lambda_i: S'_i -> S'}_i$ and faithfully flat morphisms ${f_i: S'_i -> S_i}$ between affine schemes. 

  Full faithfulness: 
  #proof[
    Let $cal(F), cal(G) in QCoh(S)$. We need to show that: 
    $
      Hom_(QCoh(S)) (cal(F), cal(G)) -> Hom_(DD(f)) (f^* cal(F), f^* cal(G))
    $
    is an isomorphism. Let $S_(i,j) = S_i ∩ S_j, S'_(i,j) = S'_i times_(S') S'_j$, and $f_(i,j): S'_(i,j) -> S_(i,j)$. We have a diagram with commuting parallelograms: 
    #align(center, diagram({
      node((0, 0), $Hom_(QCoh(S)) (cal(F), cal(G))$)
      edge("->")
      node((1, 0), $product_i Hom_(QCoh(S_i)) (cal(F)|_(S_i), cal(G)|_(S_i))$)
      edge("->", shift: (0, 0.1))
      edge("->", shift: (0, -0.1))
      node((2, 0), $product_(i,j) Hom_(QCoh(S_(i,j))) (cal(F)|_(S_(i,j)), cal(G)|_(S_(i,j)))$)

      node((0, 1), $Hom_(DD(f)) (f^* cal(F), f^* cal(G))$)
      edge("->")
      node((1, 1), $product_i Hom_(DD(f_i)) (f_i^* cal(F)|_(S_i), f_i^* cal(G)|_(S_i))$)
      edge("->", shift: (0, 0.1))
      edge("->", shift: (0, -0.1))
      node((2, 1), $product_(i,j) Hom_(DD(f_(i,j))) (cal(F)|_(f_(i,j)^* S_(i,j)), f_(i,j)^* cal(G)|_(S_(i,j)))$)

      for i in range(3) { edge((i, 0), (i, 1), "->") }
    }, spacing: (3em, 5em), node-defocus: 0))
    where the vertical arrows are the descent functors. 

    The two rows are both equalizers, since sheaves and morphisms can be glued along covers by local isomorphisms. From the affine case, the second vertical arrow is bijective. 

    - In the left square, the top and the right arrows are injective. Hence the left arrow is injective. 

      In other words, $QCoh(S) -> DD(f)$ is faithful for any fpqc $f$. Applying this to $f_(i,j)$, we see that the third vertical arrow is also injective. 

    - The second vertical arrow is bijective and all vertical arrows are injective, with all rows equalizers. By a simple diagram chase, the left arrow is surjective. 

      In other words, $QCoh(S) -> DD(f)$ is full for any fpqc $f$. 
    #suppress-qed
  ]

  Essential surjectivity: 
  #proof[
    Given any descent datum $(cal(G), eta) in DD(f)$, note that $(cal(G)|_(S'_i), lambda_i^* eta)$ are descent datum w.r.t. $f_i: S'_i -> S_i$. By the affine case, there are isomorphic to $(f_i^* cal(F)_i, eta_(cal(F)_i))$ for some $cal(F)_i in QCoh(S_i)$. 

    Next, from compatibilities of ${(cal(G)|_(S'_i), lambda_i^* eta)}$, we see that there are isomorphisms $(f_(i,j)^* cal(F)_i|_(S_(i,j)), eta_#[natural]) cong (f_(i,j)^* cal(F)_j|_(S_(i,j)), eta_#[natural])$ in $DD(f_(i,j))$, satisfying the cocycle condition. By full faithfulness, these descend to isomorphisms $cal(F)_i|_(S_(i,j)) cong cal(F)_j|_(S_(i,j))$ satisfying the cocycle condition. Thus, the $cal(F)_i$'s glue together to form $cal(F) in QCoh(S)$. 
    #suppress-qed
  ]
]

#theorem(name: <fpqc-descent-of-morphisms>)[
  (Fpqc descent of morphisms) Let $f: S' -> S$ be a fpqc morphism between $T$-schemes. Then the natural maps: 
  $
    Hom_T (S, X) ->^(- compose f) Hom_T (S', X) arrows.rr^(- compose p_1)_(- compose p_2) Hom_T (S'', X)
  $
  form an equalizer for every $T$-scheme $X$. 
]
#proof[
  We first prove this under the assumption that $X = Spec(A)$ is affine and lies above an affine open $Spec(R) subset T$. Then it suffices to show that: 
  $
    Hom_(AAlg(R)) (A, cal(O)_S (S)) -> Hom_(AAlg(R)) (A, cal(O)_(S') (S')) arrows.rr Hom_(AAlg(R)) (A, cal(O)_(S'') (S''))
  $
  is an equalizer. Since $Hom_(AAlg(R)) (A, -)$ preserves equalizers, it suffices to show that: 
  $
    cal(O)_S (S) ->^(f^\#) cal(O)_(S') (S') arrows.rr^(p_1^\#)_(p_2^\#) cal(O)_(S'') (S'')
  $
  is an equalizer. We may write this sequence as: 
  $
    Hom_(cal(O)_S) (cal(O)_S, cal(O)_S) -> Hom_(cal(O)_(S')) (cal(O)_(S'), cal(O)_(S')) arrows.rr Hom_(cal(O)_(S'')) (cal(O)_(S''), cal(O)_(S''))
  $
  which is an equalizer due to the full faithfulness of fpqc descent of quasi-coherent sheaves. 

  Next, we claim that the open subsets of $S, S', S''$ fit into an equalizer: 
  $
    "Open"(S) ->^(f^(-1)) "Open"(S') arrows.rr^(p_1^(-1))_(p_2^(-1)) "Open"(S'')
  $
  Indeed, 

  - Since $f$ is surjective, $V = f(f^(-1)(V))$, so $f^(-1)$ is injective on open sets; 

  - Suppose that $V' in "Open"(S')$ satisfies that $p_1^(-1) (V') = p_2^(-1) (V')$. 
    
    If $s'_(1,2) in S'$ lies above the same point $s in S$, there exists a point $s'' in S''$ s.t. $p_(1,2) (s'') = s'_(1,2)$. Thus: 
    $
      p_1 (s'') = s'_1 in V' <==> s'' in p_1^(-1) (V') <==> s'' in p_2^(-1) (V') <==> p_2 (s'') = s'_2 in V'
    $ 
    Thus, $V'$ is a disjoint union of fibers of $f: S' -> S$. That is, there exists some subset $V subset S$ s.t. $V' = f^(-1) (V)$. Since $f$ is surjective, $V = f(V')$, and since $f$ is flat hence open, $V subset S$ is open. We have thus found $V in "Open"(S)$ s.t. $f^(-1)(V) = V'$. 

  We are now ready to deal with the general case. Pick an affine open cover ${X_i}$ of $X$ s.t. each $X_i$ lies above an affine open of $T$. Now: 

  - Given $T$-morphisms $a,b: S -> X$ s.t. $a compose f = b compose f$, since $f$ is surjective, $a$ and $b$ agrees on the underlying topological spaces. Let $S_i = a^(-1) (X_i) = b^(-1) (X_i)$, and put $a_i, b_i: S_i -> X_i$, with $f_i: S'_i -> S_i$ being the base change of $f$, still fpqc. Now $a_i compose f_i = b_i compose f_i$, and by the affine case, $a_i = b_i$. Thus $a = b$. 

  - Let $phi: S' -> X$ be a $T$-morphism s.t. $phi compose p_1 = phi compose p_2$. Put $V'_i = phi^(-1) (X_i)$. Then we have: 
    $
      p_1^(-1) (V'_i) = p_1^(-1) (phi^(-1) (X_i)) = p_2^(-1) (phi^(-1) (X_i)) = p_2^(-1) (V'_i)
    $
    Thus by our previous discussions on lifting open sets, there exists an open $V_i subset S$ s.t. $V'_i = f^(-1) (V_i)$. Since ${V'_i}$ is an open cover of $S'$, applying $f$ (which is surjective), ${V_i}$ is an open cover of $S$. Put $f_i: V'_i -> V_i$, being still fpqc. 
    
    Put $p_(1,i), p_(2,i): p_1^(-1) (V'_i) = p_2^(-1) (V'_i) = V'_i times_(V_i) V'_i -> V'_i$, and so by the given condition, $phi|_(V'_i) compose p_(1,i) = phi|_(V'_i) compose p_(2,i)$. $phi|_(V'_i)$ is a map $V'_i -> X_i$, so by the affine case, there exists a $T$-morphism $psi_i: V_i -> X_i$ s.t. $phi|_(V'_i) = psi_i compose f_i$. 

    Restrict $f$ to $f_(i,j): V'_i inter V'_j -> V_i inter V_j$, which is a base change of $f$ and still fpqc. Now on the intersections, 
    $
      psi_i|_(V_(i,j)) compose f_(i,j) = phi|_(V'_i inter V'_j) = psi_j|_(V_(i,j)) compose f_(i,j)
    $
    By the injectivity part just proved, $psi_i|_(V_(i,j)) = psi_j|_(V_(i,j))$. Thus the ${psi_i}$'s glue together to a global $T$-morphism $psi: S -> X$ s.t. $phi = psi compose f$. 

  We are thereby done. 
]

Next, we list some useful properties that can be descended along fpqc base change. 

#theorem(name: <fpqc-descent-of-properties>)[
  Consider a Cartesian diagram: 
  // https://q.uiver.app/#r=typst&q=WzAsNCxbMCwwLCJYJyJdLFsxLDAsIlknIl0sWzAsMSwiWCJdLFsxLDEsIlkiXSxbMiwzLCJmIiwyXSxbMCwxLCJmJyJdLFsxLDMsImciXSxbMCwyLCJnJyIsMl1d
  #align(center, diagram({
    node((0, 0), [$X'$])
    node((1, 0), [$Y'$])
    node((0, 1), [$X$])
    node((1, 1), [$Y$])
    node((0.3, 0.3), $cart$)
    edge((0, 1), (1, 1), [$f$], label-side: right, "->")
    edge((0, 0), (1, 0), [$f'$], label-side: left, "->")
    edge((1, 0), (1, 1), [$g$], label-side: left, "->")
    edge((0, 0), (0, 1), [$g'$], label-side: right, "->")
  }))
  in which $g$ is fpqc. Then any of the following properties holds for $f$ if and only if it holds for $f'$. 
  + affine;
  + finite; 
  + flat; 
  + unramified; 
  + etale. 
]
#proof[
  All of these properties are preserved under base change, so we only need to show that the respective properties descend from $f'$ to $f$. 

  Note that all of these properties are Zariski local on base. Thus, we may base change to an affine open of $Y$ and assume that $Y = Spec(A)$ is affine. Next, since $g$ is fpqc, $Y'$ is quasi-compact. Cover $Y'$ by finitely many affine opens ${Y'_i}$ and take $Y'' = union.sq.big_i Y'_i$, and form the base change: 
  // https://q.uiver.app/#r=typst&q=WzAsNixbMCwxLCJYJyJdLFsxLDEsIlknIl0sWzAsMiwiWCJdLFsxLDIsIlkiXSxbMSwwLCJZJyciXSxbMCwwLCJYJyciXSxbMiwzLCJmIiwyXSxbMCwxLCJmJyJdLFsxLDMsImciXSxbMCwyLCJnJyIsMl0sWzQsMV0sWzUsMF0sWzUsNCwiZicnIl1d
  #align(center, diagram({
    node((0, 0), [$X'$])
    node((1, 0), [$Y'$])
    node((0, 1), [$X$])
    node((1, 1), [$Y$])
    node((1, -1), [$Y''$])
    node((0, -1), [$X''$])
    edge((0, 1), (1, 1), [$f$], label-side: right, "->")
    edge((0, 0), (1, 0), [$f'$], label-side: left, "->")
    edge((1, 0), (1, 1), [$g$], label-side: left, "->")
    edge((0, 0), (0, 1), [$g'$], label-side: right, "->")
    edge((1, -1), (1, 0), "->")
    edge((0, -1), (0, 0), "->")
    edge((0, -1), (1, -1), [$f''$], label-side: left, "->")
  }))
  Now the respective properties hold for $f''$, and $Y'' -> Y$ is affine fpqc. Thus we may replace $g$ by $Y'' -> Y$, and assume that $Y' = Spec(A')$ for a faithfully flat $A$-algebra $A'$. 

  (1) We first show that $X$ is qcqs. Indeed, 

  - $g$ is surjective, and so is $g'$. Since $X'$ is affine and hence quasi-compact, $X = g'(X')$ is quasi-compact. 

  - Let $U, V subset X$ be any two affine opens. Then $g'^(-1) (U) = U times_Y Y'$ is the fiber product of two affine schemes over an affine scheme, and is affine. Similarly $g'^(-1) (V)$ is affine. Thus since $X'$ is affine, $g'^(-1) (U inter V) = g'^(-1) (U) inter g'^(-1) (V)$ is affine. Thus $U inter V = g'(g'^(-1) (U inter V))$ is quasi-compact. Hence $X$ is quasi-separated. 

  Now that everything in this diagram is qcqs, flat base change for quasi-coherent sheaves may be invoked. For any quasi-coherent sheaf of ideals $cal(I) subset cal(O)_X$, 
  $
    g^* R^1 f_* cal(I) = R^1 f'_* g'^* cal(I) = 0
  $
  since $f'$ is affine. Put $R^1 f_* cal(I) = tilde(M)$, and so $M otimes_A A' = 0$. Since $A'$ is faithfully flat over $A$, by @amitsur-complex-exact $M -> M otimes_A A'$ is injective and so $M = 0$. Thus $R^1 f_* cal(I) = 0$. By Serre's criterion for affineness (#cite-stacks("0F83")[Lemma 30.3.4]), $f$ is affine. 

  (2) By (1) we know that $f$ is affine, so we may assume $X = Spec(B)$ and $Y = Spec(A)$. Now $B'$ is finite over $A'$ and $A'$ is faithfully flat over $A$, so $B$ is finite over $A$ (say by #cite-stacks("03C4")[Lemma 10.83.2]). 

  (3)(4)(5) are all Zariski local on source, so we may assume that $X = Spec(B)$ is affine and $X' = Spec(B')$. 

  (3) Since $B'$ is flat over $A'$, $B$ is flat over $A$ by @cite-matsumura-ca[(4.E)(1)]. Thus $f$ is flat.

  (4) Note that: 
  $
    0 = Omega_(B'\/A') = Omega_(B\/A) otimes_B B'
  $
  Since $B'$ is faithfully flat over $B$, this proves $Omega_(B\/A) = 0$. Thus $f$ is unramified. 

  (5) is just (3) and (4) combined. 
]

Finally, as a corollary of fpqc descent for quasi-coherent sheaves, we prove fpqc descent for relatively affine schemes. 

#theorem(name: <fpqc-descent-of-relatively-affine-schemes>)[
  Let $f: X' -> X$ be an fpqc map. Suppose that $Y' -> X'$ is an affine map, with descent datum: 
  $
    eta: Y' times_X X' -> X' times_X Y'
  $
  an isomorphism of $X'' = X' times_X X'$-schemes, s.t. the following diagram commutes: 
  // https://q.uiver.app/#r=typst&q=WzAsMyxbMCwxLCJZJyB0aW1lc19YIFgnIHRpbWVzX1ggWCciXSxbMSwwLCJYJyB0aW1lc19YIFknIHRpbWVzX1ggWCciXSxbMiwxLCJYJyB0aW1lc19YIFgnIHRpbWVzX1ggWSciXSxbMCwyLCJwXygxMyleKiBldGEiLDJdLFswLDEsInBfKDEyKV4qIGV0YSJdLFsxLDIsInBfKDIzKV4qIGV0YSJdXQ==
  #align(center, diagram({
    node((0, 1), [$Y' times_X X' times_X X'$])
    node((1, 0), [$X' times_X Y' times_X X'$])
    node((2, 1), [$X' times_X X' times_X Y'$])
    edge((0, 1), (2, 1), [$p_(13)^* eta$], label-side: right, "->")
    edge((0, 1), (1, 0), [$p_(12)^* eta$], label-side: left, "->")
    edge((1, 0), (2, 1), [$p_(23)^* eta$], label-side: left, "->")
  }))
  Then there exists an affine map $Y -> X$ s.t. $Y' cong Y times_X X'$ as $X'$-schemes, with $eta$ identified with the canonical map $(Y times_X X') times_X X' -> X' times_X (Y times_X X')$ moving $Y$ to the other component. 
]
#proof[
  Write $g': Y' -> X'$ and $cal(A)' = g'_* cal(O)_(Y')$, so that $Y' = SPec(cal(A)')$. The isomorphism $eta$ induces a descent datum on the quasi-coherent $cal(O)_(X')$-algebra $cal(A)'$. By @fpqc-descent-of-sheaves, its underlying quasi-coherent module descends to some $cal(A) in QCoh(X)$.

  The unit and multiplication of $cal(A)'$ are morphisms of descent data. By full faithfulness, they descend uniquely to maps
  $
    u: cal(O)_X -> cal(A) \
    m: cal(A) otimes_(cal(O)_X) cal(A) -> cal(A)
  $
  The algebra axioms hold because they hold after pullback to $X'$ and fpqc descent is faithful. Thus $cal(A)$ is a quasi-coherent $cal(O)_X$-algebra.

  Set $Y = SPec(cal(A))$. Then $Y -> X$ is affine. Since $SPec$ commutes with base change, so
  $
    Y times_X X' cong SPec(f^* cal(A)) cong SPec(cal(A)') 
  $
  Since the canonical descent datum on $cal(A)$ is the given descent datum on $cal(A)'$, the canonical descent datum on $Y$ is the given descent datum $eta$ on $Y'$. 
]
