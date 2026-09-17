#import "void-import.typ": *
== Projection and Kunneth formula

In this section, we aim to prove the projection formula and the Kunneth formula. These two formulas are the critical mechanisms that allow us to describe the interaction between $R f_!$ and tensor products. 

As an application, we will compute the cohomology of $PP^n_k$ and the cohomology with proper support of $AA^n_k$ for a separably closed field $k$. 

The first thing to do is to construct the projection map. Suppose that $f: X -> Y$ is a separated morphism of finite type between noetherian schemes, and $cal(K) in D_#[tor] (X_et, Lambda), cal(L) in D_#[tor] (Y_et, Lambda)$. We aim to construct a projection map: 
$
  R f_! cal(K) Lotimes_Lambda cal(L) -> R f_! (cal(K) Lotimes_Lambda f^(-1) cal(L))
$
that is natural in $cal(K)$ and $cal(L)$, compatible with composition of $f$, compatible with tensor products in $cal(L)$, and compatible with base change. We will then prove that it is an isomorphism. 
To establish these compatibilities, the best way is to construct the projection map as a Beck-Chevalley base change. But before we construct the projection map for $R f_!$, we have to construct the projection map for its constituents, namely $R f_*$ and $j_!$. 

#construction[
  (Projection for $R f_*$) For a general scheme morphism $f: X -> Y$, we may construct a projection morphism for $R f_*$ of the form:
  $
    R f_* cal(K) Lotimes_Lambda cal(L) -> R f_* (cal(K) Lotimes_Lambda f^(-1) cal(L))
  $  
  By inspecting the functors in question, we see that it can be constructed as the Beck-Chevalley base change of the following diagram: 
  // https://q.uiver.app/#r=typst&q=WzAsNCxbMCwwLCJEKFhfZXQsIExhbWJkYSkiXSxbMCwyLCJEKFhfZXQsIExhbWJkYSkiXSxbMiwwLCJEKFlfZXQsIExhbWJkYSkiXSxbMiwyLCJEKFlfZXQsIExhbWJkYSkiXSxbMCwxLCJSSEhvbV9MYW1iZGEgKGNhbChMKSwgLSkiLDJdLFsyLDMsIlJISG9tX0xhbWJkYSAoZl4oLTEpIGNhbChMKSwgLSkiLDJdLFsxLDMsIlIgZl8qIiwyXSxbMCwyLCJSIGZfKiJdXQ==
  #align(center, diagram({
    node((0, 0), [$D(X_et, Lambda)$])
    node((0, 2), [$D(X_et, Lambda)$])
    node((2, 0), [$D(Y_et, Lambda)$])
    node((2, 2), [$D(Y_et, Lambda)$])
    edge((0, 0), (0, 2), [$RHHom_Lambda (cal(L), -)$], label-side: right, "->")
    edge((2, 0), (2, 2), [$RHHom_Lambda (f^(-1) cal(L), -)$], label-side: left, "->")
    edge((0, 2), (2, 2), [$R f_*$], label-side: right, "->")
    edge((0, 0), (2, 0), [$R f_*$], label-side: left, "->")
    edge(..tune-2-mor-coords((0, 2), (2, 0), l: 0.8), "=>")
  }, spacing: 2.5em))
  where the natural transformation on the diagonal is the isomorphism: 
  $
    RHHom_Lambda (cal(L), R f_* (-)) -> R f_* RHHom_Lambda (f^(-1) cal(L), -)
  $
  following from adjunction, as in @derived-functoriality-etale (3a). 

  - Note that $RHHom_Lambda (cal(L), R f_* (-)) -> R f_* RHHom_Lambda (f^(-1) cal(L), -)$ is a morphism on the composition of two right adjoints. Its induced morphism on left adjoints is just the monoidal isomorphism: 
    $
      f^(-1) (-) Lotimes_Lambda f^(-1) cal(L) -> f^(-1) (- Lotimes_Lambda cal(L))
    $
    By @bcbc-all-rights, the projection map is thus the following map: Take the morphism $f^(-1) (R f_* cal(K) Lotimes_Lambda cal(L)) cong f^(-1) R f_* cal(K) Lotimes_Lambda f^(-1) cal(L) -> cal(K) Lotimes_Lambda f^(-1) cal(L)$, and apply adjunction to get a morphism $R f_* cal(K) Lotimes_Lambda cal(L) -> R f_* (cal(K) Lotimes_Lambda f^(-1) cal(L))$. 

  We now verify the compatibilities for this map. 

  - The projection map is compatible with composition of $f$. Suppose we have another scheme morphism $g: Y -> Z$. Then the consecutive projections: 
    $
      R g_* R f_* cal(K) Lotimes_Lambda cal(L) -> R g_* (R f_* cal(K) Lotimes_Lambda g^(-1) cal(L)) -> R g_* R f_* (cal(K) Lotimes_Lambda f^(-1) g^(-1) cal(L))
    $
    is just the projection for $g compose f$. 

    This compatibility follows from @bcbc-horizontal-concat, once we verify that the composition of adjunction isomorphisms: 
    $
      RHHom_Lambda (cal(L), R g_* R f_* (-)) ->^tilde R g_* RHHom_Lambda (g^(-1) cal(L), R f_* (-)) ->^tilde R g_* R f_* RHHom_Lambda (f^(-1) g^(-1) cal(L), -)
    $
    is just the adjunction isomorphism for $f^(-1) g^(-1) tack.l R g_* R f_*$. To verify this, we may reduce to checking on sections by applying $R Gamma(U, -)$. This allows us to replace $RHHom_Lambda$ by $RHom_Lambda$. Now $h^q (RHHom_Lambda (-, -)) = Hom_Lambda (-, -[q])$ so we may replace $RHom_Lambda$ further by $Hom_Lambda$ the categorical hom. Then this compatibility is a standard categorical fact for composition of adjoints. 

  - The projection map is compatible with tensor products in $cal(L)$. That is, consecutive projections: #h(1fr)
    $
      R f_* cal(K) Lotimes_Lambda cal(L)_1 Lotimes_Lambda cal(L)_2 -> R f_* (cal(K) Lotimes_Lambda f^(-1) cal(L)_1) Lotimes_Lambda cal(L)_2 -> R f_* (cal(K) Lotimes_Lambda f^(-1) cal(L)_1 Lotimes_Lambda f^(-1) cal(L)_2)
    $
    is just the projection for $cal(L)_1 Lotimes_Lambda cal(L)_2$, where we identify $f^(-1) (cal(L)_1 Lotimes_Lambda cal(L)_2) = f^(-1) cal(L)_1 Lotimes_Lambda f^(-1) cal(L)_2$. 

    This compatibility follows from @bcbc-vertical-concat, once we verify that the following diagram commutes: 
    #align(center, diagram({
      node((0, 0), $RHHom_Lambda (cal(L)_1, RHHom_Lambda (cal(L)_2, R f_* (-)))$)
      node((0, 1), $RHHom_Lambda (cal(L)_1, R f_* RHHom_Lambda (f^(-1) cal(L)_2, -))$)
      node((0, 2), $R f_* RHHom_Lambda (f^(-1) cal(L)_1, RHHom_Lambda (f^(-1) cal(L)_2, -))$)
      node((2, 0), $RHHom_Lambda (cal(L)_1 Lotimes_Lambda cal(L)_2, R f_* (-))$)
      node((2, 2), $R f_* RHHom_Lambda (f^(-1) cal(L)_1 Lotimes_Lambda f^(-1) cal(L)_2, -)$)
      edge((0, 0), (0, 1), "->")
      edge((0, 1), (0, 2), "->")
      edge((2, 0), (2, 2), "->")
      edge((0, 0), (2, 0), "->")
      edge((0, 2), (2, 2), "->")
    }, spacing: (2em, 3em)))
    By applying $R Gamma$ to reduce to $RHom_Lambda$, then to categorical hom, we only need to verify the commutativity of the following diagram: 
    #align(center, diagram({
      node((0, 0), $Hom_Lambda (cal(L)_1, RHHom_Lambda (cal(L)_2, R f_* (-)))$)
      node((0, 1), $Hom_Lambda (cal(L)_1, R f_* RHHom_Lambda (f^(-1) cal(L)_2, -))$)
      node((0, 2), $Hom_Lambda (f^(-1) cal(L)_1, RHHom_Lambda (f^(-1) cal(L)_2, -))$)
      node((2, 0), $Hom_Lambda (cal(L)_1 Lotimes_Lambda cal(L)_2, R f_* (-))$)
      node((2, 2), $Hom_Lambda (f^(-1) cal(L)_1 Lotimes_Lambda f^(-1) cal(L)_2, -)$)
      edge((0, 0), (0, 1), "->")
      edge((0, 1), (0, 2), "->")
      edge((2, 0), (2, 2), "->")
      edge((0, 0), (2, 0), "->")
      edge((0, 2), (2, 2), "->")
    }, spacing: (2em, 3em)))
    However, the commutativity of this diagram is exactly the construction of the monoidal isomorphism $f^(-1) (cal(L)_1 Lotimes_Lambda cal(L)_2) cong f^(-1) cal(L)_1 Lotimes_Lambda f^(-1) cal(L)_2$. 

  - The projection map is compatible with arbitrary base change. That is, given a commutative diagram: 
    // https://q.uiver.app/#r=typst&q=WzAsNCxbMCwwLCJYJyJdLFswLDEsIlgiXSxbMSwwLCJZJyJdLFsxLDEsIlkiXSxbMSwzLCJmIiwyXSxbMCwyLCJmJyJdLFsyLDMsImciXSxbMCwxLCJnJyIsMl1d
    #align(center, diagram({
      node((0, 0), [$X'$])
      node((0, 1), [$X$])
      node((1, 0), [$Y'$])
      node((1, 1), [$Y$])
      edge((0, 1), (1, 1), [$f$], label-side: right, "->")
      edge((0, 0), (1, 0), [$f'$], label-side: left, "->")
      edge((1, 0), (1, 1), [$g$], label-side: left, "->")
      edge((0, 0), (0, 1), [$g'$], label-side: right, "->")
    }))
    of scheme morphisms with $p = g compose f' = f compose g': X' -> Y$, the composition: 
    $
      g^(-1) (R f_* (-) Lotimes_Lambda cal(L)) -->^M g^(-1) R f_* (-) Lotimes_Lambda g^(-1) cal(L) -->^BC R f'_* g'^(-1) (-) Lotimes_Lambda g^(-1) cal(L) -->^P R f'_* (g'^(-1) (-) Lotimes_Lambda p^(-1) cal(L))
    $
    is the same as the composition: 
    $
      g^(-1) (R f_* (-) Lotimes_Lambda cal(L)) -->^P g^(-1) R f_* (- Lotimes_Lambda f^(-1) cal(L)) -->^BC R f'_* g'^(-1) (- Lotimes_Lambda f^(-1) cal(L)) -->^M R f'_* (g'^(-1) (-) Lotimes_Lambda p^(-1) cal(L))
    $
    where $M$ denotes the monoidal isomorphism for pullback, $BC$ denotes a base change map, and $P$ denotes a projection map. 

    Now: 

    - The monoidal isomorphism $g^(-1) (- Lotimes_Lambda cal(L)) cong g^(-1) (-) Lotimes_Lambda g^(-1) cal(L)$ comes from adjunction of the isomorphism: 
      $
        RHHom_Lambda (cal(L), R g_* (-)) cong R g_* RHHom_Lambda (g^(-1) cal(L), -)
      $
      and similarly for the other monoidal isomorphism. 

    - The base change map $g^(-1) R f_* -> R f'_* g'^(-1)$ is the Beck-Chevalley base change for $R f_* R g'_* = R p_* = R g_* R f'_*$. 

    - The projection map $R f_* (-) Lotimes_Lambda cal(L) -> R f_* (- Lotimes_Lambda f^(-1) cal(L))$ is the Beck-Chevalley base change of the adjunction isomorphism $RHHom_Lambda (cal(L), R f_* (-)) -> R f_* RHHom_Lambda (f^(-1) cal(L), -)$. 

    The desired compatibility thus follows from @bcbc-vertical-concat, @bcbc-naturality, and the equality of the red and blue path in the following cube from the magenta functor to the green functor: 
    // https://q.uiver.app/#r=typst&q=WzAsOCxbMCwxLCJEKFknKSJdLFsyLDIsIkQoWScpIl0sWzEsMCwiRChZKSJdLFszLDEsIkQoWSkiXSxbMCw0LCJEKFgnKSJdLFsyLDUsIkQoWCcpIl0sWzEsMywiRChYKSJdLFszLDQsIkQoWCkiXSxbMCwyLCJSIGdfKiIsMV0sWzEsMywiUiBnXyoiLDFdLFs0LDYsIlIgZydfKiIsMV0sWzUsNywiUiBnJ18qIiwxXSxbMiwzLCJSSEhvbV9MYW1iZGEgKGNhbChMKSwgLSkiLDFdLFswLDEsIlJISG9tX0xhbWJkYSAoZ14oLTEpIGNhbChMKSwgLSkiLDFdLFs2LDcsIlJISG9tX0xhbWJkYSAoZl4oLTEpIGNhbChMKSwgLSkiLDFdLFs0LDUsIlJISG9tX0xhbWJkYSAocF4oLTEpIGNhbChMKSwgLSkiLDFdLFs3LDMsIlIgZl8qIiwxXSxbNSwxLCJSIGZfKiIsMSx7ImxhYmVsX3Bvc2l0aW9uIjo4MH1dLFs2LDIsIlIgZidfKiIsMSx7ImxhYmVsX3Bvc2l0aW9uIjoyMH1dLFs0LDAsIlIgZidfKiIsMV1d
    #context align(center, diagram({
      edge(..tune-2-mor-coords((2, 2), (1, 0), l: 0.6), "=>", text(fill: red)[$1$], stroke: red, label-side: center)
      edge(..tune-2-mor-coords((0, 1), (1, 3)), "=>", text(fill: red)[$2$], stroke: red, label-side: center)
      edge(..tune-2-mor-coords((1, 0), (3, 4)), "=>", text(fill: red)[$3$], stroke: red, label-side: center, label-pos: 0.75, bend: 30deg)

      edge(..tune-2-mor-coords((0, 1), (2, 5)), "=>", text(fill: blue)[$1$], stroke: blue, label-side: center, label-pos: 0.25, bend: -30deg)
      edge(..tune-2-mor-coords((2, 2), (3, 4)), "=>", text(fill: blue)[$2$], stroke: blue, label-side: center)
      edge(..tune-2-mor-coords((2, 5), (1, 3), l: 0.6), "=>", text(fill: blue)[$3$], stroke: blue, label-side: center)

      node((0, 1), [$D(Y')$])
      node((2, 2), [$D(Y')$])
      node((1, 0), [$D(Y)$])
      node((3, 1), [$D(Y)$])
      node((0, 4), [$D(X')$])
      node((2, 5), [$D(X')$])
      node((1, 3), [$D(X)$])
      node((3, 4), [$D(X)$])
      edge((3, 4), (3, 1), text(fill: green)[$R f_*$], label-side: center, "->", stroke: green)
      edge((2, 5), (2, 2), [$R f_*$], label-side: center, label-pos: 0.8, "->")
      edge((1, 3), (1, 0), [$R f'_*$], label-side: center, label-pos: 0.2, "->")
      edge((0, 4), (0, 1), text(fill: fuchsia)[$R f'_*$], label-side: center, "->", stroke: fuchsia)
      edge((0, 1), (1, 0), [$R g_*$], label-side: center, "->")
      edge((2, 2), (3, 1), text(fill: fuchsia)[$R g_*$], label-side: center, "->", stroke: fuchsia)
      edge((0, 4), (1, 3), text(fill: green)[$R g'_*$], label-side: center, "->", stroke: green)
      edge((2, 5), (3, 4), [$R g'_*$], label-side: center, "->")
      edge((1, 0), (3, 1), [$RHHom_Lambda (cal(L), -)$], label-side: center, "->")
      edge((0, 1), (2, 2), text(fill: fuchsia)[$RHHom_Lambda (g^(-1) cal(L), -)$], label-side: center, "->", label-pos: 0.7, stroke: fuchsia)
      edge((1, 3), (3, 4), text(fill: green)[$RHHom_Lambda (f^(-1) cal(L), -)$], label-side: center, "->", label-pos: 0.3, stroke: green)
      edge((0, 4), (2, 5), [$RHHom_Lambda (p^(-1) cal(L), -)$], label-side: center, "->")
    }, crossing-fill: thm-box-curr-color(), label-size: 0.8em, spacing: (2.5em, 1.6em)))
    This equality is just the compatibility for composed adjunctions. (Here, we abbreviated $D_#[tor] (X_et, Lambda)$ by $D(X)$.)

  We have thus constructed a projection map for $R f_*$ satisfying our needs. 
]

#construction[
  (Projection for $f_!$) For an etale morphism $f: X -> Y$, we intend to construct a projection map: 
  $
    f_! cal(K) Lotimes_Lambda cal(L) -> f_! (cal(K) Lotimes_Lambda f^(-1) cal(L)) 
  $
  compatible with base change. This projection isomorphism is defined in @derived-functoriality-etale (4b), as the adjoint of the isomorphism: 
  $
    RHHom_Lambda (f^(-1) (-), f^(-1) cal(L)) -->^tilde f^(-1) RHHom_Lambda (-, cal(L))
  $

  - The projection is compatible with composition in $f$. Indeed, given another etale morphism $g: Y -> Z$, to show that the composition of projections: #h(1fr)
    $
      g_! f_! cal(K) Lotimes_Lambda cal(L) -> g_! (f_! cal(K) Lotimes_Lambda g^(-1) cal(L)) -> g_! f_! (cal(L) Lotimes_Lambda f^(-1) g^(-1) cal(L))
    $
    is just projection along $g compose f$, by adjunction it suffices to show that the composition: 
    $
      RHHom_Lambda (g^(-1) f^(-1) (-), g^(-1) f^(-1) cal(L)) -> g^(-1) RHHom_Lambda (f^(-1) (-), f^(-1) cal(L)) -> g^(-1) f^(-1) RHHom_Lambda (-, cal(L))
    $
    is just the same isomorphism for $g compose f$. But this is automatic. 

  - The projection is compatible with arbitrary base change. Suppose that we have a commutative diagram: 
    // https://q.uiver.app/#r=typst&q=WzAsNCxbMCwwLCJYJyJdLFswLDEsIlgiXSxbMSwwLCJZJyJdLFsxLDEsIlkiXSxbMSwzLCJmIiwyXSxbMCwyLCJmJyJdLFsyLDMsImciXSxbMCwxLCJnJyIsMl1d
    #align(center, diagram({
      node((0, 0), [$X'$])
      node((0, 1), [$X$])
      node((1, 0), [$Y'$])
      node((1, 1), [$Y$])
      edge((0, 1), (1, 1), [$f$], label-side: right, "->")
      edge((0, 0), (1, 0), [$f'$], label-side: left, "->")
      edge((1, 0), (1, 1), [$g$], label-side: left, "->")
      edge((0, 0), (0, 1), [$g'$], label-side: right, "->")
      node((0.3, 0.3), $cart$)
    }))
    with $p = g compose f' = f compose g': X' -> Y$, then the composition:
    $
      g^(-1) (f_! (-) Lotimes_Lambda cal(L)) -->^M g^(-1) f_! (-) Lotimes_Lambda g^(-1) cal(L) -->^(BC_!) f'_! g'^(-1) (-) Lotimes_Lambda g^(-1) cal(L) -->^P f'_! (g'^(-1) (-) Lotimes_Lambda p^(-1) cal(L))
    $
    is the same as the composition: 
    $
      g^(-1) (f_! (-) Lotimes_Lambda cal(L)) -->^P g^(-1) f_! (- Lotimes_Lambda f^(-1) cal(L)) -->^(BC_!) f'_! g'^(-1) (- Lotimes_Lambda f^(-1) cal(L)) -->^M f'_! (g'^(-1) (-) Lotimes_Lambda p^(-1) cal(L))
    $
    where $P$ is a projection map, $M$ is a monoidal isomorphism, and $BC_!$ is the isomorphism as in @etale-lower-shriek-first-props (4). 

    Indeed, by passing to right adjoints, it suffices to show that the following diagram commutes: 

    // https://q.uiver.app/#r=typst&q=WzAsOCxbMCwwLCJSIGcnXyogUkhIb21fTGFtYmRhIChwXigtMSkgY2FsKEwpLCAtKSJdLFsyLDAsIlIgZydfKiBSSEhvbV9MYW1iZGEgKHBeKC0xKSBjYWwoTCksIC0pIl0sWzAsMSwiUiBnJ18qIGYnXigtMSkgUkhIb21fTGFtYmRhIChnXigtMSkgY2FsKEwpLCAtKSJdLFswLDIsImZeKC0xKSBSIGdfKiBSSEhvbV9MYW1iZGEgKGdeKC0xKSBjYWwoTCksIC0pIl0sWzAsMywiZl4oLTEpIFJISG9tX0xhbWJkYSAoY2FsKEwpLCBSIGdfKiAoLSkpIl0sWzIsMSwiUkhIb21fTGFtYmRhIChmXigtMSkgY2FsKEwpLCBSIGcnXyogZideKC0xKSAoLSkpIl0sWzIsMiwiUkhIb21fTGFtYmRhIChmXigtMSkgY2FsKEwpLCBmXigtMSkgUiBnXyogKC0pKSJdLFsyLDMsImZeKC0xKSBSSEhvbV9MYW1iZGEgKGNhbChMKSwgUiBnXyogKC0pKSJdLFswLDEsIiIsMCx7InN0eWxlIjp7ImJvZHkiOnsibmFtZSI6ImRvdWJsZSBiYXJyZWQifX19XSxbMCwyXSxbMiwzXSxbMyw0XSxbMSw1XSxbNSw2XSxbNiw3XSxbNCw3LCIiLDIseyJzdHlsZSI6eyJib2R5Ijp7Im5hbWUiOiJkb3VibGUgYmFycmVkIn19fV1d
    #context align(center, diagram({
      node((0, 0), [$R g'_* RHHom_Lambda (p^(-1) cal(L), -)$])
      node((2, 0), [$R g'_* RHHom_Lambda (p^(-1) cal(L), -)$])
      node((0, 1), [$R g'_* f'^(-1) RHHom_Lambda (g^(-1) cal(L), -)$])
      node((0, 2), [$f^(-1) R g_* RHHom_Lambda (g^(-1) cal(L), -)$])
      node((0, 3), [$f^(-1) RHHom_Lambda (cal(L), R g_* (-))$])
      node((2, 1), [$RHHom_Lambda (f^(-1) cal(L), R g'_* f'^(-1) (-))$])
      node((2, 2), [$RHHom_Lambda (f^(-1) cal(L), f^(-1) R g_* (-))$])
      node((2, 3), [$f^(-1) RHHom_Lambda (cal(L), R g_* (-))$])
      edge((0, 0), (2, 0), "=")
      edge((0, 0), (0, 1), "->")
      edge((0, 1), (0, 2), "->")
      edge((0, 2), (0, 3), "->")
      edge((2, 0), (2, 1), "->")
      edge((2, 1), (2, 2), "->")
      edge((2, 2), (2, 3), "->")
      edge((0, 3), (2, 3), "=")
    }, crossing-fill: thm-box-curr-color()))
    It suffices to prove this commutation after applying $R Gamma(U, -)$ for $U in Et_X$. Furthermore, we may assume $U = X$. This is because upon applying $R Gamma(U, -)$ for general $U$ to the diagram above, we obtain what we would have obtained by applying global sections to the diagram above if we started with $U -> Y$ instead of $X -> Y$. By replacing $cal(L)$ with a K-flat complex and the complex in $(-)$ with a K-injective complex, we may drop all $R$'s from the derived functors by @hhom-from-kflat-to-kinj-is-kinj. 
    
    For $U = X$, i.e. upon taking global sections, morphisms like $f^(-1) RHHom_Lambda (-, -) cong RHHom_Lambda (f^(-1) (-), f^(-1) (-))$ turns into the identity. Then the right path becomes: 
    $
      Hom_Lambda (p^(-1) cal(L), f'^(-1) (-)) -> Hom_Lambda (f^(-1) cal(L), g'_* f'^(-1) (-)) -> Hom_Lambda (f^(-1) cal(L), f^(-1) g_* (-))
    $
    while the left path becomes: 
    $
      Hom_Lambda (p^(-1) cal(L), f'^(-1) (-)) = Gamma(X', HHom_Lambda (g^(-1) cal(L), -)) = Gamma(X, HHom_Lambda (cal(L), g_* (-))) = Hom_Lambda (f^(-1) cal(L), f^(-1) g_* (-))
    $
    It is direct to check that these two paths are equal. 

  - The projection is compatible with tensors in $cal(L)$. To show that the composition of projections: 
    $
      f_! cal(K) Lotimes_Lambda cal(L)_1 Lotimes_Lambda cal(L)_2 -> f_! (cal(K) Lotimes_Lambda f^(-1) cal(L)_1) Lotimes_Lambda cal(L)_2 -> f_! (cal(K) Lotimes_Lambda f^(-1) cal(L)_1 Lotimes_Lambda f^(-1) cal(L)_2) ->^M f_! (cal(K) Lotimes_Lambda f^(-1) (cal(L)_1 Lotimes_Lambda cal(L)_2))
    $
    is just the projection for $cal(L)_1 Lotimes_Lambda cal(L)_2$ (where $M$ is the monoidal isomorphism). 
    
    We could have checked the hard way by comparing the adjoints of both sides as functors in $cal(K)$. Instead, we will cheat by checking on stalks only, since the projection map is compatible with arbitrary base change. We may thus assume that $f$ is $union.sq.big_(i in I) Spec(Omega) -> Spec(Omega)$ for a separably closed field $Omega$, and then everything is just a complex of $Lambda$-modules. In this case compatibility can be checked directly. 
    /*, by unfolding the definition of the monoidal isomorphism, it suffices to show that the composition: 
    $
      RHHom_Lambda (f^(-1) (cal(L)_1 Lotimes_Lambda cal(L)_2), f^(-1) (-)) -> f^(-1) RHHom_Lambda (cal(L)_1 Lotimes_Lambda cal(L)_2, R f_* f^(-1) (-)) -> 
    $*/
    #remark[
      As a corollary to this compatibility, by taking adjoints, we see that the monoidal isomorphism $f^(-1) (cal(L)_1 Lotimes_Lambda cal(L)_2) cong f^(-1) cal(L)_1 Lotimes_Lambda f^(-1) cal(L)_2$ fits in the commutative diagram: 
      // https://q.uiver.app/#r=typst&q=WzAsNixbMCwwLCJSSEhvbV9MYW1iZGEgKGZeKC0xKSBjYWwoTClfMSBMb3RpbWVzX0xhbWJkYSBmXigtMSkgY2FsKEwpXzIsIGZeKC0xKSAoLSkpIl0sWzEsMCwiUkhIb21fTGFtYmRhIChmXigtMSkgY2FsKEwpXzEsIFJISG9tX0xhbWJkYShmXigtMSkgY2FsKEwpXzIsIGZeKC0xKSAoLSkpKSJdLFsxLDEsIlJISG9tX0xhbWJkYSAoZl4oLTEpIGNhbChMKV8xLCBmXigtMSkgUkhIb21fTGFtYmRhKGNhbChMKV8yLCAtKSkiXSxbMSwyLCJmXigtMSkgUkhIb21fTGFtYmRhIChjYWwoTClfMSwgUkhIb21fTGFtYmRhKGNhbChMKV8yLCAtKSkiXSxbMCwyLCJmXigtMSkgUkhIb21fTGFtYmRhIChjYWwoTClfMSBMb3RpbWVzX0xhbWJkYSBjYWwoTClfMiwgLSkiXSxbMCwxLCJSSEhvbV9MYW1iZGEgKGZeKC0xKSAoY2FsKEwpXzEgTG90aW1lc19MYW1iZGEgY2FsKEwpXzIpLCBmXigtMSkgKC0pKSJdLFswLDFdLFsxLDJdLFsyLDNdLFszLDRdLFswLDUsInRpbGRlIiwyXSxbNSw0XV0=
      #align(center, diagram({
        node((0, 0), [$RHHom_Lambda (f^(-1) cal(L)_1 Lotimes_Lambda f^(-1) cal(L)_2, f^(-1) (-))$])
        node((1, 0), [$RHHom_Lambda (f^(-1) cal(L)_1, RHHom_Lambda(f^(-1) cal(L)_2, f^(-1) (-)))$])
        node((1, 1), [$RHHom_Lambda (f^(-1) cal(L)_1, f^(-1) RHHom_Lambda(cal(L)_2, -))$])
        node((1, 2), [$f^(-1) RHHom_Lambda (cal(L)_1, RHHom_Lambda(cal(L)_2, -))$])
        node((0, 2), [$f^(-1) RHHom_Lambda (cal(L)_1 Lotimes_Lambda cal(L)_2, -)$])
        node((0, 1), [$RHHom_Lambda (f^(-1) (cal(L)_1 Lotimes_Lambda cal(L)_2), f^(-1) (-))$])
        edge((0, 0), (1, 0), "->")
        edge((1, 0), (1, 1), "->")
        edge((1, 1), (1, 2), "->")
        edge((1, 2), (0, 2), "->")
        edge((0, 0), (0, 1), [$tilde$], label-side: right, "->")
        edge((0, 1), (0, 2), "->")
      }))
      Had we not cheated by taking stalks, we would have to manually prove this. It is probably not hard anyways. 
    ]
]

We are now ready to combine the projection morphisms for $R f_*$ and for $f_!$ to define a projection morphism for $R f_!$. 

#proposition[
  For a separated morphism $f: X -> Y$ of finite type between noetherian schemes, there exists a natural projection morphism: 
  $
    R f_! cal(K) Lotimes_Lambda cal(L) -> R f_! (cal(K) Lotimes_Lambda f^(-1) cal(L))
  $
  for $cal(K) in D_#[tor] (X_et), cal(L) in D_#[tor] (Y_et)$, compatible with composition in $f$, tensors in $cal(L)$ and arbitrary base change. 
]
#proof[
  Pick a compactification $X ->^j ol(X) ->^(ol(f)) Y$ of $f$. We now define the projection map: 
  $
    R f_! cal(K) Lotimes_Lambda cal(L) cong R ol(f)_* j_! cal(K) Lotimes_Lambda cal(L) -> R ol(f)_* (j_! cal(K) Lotimes_Lambda ol(f)^(-1) cal(L)) -> R ol(f)_* j_! (cal(K) Lotimes_Lambda j^(-1) ol(f)^(-1) cal(L)) cong R f_! (cal(K) Lotimes_Lambda f^(-1) cal(L))
  $
  where the first step is projection for $R ol(f)_*$, and the second step is projection for $j_!$. 

  Now well-definedness follows from the following lemma. Compatibility with tensors in $cal(L)$ and with arbitrary base change follow from the respective properties for projection for $R ol(f)_*$ and $j_!$. Compatibility with composition in $f$ follows from the respective property for projection for $R ol(f)_*$ and $j_!$ as well as the following lemma. 

  #lemma[
    Given a commutative diagram of noetherian schemes: 
    // https://q.uiver.app/#r=typst&q=WzAsNCxbMCwwLCJYXzEiXSxbMCwxLCJYXzIiXSxbMSwxLCJZXzIiXSxbMSwwLCJZXzEiXSxbMCwzLCJmXzEiXSxbMSwyLCJmXzIiLDJdLFswLDEsImpfWCIsMl0sWzMsMiwial9ZIl1d
    #context align(center, diagram({
      node((-1, 0), [$X_1$])
      node((-1, 1), [$X_2$])
      node((0, 1), [$Y_2$])
      node((0, 0), [$Y_1$])
      edge((-1, 0), (0, 0), [$f_1$], label-side: left, "->")
      edge((-1, 1), (0, 1), [$f_2$], label-side: right, "->")
      edge((-1, 0), (-1, 1), [$j_X$], label-side: right, "->")
      edge((0, 0), (0, 1), [$j_Y$], label-side: left, "->")
      edge((-1, 0), (0, 1), $p$, label-side: center, "->")
    }, crossing-fill: thm-box-curr-color()))
    in which horizontal morphisms are proper and vertical morphisms are open immersions, let the isomorphism $j_(Y,!) R f_(1,*) -> R f_(2,*) j_(X,!)$ in @open-proper-compat be denoted by $T$. Then the composition: 
    $
      j_(Y,!) R f_(1,*) (-) Lotimes_Lambda cal(L) -->^T R f_(2,*) j_(X,!) (-) Lotimes_Lambda cal(L) -->^P R f_(2,*) (j_(X,!) (-) Lotimes_Lambda f_2^(-1) cal(L)) -->^(P_!) R f_(2,*) j_(X,!) (- Lotimes_Lambda p^(-1) cal(L))
    $
    is equal to the composition: 
    $
      j_(Y,!) R f_(1,*) (-) Lotimes_Lambda cal(L) -->^(P_!) j_(Y,!) (R f_(1,*) (-) Lotimes_Lambda j_Y^(-1) cal(L)) -->^P j_(Y,!) R f_(1,*) (- Lotimes_Lambda p^(-1) cal(L)) -->^T R f_(2,*) j_(X,!) (- Lotimes_Lambda p^(-1) cal(L))
    $
    where $P$ denotes projection for $R f_(1,*)$ or $R f_(2,*)$, and $P_!$ denotes projection for $j_(X,!)$ or $j_(Y,!)$. 
  ]
  #proof[
    We could have proved this the hard way by inspecting natural transformations in various Beck-Chevalley base changes used to define the various morphisms. 

    Instead, by @open-proper-compat-with-bc and our construction for the projections $P$ and $P_!$, all natural transformations here are compatible with base change. Furthermore, by proper base change, @etale-lower-shriek-first-props (4), and monoidal isomorphism for pullbacks, the base change maps in the respective compatibilities are all isomorphisms. Therefore, by checking stalks, it suffices to prove this lemma upon base changing the entire diagram of schemes to a geometric point of $Y_2$. 

    Upon base changing to a geometric point of $Y_2$ not in $Y_1$, $j_(Y,!)$ becomes zero, and both paths are zero. Thus, we may assume that we are base changing to a geometric point $ol(y) = Spec(k) -> Y_2$ that is in $Y_1$ for $k$ an algebraically closed field. Then under this base change, $j_Y$ becomes the identity $Spec(k) -> Spec(k)$, and our commutative diagram becomes: 
    // https://q.uiver.app/#r=typst&q=WzAsMyxbMCwwLCJYXzEiXSxbMCwyLCJYXzIiXSxbMiwxLCJTcGVjKGspIl0sWzAsMSwiaiIsMl0sWzAsMiwiZl8xIl0sWzEsMiwiZl8yIiwyXV0=
    #align(center, diagram({
      node((0, 0), [$X_1$])
      node((0, 2), [$X_2$])
      node((2, 1), [$Spec(k)$])
      edge((0, 0), (0, 2), [$j$], label-side: right, "->")
      edge((0, 0), (2, 1), [$f_1$], label-side: left, "->")
      edge((0, 2), (2, 1), [$f_2$], label-side: right, "->")
    }, spacing: 1.5em))
    in which $f_1, f_2$ are proper and $j$ is an open immersion. Thus $j$ is a proper open immersion, hence an open and closed immersion. //We may thus write $X_2 = X_1 union.sq X_3$ for another proper $k$-scheme $f_3: X_3 -> Spec(k)$. 
    
    In this case, we may identify $j_! cong R j_*$. 

    - Under this identification, the natural transformation $T: R f_(1,*) -> R f_(2,*) j_!$ is just the composition $R f_(1,*) cong R f_(2,*) R j_*$. Indeed:
    
      - By definition, $T$ is an inverse to the base change $R f_(2,*) j_! -> R f_(1,*) j^(-1) j_! cong R f_(1,*)$. 
      
      - $R f_(1,*) cong R f_(2,*) R j_*$ is an inverse to the base change $R f_(2,*) R j_* -> R f_(1,*) j^(-1) R j_* cong R f_(1,*)$. This is just compatibility of base change with horizontal concatenation of squares. 

      - The identification $j_! cong R j_*$ is compatible with the identification $j^(-1) j_! cong id cong j^(-1) R j_*$. 

    - Under this identification, the projection for $j_!$ becomes the projection for $R j_*$. Indeed, upon applying $j^(-1)$ and the monoidal isomorphism, 
      $
        P: R j_* (-) Lotimes_Lambda cal(L) -> R j_* (- Lotimes_Lambda j^(-1) cal(L))
      $
      becomes $j^(-1) R j_* (-) Lotimes_Lambda j^(-1) cal(L) -> - Lotimes_Lambda j^(-1) cal(L)$ a counit. Identifying $j^(-1) R j_*$ makes this the identity. 

      On the upon hand, upon applying $j^(-1)$ and the monoidal isomorphism, 
      $
        P_!: j_! (-) Lotimes_Lambda cal(L) -> j_! (- Lotimes_Lambda j^(-1) cal(L))
      $
      becomes the identity on $- Lotimes_Lambda j^(-1) cal(L)$ too, by compatibility of $P_!$ with base change. We have thus verified this claim.  

    Now with these two claims, the desired equality just becomes the compatibility of projection for $R f_*$ with composition. 
  ]
]

With the projection map defined, we are now ready to prove the projection formula. 

#theorem(name: <projection-formula>)[
  (Projection formula) For a separated morphism $f: X -> Y$ of finite type between noetherian schemes, the natural projection morphism: 
  $
    R f_! cal(K) Lotimes_Lambda cal(L) -> R f_! (cal(K) Lotimes_Lambda f^(-1) cal(L))
  $
  for $cal(K) in D_#[tor] (X_et), cal(L) in D_#[tor] (Y_et)$ is a quasi-isomorphism. 
]
#proof[
  Pick a compactification $X ->^j ol(X) ->^(ol(f)) Y$ of $f$. Then the projection for $R f_!$ is just the projection for $R ol(f)_*$ and that for $j_!$ chained. The projection for $j_!$ is already an isomorphism, so it suffices to prove the $R ol(f)_*$ part. We may thus replace $f$ with $ol(f)$, and assume that $f$ is proper. We aim to prove that the projection: 
  $
    R f_* cal(K) Lotimes_Lambda cal(L) -> R f_* (cal(K) Lotimes_Lambda f^(-1) cal(L))
  $
  is a quasi-isomorphism. By proper base change and the compatibility of projection with base change, this is equivalent to proving for geometric points $ol(y)$ of $Y$ that the projection: 
  $
    R Gamma(X_(ol(y)), cal(K)|_(X_(ol(y)))) Lotimes_Lambda cal(L)_(ol(y)) -> R Gamma(X_(ol(y)), cal(K)|_(X_(ol(y))) Lotimes_Lambda ul(cal(L)_(ol(y))))
  $
  is a quasi-isomorphism. This follows from the following lemma: 
  #lemma(name: <projection-formula-for-global-sections>)[
    (Projection formula for global sections) Let $X$ be scheme that is of finite type over a separably closed field $k$. Then for any $cal(K) in D(X_et, Lambda), M in D (Lambda)$, the projection map: 
    $
      R Gamma(X, cal(K)) Lotimes_Lambda M -> R Gamma(X, cal(K) Lotimes_Lambda ul(M))
    $
    is a quasi-isomorphism. 
  ]
  #proof[
    The way-out lemma is insufficient for reducing this proposition to an easy case. We thus need to use more powerful reductions: 

    #lemma(name: <cpct-generator-of-d-lambda>)[
      For a ring $Lambda$, a property $T$ on objects in $D(Lambda)$ holds for every object of $D(Lambda)$, if: 

      #set enum(numbering: "(a)")
      + Given a family of complexes $M_i in D(Lambda)$, if $T(M_i)$ holds for all $i$, then $T(oplus.big_i M_i)$ holds. 

      + Given a distinguished triangle $K -> L -> M ->^(+1)$ in $D(Lambda)$, if two of $T(K), T(L), T(M)$ holds, then so does the third. 

      + For all $k in ZZ$, $T(Lambda[k])$ holds. 
    ]
    #proof[
      This is #cite-stacks("09PB")[Remark 15.60.11], or @cpct-generation-of-triangulated-cat applied to $D(Lambda)$ and the family of generating objects ${Lambda[k]}_(k in ZZ)$. 
    ]

    Let $T$ be the property on $D(Lambda)$ such that $T(M)$ is the statement: 

    - For all $cal(K) in D(X_et, Lambda)$, the projection map: #h(1fr)
      $
        R Gamma(X, cal(K)) Lotimes_Lambda M -> R Gamma(X, cal(K) Lotimes_Lambda ul(M))
      $
      is a quasi-isomorphism. 

    Now: 

    - Both sides are triangulated in $M$, so by the derived five lemma, $T(M)$ is preserved under shifts, and if $T(K), T(L)$ holds in a distinguished triangle $K -> L -> M ->^(+1)$, then $T(M)$ holds. 

    - For arbitrary direct sums, we need to use a limit formula: 

      #proposition(name: <derived-bounded-limit-formula-for-direct-sum>)[
        Let $X$ be a qcqs scheme s.t. $R Gamma(X, -)$ is bounded above. Then for any $cal(K)_i in D (X_et, Lambda)$ the canonical map: 
        $
          oplus.big_i R Gamma(X, cal(K)_i) -> R Gamma(X, oplus.big_i cal(K)_i)
        $
        is a quasi-isomorphism. 
      ]
      #proof[
        Consider the truncations $tau_([a,b]) (cal(K)_i)$. Then: 
        $
          tau_([a,b]) (oplus.big_i cal(K)_i) = oplus.big_i tau_([a,b]) cal(K)_i
        $
        Suppose that $R Gamma(X, -)$ has cohomological dimension above $=d$. Then by using truncation triangles, the canonical map: 
        $
          h^q (R Gamma(X, tau_([q-d,q+1]) cal(K))) -> h^q (R Gamma(X, cal(K)))
        $
        is an isomorphism. Thus, to prove the desired isomorphism, we may argue for each degree separatedly, and truncate all complexes so that we may assume that each $cal(K)_i$ is supported on $[a,b]$. Now replace each $cal(K)_i$ with an injective resolution $cal(I)_i$ supported on $[a,+oo)$, and note that for each $p$, and every $q>=1$: 
        $
          H^q (X, oplus.big_i cal(I)_i^p) = oplus.big_i H^q (X, cal(I)_i^p) = 0
        $
        Thus, $oplus.big_i cal(K)_i$ is quasi-isomorphic to the bounded below complex $oplus.big_i cal(I)_i$ of $Gamma(X,-)$-acyclic sheaves. This acyclic resolution can thus be used to compute $R Gamma(X, -)$, giving: 
        $
          R Gamma(X, oplus.big_i cal(K)_i) = oplus.big_i R Gamma(X, cal(K)_i)
        $
      ]
      The lemma above is applicable because $X$ is of finite type over a separably closed field $k$, and so $R Gamma(X, -)$ is bounded above by Grothendieck vanishing. Now $Lotimes_Lambda$ is a left adjoint, and hence commutes with all direct sums. Hence: 
      $
        R Gamma(X, cal(K)) Lotimes_Lambda (oplus.big_i M_i) = oplus.big_i (R Gamma(X, cal(K)) Lotimes_Lambda M_i)
      $
      while: 
      $
        R Gamma(X, cal(K) Lotimes_Lambda ul(oplus.big_i M_i)) &= R Gamma(X, cal(K) Lotimes_Lambda (oplus.big_i ul(M_i))) \
        &= R Gamma(X, oplus.big_i (cal(K) Lotimes_Lambda ul(M_i))) \
        &= oplus.big_i R Gamma(X, cal(K) Lotimes_Lambda ul(M_i))
      $
      Therefore, $T(M_i)$ for all $i$ implies $T(oplus.big_i M_i)$. 

    - Finally, $T(Lambda[k])$ holds for all $k$. Indeed, $T$ is preserved under shifts, so it suffices to prove $T(Lambda)$. But: 
      $
        R Gamma(X, cal(K) Lotimes_Lambda ul(Lambda)) = R Gamma(X, cal(K)) = R Gamma(X, cal(K)) Lotimes_Lambda Lambda
      $

    By our lemma above, $T(M)$ holds for all $M in D(Lambda)$. We are thus done proving the projection formula for global sections. 
    /*
    Since $Lambda$ has finite global dimension, $- Lotimes_Lambda M$ and $- Lotimes_Lambda ul(M)$ are both bounded above/below functors if $M$ is a bounded above/below complex. Further, since $X$ is finite type over an algebraically closed field $k$, $R Gamma$ is bounded. 
    
    Thus, in each of the four cases, the way-out lemma is applicable, and we may reduce to the case that $cal(K)$ is a single sheaf $cal(F) in cAb(X_et)$. 
    
    Next, having fixed $cal(K) = cal(F) in cAb(X_et, Lambda)$, both sides are bounded in $M$. By way-out lemma, we may further assume that $M = N in AMod(Lambda)$ is a $Lambda$-module. Since $Lambda$ has finite global dimension, we may find a bounded projective resolution of $M$, say $0 -> P^bullet -> M$. Now: 
    $
      R Gamma(X, cal(K)) Lotimes_Lambda M = R Gamma(X, cal(F)) otimes_Lambda P \
      R Gamma(X, cal(K) Lotimes_Lambda ul(M)) = R Gamma(X, cal(F) otimes_Lambda ul(P))
    $
    Taking an injective resolution $0 -> cal(F) -> cal(I)^bullet$, and considering the double complex: 
    $
      Gamma(X, cal(I)^bullet) otimes_Lambda P^*
    $
    we get a canonical spectral sequence that is horizontally bounded: 
    $
      E_1^(p,q) = H^q (X, cal(F)) otimes_Lambda P^p => h^(p+q) (R Gamma(X, cal(F)) otimes_Lambda P)
    $
    On the other hand, the hypercohomology spectral sequence gives another canonical horizontally bounded spectral sequence: 
    $
      tilde(E)_1^(p,q) = H^q (X, cal(F) otimes_Lambda ul(P^p)) => h^(p+q) (R Gamma(X, cal(F) otimes_Lambda ul(P)))
    $
      The projection maps give a morphism $E_1^(p,q) -> tilde(E)_1^(p,q)$ of spectral sequences. Thus, to show that $R Gamma(X, cal(F)) otimes_Lambda P -> R Gamma(X, cal(F) otimes_Lambda ul(P))$ is a quasi-isomorphism, it suffices to show that each $E_1^(p,q) -> tilde(E)_1^(p,q)$ is an isomorphism, i.e. given a projective $Lambda$-module $Q$ and any $cal(F) in cAb(X_et, Lambda)$, we have: 
    $
      H^q (X, cal(F) otimes_Lambda ul(Q)) cong H^q (X, cal(F)) otimes_Lambda Q
    $
    By Lazard's theorem (#cite-stacks("058G")[Theorem 10.81.4]), $Q = dirlim_lambda Q_lambda$ is a direct limit of finite free $Lambda$-modules $Q_lambda$'s. Since tensor product commutes with colimits as a left adjoint, by the limit formula @limit-formula-for-sheaves, it suffices to prove for each $Q_lambda$: 
    $
      H^q (X, cal(F) otimes_Lambda ul(Q_lambda)) cong H^q (X, cal(F)) otimes_Lambda Q_lambda
    $
    But each $Q_lambda cong Lambda^(oplus m_lambda)$ is a direct sum of $m_lambda$ copies of $Lambda$, so both sides are direct sums of $m_lambda$ copies of $H^q (X, cal(F))$. */
  ]
]

Next, from the projection formula, we derive the Kunneth formula. 

#theorem(name: <kunneth-formula>)[
  (Kunneth formula) Given a Cartesian diagram of noetherian schemes: 
  // https://q.uiver.app/#r=typst&q=WzAsNCxbMCwwLCJYIl0sWzAsMSwiWF8xIl0sWzEsMCwiWF8yIl0sWzEsMSwiWSJdLFswLDEsInBfMSIsMl0sWzAsMiwicF8yIl0sWzEsMywiZl8xIiwyXSxbMiwzLCJmXzIiXSxbMCwzLCJmIiwxXV0=
  #context align(center, diagram({
    node((0, 0), [$X$])
    node((0, 1), [$X_2$])
    node((1, 0), [$X_1$])
    node((1, 1), [$Y$])
    edge((0, 0), (0, 1), [$p_2$], label-side: right, "->")
    edge((0, 0), (1, 0), [$p_1$], label-side: left, "->")
    edge((0, 1), (1, 1), [$f_2$], label-side: right, "->")
    edge((1, 0), (1, 1), [$f_1$], label-side: left, "->")
    edge((0, 0), (1, 1), [$f$], label-side: center, "->")
  }, crossing-fill: thm-box-curr-color()))
  there is a natural isomorphism: 
  $
    R f_! (p_1^(-1) cal(K)_1 Lotimes_Lambda p_2^(-1) cal(K)_2) cong R f_(1,!) cal(K)_1 Lotimes_Lambda R f_(2,!) cal(K)_2
  $
  for $cal(K)_1 in D_#[tor] ((X_1)_et, Lambda), cal(K)_2 in D_#[tor] ((X_2)_et, Lambda)$. This isomorphism is compatible with arbitrary base changes, is symmetric in $f_1$ and $f_2$, is compatible with $3 times 3$ Cartesian squares, and is associative w.r.t. triple products. 
]
#proof[
  We construct this isomorphism first: 
  /*$
    & R f_! (p_1^(-1) cal(K)_1 Lotimes_Lambda p_2^(-1) cal(K)_2) \
    cong& R f_(2,!) R p_(2,!) (p_1^(-1) cal(K)_1 Lotimes_Lambda p_2^(-1) cal(K)_2) \
    cong& R f_(2,!) (R p_(2,!) p_1^(-1) cal(K)_1 Lotimes_Lambda cal(K)_2) #[by projection formula] \
    cong& R f_(2,!) (f_2^(-1) R f_(1,!) cal(K)_1 Lotimes_Lambda cal(K)_2) #[by proper base change] \
    cong& R f_(1,!) cal(K)_1 Lotimes_Lambda R f_(2,!) cal(K)_2 #[by projection formula]
  $*/
  $
    & R f_(1,!) cal(K)_1 Lotimes_Lambda R f_(2,!) cal(K)_2 \
    cong& R f_(2,!) (f_2^(-1) R f_(1,!) cal(K)_1 Lotimes_Lambda cal(K)_2) #[by projection formula] \
    cong& R f_(2,!) (R p_(2,!) p_1^(-1) cal(K)_1 Lotimes_Lambda cal(K)_2) #[by proper base change] \
    cong& R f_(2,!) R p_(2,!) (p_1^(-1) cal(K)_1 Lotimes_Lambda p_2^(-1) cal(K)_2) #[by projection formula] \
    cong& R f_! (p_1^(-1) cal(K)_1 Lotimes_Lambda p_2^(-1) cal(K)_2)
  $
  By compatibility of projection with base change and by naturality of base change, this Kunneth isomorphism is compatible with arbitrary base change. We now prove the rest of compatibility statements. 

  From now on we write $Lotimes$ for $Lotimes_Lambda$ and suppress $Lambda$ from the notation. We need two lemmas to help prove the symmetry and $3 times 3$ compatibility statements. We will use:
  
  - $P(f)$ to denote the projection map by $R f_!$;
  
  - $P'(f)$ to denote the projection map by $R f_!$ in the other slot, i.e. $cal(K) Lotimes R f_! cal(L) -> R f_! (f^(-1) cal(K) Lotimes cal(L))$; 

  - $BC$ to denote a base change. 

  The first lemma is an alternative description of the Kunneth isomorphism in the case of all morphisms being proper. 
  #lemma(name: <proper-kunneth-alt-desc>)[
    In the case where $f_1, f_2$ are both proper, the Kunneth isomorphism: 
    $
      R f_(1,*) cal(K)_1 Lotimes R f_(2,*) cal(K)_2 -> R f_* (p_1^(-1) cal(K)_1 Lotimes p_2^(-1) cal(K)_2) 
    $
    can be described as follows: By adjunction of $R f_*$, it is equivalent to a map $f^(-1) (R f_(1,*) cal(K)_1 Lotimes R f_(2,*) cal(K)_2) -> p_1^(-1) cal(K)_1 Lotimes p_2^(-1) cal(K)_2$. This map is: 
    $
      f^(-1) (R f_(1,*) cal(K)_1 Lotimes R f_(2,*) cal(K)_2) &cong f^(-1) R f_(1,*) cal(K)_1 Lotimes f^(-1) R f_(2,*) cal(K)_2 \
      &= p_1^(-1) f_1^(-1) R f_(1,*) cal(K)_1 Lotimes p_2^(-1) f_2^(-1) R f_(2,*) cal(K)_2 \
      &-> p_1^(-1) cal(K)_1 Lotimes p_2^(-1) cal(K)_2
    $
    where the first map is a monoidal isomorphism, and the second map consists of two adjunction counits. 
  ]
  #proof[
    Consider the construction of the Kunneth map: 
    $
      R f_(1,*) cal(K)_1 Lotimes R f_(2,*) cal(K)_2 &-->^(P'(f_2)) R f_(2,*) (f_2^(-1) R f_(1,*) cal(K)_1 Lotimes cal(K)_2) \
      &-->^BC R f_(2,*) (R p_(2,*) p_1^(-1) cal(K)_1 Lotimes cal(K)_2) \
      &-->^(P(p_2)) R f_(2,*) R p_(2,*) (p_1^(-1) cal(K) Lotimes p_2^(-1) cal(K)_2) 
    $
    Now: 
    
    - In the construction of the projection map for $R f_*$, we have described how the projection map looks under adjunction. Under adjunction, $P(f): R f_* cal(K) Lotimes cal(L) -> R f_* (cal(K) Lotimes cal(L))$ becomes: #h(1fr)
      $
        f^(-1) (R f_* cal(K) Lotimes cal(L)) -->^M f^(-1) R f_* cal(K) Lotimes f^(-1) cal(L) -->^eta cal(K) Lotimes f^(-1) cal(L)
      $
      Here, $M$ denotes a monoidal isomorphism and $eta$ denotes a counit. $P'(f)$ looks the same but has the tensors flipped. 
  
    Thus, the Kunneth map under adjunction becomes: 
    $
      p_2^(-1) f_2^(-1) (R f_(1,*) cal(K)_1 Lotimes R f_(2,*) cal(K)_2) &-->^(M(f_2)) p_2^(-1) (f_2^(-1) R f_(1,*) cal(K)_1 Lotimes f_2^(-1) R f_(2,*) cal(K)_2) \
      &-->^(eta(f_2)) p_2^(-1) (f_2^(-1) R f_(1,*) cal(K)_1 Lotimes cal(K)_2) \
      &-->^BC p_2^(-1) (R p_(2,*) p_1^(-1) cal(K)_1 Lotimes cal(K)_2) \
      &-->^(M(p_2)) p_2^(-1) R p_(2,*) p_1^(-1) cal(K)_1 Lotimes p_2^(-1) cal(K)_2 \
      &-->^(eta(p_2)) p_1^(-1) cal(K)_1 Lotimes p_2^(-1) cal(K)_2
    $
    By naturality, we may permute the last four steps and turn this into: 
    $
      p_2^(-1) f_2^(-1) (R f_(1,*) cal(K)_1 Lotimes R f_(2,*) cal(K)_2) &-->^(M(f_2)) p_2^(-1) (f_2^(-1) R f_(1,*) cal(K)_1 Lotimes f_2^(-1) R f_(2,*) cal(K)_2) -->^(M(p_2)) p_2^(-1) f_2^(-1) R f_(1,*) cal(K)_1 Lotimes p_2^(-1) f_2^(-1) R f_(2,*) cal(K)_2 \
      &-->^BC p_2^(-1) R p_(2,*) p_1^(-1) cal(K)_1 Lotimes p_2^(-1) f_2^(-1) R f_(2,*) cal(K)_2 \
      &-->^(eta(p_2)) p_1^(-1) cal(K)_1 Lotimes p_2^(-1) f_2^(-1) R f_(2,*) cal(K)_2 \
      &-->^(eta(f_2)) p_2^(-1) (f_2^(-1) R f_(1,*) cal(K)_1 Lotimes cal(K)_2)
    $
    This already resembles the claimed morphism, and it all amounts to showing that the composition: 
    $
      p_2^(-1) f_2^(-1) R f_(1,*) cong p_1^(-1) f_1^(-1) R f_(1,*) -->^(eta(f_1)) p_1^(-1)
    $
    is the same as the composition: 
    $
      p_2^(-1) f_2^(-1) R f_(1,*) -->^(BC) p_2^(-1) R p_(2,*) p_1^(-1) -->^(eta(p_2)) p_1^(-1)
    $

    - Indeed, by @bcbc-all-rights, the second path is: #h(1fr)
      $
        p_2^(-1) f_2^(-1) R f_(1,*) &-->^(p_2^(-1) u(p_2) f_2^(-1) R f_(1,*)) p_2^(-1) R p_(2,*) p_2^(-1) f_2^(-1) R f_(1,*) cong p_2^(-1) R p_(2,*) p_1^(-1) f_1^(-1) R f_(1,*) \
        &-->^(p_2^(-1) R p_(2,*) p_1^(-1) eta(f_1)) p_2^(-1) R p_(2,*) p_1^(-1) -->^(eta(p_2) p_1^(-1)) p_1^(-1)
      $
      Exchanging the fourth map with the second and the third by naturality, then applying an adjunction identity yields the first path. 

    We may conclude the proof. 
  ]

  The second lemma is about the interaction between the condition of the Kunneth maps in a diagram being symmetric, and being compatible with $3 times 3$ Cartesian diagrams. 

  #lemma(name: <kunneth-3x3-and-symmetry>)[
    Take a $3 times 3$ Cartesian diagram of separated morphisms of finite type between noetherian schemes. 

    // https://q.uiver.app/#r=typst&q=WzAsOSxbMCwwLCJaIl0sWzEsMCwiWl8xIl0sWzIsMCwiV18xIl0sWzAsMSwiWl8yIl0sWzEsMSwiWCJdLFsyLDEsIlhfMSJdLFswLDIsIldfMiJdLFsxLDIsIlhfMiJdLFsyLDIsIlkiXSxbNSw4LCJmXzEiLDFdLFs3LDgsImZfMiIsMV0sWzQsNSwicF8xIiwxXSxbNCw3LCJwXzIiLDFdLFsyLDUsImhfMSIsMV0sWzYsNywiaF8yIiwxXSxbMSw0LCJnXzEiLDFdLFszLDQsImdfMiIsMV0sWzEsMiwic18xIiwxXSxbMyw2LCJzXzIiLDFdLFswLDEsInFfMSIsMV0sWzAsMywicV8yIiwxXV0=
    #context align(center, diagram({
      node((0, 0), [$Z$])
      node((1, 0), [$Z_1$])
      node((2, 0), [$W_1$])
      node((0, 1), [$Z_2$])
      node((1, 1), [$X$])
      node((2, 1), [$X_1$])
      node((0, 2), [$W_2$])
      node((1, 2), [$X_2$])
      node((2, 2), [$Y$])
      edge((2, 1), (2, 2), [$f_1$], label-side: center, "->")
      edge((1, 2), (2, 2), [$f_2$], label-side: center, "->")
      edge((1, 1), (2, 1), [$p_1$], label-side: center, "->")
      edge((1, 1), (1, 2), [$p_2$], label-side: center, "->")
      edge((2, 0), (2, 1), [$h_1$], label-side: center, "->")
      edge((0, 2), (1, 2), [$h_2$], label-side: center, "->")
      edge((1, 0), (1, 1), [$g_1$], label-side: center, "->")
      edge((0, 1), (1, 1), [$g_2$], label-side: center, "->")
      edge((1, 0), (2, 0), [$s_1$], label-side: center, "->")
      edge((0, 1), (0, 2), [$s_2$], label-side: center, "->")
      edge((0, 0), (1, 0), [$q_1$], label-side: center, "->")
      edge((0, 0), (0, 1), [$q_2$], label-side: center, "->")
    }, crossing-fill: thm-box-curr-color()))

    Denote by:
    
    - $BC_(1,2,3,4)$ the base changes in the upper left, upper right, lower left, lower right squares, respectively, with pullbacks along vertical maps and pushforwards along horizontal maps;
    
    - $BC_i^T$ the base change in the same square as in $BC_i$, but with pullbacks along horizontal maps and pushforwards along vertical maps; 

    - $K_1, K_2$ the Kunneth map in the upper left and lower right square, respectively. 
    
    Suppose that the Kunneth map in the lower left square is symmetric. Then the Kunneth map is compatible with this $3 times 3$ square. That is, the composition: 
    $
      & R f_(1,!) R h_(1,!) cal(K)_1 Lotimes R f_(2,!) R h_(2,!) cal(K)_2 \
      -->^(K_2) & R f_(2,!) R p_(2,!) (p_1^(-1) R h_(1,!) cal(K)_1 Lotimes p_2^(-1) R h_(2,!) cal(K)_2) \
      -->^(BC_2^T, BC_3) & R f_(2,!) R p_(2,!) (R g_(1,!) s_1^(-1) cal(K)_1 Lotimes R g_(2,!) s_2^(-1) cal(K)_2) \
      -->^(K_1) & R f_(2,!) R p_(2,!) R g_(2,!) R s_(q,!) (q_1^(-1) s_1^(-1) cal(K)_1 Lotimes q_2^(-1) s_2^(-1) cal(K)_2) \
      cong & R f_(2,!) R h_(2,!) R s_(2,!) R s_(q,!) (q_1^(-1) s_1^(-1) cal(K)_1 Lotimes q_2^(-1) s_2^(-1) cal(K)_2)
    $
    is exactly the Kunneth map of the large square. 
  ]
  #proof[
    We first write down path (1), the Kunneth of the two small squares: 
    $
      & R f_(1,!) R h_(1,!) cal(K)_1 Lotimes R f_(2,!) R h_(2,!) cal(K)_2 \
      -->^(P'(f_2)) & R f_(2,!) (f_2^(-1) R f_(1,!) R h_(1,!) cal(K)_1 Lotimes R h_(2,!) cal(K)_2) \
      -->^(BC_4^T) & R f_(2,!) (R p_(2,!) p_1^(-1) R h_(1,!) cal(K)_1 Lotimes R h_(2,!) cal(K)_2) \
      -->^(P(p_2)) & R f_(2,!) R p_(2,!) (p_1^(-1) R h_(1,!) cal(K)_1 Lotimes p_2^(-1) R h_(2,!) cal(K)_2) \
      -->^(BC_2^T, BC_3) & R f_(2,!) R p_(2,!) (R g_(1,!) s_1^(-1) cal(K)_1 Lotimes R g_(2,!) s_2^(-1) cal(K)_2) \
      -->^(P'(g_2)) & R f_(2,!) R p_(2,!) R g_(2,!) (g_2^(-1) R g_(1,!) s_1^(-1) cal(K)_1 Lotimes s_2^(-1) cal(K)_2)\
      -->^(BC_1^T) & R f_(2,!) R p_(2,!) R g_(2,!) (R q_(2,!) q_1^(-1) s_1^(-1) cal(K)_1 Lotimes s_2^(-1) cal(K)_2) & \ 
      -->^(P(q_2)) & R f_(2,!) R p_(2,!) R g_(2,!) R q_(2,!) (q_1^(-1) s_1^(-1) cal(K)_1 Lotimes q_2^(-1) s_2^(-1) cal(K)_2) \
      -->^c & R f_(2,!) R h_(2,!) R s_(2,!) R q_(2,!) (q_1^(-1) s_1^(-1) cal(K)_1 Lotimes q_2^(-1) s_2^(-1) cal(K)_2)
    $
    where $c$ is the isomorphism $R p_(2,!) R g_(2,!) -> R h_(2,!) R s_(2,!)$. Then path (2), the Kunneth of the large square, is the following path by compatibility of projection map with composition: 
    $
      & R f_(1,!) R h_(1,!) cal(K)_1 Lotimes R f_(2,!) R h_(2,!) cal(K)_2 \
      -->^(P'(f_2)) & R f_(2,!) (f_2^(-1) R f_(1,!) R h_(1,!) cal(K)_1 Lotimes R h_(2,!) cal(K)_2) \
      -->^(P'(h_2)) & R f_(2,!) R h_(2,!) (h_2^(-1) f_2^(-1) R f_(1,!) R h_(1,!) cal(K)_1 Lotimes cal(K)_2) \
      -->^(BC_(1,2,3,4)^T) & R f_(2,!) R h_(2,!) (R s_(2,!) R q_(2,!) q_1^(-1) s_1^(-1) cal(K)_1 Lotimes cal(K)_2) \
      -->^(P(s_2)) & R f_(2,!) R h_(2,!) R s_(2,!) (R q_(2,!) q_1^(-1) s_1^(-1) cal(K)_1 Lotimes s_2^(-1) cal(K)_2) \
      -->^(P(q_2)) & R f_(2,!) R h_(2,!) R s_(2,!) R q_(2,!) (q_1^(-1) s_1^(-1) cal(K)_1 Lotimes q_2^(-1) s_2^(-1) cal(K)_2)
    $
    By naturality, the last two morphisms in (1) may be permuted from $-->^(P(q_2)) -->^c$ to $-->^c -->^(P(q_2))$. Then we may immediately cancel $P'(f_2)$ and $P(q_2)$ from the ends of both paths and peel off the $R f_(2,!)$ appearing on the exterior of every functor, and it suffices to prove that path (2'): 
    $
      & f_2^(-1) R f_(1,!) R h_(1,!) cal(K)_1 Lotimes R h_(2,!) cal(K)_2 \
      -->^(P'(h_2)) & R h_(2,!) (h_2^(-1) f_2^(-1) R f_(1,!) R h_(1,!) cal(K)_1 Lotimes cal(K)_2) \
      -->^(BC_(1,2,3,4)^T) & R h_(2,!) (R s_(2,!) R q_(2,!) q_1^(-1) s_1^(-1) cal(K)_1 Lotimes cal(K)_2) \
      -->^(P(s_2)) & R h_(2,!) R s_(2,!) (R q_(2,!) q_1^(-1) s_1^(-1) cal(K)_1 Lotimes s_2^(-1) cal(K)_2)
    $ 
    is the same as path (1'): 
    $
      &f_2^(-1) R f_(1,!) R h_(1,!) cal(K)_1 Lotimes R h_(2,!) cal(K)_2 \
      -->^(BC_4^T) & R p_(2,!) p_1^(-1) R h_(1,!) cal(K)_1 Lotimes R h_(2,!) cal(K)_2 \
      -->^(P(p_2)) & R p_(2,!) (p_1^(-1) R h_(1,!) cal(K)_1 Lotimes p_2^(-1) R h_(2,!) cal(K)_2) \
      -->^(BC_2^T, BC_3) & R p_(2,!) (R g_(1,!) s_1^(-1) cal(K)_1 Lotimes R g_(2,!) s_2^(-1) cal(K)_2) \
      -->^(P'(g_2)) & R p_(2,!) R g_(2,!) (g_2^(-1) R g_(1,!) s_1^(-1) cal(K)_1 Lotimes s_2^(-1) cal(K)_2)\
      -->^(BC_1^T) & R p_(2,!) R g_(2,!) (R q_(2,!) q_1^(-1) s_1^(-1) cal(K)_1 Lotimes s_2^(-1) cal(K)_2) & \ 
      -->^c & R h_(2,!) R s_(2,!) (R q_(2,!) q_1^(-1) s_1^(-1) cal(K)_1 Lotimes s_2^(-1) cal(K)_2)
    $
    Next, in path (1'), the final $-->^(BC_1^T) -->^c$ may be exchanged to $-->^c -->^(BC_1^T)$ by naturality, and $BC_2^T$ may be thrown to the left of $P(p)_2$. In path (2'), by naturality, $BC_2^T, BC_4^T$ may be thrown to the left of $P'(h_2)$, and $BC_1^T$ may be thrown to the right of $P(s)_2$. In summarize, we are comparing path (1'): 
    $
      bullet -->^(BC_4^T) bullet -->^(BC_2^T) bullet -->^(P(p_2)) bullet -->^(BC_3) bullet -->^(P'(g_2)) bullet -->^c bullet -->^(BC_1^T) bullet
    $
    against path (2'): 
    $
      bullet -->^(BC_4^T) bullet -->^(BC_2^T) bullet -->^(P'(h_2)) bullet -->^(BC_3) bullet -->^(P(s_2)) bullet -->^(BC_1^T) bullet
    $
    We may now eliminate $BC_(1,2,4)^T$ and conclude that it suffices to show that path (1''): 
    $
      & R p_(2,!) R g_(1,!) s_1^(-1) cal(K)_1 Lotimes R h_(2,!) cal(K)_2 \
      -->^(P'(h_2)) & R h_(2,!) (h_2^(-1) R p_(2,!) R g_(1,!) s_1^(-1) cal(K)_1 Lotimes cal(K)_2) \
      -->^(BC_3^T) & R h_(2,!) (R s_(2,!) g_2^(-1) R g_(1,!) s_1^(-1) cal(K)_1 Lotimes cal(K)_2) \
      -->^(P(s_2)) & R h_(2,!) R s_(2,!) (g_2^(-1) R g_(1,!) s_1^(-1) cal(K)_1 Lotimes s_2^(-1) cal(K)_2)
    $
    is the same as path (2''): 
    $
      & R p_(2,!) R g_(1,!) s_1^(-1) cal(K)_1 Lotimes R h_(2,!) cal(K)_2 \
      -->^(P(p_2)) & R p_(2,!) (R g_(1,!) s_1^(-1) cal(K)_1 Lotimes p_2^(-1) R h_(2,!) cal(K)_2) \
      -->^(BC_3) & R p_(2,!) (R g_(1,!) s_1^(-1) cal(K)_1 Lotimes R g_(2,!) s_2^(-1) cal(K)_2) \
      -->^(P'(g_2)) & R p_(2,!) R g_(2,!) (g_2^(-1) R g_(1,!) s_1^(-1) cal(K)_1 Lotimes s_2^(-1) cal(K)_2) \
      -->^(c^(-1)) & R h_(2,!) R s_(2,!) (g_2^(-1) R g_(1,!) s_1^(-1) cal(K)_1 Lotimes s_2^(-1) cal(K)_2)
    $
    However, by definition, path (1'') is the Kunneth of the lower left square applied to $R g_(1,!) s_1^(-1) cal(K)_1$ and $cal(K)_2$, and path (2'') is the Kunneth of that square but transposed. Their equality is exactly what symmetry of the Kunneth of the lower left square means.  
  ]

  We now start to prove the symmetry and $3 times 3$ compatibility statements. 

  - Step 1. Suppose that in the given Cartesian diagram, $f_2$ is an open immersion. Then we claim that the Kunneth map in this case is symmetric. #h(1fr)
  
    Indeed, by proper base change and compatibility with arbitrary base change, it suffices to prove symmetry upon base changing to a geometric point $ol(y)$ of $Y$. If $ol(y)$ is not in $X_2$, then the stalk of both sides of $R f_(1,!) cal(K)_1 Lotimes R f_(2,!) cal(K)_2 -> R f_! (p_1^(-1) cal(K)_1 Lotimes p_2^(-1) cal(K)_2)$ are zero, and symmetry is automatic. Thus, it suffices to prove symmetry upon base changing to a geometric point of $Y$ in $X_2$. In this case, the base changed diagram is: 
    // https://q.uiver.app/#r=typst&q=WzAsNCxbMCwwLCJYIl0sWzEsMCwiWCJdLFswLDEsIlNwZWMoaykiXSxbMSwxLCJTcGVjKGspIl0sWzAsMSwiIiwwLHsic3R5bGUiOnsiYm9keSI6eyJuYW1lIjoiZG91YmxlIGJhcnJlZCJ9fX1dLFsyLDMsIiIsMCx7InN0eWxlIjp7ImJvZHkiOnsibmFtZSI6ImRvdWJsZSBiYXJyZWQifX19XSxbMCwyLCJmIiwyXSxbMSwzLCJmIl1d
    #align(center, diagram({
      node((0, 0), [$X$])
      node((1, 0), [$X$])
      node((0, 1), [$Spec(k)$])
      node((1, 1), [$Spec(k)$])
      edge((0, 0), (1, 0), "=")
      edge((0, 1), (1, 1), "=")
      edge((0, 0), (0, 1), [$f$], label-side: right, "->")
      edge((1, 0), (1, 1), [$f$], label-side: left, "->")
    }, spacing: (1.5em, 3em)))
    for a separably closed field $k$. The Kunneth map in this case is simply the projection map: 
    $
      R f_! cal(K)_1 Lotimes cal(K)_2 -> R f_! (cal(K)_1 Lotimes f^(-1) cal(K)_2)
    $
    while the Kunneth map of the transpose is also this projection map, as can be checked by definition. Thus symmetry is automatic. 

  - Step 2. In the general case, pick compactifications $X_i ->^(j_i) ol(X)_i ->^(ol(f)_i) Y$, and we may split the original Cartesian square into a $3 times 3$ Cartesian diagram: 
    // https://q.uiver.app/#r=typst&q=WzAsOSxbMCwwLCJYIl0sWzEsMCwiWl8xIl0sWzIsMCwiWF8xIl0sWzAsMSwiWl8yIl0sWzEsMSwib2woWCkiXSxbMiwxLCJvbChYKV8xIl0sWzAsMiwiWF8yIl0sWzEsMiwib2woWClfMiJdLFsyLDIsIlkiXSxbNSw4LCJvbChmKV8xIiwxXSxbNyw4LCJvbChmKV8yIiwxXSxbNCw1LCJvbChwKV8xIiwxXSxbNCw3LCJvbChwKV8yIiwxXSxbMiw1LCJqXzEiLDFdLFs2LDcsImpfMiIsMV0sWzEsNCwiZ18xIiwxXSxbMyw0LCJnXzIiLDFdLFsxLDIsInNfMSIsMV0sWzMsNiwic18yIiwxXSxbMCwxLCJxXzEiLDFdLFswLDMsInFfMiIsMV1d
    #context align(center, diagram({
      node((0, 0), [$X$])
      node((1, 0), [$Z_1$])
      node((2, 0), [$X_1$])
      node((0, 1), [$Z_2$])
      node((1, 1), [$ol(X)$])
      node((2, 1), [$ol(X)_1$])
      node((0, 2), [$X_2$])
      node((1, 2), [$ol(X)_2$])
      node((2, 2), [$Y$])
      edge((2, 1), (2, 2), [$ol(f)_1$], label-side: center, "->")
      edge((1, 2), (2, 2), [$ol(f)_2$], label-side: center, "->")
      edge((1, 1), (2, 1), [$ol(p)_1$], label-side: center, "->")
      edge((1, 1), (1, 2), [$ol(p)_2$], label-side: center, "->")
      edge((2, 0), (2, 1), [$j_1$], label-side: center, "->")
      edge((0, 2), (1, 2), [$j_2$], label-side: center, "->")
      edge((1, 0), (1, 1), [$g_1$], label-side: center, "->")
      edge((0, 1), (1, 1), [$g_2$], label-side: center, "->")
      edge((1, 0), (2, 0), [$s_1$], label-side: center, "->")
      edge((0, 1), (0, 2), [$s_2$], label-side: center, "->")
      edge((0, 0), (1, 0), [$q_1$], label-side: center, "->")
      edge((0, 0), (0, 1), [$q_2$], label-side: center, "->")
      edge((0, 0), (1, 1), [$q$], label-side: center, "->")
      edge((1, 1), (2, 2), [$ol(f)$], label-side: center, "->")
    }, crossing-fill: thm-box-curr-color()))

    By Step 1, the Kunneth in the lower left square of this diagram is symmetric. Thus by @kunneth-3x3-and-symmetry, the Kunneth map is compatible with this $3 times 3$ diagram. In other words, with $K_1, K_2$ being the Kunneth of the upper left and lower right square respectively, the Kunneth of the original square becomes: 
    $
      R f_(1,!) cal(K)_1 Lotimes R f_(2,!) cal(K)_2 &-->^(K_2) R ol(f)_! (ol(p)_1^(-1) j_(1,!) cal(K)_1 Lotimes ol(p)_2^(-1) j_(2,!) cal(K)_1) \
      &-->^BC R ol(f)_! (g_(1,!) s_1^(-1) cal(K)_1 Lotimes g_(2,!) s_2^(-1) cal(K)_1) \
      &-->^(K_1) R f_! (p_1^(-1) cal(K)_1 Lotimes p_2^(-1) cal(K)_2)
    $ 
    Thus, it suffices to prove that the Kunneth maps $K_1, K_2$ for the two small squares are symmetric. The upper left square has its horizontal morphisms being open immersions, so $K_1$ is symmetric by Step 1. On the other hand, $K_2$ is symmetric because @proper-kunneth-alt-desc gave an alternative description of the Kunneth map that is symmetric. 

    We have thus shown that the Kunneth map is always symmetric. 

  - By Step 2, the Kunneth map is always symmetric. Thus @kunneth-3x3-and-symmetry implies that the Kunneth map is always compatible with $3 times 3$ Cartesian diagrams.

  All that remains to be proved is associativity w.r.t. triple products. We only sketch this proof here. The construction in @proper-kunneth-alt-desc is also associative, so the case in which all morphisms are proper is done. 
  
  For a general triple product, we may pick compactifications $X_i ->^(j_i) ol(X)_i ->^(ol(f)_i) Y, i=1,2,3$. Now everything we will need when an open immersion occurs is automatic, for we may base change to a geometric point and make the open immersion the identity, and make the statement trivial. Then the $3 times 3$ compatibilities and other compatibility statements will conclude the proof based on the open immersion case and the proper case. 
  
  (The main reason that I didn't want to fully write down this part of the proof is that it requires constructing a $3 times 3 times 3$ cubical diagram, consisting of 27 nodes and 54 edges. You can probably infer why I chose to skip this part of the proof.)
  // - Compatibility for horizontal concatenation requires that for a Cartesian diagram: #h(1fr)
  //   // https://q.uiver.app/#r=typst&q=WzAsNixbMCwwLCJYJyJdLFswLDEsIlgnXzEiXSxbMSwwLCJYIl0sWzEsMSwiWF8xIl0sWzIsMCwiWF8yIl0sWzIsMSwiWSJdLFszLDUsImZfMSIsMl0sWzEsMywiZyIsMl0sWzIsMywicF8xIiwxXSxbMiw0LCJwXzIiXSxbNCw1LCJmXzIiXSxbMCwyLCJoXzIiXSxbMiw1LCJmIiwxXSxbMCwxLCJoXzEiLDJdLFswLDMsImgiLDFdXQ==
  //   #context align(center, diagram({
  //     node((0, 0), [$X'$])
  //     node((0, 1), [$X'_1$])
  //     node((1, 0), [$X$])
  //     node((1, 1), [$X_1$])
  //     node((2, 0), [$X_2$])
  //     node((2, 1), [$Y$])
  //     edge((1, 1), (2, 1), [$f_1$], label-side: right, "->")
  //     edge((0, 1), (1, 1), [$g$], label-side: right, "->")
  //     edge((1, 0), (1, 1), [$p_1$], label-side: center, "->")
  //     edge((1, 0), (2, 0), [$p_2$], label-side: left, "->")
  //     edge((2, 0), (2, 1), [$f_2$], label-side: left, "->")
  //     edge((0, 0), (1, 0), [$h_2$], label-side: left, "->")
  //     edge((1, 0), (2, 1), [$f$], label-side: center, "->")
  //     edge((0, 0), (0, 1), [$h_1$], label-side: right, "->")
  //     edge((0, 0), (1, 1), [$h$], label-side: center, "->")
  //   }, crossing-fill: thm-box-curr-color()))
  //   with $q: X' -> Y, q_2: X' -> X_2, g_1: X'_1 -> Y$ has the following two paths equal: 
  //   $
  //     R f_(1,!) R g_! cal(K)'_1 Lotimes_Lambda R f_(2,!) cal(K)_2 -->^K R f_! (p_1^(-1) R g_! cal(K)'_1 Lotimes_Lambda cal(K)_2) -->^BC R f_! (R h_(2,!) h_1^(-1) cal(K)'_1 Lotimes_Lambda cal(K)_2) -->^K 
  //   $
]

As an application of the Kunneth formula, we are now ready to compute the cohomology with proper support of $AA^d$ and $PP^d$. 

#proposition(name: <cohom-with-proper-supp-of-Ad-and-Pd>)[
  Let $k$ be a separably closed field, and $n in k^times$ be a natural number. Then: 

  + There are canonical isomorphisms: #h(1fr)
    $
      H^q_c (AA^d_k, ZZ\/n) cong cases(
        mu_n^(otimes -d) &\, q = 2d, 
        0 &\, #[otherwise]
      )
    $

  + There are canonical isomorphisms: #h(1fr)
    $
      H^q (PP^d_k, ZZ\/n) cong cases(
        mu_n^(otimes -j) &\, q = 2j\, 0 <= j <= d, 
        0 &\, #[otherwise]
      )
    $
]
#proof[
  (1) We first compute $H^q_c (AA^1_k, mu_n)$. By Grothendieck vanishing, it suffices to deal with $q = 0,1,2$. 
  
  Let $AA^1_k$ have compactification $AA^1_k ->^j PP^1_k -> Spec(k)$, and let $i: Spec(k) -> PP^1_k$ be the inclusion of $oo$. Then by the extension by zero triangle (@rf-lower-shriek-first-props (3)), we have a long exact sequence: 
  $
    0 &-> H^0_c (AA^1_k, mu_n) -> H^0 (PP^1_k, mu_n) -> H^0 (Spec(k), mu_n) \
    &-> H^1_c (AA^1_k, mu_n) -> underbrace(H^1 (PP^1_k, mu_n), 0) -> underbrace(H^1 (Spec(k), mu_n), 0) \
    &-> H^2_c (AA^1_k, mu_n) -> H^2 (PP^1_k, mu_n) -> underbrace(H^2 (Spec(k), mu_n), 0) -> 0
  $
  Now: 

  - The map $H^0 (PP^1_k, mu_n) -> H^0 (Spec(k), mu_n)$ is the identity $mu_n -> mu_n$. Hence, #h(1fr)
    $
      H^0_c (AA^1_k, mu_n) = ker(H^0 (PP^1_k, mu_n) -> H^0 (Spec(k), mu_n)) = 0 \
      H^1_c (AA^1_k, mu_n) = coker(H^0 (PP^1_k, mu_n) -> H^0 (Spec(k), mu_n)) = 0
    $

  - There is a canonical isomorphism $H^2_c (AA^1_k, mu_n) cong H^2 (PP^1_k, mu_n) cong ZZ\/n$, where the last step is due to @cohom-of-proj-curve (1). 

  Hence, we are done computing $H^q_c (AA^1_k, mu_n)$ and have obtained a canonical isomorphism: 
  $
    R Gamma_c (AA^1_k, mu_n) cong ZZ\/n [-2]
  $
  Tensoring with $mu_n^(otimes -1)$ and using the projection formula, this gives a canonical isomorphism: 
  $
    R Gamma_c (AA^1_k, ul(ZZ\/n)) cong mu_n^(otimes -1)[-2]
  $
  Now $AA^d_k cong underbrace(AA^1_k times_k dots.c times_k AA^1_k, d#[ copies])$ is a $d$-fold fiber product with projections $p_j: AA^d_k -> AA^1_k$, and so we have: 
  $
    R Gamma_c (AA^d_k, ul(ZZ\/n)) &cong R Gamma_c (AA^d_k, p_1^(-1) ul(ZZ\/n) Lotimes_(ZZ\/n) dots.c Lotimes_(ZZ\/n) p_d^(-1) ul(ZZ\/n)) \
    &cong underbrace(R Gamma_c (AA^1_k, ul(ZZ\/n)) Lotimes_(ZZ\/n) dots.c Lotimes_(ZZ\/n) R Gamma_c (AA^1_k, ul(ZZ\/n)), d#[ copies]) #[by Kunneth formula] \
    &cong underbrace(mu_n^(otimes -1)[-2] Lotimes_(ZZ\/n) dots.c Lotimes_(ZZ\/n) mu_n^(otimes -1)[-2], d#[ copies]) #[by Kunneth formula] \
    &cong mu_n^(otimes -d)[-2d]
  $
  We are thereby done. 

  (2) We perform induction on $d$. The case $d=1$ is just @cohom-of-proj-curve (1). Now $PP^d_k$ has a pair of complementary open and closed immersions: 
  $
    j: AA^d_k -> PP^d_k, i: PP^(d-1)_k -> PP^d_k
  $
  Thus, we have a long exact sequence: 
  $
    dots.c -> H^(q-1) (PP^(d-1)_k, ul(ZZ\/n)) -> H^q_c (AA^d_k, ul(ZZ\/n)) -> H^q (PP^d_k, ul(ZZ\/n)) -> H^q (PP^(d-1)_k, ul(ZZ\/n)) -> H^(q+1) (AA^d_k, ul(ZZ\/n)) -> dots.c
  $

  - When $q <= 2d-2$, $H^q_c (AA^d_k, ul(ZZ\/n)) = H^(q+1)_c (AA^d_k, ul(ZZ\/n)) = 0$ by (1). Thus, we have a canonical isomorphism: 
    $
      H^q (PP^d_k, ul(ZZ\/n)) cong H^q (PP^(d-1)_k, ul(ZZ\/n))
    $
    and the desired result follows by the inductive hypothesis on $PP^(d-1)_k$. 

  - For $q = 2d-1$, $H^(2d-1)_c (AA^d_k, ul(ZZ\/n)) = 0$ and $H^(2d-1) (PP^(d-1)_k, ul(ZZ\/n)) = 0$. Thus, 
    $
      H^(2d-1) (PP^d_k, ul(ZZ\/n)) = 0
    $

  - For $q = 2d$, $H^(2d-1) (PP^(d-1)_k, ul(ZZ\/n)) = 0$ and $H^(2d) (PP^(d-1)_k, ul(ZZ\/n)) = 0$. Thus, we have a canonical isomorphism: 
    $
      H^(2d) (PP^d_k, ul(ZZ\/n)) cong H^(2d)_c (AA^d_k, ul(ZZ\/n)) cong mu_n^(otimes -d)
    $

  We are thereby done. 
]
