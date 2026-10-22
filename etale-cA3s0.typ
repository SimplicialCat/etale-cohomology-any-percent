#import "void-import.typ": *

In this appendix, we introduce an abstract and purely categorical construction that will be used repeatedly. We will also prove the naturality of this construction, so that the naturality of many concrete constructions in etale cohomology follows. 

The proofs in this appendix are purely formal and categorical, so you are encouraged to skip them. 

#notation[
  Given a pair of adjoint functors $g^L tack.l g$, we denote the unit and counit by: 
  $
    u_g: id -> g g^L \
    eta_g: g^L g -> id
  $
  Given functors: 
  $
    f: cal(C) -> cal(D), g: cal(A) -> cal(B)\
    h_(1,2): cal(B) -> cal(C)
  $
  and a natural transformation $q: h_1 -> h_2$, we use the notation $f q g$ to denote the natural transformation $f h_1 g -> f h_2 g$, obtained by lifting $q$ through the functors $f,g$. 

  Thus, as an example, the adjunction identities may be denoted as: 
  $
    eta_g g^L compose g^L u_g = id \
    g eta_g compose u_g g = id
  $
  and the naturality of the unit/counit may be expressed as: Given a natural transformation $q: f_1 -> f_2$, 
  $
    q compose eta_g f_1 = eta_g f_2 compose g^L g q \
    u_g f_2 compose q = g g^L q compose u_g f_1
  $
]

#definition(name: <bcbc-defn>)[
  Suppose that we have functors between categories: 
  // https://q.uiver.app/#r=typst&q=WzAsNCxbMCwwLCJjYWwoQylfMSJdLFswLDEsImNhbChDKV8yIl0sWzEsMCwiY2FsKEQpXzEiXSxbMSwxLCJjYWwoRClfMiJdLFsxLDMsImYiLDJdLFswLDIsImYnIl0sWzIsMywiZyJdLFswLDEsImcnIiwyXSxbMSwyLCJ0IiwxXV0=
  #context align(center, diagram({
    node((-1, -1), [$cal(C)_1$])
    node((-1, 0), [$cal(C)_2$])
    node((0, -1), [$cal(D)_1$])
    node((0, 0), [$cal(D)_2$])
    edge((-1, 0), (0, 0), [$f$], label-side: right, "->")
    edge((-1, -1), (0, -1), [$f'$], label-side: left, "->")
    edge((0, -1), (0, 0), [$g$], label-side: left, "->")
    edge((-1, -1), (-1, 0), [$g'$], label-side: right, "->")
    edge((-0.7, -0.3), (-0.3, -0.7), [$t$], label-side: center, "=>")
  }, crossing-fill: thm-box-curr-color()))
  where $t: f g' -> g f'$ is a natural transformation, and $g, g'$ have left adjoints $g^L, g'^L$ respectively. We define the *Beck-Chevalley base change* along this diagram to be the natural transformation: 
  $
    g^L f -->^(g^L f u_(g')) g^L f g' g'^L -->^(g^L t g'^L) g^L g f' g'^L -->^(eta_g f' g'^L) f' g'^L
  $
  and denote it by $BC(f,f',g,g',t)$. 
]

#proposition(name: <bcbc-horizontal-concat>)[
  The Beck-Chevalley base change is compatible with horizontal concatenation of diagrams. That is, given a diagram: 
  // https://q.uiver.app/#r=typst&q=WzAsNixbMCwwLCJjYWwoQylfMSJdLFswLDEsImNhbChDKV8yIl0sWzEsMCwiY2FsKEQpXzEiXSxbMSwxLCJjYWwoRClfMiJdLFsyLDAsImNhbChFKV8xIl0sWzIsMSwiY2FsKEUpXzIiXSxbMSwzLCJoIiwyXSxbMCwyLCJoJyJdLFsyLDMsImdfMiIsMV0sWzAsMSwiZ18xIiwxXSxbMSwyLCJzIiwxXSxbMiw0LCJmJyJdLFszLDUsImYiLDJdLFs0LDUsImdfMyIsMV0sWzMsNCwidCIsMV1d
  #context align(center, diagram({
    node((-1, -1), [$cal(C)_1$])
    node((-1, 0), [$cal(C)_2$])
    node((0, -1), [$cal(D)_1$])
    node((0, 0), [$cal(D)_2$])
    node((1, -1), [$cal(E)_1$])
    node((1, 0), [$cal(E)_2$])
    edge((-1, 0), (0, 0), [$h$], label-side: right, "->")
    edge((-1, -1), (0, -1), [$h'$], label-side: left, "->")
    edge((0, -1), (0, 0), [$g_2$], label-side: center, "->")
    edge((-1, -1), (-1, 0), [$g_1$], label-side: center, "->")
    edge((-0.7, -0.3), (-0.3, -0.7), [$s$], label-side: center, "=>")
    edge((0, -1), (1, -1), [$f'$], label-side: left, "->")
    edge((0, 0), (1, 0), [$f$], label-side: right, "->")
    edge((1, -1), (1, 0), [$g_3$], label-side: center, "->")
    edge((0.3, -0.3), (0.7, -0.7), [$t$], label-side: center, "=>")
  }, crossing-fill: thm-box-curr-color()))
  in which $g_i$ has left adjoint $g_i^L$, the composition of base changes along the two small squares: 
  $
    g_3^L f h -->^(BC(f,f',g_3,g_2,t)h) f'g_2^L h ->^(f'BC(h,h',g_2,g_1,s)) f'h'g_1^L
  $
  is exactly the base change along the larger rectangle, i.e: 
  $
    f'BC(h,h',g_2,g_1,s) compose BC(f,f',g_3,g_2,t)h = BC(f h, f'h', g_3, g_1, t h' compose f s)
  $
]
#proof[
  #show math.equation: set block(breakable: true)
  Let the adjunction unit/counit of each $g_i$ be denoted $u_i, eta_i$, respectively. 

  Denote by: 
  $
    B_f := BC(f,f',g_3,g_2,t) = eta_3 f' g_2^L compose g_3^L t g_2^L compose g_3^L f u_2 \
    B_h := BC(h,h',g_2,g_1,s) = eta_2 h' g_1^L compose g_2^L s g_1^L compose g_2^L h u_1
  $
  and we intend to prove: 
  $
    f' B_h compose B_f h = BC(f h, f'h', g_3, g_1, t h' compose f s)
  $
  - By naturality of the counit, #h(1fr)
    $
      f' B_h compose eta_3 g' g_2^L h = eta_3 f' h' g_1^L compose g_3^L g_3 f' B_h
    $
    so it suffices to prove that: 
    $
      g_3^L g_3 f' B_h compose g_3^L t g_2^L h compose g_3^L f u_2 h = g_3^L t h' g_1^L compose g_3^L f s g_1^L compose g_3^L f h u_1
    $
    lifting $g_3^L$ out, it suffices to prove that: 
    $
      g_3 f' B_h compose t g_2^L h compose f u_2 h = t h' g_1^L compose f s g_1^L compose f h u_1
    $

  - Write $a = eta_2 h' g_1^L compose g_2^L s g_1^L$ so that $B_h = a compose g_2^L h u_1$, 
    $
      & g_3 f' B_h compose t g_2^L h compose f u_2 h \
      =& g_3 f' a compose g_3 f' g_2^L h u_1 compose t g_2^L h compose f u_2 h \
      =& g_3 f' a compose t g_2^L h g_1 g_1^L compose f g_2 g_2^L h u_1 compose f u_2 h \
      & #[by naturality of $t: f g_2 -> g_3 f'$ w.r.t. $g_2^L h u_1: g_2^L h -> g_2^L h g_1 g_1^L$] \
      =& g_3 f' a compose t g_2^L h g_1 g_1^L compose f (g_2 g_2^L h u_1 compose u_2 h) \
      =& g_3 f' a compose t g_2^L h g_1 g_1^L compose f (u_2 h g_1 g_1^L compose h u_1) \
      & #[by naturality of $u_2: id -> g_2 g_2^L$ w.r.t. $h u_1: h -> h g_1 g_1^L$] \
      =& t h' g_1^L compose f g_2 a compose f (u_2 h g_1 g_1^L compose h u_1)\ 
      & #[by naturality of $t: f g_2 -> g_3 f'$ w.r.t. $a: g_2^L h g_1 g_1^L -> h' g_1^L$] \
      =& t h' g_1^L compose f (g_2 a compose u_2 h g_1 g_1^L) compose f h u_1
    $
    On the other hand, the desired RHS is $t h' g_1^L compose f s g_1^L compose f h u_1$. Therefore, it suffices to prove that: 
    $
      g_2 a compose u_2 h g_1 g_1^L = s g_1^L
    $
  
  - Now check: 
    $
      & g_2 a compose u_2 h g_1 g_1^L \
      =& g_2 eta_2 h' g_1^L compose g_2 g_2^L s g_1^L compose u_2 h g_1 g_1^L \
      =& g_2 eta_2 h' g_1^L compose u_2 g_2 h' g_1^L compose s g_1^L \
      & #[by naturality of $u_2: id -> g_2 g_2^L$ w.r.t. $s g_1^L: h g_1 g_1^L -> g_2 h' g_1^L$] \
      =& (g_2 eta_2 compose u_2 g_2) h' g_1^L compose s g_1^L \
      =& s g_1^L \
      & #[by the adjunction identity $g_2 eta_2 compose u_2 g_2 = id$]
    $
  
  We are thereby done. 

  More intuitively, this proof is summarized in the following commutative diagram: 
  // https://q.uiver.app/#r=typst&q=WzAsMjUsWzAsMCwiZ18zXkwgZiBoIl0sWzAsMiwiZ18zXkwgZiBoIl0sWzAsNiwiZ18zXkwgZiBoIl0sWzYsMCwiZicgZ18yXkwgaCJdLFsxMCwwLCJmJyBoJyBnXzFeTCJdLFs2LDIsImYnIGdfMl5MIGgiXSxbMTAsMiwiZicgaCcgZ18xXkwiXSxbMiwzLCJnXzNeTCBmIGdfMiBnXzJeTCBoIl0sWzQsMywiZ18zXkwgZ18zIGYnIGdfMl5MIGgiXSxbOCwyLCJmJ2dfMl5MIGggZ18xIGdfMV5MIl0sWzcsNCwiZ18zXkwgZ18zIGYnIGdfMl5MIGggZ18xIGdfMV5MIl0sWzksNCwiZ18zXkwgZ18zIGYnIGgnIGdfMV5MIl0sWzQsNSwiZ18zXkwgZiBnXzIgZ18yXkwgaCBnXzEgZ18xXkwiXSxbMiw2LCJnXzNeTCBmIGggZ18xIGdfMV5MIl0sWzEwLDYsImYnaCdnXzFeTCJdLFs4LDYsImdfM15MIGdfMyBmJyBoJyBnXzFeTCJdLFs2LDYsImdfM15MIGYgZ18yIGgnIGdfMV5MIl0sWzUsOCwiZ18zXkwgZiBnXzIgZ18yXkwgZ18yIGgnIGdfMV5MIl0sWzMsOSwiZ18zXkwgZiBnXzIgaCcgZ18xXkwiXSxbNiwxMCwiZ18zXkwgZiBnXzIgaCcgZ18xXkwiXSxbNCwxMCwiZ18zXkwgZiBnXzIgaCcgZ18xXkwiXSxbMCwxMCwiZ18zXkwgZiBoIl0sWzEwLDEwLCJmJ2gnZ18xXkwiXSxbOCwxMCwiZ18zXkwgZ18zIGYnIGgnIGdfMV5MIl0sWzIsMTAsImdfM15MIGYgaCBnXzEgZ18xXkwiXSxbMCwxLCIiLDAseyJzdHlsZSI6eyJib2R5Ijp7Im5hbWUiOiJkYXNoZWQifSwiaGVhZCI6eyJuYW1lIjoibm9uZSJ9fX1dLFsxLDIsIiIsMCx7InN0eWxlIjp7ImJvZHkiOnsibmFtZSI6ImRhc2hlZCJ9LCJoZWFkIjp7Im5hbWUiOiJub25lIn19fV0sWzMsNSwiIiwwLHsic3R5bGUiOnsiYm9keSI6eyJuYW1lIjoiZGFzaGVkIn0sImhlYWQiOnsibmFtZSI6Im5vbmUifX19XSxbNCw2LCIiLDAseyJzdHlsZSI6eyJib2R5Ijp7Im5hbWUiOiJkYXNoZWQifSwiaGVhZCI6eyJuYW1lIjoibm9uZSJ9fX1dLFswLDMsIkJfZiBoIiwxXSxbMyw0LCJnJyBCX2giLDFdLFsxLDcsImdfM15MIGYgdV8yIGgiLDFdLFs3LDgsImdfM15MIHQgZ18yXkwgaCIsMV0sWzgsNSwiZXRhXzMgZicgZ18yXkwgaCIsMV0sWzUsOSwiZicgZ18yXkwgaCB1XzEiLDFdLFs5LDYsImYnIGEiLDFdLFs4LDEwLCJnXzNeTCBnXzMgZicgZ18yXkwgaCB1XzEiLDFdLFsxMCw5LCJldGFfMyBmJyBnXzJeTCBoIGdfMSBnXzFeTCIsMV0sWzEwLDExLCJnXzNeTCBnXzMgZicgYSIsMV0sWzExLDYsImV0YV8zIGYnIGgnIGdfMV5MIiwxXSxbNywxMiwiZ18zXkwgZiBnXzIgZ1
  // 8yXkwgaCB1XzEiLDFdLFsxMiwxMCwiZ18zXkwgdCBnXzJeTCBoIGdfMSBnXzFeTCIsMV0sWzIsMTMsImdfM15MIGYgaCB1XzEiLDFdLFsxMywxMiwiZ18zXkwgZiB1XzIgaCBnXzEgZ18xXkwiLDFdLFs2LDE0LCIiLDEseyJzdHlsZSI6eyJib2R5Ijp7Im5hbWUiOiJkYXNoZWQifSwiaGVhZCI6eyJuYW1lIjoibm9uZSJ9fX1dLFsxMSwxNSwiIiwxLHsic3R5bGUiOnsiYm9keSI6eyJuYW1lIjoiZGFzaGVkIn0sImhlYWQiOnsibmFtZSI6Im5vbmUifX19XSxbMTUsMTQsImV0YV8zIGYnIGgnIGdfMV5MIiwxXSxbMTIsMTYsImdfM15MIGYgZ18yIGEiLDFdLFsxNiwxNSwiZ18zXkwgdCBoJyBnXzFeTCIsMV0sWzEyLDE3LCJnXzNeTCBmIGdfMiBnXzJeTCBzIGdfMV5MIiwxXSxbMTcsMTYsImdfM15MIGYgZ18yIGV0YV8yIGgnIGdfMV5MIiwxXSxbMTMsMTgsImdfM15MIGYgcyBnXzFeTCIsMV0sWzE4LDE3LCJnXzNeTCBmIHVfMiBnXzIgaCcgZ18xXkwiLDFdLFsxOCwyMCwiIiwxLHsic3R5bGUiOnsiYm9keSI6eyJuYW1lIjoiZGFzaGVkIn0sImhlYWQiOnsibmFtZSI6Im5vbmUifX19XSxbMTYsMTksIiIsMSx7InN0eWxlIjp7ImJvZHkiOnsibmFtZSI6ImRhc2hlZCJ9LCJoZWFkIjp7Im5hbWUiOiJub25lIn19fV0sWzIwLDE5LCIiLDEseyJzdHlsZSI6eyJib2R5Ijp7Im5hbWUiOiJkYXNoZWQifSwiaGVhZCI6eyJuYW1lIjoibm9uZSJ9fX1dLFsyLDIxLCIiLDEseyJzdHlsZSI6eyJib2R5Ijp7Im5hbWUiOiJkYXNoZWQifSwiaGVhZCI6eyJuYW1lIjoibm9uZSJ9fX1dLFsxNSwyMywiIiwxLHsic3R5bGUiOnsiYm9keSI6eyJuYW1lIjoiZGFzaGVkIn0sImhlYWQiOnsibmFtZSI6Im5vbmUifX19XSxbMTQsMjIsIiIsMSx7InN0eWxlIjp7ImJvZHkiOnsibmFtZSI6ImRhc2hlZCJ9LCJoZWFkIjp7Im5hbWUiOiJub25lIn19fV0sWzEzLDI0LCIiLDEseyJzdHlsZSI6eyJib2R5Ijp7Im5hbWUiOiJkYXNoZWQifSwiaGVhZCI6eyJuYW1lIjoibm9uZSJ9fX1dLFsyMSwyNCwiZ18zXkwgZiBoIHVfMSIsMV0sWzI0LDIwLCJnXzNeTCBmIHMgZ18xXkwiLDFdLFsxOSwyMywiZ18zXkwgdCBoJyBnXzFeTCIsMV0sWzIzLDIyLCJldGFfMyBmJyBoJyBnXzFeTCIsMV0sWzIxLDIyLCJvcChcIkJDXCIpKGYgaCwgZidoJywgZ18zLCBnXzEsIHQgaCcgY29tcG9zZSBmIHMpIiwxLHsiY3VydmUiOjV9XV0=
  #context snap-width(align(center, diagram({
    node((0, 0), [$g_3^L f h$])
    node((0, 2), [$g_3^L f h$])
    node((0, 6), [$g_3^L f h$])
    node((6, 0), [$f' g_2^L h$])
    node((10, 0), [$f' h' g_1^L$])
    node((6, 2), [$f' g_2^L h$])
    node((10, 2), [$f' h' g_1^L$])
    node((2, 3), [$g_3^L f g_2 g_2^L h$])
    node((4, 3), [$g_3^L g_3 f' g_2^L h$])
    node((8, 2), [$f'g_2^L h g_1 g_1^L$])
    node((7, 4), [$g_3^L g_3 f' g_2^L h g_1 g_1^L$])
    node((9, 4), [$g_3^L g_3 f' h' g_1^L$])
    node((4, 5), [$g_3^L f g_2 g_2^L h g_1 g_1^L$])
    node((2, 6), [$g_3^L f h g_1 g_1^L$])
    node((10, 6), [$f'h'g_1^L$])
    node((8, 6), [$g_3^L g_3 f' h' g_1^L$])
    node((6, 6), [$g_3^L f g_2 h' g_1^L$])
    node((5, 8), [$g_3^L f g_2 g_2^L g_2 h' g_1^L$])
    node((3, 9), [$g_3^L f g_2 h' g_1^L$])
    node((6, 10), [$g_3^L f g_2 h' g_1^L$])
    node((4, 10), [$g_3^L f g_2 h' g_1^L$])
    node((0, 10), [$g_3^L f h$])
    node((10, 10), [$f'h'g_1^L$])
    node((8, 10), [$g_3^L g_3 f' h' g_1^L$])
    node((2, 10), [$g_3^L f h g_1 g_1^L$])

    node((4, 1.5), text(fill: red, $arrow.ccw_D$))
    node((8, 1), text(fill: red, $arrow.ccw_D$))
    node((6.5, 3), text(fill: red, $arrow.ccw_N$))
    node((8.5, 3), text(fill: red, $arrow.ccw_N$))
    node((4, 4), text(fill: red, $arrow.ccw_N$))
    node((2, 5), text(fill: red, $arrow.ccw_N$))
    node((7, 5), text(fill: red, $arrow.ccw_N$))
    node((5, 6), text(fill: red, $arrow.ccw_D$))
    node((3.5, 7), text(fill: red, $arrow.ccw_N$))
    node((5, 9), text(fill: red, $arrow.ccw_U$))
    node((6, 11), text(fill: red, $arrow.ccw_D$))

    edge((0, 0), (0, 2), "=")
    edge((0, 2), (0, 6), "=")
    edge((6, 0), (6, 2), "=")
    edge((10, 0), (10, 2), "=")
    edge((0, 0), (6, 0), [$B_f h$], label-side: center, "->")
    edge((6, 0), (10, 0), [$g' B_h$], label-side: center, "->")
    edge((0, 2), (2, 3), [$g_3^L f u_2 h$], label-side: center, "->")
    edge((2, 3), (4, 3), [$g_3^L t g_2^L h$], label-side: center, "->")
    edge((4, 3), (6, 2), [$eta_3 f' g_2^L h$], label-side: center, "->")
    edge((6, 2), (8, 2), [$f' g_2^L h u_1$], label-side: center, "->")
    edge((8, 2), (10, 2), [$f' a$], label-side: center, "->")
    edge((4, 3), (7, 4), [$g_3^L g_3 f' g_2^L h u_1$], label-side: center, "->")
    edge((7, 4), (8, 2), [$eta_3 f' g_2^L h g_1 g_1^L$], label-side: center, "->")
    edge((7, 4), (9, 4), [$g_3^L g_3 f' a$], label-side: center, "->")
    edge((9, 4), (10, 2), [$eta_3 f' h' g_1^L$], label-side: center, "->")
    edge((2, 3), (4, 5), [$g_3^L f g_2 g_2^L h u_1$], label-side: center, "->")
    edge((4, 5), (7, 4), [$g_3^L t g_2^L h g_1 g_1^L$], label-side: center, "->")
    edge((0, 6), (2, 6), [$g_3^L f h u_1$], label-side: left, "->", bend: 30deg)
    edge((2, 6), (4, 5), [$g_3^L f u_2 h g_1 g_1^L$], label-side: center, "->")
    edge((10, 2), (10, 6), "=")
    edge((9, 4), (8, 6), "=")
    edge((8, 6), (10, 6), [$eta_3 f' h' g_1^L$], label-side: center, "->")
    edge((4, 5), (6, 6), [$g_3^L f g_2 a$], label-side: center, "->")
    edge((6, 6), (8, 6), [$g_3^L t h' g_1^L$], label-side: center, "->")
    edge((4, 5), (5, 8), [$g_3^L f g_2 g_2^L s g_1^L$], label-side: center, "->")
    edge((5, 8), (6, 6), [$g_3^L f g_2 eta_2 h' g_1^L$], label-side: center, "->")
    edge((2, 6), (3, 9), [$g_3^L f s g_1^L$], label-side: center, "->")
    edge((3, 9), (5, 8), [$g_3^L f u_2 g_2 h' g_1^L$], label-side: center, "->")
    // edge((0, 6), (2, 6), [$g_3^L f u_2 h$], label-side: left, "->", bend: 18deg)
    // edge((0, 10), (2, 10), [$g_3^L f u_2 h$], label-side: center, "->")
    edge((3, 9), (4, 10), "=")
    edge((6, 6), (6, 10), "=")
    edge((4, 10), (6, 10), "=")
    edge((0, 6), (0, 10), "=")
    edge((8, 6), (8, 10), "=")
    edge((10, 6), (10, 10), "=")
    edge((2, 6), (2, 10), "=")
    edge((0, 10), (2, 10), [$g_3^L f h u_1$], label-side: left, "->", bend: 30deg)
    edge((2, 10), (4, 10), [$g_3^L f s g_1^L$], label-side: center, "->")
    edge((6, 10), (8, 10), [$g_3^L t h' g_1^L$], label-side: center, "->")
    edge((8, 10), (10, 10), [$eta_3 f' h' g_1^L$], label-side: center, "->")
    edge((0, 10), "dd,rrrrrrrrrr,uu", [$BC(f h, f'h', g_3, g_1, t h' compose f s)$], label-side: center, "->")
  }, spacing: 1.5em, crossing-fill: thm-box-curr-color())))
  where: 
  - $arrow.ccw_D$ in a cell indicates that this cell commutes by definition; 

  - $arrow.ccw_N$ in a cell indicates that this cell commutes as a naturality square; 

  - $arrow.ccw_U$ in a cell indicates that this cell commutes by an adjunction identity; 

  - An empty cell commutes automatically. 
]

#proposition(name: <bcbc-vertical-concat>)[
  The Beck-Chevalley base change is compatible with horizontal concatenation of diagrams. That is, given a diagram: 
  // https://q.uiver.app/#r=typst&q=WzAsNixbMCwwLCJjYWwoQylfMSJdLFswLDEsImNhbChDKV8yIl0sWzAsMiwiY2FsKEMpXzMiXSxbMSwwLCJjYWwoRClfMSJdLFsxLDEsImNhbChEKV8yIl0sWzEsMiwiY2FsKEQpXzMiXSxbMiw1LCJmXzMiLDJdLFsxLDQsImZfMiIsMV0sWzAsMywiZl8xIl0sWzQsNSwiZ18xIl0sWzMsNCwiZ18yIl0sWzEsMiwiZ18zIiwyXSxbMCwxLCJnXzQiLDJdLFsyLDQsInQiLDFdLFsxLDMsInMiLDFdXQ==
  #context align(center, diagram({
    node((-1, -1), [$cal(C)_1$])
    node((-1, 0), [$cal(C)_2$])
    node((-1, 1), [$cal(C)_3$])
    node((0, -1), [$cal(D)_1$])
    node((0, 0), [$cal(D)_2$])
    node((0, 1), [$cal(D)_3$])
    edge((-1, 1), (0, 1), [$f_3$], label-side: right, "->")
    edge((-1, 0), (0, 0), [$f_2$], label-side: center, "->")
    edge((-1, -1), (0, -1), [$f_1$], label-side: left, "->")
    edge((0, 0), (0, 1), [$g_1$], label-side: left, "->")
    edge((0, -1), (0, 0), [$g_2$], label-side: left, "->")
    edge((-1, 0), (-1, 1), [$g_3$], label-side: right, "->")
    edge((-1, -1), (-1, 0), [$g_4$], label-side: right, "->")
    edge((-0.7, 0.7), (-0.3, 0.3), [$t$], label-side: center, "=>")
    edge((-0.7, -0.3), (-0.3, -0.7), [$s$], label-side: center, "=>")
  }, label-size: 0.8em, crossing-fill: thm-box-curr-color()))
  in which $g_i$ has left adjoint $g_i^L$, the composition of base changes along the two small squares: 
  $
    g_2^L g_1^L f_3 -->^(g_2^L BC(f_3, f_2, g_1, g_3, t)) g_2^L f_2 g_3^L ->^(BC(f_2, f_1, g_2, g_4, s) g_3^L) f_1 g_4^L g_3^L
  $
  is exactly the base change along the larger rectangle, i.e: 
  $
    BC(f_2, f_1, g_2, g_4, s) g_3^L compose g_2^L BC(f_3, f_2, g_1, g_3, t) = BC(f_3, f_1, g_1 g_2, g_3 g_4, g_1 s compose t g_4)
  $
]
#proof[
  #show math.equation: set block(breakable: true)
  Let the adjunction unit/counit of each $g_i$ be denoted $u_i, eta_i$, respectively. Compute: 
  $
    & BC(f_2, f_1, g_2, g_4, s) g_3^L compose g_2^L BC(f_3, f_2, g_1, g_3, t) \
    =& eta_2 f_1 g_4^L g_3^L compose g_2^L s g_4^L g_3^L compose g_2^L f_2 u_4 g_3^L compose g_2^L eta_1 f_2 g_3^L compose g_2^L g_1^L t g_3^L compose g_2^L g_1^L f_3 u_3 \
    =& eta_2 f_1 g_4^L g_3^L compose g_2^L s g_4^L g_3^L compose g_2^L (f_2 u_4 g_3^L compose eta_1 f_2 g_3^L) compose g_2^L g_1^L t g_3^L compose g_2^L g_1^L f_3 u_3 \
    =& eta_2 f_1 g_4^L g_3^L compose g_2^L s g_4^L g_3^L compose g_2^L (eta_1 f_2 g_4 g_4^L g_3^L compose g_1^L g_1 f_2 u_4 g_3^L) compose g_2^L g_1^L t g_3^L compose g_2^L g_1^L f_3 u_3 \
    & #[by naturality of $eta_1: id -> g_1 g_1^L$ w.r.t. $f_2 u_4 g_3^L: f_2 g_3^L -> f_2 g_3 g_4^L g_3^L$] \
    =& eta_2 f_1 g_4^L g_3^L compose g_2^L (s compose eta_1 f_2 g_4) g_4^L g_3^L compose g_2^L g_1^L (g_1 f_2 u_4 compose t) g_3^L compose g_2^L g_1^L f_3 u_3 \
    =& eta_2 f_1 g_4^L g_3^L compose g_2^L (eta_1 g_2 f_1 compose g_1^L g_1 s) g_4^L g_3^L compose g_2^L g_1^L (t g_4 g_4^L compose f_3 g_3 u_4) g_3^L compose g_2^L g_1^L f_3 u_3 \
    & #[by naturality of $s: f_2 g_4 -> g_2 f_1$ w.r.t. $eta_1: g_1^L g_1 -> id$] \
    & #[and naturality of $t: f_3 g_3 -> g_1 f_2$ w.r.t. $u_4: id -> g_4 g_4^L$] \
    =& (eta_2 compose g_2^L eta_1 g_2) f_1 g_4^L g_3^L compose g_2^L g_1^L (g_1 s compose t g_4) g_4^L g_3^L compose g_2^L g_1^L f_3 (g_3 u_4 g_3^L compose u_3) \
    =& BC(f_3, f_1, g_1 g_2, g_3 g_4, g_1 s compose t g_4)
  $
  where the unit of $g_3 g_4 tack g_4^L g_3^L$ is $g_3 u_4 g_3^L compose u_3$, and the counit of $g_1 g_2 tack g_2^L g_1^L$ is $eta_2 compose g_2^L eta_1 g_2$. 

  More intuitively, this proof is summarized in the following commutative diagram: 
  // https://q.uiver.app/#r=typst&q=WzAsMTIsWzAsMCwiZ18yXkwgZ18xXkwgZl8zIl0sWzMsMCwiZ18yXkwgZl8yIGdfM15MIl0sWzYsMCwiZl8xIGdfNF5MIGdfM15MIl0sWzEsMiwiZ18yXkwgZ18xXkwgZl8zIGdfMyBnXzNeTCJdLFsyLDEsImdfMl5MIGdfMV5MIGdfMSBmXzIgZ18zXkwiXSxbNCwxLCJnXzJeTCBmXzIgZ180IGdfNF5MIGdfM15MIl0sWzUsMiwiZ18yXkwgZ18yIGZfMSBnXzReTCBnXzNeTCJdLFswLDMsImdfMl5MIGdfMV5MIGZfMyJdLFs2LDMsImdfMl5MIGdfMV5MIGZfMyJdLFszLDIsImdfMl5MIGdfMV5MIGdfMSBmXzIgZ180IGdfNF5MIGdfM15MIl0sWzIsMywiZ18yXkwgZ18xXkwgZl8zIGdfMyBnXzQgZ180XkwgZ18zXkwiXSxbNCwzLCJnXzJeTCBnXzFeTCBnXzEgZ18yIGZfMSBnXzReTCBnXzNeTCJdLFswLDcsIiIsMCx7InN0eWxlIjp7ImJvZHkiOnsibmFtZSI6ImRhc2hlZCJ9LCJoZWFkIjp7Im5hbWUiOiJub25lIn19fV0sWzIsOCwiIiwwLHsic3R5bGUiOnsiYm9keSI6eyJuYW1lIjoiZGFzaGVkIn0sImhlYWQiOnsibmFtZSI6Im5vbmUifX19XSxbMCwxLCJnXzJeTCBvcChcIkJDXCIpKGZfMyxmXzIsZ18xLGdfMyx0KSJdLFsxLDIsIm9wKFwiQkNcIikoZl8yLGZfMSxnXzIsZ180LHMpZ18zXkwiXSxbNywzLCJnXzJeTCBnXzFeTCBmXzMgdV8zIiwxXSxbMyw0LCJnXzJeTCBnXzFeTCB0IGdfM15MIiwxXSxbNCwxLCJnXzJeTCBldGFfMSBmXzIgZ18zXkwiLDFdLFsxLDUsImdfMl5MIGZfMiB1XzQgZ18zXkwiLDFdLFs1LDYsImdfMl5MIHMgZ180XkwgZ18zXkwiLDFdLFs2LDgsImV0YV8yIGZfMSBnXzReTCBnXzNeTCIsMV0sWzQsOSwiZ18yXkwgZ18xXkwgZ18xIGZfMiB1XzQgZ18zXkwiLDFdLFs5LDUsImdfMl5MIGV0YV8xIGZfMiBnXzQgZ180XkwgZ18zXkwiLDFdLFszLDEwLCJnXzJeTCBnXzFeTCBmXzMgZ18zIHVfNCBnXzNeTCIsMV0sWzEwLDksImdfMl5MIGdfMV5MIHQgZ180IGdfNF5MIGdfM15MIiwxXSxbOSwxMSwiZ18yXkwgZ18xXkwgZ18xIHMgZ180XkwgZ18zXkwiLDFdLFsxMSw2LCJnXzJeTCBldGFfMSBnXzIgZl8xIGdfNF5MIGdfM15MIiwxXSxbNywxMCwiZ18yXkwgZ18xXkwgZl8zIChnXzMgdV80IGdfM15MIGNvbXBvc2UgdV8zKSIsMix7ImN1cnZlIjozfV0sWzEwLDExLCJnXzJeTCBnXzFeTCAoZ18xIHMgY29tcG9zZSB0IGdfNCkgZ180XkwgZ18zXkwiLDIseyJjdXJ2ZSI6M31dLFsxMSw4LCIoZXRhXzIgY29tcG9zZSBnXzJeTCBldGFfMSBnXzIpIGZfMSBnXzReTCBnXzNeTCIsMix7ImN1cnZlIjo0fV1d
  #context snap-width(align(center, diagram({
    node((0, 0), [$g_2^L g_1^L f_3$])
    node((3, 0), [$g_2^L f_2 g_3^L$])
    node((6, 0), [$f_1 g_4^L g_3^L$])
    node((1, 2), [$g_2^L g_1^L f_3 g_3 g_3^L$])
    node((2, 1), [$g_2^L g_1^L g_1 f_2 g_3^L$])
    node((4, 1), [$g_2^L f_2 g_4 g_4^L g_3^L$])
    node((5, 2), [$g_2^L g_2 f_1 g_4^L g_3^L$])
    node((0, 3), [$g_2^L g_1^L f_3$])
    node((6, 3), [$g_2^L g_1^L f_3$])
    node((3, 2), [$g_2^L g_1^L g_1 f_2 g_4 g_4^L g_3^L$])
    node((2, 3), [$g_2^L g_1^L f_3 g_3 g_4 g_4^L g_3^L$])
    node((4, 3), [$g_2^L g_1^L g_1 g_2 f_1 g_4^L g_3^L$])
    edge((0, 0), (0, 3), "=")
    edge((6, 0), (6, 3), "=")
    edge((0, 0), (3, 0), [$g_2^L BC(f_3,f_2,g_1,g_3,t)$], label-side: left, "->")
    edge((3, 0), (6, 0), [$BC(f_2,f_1,g_2,g_4,s)g_3^L$], label-side: left, "->")
    edge((0, 3), (1, 2), [$g_2^L g_1^L f_3 u_3$], label-side: center, "->")
    edge((1, 2), (2, 1), [$g_2^L g_1^L t g_3^L$], label-side: center, "->")
    edge((2, 1), (3, 0), [$g_2^L eta_1 f_2 g_3^L$], label-side: center, "->")
    edge((3, 0), (4, 1), [$g_2^L f_2 u_4 g_3^L$], label-side: center, "->")
    edge((4, 1), (5, 2), [$g_2^L s g_4^L g_3^L$], label-side: center, "->")
    edge((5, 2), (6, 3), [$eta_2 f_1 g_4^L g_3^L$], label-side: center, "->")
    edge((2, 1), (3, 2), [$g_2^L g_1^L g_1 f_2 u_4 g_3^L$], label-side: center, "->")
    edge((3, 2), (4, 1), [$g_2^L eta_1 f_2 g_4 g_4^L g_3^L$], label-side: center, "->")
    edge((1, 2), (2, 3), [$g_2^L g_1^L f_3 g_3 u_4 g_3^L$], label-side: center, "->")
    edge((2, 3), (3, 2), [$g_2^L g_1^L t g_4 g_4^L g_3^L$], label-side: center, "->")
    edge((3, 2), (4, 3), [$g_2^L g_1^L g_1 s g_4^L g_3^L$], label-side: center, "->")
    edge((4, 3), (5, 2), [$g_2^L eta_1 g_2 f_1 g_4^L g_3^L$], label-side: center, "->")
    edge((0, 3), (2, 3), [$g_2^L g_1^L f_3 (g_3 u_4 g_3^L compose u_3)$], label-side: right, "->")
    edge((2, 3), (4, 3), [$g_2^L g_1^L (g_1 s compose t g_4) g_4^L g_3^L$], label-side: right, "->")
    edge((4, 3), (6, 3), [$(eta_2 compose g_2^L eta_1 g_2) f_1 g_4^L g_3^L$], label-side: right, "->")
    edge((0, 3), "d,rrrrrr,u", "->", $BC(f_3, f_1, g_1 g_2, g_3 g_4, g_1 s compose t g_4)$, label-side: right)

    node((1, 1), text(fill: red, $arrow.ccw_D$))
    node((5, 1), text(fill: red, $arrow.ccw_D$))
    node((3, 1), text(fill: red, $arrow.ccw_N$))
    node((2, 2), text(fill: red, $arrow.ccw_N$))
    node((4, 2), text(fill: red, $arrow.ccw_N$))
    node((3, 3.5), text(fill: red, $arrow.ccw_D$))
  }, crossing-fill: thm-box-curr-color())))

  where: 
  - $arrow.ccw_D$ in a cell indicates that this cell commutes by definition; 

  - $arrow.ccw_N$ in a cell indicates that this cell commutes as a naturality square; 

  - An empty cell commutes automatically. 
]

#proposition(name: <bcbc-naturality>)[
  Beck-Chevalley base change is compatible with natural transformations. That is, in a diagram: 
  // https://q.uiver.app/#r=typst&q=WzAsNCxbMCwwLCJjYWwoQylfMSJdLFswLDEsImNhbChDKV8yIl0sWzEsMSwiY2FsKEQpXzIiXSxbMSwwLCJjYWwoRClfMSJdLFswLDMsImYnIiwxLHsiY3VydmUiOjF9XSxbMSwyLCJmIiwxLHsiY3VydmUiOi0xfV0sWzAsMSwiaCciLDEseyJjdXJ2ZSI6MX1dLFszLDIsImciLDEseyJjdXJ2ZSI6MX1dLFswLDEsImcnIiwxLHsiY3VydmUiOi0xfV0sWzMsMiwiaCIsMSx7ImN1cnZlIjotMX1dLFswLDMsInBoaSciLDEseyJjdXJ2ZSI6LTF9XSxbMSwyLCJwaGkiLDEseyJjdXJ2ZSI6MX1dXQ==
  #context align(center, diagram({
    node((0, 0), [$cal(C)_1$])
    node((0, 1), [$cal(C)_2$])
    node((1, 1), [$cal(D)_2$])
    node((1, 0), [$cal(D)_1$])
    edge((0, 0), (1, 0), [$f'$], label-side: center, "->", bend: -36deg)
    edge((0, 1), (1, 1), [$f$], label-side: center, "->", bend: 36deg)
    edge((0, 0), (0, 1), [$h'$], label-side: center, "->", bend: -36deg)
    edge((1, 0), (1, 1), [$g$], label-side: center, "->", bend: -36deg)
    edge((0, 0), (0, 1), [$g'$], label-side: center, "->", bend: 36deg)
    edge((1, 0), (1, 1), [$h$], label-side: center, "->", bend: 36deg)
    edge((0, 0), (1, 0), [$phi'$], label-side: center, "->", bend: 36deg)
    edge((0, 1), (1, 1), [$phi$], label-side: center, "->", bend: -36deg)
    edge(..tune-2-mor-coords((0, 1), (1, 0)), "=>", label-side: center, $s$)
    edge((-0.15, 0.5), (0.15, 0.5), "=>", $q'$, label-side: center, label-size: 0.8em)
    edge((0.85, 0.5), (1.15, 0.5), "=>", $q$, label-side: center, label-size: 0.8em)
    edge((0.5, 0.15), (0.5, -0.15), "=>", $p'$, label-side: center, label-size: 0.8em)
    edge((0.5, 1.15), (0.5, 0.85), "=>", $p$, label-side: center, label-size: 0.8em)
  }, crossing-fill: thm-box-curr-color(), spacing: 6em))
  Then $q, q'$ induce natural transformations $q^L: h^L -> g^L, q'^L: g'^L -> h'^L$, and the composition: 
  $
    h^L phi -->^(h^L p) h^L f -->^(q^L f) g^L f -->^(BC(f,f',g,g',s)) f' g'^L -->^(f'q'^L) f' h'^L -->^(p'h'^L) phi' h'^L
  $
  is exactly the base change $BC(phi, phi', h, h', tilde(s))$, where $tilde(s)$ is the natural transformation: 
  $
    phi h' -->^(p h') f h' -->^(f q') f g' -->^s g f' -->^(q f') h f' -->^(h p') h phi' 
  $
]
#proof[
  It suffices to apply the natural transformations $p, p', q, q'$ one by one, and assume that the other three are all identities in each step. 

  - Suppose that $q, q'$ are identities. Then the composition given is: #h(1fr)
    $
      g^L phi -->^(g^L p) g^L f -->^(BC(f,f',g,g',s)) f' g'^L -->^(p' g'^L) phi' g'^L 
    $
    i.e: 
    $
      g^L phi -->^(g^L p) g^L f -->^(g^L f u_(g')) g^L f g' g'^L -->^(g^L s g'^L) g^L g f' g'^L -->^(eta_g f' g'^L) f' g'^L -->^(p' g'^L) phi' g'^L
    $
    Now the first two arrows may be exchanged by naturality, and the last two arrows may be exchanged by naturality, so that this composition is: 
    $
      g^L phi -->^(g^L phi u_(g')) g^L phi g' g'^L -->^(g^L p g' g'^L) g^L f g' g'^L -->^(g^L s g'^L) g^L g f' g'^L -->^(g^L g p' g'^L) g^L g phi' g'^L -->^(eta_g phi' g'^L) phi' g'^L 
    $
    which is $BC(phi, phi', g, g', g p' compose s compose p g')$ by definition. 

  - Suppose that $p, p', q'$ are identities. First note that $q^L: h^L -> g^L$ is constructed as: 
    $
      h^L -->^(h^L u_g) h^L g g^L -->^(h^L q g^L) h^L h g^L -->^(eta_h g^L) g^L
    $
    Now the proof is summarized in the following commutative diagram: 
    // https://q.uiver.app/#r=typst&q=WzAsMTMsWzAsMCwiaF5MIGYiXSxbMiwwLCJnXkwgZiJdLFs1LDEsImdeTCBmIGcnIGcnXkwiXSxbNywxLCJnXkwgZyBmJyBnJ15MIl0sWzksMSwiZicgZydeTCJdLFsxLDEsImheTCBmIGcnIGcnXkwiXSxbNCwyLCJoXkwgaCBnXkwgZiBnJyBnJ15MIl0sWzMsMywiaF5MIGcgZ15MIGYgZycgZydeTCJdLFs2LDIsImheTCBoIGdeTCBnIGYnIGcnXkwiXSxbOCwyLCJoXkwgaCBmJyBnJ15MIl0sWzUsMywiaF5MIGcgZ15MIGcgZiBnJ15MIl0sWzcsMywiaF5MIGcgZicgZydeTCJdLFsyLDQsImheTCBnIGYnIGcnXkwiXSxbMCwxLCJxXkwgZiIsMV0sWzEsMiwiZ15MIGYgdV8oZycpIiwxXSxbMiwzLCJnXkwgcyBnJ15MIiwxXSxbMyw0LCJldGFfZyBmJyBnJ15MIiwxXSxbNSwyLCJxXkwgZiBnJyBnJ15MIiwxXSxbMCw1LCJoXkwgZiB1XyhnJykiLDFdLFs1LDcsImheTCB1X2cgZiBnJyBnJ15MIiwxXSxbNyw2LCJoXkwgcSBnXkwgZiBnJyBnJ15MIiwxXSxbNiwyLCJldGFfaCBnXkwgZiBnJyBnJ15MIiwxXSxbNiw4LCJoXkwgaCBnXkwgcyBnJ15MIiwxXSxbOCwzLCJldGFfaCBnXkwgZyBmJyBnJ15MIiwxXSxbOCw5LCJoXkwgaCBldGFfZyBmJyBnJ15MIiwxXSxbOSw0LCJldGFfaCBmJyBnJ15MIiwxXSxbNywxMCwiaCBnIGdeTCBzIGcnXkwiLDFdLFsxMCw4LCJoXkwgcSBnXkwgZyBmJyBnJ15MIiwxXSxbMTAsMTEsImheTCBnIGV0YV9nIGYnIGcnXkwiLDFdLFsxMSw5LCJoXkwgcSBmJyBnJ15MIiwxXSxbNSwxMiwiaF5MIHMgZydeTCIsMV0sWzEyLDEwLCJoXkwgdV9nIGcgZicgZydeTCIsMV0sWzEyLDExLCIiLDEseyJjdXJ2ZSI6Miwic3R5bGUiOnsiYm9keSI6eyJuYW1lIjoiZG91YmxlIGJhcnJlZCJ9fX1dXQ==
    #context snap-width(align(center, diagram({
      node((0, 0), [$h^L f$])
      node((2, 0), [$g^L f$])
      node((5, 1), [$g^L f g' g'^L$])
      node((7, 1), [$g^L g f' g'^L$])
      node((9, 1), [$f' g'^L$])
      node((1, 1), [$h^L f g' g'^L$])
      node((4, 2), [$h^L h g^L f g' g'^L$])
      node((3, 3), [$h^L g g^L f g' g'^L$])
      node((6, 2), [$h^L h g^L g f' g'^L$])
      node((8, 2), [$h^L h f' g'^L$])
      node((5, 3), [$h^L g g^L g f g'^L$])
      node((7, 3), [$h^L g f' g'^L$])
      node((2, 4), [$h^L g f' g'^L$])
      edge((0, 0), (2, 0), [$q^L f$], label-side: center, "->")
      edge((2, 0), (5, 1), [$g^L f u_(g')$], label-side: center, "->")
      edge((5, 1), (7, 1), [$g^L s g'^L$], label-side: center, "->")
      edge((7, 1), (9, 1), [$eta_g f' g'^L$], label-side: center, "->")
      edge((1, 1), (5, 1), [$q^L f g' g'^L$], label-side: center, "->")
      edge((0, 0), (1, 1), [$h^L f u_(g')$], label-side: center, "->")
      edge((1, 1), (3, 3), [$h^L u_g f g' g'^L$], label-side: center, "->")
      edge((3, 3), (4, 2), [$h^L q g^L f g' g'^L$], label-side: center, "->")
      edge((4, 2), (5, 1), [$eta_h g^L f g' g'^L$], label-side: center, "->")
      edge((4, 2), (6, 2), [$h^L h g^L s g'^L$], label-side: center, "->")
      edge((6, 2), (7, 1), [$eta_h g^L g f' g'^L$], label-side: center, "->")
      edge((6, 2), (8, 2), [$h^L h eta_g f' g'^L$], label-side: center, "->")
      edge((8, 2), (9, 1), [$eta_h f' g'^L$], label-side: center, "->")
      edge((3, 3), (5, 3), [$h g g^L s g'^L$], label-side: center, "->")
      edge((5, 3), (6, 2), [$h^L q g^L g f' g'^L$], label-side: center, "->")
      edge((5, 3), (7, 3), [$h^L g eta_g f' g'^L$], label-side: center, "->")
      edge((7, 3), (8, 2), [$h^L q f' g'^L$], label-side: center, "->")
      edge((1, 1), (2, 4), [$h^L s g'^L$], label-side: center, "->")
      edge((2, 4), (5, 3), [$h^L u_g g f' g'^L$], label-side: center, "->")
      edge((2, 4), (7, 3), "=", bend: -20deg)

      node((2, 0.5), text(fill: red)[$arrow.ccw_N$])
      node((3, 2), text(fill: red)[$arrow.ccw_D$])
      node((5.5, 1.5), text(fill: red)[$arrow.ccw_N$])
      node((7.5, 1.5), text(fill: red)[$arrow.ccw_N$])
      node((4.5, 2.5), text(fill: red)[$arrow.ccw_N$])
      node((6.5, 2.5), text(fill: red)[$arrow.ccw_N$])
      node((2.3, 3), text(fill: red)[$arrow.ccw_N$])
      node((4.5, 3.7), text(fill: red)[$arrow.ccw_U$])
    }, spacing: (2em, 3em), crossing-fill: thm-box-curr-color())))
    where: 
    - $arrow.ccw_D$ in a cell indicates that this cell commutes by definition; 

    - $arrow.ccw_N$ in a cell indicates that this cell commutes as a naturality square; 

    - $arrow.ccw_U$ in a cell indicates that this cell commutes by an adjunction identity. 

  - The proof for nontrivial $q'$ is dual to the proof for nontrivial $q$ and is omitted. 
]

Finally, there is an alternative description for a Beck-Chevalley base change, when $f$ and $f'$ are also right adjoints. 

#proposition(name: <bcbc-all-rights>)[
  Suppose that we have functors between categories: 
  // https://q.uiver.app/#r=typst&q=WzAsNCxbMCwwLCJjYWwoQylfMSJdLFswLDEsImNhbChDKV8yIl0sWzEsMCwiY2FsKEQpXzEiXSxbMSwxLCJjYWwoRClfMiJdLFsxLDMsImYiLDJdLFswLDIsImYnIl0sWzIsMywiZyJdLFswLDEsImcnIiwyXSxbMSwyLCJ0IiwxXV0=
  #context align(center, diagram({
    node((-1, -1), [$cal(C)_1$])
    node((-1, 0), [$cal(C)_2$])
    node((0, -1), [$cal(D)_1$])
    node((0, 0), [$cal(D)_2$])
    edge((-1, 0), (0, 0), [$f$], label-side: right, "->")
    edge((-1, -1), (0, -1), [$f'$], label-side: left, "->")
    edge((0, -1), (0, 0), [$g$], label-side: left, "->")
    edge((-1, -1), (-1, 0), [$g'$], label-side: right, "->")
    edge((-0.7, -0.3), (-0.3, -0.7), [$t$], label-side: center, "=>")
  }, crossing-fill: thm-box-curr-color()))
  where $t: f g' -> g f'$ is a natural transformation, and $f, g, f', g'$ have left adjoints $f^L, g^L, f'^L, g'^L$. Then the Beck-Chevalley base change $BC(f,f',g,g',t): g^L f -> f' g'^L$ is the same as the composition: 
  $
    g^L f -->^(u_(f') g^L f) f' f'^L g^L f -->^(f' t^L f) f' g'^L f^L f -->^(f' g'^L eta_f) f' g'^L
  $
]
#proof[
  The map $t^L: f'^L g^L -> g'^L f^L$ is: 
  $
    f'^L g^L &-->^(f'^L g^L u_f) f'^L g^L f f^L -->^(f'^L g^L f u_(g') f^L) f'^L g^L f g' g'^L f^L -->^(f'^L g^L t g'^L f^L) f'^L g^L g f' g'^L f^L \
    &-->^(f'^L eta_g f' g'^L f^L) f'^L f' g'^L f^L -->^(eta_(f') g'^L f^L) g'^L f^L
  $
  Now the proof is summarized in the following commutative diagram: 
  // https://q.uiver.app/#r=typst&q=WzAsMTYsWzAsMSwiZ15MIGYiXSxbMiwwLCJmJyBmJ15MIGdeTCBmIl0sWzQsMSwiZicgZideTCBnXkwgZiBmXkwgZiJdLFs2LDAsImYnIGYnXkwgZ15MIGYgZycgZydeTCBmXkwgZiJdLFs5LDAsImYnIGYnXkwgZ15MIGcgZicgZydeTCBmXkwgZiJdLFsxMSwxLCJmJyBmJ15MIGYnIGcnXkwgZl5MIGYiXSxbMTMsMCwiZicgZydeTCBmXkwgZiJdLFsxNSwxLCJmJyBnJ15MIl0sWzIsMiwiZ15MIGYgZl5MIGYiXSxbNSwzLCJnXkwgZiBnJyBnJ15MIGZeTCBmIl0sWzEzLDIsImYnIGYnXkwgZicgZydeTCJdLFsxMCwzLCJmJyBmJ15MIGdeTCBnIGYnIGcnXkwiXSxbNiw1LCJnXkwgZiBnJyBnJ15MIl0sWzksNSwiZ15MIGcgZicgZydeTCJdLFszLDQsImdeTCBmIl0sWzEyLDQsImYnIGcnXkwiXSxbMSwyLCJmJyBmJ15MIGdeTCB1X2YgZiIsMV0sWzIsMywiZicgZideTCBnXkwgZiB1XyhnJykgZl5MIGYiLDFdLFszLDQsImYnIGYnXkwgZ15MIHQgZydeTCBmXkwgZiIsMV0sWzQsNSwiZicgZideTCBldGFfZyBmJyBnJ15MIGZeTCBmIiwxXSxbNSw2LCJmJyBldGFfKGYnKSBnJ15MIGZeTCBmIiwxXSxbNiw3LCJmJyBnJ15MIGV0YV9mIiwxXSxbMCw4LCJnXkwgdV9mIGYiLDFdLFs4LDIsInVfKGYnKSBnXkwgZiBmXkwgZiIsMV0sWzAsMSwidV8oZicpIGdeTCBmIiwxXSxbOCw5LCJnXkwgZiB1XyhnJykgZl5MIGYiLDFdLFs5LDMsInVfKGYnKSBnXkwgZiBnJyBnJ15MIGZeTCBmIiwxXSxbNSwxMCwiZicgZideTCBmJyBnJ15MIGV0YV9mIiwxXSxbMTAsNywiZicgZXRhXyhmJykgZydeTCIsMV0sWzQsMTEsImYnIGYnXkwgZ15MIGcgZicgZydeTCBldGFfZiIsMV0sWzExLDEwLCJmJyBmJ15MIGV0YV9nIGYnIGcnXkwiLDFdLFs5LDEyLCJnXkwgZiBnJyBnJ15MIGV0YV9mIiwxXSxbMTIsMTMsImdeTCB0IGcnXkwiLDFdLFsxMywxMSwidV8oZicpIGdeTCBnIGYnIGcnXkwiLDFdLFs4LDE0LCJnXkwgZiBldGFfZiIsMV0sWzE0LDEyLCJnXkwgZiB1XyhnJykiLDFdLFsxMywxNSwiZXRhX2cgZicgZydeTCIsMV0sWzE1LDEwLCJ1XyhmJykgZicgZydeTCIsMV0sWzAsMTQsIiIsMSx7ImN1cnZlIjoyLCJzdHlsZSI6eyJib2R5Ijp7Im5hbWUiOiJkb3VibGUgYmFycmVkIn19fV0sWzE1LDcsIiIsMSx7ImN1cnZlIjoyLCJzdHlsZSI6eyJib2R5Ijp7Im5hbWUiOiJkb3VibGUgYmFycmVkIn19fV1d
  #context snap-width(align(center, diagram({
    node((0, 0), [$g^L f$])
    node((2, -1), [$f' f'^L g^L f$])
    node((4, 0), [$f' f'^L g^L f f^L f$])
    node((6, -1), [$f' f'^L g^L f g' g'^L f^L f$])
    node((9, -1), [$f' f'^L g^L g f' g'^L f^L f$])
    node((11, 0), [$f' f'^L f' g'^L f^L f$])
    node((13, -1), [$f' g'^L f^L f$])
    node((15, 0), [$f' g'^L$])
    node((2, 1), [$g^L f f^L f$])
    node((5, 2), [$g^L f g' g'^L f^L f$])
    node((13, 1), [$f' f'^L f' g'^L$])
    node((10, 2), [$f' f'^L g^L g f' g'^L$])
    node((6, 4), [$g^L f g' g'^L$])
    node((9, 4), [$g^L g f' g'^L$])
    node((3, 3), [$g^L f$])
    node((12, 3), [$f' g'^L$])
    edge((2, -1), (4, 0), [$f' f'^L g^L u_f f$], label-side: center, "->")
    edge((4, 0), (6, -1), [$f' f'^L g^L f u_(g') f^L f$], label-side: center, "->")
    edge((6, -1), (9, -1), [$f' f'^L g^L t g'^L f^L f$], label-side: center, "->")
    edge((9, -1), (11, 0), [$f' f'^L eta_g f' g'^L f^L f$], label-side: center, "->")
    edge((11, 0), (13, -1), [$f' eta_(f') g'^L f^L f$], label-side: center, "->")
    edge((13, -1), (15, 0), [$f' g'^L eta_f$], label-side: center, "->")
    edge((0, 0), (2, 1), [$g^L u_f f$], label-side: center, "->")
    edge((2, 1), (4, 0), [$u_(f') g^L f f^L f$], label-side: center, "->")
    edge((0, 0), (2, -1), [$u_(f') g^L f$], label-side: center, "->")
    edge((2, 1), (5, 2), [$g^L f u_(g') f^L f$], label-side: center, "->")
    edge((5, 2), (6, -1), [$u_(f') g^L f g' g'^L f^L f$], label-side: center, "->")
    edge((11, 0), (13, 1), [$f' f'^L f' g'^L eta_f$], label-side: center, "->")
    edge((13, 1), (15, 0), [$f' eta_(f') g'^L$], label-side: center, "->")
    edge((9, -1), (10, 2), [$f' f'^L g^L g f' g'^L eta_f$], label-side: center, "->")
    edge((10, 2), (13, 1), [$f' f'^L eta_g f' g'^L$], label-side: center, "->")
    edge((5, 2), (6, 4), [$g^L f g' g'^L eta_f$], label-side: center, "->")
    edge((6, 4), (9, 4), [$g^L t g'^L$], label-side: center, "->")
    edge((9, 4), (10, 2), [$u_(f') g^L g f' g'^L$], label-side: center, "->")
    edge((2, 1), (3, 3), [$g^L f eta_f$], label-side: center, "->")
    edge((3, 3), (6, 4), [$g^L f u_(g')$], label-side: center, "->")
    edge((9, 4), (12, 3), [$eta_g f' g'^L$], label-side: center, "->")
    edge((12, 3), (13, 1), [$u_(f') f' g'^L$], label-side: center, "->")
    edge((0, 0), (3, 3), "=", bend: -30deg)
    edge((12, 3), (15, 0), "=", bend: -30deg)

    node((2, 0), text(fill: red)[$arrow.ccw_N$])
    node((13, 0), text(fill: red)[$arrow.ccw_N$])
    node((4.5, 1), text(fill: red)[$arrow.ccw_N$])
    node((10.5, 1), text(fill: red)[$arrow.ccw_N$])
    node((7.5, 1.5), text(fill: red)[$arrow.ccw_N$])
    node((4.2, 2.5), text(fill: red)[$arrow.ccw_N$])
    node((10.8, 2.5), text(fill: red)[$arrow.ccw_N$])
    node((2, 2), text(fill: red)[$arrow.ccw_U$])
    node((13, 2), text(fill: red)[$arrow.ccw_U$])
  }, crossing-fill: thm-box-curr-color(), spacing: (2.5em, 3em), label-size: 0.9em)))
  where: 
  
  - $arrow.ccw_N$ in a cell indicates that this cell commutes as a naturality square; 

  - $arrow.ccw_U$ in a cell indicates that this cell commutes by an adjunction identity. 
]

// As a corollary, we obtain the following compatibility result for various base changes, which will be occasionally useful. 

// #corollary[
//   Consider the following diagram: 
//   // https://q.uiver.app/#r=typst&q=WzAsOCxbMCwxLCJjYWwoRClfMSJdLFsxLDAsImNhbChEKV8yIl0sWzIsMiwiY2FsKEQpXzMiXSxbMywxLCJjYWwoRClfNCJdLFswLDQsImNhbChDKV8xIl0sWzEsMywiY2FsKEMpXzIiXSxbMiw1LCJjYWwoQylfMyJdLFszLDQsImNhbChDKV80Il0sWzQsNSwiZl8xIiwxXSxbNSw3LCJmXzIiLDEseyJsYWJlbF9wb3NpdGlvbiI6MzB9XSxbNiw3LCJmJ18yIiwxXSxbNCw3LCJmIiwxXSxbMCwxLCJoXzEiLDFdLFsyLDMsImgnXzIiLDFdLFsxLDMsImhfMiIsMV0sWzAsMiwiaCdfMSIsMSx7ImxhYmVsX3Bvc2l0aW9uIjo3MH1dLFs0LDYsImYnXzEiLDFdLFswLDMsImgiLDFdLFs0LDAsImdfMSIsMV0sWzUsMSwiZ18yIiwxLHsibGFiZWxfcG9zaXRpb24iOjIwfV0sWzcsMywiZ180IiwxXSxbNiwyLCJnXzMiLDEseyJsYWJlbF9wb3NpdGlvbiI6ODB9XV0=
//   #context align(center, diagram({
//     node((0, 1), [$cal(D)_1$])
//     node((1, 0), [$cal(D)_2$])
//     node((2, 2), [$cal(D)_3$])
//     node((3, 1), [$cal(D)_4$])
//     node((0, 4), [$cal(C)_1$])
//     node((1, 3), [$cal(C)_2$])
//     node((2, 5), [$cal(C)_3$])
//     node((3, 4), [$cal(C)_4$])
//     edge((0, 4), (1, 3), [$f_1$], label-side: center, "->")
//     edge((1, 3), (3, 4), [$f_2$], label-side: center, label-pos: 0.3, "->")
//     edge((2, 5), (3, 4), [$f'_2$], label-side: center, "->")
//     edge((0, 4), (3, 4), [$f$], label-side: center, "->")
//     edge((0, 1), (1, 0), [$h_1$], label-side: center, "->")
//     edge((2, 2), (3, 1), [$h'_2$], label-side: center, "->")
//     edge((1, 0), (3, 1), [$h_2$], label-side: center, "->")
//     edge((0, 1), (2, 2), [$h'_1$], label-side: center, label-pos: 0.7, "->")
//     edge((0, 4), (2, 5), [$f'_1$], label-side: center, "->")
//     edge((0, 1), (3, 1), [$h$], label-side: center, "->")
//     edge((0, 4), (0, 1), [$g_1$], label-side: center, "->")
//     edge((1, 3), (1, 0), [$g_2$], label-side: center, label-pos: 0.2, "->")
//     edge((3, 4), (3, 1), [$g_4$], label-side: center, "->")
//     edge((2, 5), (2, 2), [$g_3$], label-side: center, label-pos: 0.8, "->")
//   }, crossing-fill: thm-box-curr-color(), spacing: (2.5em, 1.6em)))
//   in which $f_i, f'_i, h_i, h'_i$ are right adjoints. 
// ]
