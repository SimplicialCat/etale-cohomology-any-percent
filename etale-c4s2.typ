#import "void-import.typ": *
== Examples of etale sheaves

/*
Let $X$ be a scheme and $Et_X$ be the category of etale $X$-schemes. Recall that $X_et = (Et_X, "etale covers")$ is the etale site of $X$. Here, ${f_i: Z_i -> Z}$ is called an etale cover, if they are jointly surjective, i.e. $Z = union.big_i f_i (Z_i)$. 

Recall that we defined presheaves $cPSh(X_et)$ on $X_et$ to be a functor $cal(F): Et_X^opp -> cSet$, and sheaves $cSh(X_et)$ to be presheaves s.t. for any etale cover ${f_i: Z_i -> Z}$, 
$
  cal(F) -> product_i cal(F)(Z_i) arrows.rr product_(i,j) cal(F)(Z_i times_Z Z_j)
$
is exact. Replacing $cSet$ with $cAb$, we get $cPAb(X_et)$ and $cAb(X_et)$. 
*/
As usual, once we have introduced an object, we study its first properties. In the case of etale sheaves, we may use the analogy with topological sheaves to have an expectation on what constructions we need. Namely, we need: 
- Examples of etale sheaves; 
- Sheafification; 
- $cAb(X_et)$ being an abelian category (a.k.a. defining kernels, cokernels and images); 
- $cAb(X_et)$ having enough injectives; 
- The adjoint pair $f_*: cAb(X_et) arrows.rl cAb(Y_et): f^(-1)$ for a morphism $f: X -> Y$ between schemes. 

We will deal with these topics in this section and the following few sections. Our arrangement of sections corresponds to the methods of obtaining an etale sheaf on $X$: 
- Constructed directly as one of the primary examples; 
- From the abelian category structure of $cAb(X_et)$, i.e as a kernel, cokernel or image of a morphism between etale sheaves on $X$; 
- From functoriality, by applying a functor like $f_*, f^(-1)$ (and $f_!$ which will be introduced much later) or a derived version of them to an etale sheaf on another scheme. 

#lemma[
  (Nine lemma for sets) Suppose that we have a diagram of sets: 
  // https://q.uiver.app/#r=typst&q=WzAsOSxbMCwwLCJBXzEiXSxbMSwwLCJCXzEiXSxbMiwwLCJDXzEiXSxbMCwxLCJBXzIiXSxbMSwxLCJCXzIiXSxbMiwxLCJDXzIiXSxbMCwyLCJBXzMiXSxbMSwyLCJCXzMiXSxbMiwyLCJDXzMiXSxbMCwxLCJmXygxLDEpIl0sWzEsMiwiZ18oMSwxKSIsMCx7Im9mZnNldCI6LTF9XSxbMSwyLCJnXygxLDIpIiwyLHsib2Zmc2V0IjoxfV0sWzMsNCwiZl8yIl0sWzYsNywiZl8zIl0sWzQsNSwiZ18oMiwxKSIsMCx7Im9mZnNldCI6LTF9XSxbNCw1LCJnXygyLDIpIiwyLHsib2Zmc2V0IjoxfV0sWzcsOCwiZ18oMywxKSIsMCx7Im9mZnNldCI6LTF9XSxbNyw4LCJnXygzLDIpIiwyLHsib2Zmc2V0IjoxfV0sWzAsMywiYWxwaGFfKDEsMSkiLDFdLFszLDYsImJldGFfKDEsMSkiLDIseyJvZmZzZXQiOjF9XSxbMyw2LCJiZXRhXygxLDIpIiwyLHsib2Zmc2V0IjotMX1dLFsxLDQsImFscGhhXzIiLDFdLFsyLDUsImFscGhhXzMiLDFdLFs0LDcsImJldGFfKDIsMSkiLDIseyJvZmZzZXQiOjF9XSxbNCw3LCJiZXRhXygyLDIpIiwwLHsib2Zmc2V0IjotMX1dLFs1LDgsImJldGFfKDMsMSkiLDIseyJvZmZzZXQiOjF9XSxbNSw4LCJiZXRhXygzLDIpIiwyLHsib2Zmc2V0IjotMX1dXQ==
  #context align(center, diagram({
    node((-1, -1), [$A_1$])
    node((0, -1), [$B_1$])
    node((1, -1), [$C_1$])
    node((-1, 0), [$A_2$])
    node((0, 0), [$B_2$])
    node((1, 0), [$C_2$])
    node((-1, 1), [$A_3$])
    node((0, 1), [$B_3$])
    node((1, 1), [$C_3$])
    edge((-1, -1), (0, -1), [$f_1$], label-side: left, "->")
    edge((0, -1 + 0.06), (1, -1 - 0.04), [$g_(1,1)$], label-side: left, shift: 0.05, "->")
    edge((0, -1 - 0.06), (1, -1 + 0.04), [$g_(1,2)$], label-side: right, shift: -0.05, "->")
    edge((-1, 0), (0, 0), [$f_2$], label-side: left, "->")
    edge((-1, 1), (0, 1), [$f_3$], label-side: left, "->")
    edge((0, 0.06), (1, -0.04), [$g_(2,1)$], label-side: left, shift: 0.05, "->")
    edge((0, -0.06), (1, 0.04), [$g_(2,2)$], label-side: right, shift: -0.05, "->")
    edge((0, 1 + 0.06), (1, 1 - 0.04), [$g_(3,1)$], label-side: left, shift: 0.05, "->")
    edge((0, 1 - 0.06), (1, 1 + 0.04), [$g_(3,2)$], label-side: right, shift: -0.05, "->")
    edge((-1, -1), (-1, 0), [$alpha_1$], label-side: center, "->")
    edge((-1 + 0.06, 0), (-1 - 0.04, 1), [$beta_(1,1)$], label-side: right, shift: -0.05, "->")
    edge((-1 - 0.06, 0), (-1 + 0.04, 1), [$beta_(1,2)$], label-side: left, shift: 0.05, "->")
    edge((0, -1), (0, 0), [$alpha_2$], label-side: center, "->")
    edge((1, -1), (1, 0), [$alpha_3$], label-side: center, "->")
    edge((0 + 0.06, 0), (0 - 0.04, 1), [$beta_(2,1)$], label-side: right, shift: -0.05, "->")
    edge((0 - 0.06, 0), (0 + 0.04, 1), [$beta_(2,2)$], label-side: left, shift: 0.05, "->")
    edge((1 + 0.06, 0), (1 - 0.04, 1), [$beta_(3,1)$], label-side: right, shift: -0.05, "->")
    edge((1 - 0.06, 0), (1 + 0.04, 1), [$beta_(3,2)$], label-side: left, shift: 0.05, "->")
  }, spacing: 5em, crossing-fill: thm-box-curr-color()))
  in which every parallelogram commutes, i.e: 
  $
    alpha_2 compose f_1 = alpha_1 compose f_2 \
    alpha_3 compose g_(1,i) = g_(2,i) compose alpha_2, forall i in {1,2} \
    beta_(2,j) compose f_2 = f_3 compose beta_(1,j), forall j in {1,2} \
    beta_(3,j) compose g_(2,i) = g_(3,i) compose beta_(2,j), forall i,j in {1, 2}
  $
  If all three columns and the bottom two rows are equalizers, then so is the top row. Furthermore, the top row is an equalizer under the weaker assumption that: 
  - $alpha_(1,2,3)$ and $f_(2,3)$ are all injective;
  - The middle row is an equalizer;
  - The equalizer of $beta_(1,1),beta_(1,2)$ factors through (i.e. is contained in) $alpha_1 (A_1)$. 
  In this weaker assumption you can actually drop $g_(3,i)$ and $beta_(3,j)$ from the diagram. 
]
#proof[
  The proof is uninteresting diagram tracing. Please skip it. 

  Since $alpha_1, f_2$ are injective, so is $alpha_2 compose f_1 = alpha_1 compose f_2$. Thus $f_1$ is injective. Furthermore, for $i in {1, 2}$, 
  $
    alpha_3 compose g_(1,i) compose f_1 = g_(2,i) compose f_2 compose alpha_1
  $
  Since $g_(2,1) compose f_2 = g_(2,2) compose f_2$, we have $alpha_3 compose g_(1,1) compose f_1 = alpha_3 compose g_(1,2) compose f_1$. Since $alpha_3$ is injective, we may left cancel it to get $g_(1,1) compose f_1 = g_(1,2) compose f_1$. 

  To show that the top row is an equalizers, it remains to show that if $g_(1,1)(b_1) = g_(1,2)(b_1)$, then $b_1 in f_1 (A_1)$. Apply $alpha_3$ to the equality, we see $g_(2,1)(alpha_2 (b_1)) = g_(2,2) (alpha_2 (b_1))$. Since the middle row is an equalizer, there exists $a_2 in A_2$ s.t. $alpha_2 (b_1) = f_2 (a_2)$. Applying $beta_(2,j)$ to this equality, we see that $beta_(2,1) (f_2 (a_2)) = beta_(2,1) (alpha_2 (b_1)) = beta_(2,2) (alpha_2 (b_1)) = beta_(2,2) (f_2 (a_2))$. In other words, $f_3 (beta_(1,1) (a_2)) = f_3 (beta_(1,2) (a_2))$. Since $f_3$ is injective, $beta_(1,1) (a_2) = beta_(1,2) (a_2)$. Since the left column is an equalizer, there exists $a_1 in A_1$ s.t. $a_2 = alpha_1 (a_1)$. Now $alpha_2 (b_1) = f_2 (alpha_1 (a_1)) = alpha_2 (f_1 (a_1))$, and since $alpha_2$ is injective, $b_1 = f_1 (a_1)$. 

  By carefully inspecting the proof, we see that the only conditions used are: 
  - $alpha_(1,2,3)$ and $f_(2,3)$ being injective; 
  - The middle row is an equalizer; 
  - The left columns satisfies that if $beta_(1,1)(a_2) = beta_(1,2)(a_2)$, then $a_2 in alpha_1 (A_1)$. That is, the equalizer of $beta_(1,1),beta_(1,2)$ factors through (i.e. is contained in) $alpha_1 (A_1)$. 
]

#lemma(name: <etale-cover-equiv-conds>)[
  Let $cal(F) in cPSh(X_et)$ or $cPAb(X_et)$. Then the following are equivalent: 

  + $cal(F) in cSh(X_et)$ (or $cAb(X_et)$ respectively), i.e. $cal(F)$ satisfies the sheaf conditions for every etale cover in $X_et$; 

  + $cal(F)$ satisfies the sheaf conditions for:
    + Every Zariski cover; 
    + Every etale cover in $X_et$ consisting of a single map. 

  + $cal(F)$ satisfies the sheaf conditions for:
    + Every Zariski cover;
    + Every etale cover in $X_et$ of the form ${Z_i -> Z}_(i in I)$ where the index set $I$ is finite, with $Z$ and every $Z_i$ quasi-compact. 

  + $cal(F)$ satisfies the sheaf conditions for:
    + Every Zariski cover;
    + Every etale cover in $X_et$ consisting of a single map $Z' -> Z$ where $Z', Z$ are affine. 

  // + $cal(F)$ satisfies the sheaf conditions for:
  //   + Every Zariski cover;
  //   + Every etale cover in $X_et$ consisting of a single map $Z' -> Z$ where $Z', Z$ are affine. 
]
#proof[
  Since an abelian sheaf is just an abelian presheaf that is a sheaf of sets, we may consider only the set case $cal(F) in cPSh(X_et)$. /*Note that under (a), (b) and (b') are equivalent since we may replace the finite family ${f_i: Z_i -> Z}$ with $f': Z' = union.sq.big_(i in I) Z_i -> Z$. If every $Z_i$ is quasi-compact, then so is $Z'$. Thus, we may assume that we have the conditions (a)(b). */

  Under the assumption that the sheaf conditions hold for every Zariski cover, we may check using the cover ${U_i -> union.sq.big_(i in I) U_i}_(i in I)$ that: 
  $
    cal(F)(union.sq.big_(i in I) U_i) cong product_(i in I) cal(F)(U_i)
  $
  canonically. Then we immediately see that the sheaf condition for a general etale cover ${Z_i -> Z}_(i in I)$ is equivalent to that of the etale cover $union.sq.big_(i in I) Z_i -> Z$ consisting of a single map. This immediately establishes (1)$<==>$(2)$==>$(3)$==>$(4). 
  
  We'll focus on proving (4)$==>$(2). Take any etale cover $g: W' -> W$. Then cover $W$ by affine opens $union.big_p U_p$. Then we have a diagram: 
  // https://q.uiver.app/#r=typst&q=WzAsOSxbMCwwLCJjYWwoRikoVykiXSxbMSwwLCJwcm9kdWN0XyhhbHBoYSkgY2FsKEYpKFdfYWxwaGEpIl0sWzIsMCwicHJvZHVjdF8oYWxwaGEsYmV0YSkgY2FsKEYpKFdfYWxwaGEgdGltZXNfVyBXX2JldGEpIl0sWzAsMSwicHJvZHVjdF9wIGNhbChGKShVX3ApIl0sWzEsMSwicHJvZHVjdF8ocCxhbHBoYSkgY2FsKEYpKFVfcCB0aW1lc19XIFdfYWxwaGEpIl0sWzIsMSwicHJvZHVjdF8ocCxhbHBoYSxiZXRhKSBjYWwoRikoVV9wIHRpbWVzX1cgV19hbHBoYSB0aW1lc19XIFdfYmV0YSkiXSxbMiwyLCJwcm9kdWN0XyhwLHEsYWxwaGEsYmV0YSkgY2FsKEYpKFVfcCB0aW1lc19XIFVfcSB0aW1lc19XICBXX2FscGhhIHRpbWVzX1cgV19iZXRhKSJdLFsxLDIsInByb2R1Y3RfKHAscSxhbHBoYSkgY2FsKEYpKFVfcCB0aW1lc19XIFVfcSB0aW1lc19XIFdfYWxwaGEpIl0sWzAsMiwicHJvZHVjdF8ocCxxKSBjYWwoRikoVV9wIHRpbWVzX1cgVV9xKSJdLFswLDFdLFsxLDIsIiIsMCx7Im9mZnNldCI6MX1dLFsxLDIsIiIsMCx7Im9mZnNldCI6LTF9XSxbMyw0XSxbNCw1LCIiLDAseyJvZmZzZXQiOjF9XSxbNCw1LCIiLDAseyJvZmZzZXQiOi0xfV0sWzgsN10sWzcsNiwiIiwwLHsib2Zmc2V0IjoxfV0sWzcsNiwiIiwwLHsib2Zmc2V0IjotMX1dLFswLDNdLFszLDgsIiIsMSx7Im9mZnNldCI6LTF9XSxbMyw4LCIiLDEseyJvZmZzZXQiOjF9XSxbMSw0XSxbNCw3LCIiLDEseyJvZmZzZXQiOjF9XSxbNCw3LCIiLDEseyJvZmZzZXQiOi0xfV0sWzIsNV0sWzUsNiwiIiwxLHsib2Zmc2V0IjotMX1dLFs1LDYsIiIsMSx7Im9mZnNldCI6MX1dXQ==
  #context align(center, diagram({
    let s = 0.45em.to-absolute()
    node((-1, -1), [$cal(F)(W)$])
    node((0, -1), [$cal(F)(W')$])
    node((1, -1), [$cal(F)(W' times_W W')$])
    node((-1, 0), [$product_p cal(F)(U_p)$])
    node((0, 0), [$product_(p) cal(F)(U_p times_W W')$])
    node((1, 0), [$product_(p) cal(F)(U_p times_W W' times_W W')$])
    node((1, 1), [$product_(p,q) cal(F)((U_p ∩ U_q) times_W  W' times_W W')$])
    node((0, 1), [$product_(p,q) cal(F)((U_p ∩ U_q) times_W W')$])
    node((-1, 1), [$product_(p,q) cal(F)(U_p ∩ U_q)$])
    edge((-1, -1), (0, -1), "->")
    edge((0, -1), (1, -1), shift: (0, -s), "->")
    edge((0, -1), (1, -1), shift: (0, s), "->")
    edge((-1, 0), (0, 0), "->")
    edge((0, 0), (1, 0), shift: (0, -s), "->")
    edge((0, 0), (1, 0), shift: (0, s), "->")
    edge((-1, 1), (0, 1), "->")
    edge((0, 1), (1, 1), shift: (0, -s), "->")
    edge((0, 1), (1, 1), shift: (0, s), "->")
    edge((-1, -1), (-1, 0), "->")
    edge((-1, 0), (-1, 1), shift: (0, 2*s), "->")
    edge((-1, 0), (-1, 1), shift: (0, -2*s), "->")
    edge((0, -1), (0, 0), "->")
    edge((0, 0), (0, 1), shift: (0, -2*s), "->")
    edge((0, 0), (0, 1), shift: (0, 2*s), "->")
    edge((1, -1), (1, 0), "->")
    edge((1, 0), (1, 1), shift: (0, 2*s), "->")
    edge((1, 0), (1, 1), shift: (0, -2*s), "->")
  }, spacing: 4.5em, node-defocus: 0))
  with commuting parallelograms. The columns are equalizers from the sheaf condition on Zariski covers for $W$, $W'$ and $W' times_W W'$, respectively. 

  We assume an auxiliary condition:  
  #[
    #set enum(numbering: _ => "(c)")

    + The sheaf condition holds for all etale covers consisting of a single map of any object $U in Et_X$ that is an affine scheme. 
  ]

  Under this assumption, the middle row is the sheaf condition for an etale cover of $U_p$, an affine scheme, and is an equalizer. Then: 

  - In the top-left square, the left and bottom arrows are injective. Thus the top arrow must be injective. 
  
  - Since $W$ is arbitrary, from the previous point $cal(F)(Z) -> cal(F)(Z')$ is injective for every $Z in Et_X$ and every etale cover $Z' -> Z$ in $Et_X$. In particular it holds for each $(U_p ∩ U_q) times_W W' -> U_p ∩ U_q$. In other words, the first arrow of the last row is injective. 

    Now that we have all columns and second row being equalizers, and the first arrow of the first and third row being injective, the nine lemma on sets is applicable, and the first arrow is an equalizer. 

  Therefore, the general sheaf condition is reduced to (c). We need to show that for any surjective etale $U' -> U$ in $Et_X$ with $U$ affine, the sheaf condition holds for $U' -> U$. 

  For an etale cover ${Z_i -> Z}_(i in I)$, we say that $cal(F)$ is separated w.r.t. ${Z_i -> Z}_(i in I)$, if: 
  $
    cal(F)(Z) -> product_(i in I) cal(F)(Z_i)
  $
  is injective. We introduce another condition: 
  #[
    #set enum(numbering: _ => "(cs)")
    + $cal(F)$ is separated w.r.t. all etale covers of an affine $U in Et_X$. 
  ]
  Note that by a disjoint union, we may trivially add the condition that the etale cover consists of a single map to (cs) without weakening it. From the top-left square in the nine lemma diagram above, we see that (cs)$==>$(s), where: 
  #[
    #set enum(numbering: _ => "(s)")
    + $cal(F)$ is separated w.r.t. all etale covers. 
  ]

  We now aim to prove (c) from the following weaker condition (d): 
  #[
    #set enum(numbering: _ => "(d)")
    + The sheaf condition holds for $cal(F)$ w.r.t. all etale covers ${U_i -> U}_(i in I)$ in which $U$ and every $U_i$ are affine, i.e. for all etale $V -> U$ in which $V$ is a disjoint union of affine schemes. 
  ]
  
  Suppose that $U$ is affine and $W -> U$ is an arbitrary etale cover. Cover $W$ by affine opens ${V_i}_(i in I)$ and take $V = union.sq.big_(i in I) V_i$ and we have $V ->> W ->> U$ in $Et_X$. Consider the following diagram in which parallelograms commute: 
  #context align(center, diagram({
    node((0, 0), $cal(F)(U)$)
    node((1, 0), $cal(F)(W)$)
    node((2, 0), $cal(F)(W times_U W)$)
    node((0, 1), $cal(F)(U)$)
    node((1, 1), $cal(F)(V)$)
    node((2, 1), $cal(F)(V times_U V)$)
    edge((0, 0), (1, 0), "->", $f_1$)
    edge((1, 0), (2, 0), "->", $g_(1,1)$, shift: (0, -0.1))
    edge((1, 0), (2, 0), "->", $g_(1,2)$, shift: (0, 0.1), label-side: right)
    edge((0, 1), (1, 1), "->", $f_2$)
    edge((1, 1), (2, 1), "->", shift: (0, -0.1), $g_(2,1)$)
    edge((1, 1), (2, 1), "->", shift: (0, 0.1), $g_(2,2)$, label-side: right)
    edge((0, 0), (0, 1), "=")
    edge((1, 0), (1, 1), "->", $beta$)
    edge((2, 0), (2, 1), "->", $gamma$)
  }))
  where the bottom row is an equalizer by (d). Then: 

  - In the left square, $f_2 = beta compose f_1$ is injective. Thus $f_1$ is injective. Since $W$ is arbitrary, this proves (cs). 

  - Since (cs)$==>$(s), we now have (s), and so $f_1, beta, gamma$ are all injective. By diagram tracing, the first row is an equalizer and we have (c). 
  
    (Here is the precise diagram tracing involved, if you want to read it. Firstly, $gamma compose g_(1,i) compose f_1 = g_(2,i) compose beta compose f_1 = g_(2,i) compose f_2$ agrees for $i = 1,2$. Since $gamma$ is injective, we may left cancel it to get $g_(1,1) compose f_1 = g_(1,2) compose f_1$. If $b in cal(F)(W)$ satisfies $g_(1,1)(b) = g_(1,2)(b)$, then applying $gamma$ and use the right commutative parallelograms gives $g_(2,1)(beta(b)) = g_(2,2)(beta(b))$. Since the bottom row is an equalizer, there exists $a in cal(F)(U)$ s.t. $f_2 (a) = beta(b)$, i.e. $beta(b) = beta(f_1(a))$. Since $beta$ is injective, $b = f_1 (a)$.)

  In summary, we have shown that (d)$==>$(c), so it remains to prove (d). Consider an etale cover $U' = union.sq.big_(i in I) U_i -> U$ in which each $U_i$ and $U$ is affine. Since $U$ is quasi-compact, there exists a finite subcollection $J subset I$ s.t. $U'_1 = union.sq.big_(i in J) U_i -> U$ is surjective. In other words, $U'_1$ is affine and $U'_1 -> U$ is surjective etale. We now consider the following diagram: 

  #context align(center, diagram(
    {
      let s = 0.45em.to-absolute()
      node((-1, -1), [$cal(F)(U)$])
      node((0, -1), [$product_(i in I) cal(F)(U_i)$])
      node((1, -1), [$product_(i,j in I) cal(F)(U_i times_U U_j)$])
      node((-1, 0), [$cal(F)(U'_1)$])
      node((0, 0), [$product_(i in I) cal(F)(U'_1 times_U U_i)$])
      node((1, 0), [$product_(i,j in I) cal(F)(U'_1 times_U U'_1 times_U U_i)$])
      node((1, 1), [$product_(i,j in I) cal(F)(U'_1 times_U U'_1 times_U U_i times_U U_j)$])
      node((0, 1), [$product_(i in I) cal(F)(U'_1 times_U U'_1 times_U U_i)$])
      node((-1, 1), [$cal(F)(U'_1 times_U U'_1)$])
      edge((-1, -1), (0, -1), "->")
      edge((0, -1), (1, -1), shift: (0, -s), "->")
      edge((0, -1), (1, -1), shift: (0, s), "->")
      edge((-1, 0), (0, 0), "->")
      edge((0, 0), (1, 0), shift: (0, -s), "->")
      edge((0, 0), (1, 0), shift: (0, s), "->")
      edge((-1, 1), (0, 1), "->")
      edge((0, 1), (1, 1), shift: (0, -s), "->")
      edge((0, 1), (1, 1), shift: (0, s), "->")
      edge((-1, -1), (-1, 0), "->")
      edge((-1, 0), (-1, 1), shift: (0, 2 * s), "->")
      edge((-1, 0), (-1, 1), shift: (0, -2 * s), "->")
      edge((0, -1), (0, 0), "->")
      edge((0, 0), (0, 1), shift: (0, -2 * s), "->")
      edge((0, 0), (0, 1), shift: (0, 2 * s), "->")
      edge((1, -1), (1, 0), "->")
      edge((1, 0), (1, 1), shift: (0, 2 * s), "->")
      edge((1, 0), (1, 1), shift: (0, -2 * s), "->")
    },
    spacing: 4.5em,
    node-defocus: 0,
  ))
  in which parallelograms commute. Now: 
  - Every column is (a direct product) of the sheaf condition sequence for $W times_U U'_1 -> W$ for $W = U, U_i$ or $U_i times_U U_j$. They are all equalizers by (4b). 

  - $U'_1 times_U U' -> U'_1$ admits a section $(id, subset): U'_1 -> U'_1 times_U U'$. Similarly, $U'_1 times_U U'_1 times_U U' -> U'_1 times_U U'_1$ also admits a section $(id_(U'_1 times_U U'_1), Delta)$. The bottom two rows are equalizers from the following lemma: 
    #lemma[
      For any $cal(F) in cPSh(X_et)$, if a morphism $f: Z -> Y$ in $Et_X$ admits a section $s: Y -> Z$, then the sheaf condition holds for $f: Z -> Y$. 
    ]
    #proof[
      We need to show that: 
      $
        cal(F)(Y) ->^(cal(F)(f)) cal(F)(Z) arrows.rr^(cal(F)(p_1))_(cal(F)(p_2)) cal(F)(Z times_Y Z)
      $
      is an equalizer. Firstly, note that $cal(F)(s) compose cal(F)(f) = id$ since $f compose s = id$, so $cal(F)(f)$ is injective. Furthermore, $f compose p_1 = f compose p_2$ is automatic. It remains to show that any $x in cal(F)(Z)$ with $cal(F)(p_1)(x) = cal(F)(p_2)(x)$ is in the image of $cal(F)(f)$. Define a map $phi = (id, s compose f): Z -> Z times_Y Z$ (since $f compose s compose f = f$). Now: 
      $
        p_1 compose phi = id_Z, p_2 compose phi = s compose f
      $
      so applying $cal(F)(phi)$ to $cal(F)(p_1)(x) = cal(F)(p_2)(x)$ yields: 
      $
        x = cal(F)(f)(cal(F)(s)(x))
      $
    ]
  From nine lemma, the top row is an equalizer, and (c) is proved. 

  /*
  We first prove that (a)(b) implies the following condition (b'): 

  #[
    #set enum(numbering: _ => "(b')")
    + For any surjective etale $V -> W$ in $Et_X$ with $V, W$ quasi-compact, and any etale $W' -> W$ (with $W'$ not necessarily quasi-compact), the sheaf condition for $cal(F)$ holds for $V' = W' times_W V -> U'$. 
  ]

  Indeed, in the setup for (b'), we may cover $U'$ by arbitrarily many affine opens ${U'_i}_(i in I)$. By (b), the sheaf condition for $cal(F)$ holds for each $U'_i times_U V -> U'_i$. //Taking $U'' = union.sq.big_(i in I) U'_i$, the sheaf condition for $cal(F)$ must thus hold for $V'' = U'' times_U V -> U''$. 

  // Note that $U'' -> U'$ is also a surjective etale map in $Et_X$, giving a refinement $U'' -> U' -> U$ of etale covers. Consider the diagram: 
  Consider the diagram: 
  #context align(center, diagram(
    {
      let s = 0.45em.to-absolute()
      node((-1, -1), [$cal(F)(U)$])
      node((0, -1), [$cal(F)(V)$])
      node((1, -1), [$cal(F)(V times_U V)$])
      node((-1, 0), [$product_i cal(F)(U_i)$])
      node((0, 0), [$product_i cal(F)(U_i times_W W')$])
      node((1, 0), [$product_i cal(F)(U_i times_W W' times_W W')$])
      node((1, 1), [$product_(i,j) cal(F)((U_i ∩ U_j) times_W W' times_W W')$])
      node((0, 1), [$product_(i,j) cal(F)((U_i ∩ U_j) times_W W')$])
      node((-1, 1), [$product_(i,j) cal(F)(U_i ∩ U_j)$])
      edge((-1, -1), (0, -1), "->")
      edge((0, -1), (1, -1), shift: (0, -s), "->")
      edge((0, -1), (1, -1), shift: (0, s), "->")
      edge((-1, 0), (0, 0), "->")
      edge((0, 0), (1, 0), shift: (0, -s), "->")
      edge((0, 0), (1, 0), shift: (0, s), "->")
      edge((-1, 1), (0, 1), "->")
      edge((0, 1), (1, 1), shift: (0, -s), "->")
      edge((0, 1), (1, 1), shift: (0, s), "->")
      edge((-1, -1), (-1, 0), "->")
      edge((-1, 0), (-1, 1), shift: (0, 2 * s), "->")
      edge((-1, 0), (-1, 1), shift: (0, -2 * s), "->")
      edge((0, -1), (0, 0), "->")
      edge((0, 0), (0, 1), shift: (0, -2 * s), "->")
      edge((0, 0), (0, 1), shift: (0, 2 * s), "->")
      edge((1, -1), (1, 0), "->")
      edge((1, 0), (1, 1), shift: (0, 2 * s), "->")
      edge((1, 0), (1, 1), shift: (0, -2 * s), "->")
    },
    spacing: 4.5em,
    node-defocus: 0,
  ))*/


  // The idea may be that each $U_p$ is quasi-compact, so you may or may not somehow apply the finite case to the last two rows and get some sort of exactness, and apply an argument similar to the nine lemma. To make things work, you need to perform a lot of reductions. 
]

#proposition(name: <examples-of-etale-sheaves>)[
  + For any $X$-scheme $Y$, #h(1fr)
    $
      h_Y : Et_X^opp -> cSet, Z |-> Hom_X (Z, Y)
    $
    is an etale sheaf of sets. If, furthermore, $Y$ is an abelian group scheme over $X$, then $h_Y$ is an etale sheaf of abelian groups. 

  + For any $cal(M) in QCoh(X)$, 
    $
      cal(M)_et: Et_X^opp -> cAb, (f: Z -> X) |-> Gamma(Z, f^* cal(M))
    $
    is an etale sheaf of abelian groups. 
]
#proof[
  In both cases, the sheaf properties hold for Zariski covers. Thus, it suffices to verify (4b) of @etale-cover-equiv-conds. Suppose that $Z' = Spec(A') ->> Z = Spec(A)$ is an etale cover of affine $X$-schemes. 
  // $
  //   cal(F)(Z') = product_i cal(F)(Z_i), cal(F)(Z' times_Z Z') = product_(i,j) cal(F)(Z_i times_Z Z_j)
  // $

  // In Lecture 3, we showed that: 
  // + For $f: Z' -> Z$ fpqc, 
  //   $
  //     Hom(Z, Y) -> Hom(Z', Y) arrows.rr Hom(Z'', Y)
  //   $
  //   is exact. 

  // + Fpqc descent holds for quasi-coherent sheaves. 

  (1) We need an equalizer: 
  $
    Hom_X (Z, Y) -> Hom_X (Z', Y) arrows.rr Hom_X (Z' times_Z Z', Y)
  $
  This is just @fpqc-descent-of-morphisms, the fpqc descent of morphisms. 

  (2) Let $f: Z -> X$ be an object of $Et_X$ and $cal(M) in QCoh(X)$. We need a left exact sequence: 
  $
    0 -> Gamma(Z, f^* cal(M)) -> Gamma(Z', f'^* cal(M)) -> Gamma(Z'', f''^* cal(M))
  $
  i.e. a left exact sequence: 
  $
    0 -> Hom(cal(O)_Z, f^* cal(M)) -> Hom(cal(O)_(Z'), f'^* cal(M)) -> Hom(cal(O)_(Z''), f''^* cal(M))
  $
  However, this follows exactly from full faithfulness of fpqc descent of quasi-coherent sheaves, i.e. @fpqc-descent-of-sheaves. 
]

#example[
  We have the following common examples of etale sheaves: 

  - The sheaf $GG_a = cal(O)_(X,et): Et_X^opp -> cAb, Z |-> cal(O)_Z (Z)$, sending every etale scheme over $X$ to its global functions. 

  - The multiplicative group sheaf $GG_m$. It is the etale sheaf associated with the abelian group scheme $GG_(m,X) = X otimes_ZZ Spec(ZZ[x, y]\/(x y - 1))$: 
    $
      GG_m: Et_X^opp -> cAb, Z |-> Hom_X (Z, GG_(m,X)) = Hom(Z, GG_(m,ZZ)) = cal(O)_Z (Z)^times
    $

  - The sheaf $mu_n$ of $n$-th roots of unity. It is the etale sheaf associated with the abelian group scheme $mu_(n,X) = X otimes_ZZ Spec(ZZ[x]\/(x^n-1))$: 
    $
      mu_n: Et_X^opp -> cAb, Z |-> Hom_X (Z, mu_(n,X)) = Hom(Z, mu_(n,ZZ)) = {omega in cal(O)_Z (Z) : omega^n = 1}
    $
]
